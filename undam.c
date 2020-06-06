#include "postgres.h"

#include "access/genam.h"
#include "access/generic_xlog.h"
#include "access/heapam.h"
#include "access/multixact.h"
#include "access/reloptions.h"
#include "access/relscan.h"
#include "access/skey.h"
#include "access/tableam.h"
#include "access/tsmapi.h"
#include "access/visibilitymap.h"
#include "access/xact.h"
#include "catalog/index.h"
#include "catalog/storage.h"
#include "catalog/storage_xlog.h"
#include "commands/vacuum.h"
#include "executor/executor.h"
#include "executor/tuptable.h"
#include "funcapi.h"
#include "mb/pg_wchar.h"
#include "miscadmin.h"
#include "nodes/execnodes.h"
#include "storage/bufmgr.h"
#include "storage/checksum.h"
#include "storage/ipc.h"
#include "storage/lmgr.h"
#include "storage/predicate.h"
#include "storage/procarray.h"
#include "storage/smgr.h"
#include "utils/builtins.h"
#include "utils/datum.h"
#include "utils/inval.h"
#include "utils/relcache.h"
#include "utils/snapmgr.h"
#include "pgstat.h"

#include "undam.h"

PG_MODULE_MAGIC;

#define FORCE_TUPLE_LOCK 1

PG_FUNCTION_INFO_V1(undam_tableam_handler);
PG_FUNCTION_INFO_V1(undam_rel_info);

typedef struct _MdfdVec
{
	File		mdfd_vfd;		/* fd number in fd.c's pool */
	BlockNumber mdfd_segno;		/* segment number, from 0 */
} MdfdVec;

void		_PG_init(void);

#define NOT_IMPLEMENTED							\
    do { \
        elog(ERROR, "UNDAM: function \"%s\" is not implemented", __func__); \
    } while (0)

static bool        UndamAutoChunkSize;
static int         UndamChunkSize;
static int         UndamNAllocChains;
static int         UndamMaxRelations;
static HTAB*       UndamRelInfoHash;
static LWLock*     UndamRelInfoLock;
static relopt_kind UndamReloptKind;

static shmem_startup_hook_type prev_shmem_startup_hook = NULL;

/********************************************************************
 * Main Undam functions
 ********************************************************************/

static uint64 UndamDeleteTuple(Relation rel, UndamPosition pos, UndamPosition undo);

/*
 * Register modified buffer for logged relation using Generic WAL record.
 */
static Page
UndamModifyBuffer(Relation rel, GenericXLogState* state, Buffer buf)
{
	Page pg;
	if (RelationNeedsWAL(rel))
	{
		pg = GenericXLogRegisterBuffer(state, buf, 0);
	}
	else
	{
		MarkBufferDirty(buf);
		pg = BufferGetPage(buf);
	}
	return pg;
}

/*
 * Flush chnages to the log if needed
 */
static void
UndamXLogFinish(Relation rel, GenericXLogState* state)
{
	if (state)
	{
		if (RelationNeedsWAL(rel))
		{
			GenericXLogFinish(state);
		}
		else
		{
			pfree(state);
		}
	}
}

/*
 * Choose optimal chunk size for the relation.
 * If relation has only fixed size attributes and their total size is in range [MIN_CHUNK_SIZE..MAX_CHUNK_SIZE] then use it chunk size
 * for this relation so that record fits in one chunk. If total size is smaller than MIN_CHUNK_SIZE, then choose MIN_CHUNK_SIZE as chunk
 * size for this relation. If total size is greater than MAX_CHUNK_SIZE or contains varying size attributes the use current value of
 * undam.chunk_size GUC as chunk size.
 * Please notice that this estimation may be not optimal in case of large fraction of NULL values in the record.
 */
static int32
UndamOptimalChunkSize(Relation rel)
{
	int32		data_length = 0;
	TupleDesc	tupdesc = rel->rd_att;
	int32		tuple_length;
	int saveEncoding = GetDatabaseEncoding();
	SetDatabaseEncoding(PG_SQL_ASCII);

	for (int i = 0; i < tupdesc->natts; i++)
	{
		Form_pg_attribute att = TupleDescAttr(tupdesc, i);

		if (att->attisdropped)
			continue;
		data_length = att_align_nominal(data_length, att->attalign);
		if (att->attlen > 0)
		{
			/* Fixed-length types are never toastable */
			data_length += att->attlen;
		}
		else
		{
			int32		maxlen = type_maximum_size(att->atttypid,
												   att->atttypmod);
			if (maxlen < 0)
			{
				SetDatabaseEncoding(saveEncoding);
				return UndamChunkSize;
			}
			else
				data_length += maxlen;
		}
	}
	SetDatabaseEncoding(saveEncoding);
	tuple_length = MAXALIGN(offsetof(UndamTupleHeader, hdr.t_bits) +
							BITMAPLEN(tupdesc->natts)) + MAXALIGN(data_length);
	return tuple_length < MIN_CHUNK_SIZE ? MIN_CHUNK_SIZE : tuple_length < MAX_CHUNK_SIZE ? tuple_length : UndamChunkSize;
}

/*
 * Read and if necesary intialize new page. We have to switch on zero_damahged_pages to allow
 * reading beyond end of file. Alternatively we have to use relation extension lock which
 * can be a battleneck and limit concurrency.
 */
static Buffer
UndamReadBuffer(Relation reln, ForkNumber forkNum, BlockNumber blockNum)
{
	bool save_zero_damaged_pages = zero_damaged_pages;
	Buffer buf;
	zero_damaged_pages = true;
	buf = ReadBufferExtended(reln, forkNum, blockNum, RBM_NORMAL, NULL);
	zero_damaged_pages = save_zero_damaged_pages;
	return buf;
}

/*
 * Locate allocation chain for the relation and initialize first UndamNAllocChains blocks of relation of not initialized yet.
 */
static UndamRelationInfo*
UndamGetRelationInfo(Relation rel)
{
	bool found;
	UndamRelationInfo* relinfo;

	LWLockAcquire(UndamRelInfoLock, LW_SHARED);
	relinfo = (UndamRelationInfo*)hash_search(UndamRelInfoHash, &RelationGetRelid(rel), HASH_FIND, NULL);
	LWLockRelease(UndamRelInfoLock);
	if (relinfo != NULL)
		return relinfo;

	LWLockAcquire(UndamRelInfoLock, LW_EXCLUSIVE);
	relinfo = (UndamRelationInfo*)hash_search(UndamRelInfoHash, &RelationGetRelid(rel), HASH_ENTER, &found);
	if (!found)
	{
		int nAllocChains = UndamNAllocChains;
		for (int fork = MAIN_FORKNUM; fork <= EXT_FORKNUM; fork++)
		{
			for (int chain = 0; chain < nAllocChains; chain++)
			{
				Buffer buf = UndamReadBuffer(rel, fork, chain);
				UndamPageHeader* pg = (UndamPageHeader*)BufferGetPage(buf);

				LockBuffer(buf, BUFFER_LOCK_SHARE);

				if (chain == 0 && fork == MAIN_FORKNUM)
				{
					relinfo->chunkSize = pg->chunkSize;
					relinfo->nChains = nAllocChains = pg->nChains;
				}
				else if (relinfo->chunkSize != pg->chunkSize || relinfo->nChains != pg->nChains)
				{
					elog(ERROR, "UNDAM: corrupted metapage");
				}
				relinfo->chains[chain].forks[fork].head = pg->head;
				relinfo->chains[chain].forks[fork].tail = pg->tail;

				UnlockReleaseBuffer(buf);
			}
		}
		relinfo->nScannedTuples = 0;
		relinfo->nScannedChunks = 0;
		relinfo->nScannedVersions = 0;
	}
	LWLockRelease(UndamRelInfoLock);
	return relinfo;
}

/*
 * Calculate last block number.
 * Please notice that there may be empty blocks in the middle.
 */
static BlockNumber
UndamGetLastBlock(Relation rel, int fork)
{
	BlockNumber last = 0;
	UndamRelationInfo* relinfo = UndamGetRelationInfo(rel);
	for (int chain = 0; chain < N_ALLOC_CHAINS; chain++)
	{
		last = Max(last, relinfo->chains[chain].forks[fork].tail);
	}
	return last + 1;
}

/*
 * Initialize shared memory hash for alloc chains
 */
static void
UndamShmemStartup(void)
{
	HASHCTL info;

	if (prev_shmem_startup_hook) {
		prev_shmem_startup_hook();
    }
	memset(&info, 0, sizeof(info));
	info.keysize = sizeof(Oid);
	info.entrysize = sizeof(UndamRelationInfo);
	UndamRelInfoHash = ShmemInitHash("undam hash",
									 UndamMaxRelations, UndamMaxRelations,
									 &info,
									 HASH_ELEM | HASH_BLOBS);
	UndamRelInfoLock = &(GetNamedLWLockTranche("undam"))->lock;
}

/*
 * Save chain of chunks representing tuple to the database.
 * For object consisting of more than one chunk tail is always written after head so that we always observer consistent chain.
 * If "tupSize" is not zero, then header chunk is written. In this case "data" points to HeapTupleHeader.
 * Returns position of first chunk in the chain.
 */
static UndamPosition
UndamWriteData(Relation rel, int forknum, char* data, uint32 size, UndamPosition undoPos, uint32 tupSize, UndamPosition tailChunk)
{
	UndamRelationInfo* relinfo = UndamGetRelationInfo(rel);
	int chunkDataSize = CHUNK_SIZE - offsetof(UndamTupleChunk, data); /* We use UndamTupleChunk for estimating of size of data stored in tuple, because head chunk is always written separately */
	int nChunks = (size + chunkDataSize - 1) / chunkDataSize;
	int available = size - (nChunks-1) * chunkDataSize;
	int chainNo = random() % N_ALLOC_CHAINS; /* choose random chain to minimize probability of allocation chain buffer lock conflicts */
	static const char zeros[BLCKSZ];

	Assert(undoPos != 0 && tailChunk != 0);

 	do
	{
		BlockNumber blocknum = relinfo->chains[chainNo].forks[forknum].head;
		UndamPageHeader* pg;
		UndamPageHeader* chain = NULL;
		int item = CHUNKS_PER_BLOCK; /* We need to link chaunks in L1 list so we have to write them in reverse order */
		Buffer chainBuf = InvalidBuffer;
		Buffer buf;
		int    segno;
		GenericXLogState* xlogState = GenericXLogStart(rel);

		if (blocknum == InvalidBlockNumber) /* Allocation chain is empty */
		{
			chainBuf = UndamReadBuffer(rel, forknum, chainNo);
			LockBuffer(chainBuf, BUFFER_LOCK_EXCLUSIVE);
			chain = (UndamPageHeader*)BufferGetPage(chainBuf);
			if (chain->head == InvalidBlockNumber) /* extend chain */
			{
				Assert(relinfo->chains[chainNo].forks[forknum].tail == chain->tail);
				chain = (UndamPageHeader*)UndamModifyBuffer(rel, xlogState, chainBuf);
				blocknum = chain->tail += N_ALLOC_CHAINS;
				/*
				 * Check if segment is already opened. We have to do this check to prevent
				 * error in _mdfd_getseg when crossing segment boundary
				 */
				segno = blocknum/RELSEG_SIZE;
				if (segno > 0 && rel->rd_smgr->md_num_open_segs[forknum] == segno)
				{
					FileTruncate(rel->rd_smgr->md_seg_fds[forknum][segno-1].mdfd_vfd, RELSEG_SIZE*BLCKSZ, WAIT_EVENT_DATA_FILE_TRUNCATE);
					smgrextend(rel->rd_smgr, forknum, blocknum, (char*)zeros, true);
				}
				/* To avoid deadlock we enforce that block with smaller address is locked first */
				Assert(blocknum > chainNo);
				chain->head = blocknum;
				relinfo->chains[chainNo].forks[forknum].tail = blocknum;
				relinfo->chains[chainNo].forks[forknum].head = blocknum;
			}
			else
			{
				blocknum = chain->head;
				/* Release chain buffer to avoid deadlock */
				UnlockReleaseBuffer(chainBuf);
				chainBuf = InvalidBuffer;
				chain = NULL;
			}
		}
		buf = UndamReadBuffer(rel, forknum, blocknum);
		LockBuffer(buf, BUFFER_LOCK_EXCLUSIVE);
		pg = (UndamPageHeader*)UndamModifyBuffer(rel, xlogState, buf);

		if (PageIsNew(pg)) /* Lazy initialization of the page */
		{
			Assert(blocknum >= N_ALLOC_CHAINS); /* Root pages should already be initialized */
			pg->pd_special = pg->pd_lower = pg->pd_upper = sizeof(UndamPageHeader);
			pg->head = pg->tail = pg->next = InvalidBlockNumber;
		}

		/* Use free chunks in this block */
		do
		{
			/* Search for free chunk */
			do
			{
				item -= 1;
			}
			while (pg->allocMask[item >> 6] & ((uint64)1 << (item & 63)));  /* first chunk is not allocated, so use it as barrier */

			if (item != 0)  /* has some free space */
			{
				if (tupSize != 0) /* Header chunk */
				{
					UndamTupleHeader* tup = (UndamTupleHeader*)((char*)pg + item*CHUNK_SIZE);
					memcpy(&tup->hdr, data, size);
					tup->undoChain = undoPos;
					tup->nextChunk = tailChunk;
					tup->size = tupSize;
					Assert(nChunks == 1);
				}
				else
				{
					UndamTupleChunk* chunk = (UndamTupleChunk*)((char*)pg + item*CHUNK_SIZE);
					memcpy(chunk->data, data + (nChunks-1)*chunkDataSize, available);
					chunk->next = tailChunk;
					available = chunkDataSize;
				}
				tailChunk = GET_POSITION(blocknum, item);
				pg->allocMask[item >> 6] |= (uint64)1 << (item & 63);
				nChunks -= 1;
			}
			else
				break;
		} while (nChunks != 0);

		/* No free space on the page: exclude it from allocation chain */
		if (item == 0)
		{
			BlockNumber nextFree = pg->next;

			if (chainNo != blocknum) /* target chunk is not chain header */
			{
				if (chain == NULL)
				{
					Assert(chainBuf == InvalidBuffer);
					/* Locate block with chain header */
					chainBuf = UndamReadBuffer(rel, forknum, chainNo);
					/* To avoid deadlock we enforce that block with smaller address is locked first */
					if (chainNo < blocknum)
					{
						/* Save updated page, unlock it and then lock chain header */
						UndamXLogFinish(rel, xlogState);
						xlogState = NULL;
						LockBuffer(buf, BUFFER_LOCK_UNLOCK);

						LockBuffer(chainBuf, BUFFER_LOCK_EXCLUSIVE);
						LockBuffer(buf, BUFFER_LOCK_EXCLUSIVE);
						pg = (UndamPageHeader*)BufferGetPage(buf);
						if (!(pg->pd_flags & PD_PAGE_FULL))
						{
							item = CHUNKS_PER_BLOCK;
							/* Recheck that page is still full */
							do
							{
								item -= 1;
							}
							while (pg->allocMask[item >> 6] & ((uint64)1 << (item & 63)));  /* first chunk is not allocated, so use it as barrier */
							if (item == 0)
							{
								xlogState = GenericXLogStart(rel);
								chain = (UndamPageHeader*)UndamModifyBuffer(rel, xlogState, chainBuf);
								nextFree = pg->next;
							}
						}
					}
					else
					{
						LockBuffer(chainBuf, BUFFER_LOCK_EXCLUSIVE);
						chain = (UndamPageHeader*)UndamModifyBuffer(rel, xlogState, chainBuf);
					}
				}
			}
			else
			{
				Assert(chain == NULL);
				chain = pg;
			}

			if (chain && chain->head == blocknum) /* Alloc chain was not already updated by some other backend */
			{
				Assert(!(pg->pd_flags & PD_PAGE_FULL));
				Assert(nextFree != blocknum);
				pg->pd_flags |= PD_PAGE_FULL;
				relinfo->chains[chainNo].forks[forknum].head = chain->head = nextFree;
			}
		}
		UndamXLogFinish(rel, xlogState);
		xlogState = NULL;
		UnlockReleaseBuffer(buf);
		if (chainBuf)
			UnlockReleaseBuffer(chainBuf);
	}
	while (nChunks != 0);

	Assert(tailChunk != 0);
	return tailChunk;
}


/*
 * Insert new tuple in the table.
 */
static void
UndamInsertTuple(Relation rel, int forknum, HeapTuple tuple)
{
	UndamRelationInfo* relinfo = UndamGetRelationInfo(rel);
	int available = CHUNK_SIZE - offsetof(UndamTupleHeader, hdr);
	UndamPosition pos;

	if (tuple->t_len <= available) /* Fit in one chunk */
	{
		pos = UndamWriteData(rel, forknum, (char*)tuple->t_data, tuple->t_len, INVALID_POSITION, tuple->t_len, INVALID_POSITION);
	}
	else /* Tuple doesn't fit in chunk */
	{
		/* First write tail... */
		pos = UndamWriteData(rel, EXT_FORKNUM, (char*)tuple->t_data + available, tuple->t_len - available, INVALID_POSITION, 0, INVALID_POSITION);
		/* ... and then head */
		pos = UndamWriteData(rel, forknum, (char*)tuple->t_data, available, INVALID_POSITION, tuple->t_len, pos);
	}
	ItemPointerSet(&tuple->t_self, POSITION_GET_BLOCK_NUMBER(pos), POSITION_GET_ITEM(pos));
}

/*
 * Update existed tuple: create copy of head chunk and link it in undo chain.
 * This function is passed locked buffer and unlock it on return.
 */
static void
UndamUpdateTuple(Relation rel, HeapTuple tuple, Buffer buffer)
{
	UndamRelationInfo* relinfo = UndamGetRelationInfo(rel);
	int offs = tuple->t_self.ip_posid*CHUNK_SIZE;
	int available = CHUNK_SIZE - offsetof(UndamTupleHeader, hdr);
	GenericXLogState* xlogState = GenericXLogStart(rel);
	UndamPageHeader* pg = (UndamPageHeader*)UndamModifyBuffer(rel, xlogState, buffer);
	UndamTupleHeader* old = (UndamTupleHeader*)((char*)pg + offs);
	int len = Min(old->size, available);
	UndamPosition undo = old->undoChain;
	UndamPosition truncateChain = INVALID_POSITION;
	Assert(len > 0);

	if (undo != INVALID_POSITION)
	{
		if (HeapTupleHeaderXminFrozen(&old->hdr)
			|| TransactionIdPrecedes(HeapTupleHeaderGetRawXmin(&old->hdr), RecentGlobalXmin))
		{
			/* Updated version is visible for everybody: truncate its undo chain */
			truncateChain = undo;
			undo = INVALID_POSITION;
		}
	}
	/* Create copy of head chunk */
	old->undoChain = UndamWriteData(rel, EXT_FORKNUM, (char*)&old->hdr, len, undo, old->size, old->nextChunk);
	if (truncateChain != INVALID_POSITION)
	{
		UndamDeleteTuple(rel, truncateChain, 0);
	}
	len = Min(tuple->t_len, available);
	memcpy(&old->hdr, tuple->t_data, len); /* in-place update of head chunk */
	old->hdr.t_ctid = tuple->t_self;
	old->size = tuple->t_len;
	if (tuple->t_len > available)
	{
		/* Write tail chunks. As far as we are writing them in another fork, there can not be deadlock caused by buffer lock conflict */
		old->nextChunk = UndamWriteData(rel, EXT_FORKNUM, (char*)tuple->t_data + len, tuple->t_len - len, INVALID_POSITION, 0, INVALID_POSITION);
	}
	else
		old->nextChunk = INVALID_POSITION;
	UndamXLogFinish(rel, xlogState);
	UnlockReleaseBuffer(buffer);
}

/*
 * Read tuple visible in the specified snapshot.
 * This function traverse undo chain and use stadnard visibility function to determine proper tuple.
 * Once such tuple is located all its chunks are fetched.
 * Returns NULL if no visible tuple is found.
 * Otherwise returns unattached heap tuple (not pinning any buffer).
 */
static HeapTuple
UndamReadTuple(UndamRelationInfo* relinfo, Relation rel, Snapshot snapshot, ItemPointer ip, Buffer currBuf)
{
	BlockNumber blocknum = BlockIdGetBlockNumber(&ip->ip_blkid);
	int offs = ip->ip_posid*CHUNK_SIZE;
	int forknum = MAIN_FORKNUM; /* Start from main fork */
	HeapTupleData tuphdr;

	tuphdr.t_tableOid = RelationGetRelid(rel);
	tuphdr.t_self = *ip;
	relinfo->nScannedTuples += 1;
	do
	{
		Buffer buf = currBuf == InvalidBuffer ? UndamReadBuffer(rel, forknum, blocknum) : currBuf;
		UndamPageHeader* pg = (UndamPageHeader*)BufferGetPage(buf);
		UndamTupleHeader* tup = (UndamTupleHeader*)((char*)pg + offs);
		int len;

		if (currBuf == InvalidBuffer)
			LockBuffer(buf, BUFFER_LOCK_SHARE);

		len = tup->size;
		tuphdr.t_data = &tup->hdr;
		tuphdr.t_len = len;

		relinfo->nScannedVersions += 1;

		if (HeapTupleSatisfiesVisibility(&tuphdr, snapshot, buf))
		{
			HeapTuple tuple = (HeapTuple)palloc(sizeof(HeapTupleData) + len);
			int available = CHUNK_SIZE - offsetof(UndamTupleHeader, hdr);

			*tuple = tuphdr;
			tuple->t_data = (HeapTupleHeader)(tuple + 1); /* store tuple's body just after the header */
			relinfo->nScannedChunks += 1;

			if (len <= available)
			{
				memcpy(tuple->t_data, &tup->hdr, len); /* tuple fits in one chunk */
			}
			else
			{
				char* dst = (char*)tuple->t_data;
				UndamPosition next = tup->nextChunk;

				memcpy(dst, &tup->hdr, available);
				dst += available;
				len -= available;
				available = CHUNK_SIZE - offsetof(UndamTupleChunk, data); /* rest chunks have more space */

				/* Copy rest of chunks */
				do {
					UndamTupleChunk* chunk;
					Assert(next != INVALID_POSITION);
					UnlockReleaseBuffer(buf);
					buf = UndamReadBuffer(rel, EXT_FORKNUM, POSITION_GET_BLOCK_NUMBER(next));
					pg = (UndamPageHeader*)BufferGetPage(buf);
					chunk = (UndamTupleChunk*)((char*)pg + POSITION_GET_BLOCK_OFFSET(next));
					LockBuffer(buf, BUFFER_LOCK_SHARE);
					memcpy(dst, chunk->data, Min(len, available));
					next = chunk->next;
					dst += available;
					len -= available;
					relinfo->nScannedChunks += 1;
				} while (len > 0);
			}
			if (currBuf == InvalidBuffer)
				UnlockReleaseBuffer(buf);
			return tuple;
		}
		currBuf = InvalidBuffer;
		blocknum = POSITION_GET_BLOCK_NUMBER(tup->undoChain);
		offs = POSITION_GET_BLOCK_OFFSET(tup->undoChain);
		UnlockReleaseBuffer(buf);
		forknum = EXT_FORKNUM; /* undo chain is in extension fork */
	}
	while (blocknum != InvalidBlockNumber);

	return NULL;
}


/*
 * Delete unused version of the tuple from extension fork.
 * If undo is 0, then we delete undo chain from the first (head) chunk.
 */
static uint64
UndamDeleteTuple(Relation rel, UndamPosition pos, UndamPosition undo)
{
	UndamRelationInfo* relinfo = UndamGetRelationInfo(rel);
	BlockNumber blocknum = POSITION_GET_BLOCK_NUMBER(pos);
	int item = POSITION_GET_ITEM(pos);
	uint64 nDeletedChunks = 0;

	while (true)
	{
		Buffer buf = UndamReadBuffer(rel, EXT_FORKNUM, blocknum);
		GenericXLogState* xlogState = GenericXLogStart(rel);
		UndamPageHeader* pg;
		UndamPosition next;
		int chainNo = 0;
		Buffer chainBuf = InvalidBuffer;
		Assert(item > 0 && item < CHUNKS_PER_BLOCK);

		LockBuffer(buf, BUFFER_LOCK_EXCLUSIVE);
		pg = (UndamPageHeader*)BufferGetPage(buf);
		if (pg->pd_flags & PD_PAGE_FULL) /* page was full: include it in allocation chain  */
		{
			chainNo = blocknum % N_ALLOC_CHAINS;
			if (chainNo != blocknum)
			{
				chainBuf = UndamReadBuffer(rel, EXT_FORKNUM, chainNo);
				/* To avoid deadlock we enforce that block with smaller address is locked first */
				if (chainNo < blocknum)
				{
					LockBuffer(buf, BUFFER_LOCK_UNLOCK);
					LockBuffer(chainBuf, BUFFER_LOCK_EXCLUSIVE);
					LockBuffer(buf, BUFFER_LOCK_EXCLUSIVE);
				}
				else
					LockBuffer(chainBuf, BUFFER_LOCK_EXCLUSIVE);
			}
		}
		pg = (UndamPageHeader*)UndamModifyBuffer(rel, xlogState, buf);
		Assert(pg->allocMask[item >> 6] & ((uint64)1 << (item & 63)));
		pg->allocMask[item >> 6] &= ~((uint64)1 << (item & 63));
		nDeletedChunks += 1;

		if (undo) /* not first chunk */
		{
			UndamTupleChunk* chunk = (UndamTupleChunk*)((char*)pg + item*CHUNK_SIZE);
			next = chunk->next;
			Assert(next != 0);
		}
		else
		{
			UndamTupleHeader* hdr = (UndamTupleHeader*)((char*)pg + item*CHUNK_SIZE);
			undo = hdr->undoChain;
			next = hdr->nextChunk;
			Assert(undo != 0 && next != 0); /* 0 is not valid position value */
		}
		memset((char*)pg + item*CHUNK_SIZE, 0xDE, CHUNK_SIZE);
		if (pg->pd_flags & PD_PAGE_FULL) /* page was full: include it in allocation chain  */
		{
			UndamPageHeader* chain;

			pg->pd_flags &= ~PD_PAGE_FULL;

			if (chainBuf) /* check if allocation chain header is at the same page */
			{
				chain = (UndamPageHeader*)UndamModifyBuffer(rel, xlogState, chainBuf);
				Assert(chain->head == relinfo->chains[chainNo].forks[EXT_FORKNUM].head);
			}
			else
			{
				Assert(chainNo == blocknum);
				chain = pg;
			}
			/* Update chain header */
			pg->next = chain->head;
			chain->head = blocknum;
			relinfo->chains[chainNo].forks[EXT_FORKNUM].head = blocknum;
		}
		UndamXLogFinish(rel, xlogState);
		if (chainBuf)
			UnlockReleaseBuffer(chainBuf);
		UnlockReleaseBuffer(buf);

		if (next == INVALID_POSITION) /* First traverse chain of tuple's chunks and then continute with undo chain */
		{
			if (undo == INVALID_POSITION)
				break;
			next = undo;
			undo = 0; /* Start with head chunk */
		}
		blocknum = POSITION_GET_BLOCK_NUMBER(next);
		item = POSITION_GET_ITEM(next);
	}
	return nDeletedChunks;
}

/********************************************************************
 * Damn! Bulk of static functions copied from heapam.c
 ********************************************************************/

/*
 * Check if the specified attribute's value is same in both given tuples.
 * Subroutine for HeapDetermineModifiedColumns.
 */
static bool
heap_tuple_attr_equals(TupleDesc tupdesc, int attrnum,
					   HeapTuple tup1, HeapTuple tup2)
{
	Datum		value1,
				value2;
	bool		isnull1,
				isnull2;
	Form_pg_attribute att;

	/*
	 * If it's a whole-tuple reference, say "not equal".  It's not really
	 * worth supporting this case, since it could only succeed after a no-op
	 * update, which is hardly a case worth optimizing for.
	 */
	if (attrnum == 0)
		return false;

	/*
	 * Likewise, automatically say "not equal" for any system attribute other
	 * than tableOID; we cannot expect these to be consistent in a HOT chain,
	 * or even to be set correctly yet in the new tuple.
	 */
	if (attrnum < 0)
	{
		if (attrnum != TableOidAttributeNumber)
			return false;
	}

	/*
	 * Extract the corresponding values.  XXX this is pretty inefficient if
	 * there are many indexed columns.  Should HeapDetermineModifiedColumns do
	 * a single heap_deform_tuple call on each tuple, instead?	But that
	 * doesn't work for system columns ...
	 */
	value1 = heap_getattr(tup1, attrnum, tupdesc, &isnull1);
	value2 = heap_getattr(tup2, attrnum, tupdesc, &isnull2);

	/*
	 * If one value is NULL and other is not, then they are certainly not
	 * equal
	 */
	if (isnull1 != isnull2)
		return false;

	/*
	 * If both are NULL, they can be considered equal.
	 */
	if (isnull1)
		return true;

	/*
	 * We do simple binary comparison of the two datums.  This may be overly
	 * strict because there can be multiple binary representations for the
	 * same logical value.  But we should be OK as long as there are no false
	 * positives.  Using a type-specific equality operator is messy because
	 * there could be multiple notions of equality in different operator
	 * classes; furthermore, we cannot safely invoke user-defined functions
	 * while holding exclusive buffer lock.
	 */
	if (attrnum <= 0)
	{
		/* The only allowed system columns are OIDs, so do this */
		return (DatumGetObjectId(value1) == DatumGetObjectId(value2));
	}
	else
	{
		Assert(attrnum <= tupdesc->natts);
		att = TupleDescAttr(tupdesc, attrnum - 1);
		return datumIsEqual(value1, value2, att->attbyval, att->attlen);
	}
}

/*
 * Check which columns are being updated.
 *
 * Given an updated tuple, determine (and return into the output bitmapset),
 * from those listed as interesting, the set of columns that changed.
 *
 * The input bitmapset is destructively modified; that is OK since this is
 * invoked at most once in heap_update.
 */
static Bitmapset *
HeapDetermineModifiedColumns(Relation relation, Bitmapset *interesting_cols,
							 HeapTuple oldtup, HeapTuple newtup)
{
	int			attnum;
	Bitmapset  *modified = NULL;

	while ((attnum = bms_first_member(interesting_cols)) >= 0)
	{
		attnum += FirstLowInvalidHeapAttributeNumber;

		if (!heap_tuple_attr_equals(RelationGetDescr(relation),
									attnum, oldtup, newtup))
			modified = bms_add_member(modified,
									  attnum - FirstLowInvalidHeapAttributeNumber);
	}

	return modified;
}

/*
 * MultiXactIdGetUpdateXid
 *
 * Given a multixact Xmax and corresponding infomask, which does not have the
 * HEAP_XMAX_LOCK_ONLY bit set, obtain and return the Xid of the updating
 * transaction.
 *
 * Caller is expected to check the status of the updating transaction, if
 * necessary.
 */
static TransactionId
MultiXactIdGetUpdateXid(TransactionId xmax, uint16 t_infomask)
{
	TransactionId update_xact = InvalidTransactionId;
	MultiXactMember *members;
	int			nmembers;

	Assert(!(t_infomask & HEAP_XMAX_LOCK_ONLY));
	Assert(t_infomask & HEAP_XMAX_IS_MULTI);

	/*
	 * Since we know the LOCK_ONLY bit is not set, this cannot be a multi from
	 * pre-pg_upgrade.
	 */
	nmembers = GetMultiXactIdMembers(xmax, &members, false, false);

	if (nmembers > 0)
	{
		int			i;

		for (i = 0; i < nmembers; i++)
		{
			/* Ignore lockers */
			if (!ISUPDATE_from_mxstatus(members[i].status))
				continue;

			/* there can be at most one updater */
			Assert(update_xact == InvalidTransactionId);
			update_xact = members[i].xid;
#ifndef USE_ASSERT_CHECKING

			/*
			 * in an assert-enabled build, walk the whole array to ensure
			 * there's no other updater.
			 */
			break;
#endif
		}

		pfree(members);
	}

	return update_xact;
}

/*
 * Each tuple lock mode has a corresponding heavyweight lock, and one or two
 * corresponding MultiXactStatuses (one to merely lock tuples, another one to
 * update them).  This table (and the macros below) helps us determine the
 * heavyweight lock mode and MultiXactStatus values to use for any particular
 * tuple lock strength.
 *
 * Don't look at lockstatus/updstatus directly!  Use get_mxact_status_for_lock
 * instead.
 */
static const struct
{
	LOCKMODE	hwlock;
	int			lockstatus;
	int			updstatus;
}

			tupleLockExtraInfo[MaxLockTupleMode + 1] =
{
	{							/* LockTupleKeyShare */
		AccessShareLock,
		MultiXactStatusForKeyShare,
		-1						/* KeyShare does not allow updating tuples */
	},
	{							/* LockTupleShare */
		RowShareLock,
		MultiXactStatusForShare,
		-1						/* Share does not allow updating tuples */
	},
	{							/* LockTupleNoKeyExclusive */
		ExclusiveLock,
		MultiXactStatusForNoKeyUpdate,
		MultiXactStatusNoKeyUpdate
	},
	{							/* LockTupleExclusive */
		AccessExclusiveLock,
		MultiXactStatusForUpdate,
		MultiXactStatusUpdate
	}
};

/* Get the LOCKMODE for a given MultiXactStatus */
#define LOCKMODE_from_mxstatus(status) \
			(tupleLockExtraInfo[TUPLOCK_from_mxstatus((status))].hwlock)

/*
 * Return the MultiXactStatus corresponding to the given tuple lock mode.
 */
static MultiXactStatus
get_mxact_status_for_lock(LockTupleMode mode, bool is_update)
{
	int			retval;

	if (is_update)
		retval = tupleLockExtraInfo[mode].updstatus;
	else
		retval = tupleLockExtraInfo[mode].lockstatus;

	if (retval == -1)
		elog(ERROR, "UNDAM: invalid lock tuple mode %d/%s", mode,
			 is_update ? "true" : "false");

	return (MultiXactStatus) retval;
}

/*
 * This table maps tuple lock strength values for each particular
 * MultiXactStatus value.
 */
static const int MultiXactStatusLock[MaxMultiXactStatus + 1] =
{
	LockTupleKeyShare,			/* ForKeyShare */
	LockTupleShare,				/* ForShare */
	LockTupleNoKeyExclusive,	/* ForNoKeyUpdate */
	LockTupleExclusive,			/* ForUpdate */
	LockTupleNoKeyExclusive,	/* NoKeyUpdate */
	LockTupleExclusive			/* Update */
};

/* Get the LockTupleMode for a given MultiXactStatus */
#define TUPLOCK_from_mxstatus(status) \
			(MultiXactStatusLock[(status)])

/*
 * For a given MultiXactId, return the hint bits that should be set in the
 * tuple's infomask.
 *
 * Normally this should be called for a multixact that was just created, and
 * so is on our local cache, so the GetMembers call is fast.
 */
static void
GetMultiXactIdHintBits(MultiXactId multi, uint16 *new_infomask,
					   uint16 *new_infomask2)
{
	int			nmembers;
	MultiXactMember *members;
	int			i;
	uint16		bits = HEAP_XMAX_IS_MULTI;
	uint16		bits2 = 0;
	bool		has_update = false;
	LockTupleMode strongest = LockTupleKeyShare;

	/*
	 * We only use this in multis we just created, so they cannot be values
	 * pre-pg_upgrade.
	 */
	nmembers = GetMultiXactIdMembers(multi, &members, false, false);

	for (i = 0; i < nmembers; i++)
	{
		LockTupleMode mode;

		/*
		 * Remember the strongest lock mode held by any member of the
		 * multixact.
		 */
		mode = TUPLOCK_from_mxstatus(members[i].status);
		if (mode > strongest)
			strongest = mode;

		/* See what other bits we need */
		switch (members[i].status)
		{
			case MultiXactStatusForKeyShare:
			case MultiXactStatusForShare:
			case MultiXactStatusForNoKeyUpdate:
				break;

			case MultiXactStatusForUpdate:
				bits2 |= HEAP_KEYS_UPDATED;
				break;

			case MultiXactStatusNoKeyUpdate:
				has_update = true;
				break;

			case MultiXactStatusUpdate:
				bits2 |= HEAP_KEYS_UPDATED;
				has_update = true;
				break;
		}
	}

	if (strongest == LockTupleExclusive ||
		strongest == LockTupleNoKeyExclusive)
		bits |= HEAP_XMAX_EXCL_LOCK;
	else if (strongest == LockTupleShare)
		bits |= HEAP_XMAX_SHR_LOCK;
	else if (strongest == LockTupleKeyShare)
		bits |= HEAP_XMAX_KEYSHR_LOCK;

	if (!has_update)
		bits |= HEAP_XMAX_LOCK_ONLY;

	if (nmembers > 0)
		pfree(members);

	*new_infomask = bits;
	*new_infomask2 = bits2;
}

/*
 * Given an original set of Xmax and infomask, and a transaction (identified by
 * add_to_xmax) acquiring a new lock of some mode, compute the new Xmax and
 * corresponding infomasks to use on the tuple.
 *
 * Note that this might have side effects such as creating a new MultiXactId.
 *
 * Most callers will have called HeapTupleSatisfiesUpdate before this function;
 * that will have set the HEAP_XMAX_INVALID bit if the xmax was a MultiXactId
 * but it was not running anymore. There is a race condition, which is that the
 * MultiXactId may have finished since then, but that uncommon case is handled
 * either here, or within MultiXactIdExpand.
 *
 * There is a similar race condition possible when the old xmax was a regular
 * TransactionId.  We test TransactionIdIsInProgress again just to narrow the
 * window, but it's still possible to end up creating an unnecessary
 * MultiXactId.  Fortunately this is harmless.
 */
static void
compute_new_xmax_infomask(TransactionId xmax, uint16 old_infomask,
						  uint16 old_infomask2, TransactionId add_to_xmax,
						  LockTupleMode mode, bool is_update,
						  TransactionId *result_xmax, uint16 *result_infomask,
						  uint16 *result_infomask2)
{
	TransactionId new_xmax;
	uint16		new_infomask,
				new_infomask2;

	Assert(TransactionIdIsCurrentTransactionId(add_to_xmax));

l5:
	new_infomask = 0;
	new_infomask2 = 0;
	if (old_infomask & HEAP_XMAX_INVALID)
	{
		/*
		 * No previous locker; we just insert our own TransactionId.
		 *
		 * Note that it's critical that this case be the first one checked,
		 * because there are several blocks below that come back to this one
		 * to implement certain optimizations; old_infomask might contain
		 * other dirty bits in those cases, but we don't really care.
		 */
		if (is_update)
		{
			new_xmax = add_to_xmax;
			if (mode == LockTupleExclusive)
				new_infomask2 |= HEAP_KEYS_UPDATED;
		}
		else
		{
			new_infomask |= HEAP_XMAX_LOCK_ONLY;
			switch (mode)
			{
				case LockTupleKeyShare:
					new_xmax = add_to_xmax;
					new_infomask |= HEAP_XMAX_KEYSHR_LOCK;
					break;
				case LockTupleShare:
					new_xmax = add_to_xmax;
					new_infomask |= HEAP_XMAX_SHR_LOCK;
					break;
				case LockTupleNoKeyExclusive:
					new_xmax = add_to_xmax;
					new_infomask |= HEAP_XMAX_EXCL_LOCK;
					break;
				case LockTupleExclusive:
					new_xmax = add_to_xmax;
					new_infomask |= HEAP_XMAX_EXCL_LOCK;
					new_infomask2 |= HEAP_KEYS_UPDATED;
					break;
				default:
					new_xmax = InvalidTransactionId;	/* silence compiler */
					elog(ERROR, "UNDAM: invalid lock mode");
			}
		}
	}
	else if (old_infomask & HEAP_XMAX_IS_MULTI)
	{
		MultiXactStatus new_status;

		/*
		 * Currently we don't allow XMAX_COMMITTED to be set for multis, so
		 * cross-check.
		 */
		Assert(!(old_infomask & HEAP_XMAX_COMMITTED));

		/*
		 * A multixact together with LOCK_ONLY set but neither lock bit set
		 * (i.e. a pg_upgraded share locked tuple) cannot possibly be running
		 * anymore.  This check is critical for databases upgraded by
		 * pg_upgrade; both MultiXactIdIsRunning and MultiXactIdExpand assume
		 * that such multis are never passed.
		 */
		if (HEAP_LOCKED_UPGRADED(old_infomask))
		{
			old_infomask &= ~HEAP_XMAX_IS_MULTI;
			old_infomask |= HEAP_XMAX_INVALID;
			goto l5;
		}

		/*
		 * If the XMAX is already a MultiXactId, then we need to expand it to
		 * include add_to_xmax; but if all the members were lockers and are
		 * all gone, we can do away with the IS_MULTI bit and just set
		 * add_to_xmax as the only locker/updater.  If all lockers are gone
		 * and we have an updater that aborted, we can also do without a
		 * multi.
		 *
		 * The cost of doing GetMultiXactIdMembers would be paid by
		 * MultiXactIdExpand if we weren't to do this, so this check is not
		 * incurring extra work anyhow.
		 */
		if (!MultiXactIdIsRunning(xmax, HEAP_XMAX_IS_LOCKED_ONLY(old_infomask)))
		{
			if (HEAP_XMAX_IS_LOCKED_ONLY(old_infomask) ||
				!TransactionIdDidCommit(MultiXactIdGetUpdateXid(xmax,
																old_infomask)))
			{
				/*
				 * Reset these bits and restart; otherwise fall through to
				 * create a new multi below.
				 */
				old_infomask &= ~HEAP_XMAX_IS_MULTI;
				old_infomask |= HEAP_XMAX_INVALID;
				goto l5;
			}
		}

		new_status = get_mxact_status_for_lock(mode, is_update);

		new_xmax = MultiXactIdExpand((MultiXactId) xmax, add_to_xmax,
									 new_status);
		GetMultiXactIdHintBits(new_xmax, &new_infomask, &new_infomask2);
	}
	else if (old_infomask & HEAP_XMAX_COMMITTED)
	{
		/*
		 * It's a committed update, so we need to preserve him as updater of
		 * the tuple.
		 */
		MultiXactStatus status;
		MultiXactStatus new_status;

		if (old_infomask2 & HEAP_KEYS_UPDATED)
			status = MultiXactStatusUpdate;
		else
			status = MultiXactStatusNoKeyUpdate;

		new_status = get_mxact_status_for_lock(mode, is_update);

		/*
		 * since it's not running, it's obviously impossible for the old
		 * updater to be identical to the current one, so we need not check
		 * for that case as we do in the block above.
		 */
		new_xmax = MultiXactIdCreate(xmax, status, add_to_xmax, new_status);
		GetMultiXactIdHintBits(new_xmax, &new_infomask, &new_infomask2);
	}
	else if (TransactionIdIsInProgress(xmax))
	{
		/*
		 * If the XMAX is a valid, in-progress TransactionId, then we need to
		 * create a new MultiXactId that includes both the old locker or
		 * updater and our own TransactionId.
		 */
		MultiXactStatus new_status;
		MultiXactStatus old_status;
		LockTupleMode old_mode;

		if (HEAP_XMAX_IS_LOCKED_ONLY(old_infomask))
		{
			if (HEAP_XMAX_IS_KEYSHR_LOCKED(old_infomask))
				old_status = MultiXactStatusForKeyShare;
			else if (HEAP_XMAX_IS_SHR_LOCKED(old_infomask))
				old_status = MultiXactStatusForShare;
			else if (HEAP_XMAX_IS_EXCL_LOCKED(old_infomask))
			{
				if (old_infomask2 & HEAP_KEYS_UPDATED)
					old_status = MultiXactStatusForUpdate;
				else
					old_status = MultiXactStatusForNoKeyUpdate;
			}
			else
			{
				/*
				 * LOCK_ONLY can be present alone only when a page has been
				 * upgraded by pg_upgrade.  But in that case,
				 * TransactionIdIsInProgress() should have returned false.  We
				 * assume it's no longer locked in this case.
				 */
				elog(WARNING, "LOCK_ONLY found for Xid in progress %u", xmax);
				old_infomask |= HEAP_XMAX_INVALID;
				old_infomask &= ~HEAP_XMAX_LOCK_ONLY;
				goto l5;
			}
		}
		else
		{
			/* it's an update, but which kind? */
			if (old_infomask2 & HEAP_KEYS_UPDATED)
				old_status = MultiXactStatusUpdate;
			else
				old_status = MultiXactStatusNoKeyUpdate;
		}

		old_mode = TUPLOCK_from_mxstatus(old_status);

		/*
		 * If the lock to be acquired is for the same TransactionId as the
		 * existing lock, there's an optimization possible: consider only the
		 * strongest of both locks as the only one present, and restart.
		 */
		if (xmax == add_to_xmax)
		{
			/*
			 * Note that it's not possible for the original tuple to be
			 * updated: we wouldn't be here because the tuple would have been
			 * invisible and we wouldn't try to update it.  As a subtlety,
			 * this code can also run when traversing an update chain to lock
			 * future versions of a tuple.  But we wouldn't be here either,
			 * because the add_to_xmax would be different from the original
			 * updater.
			 */
			Assert(HEAP_XMAX_IS_LOCKED_ONLY(old_infomask));

			/* acquire the strongest of both */
			if (mode < old_mode)
				mode = old_mode;
			/* mustn't touch is_update */

			old_infomask |= HEAP_XMAX_INVALID;
			goto l5;
		}

		/* otherwise, just fall back to creating a new multixact */
		new_status = get_mxact_status_for_lock(mode, is_update);
		new_xmax = MultiXactIdCreate(xmax, old_status,
									 add_to_xmax, new_status);
		GetMultiXactIdHintBits(new_xmax, &new_infomask, &new_infomask2);
	}
	else if (!HEAP_XMAX_IS_LOCKED_ONLY(old_infomask) &&
			 TransactionIdDidCommit(xmax))
	{
		/*
		 * It's a committed update, so we gotta preserve him as updater of the
		 * tuple.
		 */
		MultiXactStatus status;
		MultiXactStatus new_status;

		if (old_infomask2 & HEAP_KEYS_UPDATED)
			status = MultiXactStatusUpdate;
		else
			status = MultiXactStatusNoKeyUpdate;

		new_status = get_mxact_status_for_lock(mode, is_update);

		/*
		 * since it's not running, it's obviously impossible for the old
		 * updater to be identical to the current one, so we need not check
		 * for that case as we do in the block above.
		 */
		new_xmax = MultiXactIdCreate(xmax, status, add_to_xmax, new_status);
		GetMultiXactIdHintBits(new_xmax, &new_infomask, &new_infomask2);
	}
	else
	{
		/*
		 * Can get here iff the locking/updating transaction was running when
		 * the infomask was extracted from the tuple, but finished before
		 * TransactionIdIsInProgress got to run.  Deal with it as if there was
		 * no locker at all in the first place.
		 */
		old_infomask |= HEAP_XMAX_INVALID;
		goto l5;
	}

	*result_infomask = new_infomask;
	*result_infomask2 = new_infomask2;
	*result_xmax = new_xmax;
}

/*
 * Acquire heavyweight locks on tuples, using a LockTupleMode strength value.
 * This is more readable than having every caller translate it to lock.h's
 * LOCKMODE.
 */
#define LockTupleTuplock(rel, tup, mode) \
	LockTuple((rel), (tup), tupleLockExtraInfo[mode].hwlock)
#define UnlockTupleTuplock(rel, tup, mode) \
	UnlockTuple((rel), (tup), tupleLockExtraInfo[mode].hwlock)
#define ConditionalLockTupleTuplock(rel, tup, mode) \
	ConditionalLockTuple((rel), (tup), tupleLockExtraInfo[mode].hwlock)

/*
 * Acquire heavyweight lock on the given tuple, in preparation for acquiring
 * its normal, Xmax-based tuple lock.
 *
 * have_tuple_lock is an input and output parameter: on input, it indicates
 * whether the lock has previously been acquired (and this function does
 * nothing in that case).  If this function returns success, have_tuple_lock
 * has been flipped to true.
 *
 * Returns false if it was unable to obtain the lock; this can only happen if
 * wait_policy is Skip.
 */
static bool
heap_acquire_tuplock(Relation relation, ItemPointer tid, LockTupleMode mode,
					 LockWaitPolicy wait_policy, bool *have_tuple_lock)
{
	if (*have_tuple_lock)
		return true;

	switch (wait_policy)
	{
		case LockWaitBlock:
			LockTupleTuplock(relation, tid, mode);
			break;

		case LockWaitSkip:
			if (!ConditionalLockTupleTuplock(relation, tid, mode))
				return false;
			break;

		case LockWaitError:
			if (!ConditionalLockTupleTuplock(relation, tid, mode))
				ereport(ERROR,
						(errcode(ERRCODE_LOCK_NOT_AVAILABLE),
						 errmsg("could not obtain lock on row in relation \"%s\"",
								RelationGetRelationName(relation))));
			break;
	}
	*have_tuple_lock = true;

	return true;
}
static void
UpdateXminHintBits(HeapTupleHeader tuple, Buffer buffer, TransactionId xid)
{
	Assert(TransactionIdEquals(HeapTupleHeaderGetRawXmin(tuple), xid));
	Assert(!(tuple->t_infomask & HEAP_XMAX_IS_MULTI));

	if (!(tuple->t_infomask & (HEAP_XMAX_COMMITTED | HEAP_XMAX_INVALID)))
	{
		if (TransactionIdDidCommit(xid))
			HeapTupleSetHintBits(tuple, buffer, HEAP_XMIN_COMMITTED,
								 xid);
		else
			HeapTupleSetHintBits(tuple, buffer, HEAP_XMIN_INVALID,
								 InvalidTransactionId);
	}
}

/********************************************************************
 * Table AM implementations
 ********************************************************************/

static const TupleTableSlotOps *
undam_slot_callbacks(Relation relation)
{
    return &TTSOpsHeapTuple; /* we do not what to pin buffers so we create heap-only tuple */
}


static TableScanDesc
undam_beginscan(Relation relation, Snapshot snapshot,
				int nkeys, ScanKey key,
				ParallelTableScanDesc parallel_scan,
				uint32 flags)
{
    UndamScanDesc  scan;

	RelationIncrementReferenceCount(relation);

    /*
     * allocate and initialize scan descriptor
     */
    scan = (UndamScanDesc) palloc(sizeof(UndamScanDescData));
    scan->base.rs_rd = relation;
    scan->base.rs_snapshot = snapshot;
    scan->base.rs_nkeys = nkeys;
    scan->base.rs_flags = flags;
	scan->base.rs_parallel = parallel_scan;
	scan->lastBlock = UndamGetLastBlock(relation, MAIN_FORKNUM);
	scan->currBuf = InvalidBuffer;
	scan->relinfo = UndamGetRelationInfo(relation);
	ItemPointerSet(&scan->currItem, 0, 0);
    return (TableScanDesc) scan;
}

static void UndamUnlockReleaseCurrentBuffer(UndamScanDesc uscan)
{
	if (uscan->currBuf != InvalidBuffer)
	{
		UnlockReleaseBuffer(uscan->currBuf);
		uscan->currBuf = InvalidBuffer;
	}
}

static void UndamReleaseCurrentBuffer(UndamScanDesc uscan)
{
	if (uscan->currBuf != InvalidBuffer)
	{
		ReleaseBuffer(uscan->currBuf);
		uscan->currBuf = InvalidBuffer;
	}
}

static void UndamUnlockCurrentBuffer(UndamScanDesc uscan)
{
	Assert(uscan->currBuf != InvalidBuffer);
	LockBuffer(uscan->currBuf, BUFFER_LOCK_UNLOCK);
}

static Buffer UndamGetCurrentBuffer(UndamScanDesc uscan, BlockNumber blocknum)
{
	if (uscan->currBuf == InvalidBuffer)
	{
		uscan->currBuf = UndamReadBuffer(uscan->base.rs_rd, MAIN_FORKNUM, blocknum);
	}
	LockBuffer(uscan->currBuf, BUFFER_LOCK_SHARE);
	return uscan->currBuf;
}

static bool
undam_getnextslot(TableScanDesc scan, ScanDirection direction, TupleTableSlot *slot)
{
    UndamScanDesc uscan = (UndamScanDesc) scan;
    Relation      rel = scan->rs_rd;
	UndamRelationInfo* relinfo = uscan->relinfo;
	HeapTuple     tuple;
	int           item = ItemPointerGetOffsetNumberNoCheck(&uscan->currItem); /* next item to try */
	BlockNumber   blocknum = ItemPointerGetBlockNumberNoCheck(&uscan->currItem);
	int           nChunks = CHUNKS_PER_BLOCK;
	ParallelBlockTableScanDesc pbscan =	(ParallelBlockTableScanDesc) scan->rs_parallel;
    /* TODO: handle direction */
    if (direction == BackwardScanDirection)
        elog(ERROR, "UNDAM: backward scan is not implemented");

	if (pbscan != NULL && item == 0)
	{

		table_block_parallelscan_startblock_init(scan->rs_rd, pbscan);
		blocknum = table_block_parallelscan_nextpage(scan->rs_rd, pbscan);
		UndamReleaseCurrentBuffer(uscan);
	}
	item += 1;
	while (blocknum < uscan->lastBlock)
	{
		Buffer buf = UndamGetCurrentBuffer(uscan, blocknum);
		UndamPageHeader* pg = (UndamPageHeader*)BufferGetPage(buf);

		while (item < nChunks)
		{
			if (pg->allocMask[item >> 6] & ((uint64)1 << (item & 63))) /* chunk is allocated */
			{
				ItemPointerSet(&uscan->currItem, blocknum, item);
				tuple = UndamReadTuple(relinfo, rel, scan->rs_snapshot, &uscan->currItem, buf);
				if (tuple != NULL) /* Found some visible version */
				{
					ExecStoreHeapTuple(tuple, slot, true);
					ItemPointerSetOffsetNumber(&uscan->currItem, item);
					UndamUnlockCurrentBuffer(uscan);
					return true;
				}
			}
			item += 1;
		}
		UndamUnlockReleaseCurrentBuffer(uscan);
		if (pbscan != NULL)
			blocknum = table_block_parallelscan_nextpage(scan->rs_rd, pbscan);
		else
			blocknum += 1;
		item = 1; /* first chunk is used for page header, so skip it */
	}
	return false;
}

static void
undam_rescan(TableScanDesc scan, ScanKey key, bool set_params,
            bool allow_strat, bool allow_sync, bool allow_pagemode)
{
    UndamScanDesc uscan = (UndamScanDesc) scan;
	ItemPointerSet(&uscan->currItem, 0, 1); /* restart from the beginning */
}

static void
undam_endscan(TableScanDesc scan)
{
	UndamUnlockReleaseCurrentBuffer((UndamScanDesc)scan);
    /*
     * decrement relation reference count and free scan descriptor storage
     */
    RelationDecrementReferenceCount(scan->rs_rd);

    if (scan->rs_flags & SO_TEMP_SNAPSHOT)
        UnregisterSnapshot(scan->rs_snapshot);

    pfree(scan);
}

static IndexFetchTableData *
undam_index_fetch_begin(Relation rel)
{
	IndexFetchTableData *scan = (IndexFetchTableData*)palloc(sizeof(IndexFetchTableData));
	scan->rel = rel;
	return scan;
}


static void
undam_index_fetch_reset(IndexFetchTableData *scan)
{
    /* nothing to reset yet */
}

static void
undam_index_fetch_end(IndexFetchTableData *scan)
{
    pfree(scan);
}


static bool
undam_index_fetch_tuple(struct IndexFetchTableData *scan,
						ItemPointer tid,
						Snapshot snapshot,
						TupleTableSlot *slot,
						bool *call_again, bool *all_dead)
{
	HeapTuple tuple = UndamReadTuple(UndamGetRelationInfo(scan->rel), scan->rel, snapshot, tid, InvalidBuffer);
	if (tuple != NULL) /* found some visible version */
	{
		ExecStoreHeapTuple(tuple, slot, true);
		return true;
	}
	return false;
}

static bool
undam_scan_bitmap_next_block(TableScanDesc scan,
                            struct TBMIterateResult *tbmres)
{
    UndamScanDesc uscan = (UndamScanDesc) scan;
	ItemPointerSet(&uscan->currItem, tbmres->blockno, 1);
	return tbmres->blockno < uscan->lastBlock;
}

static bool
undam_scan_bitmap_next_tuple(TableScanDesc scan,
                            struct TBMIterateResult *tbmres,
                            TupleTableSlot *slot)
{
    UndamScanDesc uscan = (UndamScanDesc) scan;
    Relation      rel = scan->rs_rd;
	UndamRelationInfo* relinfo = uscan->relinfo;
	HeapTuple     tuple;
	int           offs = ItemPointerGetOffsetNumber(&uscan->currItem);
	BlockNumber   blocknum = tbmres->blockno;
	int           nChunks = CHUNKS_PER_BLOCK;
	Buffer buf = UndamReadBuffer(rel, MAIN_FORKNUM, blocknum);
	UndamPageHeader* pg = (UndamPageHeader*)BufferGetPage(buf);
	bool found = false;

	LockBuffer(buf, BUFFER_LOCK_SHARE);

	while (true)
	{
		int item;
		if (tbmres->ntuples >= 0)
		{
			/* for non-lossy scan offs points to the position in tbmres->offsets. */
			if (offs-1 >= tbmres->ntuples)  /* posid has to be greater than zero, so subtract one to use it as zero-based index in array */
				break;
			item = tbmres->offsets[offs-1];
			Assert(item > 0 && item < nChunks);
		}
		else /* lossy scan */
		{
			/* for lossy scan we interpret offs as a position in the block */
			item = offs;
 			if (item > nChunks)
				break;
		}
		offs += 1; /* advance offset: we will store it in currItem on loop exit */
		if (pg->allocMask[item >> 6] & ((uint64)1 << (item & 63))) /* chunk is allocated */
		{
			ItemPointerSetOffsetNumber(&uscan->currItem, item);
			tuple = UndamReadTuple(relinfo, rel, scan->rs_snapshot, &uscan->currItem, InvalidBuffer);
			if (tuple != NULL) /* found some visible tuple */
			{
				found = true;
				ExecStoreHeapTuple(tuple, slot, true);
				break;
			}
		}
	}
	UnlockReleaseBuffer(buf);
	ItemPointerSetOffsetNumber(&uscan->currItem, offs); /* save updated offset for next call of undam_scan_bitmap_next_tuple */
	return found;
}

static bool
undam_fetch_row_version(Relation relation,
						ItemPointer tid,
						Snapshot snapshot,
						TupleTableSlot *slot)
{
	HeapTuple tuple = UndamReadTuple(UndamGetRelationInfo(relation), relation, snapshot, tid, InvalidBuffer);
	if (tuple != NULL) /* found some visible tuple */
	{
		ExecStoreHeapTuple(tuple, slot, true);
		return true;
	}
	return false;
}

static bool
undam_tuple_tid_valid(TableScanDesc scan, ItemPointer tid)
{
	UndamScanDesc uscan = (UndamScanDesc)scan;
	UndamRelationInfo* relinfo PG_USED_FOR_ASSERTS_ONLY = UndamGetRelationInfo(scan->rs_rd);
	int item = ItemPointerGetOffsetNumber(&uscan->currItem);
	BlockNumber   blocknum = ItemPointerGetBlockNumber(&uscan->currItem);
	Buffer buf = UndamReadBuffer(scan->rs_rd, MAIN_FORKNUM, blocknum);
	UndamPageHeader* pg = (UndamPageHeader*)BufferGetPage(buf);
	bool is_valid;

	Assert(item > 0 && item < CHUNKS_PER_BLOCK);

	LockBuffer(buf, BUFFER_LOCK_SHARE);
	is_valid = (pg->allocMask[item >> 6] >> (item & 63)) & 1; /* we only check that buffer was allocated */
	UnlockReleaseBuffer(buf);

	return is_valid;
}


static bool
undam_tuple_satisfies_snapshot(Relation rel, TupleTableSlot *slot,
                                Snapshot snapshot)
{
	HeapTupleTableSlot *hslot = (HeapTupleTableSlot *) slot;
	BlockNumber   blocknum = ItemPointerGetBlockNumber(&slot->tts_tid);
	Buffer buf = UndamReadBuffer(rel, MAIN_FORKNUM, blocknum);
	bool satisfies;

	LockBuffer(buf, BUFFER_LOCK_SHARE);
	satisfies = HeapTupleSatisfiesVisibility(hslot->tuple, snapshot, buf);
	UnlockReleaseBuffer(buf);

	return satisfies;
}

static void
undam_tuple_insert(Relation rel, TupleTableSlot *slot, CommandId cid,
				   int options, BulkInsertState bistate)
{
	HeapTuple tup = ExecCopySlotHeapTuple(slot);
	TransactionId xid = GetCurrentTransactionId();

	tup->t_data->t_infomask &= ~(HEAP_XACT_MASK);
	tup->t_data->t_infomask2 &= ~(HEAP2_XACT_MASK);
	tup->t_data->t_infomask |= HEAP_XMAX_INVALID;
	HeapTupleHeaderSetXmin(tup->t_data, xid);
	if (options & HEAP_INSERT_FROZEN)
		HeapTupleHeaderSetXminFrozen(tup->t_data);

	HeapTupleHeaderSetCmin(tup->t_data, cid);
	HeapTupleHeaderSetXmax(tup->t_data, 0); /* for cleanliness */
	slot->tts_tableOid = tup->t_tableOid = RelationGetRelid(rel);

	UndamInsertTuple(rel, MAIN_FORKNUM, tup);
	slot->tts_tid = tup->t_self;

	pfree(tup);
}

static void
undam_multi_insert(Relation relation, TupleTableSlot **slots, int ntuples,
				   CommandId cid, int options, BulkInsertState bistate)
{
	for (int i = 0; i < ntuples; i++)
	{
		undam_tuple_insert(relation, slots[i], cid, options, bistate);
	}
}

static void
undam_tuple_insert_speculative(Relation rel, TupleTableSlot *slot,
							   CommandId cid, int options,
							   BulkInsertState bistate, uint32 specToken)
{
	HeapTuple tup = ExecCopySlotHeapTuple(slot);
	TransactionId xid = GetCurrentTransactionId();

	tup->t_data->t_infomask &= ~(HEAP_XACT_MASK);
	tup->t_data->t_infomask2 &= ~(HEAP2_XACT_MASK);
	tup->t_data->t_infomask |= HEAP_XMAX_INVALID;
	HeapTupleHeaderSetXmin(tup->t_data, xid);
	if (options & HEAP_INSERT_FROZEN)
		HeapTupleHeaderSetXminFrozen(tup->t_data);
	HeapTupleHeaderSetSpeculativeToken(tup->t_data, specToken);

	HeapTupleHeaderSetCmin(tup->t_data, cid);
	HeapTupleHeaderSetXmax(tup->t_data, 0); /* for cleanliness */
	slot->tts_tableOid = tup->t_tableOid = RelationGetRelid(rel);

	UndamInsertTuple(rel, MAIN_FORKNUM, tup);
	slot->tts_tid = tup->t_self;

	pfree(tup);
}

static void
undam_abort_speculative(Relation rel, ItemPointer tid)
{
	TransactionId xid = GetCurrentTransactionId();
	BlockNumber block;
	Buffer		buffer;
	TransactionId prune_xid;
	GenericXLogState* xlogState;
	Page* pg;
	HeapTupleHeader tup;
	UndamRelationInfo* relinfo = UndamGetRelationInfo(rel);

	Assert(ItemPointerIsValid(tid));

	block = ItemPointerGetBlockNumber(tid);
	buffer = ReadBuffer(rel, block);

	LockBuffer(buffer, BUFFER_LOCK_EXCLUSIVE);

	xlogState = GenericXLogStart(rel);
	pg = (Page*)UndamModifyBuffer(rel, xlogState, buffer);

	tup = &((UndamTupleHeader*)((char*)pg + ItemPointerGetOffsetNumber(tid)*CHUNK_SIZE))->hdr;
	/*
	 * Sanity check that the tuple really is a speculatively inserted tuple,
	 * inserted by us.
	 */
	if (tup->t_choice.t_heap.t_xmin != xid)
		elog(ERROR, "attempted to kill a tuple inserted by another transaction");
	if (!HeapTupleHeaderIsSpeculative(tup))
		elog(ERROR, "attempted to kill a non-speculative tuple");
	Assert(!HeapTupleHeaderIsHeapOnly(tup));

	/*
	 * No need to check for serializable conflicts here.  There is never a
	 * need for a combocid, either.  No need to extract replica identity, or
	 * do anything special with infomask bits.
	 */

	START_CRIT_SECTION();

	/*
	 * The tuple will become DEAD immediately.  Flag that this page is a
	 * candidate for pruning by setting xmin to TransactionXmin. While not
	 * immediately prunable, it is the oldest xid we can cheaply determine
	 * that's safe against wraparound / being older than the table's
	 * relfrozenxid.  To defend against the unlikely case of a new relation
	 * having a newer relfrozenxid than our TransactionXmin, use relfrozenxid
	 * if so (vacuum can't subsequently move relfrozenxid to beyond
	 * TransactionXmin, so there's no race here).
	 */
	Assert(TransactionIdIsValid(TransactionXmin));
	if (TransactionIdPrecedes(TransactionXmin, rel->rd_rel->relfrozenxid))
		prune_xid = rel->rd_rel->relfrozenxid;
	else
		prune_xid = TransactionXmin;
	PageSetPrunable(pg, prune_xid);

	/* store transaction information of xact deleting the tuple */
	tup->t_infomask &= ~(HEAP_XMAX_BITS | HEAP_MOVED);
	tup->t_infomask2 &= ~HEAP_KEYS_UPDATED;

	/*
	 * Set the tuple header xmin to InvalidTransactionId.  This makes the
	 * tuple immediately invisible everyone.  (In particular, to any
	 * transactions waiting on the speculative token, woken up later.)
	 */
	HeapTupleHeaderSetXmin(tup, InvalidTransactionId);

	/* Clear the speculative insertion token too */
	tup->t_ctid = *tid;

	END_CRIT_SECTION();
	UndamXLogFinish(rel, xlogState);
	UnlockReleaseBuffer(buffer);

	pgstat_count_heap_delete(rel);
}

static void
undam_finish_speculative(Relation rel, ItemPointer tid)
{
	BlockNumber block;
	Buffer		buffer;
	GenericXLogState* xlogState;
	Page* pg;
	HeapTupleHeader tup;
	UndamRelationInfo* relinfo = UndamGetRelationInfo(rel);

	Assert(ItemPointerIsValid(tid));

	block = ItemPointerGetBlockNumber(tid);
	buffer = ReadBuffer(rel, block);

	LockBuffer(buffer, BUFFER_LOCK_EXCLUSIVE);

	xlogState = GenericXLogStart(rel);
	pg = (Page*)UndamModifyBuffer(rel, xlogState, buffer);

	/*
	 * Replace the speculative insertion token with a real t_ctid, pointing to
	 * itself like it does on regular tuples.
	 */
	tup = &((UndamTupleHeader*)((char*)pg + ItemPointerGetOffsetNumber(tid)*CHUNK_SIZE))->hdr;

	START_CRIT_SECTION();

	tup->t_ctid = *tid;

	END_CRIT_SECTION();

	UndamXLogFinish(rel, xlogState);
	UnlockReleaseBuffer(buffer);
}

static void
undam_tuple_complete_speculative(Relation rel, TupleTableSlot *slot,
								 uint32 specToken, bool succeeded)
{
	bool		shouldFree = true;
	HeapTuple	tuple = ExecFetchSlotHeapTuple(slot, true, &shouldFree);

	/* adjust the tuple's state accordingly */
	if (succeeded)
		undam_finish_speculative(rel, &slot->tts_tid);
	else
		undam_abort_speculative(rel, &slot->tts_tid);

	if (shouldFree)
		pfree(tuple);
}

static TM_Result
undam_tuple_update(Relation relation, ItemPointer otid, TupleTableSlot *slot,
				   CommandId cid, Snapshot snapshot, Snapshot crosscheck,
				   bool wait, TM_FailureData *tmfd,
				   LockTupleMode *lockmode, bool *update_indexes)
{
	UndamRelationInfo* relinfo = UndamGetRelationInfo(relation);
	TransactionId xid = GetCurrentTransactionId();
	Bitmapset  *key_attrs;
	Bitmapset  *modified_attrs;
	HeapTupleData oldtup;
	bool		shouldFree = true;
	HeapTuple   origtup;
	HeapTuple   newtup = ExecFetchSlotHeapTuple(slot, true, &shouldFree);
	bool		key_intact;
	bool		checked_lockers;
	bool		locker_remains;
	bool		have_tuple_lock = false;
	bool		iscombo;
	TransactionId xmax_new_tuple,
				xmax_old_tuple;
	uint16		infomask_old_tuple,
				infomask2_old_tuple,
				infomask_new_tuple,
				infomask2_new_tuple;
	Buffer      buffer;
	Page		page;
	TM_Result   result;
	UndamTupleHeader* tup;

	Assert(ItemPointerIsValid(otid));

	/*
	 * Forbid this during a parallel operation, lest it allocate a combocid.
	 * Other workers might need that combocid for visibility checks, and we
	 * have no provision for broadcasting it to them.
	 */
	if (IsInParallelMode())
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_TRANSACTION_STATE),
				 errmsg("cannot update tuples during a parallel operation")));

	key_attrs = RelationGetIndexAttrBitmap(relation, INDEX_ATTR_BITMAP_KEY);
	origtup = UndamReadTuple(relinfo, relation, snapshot, otid, InvalidBuffer);
	Assert(origtup != NULL);
	modified_attrs = HeapDetermineModifiedColumns(relation, key_attrs,
												  origtup, newtup);
	pfree(origtup); /* not needed any more */

	if (!bms_is_empty(modified_attrs))
	{
		*lockmode = LockTupleNoKeyExclusive;
		key_intact = true;

		/*
		 * If this is the first possibly-multixact-able operation in the
		 * current transaction, set my per-backend OldestMemberMXactId
		 * setting. We can be certain that the transaction will never become a
		 * member of any older MultiXactIds than that.  (We have to do this
		 * even if we end up just using our own TransactionId below, since
		 * some other backend could incorporate our XID into a MultiXact
		 * immediately afterwards.)
		 */
		MultiXactIdSetOldestMember();
	}
	else
	{
		*lockmode = LockTupleExclusive;
		key_intact = false;
	}

#if FORCE_TUPLE_LOCK
	heap_acquire_tuplock(relation, otid, *lockmode,
						 LockWaitBlock, &have_tuple_lock);
#endif

	buffer = UndamReadBuffer(relation, MAIN_FORKNUM, ItemPointerGetBlockNumber(otid));
	page = BufferGetPage(buffer);
	LockBuffer(buffer, BUFFER_LOCK_EXCLUSIVE);
	tup = (UndamTupleHeader*)((char*)page + ItemPointerGetOffsetNumber(otid)*CHUNK_SIZE);
	oldtup.t_tableOid = RelationGetRelid(relation);
	oldtup.t_data = &tup->hdr;
	oldtup.t_len = tup->size;
	oldtup.t_self = *otid;

l2:
	checked_lockers = false;
	locker_remains = false;
	result = HeapTupleSatisfiesUpdate(&oldtup, cid, buffer);

	/* see below about the "no wait" case */
	Assert(result != TM_BeingModified && (result != TM_Invisible || wait));

	if (result == TM_Invisible && wait)
	{
		TransactionId xwait;
		bool		can_continue = false;

		/*
		 * XXX note that we don't consider the "no wait" case here.  This
		 * isn't a problem currently because no caller uses that case, but it
		 * should be fixed if such a caller is introduced.  It wasn't a
		 * problem previously because this code would always wait, but now
		 * that some tuple locks do not conflict with one of the lock modes we
		 * use, it is possible that this case is interesting to handle
		 * specially.
		 *
		 * This may cause failures with third-party code that calls
		 * heap_update directly.
		 */

		xwait = HeapTupleHeaderGetRawXmin(oldtup.t_data);

		if (TransactionIdIsCurrentTransactionId(xwait))
		{
			/*
			 * The only locker is ourselves; we can avoid grabbing the tuple
			 * lock here, but must preserve our locking information.
			 */
			checked_lockers = true;
			locker_remains = true;
			can_continue = true;
		}
		else
		{
			/*
			 * Wait for regular transaction to end; but first, acquire tuple
			 * lock.
			 */
			LockBuffer(buffer, BUFFER_LOCK_UNLOCK);
#if !FORCE_TUPLE_LOCK
			heap_acquire_tuplock(relation, &(oldtup.t_self), *lockmode,
								 LockWaitBlock, &have_tuple_lock);
#endif
			XactLockTableWait(xwait, relation, &oldtup.t_self,
							  XLTW_Update);
			checked_lockers = true;
			LockBuffer(buffer, BUFFER_LOCK_EXCLUSIVE);

			/*
			 * xwait is done, but if xwait had just locked the tuple then some
			 * other xact could update this tuple before we get to this point.
			 * Check for xmax change, and start over if so.
			 */
			if (!TransactionIdEquals(xwait,
									 HeapTupleHeaderGetRawXmin(oldtup.t_data)))
				goto l2;
			UpdateXminHintBits(oldtup.t_data, buffer, xwait);
			if (oldtup.t_data->t_infomask & HEAP_XMIN_INVALID)
				can_continue = true;
		}

		if (can_continue)
			result = TM_Ok;
		else if (oldtup.t_data->t_infomask & HEAP_XMAX_INVALID)
			result = TM_Updated;
		else
			result = TM_Deleted;
	}

	if (crosscheck != InvalidSnapshot && result == TM_Ok)
	{
		/* Perform additional check for transaction-snapshot mode RI updates */
		if (!HeapTupleSatisfiesVisibility(&oldtup, crosscheck, buffer))
		{
			result = TM_Updated;
			Assert(!ItemPointerEquals(&oldtup.t_self, &oldtup.t_data->t_ctid));
		}
	}

	if (result != TM_Ok)
	{
		Assert(result == TM_SelfModified ||
			   result == TM_Updated ||
			   result == TM_Deleted ||
			   result == TM_Invisible);
		Assert(!(oldtup.t_data->t_infomask & HEAP_XMIN_INVALID));
		tmfd->ctid = oldtup.t_data->t_ctid;
		tmfd->xmax = HeapTupleHeaderGetUpdateXid(oldtup.t_data);
		if (result == TM_SelfModified)
			tmfd->cmax = HeapTupleHeaderGetCmax(oldtup.t_data);
		else
			tmfd->cmax = InvalidCommandId;
		UnlockReleaseBuffer(buffer);
		if (have_tuple_lock)
			UnlockTupleTuplock(relation, &(oldtup.t_self), *lockmode);
		bms_free(key_attrs);
		bms_free(modified_attrs);
		if (shouldFree)
			heap_freetuple(newtup);
		return result;
	}
	/* Fill in transaction status data */

	/*
	 * If the tuple we're updating is locked, we need to preserve the locking
	 * info in the old tuple's Xmax.  Prepare a new Xmax value for this.
	 */
	compute_new_xmax_infomask(HeapTupleHeaderGetRawXmax(oldtup.t_data),
							  oldtup.t_data->t_infomask,
							  oldtup.t_data->t_infomask2,
							  xid, *lockmode, true,
							  &xmax_old_tuple, &infomask_old_tuple,
							  &infomask2_old_tuple);



	/*
	 * And also prepare an Xmax value for the new copy of the tuple.  If there
	 * was no xmax previously, or there was one but all lockers are now gone,
	 * then use InvalidXid; otherwise, get the xmax from the old tuple.  (In
	 * rare cases that might also be InvalidXid and yet not have the
	 * HEAP_XMAX_INVALID bit set; that's fine.)
	 */
	if ((oldtup.t_data->t_infomask & HEAP_XMAX_INVALID) ||
		HEAP_LOCKED_UPGRADED(oldtup.t_data->t_infomask) ||
		(checked_lockers && !locker_remains))
		xmax_new_tuple = InvalidTransactionId;
	else
		xmax_new_tuple = HeapTupleHeaderGetRawXmax(oldtup.t_data);

	if (!TransactionIdIsValid(xmax_new_tuple))
	{
		infomask_new_tuple = HEAP_XMAX_INVALID;
		infomask2_new_tuple = 0;
	}
	else
	{
		/*
		 * If we found a valid Xmax for the new tuple, then the infomask bits
		 * to use on the new tuple depend on what was there on the old one.
		 * Note that since we're doing an update, the only possibility is that
		 * the lockers had FOR KEY SHARE lock.
		 */
		if (oldtup.t_data->t_infomask & HEAP_XMAX_IS_MULTI)
		{
			GetMultiXactIdHintBits(xmax_new_tuple, &infomask_new_tuple,
								   &infomask2_new_tuple);
		}
		else
		{
			infomask_new_tuple = HEAP_XMAX_KEYSHR_LOCK | HEAP_XMAX_LOCK_ONLY;
			infomask2_new_tuple = 0;
		}
	}

	/*
	 * Prepare the new tuple with the appropriate initial values of Xmin and
	 * Xmax, as well as initial infomask bits as computed above.
	 */
	newtup->t_data->t_infomask &= ~(HEAP_XACT_MASK);
	newtup->t_data->t_infomask2 &= ~(HEAP2_XACT_MASK);
	HeapTupleHeaderSetXmin(newtup->t_data, xid);
	HeapTupleHeaderSetCmin(newtup->t_data, cid);
	newtup->t_data->t_infomask |= HEAP_UPDATED | infomask_new_tuple;
	newtup->t_data->t_infomask2 |= infomask2_new_tuple;
	HeapTupleHeaderSetXmax(newtup->t_data, xmax_new_tuple);

	/*
	 * Replace cid with a combo cid if necessary.  Note that we already put
	 * the plain cid into the new tuple.
	 */
	HeapTupleHeaderAdjustCmax(oldtup.t_data, &cid, &iscombo);

	/*
	 * We're about to do the actual update -- check for conflict first, to
	 * avoid possibly having to roll back work we've just done.
	 *
	 * This is safe without a recheck as long as there is no possibility of
	 * another process scanning the pages between this check and the update
	 * being visible to the scan (i.e., exclusive buffer content lock(s) are
	 * continuously held from this point until the tuple update is visible).
	 *
	 * For the new tuple the only check needed is at the relation level, but
	 * since both tuples are in the same relation and the check for oldtup
	 * will include checking the relation level, there is no benefit to a
	 * separate check for the new tuple.
	 */
#if PG_VERSION_NUM >= 130000
	CheckForSerializableConflictIn(relation, otid, BufferGetBlockNumber(buffer));
#else
	CheckForSerializableConflictIn(relation, &oldtup, BufferGetBlockNumber(buffer));
#endif

	START_CRIT_SECTION();

	/*
	 * If this transaction commits, the old tuple will become DEAD sooner or
	 * later.  Set flag that this page is a candidate for pruning once our xid
	 * falls below the OldestXmin horizon.  If the transaction finally aborts,
	 * the subsequent page pruning will be a no-op and the hint will be
	 * cleared.
	 *
	 * XXX Should we set hint on newbuf as well?  If the transaction aborts,
	 * there would be a prunable tuple in the newbuf; but for now we choose
	 * not to optimize for aborts.  Note that heap_xlog_update must be kept in
	 * sync if this decision changes.
	 */
	PageSetPrunable(page, xid);

	/* Clear obsolete visibility flags, possibly set by ourselves above... */
	oldtup.t_data->t_infomask &= ~(HEAP_XMAX_BITS | HEAP_MOVED);
	oldtup.t_data->t_infomask2 &= ~HEAP_KEYS_UPDATED;
	/* ... and store info about transaction updating this tuple */
	Assert(TransactionIdIsValid(xmax_old_tuple));
	HeapTupleHeaderSetXmax(oldtup.t_data, xmax_old_tuple);
	oldtup.t_data->t_infomask |= infomask_old_tuple;
	oldtup.t_data->t_infomask2 |= infomask2_old_tuple;
	HeapTupleHeaderSetCmax(oldtup.t_data, cid, iscombo);

	END_CRIT_SECTION();

	if (key_intact)
	{
		UndamUpdateTuple(relation, &oldtup, buffer);
		UndamInsertTuple(relation, MAIN_FORKNUM, newtup);
	}
	else
	{
		newtup->t_self = *otid;
		UndamUpdateTuple(relation, newtup, buffer); /* will release buffer lock */
	}
	slot->tts_tid = newtup->t_self;
	/*
	 * Release the lmgr tuple lock, if we had it.
	 */
	if (have_tuple_lock)
		UnlockTupleTuplock(relation, &(oldtup.t_self), *lockmode);

	pgstat_count_heap_update(relation, !key_intact);

	*update_indexes = key_intact;
	bms_free(key_attrs);
	bms_free(modified_attrs);
	if (shouldFree)
		heap_freetuple(newtup);
	return TM_Ok;
}

static TM_Result
undam_tuple_lock(Relation relation, ItemPointer tid, Snapshot snapshot,
                  TupleTableSlot *slot, CommandId cid, LockTupleMode mode,
                  LockWaitPolicy wait_policy, uint8 flags,
                  TM_FailureData *tmfd)
{
	HeapTuple tuple;
	bool have_tuple_lock = false;

	heap_acquire_tuplock(relation, tid, mode,
						 wait_policy, &have_tuple_lock);

	tuple = UndamReadTuple(UndamGetRelationInfo(relation), relation, SnapshotAny, tid, InvalidBuffer);
	if (tuple != NULL) /* found some visible version */
	{
		ExecStoreHeapTuple(tuple, slot, true);
		tmfd->traversed = true;
		return TM_Ok;
	}
	return TM_Invisible;
}

static uint64
undam_relation_size(Relation rel, ForkNumber forkNumber)
{
	return (uint64)UndamGetLastBlock(rel, forkNumber)*BLCKSZ;
}

static bool
undam_relation_needs_toast_table(Relation rel)
{
	return false;
}


static void
undam_relation_estimate_size(Relation rel, int32 *attr_widths,
							 BlockNumber *pages, double *tuples,
							 double *allvisfrac)
{
	BlockNumber forks[2];
	UndamRelationInfo* relinfo = UndamGetRelationInfo(rel);
	for (int fork = MAIN_FORKNUM; fork <= EXT_FORKNUM; fork++)
		forks[fork] = UndamGetLastBlock(rel, fork);
	*pages = forks[MAIN_FORKNUM] + forks[EXT_FORKNUM];
	*tuples = (double)forks[MAIN_FORKNUM]*(CHUNKS_PER_BLOCK-1);
	*allvisfrac = 0;
}

/*
 * Check if item is marked as dead by vacuum
 */
static bool
UndamBitmapCheck(ItemPointer itemptr, void *state)
{
	UndamVacuumContext* ctx  = (UndamVacuumContext*)state;
	UndamRelationInfo* relinfo = ctx->relinfo;
	UndamPosition item = POSITION_FROM_ITEMPOINTER(itemptr);
	return (ctx->deadBitmap[item >> 6] >> (item & 63)) & 1;
}

/*
 * Vacuum all indexes associated with this relation
 */
static void
UndamVacuumIndexes(Relation rel, uint64* deadBitmap, uint64 reltuples, BufferAccessStrategy bstrategy)
{
	Relation   *Irel;
	int			nindexes;
	IndexVacuumInfo ivinfo;
	IndexBulkDeleteResult **stats;
	UndamVacuumContext ctx;

	ctx.deadBitmap = deadBitmap;
	ctx.relinfo = UndamGetRelationInfo(rel);

	/* Open all indexes of the relation */
	vac_open_indexes(rel, RowExclusiveLock, &nindexes, &Irel);
	stats = palloc0(sizeof(IndexBulkDeleteResult*)*nindexes);

	ivinfo.analyze_only = false;
	ivinfo.report_progress = false;
	ivinfo.estimated_count = true;
	ivinfo.message_level = DEBUG2;
	ivinfo.num_heap_tuples = reltuples;
	ivinfo.strategy = bstrategy;

	for (int idx = 0; idx < nindexes; idx++)
	{
		ivinfo.index = Irel[idx];
		stats[idx] = index_bulk_delete(&ivinfo, stats[idx], UndamBitmapCheck, (void*)&ctx);
	}
	/* TODO: do something with index stats */

	/* Done with indexes */
	vac_close_indexes(nindexes, Irel, RowExclusiveLock);
}

static void
undam_relation_vacuum(Relation rel,
					  struct VacuumParams *params,
					  BufferAccessStrategy bstrategy)
{
	UndamRelationInfo* relinfo = UndamGetRelationInfo(rel);
	BlockNumber lastBlock = UndamGetLastBlock(rel, MAIN_FORKNUM);
	int nChunks = CHUNKS_PER_BLOCK;
	HeapTupleData tuple;
	uint64  nTuples  = (uint64)lastBlock*nChunks;
	uint64* deadBitmap = (uint64*)calloc((nTuples+63)/64, 8); /* bitmap can be larger than 1Gb, so use calloc */
	uint64  nDeadTuples = 0;
	uint64  nVisibleForAllTuples = 0;
	uint64  nFrozenTuples = 0;
	uint64  nTruncatedUndoChains = 0;
	uint64  nUndoVersions = 0;
	uint64  nDeletedVersions = 0;
	TransactionId oldestXmin;
	TransactionId freezeLimit;
	MultiXactId   multiXactCutoff;

	tuple.t_tableOid = RelationGetRelid(rel);

	vacuum_set_xid_limits(rel,
						  params->freeze_min_age,
						  params->freeze_table_age,
						  params->multixact_freeze_min_age,
						  params->multixact_freeze_table_age,
						  &oldestXmin,
						  &freezeLimit,
						  NULL,
						  &multiXactCutoff,
						  NULL);
	elog(LOG, "UNDAM: vacuum of relation %s started", RelationGetRelationName(rel));
	for (BlockNumber block = 0; block < lastBlock; block++)
	{
		Buffer buf = UndamReadBuffer(rel, MAIN_FORKNUM, block);
		UndamPageHeader* pg = (UndamPageHeader*)BufferGetPage(buf);
		GenericXLogState* xlogState = NULL;

		LockBuffer(buf, BUFFER_LOCK_SHARE);

		for (int chunk = 1; chunk < nChunks; chunk++)
		{
			if (pg->allocMask[chunk >> 6] & ((uint64)1 << (chunk & 63)))
			{
				UndamTupleHeader* tup = (UndamTupleHeader*)((char*)pg + chunk*CHUNK_SIZE);
				tuple.t_data = &tup->hdr;
				tuple.t_len =  tup->size;
				if (HeapTupleSatisfiesVacuum(&tuple, oldestXmin, buf) == HEAPTUPLE_DEAD)
				{
					/* We can not delete dead tuples immediately because them are referenced by index */
					UndamPosition pos = GET_POSITION(block, chunk);
					Assert(tup->undoChain == INVALID_POSITION);
					deadBitmap[pos >> 6] |= (uint64)1 << (pos & 63);
					nDeadTuples += 1;
				}
				else if (!HeapTupleHeaderXminFrozen(&tup->hdr))
				{
					TransactionId xmin = HeapTupleHeaderGetRawXmin(&tup->hdr);
					if (TransactionIdPrecedes(xmin, oldestXmin)) /* Tuple is visible for everybody */
					{
						nVisibleForAllTuples += 1;
						if (xlogState == NULL)
						{
							/* Upgrade buffer lock to exclusive */
							LockBuffer(buf, BUFFER_LOCK_UNLOCK);
							LockBuffer(buf, BUFFER_LOCK_EXCLUSIVE);
							xlogState = GenericXLogStart(rel);
							pg = (UndamPageHeader*)UndamModifyBuffer(rel, xlogState, buf);
							tup = (UndamTupleHeader*)((char*)pg + chunk*CHUNK_SIZE);
							Assert(pg->allocMask[chunk >> 6] & ((uint64)1 << (chunk & 63)));
						}
						tuple.t_data = &tup->hdr;
						tuple.t_len =  tup->size;
						if (TransactionIdPrecedes(xmin, freezeLimit))
						{
							/* TODO: not sure that it is enough to freeze tuple: or should we use heap_freeze_tuple ? */
							tup->hdr.t_infomask |= HEAP_XMIN_FROZEN;
							nFrozenTuples += 1;
						}
						if (tup->undoChain != INVALID_POSITION)
						{
							/* We do not need undo chain any more */
							nDeletedVersions += UndamDeleteTuple(rel, tup->undoChain, 0);
							tup->undoChain = INVALID_POSITION;
							nTruncatedUndoChains += 1;
						}
					}
					else /* Traverse undo chain */
					{
						UndamPosition undo = tup->undoChain;
						while (undo != INVALID_POSITION)
						{
							Buffer vbuf = UndamReadBuffer(rel, EXT_FORKNUM, POSITION_GET_BLOCK_NUMBER(undo));
							UndamPageHeader* vpg = (UndamPageHeader*)BufferGetPage(vbuf);
							UndamTupleHeader* ver;
							int offs = POSITION_GET_BLOCK_OFFSET(undo);
							LockBuffer(vbuf, BUFFER_LOCK_SHARE);
							nUndoVersions += 1;
							ver = (UndamTupleHeader*)((char*)vpg + offs);
							Assert(ver->undoChain != 0);
							undo = ver->undoChain;

							if (TransactionIdPrecedes(HeapTupleHeaderGetRawXmin(&ver->hdr), oldestXmin)) /* Tuple is visible for everybody */
							{
								if (undo != INVALID_POSITION)
								{
									GenericXLogState* vxlogState = GenericXLogStart(rel);
									LockBuffer(vbuf, BUFFER_LOCK_UNLOCK);
									LockBuffer(vbuf, BUFFER_LOCK_EXCLUSIVE);
									vpg = (UndamPageHeader*)UndamModifyBuffer(rel, vxlogState, vbuf);
									ver = (UndamTupleHeader*)((char*)vpg + offs);
									Assert(ver->undoChain == undo);
									ver->undoChain = INVALID_POSITION;
									UndamXLogFinish(rel, vxlogState);
									nTruncatedUndoChains += 1;
									UnlockReleaseBuffer(vbuf);
									nDeletedVersions += UndamDeleteTuple(rel, undo, 0); /* delete rest of chain */
								} else
									UnlockReleaseBuffer(vbuf);
								break;
							}
							UnlockReleaseBuffer(vbuf);
						}
					}
				}
			}
		}
		UndamXLogFinish(rel, xlogState);
		UnlockReleaseBuffer(buf);
	}
	if (nDeadTuples != 0)
	{
		/* Some tuples can be deleted, s we need to update indexes */
		UndamVacuumIndexes(rel, deadBitmap, nTuples, bstrategy);

		/* Second pass: do actual deletion of tuples */
		for (BlockNumber block = 0; block < lastBlock; block++)
		{
			UndamTupleHeader* tup = NULL;
			Buffer buf = InvalidBuffer;
			GenericXLogState* xlogState = NULL;
			UndamPageHeader* pg = NULL;
			Buffer chainBuf = InvalidBuffer;
			int chainNo = 0;

			for (int chunk = 1; chunk < nChunks; chunk++)
			{
				UndamPosition pos = GET_POSITION(block, chunk);
				if (deadBitmap[pos >> 6] & ((uint64)1 << (pos & 63)))
				{
					if (!xlogState)
					{
						chainNo = block % N_ALLOC_CHAINS;
						buf = UndamReadBuffer(rel, MAIN_FORKNUM, block);
						LockBuffer(buf, BUFFER_LOCK_EXCLUSIVE);
						pg = (UndamPageHeader*)BufferGetPage(buf);

						if (pg->pd_flags & PD_PAGE_FULL) /* page was full: include it in allocation chain  */
						{
							if (chainNo != block)
							{
								chainBuf = UndamReadBuffer(rel, MAIN_FORKNUM, chainNo);
								/* To avoid deadlock we enforce that block with smaller address is locked first */
								if (chainNo < block)
								{
									LockBuffer(buf, BUFFER_LOCK_UNLOCK);
									LockBuffer(chainBuf, BUFFER_LOCK_EXCLUSIVE);
									LockBuffer(buf, BUFFER_LOCK_EXCLUSIVE);
								}
								else
									LockBuffer(chainBuf, BUFFER_LOCK_EXCLUSIVE);
							}
						}
						xlogState = GenericXLogStart(rel);
						pg = (UndamPageHeader*)UndamModifyBuffer(rel, xlogState, buf);
						Assert(pg->allocMask[chunk >> 6] & ((uint64)1 << (chunk & 63)));
						pg->allocMask[chunk >> 6] &= ~((uint64)1 << (chunk & 63));
						tup = (UndamTupleHeader*)((char*)pg + chunk*CHUNK_SIZE);
						if (tup->nextChunk != INVALID_POSITION)
							nDeletedVersions += UndamDeleteTuple(rel, tup->nextChunk, INVALID_POSITION); /* delete tuple tail */
					}
				}
			}
			if (xlogState) /* Some page tuples were deleted */
			{
				if (pg->pd_flags & PD_PAGE_FULL)  /* Page was full: include it in allocation chain  */
				{
					UndamPageHeader* chain;

					pg->pd_flags &= ~PD_PAGE_FULL;

					if (chainBuf) /* check if allocation chain header is at the same page */
					{
						chain = (UndamPageHeader*)UndamModifyBuffer(rel, xlogState, chainBuf);
						Assert(chain->head == relinfo->chains[chainNo].forks[MAIN_FORKNUM].head);
					}
					else
					{
						Assert(chainNo == block);
						chain = pg;
					}
					/* Update chain header */
					pg->next = chain->head;
					chain->head = block;
					relinfo->chains[chainNo].forks[MAIN_FORKNUM].head = block;
				}
				UndamXLogFinish(rel, xlogState);
				UnlockReleaseBuffer(buf);
				if (chainBuf)
					UnlockReleaseBuffer(chainBuf);
			}
		}
	}
	elog(LOG, "UNDAM: vacuum of relation %s completed: " UINT64_FORMAT " visible for all tuples, " UINT64_FORMAT " dead tuples, " UINT64_FORMAT " frozen tuples, " UINT64_FORMAT " truncated UNDO chains, " UINT64_FORMAT " UNDO versions, " UINT64_FORMAT " deleted versions",
		 RelationGetRelationName(rel), nVisibleForAllTuples, nDeadTuples, nFrozenTuples, nTruncatedUndoChains, nUndoVersions, nDeletedVersions);

	/* TODO: update statistic, relfrozenxid,... */

	free(deadBitmap);
}

static inline TM_Result
undam_tuple_delete(Relation relation, ItemPointer tid, CommandId cid,
				   Snapshot snapshot, Snapshot crosscheck, bool wait,
				   TM_FailureData *tmfd, bool changingPart)
{
	TM_Result	result;
	UndamRelationInfo* relinfo = UndamGetRelationInfo(relation);
	TransactionId xid = GetCurrentTransactionId();
	UndamTupleHeader* tup;
	HeapTupleData tp;
	Page		page;
	BlockNumber block;
	Buffer		buffer;
	TransactionId new_xmax;
	uint16		new_infomask,
				new_infomask2;
	bool		have_tuple_lock = false;
	bool		iscombo;
	GenericXLogState* xlogState;

	Assert(ItemPointerIsValid(tid));

	/*
	 * Forbid this during a parallel operation, lest it allocate a combocid.
	 * Other workers might need that combocid for visibility checks, and we
	 * have no provision for broadcasting it to them.
	 */
	if (IsInParallelMode())
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_TRANSACTION_STATE),
				 errmsg("cannot delete tuples during a parallel operation")));

#if FORCE_TUPLE_LOCK
	heap_acquire_tuplock(relation, tid, LockTupleExclusive,
						 LockWaitBlock, &have_tuple_lock);
#endif

	block = ItemPointerGetBlockNumber(tid);
	buffer = ReadBuffer(relation, block);
	page = BufferGetPage(buffer);

	LockBuffer(buffer, BUFFER_LOCK_EXCLUSIVE);

	tup = (UndamTupleHeader*)((char*)page + ItemPointerGetOffsetNumber(tid)*CHUNK_SIZE);

	tp.t_tableOid = RelationGetRelid(relation);
	tp.t_data = &tup->hdr;
	tp.t_len = tup->size;
	tp.t_self = *tid;

l1:
	result = HeapTupleSatisfiesUpdate(&tp, cid, buffer);

	if (result == TM_Invisible && wait)
	{
		TransactionId xwait;

		/* must copy state data before unlocking buffer */
		xwait = HeapTupleHeaderGetRawXmin(tp.t_data);

		if (!TransactionIdIsCurrentTransactionId(xwait))
		{
			/*
			 * Wait for regular transaction to end; but first, acquire tuple
			 * lock.
			 */
			LockBuffer(buffer, BUFFER_LOCK_UNLOCK);
#if !FORCE_TUPLE_LOCK
			heap_acquire_tuplock(relation, &(tp.t_self), LockTupleExclusive,
								 LockWaitBlock, &have_tuple_lock);
#endif
			XactLockTableWait(xwait, relation, &(tp.t_self), XLTW_Delete);
			LockBuffer(buffer, BUFFER_LOCK_EXCLUSIVE);

			/*
			 * xwait is done, but if xwait had just locked the tuple then some
			 * other xact could update this tuple before we get to this point.
			 * Check for xmax change, and start over if so.
			 */
			if (!TransactionIdEquals(HeapTupleHeaderGetRawXmin(tp.t_data),
									 xwait))
				goto l1;

			/* Otherwise check if it committed or aborted */
			UpdateXminHintBits(tp.t_data, buffer, xwait);
		}

		/*
		 * We may overwrite if previous xmax aborted, or if it committed but
		 * only locked the tuple without updating it.
		 */
		if ((tp.t_data->t_infomask & HEAP_XMAX_INVALID) ||
			HeapTupleHeaderIsOnlyLocked(tp.t_data))
			result = TM_Ok;
		else if (!ItemPointerEquals(&tp.t_self, &tp.t_data->t_ctid) ||
				 HeapTupleHeaderIndicatesMovedPartitions(tp.t_data))
			result = TM_Updated;
		else
			result = TM_Deleted;
	}

	if (crosscheck != InvalidSnapshot && result == TM_Ok)
	{
		/* Perform additional check for transaction-snapshot mode RI updates */
		if (!HeapTupleSatisfiesVisibility(&tp, crosscheck, buffer))
			result = TM_Updated;
	}

	if (result != TM_Ok)
	{
		Assert(result == TM_SelfModified ||
			   result == TM_Updated ||
			   result == TM_Deleted ||
			   result == TM_Invisible);
		Assert(!(tp.t_data->t_infomask & HEAP_XMIN_INVALID));
		Assert(result != TM_Updated ||
			   !ItemPointerEquals(&tp.t_self, &tp.t_data->t_ctid));
		tmfd->ctid = tp.t_data->t_ctid;
		tmfd->xmax = HeapTupleHeaderGetUpdateXid(tp.t_data);
		if (result == TM_SelfModified)
			tmfd->cmax = HeapTupleHeaderGetCmax(tp.t_data);
		else
			tmfd->cmax = InvalidCommandId;
		UnlockReleaseBuffer(buffer);
		if (have_tuple_lock)
			UnlockTupleTuplock(relation, &(tp.t_self), LockTupleExclusive);
		return result;
	}
	/*
	 * We're about to do the actual delete -- check for conflict first, to
	 * avoid possibly having to roll back work we've just done.
	 *
	 * This is safe without a recheck as long as there is no possibility of
	 * another process scanning the page between this check and the delete
	 * being visible to the scan (i.e., an exclusive buffer content lock is
	 * continuously held from this point until the tuple delete is visible).
	 */
#if PG_VERSION_NUM >= 130000
	CheckForSerializableConflictIn(relation, tid, BufferGetBlockNumber(buffer));
#else
	CheckForSerializableConflictIn(relation, &tp, BufferGetBlockNumber(buffer));
#endif

	xlogState = GenericXLogStart(relation);
	page = UndamModifyBuffer(relation, xlogState, buffer);
	tup = (UndamTupleHeader*)((char*)page + ItemPointerGetOffsetNumber(tid)*CHUNK_SIZE);
	tp.t_data = &tup->hdr;

	/* replace cid with a combo cid if necessary */
	HeapTupleHeaderAdjustCmax(tp.t_data, &cid, &iscombo);

	/*
	 * If this is the first possibly-multixact-able operation in the current
	 * transaction, set my per-backend OldestMemberMXactId setting. We can be
	 * certain that the transaction will never become a member of any older
	 * MultiXactIds than that.  (We have to do this even if we end up just
	 * using our own TransactionId below, since some other backend could
	 * incorporate our XID into a MultiXact immediately afterwards.)
	 */
	MultiXactIdSetOldestMember();

	compute_new_xmax_infomask(HeapTupleHeaderGetRawXmax(tp.t_data),
							  tp.t_data->t_infomask, tp.t_data->t_infomask2,
							  xid, LockTupleExclusive, true,
							  &new_xmax, &new_infomask, &new_infomask2);

	START_CRIT_SECTION();

	/*
	 * If this transaction commits, the tuple will become DEAD sooner or
	 * later.  Set flag that this page is a candidate for pruning once our xid
	 * falls below the OldestXmin horizon.  If the transaction finally aborts,
	 * the subsequent page pruning will be a no-op and the hint will be
	 * cleared.
	 */
	PageSetPrunable(page, xid);

	/* store transaction information of xact deleting the tuple */
	tp.t_data->t_infomask &= ~(HEAP_XMAX_BITS | HEAP_MOVED);
	tp.t_data->t_infomask2 &= ~HEAP_KEYS_UPDATED;
	tp.t_data->t_infomask |= new_infomask;
	tp.t_data->t_infomask2 |= new_infomask2;
	HeapTupleHeaderClearHotUpdated(tp.t_data);
	HeapTupleHeaderSetXmax(tp.t_data, new_xmax);
	HeapTupleHeaderSetCmax(tp.t_data, cid, iscombo);
	/* Make sure there is no forward chain link in t_ctid */
	tp.t_data->t_ctid = tp.t_self;

	/* Signal that this is actually a move into another partition */
	if (changingPart)
		HeapTupleHeaderSetMovedPartitions(tp.t_data);

	END_CRIT_SECTION();

	UndamXLogFinish(relation, xlogState);
	UnlockReleaseBuffer(buffer);

	/*
	 * Release the lmgr tuple lock, if we had it.
	 */
	if (have_tuple_lock)
		UnlockTupleTuplock(relation, &(tp.t_self), LockTupleExclusive);

	pgstat_count_heap_delete(relation);

	return TM_Ok;
}

static void
undam_relation_nontransactional_truncate(Relation rel)
{
	ForkNumber	forks[EXT_FORKNUM+1] = {MAIN_FORKNUM, EXT_FORKNUM};
	BlockNumber	blocks[EXT_FORKNUM+1] = {0,0};
	UndamRelationInfo* relinfo;
	int chunkSize = UndamChunkSize;

	LWLockAcquire(UndamRelInfoLock, LW_EXCLUSIVE);

	relinfo = (UndamRelationInfo*)hash_search(UndamRelInfoHash, &RelationGetRelid(rel), HASH_ENTER, NULL);
	if (UndamAutoChunkSize)
	{
		chunkSize = UndamOptimalChunkSize(rel);
		elog(LOG, "Use chunk size %d for relation %s",
			 chunkSize, RelationGetRelationName(rel));
	}
	RelationOpenSmgr(rel);

	/*
	 * Make sure smgr_targblock etc aren't pointing somewhere past new end
	 */
	rel->rd_smgr->smgr_targblock = InvalidBlockNumber;
	rel->rd_smgr->smgr_fsm_nblocks = InvalidBlockNumber;
	rel->rd_smgr->smgr_vm_nblocks = InvalidBlockNumber;

	relinfo->chunkSize = chunkSize;
	relinfo->nChains = UndamNAllocChains;

	if (RelationNeedsWAL(rel))
	{
		/* TODO: we can not use SMGR_TRUNCATE_ALL because of special handling of free space map fork */
	}

    /* Do the real work to truncate relation forks */
#if PG_VERSION_NUM >= 130000
	smgrtruncate(rel->rd_smgr, forks, 2, blocks);
#else
	for (int fork = MAIN_FORKNUM; fork <= EXT_FORKNUM; fork++)
		smgrtruncate(rel->rd_smgr, forks[fork], blocks[fork]);
#endif

	for (int fork = MAIN_FORKNUM; fork <= EXT_FORKNUM; fork++)
	{
		for (int chain = 0; chain < UndamNAllocChains; chain++)
		{
			Buffer buf = UndamReadBuffer(rel, fork, P_NEW);
			UndamPageHeader* pg;
			GenericXLogState* xlogState = GenericXLogStart(rel);

			LockBuffer(buf, BUFFER_LOCK_EXCLUSIVE);
			pg = (UndamPageHeader*)UndamModifyBuffer(rel, xlogState, buf);
			pg->chunkSize = chunkSize;
			pg->nChains = UndamNAllocChains;
			relinfo->chains[chain].forks[fork].head = pg->head = chain;
			relinfo->chains[chain].forks[fork].tail = pg->tail = chain;
			pg->next = InvalidBlockNumber;
			pg->pd_special = pg->pd_lower = pg->pd_upper = sizeof(UndamPageHeader);

			UndamXLogFinish(rel, xlogState);
			UnlockReleaseBuffer(buf);
		}
	}
	LWLockRelease(UndamRelInfoLock);
}

static void
undam_relation_set_new_filenode(Relation rel,
								 const RelFileNode *newrnode,
								 char persistence,
								 TransactionId *freezeXid,
								 MultiXactId *minmulti)
{
	SMgrRelation srel;
	SMgrRelationData* old_smgr;
	/*
	 * Initialize to the minimum XID that could put tuples in the table. We
	 * know that no xacts older than RecentXmin are still running, so that
	 * will do.
	 */
	*freezeXid = RecentXmin;

	/*
	 * Similarly, initialize the minimum Multixact to the first value that
	 * could possibly be stored in tuples in the table.  Running transactions
	 * could reuse values from their local cache, so we are careful to
	 * consider all currently running multis.
	 *
	 * XXX this could be refined further, but is it worth the hassle?
	 */
	*minmulti = GetOldestMultiXactId();

	srel = RelationCreateStorage(*newrnode, persistence);
	smgrcreate(srel, EXT_FORKNUM, false);
	log_smgrcreate(newrnode, EXT_FORKNUM);

	old_smgr = rel->rd_smgr;
	rel->rd_smgr = srel;
	undam_relation_nontransactional_truncate(rel);
	rel->rd_smgr = old_smgr;
	smgrclose(srel);
}

static void
undam_finish_bulk_insert(Relation rel, int options)
{
}

static void
undam_get_latest_tid(TableScanDesc scan,
                    ItemPointer tid)
{
    NOT_IMPLEMENTED;
}

static TransactionId
undam_compute_xid_horizon_for_tuples(Relation rel,
                                    ItemPointerData *items,
                                    int nitems)
{
    NOT_IMPLEMENTED;
}

static void
undam_relation_copy_data(Relation rel, const RelFileNode *newrnode)
{
    NOT_IMPLEMENTED;
}

static void
undam_relation_copy_for_cluster(Relation OldHeap, Relation NewHeap,
								Relation OldIndex, bool use_sort,
								TransactionId OldestXmin,
								TransactionId *xid_cutoff,
								MultiXactId *multi_cutoff,
								double *num_tuples,
								double *tups_vacuumed,
								double *tups_recently_dead)
{
    NOT_IMPLEMENTED;
}

static bool
undam_scan_analyze_next_block(TableScanDesc scan, BlockNumber blockno,
							  BufferAccessStrategy bstrategy)
{
    UndamScanDesc   uscan = (UndamScanDesc) scan;

	if (blockno >= uscan->lastBlock)
		return false;

	ItemPointerSet(&uscan->currItem, blockno, 1);
    return true;
}

static bool
undam_scan_analyze_next_tuple(TableScanDesc scan, TransactionId OldestXmin,
							  double *liverows, double *deadrows,
							  TupleTableSlot *slot)
{
    Relation      rel = scan->rs_rd;
	UndamRelationInfo* relinfo = UndamGetRelationInfo(rel);
    UndamScanDesc uscan = (UndamScanDesc) scan;
	int           item = ItemPointerGetOffsetNumber(&uscan->currItem);
	BlockNumber   blocknum = ItemPointerGetBlockNumber(&uscan->currItem);
	int           nChunks = CHUNKS_PER_BLOCK;
	Buffer        buf = UndamReadBuffer(rel, MAIN_FORKNUM, blocknum);
	UndamPageHeader* pg = (UndamPageHeader*)BufferGetPage(buf);

	LockBuffer(buf, BUFFER_LOCK_SHARE);

	while (item < nChunks)
	{
		if (pg->allocMask[item >> 6] & ((uint64)1 << (item & 63))) /* item was allocated */
		{
			UndamTupleHeader* tup = (UndamTupleHeader*)((char*)pg + item*CHUNK_SIZE);
			HeapTupleData tuphdr;
			int len = tup->size;
			bool sample_it = false;

			tuphdr.t_tableOid = RelationGetRelid(rel);
			tuphdr.t_data = &tup->hdr;
			tuphdr.t_len = len;
			ItemPointerSet(&tuphdr.t_self, blocknum, item);

			switch (HeapTupleSatisfiesVacuum(&tuphdr, OldestXmin, buf))
			{
			case HEAPTUPLE_LIVE:
			    sample_it = true;
				*liverows += 1;
				break;

			case HEAPTUPLE_DEAD:
			case HEAPTUPLE_RECENTLY_DEAD:
				/* Count dead and recently-dead rows */
				*deadrows += 1;
				break;

			case HEAPTUPLE_INSERT_IN_PROGRESS:

				/*
				 * Insert-in-progress rows are not counted.  We assume that
				 * when the inserting transaction commits or aborts, it will
				 * send a stats message to increment the proper count.  This
				 * works right only if that transaction ends after we finish
				 * analyzing the table; if things happen in the other order,
				 * its stats update will be overwritten by ours.  However, the
				 * error will be large only if the other transaction runs long
				 * enough to insert many tuples, so assuming it will finish
				 * after us is the safer option.
				 *
				 * A special case is that the inserting transaction might be
				 * our own.  In this case we should count and sample the row,
				 * to accommodate users who load a table and analyze it in one
				 * transaction.  (pgstat_report_analyze has to adjust the
				 * numbers we send to the stats collector to make this come
				 * out right.)
				 */
				if (TransactionIdIsCurrentTransactionId(HeapTupleHeaderGetXmin(&tup->hdr)))
				{
					sample_it = true;
					*liverows += 1;
				}
				break;

			case HEAPTUPLE_DELETE_IN_PROGRESS:

				/*
				 * We count and sample delete-in-progress rows the same as
				 * live ones, so that the stats counters come out right if the
				 * deleting transaction commits after us, per the same
				 * reasoning given above.
				 *
				 * If the delete was done by our own transaction, however, we
				 * must count the row as dead to make pgstat_report_analyze's
				 * stats adjustments come out right.  (Note: this works out
				 * properly when the row was both inserted and deleted in our
				 * xact.)
				 *
				 * The net effect of these choices is that we act as though an
				 * IN_PROGRESS transaction hasn't happened yet, except if it
				 * is our own transaction, which we assume has happened.
				 *
				 * This approach ensures that we behave sanely if we see both
				 * the pre-image and post-image rows for a row being updated
				 * by a concurrent transaction: we will sample the pre-image
				 * but not the post-image.  We also get sane results if the
				 * concurrent transaction never commits.
				 */
				if (TransactionIdIsCurrentTransactionId(HeapTupleHeaderGetUpdateXid(&tup->hdr)))
					*deadrows += 1;
				else
				{
					sample_it = true;
					*liverows += 1;
				}
				break;

			default:
				elog(ERROR, "UNDAM: unexpected HeapTupleSatisfiesVacuum result");
				break;
			}
			if (sample_it)
			{
				HeapTuple tuple = (HeapTuple)palloc(sizeof(HeapTupleData) + len);
				int available = CHUNK_SIZE - offsetof(UndamTupleHeader, hdr);

				*tuple = tuphdr;
				tuple->t_data = (HeapTupleHeader)(tuple + 1); /* store tuple body just after the header */
				if (len <= available)
				{
					memcpy(tuple->t_data, &tup->hdr, len);
				}
				else
				{
					UndamTupleChunk* chunk;
					char* dst = (char*)tuple->t_data;
					UndamPosition next = tup->nextChunk;

					memcpy(dst, &tup->hdr, available);
					dst += available;
					len -= available;
					available = CHUNK_SIZE - offsetof(UndamTupleChunk, data); /* head chunk contains less data */

					do {
						Assert(next != INVALID_POSITION);
						UnlockReleaseBuffer(buf);
						buf = UndamReadBuffer(rel, EXT_FORKNUM, POSITION_GET_BLOCK_NUMBER(next));
						pg = (UndamPageHeader*)BufferGetPage(buf);
						chunk = (UndamTupleChunk*)((char*)pg + POSITION_GET_BLOCK_OFFSET(next));
						LockBuffer(buf, BUFFER_LOCK_SHARE);
						memcpy(dst, chunk->data, Min(len, available));
						dst += available;
						len -= available;
						next = chunk->next;
					} while (len > 0);
				}
				ExecStoreHeapTuple(tuple, slot, true);
				UnlockReleaseBuffer(buf);
				ItemPointerSetOffsetNumber(&uscan->currItem, item+1);
				return true;
			}
		}
		item += 1;
	}
	UnlockReleaseBuffer(buf);
	return false;
}

static double
undam_index_build_range_scan(Relation rel,
							 Relation indexRelation,
							 IndexInfo *indexInfo,
							 bool allow_sync,
							 bool anyvisible,
							 bool progress,
							 BlockNumber start_blockno,
							 BlockNumber numblocks,
							 IndexBuildCallback callback,
							 void *callback_state,
							 TableScanDesc scan)
{
    Datum		values[INDEX_MAX_KEYS];
    bool        isnull[INDEX_MAX_KEYS];
    double      reltuples;
	ExprState  *predicate;
    TupleTableSlot *slot;
    EState     *estate;
    ExprContext *econtext;
    Snapshot    snapshot;
	TransactionId OldestXmin;
	bool		need_unregister_snapshot = false;

    if (start_blockno != 0 || numblocks != InvalidBlockNumber)
        elog(ERROR, "UNDAM: partial range scan is not supported");

    /*
     * Need an EState for evaluation of index expressions and partial-index
     * predicates.  Also a slot to hold the current tuple.
     */
    estate = CreateExecutorState();
    econtext = GetPerTupleExprContext(estate);
    slot = table_slot_create(rel, NULL);

    /* Arrange for econtext's scan tuple to be the tuple under test */
    econtext->ecxt_scantuple = slot;

    /* Set up execution state for predicate, if any. */
    predicate = ExecPrepareQual(indexInfo->ii_Predicate, estate);

    /*
     * Prepare for scan of the base relation.  In a normal index build, we use
     * SnapshotAny because we must retrieve all tuples and do our own time
     * qual checks (because we have to index RECENTLY_DEAD tuples). In a
     * concurrent build, or during bootstrap, we take a regular MVCC snapshot
     * and index whatever's live according to that.
     */
    OldestXmin = InvalidTransactionId;

    /* okay to ignore lazy VACUUMs here */
    if (!IsBootstrapProcessingMode() && !indexInfo->ii_Concurrent)
        OldestXmin = GetOldestXmin(rel, PROCARRAY_FLAGS_VACUUM);

    if (!scan)
    {
        /*
         * Serial index build.
         *
         * Must begin our own heap scan in this case.  We may also need to
         * register a snapshot whose lifetime is under our direct control.
         */
        if (!TransactionIdIsValid(OldestXmin))
        {
            snapshot = RegisterSnapshot(GetTransactionSnapshot());
            need_unregister_snapshot = true;
        }
        else
            snapshot = SnapshotAny;

        scan = table_beginscan_strat(rel,  /* relation */
                                     snapshot,  /* snapshot */
                                     0, /* number of keys */
                                     NULL,  /* scan key */
                                     true,  /* buffer access strategy OK */
                                     allow_sync);   /* syncscan OK? */
    }
    else
    {
        /*
         * Parallel index build.
         *
         * Parallel case never registers/unregisters own snapshot.  Snapshot
         * is taken from parallel heap scan, and is SnapshotAny or an MVCC
         * snapshot, based on same criteria as serial case.
         */
        Assert(!IsBootstrapProcessingMode());
        Assert(allow_sync);
        snapshot = scan->rs_snapshot;
    }

    /* Publish number of blocks to scan */
    if (progress)
    {
        /* TODO */
    }

    reltuples = 0;

    while (undam_getnextslot(scan, ForwardScanDirection, slot))
    {
        CHECK_FOR_INTERRUPTS();

        /* Report scan progress, if asked to. */
        if (progress)
        {
            /* TODO */
        }

        reltuples += 1;

        MemoryContextReset(econtext->ecxt_per_tuple_memory);

        /*
         * In a partial index, discard tuples that don't satisfy the
         * predicate.
         */
        if (predicate != NULL)
        {
            if (!ExecQual(predicate, econtext))
                continue;
        }

        FormIndexDatum(indexInfo,
                       slot,
                       estate,
                       values,
                       isnull);

        /* Call the AM's callback routine to process the tuple */
#if PG_VERSION_NUM >= 130000
        callback(indexRelation, &slot->tts_tid, values, isnull, true, callback_state);
#else
		{
			bool shouldFree = false;
			HeapTuple tup = ExecFetchSlotHeapTuple(slot, true, &shouldFree);
			callback(indexRelation, tup, values, isnull, true, callback_state);
			if (shouldFree)
				heap_freetuple(tup);
		}
#endif
    }

    if (progress)
    {
        /* TODO */
    }
	table_endscan(scan);

	/* we can now forget our snapshot, if set and registered by us */
	if (need_unregister_snapshot)
		UnregisterSnapshot(snapshot);

	ExecDropSingleTupleTableSlot(slot);

	FreeExecutorState(estate);

	/* These may have been pointing to the now-gone estate */
	indexInfo->ii_ExpressionsState = NIL;
	indexInfo->ii_PredicateState = NULL;

	return reltuples;
}

static void
undam_index_validate_scan(Relation relation,
                         Relation indexRelation,
                         IndexInfo *indexInfo,
                         Snapshot snapshot,
                         ValidateIndexState *state)
{
    NOT_IMPLEMENTED;
}

static bool
undam_scan_sample_next_block(TableScanDesc scan, SampleScanState *scanstate)
{
    UndamScanDesc uscan = (UndamScanDesc) scan;
	TsmRoutine *tsm = scanstate->tsmroutine;
	BlockNumber blockno;

	/* return false immediately if relation is empty */
	if (tsm->NextSampleBlock)
	{
		blockno = tsm->NextSampleBlock(scanstate, uscan->lastBlock);
	}
	else
	{
		/* scanning table sequentially */
		blockno = ItemPointerGetBlockNumberNoCheck(&uscan->currItem);
		if (ItemPointerGetOffsetNumberNoCheck(&uscan->currItem) != 0)
		{
			blockno += 1;
		}
		if (blockno >= uscan->lastBlock)
			return false;
	}
	ItemPointerSet(&uscan->currItem, blockno, 1);
	return true;
}

static bool
undam_scan_sample_next_tuple(TableScanDesc scan, SampleScanState *scanstate,
                              TupleTableSlot *slot)
{
    Relation      rel = scan->rs_rd;
	TsmRoutine   *tsm = scanstate->tsmroutine;
	UndamRelationInfo *relinfo = UndamGetRelationInfo(rel);
    UndamScanDesc uscan = (UndamScanDesc) scan;
	BlockNumber   blocknum = ItemPointerGetBlockNumber(&uscan->currItem);
	int           nChunks = CHUNKS_PER_BLOCK;
	Buffer        buf = UndamReadBuffer(rel, MAIN_FORKNUM, blocknum);
	UndamPageHeader* pg = (UndamPageHeader*)BufferGetPage(buf);

	LockBuffer(buf, BUFFER_LOCK_SHARE);

	for (;;)
	{
		int item;

		CHECK_FOR_INTERRUPTS();

		/* Ask the tablesample method which tuples to check on this page. */
		item = tsm->NextSampleTuple(scanstate,
									blocknum,
									nChunks);
		if (pg->allocMask[item >> 6] & ((uint64)1 << (item & 63))) /* item was allocated */
		{
			UndamTupleHeader* tup = (UndamTupleHeader*)((char*)pg + item*CHUNK_SIZE);
			HeapTupleData tuphdr;
			int len = tup->size;
			bool visible;

			tuphdr.t_tableOid = RelationGetRelid(rel);
			tuphdr.t_data = &tup->hdr;
			tuphdr.t_len = len;
			ItemPointerSet(&tuphdr.t_self, blocknum, item);

			visible = HeapTupleSatisfiesVisibility(&tuphdr, scan->rs_snapshot, buf);

			/* in pagemode, heapgetpage did this for us */
#if PG_VERSION_NUM >= 130000
			HeapCheckForSerializableConflictOut(visible, scan->rs_rd, &tuphdr,
												buf, scan->rs_snapshot);
#else
			CheckForSerializableConflictOut(scan->rs_rd, GetTopTransactionIdIfAny(), scan->rs_snapshot);
#endif

			/* Try next tuple from same page. */
			if (!visible)
				continue;

			/* Found visible tuple, return it. */
			UnlockReleaseBuffer(buf);

			ExecStoreHeapTuple(&tuphdr, slot, true);

			/* Count successfully-fetched tuples as heap fetches */
			pgstat_count_heap_getnext(scan->rs_rd);

			return true;
		}
		else
		{
			/*
			 * If we get here, it means we've exhausted the items on this page
			 * and it's time to move to the next.
			 */
			UnlockReleaseBuffer(buf);

			ExecClearTuple(slot);
			return false;
		}
	}
}

/*
 * Defenition of Undam table access method.
 */
static const TableAmRoutine undam_methods =
{
    .type = T_TableAmRoutine,

    .slot_callbacks = undam_slot_callbacks,

    .scan_begin = undam_beginscan,
    .scan_getnextslot = undam_getnextslot,
    .scan_rescan = undam_rescan,
    .scan_end = undam_endscan,

    .parallelscan_estimate = table_block_parallelscan_estimate,
    .parallelscan_initialize = table_block_parallelscan_initialize,
    .parallelscan_reinitialize = table_block_parallelscan_reinitialize,

    .index_fetch_begin = undam_index_fetch_begin,
    .index_fetch_reset = undam_index_fetch_reset,
    .index_fetch_end = undam_index_fetch_end,
    .index_fetch_tuple = undam_index_fetch_tuple,

    .tuple_insert = undam_tuple_insert,
    .finish_bulk_insert = undam_finish_bulk_insert,
    .tuple_insert_speculative = undam_tuple_insert_speculative,
    .tuple_complete_speculative = undam_tuple_complete_speculative,
    .multi_insert = undam_multi_insert,
    .tuple_delete = undam_tuple_delete,
    .tuple_update = undam_tuple_update,
    .tuple_lock = undam_tuple_lock,

    .tuple_fetch_row_version = undam_fetch_row_version,
    .tuple_tid_valid = undam_tuple_tid_valid,
    .tuple_get_latest_tid = undam_get_latest_tid,
    .tuple_satisfies_snapshot = undam_tuple_satisfies_snapshot,
	.compute_xid_horizon_for_tuples = undam_compute_xid_horizon_for_tuples,

    .relation_set_new_filenode = undam_relation_set_new_filenode,
    .relation_nontransactional_truncate = undam_relation_nontransactional_truncate,
    .relation_copy_data = undam_relation_copy_data,
    .relation_copy_for_cluster = undam_relation_copy_for_cluster,
    .relation_vacuum = undam_relation_vacuum,
    .scan_analyze_next_block = undam_scan_analyze_next_block,
    .scan_analyze_next_tuple = undam_scan_analyze_next_tuple,
    .index_build_range_scan = undam_index_build_range_scan,
    .index_validate_scan = undam_index_validate_scan,

    .relation_size = undam_relation_size,
    .relation_needs_toast_table = undam_relation_needs_toast_table,

    .relation_estimate_size =undam_relation_estimate_size,

    .scan_sample_next_block = undam_scan_sample_next_block,
    .scan_sample_next_tuple = undam_scan_sample_next_tuple,

    .scan_bitmap_next_block = undam_scan_bitmap_next_block,
    .scan_bitmap_next_tuple = undam_scan_bitmap_next_tuple
};

Datum
undam_tableam_handler(PG_FUNCTION_ARGS)
{
    PG_RETURN_POINTER(&undam_methods);
}


/*
 * Module load callback
 */
void _PG_init(void)
{
	/*
	 * In order to create our shared memory area, we have to be loaded via
	 * shared_preload_libraries.  If not, fall out without hooking into any of
	 * the main system.  (We don't throw error here because it seems useful to
	 * allow the undam functions to be created even when the
	 * module isn't active.  The functions must protect themselves against
	 * being called then, however.)
	 */
	if (!process_shared_preload_libraries_in_progress)
		return;

	UndamReloptKind = add_reloption_kind();
#if PG_VERSION_NUM >= 130000
	add_int_reloption(UndamReloptKind, "chunk", "Size of allocation chunk", 64, MIN_CHUNK_SIZE, MAX_CHUNK_SIZE, AccessExclusiveLock);
	add_int_reloption(UndamReloptKind, "chains", "Number of allocation chains", 8, 1, MAX_ALLOC_CHAINS, AccessExclusiveLock);
#else
	add_int_reloption(UndamReloptKind, "chunk", "Size of allocation chunk", 64, MIN_CHUNK_SIZE, MAX_CHUNK_SIZE);
	add_int_reloption(UndamReloptKind, "chains", "Number of allocation chains", 8, 1, MAX_ALLOC_CHAINS);
#endif
	DefineCustomBoolVariable("undam.auto_chunk_size",
							 "Automatical choose chunk size for relation with fixed size attributes.",
							 NULL,
							 &UndamAutoChunkSize,
							 false,
							 PGC_USERSET,
							 0,
							 NULL,
							 NULL,
							 NULL);
	DefineCustomIntVariable("undam.chunk_size",
							"Size of allocation chunk.",
							NULL,
							&UndamChunkSize,
							64,
							MIN_CHUNK_SIZE,
							MAX_CHUNK_SIZE,
							PGC_USERSET,
							0,
							NULL,
							NULL,
							NULL);
	DefineCustomIntVariable("undam.alloc_chains",
							"Number of allocation chains.",
							NULL,
							&UndamNAllocChains,
							8,
							1,
							MAX_ALLOC_CHAINS,
							PGC_USERSET,
							0,
							NULL,
							NULL,
							NULL);

	DefineCustomIntVariable("undam.max_relations",
                            "Maximal number of UNDAM relations.",
							NULL,
							&UndamMaxRelations,
							1024,
							1,
							INT_MAX,
							PGC_POSTMASTER,
							0,
							NULL,
							NULL,
							NULL);

	RequestAddinShmemSpace(hash_estimate_size(UndamMaxRelations, sizeof(UndamRelationInfo)));
	RequestNamedLWLockTranche("undam", 1);
	prev_shmem_startup_hook = shmem_startup_hook;
	shmem_startup_hook = UndamShmemStartup;
}

#define UNDAM_REL_INFO_COLS 3

Datum
undam_rel_info(PG_FUNCTION_ARGS)
{
	TupleDesc	tupdesc;
	Datum		values[UNDAM_REL_INFO_COLS];
	bool		nulls[UNDAM_REL_INFO_COLS];
	Oid         relid = PG_GETARG_OID(0);
	UndamRelationInfo* relinfo;

	if (get_call_result_type(fcinfo, NULL, &tupdesc) != TYPEFUNC_COMPOSITE)
		elog(ERROR, "return type must be a row type");


	LWLockAcquire(UndamRelInfoLock, LW_SHARED);
	relinfo = (UndamRelationInfo*)hash_search(UndamRelInfoHash, &relid, HASH_FIND, NULL);	
	LWLockRelease(UndamRelInfoLock);

	if (relinfo)
	{
		MemSet(nulls, false, sizeof(nulls));
		values[0] = relinfo->nScannedTuples;
		values[1] = relinfo->nScannedVersions;
		values[2] = relinfo->nScannedChunks;
	}
	else
	{
		MemSet(nulls, true, sizeof(nulls));
	}
	PG_RETURN_DATUM(HeapTupleGetDatum(heap_form_tuple(tupdesc, values, nulls)));
}
