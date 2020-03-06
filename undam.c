#include "postgres.h"

#include "access/genam.h"
#include "access/generic_xlog.h"
#include "access/heapam.h"
#include "access/multixact.h"
#include "access/reloptions.h"
#include "access/relscan.h"
#include "access/skey.h"
#include "access/tableam.h"
#include "access/visibilitymap.h"
#include "access/xact.h"
#include "catalog/index.h"
#include "catalog/storage.h"
#include "catalog/storage_xlog.h"
#include "commands/vacuum.h"
#include "executor/executor.h"
#include "executor/tuptable.h"
#include "miscadmin.h"
#include "nodes/execnodes.h"
#include "storage/bufmgr.h"
#include "storage/checksum.h"
#include "storage/ipc.h"
#include "storage/lmgr.h"
#include "storage/predicate.h"
#include "storage/procarray.h"
#include "storage/smgr.h"
#include "utils/datum.h"
#include "utils/inval.h"
#include "utils/relcache.h"
#include "utils/snapmgr.h"
#include "pgstat.h"

#include "undam.h"

PG_MODULE_MAGIC;

PG_FUNCTION_INFO_V1(undam_tableam_handler);
void		_PG_init(void);

#define NOT_IMPLEMENTED							\
    do { \
        elog(ERROR, "function \"%s\" is not implemented", __func__); \
    } while (0)

static int    UndamChunkSize;
static int    UndamNAllocChains;
static int    UndamMaxRelations;
static HTAB*  UndamAllocChainsHash;
static relopt_kind UndamReloptKind;

static shmem_startup_hook_type prev_shmem_startup_hook = NULL;


/********************************************************************
 * Main Undam functions
 ********************************************************************/

/*
 * Locate allocation chain for the relation and initialize first UndamNAllocChains blocks of relation of not initialized yet.
 */
static UndamAllocChain*
UndamGetAllocChain(Relation rel)
{
	bool found;
	UndamAllocHashEntry* entry = (UndamAllocHashEntry*)hash_search(UndamAllocChainsHash, &RelationGetRelid(rel), HASH_ENTER, &found);
	if (!found)
	{
		for (int chain = 0; chain < UndamNAllocChains; chain++)
		{
			for (int fork = MAIN_FORKNUM; fork <= EXT_FORKNUM; fork++)
			{
				Buffer buf = ReadBufferExtended(rel, fork, chain, RBM_ZERO_ON_ERROR, NULL);
				UndamPageHeader* pg = (UndamPageHeader*)BufferGetPage(buf);

				LockBuffer(buf, BUFFER_LOCK_EXCLUSIVE);

				if (PageIsNew(pg))
				{
					GenericXLogState* xlogState = GenericXLogStart(rel);
					pg = (UndamPageHeader*)GenericXLogRegisterBuffer(xlogState, buf, 0);
					entry->chains[chain].forks[fork].head = pg->head = chain;
					entry->chains[chain].forks[fork].tail = pg->tail = chain + UndamNAllocChains*BLCKSZ;
					pg->next = InvalidBlockNumber;
					pg->pd_special = pg->pd_lower = pg->pd_upper = sizeof(UndamPageHeader);
					pg->chunk_size = UndamChunkSize;
					pg->n_chains = UndamNAllocChains;
					GenericXLogFinish(xlogState);
				}
				else
				{
					if (pg->chunk_size != UndamChunkSize || pg->n_chains != UndamNAllocChains)
						elog(ERROR, "Allocation parameters for UNDO storage can not be changed without removing data of existed tables");

					entry->chains[chain].forks[fork].head = pg->head;
					entry->chains[chain].forks[fork].tail = pg->tail;
				}
				UnlockReleaseBuffer(buf);
			}
		}
	}
	return entry->chains;
}

/*
 * Calculate last block number.
 * Please notice that there may be empty blocks in the middle.
 */
static BlockNumber
UndamGetLastBlock(Relation rel, int fork)
{
	BlockNumber last = 0;
	UndamAllocChain* chains = UndamGetAllocChain(rel);
	for (int chain = 0; chain < UndamNAllocChains; chain++)
	{
		last = Max(last, chains[chain].forks[fork].tail);
	}
	return last;
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
	info.entrysize = sizeof(Oid) + sizeof(UndamAllocChain)*UndamNAllocChains;
	UndamAllocChainsHash =  ShmemInitHash("undam hash",
										  UndamMaxRelations, UndamMaxRelations,
										  &info,
										  HASH_ELEM | HASH_BLOBS);
}

/*
 * Save chain of chunks representing tuple to the database.
 * For object consisting of more than one chunk tail is always written after head so that we always observer consistent chain.
 * Returns position of first chunk in the chain.
 */
static UndamPosition
UndamWriteData(Relation rel, int forknum, char* data, size_t size, UndamPosition undoPos, bool isHeader, UndamPosition tailChunk)
{
	/* We use UndamTupleChunk for estimating of size of data stored in tuple, because head chunk is always written separately */
	int chunkDataSize = UndamChunkSize - offsetof(UndamTupleChunk, data);
	int nChunks = (size + chunkDataSize - 1) / chunkDataSize;
	UndamAllocChain* chains = UndamGetAllocChain(rel);
	int available = size - (nChunks-1) * chunkDataSize;
 	do
	{
		int chainNo = random() % UndamNAllocChains; /* choose random chain to minimize probability of allocation chain buffer lock conflcits */
		BlockNumber blocknum = chains[chainNo].forks[forknum].head;
		Buffer buf = ReadBufferExtended(rel, forknum, blocknum, RBM_ZERO_ON_ERROR, NULL);
		GenericXLogState* xlogState = GenericXLogStart(rel);
		UndamPageHeader* pg;
		int item = CHUNKS_PER_BLOCK; /* We need to link chaunks in L1 list so we have to write them in reverse order */
		Buffer chainBuf = InvalidBuffer;

		LockBuffer(buf, BUFFER_LOCK_EXCLUSIVE);
		pg = (UndamPageHeader*)GenericXLogRegisterBuffer(xlogState, buf, 0);

		if (PageIsNew(pg)) /* Lazy initialization of the page */
		{
			Assert(blocknum >= UndamNAllocChains); /* Root pages shoudl already be initialized */
			pg->pd_special = pg->pd_lower = pg->pd_upper = sizeof(UndamPageHeader);
			pg->head = pg->tail = InvalidBlockNumber;
			pg->next = InvalidBlockNumber;
		}

		/* Use free chunks in this block */
		do
		{
			/* Search for free chunk */
			do
			{
				item -= 1;
			}
			while (pg->alloc_mask[item >> 6] & ((uint64)1 << (item & 63)));  /* first chunk is not allocated, so use it as barrier */

			if (item != 0)  /* has some free space */
			{
				if (isHeader)
				{
					UndamTupleHeader* tup = (UndamTupleHeader*)((char*)pg + item*UndamChunkSize);
					memcpy(&tup->hdr, data, size);
					tup->undo_chain = undoPos;
					tup->next_chunk = tailChunk;
					Assert(nChunks == 1);
				}
				else
				{
					UndamTupleChunk* chunk = (UndamTupleChunk*)((char*)pg + item*UndamChunkSize);
					memcpy(chunk->data, data + (nChunks-1)*chunkDataSize, available);
					chunk->next = tailChunk;
					available = chunkDataSize;
				}
				tailChunk = blocknum;
				pg->alloc_mask[item >> 6] |= (uint64)1 << (item & 63);
				nChunks -= 1;
			}
			else
				break;
		} while (nChunks != 0);

		if (item == 0) /* no free space on the page: exclude it from allocation chain */
		{
			BlockNumber nextFree = pg->next;

			pg->pd_flags |= PD_PAGE_FULL;
			GenericXLogFinish(xlogState);
			UnlockReleaseBuffer(buf);

			if (chainNo != blocknum)
			{
				/* Locate block with chain header */
				chainBuf = ReadBufferExtended(rel, forknum, BLCKSZ*chainNo, RBM_NORMAL, NULL);
				LockBuffer(chainBuf, BUFFER_LOCK_EXCLUSIVE);
				pg = (UndamPageHeader*)GenericXLogRegisterBuffer(xlogState, chainBuf, 0);
			}

			if (pg->head == blocknum) /* Alloc chain was not already updated by some other backend */
			{
				if (nextFree == InvalidBlockNumber) /* No more free block in chain: use last one */
				{
					nextFree = chains[chainNo].forks[forknum].tail;
					pg->tail = chains[chainNo].forks[forknum].tail += UndamNAllocChains*BLCKSZ;
				}
				chains[chainNo].forks[forknum].head = pg->head = nextFree;
			}
			item = CHUNKS_PER_BLOCK;
		}
		GenericXLogFinish(xlogState);
		UnlockReleaseBuffer(buf);
		if (chainBuf)
			UnlockReleaseBuffer(buf);
	}
	while (nChunks != 0);

	return tailChunk;
}


/*
 * Insert new tuple in the table.
 */
static void
UndamInsertTuple(Relation rel, int forknum, HeapTuple tuple)
{
	int available = UndamChunkSize - offsetof(UndamTupleHeader, hdr);
	UndamPosition pos;

	if (tuple->t_len <= available) /* Fit in one chunk */
	{
		pos = UndamWriteData(rel, forknum, (char*)tuple->t_data, tuple->t_len, INVALID_POSITION, true, INVALID_POSITION);
	}
	else /* Tuple doesn't fit in chunk */
	{
		/* First write tail... */
		pos = UndamWriteData(rel, EXT_FORKNUM, (char*)tuple->t_data + available, tuple->t_len - available, INVALID_POSITION, false, INVALID_POSITION);
		/* ... and then head */
		pos = UndamWriteData(rel, forknum, (char*)tuple->t_data, available, INVALID_POSITION, true, pos);
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
	int offs = tuple->t_self.ip_posid*UndamChunkSize;
	int available = UndamChunkSize - offsetof(UndamTupleHeader, hdr);
	GenericXLogState* xlogState = GenericXLogStart(rel);
	UndamPageHeader* pg = (UndamPageHeader*)GenericXLogRegisterBuffer(xlogState, buffer, 0);
	UndamTupleHeader* old = (UndamTupleHeader*)((char*)pg + offs);
	int len = Min(HeapTupleHeaderGetDatumLength(&old->hdr), available);

	/* Create copy of head chunk */
	old->undo_chain = UndamWriteData(rel, EXT_FORKNUM, (char*)old, len, old->undo_chain, true, old->next_chunk);

	len = Min(tuple->t_len, available);
	memcpy(&old->hdr, tuple->t_data, len); /* in-place update of head chunk */
	if (tuple->t_len > available)
	{
		/* Write tail chunks. As far as we are writing them in another fork, there can not be deadlock caused by buffer lock conflict */
		old->next_chunk = UndamWriteData(rel, EXT_FORKNUM, (char*)tuple->t_data + len, tuple->t_len - len, INVALID_POSITION, false, INVALID_POSITION);
	}
	GenericXLogFinish(xlogState);
	UnlockReleaseBuffer(buffer);
}

/*
 * Read tuple visible in specified snapshot.
 * This function traverse undo chain and use stadnard visibility function to determine proper tuple.
 * Once such tuple is located all its chaunks are fetched.
 * Returns NULL is no visible tuple is found.
 * Otherwise returns unatatched heap tuple (not pinning any buffer).
 */
static HeapTuple
UndamReadTuple(Relation rel, Snapshot snapshot, ItemPointer ip)
{
	BlockNumber blocknum = BlockIdGetBlockNumber(&ip->ip_blkid);
	int offs = ip->ip_posid*UndamChunkSize;
	int forknum = MAIN_FORKNUM; /* Start from main fork */
	HeapTupleData tuphdr;

	tuphdr.t_tableOid = RelationGetRelid(rel);
	tuphdr.t_self = *ip;

	do
	{
		Buffer buf = ReadBufferExtended(rel, forknum, blocknum, RBM_NORMAL, NULL); /* Page is expected to be already initialized */
		UndamPageHeader* pg = (UndamPageHeader*)BufferGetPage(buf);
		UndamTupleHeader* tup = (UndamTupleHeader*)((char*)pg + offs);
		int len;

		LockBuffer(buf, BUFFER_LOCK_SHARE);

		len = HeapTupleHeaderGetDatumLength(&tup->hdr);
		tuphdr.t_data = &tup->hdr;
		tuphdr.t_len = len;

		if (HeapTupleSatisfiesVisibility(&tuphdr, snapshot, buf))
		{
			HeapTuple tuple = (HeapTuple)palloc(sizeof(HeapTupleData) + len);
			int available = UndamChunkSize - offsetof(UndamTupleHeader, hdr);

			*tuple = tuphdr;
			tuple->t_data = (HeapTupleHeader)(tuple + 1); /* store tuple's body just after the header */
			if (len <= available)
			{
				memcpy(tuple->t_data, &tup->hdr, len); /* tuple fits in one chunk */
			}
			else
			{
				char* dst = (char*)tuple->t_data;
				UndamPosition next = tup->next_chunk;

				memcpy(dst, &tup->hdr, available);
				dst += available;
				len -= available;
				available = UndamChunkSize - offsetof(UndamTupleChunk, data);

				/* Copy rest of chunks */
				do {
					UndamTupleChunk* chunk;
					UnlockReleaseBuffer(buf);
					buf = ReadBufferExtended(rel, EXT_FORKNUM, POSITION_GET_BLOCK_NUMBER(next), RBM_NORMAL, NULL);
					pg = (UndamPageHeader*)BufferGetPage(buf);
					chunk = (UndamTupleChunk*)((char*)pg + POSITION_GET_BLOCK_OFFSET(next));
					memcpy(dst, chunk->data, Min(len, available));
					dst += available;
					len -= available;
				} while (len > 0);
			}
			UnlockReleaseBuffer(buf);
			return tuple;
		}
		blocknum = POSITION_GET_BLOCK_NUMBER(tup->undo_chain);
		offs = POSITION_GET_BLOCK_OFFSET(tup->undo_chain);
		UnlockReleaseBuffer(buf);
		forknum = EXT_FORKNUM; /* undo chain is in extension fork */
	}
	while (blocknum != InvalidBlockNumber);

	return NULL;
}


/*
 * Delete unused version of the tuple from extension fork.
 */
static void
UndamDeleteTuple(Relation rel, UndamPosition pos)
{
	BlockNumber blocknum = POSITION_GET_BLOCK_NUMBER(pos);
	int item = POSITION_GET_ITEM(pos);
	GenericXLogState* xlogState = GenericXLogStart(rel);
	UndamPosition next, undo = 0; /* Zero undo position means that we are proceessing head chunk */
	UndamAllocChain* chains = UndamGetAllocChain(rel);

	while (true)
	{
		Buffer buf = ReadBufferExtended(rel, EXT_FORKNUM, blocknum, RBM_NORMAL, NULL);
		UndamPageHeader* pg = (UndamPageHeader*)GenericXLogRegisterBuffer(xlogState, buf, 0);
		Buffer chainBuf = InvalidBuffer;
		LockBuffer(buf, BUFFER_LOCK_EXCLUSIVE);

		Assert(pg->alloc_mask[item >> 6] & ((uint64)1 << (item & 63)));
		pg->alloc_mask[item >> 6] &= ~((uint64)1 << (item & 63));

		if (undo) /* not first chunk */
		{
			UndamTupleChunk* chunk = (UndamTupleChunk*)((char*)pg + item*UndamChunkSize);
			next = chunk->next;
		}
		else
		{
			UndamTupleHeader* hdr = (UndamTupleHeader*)((char*)pg + item*UndamChunkSize);
			undo = hdr->undo_chain;
			next = hdr->next_chunk;
		}
		if (pg->pd_flags & PD_PAGE_FULL) /* page was full: include it in allocation chain  */
		{
			int chainNo = blocknum % UndamNAllocChains;
			UndamPageHeader* chain;

			pg->pd_flags &= ~PD_PAGE_FULL;

			if (chainNo != blocknum) /* check if allocation chain header is at the same page */
			{
				chainBuf = ReadBufferExtended(rel, EXT_FORKNUM, chainNo*BLCKSZ, RBM_NORMAL, NULL);
				LockBuffer(chainBuf, BUFFER_LOCK_EXCLUSIVE);
				chain = (UndamPageHeader*)GenericXLogRegisterBuffer(xlogState, chainBuf, 0);
				Assert(chain->head == chains[chainNo].forks[EXT_FORKNUM].head);
			}
			else
			{
				chain = pg;
				chainBuf = InvalidBuffer;
			}
			/* Update chain header */
			pg->next = chain->head;
			chain->head = blocknum;
			chains[chainNo].forks[EXT_FORKNUM].head = blocknum;
		}
		GenericXLogFinish(xlogState);
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
		elog(ERROR, "invalid lock tuple mode %d/%s", mode,
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
					elog(ERROR, "invalid lock mode");
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
 * Does the given multixact conflict with the current transaction grabbing a
 * tuple lock of the given strength?
 *
 * The passed infomask pairs up with the given multixact in the tuple header.
 *
 * If current_is_member is not NULL, it is set to 'true' if the current
 * transaction is a member of the given multixact.
 */
static bool
DoesMultiXactIdConflict(MultiXactId multi, uint16 infomask,
						LockTupleMode lockmode, bool *current_is_member)
{
	int			nmembers;
	MultiXactMember *members;
	bool		result = false;
	LOCKMODE	wanted = tupleLockExtraInfo[lockmode].hwlock;

	if (HEAP_LOCKED_UPGRADED(infomask))
		return false;

	nmembers = GetMultiXactIdMembers(multi, &members, false,
									 HEAP_XMAX_IS_LOCKED_ONLY(infomask));
	if (nmembers >= 0)
	{
		int			i;

		for (i = 0; i < nmembers; i++)
		{
			TransactionId memxid;
			LOCKMODE	memlockmode;

			if (result && (current_is_member == NULL || *current_is_member))
				break;

			memlockmode = LOCKMODE_from_mxstatus(members[i].status);

			/* ignore members from current xact (but track their presence) */
			memxid = members[i].xid;
			if (TransactionIdIsCurrentTransactionId(memxid))
			{
				if (current_is_member != NULL)
					*current_is_member = true;
				continue;
			}
			else if (result)
				continue;

			/* ignore members that don't conflict with the lock we want */
			if (!DoLockModesConflict(memlockmode, wanted))
				continue;

			if (ISUPDATE_from_mxstatus(members[i].status))
			{
				/* ignore aborted updaters */
				if (TransactionIdDidAbort(memxid))
					continue;
			}
			else
			{
				/* ignore lockers-only that are no longer in progress */
				if (!TransactionIdIsInProgress(memxid))
					continue;
			}

			/*
			 * Whatever remains are either live lockers that conflict with our
			 * wanted lock, and updaters that are not aborted.  Those conflict
			 * with what we want.  Set up to return true, but keep going to
			 * look for the current transaction among the multixact members,
			 * if needed.
			 */
			result = true;
		}
		pfree(members);
	}

	return result;
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

/*
 * Do_MultiXactIdWait
 *		Actual implementation for the two functions below.
 *
 * 'multi', 'status' and 'infomask' indicate what to sleep on (the status is
 * needed to ensure we only sleep on conflicting members, and the infomask is
 * used to optimize multixact access in case it's a lock-only multi); 'nowait'
 * indicates whether to use conditional lock acquisition, to allow callers to
 * fail if lock is unavailable.  'rel', 'ctid' and 'oper' are used to set up
 * context information for error messages.  'remaining', if not NULL, receives
 * the number of members that are still running, including any (non-aborted)
 * subtransactions of our own transaction.
 *
 * We do this by sleeping on each member using XactLockTableWait.  Any
 * members that belong to the current backend are *not* waited for, however;
 * this would not merely be useless but would lead to Assert failure inside
 * XactLockTableWait.  By the time this returns, it is certain that all
 * transactions *of other backends* that were members of the MultiXactId
 * that conflict with the requested status are dead (and no new ones can have
 * been added, since it is not legal to add members to an existing
 * MultiXactId).
 *
 * But by the time we finish sleeping, someone else may have changed the Xmax
 * of the containing tuple, so the caller needs to iterate on us somehow.
 *
 * Note that in case we return false, the number of remaining members is
 * not to be trusted.
 */
static bool
Do_MultiXactIdWait(MultiXactId multi, MultiXactStatus status,
				   uint16 infomask, bool nowait,
				   Relation rel, ItemPointer ctid, XLTW_Oper oper,
				   int *remaining)
{
	bool		result = true;
	MultiXactMember *members;
	int			nmembers;
	int			remain = 0;

	/* for pre-pg_upgrade tuples, no need to sleep at all */
	nmembers = HEAP_LOCKED_UPGRADED(infomask) ? -1 :
		GetMultiXactIdMembers(multi, &members, false,
							  HEAP_XMAX_IS_LOCKED_ONLY(infomask));

	if (nmembers >= 0)
	{
		int			i;

		for (i = 0; i < nmembers; i++)
		{
			TransactionId memxid = members[i].xid;
			MultiXactStatus memstatus = members[i].status;

			if (TransactionIdIsCurrentTransactionId(memxid))
			{
				remain++;
				continue;
			}

			if (!DoLockModesConflict(LOCKMODE_from_mxstatus(memstatus),
									 LOCKMODE_from_mxstatus(status)))
			{
				if (remaining && TransactionIdIsInProgress(memxid))
					remain++;
				continue;
			}

			/*
			 * This member conflicts with our multi, so we have to sleep (or
			 * return failure, if asked to avoid waiting.)
			 *
			 * Note that we don't set up an error context callback ourselves,
			 * but instead we pass the info down to XactLockTableWait.  This
			 * might seem a bit wasteful because the context is set up and
			 * tore down for each member of the multixact, but in reality it
			 * should be barely noticeable, and it avoids duplicate code.
			 */
			if (nowait)
			{
				result = ConditionalXactLockTableWait(memxid);
				if (!result)
					break;
			}
			else
				XactLockTableWait(memxid, rel, ctid, oper);
		}

		pfree(members);
	}

	if (remaining)
		*remaining = remain;

	return result;
}

/*
 * MultiXactIdWait
 *		Sleep on a MultiXactId.
 *
 * By the time we finish sleeping, someone else may have changed the Xmax
 * of the containing tuple, so the caller needs to iterate on us somehow.
 *
 * We return (in *remaining, if not NULL) the number of members that are still
 * running, including any (non-aborted) subtransactions of our own transaction.
 */
static void
MultiXactIdWait(MultiXactId multi, MultiXactStatus status, uint16 infomask,
				Relation rel, ItemPointer ctid, XLTW_Oper oper,
				int *remaining)
{
	(void) Do_MultiXactIdWait(multi, status, infomask, false,
							  rel, ctid, oper, remaining);
}

/*
 * Given two versions of the same t_infomask for a tuple, compare them and
 * return whether the relevant status for a tuple Xmax has changed.  This is
 * used after a buffer lock has been released and reacquired: we want to ensure
 * that the tuple state continues to be the same it was when we previously
 * examined it.
 *
 * Note the Xmax field itself must be compared separately.
 */
static inline bool
xmax_infomask_changed(uint16 new_infomask, uint16 old_infomask)
{
	const uint16 interesting =
	HEAP_XMAX_IS_MULTI | HEAP_XMAX_LOCK_ONLY | HEAP_LOCK_MASK;

	if ((new_infomask & interesting) != (old_infomask & interesting))
		return true;

	return false;
}

/*
 * UpdateXmaxHintBits - update tuple hint bits after xmax transaction ends
 *
 * This is called after we have waited for the XMAX transaction to terminate.
 * If the transaction aborted, we guarantee the XMAX_INVALID hint bit will
 * be set on exit.  If the transaction committed, we set the XMAX_COMMITTED
 * hint bit if possible --- but beware that that may not yet be possible,
 * if the transaction committed asynchronously.
 *
 * Note that if the transaction was a locker only, we set HEAP_XMAX_INVALID
 * even if it commits.
 *
 * Hence callers should look only at XMAX_INVALID.
 *
 * Note this is not allowed for tuples whose xmax is a multixact.
 */
static void
UpdateXmaxHintBits(HeapTupleHeader tuple, Buffer buffer, TransactionId xid)
{
	Assert(TransactionIdEquals(HeapTupleHeaderGetRawXmax(tuple), xid));
	Assert(!(tuple->t_infomask & HEAP_XMAX_IS_MULTI));

	if (!(tuple->t_infomask & (HEAP_XMAX_COMMITTED | HEAP_XMAX_INVALID)))
	{
		if (!HEAP_XMAX_IS_LOCKED_ONLY(tuple->t_infomask) &&
			TransactionIdDidCommit(xid))
			HeapTupleSetHintBits(tuple, buffer, HEAP_XMAX_COMMITTED,
								 xid);
		else
			HeapTupleSetHintBits(tuple, buffer, HEAP_XMAX_INVALID,
								 InvalidTransactionId);
	}
}

/********************************************************************
 * Table AM implementations
 ********************************************************************/

static const TupleTableSlotOps *
undam_slot_callbacks(Relation relation)
{
    return &TTSOpsHeapTuple;
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
	scan->last_block = UndamGetLastBlock(relation, MAIN_FORKNUM);
	ItemPointerSet(&scan->curr_item, 0, 1);
    return (TableScanDesc) scan;
}

static bool
undam_getnextslot(TableScanDesc scan, ScanDirection direction, TupleTableSlot *slot)
{
    UndamScanDesc uscan = (UndamScanDesc) scan;
    Relation      rel = scan->rs_rd;
	HeapTuple     tuple;
	int           pos = ItemPointerGetOffsetNumber(&uscan->curr_item);
	BlockNumber   blocknum = ItemPointerGetBlockNumber(&uscan->curr_item);
	int           nChunks = CHUNKS_PER_BLOCK;

    /* TODO: handle direction */
    if (direction == BackwardScanDirection)
        elog(ERROR, "undam: backward scan is not implemented");

	while (blocknum < uscan->last_block)
	{
		Buffer buf = ReadBufferExtended(rel, MAIN_FORKNUM, blocknum, RBM_ZERO_ON_ERROR, NULL); /* there may be empty pages because of difference in length of allocation chains */
		UndamPageHeader* pg = (UndamPageHeader*)BufferGetPage(buf);
		LockBuffer(buf, BUFFER_LOCK_SHARE);

		while (pos < nChunks)
		{
			if (pg->alloc_mask[pos >> 6] & ((uint64)1 << (pos & 63)))
			{
				ItemPointerSet(&uscan->curr_item, blocknum, pos);
				tuple = UndamReadTuple(scan->rs_rd, scan->rs_snapshot, &uscan->curr_item);
				if (tuple != NULL)
				{
					ExecStoreHeapTuple(tuple, slot, true);
					UnlockReleaseBuffer(buf);
					return true;
				}
			}
			pos += 1;
		}
		UnlockReleaseBuffer(buf);
		blocknum += 1;
		pos = 1;
	}
	return false;
}

static void
undam_rescan(TableScanDesc scan, ScanKey key, bool set_params,
            bool allow_strat, bool allow_sync, bool allow_pagemode)
{
    UndamScanDesc uscan = (UndamScanDesc) scan;
	ItemPointerSet(&uscan->curr_item, 0, 1);
}

static void
undam_endscan(TableScanDesc scan)
{
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
	HeapTuple tuple = UndamReadTuple(scan->rel, snapshot, tid);
	if (tuple != NULL)
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
	return tbmres->blockno < uscan->last_block;
}

static bool
undam_scan_bitmap_next_tuple(TableScanDesc scan,
                            struct TBMIterateResult *tbmres,
                            TupleTableSlot *slot)
{
    UndamScanDesc uscan = (UndamScanDesc) scan;
    Relation      rel = scan->rs_rd;
	HeapTuple     tuple;
	int           offs = ItemPointerGetOffsetNumber(&uscan->curr_item);
	BlockNumber   blocknum = tbmres->blockno;
	int           nChunks = CHUNKS_PER_BLOCK;
	Buffer buf = ReadBufferExtended(rel, MAIN_FORKNUM, blocknum, RBM_NORMAL, NULL);
	UndamPageHeader* pg = (UndamPageHeader*)BufferGetPage(buf);
	bool found = false;

	LockBuffer(buf, BUFFER_LOCK_SHARE);

	while (true)
	{
		int pos;
		if (tbmres->ntuples >= 0)
		{
			/* for non-lossy scan offs points to the position in tbmres->offsets. */
			if (offs >= tbmres->ntuples)
				break;
			pos = tbmres->offsets[offs];
		}
		else /* lossy scan */
		{
			/* for lossy scan we interpret offs as a position in the block */
 			if (offs > nChunks)
				break;
			pos = offs;
		}
		offs += 1;
		if (pg->alloc_mask[pos >> 6] & ((uint64)1 << (pos & 63)))
		{
			ItemPointerSet(&uscan->curr_item, blocknum, pos);
			tuple = UndamReadTuple(scan->rs_rd, scan->rs_snapshot, &uscan->curr_item);
			if (tuple != NULL)
			{
				found = true;
				ExecStoreHeapTuple(tuple, slot, true);
				break;
			}
		}
	}
	UnlockReleaseBuffer(buf);
	ItemPointerSetOffsetNumber(&uscan->curr_item, offs);
	return found;
}

static bool
undam_fetch_row_version(Relation relation,
						ItemPointer tid,
						Snapshot snapshot,
						TupleTableSlot *slot)
{
	HeapTuple tuple = UndamReadTuple(relation, snapshot, tid);
	if (tuple != NULL)
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
	int           pos = ItemPointerGetOffsetNumber(&uscan->curr_item);
	BlockNumber   blocknum = ItemPointerGetBlockNumber(&uscan->curr_item);
	Buffer buf = ReadBufferExtended(scan->rs_rd, MAIN_FORKNUM, blocknum, RBM_NORMAL, NULL);
	UndamPageHeader* pg = (UndamPageHeader*)BufferGetPage(buf);
	bool is_valid;

	LockBuffer(buf, BUFFER_LOCK_SHARE);
	is_valid = (pg->alloc_mask[pos >> 6] >> (pos & 63)) & 1;
	UnlockReleaseBuffer(buf);

	return is_valid;
}


static bool
undam_tuple_satisfies_snapshot(Relation rel, TupleTableSlot *slot,
                                Snapshot snapshot)
{
	HeapTupleTableSlot *hslot = (HeapTupleTableSlot *) slot;
	BlockNumber   blocknum = ItemPointerGetBlockNumber(&slot->tts_tid);
	Buffer buf = ReadBufferExtended(rel, MAIN_FORKNUM, blocknum, RBM_NORMAL, NULL);
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
undam_tuple_insert_speculative(Relation relation, TupleTableSlot *slot,
							   CommandId cid, int options,
							   BulkInsertState bistate, uint32 specToken)
{
    NOT_IMPLEMENTED;
}

static void
undam_tuple_complete_speculative(Relation relation, TupleTableSlot *slot,
								 uint32 specToken, bool succeeded)
{
    NOT_IMPLEMENTED;
}

static TM_Result
undam_tuple_update(Relation relation, ItemPointer otid, TupleTableSlot *slot,
				   CommandId cid, Snapshot snapshot, Snapshot crosscheck,
				   bool wait, TM_FailureData *tmfd,
				   LockTupleMode *lockmode, bool *update_indexes)
{
	TransactionId xid = GetCurrentTransactionId();
	Bitmapset  *key_attrs;
	Bitmapset  *modified_attrs;
	HeapTupleData oldtup;
	bool		shouldFree = true;
	HeapTuple   origtup;
	HeapTuple   newtup = ExecFetchSlotHeapTuple(slot, true, &shouldFree);
	MultiXactStatus mxact_status;
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
	origtup = UndamReadTuple(relation, snapshot, otid);
	Assert(origtup != NULL);
	modified_attrs = HeapDetermineModifiedColumns(relation, key_attrs,
												  origtup, newtup);
	pfree(origtup); /* not needed any more */

	if (!bms_is_empty(modified_attrs))
	{
		*lockmode = LockTupleNoKeyExclusive;
		mxact_status = MultiXactStatusNoKeyUpdate;
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
		mxact_status = MultiXactStatusUpdate;
		key_intact = false;
	}

	buffer = ReadBufferExtended(relation, MAIN_FORKNUM, ItemPointerGetBlockNumber(otid), RBM_NORMAL, NULL);
	page = BufferGetPage(buffer);
	LockBuffer(buffer, BUFFER_LOCK_EXCLUSIVE);
	oldtup.t_tableOid = RelationGetRelid(relation);
	oldtup.t_data = (HeapTupleHeader)((char*)page + ItemPointerGetOffsetNumber(otid)*UndamChunkSize);
	oldtup.t_len = HeapTupleHeaderGetDatumLength(oldtup.t_data);
	oldtup.t_self = *otid;

l2:
	checked_lockers = false;
	locker_remains = false;
	result = HeapTupleSatisfiesUpdate(&oldtup, cid, buffer);

	/* see below about the "no wait" case */
	Assert(result != TM_BeingModified || wait);

	if (result == TM_Invisible)
	{
		UnlockReleaseBuffer(buffer);
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("attempted to update invisible tuple")));
	}
	else if (result == TM_BeingModified && wait)
	{
		TransactionId xwait;
		uint16		infomask;
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

		xwait = HeapTupleHeaderGetRawXmax(oldtup.t_data);
		infomask = oldtup.t_data->t_infomask;

		/*
		 * Now we have to do something about the existing locker.  If it's a
		 * multi, sleep on it; we might be awakened before it is completely
		 * gone (or even not sleep at all in some cases); we need to preserve
		 * it as locker, unless it is gone completely.
		 *
		 * If it's not a multi, we need to check for sleeping conditions
		 * before actually going to sleep.  If the update doesn't conflict
		 * with the locks, we just continue without sleeping (but making sure
		 * it is preserved).
		 *
		 * Before sleeping, we need to acquire tuple lock to establish our
		 * priority for the tuple (see heap_lock_tuple).  LockTuple will
		 * release us when we are next-in-line for the tuple.  Note we must
		 * not acquire the tuple lock until we're sure we're going to sleep;
		 * otherwise we're open for race conditions with other transactions
		 * holding the tuple lock which sleep on us.
		 *
		 * If we are forced to "start over" below, we keep the tuple lock;
		 * this arranges that we stay at the head of the line while rechecking
		 * tuple state.
		 */
		if (infomask & HEAP_XMAX_IS_MULTI)
		{
			TransactionId update_xact;
			int			remain;
			bool		current_is_member = false;

			if (DoesMultiXactIdConflict((MultiXactId) xwait, infomask,
										*lockmode, &current_is_member))
			{
				LockBuffer(buffer, BUFFER_LOCK_UNLOCK);

				/*
				 * Acquire the lock, if necessary (but skip it when we're
				 * requesting a lock and already have one; avoids deadlock).
				 */
				if (!current_is_member)
					heap_acquire_tuplock(relation, &(oldtup.t_self), *lockmode,
										 LockWaitBlock, &have_tuple_lock);

				/* wait for multixact */
				MultiXactIdWait((MultiXactId) xwait, mxact_status, infomask,
								relation, &oldtup.t_self, XLTW_Update,
								&remain);
				checked_lockers = true;
				locker_remains = remain != 0;
				LockBuffer(buffer, BUFFER_LOCK_EXCLUSIVE);

				/*
				 * If xwait had just locked the tuple then some other xact
				 * could update this tuple before we get to this point.  Check
				 * for xmax change, and start over if so.
				 */
				if (xmax_infomask_changed(oldtup.t_data->t_infomask,
										  infomask) ||
					!TransactionIdEquals(HeapTupleHeaderGetRawXmax(oldtup.t_data),
										 xwait))
					goto l2;
			}

			/*
			 * Note that the multixact may not be done by now.  It could have
			 * surviving members; our own xact or other subxacts of this
			 * backend, and also any other concurrent transaction that locked
			 * the tuple with LockTupleKeyShare if we only got
			 * LockTupleNoKeyExclusive.  If this is the case, we have to be
			 * careful to mark the updated tuple with the surviving members in
			 * Xmax.
			 *
			 * Note that there could have been another update in the
			 * MultiXact. In that case, we need to check whether it committed
			 * or aborted. If it aborted we are safe to update it again;
			 * otherwise there is an update conflict, and we have to return
			 * TableTuple{Deleted, Updated} below.
			 *
			 * In the LockTupleExclusive case, we still need to preserve the
			 * surviving members: those would include the tuple locks we had
			 * before this one, which are important to keep in case this
			 * subxact aborts.
			 */
			if (!HEAP_XMAX_IS_LOCKED_ONLY(oldtup.t_data->t_infomask))
				update_xact = HeapTupleGetUpdateXid(oldtup.t_data);
			else
				update_xact = InvalidTransactionId;

			/*
			 * There was no UPDATE in the MultiXact; or it aborted. No
			 * TransactionIdIsInProgress() call needed here, since we called
			 * MultiXactIdWait() above.
			 */
			if (!TransactionIdIsValid(update_xact) ||
				TransactionIdDidAbort(update_xact))
				can_continue = true;
		}
		else if (TransactionIdIsCurrentTransactionId(xwait))
		{
			/*
			 * The only locker is ourselves; we can avoid grabbing the tuple
			 * lock here, but must preserve our locking information.
			 */
			checked_lockers = true;
			locker_remains = true;
			can_continue = true;
		}
		else if (HEAP_XMAX_IS_KEYSHR_LOCKED(infomask) && key_intact)
		{
			/*
			 * If it's just a key-share locker, and we're not changing the key
			 * columns, we don't need to wait for it to end; but we need to
			 * preserve it as locker.
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
			heap_acquire_tuplock(relation, &(oldtup.t_self), *lockmode,
								 LockWaitBlock, &have_tuple_lock);
			XactLockTableWait(xwait, relation, &oldtup.t_self,
							  XLTW_Update);
			checked_lockers = true;
			LockBuffer(buffer, BUFFER_LOCK_EXCLUSIVE);

			/*
			 * xwait is done, but if xwait had just locked the tuple then some
			 * other xact could update this tuple before we get to this point.
			 * Check for xmax change, and start over if so.
			 */
			if (xmax_infomask_changed(oldtup.t_data->t_infomask, infomask) ||
				!TransactionIdEquals(xwait,
									 HeapTupleHeaderGetRawXmax(oldtup.t_data)))
				goto l2;

			/* Otherwise check if it committed or aborted */
			UpdateXmaxHintBits(oldtup.t_data, buffer, xwait);
			if (oldtup.t_data->t_infomask & HEAP_XMAX_INVALID)
				can_continue = true;
		}

		if (can_continue)
			result = TM_Ok;
		else if (!ItemPointerEquals(&oldtup.t_self, &oldtup.t_data->t_ctid) ||
				 HeapTupleHeaderIndicatesMovedPartitions(oldtup.t_data))
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
			   result == TM_BeingModified);
		Assert(!(oldtup.t_data->t_infomask & HEAP_XMAX_INVALID));
		Assert(result != TM_Updated ||
			   !ItemPointerEquals(&oldtup.t_self, &oldtup.t_data->t_ctid));
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
	CheckForSerializableConflictIn(relation, otid, BufferGetBlockNumber(buffer));

	/* NO EREPORT(ERROR) from here till changes are logged */
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

	newtup->t_self = *otid;
	UndamUpdateTuple(relation, newtup, buffer);

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
	NOT_IMPLEMENTED;
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
	for (int fork = MAIN_FORKNUM; fork <= EXT_FORKNUM; fork++)
		forks[fork] = UndamGetLastBlock(rel, fork);
	*pages = forks[MAIN_FORKNUM] + forks[EXT_FORKNUM];
	*tuples = (double)forks[MAIN_FORKNUM]*(CHUNKS_PER_BLOCK-1);
	*allvisfrac = 0;
}

static bool
UndamBitmapCheck(ItemPointer itemptr, void *state)
{
	UndamPosition pos = POSITION_FROM_ITEMPOINTER(itemptr);
	uint64* dead_bitmap = (uint64*)state;
	return (dead_bitmap[pos >> 6] >> (pos & 63)) & 1;
}

static void
UndamVacuumIndexes(Relation rel, uint64* deadBitmap, uint64 reltuples, BufferAccessStrategy bstrategy)
{
	Relation   *Irel;
	int			nindexes;
	IndexVacuumInfo ivinfo;
	IndexBulkDeleteResult **stats;

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
		stats[idx] = index_bulk_delete(&ivinfo, stats[idx], UndamBitmapCheck, (void*)deadBitmap);
	}
	/* TODO: do something with index stats */

	/* Done with indexes */
	vac_close_indexes(nindexes, Irel, NoLock);
}

static void
undam_relation_vacuum(Relation rel,
					  struct VacuumParams *params,
					  BufferAccessStrategy bstrategy)
{
	BlockNumber lastBlock = UndamGetLastBlock(rel, MAIN_FORKNUM);
	int nChunks = CHUNKS_PER_BLOCK;
	HeapTupleData tuple;
	uint64 nTuples  = (uint64)lastBlock*nChunks;
	uint64* deadBitmap = (uint64*)calloc(nTuples/64, 8);
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

	for (BlockNumber block = 0; block < lastBlock; block++)
	{
		Buffer buf = ReadBufferExtended(rel, MAIN_FORKNUM, block, RBM_NORMAL, NULL);
		UndamPageHeader* pg = (UndamPageHeader*)BufferGetPage(buf);
		GenericXLogState* xlogState = NULL;
		uint64 nDeleted = 0;
		Buffer chainBuf = InvalidBuffer;

		LockBuffer(buf, BUFFER_LOCK_SHARE);

		for (int chunk = 1; chunk < nChunks; chunk++)
		{
			if (pg->alloc_mask[chunk >> 6] & ((uint64)1 << (chunk & 63)))
			{
				UndamTupleHeader* tup = (UndamTupleHeader*)((char*)pg + chunk*UndamChunkSize);
				if (!HeapTupleHeaderXminFrozen(&tup->hdr))
				{
					TransactionId xmin = HeapTupleHeaderGetRawXmin(&tup->hdr);
					if (TransactionIdPrecedes(xmin, oldestXmin)) /* Tuple is visible for everybody */
					{
						if (xlogState == NULL) 
						{
							LockBuffer(buf, BUFFER_LOCK_UNLOCK);
							LockBuffer(buf, BUFFER_LOCK_EXCLUSIVE);
							xlogState = GenericXLogStart(rel);
							pg = (UndamPageHeader*)GenericXLogRegisterBuffer(xlogState, buf, 0);
							chunk = 0;
							continue; /* Retry scan of page under execlusive lock */
						}
						tuple.t_data = &tup->hdr;
						tuple.t_len =  HeapTupleHeaderGetDatumLength(&tup->hdr);
						if (HeapTupleSatisfiesVacuum(&tuple, oldestXmin, buf) == HEAPTUPLE_DEAD)
						{
							UndamPosition pos = GET_POSITION(block, chunk);
							pg->alloc_mask[chunk >> 6] &= ~((uint64)1 << (chunk & 63));
							deadBitmap[pos >> 6] |= (uint64)1 << (pos & 63);
							nDeleted += 1;
							if (tup->next_chunk != INVALID_POSITION)
								UndamDeleteTuple(rel, tup->next_chunk); /* delete tuple tail */
						}
						else if (TransactionIdPrecedes(xmin, freezeLimit))
						{
							/* TODO: not sure that it is enough to freeze tuple: or should we use heap_freeze_tuple ? */
							tup->hdr.t_infomask |= HEAP_XMIN_FROZEN;
						}
						if (tup->undo_chain != INVALID_POSITION)
						{
							/* We do not ndeed undo chain any more */
							UndamDeleteTuple(rel, tup->undo_chain);
							tup->undo_chain = INVALID_POSITION;
						}
					}
					else /* Traverse undo chain */
					{
						UndamPosition undo = tup->undo_chain;
						while (undo != INVALID_POSITION)
						{
							Buffer vbuf = ReadBufferExtended(rel, MAIN_FORKNUM, POSITION_GET_BLOCK_NUMBER(undo), RBM_NORMAL, NULL);
							UndamPageHeader* vpg = (UndamPageHeader*)BufferGetPage(vbuf);
							UndamTupleHeader* ver;

							LockBuffer(vbuf, BUFFER_LOCK_SHARE);

							ver = (UndamTupleHeader*)((char*)vpg + POSITION_GET_BLOCK_OFFSET(undo));
							if (TransactionIdPrecedes(HeapTupleHeaderGetRawXmin(&ver->hdr), oldestXmin)) /* Tuple is visible for everybody */
							{
								if (ver->undo_chain != INVALID_POSITION)
								{
									GenericXLogState* vxlogState = GenericXLogStart(rel);
									LockBuffer(vbuf, BUFFER_LOCK_UNLOCK);
									LockBuffer(vbuf, BUFFER_LOCK_EXCLUSIVE);
									vpg = (UndamPageHeader*)GenericXLogRegisterBuffer(xlogState, vbuf, 0);
									ver = (UndamTupleHeader*)((char*)vpg + POSITION_GET_BLOCK_OFFSET(undo));
									Assert(ver->undo_chain != INVALID_POSITION);
									UndamDeleteTuple(rel, ver->undo_chain);
									ver->undo_chain = INVALID_POSITION;
									GenericXLogFinish(vxlogState);
								}
								UnlockReleaseBuffer(vbuf);
								break;
							}
							undo = ver->undo_chain;
							UnlockReleaseBuffer(vbuf);
						}
					}
				}
			}
		}
		if (nDeleted != 0 && (pg->pd_flags & PD_PAGE_FULL))  /* page was full: include it in allocation chain  */
		{
			int chainNo = block % UndamNAllocChains;
			Buffer chainBuf;
			UndamPageHeader* chain;
			UndamAllocChain* chains = UndamGetAllocChain(rel);

			Assert(xlogState != NULL);
			pg->pd_flags &= ~PD_PAGE_FULL;

			if (chainNo != block) /* check if allocation chain header is at the same page */
			{
				chainBuf = ReadBufferExtended(rel, MAIN_FORKNUM, chainNo*BLCKSZ, RBM_NORMAL, NULL);
				LockBuffer(chainBuf, BUFFER_LOCK_EXCLUSIVE);
				chain = (UndamPageHeader*)GenericXLogRegisterBuffer(xlogState, chainBuf, 0);
				Assert(chain->head == chains[chainNo].forks[MAIN_FORKNUM].head);
			}
			else
			{
				chain = pg;
				chainBuf = InvalidBuffer;
			}
			/* Update chain header */
			pg->next = chain->head;
			chain->head = block;
			chains[chainNo].forks[MAIN_FORKNUM].head = block;
		}
		if (xlogState)
			GenericXLogFinish(xlogState);
		UnlockReleaseBuffer(buf);
		if (chainBuf)
			UnlockReleaseBuffer(chainBuf);
	}

	UndamVacuumIndexes(rel, deadBitmap, nTuples, bstrategy);
	/* TODO: update statistic, relfrozenxid,... */

	free(deadBitmap);
}

static inline TM_Result
undam_tuple_delete(Relation relation, ItemPointer tid, CommandId cid,
				   Snapshot snapshot, Snapshot crosscheck, bool wait,
				   TM_FailureData *tmfd, bool changingPart)
{
	TM_Result	result;
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

	block = ItemPointerGetBlockNumber(tid);
	buffer = ReadBuffer(relation, block);
	page = BufferGetPage(buffer);

	LockBuffer(buffer, BUFFER_LOCK_EXCLUSIVE);

	tup = (UndamTupleHeader*)((char*)page + ItemPointerGetOffsetNumber(tid)*UndamChunkSize);

	tp.t_tableOid = RelationGetRelid(relation);
	tp.t_data = &tup->hdr;
	tp.t_len = HeapTupleHeaderGetDatumLength(&tup->hdr);
	tp.t_self = *tid;

l1:
	result = HeapTupleSatisfiesUpdate(&tp, cid, buffer);

	if (result == TM_Invisible)
	{
		UnlockReleaseBuffer(buffer);
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("attempted to delete invisible tuple")));
	}
	else if (result == TM_BeingModified && wait)
	{
		TransactionId xwait;
		uint16		infomask;

		/* must copy state data before unlocking buffer */
		xwait = HeapTupleHeaderGetRawXmax(tp.t_data);
		infomask = tp.t_data->t_infomask;

		/*
		 * Sleep until concurrent transaction ends -- except when there's a
		 * single locker and it's our own transaction.  Note we don't care
		 * which lock mode the locker has, because we need the strongest one.
		 *
		 * Before sleeping, we need to acquire tuple lock to establish our
		 * priority for the tuple (see heap_lock_tuple).  LockTuple will
		 * release us when we are next-in-line for the tuple.
		 *
		 * If we are forced to "start over" below, we keep the tuple lock;
		 * this arranges that we stay at the head of the line while rechecking
		 * tuple state.
		 */
		if (infomask & HEAP_XMAX_IS_MULTI)
		{
			bool		current_is_member = false;

			if (DoesMultiXactIdConflict((MultiXactId) xwait, infomask,
										LockTupleExclusive, &current_is_member))
			{
				LockBuffer(buffer, BUFFER_LOCK_UNLOCK);

				/*
				 * Acquire the lock, if necessary (but skip it when we're
				 * requesting a lock and already have one; avoids deadlock).
				 */
				if (!current_is_member)
					heap_acquire_tuplock(relation, &(tp.t_self), LockTupleExclusive,
										 LockWaitBlock, &have_tuple_lock);

				/* wait for multixact */
				MultiXactIdWait((MultiXactId) xwait, MultiXactStatusUpdate, infomask,
								relation, &(tp.t_self), XLTW_Delete,
								NULL);
				LockBuffer(buffer, BUFFER_LOCK_EXCLUSIVE);

				/*
				 * If xwait had just locked the tuple then some other xact
				 * could update this tuple before we get to this point.  Check
				 * for xmax change, and start over if so.
				 */
				if (xmax_infomask_changed(tp.t_data->t_infomask, infomask) ||
					!TransactionIdEquals(HeapTupleHeaderGetRawXmax(tp.t_data),
										 xwait))
					goto l1;
			}

			/*
			 * You might think the multixact is necessarily done here, but not
			 * so: it could have surviving members, namely our own xact or
			 * other subxacts of this backend.  It is legal for us to delete
			 * the tuple in either case, however (the latter case is
			 * essentially a situation of upgrading our former shared lock to
			 * exclusive).  We don't bother changing the on-disk hint bits
			 * since we are about to overwrite the xmax altogether.
			 */
		}
		else if (!TransactionIdIsCurrentTransactionId(xwait))
		{
			/*
			 * Wait for regular transaction to end; but first, acquire tuple
			 * lock.
			 */
			LockBuffer(buffer, BUFFER_LOCK_UNLOCK);
			heap_acquire_tuplock(relation, &(tp.t_self), LockTupleExclusive,
								 LockWaitBlock, &have_tuple_lock);
			XactLockTableWait(xwait, relation, &(tp.t_self), XLTW_Delete);
			LockBuffer(buffer, BUFFER_LOCK_EXCLUSIVE);

			/*
			 * xwait is done, but if xwait had just locked the tuple then some
			 * other xact could update this tuple before we get to this point.
			 * Check for xmax change, and start over if so.
			 */
			if (xmax_infomask_changed(tp.t_data->t_infomask, infomask) ||
				!TransactionIdEquals(HeapTupleHeaderGetRawXmax(tp.t_data),
									 xwait))
				goto l1;

			/* Otherwise check if it committed or aborted */
			UpdateXmaxHintBits(tp.t_data, buffer, xwait);
		}

		/*
		 * We may overwrite if previous xmax aborted, or if it committed but
		 * only locked the tuple without updating it.
		 */
		if ((tp.t_data->t_infomask & HEAP_XMAX_INVALID) ||
			HEAP_XMAX_IS_LOCKED_ONLY(tp.t_data->t_infomask) ||
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
			   result == TM_BeingModified);
		Assert(!(tp.t_data->t_infomask & HEAP_XMAX_INVALID));
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
	CheckForSerializableConflictIn(relation, tid, BufferGetBlockNumber(buffer));

	xlogState = GenericXLogStart(relation);
	page = GenericXLogRegisterBuffer(xlogState, buffer, 0);
	tup = (UndamTupleHeader*)((char*)page + ItemPointerGetOffsetNumber(tid)*UndamChunkSize);
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

	GenericXLogFinish(xlogState);
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

	RelationOpenSmgr(rel);

	/*
	 * Make sure smgr_targblock etc aren't pointing somewhere past new end
	 */
	rel->rd_smgr->smgr_targblock = InvalidBlockNumber;
	rel->rd_smgr->smgr_fsm_nblocks = InvalidBlockNumber;
	rel->rd_smgr->smgr_vm_nblocks = InvalidBlockNumber;

	if (RelationNeedsWAL(rel))
	{
		/* TODO: we can not use SMGR_TRUNCATE_ALL because of special handling of free space mao fork */
	}

    /* Do the real work to truncate relation forks */
	smgrtruncate(rel->rd_smgr, forks, 2, blocks);

	/*
	 * Remove entry from hash to force reinitialization of root pages.
	 */
	hash_search(UndamAllocChainsHash, &RelationGetRelid(rel), HASH_REMOVE, NULL);
}

static void
undam_relation_set_new_filenode(Relation rel,
								 const RelFileNode *newrnode,
								 char persistence,
								 TransactionId *freezeXid,
								 MultiXactId *minmulti)
{
	SMgrRelation srel;

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

	if (blockno >= uscan->last_block)
		return false;

	ItemPointerSet(&uscan->curr_item, blockno, 1);
    return true;
}

static bool
undam_scan_analyze_next_tuple(TableScanDesc scan, TransactionId OldestXmin,
							  double *liverows, double *deadrows,
							  TupleTableSlot *slot)
{
    UndamScanDesc uscan = (UndamScanDesc) scan;
    Relation      rel = scan->rs_rd;
	int           item = ItemPointerGetOffsetNumber(&uscan->curr_item);
	BlockNumber   blocknum = ItemPointerGetBlockNumber(&uscan->curr_item);
	int           nChunks = CHUNKS_PER_BLOCK;
	Buffer        buf = ReadBufferExtended(rel, MAIN_FORKNUM, blocknum, RBM_ZERO_ON_ERROR, NULL);
	UndamPageHeader* pg = (UndamPageHeader*)BufferGetPage(buf);

	LockBuffer(buf, BUFFER_LOCK_SHARE);

	while (item < nChunks)
	{
		if (pg->alloc_mask[item >> 6] & ((uint64)1 << (item & 63)))
		{
			UndamTupleHeader* tup = (UndamTupleHeader*)((char*)pg + item*UndamChunkSize);
			HeapTupleData tuphdr;
			int len = HeapTupleHeaderGetDatumLength(&tup->hdr);
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
				elog(ERROR, "unexpected HeapTupleSatisfiesVacuum result");
				break;
			}
			if (sample_it)
			{
				HeapTuple tuple = (HeapTuple)palloc(sizeof(HeapTupleData) + len);
				int available = UndamChunkSize - offsetof(UndamTupleHeader, hdr);

				*tuple = tuphdr;
				tuple->t_data = (HeapTupleHeader)(tuple + 1); /* store tuple bosy just after the header */
				if (len <= available)
				{
					memcpy(tuple->t_data, &tup->hdr, len);
				}
				else
				{
					UndamTupleChunk* chunk;
					char* dst = (char*)tuple->t_data;
					UndamPosition next = tup->next_chunk;

					memcpy(dst, &tup->hdr, available);
					dst += available;
					len -= available;
					available =  UndamChunkSize - offsetof(UndamTupleChunk, data); /* head chunk contains less data */

					do {
						UnlockReleaseBuffer(buf);
						buf = ReadBufferExtended(rel, EXT_FORKNUM, POSITION_GET_BLOCK_NUMBER(next), RBM_NORMAL, NULL);
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
        elog(ERROR, "partial range scan is not supported");

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
        HeapTuple   tuple;

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
        tuple = ExecCopySlotHeapTuple(slot);
        tuple->t_self = slot->tts_tid;
        callback(indexRelation, &tuple->t_self, values, isnull, true, callback_state);

        pfree(tuple);
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
    NOT_IMPLEMENTED;
}

static bool
undam_scan_sample_next_tuple(TableScanDesc scan, SampleScanState *scanstate,
                              TupleTableSlot *slot)
{
    NOT_IMPLEMENTED;
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
	 * allow the cs_* functions to be created even when the
	 * module isn't active.  The functions must protect themselves against
	 * being called then, however.)
	 */
	if (!process_shared_preload_libraries_in_progress)
		return;

#ifdef TABLEAM_OPTOINS_SUPPORTED
	UndamReloptKind = add_reloption_kind();
	add_int_reloption(UndamReloptKind, "chunk", "Size of allocation chunk", 64, 64, BLCKSZ/8, AccessExclusiveLock);
	add_int_reloption(UndamReloptKind, "chains", "Number of allocation chains", 8, 1,128, AccessExclusiveLock);
#else
       DefineCustomIntVariable("undam.chunk_size",
                            "Size of allocation chaunk.",
                                                       NULL,
                                                       &UndamChunkSize,
                                                       64,
                                                       64,
                                                       BLCKSZ/8,
                                                       PGC_POSTMASTER,
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
                                                       128,
                                                       PGC_POSTMASTER,
                                                       0,
                                                       NULL,
                                                       NULL,
                                                       NULL);
#endif

	DefineCustomIntVariable("undam.max_relations",
                            "Maximal number of relations.",
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
	RequestAddinShmemSpace(hash_estimate_size(UndamMaxRelations, sizeof(Oid) + sizeof(UndamAllocChain)*UndamNAllocChains));
	prev_shmem_startup_hook = shmem_startup_hook;
	shmem_startup_hook = UndamShmemStartup;
}

#ifdef TABLEAM_OPTOINS_SUPPORTED
/*
 * Parse reloptions for Undam table, producing a UndamOptions struct.
 */
bytea *
undamoptions(Datum reloptions, bool validate)
{
	UndamOptions *rdopts;

	/* Parse the user-given reloptions */
	rdopts = (UndamOptions *) build_reloptions(reloptions, validate,
											   UndamReloptKind,
											   sizeof(UndamOptions),
											   UndamReloptTab,
											   lengthof(UndamReloptTab));

	return (bytea *) rdopts;
}
#endif
