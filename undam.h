#ifndef __UNDAM_H__
#define __UNDAM_H__

#define EXT_FORKNUM 1
#define MAX_ALLOC_CHAINS 64
#define MIN_CHUNK_SIZE   64
#define MAX_CHUNK_SIZE   (BLCKSZ/8)

typedef uint64_t UndamPosition;

#define CHUNKS_PER_BLOCK               (BLCKSZ/relinfo->chunkSize)
#define CHUNK_SIZE                     (relinfo->chunkSize)
#define N_ALLOC_CHAINS                 (relinfo->nChains)
#define POSITION_GET_BLOCK_NUMBER(pos) ((BlockNumber)((pos)/CHUNKS_PER_BLOCK))
#define POSITION_GET_ITEM(pos)         ((uint32)((pos) % CHUNKS_PER_BLOCK))
#define POSITION_GET_BLOCK_OFFSET(pos) (POSITION_GET_ITEM(pos)*CHUNK_SIZE)
#define GET_POSITION(blocknum,item)    ((UndamPosition)(blocknum)*CHUNKS_PER_BLOCK + (item))
#define POSITION_FROM_ITEMPOINTER(ip)  GET_POSITION(BlockIdGetBlockNumber(&(ip)->ip_blkid), (ip)->ip_posid)
#define INVALID_POSITION               GET_POSITION(InvalidBlockNumber, 0)

/*
 * Structure for specifying Undam relation options.
 * Not used now because customoptions are not supported by Table-AM.
 */
typedef struct
{
	int32		vl_len_;	 /* varlena header (do not touch directly!) */
	uint32		chunkSize;	 /* chunk size */
	uint32      allocChains; /* number of allocation chains */
} UndamOptions;

/*
 * Header of Undam allocation list. We use L1 where all not completely filled relation
 * pages are linked. The tail points to first unsed page of relation which (blockno % undam.alloc_chains) == chain_no.
 */
typedef struct
{
	BlockNumber head; /* head of L1 list of not-full pages */
	BlockNumber tail; /* last allocated page */
} UndamAllocList;

/*
 * Undam allocation chain. We need two separate lists for main and extension forks.
 */
typedef struct
{
	UndamAllocList forks[2];
} UndamAllocChain;


/*
 * Undam tuple header.
 */
typedef struct
{
	UndamPosition nextChunk; /* L1-list of extension chunks */
	UndamPosition undoChain; /* L1-list of undo versions */
	uint32        size;       /* Length of the tuple */
 	HeapTupleHeaderData hdr;
} UndamTupleHeader;

/*
 * Internal chunk format. We save space of one pointer by using separate format for header and internal chunks.
 */
typedef struct
{
	UndamPosition next; /* Next chunk in L1-list of tuple's chunks */
	char   data[FLEXIBLE_ARRAY_MEMBER];
} UndamTupleChunk;

/*
 * Undam page header. First chunk of the page is not used for data and as far as minimal size of chunk is 64 bytes,
 * there are no string reasons to minimize size of pgae header. Size of standard Postgres page header is 24 bytes,
 * we add three pointers for allocation chains (next/head/tail) - yet another 12 bytes, plus 4 bytes for storing
 * allacation metainformation (filled only at root pages) and still we have more than enough space for bitmap.
 */
typedef struct
{
	/* We have to copy fields from PageHeaderDta because it has variable size pd_linp component */
	/* XXX LSN is member of *any* block, not only page-organized ones */
	PageXLogRecPtr pd_lsn;		/* LSN: next byte after last byte of xlog
								 * record for last change to this page */
	uint16		   pd_checksum;	/* checksum */
	uint16		   pd_flags;		/* flag bits, see below */
	LocationIndex  pd_lower;		/* offset to start of free space */
	LocationIndex  pd_upper;		/* offset to end of free space */
	LocationIndex  pd_special;	/* offset to start of special space */
	uint16		   pd_pagesize_version;
	TransactionId  pd_prune_xid; /* oldest prunable XID, or zero if none */

	BlockNumber    next; /* pointer to next page in L1 list of not-full pages */
	BlockNumber    head; /* head of L1 list of not-full pages */
	BlockNumber    tail; /* last allocated page */
	uint16         chunkSize; /* size of chunk: used to verify data format */
	uint16         nChains; /* number of allocation chains: used to verify data format */
	uint64         allocMask[FLEXIBLE_ARRAY_MEMBER];
} UndamPageHeader;

/*
 * Hash entry for keeping in shared memory information about Undam relations.
 */
typedef struct
{
	Oid reloid;         /* relation OID */
	uint32 chunkSize;   /* allocation chunk size */
	uint32 nChains;     /* number of allocation chains */
	uint32 nScannedTuples;
	uint32 nScannedChunks;
	uint32 nScannedVersions;
	UndamAllocChain chains[MAX_ALLOC_CHAINS]; /* allocation chains themselves */
} UndamRelationInfo;

/*
 * Undam scan descriptor. It sepcifies current block number of last block number until we should scan.
 * As far as we have multiple allocatoin chains which may have diffent length, there can be unused
 * blocks which should be ignored during sequential scan.
 */
typedef struct
{
    TableScanDescData   base;
	BlockNumber         lastBlock; /* last block until we should scan */
    ItemPointerData     currItem;  /* current block numbder */
	Buffer              currBuf;   /* currently used buffer (pinned) */
	UndamRelationInfo*  relinfo;   /* scanned relation info */
} UndamScanDescData;
typedef UndamScanDescData* UndamScanDesc;

/*
 * Context for vacuuming Undam relation.
 * instead of ordered list of ItemPointers maintained by standard Postgres vacuum,
 * we prefer to use bitmap of chunk. Minimal size fo chunk is 64, so size of this bitmap is at least 256 times
 * smaller than number of rows in relation. For example for relation containing one billion of rows size of bitmap willbe just 4Mb.
 */
typedef struct
{
	UndamRelationInfo* relinfo;
	uint64*            deadBitmap; /* bitmap of dead tuples */
} UndamVacuumContext;


#endif
