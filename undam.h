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

typedef struct
{
	int32		vl_len_;	 /* varlena header (do not touch directly!) */
	uint32		chunkSize;	 /* chunk size */
	uint32      allocChains; /* number of allocation chains */
} UndamOptions;

typedef struct
{
	BlockNumber head; /* head of L1 list of not-full pages */
	BlockNumber tail; /* first unused page */
} UndamAllocList;

typedef struct
{
	UndamAllocList forks[2];
} UndamAllocChain;

typedef struct
{
	UndamPosition nextChunk;
	UndamPosition undoChain;
	HeapTupleHeaderData hdr;
} UndamTupleHeader;

typedef struct
{
	UndamPosition next;
	char   data[FLEXIBLE_ARRAY_MEMBER];
} UndamTupleChunk;

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
	BlockNumber    tail; /* last free page */
	uint16         chunkSize; /* size of chunk: used to verify data format */
	uint16         nChains; /* number of allocation chains: used to verify data format */
	uint64         allocMask[FLEXIBLE_ARRAY_MEMBER];
} UndamPageHeader;

typedef struct
{
	Oid reloid;
	uint32 chunkSize;
	uint32 nChains;
	UndamAllocChain chains[MAX_ALLOC_CHAINS];
} UndamRelationInfo;


typedef struct
{
    TableScanDescData   base;
	BlockNumber         lastBlock;
    ItemPointerData     currItem;
} UndamScanDescData;
typedef UndamScanDescData* UndamScanDesc;

typedef struct
{
	UndamRelationInfo* relinfo;
	uint64*            deadBitmap;
} UndamVacuumContext;


#endif
