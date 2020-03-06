#ifndef __UNDAM_H__
#define __UNDAM_H__

#define EXT_FORKNUM 1

typedef uint64_t UndamPosition;

#define CHUNKS_PER_BLOCK               (BLCKSZ/UndamChunkSize)
#define POSITION_GET_BLOCK_NUMBER(pos) ((BlockNumber)((pos)/CHUNKS_PER_BLOCK))
#define POSITION_GET_ITEM(pos)         ((uint32)((pos) % CHUNKS_PER_BLOCK))
#define POSITION_GET_BLOCK_OFFSET(pos) (POSITION_GET_ITEM(pos)*UndamChunkSize)
#define GET_POSITION(blocknum,item)    ((UndamPosition)(blocknum)*CHUNKS_PER_BLOCK + (item))
#define POSITION_FROM_ITEMPOINTER(ip)  GET_POSITION(BlockIdGetBlockNumber(&(ip)->ip_blkid), (ip)->ip_posid)
#define INVALID_POSITION               GET_POSITION(InvalidBlockNumber, 0)

typedef struct
{
	int32		vl_len_;	 /* varlena header (do not touch directly!) */
	int			chunkSize;	 /* chunk size */
	int         allocChains; /* number of allocation chains */
} UndamOptions;

typedef struct
{
	BlockNumber head;
	BlockNumber tail;
} UndamAllocList;

typedef struct
{
	UndamAllocList forks[2];
} UndamAllocChain;

typedef struct
{
	UndamPosition next_chunk;
	UndamPosition undo_chain;
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
	uint16         chunk_size; /* size of chunk: used to verify data format */
	uint16         n_chains; /* number of allocation chains: used to verify data format */
	uint64         alloc_mask[FLEXIBLE_ARRAY_MEMBER];
} UndamPageHeader;

typedef struct
{
	Oid reloid;
	UndamAllocChain chains[FLEXIBLE_ARRAY_MEMBER];
} UndamAllocHashEntry;


typedef struct
{
    TableScanDescData   base;
	BlockNumber         last_block;
    ItemPointerData     curr_item;
} UndamScanDescData;
typedef UndamScanDescData* UndamScanDesc;

#endif
