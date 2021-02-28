/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Faruk Aydin",
    /* First member's email address */
    "farukaydin@outlook.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define CHUNKSIZE (1 << 8)
#define WSIZE 4 /* Word and header/footer size (bytes) */
#define DSIZE 8 /* Double word size (bytes) */
#define OVERHEAD 8
#define MINIMUM 24 /* Extend heap by this amount (bytes) */

static inline int MAX(int x, int y)
{
    return x > y ? x : y;
}

//
// Pack a size and allocated bit into a word
// We mask of the "alloc" field to insure only
// the lower bit is used
//
static inline uint32_t PACK(uint32_t size, int alloc)
{
    return ((size) | (alloc & 0x1));
}

//
// Read and write a word at address p
//
static inline uint32_t GET(void *p) { return *(uint32_t *)p; }
static inline void PUT(void *p, uint32_t val)
{
    *((uint32_t *)p) = val;
}

//
// Read the size and allocated fields from address p
//
static inline uint32_t GET_SIZE(void *p)
{
    return GET(p) & ~0x7;
}

static inline int GET_ALLOC(void *p)
{
    return GET(p) & 0x1;
}

//
// Given block ptr bp, compute address of its header and footer
//
static inline void *HDRP(void *bp)
{

    return ((char *)bp) - WSIZE;
}
static inline void *FTRP(void *bp)
{
    return ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE);
}

//
// Given block ptr bp, compute address of next and previous blocks
//
static inline void *NEXT_BLKP(void *bp)
{
    return ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)));
}

static inline void *PREV_BLKP(void *bp)
{
    return ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)));
}

//
// function prototypes for internal helper routines
//
static void *extend_heap(uint32_t words);
static void place(void *bp, uint32_t asize);
static void *find_fit(uint32_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp);
static void checkblock(void *bp);

typedef struct node node_t;

static char *heap_listp;
static node_t *free_listp;

struct node
{
    node_t *next;
    node_t *prev;
};

static void remove_freenode(node_t *node)
{
    if (GET_SIZE(HDRP(node)) == 0)
    {
        PUT(HDRP(node), PACK(0, 1));
        return;
    }
    if (node->next == NULL && node->prev == NULL)
    {
        free_listp = NULL;
    }
    else if (node->prev == NULL && node->next != NULL)
    {
        free_listp = node->next;
        free_listp->prev = NULL;
    }
    else if (node->prev != NULL && node->next == NULL)
    {
        node->prev->next = NULL;
    }
    else if (node->prev != NULL && node->next != NULL)
    {
        node->prev->next = node->next;
        node->next->prev = node->prev;
        node->prev = NULL;
        node->next = NULL;
    }
}

static void insert_front(node_t *node)
{
    if (GET_ALLOC(HDRP(node)))
    {
        return;
    }

    if (free_listp == NULL)
    {
        free_listp = node;
        node->next = NULL;
        node->prev = NULL;
    }
    else if (free_listp != NULL)
    {
        node->prev = free_listp->prev;
        node->next = free_listp;
        free_listp->prev = node;
        free_listp = node;
    }
}

static void *find_fit(uint32_t asize)
{

    /* First-fit search */
    node_t *bp;
    for (bp = free_listp; bp != NULL; bp = bp->next)
    {
        if (asize <= GET_SIZE(HDRP(bp)))
        {
            return bp;
        }
    }
    return NULL; /* No fit */
}

static void place(void *bp, uint32_t asize)
{

    uint32_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        remove_freenode(bp);

        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        insert_front(bp);
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        remove_freenode(bp);
    }
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc)
    {
        insert_front(bp);
        return bp;
    }
    else if (prev_alloc && !next_alloc)
    {
        size = size + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        remove_freenode(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));

        insert_front(bp);
        return bp;
    }
    else if (!prev_alloc && next_alloc)
    {
        size = size + GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        return bp;
    }
    else if (!prev_alloc && !next_alloc)
    {
        size = size + GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        remove_freenode(NEXT_BLKP(bp));
        remove_freenode(PREV_BLKP(bp));

        bp = PREV_BLKP(bp);
        insert_front(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        return bp;
    }
    return bp;
}

static void *extend_heap(uint32_t words)
{

    node_t *bp;
    uint32_t size;

    /* Allocate an even number of wrods to maintain alignment */

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if ((bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */

    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */

    return coalesce(bp);
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    free_listp = NULL;
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
    {
        return -1;
    }

    PUT(heap_listp, 0);                            /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */

    heap_listp += (2 * WSIZE);

    /* Extend the empty heap with a free block of MINALLOCSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(uint32_t size)
{

    int newsize = ALIGN(size + 24);
    uint32_t extendsize;
    char *bp;

    /* Search the free list for a fit */
    if ((bp = find_fit(newsize)) != NULL)
    {
        place(bp, newsize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(newsize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, newsize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{

    uint32_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, uint32_t size)
{
    void *newp;
    uint32_t copySize;

    uint32_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));

    uint32_t next_size = GET_SIZE(HDRP(NEXT_BLKP(ptr)));

    uint32_t curr_size = GET_SIZE(HDRP(ptr));
    uint32_t combine_size = curr_size + next_size;
    uint32_t asize = size + DSIZE;

    if (curr_size > asize)
    {
        return ptr;
    }

    if (!next_alloc && combine_size >= asize)
    {
        remove_freenode(NEXT_BLKP(ptr));
        PUT(HDRP(ptr), PACK(combine_size, 1));
        PUT(FTRP(ptr), PACK(combine_size, 1));

        return ptr;
    }

    newp = mm_malloc(size);
    if (newp == NULL)
    {
        printf("ERROR: mm_malloc failed in mm_realloc\n");
        exit(1);
    }
    copySize = GET_SIZE(HDRP(ptr));
    if (size < copySize)
    {
        copySize = size;
    }
    memcpy(newp, ptr, copySize);
    mm_free(ptr);
    return newp;
}

void mm_checkheap(int verbose)
{
    //
    // This provided implementation assumes you're using the structure
    // of the sample solution in the text. If not, omit this code
    // and provide your own mm_checkheap
    //
    void *bp = heap_listp;

    if (verbose)
    {
        printf("Heap (%p):\n", heap_listp);
    }

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
    {
        printf("Bad prologue header\n");
    }
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (verbose)
        {
            printblock(bp);
        }
        checkblock(bp);
    }

    if (verbose)
    {
        printblock(bp);
    }

    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
    {
        printf("Bad epilogue header\n");
    }
}

static void traverse_freelist(node_t *node)
{
    while (node)
    {
        printf("Free block with pointer: %p", node);
        node = node->next;
    }
}

static void printblock(void *bp)
{
    uint32_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));

    if (hsize == 0)
    {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n",
           bp,
           (int)hsize, (halloc ? 'a' : 'f'),
           (int)fsize, (falloc ? 'a' : 'f'));
}

static void checkblock(void *bp)
{
    if ((uintptr_t)bp % 8)
    {
        printf("Error: %p is not doubleword aligned\n", bp);
    }
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
    {
        printf("Error: header does not match footer\n");
    }
}