/*
 * Dynamic memory allocation with implicit list method
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
    "LEE BYUNGHO",
    /* First member's email address */
    "healer0607@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* Run checkheap if DEBUG is defined */
// #define DEBUG

#ifdef DEBUG
#define CHECKHEAP(lineno) printf("%s\n", __func__); mm_checkheap(lineno);
#else
#define CHECKHEAP(lineno)
#endif

/* Basic constants and macros */
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at addpress p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Given block ptr bp, compute address of predecessor and successor blocks */
#define PRED(bp) (*(void **)(bp))
#define SUCC(bp) (*((void **)((char *)(bp) + WSIZE)))

/* Set predecessor and successor block of given bp */
#define SET_PRED(bp, ptr) (PRED(bp) = ptr)
#define SET_SUCC(bp, ptr) (SUCC(bp) = ptr)

static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
void mm_checkheap(int lineno);
static void checkblock(void *bp);
static void checkheap(int verbose);
static void list_in(void *bp);
static void list_out(void *bp);

/* First block pointer */
static char *heap_listp = 0;

/* Free list head pointer */
static char *free_listp = NULL;

static void list_in(void *bp)
{
	SET_PRED(bp, NULL);
	SET_SUCC(bp ,free_listp);
	if (free_listp != NULL) {
		SET_PRED(free_listp, bp);
	}

	free_listp = bp;
}

static void list_out(void *bp)
{
	if (SUCC(bp) != NULL) {
		SET_PRED(SUCC(bp), PRED(bp));
	}
	if (PRED(bp) != NULL) {
		SET_SUCC(PRED(bp), SUCC(bp));
	}
	else
	{
		free_listp = SUCC(bp);
	}
}

/* 
 * mm_init - initialize the malloc package.
 */
static void *extend_heap(size_t words)
{
	char *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment */
	size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
	if ((long)(bp = mem_sbrk(size)) == -1)
		return NULL;

	/* Initialize free block header/footer and the epilogue header */
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

	/* Coalesce if the previous block was free */
	bp = coalesce(bp);

	CHECKHEAP(__LINE__);

	return bp;
}

int mm_init(void)
{
	char *bp;

	/* Create the initial empty heap */
	if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
		return -1;
	PUT(heap_listp, 0);
	PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
	PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
	PUT(heap_listp + (3*WSIZE), PACK(0, 1));
	heap_listp += (2*WSIZE);
	free_listp = NULL;

	/* Extend the empty heap with a free block of CHUNKSIZE byte */
	bp = extend_heap(CHUNKSIZE/WSIZE);
	if (bp == NULL)
		return -1;

	CHECKHEAP(__LINE__);

	return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
static void *find_fit(size_t asize)
{
	/* First-fit search */
	void *bp;

	for (bp = free_listp; bp != NULL; bp = SUCC(bp)) {
		if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
			return bp;
		}
	}
	return NULL;
}

static void place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));

	list_out(bp);

	if ((csize - asize) >= (2*DSIZE)) {
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize-asize, 0));
		PUT(FTRP(bp), PACK(csize-asize, 0));
		
		coalesce(bp);
	}
	else {
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
	}
}

void *mm_malloc(size_t size)
{
    size_t asize;
	size_t extendsize;
	char *bp;

	/* Initialize heap if heap is empty */
	if (heap_listp == 0) {
		mm_init();
	}

	/* Ignore spurious requests */
	if (size == 0)
		return NULL;

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)
		asize = 2*DSIZE;
	else
		asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

	/* Search the free list for a fit */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);

		CHECKHEAP(__LINE__);
		return bp;
	}

	/* No fit found. Get more memory and place the block */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
		return NULL;
	place(bp, asize);

	CHECKHEAP(__LINE__);

	return bp;
}

/*
 * mm_free
 */
static void *coalesce(void *bp)
{
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));

	if (prev_alloc && next_alloc) {
		list_in(bp);
		return bp;
	}

	else if (prev_alloc && !next_alloc) {
		list_out(NEXT_BLKP(bp));

		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	}

	else if (!prev_alloc && next_alloc) {
		list_out(PREV_BLKP(bp));

		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}

	else {
		list_out(NEXT_BLKP(bp));
		list_out(PREV_BLKP(bp));

		size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
			GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}

	list_in(bp);

	CHECKHEAP(__LINE__);

	return bp;
}

void mm_free(void *bp)
{
	/* Free can't free first block */
	if (bp == 0)
		return;

	size_t size = GET_SIZE(HDRP(bp));

	/* Initialize heap if heap is empty */
	if (heap_listp == 0) {
		mm_init();
	}

	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	coalesce(bp);

	CHECKHEAP(__LINE__);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    size_t oldsize;
	void *newptr;

	/* If oldptr is NULL, then this is just malloc. */
	if (ptr == NULL) {
		return mm_malloc(size);
	}

	newptr = mm_malloc(size);

	/* If realloc() fails the original block is left untouched */
	if (!newptr) {
		return 0;
	}

	/* Copy the old data. */
	oldsize = GET_SIZE(HDRP(ptr));
	if (size < oldsize)
		oldsize = size;
	memcpy(newptr, ptr, oldsize);

	/* Free the old block. */
	mm_free(ptr);

	CHECKHEAP(__LINE__);
	
	return newptr;
}

void mm_checkheap(int lineno)
{
	checkheap(0);
}

static void checkblock(void *bp)
{
	/* Check payload area is aligned */
	if ((size_t)bp % 8)
		printf("Error: %p is not doubleword aligned\n", bp);

	/* Check header and footer match */
	if (!(GET_ALLOC(HDRP(bp))) && (GET(HDRP(bp)) != GET(FTRP(bp)))) {
		printf("Error : head does not match footer\n");
	}

	/* Check contiguous free blocks */
	if (!(GET_ALLOC(HDRP(bp))) && !(GET_ALLOC(HDRP(NEXT_BLKP(bp))))) {
		printf("Error : contiguous free blocks\n");
	}
}

/*
 * checkheap - check of the heap for consistency
 */
static void checkheap(int verbose)
{
	char *bp = heap_listp;
	char *dbp = free_listp;

	if (verbose)
		printf("Heap (%p):\n", heap_listp);

	int count_all = 0;
	int count_free = 0;

	/* Check prologue block size and status */
	if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header\n");
	
	/* Check blocks in explicit list */
	int i = 1;
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		// printf("block no.%d\n", i);
		checkblock(bp);

		/* Count all free blocks in heap */
		if (!(GET_ALLOC(HDRP(bp))))
			count_all += 1;
		
		i++;
	}

	/* Check epilogue block size and status */
	if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
		printf("Bad epilogue header\n");

	/* Check list level invariants */
	int j = 1;
	for (bp = free_listp; bp != NULL; bp = SUCC(bp)) {
		// printf("free block no.%d\n", j);

		/* Check no cycle in the list */
		for (int k = 0; ((k < 2) && (dbp != NULL)); k++) {
			dbp = SUCC(dbp);
		}

		if ((dbp != NULL) && (dbp == bp)) {
			printf("Cycle is in free list\n");
			break;
		}

		/* Check free list contains no allocated blocks */
		if (!GET_ALLOC(HDRP(bp))) {
			/* Count all free blocks in free list */
			count_free += 1;

			/* Check next/prev ptr in consecutive free blocks are consistent */
			if ((SUCC(bp) != NULL) && (bp != PRED(SUCC(bp)))) {
				printf("Consecutive free blocks are inconsistent\n");
			}
		}
		else {
			printf("Allocated block is contained in free list\n");
		}
		j++;
	}

	/* Check all free blocks are in the free list */
	if (count_all > count_free) {
		printf("Free block not in free list exists %d\n", (count_all - count_free));
	}
	
}









