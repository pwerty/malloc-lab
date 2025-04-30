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
    "VILLIAN_KWON v2",
    /* First member's full name */
    "kwon woo hyeon",
    /* First member's email address */
    "pwertyman@naver.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

static void *coalence(void *ptr);
static void *extend_heap(size_t words);
void add_freeList(void *bp);
void remove_freeList(void *bp);

/* Basic constants and macros */
#define WSIZE 8 /* 워드와 푸터의 사이즈, 바이트 단위 */
#define DSIZE 16 /* 더블 워드 사이즈 */
// 이새끼 왜 바꿔야함?

#define CHUNKSIZE (1<<12)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word
크기와 할당 비트를 통합해서 헤더와 푸터에 저장 할 수 있는 값을 리턴한다*/
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int*)(p) = (val))

/* Read the size and allocated fields form address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
// ~0x7은 맨 우측의 3비트를 빼고 나머지 내용을 보겠다는 것.
#define GET_ALLOC(p) (GET(p) & 0x1)
// 0x1은 맨 우측의 1비트만 보겠다는 것.

/* bp : block pointer의 정의 */
// 기존 묵시적 리스트 방법
// |Header|CONTENTS|Footer|
//        |bp here|

// |Header|PrevAdd|NextAdd|CONTENTS|Footer|
// |                      |bp here|

/* Given block pte bp, compute address of its header and footer */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
// #define HDRP(bp)  ((char *)(bp) - (WSIZE + (DSIZE * 2)))
// #define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - (2*WSIZE + 2*DSIZE))

/* For Use. 실제 값을 읽거나 쓸 때는 여기를 쓰기! */
#define PREV_FREE(bp) (*(void **)(bp))
#define NEXT_FREE(bp) (*(void **)((char *)(bp) + WSIZE))

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))



/* single word (4) or double word (8) alignment */
#define ALIGNMENT (WSIZE * 2) /* 기존엔 명시 8이었으나 WSIZE에 의존적으로 전환 */
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

void* heap_listp;
void* freeList_str = NULL; // 이는 즉시 첫 bp로 매핑

static void* coalence(void *ptr)
{ // np
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));

    if (prev_alloc && next_alloc)
    {
        add_freeList(ptr);
        return ptr;
    }
    else if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        remove_freeList(NEXT_BLKP(ptr));
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
        remove_freeList(PREV_BLKP(ptr));
        PUT(FTRP(ptr), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    }
    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) +
        GET_SIZE(FTRP(NEXT_BLKP(ptr)));
        remove_freeList(PREV_BLKP(ptr));
        remove_freeList(NEXT_BLKP(ptr));

        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    }
    add_freeList(ptr);
    return ptr;
}

static void *extend_heap(size_t words)
{ // np
    char *ptr;
    size_t size;
    size = (words % 2) ? (words + 1) * WSIZE : words * (WSIZE);
    if ((long) (ptr = mem_sbrk(size)) == -1)
        return NULL;
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1));
    return coalence(ptr);
}

int mm_init(void)
{    // np
    if ((heap_listp = mem_sbrk(8 * WSIZE)) == (void *) - 1)
        return -1;
    PUT(heap_listp, 0); // Alignment padding
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 Header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 Footer
    PUT(heap_listp + (3 * WSIZE), PACK(2 * DSIZE, 0));
    PUT(heap_listp + (4 * WSIZE), NULL);
    PUT(heap_listp + (5 * WSIZE), NULL);
    PUT(heap_listp + (6 * WSIZE), PACK(2 * DSIZE, 0));
    PUT(heap_listp + (7 * WSIZE), PACK(0, 1));
    heap_listp += (4 * WSIZE); 

    // 초기 초기화 루틴을 CHUNKSIZE / WSIZE 만큼 확장 시도를 한다.
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

static void *find_fit(size_t asize)
{   // np?
    void *ptr;
    for(ptr = freeList_str; ptr != NULL; ptr = NEXT_FREE(ptr))
    {
        if(asize <= GET_SIZE(HDRP(ptr)))
            return ptr;
    }
    return NULL;
}

static void place(void *ptr, size_t asize)
{  // np
    size_t csize = GET_SIZE(HDRP(ptr));

    // 옵션으로 초과 부분을 분할하는 역할
    if((csize - asize) >= (2 *DSIZE))
    {
        PUT(HDRP(ptr), PACK(asize, 1));
        PUT(FTRP(ptr), PACK(asize, 1));
        remove_freeList(ptr);
        ptr = NEXT_BLKP(ptr);
        PUT(HDRP(ptr), PACK(csize - asize, 0));
        PUT(FTRP(ptr), PACK(csize - asize, 0));
        add_freeList(ptr);
    } 
    else
    {
        PUT(HDRP(ptr), PACK(csize, 1));
        PUT(FTRP(ptr), PACK(csize, 1));
        remove_freeList(ptr);
    }
    
}
void *mm_malloc(size_t size)
{ // np
    size_t asize;
    size_t extendSize;
    char *ptr;

    // 이상한 배정 차단
    if (size == 0)
        return NULL;

    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE); 

    if ((ptr = find_fit(asize)) != NULL)
    {
        place(ptr, asize);
        return ptr;
    }

    extendSize = MAX(asize, CHUNKSIZE);
    if ((ptr = extend_heap(extendSize/WSIZE)) == NULL)
        return NULL;
    place(ptr, asize);
    return ptr;

}


void mm_free(void *ptr)
{ // np
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalence(ptr);
}

void relist(void *bps){
    // np
    void *bp = bps;
    while (GET_SIZE(HDRP(bp)) > 0)
    {
        if (!GET_ALLOC(HDRP(bp))) 
            add_freeList(bp);                                         
        bp = NEXT_BLKP(bp);                                        
    }
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{  
    // np
    int re = 0;

    if (ptr == NULL) // 포인터가 NULL인 경우 할당만 수행
    return mm_malloc(size);

if (size <= 0) // size가 0인 경우 메모리 반환만 수행
{
    mm_free(ptr);
    return 0;
}

    
void *newptr = mm_malloc(size); // 새로 할당한 블록의 포인터
if (newptr == NULL)
    return NULL; 

size_t copySize = GET_SIZE(HDRP(ptr)) - DSIZE; 
if (size < copySize){
    copySize = size;
    re = 1;
}                           
                              

memcpy(newptr, ptr, copySize); // 새 블록으로 데이터 복사
//명시적 리스트의 수정이 필요함
if(re){
    freeList_str = NULL;
    relist(newptr);
}
    /* 기존 블록 반환 */
mm_free(ptr);
return newptr;
}

void add_freeList(void *bp)
{
    NEXT_FREE(bp) = freeList_str;
    PREV_FREE(bp) = NULL;

    if (freeList_str != NULL)
        PREV_FREE(freeList_str) = bp;
    freeList_str = bp;
}

void remove_freeList(void *bp)
{
    void *prev = PREV_FREE(bp);
    void *next = NEXT_FREE(bp);

    if(prev != NULL)
        NEXT_FREE(prev) = next;
    else
        freeList_str = next;

    if (next != NULL)
        PREV_FREE(next) = prev;
}