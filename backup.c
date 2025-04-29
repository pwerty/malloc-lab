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
    "VILLIAN_KWON v3",
    /* First member's full name */
    "kwon woo hyeon",
    /* First member's email address */
    "pwertyman@naver.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

static void *coalesce(void *ptr);
static void *extend_heap(size_t words);
void add_freeList(void *bp, void **targetList);
void remove_freeList(void *bp, void **targetList);


void** getListPointer(int idx);
int find_size_class_index(size_t size);
#define MAX_SIZE_CLASS 7

/* Basic constants and macros */
#define WSIZE 8 /* 워드와 푸터의 사이즈, 바이트 단위 */
#define DSIZE 16 /* 더블 워드 사이즈 */
#define CHUNKSIZE (1<<12)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int*)(p) = (val))

/* Read the size and allocated fields form address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
// ~0x7은 맨 우측의 3비트를 빼고 나머지 내용을 보겠다는 것.
#define GET_ALLOC(p) (GET(p) & 0x1)
// 0x1은 맨 우측의 1비트만 보겠다는 것.

#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define PREV_FREE(bp) (*(void **)(bp))
#define NEXT_FREE(bp) (*(void **)((char *)(bp) + WSIZE))

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))



/* single word (4) or double word (8) alignment */
#define ALIGNMENT (WSIZE * 2)
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

void* heap_listp;
void* freeList0 = NULL;
void* freeList1 = NULL;
void* freeList2 = NULL;
void* freeList3 = NULL;
void* freeList4 = NULL;
void* freeList5 = NULL;
void* freeList6 = NULL;
void* freeList7 = NULL;

static void* coalesce(void *ptr)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));
    void **targetList = NULL;
    int pos;

    if (prev_alloc && next_alloc)
    {
        pos = find_size_class_index(size);
        targetList = getListPointer(pos);

        add_freeList(ptr, targetList);
        return ptr;
    }
    else if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        pos = find_size_class_index(GET_SIZE(HDRP(NEXT_BLKP(ptr))));
        targetList = getListPointer(pos);

        remove_freeList(NEXT_BLKP(ptr), targetList);
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc)
    {
        // 여기 Footer Header 상태가 이상한데.. 확인 필요
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
        pos = find_size_class_index(GET_SIZE(HDRP(PREV_BLKP(ptr))));
        targetList = getListPointer(pos);

        remove_freeList(PREV_BLKP(ptr), targetList);
        PUT(FTRP(ptr), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    }
    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) +
        GET_SIZE(FTRP(NEXT_BLKP(ptr)));

        pos = find_size_class_index(GET_SIZE(HDRP(PREV_BLKP(ptr))));
        targetList = getListPointer(pos);
        remove_freeList(PREV_BLKP(ptr), targetList);

        pos = find_size_class_index(GET_SIZE(FTRP(NEXT_BLKP(ptr))));
        targetList = getListPointer(pos);
        remove_freeList(NEXT_BLKP(ptr), targetList);
        
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    }

    pos = find_size_class_index(size);
    targetList = getListPointer(pos);
    add_freeList(ptr, targetList);

    return ptr;
}

static void *extend_heap(size_t words)
{
    char *ptr;
    size_t size;
    size = (words % 2) ? (words + 1) * WSIZE : words * (WSIZE);
    if ((long) (ptr = mem_sbrk(size)) == -1)
        return NULL;
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1));
    return coalesce(ptr);
}

int mm_init(void)
{    // np
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *) - 1)
        return -1;
    PUT(heap_listp, 0); // Alignment padding
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 Header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 Footer
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
    heap_listp += (2 * WSIZE); 

    // 초기 초기화 루틴을 CHUNKSIZE / WSIZE 만큼 확장 시도를 한다.
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

static void *find_fit(size_t asize)
{
    int class_idx = find_size_class_index(asize);
    void *bp;

    // class_idx 부터 MAX_SIZE_CLASS까지 차례대로 탐색
    for (; class_idx <= MAX_SIZE_CLASS; class_idx++) {
        // 헤드 포인터의 주소를 얻고
        void **listp = getListPointer(class_idx);
        // 그 안의 값(실제 리스트 헤드)을 꺼내서
        for (bp = *listp; bp != NULL; bp = NEXT_FREE(bp)) {
            if (asize <= GET_SIZE(HDRP(bp)))
                return bp;
        }
    }
    return NULL;  // 못 찾으면 NULL
}

static void place(void *ptr, size_t asize)
{ 
    size_t csize = GET_SIZE(HDRP(ptr));
    int pos = find_size_class_index(csize);
    void **targetList = getListPointer(pos);

    if((csize - asize) >= (2 *DSIZE))
    {
        PUT(HDRP(ptr), PACK(asize, 1));
        PUT(FTRP(ptr), PACK(asize, 1));
        remove_freeList(ptr, targetList);

        ptr = NEXT_BLKP(ptr);

        pos = find_size_class_index(csize - asize);
        targetList = getListPointer(pos);
        PUT(HDRP(ptr), PACK(csize - asize, 0));
        PUT(FTRP(ptr), PACK(csize - asize, 0));
        add_freeList(ptr, targetList);
    } 
    else
    {
        PUT(HDRP(ptr), PACK(csize, 1));
        PUT(FTRP(ptr), PACK(csize, 1));
        remove_freeList(ptr, targetList);
    }
    
}

void *mm_malloc(size_t size)
{ // np
    size_t asize;
    size_t extendSize;
    char *ptr;

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
{
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

void relist(void *bps){
    void *bp = bps;
    void **targetList = getListPointer(find_size_class_index(GET_SIZE(HDRP(bp))));
        while (GET_SIZE(HDRP(bp)) > 0)
    {
        if (!GET_ALLOC(HDRP(bp))) 
            add_freeList(bp, targetList);                                         
        bp = NEXT_BLKP(bp);                                        
    }
}

void *mm_realloc(void *ptr, size_t size)
{ 
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

if(re){
    freeList0 = NULL;
    freeList1 = NULL;
    freeList2 = NULL;
    freeList3 = NULL;
    freeList4 = NULL;
    freeList5 = NULL;
    freeList6 = NULL;
    freeList7 = NULL;
    relist(newptr);
} 
    mm_free(ptr);
    return newptr;

}

void add_freeList(void *bp, void **targetList)
{
    
    NEXT_FREE(bp) = *targetList;
    PREV_FREE(bp) = NULL;

    if (*targetList != NULL)
    {
        PREV_FREE(*targetList) = bp;
        *targetList = bp;
    }

}

void remove_freeList(void *bp, void** targetList)
{
    void *prev = PREV_FREE(bp);
    void *next = NEXT_FREE(bp);

    if(prev != NULL)
        NEXT_FREE(prev) = next;
    else
        *targetList = next;

    if (next != NULL)
        PREV_FREE(next) = prev;

}



void **getListPointer(int idx)
{
    switch(idx)
    {
        case 0:
            return &freeList0;
        case 1:
            return &freeList1;
        case 2:
            return &freeList2;
        case 3:
            return &freeList3;
        case 4:
            return &freeList4;
        case 5:
            return &freeList5;
        case 6:
            return &freeList6;
        case 7:
            return &freeList7;
        default:   
            return NULL;
    }
}

int find_size_class_index(size_t size)
{
    if (size <= 24) return 0;
    else if (size <= 48) return 1;
    else if (size <= 96) return 2;
    else if (size <= 192) return 3;
    else if (size <= 384) return 4;
    else if (size <= 768) return 5;
    else if (size <= 1536) return 6;
    else return 7;
}