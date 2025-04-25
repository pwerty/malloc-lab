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
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
#define WSIZE 4 //header와 footer의 크기
#define DSIZE 8
#define CHUNKSIZE (1<<12)
#define PACK(size,alloc) ((size) | (alloc))
#define GET(p) (*(unsigned int*)(p))
#define PUT(p,val) (*(unsigned int*)(p) = (val))
#define MAX(x,y) ((x)>(y)?(x):(y))
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp)+GET_SIZE(HDRP(bp))-DSIZE)
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(((char *) (bp) - WSIZE)))
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(((char *) (bp) - DSIZE)))
/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
void *heap_listp;
/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    //주소가 -1 = 일어날수 없는 일
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void*)-1)
        return -1;
    PUT(heap_listp,0);
    PUT(heap_listp + (1*WSIZE),PACK(DSIZE,1));
    PUT(heap_listp + (2*WSIZE),PACK(DSIZE,1));
    PUT(heap_listp + (3*WSIZE),PACK(0,1));
    heap_listp += (2*WSIZE);
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}
static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    size = (words % 2) ? (words+1)*WSIZE : words*(WSIZE);
    if((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    PUT(HDRP(bp),PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1));

    return coalesce(bp);
}
static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    if(prev_alloc && next_alloc){//앞뒤로 다 할당되어있음
        return bp;
    }
    else if(prev_alloc&& !next_alloc){//뒤에는 가용가능
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));//크기를 합치고
        PUT(HDRP(bp),PACK(size,0));
        PUT(FTRP(bp),PACK(size,0));
    }
    else if(!prev_alloc&& next_alloc){//앞에가 사용가능
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp),PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    else{
        size+=GET_SIZE(HDRP(PREV_BLKP(bp)))+GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}
/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *find_fit(size_t asize){//적당한 크기 찾기
    void *bp = mem_heap_lo() + 2 * WSIZE;
    while (GET_SIZE(HDRP(bp)) > 0)
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) 
            return bp;                                             
        bp = NEXT_BLKP(bp);                                        
    }
    return NULL;
}
void place(void* pp,size_t size){//만약 남는부분이 최소크기 보다 작은지 아닌지 판단하고 분할
    size_t csize = GET_SIZE(HDRP(pp));
    if((csize - size) >= (2*DSIZE)){
        PUT(HDRP(pp),PACK(size,1));
        PUT(FTRP(pp),PACK(size,1));
        pp = NEXT_BLKP(pp);
        PUT(HDRP(pp),PACK((csize-size),0));
        PUT(FTRP(pp),PACK((csize-size),0));
    }else{
        PUT(HDRP(pp),PACK(csize,1));
        PUT(FTRP(pp),PACK(csize,1));
        
    }

}
void *mm_malloc(size_t size)
{
    size_t asize;      // 조정된 블록 사이즈
    size_t extendsize; // 확장할 사이즈
    char *bp;

    // 잘못된 요청 분기
    if (size == 0)
        return NULL;

        /* 사이즈 조정 */
    if (size <= DSIZE)     // 8바이트 이하이면
        asize = 2 * DSIZE; // 최소 블록 크기 16바이트 할당 
    else
        asize = DSIZE * ((size + DSIZE + DSIZE - 1) / DSIZE); 

        /* 가용 블록 검색 */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize); // 할당
        return bp;        // 새로 할당된 블록의 포인터 리턴
    }

    /* 적합한 블록이 없을 경우 힙확장 */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}
/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr),PACK(size,0));
    PUT(FTRP(ptr),PACK(size,0));
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    // void *oldptr = ptr;
    // void *newptr;
    // size_t copySize;
    
    // // newptr = mm_malloc(size);
    // // if (newptr == NULL)
    // //   return NULL;
    // // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    // // if (size < copySize)
    // //   copySize = size;
    // // memcpy(newptr, oldptr, copySize);
    // // mm_free(oldptr);
    // // return newptr;
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
    if (size < copySize)                           
        copySize = size;                          

    memcpy(newptr, ptr, copySize); // 새 블록으로 데이터 복사

        /* 기존 블록 반환 */
    mm_free(ptr);

    return newptr;
}
