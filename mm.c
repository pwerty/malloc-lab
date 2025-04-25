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
    "VILLIAN_KWON",
    /* First member's full name */
    "kwon woo hyeon",
    /* First member's email address */
    "pwertyman@naver.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* Basic constants and macros */
#define WSIZE 4 /* 워드와 푸터의 사이즈, 바이트 단위 */
#define DSIZE 8 /* 더블 워드 사이즈 */
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

/* Given block pte bp, compute address of its header and footer */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))



/* single word (4) or double word (8) alignment */
#define ALIGNMENT (WSIZE * 2) /* 기존엔 명시 8이었으나 WSIZE에 의존적으로 전환 */
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

void * heap_listp;
// extend_heap이 호출되는 경로 두 가지
    // 1. 힙이 초기화 되는 경우
    // 2. mm_malloc이 적당한 fit을 찾지 못한 경우
static void *extend_heap(size_t words)
{
    char *ptr;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    // 사이즈는 짝수인지 아닌지에 따라 배정되는 값이 조금 다르다 :
        // 짝수인경우 : words 에 WSIZE를 곱한만큼 배정한다.
        // 홀수인경우 : words + 1 에 WSIZE를 곱한만큼 배정한다.
    if ((long) (ptr = mem_sbrk(size)) == -1)
        return NULL;
    // 방금 계산한 size를 sbrk에 때린다. 그래서 결과가 구리면 여기서 즉시 종료.
    // ptr은 여기서 배정이 끝났다.

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(ptr), PACK(size, 0));
    // ptr의 Header 부분에서 값 배정 시도 : 물론 할당 된 것은 아님
    PUT(FTRP(ptr), PACK(size, 0));
    // ptr의 Footer 부분에서 값 배정 시도 : 위와 같이, 할당 된 것은 아님
    PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1));
    // 다음 블럭의 헤드에 뭔가를 배정하네? 이게 뭐임?

    return coalence(ptr);
}
/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* 텅 비어있는 힙을 생성할 것이다!!!*/
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *) - 1)
        return -1;
    // mem_sbrk에서 상태가 꼬롬하게 되어버리면 (void*) -1을 뱉는다.
    // 즉 실패 플래그를 감지하는 조건문

    PUT(heap_listp, 0); // Alignment padding
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 Header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 Footer
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1)); // 에필로그 Header
    heap_listp += (2 * WSIZE); 


    // 초기 초기화 루틴을 CHUNKSIZE / WSIZE 만큼 확장 시도를 한다.
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/* coalesce : 경계 태그 연결을 사용하여 상수 시간에 인접 가용 블록들과 통합.*/
static void *coalence(void *ptr)
{
    // 경계 태그라는 개념을 코드에 반영..!! 이 내용은 번역본 820p에 있다.

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr)));
    // ptr이 대상이었으니, ptr의 이전 칸에서의 끝을 봐야한다. Footer Ptr에서 Alloc 여부를 확인한다.
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    // ptr이 대상이었으니, ptr의 우측 칸에서의 시작점을 본다. Header Ptr에서 Alloc 여부를 확인한다.
    size_t size = GET_SIZE(HDRP(ptr));
    // ptr에 대한 Header Ptr 기반으로 Size를 얻기 위해 시도하기.

    if (prev_alloc && next_alloc)
        return ptr; // 케이스 1번, 이전과 다음 모두 할당된 경우
    else if (prev_alloc && !next_alloc)
    { // 케이스 2번, 이전 블록은 할당 상태, 이후는 가용 상태이다.
        // | 사용 중!|| ptr || FREE |
        //           | TARGET HERE |
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        // 여기서 size를 조정한다.
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
        // 그리고 Header, Footer에 대해 모두 Pack(size)를 적용한다.
    }
    else if (!prev_alloc && next_alloc)
    { // 케이스 3번, 이전 블록은 가용 상태, 다음 블록은 할당 상태이다.
        // | FREE || ptr || 사용 중!|
        // | TARGET HERE |
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))); // size 조정

        PUT(FTRP(ptr), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
        // ptr은 묶어둔 FREE 데이터 전체의 처음을 가리켜야한다. 그래서 ptr의 위치가 수정된다.
        // Case 2의 경우에는 ptr의 위치 자체는 유지되어도 괜찮다는 것을 알 수 있다!
    }
    else
    { // 케이스 4번, 둘 다 가용 상태이다.
        // | FREE || ptr || FREE |
        // |     TARGET HERE     |
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) +
        GET_SIZE(FTRP(NEXT_BLKP(ptr)));
        // 종합적인 사이즈가 늘어나게 됨

        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        // ptr header를 가리키던 것을 좌측 FREE 되어있는쪽으로 보냄
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
        // ptr footer를 가리키던 포인터를 우측 footer로 보냄
        ptr = PREV_BLKP(ptr);
        // ptr은 묶어둔 FREE 데이터 전체의 처음을 가리켜야한다. 그래서 ptr의 위치가 수정된다.
    }
    return ptr;
}


static void *find_fit(size_t asize)
{
    void *ptr;

}

static void place(void *ptr, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(ptr));
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendSize;
    char *ptr;

    // 이상한 배정 차단
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignmend reqs. */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE); 
    // size가 얼마 들어오냐에 따라 asize가 영향을 받게 된다.
    // 작거나 같아도 최소 두 배의 계수가 배정되고, else 로 빠지면 2배가 초과된만큼 배정됨.

    /* Search the free list for a fit */
    if ((ptr = find_fit(asize)) != NULL)
    {
        place(ptr, asize);
        return ptr;
    }

    extendSize = MAX(asize, CHUNKSIZE);
    if ((ptr = extend_heap(extendSize/WSIZE)) == NULL)
        return NULL;
    // ptr이 똑바로 배정받지 못하면 여기서 코드 진행을 끊어야한다!!
    place(ptr, asize);
    return ptr;

}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalense(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}














