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
    "VILLIAN_KWON v4",
    /* First member's full name */
    "kwon woo hyeon",
    /* First member's email address */
    "pwertyman@naver.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/*
 1차 시도. 
    * 이 코드는 WSIZE 4에서만 작동을 보장해야한다.
    * coalesce 함수를 보다 확실히 하기 위해 prev/next block을 사전 선언 하였다.
        * 여기서 매크로 GET_TOTAL_SIZE 추가 되었다. 헤더 푸더 합친 진짜 블록 크기 계산이 필요했다.
    * Free List Remove 함수를 보다 의도에 맞게 수정.
        * remove 하고자하는 아이템에 대한 안전 장치로, remove 자체에서 주소를 조회하도록 수정
    * 새 문제점.. Segregate #1에서 내가 find fit에서 remove를 안했던가? Place에서 제거하도록 되어있을텐데..
    * add Freelist에 대한 분기문에 대해 더 많은 상황을 수용 할 수 있도록 개선
    * mm_init에서 free List에 대해 초기화 수행하도록 개선
    * coalesce의 기능을 축소하고 함수 역할 분리
    * 매크로가 전체적으로 바뀌면서 Header의 직접 가리키는 내용을 제거하되, Header 포인터를 별도로 다룰 여지를 남김
*/

static void *coalesce(void *ptr);
static void *extend_heap(size_t words);
static void add_freeList(char **bp);
static void remove_freeList(char **bp);


void** getListPointer(int idx);
static size_t sizeWizard(size_t size);
#define MAX_SIZE_CLASS 7
#define MAX_POWER 50

#define STATUS_BIT_SIZE 3 // bits
#define HDR_SIZE 1 // in words
#define FTR_SIZE 1 // in words
#define PRED_FIELD_SIZE 1 // in words
#define EPILOG_SIZE 2 // in words

/* Basic constants and macros */
#define WSIZE 4 /* 워드와 푸터의 사이즈, 바이트 단위 */
#define DSIZE 8 /* 더블 워드 사이즈 */
#define CHUNKSIZE (1<<12/WSIZE)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc))
#define GET_BYTE(p) (*(char *)(p))
#define GET_WORD(p) (*(unsigned int *)(p))
#define PUT_WORD(p, val) (*(char **)(p) = (val))

/* Read the size and allocated fields form address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
// ~0x7은 맨 우측의 3비트를 빼고 나머지 내용을 보겠다는 것.
#define GET_ALLOC(p) (GET(p) & 0x1)
// 0x1은 맨 우측의 1비트만 보겠다는 것.

#define GET_TOTAL_SIZE(p) (GET_SIZE(p) + (WSIZE / 2))

// Footer만 사용
#define FTRP(headp) ((char **)(headp) + GET_SIZE(headp) + HDR_SIZE)

// FREE LIST 단위의 전 후 블럭에 대한 정보를 가져오는 매크로 4셋.
#define GET_PTR_PRED(ptr) ((char **)(ptr) + HDR_SIZE)
#define GET_PTR_SUCC(ptr) ((char **)(ptr) + HDR_SIZE + PRED_FIELD_SIZE)

#define PREV_FREE(bp) (*(GET_PTR_PRED(bp)))
#define NEXT_FREE(bp) (*(GET_PTR_SUCC(bp)))

// 힙 상에 있는 블록에 대해 조회하는 함수.
#define PREV_BLKP(bp) ((char **)(bp) - GET_TOTAL_SIZE(((char **)(bp) - FTR_SIZE)))
#define NEXT_BLKP(bp) (FTRP(bp) + FTR_SIZE)

// GET : i번째에 있는 freeList 리턴, 즉 얘는 일종의 index selector를 주소단위로 수행하는 것이다.
// SET : GET과 비슷한 계산을 때리지만 이건 값이 직접 변경된다는 점에서 놀랄만 하다.
#define GET_FREELIST_PTR(i) (*(freeLists+i))
#define SET_FREELIST_PTR(i, ptr) (*(freeLists+i) = ptr)

// 가용 리스트에 있는 블록들에 대해 prev, next를 SET 하는 함수
#define SET_PTR(p, ptr) (*(char **)(p) = (char *)(ptr))

#define EVENIZE(x) ((x + 1) & ~1)
/* single word (4) or double word (8) alignment */
#define ALIGNMENT (WSIZE * 2)
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

static char **freeLists;
static char **heapPtr;

static void* coalesce(void *ptr)
{
    // 여기의 *ptr은 header를 가리키는가?
    void ** prev_block = PREV_BLKP(ptr);
    void ** next_block = NEXT_BLKP(ptr);
    size_t prev_alloc = GET_ALLOC(prev_block);
    size_t next_alloc = GET_ALLOC(next_block);
    size_t size = GET_SIZE(ptr);

    if (prev_alloc && next_alloc)
    {
        return ptr;
    }
    else if (prev_alloc && !next_alloc)
    {
        remove_freeList(next_block);
        size += GET_TOTAL_SIZE(next_block);

        PUT_WORD(ptr, PACK(size, 0));
        PUT_WORD(FTRP(ptr), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc)
    {
        remove_freeList(prev_block);
        size += GET_TOTAL_SIZE(prev_block);

        PUT_WORD(prev_block, PACK(size, 0 ));
        PUT_WORD(FTRP(ptr), PACK(size, 0));
        ptr = prev_block;
    }
    else
    {
        remove_freeList(prev_block);
        remove_freeList(next_block);
        size += (GET_TOTAL_SIZE(prev_block) + GET_TOTAL_SIZE(next_block));
 
        PUT_WORD(prev_block, PACK(size, 0));
        PUT_WORD(FTRP(next_block), PACK(size, 0));
        ptr = prev_block;
    }
    return ptr;
}

static void *extend_heap(size_t words)
{
    char **ptr;
    char **end_ptr;
    size_t words_extend = EVENIZE(words); // make sure double aligned
    size_t total_words = words_extend + HDR_SIZE + FTR_SIZE;
    // 여기가 그 람다 식 대신 부여된 내용이구나?
    if ((long)(ptr = mem_sbrk((total_words) * WSIZE)) == -1) {
        return NULL;
    }

    ptr -= EPILOG_SIZE;

    // set new block header/footer to size (in words)
    PUT_WORD(ptr, PACK(words_extend, 0));
    PUT_WORD(FTRP(ptr), PACK(words_extend, 0));
    
    // add epilog to the end
    end_ptr = ptr + total_words;
    PUT_WORD(end_ptr, PACK(0, 1));
    PUT_WORD(FTRP(end_ptr), PACK(0, 1));
    
    return ptr;
}

int mm_init(void)
{   
    int even_max_power = EVENIZE(MAX_POWER);
    if ((long)(freeLists = mem_sbrk(even_max_power* sizeof(char *))) == -1)
        return -1;

    for (int i = 0; i <= MAX_POWER; i++) 
    {
        SET_FREE_LIST_PTR(i, NULL);
    }

    mem_sbrk(WSIZE);

    if ((long)(heapPtr = mem_sbrk(4*WSIZE)) == -1)
        return -1;

     
        PUT_WORD(heapPtr, PACK(0, 1)); // Prolog header
        PUT_WORD(FTRP(heapPtr), PACK(0, 1)); // Prolog footer
    
        char ** epilog = NEXT_BLKP(heapPtr);
        PUT_WORD(epilog, PACK(0, 1)); // Epilog header
        PUT_WORD(FTRP(epilog), PACK(0, 1)); // Epilog footer
    
        heapPtr += (HDR_SIZE + FTR_SIZE); // Move past prolog
    
        char **new_block;
        if(new_block = extend_heap(CHUNKSIZE) == NULL)
            return -1;
    
        add_freeList(new_block);
    return 0;
}

static void *find_fit(size_t asize)
{
    void *bp;
    size_t class_idx = sizeWizard(asize);


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

static void place(void *ptr, size_t reqSize)
{ 
    size_t ptrSize = GET_SIZE(ptr);
    size_t total_ptrSize = ptrSize + (HDR_SIZE + FTR_SIZE);

    size_t requireSize = reqSize;
    size_t total_requireSize = reqSize + (HDR_SIZE + FTR_SIZE);

    int total_newBlockSize = total_ptrSize - total_requireSize;
    int newBlockSize = total_newBlockSize - (HDR_SIZE + FTR_SIZE);
    
    char** newBlock;

    if((int)newBlockSize > 0)
    {
        newBlock = (char **)(ptr) + total_requireSize;

        // set new block's size and status
        PUT_WORD(newBlock, PACK(newBlockSize, 0));
        PUT_WORD(FTRP(newBlock), PACK(newBlockSize, 0));
         
        // set ptr size to exact needed size
        PUT_WORD(ptr, PACK(requireSize, 1));
        PUT_WORD(FTRP(ptr), PACK(requireSize, 1));
         
        // check if new block can become larger than it is
        newBlock = coalesce(newBlock);
         
        // handle this new block by putting back into free list
        add_freeList(newBlock);
    }
    else if(newBlockSize == 0)
    {
        requireSize += (HDR_SIZE + FTR_SIZE);

        PUT_WORD(ptr, PACK(requireSize, 1));
        PUT_WORD(FTRP(ptr), PACK(requireSize, 1 ));
    }
    else
    {
        PUT_WORD(ptr, PACK(requireSize, 1));
        PUT_WORD(FTRP(ptr), PACK(requireSize, 1));
    }
}

void *mm_malloc(size_t size)
{

    if (size <= 1<<12) {
        size = round_up_power_2(size);
    }
    // ALMOST SOLVED, maybe problem when GET_SIZE(HDRP(ptr)) / WSIZE have problem or small functions.
    size_t words = ALIGN(size) / WSIZE;
    size_t extendSize;
    char **ptr;

    if (size == 0)
        return NULL;

    if ((ptr = find_fit(words)) == NULL)
    {  
        extendSize = MAX(words, CHUNKSIZE);
        if ((ptr = extend_heap(extendSize/WSIZE)) == NULL)
            return NULL;

        place(ptr, words);
        return ptr + GET_SIZE(HDRP(ptr)) / WSIZE;
    }

    remove_freeList(ptr);
    place(ptr, words);
    return ptr + GET_SIZE(HDRP(ptr)) / WSIZE;
}


void mm_free(void *ptr)
{
    ptr -= WSIZE;
    size_t size = GET_SIZE(ptr);
    // * Assume: ptr points to the beginning of a block header

    // 여기를 수정해
    PUT_WORD(ptr, PACK(size, 0));
    PUT_WORD(FTRP(ptr), PACK(size, 0));
    ptr = coalesce(ptr);

    add_freeList(ptr);
}

static void add_freeList(char **bp)
{
    size_t size = GET_SIZE(bp);
    int idx = sizeWizard(size);

    char **frontPtr = GET_FREELIST_PTR(idx);
    char **backPtr = NULL;

    if(size == 0)
        return;

    if(frontPtr == NULL) // 리스트가 비어있는 상황인 경우
    {
        SET_PTR(GET_PTR_SUCC(bp), NULL);
        SET_PTR(GET_PTR_PRED(bp), NULL);
        SET_FREELIST_PTR(idx, bp);
        return;
    }

    if(size >= GET_SIZE(frontPtr)) // 들어갈 블럭이 frontPtr로써 받아들이기에는 현존 블럭 중 제일 큰 경우
    {
        SET_FREELIST_PTR(idx, bp);
        SET_PTR(GET_PTR_SUCC(bp), frontPtr);
        SET_PTR(GET_PTR_PRED(frontPtr), bp);
        SET_PTR(GET_PTR_PRED(bp), NULL);
        return;
    }

    ///////////// 위의 특수한 경우가 아니라면 아래에서 순회를 실시한다!!! 즉, 이건 LIFO가 아니라 크기 순 정렬이다.

    // 이 리스트는 순서를 지키게끔 한다. 이건 순회하는거임
    while (frontPtr != NULL && GET_SIZE(frontPtr) > size)
    {
        backPtr = frontPtr;
        frontPtr = cGET_SUCC(frontPtr);
    }

    if(frontPtr == NULL) // 얘가 끝에 도달해버린경우..
    {
        SET_PTR(GET_PTR_SUCC(backPtr), bp);
        SET_PTR(GET_PTR_PRED(bp), backPtr);

        SET_PTR(GET_PTR_SUCC(bp), NULL);
        return;
    }
    else // 그래도 중간에 자리를 찾은경우
    {
        SET_PTR(GET_PTR_SUCC(backPtr), bp);
        SET_PTR(GET_PTR_PRED(bp), backPtr);

        SET_PTR(GET_PTR_SUCC(bp), frontPtr);
        SET_PTR(GET_PTR_PRED(frontPtr), bp);
        return;
    }
}

static void remove_freeList(char **ptr)
{
    char **prevBlock = PREV_FREE(ptr);
    char **nextBlock = NEXT_FREE(ptr);
    int idx;

    if(GET_SIZE(ptr) == 0)
        return;

    if(prevBlock == NULL)
    {
        idx = sizeWizard(GET_SIZE(ptr));
        GET_FREELIST_PTR(idx) = nextBlock;
    }
    else
    {
       SET_PTR(GET_PTR_SUCC(prevBlock), nextBlock);
    }

    if (nextBlock != NULL)
        SET_PTR(GET_PTR_SUCC(nextBlock), prevBlock);

    SET_PTR(GET_PTR_PRED(ptr), NULL);
    SET_PTR(GET_PTR_SUCC(ptr), NULL);
}


static size_t sizeWizard(size_t size)
{  
    int index = 0;

    while((index <= MAX_POWER) && (size > 1))
    {
        size >>= 1;
        index++;
    }
    return index;
}
void *mm_realloc(void *ptr, size_t size)
 {
     static int previous_size;
     int buffer_size;
     int diff = abs(size - previous_size);
 
    // 얘는 좀 신기한게, round_up_power_2 아니면 round_to_thousand를 쓴다.
    // 2의 제곱으로 떨어지면 바로!!!!!!!!
     if (diff < 1<<12 && diff % round_up_power_2(diff)) {
         buffer_size = round_up_power_2(diff);
     } else {
         buffer_size = round_to_thousand(size);
     }
 
     void * return_value = mm_realloc_wrapped(ptr, size, buffer_size);
 
     previous_size = size;
     return return_value;
 }
 
 void *mm_realloc_wrapped(void *ptr, size_t size, int buffer_size)
 {
 
     // equivalent to mm_malloc if ptr is NULL
     if (ptr == NULL) {
         return mm_malloc(ptr);
     }
 
     // adjust to be at start of block
     char **old = (char **)ptr - 1;
     char **bp = (char **)ptr - 1;
 
     // get intended and current size
     size_t new_size = ALIGN(size) / WSIZE; // in words
     size_t size_with_buffer = new_size + buffer_size;
     size_t old_size = GET_SIZE(bp); // in words
 
     if (size_with_buffer == old_size && new_size <= size_with_buffer) {
         return bp + HDR_SIZE;
     }
 
     if (new_size == 0) {
         mm_free(ptr);
         return NULL;
     } else if (new_size > old_size) {
         if (GET_SIZE(NEXT_BLKP(bp)) + old_size + 2 >= size_with_buffer &&
                 GET_STATUS(PREV_BLKP(bp)) == 1 &&
                 GET_STATUS(NEXT_BLKP(bp)) == 0
         ) { // checks if possible to merge with previous block in memory
             PUT_WORD(bp, PACK(old_size, 0));
         PUT_WORD(FTRP(bp), PACK(old_size, 0));
 
             bp = coalesce(bp);
             place(bp, size_with_buffer);
         } else if (GET_SIZE(PREV_BLKP(bp)) + old_size + 2 >= size_with_buffer &&
                              GET_STATUS(PREV_BLKP(bp)) == 0 &&
                               GET_STATUS(NEXT_BLKP(bp)) == 1
         ) { // checks if possible to merge with next block in memory
           PUT_WORD(bp, PACK(old_size, 0));
          PUT_WORD(FTRP(bp), PACK(old_size, 0));
 
              bp = coalesce(bp);
 
             memmove(bp + 1, old + 1, old_size * WSIZE);
              place(bp, size_with_buffer);
         } else if (GET_SIZE(PREV_BLKP(bp)) + GET_SIZE(NEXT_BLKP(bp)) + old_size + 4 >= size_with_buffer &&
                              GET_STATUS(PREV_BLKP(bp)) == 0 &&
                              GET_STATUS(NEXT_BLKP(bp)) == 0
         ) { // checks if possible to merge with both prev and next block in memory
             PUT_WORD(bp, PACK(old_size, 0));
          PUT_WORD(FTRP(bp), PACK(old_size, 0));
 
              bp = coalesce(bp);
 
             memmove(bp + 1, old + 1, old_size * WSIZE);
             place(bp, size_with_buffer);
         } else { // end case: if no optimization possible, just do brute force realloc
             bp = (char **)mm_malloc(size_with_buffer* WSIZE + WSIZE) - 1;
 
             if (bp == NULL) {
                 return NULL;
             }
 
             memcpy(bp + 1, old + 1, old_size * WSIZE);
             mm_free(old + 1);
         }
     }
 
     return bp + HDR_SIZE;
 } 


 int round_to_thousand(size_t x)
 {
    // 겨우 realloc에 이게 필요하다고?
     return x % 1000 >= 500 ? x + 1000 - x % 1000 : x - x % 1000;
 }
 
 static int round_up_power_2 (int x)
 {
    // 겨우 realloc에 이게 필요하다고?
     if (x < 0)
         return 0;
     --x;
     x |= x >> 1;
     x |= x >> 2;
     x |= x >> 4;
     x |= x >> 8;
     x |= x >> 16;
     return x+1;
 }
 