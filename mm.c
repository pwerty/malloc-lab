#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include <sys/mman.h>
#include <errno.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "VILLIAN_KWON v5",
    /* First member's full name */
    "kwon woo hyeon",
    /* First member's email address */
    "pwertyman@naver.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};
#define MAX_POWER 50

#define STATUS_BIT_SIZE 3 // bits
#define HDR_SIZE 1 // in words
#define FTR_SIZE 1 // in words
#define PRED_FIELD_SIZE 1 // in words
#define EPILOG_SIZE 2 // in words

/* Basic constants and macros */
#define WSIZE 4 /* 워드와 푸터의 사이즈, 바이트 단위 */
#define DSIZE 8 /* 더블 워드 사이즈 */
#define CHUNKSIZE ((1<<12)/WSIZE)
#define ALIGNMENT (WSIZE * 2)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define GET_WORD(p) (*(unsigned int *)(p))
#define PUT_WORD(p, val) (*(char **)(p) = (val))

#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~(ALIGNMENT - 1))

#define EVENIZE(x) ((x + 1) & ~1)

#define GET_MASK(size) ((1 << size) - 1)

/* Read the size and allocated fields form address p */
#define GET_SIZE(p) ((GET_WORD(p) & ~GET_MASK(STATUS_BIT_SIZE)) >> STATUS_BIT_SIZE)

// ~0x7은 맨 우측의 3비트를 빼고 나머지 내용을 보겠다는 것.
#define GET_ALLOC(p) (GET_WORD(p) & 0x1)
// 0x1은 맨 우측의 1비트만 보겠다는 것.

#define PACK(size, status) ((size << STATUS_BIT_SIZE) | (status))

// Footer만 사용
#define FTRP(headp) ((char **)(headp) + GET_SIZE(headp) + HDR_SIZE)

#define GET_TOTAL_SIZE(p) (GET_SIZE(p) + (HDR_SIZE + FTR_SIZE))

#define GET_FREELIST_PTR(i) (*(freeLists+i))
#define SET_FREELIST_PTR(i, ptr) (*(freeLists+i) = ptr)

#define SET_PTR(p, ptr) (*(char **)(p) = (char *)(ptr))

// FREE LIST 단위의 전 후 블럭에 대한 정보를 가져오는 매크로 4셋.
#define GET_PTR_PRED(ptr) ((char **)(ptr) + HDR_SIZE)
#define GET_PTR_SUCC(ptr) ((char **)(ptr) + HDR_SIZE + PRED_FIELD_SIZE)

#define PREV_FREE(bp) (*(GET_PTR_PRED(bp)))
#define NEXT_FREE(bp) (*(GET_PTR_SUCC(bp)))

// 힙 상에 있는 블록에 대해 조회하는 함수. headP에서 내용을 다룬다.
#define PREV_BLKP(headP) ((char **)(headP) - GET_TOTAL_SIZE((char **)(headP) - FTR_SIZE))
#define NEXT_BLKP(headP) (FTRP(headP) + FTR_SIZE)



static char **freeLists;
static char **heapPtr;
static int previous_size;

static void *extend_heap(size_t words);
static void add_freeList(char **bp);
static void remove_freeList(char **bp);

static int round_up_power_2 (int x);
static int round_to_thousand(size_t x);

static size_t sizeWizard(size_t size);
static void *find_fit(size_t asize);
static void place(void *ptr, size_t reqSize);
static void *coalesce(void *ptr);
void *mm_realloc_wrapped(void *ptr, size_t size, int buffer_size);

int mm_init(void)
{   
    // Free List 사용을 위해 힙 영역 확장을 최초 시도
    if ((long)(freeLists = mem_sbrk(MAX_POWER * sizeof(char *))) == -1)
        return -1;

    // 각 배정된 내용에 대해 초기화
    for (int i = 0; i <= MAX_POWER; i++) 
    {
        SET_FREELIST_PTR(i, NULL);
    }

    // WSIZE하나 더 던져줘서 더블 워드 정렬 조건 충족
    mem_sbrk(WSIZE);

    // prologue, epilogue 작성을 위해 힙 영역 확장 시도
    if ((long)(heapPtr = mem_sbrk(4*WSIZE)) == -1)
        return -1;

     
        PUT_WORD(heapPtr, PACK(0, 1)); // Prolog header
        PUT_WORD(FTRP(heapPtr), PACK(0, 1)); // Prolog footer
    
        char **epilog = NEXT_BLKP(heapPtr);
        PUT_WORD(epilog, PACK(0, 1)); // Epilog header
        PUT_WORD(FTRP(epilog), PACK(0, 1)); // Epilog footer
    
        // modi!
        heapPtr = NEXT_BLKP(heapPtr); // heapPtr을 프롤로그 푸터 바로 다음으로 이동
    
        char **new_block;
        // 개씨발 설마??
        if((new_block = extend_heap(CHUNKSIZE)) == NULL)
            return -1;
    
    add_freeList(new_block);
    return 0;
    // 완료
}


void *mm_malloc(size_t size)
{
    if (size == 0)
        return NULL;   

    if (size <= CHUNKSIZE * WSIZE) {
        size = round_up_power_2(size);
    }

    // size를 기반으로 WSIZE로 나누어 
    size_t words = ALIGN(size) / WSIZE;
    size_t extendSize;
    char **ptr;


    // 사이즈에 맞는 블록을 탐색하기
    if ((ptr = find_fit(words)) == NULL)
    {  
        // 없으면 힙을 늘려본다.
        extendSize = MAX(words, CHUNKSIZE);
        if ((ptr = extend_heap(extendSize)) == NULL)
            return NULL;

        // 별 일 없으면 여기까지 내려오니 여기서 할당을 시도한다.
        place(ptr, words);
        return ptr + HDR_SIZE;
    }
    // 여기로 내려오면 사이즈에 맞는 블록이 있으니 할당 시도.
    remove_freeList(ptr);
    place(ptr, words);
    return ptr + HDR_SIZE;
    // 완료
}


void mm_free(void *ptr)
{
    // ptr은 payload 시작점을 가리키니 WSIZE를 좌측으로 당겨서 head를 가리키도록 한다.
    // 원문 내용 : Assume: ptr points to the beginning of a block header
    ptr -= WSIZE;

    size_t size = GET_SIZE(ptr);
    PUT_WORD(ptr, PACK(size, 0));
    PUT_WORD(FTRP(ptr), PACK(size, 0));

    // 해제 된 블록의 전 후로 가용 블록이 있다면 연결한다.
    ptr = coalesce(ptr);

    // 연결된 블록을 가용 리스트에 추가한다.
    add_freeList(ptr);
    // 완료
}

void *mm_realloc(void *ptr, size_t size)
 {
    // previous_size를 밖으로 빼는 modi!
     int buffer_size;
     int diff = abs(size - previous_size);

     if (diff < (CHUNKSIZE * WSIZE) && diff % round_up_power_2(diff)) { // diff가 4KB 보다 작은 경우
         buffer_size = round_up_power_2(diff);
     } else { // diff가 4KB보다 큰 경우
         buffer_size = round_to_thousand(size);
     }
 
     void * return_value = mm_realloc_wrapped(ptr, size, buffer_size);
 
     previous_size = size;
     return return_value;
     // 완료
 }
 

void *mm_realloc_wrapped(void *ptr, size_t size, int buffer_size)
 {
 
     // ptr이 NULL이면 그냥 mm_malloc만 한다.
     if (ptr == NULL) {
         return mm_malloc(ptr);
     }
 
     // 시작점을 가리키게 하기
     char **old = (char **)ptr - 1;
     char **bp = (char **)ptr - 1;
 
     
     size_t new_size = ALIGN(size) / WSIZE; // Word 단위로 변경
     size_t size_with_buffer = new_size + buffer_size;
     size_t old_size = GET_SIZE(bp); // Word 단위로 변경
 
     // 재할당 시도 사이즈가 기존 사이즈보다 작은 경우
     if (size_with_buffer == old_size && new_size <= size_with_buffer) {
         return bp + HDR_SIZE;
     }
 
     if (new_size == 0)
     {
         mm_free(ptr);
         return NULL;
     } 
     else if (new_size > old_size)
     {

        size_t prev_block_size = GET_SIZE(PREV_BLKP(bp));
        size_t next_block_size = GET_SIZE(NEXT_BLKP(bp));
        int prev_status = GET_ALLOC(PREV_BLKP(bp));
        int next_status = GET_ALLOC(NEXT_BLKP(bp));
        
         if (next_block_size + old_size + 2 >= size_with_buffer && prev_status == 1 && next_status == 0)
         { // checks if possible to merge with previous block in memory
            PUT_WORD(bp, PACK(old_size, 0));
            PUT_WORD(FTRP(bp), PACK(old_size, 0));
            bp = coalesce(bp);
            place(bp, size_with_buffer);
         }
         else if (prev_block_size + old_size + 2 >= size_with_buffer && prev_status == 0 &&  next_status == 1)
         { // checks if possible to merge with next block in memory
            PUT_WORD(bp, PACK(old_size, 0));
            PUT_WORD(FTRP(bp), PACK(old_size, 0));
            bp = coalesce(bp);
            memmove(bp + 1, old + 1, old_size * WSIZE);
            place(bp, size_with_buffer);
         }
         else if (prev_block_size + next_block_size + old_size + 4 >= size_with_buffer && prev_status == 0 && next_status == 0)
            { // checks if possible to merge with both prev and next block in memory
             PUT_WORD(bp, PACK(old_size, 0));
             PUT_WORD(FTRP(bp), PACK(old_size, 0));
              bp = coalesce(bp);
             memmove(bp + 1, old + 1, old_size * WSIZE);
             place(bp, size_with_buffer);
         }
         else
         { // end case: if no optimization possible, just do brute force realloc
             bp = (char **)mm_malloc(size_with_buffer* WSIZE + WSIZE) - 1;
             if (bp == NULL)
                 return NULL;
             memcpy(bp + 1, old + 1, old_size * WSIZE);
             mm_free(old + 1);
         }
     }
     return bp + HDR_SIZE;
     // 완료
 } 



static void *extend_heap(size_t words)
 {
     char **ptr;
     char **end_ptr;
     size_t words_extend = EVENIZE(words); // make sure double aligned
     size_t total_words = words_extend + HDR_SIZE + FTR_SIZE;

     if ((long)(ptr = mem_sbrk((total_words) * WSIZE)) == -1) {
         return NULL;
     }
     // 얘가 왜 이걸 해야하는지 이해 할 것
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
 
static void add_freeList(char **bp)
{
    size_t size = GET_SIZE(bp);


    if(size == 0)
        return;

    int idx = sizeWizard(size);

    char **frontPtr = GET_FREELIST_PTR(idx);
    char **backPtr = NULL;


    if(frontPtr == NULL) // 리스트가 비어있는 상황인 경우
    {
        SET_PTR(GET_PTR_PRED(bp), NULL);
        SET_PTR(GET_PTR_SUCC(bp), NULL);
        SET_FREELIST_PTR(idx, bp);
        return;
    }

    if(size >= GET_SIZE(frontPtr)) // 들어갈 블럭이 frontPtr로써 받아들이기에는 현존 블럭 중 제일 큰 경우
    {
        SET_FREELIST_PTR(idx, bp);
        SET_PTR(GET_PTR_PRED(bp), NULL);
        SET_PTR(GET_PTR_SUCC(bp), frontPtr);
        SET_PTR(GET_PTR_PRED(frontPtr), bp);
        return;
    }

    ///////////// 위의 특수한 경우가 아니라면 아래에서 순회를 실시한다!!! 즉, 이건 LIFO가 아니라 크기 순 정렬이다.

    // 이 리스트는 순서를 지키게끔 한다. 이건 순회하는거임
    while (frontPtr != NULL && GET_SIZE(frontPtr) > size)
    {
        backPtr = frontPtr;
        frontPtr = NEXT_FREE(frontPtr);
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

    // 완료
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
 
static int round_to_thousand(size_t x)
 {
    // 겨우 realloc에 이게 필요하다고?
     return x % 1000 >= 500 ? x + 1000 - x % 1000 : x - x % 1000;
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
 
static void *find_fit(size_t asize)
 {
     char **bp;
     size_t class_idx = sizeWizard(asize);
    // index while문 추가 modi!
     while (class_idx <= MAX_POWER)
     {
              // check if first free list can contain large enough block
      if ((bp = GET_FREELIST_PTR(class_idx)) != NULL && GET_SIZE(bp) >= asize) {
        // iterate through blocks
        while(1) {
            // if block is of exact size, return right away
            if (GET_SIZE(bp) == asize) {
                return bp;
            }

            // if next block is not possible, return current one
            if (NEXT_FREE(bp) == NULL || GET_SIZE(NEXT_FREE(bp)) < asize)
                return bp;

                bp = NEXT_FREE(bp);
        }
    }

    // move on from current free list
    class_idx++;
    }
         return NULL; 
}

static void place(void *ptr, size_t reqSize)
 { 
     size_t total_ptrSize = GET_SIZE(ptr) + (HDR_SIZE + FTR_SIZE);
 
     size_t requireSize = reqSize;
     size_t total_requireSize = reqSize + (HDR_SIZE + FTR_SIZE);
 
     size_t newBlockSize = total_ptrSize - total_requireSize - (HDR_SIZE + FTR_SIZE);
     
     char** newBlock;
 
     if((int)newBlockSize > 0)
     {
         PUT_WORD(ptr, PACK(requireSize, 1));
         PUT_WORD(FTRP(ptr), PACK(requireSize, 1));

         newBlock = (char **)(ptr) + total_requireSize;

         PUT_WORD(newBlock, PACK(newBlockSize, 0));
         PUT_WORD(FTRP(newBlock), PACK(newBlockSize, 0));
          
         // check if new block can become larger than it is
         newBlock = coalesce(newBlock);
          
         // handle this new block by putting back into free list
         add_freeList(newBlock);
     }
     else if(newBlockSize == 0)
     {
         PUT_WORD(ptr, PACK(total_requireSize, 1));
         PUT_WORD(FTRP(ptr), PACK(total_requireSize, 1 ));
     }
     else
     {
         PUT_WORD(ptr, PACK(requireSize, 1));
         PUT_WORD(FTRP(ptr), PACK(requireSize, 1));
     }
     // 완료
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
         SET_PTR(GET_PTR_PRED(nextBlock), prevBlock);
 
     SET_PTR(GET_PTR_PRED(ptr), NULL);
     SET_PTR(GET_PTR_SUCC(ptr), NULL);
 }

 static void* coalesce(void *ptr)
 {
     // 여기의 *ptr은 header를 가리키는가?
     char **prev_block = PREV_BLKP(ptr);
     char **next_block = NEXT_BLKP(ptr);
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
 
         PUT_WORD(prev_block, PACK(size, 0));
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
 