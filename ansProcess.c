// Segregate Free List #5 : Final
    // referenced https://github.com/quanvuong/CSAPP-Malloc-Lab/tree/master
    // 
    #include <stdio.h>
    #include <stdlib.h>
    #include <assert.h>
    #include <unistd.h>
    #include <string.h>
    #include <sys/mman.h>
    #include <errno.h>
    #include "mm.h"
    #include "memlib.h"
    
    team_t team = {
        /* Team name */
        "Jungle Team 7",
        /* First member's full name */
        "Youngeui Hong",
        /* First member's email address */
        "my-email@gmail.com",
        /* Second member's full name (leave blank if none) */
        "",
        /* Second member's email address (leave blank if none) */
        ""};
    
    /***************************************** 상수 *******************************************/
    
    #define MAX_POWER 50 // 2의 최대 몇 제곱까지 사이즈 클래스를 지원할지. 여기에서는 2^50까지의 사이즈 클래스를 지원함
    #define TAKEN 1
    #define FREE 0
    #define WORD_SIZE 4
    #define D_WORD_SIZE 8
    #define CHUNK ((1 << 12) / WORD_SIZE)
    #define STATUS_BIT_SIZE 3 // 할당된 블록과 할당되지 않은 블록을 구분하기 위해 사용되는 비트의 크기
    #define HDR_FTR_SIZE 2    // 단위: word
    #define HDR_SIZE 1        // 단위: word
    #define FTR_SIZE 1        // 단위: word
    #define PRED_FIELD_SIZE 1 // 단위: word
    #define EPILOG_SIZE 2     // 단위: word
    #define ALIGNMENT 8
    
    /*************************************** 매크로 **********************************************/
    
    /* 주소 p에 적힌 값을 읽어오기 */
    #define GET_WORD(p) (*(unsigned int *)(p))
    
    /* 주소 p에 새로운 값을 쓰기*/
    #define PUT_WORD(p, val) (*(char **)(p) = (val))
    
    /* size보다 크면서 가장 가까운 ALIGNMENT의 배수 찾기 */
    #define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~(ALIGNMENT - 1))
    
    /* x보다 크면서 가장 가까운 짝수 찾기 */
    #define EVENIZE(x) ((x + 1) & ~1)
    
    /* 주어진 사이즈의 비트 마스크 생성하기 */
    #define GET_MASK(size) ((1 << size) - 1)
    
    /* 블록 사이즈 가져오기 */
    #define GET_SIZE(p) ((GET_WORD(p) & ~GET_MASK(STATUS_BIT_SIZE)) >> STATUS_BIT_SIZE)
    
    /* 블록의 할당 여부 가져오기 */
    #define GET_STATUS(p) (GET_WORD(p) & 0x1)
    
    #define PACK(size, status) ((size << STATUS_BIT_SIZE) | (status))
    
    /*
     * 블록 헤더의 주소 가져오기
     */
    #define HDRP(bp) ((char *)(bp)-WSIZE)
    
    /* 블록 푸터의 주소 가져오기 */
    #define FTRP(header_p) ((char **)(header_p) + GET_SIZE(header_p) + HDR_SIZE)
    
    /* 헤더와 푸터를 포함한 블록의 사이즈 가져오기 */
    #define GET_TOTAL_SIZE(p) (GET_SIZE(p) + HDR_FTR_SIZE)
    
    /* free_lists의 i번째 요소 가져오기 */
    #define GET_FREE_LIST_PTR(i) (*(free_lists + i))
    #define SET_FREE_LIST_PTR(i, ptr) (*(free_lists + i) = ptr)
    
    /* 가용 블록의 predecessor, successor 주소값 셋팅 */
    #define SET_PTR(p, ptr) (*(char **)(p) = (char *)(ptr))
    
    #define GET_PTR_PRED_FIELD(ptr) ((char **)(ptr) + HDR_SIZE)
    #define GET_PTR_SUCC_FIELD(ptr) ((char **)(ptr) + HDR_SIZE + PRED_FIELD_SIZE)
    
    /* 가용 블록의 predecessor 메모리 공간에 저장된 주소값 가져오기 */
    #define GET_PRED(bp) (*(GET_PTR_PRED_FIELD(bp)))
    #define GET_SUCC(bp) (*(GET_PTR_SUCC_FIELD(bp)))
    
    /* 이전 블록의 포인터 가져오기 */
    #define PREV_BLOCK_IN_HEAP(header_p) ((char **)(header_p)-GET_TOTAL_SIZE((char **)(header_p)-FTR_SIZE))
    #define NEXT_BLOCK_IN_HEAP(header_p) (FTRP(header_p) + FTR_SIZE)
    
    /************************************** 변수 선언부 *******************************************/
    
    static char **free_lists;
    static char **heap_ptr;
    static int previous_size;
    
    /************************************** 함수 선언부 *******************************************/
    
    static void *extend_heap(size_t words);
    static void add_freeList(char **bp);
    static void remove_freeList(char **bp);
    
    static int round_up_power_2(int x);
    static int round_to_thousand(size_t x);
    static size_t sizeWizard(size_t words);
    static void *find_free_block(size_t words);
    static void alloc_free_block(void *bp, size_t words);
    static void *coalesce(void *bp);
    void *mm_realloc_wrapped(void *ptr, size_t size, int buffer_size);
    
    /************************************** 함수 구현부 *******************************************/
    
    /* mm_init: malloc 패키지 초기화하기 */
    int mm_init(void)
    {
        // segregated free list를 위해 MAX_POWER * sizeof(char *) 만큼 힙 영역 확장하기
        if ((long)(free_lists = mem_sbrk(MAX_POWER * sizeof(char *))) == -1)
            return -1;
    
        // segregated free list 초기화
        for (int i = 0; i <= MAX_POWER; i++)
        {
            SET_FREE_LIST_PTR(i, NULL);
        }
    
        // 더블 워드 정렬 조건 충족을 위해 워드 사이즈만큼 힙 영역 확장
        mem_sbrk(WORD_SIZE);
    
        // 프롤로그 블록과 에필로그 블록을 위해 힙 영역 추가 확장
        if ((long)(heap_ptr = mem_sbrk(4 * WORD_SIZE)) == -1)
            return -1;
    
        PUT_WORD(heap_ptr, PACK(0, TAKEN));       // 프롤로그 헤더
        PUT_WORD(FTRP(heap_ptr), PACK(0, TAKEN)); // 프롤로그 푸터
    
        char **epilog = NEXT_BLOCK_IN_HEAP(heap_ptr); // 에필로그 헤더 포인터
        PUT_WORD(epilog, PACK(0, TAKEN));             // 에필로그 헤더
        PUT_WORD(FTRP(epilog), PACK(0, TAKEN));       // 에필로그 푸터
    
        heap_ptr = NEXT_BLOCK_IN_HEAP(heap_ptr); // heap 포인터를 프롤로그 블록 다음으로 이동시킴
    
        // CHUNK 사이즈만큼 힙 영역을 확장하기
        char **new_block;
        if ((new_block = extend_heap(CHUNK)) == NULL)
            return -1;
    
        // 힙 영역을 확장하여 새로 얻은 블록을 가용 리스트에 추가해주기
        add_freeList(new_block);
    
        return 0;
    }
    
    /* mm_malloc: 메모리 할당하기 */
    void *mm_malloc(size_t size)
    {
        if (size == 0)
            return NULL;
    
        // CHUNK 사이즈보다 작으면 가장 가까운 2의 제곱 사이즈로 만들기
        if (size <= CHUNK * WORD_SIZE)
            size = round_up_power_2(size);
    
        // 바이트 단위 사이즈를 워드 단위 사이즈로 변환하기
        size_t words = ALIGN(size) / WORD_SIZE;
    
        size_t extend_size;
        char **bp;
    
        // 할당하려는 사이즈에 적합한 블록이 있는지 찾았는데 없는 경우 힙 영역을 확장
        if ((bp = find_free_block(words)) == NULL)
        {
            extend_size = words > CHUNK ? words : CHUNK;
            if ((bp = extend_heap(extend_size)) == NULL)
                return NULL;
    
            // 새로 할당 받은 힙 영역에서 필요한 만큼 메모리 할당하고 나머지는 가용 리스트에 추가
            alloc_free_block(bp, words);
    
            return bp + HDR_SIZE;
        }
    
        remove_freeList(bp); // 사용하려는 블록을 가용 리스트에서 제거
        alloc_free_block(bp, words);     // 가용 블록에서 필요한 만큼 메모리 할당하고, 남은 블록은 다시 가용 리스트에 추가
    
        return bp + HDR_SIZE;
    }
    
    /* mm_free: 메모리 반환하기 */
    void mm_free(void *ptr)
    {
        ptr -= WORD_SIZE; // 헤더 포인터
    
        // 헤더와 푸터의 할당 상태 정보를 free 상태로 수정
        size_t size = GET_SIZE(ptr);
        PUT_WORD(ptr, PACK(size, FREE));
        PUT_WORD(FTRP(ptr), PACK(size, FREE));
    
        // 해제된 블록의 전후로 가용 블록이 있다면 연결
        ptr = coalesce(ptr);
    
        // 연결된 블록을 가용 리스트에 추가
        add_freeList(ptr);
    }
    
    /* mm_realloc: 메모리 재할당하기 */
    void *mm_realloc(void *ptr, size_t size)
    {
        int buffer_size;
        int diff = abs(size - previous_size);
    
        if (diff < CHUNK * WORD_SIZE && diff % round_up_power_2(diff)) // diff가 4KB보다 작은 경우
        {
            buffer_size = round_up_power_2(diff);
        }
        else // diff 사이즈가 4KB보다 큰 경우
        {
            buffer_size = round_to_thousand(size);
        }
    
        void *return_value = mm_realloc_wrapped(ptr, size, buffer_size);
    
        previous_size = size;
    
        return return_value;
    }
    
    /*
    mm_realloc_wrapped: mm_realloc의 helper function
    - ptr이 NULL인 경우 mm_malloc 수행
    - size가 0인 경우 메모리 해제 수행
    - 최적화를 위해 인접한 블록을 사용할 수 있는지 확인하고 연결하여 새로운 블록을 할당하는 것을 방지함
    - 사용 가능한 인접 블록이 없는 경우 단순히 할당하고 해제함
    - 너무 자주 재할당하지 않도록 buffer 사용
    */
    void *mm_realloc_wrapped(void *ptr, size_t size, int buffer_size)
    {
        if (ptr == NULL)
            return mm_malloc(ptr); // ptr이 NULL인 경우 mm_malloc 수행
    
        // 블록의 시작 지점을 가리키도록 조정
        char **old = (char **)ptr - 1;
        char **bp = (char **)ptr - 1;
    
        size_t new_size = ALIGN(size) / WORD_SIZE;
        size_t size_with_buffer = new_size + buffer_size;
        size_t old_size = GET_SIZE(bp);
    
        // 재할당하려는 사이즈가 기존 사이즈보다 작은 경우
        if (size_with_buffer == old_size && new_size <= size_with_buffer)
            return bp + HDR_SIZE;
    
        if (new_size == 0)
        {
            mm_free(ptr);
            return NULL;
        }
        else if (new_size > old_size)
        {
            size_t prev_block_size = GET_SIZE(PREV_BLOCK_IN_HEAP(bp));
            size_t next_block_size = GET_SIZE(NEXT_BLOCK_IN_HEAP(bp));
            int prev_status = GET_STATUS(PREV_BLOCK_IN_HEAP(bp));
            int next_status = GET_STATUS(NEXT_BLOCK_IN_HEAP(bp));
    
            if (next_block_size + old_size + 2 >= size_with_buffer && prev_status == TAKEN && next_status == FREE) // 뒤의 블록이 가용 블록인 경우
            {
                PUT_WORD(bp, PACK(old_size, FREE));
                PUT_WORD(FTRP(bp), PACK(old_size, FREE));
                bp = coalesce(bp);
                alloc_free_block(bp, size_with_buffer);
            }
            else if (prev_block_size + old_size + 2 >= size_with_buffer && prev_status == FREE && next_status == TAKEN) // 앞의 블록이 가용 블록인 경우
            {
                PUT_WORD(bp, PACK(old_size, FREE));
                PUT_WORD(FTRP(bp), PACK(old_size, FREE));
                bp = coalesce(bp);
                memmove(bp + 1, old + 1, old_size * WORD_SIZE);
                alloc_free_block(bp, size_with_buffer);
            }
            else if (prev_block_size + next_block_size + old_size + 4 >= size_with_buffer && prev_status == FREE && next_status == FREE) // 앞뒤 블록이 모두 가용 블록인 경우
            {
                PUT_WORD(bp, PACK(old_size, FREE));
                PUT_WORD(FTRP(bp), PACK(old_size, FREE));
                bp = coalesce(bp);
                memmove(bp + 1, old + 1, old_size * WORD_SIZE);
                alloc_free_block(bp, size_with_buffer);
            }
            else
            {
                bp = (char **)mm_malloc(size_with_buffer * WORD_SIZE + WORD_SIZE) - 1;
                if (bp == NULL)
                    return NULL;
                memcpy(bp + 1, old + 1, old_size * WORD_SIZE);
                mm_free(old + 1);
            }
        }
    
        return bp + HDR_SIZE;
    }
    
    /*
    extend_heap: 힙 영역 확장하기
    - 힙 영역 확장에 성공하는 경우 새로운 블록의 헤더와 푸터 영역을 정의하고, 해당 블록의 포인터를 반환
    - 힙 영역 확장에 실패하는 경우 NULL을 리턴
    */
    static void *extend_heap(size_t words)
    {
        char **bp;                                               // 힙 영역을 확장하여 새로 생긴 가용 블록을 가리키는 포인터
        char **end_pointer;                                      // 가용 블록의 끝을 가리키는 포인터
        size_t words_extend = EVENIZE(words);                    // 더블 워드 정렬
        size_t words_extend_total = words_extend + HDR_FTR_SIZE; // 헤더와 푸터 사이즈를 더한 총 블록 사이즈
    
        if ((long)(bp = mem_sbrk((words_extend_total)*WORD_SIZE)) == -1)
            return NULL;
    
        // 힙 영역 마지막에 에필로그 블록 추가
        bp -= EPILOG_SIZE;
    
        // 새로운 가용 블록의 헤더와 푸터에 값 셋팅
        PUT_WORD(bp, PACK(words_extend, FREE));
        PUT_WORD(FTRP(bp), PACK(words_extend, FREE));
    
        end_pointer = bp + words_extend_total;
        PUT_WORD(end_pointer, PACK(0, TAKEN));
        PUT_WORD(FTRP(end_pointer), PACK(0, TAKEN));
    
        return bp;
    }
    
    /* add_freeList: 블록 사이즈에 따라 적절한 위치에 새로운 가용 블록 추가하기 */
    static void add_freeList(char **bp)
    {
        size_t size = GET_SIZE(bp); // 새로 배치할 가용 블록의 사이즈
    
        if (size == 0)
            return;
    
        // 가용 블록에 적합한 size class의 가용 리스트 찾기
        int index = sizeWizard(size);
        char **front_ptr = GET_FREE_LIST_PTR(index); // 해당 가용 리스트의 주소를 받아오기
        char **prev_ptr = NULL;
    
        // 만약 그 size class의 가용 리스트가 비어있다면
        if (front_ptr == NULL)
        {
            SET_PTR(GET_PTR_PRED_FIELD(bp), NULL);
            SET_PTR(GET_PTR_SUCC_FIELD(bp), NULL);
            SET_FREE_LIST_PTR(index, bp); // 가용 리스트의 시작 지점으로 설정
            return;
        }
    
        // 만약 새로운 블록이 이 size class의 가용 리스트 내에서 가장 큰 사이즈라면 (가용 리스트는 내림차순으로 정렬되어 있음)
        if (size >= GET_SIZE(front_ptr))
        {
            SET_FREE_LIST_PTR(index, bp); // 가용 리스트의 시작 지점으로 설정
            SET_PTR(GET_PTR_PRED_FIELD(bp), NULL);
            SET_PTR(GET_PTR_SUCC_FIELD(bp), front_ptr);
            SET_PTR(GET_PTR_PRED_FIELD(front_ptr), bp);
            return;
        }
    
        // 내림차순으로 정렬된 가용 리스트에서 블록이 들어갈 지점 찾기
        while (front_ptr != NULL && GET_SIZE(front_ptr) > size)
        {
            prev_ptr = front_ptr;
            front_ptr = GET_SUCC(front_ptr);
        }
    
        if (front_ptr == NULL) // 가용 리스트의 끝에 도달한 경우
        {
            SET_PTR(GET_PTR_SUCC_FIELD(prev_ptr), bp);
            SET_PTR(GET_PTR_PRED_FIELD(bp), prev_ptr);
            SET_PTR(GET_PTR_SUCC_FIELD(bp), NULL);
            return;
        }
        else
        { // 가용 리스트의 중간에 집어넣는 경우
            SET_PTR(GET_PTR_SUCC_FIELD(prev_ptr), bp);
            SET_PTR(GET_PTR_PRED_FIELD(bp), prev_ptr);
            SET_PTR(GET_PTR_SUCC_FIELD(bp), front_ptr);
            SET_PTR(GET_PTR_PRED_FIELD(front_ptr), bp);
            return;
        }
    }
    
    /* 주어진 수 x보다 크거나 같은 2의 제곱 중에서 가장 작은 값을 찾는 함수*/
    static int round_up_power_2(int x)
    {
        if (x < 0)
            return 0;
        --x;
        x |= x >> 1;
        x |= x >> 2;
        x |= x >> 4;
        x |= x >> 8;
        x |= x >> 16;
        return x + 1;
    }
    
    /* 가장 가까운 1000의 단위의 수를 찾는 함수 */
    static int round_to_thousand(size_t x)
    {
        return x % 1000 >= 500 ? x + 1000 - x % 1000 : x - x % 1000;
    }
    
    /* sizeWizard: 주어진 words 사이즈가 속하는 size class, 즉 가용 리스트 상의 인덱스를 찾는 함수 */
    static size_t sizeWizard(size_t words)
    {
        int index = 0;
    
        while ((index <= MAX_POWER) && (words > 1))
        {
            words >>= 1; // words가 1보다 작거나 같아질 때까지 오른쪽으로 shift 연산
            index++;
        }
    
        return index;
    }
    
    /* find_free_block: 전체 Segregated Free List에서 주어진 words 사이즈에 적합한 가용 블록 찾기 */
    static void *find_free_block(size_t words)
    {
        char **bp;
        size_t index = sizeWizard(words); // 주어진 words 사이즈보다 큰 size class 중 가장 작은 size class의 가용 리스트 찾기
    
        // 사용할 수 있는 가용 블록을 찾을 때까지 탐색
        while (index <= MAX_POWER)
        {
            // 현재 size class의 가용 리스트가 비어 있지 않고, 블록의 크기도 충분히 커서 메모리 할당이 가능한 경우
            if ((bp = GET_FREE_LIST_PTR(index)) != NULL && GET_SIZE(bp) >= words)
            {
                // 가용 리스트를 순회하며 사이즈가 가장 적합한 블록 찾기
                while (1)
                {
                    if (GET_SIZE(bp) == words)
                        return bp;
    
                    // 다음 블록이 없거나, 다음 불록이 필요한 사이즈보다 작으면 현재 블록을 리턴
                    if (GET_SUCC(bp) == NULL || GET_SIZE(GET_SUCC(bp)) < words)
                        return bp;
    
                    bp = GET_SUCC(bp);
                }
            }
    
            index++;
        }
    
        // 만약 모든 리스트를 탐색했는데도 사용할 수 있는 가용 블록이 없는 경우 NULL 리턴
        return NULL;
    }
    
    /*
    alloc_free_block: 가용 블록에서 메모리 할당하기
    */
    static void alloc_free_block(void *bp, size_t words)
    {
        size_t bp_tot_size = GET_SIZE(bp) + HDR_FTR_SIZE;                      // 가용 블록의 사이즈 (= 페이로드 + 헤더 + 푸터)
        size_t needed_size = words;                                            // 할당 받아야 하는 사이즈
        size_t needed_tot_size = needed_size + HDR_FTR_SIZE;                   // 할당 받아야 하는 사이즈 (헤더, 푸터 포함)
        size_t left_block_size = bp_tot_size - needed_tot_size - HDR_FTR_SIZE; // 할당하고 남는 블록의 사이즈
    
        char **new_block_ptr; // 할당하고 남는 새로운 가용 블록의 포인터
    
        if ((int)left_block_size > 0) // 할당하고도 블록이 남는 경우
        {
            // 필요한 사이즈만큼 메모리 할당
            PUT_WORD(bp, PACK(needed_size, TAKEN));
            PUT_WORD(FTRP(bp), PACK(needed_size, TAKEN));
    
            // 새로운 가용 블록의 포인터
            new_block_ptr = (char **)(bp) + needed_tot_size;
    
            // 새로운 가용 블록의 헤더, 푸터 정보 셋팅
            PUT_WORD(new_block_ptr, PACK(left_block_size, FREE));
            PUT_WORD(FTRP(new_block_ptr), PACK(left_block_size, FREE));
    
            // 인접한 가용 블록이 있는 경우 연결
            new_block_ptr = coalesce(new_block_ptr);
    
            // 가용 리스트에 추가
            add_freeList(new_block_ptr);
        }
        else if (left_block_size == 0) // 필요한 만큼 할당하고 남는 블록이 2워드이면 쪼갤 수 없으므로 2워드를 추가하여 메모리를 할당함
        {
            PUT_WORD(bp, PACK(needed_tot_size, TAKEN));
            PUT_WORD(FTRP(bp), PACK(needed_tot_size, TAKEN));
        }
        else // 할당하려는 블록의 사이즈와 동일한 경우
        {
            PUT_WORD(bp, PACK(needed_size, TAKEN));
            PUT_WORD(FTRP(bp), PACK(needed_size, TAKEN));
        }
    }
    
    /* remove_freeList: 가용 리스트에서 블록 제거하기 */
    static void remove_freeList(char **bp)
    {
        char **prev_block = GET_PRED(bp);
        char **next_block = GET_SUCC(bp);
        int index;
    
        if (GET_SIZE(bp) == 0)
            return;
    
        if (prev_block == NULL) // 해당 size class 리스트의 맨 앞에 있는 가장 큰 블록인 경우
        {
            index = sizeWizard(GET_SIZE(bp)); // 블록이 포함된 가용 리스트의 인덱스
            GET_FREE_LIST_PTR(index) = next_block;      // 다음 블록을 가용 리스트의 첫 번째 블록으로 설정
        }
        else
        {
            SET_PTR(GET_PTR_SUCC_FIELD(prev_block), next_block); // 이전 블록이 다음 블록을 가리키도록 수정
        }
    
        if (next_block != NULL)
        {
            SET_PTR(GET_PTR_PRED_FIELD(next_block), prev_block);
        }
    
        // 현재 블록의 predecessor와 successor를 NULL로 셋팅
        SET_PTR(GET_PTR_PRED_FIELD(bp), NULL);
        SET_PTR(GET_PTR_SUCC_FIELD(bp), NULL);
        // 완료
    }
    
    /* coalesce: 가용 블록 연결하기 */
    static void *coalesce(void *bp)
    {
        char **prev_block = PREV_BLOCK_IN_HEAP(bp);
        char **next_block = NEXT_BLOCK_IN_HEAP(bp);
        size_t prev_status = GET_STATUS(prev_block);
        size_t next_status = GET_STATUS(next_block);
        size_t new_size = GET_SIZE(bp);
    
        // Case 1
        if (prev_status == TAKEN && next_status == TAKEN)
        {
            return bp;
        }
        // Case 2
        else if (prev_status == TAKEN && next_status == FREE)
        {
            // 다음 블록을 우선 가용 리스트에서 제거
            remove_freeList(next_block);
            // 다음 블록을 합친 사이즈로 가용 블록의 헤더와 푸터 업데이트
            new_size += GET_TOTAL_SIZE(next_block);
            PUT_WORD(bp, PACK(new_size, FREE));
            PUT_WORD(FTRP(next_block), PACK(new_size, FREE));
        }
        // Case 3
        else if (prev_status == FREE && next_status == TAKEN)
        {
            // 이전 블록을 우선 가용 리스트에서 제거
            remove_freeList(prev_block);
            // 이전 블록을 합친 사이즈로 가용 블록의 헤더와 푸터 업데이트
            new_size += GET_TOTAL_SIZE(prev_block);
            PUT_WORD(prev_block, PACK(new_size, FREE));
            PUT_WORD(FTRP(bp), PACK(new_size, FREE));
            bp = prev_block;
        }
        // Case 4
        else if (prev_status == FREE && next_status == FREE)
        {
            remove_freeList(prev_block);
            remove_freeList(next_block);
            new_size += GET_TOTAL_SIZE(prev_block) + GET_TOTAL_SIZE(next_block);
            PUT_WORD(prev_block, PACK(new_size, FREE));
            PUT_WORD(FTRP(next_block), PACK(new_size, FREE));
            bp = prev_block;
        }
    
        return bp;
    }