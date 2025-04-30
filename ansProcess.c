/*
 * We use explitict segregated free lists with rounding to upper power of 2 as the class equivalence condition
 * Blocks within each class are sorted based on size in descending order
 *
 * Format of allocated block and free block are shown below

///////////////////////////////// Block information /////////////////////////////////////////////////////////
/*

A   : Allocated? (1: true, 0:false)

 < Allocated Block >

             31 30 29 28 27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10  9  8  7  6  5  4  3  2  1  0
bp --->     +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Header :   |                              size of the block                                       |  |  | A|
			+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            |                                                                                               |
            |                                                                                               |
            .                              Payload			                                                .
            .                                                                                               .
            .                                                                                               .
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Footer :   |                              size of the block                                       |     | A|
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+

 < Free block >

             31 30 29 28 27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10  9  8  7  6  5  4  3  2  1  0
 bp --->    +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Header :   |                              size of the block                                       |  |  | A|
 bp+4 --->  +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            |                        pointer to its predecessor in Segregated list                          |
			+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            |                        pointer to its successor in Segregated list                            |
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            .                                                                                               .
            .                                                                                               .
            .                                                                                               .
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Footer :   |                              size of the block                                       |     | A|
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+

 ///////////////////////////////// End of Block information /////////////////////////////////////////////////////////
 // This visual text-based description is taken from: https://github.com/mightydeveloper/Malloc-Lab/blob/master/mm.c
 *
 */

 #include <stdio.h>
 #include <stdlib.h>
 #include <assert.h>
 #include <unistd.h>
 #include <string.h>
 
 #include "mm.h"
 #include "memlib.h"

 
 #define MAX_POWER 50
 #define TAKEN 1
 #define FREE 0
 
 #define WORD_SIZE 4 /* bytes */
 #define D_WORD_SIZE 8
 #define CHUNK ((1<<12)/WORD_SIZE) /* extend heap by this amount (words) */
 #define STATUS_BIT_SIZE 3 // bits
 #define HDR_FTR_SIZE 2 // in words
 #define HDR_SIZE 1 // in words
 #define FTR_SIZE 1 // in words
 #define PRED_FIELD_SIZE 1 // in words
 #define EPILOG_SIZE 2 // in words
 
 // Read and write a word at address p
 #define GET_BYTE(p) (*(char *)(p))
 #define GET_WORD(p) (*(unsigned int *)(p))
 #define PUT_WORD(p, val) (*(char **)(p) = (val))
 
 // Get a bit mask where the lowest size bit is set to 1
 #define GET_MASK(size) ((1 << size) - 1)
 
 /* single word (4) or double word (8) alignment */
 #define ALIGNMENT 8
 
 /* rounds up to the nearest multiple of ALIGNMENT */
 #define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~(ALIGNMENT-1))
 
 // Pack a size and allocated bit into a BIT_word
 #define PACK(size, status) ((size<<STATUS_BIT_SIZE) | (status))
 
 /* Round up to even */
 #define EVENIZE(x) ((x + 1) & ~1)
 
 
 // Address of block's footer
 // Take in a pointer that points to the header
 #define FTRP(header_p) ((char **)(header_p) + GET_SIZE(header_p) + HDR_SIZE)
 
 // Get total size of a block
 // Size indicates the size of the free space in a block
 // Total size = size + size_of_header + size_of_footer = size + D_WORD_SIZE
 // p must point to a header
 #define GET_TOTAL_SIZE(p) (GET_SIZE(p) + HDR_FTR_SIZE)
 
 // Define this so later when we move to store the list in heap,
 // we can just change this function
 #define GET_FREE_LIST_PTR(i) (*(free_lists+i))
 #define SET_FREE_LIST_PTR(i, ptr) (*(free_lists+i) = ptr)
 
 // Set pred or succ for free blocks
 #define SET_PTR(p, ptr) (*(char **)(p) = (char *)(ptr))
 
 // Global variables
 static char **free_lists;
 static char **heap_ptr;
 
 static void *find_fit(size_t words);
 static void place(void *bp, size_t words);
 void *mm_realloc_wrapped(void *ptr, size_t size, int buffer_size);
 
 

 /*
     Finds the block from the free lists that is large
     enough to hold the amount of words specified.
     Returns the pointer to that block.
     Does not take the block out of the free list.
     Does not extend heap.
     Returns the pointer to the block.
     Returns NULL if block large enough is not found.
 */
 static void *find_fit(size_t words) {
     char **bp;
     size_t index = sizeWizard(words);
 
     // check if first free list can contain large enough block
     if ((bp = GET_FREE_LIST_PTR(index)) != NULL && GET_SIZE(bp) >= words) {
         // iterate through blocks
         while(1) {
             // if block is of exact size, return right away
             if (GET_SIZE(bp) == words) {
                 return bp;
             }
 
             // if next block is not possible, return current one
             if (GET_SUCC(bp) == NULL || GET_SIZE(GET_SUCC(bp)) < words) {
                 return bp;
             } else {
                 bp = GET_SUCC(bp);
             }
         }
     }
 
     // move on from current free list
     index++;
 
     // find a large enough non-empty free list
     while (GET_FREE_LIST_PTR(index) == NULL && index < MAX_POWER) {
         index++;
     }
 
     // if there is a non-NULL free list, go until the smallest block in free list
     if ((bp = GET_FREE_LIST_PTR(index)) != NULL) {
         while (GET_SUCC(bp) != NULL) {
             bp = GET_SUCC(bp);
         }
 
         return bp;
     } else { // if no large enough free list available, return NULL
         return NULL;
     }
 }
 
 /*
     The function takes free block and changes status to taken.
     The free block is assumed to have been removed from free list.
     The function reduces the size of the free block (splits it) if size is too large.
     Too large is a free block whose size is > needed size + HDR_FTR_SIZE
     The remaining size is either placed in free_list or left hanging if it is > 0.
     If remaining size is 0 it becomes part of the allocated block.
     bp input is the block that you found already that is large enough.
     Assume that size in words given is <= the size of the block at input.
 */