/**
 * @file mm.c
 * @brief A 64-bit struct-based implicit free list memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 * TODO: insert your documentation here. :)
 *
 *************************************************************************
 *
 * ADVICE FOR STUDENTS.
 * - Step 0: Please read the writeup!
 * - Step 1: Write your heap checker.
 * - Step 2: Write contracts / debugging assert statements.
 * - Good luck, and have fun!
 *
 *************************************************************************
 *
 * @author Kevin Kyi <kwkyi@andrew.cmu.edu>
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* Do not change the following! */

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 *****************************************************************************
 * If DEBUG is defined (such as when running mdriver-dbg), these macros      *
 * are enabled. You can use them to print debugging output and to check      *
 * contracts only in debug mode.                                             *
 *                                                                           *
 * Only debugging macros with names beginning "dbg_" are allowed.            *
 * You may not define any other macros having arguments.                     *
 *****************************************************************************
 */
#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, no code gets generated for these */
/* The sizeof() hack is used to avoid "unused variable" warnings */
#define dbg_printf(...) (sizeof(__VA_ARGS__), -1)
#define dbg_requires(expr) (sizeof(expr), 1)
#define dbg_assert(expr) (sizeof(expr), 1)
#define dbg_ensures(expr) (sizeof(expr), 1)
#define dbg_printheap(...) ((void)sizeof(__VA_ARGS__))
#endif

/* Basic constants */

typedef uint64_t word_t;

/** @brief Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/** @brief Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/** @brief Minimum block size (bytes) */
static const size_t min_block_size = 2 * dsize;

/**
 * TODO: explain what chunksize is
 * (Must be divisible by dsize)
 */
static const size_t chunksize = (1 << 12);

/**
 * TODO: explain what alloc_mask is
 */
static const word_t alloc_mask = 0x1;

/**
 * TODO: explain what size_mask is
 */
static const word_t size_mask = ~(word_t)0xF;

static const size_t seg_size = 10;

/** @brief Represents the header and payload of one block in the heap */
typedef struct block {
    /** @brief Header contains size + allocation flag */
    word_t header;
    union {
        struct {
            struct block *explicit_next;
            struct block *explicit_prev;

        } fb;
        char payload[0];
    };
} block_t;

/* Global variables */

/** @brief Pointer to first block in the heap */
static block_t *heap_start = NULL;
// static block_t *exp_start = NULL;
static block_t *seg_list[seg_size];

/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details for the functions that you write yourself!               *
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/**
 * @brief Returns the maximum of two integers.
 * @param[in] x
 * @param[in] y
 * @return `x` if `x > y`, and `y` otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}

/**
 * @brief Rounds `size` up to next multiple of n
 * @param[in] size
 * @param[in] n
 * @return The size after rounding up
 */
static size_t round_up(size_t size, size_t n) {
    return n * ((size + (n - 1)) / n);
}

/**
 * @brief Packs the `size` and `alloc` of a block into a word suitable for
 *        use as a packed value.
 *
 * Packed values are used for both headers and footers.
 *
 * The allocation status is packed into the lowest bit of the word.
 *
 * @param[in] size The size of the block being represented
 * @param[in] alloc True if the block is allocated
 * @return The packed value
 */
static word_t pack(size_t size, bool alloc) {
    word_t word = size;
    if (alloc) {
        word |= alloc_mask;
    }
    return word;
}

/**
 * @brief Extracts the size represented in a packed word.
 *
 * This function simply clears the lowest 4 bits of the word, as the heap
 * is 16-byte aligned.
 *
 * @param[in] word
 * @return The size of the block represented by the word
 */
static size_t extract_size(word_t word) {
    return (word & size_mask);
}

/**
 * @brief Extracts the size of a block from its header.
 * @param[in] block
 * @return The size of the block
 */
static size_t get_size(block_t *block) {
    dbg_requires(block != NULL);
    return extract_size(block->header);
}

/**
 * @brief Given a payload pointer, returns a pointer to the corresponding
 *        block.
 * @param[in] bp A pointer to a block's payload
 * @return The corresponding block
 */
static block_t *payload_to_header(void *bp) {
    return (block_t *)((char *)bp - offsetof(block_t, payload));
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        payload.
 * @param[in] block
 * @return A pointer to the block's payload
 * @pre The block must be a valid block, not a boundary tag.
 */
static void *header_to_payload(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0);
    return (void *)(block->payload);
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        footer.
 * @param[in] block
 * @return A pointer to the block's footer
 * @pre The block must be a valid block, not a boundary tag.
 */
static word_t *header_to_footer(block_t *block) {
    dbg_requires(get_size(block) != 0 &&
                 "Called header_to_footer on the epilogue block");
    return (word_t *)(block->payload + get_size(block) - dsize);
}

/**
 * @brief Given a block footer, returns a pointer to the corresponding
 *        header.
 * @param[in] footer A pointer to the block's footer
 * @return A pointer to the start of the block
 * @pre The footer must be the footer of a valid block, not a boundary tag.
 */
static block_t *footer_to_header(word_t *footer) {
    size_t size = extract_size(*footer);
    dbg_assert(size != 0 && "Called footer_to_header on the prologue block");
    return (block_t *)((char *)footer + wsize - size);
}

/**
 * @brief Returns the payload size of a given block.
 *
 * The payload size is equal to the entire block size minus the sizes of the
 * block's header and footer.
 *
 * @param[in] block
 * @return The size of the block's payload
 */
static size_t get_payload_size(block_t *block) {
    size_t asize = get_size(block);
    return asize - dsize;
}

/**
 * @brief Returns the allocation status of a given header value.
 *
 * This is based on the lowest bit of the header value.
 *
 * @param[in] word
 * @return The allocation status correpsonding to the word
 */
static bool extract_alloc(word_t word) {
    return (bool)(word & alloc_mask);
}

/**
 * @brief Returns the allocation status of a block, based on its header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) {
    return extract_alloc(block->header);
}

/**
 * @brief Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, and is marked as allocated.
 *
 * @param[out] block The location to write the epilogue header
 */
static void write_epilogue(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires((char *)block == mem_heap_hi() - 7);
    block->header = pack(0, true);
}

/**
 * @brief Writes a block starting at the given address.
 *
 * This function writes both a header and footer, where the location of the
 * footer is computed in relation to the header.
 *
 * TODO: Are there any preconditions or postconditions?
 *
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] alloc The allocation status of the new block
 */
static void write_block(block_t *block, size_t size, bool alloc) {
    dbg_requires(block != NULL);
    dbg_requires(size > 0);
    block->header = pack(size, alloc);
    word_t *footerp = header_to_footer(block);
    *footerp = pack(size, alloc);
}

/**
 * @brief Finds the next consecutive block on the heap.
 *
 * This function accesses the next block in the "implicit list" of the heap
 * by adding the size of the block.
 *
 * @param[in] block A block in the heap
 * @return The next consecutive block on the heap
 * @pre The block is not the epilogue
 */
static block_t *find_next(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called find_next on the last block in the heap");
    return (block_t *)((char *)block + get_size(block));
}

/**
 * @brief Finds the footer of the previous block on the heap.
 * @param[in] block A block in the heap
 * @return The location of the previous block's footer
 */
static word_t *find_prev_footer(block_t *block) {
    // Compute previous footer position as one word before the header
    return &(block->header) - 1;
}

/**
 * @brief Finds the previous consecutive block on the heap.
 *
 * This is the previous block in the "implicit list" of the heap.
 *
 * If the function is called on the first block in the heap, NULL will be
 * returned, since the first block in the heap has no previous block!
 *
 * The position of the previous block is found by reading the previous
 * block's footer to determine its size, then calculating the start of the
 * previous block based on its size.
 *
 * @param[in] block A block in the heap
 * @return The previous consecutive block in the heap.
 */
static block_t *find_prev(block_t *block) {
    dbg_requires(block != NULL);
    word_t *footerp = find_prev_footer(block);

    // Return NULL if called on first block in the heap
    if (extract_size(*footerp) == 0) {
        return mem_heap_lo();
    }

    return footer_to_header(footerp);
}

void print_heap(int line) {
    block_t *block;
    int a;
    dbg_printf("\n*************************\n");
    dbg_printf("\n HEAP PRINT:\n");
    dbg_printf("PROLOGUE: %p\n", mem_heap_lo());
    dbg_printf("=======================\n");
    for (block = heap_start; get_size(block) > 0; block = find_next(block)) {
        dbg_printf("=======================\n");
        dbg_printf("Address: %p : \n", block);
        a = get_alloc(block) ? 1 : 0;
        dbg_printf("Allocation status: %d\n", a);
        dbg_printf("Size: %lu\n", get_size(block));
        block_t *blk = find_prev(block);
        dbg_printf("Prev Block: %p\n", blk);
        a = get_alloc(blk) ? 1 : 0;
        dbg_printf("Prev_Alloc status: %d\n", a);
    }
    dbg_printf("=======================\n");
    int epilogue = (int)((char *)mem_heap_hi() - 7);
    dbg_printf("EPILOGUE: %x", epilogue);

    dbg_printf("\n*************************\n\n\n\n");
    return;
}

/*
 * ---------------------------------------------------------------------------
 *                        END SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/******** The remaining content below are helper and debug routines ********/

static size_t seg_index(size_t bSize) {
    dbg_assert(bSize >= min_block_size);
    size_t i, exp;
    exp = 5;

    for (i = 0; i < seg_size; i++) {
        if ((1 << (exp + i)) >= bSize) {
            if ((1 << (exp + i + 1)) >= bSize) {
                return i;
            }
        }
    }
    return seg_size - 1;
}

// Explicit List Implementation Helpers
static void explicitRemove(block_t *block) {
    dbg_assert(block != NULL);

    // block_t *temp = block;

    // size_t bSize = get_size(temp);
    // size_t index = seg_index(bSize);
    // temp = seg_list[index];

    // // dbg_printf("explicitRemove: \n");
    // // print_heap(__LINE__);

    // //Case 1: root == NULL -> return;
    // if (temp == NULL) return;
    // //Case 2:if there is only one elem in free list
    // if (temp->fb.explicit_next == temp &&
    //     temp->fb.explicit_prev == temp){
    //     temp = NULL;
    //     seg_list[index] = temp;
    //     return;
    // }
    // //Case 3: regular insertion
    // else{
    //     //Extra case: if we want to remove the first elem we can just switch
    //     pointer if (temp == block) temp = temp->fb.explicit_next;
    //     //normal case of switching pointers:
    //     //block->prev->next = block->next
    //     block->fb.explicit_prev->fb.explicit_next = block->fb.explicit_next;
    //     //block->next->prev = block->prev
    //     block->fb.explicit_next->fb.explicit_prev = block->fb.explicit_prev;
    //     seg_list[index] = temp;
    // }

    size_t index = seg_index(get_size(block));
    block_t *exp_start = seg_list[index];
    // EXPLICIT IMPLEMENTATION:
    // Case 1: root == NULL -> return;
    if (exp_start == NULL)
        return;
    // Case 2:if there is only one elem in free list
    if (exp_start->fb.explicit_next == exp_start &&
        exp_start->fb.explicit_prev == exp_start) {
        exp_start = NULL;
        return;
    }
    // Case 3: regular insertion
    else {
        // Extra case: if we want to remove the first elem we can just switch
        // pointer
        if (exp_start == block)
            exp_start = exp_start->fb.explicit_next;
        // normal case of switching pointers:
        // block->prev->next = block->next
        block->fb.explicit_prev->fb.explicit_next = block->fb.explicit_next;
        // block->next->prev = block->prev
        block->fb.explicit_next->fb.explicit_prev = block->fb.explicit_prev;
    }
}

static void explicitInsert(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) > 0);

    // dbg_printf("explicitInsert: \n");
    // print_heap(__LINE__);

    // block_t *temp;
    // size_t index = seg_index(get_size(block));
    // temp = seg_list[index];

    // // exp list is empty
    // if (temp == NULL){
    //     block->fb.explicit_prev = block;
    //     block->fb.explicit_next = block;
    //     temp = block;
    // } else {
    //     temp->fb.explicit_next->fb.explicit_prev = block;
    //     block->fb.explicit_next = temp->fb.explicit_next;
    //     temp->fb.explicit_next = block;
    //     block->fb.explicit_prev = temp;
    // }
    // seg_list[index] = temp;

    // EXPLICIT LIST IMPLEMENTATION:
    // exp list is empty

    size_t index = seg_index(get_size(block));
    block_t *exp_start = seg_list[index];

    if (exp_start == NULL) {
        block->fb.explicit_prev = block;
        block->fb.explicit_next = block;
        exp_start = block;
    } else {
        exp_start->fb.explicit_next->fb.explicit_prev = block;
        block->fb.explicit_next = exp_start->fb.explicit_next;
        exp_start->fb.explicit_next = block;
        block->fb.explicit_prev = exp_start;
    }
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] block
 * @return
 */

// Constant time Coalescing cases
// case 1: |allocated, block to be freed, allocated|
//       - free block and reset the header footer
// case 2: |allocated, block to be freed, free|
//       - free block and combine with other lower free block
// case 3: |free, block to be freed, allocated|
//       - free block and combine with other upper free block
// case 4: |free, block to be freed, free|
//       - free block and combine with other two free blocks

static block_t *coalesce_block(block_t *block) {
    if (block == NULL)
        return block;
    size_t blockSize = get_size(block);
    size_t leftBlockSize = 0;
    size_t rightBlockSize = 0;
    // check: if first block
    bool leftAlloc = 1;
    bool rightAlloc = get_alloc(find_next(block));

    block_t *pBlock = find_prev(block);
    block_t *nBlock = find_next(block);

    if (pBlock != NULL)
        leftAlloc = get_alloc(pBlock);
    if (!leftAlloc)
        leftBlockSize = get_size(pBlock);

    if (!rightAlloc)
        rightBlockSize = get_size(nBlock);

    // case 1: |allocated, block to be freed, allocated|
    if (leftAlloc && rightAlloc) {
        write_block(block, blockSize, false);
        explicitInsert(block);
    }

    // case 2: |allocated, block to be freed, free|
    if (leftAlloc && !rightAlloc) {
        explicitRemove(find_next(block));
        write_block(block, (blockSize + rightBlockSize), false);
        explicitInsert(block);
    }

    // case 3: |free, block to be freed, allocated|
    block_t *prev = find_prev(block);
    if (!leftAlloc && rightAlloc) {
        explicitRemove(prev);
        write_block(prev, (leftBlockSize + blockSize), false);
        explicitInsert(prev);
        // print_heap(__LINE__);

        return prev;
    }

    // case 4: |free, block to be freed, free|
    if (!leftAlloc && !rightAlloc) {
        explicitRemove(prev);
        explicitRemove(find_next(block));
        write_block(prev, (blockSize + leftBlockSize + rightBlockSize), false);
        explicitInsert(prev);
        // print_heap(__LINE__);

        return prev;
    }
    // print_heap(__LINE__);

    return block;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] size
 * @return
 */
static block_t *extend_heap(size_t size) {
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1) {
        return NULL;
    }
    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    write_block(block, size, false);

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_epilogue(block_next);

    // Coalesce in case the previous block was free
    if (block != heap_start && get_alloc(find_prev(block)) != 1) {
        block = coalesce_block(block);
    } else if (get_alloc(block) == 0)
        explicitInsert(block);

    return block;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] block
 * @param[in] asize
 */
static void split_block(block_t *block, size_t asize) {
    // dbg_requires(get_alloc(block));
    /* TODO: Can you write a precondition about the value of asize? */

    size_t block_size = get_size(block);

    if ((block_size - asize) >= min_block_size) {
        block_t *block_next;
        write_block(block, asize, true);
        explicitRemove(block);
        block_next = find_next(block);
        write_block(block_next, block_size - asize, false);

        explicitInsert(block_next);
    }

    dbg_ensures(get_alloc(block));
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] asize
 * @return
 */
static block_t *find_fit(size_t asize) {
    block_t *block;

    size_t index = seg_index(asize);
    block_t *temp = seg_list[index];

    dbg_printf("find_fit access: \n");

    if (temp == NULL) {
        dbg_printf("returned NULL \n");
        return NULL;
    }

    else if (asize <= get_size(temp)) {
        dbg_printf("returned exp_start \n");
        return temp;
    }

    // SEGLIST IMPLEMENTATION:
    // iterate through the seglist and the elements in each index to find fit
    else {

        // for (block = temp; get_size(block) != 0; block =
        // block->fb.explicit_next){

        //     dbg_printf("entered first loop \n");
        //     if (asize <= get_size(block) && !get_alloc(block)) return block;

        // }

        for (block = temp->fb.explicit_next; block != temp;
             block = block->fb.explicit_next) {

            dbg_printf("entered first loop \n");
            if (asize <= get_size(block) && !get_alloc(block) && block != NULL)
                return block;
        }
    }

    // EXPLICIT LIST IMPLEMENTATION
    // for (block = exp_start->fb.explicit_next; block != exp_start; block =
    // block->fb.explicit_next) {
    //     //dbg_printf("findFit call: \n");
    //     if (!(get_alloc(block)) && (asize <= get_size(block))) {
    //         return block;
    //     }
    // }
    return NULL; // no fit found
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] line
 * @return
 */

// mm_checkheap(int line) fucntion requirements
// 1. check epi/pro blocks: that that there are no blocks that have a size = 0
// and allocated = 1 (no empty alloc blocks)
// 2. check alignment: check that all the total block size are factors of 16
// 3. check addresses: make sure that all the addy's are within the "heap
// boundary limits" of possible addy's
// 4. check size: make sure that the blocks sizes are above the min alloc'd
// block size
// - check that the footer and the header are the same size
// 5. check coalesce: make sure that there are no consequtive free blocks on the
// list

// checking that start and end blocks are correct
bool checkStartEnd() {
    block_t *prologueBlock = (block_t *)((char *)mem_heap_lo());
    block_t *epilogueBlock = (block_t *)((char *)mem_heap_hi() - 7);

    // check: size = 0
    if (get_size(prologueBlock) != 0 || get_size(epilogueBlock) != 0) {
        printf("Error(checkHeap case 1): size != 0 \n");
        return false;
    }
    // check: alloc = 1
    if (get_alloc(prologueBlock) != 1 || get_alloc(epilogueBlock) != 1) {
        printf("Error(checkHeap case 1): alloc != 1 \n");
        return false;
    }
    return true;
}
// checking that each block is aligned
bool checkAlignment(block_t *startBlock) {

    if ((get_size(startBlock) % 16) != 0 || (size_t)startBlock % wsize != 0) {
        printf("Error(checkHeap case 2): Block not aligned \n");
        return false;
    }
    return true;
}
// checking if address is within range of valid addresses
bool checkAddresses(block_t *startBlock) {
    dbg_assert(startBlock != NULL);
    char *address;
    address = (char *)startBlock;

    if ((unsigned long)address % wsize != 0)
        return false;

    return true;
}
// checking that size is more than min and header == footer
bool checkBlockSize(block_t *startBlock) {
    // if (get_size(startBlock) % 16 != 0) return false;

    if (get_size(startBlock) < min_block_size) {
        printf("Error(checkHeap case 4): block size too small \n");
        return false;
    }
    if (startBlock->header != *(header_to_footer(startBlock))) {
        printf("Error(checkHeap case 4): invalid header and footer \n");
        return false;
    }
    return true;
}
// checking if you need to coalesce free blocks
bool checkCoalescing(block_t *startBlock) {

    if (get_alloc(startBlock) == 0 && get_alloc(find_next(startBlock)) == 0) {
        printf("Error(checkHeap case 5): coalesce \n");
        return false;
    }

    return true;
}

bool mm_checkheap(int line) {
    block_t *firstBlock = heap_start;
    checkStartEnd();

    for (block_t *tmp = firstBlock; get_size(tmp) > 0; tmp = find_next(tmp)) {
        checkAlignment(tmp);
        checkAddresses(tmp);
        checkBlockSize(tmp);
        checkCoalescing(tmp);
    }

    return true;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @return
 */
bool mm_init(void) {
    // Create the initial empty heap
    heap_start = NULL;
    // exp_start = NULL;
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));

    if (start == (void *)-1) {
        return false;
    }

    // initializing indexes of seg_list to NULL
    for (size_t i = 0; i < (size_t)seg_size; i++) {
        seg_list[i] = NULL;
    }

    start[0] = pack(0, true); // Heap prologue (block footer)
    start[1] = pack(0, true); // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1]);

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL) {
        return false;
    }

    return true;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] size
 * @return
 */
void *malloc(size_t size) {
    dbg_requires(mm_checkheap(__LINE__));

    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    // Initialize heap if it isn't initialized
    if (heap_start == NULL) {
        mm_init();
    }

    // Ignore spurious request
    if (size == 0) {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + dsize, dsize);

    // Search the free list for a fit
    // dbg_printf("entering find fit \n");
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL) {
        // Always request at least chunksize
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        // extend_heap returns an error
        if (block == NULL) {
            return bp;
        }
    }

    // The block should be marked as free
    dbg_assert(!get_alloc(block));

    // Mark block as allocated
    size_t block_size = get_size(block);
    explicitRemove(block);
    write_block(block, block_size, true);

    // Try to split the block if too large
    split_block(block, asize);

    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] bp
 */
void free(void *bp) {
    dbg_requires(mm_checkheap(__LINE__));

    if (bp == NULL) {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    // The block should be marked as allocated
    dbg_assert(get_alloc(block));

    // Mark the block as free
    write_block(block, size, false);

    // Try to coalesce the block with its neighbors
    block = coalesce_block(block);

    dbg_ensures(mm_checkheap(__LINE__));
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] ptr
 * @param[in] size
 * @return
 */
void *realloc(void *ptr, size_t size) {
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0) {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL) {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);

    // If malloc fails, the original block is left untouched
    if (newptr == NULL) {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if (size < copysize) {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] elements
 * @param[in] size
 * @return
 */
void *calloc(size_t elements, size_t size) {
    void *bp;
    size_t asize = elements * size;

    if (elements == 0) {
        return NULL;
    }
    if (asize / elements != size) {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL) {
        return NULL;
    }

    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/*
 *****************************************************************************
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a c5 7c fc 80 6e 57 0a               *
 *                                                                           *
 *****************************************************************************
 */
