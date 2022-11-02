// mm_implicit.c // first-fit -> 53점, next-fit -> 81,80,79점, best-fit -> 53점
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
    "3team",
    /* First member's full name */
    "Sungtae Kim",
    /* First member's email address */
    "devsungtae@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8 // double word alignment

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// 가용 리스트 조작을 위한 기본 상수와 매크로
/* Basic constants and macros */
#define WSIZE 4             /* Word and header/footer size (bytes) */
#define DSIZE 8             /* Double word size (bytes) */
#define CHUNKSIZE (1 << 12) /* Extend heap by this amount (bytes) 2^12 -> 초기 가용블록과 힙 확장을 위한 기본크기*/

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word 가용리스트를 접근하고 방문하는 작은 매크로 */
#define PACK(size, alloc) ((size) | (alloc))    // pack 매크로 -> 크기와 할당비트를 통합해서 헤더와 풋터에 저장할 수 있는 값을 리턴
                                                // '|' OR 비트연산자
/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))   // get -> 파라미터 p가 참조하는 워드를 읽어 리턴
#define PUT(p, val) (*(unsigned int *)(p) = (val))  // put -> 파라미터 p가 가르키는 워드에 val 저장
/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7) // 주소 p에 있는 헤더 또는 풋터의 size와 할당 비트 리턴 // ~0x7 -> 맨뒤 3개의 0을 제외하고 모두 1 만들고 그걸 곱함
#define GET_ALLOC(p) (GET(p) & 0x1) 
/* Given block ptr bp, compute address of its header and footer */
// bp -> 블록 포인터
#define HDRP(bp) ((char *)(bp) - WSIZE) // header pointer - header 가르킴
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // footer pointer - footer 가르킴
/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // next block pointer - 다음 블록의 bp
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // previous block pointer - 이전 블록의 bp

// pointer 미리 선언
static void *heap_listp;
static char *last_bp;

// 추가함수
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                             /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        /* Epilogue header */
    heap_listp += (2*WSIZE);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */ // CHUNKSIZE = 2^12
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/* extend_heap 함수 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;  // 요청한 크기를 2word(8bytes)의 배수로 반올림한다
    if ((long)(bp = mem_sbrk(size)) == -1)  // mem_sbrk를 통해 추가적인 힙 공간 요청
        return NULL;
    
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));           /* Free block header */ // 'HDRP'->header를 가르팀, PACK->헤더에 들어갈 값 넣어줌 
    PUT(FTRP(bp), PACK(size, 0));           /* Free block footer */ // 'FTRP'->footer를 가르킴, PACK->헤더에 들어갈 값 넣어줌
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   /* New epilogue header */ // 'NEXT_BLKP'->다음 블록의 bp를 가르킴

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;   /* Adjusted block size */
    size_t extendsize;  /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;
    
    /* Adjust block size to 1. allow room for the header and footer 2. satisfy the double-word alignment requests */
    if (size <= DSIZE)  
        asize = 2*DSIZE;    // minimum 블록 size를 16bytes로 두기   
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); // 8바이트 넘는 요청에 대해서, overhead 바이트를 추가하고 8배수로 반올림
    
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {  // 적합한 free list를 찾음
        place(bp, asize);   // 찾은 경우 블록을 배치하고 옵션으로 초과 부분을 분할한다 
        last_bp = bp;   // last-fit을 위해 이전에 탐색한 bp를 last_bp에 저장
        return bp;  // 새롭게 할당된 블록의 주소를 return
    }

    /* No fit found. Get more memory and place the block */ // 적합한 free list를 찾지 못한 경우 
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)   // heap을 extend한다
        return NULL;
    place(bp, asize);   // 요청된 블록을 새로운 free 블록에 배치하고, optionally splitting한다
    last_bp = bp;   // last-fit을 위해 이전에 탐색한 bp를 last_bp에 저장
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));   // 'HDRP'->header를 가르킴, size 리턴
    
    PUT(HDRP(bp), PACK(size, 0));   //  bp가 헤더 가르킴
    PUT(FTRP(bp), PACK(size, 0));   //  bp가 footer 가르킴
    coalesce(bp);   // 
}

/*
* coalesce - 연결함수
*/
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // GET_ALLOC(이전 블록의 footer) -> 항상 할당된 상태
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // GET_ALLOC(다음 블록의 header) -> 항상 할당된 상태
    size_t size = GET_SIZE(HDRP(bp));   // 헤더에 적힌 현재 size

    /* Case 1 */ 
    if (prev_alloc && next_alloc) { // 이전과 다음 블록이 모두 allocated
        last_bp = bp;               // last_bp 업데이트
        return bp;                  
    }

    /* Case 2 */
    else if (prev_alloc && !next_alloc) { // 이전 블록은 allocated, 다음 블록은 free
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));  // 다음 블록의 header에 적혀있는 크기를 size에 더해준다
        PUT(HDRP(bp), PACK(size, 0));   // header에 size값 넣어줌
        PUT(FTRP(bp), PACK(size, 0));   // footer에 size값 넣어줌
    }

    /* Case 3 */
    else if (!prev_alloc && next_alloc) {   // 이전 블록은 free, 다음 블록은 allocated
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));  // 이전 블록의 header에 적혀있는 크기를 size에 더해준다
        PUT(FTRP(bp), PACK(size, 0));           // footer에 size값 넣어줌
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));    // 이전 블록의 header에 size값 넣어줌
        bp = PREV_BLKP(bp);
    }

    /* Case 4 */
    else {  // 이전 블록과 다음 블록이 모두 free
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));// 이전 블록의 header에 적혀있는 크기와 
                  // 다음 블록의 footer에 적혀있는 크기를 size에 더해준다
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));    // 이전 블록의 header에 size값 넣어줌
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));    // 다음 블록의 footer에 size값 넣어줌
        bp = PREV_BLKP(bp); // block pointer를 이전 블록의 bp 위치로 바꿔줌
    }
    last_bp = bp;           // last_bp 업데이트
    return bp;
}

/*
   기존에 malloc으로 동적 할당된 메모리 크기를 변경시켜주는 함수
   현재 메모리에 bp가 가르키는 사이즈를 할당한 만큼 충분하지 않다면 메모리의 다른 공간의 기존 크기의 공간 할당 + 기존에 있던 데이터를 복사한 후 추가로 메모리 할당
*/
void *mm_realloc(void *bp, size_t size) {

    void *oldptr = bp;  // 크기를 조절하고 싶은 힙의 시작 포인터
    void *nextptr;
    void *newptr;       // 크기 조절 뒤, 새 힙의 시작 포인터
    
    size_t asize = ALIGN(size) + DSIZE;
    
    size_t copySize = GET_SIZE(HDRP(oldptr));  // 복사할 기존 메모리의 사이즈를 oldptr로부터 가져오기  // 복사할 힙의 크기
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(oldptr))); // GET_ALLOC(직후 블록의 header) -> 직후 블록 가용 여부
    size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(oldptr)));   // 직후블록 size
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    copySize = GET_SIZE(HDRP(oldptr));  // ?
    if (size < copySize)
      copySize = size;
    // 메모리의 특정한 부분으로부터 얼마까지의 부분을 다른 메모리 영역으로 복사해주는 함수
    // oldptr로부터 copySize만큼의 문자를 newptr에 복사
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

/*
 * find_fit -> first-fit 방법
 */
// static void *find_fit(size_t asize)    
// {
//     /* First-fit search */
//     void *bp;

//     // heap list pointer로 맨 앞부터 모든 블록을 본다
//     for (bp = (char *)heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) { 
//         if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {    // 만약 해당 블록이 free 상태이고, size가 asize보다 크다면
//             return bp;  // block pointer 반환
//         }
//     }
//     return NULL; /* No fit */ // 못찾은 경우
// }

/*
 * find_fit -> next-fit 방법
 */
static void *find_fit(size_t asize)
{
    /* Next-fit search */
    char *bp = last_bp;
    
    for (bp = NEXT_BLKP(bp); GET_SIZE(HDRP(bp)) != 0; bp = NEXT_BLKP(bp)) { // 시작은 last_bp의 다음부터, size가 0이 아닐 때 for문 돌리기
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize) {  // free 블록이고 size가 asize보다 크거나 같으면
            last_bp = bp;   // last_bp 저장해두기
            return bp;      // bp 반환
        }
    }

    // next에서 못찾을 경우 처음부터 다시 찾음
    bp = heap_listp;        // bp를 heap_listp로 
    while (bp < last_bp) {  // bp가 last_bp보다 작을 때까지
        bp = NEXT_BLKP(bp); 
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize) {  // free 블록 중에 size가 asize보다 크거나 같으면
            last_bp = bp;   // last_bp 업데이트
            return bp;
        }
    }
    return NULL;
}

/*
 * find_fit -> best-fit 방법
 */
// static void *find_fit(size_t asize)
// {
//     /* Best-fit search */
//     void *bp;
//     void *min_bp = NULL;

//     size_t min = 0xffffff;
//     // min값 찾기
//     for (bp = (char *)heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
//         if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))) && (GET_SIZE(HDRP(bp)) < min)) {  // free 블록이고, size가 asize보다 크거나 같고, size가 min 값보다 작다면
//             min = GET_SIZE(HDRP(bp));   // min값을 업데이트 
//             min_bp = bp;
//         }
//     }

//     if (min != 0xffffff) {  // 찾은 경우 
//         return min_bp;
//     }
//     return NULL;    /* No fit */    // 못찾은 경우
// }


/*
 * place
 */
static void place(void *bp, size_t asize)   // 블록을 배치, 블록의 크기가 크면 분할함
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2*DSIZE)) { // 블록의 크기가 asize보다 크고 그 차이가 4word보다 크거나 같은 경우
        PUT(HDRP(bp), PACK(asize, 1));  // asize만큼 할당시키고 헤더에 값 넣기
        PUT(FTRP(bp), PACK(asize, 1));  // footer에 값 넣기
        bp = NEXT_BLKP(bp);             // bp를 다음 블록의 block pointer로 옮기기
        PUT(HDRP(bp), PACK(csize-asize, 0));    // csize-asize만큼 남은 블록의 헤더에 값 넣기
        PUT(FTRP(bp), PACK(csize-asize, 0));    // footer에 값 넣기 
    }

    else {                              // 블록의 크기의 차이가 4word보다 작은 경우 - 분할하지 않아도 딱 들어맞는 경우
        PUT(HDRP(bp), PACK(csize, 1));  // csize만큼 할당시키고 헤더에 값 넣기
        PUT(FTRP(bp), PACK(csize, 1));  // footer에 값 넣기
    }
}











