// mm_explicit.c -> 83점, mm_realloc() 최적화
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

/* 메모리 할당 시 기본적으로 header와 footer를 위해 필요한 더블워드만큼의 메모리 크기 */
#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) // SIZE_T_SIZE = 8bytes = ALIGN(4) // size_t = 4bytes

// 가용 리스트 조작을 위한 기본 상수와 매크로
/* Basic constants and macros */
#define WSIZE 4             /* Word and header/footer size (bytes) */
#define DSIZE 8             /* Double word size (bytes) */
#define MINIMUM 16          /* Initial Prologue block size, header, footer, PREC, SUCC */
#define CHUNKSIZE (1 << 12) /* Extend heap by this amount (bytes) 2^12 -> 초기 가용블록과 힙 확장을 위한 기본크기*/

#define MAX(x, y) ((x) > (y) ? (x) : (y))   // 최대값 구하는 매크로

/* Pack a size and allocated bit into a word 가용리스트를 접근하고 방문하는 작은 매크로 */
// PACK - header 및 footer 값(size + allocated) return
#define PACK(size, alloc) ((size) | (alloc))    // pack 매크로 -> 크기와 할당비트를 통합해서 헤더와 풋터에 저장할 수 있는 값을 리턴
                                                // '|' OR 비트연산자

/* Read and write a word at address p */
// 주소 p에서의 word를 읽거나 쓰는 매크로
#define GET(p) (*(unsigned int *)(p))   // get -> 파라미터 p가 참조하는 워드를 읽어 리턴
#define PUT(p, val) (*(unsigned int *)(p) = (val))  // put -> 파라미터 p가 가르키는 워드에 val 저장

/* Read the size and allocated fields from address p */
// header 혹은 footer에서 블록의 size 혹은 allocated field를 읽어옴
#define GET_SIZE(p) (GET(p) & ~0x7) // 주소 p에 있는 header 또는 footer의 size와 할당 비트 리턴 // ~0x7 -> 맨뒤 3개의 0을 제외하고 모두 1 만들고 그걸 곱함
#define GET_ALLOC(p) (GET(p) & 0x1) 

/* Given block ptr bp, compute address of its header and footer */
// 블록 포인터 bp를 인자로 받아 블록의 header와 footer의 주소를 반환
#define HDRP(bp) ((char *)(bp) - WSIZE) // header pointer - header 가르킴
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // footer pointer - footer 가르킴

/* Given block ptr bp, compute address of next and previous blocks */
// 블록 포인터 bp를 인자로 받아 이후 블록, 이전 블록의 주소를 반환
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // (char *)(bp) + GET_SIZE(지금 블록의 header값)
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // (char *)(bp) - GET_SIZE(이전 블록의 footer값)

/* Free List 상에서의 이전, 이후 블록의 포인터를 리턴 */
#define PREC_FREEP(bp) (*(void**)(bp))          // 이전 블록의 bp ///////////??????????????????????????????
#define SUCC_FREEP(bp) (*(void**)(bp + WSIZE))  // 이후 블록의 bp

/* define searching method for find suitable free blocks to allocate */
// #define NEXT_FIT  // define하면 next_fit, 안 하면 first_fit으로 탐색

/* global variable & functions */
static char* heap_listp = NULL; // 항상 prologue block을 가리키는 정적 전역 변수 설정
static char* free_listp = NULL; // free list의 맨 첫 블록을 가리키는 포인터

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

int mm_init(void);
void *mm_malloc(size_t size);
void mm_free(void *bp);
void *mm_realloc(void *bp, size_t size);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap */ // 메모리에서 6word 가져오고 이걸로 빈 free 리스트 초기화
    /* alignment padding, prologue header, PREC, SUCC, prologue footer, epilogue header*/    // 
    if ((heap_listp = mem_sbrk(6*WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);                             /* Alignment padding */ // double word aligned 미사용 패딩
    PUT(heap_listp + (1*WSIZE), PACK(MINIMUM, 1));    /* Prologue header */ // MINIMUM = 16bytes = 4word
    PUT(heap_listp + (2*WSIZE), NULL);  // prologue block 안의 PREC 포인터 NULL로 초기화
    PUT(heap_listp + (3*WSIZE), NULL);  // prologue block 안의 SUCC 포인터 NULL로 초기화
    PUT(heap_listp + (4*WSIZE), PACK(MINIMUM, 1));    /* Prologue footer */
    PUT(heap_listp + (5*WSIZE), PACK(0, 1));        /* Epilogue header */
    
    free_listp = heap_listp + 2*WSIZE;  // free_listp를 탐색의 시작점으로 둔다

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */ // CHUNKSIZE = 2^12
    // CHUNKSIZE만큼 힙을 확장하여 힙을 초기화 
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)   // 실해하면 -1 리턴
        return -1;
    return 0;
}

/* extend_heap 함수 */ // word 단위 메모리를 인자로 받아 힙을 늘려준다. 
static void *extend_heap(size_t words)  // word 단위로 받는다
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    /* 더블 워드 정렬에 따라 메모리를 mem_sbrk 함수를 이용해 할당받는다 */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;  // 요청한 크기를 2word(8bytes)의 배수로 반올림한다 // size를 짝수 word && byte 형태로 만든다
    if ((long)(bp = mem_sbrk(size)) == -1)  // 새 메모리의 첫 부분을 bp로 둔다. 주소값은 int로 못 받기에 long으로 casting
        return NULL;
    
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));   // header  /* Free block header */ // 'HDRP'->header를 가르팀, PACK->헤더에 들어갈 값 넣어줌 
    PUT(FTRP(bp), PACK(size, 0));   // footer  /* Free block footer */ // 'FTRP'->footer를 가르킴, PACK->헤더에 들어갈 값 넣어줌
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 새 에필로그 헤더 /* New epilogue header */ // 'NEXT_BLKP'->다음 블록의 bp를 가르킴

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

    /* 가짜요청 spurious requests 무시 */
    if (size == 0)
        return NULL;
    
    // 요청 사이즈에 header와 footer를 위한 dword 공간(SIZE_T_SIZE)을 추가한 후 align 해준다. // SIZE_T_SIZE = 8bytes = 2words
    asize = ALIGN(size + SIZE_T_SIZE);

    // 할당할 free list를 찾아, 필요하다면 분할해서 할당한다
    if ((bp = find_fit(asize)) != NULL) {  // first-fit으로 추적    ///////////[[[ First-fit ]]]//////////
        place(bp, asize);   // 필요하다면 분할해서 할당한다.
        return bp;  // 새롭게 할당된 블록의 주소를 return
    }

    // 만약 맞는 크기의 가용 블록이 없는 경우, 힙을 늘려서 새로운 메모리를 할당한다. 
    extendsize = MAX(asize, CHUNKSIZE); // 둘 중 더 큰 값으로 size 정한다.
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)   // heap을 extend한다
        return NULL;
    place(bp, asize);   // 요청된 블록을 새로운 free 블록에 배치하고, optionally splitting한다
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));   // 해당 블록의 size를 받음
    
    // header와 footer의 설정을 바꿔줌 -> 블록 크기를 0으로 만들기
    PUT(HDRP(bp), PACK(size, 0));   //  header에 블록 크기를 0으로
    PUT(FTRP(bp), PACK(size, 0));   //  footer에 블록 크기를 0으로

    // 앞뒤블록과 연결할 수 있다면 연결한다. 
    coalesce(bp);   
}

/*
* coalesce - 연결함수 - 해당 free 블록을 앞뒤 free 블록과 연결하고, 연결된 free 블록의 주소를 반환한다. 
*/
static void *coalesce(void *bp)
{   // 직전 블록의 footer, 직후 블록의 header를 보고 free 여부를 확인
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // GET_ALLOC(직전 블록의 footer) -> 직전 블록 가용 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // GET_ALLOC(직후 블록의 header) -> 직후 블록 가용 여부
    size_t size = GET_SIZE(HDRP(bp));   // 헤더에 적힌 현재 size

    // case 1 : 직전, 직후 블록이 모두 할당 -> 연결할 필요 없음 -> 해당 블록만 free list에 넣어주면 됨

    // case 2 : 직전 블록 할당, 직후 블록 free
    if (prev_alloc && !next_alloc) { 
        removeBlock(NEXT_BLKP(bp)); // free 상태였던 직후 블록을 free list에서 제거한다. 
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));  // 직후 블록의 header에 적혀있는 크기를 size에 더해준다
        PUT(HDRP(bp), PACK(size, 0));   // header에 size값 넣어줌
        PUT(FTRP(bp), PACK(size, 0));   // footer에 size값 넣어줌
    }

    // case 3 : 직전 블록 free, 직후 블록 할당
    else if (!prev_alloc && next_alloc) {   
        removeBlock(PREV_BLKP(bp)); // free 상태였던 직전 블록을 free list에서 제거한다.
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));  // 직전 블록의 header에 적혀있는 크기를 size에 더해준다
        bp = PREV_BLKP(bp); // bp를 직전 블록의 bp로 갱신
        PUT(HDRP(bp), PACK(size, 0));   // 직전 블록의 header 자리 = 갱신된 블록의 header에 size값 넣어줌
        PUT(FTRP(bp), PACK(size, 0));   // footer에 size값 넣어줌
    }

    // case 4 : 직전 블록 free, 직후 블록 free
    else if (!prev_alloc && !next_alloc) { 
        removeBlock(PREV_BLKP(bp)); // free 상태였던 직전 블록을 free list에서 제거
        removeBlock(NEXT_BLKP(bp)); // free 상태였던 직후 블록을 free list에서 제거
        // 이전 블록의 header에 적혀있는 크기와 다음 블록의 footer에 적혀있는 크기를 size에 더해준다
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); 
        bp = PREV_BLKP(bp); // bp를 직전 블록의 bp로 갱신
        PUT(HDRP(bp), PACK(size, 0));   // header에 size값 넣어줌
        PUT(FTRP(bp), PACK(size, 0));   // footer에 size값 넣어줌
    }

    // 연결된 새 free 블록을 free list에 추가
    putFreeBlock(bp);

    return bp;
}

/*
 * mm_realloc : Implemented simply in terms of mm_malloc and mm_free

   기존에 malloc으로 동적 할당된 메모리 크기를 변경시켜주는 함수
   현재 메모리에 bp가 가르키는 사이즈를 할당한 만큼 충분하지 않다면 메모리의 다른 공간의 기존 크기의 공간 할당 + 기존에 있던 데이터를 복사한 후 추가로 메모리 할당
*/
void *mm_realloc(void *bp, size_t size) {   // realloc 최적화 완료

    void *oldptr = bp;  // 크기를 조절하고 싶은 힙의 시작 포인터
    void *nextptr;
    void *newptr;       // 크기 조절 뒤, 새 힙의 시작 포인터
    
    size_t asize = ALIGN(size) + DSIZE;
    
    size_t copySize = GET_SIZE(HDRP(oldptr));  // 복사할 기존 메모리의 사이즈를 oldptr로부터 가져오기  // 복사할 힙의 크기
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(oldptr))); // GET_ALLOC(직후 블록의 header) -> 직후 블록 가용 여부
    size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(oldptr)));   // 직후블록 size

    // [[[  뒤로 붙이는 경우  ]]]
    if (!next_alloc && (copySize + next_size >= asize)) {   // 뒤가 free이고, 합쳤을 때 최대 크기가 size보다 큰 경우

        // [[[ 다음 블록이 끝인경우 ]]]
        if (next_size == 0) {
            extend_heap(MAX(asize-copySize, CHUNKSIZE));
            next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(oldptr))); 
            next_size = GET_SIZE(HDRP(NEXT_BLKP(oldptr)));
        }

        // 분할이 필요한 경우
        if ((copySize + next_size - asize) >= (24)) {   // 24 최소크기 -> header + footer + data(8) 
            // 앞 블록 할당
            removeBlock(NEXT_BLKP(oldptr));         // free 상태였던 직후 블록을 free list에서 제거한다. 
            PUT(HDRP(oldptr), PACK(asize, 1));      // header에 size값 넣어줌
            PUT(FTRP(oldptr), PACK(asize, 1));      // footer에 size값 넣어줌

            // 뒤의 블록은 free 블록으로 분할
            nextptr = NEXT_BLKP(oldptr);            // 뒤의 블록을 nextptr로
            PUT(HDRP(nextptr), PACK(copySize + next_size-asize, 0));    // csize-asize만큼 남은 블록의 헤더에 값 넣기
            PUT(FTRP(nextptr), PACK(copySize + next_size-asize, 0));    // footer에 값 넣기 
            coalesce(nextptr);                      

            return oldptr;
        }
        // 분할 불가능한 경우
        else {  // 블록의 크기의 차이가 4word보다 작은 경우 
            removeBlock(NEXT_BLKP(oldptr)); // free 상태였던 직후 블록을 free list에서 제거한다. 
            PUT(HDRP(oldptr), PACK(copySize + next_size, 1));   // header에 size값 넣어줌
            PUT(FTRP(oldptr), PACK(copySize + next_size, 1));   // footer에 size값 넣어줌
            return oldptr;
        }  
    }
    
    // [[[  기존 방법  ]]]
    newptr = mm_malloc(asize);   // 새로운 크기로 malloc
    if (newptr == NULL) // 실패 시 NULL 반환
      return NULL;

    // 원래 메모리 크기보다 적은 크기를 realloc하면 크기에 맞는 메모리만 할당되고 나머지는 안된다
    if (asize < copySize)
      copySize = asize;

    // 메모리의 특정한 부분으로부터 얼마까지의 부분을 다른 메모리 영역으로 복사해주는 함수
    // oldptr로부터 copySize만큼의 문자를 newptr에 복사
    memcpy(newptr, oldptr, copySize);   // newptr에 oldptr를 시작으로 copySize만큼의 메모리 값을 복사한다.
    mm_free(oldptr);    // 기존의 힙을 반환한다. 
    return newptr;
}

/*
 * find_fit -> first-fit 방법 : 힙의 맨 처음부터 탐색하여 요구하는 메모리 공간보다 큰 가용 블록의 주소를 반환한다. 
 */
static void *find_fit(size_t asize)    // first-fit 방법
{
    /* First-fit search */
    void *bp;

    // free list의 맨 끝은 프롤로그 블록이다. Free list에서 유일하게 할당된 블록이다. -> 만나면 탐색 종료
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = SUCC_FREEP(bp)) { 
        if (asize <= GET_SIZE(HDRP(bp))) {    // 만약 탐색한 free 블록의 size가 asize보다 크거나 같다면
            return bp;  // block pointer 반환
        }
    }
    return NULL;    // 못 찾으면 NULL을 반환
}

/*
 * place : 요구한 메모리를 가용 블록에 할당함, 분할이 필요하면 분할함
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));  // 현재 할당할 수 있는 후보 free 블록의 size

    removeBlock(bp);    // 할당될 블록이므로 free list에서 제거

    // 분할이 필요한 경우
    if ((csize - asize) >= (2*DSIZE)) { // 블록의 크기가 asize보다 크고 그 차이가 4word보다 크거나 같은 경우
        // 앞의 블록은 할당 블록으로
        PUT(HDRP(bp), PACK(asize, 1));  // asize만큼 할당시키고 header에 값 넣기
        PUT(FTRP(bp), PACK(asize, 1));  // footer에 값 넣기

        // 뒤의 블록은 free 블록으로 분할
        bp = NEXT_BLKP(bp);             // bp를 다음 블록의 block pointer로 옮기기
        PUT(HDRP(bp), PACK(csize-asize, 0));    // csize-asize만큼 남은 블록의 헤더에 값 넣기
        PUT(FTRP(bp), PACK(csize-asize, 0));    // footer에 값 넣기 

        // free list의 첫번째에 분할된 블록 넣기
        putFreeBlock(bp);
    }
    // 분할 불가능한 경우
    else {                              // 블록의 크기의 차이가 4word보다 작은 경우 - 분할하지 않아도 딱 들어맞는 경우
        PUT(HDRP(bp), PACK(csize, 1));  // csize만큼 할당시키고 헤더에 값 넣기
        PUT(FTRP(bp), PACK(csize, 1));  // footer에 값 넣기
    }
}

/*
 * putFreeBlock(bp) : 새로 free되거나 생성된 free 블록을 free list의 첫번째에 넣는다. 
 */
void putFreeBlock(void* bp)
{
    // bp로 받은 블록을 free list의 맨 앞에 넣어준다.
    SUCC_FREEP(bp) = free_listp;    // 직후 블록의 bp를 free_listp 즉, free list의 맨 첫번째 블록을 가리키는 포인터로 둠    
    PREC_FREEP(bp) = NULL;          // 직전 블록의 bp를 NULL로 처리
    PREC_FREEP(free_listp) = bp;    // 맨 첫번째 블록의 직전 블록을 bp로 설정
    free_listp = bp;
}

/*
 * removeBlock(bp) : 할당되거나 연결되는 free 블록을 free list에서 없앤다.
 */
 void removeBlock(void *bp)
 {
    // free list의 첫번째 블록을 없앨 때
    if (bp == free_listp) {
        PREC_FREEP(SUCC_FREEP(bp)) = NULL; // 직후 블록(두번째 블록)의 직전을 NULL로 없애준다
        free_listp = SUCC_FREEP(bp);    //  두번째 블록이 첫번째 블록이 됨
    }
    // free list 안에 있는 블록을 없앨 때
    else {
        SUCC_FREEP(PREC_FREEP(bp)) = SUCC_FREEP(bp);   // 직전 블록의 직후를 현재블록이 아니라 현재블록의 직후 블록으로 바꿔준다 -> 현재블록 없앰
        PREC_FREEP(SUCC_FREEP(bp)) = PREC_FREEP(bp);   // 직후 블록의 직전을 현재블록이 아니라 현재블록의 직전 블록으로 바꿔준다
    }
 }


