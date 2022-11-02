// mm_segregated.c -> 85점
// https://velog.io/@gitddabong/week06.-malloc-lab-Segregated-list 참고
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
#define CHUNKSIZE (1 << 12) /* Extend heap by this amount (bytes) 2^12 -> 초기 가용블록과 힙 확장을 위한 기본크기*/
#define INITCHUNKSIZE (1<<6)    // 64
#define LISTLIMIT 20
#define REALLOC_BUFFER (1<<7)   // 128

#define MAX(x, y) ((x) > (y) ? (x) : (y))   // 최대값 구하는 매크로

/* Pack a size and allocated bit into a word 가용리스트를 접근하고 방문하는 작은 매크로 */
// PACK - header 및 footer 값(size + allocated) return
#define PACK(size, alloc) ((size) | (alloc))    // pack 매크로 -> 크기와 할당비트를 통합해서 헤더와 풋터에 저장할 수 있는 값을 리턴                                               

/* Read and write a word at address p */
// 주소 p에서의 word를 읽거나 쓰는 매크로
#define GET(p) (*(unsigned int *)(p))   // get -> 파라미터 p가 참조하는 워드를 읽어 리턴
#define PUT(p, val) (*(unsigned int *)(p) = (val))  // put -> 파라미터 p가 가르키는 워드에 val 저장

/* Read the size and allocated fields from address p */
// header 혹은 footer에서 블록의 size 혹은 allocated field를 읽어옴
#define GET_SIZE(p) (GET(p) & ~0x7) // 주소 p에 있는 header 또는 footer의 size와 할당 비트 리턴 // ~0x7 -> 맨뒤 3개의 0을 제외하고 모두 1 만들고 그걸 곱함 -> 블록 사이즈 (header+footer+payload+padding)
#define GET_ALLOC(p) (GET(p) & 0x1) 

/* Given block ptr bp, compute address of its header and footer */
// 블록 포인터 bp를 인자로 받아 블록의 header와 footer의 주소를 반환
#define HDRP(bp) ((char *)(bp) - WSIZE) // header pointer - header 가르킴
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // footer pointer - footer 가르킴

/* Given block ptr bp, compute address of next and previous blocks */
// 블록 포인터 bp를 인자로 받아 이후 블록, 이전 블록의 주소를 반환
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // (char *)(bp) + GET_SIZE(지금 블록의 header값)
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // (char *)(bp) - GET_SIZE(이전 블록의 footer값)

// 포인터 p가 가리키는 메모리에 포인터 ptr을 입력
#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))

// 가용 블록 리스트에서 next와 prev의 포인터를 반환
#define NEXT_PTR(ptr) ((char *)(ptr))
#define PREV_PTR(ptr) ((char *)(ptr) + WSIZE)

// segregated list 내에서 next와 prev의 포인터를 반환
#define NEXT(ptr) (*(char **)(ptr))
#define PREV(ptr) (*(char **)(PREV_PTR(ptr)))

/* global variable & functions */
char *heap_listp = 0; // 항상 prologue block을 가리키는 정적 전역 변수 설정
void *segregated_free_lists[LISTLIMIT];

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void insert_node(void *ptr, size_t size);
static void delete_node(void *ptr);

int mm_init(void);
void *mm_malloc(size_t size);
void mm_free(void *bp);
void *mm_realloc(void *bp, size_t size);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    int list;

    for (list = 0; list < LISTLIMIT; list++) {  // segregated_free_lists의 모든 원소를 NULL로 초기화
        segregated_free_lists[list] = NULL;     
    }

    /* Create the initial empty heap */ 
    /* alignment padding, prologue header, prologue footer, epilogue header*/
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                             /* Alignment padding */ 
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    /* Prologue header */ 
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        /* Epilogue header */
    heap_listp += (2*WSIZE);

    /* Extend the empty heap with a free block of INITCHUNKSIZE = 2^6 */
    // INITCHUNKSIZE만큼 힙을 확장하여 힙을 초기화 
    if (extend_heap(INITCHUNKSIZE) == NULL)   // 실해하면 -1 리턴
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
    insert_node(bp, size);  // free list에 새로 할당받은 영역 추가

    /* Coalesce if the previous block was free */
    return coalesce(bp);    // 새로 할당받은 free 블록 리스트를 기존 free 블록 리스트에 합치기
}

/*
 * insert_node : free list에 size크기의 블록 추가
 */
 static void insert_node(void *ptr, size_t size) {
    int idx = 0;    // 리스트의 인덱스
    void *search_ptr = ptr;
    void *insert_ptr = NULL;    // 실제 노드가 삽입되는 위치    

    // Select segregated list
    // 2의 지수 승으로 인덱스를 나누어 리스트를 관리
    // size의 비트를 하나씩 제거하며 카운트를 세면, 그 카운트 수가 리스트의 index가 됨
    while ((idx < LISTLIMIT - 1) && (size > 1)) {   // 리스트의 인덱스 계산
        size >>= 1;
        idx++;
    }

    // keep size ascending order and search
    search_ptr = segregated_free_lists[idx];    // search_ptr를 계산한 index에 위치시키기
    // 1. 첫 삽입이라면 search_ptr이 null이므로 반복문을 거치지 않음
    // 2. 만약 이 위치에 삽입이 되어있다면 null이 아님, 기존 블록의 사이즈보다 만들고자하는 사이즈가 더 크면 반복문 시작
    while ((search_ptr != NULL) && (size > GET_SIZE(HDRP(search_ptr)))) {
        insert_ptr = search_ptr;        // insert ptr을 search_ptr로 
        search_ptr = NEXT(search_ptr);  // 다음 블록 탐색
    }

    // 이전 - insert_ptr, 이후 - search_ptr
    // Set NEXT and PREV
    if (search_ptr != NULL) {
        if (insert_ptr != NULL) {   // 이전, 이후 블록이 모두 NULL이 아닌 경우
            SET_PTR(NEXT_PTR(ptr), search_ptr); // 새 블록의 next를 이후 블록 주소로 변경
            SET_PTR(PREV_PTR(search_ptr), ptr); // 이후 블록의 prev를 새 블록으로 변경
            SET_PTR(PREV_PTR(ptr), insert_ptr); // 새 블록의 prev를 이전 블록 주소로 변경
            SET_PTR(NEXT_PTR(insert_ptr), ptr); // 이전 블록의 next를 새 블록으로 변경
        }
        else                        // 이전 블록이 NULL, 이후 블록이 NULL이 아닌 경우
        {
            SET_PTR(NEXT_PTR(ptr), search_ptr); // 새 블록의 next를 이후 블록 주소로 변경
            SET_PTR(PREV_PTR(search_ptr), ptr); // 이후 블록의 prev를 새 블록으로 변경
            SET_PTR(PREV_PTR(ptr), NULL);       // 새 블록의 prev를 NULL로 설정
            segregated_free_lists[idx] = ptr;   // seg_free_list의 인덱스에 ptr 업데이트 -> 시작 블록이 새 블록으로 바뀌었으니깐 ptr 업데이트
        }
    }
    else {  // search_ptr == NULL
        if (insert_ptr != NULL) {   // 이전 블록이 NULL이 아니고, 이후 블록이 NULL인 경우
            SET_PTR(NEXT_PTR(ptr), NULL);       // 새 블록의 next를 NULL로 설정
            SET_PTR(PREV_PTR(ptr), insert_ptr); // 새 블록의 prev를 이전 블록으로 설정
            SET_PTR(NEXT_PTR(insert_ptr), ptr); // 이전 블록의 next를 새 블록으로 설정
        }
        else {                      // 이전, 이후 블록이 모두 NULl인 경우
            SET_PTR(NEXT_PTR(ptr), NULL);       // 새 블록의 next를 NULL로 설정
            SET_PTR(PREV_PTR(ptr), NULL);       // 새 블록의 prev를 NULL로 설정
            segregated_free_lists[idx] = ptr;   // seg_free_list의 인덱스에 ptr 업데이트 -> 시작 블록이 새 블록으로 바뀌었으니깐 ptr 업데이트
        }
    }
 }

/*
 * delete_node : free list에서 해당 블록 삭제
 */
static void delete_node(void *ptr) {
    int idx = 0;
    size_t size = GET_SIZE(HDRP(ptr));

    // Select segregated list
    // 사이즈에 맞는 free 리스트의 index 찾기
    while ((idx < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        idx ++;
    }

    if (NEXT(ptr) != NULL) {
        if (PREV(ptr) != NULL) {        // 이전, 이후 free 블록이 모두 NULL이 아닌 경우
            SET_PTR(PREV_PTR(NEXT(ptr)), PREV(ptr));    // 이후 블록의 prev에 target 블록의 prev 주소를 넣어줌
            SET_PTR(NEXT_PTR(PREV(ptr)), NEXT(ptr));    // 이전 블록의 next에 target 블록의 next 주소를 넣어줌
        }
        else {                          // 이전 블록은 NULL, 이후 블록은 NULL이 아닌 경우
            SET_PTR(PREV_PTR(NEXT(ptr)), NULL);         // 다음 블록의 prev를 NULL로 처리
            segregated_free_lists[idx] = NEXT(ptr);     // seg_free_list의 인덱스에 ptr 업데이트 -> 시작 블록을 다음 블록으로 처리
        }
    }
    else {
        if (PREV(ptr) != NULL) {        // 이전 블록이 NULL이 아니고, 이후 블록이 NULL인 경우
            SET_PTR(NEXT_PTR(PREV(ptr)), NULL);         // 이전 블록의 next를 NULL로 처리
        }
        else {                          // 이전 블록, 이후 블록이 모두 NULL인 경우
            segregated_free_lists[idx] = NULL;          // 해당 seg_free_list의 인덱스를 NULL로 처리
        }
    }

    return;
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

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    // 할당할 free list를 찾아, 필요하다면 분할해서 할당한다
    if ((bp = find_fit(asize)) != NULL) {  // 
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
* coalesce - 연결함수 - 전, 후에 free 블록이 있으면 합치고 seg_list에서 기존 free 블록을 삭제함
                    // 합칠 때는 기존 free 블록들을 seg_list에서 삭제하고, 합쳐진 크기로 다시 seg_list에 삽입
*/
static void *coalesce(void *bp)
{   // 직전 블록의 footer, 직후 블록의 header를 보고 free 여부를 확인
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // GET_ALLOC(직전 블록의 footer) -> 직전 블록 가용 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // GET_ALLOC(직후 블록의 header) -> 직후 블록 가용 여부
    size_t size = GET_SIZE(HDRP(bp));   // 헤더에 적힌 현재 size

    // case 1 : 직전, 직후 블록이 모두 할당 -> 연결할 필요 없음 -> 해당 블록만 free list에 넣어주면 됨
    if(prev_alloc && next_alloc) {
        return bp;
    }

    // case 2 : 직전 블록 할당, 직후 블록 free
    if (prev_alloc && !next_alloc) { 
        delete_node(bp);                        // 현재 블록 삭제
        delete_node(NEXT_BLKP(bp));             // 직후 블록 삭제
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));  // 직후 블록의 헤더의 크기값을 가져와 size에 더하기
        PUT(HDRP(bp), PACK(size, 0));           // header에 size값 넣어줌
        PUT(FTRP(bp), PACK(size, 0));           // footer에 size값 넣어줌
    }

    // case 3 : 직전 블록 free, 직후 블록 할당
    else if (!prev_alloc && next_alloc) {   
        delete_node(bp);                        // 현재 블록 삭제
        delete_node(PREV_BLKP(bp));             // 직전 블록 삭제
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));  // 직전 블록의 헤더의 크기값을 가져와 size에 더하기
        PUT(FTRP(bp), PACK(size, 0));           // footer에 size값 넣어줌
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));// 직전 블록의 헤더 위치(새 블록의 헤더)에 size값 넣어줌
        bp = PREV_BLKP(bp);                     // bp값을 직전 블록의 bp 위치(새 블록의 bp 위치)로 옮기기
    }

    // case 4 : 직전 블록 free, 직후 블록 free
    else if (!prev_alloc && !next_alloc) { 
        delete_node(bp);                        // 현재 블록 삭제
        delete_node(PREV_BLKP(bp));             // 직전 블록 삭제
        delete_node(NEXT_BLKP(bp));             // 직후 블록 삭제
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));  // 직전, 직후 블록의 크기값을 size에 더하기
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));// 직전 블록의 header 위치에 size값 넣어주기
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));// 직후 블록의 footer 위치에 size값 넣어주기
        bp = PREV_BLKP(bp);                     // bp값을 직전 블록의 bp 위치(새 블록의 bp 위치)로 옮기기
    }

    // 삭제한 기준 블록을 free list에 넣어주기
    insert_node(bp, size); 
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

    insert_node(bp, size);  

    // 앞뒤블록과 연결할 수 있다면 연결한다. 
    coalesce(bp);   
}

void *mm_realloc(void *bp, size_t size) {

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
            delete_node(NEXT_BLKP(oldptr));         // free 상태였던 직후 블록을 free list에서 제거한다. 
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
            delete_node(NEXT_BLKP(oldptr)); // free 상태였던 직후 블록을 free list에서 제거한다. 
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
 * mm_realloc : Implemented simply in terms of mm_malloc and mm_free

   기존에 malloc으로 동적 할당된 메모리 크기를 변경시켜주는 함수
   현재 메모리에 bp가 가르키는 사이즈를 할당한 만큼 충분하지 않다면 메모리의 다른 공간의 기존 크기의 공간 할당 + 기존에 있던 데이터를 복사한 후 추가로 메모리 할당
*/
// void *mm_realloc(void *bp, size_t size) {   // 바로 뒤가 free인 경우 최대 크기 확인하고 그 크기가 asize보다 크면 realloc, 아니면 원래 방식대로, 뒤가 힙인 경우에는 힙 크기 늘려주기
//     void *oldptr = bp;  // 크기를 조절하고 싶은 힙의 시작 포인터
//     void *newptr;       // 크기 조절 뒤, 새 힙의 시작 포인터
//     size_t copySize;    // 복사할 힙의 크기
    
//     newptr = mm_malloc(size);   // 새로운 크기로 malloc
//     if (newptr == NULL) // 실패 시 NULL 반환
//       return NULL;

//     // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
//     copySize = GET_SIZE(HDRP(oldptr));  // 복사할 기존 메모리의 사이즈를 oldptr로부터 가져오기

//     // 원래 메모리 크기보다 적은 크기를 realloc하면 크기에 맞는 메모리만 할당되고 나머지는 안된다
//     if (size < copySize)
//       copySize = size;

//     // 메모리의 특정한 부분으로부터 얼마까지의 부분을 다른 메모리 영역으로 복사해주는 함수
//     // oldptr로부터 copySize만큼의 문자를 newptr에 복사
//     memcpy(newptr, oldptr, copySize);   // newptr에 oldptr를 시작으로 copySize만큼의 메모리 값을 복사한다.
//     mm_free(oldptr);    // 기존의 힙을 반환한다. 
//     return newptr;
// }

/*
 * find_fit -> first-fit 방법 : 힙의 맨 처음부터 탐색하여 요구하는 메모리 공간보다 큰 가용 블록의 주소를 반환한다. 
 */
static void *find_fit(size_t asize) /////////////////////////??????????????????????
{
    char *bp;
    int idx = 0;
    size_t searchsize = asize;  // 찾고자 하는 사이즈
    
    // search for free block in segregated list
    // index 0부터 free list 검색
    while (idx < LISTLIMIT) {
        // 마지막 인덱스 or (찾고자 하는 사이즈가 1보다 작고 && seg_free_list의 인덱스가 NULL이 아닌 경우)
        if ((idx == LISTLIMIT - 1) || ((searchsize <= 1) && (segregated_free_lists[idx] != NULL))) {
            bp = segregated_free_lists[idx];    // bp에 현재 찾고 있는 블록 주소 넣기
            // Ignore blocks that are too small or marked with the reallocation bit
            // 너무 작거나 재할당 비트로 표시된 블록 무시   /////////////////????????????
            while ((bp != NULL) && ((asize > GET_SIZE(HDRP(bp))))) { // bp 블록이 NULL이 나이고 target size를 넣을 수 있는 블록을 찾을 때까지
                bp = NEXT(bp);  // 블록 탐색
            }
            if (bp != NULL)     // 할당 가능한 블록을 찾은 경우
                return bp;
        }
        searchsize >>= 1;       // 반복문 종료 조건
        idx++;                  // 인덱스 올려서 더 큰 블록을 탐색
    }
    return NULL;
}

//////////////////////////////////////////여기부터 다시 시작
/*
 * place : 요구한 메모리를 가용 블록에 할당함, 분할이 필요하면 분할함
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));  // 현재 할당할 수 있는 후보 free 블록의 size

    delete_node(bp);    // 할당될 블록이므로 free list에서 제거

    // 분할이 필요한 경우
    if ((csize - asize) >= (2*DSIZE)) { // 블록의 크기가 asize보다 크고 그 차이가 4word보다 크거나 같은 경우
        // 앞의 블록은 할당 블록으로
        PUT(HDRP(bp), PACK(asize, 1));  // asize만큼 할당시키고 header에 값 넣기
        PUT(FTRP(bp), PACK(asize, 1));  // footer에 값 넣기

        // 뒤의 블록은 free 블록으로 분할
        bp = NEXT_BLKP(bp);             // bp를 다음 블록의 block pointer로 옮기기
        PUT(HDRP(bp), PACK(csize-asize, 0));    // csize-asize만큼 남은 블록의 헤더에 값 넣기
        PUT(FTRP(bp), PACK(csize-asize, 0));    // footer에 값 넣기 

        // free list에 분할된 블록 넣기
        insert_node(bp, (csize-asize));
    }
    // 분할 불가능한 경우
    else {                              // 블록의 크기의 차이가 4word보다 작은 경우 - 분할하지 않아도 딱 들어맞는 경우
        PUT(HDRP(bp), PACK(csize, 1));  // csize만큼 할당시키고 헤더에 값 넣기
        PUT(FTRP(bp), PACK(csize, 1));  // footer에 값 넣기
    }
}

