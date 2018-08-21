#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#include "memory.h"
#include "fail.h"
#include "engine.h"

#if GC_VERSION == GC_MARK_N_SWEEP

static void* memory_start = NULL;
static void* memory_end = NULL;

static uvalue_t* bitmap_start = NULL;

static value_t* heap_start = NULL;
static value_t* heap_end = NULL;

static value_t heap_start_v = 0;
static value_t heap_end_v = 0;

static value_t* heap_first_block = NULL;

#define FREE_LISTS_COUNT 32

// physical addresses
static value_t* free_list_heads[FREE_LISTS_COUNT];

#define MIN_BLOCK_SIZE 1
#define HEADER_SIZE 1

// Type conversion
#define ct( x , y) (( x )( y ))
#define vp( x ) ((value_t *)addr_v_to_p(x))
#define pv( x ) (addr_p_to_v(x))
// Header management

#define us( x ) (header_unpack_size( x ))
#define ut( x ) (header_unpack_tag( x ))
#define ph( x , y ) (header_pack( x , y ))


// header :: value_t
// [ size : 3 bytes | tag : 1 byte ] :: total size 4 bytes

// pack the last byte of size with the passed in tag
static value_t header_pack(tag_t tag, value_t size) {
  return (size << 8) | (value_t)tag;
}

// return the tag as the first byte of the header
static tag_t header_unpack_tag(value_t header) {
  return (tag_t)(header & 0xFF);
}

// return the size as the last 3 bytes of the header
static value_t header_unpack_size(value_t header) {
  return header >> 8;
}

// Bitmap management
// these functions are not used outside of this file
// must use them in implementing the tasks below
static int bitmap_is_bit_set(value_t* ptr) {
  assert(heap_start <= ptr && ptr < heap_end);
  long index = ptr - heap_start;
  long word_index = index / (long)VALUE_BITS;
  long bit_index = index % (long)VALUE_BITS;
  return (bitmap_start[word_index] & ((uvalue_t)1 << bit_index)) != 0;
}

static void bitmap_set_bit(value_t* ptr) {
  assert(heap_start <= ptr && ptr < heap_end);
  long index = ptr - heap_start;
  long word_index = index / (long)VALUE_BITS;
  long bit_index = index % (long)VALUE_BITS;
  bitmap_start[word_index] |= (uvalue_t)1 << bit_index;
}

static void bitmap_clear_bit(value_t* ptr) {
  assert(heap_start <= ptr && ptr < heap_end);
  long index = ptr - heap_start;
  long word_index = index / (long)VALUE_BITS;
  long bit_index = index % (long)VALUE_BITS;
  bitmap_start[word_index] &= ~((uvalue_t)1 << bit_index);
}

// Virtual <-> physical address translation

static void* addr_v_to_p(value_t v_addr) {
  return (char*)memory_start + v_addr;
}

static value_t addr_p_to_v(void* p_addr) {
  return (value_t)((char*)p_addr - (char*)memory_start);
}

// Free lists management

static value_t real_size(value_t size) {
  assert(0 <= size);
  return size < MIN_BLOCK_SIZE ? MIN_BLOCK_SIZE : size;
}


static unsigned int free_list_index(value_t size) {
  assert(0 <= size);
  return size >= FREE_LISTS_COUNT ? FREE_LISTS_COUNT - 1 : (unsigned int)size;
}

char* memory_get_identity() {
  return "mark & sweep garbage collector";
}

// called in main.c, creates the heap
void memory_setup(size_t total_byte_size) {
  memory_start = calloc(total_byte_size, 1);
  if (memory_start == NULL)
    fail("cannot allocate %zd bytes of memory", total_byte_size);
  memory_end = (char*)memory_start + total_byte_size;
}

void memory_cleanup() {
  assert(memory_start != NULL);
  free(memory_start);

  memory_start = memory_end = NULL;
  bitmap_start = NULL;
  heap_start = heap_end = NULL;
  heap_start_v = heap_end_v = 0;
  for (int l = 0; l < FREE_LISTS_COUNT; ++l)
    free_list_heads[l] = NULL;
}

void* memory_get_start() {
  return memory_start;
}

void* memory_get_end() {
  return memory_end;
}

// set the start of the heap after the last instruction
// called after memory_setup and the instructions have 
// been inserted into memory 
// 
// function also sets up memory for the bitmap
void memory_set_heap_start(void* ptr) {
  assert(memory_start <= ptr && ptr < memory_end);

  const size_t bh_size =
    (size_t)((char*)memory_end - (char*)ptr) / sizeof(value_t);

  const size_t bitmap_size = (bh_size - 1) / (VALUE_BITS + 1) + 1;
  const size_t heap_size = bh_size - bitmap_size;

  bitmap_start = ptr;
  memset(bitmap_start, 0, bitmap_size * sizeof(value_t));

  heap_start = (value_t*)bitmap_start + bitmap_size;
  heap_end = heap_start + heap_size;
  assert(heap_end == memory_end);

  heap_start_v = addr_p_to_v(heap_start);
  heap_end_v = addr_p_to_v(heap_end);
  
  // first block past the header
  // HEADER_SIZE is one byte
  heap_first_block = heap_start + HEADER_SIZE;
  const value_t initial_block_size = (value_t)(heap_end - heap_first_block);
  heap_first_block[-1] = header_pack(tag_None, initial_block_size);
  heap_first_block[0] = 0;
  
  // free_list_heads 0 - 30 used for the segregated free list
  // freelist[FREE_LISTS_COUNT - 1] used for regular list
  for (int l = 0; l < FREE_LISTS_COUNT - 1; ++l)
    free_list_heads[l] = memory_start;

  // setup head of singly linked list for regular (non-segregated) free list
  free_list_heads[FREE_LISTS_COUNT - 1] = heap_first_block;
}

static value_t *init_freelists(int i) 
  { //setup free_list_heads
    value_t half = (heap_end - heap_start) / 2;
    value_t mn = 31*16, q = half / mn, r = half % mn;
    if (q == 0 && i > r) return NULL;
    value_t in = (i * (i - 1)) / 2;
    value_t qn = in * (i < r)? q : q - 1;
    return addr_v_to_p(heap_start_v + qn); 
  }

#define me( X ) ( X == memory_start )
static value_t* freelist(value_t size) 
  { // return segregated free list 
    value_t i = (size % 32) + (size == 32) * 31;
    if (me(free_list_heads[i]))
      free_list_heads[i] = init_freelists(i);
    return free_list_heads[i];
  }

static value_t* allocate(tag_t tag, value_t size)
  { // search free list for space and return it
  assert(0 <= size);

  // create header
  // every header takes up 4 bytes
  // all sizes are in value_t
  value_t header = header_pack(tag, size); 
  
  const value_t total_size = size + HEADER_SIZE;
   
  value_t *cb = freelist(size);
  while(cb != memory_start) 
    { // while there is an unchecked block
    value_t sz = us(cb[-1]);
    value_t * prev = cb;
    if (sz > total_size) 
      { // if block has enough space
        if ( sz == total_size ) return prev;

        // create new block for freelist
        prev = cb + real_size(total_size);
        // update new header
        value_t ot = ut(cb[-1]);
        value_t os = us(cb[-1]);
        prev[-1] = header_pack(ot, os - total_size);
        prev[0] = 0;

        // update old header
        cb[-1] = header;
        return cb;
      } else cb = addr_v_to_p(cb[0]);
    }

  return NULL; 
}

static value_t valid_block(value_t * block) {
  return pv(block) >= 0 && pv(block) < heap_end_v ;
}
static void mark(value_t* block) {
  assert(valid_block(block));
  // block of value_t + value_t *
  value_t sz = us(block[-1]);
  // size of block 
  printf("mark : block size :%d\n", sz);
  value_t i;
  for (i = 0 ; i < sz ; ++i ) 
    {
      if ( block[i] % 4 == 0 && valid_block(block)) {
        bitmap_set_bit(block + i);
      }
    }
  return;
}

static void check_heap() {
  value_t * h = heap_first_block;
  while (h < heap_end && us(h[-1]) > 0) {
    printf("%d %d\n", h[0], us(h[-1]));    
    h += us(h[-1]);
  }
 printf("\n"); 
}

static void sweep() {
  value_t h = pv(heap_first_block);
  value_t step = us(heap_first_block[-1]);
  for (; h < heap_end_v && step > 0; h += step )  {
    if (bitmap_is_bit_set(vp(h)))
      check_heap();
    step = us(vp(h)[-1]);  
  }
}

value_t* memory_allocate(tag_t tag, value_t size) {
 // mark and sweep only done when allocate fails
  value_t* first_try = allocate(tag, size);
  if (first_try != NULL)
    return first_try;

  value_t* lb = engine_get_Lb();
  if (lb != memory_start) mark(lb);
  value_t* ib = engine_get_Ib();
  if (ib != memory_start) mark(ib);
  value_t* ob = engine_get_Ob();
  if (ob != memory_start) mark(ob);

  sweep();

  // try allocating post sweep, if not the throw error
  // error says "YOU ARE OUT OF MEMORY!"
  value_t* second_try = allocate(tag, size);
  if (second_try != NULL)
    return second_try;

  fail("\ncannot allocate %d words of memory, even after GC\n", size);
}

value_t memory_get_block_size(value_t* block) {
  return header_unpack_size(block[-1]);
}

tag_t memory_get_block_tag(value_t* block) {
  return header_unpack_tag(block[-1]);
}

#endif
