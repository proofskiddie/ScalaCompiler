#define _DEFAULT_SOURCE
#include <assert.h>
#include <stdio.h>

#include "vmtypes.h"
#include "engine.h"
#include "opcode.h"
#include "memory.h"
#include "fail.h"

// each designates a block of 32
// psuedo-registers
typedef enum {
  Lb, Lb1, Lb2, Lb3, Lb4, Lb5,
  Ib, Ob
} reg_bank_t;

static void* memory_start;
static void* memory_end;

// base reigsters store
// pointers to psuedo registers 
static value_t* R[8];           /* (pseudo)base registers */

void engine_setup(void) {
  memory_start = memory_get_start();
  memory_end = memory_get_end();
}

void engine_cleanup(void) {
  // nothing to do
}

// instructions are stored on the heap
// allocation limits (heap size) are set from the command line
void engine_emit(instr_t instr, instr_t** instr_ptr) {
  if ((void*)(*instr_ptr + 1) > memory_end)
    fail("not enough memory to load code");
  **instr_ptr = instr;
  *instr_ptr += 1;
}

// contiguous blocks for base registers
value_t* engine_get_Lb(void) { return R[Lb]; }
value_t* engine_get_Ib(void) { return R[Ib]; }
value_t* engine_get_Ob(void) { return R[Ob]; }

void engine_set_Lb(value_t* new_value) {
  for (reg_bank_t pseudo_bank = Lb; pseudo_bank <= Lb5; ++pseudo_bank)
    R[pseudo_bank] = new_value + (pseudo_bank - Lb) * 32;
}
void engine_set_Ib(value_t* new_value) { R[Ib] = new_value; }
void engine_set_Ob(value_t* new_value) { R[Ob] = new_value; }

// Virtual <-> physical address translation

static void* addr_v_to_p(value_t v_addr) {
  assert(0 <= v_addr);
  return (char*)memory_start + v_addr;
}

static value_t addr_p_to_v(void* p_addr) {
  assert(memory_start <= p_addr && p_addr <= memory_end);
  return (value_t)((char*)p_addr - (char*)memory_start);
}

// Instruction decoding

static reg_bank_t reg_bank(reg_id_t r) {
  return r >> 5;
}

static unsigned int reg_index(reg_id_t r) {
  return r & 0x1F;
}

// returns elements of instr starting at start and ending at start + len
static unsigned int instr_extract_u(instr_t instr, int start, int len) {
  return (instr >> start) & ((1 << len) - 1);
}

static int instr_extract_s(instr_t instr, int start, int len) {
  int bits = (int)instr_extract_u(instr, start, len);
  int m = 1 << (len - 1);
  return (bits ^ m) - m;
}

static opcode_t instr_opcode(instr_t instr) {
  unsigned int opcode = instr_extract_u(instr, 26, 6);
  return (opcode_t)opcode;
}

static reg_id_t instr_ra(instr_t instr) {
  return (reg_id_t)instr_extract_u(instr, 18, 8);
}

static reg_id_t instr_rb(instr_t instr) {
  return (reg_id_t)instr_extract_u(instr, 10, 8);
}

static reg_id_t instr_rc(instr_t instr) {
  return (reg_id_t)instr_extract_u(instr, 2, 8);
}

static int instr_d(instr_t instr) {
  return instr_extract_s(instr, 0, 10);
}

// (Pseudo-)register access

#define Ra (R[reg_bank(instr_ra(*pc))][reg_index(instr_ra(*pc))])
#define Rb (R[reg_bank(instr_rb(*pc))][reg_index(instr_rb(*pc))])
#define Rc (R[reg_bank(instr_rc(*pc))][reg_index(instr_rc(*pc))])

#define GOTO_NEXT goto *labels[instr_opcode(*pc)]

// Floor division and modulus
// (see "Division and Modulus for Computer Scientists" by Daan Leijen)

static int signum(value_t x) {
  return (x > 0) - (x < 0);
}
static value_t floorDiv(value_t x, value_t y) {
  value_t rt = x % y;
  int i = signum(rt) == -signum((y));
  return (x / y) - i;
}

static value_t floorMod(value_t x, value_t y) {
  value_t rt = x % y;
  int i = signum(rt) == -signum(y);
  return rt + i * y;
}

value_t engine_run() {
  setbuffer(stdout, NULL, 0);

  instr_t* pc = memory_start;
  engine_set_Lb(memory_start);
  engine_set_Ib(memory_start);
  engine_set_Ob(memory_start);

  void** labels[OPCODE_COUNT];
  labels[opcode_ADD] = &&l_ADD;
  labels[opcode_SUB] = &&l_SUB;
  labels[opcode_MUL] = &&l_MUL;
  labels[opcode_DIV] = &&l_DIV;
  labels[opcode_MOD] = &&l_MOD;
  labels[opcode_ASL] = &&l_ASL;
  labels[opcode_ASR] = &&l_ASR;
  labels[opcode_AND] = &&l_AND;
  labels[opcode_OR] = &&l_OR;
  labels[opcode_XOR] = &&l_XOR;
  labels[opcode_JLT] = &&l_JLT;
  labels[opcode_JLE] = &&l_JLE;
  labels[opcode_JEQ] = &&l_JEQ;
  labels[opcode_JNE] = &&l_JNE;
  labels[opcode_JGE] = &&l_JGE;
  labels[opcode_JGT] = &&l_JGT;
  labels[opcode_JI] = &&l_JI;
  labels[opcode_TCAL] = &&l_TCAL;
  labels[opcode_CALL] = &&l_CALL;
  labels[opcode_RET] = &&l_RET;
  labels[opcode_HALT] = &&l_HALT;
  labels[opcode_LDLO] = &&l_LDLO;
  labels[opcode_LDHI] = &&l_LDHI;
  labels[opcode_MOVE] = &&l_MOVE;
  labels[opcode_RALO] = &&l_RALO;
  labels[opcode_BALO] = &&l_BALO;
  labels[opcode_BSIZ] = &&l_BSIZ;
  labels[opcode_BTAG] = &&l_BTAG;
  labels[opcode_BGET] = &&l_BGET;
  labels[opcode_BSET] = &&l_BSET;
  labels[opcode_BREA] = &&l_BREA;
  labels[opcode_BWRI] = &&l_BWRI;

  GOTO_NEXT;

 l_ADD: {
    Ra = Rb + Rc;
    pc += 1;
 } GOTO_NEXT;

 l_SUB: {
    Ra = Rb - Rc;
    pc += 1;
  } GOTO_NEXT;

 l_MUL: {
    Ra = Rb * Rc;
    pc += 1;
  } GOTO_NEXT;

 l_DIV: {
    Ra = floorDiv(Rb, Rc);
    pc += 1;
  } GOTO_NEXT;

 l_MOD: {
    Ra = floorMod(Rb, Rc);
    pc += 1;
  } GOTO_NEXT;

 l_ASL: {
    Ra = Rb << Rc;
    pc += 1;
  } GOTO_NEXT;

 l_ASR: {
    Ra = Rb >> Rc;
    pc += 1;
  } GOTO_NEXT;

 l_AND: {
    Ra = Rb & Rc;
    pc += 1;
  } GOTO_NEXT;

 l_OR: {
    Ra = Rb | Rc;
    pc += 1;
  } GOTO_NEXT;

 l_XOR: {
    Ra = Rb ^ Rc;
    pc += 1;
  } GOTO_NEXT;

 l_JLT: {
    pc += (Ra < Rb ? instr_d(*pc) : 1);
  } GOTO_NEXT;

 l_JLE: {
    pc += (Ra <= Rb ? instr_d(*pc) : 1);
  } GOTO_NEXT;

 l_JEQ: {
    pc += (Ra == Rb ? instr_d(*pc) : 1);
  } GOTO_NEXT;

 l_JNE: {
    pc += (Ra != Rb ? instr_d(*pc) : 1);
  } GOTO_NEXT;

 l_JGE: {
    pc += (Ra >= Rb ? instr_d(*pc) : 1);
  } GOTO_NEXT;

 l_JGT: {
    pc += (Ra > Rb ? instr_d(*pc) : 1);
  } GOTO_NEXT;

 l_JI: {
    pc += instr_extract_s(*pc, 0, 26);
  } GOTO_NEXT;

 l_TCAL: {
    instr_t* target_pc = addr_v_to_p(Ra);
    R[Ob][0] = R[Ib][0];
    R[Ob][1] = R[Ib][1];
    R[Ob][2] = R[Ib][2];
    R[Ob][3] = R[Ib][3];
    engine_set_Ib(R[Ob]);
    engine_set_Lb(memory_start);
    engine_set_Ob(memory_start);
    pc = target_pc;
  } GOTO_NEXT;

 l_CALL: {
    instr_t* target_pc = addr_v_to_p(Ra);
    R[Ob][0] = addr_p_to_v(R[Ib]);
    R[Ob][1] = addr_p_to_v(R[Lb]);
    R[Ob][2] = addr_p_to_v(R[Ob]);
    R[Ob][3] = addr_p_to_v(pc + 1);
    engine_set_Ib(R[Ob]);
    engine_set_Lb(memory_start);
    engine_set_Ob(memory_start);
    pc = target_pc;
  } GOTO_NEXT;

 l_RET: {
    value_t ret_value = R[Ib][4];
    instr_t* target_pc = addr_v_to_p(R[Ib][3]);
    engine_set_Ob(addr_v_to_p(R[Ib][2]));
    engine_set_Lb(addr_v_to_p(R[Ib][1]));
    engine_set_Ib(addr_v_to_p(R[Ob][0]));
    R[Ob][0] = ret_value;
    pc = target_pc;
  } GOTO_NEXT;

 l_HALT: {
    return Ra;
  }

 l_LDLO: {
    Ra = instr_extract_s(*pc, 0, 18);
    pc += 1;
  } GOTO_NEXT;

 l_LDHI: {
    Ra = ((value_t)instr_extract_u(*pc, 0, 16) << 16) | (Ra & 0xFFFF);
    pc += 1;
  } GOTO_NEXT;

 l_MOVE: {
    Ra = Rb;
    pc += 1;
  } GOTO_NEXT;

 // allocates registers
 l_RALO: {
    // grab hexdigits 5 and 6 as size of 32 bit instruction
    // (hexdigits 7 and 8 are the op_code)
    value_t size = (value_t)instr_extract_u(*pc, 16, 8);

    // allocate the specified number of bytes of type tag_RegisterFrame (201)
    // this function must be implemented in memory_*.c for the different versions
    // of GC to work (already implemented for memory_nofree.c
    value_t* block = memory_allocate(tag_RegisterFrame, size);

    // switch on 
    switch (instr_extract_u(*pc, 24, 2)) {
    case 0: engine_set_Lb(block); break;
    case 1: engine_set_Ib(block); break;
    case 2: engine_set_Ob(block); break;
    }
    pc += 1;
  } GOTO_NEXT;

 l_BALO: {
    value_t* block = memory_allocate(instr_extract_u(*pc, 2, 8), Rb);
    Ra = addr_p_to_v(block);
    pc += 1;
  } GOTO_NEXT;

 l_BSIZ: {
    Ra = memory_get_block_size(addr_v_to_p(Rb));
    pc += 1;
  } GOTO_NEXT;

 l_BTAG: {
    Ra = memory_get_block_tag(addr_v_to_p(Rb));
    pc += 1;
  } GOTO_NEXT;

 l_BGET: {
    value_t* block = addr_v_to_p(Rb);
    value_t index = Rc;
    assert(0 <= index && index < memory_get_block_size(block));
    Ra = block[index];
    pc += 1;
  } GOTO_NEXT;

 l_BSET: {
    value_t* block = addr_v_to_p(Rb);
    value_t index = Rc;
    assert(0 <= index && index < memory_get_block_size(block));
    block[index] = Ra;
    pc += 1;
  } GOTO_NEXT;

 l_BREA: {
    uint8_t byte;
    size_t read = fread(&byte, sizeof(byte), 1, stdin);
    Ra = (read == sizeof(byte) ? byte : -1);
    pc += 1;
  } GOTO_NEXT;

 l_BWRI: {
    uint8_t byte = (uint8_t)Ra;
    fwrite(&byte, sizeof(byte), 1, stdout);
    pc += 1;
  } GOTO_NEXT;
}
