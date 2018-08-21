#ifndef VMTYPES_H
#define VMTYPES_H

#include <limits.h>
#include <stdint.h>
#include <assert.h>

typedef uint32_t instr_t;       /* instruction */
typedef int32_t value_t;        /* value (signed int / non-negative pointer) */
typedef uint32_t uvalue_t;      /* unsigned value (for bitmap only) */
typedef uint_fast8_t reg_id_t;  /* register identity */

static_assert(sizeof(value_t) == sizeof(uvalue_t),
              "signed and unsigned values must have the same size");
static_assert(sizeof(value_t) % sizeof(instr_t) == 0,
              "value size must be a multiple of instruction size");

#define VALUE_BITS (sizeof(value_t) * CHAR_BIT)

#endif
