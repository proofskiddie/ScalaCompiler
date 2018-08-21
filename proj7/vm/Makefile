# Makefile to compile

SRCS=src/engine.c \
     src/fail.c \
     src/main.c \
     src/memory*.c

CFLAGS_COMMON=-std=c11 -fwrapv

# Clang address sanitizer flags
# (see http://clang.llvm.org/docs/AddressSanitizer.html)
CLANG_ASAN_CFLAGS=-fsanitize=address

# Clang undefined behavior sanitizer flags
# (see http://clang.llvm.org/docs/UndefinedBehaviorSanitizer.html)
CLANG_UBSAN_CFLAGS=-fsanitize=undefined-trap -fsanitize-undefined-trap-on-error

# Clang warning flags
CLANG_WARNING_FLAGS=-Wall -Wno-format-nonliteral

# Flags for debugging:
CFLAGS_DEBUG=${CFLAGS_COMMON} -g ${CLANG_ASAN_FLAGS} ${CLANG_UBSAN_FLAGS} ${CLANG_WARNING_FLAGS}

# Flags for maximum performance:
CFLAGS_RELEASE=${CFLAGS_COMMON} -O3 -DNDEBUG

CFLAGS=${CFLAGS_DEBUG}

default:
	@echo "Use the following targets:"
	@echo " - 'make vm' to use your copying GC"
	@echo " - 'make test' to test the VM"
	@echo " - 'make clean' to clean the VM"
	@echo ""
	@echo "Note: the GC_VERSION preprocessor variable controls which"
	@echo "      garbage collector is used in the virtual machine."

bin:
	mkdir -p bin

vm: clean bin/vm

bin/vm: bin ${SRCS}
	${CC} ${CFLAGS} ${LDFLAGS} ${SRCS} -o bin/vm 

test: vm
	@((echo 10   | bin/vm ../examples/asm/queens.asm  2>&1) >/dev/null && echo Queens test passed!) || echo Queens test failed!
	@((echo 400 | bin/vm ../examples/asm/bignums.asm 2>&1) >/dev/null && echo Bignums test passed!) || echo Bignums test failed!
	@((echo 120  | bin/vm ../examples/asm/pascal.asm  2>&1) >/dev/null && echo Pascal test passed!) || echo Pascal test failed!
	@((echo 10  | bin/vm ../examples/asm/maze.asm    2>&1) >/dev/null && echo Maze test passed!) || echo Maze test failed!

clean:
	rm -rf bin

all: clean vm
