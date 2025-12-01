# Soma Runtime Makefile
#
# The INET runtime is the primary parallel reduction engine.
# It uses a hybrid stack + work-stealing architecture for
# maximum parallelism on tree-structured computations.

CC = clang
CFLAGS = -O3 -Wall -Wextra -fPIC -std=c11 -pthread

# Output
LIB = libsoma_runtime.a
OBJ = soma_inet.o

.PHONY: all clean test

all: $(LIB)

$(LIB): $(OBJ)
	ar rcs $@ $^

# Core runtime
soma_inet.o: soma_inet.c soma_inet.h
	$(CC) $(CFLAGS) -c $< -o $@

# Test program (compile runtime with SOMA_NO_MAIN to avoid main conflict)
test_inet: test_inet.c soma_inet.c soma_inet.h
	$(CC) $(CFLAGS) -DSOMA_NO_MAIN test_inet.c soma_inet.c -o $@

test: test_inet
	./test_inet

# Debug build
test_inet_debug: test_inet.c soma_inet.c soma_inet.h
	$(CC) -O0 -g -Wall -Wextra -std=c11 -pthread -DINET_DEBUG $< soma_inet.c -o $@

# Benchmark
bench: test_inet
	./test_inet bench 25 8 4

clean:
	rm -f $(OBJ) $(LIB) test_inet test_inet_debug
