# Soma Runtime Makefile

CC = clang
CFLAGS = -O3 -Wall -Wextra -fPIC -std=c11 -pthread

# Output
LIB = libsoma_runtime.a
OBJ = soma_runtime.o soma_graph.o

.PHONY: all clean test_graph

all: $(LIB)

$(LIB): $(OBJ)
	ar rcs $@ $^

soma_runtime.o: soma_runtime.c soma_runtime.h
	$(CC) $(CFLAGS) -c $< -o $@

soma_graph.o: soma_graph.c soma_graph.h
	$(CC) $(CFLAGS) -c $< -o $@

# Test program for graph reduction
test_graph: test_graph.c soma_graph.o
	$(CC) $(CFLAGS) $^ -o $@

# HVM-style runtime
soma_hvm.o: soma_hvm.c soma_hvm.h
	$(CC) $(CFLAGS) -c $< -o $@

# Test program for HVM-style reduction
test_hvm: test_hvm.c soma_hvm.o
	$(CC) $(CFLAGS) $^ -o $@

# Pure interaction net runtime (maximum parallelism)
soma_inet.o: soma_inet.c soma_inet.h
	$(CC) $(CFLAGS) -c $< -o $@

# Test program for pure inet reduction
test_inet: test_inet.c soma_inet.o
	$(CC) $(CFLAGS) $^ -o $@

# Debug build with assertions
test_inet_debug: test_inet.c soma_inet.c soma_inet.h
	$(CC) -O0 -g -Wall -Wextra -std=c11 -pthread -DINET_DEBUG $< soma_inet.c -o $@

clean:
	rm -f $(OBJ) $(LIB) test_graph soma_hvm.o test_hvm soma_inet.o test_inet test_inet_debug
