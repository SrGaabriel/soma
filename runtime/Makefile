# Soma Runtime Makefile
#
# Three runtime modes:
# 1. Native (native_soma.a)  - Pure stack-based, no pools, minimal overhead
# 2. Hybrid (hybrid_soma.a)  - Stack + pools + optional fork-join parallelism
# 3. Graph  (inets_soma.a)   - Full interaction net graph reduction
#
# Use -m native|hybrid|graph when compiling Soma programs.

CC = clang
CFLAGS = -O3 -Wall -Wextra -fPIC -std=c11 -pthread

# Output libraries
NATIVE_LIB = native_soma.a
HYBRID_LIB = hybrid_soma.a
INETS_LIB  = inets_soma.a

.PHONY: all clean test native hybrid inets

all: $(NATIVE_LIB) $(HYBRID_LIB) $(INETS_LIB)

native: $(NATIVE_LIB)
hybrid: $(HYBRID_LIB)
inets: $(INETS_LIB)

# Native runtime - pure stack-based, minimal overhead
$(NATIVE_LIB): soma_runtime.o
	ar rcs $@ $^

soma_runtime.o: soma_runtime.c soma_runtime.h
	$(CC) $(CFLAGS) -c $< -o $@

# Hybrid runtime - pools + optional fork-join parallelism
$(HYBRID_LIB): soma_hybrid.o
	ar rcs $@ $^

soma_hybrid.o: soma_hybrid.c soma_runtime.c soma_runtime.h
	$(CC) $(CFLAGS) -c soma_hybrid.c -o $@

# Graph runtime - full interaction net reduction
$(INETS_LIB): soma_inet.o
	ar rcs $@ $^

soma_inet.o: soma_inet.c soma_inet.h
	$(CC) $(CFLAGS) -c $< -o $@

# Test programs
test_inet: test_inet.c soma_inet.c soma_inet.h
	$(CC) $(CFLAGS) -DSOMA_NO_MAIN test_inet.c soma_inet.c -o $@

	./test_inet

# Debug builds
test_inet_debug: test_inet.c soma_inet.c soma_inet.h
	$(CC) -O0 -g -Wall -Wextra -std=c11 -pthread -DINET_DEBUG $< soma_inet.c -o $@


clean:
	rm -f *.o $(NATIVE_LIB) $(HYBRID_LIB) $(INETS_LIB) test_inet test_inet_debug
