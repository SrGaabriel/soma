# Soma Runtime Makefile

CC = clang
CFLAGS = -O3 -Wall -Wextra -fPIC -std=c11 -pthread

# Output
LIB = libsoma_runtime.a
OBJ = soma_runtime.o

.PHONY: all clean

all: $(LIB)

$(LIB): $(OBJ)
	ar rcs $@ $^

$(OBJ): soma_runtime.c soma_runtime.h
	$(CC) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(OBJ) $(LIB)
