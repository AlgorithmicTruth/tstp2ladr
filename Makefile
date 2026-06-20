# tstp2ladr - TSTP-to-LADR proof converter
#
# Reads TSTP proofs (Vampire, E prover, Prover9) and converts
# to LADR format or Ivy (ACL2) format.
#
# Links against LADR-2026 libladr.a.

CC = gcc

# Path to your LADR-2026 (Prover9/Mace4) tree, built with libladr.a.
# Default assumes LADR-2026 sits beside this repo; override as needed:
#   make LADR=/path/to/LADR-2026
LADR = ../LADR-2026

# Detect OS and set platform-specific flags
UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Darwin)
    DARWIN_MAJOR := $(shell uname -r | cut -d. -f1)
    PLATFORM_FLAGS := $(shell \
        v=$(DARWIN_MAJOR); \
        if [ $$v -ge 20 ]; then \
            echo "-arch arm64 -arch x86_64"; \
        elif [ $$v -ge 18 ]; then \
            echo "-arch x86_64"; \
        elif [ $$v -ge 10 ]; then \
            echo "-arch i386 -arch x86_64"; \
        else \
            echo ""; \
        fi)
else
    PLATFORM_FLAGS =
endif

ifdef DEBUG
  OPTFLAGS = -g -O0
else
  OPTFLAGS = -O2
endif

CFLAGS = $(OPTFLAGS) -Wall $(PLATFORM_FLAGS) -I$(LADR)

OBJECTS = tstp2ladr.o fix_positions.o

tstp2ladr: $(OBJECTS)
	$(CC) $(CFLAGS) -o tstp2ladr $(OBJECTS) $(LADR)/ladr/libladr.a

tstp2ladr.o: tstp2ladr.c fix_positions.h
	$(CC) $(CFLAGS) -c tstp2ladr.c

fix_positions.o: fix_positions.c fix_positions.h
	$(CC) $(CFLAGS) -c fix_positions.c

clean:
	/bin/rm -f *.o tstp2ladr

.PHONY: clean
