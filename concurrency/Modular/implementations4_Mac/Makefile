CC = gcc
CFLAGS = -pthread

TARGETS = bst list

ifeq ($(filter list, $(MAKECMDGOALS)),list)
    CASE = 2
    TARGET = list
else ifeq ($(filter bst, $(MAKECMDGOALS)),bst)
    CASE = 1
    TARGET = bst
else
    CASE = 0
    TARGET = bst
endif

ifeq ($(filter lock, $(MAKECMDGOALS)),lock)
    LOCK_TYPE = lock
else ifeq ($(filter giveup, $(MAKECMDGOALS)),giveup)
    LOCK_TYPE = giveup
else
    LOCK_TYPE = lock
endif

ifeq ($(CASE), 1)
    OBJS = threads.o bst.o bst_$(LOCK_TYPE).o $(LOCK_TYPE)_template.o template.o main.o
else ifeq ($(CASE), 2)
    OBJS = threads.o list.o list_$(LOCK_TYPE).o $(LOCK_TYPE)_template.o template.o main.o
endif

.SECONDARY:

.DEFAULT_GOAL := all

all: $(TARGETS)

$(TARGETS): $(OBJS)
	$(CC) $(CFLAGS) -o $@ $^

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(TARGETS) $(OBJS) *.gch *.o bst list *.out

.PHONY: lock giveup clean

# Always run `clean` before compiling the target
lock: clean
lock: CFLAGS += -DLOCK_TYPE=\"lock\"
lock: all

giveup: clean
giveup: CFLAGS += -DLOCK_TYPE=\"giveup\"
giveup: all

# Optional: Always run `clean` before `all`
all: clean $(TARGETS)