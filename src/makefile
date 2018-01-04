# Btree Libraries Makefile
# Author: Oluwatosin V. Adewale

CC = gcc 

# CFLAGS = -Wall -Wextra -Wno-unused-parameter -pedantic -Wall -std=c89
CFLAGS = -g -Wall -Wextra -Wno-unused-parameter -pedantic -Wall -std=c89
# CFLAGS = -NDEBUG  -O -g -Wall -Wextra -Wno-unused-parameter -pedantic -Wall -std=c89

# Library object files
UTILOBJ = util.o
RELATIONOBJ = relation_mem.o
STRINGBAGOBJ = stringbag.o
RELAPPSOBJ = relapps.o
BORDERNODEOBJ = bordernode.o
LIBOBJECTFILES = $(UTILOBJ) $(RELATIONOBJ) $(STRINGBAGOBJ) $(RELAPPSOBJ) $(BORDERNODEOBJ)

# Test object Files
RANGECLIENTOBJ = rangequeryclient.o 
RELATIONTESTSOBJ = relationtests.o 
STRINGBAGCLIENTOBJ = stringbagclient.o
TESTOBJFILES = $(RANGECLIENTOBJ) $(RELATIONTESTSOBJ) $(STRINGBAGCLIENTOBJ)

# Executable Files
RANGEEXEC = rangequery.exe
RELATIONTESTSEXEC = relationtests.exe
STRINGBAGCLIENT = stringbagclient.exe
TESTEXECFILES = $(RANGEEXEC) $(RELATIONTESTSEXEC) $(STRINGBAGCLIENT)

all: $(LIBOBJECTFILES) $(TESTOBJFILES) $(TESTEXECFILES)

clean:
	rm -f *.o
	rm -f *.exe
	

$(RANGEEXEC): rangequeryclient.o util.o relation_mem.o relapps.o
	$(CC) $(CFLAGS) rangequeryclient.o util.o relation_mem.o relapps.o -o $@
	
$(RELATIONTESTSEXEC): relationtests.o util.o relation_mem.o bordernode.o
	$(CC) $(CFLAGS) relationtests.o util.o relation_mem.o bordernode.o -o $@
	
$(STRINGBAGCLIENT): stringbagclient.o util.o stringbag.o
	$(CC) $(CFLAGS) stringbagclient.o util.o stringbag.o -o $@


rangequeryclient.o: rangequeryclient.c relation.h util.h relapps.h
	$(CC) $(CFLAGS) -c $<
	
relationtests.o: relationtests.c relation.h util.h
	$(CC) $(CFLAGS) -c $<

stringbagclient.o: stringbagclient.c  stringbag.h util.h
	$(CC) $(CFLAGS) -c $<
	
relapps.o: relapps.c relapps.h relation.h util.h
	$(CC) $(CFLAGS) -c $<
	
util.o: util.c util.h
	$(CC) $(CFLAGS) -c $<

relation_mem.o: relation_mem.c relation.h util.h 
	$(CC) $(CFLAGS) -c $<
	
stringbag.o: stringbag.c stringbag.h util.h
	$(CC) $(CFLAGS) -c $<
	
bordernode.o: bordernode.c bordernode.h relation.h util.h
	$(CC) $(CFLAGS) -c $<

