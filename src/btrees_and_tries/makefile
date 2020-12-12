# Btree Libraries Makefile
# Author: Oluwatosin V. Adewale

CC = gcc 

  CFLAGS = -Wall -Wextra -Wno-unused-parameter -pedantic -Wall -std=c99
# CFLAGS = -g -Wall -Wextra -Wno-unused-parameter -pedantic -Wall -std=c89
# CFLAGS = -D NDEBUG  -O3 -Wall -Wextra -Wno-unused-parameter -pedantic -Wall -std=c89

# Library object files
UTILOBJ = util.o
RELATIONOBJ = relation_mem.o
STRINGBAGOBJ = stringbag.o
RELAPPSOBJ = relapps.o
BORDERNODEOBJ = bordernode.o
KVSTOREOBJ = kvstore.o

LIBOBJECTFILES =    $(UTILOBJ) $(RELATIONOBJ) $(STRINGBAGOBJ) $(RELAPPSOBJ) \
		    $(BORDERNODEOBJ) $(KVSTOREOBJ)

# Test object Files
RANGECLIENTOBJ = rangequeryclient.o 
RELATIONTESTSOBJ = relationtests.o 
STRINGBAGCLIENTOBJ = stringbagclient.o
KVSTORETESTSOBJ = kvstoretests.o
COMPLEXITYOBJ = btreecomplexity.o
TESTOBJFILES =	    $(RANGECLIENTOBJ) $(RELATIONTESTSOBJ) $(STRINGBAGCLIENTOBJ) \
		    $(KVSTORETESTSOBJ) $(COMPLEXITYOBJ)

# Executable Files
RANGEEXEC = rangequery.exe
RELATIONTESTSEXEC = relationtests.exe
STRINGBAGCLIENT = stringbagclient.exe
KVSTORETESTS = kvstoretests.exe
COMPLEXITYCLIENT = btreecomplexity.exe

TESTEXECFILES = $(RANGEEXEC) $(RELATIONTESTSEXEC) $(STRINGBAGCLIENT) \
		$(KVSTORETESTS) $(COMPLEXITYCLIENT)

all: $(LIBOBJECTFILES) $(TESTOBJFILES) $(TESTEXECFILES) clean

debug:  $(LIBOBJECTFILES) $(TESTOBJFILES) $(TESTEXECFILES) 

clean:
	rm -f *.o
	
# Rules to build executable targets.
$(RANGEEXEC): rangequeryclient.o util.o relation_mem.o relapps.o
	$(CC) $(CFLAGS) rangequeryclient.o util.o relation_mem.o relapps.o -o $@
	
$(RELATIONTESTSEXEC): relationtests.o util.o relation_mem.o bordernode.o
	$(CC) $(CFLAGS) relationtests.o util.o relation_mem.o bordernode.o -o $@
	
$(STRINGBAGCLIENT): stringbagclient.o util.o stringbag.o
	$(CC) $(CFLAGS) stringbagclient.o util.o stringbag.o -o $@

$(KVSTORETESTS): kvstoretests.o kvstore.o util.o bordernode.o relation_mem.o
	$(CC) $(CFLAGS) kvstoretests.o kvstore.o util.o \
			bordernode.o relation_mem.o -o $@
	
$(COMPLEXITYCLIENT): btreecomplexity.o relation_mem.o util.o kvstore.o bordernode.o
	$(CC) $(CFLAGS) btreecomplexity.o relation_mem.o util.o kvstore.o bordernode.o -o $@
	
db_operations.exe: db_operations.o relation_mem.o kvstore.o bordernode.o index_string.o util.o
	$(CC) $(CFLAGS) db_operations.o relation_mem.o kvstore.o bordernode.o index_string.o util.o -o $@
	
# Rules to build client / test object file targets.
rangequeryclient.o: rangequeryclient.c relation.h util.h relapps.h
	$(CC) $(CFLAGS) -c $<
	
relationtests.o: relationtests.c relation.h util.h
	$(CC) $(CFLAGS) -c $<

stringbagclient.o: stringbagclient.c  stringbag.h util.h
	$(CC) $(CFLAGS) -c $<

kvstoretests.o: kvstoretests.c relation.h util.h bordernode.h kvstore.h
	$(CC) $(CFLAGS) -c $<

btreecomplexity.o: btreecomplexity.c relation.h util.h
	$(CC) $(CFLAGS) -c $<



# Rules to build implementation / library object file targets.
relapps.o: relapps.c relapps.h relation.h util.h
	$(CC) $(CFLAGS) -c $<
	
util.o: util.c util.h
	$(CC) $(CFLAGS) -c $<

relation_mem.o: relation_mem.c relation.h util.h 
	$(CC) $(CFLAGS) -c $<
	
stringbag.o: stringbag.c stringbag.h util.h
	$(CC) $(CFLAGS) -c $<
	
bordernode.o: bordernode.c bordernode.h relation.h util.h inttypes.h surely_malloc.h
	$(CC) $(CFLAGS) -c $<

kvstore.o: kvstore.c kvstore.h bordernode.h relation.h util.h kvstore_int.h surely_malloc.h
	$(CC) $(CFLAGS) -c $<

index_string.o: index_string.c inttypes.h index_int.h index_string.h util.h
	$(CC) $(CFLAGS) -c $<
	
index_int.o: index_int.c relation_mem.c inttypes.h relation.h index_int.h util.h
	$(CC) $(CFLAGS) -c $< 
