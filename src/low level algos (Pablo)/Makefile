all: queue2.o index.o stringlist.o inthash.o inthash_schema.o stringlist_schema.o \
tuple_schema.o db_util.o db_seq_scan.o

surely_malloc.o: surely_malloc.c
	gcc -c surely_malloc.c 

queue2.o: queue2.c surely_malloc.h
	gcc -c queue2.c

index.o: index.c
	gcc -c index.c

stringlist.o: stringlist.c
	gcc -c stringlist.c

inthash.o: inthash.c 
	gcc -c inthash.c

inthash_schema.o: inthash_schema.c inthash.h
	gcc -c inthash_schema.c

stringlist_schema.o: stringlist_schema.c stringlist.h 
	gcc -c stringlist_schema.c 

tuple_schema.o: tuple_schema.c index.h
	gcc -c tuple_schema.c

db_util.o: db_util.c queue2.h index.h inthash_schema.h stringlist_schema.h tuple_schema.h
	gcc -c db_util.c

db_seq_scan.o: db_seq_scan.c db_util.h
	gcc -c db_seq_scan.c

