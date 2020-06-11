all: relation_mem.o db_client.o client.exe relation_mem.v db_client.v

client.exe: db_client.o relation_mem.o
	gcc db_client.o relation_mem.o -o client.exe

relation_mem.o: relation_mem.c relation.h 
	gcc -c relation_mem.c

db_client.o: db_client.c relation_mem.o relation.h 
	gcc -c db_client.c

relation_mem.v db_client.v: relation_mem.c relation.h db_client.c db_client.h
	clightgen -normalize -fstruct-passing relation_mem.c db_client.c

clean:
	rm *.o *.v