include CONFIGURE

all: relation_mem.o db_client.o client.exe relation_mem.v db_client.v

client.exe: db_client.o
	gcc db_client.o -o client.exe

relation_mem.o: relation_mem.c relation.h assert.h
	gcc -c relation_mem.c

db_client.o: db_client.c relation_mem.o relation.h assert.h 
	gcc -c db_client.c

relation_mem.v db_client.v: relation_mem.c relation.h db_client.c db_client.h assert.h
	$(CLIGHTGEN) -normalize relation_mem.c db_client.c

clean:
	rm *.o *.v
