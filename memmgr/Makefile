COMPCERT = ~/CompCert-3.2

test:
	clang -g -O0 malloc.c; valgrind ./a.out

clight: 
	$(COMPCERT)/clightgen -normalize malloc.c; echo "Expect warning from cdefs.h about unsupported compiler."; coqc `cat _CoqProject-export` malloc.v
