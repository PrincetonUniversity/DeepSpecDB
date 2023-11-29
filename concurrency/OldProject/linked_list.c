#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include "linked_list.h"


extern void *malloc(size_t n);
extern void free(void *p);


void *surely_malloc(size_t n)
{
	void *p = malloc(n);
	if (!p)
		exit(1);
	return p;
}

struct list *createNode(void *v){
  struct list *p = (struct list *)surely_malloc(sizeof *p);
  p->ptr = v;
  p->tail = NULL;
  return p;
}
int size(struct list *x){
  struct list *t = x;
  int count = 0;
    while (t!=NULL) {
      count += 1;
      t = t->tail;
      
    }
    return count;
}
int search(struct list *x, void *y){
  int found = 0;
  struct list *t = x;
  while (t!=NULL) {
      if(t->ptr == y){
        found = 1;
        break;
      }
      t = t->tail;
      
    }
    return found;

}

struct list *append (struct list *x, struct list *y) {
  struct list *t, *u;
  if (x==NULL)
    return y;
  else {
    t = x;
    u = t->tail;
    while (u!=NULL) {
      t = u;
      u = t->tail;
    }
    t->tail = y;
    return x;
  }
}

struct list *detach(struct list *x, struct list *y) {
  struct list *t, *u;
  if (x==NULL)
    return x;
  else {
    if(x == y){
      t = x;
      x = x->tail;
      free(t);
      return x;

    }
    t = x;
    u = t->tail;
    while (u!=NULL) {
      if(u == y)
      {
        t->tail = u->tail;
        free(u);
        return x;

      }
      t = u;
      u = t->tail;
    }
    return x;
  }
}
// int main(void)
// {
//   struct list * x, *y, *z;
//   char first[] ="firstname";
//   char last[] = "lastname";
//   x = NULL;
//   y = createNode(first);
//   z = createNode(last);
//   x = append(x,y);
//   append(x,z);
//   printf("Size of Linked list: %d\n", size(x));
//   x = delete(x,y);
//   printf("Size of Linked list: %d\n", size(x));
//   x = delete(x,z);
//   printf("Size of Linked list: %d\n", size(x));


//   return 0;
// }
