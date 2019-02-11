#include <stddef.h>
#include "stdlib.h"
#include "stringlist.h"

struct scell {
  char *key;
  void *value;
  struct scell *next;
};

struct stringlist {
  struct scell *root;
};

stringlist_t stringlist_new(void) {
  struct stringlist *p = (struct stringlist *)malloc(sizeof(struct stringlist));
  if (!p) exit(1);
  p->root=NULL;
  return p;
}  
  
char *copy_string (char *s) {
  int i,n = strlen(s)+1;
  char *p = malloc(n);
  if (!p) exit(1);
  strcpy(p,s);
  return p;
}

struct scell *new_scell (char *key, void *value, struct scell *next) {
  struct scell *p = (struct scell *)malloc(sizeof(struct scell));
  if (!p) exit(1);
  p->key = copy_string(key);
  p->value = value;
  p->next = next;
  return p;
}

void *stringlist_insert(stringlist_t p, char *key, void *value) {
  struct scell *q, **r;
  void *old;
  for(r= &p->root; ; r= &q->next) {
    q = *r;
    if (!q) {
      *r = new_scell(key,value,NULL);
      return NULL;
    }
    if (strcmp(q->key, key)==0) {
      old = q->value;
      q->value = value;
      return old;
    }
  }
}  
  
void *stringlist_lookup(stringlist_t p, char *key) {
  struct scell *q;
  for (q=p->root; q; q=q->next) {
    if (strcmp(q->key, key) == 0)
      return q->value;
  }
  return NULL;
}

    

