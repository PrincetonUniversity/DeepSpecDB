#include <stddef.h>
#include "stdlib.h"
#include "inthash.h"

#define N 65599L

struct icell {
  size_t key;
  void *value;
  struct icell *next;
};

struct inthash {
  struct icell *buckets[N];
};

inthash_t inthash_new(void) {
  int i;
  struct inthash *p = (struct inthash *)malloc(sizeof(struct inthash));
  if (!p) exit(1);
  for (i=0; i<N; i++) p->buckets[i]=NULL;
  return p;
}  

struct icell *new_icell (size_t key, void *value, struct icell *next) {
  struct icell *p = (struct icell *)malloc(sizeof(struct icell));
  if (!p) exit(1);
  p->key = key;
  p->value = value;
  p->next = next;
  return p;
}

void *inthash_lookup (struct inthash *p, size_t key) {
  struct icell *q = p->buckets[key%N];
  while (q) {
    if (q->key==key)
      return q->value;
    q=q->next;
  }
  return NULL;
}

struct icell *inthash_insert_list (struct icell **r0, size_t key) {
  struct icell *p, **r;
  for(r=r0; ; r=&p->next) {
    p = *r;
    if (!p) {
      p = new_icell(key,NULL,NULL);
      *r = p;
      return p;
    }
    if (p->key==key) {
      return p;
    }
  }
}  

void* inthash_insert (inthash_t p, size_t key, void *value) {
  struct icell *q;
  void *old;
  q=inthash_insert_list (& p->buckets[key%N], key);
  old=q->value;
  q->value=value;
  return old;
}
