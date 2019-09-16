#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include "stringlist.h"


struct scell {
  char *key;
  void *value;
  struct scell *next;
};

struct stringlist {
  struct scell *root;
};

typedef struct stringlist* stringlist_t;

struct kvpair {
  char *key;
  void *value;
};


stringlist_t stringlist_new(void) {
  struct stringlist *p = (struct stringlist *)malloc(sizeof(struct stringlist));
  if (!p) exit(1);
  p->root=NULL;
  return p;
}  
  
char *copy_string (char *s) {
  int n = strlen(s)+1;
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

int stringlist_cardinality(stringlist_t p) {
  struct scell *q;
  int size = 0;
  for (q=p->root; q; q=q->next) {
    size++;
  }
  return size;
}

/********* CURSOR OPERATIONS **********/

struct cursor {
  stringlist_t list;
  int cur;
};

/* get cursor - takes a key, returns a cursor */
struct cursor* stringlist_get_cursor(stringlist_t p, char *key) {
  struct scell *q;
  int cur = 0;
  struct cursor *mc = (struct cursor*) malloc(sizeof(struct cursor));
  mc->list = p;
  for (q=p->root; q; q=q->next) {
    if (strcmp(q->key, key) == 0) {
      mc->cur = cur;
      return mc;
    }
    cur++;
  }
  mc->cur = 0;
  return mc;
}

/* get pair - given cursor, return key value pair */
struct kvpair* stringlist_get_pair(struct cursor *mc) {
  stringlist_t p = mc->list;
  int cur = mc->cur;
  struct scell *q;
  int position = 0;
  struct kvpair *pair; 
  for (q=p->root; q; q=q->next) {
    if (cur == position) {
      pair = (struct kvpair*) malloc(sizeof(struct kvpair));
      pair->key = q->key;
      pair->value = q-> value;
      return pair;
    }
    position++;
  }
  return pair;
}

/* move to next - takes cursor, moves to next position */
struct cursor* stringlist_move_to_next(struct cursor *mc) {
  stringlist_t p = mc->list;
  int cur = mc->cur;
  int length = stringlist_cardinality(p);
  cur++;
  if (cur > length) 
    mc->cur = length-1;
  else if (cur <= 0) 
    mc->cur = 0;
  else mc->cur = cur;
  return mc;
}

/* move to first - move to 0 */
struct cursor* stringlist_move_to_first(struct cursor* mc) {
  mc->cur = 0;
  return mc;
}




