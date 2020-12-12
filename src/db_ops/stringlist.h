#ifndef _STRINGLISTH_
#define _STRINGLISTH_

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

struct cursor {
  stringlist_t list;
  int cur;
};

stringlist_t stringlist_new(void);

char *copy_string (char *s);

struct scell *new_scell (char *key, void *value, struct scell *next);

void *stringlist_insert(stringlist_t p, char *key, void *value);

void *stringlist_lookup(stringlist_t p, char *key) ;

int stringlist_cardinality(stringlist_t p);

struct cursor* stringlist_get_cursor(stringlist_t p, char *key);

struct kvpair* stringlist_get_pair(struct cursor *mc);

struct cursor* stringlist_move_to_next(struct cursor *mc) ;

struct cursor* stringlist_move_to_first(struct cursor* mc);


#endif