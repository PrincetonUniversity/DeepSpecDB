
typedef struct stringlist *stringlist_t;

stringlist_t stringlist_new(void);

void *stringlist_insert(stringlist_t p, char *key, void *value);
void *stringlist_lookup(stringlist_t p, char *key);
