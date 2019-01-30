
typedef struct inthash *inthash_t;

inthash_t inthash_new(void);

void *inthash_insert(inthash_t p, size_t key, void *value);
void *inthash_lookup(inthash_t p, size_t key);
