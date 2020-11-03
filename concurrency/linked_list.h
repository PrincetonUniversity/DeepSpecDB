void *surely_malloc(size_t n);
struct list {void *ptr; struct list *tail;};
struct list *createNode(void *v);
struct list *append (struct list *x, struct list *y);
struct list *detach(struct list *x, struct list *y);
int size(struct list *x);
int search(struct list *x, void *y);