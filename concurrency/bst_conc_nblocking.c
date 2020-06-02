#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include "threads.h"
#include "SC_atomics.h"


#define N 10

extern void *malloc(size_t n);
extern void free(void *p);

typedef struct tree{
  int key;
  atom_int *value;
  atom_int *left, *right;
} tree;
typedef atom_int *treebox;
treebox tb;
static const struct tree EmptyStruct;

lock_t thread_lock[N];

void *surely_malloc(size_t n)
{
  void *p = malloc(n);
  if (!p)
    exit(1);
  return p;
}

treebox treebox_new(void)
{
  treebox p = make_atomic(0);  
  return p;
}

void treebox_free(treebox b)
{
  // struct tree *t = *b;
  // if (t != NULL)
  // {
  //   treebox_free(t->right);
  //   treebox_free(t->left);
  //   free(t->value);
  //   free(t);
  // }
  // free(b);
}

void insert(treebox tb, int x, void *value)
{
  atom_int *temp = tb;
  struct tree *t;
  int ref = 0;
  for (;;)
  {
    t = atom_load(temp);
    if (t == NULL)
   {
      printf("insert method called\n");
      struct tree *p = (struct tree *)surely_malloc(sizeof *p);
      p->key = x;
      // valuepointer v = (valuepointer)surely_malloc(sizeof *v);
      // atomic_store(v, value);
      atom_int *val = make_atomic(value);
      p->value = val;
      // treebox lp = (treebox)surely_malloc(sizeof(*p));
      // *lp = NULL;
      atom_int *left = make_atomic(0);
      p->left = left;
      // treebox rp = (treebox)surely_malloc(sizeof(*p));
      // *rp = NULL;
      atom_int *right = make_atomic(0);
      p->right = right;
      printf("%x-before CAS\n",temp);
      int result = atom_CAS(temp, &ref, p);
      printf("%x-afterCAS",temp);
      if (result)
      {
        printf("%d", result);
        return;
      }
      else
      {
        free(val);
        free(left);
        free(right);
        free(p);
        continue;
      }
      return;
    }
    else
    {
      int y = t->key;
      if (x < y)
      {
        temp = t->left;
      }
      else if (y < x)
      {
        temp = t->right;
      }
      else
      {
        atom_store(t->value,value);
        return;
      }
    }
  }
}

void *lookup(treebox tb, int x)
{
  atom_int *t = tb;
  struct tree *p = atom_load(t);
  void *v;
  while (p != NULL)
  {
    int y = p->key;
    if (x < y)
    {
      p = atom_load(p->left);
    }
    else if (y < x)
    {
      p = atom_load(p->right);
    }
    else
    {
      v = atom_load(p->value);
      return v;
    }
  }
  return "value not found";
}

void *thread_func_insert(void *args)
{
  lock_t *l = (lock_t *)args;
  for (int i = 1; i <= 10; i++)
  {
    insert(tb, i, "value");
  }
  printf("insert thread done\n");
  release2((void *)l);
  printf("insert thread release thread lock\n");
  return (void *)NULL;
}
void *thread_func_lookup(void *args)
{
  lock_t *l = (lock_t *)args;
  for (int i = 1; i <= 10; i++)
  {
    printf("%s\n", lookup(tb, i));
  }
  printf("lookup thread done\n");
  release2((void *)l);
  printf("lookup thread release thread lock\n");
  return (void *)NULL;
}

int main(void)
{
  tb = treebox_new();

  /* Spwan 100 lookup thread */
  for (int i = 0; i < 5; i++)
  {
    lock_t *l = &(thread_lock[i]);
    makelock((void *)l);
    spawn((void *)&thread_func_lookup, (void *)l);
  }

  /* Spwan 100 insert thread */
  for (int i = 5; i < 10; i++)
  {
    lock_t *l = &(thread_lock[i]);
    makelock((void *)l);
    spawn((void *)&thread_func_insert, (void *)l);
  }
  printf("I am done to spwan all thread here \n");
  /*JOIN */
  for (int i = 0; i < N; i++)
  {
    lock_t *l = &(thread_lock[i]);
    acquire((void *)l);
    freelock2((void *)l);
  }
  treebox_free(tb);
  printf("Everything done here \n");
  return 0;
}
