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
  atom_ptr *value;
  atom_ptr *left, *right;
} tree;
typedef atom_ptr *treebox;
treebox tb;
lock_t thread_lock[N];
typedef struct tree **refpointer;

void *surely_malloc(size_t n)
{
  void *p = malloc(n);
  if (!p)
    exit(1);
  return p;
}

treebox treebox_new(void)
{
  treebox p = make_atomic_ptr(0); 
  return p;
}

void treebox_free(treebox b)
{
  atom_ptr *at = b;
  struct tree *t = atomic_load_ptr(at);
  if (t != NULL)
  {
    treebox_free(t->right);
    treebox_free(t->left);
    free_atomic_ptr(t->value);
    free(t);
  }
  free_atomic_ptr(at);
}

void insert(treebox t, int x, void *value)
{
  atom_ptr *temp = t;
  struct tree *tp;  
  void ** ref = (void**)surely_malloc(sizeof (*ref));
  *ref = NULL;
  for (;;)
  {
    tp = atomic_load_ptr(temp);
    if (tp == NULL)
   {
      //printf("insert method called\n");
      struct tree *p = (struct tree *)surely_malloc(sizeof *p);
      p->key = x;
      atom_ptr *val = make_atomic_ptr(value);
      p->value = val;
      atom_ptr *left = make_atomic_ptr(0);
      p->left = left;
      atom_ptr *right = make_atomic_ptr(0);
      p->right = right;
      int result = atomic_CAS_ptr(temp, ref, p);
      if (!result)
      {
        //printf("CAS failed\n");
        free_atomic_ptr(val);
        free_atomic_ptr(left);
        free_atomic_ptr(right);
        free(p);
        continue;
      }      
      free(ref);
      return;
    }
    else
    {
      int y = tp->key;
      if (x < y)
      {
        temp = tp->left;
      }
      else if (y < x)
      {
        temp = tp->right;
      }
      else
      {
        atomic_store_ptr(tp->value,value);
        free(ref);
        return;
      }
    }
  }
}

void *lookup(treebox t, int x)
{
  atom_ptr *ap = t;
  struct tree *p = atomic_load_ptr(ap);
  void *v;
  while (p != NULL)
  {
    int y = p->key;
    if (x < y)
    {
      p = atomic_load_ptr(p->left);
    }
    else if (y < x)
    {
      p = atomic_load_ptr(p->right);

    }
    else
    {
      v = atomic_load_ptr(p->value);
      return v;
    }
  }
  return NULL;
}

void *thread_func_insert(void *args)
{
  lock_t *l = (lock_t *)args;
  for (int i = 1; i <= 10; i++)
  {
    insert(tb, i, "value");
  }
  //printf("insert thread done\n");
  release2((void *)l);
  //printf("insert thread release thread lock\n");
  return (void *)NULL;
}
void *thread_func_lookup(void *args)
{
  lock_t *l = (lock_t *)args;
  for (int i = 10; i >= 1; i--)
  {
    void *v = lookup(tb,i);
    //printf("%s\n", ((v != NULL) ? v : "value not found"));
  }
  //printf("lookup thread done\n");
  release2((void *)l);
  //printf("lookup thread release thread lock\n");
  return (void *)NULL;
}

int main(void)
{
  tb = treebox_new();

  /* Spwan 100 lookup thread */
  for (int i = 5; i < 10; i++)
  {
    lock_t *l = &(thread_lock[i]);
    makelock((void *)l);
    spawn((void *)&thread_func_lookup, (void *)l);
  }

  /* Spwan 100 insert thread */
  for (int i = 0; i < 5; i++)
  {
    lock_t *l = &(thread_lock[i]);
    makelock((void *)l);
    spawn((void *)&thread_func_insert, (void *)l);
  }
  

 // printf("I am done spawning all threads here \n");
  /*JOIN */
  for (int i = 0; i < N; i++)
  {
    lock_t *l = &(thread_lock[i]);
    acquire((void *)l);
    freelock2((void *)l);
  }
  treebox_free(tb);
  //printf("Everything done here \n");
  return 0;
}
