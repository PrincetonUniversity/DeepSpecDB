// Authors: Pablo Le Hénaff, Oluwatosin V. Adewale, Aurèle Barrière

#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <stddef.h>

#define PARAM 8
#define MAX_DEPTH 20

typedef unsigned int key;
typedef struct node node;

struct btree {
  struct node* root;
  unsigned int num_records;
  unsigned int depth;
};

struct entry {
  key key;
  void* ptr;
};

struct node {
  unsigned char is_leaf; // or bit field
  unsigned int num_keys;
  node* ptr0;
  struct entry entries[2*PARAM + 1]; // extra space for insertion before splitting
};

struct cursor_entry {
  int index;
  node *node;
};  

typedef struct cursor {
  struct btree *btree;
  unsigned int level;
  struct cursor_entry ancestors[MAX_DEPTH];
} cursor;

struct btree* new_btree() {
  struct btree *t;
  if(! (t = malloc(sizeof(struct btree)))) exit(1);
  if(! (t->root = malloc(sizeof(node)))) exit(1);
  t->root->is_leaf = 1;
  t->root->num_keys = 0;
  t->root->ptr0 = NULL;
  t->num_records = 0;
  t->depth=0;
  return t;
};

void* ptr_at(node *n, int i) {
  if(i < 0) return (void*) n->ptr0;
  else return n->entries[i].ptr;
};

void down_to_first(cursor *c) {
  while(!c->ancestors[c->level].node->is_leaf) {
    struct cursor_entry last = c->ancestors[c->level];
    c->level++;
    c->ancestors[c->level].node = (node*) ptr_at(last.node, last.index);
    c->ancestors[c->level].index = c->ancestors[c->level].node->is_leaf ? 0 : -1;
  };
};

void move_to_first(cursor *c) {
  while(c->level > 0 && c->ancestors[c->level].index > 0)
    c->level--;
  c->ancestors[c->level].index = c->ancestors[c->level].node->is_leaf ? 0 : -1;
  down_to_first(c);
  return;
};

cursor* new_cursor(struct btree *t) {
  cursor *c;
  if(! (c = malloc(sizeof(cursor)))) exit(1);
  c->btree = t;
  c->level = 0;
  c->ancestors[0].node = t->root;
  move_to_first(c);
  return c;
};

void move_to_next(cursor *c) {
  while(c->level > 0 && c->ancestors[c->level].index >= c->ancestors[c->level].node->num_keys - 1)
    c->level--;

  if(c->ancestors[c->level].index >= (int) c->ancestors[c->level].node->num_keys - 1)
    { c->level = c->btree->depth; return; } // the cursor stays empty, at the last position

  c->ancestors[c->level].index++;
  down_to_first(c);

  return;
};

int find_index(node *n, key k) {
  int i = 0;
  if(n->is_leaf) {
    while(i < n->num_keys && n->entries[i].key < k) i++;
    return i;
  } else {
    while(i < n->num_keys && n->entries[i].key <= k) i++;
    return (i-1);
  };
};

void down_to_key(cursor *c, key k) {
  while(!c->ancestors[c->level].node->is_leaf) {
    struct cursor_entry last = c->ancestors[c->level];
    c->level++;
    c->ancestors[c->level].node = (node*) ptr_at(last.node, last.index);
    c->ancestors[c->level].index = find_index(c->ancestors[c->level].node, k);
  };
};

void move_to_key(cursor *c, key k) {
  while(c->level > 0 && (k < c->ancestors[c->level].node->entries[0].key || k > c->ancestors[c->level].node->entries[c->ancestors[c->level].node->num_keys - 1].key)) c->level--;
  c->ancestors[c->level].index = find_index(c->ancestors[c->level].node, k);
  down_to_key(c, k);
  return;
};

void* get(cursor *c, key k) {
  move_to_key(c, k);
  return ptr_at(c->ancestors[c->level].node, c->ancestors[c->level].index);
};

void init(cursor *c) {
  move_to_first(c);
};

void* next(cursor *c) {
  void *rec = ptr_at(c->ancestors[c->level].node, c->ancestors[c->level].index);
  move_to_next(c);
  return rec;
};

void insert_entry(node *n, unsigned int i, key k, void* ptr) {
  int c;
  for(c = n->num_keys; c > i; c--)
    n->entries[c] = n->entries[c-1]; // shift
    
  n->entries[i].key = k;
  n->entries[i].ptr = ptr;
  n->num_keys++;
};

void insert_aux(cursor *c, int level, key k, void* ptr) {
  if(level <= -1) { // update the cursor too

    if(c->btree->depth >= MAX_DEPTH - 1) exit(1);
    
    node *new_root;
    if(! (new_root = malloc(sizeof(node)))) exit(1);
    new_root->is_leaf = 0;
    new_root->num_keys = 1;
    node *old_root = c->btree->root;
    new_root->ptr0 = old_root;
    new_root->entries[0].key = k;
    new_root->entries[0].ptr = ptr;
    c->btree->root = new_root;
    c->btree->num_records++;
    c->btree->depth++;
    
    unsigned int j = c->level;
    for(; j > 0; j--)
      c->ancestors[j] = c->ancestors[j-1];
    c->ancestors[0].node = new_root;
    c->ancestors[0].index = c->ancestors[1].index < PARAM - 1 ? -1 : 0;
    return;
  };

  int i = c->ancestors[level].index;
  node *n = c->ancestors[level].node;

  if(n->is_leaf) {
    if(i < n->num_keys && n->entries[i].key == k) n->entries[i].ptr = ptr; // update
    else if(n->num_keys < 2*PARAM) {
      insert_entry(n, i, k, ptr);
      c->btree->num_records++;
    } else {
      insert_entry(n, i, k, ptr);
      // split the leaf node
      node* new;
      if(! (new = malloc(sizeof(struct node)))) exit(1);
      new->ptr0 = NULL;
      new->is_leaf = 1;
      memcpy(new->entries, n->entries + PARAM, (PARAM + 1) * sizeof(struct entry));
      new->num_keys = PARAM + 1;
      n->num_keys = PARAM;
      insert_aux(c, level - 1, new->entries[0].key, (void*) new);
    };
  } else {
    if(n->num_keys < 2*PARAM) {
      insert_entry(n, i + 1, k, ptr);
      c->btree->num_records++;
    } else {
      insert_entry(n, i + 1, k, ptr);
      node *new;
      if(! (new = malloc(sizeof(struct node)))) exit(1);
      key middle_key = n->entries[PARAM].key;
      new->ptr0 = (node*) n->entries[PARAM].ptr;
      new->is_leaf = 0;
      memcpy(new->entries, n->entries + PARAM + 1, (PARAM + 1) * sizeof(struct entry));
      new->num_keys = PARAM;
      n->num_keys = PARAM;
      insert_aux(c, level - 1, middle_key, (void*) new);
    };
  };

  return;
};

void insert(cursor *c, key k, void* ptr) {
  move_to_key(c, k);
  insert_aux(c, c->level, k, ptr);
};

int main() {

  struct btree *t = new_btree();
  cursor *c = new_cursor(t);

  for(int i = 0; i < 100; i++) insert(c, 2*i, NULL);

  insert(c, 11, NULL);
  insert(c, 33, NULL);

  move_to_key(c, 0);
  
  for(int i = 0; i < 102; i++) {
    printf("%i\n", c->ancestors[c->level].node->entries[c->ancestors[c->level].index].key);
    move_to_next(c);
  };

  return 0;
};
