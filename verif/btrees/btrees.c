// Authors: Oluwatosin V. Adewale, Aurèle Barrière, Pablo Le Hénaff 

#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <stddef.h>

#define PARAM 8
#define MAX_DEPTH 20

typedef size_t key;
typedef struct node node;
struct btree {
  struct node* root;
  size_t num_records;
  unsigned int depth;
};

typedef union child_or_record {
  node* child;
  const void* record;
} child_or_record;

struct entry {
  key key;
  union child_or_record content;
};

struct node {
  unsigned int is_leaf: 1;
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
  struct btree* t;
  if(! (t = malloc(sizeof(struct btree)))) exit(1);
  if(! (t->root = malloc(sizeof(node)))) exit(1);
  t->root->is_leaf = 1;
  t->root->num_keys = 0;
  t->root->ptr0 = NULL;
  t->num_records = 0;
  t->depth=0;
  return t;
};

node* child_at(node *n, int i) {
  if(i < 0) return n->ptr0;
  else return n->entries[i].content.child;
};

const void* record_at(node *n, int i) {
  return n->entries[i].content.record;
};

void down_to_first(cursor *c) {
  while(!c->ancestors[c->level].node->is_leaf) {
    struct cursor_entry last = c->ancestors[c->level];
    c->level++;
    c->ancestors[c->level].node = child_at(last.node, last.index);
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

  if(c->ancestors[c->level].index >= c->ancestors[c->level].node->num_keys - 1)
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
    c->ancestors[c->level].node = child_at(last.node, last.index);
    c->ancestors[c->level].index = find_index(c->ancestors[c->level].node, k);
  };
};

void move_to_key(cursor *c, key k) {
  while(c->level > 0 && (k < c->ancestors[c->level].node->entries[0].key || k > c->ancestors[c->level].node->entries[c->ancestors[c->level].node->num_keys - 1].key)) c->level--;
  c->ancestors[c->level].index = find_index(c->ancestors[c->level].node, k);
  down_to_key(c, k);
  return;
};

const void* get(cursor *c, key k) {
  move_to_key(c, k);
  return record_at(c->ancestors[c->level].node, c->ancestors[c->level].index);
};

void insert_entry(node *n, unsigned int i, key k, child_or_record data) {
  int c;
  for(c = n->num_keys; c > i; c--)
    n->entries[c] = n->entries[c-1]; // shift
    
  n->entries[i].key = k;
  n->entries[i].content = data;
  n->num_keys++;
};

void insert_aux(cursor *c, int level, key k, child_or_record data) {
  if(level <= -1) { // update the cursor too
    node *new_root;
    if(! (new_root = malloc(sizeof(node)))) exit(1);
    new_root->is_leaf = 0;
    new_root->num_keys = 1;
    node *old_root = c->btree->root;
    new_root->ptr0 = old_root;
    new_root->entries[0].key = k;
    new_root->entries[0].content = data;
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
    if(i < n->num_keys && n->entries[i].key == k) n->entries[i].content = data; // update, i >= 0
    else if(n->num_keys < 2*PARAM) {
	insert_entry(n, i, k, data);
	c->btree->num_records++;
    } else {
      insert_entry(n, i, k, data);
      // split the leaf node
      node *new;
      if(! (new = malloc(sizeof(struct node)))) exit(1);
      new->ptr0 = NULL;
      new->is_leaf = 1;
      memcpy(new->entries, n->entries + PARAM, (PARAM + 1) * sizeof(struct entry));
      new->num_keys = PARAM + 1;
      n->num_keys = PARAM;
      return insert_aux(c, level - 1, new->entries[0].key, (child_or_record) new);
    };
  } else {
    if(n->num_keys < 2*PARAM) {
      insert_entry(n, i + 1, k, data);
      c->btree->num_records++;
    } else {
      insert_entry(n, i + 1, k, data);
      node *new;
      if(! (new = malloc(sizeof(struct node)))) exit(1);
      key middle_key = n->entries[PARAM].key;
      new->ptr0 = n->entries[PARAM].content.child;
      new->is_leaf = 0;
      memcpy(new->entries, n->entries + PARAM + 1, (PARAM + 1) * sizeof(struct entry));
      new->num_keys = PARAM;
      n->num_keys = PARAM;
      return insert_aux(c, level - 1, middle_key, (child_or_record) new);
    };
  };
  return;
};

void insert(cursor *c, key k, const void* rec) {
  move_to_key(c, k);
  insert_aux(c, c->level, k, (child_or_record) rec);
};

int main() {

  struct btree *t = new_btree();
  cursor *c = new_cursor(t);

  int k;
  for(k = 0; k < 30; k++) insert(c, k, NULL);
  for(k = 29; k >= 0; k--) insert(c, k, k%2==0 ? NULL : 1);

  

  printf("%p\n", get(c, 23));

  return 0;
};
