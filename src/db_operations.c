#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "util.h"

// resolve conflicting Key typedef
// I know, this is ugly and needs to be fixed
#define Key btree_Key
#include "relation.h"
#undef Key

#include "queue2.c"

#include "index.h" // in ../tuplekey/
#include "inthash_schema.h"
#include "stringlist_schema.h"
#include "tuple_schema.h"

typedef enum domain { Int, Str } domain;

typedef struct attribute_list_t {
  char* id;
  domain domain;
  struct attribute_list_t* next;
} *attribute_list;

size_t attribute_list_length(attribute_list l) {
  attribute_list x = l;
  size_t n = 0;
  while(x) { x = x->next; n++; }
  return n;
};

typedef Relation_T btree;
typedef Cursor_T btree_cursor;

typedef struct relation_t {
  attribute_list attrs;
  attribute_list pk_attrs; // has to be unique for now
  btree pk_index;
} *relation;

union value {
  unsigned long int_value;
  char* str_value;
};

struct entry {
  domain domain;
  union value value;
};

/* The iterator class */

struct methods {
  void (*init) (void* env);
  const void* (*next) (void* env);
  void (*close) (void* env);
};

typedef struct iterator_t {
  struct methods *mtable;
  void* env;
} *iterator;

void init_iterator(iterator it) { it->mtable->init(it->env); };
const void* get_next(iterator it) { return it->mtable->next(it->env); };
void close_iterator(iterator it) { it->mtable->close(it->env); };

/* Materialize produces a fifo list out of an iterator. */

fifo* materialize(iterator it) {
  fifo* res = fifo_new();
  init_iterator(it);
  const void* a;
  while((a = get_next(it))) {
    fifo_put(res, make_elem(a));
  };
  return res;
};

/* The sequential scan creates an iterator on the tuples
   pointed to by the primary key index of the relation.
   To learn more about PostgreSQL's physical plans, visit
   https://www.postgresql.org/docs/9.2/using-explain.html */

struct seq_scan_env {
  btree bt;
  btree_cursor c; // this includes the btree too, but is uninitialized before a call to init(). We need the btree to be able to create the new cursor.
};

void seq_scan_init(void* env) {
  struct seq_scan_env *e = (struct seq_scan_env*) env;
  if(!(e->c = RL_NewCursor(e->bt))) exit(1);
  RL_MoveToFirst(e->c);
};

const void* seq_scan_next(void* env) {
  btree_cursor c = ((struct seq_scan_env*) env)->c;
  if (RL_IsEmpty(c) || !RL_CursorIsValid(c)) return NULL;
  const void* res = RL_GetRecord(c);
  // then, move the btree cursor to the next position
  RL_MoveToNext(c);
  return res;
};

void seq_scan_close(void* env) {
  btree_cursor c = ((struct seq_scan_env*) env)->c;
  RL_FreeCursor(c);
}

struct methods seq_scan_iterator_mtable = {&seq_scan_init, &seq_scan_next, &seq_scan_close};
					   
iterator seq_scan(relation r) {
  iterator it = malloc(sizeof(struct iterator_t));
  if(!it) exit(1);
  it->mtable = &seq_scan_iterator_mtable;
  struct seq_scan_env *env = malloc(sizeof(struct seq_scan_env));
  if(!env) exit(1);
  env->bt = r->pk_index;
  env->c = NULL;
  it->env = (void*) env;
  return (iterator) it;
}

/* The index scan produces an index given a list of attributes and a pk index (btree).
   The returned index maps projections of tuples on the given list of attributes to fifo lists of tuple addresses. */

// Generate a Schema out of an attribute list
Schema get_schema_aux(domain d) {
  switch (d) {
  case Int:
    return &inthash_schema;
  case Str:
    return &stringlist_schema;
  default:
    exit(1);
  };
};

Schema get_schema(attribute_list attrs) {
  if(!attrs) return NULL;
  Schema s = get_schema_aux(attrs->domain);
  if(!attrs->next) return s;
  return tuple_schema(s, get_schema(attrs->next));
};

/* The get_offset function retrieves the index (as "number" starting from 0) of the attribute whose name is id,
   among the attribute list attrs_all.
   The function returns -1 if the "id" column was not found.
   It fails if the domains don't match, or if the attribute list is empty. */
int get_offset(attribute_list attrs_all, char* id, domain dom) {
  
  if (!attrs_all) exit(1);
  attribute_list x = attrs_all;
  unsigned int res = 0;
  
  do {
    if(strcmp(id, x->id) == 0) {
      if(dom == x->domain) return res;
      else exit(1); // There exist an "id" attribute but it has a domain different from "dom"
    };
    res++;
  }  while((x = x->next));
  return -1; // attribute not found
};

const void* get_field_address(attribute_list attrs_all, char* id, domain dom, const void* t) {
  size_t ofs = get_offset(attrs_all, id, dom);
  return (void*) ((size_t*) t + ofs);
};

Key get_projection(attribute_list attrs_all, const void* t, attribute_list attrs_proj) {
  if(!attrs_proj) exit(1);
  size_t ofs = get_offset(attrs_all, attrs_proj->id, attrs_proj->domain);
  Key current = (void*) *((size_t*) t + ofs);
  if(!attrs_proj->next) return current;
  return build_keypair(current, get_projection(attrs_all, t, attrs_proj->next)); // TODO: optimize this? iterative instead of recursive?
};

Index index_scan(relation rel, attribute_list attrs) {
  Schema sch = get_schema(attrs);
  Index ind = index_new(sch);
  iterator it = seq_scan(rel);
  init_iterator(it);
  const void* t; Key proj;
  while((t = get_next(it))) {
    proj = get_projection(rel->attrs, t, attrs);
    // TODO: lookup, then insert in the lookuped list, then insert back into the index
    fifo* l = (fifo*) index_lookup(sch, ind, proj);
    if(!l) l = fifo_new();
    fifo_put(l, make_elem(t));
    index_insert(sch, ind, proj, l);
  };
  return ind;
};

/* The index join receives as input a schema of the join attributes, an interator for the outer relation
   and an index for the inner relation. This index must map join attributes values to iterators (or fifo lists)
   whose collection is the set of tuples in the inner relation whose projection on the join attributes gives the key.
   It outputs an iterator giving the merged tuples. */

struct index_join_env {
  iterator outer;
  attribute_list outer_attrs;
  attribute_list outer_join_attrs;
  attribute_list inner_attrs;
  attribute_list inner_join_attrs;
  Index ind_on_inner;
  Schema ind_on_inner_sch;
  fifo* current_inner;
  const void* current_outer;
};

void index_join_init(void* env) {
  struct index_join_env* e = (struct index_join_env*) env;
  init_iterator(e->outer);
  e->current_inner = NULL;
  e->current_outer = NULL;
};

const void* index_join_next(void* env) {
  struct index_join_env* e = (struct index_join_env*) env;
  while((e->current_inner == NULL || fifo_empty(e->current_inner)) && (e->current_outer = get_next(e->outer)) ) {
    Key proj = get_projection(e->outer_attrs, e->current_outer, e->outer_join_attrs);
    e->current_inner = (fifo*) index_lookup(e->ind_on_inner_sch, e->ind_on_inner, proj);
  };
  
  if(!e->current_outer) return NULL;
  
  // join the two tuples e->current_outer and fifo_get(e->current_inner) into a new memory slot
  size_t outer_t_length = attribute_list_length(e->outer_attrs);
  size_t inner_t_length = attribute_list_length(e->inner_attrs);
  size_t join_length = attribute_list_length(e->inner_join_attrs);
  void* new_t = malloc(sizeof(void*) * (outer_t_length + inner_t_length - join_length + 1));
  // copy the whole outer tuple
  memcpy(new_t, e->current_outer, sizeof(void*) * outer_t_length);
  // copy the part of the inner tuple that is not common
  const void* inner_t = fifo_get(e->current_inner)->data;
  attribute_list l = e->inner_attrs;
  size_t n = 0;
  for(; l != NULL; l=l->next) {
    size_t inner_t_ofs = get_offset(e->inner_attrs, l->id, l->domain); // Optimization: getting the offsets should be only performed once and not at each next()
    // IF this attribute is not in the inner join attributes list
    if(get_offset(e->inner_join_attrs, l->id, l->domain) < 0) {
      memcpy((void*) (((size_t*) new_t) + outer_t_length + n), (void*) ((size_t*) inner_t + inner_t_ofs), sizeof(size_t));
      n++;
    };
  }
  return new_t;
};

void index_join_close(void* env) {
  struct index_join_env* e = (struct index_join_env*) env;
  close_iterator(e->outer);
  return; /* TODO */
};

struct methods index_join_iterator_mtable = { &index_join_init, &index_join_next, &index_join_close };

iterator index_join(attribute_list outer_attrs, attribute_list inner_attrs, attribute_list outer_join_attrs, attribute_list inner_join_attrs,
		    iterator outer, Index ind_on_inner) {
  assert(attribute_list_length(outer_join_attrs) == attribute_list_length(inner_join_attrs)); // should also check the domains?
  struct index_join_env *env = malloc(sizeof(struct index_join_env)); if(!env) exit(1);
  env->outer = outer;
  env->ind_on_inner = ind_on_inner;
  env->outer_attrs = outer_attrs;
  env->inner_attrs = inner_attrs;
  env->outer_join_attrs = outer_join_attrs;
  env->inner_join_attrs = inner_join_attrs;
  env->ind_on_inner_sch = get_schema(inner_join_attrs);

  iterator it = malloc(sizeof(struct iterator_t));
  if(!it) exit(1);
  it->mtable = &index_join_iterator_mtable;
  it->env = (void*) env;
  return it;
}

/* This function is useful for testing purposes ie easy creation of test tables (see main).
   It creates a new primary key index pointing to the given data. */
btree index_data(void*** data, int tuple_count, attribute_list attrs, attribute_list primary_key) { 
// The schema has to have a unique, integer primary key attribute.
	if(primary_key == NULL || primary_key->next != NULL || primary_key->domain != Int) exit(1);
	
	// Retrieve the offset of the primary key attribute.
	// Remainder: this will exit(1) if the column is not found in the given schema.
	
	size_t ofs = get_offset(attrs, primary_key->id, primary_key->domain);

	btree bt = RL_NewRelation();
	btree_cursor c = RL_NewCursor(bt); // The btree and cursor creation are already safe malloc-wise.
	
	for (int i = 0; i < tuple_count; i++) {
	  size_t* current_tuple = (size_t*) data[i];
	  btree_Key k = current_tuple[ofs];
	  RL_PutRecord(c, k, (void*) current_tuple);
	};
	return bt;
};

/* Pretty-printing */

size_t nformat_tuple(char* buffer, size_t n, void* t, attribute_list attrs) {
  size_t count = n; int p;
  char formatted [n];
  
  for(attribute_list x = attrs; x != NULL; x = x->next) {
    switch(x->domain) {
    case Int:
      p = snprintf(formatted, n, "| %-5zu ", *((size_t*) get_field_address(attrs, x->id, x->domain, t)));
      break;
    case Str:
      p = snprintf(formatted, n, "| %-20.20s ", *((char**) get_field_address(attrs, x->id, x->domain, t)));
      break;
    default: exit(1);
    };
    if (p < 0) exit(1);
    strncat(buffer, formatted, count);
    if (p >= count) count = 0;
    else count -= p;
  };
  strncat(buffer, "|", count);
  return (n - count - 1);
};

size_t nformat_attrs(char* buffer, size_t n, attribute_list attrs) {
  size_t count = n; int p = 0;
  char formatted [n];
  
  for(attribute_list x = attrs; x != NULL; x = x->next) {
    switch(x->domain) {
    case Int:
      p = snprintf(formatted, n, "| %-5s ", x->id);
      break;
    case Str:
      p = snprintf(formatted, n, "| %-20.20s ", x->id);
      break;
    default: exit(1);
    };
    if (p < 0) exit(1);
    strncat(buffer, formatted, count);
    if (p >= count) count = 0;
    else count -= p;
  };
  strncat(buffer, "|\n", count);
  count -= 3;
  return (n - count);
};


void display_iterator(iterator it, attribute_list attrs) {
  fifo* l = materialize(it); // set a maximum size for the fifo?
  size_t c = 3000;
  char buf[c];
  c -= nformat_attrs(buf, c, attrs);
  while(!fifo_empty(l)) {
    c -= nformat_tuple(buf, c, fifo_get(l)->data, attrs);
    strncat(buf, "\n", c); c--;    
  };
  printf("%s", buf);
};

int main(void) {
  
  // sample table 1 attribute list
  attribute_list a = malloc(sizeof(struct attribute_list_t));
  attribute_list b = malloc(sizeof(struct attribute_list_t));
  
  a->next = b;
  a->id = strdup("A");
  a->domain = Int;
  b->next = NULL;
  b->id = strdup("B");
  b->domain = Str;
  
  attribute_list rel1_pk = malloc(sizeof(struct attribute_list_t));
  rel1_pk->next = NULL;
  rel1_pk->id = strdup("A");
  rel1_pk->domain = Int;

  // sample table 2 attribute list
  attribute_list b2 = malloc(sizeof(struct attribute_list_t));
  attribute_list c = malloc(sizeof(struct attribute_list_t));
  b2->next = c;
  b2->id = strdup("B");
  b2->domain = Str;
  c->next = NULL;
  c->id = strdup("C");
  c->domain = Int;
  
  /* Adding some data

    |--- Relat 1 ---|    |--- Relat 2 ---| 
    | A (pk)|   B   |    |   B   | C (pk)|
    _________________    _________________
    -----------------    -----------------
    |   0   |  zero |    |  zero |   10  |
    -----------------    -----------------
    |   1   |  one  |    |  two  |   12  |
    -----------------    -----------------
    |   2   |  two  |    | three |   13  |
    -----------------    ----------------- 
  */
  
  void** col10 = malloc(2 * sizeof(void*));
  col10[0] = (void*) 0; col10[1] = strdup("zero");
  void** col11 = malloc(2 * sizeof(void*));
  col11[0] = (void*) 1; col11[1] = strdup("one");
  void** col12 = malloc(2 * sizeof(void*));
  col12[0] = (void*) 2; col12[1] = strdup("two");
  
  void*** data1 = malloc(3 * 2 * sizeof(void*));
  data1[0] = col10; data1[1] = col11; data1[2] = col12;
  
  relation rel1 = malloc(sizeof(struct relation_t));
  rel1->pk_index = index_data(data1, 3, a, rel1_pk);
  rel1->attrs = a;
  rel1->pk_attrs = rel1_pk;
  
  void** col20 = malloc(2 * sizeof(void*));
  col20[0] = strdup("zero"); col20[1] = (void*) 10;
  void** col21 = malloc(2 * sizeof(void*));
  col21[0] = strdup("two"); col21[1] = (void*) 12;
  void** col22 = malloc(2 * sizeof(void*));
  col22[0] = strdup("three"); col22[1] = (void*) 13;

  void*** data2 = malloc(3 * 2 * sizeof(void*));
  data2[0] = col20; data2[1] = col21; data2[2] = col22;
  
  relation rel2 = malloc(sizeof(struct relation_t));
  rel2->pk_index = index_data(data2, 3, b2, c);
  rel2->attrs = b2;
  rel2->pk_attrs = c;
    
  iterator rel1_ss = seq_scan(rel1);

  attribute_list ind_attr = malloc(sizeof(struct attribute_list_t));
  ind_attr->next = NULL;
  ind_attr->id = strdup("B");
  ind_attr->domain = Str;


    /* Testing the index join

                 Index Join
       Index cond: rel1.B = rel2.B
                     /\
		    /  \
		   /    \
		  /      \
		 /        \
		/          \
     Sequential scan      Hash        -|
         on rel1       Hash key: B     |
	                    |          |
			    |          |
			    |          |   == Index scan on rel2.B
			    |          |
		     Sequential scan   |
		         on rel2      -|


    |---  Relation 1 |><| Relation 2  ---| 
    |    A    |  rel1.B = rel2.B |   C   |
    _________________    _________________
    -----------------    -----------------
    |    0    |       zero       |  10   |
    --------------------------------------
    |    2    |        two       |  12   |
    --------------------------------------
  */
  
  Index ind_on_rel2 = index_scan(rel2, ind_attr);

  attribute_list rel2_1stcol = malloc(sizeof(struct attribute_list_t));
  rel2_1stcol->next = NULL;
  rel2_1stcol->id = strdup("B");
  rel2_1stcol->domain = Str;
  
  iterator ij_rel1_rel2 = index_join(rel1->attrs, rel2->attrs, b, rel2_1stcol, rel1_ss, ind_on_rel2);

  attribute_list rel12_attrs = malloc(sizeof(struct attribute_list_t));
  rel12_attrs->next = b2;
  rel12_attrs->id = strdup("A");
  rel12_attrs->domain = Int;
  
  display_iterator(ij_rel1_rel2, rel12_attrs);
  
  /* init_iterator(ij_rel1_rel2); // TODO (important): add a warning/fail when next() is called on an uninitialized iterator
  const void* t1 = get_next(ij_rel1_rel2);
  const void* t2 = get_next(ij_rel1_rel2);
  const void* t3 = get_next(ij_rel1_rel2);


  
  char str [300]; str[0] = 0;
  nformat_tuple(str, 300, t2, rel12_attrs);
  printf("%s", str); */
  
  return 0;
};
