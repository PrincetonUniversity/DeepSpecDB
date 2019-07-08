#include "db_index_join.h"

/* The index scan produces an index given a list of attributes and a pk index (btree).
   The returned index maps projections of tuples on the given list of attributes to fifo lists of tuple addresses. */

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