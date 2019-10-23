#include "db_index_join.h"

/* The index scan produces an index given a list of attributes and a pk index (btree).
   The returned index maps projections of tuples on the given list of attributes to fifo lists of tuple addresses. */

/*
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
}; */






/* The index join receives as input a schema of the join attributes, an interator for the outer relation
   and an index for the inner relation. This index must map join attributes values to iterators (or fifo lists)
   whose collection is the set of tuples in the inner relation whose projection on the join attributes gives the key.
   It outputs an iterator giving the merged tuples. */


void index_join_init(void* env) {
  struct index_join_env* e = (struct index_join_env*) env;
  init_iterator(e->outer);
  
  // what are these for?
  e->current_inner = NULL;
  outer_tuple = NULL;
};




const void* index_join_next(void* env) {
  // environment
  struct index_join_env* e = (struct index_join_env*) env;
  // outer tuple
  const void* outer_tuple = e->current_outer;
  // inner and outer attributes (all columns)
  attribute_list inner_attrs = e->inner_attrs;
  attribute_list outer_attrs = e->outer_attrs;
  
  // build key and look up the tuples in the inner index with that key
  
  // while fifo is null or empty, AND there's more tuples in outer index, keep going until we get 
  while((e->current_inner == NULL || fifo_empty(e->current_inner)) && (outer_tuple = get_next(e->outer)) ) {
    // this is the key we're looking for
    const void* proj = get_projection(outer_attrs, outer_tuple, e->join_attrs);
    // set current inner to be what we looked up in the index
    e->current_inner = (fifo*) index_lookup(e->ind_on_inner_sch, e->ind_on_inner, proj);
  };
  
  if(!outer_tuple) return NULL;
  
  // join the two tuples outer_tuple and fifo_get(e->current_inner) into a new memory slot
  size_t outer_num_cols = attribute_list_length(outer_attrs);
  size_t inner_num_cols = attribute_list_length(inner_attrs);
  size_t join_length = attribute_list_length(e->join_attrs);
  
  // calculate the size of the joined tuple
  size_t joined_tuple_size = outer_num_cols + inner_num_cols - join_length + 1;
  // allocate memory for joined tuple
  void* new_tuple = malloc(sizeof(void*) * joined_tuple_size);
  // copy the whole outer tuple into new tuple
  memcpy(new_tuple, outer_tuple, sizeof(void*) * outer_num_cols);
  // copy the part of the inner tuple that is not common
  const void* inner_tuple = fifo_get(e->current_inner)->data;
  
  attribute_list k = inner_attrs;
  size_t n = 0;
  for(; k != NULL; k=k->next) {
    // name of this column
    char* id = k->id;
    // domain of this column
    domain dom = k->domain;
    // calculate offset in the inner tuple
    size_t inner_t_ofs = get_offset(inner_attrs, id, dom); // Optimization: getting the offsets should be only performed once and not at each next()
    // IF this attribute is not in the inner join attributes list
    if(get_offset(e->join_attrs, id, dom) < 0) {
      //TODO: no idea what this does -- check if this actually works
      memcpy((void*) (((size_t*) new_tuple) + outer_num_cols + n), (void*) ((size_t*) inner_tuple + inner_t_ofs), sizeof(size_t));
      n++;
    };
  }
  return new_tuple;
};

void index_join_close(void* env) {
  struct index_join_env* e = (struct index_join_env*) env;
  close_iterator(e->outer);
  return; 
};

struct methods index_join_iterator_mtable = { &index_join_init, &index_join_next, &index_join_close };

iterator index_join(attribute_list outer_attrs, attribute_list inner_attrs, attribute_list join_attrs,
		    iterator outer, Index ind_on_inner) {
  struct index_join_env *env = malloc(sizeof(struct index_join_env)); if(!env) exit(1);
  env->outer = outer;
  env->ind_on_inner = ind_on_inner;
  env->outer_attrs = outer_attrs;
  env->inner_attrs = inner_attrs;
  env->join_attrs = join_attrs;
  env->ind_on_inner_sch = get_schema(join_attrs);

  iterator it = malloc(sizeof(struct iterator_t));
  if(!it) exit(1);
  it->mtable = &index_join_iterator_mtable;
  it->env = (void*) env;
  return it;
}