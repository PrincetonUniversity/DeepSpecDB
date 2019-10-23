#ifndef _DBINDEXJOINH_
#define _DBINDEXJOINH_

#include "db_seq_scan.h"

struct index_join_env {
  // outer relation info
  iterator outer;
  attribute_list outer_attrs;
  
  // inner relation info
  attribute_list inner_attrs;
  Index ind_on_inner;
  Schema ind_on_inner_sch;
  
  // what is this?
  fifo* current_inner;
  const void* current_outer;
  
  // columns to be joined
  attribute_list join_attrs;
};

// Index index_scan(relation rel, attribute_list attrs);

void index_join_init(void* env);

const void* index_join_next(void* env);

void index_join_close(void* env);

iterator index_join( /*attribute_list outer_attrs, attribute_list inner_attrs, */ attribute_list outer_join_attrs, attribute_list inner_join_attrs,
		    iterator outer, Index ind_on_inner);
			
#endif