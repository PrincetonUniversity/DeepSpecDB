#ifndef _DBINDEXJOINH_
#define _DBINDEXJOINH_

#include "db_seq_scan.h"

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

Index index_scan(relation rel, attribute_list attrs);

void index_join_init(void* env);

const void* index_join_next(void* env);

void index_join_close(void* env);

iterator index_join(attribute_list outer_attrs, attribute_list inner_attrs, attribute_list outer_join_attrs, attribute_list inner_join_attrs,
		    iterator outer, Index ind_on_inner);
			
#endif