#include "db_util.h"

size_t attribute_list_length(attribute_list l) {
  attribute_list x = l;
  size_t n = 0;
  while(x) { x = x->next; n++; }
  return n;
};

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
  close_iterator(it);
  return res;
};


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


void* get_projection(attribute_list attrs_all, const void* t, attribute_list attrs_proj) {
  if(!attrs_proj) exit(1);
  size_t ofs = get_offset(attrs_all, attrs_proj->id, attrs_proj->domain);
  void* current = (void*) *((size_t*) t + ofs);
  if(!attrs_proj->next) return current;
  return build_keypair(current, get_projection(attrs_all, t, attrs_proj->next)); // TODO: optimize this? iterative instead of recursive?
};

/* This function is useful for testing purposes ie easy creation of test tables (see main).
   It creates a new primary key index pointing to the given data. */
   
   /*
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
*/


