#include "db_index_join.h"
#include "db_seq_scan.h"
#include "db_util.h"

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
