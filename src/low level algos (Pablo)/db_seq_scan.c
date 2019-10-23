/* The sequential scan creates an iterator on the tuples
   pointed to by the primary key index of the relation.
   To learn more about PostgreSQL's physical plans, visit
   https://www.postgresql.org/docs/9.2/using-explain.html */

#include "db_seq_scan.h"

/* 
when we init, we create a new cursor
on the index data. The iterator environment
now has the index and a working cursor.
Before init, we cannot assume there's a 
cursor. 
*/
void seq_scan_init(void* env) {
  // get index from environment
  struct seq_scan_env *e = (struct seq_scan_env*) env;
  struct IndexObj* idx = e->index_obj;
  char* index_type = e->index_type;
  
  // CASE STRINGLIST
  if (strcmp(index_type, "stringlist") == 0) {
    struct StringlistIndexObj* slist = (struct StringlistIndexObj*) idx->obj;
    struct UnordSetMtable* mtable = slist->mtable;
    // get index data
    void* data = slist->index_data;
    // if cannot create new cursor, exit
    if(!(e->cursor =  mtable->get_cursor(data))) exit(1);
    // otherwise, move cursor to beginning
    mtable->move_to_first(e->cursor);
  } 

  // CASE HASHTABLE
  else if (strcmp(index_type, "inthash") == 0) {
    struct HashtableIndexObj* ht = (struct HashtableIndexObj*) idx->obj;
    struct UnordIndexMtable* mtable = ht->mtable;
    // get index data
    void* data = ht->index_data;
    // if cannot create new cursor, exit
    if(!(e->cursor =  mtable->get_cursor(data))) exit(1);
    // otherwise, move cursor to beginning
    mtable->move_to_first(e->cursor);
  }
};


/* 
when we  move to next, we use the
current cursor on the data and advance
it one position. Sequential scan accesses
all elements in the index.
*/ 
const void* seq_scan_next(void* env) {
  // access cursor and indexobj
  struct seq_scan_env *e = (struct seq_scan_env*) env;
  struct IndexObj* idx = e->index_obj;
  char* index_type = e->index_type;
  void* cursor = e->cursor;
  
  // CASE STRINGLIST
  if (strcmp(index_type, "stringlist") == 0) {
    struct StringlistIndexObj* slist = (struct StringlistIndexObj*) idx->obj;
    struct UnordSetMtable* mtable = slist->mtable;
    // get what the cursor is pointing at
    const void* pair = mtable->get_pair(env);
    // advance cursor
    mtable->move_to_next(cursor);
    return pair;
  } 
  
  // CASE HASHTABLE
  else if (strcmp(index_type, "inthash") == 0) {
    struct HashtableIndexObj* ht = (struct HashtableIndexObj*) idx->obj;
    struct UnordIndexMtable* mtable = ht->mtable;
    // get what the cursor is pointing at
    const void* pair = mtable->get_pair(env);
    // advance cursor
    mtable->move_to_next(cursor);
    return pair;
  }
  
  return NULL;
};


/* when we close, free the cursor */ 
void seq_scan_close(void* env) {
  struct seq_scan_env *e = (struct seq_scan_env*) env;
  struct IndexObj* idx = e->index_obj;
  char* index_type = e->index_type;
  void* cursor =e->cursor;
  
  // CASE STRINGLIST
  if (strcmp(index_type, "stringlist") == 0) {
    struct StringlistIndexObj* slist = (struct StringlistIndexObj*) idx->obj;
    struct UnordSetMtable* mtable = slist->mtable;
    mtable->free_cursor(cursor);
  }
  
  // CASE HASHTABLE
  else if (strcmp(index_type, "inthash") == 0) {
    struct HashtableIndexObj* ht = (struct HashtableIndexObj*) idx->obj;
    struct UnordIndexMtable* mtable = ht->mtable;
    mtable->free_cursor(cursor);
  }
} 

// collect all methods for seq scan in one mtable
struct iterator_methods seq_scan_iterator_mtable = {&seq_scan_init, &seq_scan_next, &seq_scan_close};

					   
/* sequential scan operator takes an 
Index Object and returns an iterator on this index */ 

iterator seq_scan(struct IndexObj* index_obj) {
  // malloc iterator, exit if needed
  iterator it = malloc(sizeof(struct iterator_t));
  if(!it) exit(1);
  
  // the method table is the seq scan mtable
  it->mtable = &seq_scan_iterator_mtable;
  
  // malloc environment, exit if needed 
  struct seq_scan_env *env = malloc(sizeof(struct seq_scan_env));
  if(!env) exit(1);
  
  // set up and return
  env->index_obj = index_obj;
  it->env = (void*) env;
  return (iterator) it;
}  
