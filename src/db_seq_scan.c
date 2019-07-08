/* The sequential scan creates an iterator on the tuples
   pointed to by the primary key index of the relation.
   To learn more about PostgreSQL's physical plans, visit
   https://www.postgresql.org/docs/9.2/using-explain.html */

#include "db_seq_scan.h"

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
