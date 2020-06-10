#ifndef _DBSEQSCANH_
#define _DBSEQSCANH_

#include "db_util.h"

// when the environment is created
// index_obj and index_type are specified
// cursor is created later by init
struct seq_scan_env {
  struct IndexObj* index_obj;
  void* cursor;
  char* index_type;
};

void seq_scan_init(void* env);

const void* seq_scan_next(void* env);

void seq_scan_close(void* env);

iterator seq_scan(struct IndexObj* ic);

#endif