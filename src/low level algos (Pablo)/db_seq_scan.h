#ifndef _DBSEQSCANH_
#define _DBSEQSCANH_

#include "db_util.h"

struct seq_scan_env {
  btree bt;
  btree_cursor c; // this includes the btree too, but is uninitialized before a call to init(). We need the btree to be able to create the new cursor.
};

void seq_scan_init(void* env);

const void* seq_scan_next(void* env);

void seq_scan_close(void* env);

iterator seq_scan(relation r);

#endif