#ifndef db_client_h
#define db_client_h

#include <stdio.h>
#include <stdbool.h>
#include "relation.h"

/*=========== ENTRIES AND ATTRIBUTES =========== */

// types of entries that can appear in the table
typedef enum domain { Int, Str } domain;

// list of "columns" in the table
typedef struct attribute_list {
    char* id;
    domain domain;
    struct attribute_list* next;
}* attribute_list_t;

typedef struct index_attributes {
    attribute_list_t attrs;
    attribute_list_t pk_attrs; // UNIQUE
}* index_attributes_t;

// a single value in the table
// does this need to have size_t?
typedef union contents {
    size_t int_cont;
    char* str_cont;
} contents;

// an entry is an int val/string val + domain specifying which one it is
typedef struct entry {
    domain dom;
    contents cont;
} entry;

/*=========== ORDERED INDEX =========== */

// env should be cursor? make cursor struct

typedef struct OrdIndexMtable {
    //basic
    void* (*create_index) ();
    void* (*create_cursor) (void* env);
    size_t (*cardinality) (void* env);
    
    //cursor
    Bool (*move_to_next) (void* env);
    Bool (*move_to_first) (void* env);
    void* (*go_to_key) (void* env, entry key);
    Bool (*cursor_has_next) (void* env);
    
    //insert & lookup
    void* (*put_record) (void* env, entry key, const void* value);
    const void* (*get_record) (void* env);
} OrdIndexMtable;

/*=========== BTREE INDEX =========== */

typedef struct BtreeCursor {
    Relation_T btree;
    Cursor_T cur;
}* BtreeCursor_T;

//typedef struct BtreeIndex {
//    OrdIndexMtable* methods;
//    BtreeCursor* index;
//    index_attributes attrs;
//} BtreeIndex;

#endif /* db_client_h */
