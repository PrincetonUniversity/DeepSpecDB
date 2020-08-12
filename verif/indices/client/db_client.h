#ifndef db_client_h
#define db_client_h

#include <stdio.h>
#include <stdbool.h>
#include "relation.h"

/*=========== ENTRIES AND ATTRIBUTES =========== */

// types of entries that can appear in the table
typedef enum domain { Int = 0, Str = 1 } domain;

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
typedef union entry {
    size_t int_cont;
    char* str_cont;
} entry;

typedef struct BtreeCursor {
    Relation_T btree;
    Cursor_T cur;
}* BtreeCursor_T;

/*=========== ORDERED INDEX =========== */
typedef struct value_t *Value_T;
typedef struct key_t *Key_T;
typedef struct db_cursor_t *DB_Cursor_T;
typedef struct index_t *Index_T;

typedef struct OrdIndexMtable {
    //basic
    Index_T (*create_index) ();
    DB_Cursor_T (*create_cursor) (Index_T env);
    size_t (*cardinality) (DB_Cursor_T env);
    
    //cursor
    Bool (*move_to_next) (DB_Cursor_T env);
    Bool (*move_to_first) (DB_Cursor_T env);
    Bool (*go_to_key) (DB_Cursor_T env, Key_T key);
    Bool (*cursor_has_next) (DB_Cursor_T env);
    
    //insert & lookup
    void (*put_record) (DB_Cursor_T env, Key_T key, const Value_T value);
    const Value_T (*get_record) (DB_Cursor_T env);
} OrdIndexMtable;

#endif /* db_client_h */
