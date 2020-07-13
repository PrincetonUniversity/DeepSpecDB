#include "db_client.h"
#include "relation.h"
#include "relation_mem.c"
#include <stdlib.h>
#include <stddef.h>
#include <string.h>
#include <stdio.h>
#include "assert.h"

// init all btree methods
DB_Cursor_T btree_create_index () {
    return (DB_Cursor_T) RL_NewRelation();
}

DB_Cursor_T btree_create_cursor (Index_T env) {
    Relation_T tree = (Relation_T) env;
    BtreeCursor_T cursor = malloc(sizeof(struct BtreeCursor));
    assert(cursor != NULL);
    cursor->btree = tree;
    cursor->cur = RL_NewCursor(tree);
    return (DB_Cursor_T) cursor;
}

size_t btree_cardinality (DB_Cursor_T env) {
    BtreeCursor_T cursor = (BtreeCursor_T) env;
    return RL_NumRecords(cursor->cur);
}

Bool btree_move_to_next (DB_Cursor_T env) {
    BtreeCursor_T cursor = (BtreeCursor_T) env;
    return RL_MoveToNextValid(cursor->cur);
}

Bool btree_move_to_first (DB_Cursor_T env) {
    BtreeCursor_T cursor = (BtreeCursor_T) env;
    return RL_MoveToFirst(cursor->cur);
}

Bool btree_go_to_key (DB_Cursor_T env, Key_T key) {
    BtreeCursor_T cursor = (BtreeCursor_T) env;
    entry* k = (entry*) key;
    goToKey(cursor->cur, k->int_cont);
    return RL_CursorIsValid(cursor->cur);
}

Bool btree_cursor_has_next (DB_Cursor_T env) {
    BtreeCursor_T cursor = (BtreeCursor_T) env;
    return RL_CursorIsValid(cursor->cur);
}

void btree_put_record (DB_Cursor_T env, Key_T key, const Value_T value) {
    BtreeCursor_T cursor = (BtreeCursor_T) env;
    entry* k = (entry*) key;
    RL_PutRecord(cursor->cur, k->int_cont, value);
}

const Value_T btree_get_record (DB_Cursor_T env) {
    BtreeCursor_T cursor = (BtreeCursor_T) env;
    return (Value_T) RL_GetRecord(cursor->cur);
}

OrdIndexMtable btree_mtable =
        {&btree_create_index, &btree_create_cursor,
        &btree_cardinality, &btree_move_to_next,
        &btree_move_to_first, &btree_go_to_key,
        &btree_cursor_has_next, &btree_put_record,
        &btree_get_record};

size_t attr_list_length(attribute_list_t lst) {
    size_t length = 0;
    while(lst != NULL) {
        length++;
        lst = lst->next;
    }
    return length;
}

// for now, assumes only 1 pk column
// return -1 if no match
int index_of_pk_column(attribute_list_t lst, attribute_list_t pk) {
    int ind = 0;
    char* pk_ID = pk->id;
    while(lst != NULL) {
        if (strcmp(pk_ID, lst->id) == 0) {
            return ind;
        }
        ind++;
        lst = lst->next;
    }
    return -1;
}

Cursor_T malloc_btree_cursor() {
    Relation_T rel = RL_NewRelation();
    Cursor_T cur = RL_NewCursor(rel);
    return cur;
}

Relation_T fill_relation(entry arr[], Cursor_T cur, size_t numrows, index_attributes_t att) {
    size_t numcols = attr_list_length(att->attrs);
    size_t pk_num = index_of_pk_column(att->attrs, att->pk_attrs);
    size_t i;
    for (i = 0; i < numrows; i++) {
        void* ptr_to_row = &arr[i * numcols];
        entry key = arr[i*numcols + pk_num];
        RL_PutRecord(cur, key.int_cont, ptr_to_row);
    }
    return cur->relation;
}

// data - 2 columns, student id and name
entry data[] = {{ .int_cont = 1}, { .str_cont = "Alice"},
                { .int_cont = 2}, { .str_cont = "Bob"},
                { .int_cont = 3}, { .str_cont = "Claire"},
                { .int_cont = 4}, { .str_cont = "Dean"}};

// two columns, student ID and student Name
struct attribute_list snd = {"Name", Str, NULL};
struct attribute_list schema = {"ID", Int, &snd};
// the primary key is just the ID column
struct attribute_list primary = {"ID", Int, NULL};
// index attrs
struct index_attributes attrs = {&schema, &primary};



int main(int argc, char *argv[]) {
    
    Cursor_T cur = malloc_btree_cursor();
    Index_T tree = (Index_T) fill_relation(data, cur, 4, &attrs);
    
    
    // first cursor
    DB_Cursor_T bc1 = (DB_Cursor_T) btree_mtable.create_cursor(tree);
    
    // second cursor
    DB_Cursor_T bc2 = (DB_Cursor_T) btree_mtable.create_cursor(tree);
    
    // move the first cursor once
    btree_mtable.move_to_next(bc1);
    // move the second cursor twice
    btree_mtable.move_to_next(bc2);
    btree_mtable.move_to_next(bc2);
    
  /*  const entry_t* rec1 = (const entry_t*) btree_mtable.get_record(bc1);
    const entry_t* rec2 = (const entry_t*) btree_mtable.get_record(bc2);
    
    size_t id1 = ((*rec1)->cont).int_cont;
    char* name1 = ((*(rec1 + 1))->cont).str_cont;
    size_t id2 = ((*rec2)->cont).int_cont;
    char* name2 = ((*(rec2 + 1)))->cont.str_cont;
    
    printf("ID: %d, Name: %s \n", (int) id1, name1);
    printf("ID: %d, Name: %s \n", (int) id2, name2); */
}
