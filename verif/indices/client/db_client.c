#include "db_client.h"
#include "relation.h"
#include <stdlib.h>
#include <stddef.h>
#include <string.h>
#include <stdio.h>

// init all btree methods
void* btree_create_index () {
    return RL_NewRelation();
}

void* btree_create_cursor (void* env) {
    Relation_T tree = (Relation_T) env;
    BtreeCursor_T cursor = malloc(sizeof(struct BtreeCursor));
    cursor->btree = tree;
    cursor->cur = RL_NewCursor(tree);
    return cursor;
}

size_t btree_cardinality (void* env) {
    BtreeCursor_T cursor = (BtreeCursor_T) env;
    return RL_NumRecords(cursor->cur);
}

Bool btree_move_to_next (void* env) {
    BtreeCursor_T cursor = (BtreeCursor_T) env;
    return RL_MoveToNextValid(cursor->cur);
}

Bool btree_move_to_first (void* env) {
    BtreeCursor_T cursor = (BtreeCursor_T) env;
    return RL_MoveToFirst(cursor->cur);
}

void* btree_go_to_key (void* env, entry key) {
    BtreeCursor_T cursor = (BtreeCursor_T) env;
    RL_MoveToKey(cursor->cur, (key.cont).int_cont);
    return cursor;
}

Bool btree_cursor_has_next (void* env) {
    BtreeCursor_T cursor = (BtreeCursor_T) env;
    return RL_CursorIsValid(cursor->cur);
}

void* btree_put_record (void* env, entry key, const void* value) {
    BtreeCursor_T cursor = (BtreeCursor_T) env;
    RL_PutRecord(cursor->cur, (key.cont).int_cont, value);
    return cursor;
}

const void* btree_get_record (void* env) {
    BtreeCursor_T cursor = (BtreeCursor_T) env;
    return RL_GetRecord(cursor->cur);
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
size_t index_of_pk_column(attribute_list_t lst, attribute_list_t pk) {
    size_t ind = 0;
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

Relation_T create_relation(entry arr[], size_t numrows, index_attributes_t att) {
    
    // if our key is not integer, return null
    if (att->pk_attrs->domain != Int) {
        return NULL;
    }
    
    Relation_T rel = RL_NewRelation();
    Cursor_T cur = RL_NewCursor(rel);
    size_t numcols = attr_list_length(att->attrs);
    size_t pk_num = index_of_pk_column(att->attrs, att->pk_attrs);
    
    size_t i;
    for (i = 0; i < numrows; i++) {
        void* ptr_to_row = &arr[i * numcols];
        entry key = arr[i*numcols + pk_num];
        RL_PutRecord(cur, (key.cont).int_cont, ptr_to_row);
    }
    
    return rel;
}

int main(int argc, char *argv[]) {
    entry e1 = {Int, { .int_cont = 1}};
    entry e2 = {Str, { .str_cont = "Alice"}};
    entry e3 = {Int, { .int_cont = 2}};
    entry e4 = {Str, { .str_cont = "Bob"}};
    entry e5 = {Int, { .int_cont = 3}};
    entry e6 = {Str, { .str_cont = "Claire"}};
    entry e7 = {Int, { .int_cont = 4}};
    entry e8 = {Str, { .str_cont = "Dean"}};
    entry data[] = {e1, e2, e3, e4, e5, e6, e7, e8};
    
    // two columns, student ID and student Name
    struct attribute_list snd = {"Name", Str, NULL};
    struct attribute_list schema = {"ID", Int, &snd};
    // the primary key is just the ID column
    struct attribute_list primary = {"ID", Int, NULL};
    // index attrs
    struct index_attributes attrs = {&schema, &primary};
    
    Relation_T tree = create_relation(data, 4, &attrs);
    
    // first cursor
    BtreeCursor_T bc1 = (BtreeCursor_T) btree_mtable.create_cursor(tree);
    
    // second cursor
    BtreeCursor_T bc2 = (BtreeCursor_T) btree_mtable.create_cursor(tree);
    
    // move the first cursor once
    btree_mtable.move_to_next(bc1);
    // move the second cursor twice
    btree_mtable.move_to_next(bc2);
    btree_mtable.move_to_next(bc2);
    
    const entry* rec1 = (const entry*) btree_mtable.get_record(bc1);
    const entry* rec2 = (const entry*) btree_mtable.get_record(bc2);
    
    size_t id1 = ((*rec1).cont).int_cont;
    char* name1 = (*(rec1 + 1)).cont.str_cont;
    size_t id2 = ((*rec2).cont).int_cont;
    char* name2 = (*(rec2 + 1)).cont.str_cont;
    
    printf("ID: %d, Name: %s \n", (int) id1, name1);
    printf("ID: %d, Name: %s \n", (int) id2, name2);
}
