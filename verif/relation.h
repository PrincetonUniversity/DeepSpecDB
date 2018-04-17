/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   relation.h
 * Authors: Oluwatosin V. Adewale   &   Aurèle Barrière
 * A Relation Library(RL)
 * Created on September 29, 2017, 4:39 PM
 */


#ifndef RELATION_H
#define RELATION_H

/* #include "util.h" */
#include <stddef.h>

/* util.h */
typedef enum { False = 0 , True = 1} Bool;
enum {FANOUT = 15};
enum {MAX_TREE_DEPTH = 20};
size_t UTIL_Min(size_t a, size_t b);
Bool UTIL_StrEqual(const char* a, size_t lenA, const char* b, size_t lenB);

/* A Relation is a set of Records. */
typedef struct Relation* Relation_T;
/* A cursor operates on the relation. */
typedef struct Cursor* Cursor_T;
/* Keys of the BTrees */
typedef unsigned long Key;


/* Create a new relation. 
 * Returns the relation on success. Returns NULL on failure. */
Relation_T RL_NewRelation(void);

/* Delete the relation. Free records with a pointer to a call back function.
 * freeRecord can be NULL. 
 * Future/TODO: Should somehow notify cursors that relation has been deleted. */
void RL_DeleteRelation(Relation_T relation, void (* freeRecord)(void *));

/* Create a cursor on the specified relation. On creation, cursor is invalid. 
 * i.e. It is not pointing to a record in the table.
 * Hence, certain operations cannot be carried out on it. 
 * Returns cursor on success. On failure, returns NULL. */
Cursor_T RL_NewCursor(Relation_T relation);

/* Free the cursor. */
void RL_FreeCursor(Cursor_T cursor);

/* The cursor is invalid if it points after the biggest key. */
Bool RL_CursorIsValid(Cursor_T cursor);

/* Get the key of the entry the cursor is currently pointing at. */
Key RL_GetKey(Cursor_T cursor);

/*************************
 * Relation  Operations  *
 *************************/

/* Put a key and its record into the relation. If the key already exists,
 * update record. Leave the cursor at next key's position. If no such next key
 * exists, return False, and the cursor is invalid. Otherwise, cursor is valid. */
void RL_PutRecord(Cursor_T cursor, Key key, const void* record);

/* Move the cursor to the position of key in it's relation. 
 * Return True if key in Relation. Return False if Relation empty or key not in 
 * relation. Cursor will be Invalid if the Relation is empty. */
Bool RL_MoveToKey(Cursor_T cursor, Key key);

/* Get the record from the location cursor is currently at. 
 * cursor must be valid.*/
const void* RL_GetRecord(Cursor_T cursor);

/* Delete key and its record from cursor's relation. Cursor is invalid. */
Bool RL_DeleteRecord(Cursor_T cursor, Key key);

/* Move the cursor to the first record of it's relation. Return True. 
 * cursor is valid. If the relation is empty, return False. cursor is invalid.*/
Bool RL_MoveToFirst(Cursor_T btCursor);

/* Go to the next record of cursor's relation. */
void RL_MoveToNext(Cursor_T btCursor);

/* Calls MoveToNext, then checks if the cursor is valid */
Bool RL_MoveToNextValid(Cursor_T cursor);

/* Go to the previous record of cursor's relation. */
void RL_MoveToPrevious(Cursor_T btCursor);

/* Go to the previous record of cursor's relation. If there is a previous 
 * record, return True. If no previous record, return False. 
 * cursor is at first record.*/
Bool RL_MoveToPreviousNotFirst(Cursor_T cursor);

/* Return True if the relation is empty. */
Bool RL_IsEmpty(Cursor_T btCursor);

/* Return the Number of Records in the Relation */
size_t RL_NumRecords(Cursor_T btCursor);

void RL_PrintTree(Relation_T relation);

void RL_PrintCursor(Cursor_T cursor);

#endif /* RELATION_H */

