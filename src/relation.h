/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   relation.h
 * Author: Oluwatosin V. Adewale
 * A Relation Library(RL)
 * Created on September 29, 2017, 4:39 PM
 */


#ifndef RELATION_H
#define RELATION_H

#include "util.h"
#include <stddef.h>

/* A Relation is a set of Records. */
typedef struct Relation* Relation_T;
/* A cursor operates on the relation. */
typedef struct Cursor* Cursor_T;


/* Create a new relation. 
 * Returns the relation on success. Returns NULL on failure. */
Relation_T RL_NewRelation(void);

/* Delete the relation. Free records with a pointer to a call back function.
 * freeRecord can be NULL. 
 * Future / TODO: Should somehow notify cursors. */
void RL_DeleteRelation(Relation_T relation, void (* freeRecord)(void *));

/* Create a cursor on the specified relation. On creation, cursor is invalid. 
 * i.e. It is not pointing to a record in the table.
 * Hence, certain operations cannot be carried out on it. */
Cursor_T RL_NewCursor(Relation_T relation);

/* Free the cursor. */
void RL_FreeCursor(Cursor_T cursor);

/* Is the cursor valid? Is the cursor pointing to a particular record. */
Bool RL_CursorIsValid(Cursor_T cursor);

/* Get the key of the entry the cursor is currently pointing at. */
unsigned long RL_GetKey(Cursor_T cursor);

/*************************
 * Relation  Operations  *
 *************************/

/* Put a key and its record into the relation. If the key already exists,
 * update record. Leave the cursor at key's position, if successful. Else, 
 * the cursor is invalid. Return TRUE on success; return FALSE on failure. 

 * TODO: PutRecord will be faster if Cursor is pointing near record.
 * TODO: what kind of failures can occur?
 */
Bool RL_PutRecord(Cursor_T cursor, unsigned long key, const void* record);

/* Move the cursor to the position of key in it's relation. 
 * Return True if key in Relation. Return False if Relation empty or key not in 
 * relation. Cursor will be Invalid if the Relation is empty.
 * Write to pRes, whether the key of the record at the current location of 
 * cursor is: less than (*pRes < 0), equal to (*pRes == 0), 
 * or greater than (*pRes > 0) the search key.
 * TODO: PutRecord will be faster if Cursor is pointing near record. */
Bool RL_MoveToRecord(Cursor_T cursor, unsigned long key, int* pRes);

/* Get the record from the location cursor is currently at. 
 * cursor must be valid.*/
const void* RL_GetRecord(Cursor_T cursor);

/* Delete key and its record from cursor's relation. Cursor is invalid. */
Bool RL_DeleteRecord(Cursor_T cursor, unsigned long key);

/* Move the cursor to the first record of it's relation. Return True. 
 * cursor is valid. If the relation is empty, return False. cursor is invalid.*/
Bool RL_MoveToFirstRecord(Cursor_T btCursor);

/* Go to the next record of cursor's relation. If there is a next record, 
 * return True. If no next record, return False. cursor is at last record. */
Bool RL_MoveToNext(Cursor_T btCursor);

/* Go to the previous record of cursor's relation. If there is a previous 
 * record, return True. If no previous record, return False. 
 * cursor is at first record.*/
Bool RL_MoveToPrevious(Cursor_T btCursor);

/* Return True if the relation is empty. */
Bool RL_IsEmpty(Cursor_T btCursor);

/* Return the Number of Records in the Relation */
size_t RL_NumRecords(Cursor_T btCursor);

void RL_PrintTree(Relation_T relation);


#endif /* RELATION_H */

