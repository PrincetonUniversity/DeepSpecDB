/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   btree_mem.c
 * Authors: Oluwatosin V. Adewale   &   Aurèle Barrière
 * 
 * Created on September 23, 2017, 7:31 PM
 */

#include "relation.h"
#include <assert.h>
/* #include <stdlib.h> */
#include <string.h>
#include <stdio.h>
#include <stddef.h>

/* extern void * malloc (size_t n); */
extern void free (void *);
extern void * malloc (unsigned int n);

/* Type declarations */
typedef struct BtNode BtNode;
typedef struct Entry Entry;
typedef union Child_or_Record Child_or_Record;
typedef struct Cursor Cursor;

/* Function Declarations */
static BtNode* createNewNode(Bool isLeaf, Bool First, Bool Last);

static void goToKey(Cursor_T cursor, Key key);

static Bool isNodeParent(BtNode * node, Key key);

static void putEntry(Cursor_T cursor, Entry * newEntry, size_t key);

static Bool deleteKeyRecord(BtNode* parentNode, BtNode* node, Key key,
        Entry* const oldEntryFromChild, Cursor* cursor, Relation_T relation, 
        const int level);

static Bool handleDeleteOfEntry(BtNode* parentNode, BtNode* node, 
        Entry* const oldEntryFromChild, Cursor* cursor,
        Relation_T relation, const int level);

static void redistributeOrMerge(BtNode* leftNode, BtNode* rightNode,
        Entry* const parentEntry, Bool isLeaf,  Bool* wasMerged);

static int findChildIndex(BtNode* node, Key key);

static int findRecordIndex(BtNode* node, Key key);

static void moveToKey(BtNode* node, Key key, Cursor* cursor,
	const int level);

static void moveToNext(Cursor_T cursor);

static void moveToFirst(BtNode* node, Cursor* cursor, int level);

static void moveToLast(BtNode* node, Cursor* cursor, int level);

static void handleDeleteBtree(BtNode* node, void (* freeRecord)(void *));

static void ASSERT_NODE_INVARIANT(BtNode* node, Relation_T relation);

static void printTree(BtNode* node, int level);

static void printCursor(Cursor_T cursor);

/* Surely Malloc */
extern void exit(int code);

void *surely_malloc (unsigned int n) {
  void *p = malloc(n);
  if (!p) exit(1);
  return p;
}

/**********************************
 * Type Definitions               *
 **********************************/

/* A relation is implemented using a B-tree datastructure.
 * 
 * A B-tree is a self-balancing tree datastructure with efficient insertion, 
 * deletion and search. Because of their efficiency and high fan-out it is good 
 * for indexing data in secondary storage (files). Because of their high
 * fanout, B-trees have a small height (the distance from the root to the 
 * leaves is small). Btree is actually a B+ tree where records are stored in the
 * leaves and not in internal nodes. */
typedef struct Relation {
    /* Root node of btree */
    struct BtNode* root;
    size_t numRecords;
    int depth;
} Relation;

/* Each entry in a btree node has a key. 
 * Entries in the leaf have an associated record. */
union Child_or_Record {
    /* Key of entry */
    BtNode* child;
    /* Record in entry, if entry is in leaf node */
    const void* record;
};

struct Entry {
    Key key;
    Child_or_Record ptr;
};

/* B-trees consist of nodes.
 * Each node of a btree has keys and pointers to its children (interior nodes) 
 * or records(leaf nodes). */
struct BtNode {
    /* Is this a leaf?*/
    Bool isLeaf;
    /* Is this the first Leaf */
    Bool First;
    /* Is this the last Leaf */
    Bool Last;
    /* Current number of keys in the node */
    int numKeys;
    /* Ptr to first child */
    BtNode* ptr0;
    /* Array of entries in the Node. An entry consists of a key and a pointer.
     * The pointer is either a pointer to a child or a pointer to a record. 
     * A BtNode contains at most FANOUT keys and FANOUT + 1 children 
     * (including ptr0) records. */
    Entry entries[FANOUT];
};

struct Cursor {
    /* The relation that this cursor points to*/
    Relation* relation;
    /*What level is the cursor at*/
    int level;
    /* Arrays of index at ancestor node[i] containing child pointer to next 
     * ancestor node [i + 1]. */
    /* indices range from -1 to NUM_KEYS - 1. At leaf, index is entryIdx */
    int ancestorsIdx[MAX_TREE_DEPTH];
    /* Array of Current Nodes Ancestors*/
    BtNode* ancestors[MAX_TREE_DEPTH];
};

int entryIndex (Cursor_T cursor) {
  return cursor->ancestorsIdx[cursor->level];
}

BtNode* currNode (Cursor_T cursor) {
  return cursor->ancestors[cursor->level];
}

Bool isValid (Cursor_T cursor) {
  if (entryIndex(cursor) == currNode(cursor)->numKeys &&
      currNode(cursor)->Last == True) {
    return False;
  } else {
    return True;
  }
}

Bool isFirst (Cursor_T cursor) {
  if (entryIndex(cursor) == 0 &&
      currNode(cursor)->First == True) {
    return True;
  } else {
    return False;
  }
}

/**********************************
 * Function Definitions           *
 **********************************/

Relation_T RL_NewRelation(void) {
    BtNode* pRootNode;
    Relation* pNewRelation;

    pRootNode = createNewNode(True, True, True);
    if (pRootNode == NULL) {
        return NULL;
    }

    pNewRelation = (Relation*) surely_malloc(sizeof (Relation));
    if (pNewRelation == NULL) {
        free(pRootNode);
        return NULL;
    }

    pNewRelation->root = pRootNode;
    pNewRelation->numRecords = 0;
    pNewRelation->depth = 0;
    
    return pNewRelation;
}

/* TODO: do this later. */
void RL_DeleteRelation(Relation_T relation, void (* freeRecord)(void *)){
    assert(relation != NULL);
    handleDeleteBtree(relation->root, freeRecord);
}

Cursor_T RL_NewCursor(Relation_T relation) {
    Cursor* cursor;
    size_t i;

    assert(relation != NULL);

    cursor = (Cursor*) surely_malloc(sizeof (Cursor));
    if (cursor == NULL) {
        return NULL;
    }

    cursor->relation = relation;
    cursor->level = -1;
    moveToFirst(relation->root, cursor, 0);
    
    return cursor;
}

void RL_FreeCursor(Cursor_T btCursor) {
    free(btCursor);
}

Bool RL_CursorIsValid(Cursor_T cursor) {
    assert(cursor != NULL);
    return isValid(cursor);
}

void RL_PutRecord(Cursor_T cursor, Key key, const void* record) {
    Entry newEntry;
    assert(cursor != NULL);

    newEntry.ptr.record = record;
    newEntry.key = key;

    goToKey(cursor,key);
    putEntry(cursor, &newEntry, key);
    RL_MoveToNext(cursor);
    
    return;
}

/* Returns true if we know for sure that currNode (Intern Node) is a parent of the key
 * Returns False if we can't know */
static Bool isNodeParent (BtNode * node, Key key) {
  int idx;
  Key lowest, highest;
  if (node->isLeaf == True) {	/* Leaf node */

    if (node->numKeys == 0) {	/* root is always a parent */
      return True; }
    
     /* we check if the cursor should point to the same leaf node */
    lowest = node->entries[0].key;
    highest = node->entries[node->numKeys - 1].key;

    if ((key >= lowest || node->First == True) &&
	(key <= highest || node->Last == True)) {
      return True;
    }
    
    return False;
    
  } else { /* Intern node */
    idx = findChildIndex(node, key);
    if (idx == -1 || idx == node->numKeys -1) {
      return False;
    }
    return True;
  }

}

/* Go up in the cursor until we are sure to be in a parent node of the key */
void AscendToParent (Cursor_T cursor, Key key) {

  if (cursor->level == 0) {/* if we are at the root */
    return;
  }

  if (isNodeParent(currNode(cursor), key) == True) {
    return;
  }
  else {
    cursor->level --;
    AscendToParent(cursor, key);
  }
}

const void* RL_GetRecord(Cursor_T cursor) {
  assert(isValid(cursor) == True);

  /* if the cursor is at the last position of a leaf node, we move to the equivalent position */
  if (entryIndex(cursor) == currNode(cursor)->numKeys) {
    moveToNext(cursor);
  }
  
  return (currNode(cursor)->entries)[entryIndex(cursor)].ptr.record;
}

Key RL_GetKey(Cursor_T cursor) {
    assert(isValid(cursor)==True);

    /* if the cursor is at the last position of a leaf node, we move to the equivalent position */
    if (entryIndex(cursor) == currNode(cursor)->numKeys) {
      moveToNext(cursor);
    }
    
    return currNode(cursor)->entries[entryIndex(cursor)].key;
}

void goToKey(Cursor_T cursor, Key key) {
  assert(cursor != NULL);
  AscendToParent(cursor, key);
  moveToKey(currNode(cursor), key, cursor, cursor->level);
}

Bool RL_MoveToKey(Cursor_T cursor, Key key) {
    goToKey(cursor,key);
    
    if (isValid(cursor) == False) {
      return False;
    }
    if (RL_GetKey(cursor) == key) {
      return True;
    } else {
      return False;
    } 
}

Bool RL_DeleteRecord(Cursor_T cursor, Key key) {
    /* Bool success; */
    /* Entry oldEntryFromChild; */
    /* assert(cursor != NULL); */

    /* oldEntryFromChild.ptr.child = NULL; */

    /* success = deleteKeyRecord(NULL, cursor->relation->root, key, */
    /*         &oldEntryFromChild, cursor, cursor->relation, 0); */

    /* /\*TODO: move cursor->isValid = True, etc into return statement here. *\/ */
    /* if (success) { */
    /*     isValid(cursor) = False; */
    /*     cursor->relation->numRecords--; */
    /*     return success; */
    /* } */

    /* cursor->isValid = False; */
    return False;
}

Bool RL_MoveToFirst(Cursor_T cursor) {  
    assert(cursor);

    cursor->level = -1;
    moveToFirst(cursor->relation->root, cursor, 0);
    return isValid(cursor);
}


int lastpointer(BtNode * node) {
  if (node->isLeaf == True) {
    return node->numKeys;
  } else {
    return node->numKeys-1;
  }
}

int firstpointer(BtNode * node) {
  if (node->isLeaf == True) {
    return 0;
  } else {
    return -1;
  }
}

/* Moves the cursor to the next position */
static void moveToNext(Cursor_T cursor) {
  /* If past last element, stay past element and return. */
  if(isValid(cursor) == False) {
    return;
  }
        
  /* While ancestor pointer is last pointer, ascend. */
  while(cursor->level > 0 && entryIndex(cursor) == lastpointer(currNode(cursor))) {
        cursor->level--;
  }

  /* Increase index */
  cursor->ancestorsIdx[cursor->level] ++;
  
  if(currNode(cursor)->isLeaf == True) {
    return;
  }

  moveToFirst(currNode(cursor)->entries[entryIndex(cursor)].ptr.child, cursor, cursor->level+1);
  return;
}

static void moveToPrev(Cursor_T cursor) {
  /* If first cursor, stay first cursor and return */
  if(isFirst(cursor) == True) {
    return;
  }

  /* While ancestor pointer is first pointer, ascend */
  while(cursor->level > 0 && entryIndex(cursor) == firstpointer(currNode(cursor))) {
    cursor->level--;
  }

  /* Decrease Index */
  cursor->ancestorsIdx[cursor->level] --;

  if(currNode(cursor)->isLeaf == True) {
    return;
  }

  moveToLast(currNode(cursor)->entries[entryIndex(cursor)].ptr.child, cursor, cursor->level+1);
  return;
}

void RL_MoveToNext(Cursor_T cursor) {
  
  /* if we are at the end of a leaf, we must move to next position twice */
  if (entryIndex(cursor) == currNode(cursor)->numKeys) {
    moveToNext(cursor);
  }
  moveToNext(cursor);
  return;
 }

void RL_MoveToPrevious(Cursor_T cursor) {
  if (entryIndex(cursor) == 0) {
    moveToPrev(cursor);
  }
  moveToPrev(cursor);
  return;
}

Bool RL_MoveToNextValid(Cursor_T cursor) {
  RL_MoveToNext(cursor);
  return RL_CursorIsValid(cursor);
}

Bool RL_MoveToPreviousNotFirst(Cursor_T cursor) {
  RL_MoveToPrevious(cursor);
  if (isFirst(cursor) == True) {
    return False;
  } else {
    return True;
  }
}

Bool RL_IsEmpty(Cursor_T cursor) {
    assert(cursor != NULL);
    
    if (cursor->relation->root->numKeys == 0) {
        return True;
    }
    return False;
}

size_t RL_NumRecords(Cursor_T cursor) {
    assert(cursor != NULL);
    
    return cursor->relation->numRecords;
    
}

void RL_PrintTree(Relation_T relation) {

    assert(relation != NULL);
    assert(relation->root != NULL);
    
    printTree(relation->root, 0);
    
}

void RL_PrintCursor(Cursor_T cursor) {

  assert (cursor != NULL);

  printCursor(cursor);

}


static BtNode* createNewNode(Bool isLeaf, Bool First, Bool Last) {
    BtNode* newNode;

    newNode = (BtNode*) surely_malloc(sizeof (BtNode));
    if (newNode == NULL) {
        return NULL;
    }

    newNode->numKeys = 0;
    newNode->isLeaf = isLeaf;
    newNode->First = First;
    newNode->Last = Last;
    newNode->ptr0 = NULL;

    return newNode;
}

/* Insert entry and split node. Return a new entry to be inserted in parent, inside entry. 
 * If this is a leaf node, new entry's key is a copy of the first key to
 * in the second node. Otherwise, new entry's key is the key between the last key
 * of the first node and the first key of the second node. In both cases ptr is 
 * a ptr to the newly created node. */
static void splitnode(BtNode* node, Entry* entry, Bool isLeaf) {
  Entry allEntries[FANOUT + 1];
  BtNode* newNode;
  int i, tgtIdx;

  /* Find first key that is greater than search key. Search key goes before this key. */
  tgtIdx = findRecordIndex(node, entry->key);

  /* Create the new node. */
  newNode = createNewNode(isLeaf,False,node->Last);
  assert(newNode);
  node->Last = False; /* split node can't be Last Leaf */
    
    if(node->isLeaf == True) {	/* leaf node */
      /* copy all entries into allentries */
      for(i = 0; i < tgtIdx; i++) {
	allEntries[i].key = node->entries[i].key;
	allEntries[i].ptr.record = node->entries[i].ptr.record;
      }
    
      allEntries[tgtIdx].key = entry->key;
      allEntries[tgtIdx].ptr.record = entry->ptr.record;
    
      for(i = tgtIdx; i < FANOUT; i++) {
	allEntries[i+1].key = node->entries[i].key;
	allEntries[i+1].ptr.record = node->entries[i].ptr.record;
      }

      /* if the new entry came before an entry in the first node, 
       * then we need to update those entries in the first node.*/
      node->numKeys = MIDDLE;
      
      if(tgtIdx < MIDDLE) {
        for(i = tgtIdx; i < MIDDLE; i++) {
	  node->entries[i].key = allEntries[i].key;
	  node->entries[i].ptr.record = allEntries[i].ptr.record;
        }
      }

      /*Copy entries to second node.*/
      for (i = MIDDLE; i < FANOUT + 1; i++) {
        newNode->entries[i-MIDDLE].key = allEntries[i].key;
	newNode->entries[i-MIDDLE].ptr.record = allEntries[i].ptr.record;
      }
      newNode->numKeys = FANOUT + 1 - MIDDLE;

      entry->key = allEntries[MIDDLE].key;
      entry->ptr.child = newNode;
      return;

    } else {			/* intern node */
      /* copy all entries into allentries */
      for(i = 0; i < tgtIdx; i++) {
	allEntries[i].key = node->entries[i].key;
	allEntries[i].ptr.child = node->entries[i].ptr.child;
      }
    
      allEntries[tgtIdx].key = entry->key;
      allEntries[tgtIdx].ptr.child = entry->ptr.child;
      
      for(i = tgtIdx; i < FANOUT; i++) {
	allEntries[i+1].key = node->entries[i].key;
	allEntries[i+1].ptr.child = node->entries[i].ptr.child;
      }

      /* if the new entry came before an entry in the first node, 
       * then we need to update those entries in the first node.*/
      if(tgtIdx < MIDDLE) {
        for(i = tgtIdx; i < MIDDLE; i++) {
	  node->entries[i].key = allEntries[i].key;
	  node->entries[i].ptr.child = allEntries[i].ptr.child;
        }
      }
      node->numKeys = MIDDLE;

      /*Copy entries to second node. Don't copy the middle key */
      for (i = MIDDLE+1; i < FANOUT + 1; i++) {
        newNode->entries[i-(MIDDLE+1)].key = allEntries[i].key;
	newNode->entries[i-(MIDDLE+1)].ptr.child = allEntries[i].ptr.child;
      }
      newNode->numKeys = FANOUT - MIDDLE;

      entry->key = allEntries[MIDDLE].key;
      entry->ptr.child = newNode;
      newNode->ptr0 = allEntries[MIDDLE].ptr.child;
      return;

    }
}
  

/* Insert entry and split node. Return a new entry to be inserted in parent, inside entry. 
 * If this is a leaf node, new entry's key is a copy of the first key to
 * in the second node. Otherwise, new entry's key is the key between the last key
 * of the first node and the first key of the second node. In both cases ptr is 
 * a ptr to the newly created node. */
/* static void splitnode(BtNode* node, Entry* entry, Bool isLeaf) { */
/*     Entry allEntries[FANOUT + 1]; */
/*     BtNode* newNode; */
/*     int i, j, tgtIdx, startIdx; */
/*     Bool inserted; */
    
/*     /\* Find first key that is greater than search key. Search key goes before this key. *\/ */
/*     tgtIdx = findRecordIndex(node, entry->key); */
    
/*     j = 0; */
/*     inserted = False; */
    
/*     Build list of all entries. */
/*     for(i = 0; i < FANOUT + 1; i++) { */
/*         if(inserted == False && j == tgtIdx) { */
/*             allEntries[i] = *entry; */
/*             inserted = True; */
/*             continue; */
/*         } */
/*         allEntries[i] = node->entries[j]; */
/*         j++; */
/*     } */

/*     /\* if the new entry came before an entry in the first node,  */
/*      * then we need to update those entries in the first node.*\/ */
/*     if(tgtIdx < MIDDLE) { */
/*         for(i = tgtIdx; i < MIDDLE; i++) { */
/*             node->entries[i] = allEntries[i];    */
/*         } */
/*     } */
/*     node->numKeys = MIDDLE; */
    
/*     /\* Create the new node. *\/ */
/*     newNode = createNewNode(isLeaf,False,node->Last); */
/*     assert(newNode); */
/*     node->Last = False; /\* split node can't be Last Leaf *\/ */
    
/*     /\* Select appropriate idx to start copying. *\/ */
/*     if(isLeaf) { */
/*         startIdx = MIDDLE; */
/*     } else { */
/*         /\* We push up MIDDLE node, so don't copy it into snd node. *\/ */
/*         startIdx = MIDDLE + 1; */
/*     } */
    
/*     /\*Copy entries to second node.*\/ */
/*     j = 0; */
/*     for (i = startIdx; i < FANOUT + 1; i++) { */
/*         newNode->entries[j] = allEntries[i]; */
/*         j++; */
/*     } */
/*     newNode->numKeys = FANOUT + 1 - startIdx; */
    
/*     /\* If this is a leaf, copy up first entry on second node. *\/ */
/*     if(isLeaf) { */
/*         entry->key = allEntries[startIdx].key; */
/*         entry->ptr.child = newNode; */
/*     } */
/*     /\* Else we are pushing up entry before second node. *\/ */
/*     else { */
/*         entry->key = allEntries[startIdx - 1].key; */
/*         entry->ptr.child = newNode; */
/* 	newNode->ptr0 = allEntries[startIdx - 1].ptr.child; */
/*     } */

/*     return; */
/* } */
  
/* Inserting a new entry at a position given by the cursor.
 * The cursor should point to the correct location: this function should only be called after goToKey
 * If the key already exists in the relation, its record will be updated. */
static void putEntry(Cursor_T cursor, Entry * newEntry, size_t key) {
  if (cursor->level==-1) {
    /* the root has been split, and newEntry should be the only entry in the new root */
    BtNode* currNode = createNewNode(False, True, True);
    assert(currNode);

    currNode->ptr0 = cursor->relation->root;
    currNode->numKeys = 1;
    currNode->entries[0].key = newEntry->key;
    currNode->entries[0].ptr.child = newEntry->ptr.child;

    cursor->relation->root = currNode;
    cursor->relation->depth ++;
    cursor->relation->numRecords ++;
    cursor->ancestors[0] = currNode;

    /* we need to update the cursor for the original inserted key */
    moveToKey(currNode, key, cursor, 0);
    
    return;
  }

  if (currNode(cursor)->isLeaf) { /* current node is a leaf node */
    if (entryIndex(cursor) < currNode(cursor)->numKeys &&
	currNode(cursor)->entries[entryIndex(cursor)].key == newEntry->key) {
      /* the key already exists in the cursor */
      currNode(cursor)->entries[entryIndex(cursor)].ptr = newEntry->ptr;
      return;
    }
    else {
      /* the key does not exist and must be inserted */

      if (currNode(cursor)->numKeys < FANOUT) {
	const int tgtIdx = entryIndex(cursor);
	
	int i;
	/* Move all entries to the right of tgtIdx one to the right*/
	for (i=currNode(cursor)->numKeys; i > tgtIdx; i--) {
	  currNode(cursor)->entries[i] = currNode(cursor)->entries[i-1];
	}
	currNode(cursor)->entries[tgtIdx] = *newEntry;
	currNode(cursor)->numKeys++;
	cursor->relation->numRecords++;
	return;
      }
      else {
	/* the leaf node must be split */
	splitnode(currNode(cursor), newEntry, True);
	cursor->level--;
	/* recursive call to insert the newEntry from splitnode a level above */
	putEntry(cursor, newEntry, key);
      }
    }
  }
  else { /* current node is an intern node */
    if (currNode(cursor)->numKeys < FANOUT) {
      /* the current intern node has enough space to insert a new entry */
      const int tgtIdx = entryIndex(cursor) +1;
      /* this is a correct index because there is enough space in the node */
      
      int i;
      /* Move all entries to the right of tgtIdx one to the right*/
      for (i=currNode(cursor)->numKeys; i > tgtIdx; i--) {
	currNode(cursor)->entries[i] = currNode(cursor)->entries[i-1];
      }
      currNode(cursor)->entries[tgtIdx] = *newEntry;
      currNode(cursor)->numKeys++;
      cursor->relation->numRecords++; /* is that the good place to put it? */

      /* update the cursor to make it point to the inserted key */
      moveToKey(currNode(cursor), key, cursor, cursor->level);

      return;
    }
    else {
      /* the node must be split */
      splitnode(currNode(cursor), newEntry, False);
      cursor->level--;
      /* recursive call to insert the newEntry from splitnode a level above */
      putEntry(cursor, newEntry, key);
      
    }
  }
}

/* Algorithm from page 262 of Database Management Systems Second Edition. 
 * Delete key and record from the appropriate leaf in nodePtr. Use parentNode
 * to get siblings if redistribution or merging of children nodes is necessary.
 * Use oldEntryFromChild to detect if a merge occurred in the current node's 
 * child. It is a constant pointer to an entry. It should be filled in with the 
 * correct value. It contains a key and its pointer. It is the entry in the 
 * current node that points into the (right) child node merged into its (left) 
 * sibling node.
 *  
 * Return True on success. Return False on failure.
 * TODO: Ancestor tracking code.
 */
static Bool deleteKeyRecord(BtNode* parentNode, BtNode* node, Key key,
        Entry* const oldEntryFromChild, Cursor* cursor, Relation_T relation, 
        const int level){
    
    /* Bool success; */
    /* int i; */
    
    /* /\* Index of pointer to child tree containing key to be deleted *\/ */
    /* int childTreePtrIdx; */
    
    /* assert(node != NULL); */
    /* assert(cursor != NULL); */
    /* /\* Container to store new entry should never be NULL.*\/ */
    /* assert(oldEntryFromChild != NULL); */
    /* ASSERT_NODE_INVARIANT(node, relation); */
        
    /* if (node->isLeaf == False) { */
    /*     BtNode* childNode; */
        
    /*     /\* Get index of child node that contains. *\/ */
    /*     childTreePtrIdx = findChildIndex(node->entries, key, node->numKeys); */
        
    /*     /\* Get child node*\/ */
    /*     if (childTreePtrIdx == -1) { */
    /*         childNode = node->ptr0; */
    /*     } else { */
    /*         childNode = node->entries[childTreePtrIdx].ptr.child; */
    /*     } */
                
    /*     /\* Recursively delete *\/ */
    /*     success = deleteKeyRecord(node, childNode, key,  */
    /*             oldEntryFromChild, cursor, relation, level+1); */
                
    /*     /\* if delete failed, return that delete failed *\/ */
    /*     if (success == False) { */
    /*         return False; */
    /*     }            */
        
    /*     /\* else if successful and no merges, return success.*\/ */
    /*     if (oldEntryFromChild->ptr.child == NULL) { */
    /*         return success; */
    /*     } */
        
    /*     /\* Handle case where entry / key has to be deleted in node because */
    /*      * children were merged. *\/ */
    /*     return handleDeleteOfEntry(parentNode, node,  */
    /*             oldEntryFromChild, cursor, relation, level);     */
        
    /* }  */
    /* /\* Handle delete in child. *\/ */
    /* else { */
    /*     for (i = 0; i < node->numKeys; i++) { */
    /*         if (node->entries[i].key == key) { */
    /*             *oldEntryFromChild = node->entries[i]; */
    /*             return handleDeleteOfEntry(parentNode, node, oldEntryFromChild, */
    /*                     cursor, relation, level); */
    /*         } */
    /*     } */
    /*     return False; */
    /* } */
  return False;
}


/* Code to handle deletion of entry in non-leaf or leaf node when children 
 * nodes have been merged. 
 * TODO: ancestor tracking code.*/
static Bool handleDeleteOfEntry(BtNode* parentNode, BtNode* node, 
        Entry* const oldEntryFromChild, Cursor* cursor,
        Relation_T relation, const int level) {

    /* int i, idx; */
    /* Bool found = False, wasMerged = False; */
    /* BtNode* leftSibling = NULL;  */
    /* BtNode* rightSibling = NULL; */

    /* assert(node != NULL); */
    /* assert(cursor != NULL); */
    /* assert(oldEntryFromChild != NULL); */
    
    /* /\* find the entry that matches oldEntry.*\/ */
    /* for (i = 0; i < node->numKeys; i++) { */
    /*     /\* if these entries match *\/ */
    /*     if ((oldEntryFromChild->key == node->entries[i].key) && */
    /*             (oldEntryFromChild->ptr.child == node->entries[i].ptr.child)) { */
    /*         idx = i; */
    /*         found = True; */
    /*         break; */
    /*     }  */
    /* } */
    
    /* assert(found == True); */
    
    /* /\* if found, delete the entry *\/ */
    /* for(i = idx; i < node->numKeys - 1; i++) { */
    /*     node->entries[i] = node->entries[i+1]; */
    /* } */
    /* node->numKeys--; */
    
    /* /\* MAKE SURE ENTRY IS NOT ROOT. Root is allowed to have less than FANOUT / 2 */
    /*  * entries. *\/ */
    
    /* /\* If this is root. *\/ */
    /* if(relation->root == node) { */
    /*     /\* if the root is now empty. and this is not a leaf. *\/ */
    /*     if (node->numKeys == 0 && node->isLeaf == False) { */
    /*         /\* Set the new root. *\/ */
    /*         relation->root = node->ptr0; */
    /*         /\* Free the old root. *\/ */
    /*         free(node); */
    /*     } */
    /*     /\* Otherwise if this is a leaf, leave leaf node as root for insertion.*\/ */
        
    /*     /\* set oldEntryFromChild('s ptr) to NULL. *\/ */
    /*     oldEntryFromChild->ptr.child = NULL; */
    /*     return True;   */
    /* } */
    
    
    /* /\* if this not the root and the node had enough entries, set old entries  */
    /*  * pointer to null to indicate that there is no node deleted at this level. */
    /*  *\/ */
    /* if (node->numKeys >= FANOUT/2) { */
    /*     oldEntryFromChild->ptr.child = NULL; */
    /*     return True; */
    /* } */
    
    /* /\* Else redistribute or merge. *\/ */
    
    /* found = False; */
    /* for(i=0; i < parentNode->numKeys; i++) { */
    /*     if(parentNode->entries[i].ptr.child == node) { */
    /*         found = True; */
    /*         idx = i; */
    /*         break; */
    /*     } */
    /* } */
    
    /* if (parentNode->ptr0 != node) { */
    /*     assert(found == True); */
    /* } */
    
    /* /\* First get sibling(s). Non-root nodes must have at least one sibling. *\/ */
    /* /\* if node is leftmost or rightmost child, only one sibling *\/ */
    /* if(parentNode->ptr0 == node) { */
    /*     rightSibling = parentNode->entries[0].ptr.child; */
    /* }  */
    /* else if (parentNode->entries[parentNode->numKeys - 1].ptr.child == node) { */
    /*     leftSibling = parentNode->entries[parentNode->numKeys - 2].ptr.child; */
    /* }  */
    /* /\* otherwise, one or two siblings*\/ */
    /* else { */
        
    /*     /\* Get left sibling. *\/ */
    /*     if(idx == 0){ */
    /*         leftSibling = parentNode->ptr0; */
    /*     } else { */
    /*         leftSibling = parentNode->entries[idx - 1].ptr.child; */
    /*     } */
        
    /*     /\* Get right sibling. *\/ */
    /*     if(idx + 1 < parentNode->numKeys) { */
    /*         rightSibling = parentNode->entries[idx + 1].ptr.child; */
    /*     } */
    /* } */
    
    /* /\* There must be a sibling as this is not the root. *\/ */
    /* assert(leftSibling != NULL || rightSibling != NULL); */
    
    /* /\* Now attempt redistribute or merge using node and smallest sibling. We use */
    /*  * the smallest sibling as this increases the chance of redistributions  */
    /*  * which is more favorable as redistributions do not propagate*\/ */
    
    /* if(rightSibling == NULL) { */
    /*     rightSibling = node; */
    /* } else if (leftSibling == NULL) { */
    /*     leftSibling = node; */
    /* } else if (leftSibling->numKeys <= rightSibling->numKeys) { */
    /*     rightSibling = node; */
    /* } else { */
    /*     leftSibling = node; */
    /* } */
    
    /* /\* Find splitting parent entry. *\/ */
    /* found = False; */
    /* for(idx = 0; idx < parentNode->numKeys; idx++) { */
    /*     if(parentNode->entries[idx].ptr.child == rightSibling) { */
    /*         found = True; */
    /*         break; */
    /*     } */
    /* } */
    
    /* assert(found == True); */
    
    /* redistributeOrMerge(leftSibling, rightSibling, &(parentNode->entries[idx]),  */
    /*                     leftSibling->isLeaf, &wasMerged); */
    
    /* /\* If nodes weren't merged, set oldEntryFromChild to false, return True*\/ */
    /* if(wasMerged == False){ */
    /*     oldEntryFromChild->ptr.child = NULL; */
    /*     return True; */
    /* } */
    /* /\* Else splitting entry has to be deleted in parent. And right node */
    /*  * should be freed as its entries have been merged into left node. *\/ */
    /* *oldEntryFromChild = parentNode->entries[idx]; */
    /* free(rightSibling); */
    /* return True; */
  return False;
}


/* Redistributes entries between siblings if one sibling has 
 * enough entries to spare. If this is not possible, it merges both siblings.
 * Both siblings must have at least FANOUT / 2 entries. If the nodes were 
 * merged, set wasMerged to True. Otherwise, set wasMerged to False. 
 * isLeaf is True if the left and right nodes are leaf nodes, otherwise the 
 * nodes are non-leaf nodes. parentEntry is a pointer to the entry splitting both nodes in 
 * the parent node. Algorithm from Database Management Systems Textbook. 
 * 
 * TODO: redistribution code can be optimized to copy right amount at once 
 * instead of using while loops.
 */
static void redistributeOrMerge(BtNode* leftNode, BtNode* rightNode,
        Entry* const parentEntry, Bool isLeaf,  Bool* wasMerged) {
    /* int totalKeys = leftNode->numKeys + rightNode->numKeys; */
    /* int i; */
    
    /* assert(leftNode != NULL); */
    /* assert(rightNode != NULL); */
    /* /\* Assert there are enough keys for redistribution or a merge.*\/ */
    /* assert(totalKeys >= FANOUT / 2); */
    
    /* /\* Algorithm for redistributing or merging in non-Leaf. *\/ */
    /* if (isLeaf == False) { */
    /*     /\* If the total number of keys is greater than FANOUT, we can and  */
    /*      * should redistribute. *\/ */
    /*     if(totalKeys >= FANOUT) { */
    /*         /\* if the left node has less keys, redistribute from right to left. *\/ */
    /*         if (leftNode->numKeys < rightNode->numKeys) { */
    /*             /\* while the left node is smaller than the right node, redistribute*\/ */
    /*             while(leftNode->numKeys < rightNode->numKeys){ */
    /*                 /\* copy parentEntry key into new space on left node*\/ */
    /*                 leftNode->entries[leftNode->numKeys].key = parentEntry->key; */
    /*                 /\* copy right node's key into parentEntry key*\/ */
    /*                 parentEntry->key = rightNode->entries[0].key; */

    /*                 /\* Move Pointers appropriately. *\/ */
    /*                 leftNode->entries[leftNode->numKeys].ptr.child = rightNode->ptr0; */
    /*                 rightNode->ptr0 = rightNode->entries[0].ptr.child; */
                    
    /*                 /\* Delete first entry*\/ */
    /*                 for (i = 1; i < rightNode->numKeys; i++) { */
    /*                     rightNode->entries[i-1] = rightNode->entries[i]; */
    /*                 } */
    /*                 leftNode->numKeys++; */
    /*                 rightNode->numKeys--; */
    /*             } */
    /*         } */
    /*         /\* else right node has less keys, so redistribute from left to right. *\/ */
    /*         else { */
    /*             /\* while the right node is smaller than the left node, redistribute*\/ */
    /*             while(rightNode->numKeys < leftNode->numKeys){ */
    /*                 /\* make space for a new entry on the right node *\/ */
    /*                 for (i = rightNode->numKeys; i > 0; i--) { */
    /*                     rightNode->entries[i] = rightNode->entries[i-1]; */
    /*                 } */

    /*                 /\* copy parentEntry key into new space on right node*\/ */
    /*                 rightNode->entries[0].key = parentEntry->key; */
    /*                 /\* copy left node's last key into parentEntry key*\/ */
    /*                 parentEntry->key = leftNode->entries[leftNode->numKeys-1].key; */
                    
    /*                 /\* Move Pointers appropriately. *\/ */
    /*                 rightNode->entries[0].ptr.child = rightNode->ptr0; */
    /*                 rightNode->ptr0 = leftNode->entries[leftNode->numKeys-1].ptr.child; */
                    

    /*                 leftNode->numKeys--; */
    /*                 rightNode->numKeys++; */
    /*             } */
    /*         } */

    /*         *wasMerged = False; */
    /*     } */
    /*     /\* else if not enough total keys for two nodes, merge both nodes. *\/ */
    /*     else { */
    /*         /\* First copy parent splitting key and left most pointer in right node */
    /*          * as new entry in left node. *\/ */
    /*         leftNode->entries[leftNode->numKeys].key = parentEntry->key; */
    /*         leftNode->entries[leftNode->numKeys].ptr.child = rightNode->ptr0; */
    /*         leftNode->numKeys++; */

    /*         /\* Move all entries from right node and add them to left node. *\/ */
    /*         for(i = 0; i < rightNode->numKeys; i++) { */
    /*             leftNode->entries[leftNode->numKeys] = rightNode->entries[i]; */
    /*             leftNode->numKeys++; */
    /*         } */

    /*         *wasMerged = True; */
    /*     } */
    /* } */
    /* /\* Algorithm for redistributing or merging in leaf. *\/ */
    /* else { */
    /*     /\* If the total number of keys is greater than FANOUT, we can and  */
    /*      * should redistribute. *\/ */
    /*     if(totalKeys >= FANOUT) { */
    /*         /\* if the left node has less keys, redistribute from right to left. *\/ */
    /*         if (leftNode->numKeys < rightNode->numKeys) { */
    /*             /\* while the left node is smaller than the right node, redistribute*\/ */
    /*             while(leftNode->numKeys < rightNode->numKeys){ */
    /*                 /\* copy entry from the right node to the left node. *\/ */
    /*                 leftNode->entries[leftNode->numKeys] = rightNode->entries[0]; */
                   
    /*                 /\* Delete first entry*\/ */
    /*                 for (i = 1; i < rightNode->numKeys; i++) { */
    /*                     rightNode->entries[i-1] = rightNode->entries[i]; */
    /*                 } */
                    
    /*                 /\* Set new splitting key in parent. *\/ */
    /*                 parentEntry->key = rightNode->entries[0].key; */
                    
    /*                 leftNode->numKeys++; */
    /*                 rightNode->numKeys--; */
    /*             } */
    /*         } */
    /*         /\* else right node has less keys, so redistribute from left to right. *\/ */
    /*         else { */
    /*             /\* while the right node is smaller than the left node, redistribute*\/ */
    /*             while(rightNode->numKeys < leftNode->numKeys){ */
    /*                 /\* make space for a new entry on the right node *\/ */
    /*                 for (i = rightNode->numKeys; i > 0; i--) { */
    /*                     rightNode->entries[i] = rightNode->entries[i-1]; */
    /*                 } */
                    
    /*                 /\* copy entry from the left node to the right node. *\/ */
    /*                 rightNode->entries[0] = leftNode->entries[leftNode->numKeys-1]; */
                    
    /*                 /\* set new splitting key in parent. *\/ */
    /*                 parentEntry->key = rightNode->entries[0].key; */

    /*                 leftNode->numKeys--; */
    /*                 rightNode->numKeys++; */
    /*             } */
    /*         } */

    /*         *wasMerged = False; */
    /*     } */
    /*     /\* else if not enough total keys for two nodes, merge both nodes. *\/ */
    /*     else { */

    /*         /\* Move all entries from right node and add them to left node. *\/ */
    /*         for(i = 0; i < rightNode->numKeys; i++) { */
    /*             leftNode->entries[leftNode->numKeys] = rightNode->entries[i]; */
    /*             leftNode->numKeys++; */
    /*         } */

    /*         *wasMerged = True; */
    /*     } */
    /* } */
  return;    
}



/* Given an array of entries, find the index of the last entry whose key is
 * less than or equal to the search key. */
static int findChildIndex(BtNode* node, Key key) {
    int i = 0;
    assert(node->numKeys > 0);

    /* if key less than first element, return index of first*/
    if (key < node->entries[0].key) {
        return -1;
    }
    /* else see if key falls in between any two keys, return index of first key*/
    for (i = 0; i <= node->numKeys - 2; i++) {
      if (key >= node->entries[i].key && key < node->entries[i + 1].key) {
            return i;
      }
    }
    /* if key greater or equal to last element, return index of last element*/
    return node->numKeys - 1;
}

/* Given an array of entries, find the index of the first entry whose key is
 * greater than or equal to the search key. */
static int findRecordIndex(BtNode* node, Key key) {
  int i = 0;
  assert(node->entries != NULL);
  assert(node->numKeys >= 0);

  if (node->numKeys == 0) {
    return 0;
  }

  for (i = 0; i <= node->numKeys - 1; i++) {
    if (key <= node->entries[i].key) {
      return i;
    }
  }

  /* if the key is strictly greater than any key in the node */
  return node->numKeys;
}


/* move cursor to key in node. On finding key's record, return True and update cursor.
 * The function assumes that node is a parent of the key
 * If relation empty or key not in B+-tree, return False */
static void moveToKey(BtNode* node, Key key, Cursor* cursor, const int level) {
  cursor->ancestors[level] = node;
  cursor->level = level;
  
  if (node->isLeaf) {
    cursor->ancestorsIdx[level] = findRecordIndex(node, key);
    return;
    
  } else { /* intern node */
    int i;
    BtNode* child;
    Entry* e;
    
    i = findChildIndex(node, key);
    cursor->ancestorsIdx[level] = i;
    
    if (i == -1) {
      child = node->ptr0;
    } else {
      child = node->entries[i].ptr.child;
    }
    
    moveToKey(child, key, cursor, level + 1);
    return;
  }
}

/* Move to the first record in the B-tree*/
static void moveToFirst(BtNode* node, Cursor* cursor, int level) {
  assert(node != NULL);
  assert(cursor != NULL);
  assert(level >= 0);
  
  /* Track ancestors as you go to first node*/
  cursor->ancestors[level] = node;
  cursor->level = level;
  
  if (node->isLeaf) {
    cursor->ancestorsIdx[level] = 0;
    return;
  }

  /* Otherwise intern node, we need to keep going down */
  cursor->ancestorsIdx[level] = -1;
  moveToFirst(node->ptr0, cursor, level+1);
}

static void moveToLast(BtNode* node, Cursor* cursor, int level) {
  assert(node != NULL);
  assert(cursor != NULL);
  assert(level >= 0);

  cursor->ancestors[level] = node;
  cursor->level = level;
  
  if (node->isLeaf) {
    cursor->ancestorsIdx[level] = node->numKeys;
    return;
  }

  /* Otherwise intern node, we need to keep going down */
  cursor->ancestorsIdx[level] = node->numKeys-1;
  moveToLast(node->entries[node->numKeys-1].ptr.child, cursor, level+1);
  return;
}  

static void handleDeleteBtree(BtNode* node, void (* freeRecord)(void *)) {
    /* int i; */
    
    /* /\* Part of base case. In leaf node, free all records with  */
    /*  * freeRecord function, if any. *\/ */
    /* if (node->isLeaf) { */
    /*     if (freeRecord == NULL){ */
    /*         return; */
    /*     } */
        
    /*     for (i = 0; i < node->numKeys; i++) { */
    /*         freeRecord((void *)node->entries[i].ptr.record); */
    /*     } */
        
    /*     return; */
    /* } */
    
    /* /\* Recursively delete every child subtree. If the child is a leaf, after  */
    /*  * recursively deleting every child subtree, free the node. *\/ */
    /* handleDeleteBtree(node->ptr0, freeRecord); */
    /* if (node->ptr0->isLeaf) { */
    /*     free(node->ptr0); */
    /* } */
    /* for(i = 0; i < node->numKeys; i++) { */
    /*     handleDeleteBtree(node->entries[i].ptr.child, freeRecord); */
    /*     if (node->entries[i].ptr.child->isLeaf) { */
    /*         free(node->entries[i].ptr.child); */
    /*     } */
    /* } */
  return;
}

/* Check node size invariants */
static void ASSERT_NODE_INVARIANT(BtNode* node, Relation_T relation) {
    
    /* If not root, must have at least fanout / 2 keys*/
    if(relation->root != node) {
        assert(node->numKeys >= FANOUT / 2);
    }
    assert(node->numKeys <= FANOUT);
}

/* TODO: refactor out common code etc. maybe create library for them 
 * TODO: pass in schema object to btree on initialization to determine 
 * types of record. Also pass in schema type into record init so btree can 
 * assert that an input record is of correct type. 
 * careful of typedefs and all
 * 
 * Todo: notify cursors on update.
 * TODO: make some strings const??
 * Make indices const were possible
 * check for use of semi colons
 * 
 * What id we pass max index level? weird cases like that.. check for such
 * bugs.
 * 
 * Todo leaf would split 15 to 7 and 9
 */

static void printTree(BtNode* node, int level) {
    int i;

    if(node->First) {
      fprintf(stderr,"FIRST ");
    }
    if(node->Last) {
      fprintf(stderr,"LAST ");
    }
    
    if(node->isLeaf) {
        fprintf(stderr, "Leaf Level: %d) ", level);
        for(i = 0; i < node->numKeys; i++) {
            fprintf(stderr, " %lu", node->entries[i].key);
        }
        fprintf(stderr, "\n");
        return;
    }
    
    fprintf(stderr, "Intern Level: %d) ", level);
    for(i = 0; i < node->numKeys; i++) {
        fprintf(stderr, " %lu", node->entries[i].key);
    }
    fprintf(stderr, "\n");
    
    printTree(node->ptr0, level + 1);
    for(i = 0; i < node->numKeys; i++) {
        printTree(node->entries[i].ptr.child, level+1);
    }
}

static void printCursor(Cursor_T cursor) {
  int i;
  printf("Cursor: ");
  for (i=0; i <= cursor->level; i++) {
    printf("%d ", cursor->ancestorsIdx[i]);
  }
  printf("\n");
}
