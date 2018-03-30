/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   kvstoretests.c
 * Author: Oluwatosin V. Adewale
 *
 * Created on February 28, 2018, 6:27 PM
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>
#include <time.h>
/* #include <sys/_types/_key_t.h> */

#include "kvstore.h"
#include "relation.h"
#include "kvstore_int.h"
#include "bordernode.h"

/*
 * Simple C Test Suite
 */
/* FILE* fp; */

static void WriteKeyToStream(KVKey_T key, FILE* stream){
    size_t i = 0;
    fputc((int)key->len, stream);
    
    for(i = 0; i < key->len; i++) {
        fputc(key->str[i], stream);
    }
}

static KVKey_T* ReadKeysFromStream(FILE* stream, int* len) {
    int c;
    char* str;
    KVKey_T* kvKeyArr;
    size_t arrSize = 10;
    size_t arrIdx = 0;
    int count;
    
    kvKeyArr = (KVKey_T*) calloc(arrSize, sizeof(KVKey_T));
    
    c = getc(stream);
    while(c != EOF) {
        str =  (char*) calloc(c, sizeof(char));
        count = fread(str, sizeof(char), c, stream);
        
        if(count != c) {
            fprintf(stderr,"Error reading correct number of bytes.\n");
            exit(EXIT_FAILURE);
        }
        
        if(arrIdx == arrSize) {
            kvKeyArr = (KVKey_T*) UTIL_ResizeArray(kvKeyArr, arrSize, arrSize*2);
            arrSize *= 2;
            if(kvKeyArr == NULL) {
                fprintf(stderr,"Error resizing array.\n");
                exit(EXIT_FAILURE);
            }
        }
        
        kvKeyArr[arrIdx] = KV_NewKey(str, c);
        arrIdx++;
        
        c = getc(stream);
        
        free(str);
    }
    
    *len = arrIdx;
    
    return kvKeyArr;
}

static void testSinglePutAndGet(KVStore_T kvStore, KVKey_T testKey, void* value, size_t valueLen) {
    Bool status;
    int res;
    void* resultValue;
    
    assert(kvStore != NULL);
    assert(testKey != NULL);
    assert(value != NULL);
    
    
    if (testKey->len == 31) {
        assert(True);
    }
    
    status = KV_Put(kvStore, testKey, value);
    assert(status == True);
    
        
    resultValue = (char*) KV_Get(kvStore, testKey);
    if(resultValue == NULL) {
        resultValue = (char*) KV_Get(kvStore, testKey);
        /* status = KV_Put(kvStore, testKey, value);
        resultValue = (char*) KV_Get(kvStore, testKey); */
        assert(resultValue != NULL);
    }
    assert(resultValue != NULL);
    
    res = memcmp(resultValue, value, valueLen);
    assert(res == 0);  
}

static void testSingleGet(KVStore_T kvStore, KVKey_T testKey, void* value, size_t valueLen) {
    int res;
    void* resultValue;

    resultValue = (void*) KV_Get(kvStore, testKey);
    assert(resultValue != NULL);
    
    res = memcmp(resultValue, value, valueLen);
    if(res != 0) {
        assert(res == 0);
    }
}

static KVKey_T GetRandomKey(size_t alphSize, size_t maxLen) {
    /* Create a string*/
    size_t strLen = rand() % (maxLen + 1);
    size_t i;
    char letter;
    KVKey_T key;
    
    char* str = (char *) calloc(strLen, sizeof(char));
    
    /* Create a random key where each 8 byte slice has the same characters */
    for(i = 0; i < strLen; i++) {
        if(i % 8 == 0) {
            letter = rand() % alphSize;
        }
        str[i] = letter;
    }
    
    key = KV_NewKey(str, strLen);
    assert(key!= NULL);
    free(str);
    
    return key;   
}

/* Returns an array of num positive random values between 0 and maxVal inclusive. */
static size_t* GetRandomValues(int maxVal, size_t num) {
    size_t* results;
    size_t i;    
    assert(maxVal >= 0);

    results = (size_t *) malloc(sizeof(size_t) * num);
    assert(results != NULL);
    
    for(i = 0; i < num; i++) {
        results[i] = rand() % (maxVal + 1);
    }
    
    return results;
}

void PutUnitTests() {
    KVStore_T kvStore;
    char* str1, *str2, *str3;
    size_t strLength;
    int value1 = 1, value2 = 2, value3 = 3;
    size_t i;
    KVKey_T testKey;
    BorderNode_T borderNode;
    BorderNodeEntry* bnEntry;
    Cursor_T btreeCursor;
    unsigned long keySlice;
    Bool status;
    
    
    kvStore = KV_NewKVStore();
    assert(kvStore != NULL);
    assert(KV_NumKeys(kvStore) == 0);
    
    str1 = "booooooo"; str2 = "boooooooo"; str3 = "boooooooooo";
    
    strLength = strlen(str1);
    testKey = KV_NewKey(str1, strLength);
    KV_Put(kvStore, testKey, &value1);
    KV_FreeKey(testKey);
    
    /* Get the bordernode we just inserted they key and value into*/
    btreeCursor = getNodeCursor(kvStore->rootNode);
    keySlice = UTIL_GetNextKeySlice(str1, strLength);
    status = RL_MoveToKey(btreeCursor, keySlice);
    assert(status == True);
    borderNode = (BorderNode_T)RL_GetRecord(btreeCursor);
    assert(borderNode != NULL);
    
    /* Keyslices should be the same */
    assert(BN_GetKeySlice(borderNode) == keySlice);
    assert(BN_GetSuffix(borderNode) == NULL); 
    assert(BN_GetSuffixLength(borderNode) == 0);
    for(i = 0; i < 9; i++) {
        /* Every entry should be null except the entry of the key we just inserted. */
        if(i == strLength) {
            bnEntry = BN_GetValue(borderNode, i);
            assert(bnEntry != NULL);
            assert(bnEntry->isLink == False);
            assert(bnEntry->linkOrValue.value == &value1);
        }
        
        else { assert(BN_GetValue(borderNode, i) == NULL);}
    }
    
        
    strLength = strlen(str2);
    testKey = KV_NewKey(str2, strLength);
    KV_Put(kvStore, testKey, &value2);
    KV_FreeKey(testKey);

    /* Get the bordernode we just inserted they key and value into*/
    btreeCursor = getNodeCursor(kvStore->rootNode);
    keySlice = UTIL_GetNextKeySlice(str2, KEY_SLICE_LENGTH);
    status = RL_MoveToKey(btreeCursor, keySlice);
    assert(status == True);
    borderNode = (BorderNode_T)RL_GetRecord(btreeCursor);
    assert(borderNode != NULL);
    
    /* Keyslices should be the same */
    assert(BN_GetKeySlice(borderNode) == keySlice);

    for(i = 0; i <= 9; i++) {
        /* Every entry should be null except the entry of the key we just inserted. */
        if(i == strlen(str1)) {
            bnEntry = BN_GetValue(borderNode, i);
            assert(bnEntry != NULL);
            assert(bnEntry->isLink == False);
            assert(bnEntry->linkOrValue.value == &value1);
        }
        else if (i == 9) {
            char* suffix;
            size_t suffixLength;
            size_t strSuffixLength = strlen(str2) - KEY_SLICE_LENGTH;
            
            bnEntry = BN_GetValue(borderNode, i);
            assert(bnEntry != NULL);
            assert(bnEntry->isLink == False);
            assert(bnEntry->linkOrValue.value == &value2);
            
            suffix = BN_GetSuffix(borderNode);
            assert(suffix != NULL);
            suffixLength = BN_GetSuffixLength(borderNode);
            assert(suffixLength != 0);
            
            assert(UTIL_StrEqual(suffix, suffixLength, str2 + KEY_SLICE_LENGTH, strSuffixLength) == True);
        }
        else { 
            assert(BN_GetValue(borderNode, i) == NULL);
        }
    }
    
    
    strLength = strlen(str3);
    testKey = KV_NewKey(str3, strLength);
    KV_Put(kvStore, testKey, &value3);
    KV_FreeKey(testKey);

    /* Get the bordernode we just inserted they key and value into*/
    btreeCursor = getNodeCursor(kvStore->rootNode);
    keySlice = UTIL_GetNextKeySlice(str3, KEY_SLICE_LENGTH);
    status = RL_MoveToKey(btreeCursor, keySlice);
    assert(status == True);
    borderNode = (BorderNode_T)RL_GetRecord(btreeCursor);
    assert(borderNode != NULL);
    
    /* Keyslices should be the same */
    assert(BN_GetKeySlice(borderNode) == keySlice);
    assert(BN_GetSuffix(borderNode) == NULL); 
    assert(BN_GetSuffixLength(borderNode) == 0);

    for(i = 0; i <= 9; i++) {
        /* Every entry should be null except the entry of the key we just inserted. */
        if(i == strlen(str1)) {
            bnEntry = BN_GetValue(borderNode, i);
            assert(bnEntry != NULL);
            assert(bnEntry->isLink == False);
            assert(bnEntry->linkOrValue.value == &value1);
        }  
        else if (i == 9) {            
            bnEntry = BN_GetValue(borderNode, i);
            assert(bnEntry != NULL);
            assert(bnEntry->isLink == True);
            assert(bnEntry->linkOrValue.value != NULL);
        }
        else { 
            assert(BN_GetValue(borderNode, i) == NULL);
        }
    }
    
    
    bnEntry = BN_GetValue(borderNode, 9);
    assert(bnEntry->isLink == True);
    /* Get the tree at the next layer */ 
    btreeCursor = getNodeCursor(bnEntry->linkOrValue.link);
    
    keySlice = UTIL_GetNextKeySlice(str3 + KEY_SLICE_LENGTH, strlen(str3) - KEY_SLICE_LENGTH);
    status = RL_MoveToKey(btreeCursor, keySlice);
    assert(status == True);
    borderNode = (BorderNode_T)RL_GetRecord(btreeCursor);
    assert(borderNode != NULL);
    
    /* Keyslices should be the same */
    assert(BN_GetKeySlice(borderNode) == keySlice);
    assert(BN_GetSuffix(borderNode) == NULL); 
    assert(BN_GetSuffixLength(borderNode) == 0);
    
    
    
   
}

void BasicTests() {
    KVStore_T kvStore;
    char* str1, *str2, *str3;
    size_t strLength;
    char* value1, *value2; int value3 = 3;
    KVKey_T testKey;
    
    kvStore = KV_NewKVStore();
    assert(kvStore != NULL);
    assert(KV_NumKeys(kvStore) == 0);
    
    str1 = "foo"; str2 = "boooooooo"; str3 = "boooooooooo";
    /*fprintf(stderr, "%s is %lu\n", str1, UTIL_GetNextKeySlice(str1, strlen(str1) + 1));
    fprintf(stderr, "%s is %lu\n", str2, UTIL_GetNextKeySlice(str2, 8));*/

    value1 = "bar1"; value2 = "2"; 
    
    strLength = strlen(str1) + 1;
    testKey = KV_NewKey(str1, strLength);
    testSinglePutAndGet(kvStore, testKey, value1, strlen(value1));
    KV_FreeKey(testKey);
    /*fprintf(stderr, "Num Keys %lu\n",KV_NumKeys(kvStore));*/

    
    strLength = strlen(str2) + 1;
    testKey = KV_NewKey(str2, strLength);
    testSinglePutAndGet(kvStore, testKey, value2, strlen(value2));
    KV_FreeKey(testKey);
    /*fprintf(stderr, "Num Keys %lu\n",KV_NumKeys(kvStore));*/

    
    strLength = strlen(str3) + 1;
    testKey = KV_NewKey(str3, strLength);
    testSinglePutAndGet(kvStore, testKey, &value3, sizeof(value3));
    KV_FreeKey(testKey);
    /*fprintf(stderr, "Num Keys %lu\n",KV_NumKeys(kvStore));*/
    
    /* See if updates are successful. */
    strLength = strlen(str1) + 1;
    testKey = KV_NewKey(str1, strLength);
    testSinglePutAndGet(kvStore, testKey, value1, strlen(value1));
    KV_FreeKey(testKey);
    /*fprintf(stderr, "Num Keys %lu\n",KV_NumKeys(kvStore));*/
    
    strLength = strlen(str2) + 1;
    testKey = KV_NewKey(str2, strLength);
    testSinglePutAndGet(kvStore, testKey, value2, strlen(value2));
    KV_FreeKey(testKey);
    /*fprintf(stderr, "Num Keys %lu\n",KV_NumKeys(kvStore));*/

    
    strLength = strlen(str3) + 1;
    testKey = KV_NewKey(str3, strLength);
    testSinglePutAndGet(kvStore, testKey, &value3, sizeof(value3));
    KV_FreeKey(testKey);
    /*fprintf(stderr, "Num Keys %lu\n",KV_NumKeys(kvStore));*/
    
        
    /* Can we successfully get? */
    strLength = strlen(str1) + 1;
    testKey = KV_NewKey(str1, strLength);
    testSingleGet(kvStore, testKey, value1, strlen(value1));
    KV_FreeKey(testKey);
    /*fprintf(stderr, "Num Keys %lu\n",KV_NumKeys(kvStore));*/
    
    strLength = strlen(str2) + 1;
    testKey = KV_NewKey(str2, strLength);
    testSingleGet(kvStore, testKey, value2, strlen(value2));
    KV_FreeKey(testKey);
    /*fprintf(stderr, "Num Keys %lu\n",KV_NumKeys(kvStore));*/

    
    strLength = strlen(str3) + 1;
    testKey = KV_NewKey(str3, strLength);
    testSingleGet(kvStore, testKey, &value3, sizeof(value3));
    KV_FreeKey(testKey);
    /*fprintf(stderr, "Num Keys %lu\n",KV_NumKeys(kvStore));*/

    
    assert(KV_NumKeys(kvStore) == 3);
     
}

void StressTests (size_t inputSize) {
    KVStore_T kvStore;
    /* Array of keys and values */
    KVKey_T* keys;
    size_t* values;
    size_t i, j;
    size_t count = 0;
        
    keys = (KVKey_T*) calloc(inputSize, sizeof(KVKey_T));
    assert(keys != NULL);
    
    for(i = 0; i < inputSize; i++) {
        keys[i] = GetRandomKey(10, 40);
    }
    
    /*values = GetRandomValues(10, inputSize);*/
    values = (size_t *) calloc(inputSize, sizeof(size_t));
    
    for(i = 0; i < inputSize; i++) {
        values[i] = i;
    }
    
    
    kvStore = KV_NewKVStore();
    assert(kvStore != NULL);
    assert(KV_NumKeys(kvStore) == 0);

    for(i = 0; i < inputSize; i++) {
        /*fprintf(stderr, "i = %lu. Testing Put and get\n", i );*/
        /*WriteKeyToStream(keys[i], fp);
        fflush(fp);*/
        testSinglePutAndGet(kvStore, keys[i], &(values[i]), sizeof(size_t));
        
        for(j = 0; j < i; j++) {
            /* If there was an older key free it and set to null. */
            if(keys[j] != NULL && KV_KeyEqual(keys[i], keys[j]) == True) {
                KV_FreeKey(keys[j]);
                keys[j] = NULL;
            }
        }
        
    }
    
    for(i = 0; i < inputSize; i++) {
        /*fprintf(stderr, "i = %lu. Testing Get\n", i );*/
        if(keys[i] != NULL) {
            testSingleGet(kvStore, keys[i], &(values[i]), sizeof(size_t));
            count++;
        }
    }
    
    assert(count == KV_NumKeys(kvStore));

}

void StrKeySliceConversionTests() {
   
    char test1[]= "foo";
    char test2[]= "sherlock";
    char test3[]= "sherloc";
    char test4[]= "sherlockholmes";
    
    unsigned long ul_test1 = UTIL_GetNextKeySlice(test1, strlen(test1));
    unsigned long ul_test2 = UTIL_GetNextKeySlice(test2, strlen(test2));
    unsigned long ul_test3 = UTIL_GetNextKeySlice(test3, strlen(test3));
    unsigned long ul_test4 = UTIL_GetNextKeySlice(test4, 0);
    
    assert(ul_test1 < ul_test2);
    assert(ul_test1 < ul_test3);
    assert(ul_test2 > ul_test3);
    
    assert(ul_test4 == 0);
    assert(ul_test4 < ul_test1);

    
    
    assert(0 == memcmp(test1, UTIL_KeySliceToStr(ul_test1, strlen(test1)), strlen(test1)));
    assert(0 == memcmp(test2, UTIL_KeySliceToStr(ul_test2, strlen(test2)), strlen(test1)));
    assert(0 == memcmp(test3, UTIL_KeySliceToStr(ul_test3, strlen(test3)), strlen(test1)));
    
    
    /*printf("kvstoretests test 2\n");
    printf("%%TEST_FAILED%% time=0 testname=test2 (kvstoretests) message=error message sample\n");*/
}

/* */
double PerformanceTest(size_t inputSize) {
    KVStore_T kvStore;
    /* Array of keys and values */
    KVKey_T* keys;
    size_t* values;
    size_t i;
    void* result;
    clock_t begin, end;
        
    keys = (KVKey_T*) calloc(inputSize, sizeof(KVKey_T));
    assert(keys != NULL);
    
    for(i = 0; i < inputSize; i++) {
        keys[i] = GetRandomKey(10, 32);
    }
    
    values = GetRandomValues(10, inputSize);
    
    
    kvStore = KV_NewKVStore();
    assert(kvStore != NULL);
    assert(KV_NumKeys(kvStore) == 0);

    begin = clock();
    for(i = 0; i < inputSize; i++) {
        KV_Put(kvStore, keys[i], &(values[i]));
    }
   
    for(i = 0; i < inputSize; i++) {
        result = (void*) KV_Get(kvStore, keys[i]);
    }  
    end = clock();
    
    return (double) (end - begin) / CLOCKS_PER_SEC;
}



int main(int argc, char** argv) {
    
    size_t inputSize = 10000000;
    double timeSpent;
    
    
    if (argc == 2) {
        KVKey_T* keyArr;
        KVStore_T store = KV_NewKVStore();
        int len;
        int i;
        
        FILE* fp = fopen(argv[1], "r");
        
        keyArr = ReadKeysFromStream(fp, &len);
        fclose(fp);
        
        for(i = 0; i < len; i++) {
            testSinglePutAndGet(store, keyArr[i], &keyArr[i], sizeof(KVKey_T*));
        }
        
        return 0;
    }
    

    
    printf("%%SUITE_STARTING%% kvstoretests\n");
    printf("%%SUITE_STARTED%%\n");

    printf("%%TEST_STARTED%% keyslice conversion tests (kvstoretests)\n");
    StrKeySliceConversionTests();
    printf("%%TEST_FINISHED%% time=0 keyslice conversion tests (kvstoretests) \n");
    
    printf("%%TEST_STARTED%% Put Unit tests (kvstoretests)\n");
    PutUnitTests();
    printf("%%TEST_FINISHED%% time=0 Put Unit tests (kvstoretests) \n");

    
    fprintf(stderr, "%%TEST_STARTED%% Basic Tests (kvstoretests)\n");
    BasicTests();
    fprintf(stderr, "%%TEST_FINISHED%% time=0 Basic Tests (kvstoretests) \n");

    fprintf(stderr,"%%TEST_STARTED%% Stress Tests (kvstoretests)\n");
    StressTests(10000);
    fprintf(stderr,"%%TEST_FINISHED%% time=0 Stress Tests (kvstoretests) \n");

    fprintf(stderr,"%%TEST_STARTED%% Performance Test with %lu keys (kvstoretests)\n", (unsigned long) inputSize);
    timeSpent = PerformanceTest(inputSize);
    fprintf(stderr,"%%TEST_FINISHED%% time= %0.2f secs Stress Tests (kvstoretests) \n", timeSpent);
    fprintf(stderr,"%% %0.2f queries per second \n .", (inputSize / timeSpent));
    
    printf("%%SUITE_FINISHED%% time=0\n");

    return (EXIT_SUCCESS);
}
