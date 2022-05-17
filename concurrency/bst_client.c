#include "./bst_conc.h"

int a, b, c, d;

void insert_int(treebox t, int key, int value){
   void* p_value = surely_malloc(sizeof(int));
   *((int*)p_value) = value;
   insert(t, key, (void*) &value);
}

void* update_tree(void* t){
  a = 1;
  b = 2;
  c = 3; 
  d = 4;
  // insert_int(t, 2, 20);
  // insert_int(t, 1, 1);
  // insert_int(t, 1, 100);
  // insert_int(t, 2, 1);
  // int m = 1;
  // int n = 2;
  // int k = 2;
  // int j = 3;
  // void* pm = &m;
  // void* pn = &n;
  // void* pk = &k;
  // void* pj = &k;
  insert(t, 1, &a);
  insert(t, 2, &b);
  insert(t, 1, &c);
  insert(t, 2, &d);
  return (void*)NULL;
}

int retrieve_value(treebox t){
  void* searchResult;
  int y = -1;
  do {
     searchResult = lookup (t,  2);
     if (searchResult != NULL) {
        y = *((int *) searchResult);
        //printf("Key 1 returns %d\n", y);
     }
  } while (y != 4);
   searchResult = lookup (t,  1);
   return *((int *) searchResult);
}



int main(){
  treebox t;
  t = treebox_new();  

   
 int* result;


  //  makelock((void*)t_lock);
  // /* Spawn */
  spawn((void *)&update_tree, t);

  //printf("Key 1 returns %d\n", retrieve_value(t));
  int retVal =  retrieve_value(t);
  
  // /*JOIN */
  //  acquire((void*)t_lock);  
  //  freelock2((void*)t_lock);
  
  treebox_free(t);
  return 0;
}
