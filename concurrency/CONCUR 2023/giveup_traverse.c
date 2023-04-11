int traverse(pn *pn, int k, void *value){
  tree_t *p = (pn->n); 
  int flag = 1;
  for( ; ; ){
    acquire(pn->n->lock); 
    pn->p = pn->n;
    if (inRange(pn, k) == 1){
      if (pn->p->t == NULL)
        break;
      else{
        int b = findNext(pn, k, value);
        if (b == 0){
          flag = 0;
          break;
        }
        else
          release(pn->p->lock);
      }
    }
    else{
      release(pn->p->lock);
      pn->n = p;
    }
  }
  return flag;
}