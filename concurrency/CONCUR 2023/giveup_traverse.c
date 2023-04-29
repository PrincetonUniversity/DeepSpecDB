int traverse(pn *pn, int k){
  node_t *r = (pn->n); 
  int flag = 1;
  for( ; ; ){
    acquire(pn->n->lock); 
    pn->p = pn->n;
    if (inRange(pn, k) == 1){
      if (pn->p->t == NULL)
        break;
      else{
        int b = findNext(pn, k);
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
      pn->n = r;
    }
  }
  return flag;
}