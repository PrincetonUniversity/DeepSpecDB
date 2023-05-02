int traverse(pn *pn, int k){
  node_t *r = (pn->n); 
  for( ; ; ){
    acquire(pn->n->lock); 
    pn->p = pn->n;
    if (inRange(pn, k) == 1){
      if (pn->p->t == NULL)
        return 1;
      else{
        int b = findNext(pn, k);
        if (b == 0){
          return 0;
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
}