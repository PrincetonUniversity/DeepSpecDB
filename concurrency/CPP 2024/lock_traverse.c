int traverse(pn *pn, int k){
  for( ; ; ){
    pn->p = pn->n;
    if (pn->p->t == NULL)
      return 1;
    else{
      int b = findNext(pn, k);
      if (b == 0){
        return 0;
      }
      else{
        acquire(pn->n->lock);
        release(pn->p->lock);
      }
    }
  }
}