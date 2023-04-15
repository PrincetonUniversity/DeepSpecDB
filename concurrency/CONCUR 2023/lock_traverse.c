int traverse(pn *pn, int k){
  int flag = 1;
  for( ; ; ){
    pn->p = pn->n;
    if (pn->p->t == NULL)
      break;
    else{
      int b = findNext(pn, k);
      if (b == 0){
        flag = 0;
        break;
      }
      else{
        acquire(pn->n->lock);
        release(pn->p->lock);
      }
    }
  }
  return flag;
}