int traverse(pn *pn, int x, void *value){
  int flag = 1;
  for( ; ; ){
    pn->p = pn->n;
    if (pn->p->t == NULL)
      break;
    else{
      int b = findnext(pn, x, value);
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