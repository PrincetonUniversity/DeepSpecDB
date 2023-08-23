int findNext (pn *pn, int k){
  int y = pn->p->t->key;
  if (x < y){
    pn->n = pn->p->t->left;
    return 1;
  } 
  else if (x > y){
    pn->n = pn->p->t->right;
    return 1;
  } 
  else
    return 0;
}