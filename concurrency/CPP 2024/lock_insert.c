void insert (node_t **r, int k, void *v){
  struct pn *pn = (struct pn*)surely_malloc(sizeof *pn);
  pn->n = *r;
  acquire(pn->n->lock);  
  if (traverse(pn, k) == 0){
    pn->p->t->value = v;
  }
  else{
    insertOp(pn, k, v);
  }
  release(pn->n->lock);
  free(pn);
}