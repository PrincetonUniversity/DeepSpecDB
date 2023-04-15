void insert (node_t **t, int k, void *value){
  struct pn *pn = (struct pn *) surely_malloc (sizeof *pn);
  pn->n = *t;
  if (traverse(pn, k) == 0){
    pn->p->t->value = value;
  }
  else{
    insertOp(pn, k, value);
  }
  release(pn->n->lock);
  free(pn);
}