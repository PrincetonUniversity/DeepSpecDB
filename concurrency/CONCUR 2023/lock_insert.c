void insert (treebox t, int x, void *value){
  struct pn *pn = (struct pn *) surely_malloc (sizeof *pn);
  pn->n = *t;
  acquire(pn->n->lock);
  if (traverse(pn, x, value) == 0){
        pn->p->t->value = value;
  }
  else{
    insertOp(pn, x, value);
  }
  release(pn->n->lock);
  free(pn);
}