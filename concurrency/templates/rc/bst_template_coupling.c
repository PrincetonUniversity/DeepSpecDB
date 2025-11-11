//
//  main.c
//  BST
//
//  Created by Duc-Than Nguyen on 1/2/22.
//


#include <stdio.h>
/* #include <stdlib.h> */
#include "threads.h"


extern void *malloc (size_t n);
extern void free(void *p);
extern void exit(int code);

//@rc::import puretree from refinedc.project.rc.bst_template_coupling

typedef struct [[rc::refined_by("k: Z", "v: val", "l: val", "r: val")]] tree {
  [[rc::field("k @ int<tint>")]] int key;
  [[rc::field("value<{tptr tvoid}, v>")]] void *value;
  [[rc::field("value<{tptr (Tstruct _tree_t noattr)}, l>")]] struct tree_t *left;
  [[rc::field("value<{tptr (Tstruct _tree_t noattr)}, r>")]] struct tree_t *right;
} tree;
typedef struct [[rc::refined_by("t: {option (Z * val * val * val)}", "lock: val")]] tree_t {
    [[rc::field("t @ optionalO<λ t. &own<t @ tree>, null>")]] tree *t;
    [[rc::field("value<{tptr tvoid}, lock>")]] lock_t lock;
} tree_t;

typedef struct tree_t **treebox;
treebox tb;

void *surely_malloc (size_t n) {
    void *p = malloc(n);
    if (!p) exit(1);
    return p;
}

treebox treebox_new(void) {
    treebox p = (treebox) surely_malloc(sizeof (*p));
    tree_t *newt = (tree_t *) surely_malloc(sizeof(tree_t));
    *p = newt;
    lock_t l;
    l = makelock();
    newt->lock = l;
    newt->t = NULL;
    release(l);
    return p;
}

void tree_free(struct tree_t *tgp) {
    struct tree_t *pa, *pb;
    tree* p;
    void *l = tgp->lock;
    acquire(l);
    p = tgp->t;
    if (p!=NULL) {
        pa=p->left;
        pb=p->right;
        free(p);
        tree_free(pa);
        tree_free(pb);
    }
    freelock(l);
    free(tgp);
}

void treebox_free(treebox b) {
    struct tree_t *t = *b;
    tree_free(t);
    free(b);
}

//Template style
typedef struct [[rc::refined_by("t : {option (Z * val * val * val) * val}", "n : val")]] pn {
    [[rc::field("&own<t @ tree_t>")]] struct tree_t *p;
    [[rc::field("value<{tptr (Tstruct _tree_t noattr)}, n>")]] struct tree_t *n;
} pn;

[[rc::parameters("ppn: address", "n: val", "k: Z", "v: val",
    "l: val", "r: val", "lock: val", "x: Z")]]
[[rc::args("ppn @ &own<{((Some (k, v, l, r), lock), n)} @ pn>", "x @ int<tint>")]]
[[rc::requires("{l ≠ Vundef}")]]
[[rc::requires("{r ≠ Vundef}")]]
[[rc::exists("succ: bool", "nn: val")]]
[[rc::returns("succ @ boolean<tint>")]]
[[rc::ensures("{if succ then (nn = l ∧ x < k) ∨ (nn = r ∧ k < x) else nn = n ∧ x = k}")]]
[[rc::ensures("own ppn : &own<{((Some (k, v, l, r), lock), nn)} @ pn>")]]
int findnext (pn *pn, int x){
    int y = pn->p->t->key;
    
    if (x < y){
        pn->n = pn->p->t->left;
        return 1;
    }
    else if (x > y){
        pn->n = pn->p->t->right;
        return 1;
    }
    else{
        return 0;
    }
}

int traverse(pn *pn, int x, void *value) {
    int flag = 1;
    for( ; ; ){
        pn->p = pn->n;
        if (pn->p->t == NULL){
            break;
        } else {
            int b = findnext(pn, x);
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

void insertOp(pn *pn, int x, void *value){
    tree_t *p1 = (struct tree_t *) surely_malloc (sizeof *(pn->p));
    tree_t *p2 = (struct tree_t *) surely_malloc (sizeof *(pn->p));
    p1->t = NULL;
    p2->t = NULL;
    lock_t l1;
    l1 = makelock();
    p1->lock = l1;
    release(l1);
    lock_t l2;
    l2 = makelock();
    p2->lock = l2;
    release(l2);
    pn->p->t = (struct tree *) surely_malloc (sizeof *(pn->p->t));
    pn->p->t->key = x;
    pn->p->t->value = value;
    pn->p->t->left = p1;
    pn->p->t->right = p2;
}

void insert (treebox t, int x, void *value) {
    struct pn *pn = (struct pn *) surely_malloc (sizeof *pn);
    pn->n = *t;

    acquire(pn->n->lock);
    if (traverse(pn, x, value) == 0){
        pn->p->t->value = value;
    }
    else
    {
        insertOp(pn, x, value);
    }
    release(pn->n->lock);
    free(pn);
}

void *lookup (treebox t, int x) {
    struct pn *pn = (struct pn *) surely_malloc (sizeof *pn);
    void *v;
    pn->n = *t;
    
    acquire(pn->n->lock);
    if (traverse(pn, x, NULL) == 0){
        v = pn->p->t->value;
    }
    else
    {
        v = NULL;
    }

    release(pn->n->lock);
    free(pn);
    return v;
}

void turn_left(struct tree_t * tgl, struct tree_t * tgr) {
  struct tree_t * mid;
  struct tree * r, *l;
  r = tgr->t;
  mid = r->left;
  l = tgl->t;
  l->right = mid;
  r->left = tgr;
  tgl->t = r;
  tgr->t = l;
}

void pushdown_left (struct tree_t *tgp) {
  struct tree *p, *q;
  struct tree_t *tgq;
  for(;;) {
    void *lp = tgp->lock; // initial lp acquired in delete
    p = tgp->t;
    tgq = p->right;
    void *lq = tgq->lock;
    acquire(lq);
    q = tgq->t;
    if (q==NULL) {
      struct tree_t *tgl = p->left;
      acquire(tgl->lock);
      tgp->t = tgl->t;
      free(p);
      freelock(lq);
      free(tgq);
      freelock(tgl->lock);
      free(tgl);
      release(lp);
      return;
    } else {
      turn_left(tgp, tgq);
      tgp = q->left;
      release(lp);
    }
  }
}

void delete (treebox t, int x) {
    struct pn *pn = (struct pn *) surely_malloc (sizeof *pn);
    pn->n = *t;
    
    acquire(pn->n->lock);
    if (traverse(pn, x, NULL) == 0){
        pushdown_left(pn->n);
    }
    else
    {
        release(pn->n->lock);
    }
    
    free(pn);
    return;
}

//Traverse
void Inorder(struct tree_t *p){
    if (p->t != NULL){
        Inorder(p->t->left);
        printf ("node->data %d %s \n", p->t->key, p->t->value);
        Inorder(p->t->right);
    }
}

void traverseInorder (treebox t){
    struct tree_t *tgt;
    tgt = *t;
    Inorder(tgt);
}

void *thread_func(void *args) {
    lock_t l = (lock_t)args;
    
    // insert at key 1
    insert(tb,6,"ONE_FROM_THREAD");
    insert(tb,4,"FOUR");
    //   insert(tb,5,"FIVE");
    
    release((void*)l);
    return (void *)NULL;
}

int main (void) {
    tb = treebox_new();
    lock_t t_lock ;
    insert(tb,3,"three");
    insert(tb,1,"One");
    insert(tb,4,"four");
    
    t_lock = makelock();
    /* Spawn */
    spawn((void *)&thread_func, (void *)t_lock);
    /*JOIN */
    acquire((void*)t_lock);
    freelock((void*)t_lock);
    printf ("\nTraverse\n");
    traverseInorder(tb);
    delete(tb, 1);
    delete(tb, 1);
    delete(tb, 3);
    delete(tb, 4);
    delete(tb, 6);
    delete(tb, 6);
    printf ("\nTraverse\n");
    traverseInorder(tb);
    treebox_free(tb);
    fflush(stdout);
    return 0;
}
