void insert (node_t **r, int k, void *v){
	struct pn *pn = (struct pn *)surely_malloc(sizeof *pn);
	pn->n = *r;
	$\color{specblue} \left\{\begin{array}{l} \texttt{pn} \mapsto (\texttt{\_}, \texttt{r}) \ast  \nodeboxrep(\texttt{r}) \end{array}\right\}$
	acquire(pn->n->lock);
	$\color{specblue} \left\{\begin{array}{l}  \texttt{pn} \mapsto (\texttt{\_}, \texttt{r}) \ast  \nodeboxrep(\texttt{r}) \ast \mathsf{R}(\texttt{r}) \end{array}\right\}$
	if (traverse(pn, k) == 0){
		$\color{specblue} \left\{\begin{array}{l}  \exists\ n'.\ \texttt{pn} \mapsto (n', n') \ast \nodeboxrep(n') \ast \mathsf{node\_contents}(n', (\texttt{k}, v'), \mathsf{range}) \end{array}\right\}$
		pn->p->t->value = v;
		$\color{specblue} \left\{\begin{array}{l}  \texttt{pn} \mapsto (n', n') \ast \nodeboxrep(n') \ast \mathsf{node\_contents}(n', (\texttt{k}, \texttt{v}), \mathsf{range}) \end{array}\right\}$ 
		//Linearization point
	}
	else{
		$\color{specblue} \left\{\begin{array}{l}  \exists\ n'.\ \texttt{pn} \mapsto (n', n') \ast n'\texttt{->t} = \texttt{NULL}  \ast \nodeboxrep(n') \ast \mathsf{node\_contents}(n', \cdot, \mathsf{range}) \ast \texttt{k} \in \mathsf{range} \end{array}\right\}$
		insertOp(pn, k, v);
		$\color{specblue} \left\{\begin{array}{l} \texttt{pn} \mapsto (n', n') \ast \nodeboxrep(n') \ast \mathsf{node\_contents}(n', \cdot, \mathsf{range}) \ast \texttt{k} \in \mathsf{range}\ \ast \\ n'\texttt{->t}\mapsto (\texttt{k}, \texttt{v}, l, r')  \ast l \mapsto \texttt{NULL} \ast  r' \mapsto \texttt{NULL} \end{array}\right\}$ 
		//Linearization point
		$\color{specblue} \left\{\begin{array}{l} \texttt{pn} \mapsto (n', n') \ast \nodeboxrep(n') \ast \mathsf{node\_contents}(n', (\texttt{k}, \texttt{v}), \mathsf{range}) \ast \texttt{k} \in \mathsf{range} \end{array}\right\}$ 
	}
	$\color{specblue} \left\{\begin{array}{l} \texttt{pn} \mapsto (n', n') \ast \nodeboxrep(n') \ast \mathsf{R}(n') \end{array}\right\}$ 
	release(pn->n->lock);
	$\color{specblue} \left\{\begin{array}{l}  \texttt{pn} \mapsto (n', n') \ast \nodeboxrep(n') \end{array}\right\}$
	free(pn);
	$\color{specblue} \left\{\begin{array}{l}  \nodeboxrep(n') \end{array}\right\}$
}
