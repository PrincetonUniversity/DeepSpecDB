void insert (node_t **r, int k, void *v){
		struct pn *pn = (struct pn *) surely_malloc (sizeof *pn);
		pn->n = *r;
		$\color{blue} \left\{\begin{array}{l} \texttt{pn} \mapsto (\texttt{p, r}) \ast  \infp(\texttt{r}) \ast \treerep\ m \end{array}\right\}$
		if (traverse(pn, k) == 0){
				$\color{blue} \left\{\begin{array}{l}  \mathit{res} = \mathsf{false} \ast \texttt{pn} \mapsto (\texttt{p', p'}) \ast \texttt{p'->t} \neq \texttt{NULL}  \ast \infp (\texttt{p'}) \ast \mathsf{R}(\texttt{p'}) \ast \texttt{k} \in \mathsf{range}(\texttt{p'}) \ast \cdots \end{array}\right\}$
				pn->p->t->value = v;
				$\color{blue} \left\{\begin{array}{l}  \mathit{res} = \mathsf{false} \ast \texttt{pn} \mapsto (\texttt{p', p'}) \ast \infp (\texttt{p'}) \ast \texttt{p'->t->value} \mapsto \texttt{v} \ast \cdots \end{array}\right\} \Rrightarrow{\textbf{commit}}$ 
				//Linearization point
				$\color{blue} \left\{\begin{array}{l}  \texttt{pn} \mapsto (\texttt{p', p'}) \ast \infp (\texttt{p'}) \ast \mathsf{R}(\texttt{p'}) \ast \cdots \end{array}\right\}$
		}
		else{
				$\color{blue} \left\{\begin{array}{l}  \mathit{res} = \mathsf{true} \ast \texttt{pn} \mapsto (\texttt{p', p'}) \ast \texttt{p'->t} = \texttt{NULL}  \ast \infp (\texttt{p'}) \ast \mathsf{R}(\texttt{p'}) \ast \texttt{k} \in \mathsf{range}(\texttt{p'}) \ast \cdots \end{array}\right\}$
				insertOp(pn, k, v);
				$\color{blue} \left\{\begin{array}{l}  \mathit{res} =\mathsf{true} \ast \texttt{pn} \mapsto (\texttt{p', p'}) \ast  \infp (\texttt{p'}) \ast \\ \texttt{p'->t}\mapsto (\texttt{k, v', l, r})  \ast \texttt{l} \mapsto \texttt{NULL} \ast  \texttt{r} \mapsto \texttt{NULL} \ast \cdots \end{array}\right\} \Rrightarrow{\textbf{commit}}$ 
				//Linearization point
				$\color{blue} \left\{\begin{array}{l}  \texttt{pn} \mapsto (\texttt{p', p'}) \ast \infp (\texttt{p'}) \ast \mathsf{R}(\texttt{p'}) \ast \cdots \end{array}\right\}$
		}
		release(pn->n->lock);
		$\color{blue} \left\{\begin{array}{l}  \texttt{pn} \mapsto (\texttt{p', p'}) \ast \infp (\texttt{p'}) \ast \cdots \end{array}\right\}$
		free(pn);
		$\color{blue} \left\{\begin{array}{l} \infp (\texttt{p'}) \ast \cdots \end{array}\right\}$
}