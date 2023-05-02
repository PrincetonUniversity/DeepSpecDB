void insert (node_t **r, int k, void *v){
		struct pn *pn = (struct pn *) surely_malloc (sizeof *pn);
		pn->n = *r;
		$\color{blue} \left\{\begin{array}{l} \texttt{pn} \mapsto (\texttt{\_, r}) \ast  \infp(\texttt{r}) \end{array}\right\}$
		if (traverse(pn, k) == 0){
				$\color{blue} \left\{\begin{array}{l}  \exists\ \texttt{n'}.\ \texttt{pn} \mapsto (\texttt{n', n'}) \ast \infp(\texttt{n'}) \ast \mathsf{node\_contents}(\texttt{n'}, (\texttt{k}, \mathsf{v'}), \mathsf{range'}) \end{array}\right\}$
				pn->p->t->value = v;
				$\color{blue} \left\{\begin{array}{l}  \texttt{pn} \mapsto (\texttt{n', n'}) \ast \nodeboxrep(\texttt{n'}) \ast \mathsf{node\_contents}(\texttt{n'}, (\texttt{k}, \texttt{v}), \mathsf{range'}) \end{array}\right\} \Rrightarrow{\textbf{commit}}$ 
				//Linearization point
		}
		else{
				$\color{blue} \left\{\begin{array}{l}  \exists\ \texttt{n'}.\ \texttt{pn} \mapsto (\texttt{n', n'}) \ast \texttt{n'->t} = \texttt{NULL}  \ast \infp(\texttt{n'}) \ast \mathsf{node\_contents}(\texttt{n'}, \cdot, \mathsf{range'}) \ast \texttt{k} \in \mathsf{range'} \end{array}\right\}$
				insertOp(pn, k, v);
				$\color{blue} \left\{\begin{array}{l}  \texttt{pn} \mapsto (\texttt{n', n'}) \ast \infp(\texttt{n'}) \ast \mathsf{node\_contents}(\texttt{n'}, \cdot, \mathsf{range'}) \ast \texttt{k} \in \mathsf{range'}\ \ast \\ \texttt{n'->t}\mapsto (\texttt{k, v, l, r})  \ast \texttt{l} \mapsto \texttt{NULL} \ast  \texttt{r} \mapsto \texttt{NULL} \end{array}\right\}$ 
				//Linearization point
				$\color{blue} \left\{\begin{array}{l} \texttt{pn} \mapsto (\texttt{n', n'}) \ast \infp(\texttt{n'}) \ast \mathsf{node\_contents}(\texttt{n'}, (\texttt{k}, \texttt{v}), \mathsf{range'}) \ast \texttt{k} \in \mathsf{range'} \end{array}\right\}$ 
		}
		$\color{blue} \left\{\begin{array}{l} \texttt{pn} \mapsto (\texttt{n', n'}) \ast \infp(\texttt{n'}) \ast \mathsf{R}(\texttt{n'}) \end{array}\right\}$ 
		release(pn->n->lock);
		$\color{blue} \left\{\begin{array}{l}  \texttt{pn} \mapsto (\texttt{n', n'}) \ast \infp(\texttt{n'}) \end{array}\right\}$
		free(pn);
		$\color{blue} \left\{\begin{array}{l} \infp (\texttt{n'}) \end{array}\right\}$
}