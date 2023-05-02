int traverse(pn *pn, int k){
		int flag = 1; 			$\color{blue} \left\{\begin{array}{l}  \mathit{res} = \mathsf{true} \ast  \texttt{pn} \mapsto (\texttt{p, n}) \ast  
				\nodeboxrep(\texttt{n})  \ast \mathsf{R}(\texttt{n})  \ast \treerep\ m 		\end{array}\right\} \Rrightarrow \left\{\begin{array}{l} \mathsf{traverse\_inv} \end{array}\right\}$
		for( ; ; ){ 			$\color{blue} \left\{\begin{array}{l} \mathsf{traverse\_inv} \end{array}\right\} \triangleq \left\{\begin{array}{l} 
			\texttt{pn} \mapsto (\texttt{p, n}) \ast  \nodeboxrep(\texttt{n}) \ast  \mathsf{R}(\texttt{n}) \ast \texttt{k} \in \mathsf{range}(\texttt{n}) \ast \treerep\ m
		 \end{array}\right\}$
				pn->p = pn->n;
				$\color{blue} \left\{\begin{array}{l} \texttt{pn} \mapsto (\texttt{n, n}) \ast  \nodeboxrep(\texttt{n}) \ast  \mathsf{R}(\texttt{n}) \ast \texttt{k} \in \mathsf{range}(\texttt{n}) \ast \treerep\ m\end{array}\right\}$
				if (pn->p->t == NULL)
						break;
						$\color{violet} \left\{\begin{array}{l} \mathit{res} = \mathsf{true} \ast \texttt{pn} \mapsto (\texttt{n, n}) \ast \texttt{n->t} = \texttt{NULL}  \ast \texttt{n->lock} \lockvar \mathsf{R}(\texttt{n}) \ast \mathsf{R}(\texttt{n}) \ast \texttt{k} \in \mathsf{range}(\texttt{n}) \ast \cdots \end{array}\right\}$
				else{
						int b = findNext(pn, k);
						$\color{blue} \left\{\begin{array}{l} \exists \  \texttt{n'}. \ \texttt{pn} \mapsto (\texttt{n, n}) \ast \texttt{n->t} \neq \texttt{NULL} \ast \texttt{n->lock} \lockvar \mathsf{R}(\texttt{n}) \ast \mathsf{R}(\texttt{n}) \ast\\ 
						((\mathit{res'} = \mathsf{false} \ast \texttt{k} \in \mathsf{range}(\texttt{n}) \ast \cdots )\  \lor \\ 
						\ (\mathit{res'} = \mathsf{true}  \ast  \texttt{n->t} \mapsto \texttt{n'} \ast \texttt{n'->lock} \lockvar \mathsf{R}(\texttt{n'}) \ast \texttt{k} \in \mathsf{range}(\texttt{n'}) \ast \cdots))   \end{array}\right\}$
						if (b == 0){
								$\color{blue} \left\{\begin{array}{l} 
								\mathit{res'} = \mathsf{false} \ast \texttt{pn} \mapsto (\texttt{n, n}) \ast \texttt{n->t} \neq \texttt{NULL} \ast \\ \texttt{n->lock} \lockvar \mathsf{R}(\texttt{n}) \ast \mathsf{R}(\texttt{n}) \ast \texttt{k} \in \mathsf{range}(\texttt{n}) \ast \cdots    \end{array}\right\}$
								flag = 0;
								$\color{blue} \left\{\begin{array}{l} 
								\mathit{res} = \mathsf{false} \ast \mathit{res'} = \mathsf{false} \ast \texttt{pn} \mapsto (\texttt{n, n}) \ast \texttt{n->t} \neq \texttt{NULL} \ast \\ \texttt{n->lock} \lockvar \mathsf{R}(\texttt{n}) \ast \mathsf{R}(\texttt{n}) \ast \texttt{k} \in \mathsf{range}(\texttt{n}) \ast \cdots    \end{array}\right\}$
								break;
								$\color{violet} \left\{\begin{array}{l} 
								\mathit{res} = \mathsf{false} \ast \texttt{pn} \mapsto (\texttt{n, n}) \ast \texttt{n->t} \neq \texttt{NULL} \ast \texttt{n->lock} \lockvar \mathsf{R}(\texttt{n}) \ast \mathsf{R}(\texttt{n}) \ast \texttt{k} \in \mathsf{range}(\texttt{n}) \ast \cdots    \end{array}\right\}$
						}
						else{
								$\color{blue} \left\{\begin{array}{l} \mathit{res} = \mathsf{true} \ast \texttt{pn} \mapsto (\texttt{n, n}) \ast  \texttt{n->lock} \lockvar \mathsf{R}(\texttt{n}) \ast \mathsf{R}(\texttt{n}) \ast \\ \texttt{n->t} \mapsto \texttt{n'} \ast \texttt{n'->lock} \lockvar \mathsf{R}(\texttt{n'}) \ast \texttt{k} \in \mathsf{range}(\texttt{n'}) \ast\cdots    \end{array}\right\}$
								acquire(pn->n->lock);
								$\color{blue} \left\{\begin{array}{l} \mathit{res} = \mathsf{true} \ast \texttt{pn} \mapsto (\texttt{n, n}) \ast  \texttt{n->lock} \lockvar \mathsf{R}(\texttt{n}) \ast \mathsf{R}(\texttt{n}) \ast \\ \texttt{n->t} \mapsto \texttt{n'} \ast \texttt{n'->lock} \lockvar \mathsf{R}(\texttt{n'}) \ast \mathsf{R}(\texttt{n'}) \ast \cdots    \end{array}\right\}$
								release(pn->p->lock);
								$\color{blue} \left\{\begin{array}{l} \mathit{res} = \mathsf{true} \ast \texttt{pn} \mapsto (\texttt{n, n}) \ast  \texttt{n->lock} \lockvar \mathsf{R}(\texttt{n}) \ast \\ \texttt{n->t} \mapsto \texttt{n'} \ast \texttt{n'->lock} \lockvar \mathsf{R}(\texttt{n'}) \ast \mathsf{R}(\texttt{n'}) \ast \cdots    \end{array}\right\}$
						}
				}
		}
		return flag;
		$\color{blue} \left\{\begin{array}{l} (\mathit{res} = \mathsf{false} \ast \texttt{pn} \mapsto (\texttt{p', p'}) \ast \texttt{p'->t} \neq \texttt{NULL} \ast \texttt{p'->lock} \lockvar \mathsf{R}(\texttt{p'}) \ast \mathsf{R}(\texttt{p'}) \ast \texttt{k} \in \mathsf{range}(\texttt{p'}) \ast \cdots) \  \lor \\
		(\mathit{res} =\mathsf{true} \ast \texttt{pn} \mapsto (\texttt{p', p'}) \ast \texttt{p'->t} = \texttt{NULL}  \ast \texttt{p'->lock} \lockvar \mathsf{R}(\texttt{p'}) \ast \mathsf{R}(\texttt{p'}) \ast \texttt{k} \in \mathsf{range}(\texttt{p'}) \ast \cdots)
		\end{array}\right\}$
}