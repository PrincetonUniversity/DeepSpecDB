int traverse(pn *pn, int k){
	node_t *r = (pn->n); $\color{specblue} \left\{\begin{array}{l}  \texttt{pn} \mapsto (\texttt{\_, r}) \ast  
				\inFP (\texttt{r}) \end{array}\right\} \Rrightarrow \left\{\begin{array}{l} \mathsf{traverse\_inv}(\texttt{pn}) \end{array}\right\}$
	for( ; ; ){ 			$\color{specblue} \left\{\begin{array}{l} \mathsf{traverse\_inv} \end{array}\right\} \triangleq \left\{\begin{array}{l} 
		\exists\ n'.\ \texttt{pn} \mapsto (\texttt{\_}, n') \ast \inFP (n') \ast \inFP (\texttt{r})
		 \end{array}\right\}$
		acquire(pn->n->lock);
		$\color{specblue} \left\{\begin{array}{l} \texttt{pn} \mapsto (\texttt{\_}, n') \ast \inFP (n') \ast \mathsf{R}(n') \ast \inFP (\texttt{r}) \end{array}\right\}$
		pn->p = pn->n; $\color{specblue} \left\{\begin{array}{l} \texttt{pn} \mapsto (n', n') \ast \inFP (n') \ast \mathsf{R}(n') \ast \inFP (\texttt{r}) \end{array}\right\}$
		if (inRange(pn, k) == 1){
			$\color{specblue} \left\{\begin{array}{l} \texttt{k} \in \mathsf{range} \ast \texttt{pn} \mapsto (n', n') \ast \inFP (n') \ast \mathsf{node\_contents}(n', c, \mathsf{range}) \ast \inFP (\texttt{r}) \end{array}\right\}$
			if (pn->p->t == NULL)
				return 1;
				$\color{purple!40!black} \left\{\begin{array}{l} \texttt{k} \in \mathsf{range} \ast \texttt{pn} \mapsto (n', n') \ast \inFP (n') \ast \mathsf{node\_contents}(n', \cdot, \mathsf{range}) \end{array}\right\}$
			else{
				$\color{specblue} \left\{\begin{array}{l} \texttt{k} \in \mathsf{range} \ast \texttt{pn} \mapsto (n', n') \ast \inFP (n') \ast \mathsf{node\_contents}(n', (k', v'), \mathsf{range}) \ast \inFP (\texttt{r}) \end{array}\right\}$
				int b = findNext(pn, k);
				$\color{specblue} \left\{\begin{array}{l} \exists \  n''. \ \texttt{pn} \mapsto (n', n'') \ast \inFP (n') \ast  \texttt{k} \in \mathsf{range} \ast \mathsf{node\_contents}(n', (k', v'), \mathsf{range})\ \ast \\\inFP (\texttt{r}) \ast
						((\texttt{b} = 0 \ast k' = \texttt{k} \ast n'' = n')  \lor 						 (\texttt{b} = 1  \ast \inFP (n'')))   \end{array}\right\}$
				if (b == 0){
					$\color{specblue} \left\{\begin{array}{l} 
								\texttt{pn} \mapsto (n', n') \ast k' = \texttt{k} \ast \cdots    \end{array}\right\}$
					return 0;
					$\color{purple!40!black} \left\{\begin{array}{l} \texttt{pn} \mapsto (n', n') \ast \inFP (n') \ast  \texttt{k} \in \mathsf{range'} \ast \mathsf{node\_contents}(n', (\texttt{k}, v'), \mathsf{range})   \end{array}\right\}$
				}
				else{
					$\color{specblue} \left\{\begin{array}{l} \texttt{pn} \mapsto (n', n'') \ast \inFP (n') \ast  \texttt{k} \in \mathsf{range} \ast \mathsf{node\_contents}(n',(k', v'), \mathsf{range})\ \ast\\ \inFP (n'') \ast \inFP (\texttt{r})   \end{array}\right\}$
					release(pn->p->lock);
					$\color{specblue} \left\{\begin{array}{l} \texttt{pn} \mapsto (n', n'') \ast \inFP (n') \ast  \texttt{k} \in \mathsf{range} \ast \inFP (n'') \ast \inFP (\texttt{r})\end{array}\right\}$
				}
			}
		}
		else{
			$\color{specblue} \left\{\begin{array}{l} \texttt{pn} \mapsto (n', n') \ast \inFP (n') \ast \mathsf{R}(n') \ast \inFP (\texttt{r})\end{array}\right\}$
			release(pn->p->lock);
			$\color{specblue} \left\{\begin{array}{l} \texttt{pn} \mapsto (n', n') \ast \inFP (n') \ast \inFP (\texttt{r}) \end{array}\right\}$
			pn->n = r;
			$\color{specblue} \left\{\begin{array}{l} \texttt{pn} \mapsto (n', \texttt{r}) \ast \inFP (\texttt{r})   \end{array}\right\}$
		}
	}
}
