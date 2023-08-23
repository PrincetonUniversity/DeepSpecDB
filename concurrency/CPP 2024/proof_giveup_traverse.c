int traverse(pn *pn, int k){
		node_t *r = (pn->n); $\color{blue} \left\{\begin{array}{l}  \texttt{pn} \mapsto (\texttt{\_, r}) \ast  
\infp (\texttt{r}) \end{array}\right\} \Rrightarrow \left\{\begin{array}{l} \mathsf{traverse\_inv} \end{array}\right\}$
		for( ; ; ){ 			$\color{blue} \left\{\begin{array}{l} \mathsf{traverse\_inv} \end{array}\right\} \triangleq \left\{\begin{array}{l} 
			\exists\ n'.\ \texttt{pn} \mapsto (\texttt{\_}, n') \ast \infp (n') \ast \infp (\texttt{r})
		 \end{array}\right\}$
				acquire(pn->n->lock);
				$\color{blue} \left\{\begin{array}{l} \texttt{pn} \mapsto (\texttt{\_}, n') \ast \infp (n') \ast \mathsf{R}(n') \ast \infp (\texttt{r}) \end{array}\right\}$
				pn->p = pn->n; $\color{blue} \left\{\begin{array}{l} \texttt{pn} \mapsto (n', n') \ast \infp (n') \ast \mathsf{R}(n') \ast \infp (\texttt{r}) \end{array}\right\}$
				if (inRange(pn, k) == 1){
						$\color{blue} \left\{\begin{array}{l} \texttt{k} \in \mathsf{range} \ast \texttt{pn} \mapsto (n', n') \ast \infp (n') \ast \mathsf{node\_contents}(n', c, \mathsf{range}) \ast \infp (\texttt{r}) \end{array}\right\}$
						if (pn->p->t == NULL)
								return 1;
								$\color{violet} \left\{\begin{array}{l} \texttt{k} \in \mathsf{range} \ast \texttt{pn} \mapsto (n', n') \ast \infp (n') \ast \mathsf{node\_contents}(n', \cdot, \mathsf{range}) \end{array}\right\}$
						else{
								$\color{blue} \left\{\begin{array}{l} \texttt{k} \in \mathsf{range} \ast \texttt{pn} \mapsto (n', n') \ast \infp (n') \ast \mathsf{node\_contents}(n', (k', v'), \mathsf{range}) \ast \infp (\texttt{r}) \end{array}\right\}$
								int b = findNext(pn, k);
								$\color{blue} \left\{\begin{array}{l} \exists \  n''. \ \texttt{pn} \mapsto (n', n'') \ast \infp (n') \ast  \texttt{k} \in \mathsf{range} \ast \mathsf{node\_contents}(n', (k', v'), \mathsf{range})\ \ast \\\infp (\texttt{r}) \ast
						((\texttt{b} = 0 \ast k' = \texttt{k} \ast n'' = n')  \lor 						 (\texttt{b} = 1  \ast \infp (n'')))   \end{array}\right\}$
								if (b == 0){
										$\color{blue} \left\{\begin{array}{l} 
								\texttt{pn} \mapsto (n', n') \ast k' = \texttt{k} \ast \cdots    \end{array}\right\}$
										return 0;
										$\color{violet} \left\{\begin{array}{l} \texttt{pn} \mapsto (n', n') \ast \infp (n') \ast  \texttt{k} \in \mathsf{range'} \ast \mathsf{node\_contents}(n', (\texttt{k}, v'), \mathsf{range})   \end{array}\right\}$
								}
								else
										$\color{blue} \left\{\begin{array}{l} \texttt{pn} \mapsto (n', n'') \ast \infp (n') \ast  \texttt{k} \in \mathsf{range} \ast \mathsf{node\_contents}(n',(k', v'), \mathsf{range})\ \ast\\ \infp (n'') \ast \infp (\texttt{r})   \end{array}\right\}$
										release(pn->p->lock);
										$\color{blue} \left\{\begin{array}{l} \texttt{pn} \mapsto (n', n'') \ast \infp (n') \ast  \texttt{k} \in \mathsf{range} \ast \infp (n'') \ast \infp (\texttt{r})\end{array}\right\}$
						}
				}
				else{
						$\color{blue} \left\{\begin{array}{l} \texttt{pn} \mapsto (n', n') \ast \infp (n') \ast \mathsf{R}(n') \ast \infp (\texttt{r})\end{array}\right\}$
						release(pn->p->lock);
						$\color{blue} \left\{\begin{array}{l} \texttt{pn} \mapsto (n', n') \ast \infp (n') \ast \infp (\texttt{r}) \end{array}\right\}$
						pn->n = r;
						$\color{blue} \left\{\begin{array}{l} \texttt{pn} \mapsto (n', \texttt{r}) \ast \infp (\texttt{r})   \end{array}\right\}$
				}
		}
}
