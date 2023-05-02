int traverse(pn *pn, int k){
		node_t *r = (pn->n); $\color{blue} \left\{\begin{array}{l}  \texttt{pn} \mapsto (\texttt{\_, r}) \ast  
\infp (\texttt{r}) \end{array}\right\} \Rrightarrow \left\{\begin{array}{l} \mathsf{traverse\_inv} \end{array}\right\}$
		for( ; ; ){ 			$\color{blue} \left\{\begin{array}{l} \mathsf{traverse\_inv} \end{array}\right\} \triangleq \left\{\begin{array}{l} 
			\exists\ \texttt{n'}.\ \texttt{pn} \mapsto (\texttt{\_, n'}) \ast \infp (\texttt{n'}) \ast \infp (\texttt{r})
		 \end{array}\right\}$
				acquire(pn->n->lock);
				$\color{blue} \left\{\begin{array}{l} \texttt{pn} \mapsto (\texttt{\_, n'}) \ast \infp (\texttt{n'}) \ast \mathsf{R}(\texttt{n'}) \ast \infp (\texttt{r}) \end{array}\right\}$
				pn->p = pn->n; $\color{blue} \left\{\begin{array}{l} \texttt{pn} \mapsto (\texttt{n', n'}) \ast \infp (\texttt{n'}) \ast \mathsf{R}(\texttt{n'}) \ast \infp (\texttt{r}) \end{array}\right\}$
				if (inRange(pn, k) == 1){
				$\color{blue} \left\{\begin{array}{l} \texttt{k} \in \mathsf{range'} \ast \texttt{pn} \mapsto (\texttt{n', n'}) \ast \infp (\texttt{n'}) \ast \mathsf{node\_contents}(\texttt{n'}, \mathsf{k'}, \mathsf{v'}, \mathsf{range'}) \ast \infp (\texttt{r}) \end{array}\right\}$
						if (pn->p->t == NULL)
								return 1;
								$\color{violet} \left\{\begin{array}{l} \texttt{k} \in \mathsf{range'} \ast \texttt{pn} \mapsto (\texttt{n', n'}) \ast \texttt{n'->t} = \texttt{NULL} \ast \infp (\texttt{n'}) \ast \mathsf{node\_contents}(\texttt{n'}, \mathsf{k'}, \mathsf{v'}, \mathsf{range'}) \end{array}\right\}$
						else{
								int b = findNext(pn, k);
								$\color{blue} \left\{\begin{array}{l} \exists \  \texttt{n''}. \ \texttt{pn} \mapsto (\texttt{n', n''}) \ast \infp (\texttt{n'}) \ast  \texttt{k} \in \mathsf{range'} \ast \mathsf{node\_contents}(\mathsf{k'}, \mathsf{v'}, \mathsf{range'})\ast \infp (\texttt{r})\ \ast\\ 
						((\texttt{b} = 0 \ast \mathsf{k'} = \mathsf{k} \ast \texttt{n''} = \texttt{n'})  \lor 						 (\texttt{b} = 1  \ast \infp (n'')))   \end{array}\right\}$
								if (b == 0){
										$\color{blue} \left\{\begin{array}{l} 
								\texttt{pn} \mapsto (\texttt{n', n'}) \ast \mathsf{k' = \texttt{k}} \ast \cdots    \end{array}\right\}$
										return 0;
										$\color{violet} \left\{\begin{array}{l} \texttt{pn} \mapsto (\texttt{n', n'}) \ast \infp (\texttt{n'}) \ast  \texttt{k} \in \mathsf{range'} \ast \mathsf{node\_contents}(\texttt{k}, \mathsf{v'}, \mathsf{range'})   \end{array}\right\}$
								}
								else
										$\color{blue} \left\{\begin{array}{l} \texttt{pn} \mapsto (\texttt{n', n''}) \ast \infp (\texttt{n'}) \ast  \texttt{k} \in \mathsf{range'} \ast \mathsf{node\_contents}(\mathsf{k'}, \mathsf{v'}, \mathsf{range'}) \ast \infp (\texttt{n''}) \ast \infp (\texttt{r})   \end{array}\right\}$
										release(pn->p->lock);
										$\color{blue} \left\{\begin{array}{l} \texttt{pn} \mapsto (\texttt{n', n''}) \ast \infp (\texttt{n'}) \ast  \texttt{k} \in \mathsf{range'} \ast \infp (\texttt{n''}) \ast \infp (\texttt{r})\end{array}\right\}$
						}
				}
				else{
						$\color{blue} \left\{\begin{array}{l} \texttt{pn} \mapsto (\texttt{n', n'}) \ast \infp (\texttt{n'}) \ast \mathsf{R}(\texttt{n'}) \ast \infp (\texttt{r})\end{array}\right\}$
						release(pn->p->lock);
						$\color{blue} \left\{\begin{array}{l} \texttt{pn} \mapsto (\texttt{n', n'}) \ast \infp (\texttt{n'}) \ast \infp (\texttt{r}) \end{array}\right\}$
						pn->n = r;
						$\color{blue} \left\{\begin{array}{l} \texttt{pn} \mapsto (\texttt{n', r}) \ast \infp (\texttt{r})   \end{array}\right\}$
				}
		}
}