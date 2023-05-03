int traverse(pn *pn, int k){
		$\color{blue} \left\{\begin{array}{l}  \texttt{pn} \mapsto (p, n) \ast  
				\nodeboxrep(n)  \ast \mathsf{R}(n) 		\end{array}\right\} \Rrightarrow \left\{\begin{array}{l} \mathsf{traverse\_inv} \end{array}\right\}$
		for( ; ; ){ 			$\color{blue} \left\{\begin{array}{l} \mathsf{traverse\_inv} \end{array}\right\} $
				pn->p = pn->n;
				$\color{blue} \left\{\begin{array}{l} \texttt{pn} \mapsto (n', n') \ast  \nodeboxrep(n') \ast  \texttt{k} \in \mathsf{range} \ast \mathsf{node\_contents}(n', c, \mathsf{range})\end{array}\right\}$
				if (pn->p->t == NULL)
						return 1;						
						$\color{violet} \left\{\begin{array}{l} \texttt{pn} \mapsto (n', n') \ast \nodeboxrep(n') \ast  \texttt{k} \in \mathsf{range} \ast \mathsf{node\_contents}(n', \cdot, \mathsf{range}) \end{array}\right\}$
				else{
						$\color{blue} \left\{\begin{array}{l} \texttt{pn} \mapsto (n', n') \ast  \nodeboxrep(n') \ast  \texttt{k} \in \mathsf{range} \ast \mathsf{node\_contents}(n', (k', v'), \mathsf{range})\end{array}\right\}$
						int b = findNext(pn, k);
						$\color{blue} \left\{\begin{array}{l} \exists \  n''. \ \texttt{pn} \mapsto (n', n'') \ast \nodeboxrep(n') \ast  \texttt{k} \in \mathsf{range} \ast \mathsf{node\_contents}(n', (k', v'), \mathsf{range})\ \ast\\ 
						((\texttt{b} = 0 \ast k' = \texttt{k} \ast n'' = n')  \lor 						 (\texttt{b} = 1  \ast \texttt{k} \in \mathsf{range}(n'') \ast \nodeboxrep(n'')))   \end{array}\right\}$
						if (b == 0){
								$\color{blue} \left\{\begin{array}{l} 
								\texttt{pn} \mapsto (n', n') \ast k' = \texttt{k} \ast \cdots    \end{array}\right\}$
								return 0;
								$\color{violet} \left\{\begin{array}{l} 
								\texttt{pn} \mapsto (n', n') \ast \nodeboxrep(n') \ast  \texttt{k} \in \mathsf{range'} \ast \mathsf{node\_contents}(n', (\texttt{k}, v'), \mathsf{range'})    \end{array}\right\}$
						}
						else{
								$\color{blue} \left\{\begin{array}{l} \texttt{pn} \mapsto (n', n'') \ast \nodeboxrep(n') \ast  \texttt{k} \in \mathsf{range}(n'') \ast \mathsf{R}(n') \ast \nodeboxrep(n'')    \end{array}\right\}$
								acquire(pn->n->lock);
								$\color{blue} \left\{ \begin{array}{l}\texttt{pn} \mapsto (n', n'') \ast \nodeboxrep(n') \ast  \texttt{k} \in \mathsf{range}(n'') \ast \mathsf{R}(n') \ast \nodeboxrep(n'') \ast \mathsf{R}(n'')\end{array}\right\}$
								release(pn->p->lock);
								$\color{blue} \left\{\begin{array}{l} \texttt{pn} \mapsto (n', n'') \ast \texttt{k} \in \mathsf{range}(n'') \ast \nodeboxrep(n'') \ast \mathsf{R}(n'')    \end{array}\right\}$
						}
				}
		}
}
