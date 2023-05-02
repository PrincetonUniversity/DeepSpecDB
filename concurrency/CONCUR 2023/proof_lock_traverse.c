int traverse(pn *pn, int k){
		$\color{blue} \left\{\begin{array}{l}  \texttt{flag} = \mathsf{true} \ast  \texttt{pn} \mapsto (\texttt{p, n}) \ast  
				\nodeboxrep(\texttt{n})  \ast \mathsf{R}(\texttt{n}) 		\end{array}\right\} \Rrightarrow \left\{\begin{array}{l} \mathsf{traverse\_inv} \end{array}\right\}$
		for( ; ; ){ 			$\color{blue} \left\{\begin{array}{l} \mathsf{traverse\_inv} \end{array}\right\} $
				pn->p = pn->n;
				$\color{blue} \left\{\begin{array}{l} \texttt{pn} \mapsto (\texttt{n', n'}) \ast  \nodeboxrep(\texttt{n'}) \ast  \texttt{k} \in \mathsf{range} \ast \mathsf{node\_contents}(\texttt{n'}, \mathsf{c}, \mathsf{range})\end{array}\right\}$
				if (pn->p->t == NULL)
						return 1;						
						$\color{violet} \left\{\begin{array}{l} \texttt{pn} \mapsto (\texttt{n', n'}) \ast \nodeboxrep(\texttt{n'}) \ast  \texttt{k} \in \mathsf{range} \ast \mathsf{node\_contents}(\texttt{n'}, \cdot, \mathsf{range}) \end{array}\right\}$
				else{
						$\color{blue} \left\{\begin{array}{l} \texttt{pn} \mapsto (\texttt{n', n'}) \ast  \nodeboxrep(\texttt{n'}) \ast  \texttt{k} \in \mathsf{range} \ast \mathsf{node\_contents}(\texttt{n'}, (\mathsf{k'}, \mathsf{v'}), \mathsf{range})\end{array}\right\}$
						int b = findNext(pn, k);
						$\color{blue} \left\{\begin{array}{l} \exists \  \texttt{n''}. \ \texttt{pn} \mapsto (\texttt{n', n''}) \ast \nodeboxrep(\texttt{n'}) \ast  \texttt{k} \in \mathsf{range} \ast \mathsf{node\_contents}(\texttt{n'}, (\mathsf{k'}, \mathsf{v'}), \mathsf{range})\ \ast\\ 
						((\texttt{b} = 0 \ast \mathsf{k'} = \mathsf{k} \ast \texttt{n''} = \texttt{n'})  \lor 						 (\texttt{b} = 1  \ast \texttt{k} \in \mathsf{range}(\texttt{n''}) \ast \nodeboxrep(\texttt{n''})))   \end{array}\right\}$
						if (b == 0){
								$\color{blue} \left\{\begin{array}{l} 
								\texttt{pn} \mapsto (\texttt{n', n'}) \ast \mathsf{k' = \texttt{k}} \ast \cdots    \end{array}\right\}$
								return 0;
								$\color{violet} \left\{\begin{array}{l} 
								\texttt{pn} \mapsto (\texttt{n', n'}) \ast \nodeboxrep(\texttt{n'}) \ast  \texttt{k} \in \mathsf{range'} \ast \mathsf{node\_contents}(\texttt{n'}, (\texttt{k}, \mathsf{v'}), \mathsf{range'})    \end{array}\right\}$
						}
						else{
								$\color{blue} \left\{\begin{array}{l} \texttt{pn} \mapsto (\texttt{n', n''}) \ast \nodeboxrep(\texttt{n'}) \ast  \texttt{k} \in \mathsf{range}(\texttt{n''}) \ast \mathsf{R}(\texttt{n'}) \ast \nodeboxrep(\texttt{n''})    \end{array}\right\}$
								acquire(pn->n->lock);
								$\color{blue} \left\{ \cdots \ast \mathsf{R}(\texttt{n''})\right\}$
								release(pn->p->lock);
								$\color{blue} \left\{\begin{array}{l} \texttt{pn} \mapsto (\texttt{n', n''}) \ast \texttt{k} \in \mathsf{range}(\texttt{n''}) \ast \nodeboxrep(\texttt{n''}) \ast \mathsf{R}(\texttt{n''})    \end{array}\right\}$
						}
				}
		}
}