let rec traverse p n k = 
  match findNext n k with 
  | None -> (p, n)
  | Some n' -> 
      lockNode n;
      unlockNode p;
      traverse n n' k