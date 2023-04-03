let rec traverse p n k = 
    match findNext n k with 
    | None -> (p, n)
    | Some n' -> 
        unlockNode p;
        lockNode n;
        traverse n n' k 