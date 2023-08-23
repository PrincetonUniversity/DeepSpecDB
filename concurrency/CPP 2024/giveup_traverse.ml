let rec traverse r n k =
  lockNode n;
  if inRange n k then
    match findNext n k with 
    | None -> n
    | Some n' -> unlockNode n;
        traverse n' k
  else
    unlockNode n;
    traverse r r k 