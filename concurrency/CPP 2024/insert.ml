let insert r k =
    lockNode r;
    let n = traverse r k in
    let res = insertOp n k in
    unlockNode n; 
    res