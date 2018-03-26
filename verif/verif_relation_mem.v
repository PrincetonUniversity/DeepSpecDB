(** * verif_relation_mem.v: Correctness proof of relation_mem.c *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import relation_mem.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import VST.msl.wand_frame.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.
Require Import FunInd.

(**
    BTREES FORMAL MODEL
**)

Definition Fanout := 15%nat.
Definition MaxTreeDepth := 20%nat.

Definition key := Z.            (* unsigned long in C *)
Definition V:Type := Z.         (* I need some type for value_rep *)
Variable b : nat.
Variable X:Type.                (* val or unit *)

Inductive entry (X:Type): Type :=
     | keyval: key -> V -> X -> entry X
     | keychild: key -> node X -> entry X
with node (X:Type): Type :=
     | btnode: option (node X) -> listentry X -> bool -> X -> node X
with listentry (X:Type): Type :=
     | nil: listentry X
     | cons: entry X -> listentry X -> listentry X.

Inductive index: Type :=
| im: index
| ip: nat -> index.

Definition nat_to_index (n:nat) := ip n.

Definition cursor (X:Type): Type := list (node X * index). (* ancestors and index *)
Definition relation (X:Type): Type := node X * nat * X.  (* root and numRecords *)

Definition next_index (i:index) : index :=
  match i with
  | im => ip (O%nat)
  | ip n => ip (S n)
  end.

Fixpoint max_nat (m : nat) (n : nat) : nat :=
  match m with
  | O => n
  | S m' => (match n with
             | O => m
             | S n' => S (max_nat m' n')
             end)
  end.

Lemma max_0: forall a, max_nat a 0 = a.
Proof. induction a. auto. simpl. auto. Qed.

Theorem le_max_split_l: forall n a b,
    (n < a)%nat -> (n< max_nat a b)%nat.
Proof.
  intros.
  generalize dependent n.
  generalize dependent b0.
  generalize dependent a.
  induction a; intros.
  - inversion H.
  - destruct b0.
    + rewrite max_0. auto.
    + simpl. destruct n. omega.
      assert (n<a)%nat by omega. apply IHa with (b0:=b0) in H0. omega.
Qed.      

Theorem max_flip: forall a b, max_nat a b = max_nat b a.
Proof.
  induction a; intros.
  - simpl. rewrite max_0. auto.
  - simpl. destruct b0.
    + simpl. auto.
    + simpl. rewrite IHa. auto.
Qed.    

Theorem le_max_split_r: forall n a b,
    (n < b)%nat -> (n< max_nat a b)%nat.
Proof.
  intros. rewrite max_flip. apply le_max_split_l. auto.
Qed.
  
Definition max_index (i1:index) (i2:index): index :=
  match i1 with
  | im => i2
  | ip n1 => match i2 with
            | im => i1
            | ip n2 => ip (max_nat n1 n2)
             end
  end.

Fixpoint node_depth {X:Type} (n:node X) : nat :=
  match n with
    btnode ptr0 le _ _ => max_nat (listentry_depth le)
                                (match ptr0 with
                                 | None => O
                                 | Some n' => S (node_depth n') end)
  end
with listentry_depth {X:Type} (le:listentry X) : nat :=
       match le with
       | nil => O
       | cons e le' => max_nat (entry_depth e) (listentry_depth le')
       end
with entry_depth {X:Type} (e:entry X) : nat :=
       match e with
       | keyval _ _ _ => S O
       | keychild _ n => S (node_depth n)
       end.                                                 

Fixpoint nth_entry_le {X:Type} (i:nat) (le:listentry X): option (entry X) :=
  match i with
  | O => match le with
         | nil => None
         | cons e _ => Some e
         end
  | S i' => match le with
            | nil => None
            | cons _ le' => nth_entry_le i' le'
            end
  end.                          (* USEFUL? *)

Fixpoint move_to_first {X:Type} (c:cursor X) (curr:node X): cursor X:=
  match curr with btnode ptr0 le _ _ =>
                  match ptr0 with
                  | Some n => move_to_first ((curr,im)::c) n
                  | None => match le with
                            | nil => c (* possible? *)
                            | cons e le' => match e with
                                            | keyval _ _ _ => ((curr,ip (0%nat))::c)
                                            | keychild _ _ => c (* not possible, we would have a ptr0 otherwise *)
                                            end
                            end
                  end
  end.

Fixpoint le_length {X:Type} (le:listentry X) : nat :=
  match le with
  | nil => O
  | cons _ le' => S (le_length le')
  end.

Definition node_length {X:Type} (n:node X) : nat :=
  match n with btnode ptr0 le _ _ => le_length le end.

Definition index_leb_nat (i:index) (n:nat) : bool :=
  match i with
  | im => true
  | ip n' => (n' <=? n)%nat
  end.

Fixpoint move_to_next_partial {X:Type} (c:cursor X) : cursor X :=
  match c with
  | [] => []
  | (n,i)::c' =>
    match (index_leb_nat i (node_length n -2)) with 
    | true => (n,next_index i)::c'
    | false => move_to_next_partial c'
    end
  end.

Fixpoint nth_node_le {X:Type} (i:nat) (le:listentry X): option (node X) :=
  match i with
  | O => match le with
         | nil => None
         | cons e _ => match e with
                       | keychild _ n => Some n
                       | keyval _ _ _ => None
                       end
         end
  | S i' => match le with
            | nil => None
            | cons _ le' => nth_node_le i' le'
            end
  end.

Lemma nth_node_le_decrease: forall X (le:listentry X) (n:node X) i,
    nth_node_le i le = Some n ->
    (node_depth n < listentry_depth le)%nat.
Proof.
  induction le; intros.
  - unfold nth_node_le in H.
    destruct i; inversion H.
  - simpl.
    destruct i.
    + apply le_max_split_l. simpl in H. destruct e; try inv H. simpl. auto.
    + apply le_max_split_r. apply IHle with (i:=i). simpl in H. auto.
Qed.
      
Definition nth_node {X:Type} (i:index) (n:node X): option (node X) :=
  match n with btnode ptr0 le _ _ =>
               match i with
               | im => ptr0
               | ip na => nth_node_le na le
               end
  end.

Lemma nth_node_decrease: forall X (n:node X) (n':node X) i,
    nth_node i n = Some n' ->
    (node_depth n' < node_depth n)%nat.
Proof.
  intros. unfold nth_node in H.
  destruct n. destruct i.
  - simpl. destruct o. inversion H. subst.
    apply le_max_split_r. auto. inversion H.
  - simpl. apply le_max_split_l. apply nth_node_le_decrease with (i:=n). auto.
Qed.

Definition move_to_next {X:Type} (c:cursor X): cursor X * bool :=
  match (move_to_next_partial c) with
  | [] => (c,false)                     (* C program returns false here *)
  | (n,i)::c' => match nth_node i n with
                 | Some n' => (move_to_first c n',true)
                 | None => (c,true)    (* possible at leaf nodes *)
                 end
  end.

Definition getRecord (c:cursor val): val :=
  match c with
  | [] => nullval
  | (n,i)::c' =>
    match n with
      btnode ptr0 le b x =>
      match i with
      | im => nullval              (* no -1 at leaf nodes *)
      | ip ii =>
        match (nth_entry_le ii le) with
        | None => nullval
        | Some e =>
          match e with
          | keychild _ _ => nullval
          | keyval k v x => x
          end
        end
      end
    end
  end.

Definition getKey {X:Type} (c:cursor X): option key :=
  match c with
  | [] => None
  | (n,i)::c' =>
    match n with
      btnode ptr0 le b x =>
      match i with
      | im => None            (* ptr0 has no key *)
      | ip ii => 
        match (nth_entry_le ii le) with
        | None => None
        | Some e =>
          match e with
          | keychild k _ => Some k
          | keyval k _ _ => Some k
          end
        end
      end
    end
  end.

Fixpoint findChildIndex' {X:Type} (le:listentry X) (key:key) (i:index): index :=
  match le with
  | nil => i
  | cons e le' =>
    match e with
    | keyval k v x =>
      match (key <=? k) with
      | true => i
      | false => findChildIndex' le' key (next_index i)
      end
    | keychild k c =>
      match (key <=? k) with
      | true => i
      | false => findChildIndex' le' key (next_index i)
      end
    end
  end.

Definition findChildIndex {X:Type} (le:listentry X) (key:key): index :=
  findChildIndex' le key im.

(* n should be the current node pointed to, so if c=(m,i)::c', it should be m(i) *)
Function moveToRecord {X:Type} (c:cursor X) (key:key) (n:node X) {measure node_depth n}: cursor X * bool :=
  match n with btnode ptr0 le isLeaf x =>
               match isLeaf with
               | true =>
                 match findChildIndex le key with
                 | im => ((n,ip 0)::c, false)
                 | ip ii =>
                   match getKey ((n,ip ii)::c) with
                   | None => (c,false)  (* shouldnt happen, findChildIndex return valid indexes *)
                   | Some k => ((n,ip ii)::c, key =? k)
                   end
                 end
               | false =>
                 match nth_node (findChildIndex le key) n with
                 | None => (c,false)    (* should not happen: we should have ptr0 and findChildIndex should not overflow *)
                 | Some n' =>
                   moveToRecord ((n,findChildIndex le key)::c) key n'
                 end
               end
  end.
Proof.
  intros.
  apply nth_node_decrease with (i:= findChildIndex le key0). auto.
Qed.

Fixpoint numKeys_le {X:Type} (le:listentry X) : nat :=
  match le with
  | nil => 0%nat
  | cons e le' => S (numKeys_le le')
  end.

Definition numKeys {X:Type} (n:node X) : nat :=
  match n with btnode ptr0 le _ x => numKeys_le le end.

Fixpoint update_le_nth_child {X:Type} (i:nat) (le:listentry X) (n:node X) : listentry X :=
  match le with
  | nil => nil X
  | cons e le' => match i with
                  | O => match e with
                         | keychild k c => cons X (keychild X k n) le'
                         | keyval k v x => cons X (keychild X k n) le' (* shouldnt happen *)
                         end
                  | S i' => update_le_nth_child i' le' n
                  end
  end.  

Fixpoint update_le_nth_val {X:Type} (i:nat) (le:listentry X) (newv:V) (newx:X) : listentry X :=
  match le with
  | nil => nil X
  | cons e le' => match i with
                  | O => match e with
                         | keychild k c => cons X (keyval X k newv newx) le' (* shouldnt happen *)
                         | keyval k v x => cons X (keyval X k newv newx) le'
                         end
                  | S i' => update_le_nth_val i' le' newv newx
                  end
  end.

Definition update_node_nth_child {X:Type} (i:index) (oldn:node X) (n:node X) : node X :=
  match oldn with btnode ptr0 le isLeaf x =>
  match i with
  | im => btnode X (Some n) le isLeaf x
  | ip ii => btnode X ptr0 (update_le_nth_child ii le n) isLeaf x
  end
  end.

Fixpoint update_cursor {X:Type} (c:cursor X) (n:node X) : cursor X :=
  match c with
  | [] => []
  | (oldn,i)::c' =>
    let newn := update_node_nth_child i oldn n in
    (newn,i)::(update_cursor c' newn)
  end.

Fixpoint nth_key {X:Type} (i:nat) (le:listentry X): option key :=
  match le with
  | nil => None
  | cons e le' => match i with
                  | O => match e with
                         | keychild k _ => Some k
                         | keyval k _ _ => Some k
                         end
                  | S i' => nth_key i' le'
                  end
  end.
  
(* c should not be complete, and points to n *)
(* nEFC is newEntryFromChild pointer *)
Fixpoint insertKeyRecord' {X:Type} (key:key) (value:V) (nEFC:X) (n:node X) (c:cursor X): node X * cursor X * bool :=
  match n with btnode ptr0 le isLeaf x =>
  match isLeaf with
  | true =>
    match le with
    | nil =>               (* first key *)
      let newn:= btnode X ptr0 (cons X (keyval X key value nEFC) (nil X)) isLeaf x in
      (newn,update_cursor c newn,true)
    | _ =>
      match (findChildIndex le key) with
      | im => (n,c,false) (* TODO: THIS IS NOT ADDRESSED IN THE C CODE!!! *)
      | ip ii =>
        match (nth_key ii le) with
        | None => (n,c,false)   (* impossible, findChildIndex returns an index in range ? *)
        | Some k =>
          match (k =? key) with
          | true =>             (* update *)
            let newn:= btnode X ptr0 (update_le_nth_val ii le value nEFC) isLeaf x in
            (newn,update_cursor c newn,true) (* I don't think we should use nEFC. wich val? *)
          | false => (n,c,false)          (* new node, TODO *)
          end
        end
      end
    end
  | false => (n,c,false) (* TODO *)
  end
  end.

(**
    REPRESENTATIONS IN SEPARATION LOGIC
 **)

Definition tbtnode:=      Tstruct _BtNode noattr.
Definition tentry:=       Tstruct _Entry noattr.
Definition tchildrecord:= Tunion _Child_or_Record noattr.
Definition trelation:=    Tstruct _Relation noattr.
Definition tcursor:=      Tstruct _Cursor noattr.

Definition value_rep (v:V) (p:val):= (* this should change if we change the type of Values? *)
  data_at Tsh tint (Vint (Int.repr v)) p.

Definition isLeaf {X:Type} (n:node X) : bool :=
  match n with btnode ptr0 le b w => b end.

Definition getval (n:node val): val :=
  match n with btnode _ _ _ x => x end.

Fixpoint le_to_list (le:listentry val) : list (val * (val + val)) :=
  match le with
  | nil => []
  | cons e le' =>
    (match e with
     | keychild k c => ((Vlong(Int64.repr k)),  inl (getval c))
     | keyval k v x => ((Vlong(Int64.repr k)),  inr x) (* ptr to the record?? *)
     end) :: le_to_list le'
  end.

Definition le_to_list_complete (le:listentry val):=
  le_to_list le ++ list_repeat (Fanout - numKeys_le le) (Vundef, inl Vundef).
                        
Fixpoint entry_rep (e:entry val):=
  match e with
  | keychild _ n => match n with btnode _ _ _ x => btnode_rep n x end
  | keyval _ v x => value_rep v x
  end
with btnode_rep (n:node val) (p:val):mpred :=
  match n with btnode ptr0 le b x =>
  !!(x=p) &&
  malloc_token Tsh tbtnode p *
  field_at Tsh tbtnode (DOT _numKeys) (Vint(Int.repr (Z.of_nat (numKeys n)))) p *
  field_at Tsh tbtnode (DOT _isLeaf) (Val.of_bool b) p *
  match ptr0 with
  | None => field_at Tsh tbtnode (DOT _ptr0) nullval p
  | Some n' => match n' with btnode _ _ _ p' => field_at Tsh tbtnode (DOT _ptr0) p' p * btnode_rep n' p' end
  end *
  field_at Tsh tbtnode (DOT _entries) (le_to_list_complete le) p *
  le_iter_sepcon le
  end
with le_iter_sepcon (le:listentry val):mpred :=
  match le with
  | nil => emp
  | cons e le' => entry_rep e * le_iter_sepcon le'
  end.

Definition relation_rep (r:relation val) (p:val):mpred :=
  match r with
  | (n,c,x) => !!(x=p) &&
    EX p':val,
          field_at Tsh trelation (DOT _root) p' p *
          btnode_rep n p' *
          field_at Tsh trelation (DOT _numRecords) (Vlong(Int64.repr(Z.of_nat c))) p * (* long?int? *)
          malloc_token Tsh trelation p
  end.

Definition getCurrVal (c:cursor val): val :=
  match c with
  | [] => nullval
  | (n,_)::_ => match n with btnode _ _ _ x => x end
  end.

Definition getEntryIndex {X:Type} (c:cursor X) : index :=
  match c with
  | (n,i)::_ => i
  | [] => ip (0%nat)
  end.

Fixpoint cursor_valid_bool {X:Type} (c:cursor X): bool :=
  match c with
  | [] => true
  | (b,i)::c' => match b with btnode ptr0 le _ x => (index_leb_nat i (numKeys_le le -1)) && cursor_valid_bool c' end
  end.                          (* might be incomplete *)

Definition rep_index (i:index):=
  match i with
  | im => Vint(Int.repr(-1))
  | ip n => Vint(Int.repr(Z.of_nat n))
  end.

Definition cursor_rep (c:cursor val) (r:relation val) (p:val):mpred :=
  EX anc_end:list val, EX idx_end:list val,
  malloc_token Tsh tcursor p *
  field_at Tsh tcursor (DOT _currNode) (getCurrVal c) p *
  match r with (n,c,x) => field_at Tsh tcursor (DOT _relation) x p end *
  field_at Tsh tcursor (DOT _entryIndex) (rep_index(getEntryIndex c)) p *
  field_at Tsh tcursor (DOT _isValid) (Val.of_bool (cursor_valid_bool c)) p *
  field_at Tsh tcursor (DOT _level) (Vint(Int.repr(Zlength c))) p *
  field_at Tsh tcursor (DOT _nextAncestorPointerIdx) ((map (fun x => (rep_index (snd x)))  c) ++ idx_end) p * (* or its reverse? *)
  field_at Tsh tcursor (DOT _ancestors) ((map getval (map fst c)) ++ anc_end) p.
(* what about the list length that can be shorter than the array? *)
(* also the index might be not exactly the same for intern nodes (no -1) *)

(**
    FUNCTION SPECIFICATIONS
 **)
Definition empty_node (b:bool) (p:val):node val := (btnode val) None (nil val) b p.
Definition empty_relation (pr:val) (pn:val): relation val := ((empty_node true pn),0%nat,pr).
Definition empty_cursor := []:cursor val.

(* the malloc_spec from the floyd library, modified so that it takes a long argument *)
Definition malloc_spec'  {cs: compspecs} :=
   WITH t:type
   PRE [ 1%positive OF tulong ]
       PROP (0 <= sizeof t <= Int64.max_unsigned;
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       LOCAL (temp 1%positive (Vlong (Int64.repr (sizeof t))))
       SEP ()
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (if eq_dec p nullval then emp
            else (malloc_token Tsh t p * data_at_ Tsh t p)).

Definition malloc_spec  {cs: compspecs} (prog: program) :=
   try_spec prog "_malloc" malloc_spec'.
Arguments malloc_spec {cs} prog / .

Definition library_G  {cs: compspecs} prog :=
  exit_spec prog ++ malloc_spec prog ++ free_spec prog.

Ltac with_library prog G := 
 let x := constr:(library_G prog) in
 let x := eval hnf in x in 
 let x := eval simpl in x in
 let y := constr:(x++G) in
 let y := eval cbv beta iota delta [app] in y in 
 with_library' prog y.

Definition createNewNode_spec : ident * funspec :=
  DECLARE _createNewNode
  WITH isLeaf:bool
  PRE [ _isLeaf OF tint ]       (* why tint and not tbool? *)
  PROP ()
  LOCAL (temp _isLeaf (Val.of_bool isLeaf))
  SEP ()
  POST [ tptr tbtnode ]
  EX p:val, PROP ()
  LOCAL (temp ret_temp p)
  SEP (btnode_rep (empty_node isLeaf p) p).

Definition RL_NewRelation_spec : ident * funspec :=
  DECLARE _RL_NewRelation
  WITH u:unit
  PRE [ ]
  PROP ()
  LOCAL ()
  SEP ()
  POST [ tptr trelation ]
  EX pr:val, EX pn:val, PROP ()
  LOCAL(temp ret_temp pr)
  SEP (relation_rep (empty_relation pr pn) pr).

Definition RL_NewCursor_spec : ident * funspec :=
  DECLARE _RL_NewCursor
  WITH r:relation val, p:val
  PRE [ _relation OF tptr trelation ]
  PROP ()
  LOCAL (temp _relation p)
  SEP (relation_rep r p)
  POST [ tptr tcursor ]
  EX p':val, PROP ()
  LOCAL(temp ret_temp p')
  SEP (relation_rep r p * (if (eq_dec p' nullval)
                           then emp
                           else cursor_rep empty_cursor r p')).

Definition RL_MoveToNext_spec : ident * funspec :=
  DECLARE _RL_MoveToNext
  WITH c:cursor val, p:val, rel:relation val, prel:val
  PRE [ _btCursor OF tptr tcursor ]
  PROP ()
  LOCAL (temp _btCursor p)
  SEP (cursor_rep c rel p; relation_rep rel prel)
  POST [ tint ]
  EX b:bool, EX c':cursor val,
  PROP (move_to_next c = (c',b))
  LOCAL (temp ret_temp (Val.of_bool b))
  SEP(cursor_rep c' rel p; relation_rep rel prel).
                             
(**
    GPROG
 **)

Definition Gprog : funspecs :=
        ltac:(with_library prog [
                             createNewNode_spec; RL_NewRelation_spec; RL_NewCursor_spec;
                             RL_MoveToNext_spec(* ; malloc_spec *)
 ]).

(**
    FUNCTION BODIES PROOFS
 **)

Lemma body_createNewNode: semax_body Vprog Gprog f_createNewNode createNewNode_spec.
Proof.
  start_function.
  forward_call tbtnode.
  - admit.                      (* typecheck_error? *)
  - simpl. entailer!. admit.           (* false! *)
  - split. simpl. rep_omega.
    split. auto. admit.
  - Intros vret.
    forward_if (PROP (vret<>nullval)
     LOCAL (temp _newNode vret; temp _isLeaf (Val.of_bool isLeaf))
     SEP (if eq_dec vret nullval
          then emp
          else malloc_token Tsh tbtnode vret * data_at_ Tsh tbtnode vret; emp)).
    + admit.
    + forward. rewrite if_true; auto.
      admit.                    (* change the spec if malloc fails *)
    + forward. rewrite if_false; auto. entailer!.
    + Intros. rewrite if_false; auto. Intros.
      forward.                  (* newNode->numKeys = 0 *)
      forward.                  (* newnode->isLeaf=isLeaf *)
      forward.                  (* newnode->ptr0=null *)
      forward.                  (* return newnode *)
      Exists vret. entailer!.
      unfold_data_at 1%nat.
      entailer!.
Admitted.

Lemma body_NewRelation: semax_body Vprog Gprog f_RL_NewRelation RL_NewRelation_spec.
Proof.
start_function.
forward_call(true).
Intros vret.
forward_if (PROP (vret<>nullval)  LOCAL (temp _pRootNode vret)  SEP (btnode_rep (empty_node true vret) vret; emp)).
- subst vret.
  forward. entailer!.
- forward.
  entailer!.
- forward_call trelation.
  + admit.
  + entailer!.
    admit.                      (* false *)
  + split. unfold sizeof. simpl. rep_omega.
    split. auto. admit.
  + Intros newrel.
    forward_if(PROP (newrel<>nullval)
     LOCAL (temp _pNewRelation newrel; temp _pRootNode vret)
     SEP (if eq_dec newrel nullval
          then emp
          else malloc_token Tsh trelation newrel * data_at_ Tsh trelation newrel;
          btnode_rep (empty_node true vret) vret)).
    * apply denote_tc_test_eq_split.
      entailer!. admit.
      entailer!.
    * rewrite if_true; auto. subst newrel.
      forward_call (tbtnode, vret).
      { admit. }
      { forward. admit. }
    * rewrite if_false; auto.
      forward.
      entailer!. rewrite if_false; auto.
    * Intros. rewrite if_false; auto. Intros.
      forward.                  (* pnewrelation->root = prootnode *)
      forward.                  (* pnewrelation->numrecords=0 *)
      forward.                  (* return pnewrelation *)
      Exists newrel. Exists vret. Exists vret.
      entailer!.
      unfold_data_at 1%nat. cancel.
Admitted.

Lemma body_NewCursor: semax_body Vprog Gprog f_RL_NewCursor RL_NewCursor_spec.
Proof.
start_function.
forward_if (PROP() LOCAL(temp _relation p) SEP(relation_rep r p)).
- admit.
- forward. auto.
- subst p.
  (* forward_call tt. *)              (* telling me to import VST.floyd.library, but it has been done *)
  admit.
- forward_call tcursor.
  + admit.
  + entailer!. admit.
  + split. unfold sizeof. simpl. rep_omega.
    split. auto. admit.
  + Intros vret.
    forward_if ((PROP (vret<>nullval)
     LOCAL (temp _cursor vret; temp _relation p)
     SEP (if eq_dec vret nullval
          then emp
          else malloc_token Tsh tcursor vret * data_at_ Tsh tcursor vret; 
          relation_rep r p))).
    * admit.
    * rewrite if_true; auto.
      forward. Exists nullval. entailer!.
    * forward. rewrite if_false; auto. entailer!.
    * Intros. rewrite if_false; auto. Intros.
      forward.                  (* cursor->relation=relation *)
      forward.                  (* cursor->currnode=null *)
      forward.                  (* cursor->entryIndex=0 *)
      forward.                  (* cursor->isValid=0 *)
      forward.                  (* cursor->level=0 *)
      autorewrite with norm. simpl.
      pose (n:=20).
      pose (Pre:=(EX i:Z,
            PROP ((0 <= i)%Z; (i <= n)%Z)
            LOCAL(temp _cursor vret; temp _relation p)         
            SEP(malloc_token Tsh tcursor vret;
                relation_rep r p;
                data_at Tsh tcursor
               (force_val (sem_cast_pointer p),
               (Vint (Int.repr 0),
               (Vlong (Int64.repr 0),
               (Vint (Int.repr 0),
               (Vint (Int.repr 0),
               (list_repeat (Z.to_nat i) (Vint(Int.repr 0)) ++  list_repeat (MaxTreeDepth - (Z.to_nat i)) Vundef,
                (list_repeat (Z.to_nat i) nullval ++ list_repeat (MaxTreeDepth - (Z.to_nat i)) Vundef))))))) vret))%assert).
      (* forward_loop Pre. *)




      
      (* | simple eapply semax_seq'; *)
      (*     [forward_for_simple_bound' n Pre *)
      (*     | cbv beta; simpl update_tycon; abbreviate_semax  ] *)
      
      simple eapply semax_seq'.
      { Locate semax_for_const_bound_const_init.
        pose(Pre':= (PROP ( )
     LOCAL (temp _cursor vret; temp _relation p)
     SEP (malloc_token Tsh tcursor vret;
     data_at Tsh tcursor
       (force_val (sem_cast_pointer p),
       (Vint (Int.repr 0),
       (Vlong (Int64.repr 0),
       (Vint (Int.repr 0),
       (Vint (Int.repr 0),
       ([Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef;
        Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef],
       [Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef;
       Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef])))))) vret;
     relation_rep r p))). fold Pre'.
        (* forward_loop *)
        match goal with
        | |- semax _ ?P (Sfor (Sset _ ?E) _ ?C _) ?Q => 
        try eapply (semax_for_const_bound_const_init n Pre) with (_i:=_i) (hi:=20) (Delta:=Delta) (body:=C) (Pre0:=P) end.
        (* this one fails but shouldn't ? *)
        (* because of the cast to tulong *)
        admit.
      }
      {  cbv beta. simpl update_tycon. abbreviate_semax. forward. }
(* forward_for_simple_bound n Pre. *)
Admitted.

Lemma body_MoveToNext: semax_body Vprog Gprog f_RL_MoveToNext RL_MoveToNext_spec.
Proof.
start_function.
unfold cursor_rep. Intros anc_end. Intros idx_end.
forward.                        (* t'17=btCursor->currNode *)
- autorewrite with norm. entailer!. unfold getCurrVal.
  destruct c. auto. admit.
-
  (* we need to show that the current value is a node, represented in the memory *)
  admit.
Admitted.