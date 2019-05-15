Require Import VST.floyd.proofauto.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.
Require Import FunInd.
Require Import Coq.Strings.Ascii.
Require btrees.btrees.
Require btrees.btrees_sep.

Require Import DB.functional.trie.
Require Import DB.functional.btree.
Require Import DB.representation.trie.

Require Import Top.db_operations.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(* types from .c file *)
Definition Node := Tstruct _Node noattr.
Definition Column := Tstruct _Column noattr.
Definition Schema := Tstruct _Schema noattr.
Definition Element := Tstruct _Element noattr.
Definition DBIndex := Tstruct _DBIndex noattr.


Definition _list : ident := 2%positive.
Definition t_list := Tstruct _list noattr.

(* FUNCTIONAL MODEL *)

Inductive col_t : Type := Int | Str.

(* Schema type - has a list of column types AND the ordered list of indices of PK columns *)
Record schema : Type := mk_schema
                          { col_types : list col_t ;
                            pk_indices : list Z ;
                            range : Forall (fun i => 0 <= i < Z.of_nat (length col_types)) pk_indices ;
                            nodup : NoDup pk_indices }.

(* schema_tail makes it possible to use schemas like lists *)
Program Definition schema_tail sch := match col_types sch with
                              | [] => sch
                              | hd :: tl =>                                (* or x <> 0? *)
                                mk_schema tl (map (fun x => x - 1) (filter (fun x => x >=? 1) (pk_indices sch))) _ _ end.
Next Obligation. (* range of the new pk indices *)
  destruct sch. simpl in *.
  subst col_types0. simpl Datatypes.length in range0.
  rewrite Forall_map.
  induction pk_indices0; inversion range0; inversion nodup0. apply Forall_nil.
  simpl. case_eq (a >=? 1); intro h. 
  apply Forall_cons. simpl. apply Forall_inv in range0. rewrite Z.geb_le in h.
  rewrite Nat2Z.inj_succ in range0. omega.
  auto.
  auto.
Defined.

Next Obligation. (* nodup of the new pk indices *)
  destruct sch. simpl in *.
  induction pk_indices0. simpl. apply NoDup_nil.
  simpl. case_eq (a >=? 1); intro h; inversion nodup0; inversion range0. simpl. apply NoDup_cons.
  intro k. apply list_in_map_inv in k.
  destruct k as [x1 [p1 p2]].
  rewrite filter_In in p2. destruct p2 as [p21 p22].
  replace x1 with a in p21 by omega. auto.
  auto. auto.
Defined.

Definition num_cols (sch: schema) : nat :=
  length (col_types sch).

Definition num_pks (sch: schema) : nat :=
  length (pk_indices sch).

(* element type - what tuples in the table consist of *)
Inductive elt : Type := 
| int_elt: ptrofs -> elt
| str_elt: list byte -> elt. 

(* This predicate serves to ensure compatibility between a tuple and a schema *)
Inductive col_types_compat : col_t -> elt -> Prop :=
| compat_int : forall n, col_types_compat Int (int_elt n)
| compat_str : forall s, col_types_compat Str (str_elt s).

(* A tuple is valid with respect to a given schema when its elements' types match the schema *)
Definition is_valid_elt_list (sch : schema) (le : list elt) : Prop :=
  Forall2 col_types_compat (col_types sch) le.

(* A tuple sch is a list of elements that matches sch *)
Record tuple (sch : schema) := mk_tuple
                                 { elts : list elt ;
                                   adequacy : is_valid_elt_list sch elts }.

Arguments elts {sch}.

(* A schema is nil iff it can accomodate the nil tuple *)
Lemma is_valid_nil (sch : schema) : is_valid_elt_list sch [] <-> col_types sch = [] /\ pk_indices sch = [].
Proof.
  split ; intro h.
  destruct sch.
  inversion h. simpl in H |- *. clear h. rewrite <- H in range0.
  destruct pk_indices0. easy. apply Forall_inv in range0. simpl in range0. omega.
  destruct h. destruct sch. simpl in *. subst col_types0 pk_indices0.
  unfold is_valid_elt_list. apply Forall2_nil.
Qed.

(* The number of columns of a tuple and the corresponding schema are equal *)
Lemma tuple_schema_length_eq (sch : schema) (t : tuple sch) : length (col_types sch) = length (elts t).
Proof.
  destruct sch, t as [elts ad]. simpl. unfold is_valid_elt_list in ad.
  simpl in ad. apply mem_lemmas.Forall2_length in ad. auto.
Qed.  

(* Manipulate tuples like lists *)
Program Definition tuple_tail {sch} (t : tuple sch) : tuple (schema_tail sch) :=
  mk_tuple (schema_tail sch) (tail (elts t)) _.
Next Obligation.
  destruct sch, t. simpl.
  inversion adequacy0; simpl in *;
  subst elts0; subst col_types0; simpl; easy.
Qed.  

Lemma elts_tuple_tail {sch} (t : tuple sch) : elts (tuple_tail t) = tail (elts t).
reflexivity.
Qed.

Instance inhabitant_elt : Inhabitant elt := int_elt (Ptrofs.zero).
Instance inhabitant_col_t : Inhabitant col_t := Int.

(* get the n-th component of a tuple *)
Definition nth_tuple {sch} (t : tuple sch) (n : nat) (h : (n < num_cols sch)%nat) : elt := nth n (elts t) inhabitant_elt.

(* strips non-pk cols from l, order according to the pk_indices list *)
(* l can be any list in this function *)
Fixpoint get_pk_cols {X : Type} {i : Inhabitant X} (l : list X) (pk_indices : list Z) :=
  match pk_indices with
  | [] => []
  | hd :: tl => Znth hd l :: get_pk_cols l tl end.

Lemma get_pk_cols_length (sch : schema) : length (get_pk_cols (col_types sch) (pk_indices sch)) = num_pks sch.
Proof.
  destruct sch.
  simpl. induction pk_indices0 as [ | pki pkis ]; simpl.
  easy.
  unfold num_pks in IHpkis |- *. simpl in IHpkis |- *. f_equal. 
  apply IHpkis ; inversion range0; inversion nodup0; easy. 
Qed.

(* This function strips the schema from non-primary keys and orders the remaining columns according to their rank in the pk_indices list. *)
Program Definition sch_projection_on_pks (sch : schema) : schema :=
  mk_schema (get_pk_cols (col_types sch) (pk_indices sch)) (map Z.of_nat (seq 0 (length (pk_indices sch)))) _ _.

Next Obligation.
  rewrite get_pk_cols_length.
  destruct sch.
  simpl. induction pk_indices0.
  simpl. easy.
  simpl length.
  unfold seq ; fold seq.
  simpl map. apply Forall_cons ; [ easy | ].
  unfold num_pks in IHpk_indices0 |- *. simpl length in IHpk_indices0 |- *.
  rewrite <- seq_shift, map_map, Forall_map. rewrite Forall_map in IHpk_indices0.
  apply (@Forall_impl _ ((fun i : Z => 0 <= i < Z.of_nat (Datatypes.length pk_indices0)) oo Z.of_nat)).
  cbn beta delta. intros.
  split. easy. do 2 rewrite Nat2Z.inj_succ. omega.
  apply IHpk_indices0. inversion range0 ; easy. inversion nodup0 ; easy.
Defined.
Next Obligation.
  destruct sch. simpl.
  apply FinFun.Injective_map_NoDup. unfold FinFun.Injective. apply Nat2Z.inj.
  apply seq_NoDup.
Defined.

Lemma Forall2_Znth {A B} {ia : Inhabitant A} {ib : Inhabitant B} :
  forall (R : A -> B -> Prop) (h : R ia ib) (l1 : list A) (l2 : list B) n,
    Forall2 R l1 l2 -> R (Znth n l1) (Znth n l2).
Proof.
  intros.
  unfold Znth. destruct (zlt n 0). easy.
  generalize (Z.to_nat n) as m. intro m. revert m l1 l2 H. 
  induction m. destruct l1 ; destruct l2 ; try easy.
  simpl. intro H. inversion H. easy.
  intros. inversion H ; simpl.
  easy.
  apply IHm. easy.
Qed.
 
Lemma Forall2_Znth_range {A B} {ia : Inhabitant A} {ib : Inhabitant B} :
  forall (R : A -> B -> Prop) (l1 : list A) (l2 : list B) n (h : 0 <= n < Z.of_nat (min (length l1) (length l2))),
    Forall2 R l1 l2 -> R (Znth n l1) (Znth n l2).
Proof.
  intros.
  unfold Znth. destruct (zlt n 0). omega. apply proj2 in h. rewrite <- (Z2Nat.id n), <- Nat2Z.inj_lt in h.
  revert h. 
  generalize (Z.to_nat n) as m. intros m hm. revert m l1 l2 H hm . 
  induction m. destruct l1 ; destruct l2 ; try easy.
  simpl. intro hO. inversion hO. easy.
  intros. inversion H. subst l1 l2. simpl in hm. omega.
  simpl. apply IHm. easy. subst l1 l2. simpl in hm. omega. omega.
Qed.

(* Tuple version of sch_projection_on_pks *)
Program Definition tuple_projection_on_pks {sch} (t : tuple sch) : tuple (sch_projection_on_pks sch) :=
  mk_tuple (sch_projection_on_pks sch) (get_pk_cols (elts t) (pk_indices sch)) _.

Next Obligation.
  pose proof (tuple_schema_length_eq sch t).
  destruct sch as [ct pkis ra nod], t as [elts ad].
  unfold is_valid_elt_list in ad |- *.
  simpl in ad |- *.
  induction pkis ; simpl ; [ easy |].
  inversion ra. simpl in H, IHpkis.
  apply Forall2_cons ; [ | inversion nod ; inversion ra ].
  apply Forall2_Znth_range.
  apply Forall_inv in ra. rewrite <- H, Nat.min_id. omega.
  easy.
  apply IHpkis ; easy.
Defined.   

(* A table is a list of tuples such that the projections of these tuples on the table's schema's pks contains no duplicates *)
Record table (sch : schema) := mk_table {
                                   tuples : list (tuple sch) ;
                                   (* for now, we can only accomodate single fields for the pk *)
                                   (* when we know how to use concatenated indices, we could have something like *)
                                   (* has_pk_field : pk_indices sch <> [] ; *)
                                   unique_pk_field : { a | pk_indices sch = [a] } ;
                                   no_dup_on_pk : NoDup (map tuple_projection_on_pks tuples) }.

Arguments mk_table {sch}.
Arguments tuples {sch}. Arguments unique_pk_field {sch}.

Definition empty_table (sch : schema) (unique_pk_field : { a | pk_indices sch = [a] }) :
  table sch := mk_table [] unique_pk_field (NoDup_nil _). 

(* This definition is relevant only when the primary key has a single field *)
Definition get_pk_projection {sch} (tab : table sch) : list elt :=
  flat_map (elts oo tuple_projection_on_pks) (tuples tab).

(* This is a lemma only because our tables have only one pk field *)
Lemma pk_projection_length {sch} (tab : table sch) : length (get_pk_projection tab) = length (tuples tab).
Proof.
  unfold get_pk_projection, tuple_projection_on_pks. simpl. unfold "oo".
  simpl. destruct sch, tab.
  simpl in *.
  induction tuples0, pk_indices0 ; simpl ; destruct unique_pk_field0 ; try easy.
  inversion e. subst pk_indices0. simpl in IHtuples0 |- *.
  inversion no_dup_on_pk0. f_equal. auto.
Qed.

Inductive index : Type -> Type -> Type :=
| int_index: btrees.btrees.relation val -> btrees.btrees.cursor val -> index btrees.btrees.key btrees.btrees.V
| str_index: Trie.trie val -> index Trie.key Trie.value.

Definition get_index_kv_pair {k v} (i : index k v) : list (k * v) :=
  match i with
  | int_index (bt, _) _ => btrees.btrees.abs_node bt
  | str_index tr => Trie.flatten tr end.

Definition get_key_as_elt_list {k v} (i : index k v) : list elt :=
  match i with
  | int_index (bt, _) _ => map (int_elt oo Ptrofs.of_int oo fst) (btrees.btrees.abs_node bt)
  | str_index tr => map (str_elt oo fst) (Trie.flatten tr) end.

Definition clustered_pk_index {k v} {sch : schema} (tab : table sch) : Type :=
  { ind : index k v | get_key_as_elt_list ind = get_pk_projection tab }.

Definition index_rep {k v} (ind : index k v) (p: val) : mpred :=
  match ind with 
  | int_index rel cur => btrees.btrees_sep.relation_rep rel (btrees.btrees.get_numrec rel) * btrees.btrees_sep.cursor_rep cur rel p
  | str_index tr => Trie.trie_rep tr
  end.


(* REPRESENTATION IN MEMORY *)

Definition val_of_col_t (c : col_t) : val := match c with
                                             | Int => Vptrofs (Ptrofs.zero)
                                             | Str => Vptrofs (Ptrofs.one)
                                             end.

Fixpoint coltype_rep (sh: share) (col: col_t) (p: val) : mpred :=
data_at sh size_t (val_of_col_t col) p.

Fixpoint listcol_rep  (sh: share) (lst: list col_t) (p: val) : mpred := 
 match lst with 
   | t::hs => EX y: val, coltype_rep sh t p * listcol_rep sh hs y
   | _ => !! (p = nullval) && emp
 end.

Fixpoint listpk_rep (sh: share) (lst: list Z) (p: val) : mpred :=
 match lst with
  | h :: hs => EX y: val, data_at sh size_t (Vptrofs(Ptrofs.repr h)) p * listpk_rep sh hs y
  | _ => !! (p = nullval) && emp
 end.

Definition schema_rep (sh: share) (sch: schema) (p: val) : mpred :=
EX x: val, EX y: val, listcol_rep sh (col_types sch) x * listpk_rep sh (pk_indices sch) y.


Definition schlen (sch: schema) : nat :=
  length (col_types sch) + length (pk_indices sch).


Definition elt_rep (sh: share) (e: elt) (p: val) : mpred := 
  match e with
  | int_elt n => data_at sh (size_t) (Vptrofs(n)) p
  | str_elt s => EX q: val, EX sh' : share, data_at sh (tptr tschar) q p *
                                            !! readable_share sh' && cstring sh' s q
  end.

Program Fixpoint tuple_rep (sh: share) {sch} (t: tuple sch) (p: val) {measure (length (elts t))} : mpred :=
  match elts t with 
  | h :: hs => EX y: val, elt_rep sh h p * tuple_rep sh (tuple_tail t) y
  | _ => !! (p = nullval) && emp
  end.

(*
Definition table_rep {sch: schema} (sh: share) (tab : table sch) (p: val) : mpred :=
  EX clustered_index : clustered_pk_index tab,
                       iter_sepcon (fun tup => tuple_rep sh tup data 


*)
                                                                    

(*
Definition relation_rep (r:relation val) (numrec:nat) :mpred :=
  match r with
  (n,prel) =>
    malloc_token Tsh trelation prel *
    data_at Tsh trelation (getval n, (Vint(Int.repr(Z.of_nat(numrec))), (Vint (Int.repr (Z.of_nat(get_depth r)))))) prel *
    btnode_rep n
  end.
*)

(*
Definition cursor_rep (c:cursor val) (r:relation val) (p:val):mpred :=
  EX anc_end:list val, EX idx_end:list val,
  malloc_token Tsh tcursor p *
  match r with (_,prel) =>
               data_at Tsh tcursor (prel,(
                                    Vint(Int.repr((Zlength c) - 1)),(
                                    List.rev (map (fun x => (Vint(Int.repr(rep_index (snd x)))))  c) ++ idx_end,(
                                    List.rev (map getval (map fst c)) ++ anc_end)))) p end.
*)

(*
  Fixpoint trie_rep (t: trie val): mpred :=
    match t with
    | Trie.trienode_of addr tableform listform =>
      BTree.table_rep tableform addr * (* that actually at this address we store a B+ tree *)
      iter_sepcon (compose (@bordernode_rep trie_rep) snd) listform
    end.
*)







