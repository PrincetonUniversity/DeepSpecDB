Require Import VST.concurrency.conclib.
Require Import VST.floyd.proofauto.
Require Import VST.atomics.general_locks.
Require Import Coq.Sets.Ensembles.
Require Import bst.puretree.
Require Import bst.give_up_template.
(* Require Import bst.bst_inst. *)
Require Import VST.atomics.verif_lock_atomic.
Require Import VST.floyd.library.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(* Definition t_struct_tree := Tstruct _node noattr.
Definition t_struct_tree_t := Tstruct _node_t noattr. *)
Definition t_struct_node := Tstruct _node_t noattr.
Definition t_struct_pn := Tstruct _pn noattr.

Definition number2Z (x : number) : Z :=
  match x with
    | Finite_Integer y => y
    | Neg_Infinity => Int.min_signed
    | Pos_Infinity => Int.max_signed
  end.

Inductive enum : Type := Zero | One | Two.

Definition enums x : val :=
  match x with
  | Zero => Vint Int.zero
  | One => Vint Int.one
  | Two => Vint (Int.repr 2%Z)
  end.

#[global] Instance enum_inhabited : Inhabitant (enum).
Proof.
  unfold Inhabitant; apply Zero.
Defined.

#[export] Instance pointer_lock : Ghost := discrete_PCM (val * val * range).
Definition ghost_info : Type := (key * val)%type.

(* This allows the range to be outdated while the ghost_info may be present or absent. *)
#[export] Instance node_ghost : Ghost := prod_PCM pointer_lock (exclusive_PCM (option ghost_info)).
Notation node_info := (@G node_ghost).

Definition in_tree (g: gname) (g1 : gname) (pn: val) (lock: val):=
      ghost_snap (P := gmap_ghost (K := gname)(A := discrete_PCM (val * val)) )
        ({[g1 := (pn, lock)]}) g.

Lemma in_tree_duplicate g gin pn lock:
  in_tree g gin pn lock |-- in_tree g gin pn lock * in_tree g gin pn lock.
Proof. by rewrite - bi.persistent_sep_dup. Qed.


Class NodeRep : Type := {
      node_rep_R : val -> range -> option (option ghost_info) -> gname -> mpred}.
  Context (NR: NodeRep).
  Definition node_rep pn g g_current (r : node_info) :=
    !!(repable_signed (number2Z r.1.2.1) ∧ repable_signed (number2Z r.1.2.2) /\
         is_pointer_or_null r.1.1.2) &&
      field_at Ews (t_struct_node) [StructField _t] r.1.1.1 pn *
      field_at Ews (t_struct_node) [StructField _min] (vint (number2Z (r.1.2.1))) pn * (*min*)
      field_at Ews (t_struct_node) [StructField _max] (vint (number2Z (r.1.2.2))) pn * (*max*)
      malloc_token Ews t_struct_node pn * in_tree g g_current pn r.1.1.2 *
      node_rep_R r.1.1.1 r.1.2 r.2 g.

  Definition node_lock_inv_pred g p gp a := my_half gp Tsh a * node_rep p g gp a.
  Definition ghost_ref (g : own.gname) r1 :=
  ghost_master1 (P := gmap_ghost (K := gname) (A := discrete_PCM (val * val))) r1 g.

Lemma ghost_snapshot_intree g (s : gmap gname (val * val))(pn : val)(lock: val)(g_in: gname):
    ghost_ref g s * (!! (s !! g_in = Some(pn, lock)) && seplog.emp)
                      |-- ( in_tree g g_in pn lock * ghost_ref g s).
Proof.
  unfold ghost_ref, ghost_master1, in_tree.
  iIntros "(H & (%Hx & _))".
  rewrite snap_master_join; auto.
  iFrame "H".
  iPureIntro.
  by eapply map_singleton_subseteq_l in Hx.
Qed.

Lemma node_exist_in_tree: forall g (s : gmap gname (val * val)) (pn : val) (lock: val) (g_in:gname),
    in_tree g g_in pn lock * ghost_ref g s |-- !! ( s !! g_in = Some(pn, lock)).
Proof.
 intros.
 unfold ghost_ref, in_tree.
 rewrite -> snap_master_join1.
 iIntros "(% & H)".
 iPureIntro.
 by apply map_singleton_subseteq_l.
Qed.

Definition ltree p (lock : val) R:=
  EX lsh, !!(field_compatible t_struct_node nil p /\ readable_share lsh) &&
  (field_at lsh t_struct_node [StructField _lock] lock p * inv_for_lock lock R).

(* Record tuple of (g, g_in, pn, lock, info)
In the future, we might replace info with only range,
Note that in each node we have a pointer that points to the node info
For e.g, with bst that has {int k, void *v, node_t * left, * right }
We have two cases (1) node info is NULL, then the pointer that points to nullval
(2) is (k, v, left, right)
Updated: no need to have g in the record. 
 *)

(* rename g, g_in, ... *)
Record mpredList := {
    g_inL : gname; pnL : val; lockL: val;
    NodeL: (@G (prod_PCM (discrete_PCM (val * val * range)) (exclusive_PCM (option (key * val)))));
}.

(* CSSi *)
Definition ghost_tree_rep {N: NodeRep} (I : list mpredList) (g: gname): mpred :=
  iter_sepcon (fun (p: mpredList) => ltree p.(pnL) p.(lockL)
                                (node_lock_inv_pred g p.(pnL) p.(g_inL) p.(NodeL))) I.

(* Global ghost *)
Definition find_ghost_set (I : list mpredList): gmap gname (val * val) :=
  let add_to_map (gmap_acc : gmap gname (val * val)) (mp : mpredList) :=
    let cur_gname := g_inL mp in
    match gmap_acc !! cur_gname with
    | Some _ => gmap_acc (* Already added to the map *)
    | None => <[ cur_gname := (pnL mp, lockL mp) ]> gmap_acc
    end
  in
  List.fold_left add_to_map I ∅.

Check find_ghost_set.

(* return the first element of g_in of the list *)
Definition extract_g_and_g_in (lst : list mpredList) : option (gname) :=
  match lst with
  | [] => None  (* Empty list *)
  | hd :: _ => Some (hd.(g_inL))
  end.
(*
Lemma test: forall (p : mpredList), True.
Proof.
  intros.
  Check p.(node_info).1.1.1. (* pointer *)
  Check p.(node_info).1.1.2. (* lock *)
  Check p.(node_info).1.2.   (* range *)
  Check ((p.(node_info).2)).
Abort.
*)
Definition extract_key_value (m: mpredList) : option (key * val) :=
  match m.(NodeL).2 with
  | Some (Some (key, value)) => Some (key, value)
  | _ => None
  end.

Check extract_key_value _.
Definition extract_key (opt : option (key * val)) : option key :=
  option_map (fun '(k, _) => k) opt.

Definition extract_value (opt : option (key * val)) : option val :=
  option_map (fun '(_, v) => v) opt.


Definition tree_to_gmap (I : list mpredList): gmap key val :=
  let add_to_map (gmap_acc : gmap key val) (mp : mpredList) :=
    match extract_key_value mp with
    | Some (cur_key, cur_value) =>
      match gmap_acc !! cur_key with
      | Some _ => gmap_acc (* Already added to the map *)
      | None => <[ cur_key := cur_value ]> gmap_acc
      end
    | None => gmap_acc (* No (key, value) pair, just return the current map *)
    end
  in
  List.fold_left add_to_map I ∅.

Check ghost_ref _.
Check find_ghost_set _.

(* CSS *)
(* old name is tree_rep*)
(* we need to have g_root that represents for the root node of BST, or the head of linked list *)
(* therefore, (extract_g_and_g_in I = Some (g, g_root)) ensures that the first element of the list,
in which (g, g_in) should be (g, g_root) with the keep-track purpose. *)
Definition CSS (g g_root : gname) (m: gmap key val): mpred :=
  EX I, !!(extract_g_and_g_in I = Some (g_root)) && !! (tree_to_gmap I = m) && 
          ghost_tree_rep I g * ghost_ref g (find_ghost_set I).


Lemma node_conflict_local {N: NodeRep} pn g g_in a b: node_rep pn g g_in a * node_rep pn g g_in b  |-- FF.
Proof.
  unfold node_rep.
  iIntros "(((((((_ & H) & _) & _) & _) & _) & _) & ((((((_ & H') & _) & _) & _) & _) & _))".
  Check field_at_conflict Ews t_struct_node (DOT _t) pn.
  iPoseProof (field_at_conflict Ews t_struct_node (DOT _t) pn  with "[$H $H']") as "HF";
      simpl; eauto. lia.
Qed.

Definition extract_mp_fields (m : mpredList) :=
  (g_inL m, pnL m, lockL m, NodeL m).


Lemma find_ghost (I : list mpredList) (pn lock_in : val) (g g_in: gname):
  find_ghost_set I !! g_in = Some (pn, lock_in) -> exists nodeI,
  In ({| g_inL := g_in; pnL := pn; lockL := lock_in; NodeL := nodeI |}) I.
Proof.
  intros.
  unfold find_ghost_set in H.
  set (S := empty) in H.
  assert (( ∃ nodeI : G, In {| g_inL := g_in; pnL := pn; lockL := lock_in; NodeL := nodeI |} I) \/
            S !! g_in = Some(pn, lock_in)).
  {
    clearbody S.
    generalize dependent S.
    induction I as [| mp I']; intros S; simpl in *.
    - by right.
    - destruct (S !! g_inL mp) eqn: Heq; intros.
      + specialize ((IHI' _) H).
        destruct IHI' as [(NodeI & H1) | H2].
        left; auto.
        exists NodeI; auto. auto.
      + specialize ((IHI' _ ) H).
        destruct IHI' as [(NodeI & H1) | H2].
        left. exists NodeI; by right. 
        destruct (g_inL mp =? g_in)%nat eqn: Hg.
        * rewrite Nat.eqb_eq in Hg.
          subst g_in.
          pose proof Heq as HNone.
          apply insert_union_singleton_r with (x:= (pnL mp, lockL mp)) in Heq.
          rewrite Heq lookup_union_r in H2; auto. 
          rewrite lookup_singleton in H2.
          inversion H2; subst.
          left. exists (NodeL mp).
          left. by destruct mp.
        * rewrite Nat.eqb_neq in Hg.
          pose proof Heq as HNone.
          apply insert_union_singleton_r with (x:= (pnL mp, lockL mp)) in Heq.
          rewrite Heq lookup_union_l in H2; auto.
          by apply lookup_singleton_None.
  }
  destruct H0 as [(NodeI & H1) | H2].
  - eexists; eauto.
  - by replace S with (∅ : gmap gname (val * val)) in H2.
Qed.

#[global] Instance Inhabitant_mpredList : Inhabitant mpredList := {
    default := {| g_inL := 0%nat; pnL := Vnullptr; lockL := Vnullptr;
               NodeL := ((Vnullptr, Vnullptr, (Neg_Infinity, Pos_Infinity)), None)|} }.

Lemma in_tree_inv1 I pn g g_in (lock_in : val) (lk : val):
       in_tree g g_in pn lock_in * (ghost_tree_rep I g * ghost_ref g (find_ghost_set I)) |--
  (EX a : node_info,
  inv_for_lock lock_in (node_lock_inv_pred g pn g_in a) *
  (inv_for_lock lock_in (node_lock_inv_pred g pn g_in a) -*
   (ghost_tree_rep I g * ghost_ref g (find_ghost_set I)))) &&
     (EX R, (ltree pn lock_in R) * (ltree pn lock_in R -* (ghost_tree_rep I g * ghost_ref g (find_ghost_set I)))).
Proof.
  iIntros "(H1 & (H2 & H3))".
  iPoseProof (node_exist_in_tree with "[$H1 $H3]") as "%".
  unfold ghost_tree_rep at 1.
  apply (find_ghost _ _ _ g _) in H.
  destruct H as [node H].
  eapply (In_Znth_iff I) in H.
  destruct H as [i [H H1]].
  erewrite -> (iter_sepcon_Znth  _ _ i); eauto.
  erewrite H1.
  simpl.
  iDestruct "H2" as "(H22 & H32)".
  unfold ltree at 1.
  iDestruct "H22" as (lsh) "(%H2 & (H23 & H24))".
  iSplit.
  - iExists _.
    iFrame "H24".
    iIntros "H2".
    iFrame.
    unfold ghost_tree_rep.
    erewrite (iter_sepcon_Znth _ I i); auto.
    iFrame "H32".
    erewrite H1; simpl.
    unfold ltree.
    iExists _.
    iFrame. done.
  - unfold ltree at 2.
    iExists _.
    iSplitL "H23 H24".
    + iExists _. iFrame. done.
    + iIntros "H2". iFrame.
      unfold ghost_tree_rep.
      erewrite (iter_sepcon_Znth (λ p : mpredList,
       ltree (pnL p) (lockL p) (node_lock_inv_pred g (pnL p) (g_inL p) (NodeL p))) I i); auto.
      iFrame "H32".
      erewrite H1.
      simpl.
      iFrame "H2".
Qed.

Lemma in_tree_inv g g_in g_root (pn : val) (lock_in : val) (M: gmap key val):
    in_tree g g_in pn lock_in * CSS g g_root M |--
      (EX a, (inv_for_lock lock_in (node_lock_inv_pred g pn g_in a) *
      (inv_for_lock lock_in (node_lock_inv_pred g pn g_in a)
         -* CSS g g_root M))) &&
      (EX R, (ltree pn lock_in R) * (ltree pn lock_in R -* CSS g g_root M)).
Proof.
  unfold CSS.
  iIntros "[H1 H2]".
  iDestruct "H2" as (I) "((%H3 & H4) & H5)".
  iPoseProof (in_tree_inv1 I pn g g_in with "[H1 H4 H5]") as "H"; auto.
  + iFrame "H4". iFrame "H1 H5".
  + iSplit.
    * iDestruct "H" as "(H & _)".
      iDestruct "H" as (r) "(H1 & H2)".
      iExists r. iFrame.
      iIntros "H".
      iSpecialize ("H2" with "H").
      iDestruct "H2" as "(H1 & H2)".
      iExists I; iFrame; done.
    * iDestruct "H" as "(_ & H)".
      iDestruct "H" as (r) "(H1 & H2)".
      iExists r. iFrame.
      iIntros "H".
      iSpecialize ("H2" with "H").
      iDestruct "H2" as "(H1 & H2)".
      iExists I; iFrame; done.
Qed.

Program Definition traverse_spec :=
  DECLARE _traverse
          ATOMIC TYPE (rmaps.ConstType
                       (val * val * val * Z  * val * globals * gname * gname))
          OBJ M INVS ∅
  WITH b, n, lock, x, v, gv, g, g_root
  PRE [ tptr t_struct_pn, tint]
  PROP (and (Z.le (Int.min_signed) x) (Z.le x (Int.max_signed)); is_pointer_or_null v)
  PARAMS (b; Vint (Int.repr x)) GLOBALS (gv)
  SEP  (mem_mgr gv;
        in_tree g g_root n lock;
        !!(is_pointer_or_null lock /\ is_pointer_or_null n) && seplog.emp;
        EX (p: val), data_at Ews (t_struct_pn) (p, n) b ) | (CSS g g_root M)
  POST [ tint ]
  EX  pt: enum * (val * (share * gname )) %type,
  PROP () (* pt: enum * (val * (share * (gname * node_info))) *)
  LOCAL (temp ret_temp (enums pt.1))
  SEP (mem_mgr gv)| (CSS g g_root M).

(* t_struct_node represents for the generic-struct rather specific-data-structure *)

#[global] Instance gmap_inhabited V : Inhabitant (gmap key V).
Proof. unfold Inhabitant; apply empty. Defined.

#[global] Instance number_inhabited: Inhabitant number.
Proof. unfold Inhabitant; apply Pos_Infinity. Defined.

(*

Definition tree_rep_1 p (sh :share):= EX (tp pa pb vp: val) (xp : Z),
  field_at sh (t_struct_tree_t) [StructField _t] tp p *
  data_at sh t_struct_tree (Vint (Int.repr xp), (vp, (pa, pb))) tp *
  (!!(is_pointer_or_null pa /\ is_pointer_or_null pb) && seplog.emp).

Definition pn_rep p n (sh : share)(pn : val) :=
  data_at sh (t_struct_pn) (p, n) pn * tree_rep_1 p sh.

Definition pn_rep_1 (g g_root: gname) (sh : share) (pn n: val) :=
  EX (p: val), data_at sh (t_struct_pn) (p, n) pn.

Definition nodebox_rep (g : gname) (g_root : gname) (sh : share) (lock: val) (nb : val) :=
  EX (np: val) (lsh : share),
                data_at sh (tptr (t_struct_tree_t)) np nb *
                (!!(field_compatible t_struct_tree_t nil np /\ is_pointer_or_null lock) &&
                field_at lsh t_struct_tree_t [StructField _lock] lock np) *
                in_tree g g_root np lock.
*)

(*
(* Spec of findnext function *)
Definition findnext_spec :=
  DECLARE _findnext
  WITH x: Z, v: val, b: val, p: val, n: val, tp: val, 
       pa: val, pb: val, px: Z, pv: val, sh: share, gv: globals
  PRE [ tptr t_struct_pn, tint, tptr tvoid ]
          PROP (writable_share sh; is_pointer_or_null pa; is_pointer_or_null pb)
          PARAMS (b; Vint (Int.repr x); v) GLOBALS (gv)
          SEP (data_at sh (t_struct_pn) (p, n) b;
               field_at sh (t_struct_tree_t) [StructField _t] tp p;
               data_at sh t_struct_tree (Vint (Int.repr px), (pv, (pa, pb))) tp)
  POST [ tint ]
  EX (succ: bool), EX (n' : val),
         PROP (match succ with
               | true => ((n' = pa /\ (Z.lt (Int.signed (Int.repr x)) (Int.signed (Int.repr px)))) \/
                         (n' = pb /\ (Z.lt (Int.signed (Int.repr px)) (Int.signed (Int.repr x)))))
               | false => (n' = p /\ Int.signed (Int.repr x) = Int.signed (Int.repr px))
               end)
        LOCAL (temp ret_temp (Vint (if succ then Int.one else Int.zero)))
        SEP (match succ with
             | true =>
               (data_at sh (t_struct_pn) (p, n') b *
               field_at sh (t_struct_tree_t) [StructField _t] tp p *
               data_at sh t_struct_tree (Vint (Int.repr px), (pv, (pa, pb))) tp)
             | false =>
               (data_at sh (t_struct_pn) (p, n) b *
               field_at sh (t_struct_tree_t) [StructField _t] tp p *
               data_at sh t_struct_tree (Vint (Int.repr px), (pv, (pa, pb))) tp)
             end).

 *)


(* Spec of inrange function *)
Definition inRange_spec :=
  DECLARE _inRange
    WITH x: Z, p: val, min: Z, max : Z, sh: share, gv: globals
  PRE [ tptr t_struct_node, tint]
          PROP (writable_share sh; repable_signed min; repable_signed max; repable_signed x)
          PARAMS (p; Vint (Int.repr x)) GLOBALS (gv)
          SEP (
              field_at sh (t_struct_node) [StructField _min] (Vint (Int.repr min)) p;
              field_at sh (t_struct_node) [StructField _max] (Vint (Int.repr max)) p)
  POST [ tint ]
  EX (succ: bool),
         PROP (match succ with
               | true => (and (Z.lt min x) (Z.lt x max))
               | false => (or (Z.le x min) (Z.le max x))
               end)
        LOCAL (temp ret_temp (Vint (if succ then Int.one else Int.zero)))
        SEP (
             field_at sh (t_struct_node) [StructField _min] (Vint (Int.repr min)) p;
              field_at sh (t_struct_node) [StructField _max] (Vint (Int.repr max)) p).

(*Definition spawn_spec := DECLARE _spawn spawn_spec. *)

Check CSS .
Context `{N: NodeRep}.


Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec; 
                             inRange_spec; traverse_spec ]).

(* Proving inrange spec *)
Lemma body_inrange: semax_body Vprog Gprog f_inRange inRange_spec.
Proof.
  start_function.
  forward.
  forward_if ( PROP ()
                 LOCAL (temp _t'1 (if andb (min <? x) (x <? max) then Val.of_bool true else Val.of_bool false);
                        temp _t'2 (vint min); gvars gv; temp _p p; 
     temp _x (vint x))
     SEP (field_at sh t_struct_node (DOT _min) (vint min) p;
     field_at sh t_struct_node (DOT _max) (vint max) p)).
  - repeat forward. entailer !.
     destruct (Z.ltb_spec min x), (Z.ltb_spec x max); try rep_lia.
    + unfold Val.of_bool, Int.lt.
      autorewrite with norm; auto.
    + unfold Val.of_bool, Int.lt.
      Check Z.le_ge.
      apply Z.le_ge in H8.
      destruct (zlt x max); [try easy | auto].
  - forward.
    destruct (Z.ltb_spec min x); try rep_lia.
    entailer !.
  - forward_if; forward.
    + assert (((min <? x) && (x <? max))%bool = true) as Hx.
      { destruct((min <? x) && (x <? max))%bool; easy. }
      Exists true. entailer !.
    + assert (((min <? x) && (x <? max))%bool = false) as Hy.
      { destruct ((min <? x) && (x <? max))%bool; easy. }
      Exists false. entailer !.
Qed.


(* traverse invariants *)
Definition traverse_inv (b: val) (n pnN': val) (sh: share)
                        (x : Z) (v: val) (g_root: gname) (lock: val) gv
                        (inv_names : invariants.invG) (g : gname) AS : environ -> mpred :=
  (EX (pnN p: val) (gN_in: gname) (lockN_in: val),
            PROP ()
            LOCAL (temp _p pnN';  temp _status (vint 1);  temp _pn__2 b; temp _x (vint x);
                   (* temp _value v; *) gvars gv)
            SEP (data_at sh (t_struct_pn) (p, pnN) b;
                 in_tree g gN_in pnN lockN_in; in_tree g g_root pnN' lock;
                 !!(is_pointer_or_null lockN_in) && seplog.emp; AS; mem_mgr gv))%assert.

Definition traverse_inv_1 (b p: val) (sh: share) (x : Z) (g_root g_in: gname)
                          (g: gname) (r: node_info) :=
  data_at sh (t_struct_pn) (p, p) b * in_tree g g_in p r.1.1.2 *
  node_lock_inv_pred g p g_in r *
  (!!(key_in_range x r.1.2 = true /\ r.2 = Some None /\
      repable_signed (number2Z r.1.2.1) ∧
      repable_signed (number2Z r.1.2.2) /\ is_pointer_or_null r.1.1.2) && seplog.emp).

Definition traverse_inv_2 (b p: val) (sh : share) (x : Z) (g_root g_in: gname)
                          (g: gname) (r: node_info) :=
  data_at sh (t_struct_pn) (p, p) b *
  in_tree g g_in p r.1.1.2 *
  (* node_lock_inv_pred_1 g p g_in r x * *) (* modify it later*)
  (!!(repable_signed (number2Z r.1.2.1) ∧
      repable_signed (number2Z r.1.2.2) /\ is_pointer_or_null r.1.1.2) && seplog.emp).


(* PROVING traverse spec *)
Lemma traverse: semax_body Vprog Gprog f_traverse traverse_spec.
Proof.
  start_function.
  Intros p.
  forward.
  set (AS := atomic_shift _ _ _ _ _ ).
  (* New pt: bool * (val * (share * (gname * node_info))) *)
  forward_loop (traverse_inv b n n Ews x v g_root lock gv inv_names g AS)
    break: (*consider to remove gsh *)
    (EX (stt: enum) (q : val) (gsh: share) (g_in: gname) (r: node_info),
     PROP() LOCAL(temp _status (enums stt))
     SEP((match stt with
            | Zero => ((traverse_inv_1 b q Ews x g_root g_in g r) *
                      (!!(r.1.1.1 = nullval) && seplog.emp))
            | One => ((traverse_inv_1 b q Ews x g_root g_in g r) *
                      (!!(r.1.1.1 = nullval) && seplog.emp))
            | Two => ((traverse_inv_2 b q Ews x g_root g_in g r) *
                      (!!( r.1.1.1 <> nullval) && seplog.emp)) end) *
                       Q (stt, (q, (gsh, g_in))) * mem_mgr gv)).
  - unfold traverse_inv.
    Exists n p g_root lock. sep_apply in_tree_duplicate. entailer !.
    Check No_value_for_temp_variable _status. admit.
  - (*go deeply into loop*) (*pre-condition*)
    unfold traverse_inv.
    Intros pn p1 g_in lock_in.
    gather_SEP AS (in_tree g g_in pn lock_in).
    viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in) *
                          (EX lsh, !!(readable_share lsh) &&
                                     field_at lsh t_struct_node (DOT _lock) lock_in pn)).
    { go_lower.
      (* apply lock_alloc.*) (* fix later*) admit. }
    Intros lsh.
    forward.
    forward.
    sep_apply in_tree_duplicate.
    (* acquire(pn->n->lock); *)
    forward_call acquire_inv_atomic (lock_in,
        AS  * (EX R, node_lock_inv_pred g pn g_in R)  ).
    {
      iIntros "[[[[[[HITlkin HITlkin1] HAS] H4] H5] HITlkin2] H7]".
      iCombine "HITlkin HAS" as "HITlkin".
      iCombine "HITlkin HITlkin1 H4 H5 HITlkin2 H7" as "HITAS".
      iVST.
      apply sepcon_derives; [| cancel_frame].
      unfold atomic_shift. iIntros "AU". iAuIntro; unfold atomic_acc; simpl.
      iDestruct "AU" as "[#HITlkin AU]".
      iMod "AU" as (m) "[Hm HClose]".
      iModIntro.
      iPoseProof (in_tree_inv g g_in g_root with "[$HITlkin $Hm]") as "InvLock".
      iDestruct "InvLock" as "(InvLock & _)".
      iDestruct "InvLock" as (r) "[H1 H2]".
      iExists _. iFrame.
      iSplit; iFrame.
      iIntros "H1".
      iSpecialize ("H2" with "H1").
      iFrame "HITlkin".
      iDestruct "HClose" as "[HClose _]".
      iSpecialize ("HClose" with "H2"); auto.
      iIntros (m') "((H1 & H1') & _)".
      iSpecialize ("H2" with "H1").
      iDestruct "HClose" as "[HClose _]".
      iSpecialize ("HClose" with "H2").
      iMod ("HClose").
      iFrame "HClose". by iExists _.
    }
    Intros r.
    forward.
    forward.
    unfold node_lock_inv_pred, node_rep.
    Intros.
    forward.
    (* inrange function *)
    forward_call(x, pn, (number2Z r.1.2.1), (number2Z r.1.2.2), Ews, gv).
    Intros succ1.
    destruct succ1.
    + forward_if.
      forward.
      forward.
      entailer. admit.
      (*tp = nullval --- pn->p->t == NULL; break*)
      forward_if. 
      entailer. admit.
      viewshift_SEP 0 (EX y, Q y * (in_tree g g_in pn lock_in) *
                               (!!(y = (2, (pn, (lsh, g_in)))) && seplog.emp)).
      {
        admit.
      }
      unfold node_rep_R. 
      forward.
      simpl.
      Exists  (2, (pn, (lsh, g_in))). entailer !. admit.
      forward.
      simpl.
      
      entailer !.
      Exists _.




      
      unfold tree_rep_R.
      rewrite -> if_true; auto.
      Intros.
      gather_SEP (in_tree g g_in pn r.1.1.2) (in_tree g g_in pn lock_in).
      viewshift_SEP 0 (in_tree g g_in pn r.1.1.2 * in_tree g g_in pn lock_in *
                         (!!(r.1.1.2 = lock_in) && seplog.emp)).
      {
        go_lower.
        iIntros "(H1 & H2)".
        iPoseProof (in_tree_equiv g g_in pn with "[$H1 $H2]") as "%Hx".
        iFrame. edestruct Hx; auto.
      }
      Intros.
      (* push back lock into invariant *)
      gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_tree_t _ _ pn).
      viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in)).
      {
        go_lower.
        iIntros "((AU & #H) & H1)".
        iMod "AU" as (m) "[Hm HClose]".
        iPoseProof (in_tree_inv g g_in g_root with "[$H $Hm]") as "InvLock".
        iDestruct "InvLock" as "(_ & InvLock)".
        iDestruct "InvLock" as (R) "[H1' H2']".
        unfold ltree.
        iDestruct "H1'" as (lsh1) "(%H12 & (H12 & H13))".
        iAssert(EX lsh0 : share,
           !! (field_compatible t_struct_tree_t [] pn ∧ readable_share lsh0 ) &&
           (@field_at CompSpecs lsh0 t_struct_tree_t (DOT _lock) lock_in pn *
               inv_for_lock lock_in R))
               with "[H1 H12 H13]" as "H1'".
        {
          destruct H12 as (Hf & Hrs).
          iPoseProof (lock_join with "[H1 H12]") as "H1".
          { iSplitL "H1"; iFrame; iPureIntro; auto. }
          iDestruct "H1" as (Lsh) "(% & H1)".
          iExists _. iFrame; iPureIntro; repeat (split; auto).
        }
        iSpecialize ("H2'" with "H1'").
        iDestruct "HClose" as "(HClose & _)".
        iSpecialize ("HClose" with "H2'").
        iMod "HClose". by iFrame. 
      }
      viewshift_SEP 0 (EX y, Q y * (in_tree g g_in pn lock_in) *
                               (!!(y = (true, (pn, (Ews, (g_in, r))))) && seplog.emp)).
      {
        go_lower.
        iIntros "(AU & #HITlkin)".
        iMod "AU" as (m) "[Hm HClose]".
        iDestruct "HClose" as "[_ HClose]".
        iSpecialize ("HClose" $! (true, (pn, (Ews, (g_in, r))))).
        iFrame "HITlkin".
        iMod ("HClose" with "[Hm]") as "Hm".
        iFrame "Hm".
        iModIntro. iExists _.
        by iFrame "Hm".
      }
      Intros y.
      forward.
      unfold traverse_inv_1, node_lock_inv_pred, node_rep, tree_rep_R.
      Exists true pn Ews g_in r.
      Intros.
      rewrite -> if_true; auto.
      subst.
      destruct r.1.2.
      simpl in H5.
      go_lower.
      entailer !.
      iIntros "(H & _)"; iFrame.
      unfold tree_rep_R.
      rewrite -> if_false; auto.
      Intros ga gb x0 v1 pa pb locka lockb.
      (*findNext*)
      forward_call(x, v, b, pn, pn, r.1.1.1, pa, pb, x0, v1, Ews, gv).
      {
        Intros succ.
        assert_PROP(r.1.1.1 <> nullval) by entailer !.
        destruct succ.1.
        destruct H12 as [(Hx & Hy) | Hz].
        + forward_if.
          pose proof (Int.one_not_zero); easy.
          (* flag = 0 *)
          Intros.
          forward.
          forward.
          gather_SEP (in_tree g g_in pn r.1.1.2) (in_tree g g_in pn lock_in).
          assert_PROP (r.1.1.2 = lock_in) as Hlk.
          { sep_apply in_tree_equiv; entailer !. }
          rewrite Hlk.
          Intros.
          (* push back lock into invariant *)
          gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_tree_t _ _ pn).
          viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in)).
          { go_lower; apply push_lock_back; auto. }
          sep_apply (in_tree_duplicate g ga pa locka).
          (* _release(_t'8);) *)
          forward_call release_inv (lock_in, node_lock_inv_pred g pn g_in r, AS).
          {
            lock_props.
            iIntros "(((((((((((((((HITlka & HITlka1) & HAS) &
                     HITlkin) & HITlkin1) & Hdtb) & Hdtpn) & Hdtpapb) & Hftmin) & Hftmax) &
                     Hmhr) & Hmlpn) & Hmlpn') & HITlkb) & HITlkin2) & Hgv)".
            iCombine "HAS HITlkin Hmhr Hftmin Hftmax Hmlpn Hdtpn Hdtpapb
                      Hmlpn' HITlka HITlkb HITlkin1 Hdtb HITlka1 HITlkin2 Hgv"
              as "Hnode_inv_pred".
            iVST.
            rewrite Hx.
            rewrite <- 10sepcon_assoc; rewrite <- 2sepcon_comm.
            apply sepcon_derives; [| cancel_frame].
            apply release_root; try repeat (split; auto); auto.
         }
        (* proving |--  traverse_inv *)
        Exists pa pn ga locka. entailer!. by iIntros "_".
    + (* if (_b == (0)) *)
      forward_if.
      pose proof (Int.one_not_zero); easy.
      Intros.
      forward.
      forward.
      destruct Hz as (Hz & Ht).
      gather_SEP (in_tree g g_in pn r.1.1.2) (in_tree g g_in pn lock_in).
      assert_PROP (r.1.1.2 = lock_in) as Hlk.
      { sep_apply in_tree_equiv; entailer !. }
      rewrite Hlk.
      Intros.
      (* push back lock into invariant *)
      gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_tree_t _ _ pn).
      viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in)).
      { go_lower; apply push_lock_back; auto. }
      sep_apply (in_tree_duplicate g gb pb lockb).
      Intros.
      (* _release(_t'8);) *)
      forward_call release_inv (lock_in, node_lock_inv_pred g pn g_in r, AS).
      {
        lock_props.
        iIntros "(((((((((((((((HITlkb & HITlkb1) & HAS) & HITlkin) & HITlkin1) & Hdtb) & Hdtpn) & Hdtpapb) & Hftmin) & Hftmax) & Hmhr) & Hmlpn) & Hmlpn') & HITlka) & HITlkin2) & Hgv)".
        iCombine "HAS HITlkin Hmhr Hftmin Hftmax Hmlpn Hdtpn Hdtpapb  Hmlpn' HITlka HITlkb  HITlkin1 Hdtb HITlkb1 HITlkin2 Hgv" as "Hnode_inv_pred".
        iVST.
        rewrite Hz.
        rewrite <- 10sepcon_assoc; rewrite <- 2sepcon_comm.
        apply sepcon_derives; [| cancel_frame].
        apply release_root; try repeat (split; auto); auto.
      }
      (* proving |--  traverse_inv *)
      Exists pb pn gb lockb. entailer!. by iIntros "_".
    + destruct H12 as (Hx & Hy).
      forward_if.
      assert_PROP (r.1.1.2 = lock_in) as Hlk. { sep_apply in_tree_equiv; entailer !. }
      rewrite Hlk.
      Intros.
      (* push back lock into invariant *)
      gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_tree_t _ _ pn).
      viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in)).
      { go_lower; apply push_lock_back; auto. }
      viewshift_SEP 0 (EX y, Q y * (in_tree g g_in pn lock_in) *
                                (!!( y = (false, (pn, (Ews, (g_in, r))))) && seplog.emp)).
      {
        go_lower.
        iIntros "(AU & #HITlkin)".
        iMod "AU" as (m) "[Hm HClose]".
        iDestruct "HClose" as "[_ HClose]".
        iSpecialize ("HClose" $! (false, (pn, (Ews, (g_in, r))))).
        iFrame "HITlkin".
        iMod ("HClose" with "[Hm]") as "Hm". iFrame "Hm".
        iModIntro.
        iExists _. by iFrame "Hm".
      }
      Intros y.
      forward.
      forward.
      unfold traverse_inv_2, node_lock_inv_pred_1, node_rep_1, tree_rep_R_1.
      Exists false pn Ews g_in r.
      subst.
      Exists ga gb v1 pa pb locka lockb.
      rewrite ! Int.signed_repr in Hy; auto.
      subst.
      entailer !. by iIntros "_".
      pose proof Int.one_not_zero; easy.
    }
    pose proof Int.one_not_zero; easy. 
   + assert_PROP (r.1.1.2 = lock_in) as Hlk.
     { sep_apply in_tree_equiv; entailer !. }
     rewrite Hlk.
     assert_PROP(is_pointer_or_null r.1.1.1) by entailer !.
     gather_SEP (field_at _ t_struct_tree_t (DOT _t) _ pn)
                (field_at _ _ (DOT _min) _ pn)
                (field_at _ _ (DOT _max) _ pn)
                (malloc_token Ews t_struct_tree_t pn)
                (in_tree g g_in pn lock_in) (tree_rep_R r.1.1.1 r.1.2 r.2 g).
     viewshift_SEP 0 (node_rep pn g g_in r).
     {
       go_lower.
       unfold node_rep.
       rewrite Hlk.
       iIntros "(((((? & ?) & ?) & ?) & ?) & ?)".
       by iFrame.
     }
     Intros.
     forward_if.
     pose proof (Int.one_not_zero).
     assert (Int.zero <> Int.one); try easy.
     forward.
     forward.
     (* push back lock into invariant *)
     gather_SEP AS (in_tree g g_in pn lock_in) (field_at lsh t_struct_tree_t _ _ pn).
     viewshift_SEP 0 (AS * (in_tree g g_in pn lock_in)).
     { go_lower; apply push_lock_back; auto. }
     forward_call release_inv (lock_in, node_lock_inv_pred g pn g_in r, AS).
     {
       lock_props.
       iIntros "((((((HAS & HITlkin) & Hnode) & Hdtb) & Hmhr) & HITlkin1) & Hgv)".
       iCombine "HAS HITlkin Hmhr Hnode HITlkin1 Hdtb Hgv" as "Hnode_inv_pred".
       iVST.
       rewrite <- 3sepcon_assoc; rewrite <- 2sepcon_comm.
       apply sepcon_derives; [| cancel_frame].
       unfold atomic_shift; iIntros "(((AU & #HITlkin) & Hmhr) & Hnode)";
            iAuIntro; unfold atomic_acc; simpl.
       iMod "AU" as (m) "[Hm HClose]".
       iModIntro.
       iExists tt.
       iAssert (node_lock_inv_pred g pn g_in r) with "[$Hmhr $Hnode]" as"Hnode_Iinv".
       iPoseProof (in_tree_inv' g g_in g_root pn lock_in _ r
                         with "[$HITlkin $Hnode_Iinv $Hm]") as "(HI1 & HI2)".
       iSplitL "HI1"; iFrame.
       iSplit.
       {
         iIntros "(Hnode_Iinv & InvLock)".
         iSpecialize ("HI2" with "InvLock").
         iDestruct "HClose" as "[HClose _]".
         iFrame.
         by iSpecialize ("HClose" with "HI2").
       }
       iIntros (_) "(H & _)".
       iSpecialize ("HI2" with "H").
       iDestruct "HClose" as "[HClose _]".
       by iSpecialize ("HClose" with "HI2").
    }
    forward.
    Exists n pn g_root lock.
    sep_apply (in_tree_duplicate g g_root n).
    entailer !.
    - (* semax Delta (PROP ( )  RETURN ( ) SEP ()) (return _flag;) POSTCONDITION *)
       Intros flag.
       Intros pn gsh g_in r.
       unfold traverse_inv_1, traverse_inv_2.
       destruct flag.
       + forward.
         Exists (true, (pn, (gsh, (g_in, r)))).
         simpl. entailer !. 
       + forward.
         Exists (false, (pn, (gsh, (g_in, r)))).
         simpl.
         unfold node_lock_inv_pred_1, node_rep_1 at 1, tree_rep_R_1 at 1.
         Intros g1 g2 v1 p1 p2 l1 l2.
         rewrite H7.
         entailer !.
         exists v1, g1, g2; auto.
         unfold node_lock_inv_pred, node_rep, tree_rep_R.
         rewrite -> if_false; auto.
         simpl.
         Exists g1 g2 x v1 p1 p2 l1 l2.
         entailer !. apply derives_refl.
Qed.
