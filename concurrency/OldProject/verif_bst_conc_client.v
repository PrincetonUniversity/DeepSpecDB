Require Import VST.veric.rmaps.
Require Import VST.concurrency.conclib.
Require Import VST.atomics.SC_atomics.
Require Import VST.veric.bi.
Require Import VST.floyd.library.
(* Require Import VST.floyd.sublist.  *)
Require Import VST.atomics.general_atomics.
Require Import VST.msl.iter_sepcon.
Require Import bst.bst_conc.
Require Import bst.verif_bst_conc_atomic.
Require Import bst.bst_client.
Import List.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Section Proofs.

Definition surely_malloc_spec :=
 DECLARE _surely_malloc
   WITH t : type, gv : globals
   PRE [ tuint ]
       PROP (0 <= sizeof t <= Int.max_unsigned; complete_legal_cosu_type t = true;
             natural_aligned natural_alignment t = true)
       PARAMS (Vint (Int.repr (sizeof t))) GLOBALS (gv)
       SEP (mem_mgr gv)
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       RETURN (p)
       SEP (mem_mgr gv; malloc_token Ews t p; data_at_ Ews t p).

Inductive bst_hist_el :=
  | MInsert (k : key) (v : val) | MLookup (k : key) | MDelete (k : key).

Notation hist := (nat -> option bst_hist_el).

Fixpoint apply_hist (M:gmap key val)  h :=
  match h with
  | [] => M
  | MInsert k v :: h' => apply_hist (<[k:=v]>M) h'
  | MLookup k :: h' => match M !! k with Some v' => apply_hist M h' 
                       | None => apply_hist M h' end
  | MDelete k :: h' => match M !! k with Some v' =>  apply_hist (delete k M) h'
                       | None => apply_hist M h' end
  end.

Definition is_write(el: bst_hist_el) :=
match el with 
  | MInsert _ _ => true
  | MDelete _ => true
  | _ => false
  end.

(*Instance join_bool: sepalg.Join bool := fun a b c => andb a b = c. 

Program Instance bool_ghost: Ghost :=
{ valid := fun _ => True; Join_G := join_bool }.
Next Obligation.  exists (fun _ => true); auto; intros. unfold sepalg.unit_for. hnf.
destruct t; auto.
Defined.
Next Obligation.
  intros. hnf in *.
  constructor.
  - unfold join; congruence.
  - unfold join; eexists; split; eauto.
    rewrite Nat.max_assoc; subst; auto.
  - unfold join; intros.
    rewrite Nat.max_comm; auto.
  - unfold join; intros.
    apply Nat.le_antisymm; [subst b | subst a]; apply Nat.le_max_l.
Qed. 

Definition tf_order : bool -> bool -> Prop :=
false, true -> False
_ -> True *)

(*if the implicit arg is needed, it would be bool_ghost* -> exclusive_PCM) *)

(*Program Instance boolean_ord: PCM_order . *)
Locate NoneP.

Definition ghost_events (v : option val) g := ghost_master1 (P := @option_PCM (discrete_PCM _)) v g. (*
  own(RA := @option_PCM (discrete_PCM _)) g (v) compcert_rmaps.RML.R.NoneP
*)
(*Typeclasses eauto := 3. *) (*Avoid endless compilation*)

Definition set_snap (v : val) pgname := ghost_snap (P := @option_PCM (discrete_PCM val)) (Some v) pgname.
Locate exclusive_PCM.
Definition reader_token g := excl g tt.
(*The term "Some M" has type "option (gmap key val)"
while it is expected to have type "option (Z → option Z)".*)



Definition bst_inv gh ghi gvbd g (g_root:gname) (pgname: gname) (grt: gname) (gv : globals) := EX M : _,  tree_rep g g_root M  * 
  EX hr : _, !!(apply_hist empty hr = M) && ghosts.ghost_ref hr gh * EX p_set, ghost_events p_set pgname*
  ghost_var gsh2 (List.filter is_write hr) ghi * EX v : Z, ghost_var gsh2 (vint v) gvbd *
  (( match M !! 2 with Some p => EX sh, !!(readable_share sh  /\ repable_signed v) && data_at sh tint (vint v) p  *
  if (eq_dec v 4) then
 !! ( p_set = Some p ) && (( EX (p2: val) sh1, !!(M !! 1 = Some p2  /\ readable_share sh1) && (*We need this part for "fixing" the pointer in the tree*)
 ( data_at Ews tint (Vint (Int.repr 3)) p2 * data_at Ews tint (vint 1) (gv _a) * 
 EX sh_b, !! (readable_share sh_b) && data_at sh_b tint (vint 2) (gv _b) )) || reader_token grt ) (* * 
 nodebox_rep g g_root sh lock b *)(*other thread resourse - nodebox_rep*) 
  else !!(p_set = None) && emp  | None => !!(p_set = None) && emp end)).

(*
 void* update_tree(void* t){
  a = 1;
  b = 2;
  c = 3; 
  d = 4;
  insert(t, 1, &a);
  insert(t, 2, &b);
  insert(t, 1, &c);
  insert(t, 2, &d);
  return (void* )NULL;
}
*)

Definition update_tree_spec :=
 DECLARE _update_tree
    WITH b : val, x :  share * share * val * globals * gname * gname 
    * gname  * iname * gname * gname * gname * gname * invG
   PRE [ tptr tvoid ] 
     let '(sh, gsh, lock, gv, g, g_root, pgname, i, gh, ghi, gvbd, grt, inv_names) := x in
       PROP ( readable_share sh; isptr lock; gsh <> Share.bot) 
        PARAMS ( b ) GLOBALS ( gv )
          SEP  (mem_mgr gv; 
          invariant i (bst_inv gh ghi gvbd g g_root pgname grt gv);
          data_at_ Ews tint (gv _a);
          data_at_ Ews tint (gv _b); 
          data_at_ Ews tint (gv _c);
          data_at_ Ews tint (gv _d);
          nodebox_rep g g_root sh lock b; 
          ghost_hist(hist_el := bst_hist_el) gsh empty_map gh;
          ghost_var gsh1 ([] : list bst_hist_el) ghi;
          ghost_var gsh1 ((Vint (Int.repr 0))) gvbd
          )  
   POST [ tptr tvoid ] PROP () LOCAL () SEP (). (*Postcondition is empty - all of the useful info on the thread's work will be reflected in the bst_inv*)



(*int retrieve_value(treebox t){
  void* searchResult;
  int y = -1;
  do {
     searchResult = lookup (t,  2);
     if (searchResult != NULL) {
        y = *((int* ) searchResult);
     }
  } while (y != 4);
   searchResult = lookup (t,  1);
   return *((int* ) searchResult);
}*)

Definition retrieve_value_spec :=
 DECLARE _retrieve_value
   WITH gv : globals, sh : share, i : iname, b : val, gh : gname, ghi : gname, g : gname,
 gvbd : gname, pgname : gname, g_root : gname, lock : val, gsh : share, grt : gname, inv_names : invG
   PRE [ tptr (tptr t_struct_tree_t)] 
       PROP (readable_share sh; isptr lock ) (*Required by the insert function*)
        PARAMS (b ) GLOBALS ( gv ) (*key is an int, value is a pointer*)
          SEP  (mem_mgr gv; nodebox_rep g g_root sh lock b; reader_token grt;
    invariant i (bst_inv gh ghi gvbd g g_root pgname grt gv))
   POST [ tint  ]  EX ret: val,
    PROP ( ret = vint 3)
    LOCAL (temp ret_temp (Vint (Int.repr (3))))
    SEP (mem_mgr gv; nodebox_rep g g_root sh lock b;  EX (p2: val), 
         data_at Ews tint (Vint (Int.repr 3)) p2; data_at Ews tint (vint 1) (gv _a);
         EX sh_b, !! (readable_share sh_b) && data_at sh_b tint (vint 2) (gv _b)).

(*
int main(){
  treebox t;
  t = treebox_new();  
  int* result;
  spawn((void* )&update_tree, t);
  int retVal =  retrieve_value(t);
  treebox_free(t);
  return 0;
} *)

Definition main_spec :=
 DECLARE _main
   WITH gv : globals
   PRE  [] main_pre prog tt gv
   POST [ tint ] PROP () LOCAL () SEP (). (*Postcondition is empty - all resources were cleared*)


Definition Gprog : funspecs := [insert_spec; lookup_spec; delete_spec; treebox_new_spec;
update_tree_spec; retrieve_value_spec; spawn_spec; main_spec].


Lemma lookup_empty_hist :  forall M0 hr M k, (forall v, ~ In (MInsert k v) (List.filter is_write hr)) -> 
apply_hist M0 hr =  M ->
((M !! k = M0 !! k) ∨ (M !! k = None)). 
Proof.
intros.
generalize dependent M0. generalize dependent M.
induction hr; simpl in *.
- intros. inversion H0. auto. 
- intros. destruct a; simpl in *.  spec IHhr. { intros. specialize H with v0. auto. }
 -- apply IHhr in H0. inversion H0. rewrite lookup_insert_ne in H1. auto. 
    specialize H with v.  apply not_in_cons in H. destruct H as [key_not_eq not_in]. 
    congruence. auto.
 -- apply IHhr; destruct (M0 !! k0); auto.  
 -- destruct (M0 !! k0). apply IHhr in H0; auto. inversion H0. destruct (decide (k = k0)).
    rewrite <- e in H1. rewrite lookup_delete in H1. auto. rewrite H1. 
    rewrite lookup_delete_ne; auto. auto. intros. intros not_in. specialize H with v0. contradiction H. auto.
apply IHhr.  intros. intros not_in. specialize H with v. contradiction H. auto. auto.
 Qed.
(*Reestablish that ghosts are synchronized - use update from ghosts.v*)


Definition get_val_from_hist (h: list bst_hist_el)(k: key) := (apply_hist empty h) !! k.

Lemma lookup_key_newest : forall M0 (h: list bst_hist_el), apply_hist M0 h = apply_hist M0 (List.filter is_write h).
Proof.
intros. generalize dependent M0.
induction h. auto.
 destruct a; simpl; intros.
 - auto.
 - destruct  (M0 !! k); auto.
 - destruct (M0 !! k); auto.
Qed.

Instance ghost_tree_rep_timeless : forall t g range, Timeless (ghost_tree_rep t g range).
Proof.
  intros. revert g range. induction t; intros. 
  - simpl. unfold public_half. apply (@bi.sep_timeless); apply own_timeless.
  - simpl. destruct range as [l r]. apply (@bi.sep_timeless). 
    apply (@bi.sep_timeless). 
    * unfold public_half. apply (@bi.sep_timeless); apply own_timeless.
    * apply IHt1.
    * apply IHt2.
Qed.

Instance tree_rep_timeless : forall g g_root M, Timeless (tree_rep g g_root M).
Proof.
  intros; unfold tree_rep. apply _.
Qed.



Lemma apply_hist_app : forall h1 h2 M, apply_hist M (h1 ++ h2) =
   apply_hist (apply_hist M h1) h2.
Proof.
  induction h1; intros; auto. simpl.
  destruct a; auto. rewrite IHh1.
  - destruct (M !! k); auto. 
  - destruct (M !! k); auto. 
Qed. 


Lemma excl_unique : forall T a1 a2 g, @excl T g a1 * @excl T g a2 |-- FF.
Proof.
intros. rewrite own_op'. Intros a3. inversion H. subst. inversion H2. 
Qed.



Lemma body_update_tree : semax_body Vprog Gprog f_update_tree update_tree_spec.
Proof.
start_function.
repeat forward.
assert_PROP (isptr (gv _a)) as isprt_a. entailer!. assert_PROP (isptr (gv _b)) as isprt_b. entailer!.  
assert_PROP (isptr (gv _c)) as isprt_c. entailer!. assert_PROP (isptr (gv _d)) as isprt_d. entailer!. 
rewrite invariant_dup. (* copy the invariant for future calls *)
(*insert(t, 1, &a);*)
forward_call(b, sh, lock, 1, gv _a, gv, g, g_root, EX h' : _, 
!!(add_events empty_map [MInsert 1 (gv _a)] h') && ghost_var gsh1 [(MInsert 1 (gv _a))] ghi * ghost_hist gsh h' gh, inv_names).
{ 
 rewrite <- (sepcon_comm (ghost_var gsh1 [] ghi)).
 rewrite <- (sepcon_comm (ghost_hist gsh empty_map gh)).
rewrite <- 6sepcon_assoc. rewrite -> 5sepcon_assoc.  apply sepcon_derives; [|cancel].
iIntros "[[gvh hist] #inv]".  
     unfold atomic_shift; iAuIntro.
      rewrite /atomic_acc /=.
      iMod (inv_open top with "inv") as "[ins Hclose]"; [auto|].  
iMod (bi.later_exist_except_0 with "ins") as "ins". 
  iDestruct "ins" as (M) "(treerep & ins)". iExists M.  iMod "treerep". 



 iMod (fupd_mask_subseteq) as "Hclose'".
      { apply empty_subseteq. }
      iModIntro. 
 iFrame "treerep". iSplit. 

(*instantiate (1 := [data_at Ews tint (vint 3) (gv _c); data_at Ews tint (vint 4) (gv _d); 
  data_at Ews tint (vint 1) (gv _a); data_at Ews tint (vint 2) (gv _b); ghost_var gsh1 ((Vint (Int.repr 0))) gvbd; 
  invariant i (bst_inv gh ghi gvbd g g_root pgname grt gv)  ]) in (value of Frame).
  subst Frame. simpl. cancel.
iIntros "[invar ghv]". iDestruct "invar" as "(inv  & hist)". unfold atomic_shift. 
iExists (ghost_hist gsh empty_map gh * ghost_var gsh1 [] ghi);(*Frame everything but the invariant*)
iFrame "hist".  iFrame "ghv". iSplitL ""; auto. iSplit; [|iApply invariant_cored; auto].
iIntros "combo". iDestruct "combo" as "(hist & gvh)". iMod "hist". iMod (inv_open top with "inv") as "[inv Hclose]"; [auto|].
unfold bst_inv at 1. iDestruct "inv" as (M) "[bst inv]". iDestruct "inv" as (hr) "inv".  iDestruct "inv" as "[ref ins]". 
iDestruct "ref" as "[gvh2 ref]". iMod "gvh2". iDestruct "gvh2" as "%gvh2". iExists M. iMod "bst". iFrame "bst". iMod "gvh".   
iMod (fupd_mask_subseteq) as "Hclose'". { apply empty_subseteq. } (*other invariants do not affect the proof*) 
iModIntro. iSplit. iFrame. *)
  + iIntros "bst". iMod "Hclose'".  iMod ("Hclose" with "[bst ins]"); auto. iNext. iExists (M). iSplitL "bst"; auto. iFrame.
     auto. 
  + iDestruct "ins" as (hr) "ins".  iDestruct "ins" as "[ref ins]". 
    iDestruct "ref" as "[gvh2 ref]".  iMod "gvh2". iDestruct "gvh2" as "%gvh2".
    iIntros (bs) "[[% bst] _]".  iMod (bi.later_exist_except_0 with "ins") as "ins_v". iDestruct "ins_v" as (p_set) "ins_v". 
    iDestruct "ins_v" as "(ins_v & ins)". iMod "ref".  
    (*IExists None for all inserts until the last one, the last one - some gv _d*)
    iPoseProof (hist_ref_incl with "[$hist $ref]") as "%"; [auto|].  
    iMod (hist_add' _ _ _ ( MInsert 1 (gv _a)) with "[$hist $ref]") as "[hist ref]"; [auto|]. (*adding insertion of gv _a to the history*)
    iMod "ins_v". iDestruct "ins_v" as "(snap & gvh2)". iCombine "gvh" "gvh2" as "gvh". 
    setoid_rewrite (ghost_var_share_join' gsh1 gsh2 Tsh _ _ ghi); eauto. (*Join parts of the ghost_var for adding the insertion of a*)
    iDestruct "gvh" as "[% gvh]". 
    iMod (ghost_var_update ( A := list bst_hist_el) _ ghi [MInsert 1 (gv _a)] with "[$gvh]") as "gvh". (*split right back*)
    rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share. iDestruct "gvh" as "[gvh gvh2]". 
    iDestruct "bst" as "(bst & ghostref)". iMod "Hclose'". iMod ("Hclose" with "[bst gvh2 ghostref ins ref snap]").
    { iNext. unfold bst_inv. iExists (<[1:=gv _a]> M). iSplitL "bst ghostref". unfold tree_rep. iExists tg; iFrame; 
      iFrame; auto. iExists (hr ++ [MInsert 1 (gv _a)]). iSplitL "ref". 
      { iFrame; auto. rewrite apply_hist_app H2. rewrite <- H2. simpl. iPureIntro. rewrite gvh2. auto. }
      iExists p_set. iFrame "snap".  apply lookup_empty_hist with (k := 2) in gvh2. rewrite List.filter_app. rewrite <- H2. simpl.  iFrame "gvh2". iDestruct "ins" as (v) "(gh2 & ins)".
      iExists v. iFrame "gh2". rewrite lookup_empty in gvh2. simpl in gvh2. assert (M !! 2 = None). { destruct gvh2; auto. 
      }
      rewrite H3. simpl.   rewrite lookup_insert_ne; auto. rewrite H3. auto. rewrite <- H2; auto. 
    } 
    iExists (map_upd empty_map (length hr) (MInsert 1 (gv _a))). iModIntro. iFrame. iSplit. iPureIntro. auto. 
    apply add_events_1. apply hist_incl_lt. exact H1. iFrame; auto. }

Intros hist_a.
rewrite invariant_dup.
(*insert(t, 2, &b);*)

forward_call(b, sh, lock, 2, gv _b, gv, g, g_root, EX h' : _, !!(add_events hist_a [MInsert 2 (gv _b)] h') && 
ghost_var gsh1 [(MInsert 1 (gv _a)); MInsert 2 (gv _b)] ghi * ghost_hist gsh h' gh *
ghost_var gsh1 ((Vint (Int.repr 2))) gvbd, inv_names).
{ (* instantiate (1 := [data_at Ews tint (vint 3) (gv _c); data_at Ews tint (vint 4) (gv _d); 
  data_at Ews tint (vint 1) (gv _a);  invariant i (bst_inv gh ghi gvbd g g_root pgname grt gv)]) in (value of Frame).
  subst Frame. simpl. cancel. iIntros "[combo inv]". iDestruct "combo" as "(((ghv & hist) & data_b) & gvbd)".
  unfold atomic_shift. iExists (ghost_hist gsh hist_a gh * data_at Ews tint (vint 2) (gv _b) * ghost_var gsh1 [MInsert 1 (gv _a)] ghi 
  * ghost_var gsh1 ((Vint (Int.repr 0))) gvbd). (*Frame everything but the invariant*)
  iFrame "hist".  iFrame "data_b". iFrame "ghv". iFrame "gvbd". (*Frame everything but the invariant*)
  iSplitL ""; auto. 
  iSplit; [|iApply invariant_cored; auto].
  iIntros "combo". iDestruct "combo" as "(((>hist & >data_b) & gvh) & gvdb)". (*reintroduce previously framed pieces*)
  iMod (inv_open top with "inv") as "[inv Hclose]"; [auto|]. unfold bst_inv at 1. iDestruct "inv" as (M) "[bst inv]". 
  iDestruct "inv" as (hr) "inv".  iDestruct "inv" as "[ref ins]". iDestruct "ref" as "(appl_hist & ref)". iMod "ref". 
  iMod "appl_hist". iDestruct "appl_hist" as "%appl_hist". 
  iExists (M). iMod "bst". iFrame "bst". iMod "gvh". 
  iDestruct "ins" as (p_set) "((gh_ev & gvh2) & ins)".  iMod (bi.later_exist_except_0 with "ins") as "ins". 
  iDestruct "ins" as (v) "(gvar & ins)".
  iMod (fupd_mask_subseteq) as "Hclose'". { apply empty_subseteq. } 
  iModIntro. iSplit. iFrame.  *)
  rewrite <- (sepcon_comm (data_at Ews tint (vint 2) (gv _b))).
  rewrite <- (sepcon_comm (ghost_var gsh1 (vint 0) gvbd)).
  rewrite <- 7sepcon_assoc. rewrite -> 3sepcon_assoc.  apply sepcon_derives; [|cancel].
  iIntros "[[[[gvdb data_b] gvh] hist] #inv]".  
  unfold atomic_shift; iAuIntro. rewrite /atomic_acc /=.
  iMod (inv_open top with "inv") as "[ins Hclose]"; [auto|].  
  iMod (bi.later_exist_except_0 with "ins") as "ins". 
  iDestruct "ins" as (M) "(treerep & ins)". iExists M.  iMod "treerep". 
  iMod (fupd_mask_subseteq) as "Hclose'".
      { apply empty_subseteq. }
      iModIntro. 
  iFrame "treerep". iSplit. 
  + iIntros "bst". iMod "Hclose'". iMod ("Hclose" with "[bst ins]"); auto.
    iNext. iExists (M). iSplitL "bst"; auto. iFrame. auto.
  + iIntros (bs) "[[% bst] _]".
    iDestruct "ins" as (hr) "ins".  iDestruct "ins" as "[ref ins]". iDestruct "ref" as "(appl_hist & ref)". iMod "ref". 
    iMod "appl_hist". iDestruct "appl_hist" as "%appl_hist". 
    iDestruct "ins" as (p_set) "((gh_ev & gvh2) & ins)".  iMod (bi.later_exist_except_0 with "ins") as "ins". 
    iDestruct "ins" as (v) "(gvar & ins)".
    iPoseProof (hist_ref_incl with "[$hist $ref]") as "%"; [auto|].
    iMod (hist_add' _ _ _ ( MInsert 2 (gv _b)) with "[$hist $ref]") as "[hist ref]"; [auto|].
    iMod "gvh2". iCombine "gvh" "gvh2" as "gvh". setoid_rewrite (ghost_var_share_join' gsh1 gsh2 Tsh _ _ ghi); eauto.
    iDestruct "gvh" as "[% gvh]". iMod (ghost_var_update ( A := list bst_hist_el) _ ghi [MInsert 1 (gv _a); MInsert 2 (gv _b)] with "[$gvh]") as "gvh".
    rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share.  iMod "gvar". (* rewrite bi.later_exist. *)
    iCombine "gvdb" "gvar" as "gvdbt". setoid_rewrite (ghost_var_share_join' gsh1 gsh2 Tsh _ _ gvbd); eauto.
    iDestruct "gvdbt" as "[% gvdbt]". iMod (ghost_var_update (A := val) (vint v) gvbd (vint 2) with "[gvdbt]") as "gvdbt". iFrame.
    iDestruct "bst" as "(bst & ghostref)". iMod "Hclose'". iDestruct "gvh" as "(gvh1 & gvh2)".
    rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share. 
    iDestruct "gvdbt" as "(gvbd_1 & gvbd_2)".
    iMod ("Hclose" with "[bst gvh2 data_b gh_ev ghostref ref ins gvbd_2]").
    { iNext. unfold bst_inv. iExists (<[2:=gv _b]> ( M) ).  iSplitL "bst ghostref". unfold tree_rep. 
      iExists tg; iFrame; iFrame; auto. iExists (hr ++ [MInsert 2 (gv _b)]). iSplitL "ref". 
      { iFrame. rewrite apply_hist_app. simpl. rewrite appl_hist. auto. } 
      iExists p_set. iSplitL "gh_ev gvh2". 
      { iFrame. rewrite List.filter_app. rewrite <- H3. simpl. iFrame. }
      iExists (2). rewrite lookup_insert. iFrame "gvbd_2". 
      assert (forall v, ¬ In (MInsert 2 v) (List.filter is_write hr)). rewrite <- H3. intros. apply not_in_cons. 
      auto. rename H5 into lookup_M_empty. apply lookup_empty_hist with (M0 := empty) (M := M) in lookup_M_empty; auto. 
      rewrite lookup_empty in lookup_M_empty. simpl in lookup_M_empty. assert (M !! 2 = None). 
      { destruct lookup_M_empty; auto. } 
      rewrite H5; auto. iExists Ews. iFrame. auto.  }
    iExists (map_upd hist_a (length hr) (MInsert 2 (gv _b))). iModIntro. iFrame. iPureIntro. 
    split; auto. apply add_events_1. apply hist_incl_lt. exact H2. }
Intros hist_b.
rewrite invariant_dup.
(*insert(t, 1, &c);*)
forward_call(b, sh, lock, 1, gv _c, gv, g, g_root, EX h' : _, 
!!(add_events hist_b [MInsert 1 (gv _c)] h') && ghost_var gsh1 [(MInsert 1 (gv _a)); MInsert 2 (gv _b); MInsert 1 (gv _c)] ghi * ghost_hist gsh h' gh 
* ghost_var gsh1 ((Vint (Int.repr 2))) gvbd, inv_names).
{ (*instantiate (1 := [ data_at Ews tint (vint 4) (gv _d); data_at Ews tint (vint 1) (gv _a);
  invariant i (bst_inv gh ghi gvbd g g_root pgname grt gv); data_at Ews tint (vint 3) (gv _c) ]) in (value of Frame).
  subst Frame. simpl. cancel. iIntros "[combo inv]". iDestruct "combo" as "((ghv & hist) & gvbd)".
  unfold atomic_shift. iExists (ghost_hist gsh hist_b gh * ghost_var gsh1 (vint 2) gvbd * ghost_var gsh1 [MInsert 1 (gv _a); MInsert 2 (gv _b)] ghi); (*Frame everything but the invariant*)
  iFrame "hist".   iFrame "ghv". iFrame "gvbd". (*Frame everything but the invariant*) iSplitL ""; auto. 
  iSplit; [|iApply invariant_cored; auto].
  iIntros "combo". iDestruct "combo" as "((>hist & gvbd) & gvh)".
  iMod (inv_open top with "inv") as "[inv Hclose]"; [auto|].
  unfold bst_inv at 1. iDestruct "inv" as (M) "[bst inv]". 
  iDestruct "inv" as (hr) "inv".  iDestruct "inv" as "[ref ins]". iDestruct "ref" as "[app_hist ref]". iMod "ref".
  iExists (M). iMod "bst". iFrame "bst". iMod "gvh". 
  iDestruct "ins" as (p_set) "((gh_ev & gvh2) & ins)".  iMod (bi.later_exist_except_0 with "ins") as "ins". 
  iDestruct "ins" as (v) "(gvar & ins)".  iMod "app_hist". iDestruct "app_hist" as "%appl_hist".
  iMod (fupd_mask_subseteq) as "Hclose'". { apply empty_subseteq. }
  iModIntro. iSplit. iFrame. *)

 rewrite <- sepcon_assoc. rewrite -> 3sepcon_assoc.  apply sepcon_derives; [|cancel].
 iIntros "[[[gvh hist] gvbd] #inv]".  
 unfold atomic_shift; iAuIntro.
 rewrite /atomic_acc /=.
 iMod (inv_open top with "inv") as "[ins Hclose]"; [auto|].  
 iMod (bi.later_exist_except_0 with "ins") as "ins". 
 iDestruct "ins" as (M) "(treerep & ins)". iExists M.  iMod "treerep". 



 iMod (fupd_mask_subseteq) as "Hclose'".
      { apply empty_subseteq. }
      iModIntro. 
 iFrame "treerep". iSplit. 

      + iIntros "bst".
        iMod "Hclose'".  iMod ("Hclose" with "[bst ins]"); auto.
        iNext. iExists (M). iSplitL "bst"; auto.  iFrame; auto.
      + iIntros (bs) "[[% bst] _]".  iDestruct "ins" as (hr) "ins".  iDestruct "ins" as "[ref ins]". iDestruct "ref" as "(appl_hist & ref)". iMod "ref". 
  iMod "appl_hist". iDestruct "appl_hist" as "%appl_hist". 
  iDestruct "ins" as (p_set) "((gh_ev & gvh2) & ins)".  iMod (bi.later_exist_except_0 with "ins") as "ins". 
  iDestruct "ins" as (v) "(gvar & ins)".
        iPoseProof (hist_ref_incl with "[$hist $ref]") as "%"; [auto|].
        iMod (hist_add' _ _ _ ( MInsert 1 (gv _c)) with "[$hist $ref]") as "[hist ref]"; [auto|].
        iMod "gvh2".
        iCombine "gvh" "gvh2" as "gvh". setoid_rewrite (ghost_var_share_join' gsh1 gsh2 Tsh _ _ ghi); eauto.
        iDestruct "gvh" as "[% gvh]".
        iMod (ghost_var_update ( A := list bst_hist_el) _ ghi [MInsert 1 (gv _a); MInsert 2 (gv _b); MInsert 1 (gv _c)] with "[$gvh]") as "gvh".
        rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share.
        iDestruct "bst" as "(bst & ghostref)". iMod "Hclose'". iDestruct "gvh" as "(gvh1 & gvh2)". iMod "gvar".
        iCombine "gvbd" "gvar" as "gvdbt".
        setoid_rewrite (ghost_var_share_join' gsh1 gsh2 Tsh _ _ gvbd); eauto. 
        iDestruct "gvdbt" as "[% gvdbt]". rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share.
        iDestruct "gvdbt" as "(gvbd_1 & gvbd_2)".
        iMod ("Hclose" with "[bst gvh2 ghostref ref ins gh_ev gvbd_2]").
        { iNext. unfold bst_inv. iExists (<[1:=gv _c]> ( M) ). iSplitL "bst ghostref". 
          unfold tree_rep. iExists tg; iFrame; iFrame; auto. 
          iExists (hr ++ [MInsert 1 (gv _c)]). 
          iSplitL "ref". { iFrame.  rewrite apply_hist_app. simpl. rewrite appl_hist. auto. }
          rewrite <- H5. iExists p_set. iFrame; auto. rewrite List.filter_app. rewrite <- H4. simpl. iFrame. 
          iExists 2. iFrame.  rewrite lookup_insert_ne. destruct (M !! 2). inversion H5. simpl. 
          iDestruct "ins" as (shar) "(data_v & ins)". destruct (eq_dec v 4). iFrame; auto. rewrite e in H7. simpl in H7.
          discriminate.  iExists shar.   iFrame. iDestruct "data_v" as "(%rshar & data_v)". iFrame. destruct rshar as [rshar repable].  auto. iFrame; auto. auto. 
        }
   iExists (map_upd hist_b (length hr) (MInsert 1 (gv _c))). iModIntro. iFrame. iSplitR. iPureIntro. 
   split. apply add_events_1. apply hist_incl_lt. exact H3. auto. rewrite H5. iFrame; auto. 
}

Intros hist_c.

forward_call(b, sh, lock, 2, gv _d, gv, g, g_root, EX h' : _, 
!!(add_events hist_c [MInsert 2 (gv _d)] h') && ghost_var gsh1 [(MInsert 1 (gv _a)); MInsert 2 (gv _b); MInsert 1 (gv _c); MInsert 2 (gv _d)] ghi *  
ghost_hist gsh h' gh * ghost_var gsh1 ((Vint (Int.repr 4))) gvbd, inv_names).
{ (*instantiate (1 := []) in (value of Frame). subst Frame. simpl. cancel. iIntros "[combo data_c]". 
  iDestruct "combo" as "(((((ghv & hist) & gvbd) & data_d ) & data_a) & inv)".
  unfold atomic_shift. iExists (ghost_hist gsh hist_c gh * data_at Ews tint (vint 4) (gv _d) * data_at Ews tint (vint 3) (gv _c) * data_at Ews tint (vint 1) (gv _a) * ghost_var gsh1 [MInsert 1 (gv _a); MInsert 2 (gv _b); MInsert 1 (gv _c)] ghi
  * ghost_var gsh1 ((Vint (Int.repr 2))) gvbd). (*Frame everything but the invariant*)
  iFrame "hist".  iFrame "data_d". iFrame "data_c".  iFrame "data_a". iFrame "ghv". iFrame "gvbd". (*Frame everything but the invariant*)
  iSplitL ""; auto. iSplit; [|iApply invariant_cored; auto].
  iIntros "combo". iDestruct "combo" as "(((((>hist & >data_d) & >data_c) & >data_a) & gvh) & gvbd)".
  iMod (inv_open top with "inv") as "[inv Hclose]"; [auto|]. unfold bst_inv at 1. iDestruct "inv" as (M) "[bst inv]". 
  iDestruct "inv" as (hr) "inv".  iDestruct "inv" as "[ref ins]". iDestruct "ref" as "[appl_hist ref]". iMod "appl_hist". 
  iDestruct "appl_hist" as "%appl_hist". iMod "ref". iMod (bi.later_exist_except_0 with "ins") as "ins". 
  iDestruct "ins" as (p_set) "((gh_ev & gvh2) & ins)".  iMod (bi.later_exist_except_0 with "ins") as "ins". 
  iDestruct "ins" as (v) "(gvar & ins)". iExists (M). iMod "bst". iFrame "bst". iMod "gvh".   
  iMod (fupd_mask_subseteq) as "Hclose'". { apply empty_subseteq. }
  iModIntro. iSplit. iFrame. *)
 rewrite <- sepcon_emp at 1.  apply sepcon_derives; [|cancel].
 iIntros "[[[[[[gvh hist] gvbd] #inv] data_a] data_c] data_d]".  
 unfold atomic_shift; iAuIntro.
 rewrite /atomic_acc /=.
 iMod (inv_open top with "inv") as "[ins Hclose]"; [auto|].  
 iMod (bi.later_exist_except_0 with "ins") as "ins". 
 iDestruct "ins" as (M) "(treerep & ins)". iExists M.  iMod "treerep". 
 iMod (fupd_mask_subseteq) as "Hclose'".
      { apply empty_subseteq. }
      iModIntro. 
 iFrame "treerep". iSplit. 

  + iIntros "bst". iMod "Hclose'".  iMod ("Hclose" with "[bst ins]"); auto.
    iNext. iExists (M). iSplitL "bst"; auto. iFrame; auto. 
  + iIntros (bs) "[[% bst] _]".  iDestruct "ins" as (hr) "ins".  iDestruct "ins" as "[ref ins]". iDestruct "ref" as "(appl_hist & ref)". iMod "ref". 
  iMod "appl_hist". iDestruct "appl_hist" as "%appl_hist". 
  iDestruct "ins" as (p_set) "((gh_ev & gvh2) & ins)".  iMod (bi.later_exist_except_0 with "ins") as "ins". 
  iDestruct "ins" as (v) "(gvar & ins)".



    iPoseProof (hist_ref_incl with "[$hist $ref]") as "%"; [auto|].
    iMod (hist_add' _ _ _ ( MInsert 2 (gv _d)) with "[$hist $ref]") as "[hist ref]"; [auto|].
    iMod "gvh2". iCombine "gvh" "gvh2" as "gvh". setoid_rewrite (ghost_var_share_join' gsh1 gsh2 Tsh _ _ ghi); eauto.
    iDestruct "gvh" as "[% gvh]". iMod (ghost_var_update ( A := list bst_hist_el) _ ghi [MInsert 1 (gv _a); MInsert 2 (gv _b); MInsert 1 (gv _c); MInsert 2 (gv _d)] with "[$gvh]") as "gvh".
    rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share. iMod "gvar". 
    iCombine "gvbd" "gvar" as "gvdbt". setoid_rewrite (ghost_var_share_join' gsh1 gsh2 Tsh _ _ gvbd); eauto.
    iDestruct "gvdbt" as "[% gvdbt]". iMod (ghost_var_update (A := val) _ gvbd (vint 4) with "[$gvdbt]") as "gvdbt". 
    iDestruct "bst" as "(bst & ghostref)". iMod "Hclose'". iDestruct "gvh" as "(gvh1 & gvh2)".
    rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share. 
    iDestruct "gvdbt" as "(gvbd_1 & gvbd_2)". iMod "gh_ev". assert (M !! 2 = Some (gv _b)) as M_lookup.
    {
      rewrite lookup_key_newest in appl_hist. 
      rewrite <- H5 in appl_hist.  rewrite <- appl_hist. simpl in *. (*Search (insert ?x). *) rewrite insert_commute; auto.
          } rewrite M_lookup. iMod (bi.later_exist_except_0 with "ins") as "ins".
          iDestruct "ins" as (sh_d) "(data_b & ins)". if_tac. subst. discriminate.
          iMod "ins" as "(%p_set_val & _)". 
          
 iMod (master_update (P := @option_PCM (discrete_PCM _)) _ (Some (gv _d)) with "gh_ev") as "gh_ev". 
   rewrite p_set_val. simpl. auto.

        iMod ("Hclose" with "[bst gvh2 data_c data_a data_d ghostref ref gvbd_2 data_b gh_ev]").
        { 
          iNext. unfold bst_inv. iExists (<[2:=gv _d]> ( M) ). iSplitL "bst ghostref". 
          unfold tree_rep. iExists tg; iFrame; iFrame; auto. 
          iExists (hr ++ [MInsert 2 (gv _d)]). 
          iSplitL "ref". { iFrame.  rewrite apply_hist_app. simpl.
           rewrite appl_hist. auto. } 
          rewrite List.filter_app.  rewrite <- H5. iExists (Some (gv _d)). iFrame "gh_ev gvh2".
          iExists 4. iFrame "gvbd_2". rewrite lookup_insert.  iExists Ews. iFrame "data_d". 
          iSplit. auto. rewrite lookup_key_newest in appl_hist. simpl. iSplit. auto. 
          iLeft. iExists (gv _c). iExists Ews. iFrame.  rewrite lookup_key_newest in appl_hist. rewrite <- H5 in appl_hist.
          rewrite <- appl_hist.
          rewrite insert_commute; auto. inversion H6. 
          auto. iSplit. iPureIntro; auto. inversion H6. simpl in *. iExists sh_d.
          iDestruct "data_b" as "(%rsh_d & data_b)". destruct rsh_d as [rsh_d  repable]. iSplit. auto. rewrite H6.
          iFrame "data_b". (*
          rewrite lookup_key_newest in appl_hist. rewrite <- H5 in appl_hist.
          rewrite <- appl_hist.
          rewrite insert_commute; auto. iExists sh_d.  rewrite H6. iDestruct "data_b" as "(%share_d & data_b)". iFrame. auto. *)
        }
         
        iExists (map_upd hist_c (length hr) (MInsert 2 (gv _d))). iModIntro. iFrame. iPureIntro. 
         split; auto. apply add_events_1. apply hist_incl_lt. exact H4. }  
          viewshift_SEP 0 (emp). { go_lower. Intros sh'. iIntros "[[histl hist2 ]hist]". 
        iDestruct "histl" as "_".  iDestruct "hist2" as "_".  iDestruct "hist" as "_".
 Admitted.






Lemma body_retrieve_value : semax_body Vprog Gprog f_retrieve_value retrieve_value_spec.
Proof.
start_function.
(* int y = -1; *)
forward.  
(* do {  } while (y != 4); *)
forward_loop (EX y: val,
   PROP (y <> vint 4)
   LOCAL (gvars gv; temp _y y; temp _t b)
   SEP (mem_mgr gv * nodebox_rep g g_root sh lock b  *
invariant i (bst_inv gh ghi gvbd g g_root pgname grt gv) * reader_token grt)) break: 
( PROP ()
   LOCAL (temp _y (vint 4); gvars gv; temp _t b)
   SEP (EX v, set_snap (v) pgname * mem_mgr gv * nodebox_rep g g_root sh lock b * reader_token grt *
invariant i (bst_inv gh ghi gvbd g g_root pgname grt gv))). 
(* invariant holds at the start of the loop *)
- Exists ((Vint (Int.neg (Int.repr 1)))). entailer!. 

- Intros y. rewrite invariant_dup.  (* we still need the invariant for other calls *)
(*searchResult = lookup (t,  2);*)
 forward_call (b, sh, lock, 2, gv, g, g_root, fun p => if (eq_dec p nullval) then emp else EX v rsh,
!!(readable_share rsh /\ repable_signed v) && data_at rsh tint (vint v) p *
    if (eq_dec v 4) then set_snap (p) pgname else emp, inv_names).
   (*
(* everything not used in this call should be framed *)
instantiate (1:= [invariant i (bst_inv gh ghi gvbd g g_root pgname grt gv);  reader_token grt]) in (value of Frame).
subst Frame. simpl. cancel. iIntros "inv". *) 
rewrite -> sepcon_assoc.  apply sepcon_derives; [|cancel].  
      iIntros "#inv"; unfold atomic_shift; iAuIntro.
      rewrite /atomic_acc /=.
      iMod (inv_open top with "inv") as "[ins Hclose]"; [auto|].  
iMod (bi.later_exist_except_0 with "ins") as "ins". 
  iDestruct "ins" as (M) "(treerep & ins)". iExists M.  iMod "treerep". 



 iMod (fupd_mask_subseteq) as "Hclose'".
      { apply empty_subseteq. }
      iModIntro. 
 iFrame "treerep". iSplit. 


+  iIntros "treerep". iMod "Hclose'".  iMod ("Hclose" with "[ins treerep]"). iNext. iExists M.
iFrame "treerep". iFrame "ins". auto.

  + destruct (M !! 2) eqn: HM2.
      ++ (*Taking all the pieces we need from the invariant before closing it*)
         iIntros (bs) "[[% bst] _]".  iMod (bi.later_exist_except_0 with "ins") as "ins". 
          iDestruct "ins" as (hr) "ins". iDestruct "ins" as "[ref ins]". iMod "ref". iDestruct "ref" as "(%hist & ref)".  
         iDestruct "ins" as (p_set) "((gh_ev & gh_var) & ins)". 
         iDestruct "ins" as (val) "(gh_var2 & ins)".  iMod (bi.later_exist_except_0 with "ins") as "ins". 
         iDestruct "ins" as (sh0) "(share & ins)". iMod "share". iDestruct "share" as "(%share & data_share)". 
         destruct share as (share & val_rep). apply split_readable_share in share. 
         iMod "gh_ev". destruct share as [sh1 share]. destruct share as [sh2 share]. 
         iPoseProof (data_at_share_join with "data_share") as "data_share". apply share. iDestruct "data_share" as "(data_sh1 & data_sh2)". 
         destruct share as (share1 & share2). destruct share2 as (share2 & share_join).
         destruct (eq_dec val 4).
          +++ iPoseProof (make_snap with "gh_ev") as ">gh_ev". iDestruct "gh_ev" as "(gh_snap & gh_ev)". 
              iMod "ins". iDestruct "ins" as "(%p_set_val & ins)". iDestruct "ins" as "[ins | read_token]".
              iDestruct "ins" as (p2 sh4) "(%M1_val & ((data_p2 & data_a) & data_b))". destruct M1_val as [M1_val rsh4].
              iMod "Hclose'".  iMod ("Hclose" with "[bst data_a data_b data_p2 gh_ev gh_var gh_var2 ref data_sh2]"). 
              { iNext. unfold bst_inv. iExists M. iFrame "bst". iExists hr.  iSplitL "ref". iFrame. auto. iExists p_set.  
                iFrame. rewrite HM2. iExists val. iFrame "gh_var2". iExists sh2.  iFrame. iSplitR. auto. rewrite e. simpl. 
                iSplit. auto. iLeft. iExists p2.  iExists sh4.  iFrame. auto. }
              iModIntro. rewrite e. simpl. rewrite H1. destruct (eq_dec v nullval). rewrite e0. unfold data_at. 
              unfold field_at. iDestruct "data_sh1" as "(%field_comp & data_sh1)". inversion field_comp. inversion  H2. 
              iExists (4). iExists sh1. iFrame "data_sh1". iSplitR. auto. unfold set_snap. simpl. rewrite p_set_val. iFrame "gh_snap".
              { iMod "Hclose'".  iMod ("Hclose" with "[bst read_token gh_ev gh_var gh_var2 ref data_sh2]"). iNext.
                unfold bst_inv. iExists M. iFrame "bst". iExists hr.  iSplitL "ref". iFrame. auto. iExists p_set.  
                iFrame. rewrite HM2. iExists val. iFrame "gh_var2". iExists sh2.  iFrame. iSplitR. auto. 
                rewrite e. simpl. iSplit. auto. iRight. auto. iModIntro.  rewrite e. simpl. rewrite H1. destruct (eq_dec v nullval). 
                rewrite e0. unfold data_at. unfold field_at. iDestruct "data_sh1" as "(%field_comp & data_sh1)". inversion field_comp.
                inversion  H2. iExists (4). iExists sh1. iFrame "data_sh1". iSplitR. auto. unfold set_snap. simpl. rewrite p_set_val. iFrame "gh_snap". }
         +++ iMod "Hclose'".  iMod ("Hclose" with "[bst data_sh2 gh_ev gh_var gh_var2 ref ins]").
             { iNext. unfold bst_inv. iExists M. iFrame "bst". iExists hr.  iSplitL "ref". iFrame. auto. 
             iExists p_set.  iFrame. iExists val. iFrame. rewrite HM2. iExists sh2. iFrame. iSplitR. auto. 
             destruct (eq_dec val 4). contradiction. auto. }
             iModIntro.  destruct (eq_dec bs nullval). rewrite <- H1. rewrite e. unfold data_at. unfold field_at. 
             iDestruct "data_sh1" as "(%field_comp & data_sh1)". inversion field_comp. inversion  H2. rewrite H1. iExists (val). 
             iExists sh1. iFrame "data_sh1". iSplitR. auto. destruct eq_dec. contradiction. auto.
     ++ iIntros (bs) "[[% bst] _]".  iMod (bi.later_exist_except_0 with "ins") as "ins". iMod "Hclose'".  
        iMod ("Hclose" with "[bst ins ]"). unfold bst_inv. iExists M. rewrite HM2. iNext. iSplitL "bst". iFrame. auto. 
         rewrite H1. simpl. iModIntro. auto.
  + Intros vret. 
    (* if (searchResult != NULL) {
        y = *((int* ) searchResult);
     } *)
    forward_if (EX y : Z, PROP ( repable_signed y )
    LOCAL (temp _searchResult vret; gvars gv;
    temp _y (vint y); temp _t b)
    SEP (mem_mgr gv; nodebox_rep g g_root sh lock b;
    invariant i (bst_inv gh ghi gvbd g g_root pgname grt gv); reader_token grt;
     if eq_dec y 4
        then 
        set_snap vret pgname
        else
        emp
    )).
     ++ apply denote_tc_test_eq_split; entailer!. destruct eq_dec. entailer!. entailer!.
        sep_apply data_at_valid_ptr; auto. entailer!.
     ++ destruct (eq_dec vret nullval). contradiction. Intros v0 rsh. forward. Exists  v0. entailer!. 
        destruct (eq_dec v0 4). 
         * rewrite e. simpl. entailer!. admit. (*discard readable share*)
         * destruct (eq_dec (vint v0) (vint 4)). contradiction n0. apply repr_inj_signed; auto. congruence. admit. (*discard readable share*)
     ++ forward. rewrite H1. entailer. Exists ( Int.signed y). entailer!. rewrite Int.repr_signed. auto. if_tac.  
        rewrite <- (Int.repr_signed y) in H0. congruence. auto.
     ++ Intros y0. 
        forward_if.
         * forward. entailer. Exists (vint y0).  entailer!. contradiction H2. apply repr_inj_signed; auto. if_tac. congruence. auto. 
         * forward. entailer. Exists vret. entailer!. if_tac. auto. contradiction. 
- Intros gvd. 
(*  searchResult = lookup (t,  1);*)
forward_call (b, sh, lock, 1, gv, g, g_root, fun p => |> data_at Ews tint (vint 3) p * |> data_at Ews tint (vint 1) (gv _a) *
|> EX sh_b, !! (readable_share sh_b) &&  data_at sh_b tint (vint 2) (gv _b), inv_names).
rewrite <- sepcon_emp at 1.
 apply sepcon_derives; [|cancel].  
      iIntros "inv". iDestruct "inv" as "((snap & read_token) & #inv)".
 unfold atomic_shift; iAuIntro.
      rewrite /atomic_acc /=.
      iMod (inv_open top with "inv") as "[ins Hclose]"; [auto|].  
iMod (bi.later_exist_except_0 with "ins") as "ins". 
  iDestruct "ins" as (M) "(treerep & ins)". iExists M.  iMod "treerep". 



 iMod (fupd_mask_subseteq) as "Hclose'".
      { apply empty_subseteq. }
      iModIntro. 
 iFrame "treerep". 
iSplit. 

(*
iExists (set_snap gvd pgname * reader_token grt).  iFrame "snap".   iSplitL ""; auto. iSplit; [|iApply invariant_cored; auto].     
iIntros "snap". iMod (inv_open top with "inv") as "[inv Hclose]"; [auto|]. unfold bst_inv at 1. 
iDestruct "inv" as (M) "[bst inv]". iDestruct "inv" as (hr) "inv". iExists M. iDestruct "inv" as "[ref ins]". iMod "ref". 
iDestruct "ref" as "(%hist & ref)". iMod "bst". iFrame "bst". iMod (fupd_mask_subseteq) as "Hclose'". { apply empty_subseteq. }
iModIntro. iSplit. iFrame. *)
  + iIntros "treerep".  iMod "Hclose'".  iMod ("Hclose" with "[treerep ins]"); auto. iNext. iExists (M). iFrame "treerep".  iFrame.
  + iIntros (bs) "[[% bst] _]".  unfold ghost_events. unfold set_snap. 
    iMod "Hclose'".  iMod (bi.later_exist_except_0 with "ins") as "ins". iDestruct "ins" as (hr) "ins".  iDestruct "ins" as "[ref ins]".
iMod "ref". 
iDestruct "ref" as "(%hist & ref)".

 iDestruct "ins" as (p_set) "((gh_ev & gh_var) & ins)". 
    iMod (bi.later_exist_except_0 with "ins") as "ins". iDestruct "ins" as (val) "(gh_var2 & ins)". destruct (M !! 2) eqn: HM2.
    ++ iMod (bi.later_exist_except_0 with "ins") as "ins".  
       iDestruct "ins" as (sh0) "(share & ins)". iMod "share". iDestruct "share" as "(%share & data_share)". if_tac.   
       +++ rewrite bi.later_and. iDestruct "ins" as "(>%snap_set & ins)". rewrite bi.later_or. iDestruct "ins" as "[ins | read_token2]". 
           iMod (bi.later_exist_except_0 with "ins") as "ins".  iDestruct "ins" as (p2) "ins". iMod (bi.later_exist_except_0 with "ins") as "ins".
           iDestruct "ins" as (sh4) "(>%M_val1 & ins)". iDestruct "ins" as "((data_vret & data_a) & data_b)". destruct M_val1 as [M_look_1 rsh4].
           apply split_readable_share in rsh4. iMod "gh_ev". destruct rsh4 as [sh1 rsh4]. destruct rsh4 as [sh2 rsh4]. 
           destruct rsh4 as (share1 & share2). destruct share2 as (share2 & share_join). iMod ("Hclose" with "[bst read_token ref gh_var gh_var2 gh_ev data_share]").
           { iNext. unfold bst_inv. iExists M. iFrame "bst". iExists hr. iFrame "ref". iSplitR. auto. iExists p_set. iFrame "gh_ev". 
             iFrame "gh_var". iExists val. iFrame. rewrite HM2. iExists sh0. iFrame. iSplitR. auto. rewrite H1. simpl. iSplit. 
             auto. iRight.  iFrame "read_token". }
           iModIntro. iFrame. rewrite M_look_1 in H0. rewrite H0. iFrame "data_vret". 

          (*admit. (*Get rid of the ghost_snap*) *)
           iMod "read_token2". iCombine "read_token" "read_token2" as "read_token".  unfold reader_token. 
           iPoseProof (excl_unique with "read_token") as "read_token". iPoseProof (FF_local_facts with "read_token") as "%read_token". contradiction. 
       +++ iMod "gh_ev". iAssert ( ghost_snap (P := @option_PCM (discrete_PCM _))(Some gvd) pgname * ghost_master1 (P := @option_PCM (discrete_PCM _)) p_set pgname)%I with "[snap gh_ev]" as "snaps". iFrame.
           iAssert (!! (option_ord  (P := (discrete_PCM _)) (Some gvd) p_set) &&
           ghost_master1  (P := @option_PCM (discrete_PCM _)) p_set pgname)%I with "[snaps]" as "snaps".
           { iApply (snap_master_join1 (P := @option_PCM (discrete_PCM _)) (Some gvd) p_set pgname); iFrame. }
          iDestruct "snaps" as "(%pset & gh_ev)". iMod "ins" as "(%psetVal & emp)". rewrite psetVal in pset. simpl in pset. contradiction.
   ++ iMod "gh_ev". iAssert ( ghost_snap (P := @option_PCM (discrete_PCM _))(Some gvd) pgname * ghost_master1 (P := @option_PCM (discrete_PCM _)) p_set pgname)%I with "[snap gh_ev]" as "snaps". iFrame.
      iAssert (!! (option_ord  (P := (discrete_PCM _)) (Some gvd) p_set) && ghost_master1  (P := @option_PCM (discrete_PCM _)) p_set pgname)%I with "[snaps]" as "snaps".
      { iApply (snap_master_join1 (P := @option_PCM (discrete_PCM _)) (Some gvd) p_set pgname); iFrame. }
      iDestruct "snaps" as "(%pset & gh_ev)". iMod "ins" as "(%psetVal & emp)". rewrite psetVal in pset. simpl in pset. contradiction. 
  + Intros vret.  forward. unfold POSTCONDITION. unfold abbreviate. forward. Exists (vint 3). entailer!. Exists sh_b. entailer!. 
    Exists vret. entailer.  Admitted.







Lemma  ghost_hist_join_empty: ∀ (hist_el: Type) (sh1 sh2 sh : Share.t)
         (p : own.gname),
         sepalg.join sh1 sh2 sh
         → sh1 ≠ Share.bot
           → sh2 ≠ Share.bot
             → @ghost_hist hist_el sh1 empty_map p *
               @ghost_hist hist_el sh2 empty_map p = 
               @ghost_hist hist_el sh empty_map p.
Proof.
intros.
replace empty_map with (@map_add nat hist_el empty_map empty_map) by apply map_add_empty.
      pose proof (@empty_map_disjoint nat hist_el empty_map) as Hdisj.
      erewrite (add_andp (ghost_hist sh _ _) (!!_)) by (apply prop_right, Hdisj).
      rewrite -> andp_comm, <- (ghost_hist_join _ _ _ _ _ _ H); auto.
Qed.


(*ltree g g_root sh1 (Share.split gsh1).1 np lock *)
Lemma  ltree_share_join: ∀ (g g_root : gname) (sh1 sh2 sh : Share.t) (gsh : share) 
  (p : val) (lock : reptype
                      (nested_field_type t_struct_tree_t
                         (DOT bst_conc._lock))) (H : sepalg.join sh1 sh2 sh),
         sepalg.join sh1 sh2 sh
           → sh1 ≠ Share.bot
             → sh2 ≠ Share.bot
              → readable_share sh1
               → readable_share sh2
                 → ltree g g_root sh1 gsh p lock *
                 ltree g g_root sh2 gsh p lock = 
                 ltree g g_root sh gsh p lock.
Proof.
intros. unfold ltree. symmetry. rewrite <- lock_inv_share_join with (sh1 := sh1) (sh2 := sh2); auto.
rewrite <- @field_at_share_join with (sh1 := sh1) (sh2 := sh2); auto. 
auto.
apply pred_ext.
- iIntros "(%field_comp & field_2)". iDestruct "field_2" as "((field_1 & field_2) & lock_i)".
iDestruct "lock_i" as "(lock_1 & lock_2)". iSplitL "field_1 lock_1".   iFrame "field_1 lock_1"; auto.
iFrame "field_2 lock_2"; auto.
- iIntros "((%field_comp & field) & lock)".  iDestruct "lock" as "(%field_compatible & field_2)". 
rewrite <- sepcon_andp_prop'. rewrite <- !sepcon_assoc. rewrite <- sepcon_andp_prop'.
 iDestruct "field_2" as "(field_2 & lock_2)". iDestruct "field" as "(field_1 & lock_1)".
iFrame; auto.
Qed.
(*
Search (isptr ?v1). Search (mapsto).
Lemma data_at_pointer_cohere : forall {cs : compspecs} sh1 sh2 t v1 v2 p, readable_share sh1 ->
  type_is_by_value t = true -> type_is_volatile t = false -> isptr v1 -> isptr v2 ->
  data_at sh1 t v1 p * data_at sh2 t v2 p |--
  data_at sh1 t v1 p * data_at sh2 t v2 p * !! v1 = v2.
Proof.
  intros; unfold data_at, field_at, at_offset; Intros.
  apply andp_right; [apply prop_right; auto|].
  rewrite !by_value_data_at_rec_nonvolatile by auto.
  apply mapsto_value_cohere; auto.
Qed.
(*
Lemma ltree_value_cohere
     : ∀ (g g_root : gname) (sh : Share.t) (gsh : share) (p np : val) (lock : reptype
                      (nested_field_type t_struct_tree_t
                         (DOT bst_conc._lock))),
         readable_share sh1
             → ltree g g_root sh1 gsh p lock * ltree g g_root sh2 gsh np lock 
               |-- ltree g g_root sh1 gsh np lock * ltree g g_root sh2 gsh np lock.
Proof.
intros. unfold ltree, lock_inv, field_at, at_offset. Intros.  
apply andp_right; [apply prop_right; auto|].
  rewrite !by_value_data_at_rec_nonvolatile; auto. 
entailer.
  apply mapsto_value_cohere; auto.
apply andp_right; [apply prop_right; auto|].

*) *)

Definition lsh1_1 := fst (slice.cleave lsh1).
Definition lsh1_2 := snd (slice.cleave lsh1).


Lemma lsh1_1_lsh1_2_join : sepalg.join lsh1_1 lsh1_2 lsh1.
Proof.
  apply slice.cleave_join; unfold lsh1_1, lsh1_2; destruct (slice.cleave Ews); auto.
Qed.

Lemma readable_lsh1_1 : readable_share lsh1_1.
Proof.
  apply slice.cleave_readable1; auto.
Qed.

Lemma readable_lsh1_2 : readable_share lsh1_2.
Proof.
  apply slice.cleave_readable2; auto.
Qed.


(* nodebox_rep g g_root sh lock b; *)
Lemma  nodebox_rep_join: ∀ (g g_root : gname) (sh1 sh2 sh : Share.t) (lock nb : val) (t : val),
         sepalg.join sh1 sh2 sh
         → sh1 ≠ Share.bot
           → sh2 ≠ Share.bot
             → readable_share sh1
              → readable_share sh2
               → nodebox_rep g g_root sh1 lock nb *
                 nodebox_rep g g_root sh2 lock nb = 
                 nodebox_rep g g_root sh lock nb.
Proof.
intros.
apply pred_ext.
- unfold nodebox_rep. Intros np. Exists np. entailer. iIntros "(((((data_sh1 & ltree_sh1) & my_half_1) & data_sh2) & ltree_sh2) & my_half_2)".
iCombine "my_half_1 my_half_2" as "my_half". (*
iPoseProof (general_locks.my_half_join (Share.split gsh1).2 (Share.split gsh1).2 (Share.split gsh1).2 with "my_half") as "my_half"; auto. *)


iCombine "data_sh1 data_sh2" as "data_sh". 
assert (type_is_by_value (tptr t_struct_tree_t) = true). auto.
assert (type_is_volatile (tptr t_struct_tree_t) = false). auto.
iPoseProof (data_at_value_cohere sh1 sh2 _ _ _ nb with "data_sh") as "data_sh"; auto.
iPoseProof (data_at_share_join _ _ _ _ _ _ H with "data_sh") as "data_sh". iFrame "data_sh".

iCombine "ltree_sh1 ltree_sh2" as "ltree_sh". assert (np = x). { admit. }
rewrite H8. iPoseProof (ltree_share_join _ _ _ _ _ _ _ _ H  with "ltree_sh") as "ltree_sh"; auto.
iFrame "ltree_sh". auto.
admit.
- unfold nodebox_rep. Intros np. Exists np. entailer. iIntros "((data_sh & ltree_sh) & lock_half)".
  iExists np. iPoseProof (data_at_share_join _ _ _ _ _ _ H with "data_sh") as "data_sh".
  iDestruct "data_sh" as "(data_sh1 & data_sh2)". iFrame "data_sh1". iFrame "data_sh2".
   iPoseProof (ltree_share_join _ _ _ _ _ _ _ _ H with "ltree_sh") as "ltree_sh"; auto.
  iDestruct "ltree_sh" as "(ltree_sh1 & ltree_sh2)". iFrame "ltree_sh1". iFrame "ltree_sh2".
  iFrame "lock_half". admit.
Admitted.

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
  sep_apply (create_mem_mgr gv).
forward_call. Intros vret.  
Search (emp |-- ?x).
  ghost_alloc (ghost_hist_ref(hist_el := bst_hist_el) Tsh empty_map empty_map).
 { split; auto with share; apply @self_completable. }
Intros gh.
ghost_alloc (ghost_var Tsh ([] : list bst_hist_el)).
  Intro ghi.
rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share; Intros. 
ghost_alloc ( ghost_var Tsh ((Vint (Int.repr 0)))).
 Intro gvbd.
rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share; Intros. 
ghost_alloc ( reader_token ). Intros grt.
  sep_apply (create_mem_mgr gv).
destruct vret as [g g_root].   destruct g as [gsh g]. destruct gsh as [b lock]. simpl.
assert_PROP (isptr lock). unfold nodebox_rep. Intros np. unfold ltree. Intros. entailer!.
  rewrite <- (emp_sepcon (ghost_var _ _ _)); Intros.
  ghost_alloc (ghost_events None).
Intros pgname.
(* allocating the invariant *)

viewshift_SEP 3 (EX inv_names : invG, wsat).
{ go_lower. apply make_wsat. }
Intros inv_names.
simpl. rewrite <- hist_ref_join_nil.
Intros. Locate ghost_ref.
gather_SEP (wsat) ( tree_rep g g_root ∅ ) (ghosts.ghost_ref [] gh)  (ghost_events None pgname) (ghost_var gsh2 [] ghi)
(ghost_var gsh2 (vint 0) gvbd).
viewshift_SEP 0 (EX i, |> (wsat * invariant i (bst_inv gh ghi gvbd g g_root pgname grt gv))).
{ go_lower. rewrite !sepcon_assoc. apply make_inv'. unfold bst_inv.
   iIntros "(tree_rep & ghost_ref & gh_ev & gh_hist & gvbd)". 
  iExists empty. simpl. iFrame "tree_rep". iExists ∅. iFrame  "ghost_ref". 
  iSplit; auto. iExists None. iFrame "gh_ev gh_hist". iExists (0). 
  iFrame "gvbd". rewrite lookup_empty. auto. }

Intros i.

rewrite invariant_dup. Intros. 


assert_PROP(isptr b). entailer!. rewrite <- ghost_hist_join_empty with (sh1 := gsh1) (sh2 := gsh2); auto.

assert (readable_share lsh1_1) as lsh1_1_read; auto. 
assert (readable_share lsh1_2) as lsh1_2_read; auto.

apply readable_not_bot in lsh1_1_read. apply readable_not_bot in lsh1_2_read.

rewrite <- nodebox_rep_join with (sh1 := lsh1_1) (sh2 := lsh1_2); auto.
Intros. rewrite !later_sepcon. Intros.

forward_spawn _update_tree b (lsh1_1, gsh1, lock, gv, g, g_root, pgname, i, gh, ghi, gvbd, grt, inv_names).


entailer!. simpl. auto. 


forward_call(gv, lsh1_2, i, b, gh, ghi, g, gvbd, pgname, g_root, lock, gsh2, grt, inv_names).

Intros vret.

Admitted.






