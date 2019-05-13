Require Import VST.floyd.proofauto.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.

(* To import the above and use VST, you need to add the following to _CoqProject and then do
coq_makefile -f _CoqProject -o Makefile

-R /PATH_TO_VST/compcert compcert -Q /PATH_TO_VST/msl VST.msl -Q /PATH_TO_VST/sepcomp VST.sepcomp -Q /PATH_TO_VST/veric VST.veric -Q /PATH_TO_VST/floyd VST.floyd -Q /PATH_TO_VST/progs VST.progs -R /PATH_TO_VFA/ Top -R ../../model Model

Replace PATH_TO_VST and PATH_TO_VFA by the appropriate paths.
Maybe we'll set up a nice script later, like add a _CoqProject target in the Makefile, like in the tutorial.

This is also needed to import libs that use VST, such as our btrees.
*)

Require Import Signatures.
Require Import btrees.
Require Import Top.db.

Definition next {X:Type} (r: relation X) (c: cursor X) : (result tuple_t * cursor X) := (* add valid hyp? *)
  let cincr := next_cursor (up_at_last c) in
    match cincr with
    | List.nil => (Empty_Cursor, c) (* the cursor was at the last position in the tree *)
    | List.cons (n,i) c' =>
      match getCRecord cincr with
      | Some v =>
        (* now, retrieve the tuple at the address v *)
        (Result v, cincr) (* must be a leaf, we didn't go up *)
      | None =>
        match (nth_node i n) with
        | None => (No_Result, cincr) (* impossible *)
        | Some n' => let c' := moveToFirst n' cincr (length cincr) in
                     match getCVal c' with
                     | Some x => (Result x, c')
                     | None => (No_Result, c') (* impossible *)
                     end
        end
      end
    end.

Import OrderedSet.Oeset.
Require Import compcert.lib.Integers.

Search Znth. Print Inhabitant.
Instance col_t_Inhabitant : Inhabitant col_t := Int.
Instance elt_t_Inhabitant : Inhabitant elt_t := int_elt Ptrofs.zero.

(* should add a predicate relating the tuples to the schema?? *)
(* HOW do we relate individual tuples and the schema of the relation *)
(* so far, our indices are only on ONE key => all good *)
Program Definition order_on_tuples (sch : schema_t) (key_index: Z)
  (h : Znth key_index (col_types sch) = Int) : OrderedSet.Oeset.Rcd tuple_t :=
  {| compare := fun t1 t2 =>
                  match Znth key_index t1, Znth key_index t2 with
                  | int_elt k1, int_elt k2 =>
                    let (k1', k2') := (Ptrofs.to_int k1, Ptrofs.to_int k2) in
                      if Int.eq k1' k2' then Eq else
                        if Int.lt k1' k2' then Lt else Gt
                    | _, _ => Eq (* will not happen, dummy value *)
                  end |}.

(* next is work in progress and won't type-check, sorry *)

Next Obligation.
  simpl.
  intros. destruct a1 as [k1 v1], a2 as [k2 v2], a3 as [k3 v3].
  enough (h : Int.eq k1 k3 = true). rewrite h. auto.
  unfold Int.eq, Int.lt, Coqlib.zeq, Coqlib.zlt in *. destruct ZArith_dec.Z_lt_dec, ZArith_dec.Z_lt_dec, BinInt.Z.eq_dec, BinInt.Z.eq_dec, BinInt.Z.eq_dec; try auto; try discriminate; rewrite e0 in e; contradiction.
Qed.

Next Obligation.
  simpl; intros. destruct a1 as [k1 v1], a2 as [k2 v2], a3 as [k3 v3].
  enough (h : Int.eq k1 k3 = false /\ Int.lt k1 k3 = true). destruct h as [h1 h2]. rewrite h1, h2. auto.
  unfold Int.eq, Int.lt. , Coqlib.zeq, Coqlib.zlt in *.
  destruct ZArith_dec.Z_lt_dec, ZArith_dec.Z_lt_dec, BinInt.Z.eq_dec, BinInt.Z.eq_dec, BinInt.Z.eq_dec, ZArith_dec.Z_lt_dec; try auto; try discriminate H0; try discriminate H.
  rewrite e in e0; contradiction.
  rewrite e in e0; contradiction.
  Search Int.unsigned Int.signed.
  rewrite e in n0; contradiction.


Program Definition Cursor_of_relation {order : OrderedSet.Oeset.Rcd tuple_t}
        (r : relation unit) : Cursor.Rcd order :=
  {| Cursor.cursor := cursor unit
  ;   Cursor.empty_cursor := moveToLast _ (btrees.get_root r) Datatypes.nil O
  ;   Cursor.reset := fun _ => moveToFirst (btrees.get_root r) Datatypes.nil O
  ;   Cursor.next := next r
  ;   Cursor.collection := fun _ => collection (get_root r)
  ;   Cursor.visited := _
  ;   Cursor.coherent := fun _ => True |}.

Next Obligation.
Admitted.
 (* ... *)
