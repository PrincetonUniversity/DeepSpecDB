(* Require Import VST.floyd.proofauto.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand. *)

(* To import the above and use VST, you need to add the following to _CoqProject and then do
coq_makefile -f _CoqProject -o Makefile

-R /PATH_TO_VST/compcert compcert -Q /PATH_TO_VST/msl VST.msl -Q /PATH_TO_VST/sepcomp VST.sepcomp -Q /PATH_TO_VST/veric VST.veric -Q /PATH_TO_VST/floyd VST.floyd -Q /PATH_TO_VST/progs VST.progs -R /PATH_TO_VFA/ Top -R ../../model Model

Replace PATH_TO_VST and PATH_TO_VFA by the appropriate paths.
Maybe we'll set up a nice script later, like add a _CoqProject target in the Makefile, like in the tutorial.

This is also needed to import libs that use VST, such as our btrees.
*)

Require Import Signatures.
Require Import btrees.

Definition next {X:Type} (r: btrees.relation X) (c: btrees.cursor X) : (result X * btrees.cursor X) := (* add valid hyp? *)
  let cincr := next_cursor (up_at_last c) in
    match cincr with
    | List.nil => (Empty_Cursor, c) (* the cursor was at the last position in the tree *)
    | List.cons (n,i) c' =>
      match getCVal cincr with
      | Some x => (Result x, cincr) (* must be a leaf, we didn't go up *)
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

Fixpoint collection {X:Type} (n : node X) : list X :=
  match n with
    btnode o le isLeaf First Last x =>
    match o with
    | Some n' => collection n' ++ abs_le le
    | None => abs_le le
    end
  end
with abs_le {X:Type} (le:listentry X) : list X := (* use fold instead? *)
       match le with
       | nil => List.nil
       | cons e le' => abs_entry e ++ abs_le le'
       end
with abs_entry {X:Type} (e:entry X) : list X :=
       match e with
       | keyval k v x => List.cons x List.nil
       | keychild k n => collection n
       end.    

Print Cursor.

(* WORK IN PROGRESS 
Fixpoint visited {X:Type} (n : node X) (c : cursor X) : list X :=
  match c with
  | List.nil => List.nil
  | List.cons (btnode o le isLeaf First Last x, index.ip ii) c' =>
    match o with
    | Some _ => visited c' ++ abs_le (nth_first_le le ii)
    | None => abs_le (nth_first_le le ii)
    end
  | List.cons (btnode o le isLeaf First Last x, index.im) c' =>
    match o with
    | Some n' => visited c'
    | None => nil
    end
  end
with abs_le {X:Type} (le:listentry X) : list X := (* use fold instead? *)
       match le with
       | nil => List.nil
       | cons e le' => abs_entry e ++ abs_le le'
       end
with abs_entry {X:Type} (e:entry X) : list X :=
       match e with
       | keyval k v x => List.cons x List.nil
       | keychild k n => collection n
       end.    


Fixpoint get_visited_tree {X : Type} (n : node X) (c : cursor X) : node X :=
  match (c, n) with
  | ([], _) => n (* shouldn't happen? *)
  | (List.cons (n, i) c'), btnode ptr0 le isLeaf First Last x) =>
      match i with
      | im => btnode ptr0 nil isLeaf First Last
      | ip ii => btnode ptr0 (get_visited_le le ii c') isLeaf First Last
      end
end
with get_visited_le le ii c := 
                                                               
          
                                                               let le' := nth_first_le le (
  end.

Definition visited {X : Type} (r : relation X) (c : cursor X) :=
  let n := get_visited_tree r c in
  collection n

*)

             
Print Cursor.
Program Definition Cursor_of_relation {X : Type} {order : OrderedSet.Oeset.Rcd X}
        (r : relation X) : Cursor.Rcd order :=
  {| Cursor.cursor := cursor X
  ;   Cursor.empty_cursor := moveToLast _ (btrees.get_root r) Datatypes.nil O
  ;   Cursor.reset := fun _ => moveToFirst (btrees.get_root r) Datatypes.nil O
  ;   Cursor.next := next r
  ;   Cursor.collection := fun _ => collection (get_root r)
  ;   Cursor.visited := _
  ;   Cursor.coherent := fun _ => True |}.

Next Obligation.
Admitted.
 (* ... *)
