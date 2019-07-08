(**                                                                                 *)
(**                             The SQLEngines Library                              *)
(**                                                                                 *)
(**            LRI, CNRS & Université Paris-Sud, Université Paris-Saclay            *)
(**                                                                                 *)
(**                        Copyright 2016-2019 : FormalData                         *)
(**                                                                                 *)
(**         Authors: Véronique Benzaken                                             *)
(**                  Évelyne Contejean                                              *)
(**                  Chantal Keller                                                 *)
(**                  Eunice-Raquel Martins                                          *)
(**                                                                                 *)
(************************************************************************************)

Set Implicit Arguments.

Require Import Relations SetoidList List String Ascii Bool ZArith NArith.

Require Import FlatData ListFacts OrderedSet
        FiniteSet FiniteBag FiniteCollection Tree Formula SqlCommon SqlAlgebra.

Import Tuple.
Require Import Values Relnames SortedAttributes SortedTuples. 

(** Defining functions and aggregates, and giving their interpretation *)

Inductive symbol : Type := 
  | Symbol : string -> symbol
  | CstVal : value -> symbol.

Inductive predicate : Type := Predicate : string -> predicate.

Definition OP : Oset.Rcd predicate.
split with (fun x y => match x, y with Predicate s1, Predicate s2 => string_compare s1 s2 end).
- intros [s1] [s2]; generalize (Oset.eq_bool_ok Ostring s1 s2); simpl.
  case (string_compare s1 s2).
  + apply f_equal.
  + intros H1 H2; apply H1; injection H2; exact (fun h => h).
  + intros H1 H2; apply H1; injection H2; exact (fun h => h).
- intros [s1] [s2] [s3]; apply (Oset.compare_lt_trans Ostring s1 s2 s3).
- intros [s1] [s2]; apply (Oset.compare_lt_gt Ostring s1 s2).
Defined.

Definition symbol_compare (s1 s2 : symbol) := 
  match s1, s2 with
    | Symbol s1, Symbol s2 => string_compare s1 s2
    | Symbol _, CstVal _ => Lt
    | CstVal _, Symbol _ => Gt
    | CstVal v1, CstVal v2 => value_compare v1 v2
  end.

Definition OSymbol : Oset.Rcd symbol.
split with symbol_compare.
- intros [s1 | s1] [s2 | s2]; simpl; try discriminate.
  + generalize (Oset.eq_bool_ok Ostring s1 s2); simpl.
    case (string_compare s1 s2).
    * apply f_equal.
    * intros H1 H2; apply H1; injection H2; exact (fun h => h).
    * intros H1 H2; apply H1; injection H2; exact (fun h => h).
  + generalize (Oset.eq_bool_ok OVal s1 s2); simpl.
    case (value_compare s1 s2).
    * apply f_equal.
    * intros H1 H2; apply H1; injection H2; exact (fun h => h).
    * intros H1 H2; apply H1; injection H2; exact (fun h => h).
- intros [s1 | s1] [s2 | s2] [s3 | s3]; simpl;
  try (apply (Oset.compare_lt_trans Ostring) || 
             apply (Oset.compare_lt_trans OVal) || 
             trivial || discriminate).
- intros [s1 | s1] [s2 | s2]; simpl;
  try (apply (Oset.compare_lt_gt Ostring) || 
             apply (Oset.compare_lt_gt OVal) || 
             trivial || discriminate).
Defined.

Require Import compcert.lib.Integers.

Definition interp_symbol f := 
  match f with
    | Symbol "plus" => 
      fun l => 
        match l with 
          | Value_ptrofs a1 :: Value_ptrofs a2 :: nil => Value_ptrofs (Ptrofs.add a1 a2)
          | _ => Value_ptrofs Ptrofs.zero end
    | Symbol "mult" => 
      fun l => 
        match l with 
          | Value_ptrofs a1 :: Value_ptrofs a2 :: nil => Value_ptrofs (Ptrofs.mul a1 a2)
          | _ => Value_ptrofs Ptrofs.zero end
    | Symbol "minus" => 
      fun l => 
        match l with 
          | Value_ptrofs a1 :: Value_ptrofs a2 :: nil => Value_ptrofs (Ptrofs.sub a1 a2)
          | _ => Value_ptrofs Ptrofs.zero end
    | Symbol "opp" => 
      fun l => 
        match l with 
          | Value_ptrofs a1 :: nil => Value_ptrofs (a1 (* ? *)) 
          | _ => Value_ptrofs Ptrofs.zero end
    | CstVal v => 
      fun l => 
        match l with 
          | nil => v
          | _ => default_value (type_of_value v)
        end
    | _ => fun _ => Value_ptrofs Ptrofs.zero
  end.

Definition interp_predicate p := 
  match p with
    | Predicate "<" =>
      fun l =>
        match l with
          | Value_ptrofs a1 :: Value_ptrofs a2 :: nil => 
            match ptrofs_compare a1 a2 with Lt => true | _ => false end
          | _ => false
        end
    | Predicate "<=" =>
      fun l =>
        match l with
          | Value_ptrofs a1 :: Value_ptrofs a2 :: nil => 
            match ptrofs_compare a1 a2 with Gt => false | _ => true end
          | _ => false
        end

    | Predicate ">" =>
      fun l =>
        match l with
          | Value_ptrofs a1 :: Value_ptrofs a2 :: nil => 
            match ptrofs_compare a1 a2 with Gt => true | _ => false end
          | _ => false
        end

    | Predicate ">=" =>
      fun l =>
        match l with
          | Value_ptrofs a1 :: Value_ptrofs a2 :: nil => 
            match ptrofs_compare a1 a2 with Lt => false | _ => true end
          | _ => false
        end

    | Predicate "=" =>
      fun l =>
        match l with
          | Value_ptrofs a1 :: Value_ptrofs a2 :: nil => 
            match ptrofs_compare a1 a2 with Eq => true | _ => false end
          | Value_string s1 :: Value_string s2 :: nil =>
            match string_compare s1 s2 with Eq => true | _ => false end
          | _ => false
        end
   | _ => fun _ => false
  end.

Inductive aggregate : Type := 
  | Aggregate : string -> aggregate.

Definition OAgg : Oset.Rcd aggregate.
split with (fun x y => match x, y with Aggregate s1, Aggregate s2 => string_compare s1 s2 end).
- intros [s1] [s2]; generalize (Oset.eq_bool_ok Ostring s1 s2); simpl.
  case (string_compare s1 s2).
  + apply f_equal.
  + intros H1 H2; apply H1; injection H2; exact (fun h => h).
  + intros H1 H2; apply H1; injection H2; exact (fun h => h).
- intros [s1] [s2] [s3]; apply (Oset.compare_lt_trans Ostring s1 s2 s3).
- intros [s1] [s2]; apply (Oset.compare_lt_gt Ostring s1 s2).
Defined.

Definition interp_aggregate a := fun l =>
  match a with
    | Aggregate "count" => Value_ptrofs (Ptrofs.of_int (Int.repr (Zlength l)))
    | Aggregate "sum" => 
      Value_ptrofs 
        (fold_left (fun acc x => match x with Value_ptrofs x => (Ptrofs.add acc x)%N | _ => acc end) l Ptrofs.zero)
    | Aggregate "avg" =>
      Value_ptrofs 
        (let sum := 
                   fold_left (fun acc x => match x with 
                                           | Value_ptrofs x => (Ptrofs.add acc x)%N 
                                           | _ => acc end) l Ptrofs.zero in 
               Ptrofs.divu sum (Ptrofs.of_int (Int.repr (Zlength l))))
    | Aggregate _ => Value_ptrofs Ptrofs.zero
  end.

(** Building a database instance, and updating it  *)
Definition mk_tuple la f := mk_tuple T (Fset.mk_set FAN la) f.

Definition show_tuple t :=
  List.map
    (fun a => (a, dot T t a))
    (Fset.elements _ (support _ t)).

Definition show_bag_tuples x :=
  List.map show_tuple (Febag.elements (Fecol.CBag (CTuple T)) x).

Definition show_col_tuples x :=
  List.map show_tuple (Fecol.elements (CA := CTuple T) x).

Record db_state : Type :=
  mk_state
    {
      _relnames : list relname;
      _basesort : relname -> Fset.set FAN;
      _instance : relname -> Febag.bag (Fecol.CBag (CTuple T))
    }.

Definition show_state (db : db_state) :=
  (_relnames db,
   List.map (fun r => (r, Fset.elements _ (_basesort db r))) (_relnames db),
   List.map (fun r => (r, show_bag_tuples (_instance db r))) (_relnames db)).

Definition init_db :=
  mk_state
    nil
    (fun _ => Fset.empty FAN)
    (fun _ => Febag.empty (Fecol.CBag (CTuple T))).

Definition create_table 
           (* old state *) db 
           (* new table name *) t 
           (* new table sort *) st 
            :=
  mk_state
    (t :: _relnames db)
    (fun x =>
       match Oset.compare ORN x t with
         | Eq => Fset.mk_set FAN st
         |_ => _basesort db x
       end)
    (_instance db).

Definition insert_tuple_into  
           (* old state *) db 
           (* new tuple *) tpl 
           (* table *) tbl
            :=
  mk_state 
    (_relnames db)
    (_basesort db)
    (fun x =>
       match Oset.compare ORN x tbl with
       | Eq => Febag.add (Fecol.CBag (CTuple T)) tpl (_instance db tbl)
       |_ => _instance db x
       end).

Fixpoint insert_tuples_into
           (* old state *) db 
           (* new tuple list *) ltpl 
           (* table *) tbl :=
  match ltpl with
    | nil => db
    | t :: l => insert_tuple_into (insert_tuples_into db l tbl) t tbl
  end.

Definition MyDBS db := DatabaseSchema.mk_R (Tuple.A T) ORN (_basesort db).

Definition db0 := init_db.

Notation year := (Attr_ptrofs 0 "year").
Notation firstname := (Attr_string 0 "firstname").
Notation lastname := (Attr_string 0 "lastname").
Notation title := (Attr_string 0 "title").
Notation name := (Attr_string 0 "name").
Notation r_mid := (Attr_ptrofs 0 "r.mid").
Notation runtime := (Attr_ptrofs 0 "runtime").
Notation rank := (Attr_ptrofs 0 "rank").
Notation r_pid := (Attr_ptrofs 0 "r.pid").
Notation d_mid := (Attr_ptrofs 0 "d.mid").
Notation d_pid := (Attr_ptrofs 0 "d.pid").
Notation p_pid := (Attr_ptrofs 0 "p.pid").
Notation m_mid := (Attr_ptrofs 0 "m.mid").

(* role: mid, pid, name *)
Definition mk_role mid pid n :=
  mk_tuple
    (r_mid :: r_pid :: nil)
    (fun a => match a with 
              | r_mid => Value_ptrofs (Ptrofs.of_int (Int.repr mid))
              | r_pid => Value_ptrofs (Ptrofs.of_int (Int.repr pid)) 
              | name => Value_string n
              | Attr_string _ _ => Value_string ""
              | Attr_ptrofs _ _ => Value_ptrofs Ptrofs.zero
              end) base.nullval.

Definition roles := 
  mk_role 2120 640 "Man with Knife" 
    :: mk_role 2120 715 "J.J. Gittes"
    :: mk_role 2279 2330 "Cliff Stern"
    :: mk_role 2279 874 "Judah Rosenthal"
    :: mk_role 2406 4970 "Shrek"
    :: mk_role 2406 4972 "Princess Fiona"
    :: mk_role 2139 1805 "'Maxim' de Winter"
    :: mk_role 2139 1806 "Mrs. de Winter"
    :: nil.

(* director: mid, pid *)
Definition mk_director mid pid :=
  mk_tuple
    (d_mid :: d_pid :: nil)
    (fun a => match a with 
              | d_mid => Value_ptrofs (Ptrofs.of_int (Int.repr mid))
              | d_pid => Value_ptrofs (Ptrofs.of_int (Int.repr pid)) 
              | Attr_string _ _ => Value_string ""
              | Attr_ptrofs _ _ => Value_ptrofs Ptrofs.zero
              end) base.nullval.

Definition directors := 
  mk_director 2120 640
    :: mk_director 2279 2330
    :: mk_director 2406 4969
    :: mk_director 2139 464
    :: nil.

(* movie: mid, title, year, runtime, rank *)
Definition mk_movie mid t y rt rk :=
  mk_tuple 
    (m_mid :: title :: year :: nil)
    (fun a => match a with 
              | m_mid => Value_ptrofs (Ptrofs.of_int (Int.repr mid))
              | title => Value_string t 
              | year => Value_ptrofs (Ptrofs.of_int (Int.repr y))
              | runtime => Value_ptrofs (Ptrofs.of_int (Int.repr rt))
              | rank => Value_ptrofs (Ptrofs.of_int (Int.repr rk))
              | Attr_string _ _ => Value_string ""
              | Attr_ptrofs _ _ => Value_ptrofs Ptrofs.zero
              end) base.nullval.

Definition movies :=
  mk_movie 2120 "Chinatown" 1974 130 121
    :: mk_movie 2279 "Crimes and Misdemeanors" 1989 104 280
    :: mk_movie 2406 "Shrek" 2001 90 407
    :: mk_movie 2139 "Rebecca" 1940 130 140
    :: nil.


(* people: pid, firstname, lastname *)
Definition mk_people pid f l :=
  mk_tuple 
    (p_pid :: lastname :: nil)
    (fun a => match a with 
              | p_pid => Value_ptrofs (Ptrofs.of_int (Int.repr pid)) 
              | firstname => Value_string f
              | lastname => Value_string l 
              | Attr_string _ _ => Value_string ""
              | Attr_ptrofs _ _ => Value_ptrofs Ptrofs.zero
              end) base.nullval.

Definition people := 
  mk_people 640 "Roman" "Polanski" 
    :: mk_people 715 "Jack" "Nicholson"
    :: mk_people 2330 "Woody" "Allen"
    :: mk_people 874 "Martin" "Landau"
    :: mk_people 4970 "Mike" "Myers"
    :: mk_people 4972 "Cameron" "Diaz"
    :: mk_people 1805 "Laurence" "Olivier"
    :: mk_people 1806 "Joan" "Fontaine"
    :: mk_people 4969 "Vicky" "Jenson"
    :: mk_people 464 "Alfred" "Hitchcock"
    :: nil.

Definition create_schema := 
create_table 
  (create_table 
     (create_table 
        (create_table db0 (Rel "role") (r_mid :: r_pid :: name :: nil)) 
        (Rel "director") (d_mid :: d_pid :: nil)) 
     (Rel "people") (p_pid :: firstname :: lastname :: nil)) 
  (Rel "movie") (m_mid :: title :: year :: runtime :: rank :: nil).

Definition create_db roles directors people movies :=
  insert_tuples_into 
    (insert_tuples_into 
       (insert_tuples_into 
          (insert_tuples_into create_schema movies (Rel "movie"))
          people (Rel "people"))
       directors (Rel "director"))
    roles (Rel "role").

Definition db1 := create_db roles directors people movies.
                   
Require Import Signatures SeqScan HashIndexScan IndexJoin Filter QEP.

Module TPL <: TUPLE.
  Definition T := T.
End TPL.

Module QEP := QEP TPL.

Definition show c := 
   (map show_tuple (Cursor.materialize _ (QEP.eval_cursor c))).

(* The QEP *)
Definition seq_scan_on_role := QEP.SeqScan roles.

Definition hash_and_seq_scan_on_director :=
  QEP.SimpleHashIndexScan (d_mid :: d_pid :: nil) directors.

Definition hash_join :=
  QEP.IndexJoin (r_mid :: r_pid :: nil) seq_scan_on_role hash_and_seq_scan_on_director.

(* Projection for people: (p_pid, firstname, lastname) -> (p_pid) *)
Definition index_scan_on_people :=
  QEP.SimpleHashIndexScan (p_pid :: nil) people.

(* Projection for the deeper Index Join: (d_mid, d_pid, r_mid, r_pid) -> (d_pid) *)
Definition deeper_index_join :=
  QEP.IndexJoin (d_pid :: nil) hash_join index_scan_on_people.


(* Filter for movie year > 1950 *)
Definition theta_movie (x : tuple T) : bool :=
  match dot _ x year with
  | Value_ptrofs y => Ptrofs.lt (Ptrofs.of_int (Int.repr 1950)) y
  | _ => false
  end.

Lemma htheta_movie s f p1 p2:
  theta_movie (Tuple.mk_tuple _ s f p1) = theta_movie (Tuple.mk_tuple _ s f p2).
Proof.
  unfold theta_movie.
  unfold dot, dot_. simpl. unfold Tuple1.support, Tuple1.abs.
  simpl. reflexivity.
Qed.

(* Projection for movie: (m_mid, title, year, runtime, rank) -> (m_mid) *)
Definition index_scan_on_movie :=
  QEP.FilterHashIndexScan theta_movie htheta_movie (m_mid :: nil) movies.

(* Projection for the shallower Index Join: 
  (lastname, d_mid, d_pid, p_pid, r_mid, r_pid) -> d_mid) *)
Definition qep :=
  QEP.IndexJoin (d_mid :: nil) deeper_index_join index_scan_on_movie.

(* Cannot compute *)
(* Definition qep_run :=
  Eval compute in (map show_tuple (Cursor.materialize _ (QEP.eval_cursor qep))).
Print qep_run. *)
