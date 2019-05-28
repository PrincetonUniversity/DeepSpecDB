Require Import VST.floyd.proofauto.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.

Require Import Signatures.

Require Import db_operations.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import FiniteSet FlatData SortedTuples SortedAttributes Values Plans.

Fixpoint string_to_list_byte (s: string) : list byte :=
  match s with
  | EmptyString => nil
  | String a s' => Byte.repr (Z.of_N (Ascii.N_of_ascii a)) :: string_to_list_byte s'
  end.

Definition stringpool : Type := (* This is only temporary. *)
  { v | (type_of_value v) = type_string } -> val.

Program Definition val_of_value (sp : stringpool) (v : value) : val :=
  match v with
  | Value_string s => sp (exist _ v _)
  | Value_ptrofs x => Vint (Ptrofs.to_int x) end.

(* This need to be implemented. *)
Definition stringpool_rep (sp : stringpool) : mpred := emp.

Definition tuple := Tuple1.tuple attribute value OAN FAN.
Definition support := Tuple1.support attribute value OAN FAN.
Definition dot := Tuple1.dot attribute value OAN FAN.

Definition tuple_rep (sh : share) (t : tuple) (p : val) : mpred :=
  EX sp : stringpool,
          data_at sh (tarray size_t (Z.of_nat (Fset.cardinal FAN (support t))))
                  (map (val_of_value sp oo dot t) (Fset.elements FAN (support t))) p * stringpool_rep sp.

Definition t_attr_list := Tstruct _attribute_list_t noattr.

Definition id_of_attribute (a : attribute) : list byte :=
  match a with
  | Attr_string _ s => string_to_list_byte s
  | Attr_ptrofs _ s => string_to_list_byte s end.

Eval compute in reptype t_attr_list.

Definition domain_of_attribute (a : attribute) : val :=
  match a with
    | Attr_ptrofs _ _ => Vint (Int.repr 0)
    | Attr_string _ _ => Vint (Int.repr 1) end.

Definition attribute_string_rep sh (a : attribute) (p : val) : mpred :=
  match a with
  | Attr_ptrofs _ _ => emp
  | Attr_string _ s => cstring sh (string_to_list_byte s) p end.

Fixpoint attribute_lseg_rep (sh : share) (l : list attribute) (p q : val) : mpred :=
  match l with
  | [] => !! (p = q) && emp
  | a :: tl =>
    EX r : val, EX sptr : val, data_at sh t_attr_list (sptr, (domain_of_attribute a, r)) p * attribute_lseg_rep sh tl r q * attribute_string_rep sh a sptr end.

Definition attribute_list_rep sh l p := attribute_lseg_rep sh l p nullval.

Lemma attribute_list_rep_valid_pointer:
  forall sh l p,
   attribute_list_rep sh l p |-- valid_pointer p.
Proof.
  intros.
  unfold attribute_list_rep; destruct l; simpl; entailer!. Admitted.

Hint Resolve attribute_list_rep_valid_pointer : valid_pointer.

Definition attributes_rep (sh : share) (attrs : Fset.set FAN) (p : val) : mpred :=
  let attrs_list := Fset.elements _ attrs in
  attribute_list_rep sh attrs_list p.

Definition attribute_list_length_spec :=
 DECLARE _attribute_list_length
  WITH sh : share, l: val, attrs: Fset.set FAN
  PRE [ _l OF (tptr t_attr_list)]
     PROP(readable_share sh)
     LOCAL (temp _l l; temp _x l)
     SEP (attributes_rep sh attrs l)
  POST [ size_t ]
     PROP()
     LOCAL(temp ret_temp (Vint (Int.repr (Z.of_nat (Fset.cardinal _ attrs)))))
     SEP (attributes_rep sh attrs l).

Definition Gprog := ltac:(with_library prog [attribute_list_length_spec]).

Lemma body_sumarray: semax_body Vprog Gprog f_attribute_list_length attribute_list_length_spec.
Proof.
  start_function.
  forward.
  forward.
  forward_loop
    (EX x : val, EX l1 : list attribute, EX l2 : list attribute,
            PROP ( Fset.elements _ attrs = l1 ++ l2 )
                 LOCAL (temp _n (Vint (Int.repr (Zlength l1))); temp _x x; temp _l l)
                 SEP (attribute_lseg_rep sh l1 l x * attribute_lseg_rep sh l2 x nullval )).
  entailer. Exists l (@nil attribute) (Fset.elements _ attrs).
  entailer!. simpl. unfold attributes_rep, attribute_list_rep. entailer.
  entailer!.
  
