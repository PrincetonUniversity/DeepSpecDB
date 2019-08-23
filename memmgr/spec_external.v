Require Import VST.floyd.proofauto.
Require Import mmap0. 
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition placeholder_spec :=
 DECLARE _placeholder
 WITH u: unit
 PRE [ ]
   PROP (False) LOCAL() SEP()
 POST [ tint ]
   PROP() LOCAL() SEP().

Definition ispecs := [placeholder_spec].
