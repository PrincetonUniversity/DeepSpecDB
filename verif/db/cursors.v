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


Require Import FunInd.
Require Import Coq.Strings.Ascii.

Require Import Signatures.


Search "cursor".

Print Cursor.
(* now we have that cursor interface from the French *)

Require Import btrees.

Print cursor.


