Require Import VST.floyd.proofauto.
Require Import malloc_lemmas.
Require Import malloc.
Require Import spec_malloc.
Require Import linking.

Definition Gprog : funspecs := user_specs_R ++ private_specs.

Lemma body_pre_fill:  semax_body Vprog Gprog f_pre_fill pre_fill_spec'.
Proof. 
start_function. 
rewrite <- seq_assoc.  
forward_call n. (*! b = size2bin(n) *)
destruct H as [[Hn_lo Hn_hi] Hp].
rep_omega.
forward.
set (b:=size2binZ n). 
assert (Hb: 0 <= b < BINS) by (apply size2bin_range; rep_omega).
forward_call b. (*! t2 = bin2size(b) *)
rewrite (mem_mgr_split_R gv b rvec) by apply Hb.
Intros bins idxs lens.
freeze [1; 3] Otherlists.
deadvars!.
destruct H as [[Hn_lo Hn_hi] Hp].
forward. (*! t4 = bin[b] *)
forward_call ((bin2sizeZ b), p, (Znth b bins), (Znth b lens)). (*! t3 = list_from_block(t2,p,t4) *)
{ split. pose proof (bin2size_range b). rep_omega. assumption. }
Intros q.
forward. (*! bin[b] = t3 *)
thaw Otherlists.

WORKING HERE - restore invar 
