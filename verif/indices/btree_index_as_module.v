Require Export VST.floyd.proofauto.
Require Import indices.btree_instance.
Require Import indices.ordered_interface.
Require Export VST.floyd.proofauto.

Import OrderedIndex.

Section BtreeIndexASI.
  Variable BtreeIndexPreds: index. Print funspecs.
  
  Definition BtreeIndexASI:funspecs := 
      [ go_to_key_spec  ].

