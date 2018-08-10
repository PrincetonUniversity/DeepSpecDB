Require Export VST.floyd.proofauto.
Require Export DB.clight.index_string.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
