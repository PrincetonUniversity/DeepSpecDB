Require Export VST.floyd.proofauto.
Require Export deepDB.clight.verifiable.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
