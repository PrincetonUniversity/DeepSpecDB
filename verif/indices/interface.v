Require Import VST.floyd.functional_base VST.floyd.proofauto.
Record index :=
  {
    key: Type;
    key_repr: key -> val -> mpred;
    
    value: Type;
    value_repr: value -> val -> mpred;

    cursor := Z;
    
    a: Type
  }.


