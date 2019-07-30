Require Import FMapInterface FMapList FMapFacts OrderedTypeEx.

Require Relations VST.floyd.functional_base VST.floyd.sublist VST.progs.conclib.

Fixpoint wf_guard {A} {R : A -> A -> Prop}
      (n : nat) (wfR : well_founded R) : well_founded R :=
    match n with
    | 0 => wfR
    | S n => fun x =>
       Acc_intro x (fun y _ => wf_guard n (wf_guard n wfR) y)
    end.
Strategy 100 [wf_guard].

Module Type BPlusTreeParams.
  Module InfoTyp.
    Parameter t: Type.
  End InfoTyp.
  Parameter min_fanout: nat.
End BPlusTreeParams.

Module Raw (X: OrderedType) (Params: BPlusTreeParams).

  Module Info := Params.InfoTyp.

  Module Omap := FMapList.Raw X.
  Import Omap Omap.PX Omap.MX.

  (* Order functions for X.t only *)
  Notation key_eq := X.eq.
  Notation key_le := TO.le.
  Notation key_lt := X.lt.
  Notation key_compare := X.compare.

  Section Forall_OMap.
    Context {elt: Type}.

    Definition Forall_range (P: elt -> Prop) (m: t elt): Prop :=
      forall k n, MapsTo k n m -> P n.

    Definition Forall_dom (P: key -> Prop) (m: t elt): Prop :=
      forall k, In k m -> P k.

    Lemma Forall_range_nil: forall P, Forall_range P (empty elt).
    Proof.
      intros P k n h. inversion h.
    Qed.

    Lemma Forall_range_cons: forall (P: elt -> Prop) k n m, P n -> Forall_range P m -> Forall_range P ((k, n) :: m).
    Proof.
      intros P k n m Pn Pm k' n' h.
      setoid_rewrite SetoidList.InA_cons in h. destruct h as [heq|htl].
      inversion heq; cbn in *; subst; assumption.
      eapply Pm; eassumption.
    Qed.

    Lemma Forall_range_inv: forall (P: elt -> Prop) k n m, Forall_range P ((k, n) :: m) ->
                                                  P n /\ Forall_range P m.
    Proof.
      intros P k n m Pnm. split.
      refine (Pnm k n _). constructor. apply eqke_refl.
      intros k' n' hk'n'. eapply Pnm. apply InA_cons_tl. apply hk'n'.
    Qed.

    Lemma Forall_dom_nil: forall P, Forall_dom P (empty elt).
    Proof.
      intros P k h. exfalso. destruct h.
      eapply empty_1. eassumption.
    Qed.

    Lemma Forall_dom_cons: forall (P: key -> Prop) k n m, Proper (key_eq ==> flip impl) P ->
                                                 P k -> Forall_dom P m -> Forall_dom P ((k, n) :: m).
    Proof.
      intros P k n m hP Pk Pm k' h.
      apply In_inv in h. destruct h as [heq|htl].
      setoid_rewrite heq; assumption.
      eapply Pm; eassumption.
    Qed.
    
    Lemma Forall_dom_inv: forall (P: key -> Prop) k n m, Forall_dom P ((k, n) :: m) ->
                                                  P k /\ Forall_dom P m.
    Proof.
      intros P k n m Pnm. split. eapply Pnm.
      exists n. constructor. apply eqke_refl.
      intros k' [n' hk'n']. eapply Pnm. exists n'. apply InA_cons_tl. apply hk'n'.
    Qed.

    Lemma Forall_dom_app: forall (P: key -> Prop) m m', Forall_dom P (m ++ m') <-> Forall_dom P m /\ Forall_dom P m'.
    Proof.
      split; intro h.
      + split; intros k [e hke]; eapply h; econstructor; setoid_rewrite InA_app_iff;
        [left|right]; eassumption.
      + intros k [e hke%InA_app]. destruct hke; [apply (proj1 h) | apply (proj2 h)]; econstructor; eassumption.
    Qed.

    Lemma Forall_dom_impl: forall (P Q: key -> Prop) m, (forall k, P k -> Q k) -> Forall_dom P m -> Forall_dom Q m.
    Proof.
      intros * h hP.
      intros k hk. apply h. apply hP. assumption.
    Qed.

  End Forall_OMap.

  Section Elt.
    
    (* elt is the type of the values stored in the B+Tree *)
    Context {elt: Type}.

    (* Order functions for pairs of type key * elt for a given elt type *)
    Arguments ltk {elt}. 
    Arguments eqk {elt}.
    Arguments eqke {elt}.
  
    Unset Elimination Schemes.
    
    Inductive node: Type :=
    | leaf: forall (entries: t elt) (info: Info.t), node
    | internal: forall (ptr0: node) (entries: t node) (info: Info.t), node.
    
    Lemma node_ind (P: node -> Prop)
          (hleaf: forall entries info, P (leaf entries info))
          (hinternal: forall ptr0 entries info,
              P ptr0 ->
              Forall_range P entries ->
              P (internal ptr0 entries info)) :
      forall n, P n.
    Proof.
      fix hrec 1.
      intros [].
      apply hleaf.
      apply hinternal. apply hrec.
      induction entries as [|[k n] entries]. apply Forall_range_nil.
      apply Forall_range_cons; auto.
    Qed.

    Lemma node_rect (P: node -> Type)
          (hleaf: forall entries info, P (leaf entries info))
          (hinternal: forall ptr0 entries info,
              P ptr0 ->
              (forall k n, find k entries = Some n -> P n) ->
              P (internal ptr0 entries info)) :
      forall n, P n.
    Proof.
      fix hrec 1.
      intros [].
      apply hleaf.
      apply hinternal. apply hrec.
      induction entries as [|[k n] entries] using list_rect. intros * h; inversion h.
      intros * h. rewrite find_equation in h.
      destruct key_compare. 
      discriminate.
      inversion h as [hnn0]. rewrite <- hnn0. apply hrec.
      eapply IHentries. eassumption.
    Qed.

    Set Elimination Schemes.

    Inductive direct_subnode: relation node :=
    | subnode_ptr0: forall ptr0 entries info,
        direct_subnode ptr0 (internal ptr0 entries info)
    | subnode_entry: forall k n ptr0 entries info,
        MapsTo k n entries ->
        direct_subnode n (internal ptr0 entries info).

    Lemma direct_subnode_wf: well_founded direct_subnode.
    Proof.
      unfold well_founded.
      apply (node_ind (fun n => Acc direct_subnode n)).
      + constructor. intros n hn. inversion hn.
      + intros * hptr0 hentries. constructor.
        intros n hn. inversion hn. assumption.
        eapply hentries. eassumption.
    Qed.
    
    Definition subnode: relation node := Relation_Operators.clos_refl_trans node direct_subnode.

    Inductive balanced: nat -> node -> Prop :=
    | balanced_leaf: forall {entries info}, balanced 0 (leaf entries info)
    | balanced_internal: forall {depth ptr0 entries info},
        balanced depth ptr0 -> Forall_range (balanced depth) entries ->
        balanced (S depth) (internal ptr0 entries info). 
    
    Fixpoint well_sorted (min max: key) (n: node): Prop :=
      match n with
      | leaf entries info => Sorted ltk entries /\
                            key_lt min max /\ (* in case entries is empty *)
                            Forall_dom (fun k => key_le min k /\ key_lt k max) entries
      | internal ptr0 entries info => Sorted ltk entries /\
                                     exists max_ptr0, well_sorted min max_ptr0 ptr0 /\
                                     (fix ws_entries l: forall (min: key), Prop :=
                                        match l with
                                        | nil => fun min => key_le min max
                                        | (k, n) :: tl => fun min =>
                                                          key_le min k /\
                                                          exists max_n, well_sorted k max_n n /\
                                                                   ws_entries tl max_n
                                        end) entries max_ptr0
      end.

    Add Parametric Morphism: key_lt
      with signature key_eq ==> key_eq ==> iff as key_lt_mor.
    Proof. exact lt_compat. Qed.

    Add Parametric Morphism: key_le
      with signature key_eq ==> key_eq ==> iff as key_le_mor.
    Proof. intros k1 k1' hk1 k2 k2' hk2.
           do 2 rewrite IsTO.le_lteq.
           setoid_rewrite hk1. setoid_rewrite hk2. reflexivity.
    Qed.

    Add Parametric Morphism: well_sorted
        with signature key_eq ==> key_eq ==> eq ==> iff as ws_mor.
    Proof.
      intros min min' hmin max max' hmax n.
      revert n min min' hmin max max' hmax.
      apply (node_ind (fun n => 
                       forall (min min' : key),
  key_eq min min' -> forall max max' : key, key_eq max max' -> well_sorted min max n <-> well_sorted min' max' n)).
      + intros * hmin * hmax.
        simpl. unfold Forall_dom. setoid_rewrite hmin. setoid_rewrite hmax. reflexivity.
      + intros * hptr0 hentries * hmin * hmax.
        simpl. Set Default Timeout 2.
        apply and_iff_compat_l.
        match goal with
          | |- (ex ?a) <-> (ex ?b) => enough (henough: forall k, a k <-> b k)
        end.
        setoid_rewrite henough. reflexivity.
        intro k.
        rewrite <- hptr0. apply and_iff_compat_l.
        generalize dependent k. clear hentries.
        induction entries as [|[k n] entries].
        setoid_rewrite hmax. easy.
        intro k'. apply and_iff_compat_l.
        setoid_rewrite IHentries. reflexivity. order. order. 
    Qed.      
    
    Inductive well_sized: node -> Prop :=
    | ws_leaf: forall entries info, Params.min_fanout <= length entries <= 2 * Params.min_fanout -> well_sized (leaf entries info)
    | ws_internal: forall ptr0 entries info,
        Params.min_fanout <= length entries <= 2 * Params.min_fanout ->
        well_sized ptr0 -> Forall_range well_sized entries -> well_sized (internal ptr0 entries info).

    Fixpoint well_sized' (n: node): Prop := 
      match n with
      | leaf entries info => Params.min_fanout <= length entries <= 2 * Params.min_fanout
      | internal ptr0 entries info =>
        Params.min_fanout <= length entries <= 2 * Params.min_fanout /\
        well_sized' ptr0 /\
        (fix forall_entries l acc := 
           match l with | nil => acc | (k, n) :: tl => acc /\ well_sized' n end) entries True
      end.
    
    Definition is_leaf (n: node): Prop :=
      match n with
      | leaf _ _ => True
      | _ => False
      end.

    Definition is_leaf_dec (n: node): { is_leaf n } + { ~ is_leaf n } :=
      match n as m return { is_leaf m } + { ~ is_leaf m } with
      | leaf _ _ => left I
      | internal _ _ _ => right (fun hcontr => hcontr)
      end.

    Definition node_info (n: node): Info.t := 
      match n with | leaf _ info | internal _ _ info => info end.
    
    (* Here, we would like to use omap.Raw functions, but such a definition doesn't pass
       Coq's structural recursion criterion *)

    Fixpoint flatten (n: node): t elt :=
      match n with
      | leaf entries _ => entries
      | internal ptr0 entries _ => flatten ptr0 ++ flat_map (compose flatten snd) entries
      end.
    
    Fixpoint cardinal (n: node): nat :=
      match n with
      | leaf entries _ => Datatypes.length entries
      | internal ptr0 entries _ => cardinal ptr0 + fold_right Nat.add 0%nat (List.map (compose cardinal snd) entries)
      end.

    Lemma cardinal_flatten_length: forall n, length (flatten n) = cardinal n.
    Proof.
      apply node_ind.
      + intros. reflexivity.
      + intros * hlength hchildren.
        simpl. rewrite app_length, hlength, flat_map_concat_map, conclib.length_concat,
               map_map. do 2 f_equal.
        apply map_ext_in.
        intros [k n'] hin. eapply hchildren. apply SetoidList.In_InA. apply eqke_equiv. eassumption.
    Qed.

    Lemma well_sorted_extends: forall n min max min' max',
        key_le min' min -> key_le max max' ->
        well_sorted min max n ->
        well_sorted min' max' n.
    Proof.
      apply (node_ind (fun n => forall min max min' max',
                           key_le min' min -> key_le max max' ->
                           well_sorted min max n ->
                           well_sorted min' max' n)).
      + intros * hm hM (hsorted & hminmax & hentries). split; [|split].
      - assumption.
      - order.
      - eapply Forall_dom_impl; try eassumption.
        intros k []. split; order.
      + intros * hptr0 hentries * hm hM hn.
        destruct hn as (hsorted & max_ptr0 & ptr0_ws & entries_ws).
        split. assumption.
        exists max_ptr0. split.
        eapply hptr0. eassumption. apply OrderTac.le_refl. assumption.
        clear - entries_ws hm hM.
        revert entries_ws. generalize max_ptr0.
        induction entries as [|[k n] entries].
        - order.
        - intros max_ptr1 (hk & max_n & ws_n & rest).
          split. assumption. exists max_n. split. assumption. apply IHentries.
          assumption.
    Qed.

    Lemma well_sorted_lt: forall n min max,
        well_sorted min max n -> key_lt min max.
    Proof.
      apply (node_ind (fun n => forall min max, well_sorted min max n -> key_lt min max)).
      + simpl; easy.
      + intros * hptr0 hentries * h.
        eapply hptr0. destruct h as (keys_sorted & max_ptr0 & ptr0_ws & entries_ws).
        assert (key_le max_ptr0 max).
        { clear keys_sorted ptr0_ws.
          revert dependent max_ptr0. induction entries as [|[k n] entries].
          easy.
          intros max_ptr0 (hk & max_n & n_ws & rest).
          apply IHentries in rest. eapply hentries in n_ws. 
          order. constructor. apply eqke_refl.
          eapply Forall_range_inv. eassumption. }
        eapply well_sorted_extends; try eassumption. order.
    Qed.

    (* It is required to prove at the same time the bounds and the sortedness,
       because the bounds of l1 and l2 are needed for the sortedness of l1 ++ l2 *)
    Lemma well_sorted_flatten: forall n min max,
        well_sorted min max n ->
        Forall_dom (fun k => key_le min k /\ key_lt k max) (flatten n) /\ Sorted ltk (flatten n).
    Proof.
      apply (node_ind (fun n => forall min max, well_sorted min max n ->
                                        Forall_dom (fun k => key_le min k /\ key_lt k max) (flatten n) /\ Sorted ltk (flatten n))).
      + cbn; easy.
      + intros * hptr0 hentries * h. simpl in h |- *.
        destruct h as (keys_sorted & max_ptr0 & ptr0_ws & entries_ws).
        
        assert (hle: forall entries min max,
                   (fix ws_entries (l : list (X.t * node)) : key -> Prop :=
                      match l with
                      | nil => fun min : key => key_le min max
                      | (k, n) :: tl =>
                        fun min : key =>
                          key_le min k /\ (exists max_n : key, well_sorted k max_n n /\ ws_entries tl max_n)
                      end) entries min ->
                   key_le min max /\
                   forall k n, MapsTo k n entries -> key_le min k /\
                                               exists max_n, well_sorted k max_n n /\ key_le max_n max).
        { clear. induction entries as [|[k n] entries].
          easy. intros min max (hk & max_n & n_ws & rest).
          specialize (IHentries _ _ rest). pose proof (well_sorted_lt _ _ _ n_ws).
          destruct IHentries as [hle hin].
          split. order. intros k' n' hk'n'%InA_cons.
          destruct hk'n' as [[hk' hn']|hmapsto]. simpl in hk', hn'.
          split. order. exists max_n. split.          
          setoid_rewrite hk'. subst n'. assumption.
          order.
          specialize (hin _ _ hmapsto).
          destruct hin as (hlek' & h).
          split. order. assumption. }

        rewrite Forall_dom_app, and_assoc. split.
        - refine (proj1 (hptr0 _ _ _)).
          eapply well_sorted_extends in ptr0_ws. eassumption. order.
          specialize (hle _ _ _ entries_ws). easy.
        - 
        specialize (hptr0 _ _ ptr0_ws). destruct hptr0 as [ptr0_flatten_bounds ptr0_flatten_sorted].
        enough (henough: Forall_dom (fun k : key => key_le max_ptr0 k /\ key_lt k max) (flat_map (compose flatten snd) entries) /\
                Sorted ltk (flat_map (compose flatten snd) entries)).
        destruct henough as [hbounds hsorted].
        split.
        eapply Forall_dom_impl; try eassumption. intros k [].
        apply well_sorted_lt in ptr0_ws. split; order.
        eapply SortA_app. apply eqke_equiv. assumption. assumption.
        intros [k e] [k' e'] hke hk'e'.
        specialize (hbounds k' (ex_intro _ e' hk'e')).
        specialize (ptr0_flatten_bounds k (ex_intro _ e hke)). simpl in ptr0_flatten_bounds, hbounds.
        destruct ptr0_flatten_bounds, hbounds. order.
        clear ptr0_ws ptr0_flatten_bounds ptr0_flatten_sorted ptr0.        
        generalize dependent max_ptr0.
        induction entries as [|[k n] entries].
        -- split. apply Forall_dom_nil. constructor.
        -- intros min' (hk & max_n & n_ws & rest).
           apply Forall_range_inv in hentries.
           destruct hentries as [hn hrest].
           specialize (hn _ _ n_ws).
           apply Sorted_inv in keys_sorted. simpl.
           specialize (IHentries
                        ltac:(easy) ltac:(easy) _ rest).
           destruct IHentries as [hforallrec hsortedrec]. split.
           apply Forall_dom_app. split.
           intros k' hk'. specialize ((proj1 hn) k' hk').
           simpl. intros []. apply hle in rest. destruct rest. split; order.
           intros k' hk'.
           specialize (hforallrec k' hk'). destruct hforallrec. apply well_sorted_lt in n_ws. split; order.
           eapply SortA_app. apply eqke_equiv.
           easy. assumption.
           intros [k1 e1] [k2 e2] h1 h2.
           pose proof ((proj1 hn) k1 (ex_intro _ _ h1)) as h1'.
           pose proof (hforallrec k2 (ex_intro _ _ h2)) as h2'.
           destruct h1', h2'.
           order.
    Qed.

  Section ZSection.
    Import floyd.functional_base msl.base progs.conclib.
    
    Instance Inhabitant_node {default_info: Inhabitant Info.t}:
      Inhabitant node := leaf [] default_info.

    Context {default_key: Inhabitant key}
            {default_info: Inhabitant Info.t} {default_elt: Inhabitant elt}.

    Definition Zcardinal (n: node): Z := Z.of_nat (cardinal n).

    Lemma Zcardinal_flatten_Zlength n : Zlength (flatten n) = Zcardinal n.
    Proof.
      rewrite Zlength_correct, cardinal_flatten_length. reflexivity.
    Qed.
    
    Lemma HdRel_dec {A: Type} (R: relation A) (hR: forall a b, {R a b} + {~ R a b}):
      forall x l, {HdRel R x l} + {~ HdRel R x l}.
    Proof.
      destruct l as [|hd tl].
      + left. constructor.
      + destruct (hR x hd).
        - left. constructor. assumption.
        - right. intros hcontr%HdRel_inv. contradiction.
    Defined.

    Fixpoint find_record_index_aux k0 (entries : t elt) i: Z :=
      match entries with
      | nil => i
      | (k, rec) :: tl =>
        match key_compare k0 k with
        | GT _ => find_record_index_aux k0 tl (i + 1)
        | _ => i
        end
      end.

    Definition find_record_index (k0: key) (entries: t elt): Z :=
      find_record_index_aux k0 entries 0.

    Lemma find_record_index_aux_add: forall k l i,
        find_record_index_aux k l i = find_record_index_aux k l 0 + i.
    Proof.
      induction l as [|[k' e'] l].
      + simpl; intros; omega.
      + simpl. intro i. destruct key_compare. omega.
        omega. rewrite (IHl (i + 1)), (IHl 1). omega.
    Qed. 

    Lemma find_record_index_bounds: forall k l,
        0 <= find_record_index k l <= Zlength l.
    Proof.
      unfold find_record_index.
      induction l as [|[k' e'] l].
      + cbn; omega.
      + simpl. rewrite Zlength_cons. destruct key_compare. omega.
        omega. rewrite find_record_index_aux_add.
        omega.
    Qed. 

    Fixpoint find_child_index_aux (k0: key) (entries: t node) i: Z :=
        match entries with
        | nil => i - 1
        | (k, rec) :: tl => match key_compare k0 k with
                          | LT _ => i - 1
                          | _ => find_child_index_aux k0 tl (i + 1)
                          end
        end.

    Lemma find_child_index_aux_add: forall k l i,
        find_child_index_aux k l i = find_child_index_aux k l 0 + i.
    Proof.
      induction l as [|[k' e'] l].
      + simpl; intros; omega.
      + simpl. intro i. rewrite (IHl (i + 1)), (IHl 1). destruct key_compare. omega.
        omega. omega.
    Qed.

    Definition find_child_index (k0: key) (entries: t node): Z :=
      find_child_index_aux k0 entries 0.
   
    (* find_child_index does not depend on the nodes inside the map, only the keys *)
    Add Parametric Morphism: find_child_index
      with signature key_eq ==> eqlistA eqk ==> eq as find_child_index_mor.
    Proof.
      intros x y hxy l l' hll'.
      unfold find_child_index.
      revert dependent l'.
      induction l as [|[k n] l].
      + intros * hnil. inversion hnil. subst. reflexivity.
      + intros * hll'. inversion hll' as [|?[k'' n''] ? ? heq].
        simpl. rewrite (find_child_index_aux_add x), (find_child_index_aux_add y).
        rewrite <- IHl by assumption.
        unfold eqk in heq. simpl in heq.
        destruct key_compare, key_compare; try order; reflexivity.
    Qed.
    
    Lemma find_child_index_bounds: forall k l,
        -1 <= find_child_index k l < Zlength l.
    Proof.
      unfold find_child_index.
      induction l as [|[k' e'] l].
      + cbn; omega.
      + rewrite Zlength_cons. simpl.
        rewrite find_child_index_aux_add.
        destruct key_compare; omega.
    Qed.
        (* It never happens that a child is inserted into an internal node that already contains the key *)
    Definition add_child (k: key) (n: node) (i: Z) (entries: t node): t node :=
      sublist 0 i entries ++ (k, n) :: sublist i (Zlength entries) entries.

    Lemma add_child_correct: forall k0 n0 entries,
        ~ In k0 entries ->
        add_child k0 n0 (find_child_index k0 entries + 1) entries = add k0 n0 entries.
    Proof.
      intros * hin.
      unfold add_child, find_child_index.
      induction entries as [|[k' n'] entries].
      + cbn; reflexivity.
      + simpl. destruct key_compare.
        - simpl.
          rewrite sublist_same; reflexivity.
        - exfalso. apply hin.
          eapply PX.In_eq. apply X.eq_sym. eassumption.
          exists n'. constructor. apply eqke_refl.
        - rewrite find_child_index_aux_add.
          pose proof (find_child_index_bounds k0 entries) as hb. unfold find_child_index in hb.
          rewrite sublist_0_cons, sublist_S_cons, <- Z.add_assoc, <- Z.add_sub_assoc by omega.
          simpl.
          rewrite Zlength_cons, <- Z.add_1_r, <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r by omega.
          rewrite IHentries. reflexivity.
          intros [n'' hn'']. apply hin. exists n''. apply InA_cons_tl. assumption.
    Qed.

    Definition add_record (k: key) (e: elt) (i: Z) (entries: t elt): t elt :=
      if X.eq_dec (fst (@Znth _ (k, e) i entries)) k then
        upd_Znth i entries (k, e)
      else
        sublist 0 i entries ++ (k, e) :: sublist i (Zlength entries) entries.

    Lemma add_record_correct: forall k0 e0 entries,
        add_record k0 e0 (find_record_index k0 entries) entries = add k0 e0 entries.
    Proof.
      intros.
      unfold add_record.
      induction entries as [|[k e] entries]; unfold find_record_index.
      + cbn; destruct X.eq_dec; reflexivity.
      + simpl. destruct key_compare.
        - rewrite Znth_0_cons. simpl. rewrite if_false by order.
          rewrite sublist_same; reflexivity.
        - rewrite Znth_0_cons. simpl. rewrite if_true by order.
          rewrite upd_Znth0, sublist_1_cons, Zlength_cons, <- Z.add_1_r,
          <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r, sublist_same; reflexivity.
        - rewrite find_record_index_aux_add.
          pose proof (find_record_index_bounds k0 entries) as hb.
          unfold find_record_index in hb.
          rewrite Zlength_cons, Znth_pos_cons, upd_Znth_cons, sublist_0_cons', sublist_S_cons,
            <- Z.add_1_r by omega.
          do 2 rewrite <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r by omega.
          rewrite <- IHentries. destruct X.eq_dec; reflexivity.
    Qed.

    Definition update_internal (ptr0: node) (entries: t node) (new: node) (i: Z):
      node * t node :=
      if Z_lt_ge_dec i 0 then (new, entries)
      else (ptr0, upd_Znth i entries (fst (Znth i entries), new)).

    Lemma update_internal_same_keys: forall ptr0 entries new i,
        i < Zlength entries ->
        eqlistA eqk (snd (update_internal ptr0 entries new i)) entries.
    Proof.
      intros.
      unfold update_internal.
      destruct Z_lt_ge_dec. reflexivity.
      simpl. rewrite eqlistA_altdef.
      erewrite <- (upd_Znth_triv i) by (try omega; reflexivity).
      unfold upd_Znth.
      apply Forall2_app. rewrite <- eqlistA_altdef. reflexivity.
      constructor. unfold eqk. reflexivity.
      rewrite <- eqlistA_altdef. reflexivity.
    Qed.      

    Lemma update_internal_correct_ptr0: forall ptr0 entries new k0,
        HdRel key_lt k0 (List.map fst entries) ->
        update_internal ptr0 entries new (find_child_index k0 entries) = (new, entries). 
    Proof.
      intros * h.
      enough (henough: find_child_index k0 entries = -1).
      + rewrite henough. reflexivity.
      + induction entries as [|[k n] entries].
      - reflexivity.
      - unfold find_child_index. simpl.
        apply HdRel_inv in h. simpl in h.
        destruct key_compare. reflexivity. order. order.
    Qed.
    
    Lemma update_internal_correct_entries: forall ptr0 entries new k0 k1,
        Sorted ltk entries ->
        In k1 entries -> key_le k1 k0 ->
        (* k1 is the highest key that is <= k0 *)
        Forall_dom (fun k2 => key_le k2 k0 -> key_le k2 k1) entries ->
        let pair := update_internal ptr0 entries new (find_child_index k0 entries) in
        fst pair = ptr0 /\ eqlistA eqke (snd pair) (add k1 new entries). 
    Proof.
      intros * hsort hin hle hsup.
      unfold update_internal, find_child_index.
      induction entries as [|[k n] entries].
      + destruct hin as [n1 hn1]. inversion hn1.
      + destruct hin as [n1 hin%InA_cons].
        destruct hin as [[eqk eqn]|hin].
      - simpl in eqk, eqn |- *.
        destruct (key_compare k1 k); try order.
        pose proof (find_child_index_bounds k0 entries) as hb. unfold find_child_index in hb.
        destruct (key_compare k0 k); cbn.
        -- repeat f_equal; order. 
        -- rewrite find_child_index_aux_add.
           rewrite if_false by omega.
           pose proof (hsup k (ex_intro _ n (InA_cons_hd _ (eqke_refl _))) ltac:(order)).
           replace (find_child_index_aux k0 entries 0) with (-1).
           rewrite upd_Znth0, sublist_1_cons, Zlength_cons, sublist_same by
               (try rewrite Zlength_cons; omega).
           simpl. split. reflexivity. constructor. split; simpl. order. reflexivity.
           reflexivity.
           (* unprovable, TODO: change for sth else than Leibniz equality *)
           { apply Sorted_inv in hsort.
             destruct entries as [|[k' n'] entries].
             + reflexivity.
             + simpl.
               pose proof (HdRel_inv (proj2 hsort)) as hlt.
               unfold ltk in hlt. simpl in hlt.
               destruct key_compare. reflexivity. order. order. }                 
        -- rewrite find_child_index_aux_add, if_false by omega.
           f_equal. replace (find_child_index_aux k0 entries 0) with (-1).
           rewrite Znth_0_cons, upd_Znth0, sublist_S_cons, sublist_same by (try rewrite Zlength_cons; omega).
           simpl. split. reflexivity. constructor. split; simpl. order. reflexivity. reflexivity.
           { apply Sorted_inv in hsort.
             destruct entries as [|[k' n'] entries].
             + reflexivity.
             + simpl.
               pose proof (HdRel_inv (proj2 hsort)) as hlt.
               unfold ltk in hlt. simpl in hlt. 
               specialize (hsup k' (ex_intro _ n' (InA_cons_tl _ (InA_cons_hd _ (eqke_refl _))))).
               destruct key_compare; try reflexivity; specialize (hsup ltac:(order)); order.
           } 
      - apply Sorted_inv in hsort. apply Forall_dom_inv in hsup.
        specialize (IHentries ltac:(easy) (ex_intro _ n1 hin) ltac:(easy)).
        apply InA_eqke_eqk in hin.
        pose proof (PX.Sort_Inf_In (proj1 hsort) (proj2 hsort) hin) as hlt.
        unfold ltk in hlt. simpl in hlt.
        simpl. destruct key_compare; try order.
        rewrite find_child_index_aux_add.
        pose proof (find_child_index_bounds k0 entries) as hb. unfold find_child_index in hb.
        enough (find_child_index_aux k0 entries 0 <> -1).
        ++ rewrite if_false in IHentries |- * by omega. destruct key_compare; try order.
           simpl in IHentries |- *.
           split. reflexivity.
           rewrite upd_Znth_cons, Znth_pos_cons, <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r by omega.
           constructor. reflexivity. easy.
        ++ destruct entries as [|[k' n'] entries]. inversion hin.
           pose proof (find_child_index_bounds k0 entries) as hb'. unfold find_child_index in hb'.
           simpl in hb' |- *. destruct key_compare; try rewrite find_child_index_aux_add; try omega.
           rewrite InA_cons in hin. destruct hin as [heq | hin].
        -- unfold eqk in heq. simpl in heq. order.
        -- enough (key_lt k' k1). order.
           destruct hsort as [hsort _]. apply Sorted_inv in hsort.
           epose proof (PX.Sort_Inf_In (proj1 hsort) (proj2 hsort) hin) as hlt'.
           unfold ltk in hlt'. simpl in hlt'. order.
    Qed.

    Function get_cursor(k0: key) (root: node)
             {wf direct_subnode root}: list (Z * node) :=
      match root with
      | leaf entries info => [(find_record_index k0 entries, root)]
      | internal ptr0 entries info =>
        let i := find_child_index k0 entries in
        (i, root) :: get_cursor k0 (@Znth _ ptr0 i (List.map snd entries))
      end.
    Proof.
      + intros * heq.
        destruct (eq_dec (find_child_index k0 entries) (-1)) as [hptr0|hentry].
      - rewrite hptr0. apply subnode_ptr0. 
      - eapply subnode_entry.
        eapply In_InA. apply eqke_equiv.
        pose proof (find_child_index_bounds k0 entries).
        rewrite (@Znth_map _ (default_key, ptr0)) by (unfold Inhabitant, key; omega).
        rewrite <- surjective_pairing.
        apply Znth_In. omega.
      + apply (wf_guard 32), direct_subnode_wf.
    Defined.

    Import Sumbool. Arguments sumbool_and {A B C D}.

    Notation min_fanout := (Z.of_nat Params.min_fanout).
    
    Fixpoint insert_aux (k0: key) (e: elt) (cursor: list (Z * node)):
      node * option (key * node) :=
      match cursor with
      | (i, leaf entries info) :: _ =>
        let new_entries := add_record k0 e i entries in
        if Z_gt_le_dec (Zlength entries + 1) (2 * min_fanout) then
          let new_info := info in
          let new_node_left := leaf (sublist 0 min_fanout new_entries) info in
          let new_node_right := leaf (sublist min_fanout (2 * min_fanout + 1) new_entries) new_info in
          (new_node_left, Some ((Znth min_fanout (List.map fst new_entries)), new_node_right))
        else (leaf new_entries info, None)
      | (i, internal ptr0 entries info) :: tl =>
        let (new_at_i, new_entry) := insert_aux k0 e tl in
        let (ptr0, entries) := update_internal ptr0 entries new_at_i i in
        match new_entry with
        | Some (new_key, new_child) =>
          let new_entries := add_child new_key new_child (i + 1) entries in
          if Z_gt_le_dec (Zlength entries + 1) (2 * min_fanout) then
            let new_info := info in
            let new_node_left := internal ptr0 (sublist 0 min_fanout new_entries) info in
            let (new_key, new_ptr0) := Znth min_fanout new_entries in
            let new_node_right := internal new_ptr0 (sublist (min_fanout + 1) (2 * min_fanout + 1) new_entries) new_info in
            (new_node_left, Some (new_key, new_node_right))
          else (internal ptr0 new_entries info, None)
        | None => (internal ptr0 entries info, None)
        end
      | [] => (default, None)
      end.

    Definition insert (k0: key) (e: elt) (new_info: Info.t) (root: node): node :=
      let c := get_cursor k0 root in
      let (root, new_entry) := insert_aux k0 e c in
      match new_entry with
      | None => root
      | Some new_entry => internal root [new_entry] new_info
      end.
(*
    Lemma insert_aux_new_key:
      insert_aux k0 e (get_cursor k0 root) = (left, Some (new_k, new_right)) ->
      find_child_index new_k entries = find_child_index k0 entries + 1.
*)
    Definition min (k1 k2: key): key :=
      match key_compare k1 k2 with LT _ => k1 | _ => k2 end.

    Definition max (k1 k2: key): key :=
      match key_compare k1 k2 with GT _ => k1 | _ => k2 end.

    Lemma Sorted_sublist: forall X R (l: list X) lo hi,
        Sorted R l -> Sorted R (sublist lo hi l).
    Proof.
      induction l; intros * h.
      + now rewrite sublist_of_nil.
      + destruct (Z_lt_ge_dec lo hi).
      - destruct (Z_gt_le_dec lo 0).
        { rewrite sublist_S_cons by assumption. apply IHl.
          inversion h. assumption. }
        { rewrite sublist_0_cons' by omega.
          apply Sorted_inv in h. destruct h as [hsorted hR].
          constructor. apply IHl. easy.
          destruct l.
          rewrite sublist_of_nil. constructor.
          apply HdRel_inv in hR.
          destruct (Z_lt_ge_dec lo (hi - 1)).
          rewrite sublist_0_cons' by omega. constructor. assumption.
          rewrite sublist_nil_gen by omega. constructor. }
      - rewrite sublist_nil_gen. constructor. omega.
    Qed.
    
    Lemma insert_aux_well_sorted: forall root k0 e m M,
        well_sorted m M root ->
        let (left, oright) := insert_aux k0 e (get_cursor k0 root) in
        match oright with
        | None => well_sorted (min m k0) (max M k0) left
        | Some (right_k, right_n) => well_sorted (min m k0) right_k left /\
        well_sorted right_k (max M k0) right_n
        end.
    Proof.
      apply (node_ind (fun root => forall k0 e m M,
                           well_sorted m M root ->
                           let (left, oright) := insert_aux k0 e (get_cursor k0 root) in
                           match oright with
                           | None => well_sorted (min m k0) (max M k0) left
                           | Some (right_k, right_n) => well_sorted (min m k0) right_k left /\
                                                       well_sorted right_k (max M k0) right_n
                           end)).
      + intros * h.
        rewrite get_cursor_equation. simpl.
        destruct h as (entries_sorted & hmM & entries_bounds).
        destruct Z_gt_le_dec.
      - rewrite add_record_correct.
        split3; [split3 | | split].
        -- apply Sorted_sublist, add_sorted, entries_sorted.
        -- admit.
        -- admit.
        -- apply Sorted_sublist, add_sorted, entries_sorted.
        -- admit.
        -- admit.
      - rewrite add_record_correct. split3.
        -- apply add_sorted, entries_sorted.
        -- admit.
        -- admit.
    + intros * hptr0 hentries * h.
      rewrite get_cursor_equation.
      destruct h as (entries_sorted & max_ptr0 & ws_ptr0 & ws_entries).
      simpl.
      remember (find_child_index k0 entries) as i.
      case_eq (insert_aux k0 e (get_cursor k0 (@Znth _ ptr0 i (List.map snd entries)))).
      intros left [[new_k right]|] heqrec.
      - rewrite (surjective_pairing (update_internal _ _ _ _)).
        destruct Z_gt_le_dec.
        ++ rewrite (surjective_pairing (Znth _ _)).           
           
           Check add_child_correct.
           admit.
           (* setoid_rewrite update_internal_same_keys at 1. reflexivity. *)
        ++ admit.
      - rewrite (surjective_pairing (update_internal _ _ _ _)).
        destruct (eq_dec i (-1)) as [hm1|hm1].
        ++ rewrite hm1 in heqrec |- *. cbn in heqrec |- *.
           unfold default in heqrec.
           specialize (hptr0 k0 e _ _ ws_ptr0).
           rewrite heqrec in hptr0. split. assumption.
           exists (max max_ptr0 k0). split.
           assumption.
           
        simpl.
    Admitted.

  End ZSection.
  End Elt.

End Raw.

Import VST.floyd.val_lemmas.

Module MyParams <: BPlusTreeParams.
  Module InfoTyp.
    Definition t := unit.
  End InfoTyp.
  Definition min_fanout: nat := 1.
End MyParams.

Module bt := Raw DecidableTypeEx.Z_as_DT MyParams.

Section Tests.
  Import bt.
  Fixpoint insert_list (n: node) (l: list Z): @node (unit + unit) :=
    match l with
    | nil => n
    | k :: tl => insert_list (@bt.insert _ _ tt k (inl tt) tt n) tl
    end.    
  
  (* Definition test := insert_list (leaf nil tt) (map (Z.mul 2) (conclib.upto 100)). *)

  Definition test' := insert_list (leaf nil tt) (map (compose (Z.add 1) (Z.mul 2)) (rev (conclib.upto 18))).
  Compute test'.
  Compute insert 219 (inr tt) tt test'.

End Tests.





    Fixpoint find_path (k0: key) (root: node) {struct root}: list (Z * node) :=
      match root with
      | leaf entries info =>
        let index := (fix get_index entries index :=
                        match entries with
                        | [] => index
                        | (k, r) :: entries =>
                          if Xf.lt_dec k k0 then get_index entries (index + 1) else index
                        end) entries 0 in [(index, root)]
      | internal ptr0 (((first_k, first_n) :: _) as entries) info =>
        if Xf.lt_dec k0 first_k then (-1, root) :: find_path k0 ptr0 else
          (fix get_cursor_entry entries index :=
             match entries with
             | [] => [] (* impossible case *)
             | [(k, n)] => (index, root) :: find_path k0 n
             | (k, n) :: (((k', n') :: _) as entries) =>
               if (sumbool_and (Z_le_dec k k0) (Z_lt_ge_dec k0 k')) then (index, root) :: find_path key n
               else get_cursor_entry entries (index + 1)
             end) entries 0
      | internal ptr0 [] p => (-1, root) :: find_path k0 ptr0
      end.

    Theorem find_path_leaf: forall key entries info,
        exists i, find_path key (leaf entries info) = [(i, leaf entries info)] /\
             0 <= i <= Zlength entries /\
             Forall (Z.gt key) (sublist 0 i (map fst entries)) /\
         (i < Zlength entries -> fst (Znth i entries) >= key).
Proof.
  intros.
  pose (i entries z := (fix get_index (entries0 : list (Z * V)) (index : Z) {struct entries0} : Z :=
         match entries0 with
         | [] => index
         | (k, _) :: entries1 => if Z_ge_lt_dec k key then index else get_index entries1 (index + 1)
         end) entries z).
  
  assert (hadd: forall entries z, i entries z = i entries 0 + z).
  { intro l; induction l as [|[k n] l]; simpl; intro z.
    omega.
    destruct Z_ge_lt_dec. omega.
    rewrite (IHl (z + 1)), (IHl 1).
    omega. }
  
  assert (hbounds: forall entries, 0 <= i entries 0 <= Zlength entries).
  { intro l; induction l as [|[k' n'] l]; simpl.
    - easy.
    - rewrite Zlength_cons. destruct Z_ge_lt_dec. omega.
      rewrite hadd. omega. }

  assert (hforall: Forall (Z.gt key) (sublist 0 (i entries 0) (map fst entries))).
  { induction entries as [|[k n] entries].
    rewrite sublist_nil_gen. constructor.
    unfold i; omega. simpl.
    destruct Z_ge_lt_dec. rewrite sublist_nil_gen. constructor. omega.
    specialize (hbounds entries).
    rewrite sublist_0_cons' by (try rewrite hadd; rep_omega). constructor. omega.
    rewrite hadd, <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r. assumption. }

  exists (i entries 0); split3; auto; split; auto.
  { clear hforall; induction entries as [|[k n] entries].
    cbn. omega.
    simpl. destruct Z_ge_lt_dec. rewrite Znth_0_cons. simpl; omega.
    rewrite Zlength_cons, hadd, Znth_pos_cons,
      <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r by (specialize (hbounds entries); rep_omega).
    intros. apply IHentries. omega. }
Qed.

Theorem find_path_internal: forall key ptr0 entries info,
    exists i, find_path key (internal ptr0 entries info) =
         (i, internal ptr0 entries info) :: find_path key (@Znth _ ptr0 i (map snd entries)) /\
         -1 <= i < Zlength entries /\
         Forall (Z.ge key) (sublist 0 (i + 1) (map fst entries)) /\
         (i + 1 < Zlength entries -> key < Znth (i + 1) (map fst entries)).
Proof.
  intros.
  destruct entries as [|[first_k first_n] entries]; simpl.
  + exists (-1). split3.
    - reflexivity.
    - rewrite Zlength_nil; omega.
    - now rewrite sublist_of_nil, Zlength_nil, Znth_nil.
  + destruct Z_lt_ge_dec as [hlt | hge]; simpl.
    - exists (-1). rewrite Zlength_cons, Znth_underflow, sublist_nil, Znth_0_cons by omega.
      split3; try easy; rep_omega.
    - generalize (internal ptr0 ((first_k, first_n) :: entries) info) as root.
      revert hge.
      generalize first_k as k, first_n as n. clear first_k first_n. intros.

      pose (i l z := (fix get_index (l : list (Z * node)) index :=
                     match l with
                     | [] => index
                     | [(k, n)] => index
                     | (k, _) :: ((k', _) :: _) as tl =>
                       if (sumbool_and (Z_le_dec k key) (Z_lt_ge_dec key k'))
                       then index
                       else get_index tl (index + 1)
                     end) l z).
      
      assert (hadd: forall l z, i l z = i l 0 + z).
      { induction l as [|[k' n'] l]; intros; simpl.
        omega.
        destruct l as [|[k'' n''] l]. omega.
        destruct sumbool_and. omega. rewrite (IHl (z + 1)), (IHl 1). omega. }
      
      assert (hbounds: forall l k n z, z <= i ((k, n) :: l) z < z + 1 + Zlength l).
      { induction l as [|[k' n'] l]; intros. simpl.
        rewrite Zlength_nil; simpl; omega.
        specialize (IHl k' n' (z + 1)). rewrite Zlength_cons; simpl in IHl |- *.
        destruct sumbool_and; rep_omega. }
      
      exists (i ((k, n) :: entries) 0).
      split3.
      ++ generalize k as k0, n as n0.
         change 1 with (0 + 1) at 2.
         generalize 0 at -5 as z.
         induction entries as [|[k0 n0] entries]; intros.
         reflexivity.
         simpl; destruct sumbool_and.
         reflexivity.
         simpl in hadd.
         rewrite IHentries.
         rewrite (Znth_pos_cons _ (n0 :: _)).
         simpl. 
         specialize (hadd ((k0, n0) :: entries) 1). simpl in hadd.
         rewrite hadd. rewrite <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r. reflexivity. 
         destruct entries as [|[k' n'] entries]. omega.
         destruct sumbool_and. omega. specialize (hbounds entries k' n' 2). omega.
      ++ pose proof (hbounds entries k n 0) as h.
         rewrite Zlength_cons; omega.
      ++ split.
      -- revert hge. generalize k as k0, n as n0. 
         induction entries as [|[k' n'] entries]; intros.
         cbn. constructor. omega. constructor.
         specialize (IHentries k' n').
         rewrite <- hadd in IHentries.
         pose proof (hbounds entries k n 1). pose proof (hbounds entries k' n' 1).
         simpl in *. rewrite sublist_0_cons in IHentries by rep_omega.
         destruct sumbool_and.
         cbn. constructor. omega. constructor.
         rewrite sublist_0_cons by rep_omega.
         constructor. apply Z.le_ge. omega.
         rewrite <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r, sublist_0_cons by rep_omega.
         constructor. omega.
         specialize (IHentries ltac:(omega)).
         inversion IHentries. assumption.
      -- revert hge. generalize k. induction entries as [|[k' n'] entries]. 
         cbn; intros; omega.
         simpl; intros k_ hk_.
         specialize (IHentries k'). specialize (hbounds entries k' n' 1).
         destruct sumbool_and.
         * simpl. rewrite Znth_pos_cons, Znth_0_cons; omega.
         * rewrite <- hadd in IHentries. simpl in IHentries.
           rewrite Znth_pos_cons. rewrite <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r.
           intro h. apply IHentries. omega.
           rewrite Zlength_cons, Zlength_cons in h.
           rewrite Zlength_cons. rep_omega.
           simpl in hbounds. rep_omega.
Qed.

Corollary find_path_hd: forall key root,
    exists tl, map snd (find_path key root) = root :: tl.
Proof.
  intros.
  destruct root as [|ptr0].
  + pose proof (find_path_leaf key entries info) as hleaf.
    destruct hleaf as [i (heq & _)].
    rewrite heq. exists nil. reflexivity.
  + pose proof (find_path_internal key ptr0 entries info) as hinternal.
    destruct hinternal as [i (heq & _)].
    rewrite heq. exists (map snd (find_path key (@Znth _ ptr0 i (map snd entries)))). reflexivity.
Qed.

Corollary find_path_Zlength: forall key root depth,
    balanced depth root ->
    Zlength (find_path key root) = depth + 1.
Proof.
  intro key. apply (node_ind (fun root => forall depth, balanced depth root -> Zlength (find_path key root) = depth + 1)).
  + intros * h. inversion h. reflexivity.
  + intros * hptr0 hentries depth h.
    inversion h. edestruct find_path_internal as [i (heq & hbounds & _)].
    rewrite heq. rewrite Zlength_cons.
    destruct (eq_dec i (-1)).
    - subst. replace (Znth _ _) with ptr0 by now compute.
      erewrite hptr0 by eassumption. reflexivity.
    - rewrite Forall_forall in hentries.
      erewrite hentries. reflexivity. apply Znth_In. rewrite Zlength_map; rep_omega.
      eapply computable_theorems.Forall_forall1. eassumption.
      apply Znth_In. rewrite Zlength_map; rep_omega.
Qed.

Theorem find_path_is_path: forall key root,
    Sorted (flip direct_subnode) (map snd (find_path key root)).
Proof.
  intro key.
  apply node_ind.
  + repeat constructor.
  + intros * hptr0 hentries.
    edestruct (find_path_internal key ptr0 entries info) as [i (heq & hbounds & hbefore & hafter)].
    rewrite heq.
    case_eq (@Znth _ ptr0 i (map snd entries)).
  - intros entries' info' h.
    edestruct (find_path_leaf key entries' info') as [i' (heq' & hbounds' & hbefore' & hafter')].
    rewrite heq'. constructor. do 2 constructor.
    constructor. simpl. rewrite <- h.
    destruct (eq_dec i (-1)) as [hm1|hm1].
    rewrite hm1. compute. constructor.
    apply subnode_entry. apply Znth_In. rewrite Zlength_map; rep_omega.
  - intros ptr0' entries' info' h.
    edestruct (find_path_internal key ptr0' entries' info') as [i' (heq' & hbounds' & hbefore' & hafter')].
    rewrite heq'. simpl.
    destruct (eq_dec i (-1)) as [hm1 | hm1].
    * rewrite hm1 in *. compute in h. rewrite h.
      constructor. rewrite h, heq' in hptr0.
      assumption.
      constructor. constructor.
    * constructor. rewrite Forall_forall in hentries.
      specialize (hentries (internal ptr0' entries' info')).
      rewrite heq' in hentries. apply hentries.
      rewrite <- h. apply Znth_In. rewrite Zlength_map. omega.
      constructor. rewrite <- h. apply subnode_entry with (n := Znth i (map snd entries)).
      apply Znth_In. rewrite Zlength_map. omega.
Qed.

Corollary find_path_subnode: forall key root n,
    List.In n (map snd (find_path key root)) -> subnode n root.
Proof.
  intros key root. rewrite <- Forall_forall.
  change (fun x => subnode x root) with (flip subnode root).
  apply Sorted_extends.
  apply flip_Transitive. unfold subnode, Transitive. apply rt_trans.
  edestruct find_path_hd as [tl htl].
  rewrite htl.
  constructor. rewrite <- htl.
  apply Sorted_ind with (R := flip direct_subnode). constructor.
  intros * hl hldirect hhdrel. constructor. assumption.
  inversion hhdrel. constructor. constructor. apply rt_step. assumption.
  apply find_path_is_path.
  constructor. apply rt_refl.
Qed.

Fixpoint insert_aux (key: Z) (rec: V) (l: list (Z * node)):
  node * option (Z * node) :=
  match l with
  | (i, leaf entries info) :: _ =>
    if (sumbool_and (Z_lt_ge_dec i (Zlength entries)) (eq_dec (fst (Znth i entries)) key)) then
      (leaf (upd_Znth i entries (key, rec)) info, None)
    else
      let new_entries := sublist 0 i entries ++ (key, rec) :: sublist i (Zlength entries) entries in
      if Z_gt_le_dec (Zlength entries + 1) (2 * param) then
        let new_info := nullval in
        let new_node_left := leaf (sublist 0 param new_entries) info in
        let new_node_right := leaf (sublist param (2 * param + 1) new_entries) new_info in
        (new_node_left, Some (fst (Znth param new_entries), new_node_right))
      else (leaf new_entries info, None)
  | (i, internal ptr0 entries info) :: tl =>
    let (new_at_i, entry_to_add) := insert_aux key rec tl in
    let ptr0 := if eq_dec i (-1) then new_at_i else ptr0 in
    let entries := if Z_ge_lt_dec i 0 then upd_Znth i entries (fst (Znth i entries), new_at_i) else entries in
    match entry_to_add with
    | None => (internal ptr0 entries info, None)
    | Some (new_key, new_node) =>
      let new_entries := sublist 0 (i + 1) entries ++ (new_key, new_node) :: sublist (i + 1) (Zlength entries) entries in
      if Z_gt_le_dec (Zlength entries + 1) (2 * param) then
        let new_info := nullval in
        let new_node_left := internal ptr0 (sublist 0 param new_entries) new_info in
        let new_node_right := internal (snd (Znth param new_entries))
                                       (sublist (param + 1) (2 * param + 1) new_entries) info in
        (new_node_left, Some (fst (Znth param new_entries), new_node_right))
      else (internal ptr0 new_entries info, None)
    end 
  | [] => (default, None)
  end.

Definition insert (root: node) (key: Z) (value: V): node :=
  let path := find_path key root in
  let (root, new_entry) := insert_aux key value path in
  match new_entry with
    | None => root
    | Some new_entry => internal root [new_entry] nullval
  end.



Lemma Sorted_ltk_map: forall X (l: list (Z * X)),
    Sorted ltk l <-> Sorted Z.lt (map fst l).
Proof.
  intros.
  unfold ltk.
  induction l. split; constructor.
  cbn; split; intros h%Sorted_inv; destruct h as [hsorted hhdrel]; constructor.
  + rewrite <- IHl. assumption.
  + inversion hhdrel. constructor. constructor. assumption.
  + rewrite IHl. assumption.
  + inversion hhdrel. symmetry in H0. apply map_eq_nil in H0. subst. constructor. 
    destruct l. discriminate. inversion H. subst. constructor. assumption.
Qed.

Lemma Sorted_insert {X} {x: Inhabitant X}: forall (l: list (Z * X)) i key value,
    0 <= i <= Zlength l ->
    Sorted ltk l ->
    Forall (Z.gt key) (sublist 0 i (map fst l)) ->
    (i < Zlength l -> fst (Znth i l) > key) ->
    Sorted ltk (sublist 0 i l ++ (key, value) :: sublist i (Zlength l) l).
Proof.
  intros * hi hsorted hbefore hafter.
  destruct (eq_dec i (Zlength l)) as [heq|hneq].
  - rewrite sublist_same_gen, sublist_nil_gen by rep_omega.
    rewrite sublist_same_gen in hbefore by (try rewrite Zlength_map; rep_omega).
    clear -hsorted hbefore.
    rewrite Sorted_ltk_map, map_app. simpl. rewrite Sorted_ltk_map in hsorted.
    induction l. repeat constructor.
    simpl. constructor. apply IHl. now inversion hsorted. now inversion hbefore.
    destruct l; constructor. inversion hbefore; omega. inversion hsorted. now inversion H2.
  - rewrite Sorted_ltk_map, map_app, map_sublist, map_cons, map_sublist, (sublist_next i), Znth_map by
        (try rewrite Zlength_map; rep_omega).
    specialize (hafter ltac:(rep_omega)).
    erewrite <- sublist_same in hsorted by reflexivity.
    rewrite sublist_split with (mid := i), (sublist_next i), Sorted_ltk_map, map_app, map_cons, map_sublist, map_sublist in hsorted by (try rewrite Zlength_sublist; rep_omega).
    revert hafter hbefore hsorted. simpl. clear.
    generalize (sublist 0 i (map fst l)) (sublist (i + 1) (Zlength l) (map fst l)) (fst (Znth i l)).
    intros. induction l0.
    constructor. assumption. constructor. omega.
    simpl. constructor. apply IHl0. now inversion hbefore. now inversion hsorted.
    destruct l0. constructor. inversion hbefore; omega.
    constructor. inversion hsorted. inversion H2. assumption.    
Qed.

Lemma Sorted_bounds {X} {inh: Inhabitant X} (l: list (Z * X)): forall m M,
  Zlength l > 0 ->
  Sorted ltk l ->
  m <= fst (Znth 0 l) ->
  fst (Znth (Zlength l - 1) l) < M ->
  Forall (fun k => m <= k < M) (map fst l).
Proof.
  induction l as [|[k n] l].
  + constructor.
  + simpl. intros * hlen hsort%Sorted_inv hm hM.
    clear hlen.
    destruct l as [|[k' n'] l].
    - constructor. cbn in hM. omega.
      constructor.
    - destruct hsort as [hsort hhdrel].
      apply HdRel_inv in hhdrel. unfold ltk in hhdrel. cbn in hhdrel.
      specialize (IHl m M ltac:(rewrite Zlength_cons; rep_omega)
                 hsort ltac:(cbn; rep_omega)).
      rewrite Zlength_cons, Znth_pos_cons in hM by (rewrite Zlength_cons; rep_omega).
      unfold Z.succ in hM. rewrite Z.add_simpl_r in hM.
      specialize (IHl hM). constructor. rewrite Forall_forall in IHl.
      specialize (IHl k' ltac:(cbn; constructor; reflexivity)). 
      omega. assumption.
Qed.

Lemma Sorted_bounds_sublist {X} {inh: Inhabitant X}: forall (l: list (Z * X)) i j,
    0 <= i < j -> j < Zlength l ->
    Sorted ltk l ->
    Forall (fun k => fst (Znth i l) <= k < fst (Znth j l)) (sublist i j (map fst l)).
Proof.
  intros * hij hj hsort.
  rewrite sublist_map.
  apply Sorted_bounds.
  rewrite Zlength_sublist; omega.
  now apply Sorted_sublist.
  rewrite Znth_sublist, Z.add_0_l by omega. easy.
  rewrite Zlength_sublist, Znth_sublist by omega.
  replace (j - i - 1 + i) with (j - 1) by omega.
  assert (hj': 0 < j < Zlength l) by omega. clear hj hij.
  generalize dependent j.
  induction l. rewrite Zlength_nil; intros; rep_omega.
  intros j hj. 
  destruct (eq_dec j 1). subst. rewrite Znth_0_cons, Znth_pos_cons by omega.
  simpl. apply Sorted_inv in hsort. destruct l. cbn in hj. omega.
  cbn. destruct hsort as [_ hhd]. now inversion hhd.
  rewrite Znth_pos_cons, Znth_pos_cons by omega. apply IHl.
  now inversion hsort. rewrite Zlength_cons in hj; omega.
Qed.

Lemma good_root_node:
  forall n, good_root n ->
       num_keys n >= param ->
       exists m M, good_node m M n.
Proof.
  intros * hn hkeys.
  pose (l := flatten n).
  destruct n as [|ptr0]; cbn in hn, hkeys, l; rewrite Zlength_map in hkeys.
  + exists (fst (Znth 0 l)). exists (fst (Znth (Zlength l - 1) l) + 1).
    destruct hn as [hnsorted hnlength].
    constructor. assumption. omega.
    apply Sorted_bounds. rep_omega.
    assumption. easy. unfold l. omega.
  + destruct hn as (min_ptr0 & max_ptr0 & max & hlen & hptr0 & hentries).
    exists min_ptr0. exists max.
    econstructor. 
    omega. eassumption. assumption.
Qed.

Lemma Sorted_add: forall (l l': list Z) m M key,
    Add key l l' ->
    Forall (fun k => m <= k < M) l ->
    Forall (fun k => Z.min m key <= k < Z.max M (key + 1)) l'.
Proof.
  intros * hadd hl.
  pose proof (Z.le_min_l m key). pose proof (Z.le_max_l M (key + 1)).
  induction hadd.
  + constructor. split. apply Z.le_min_r. apply (Z.lt_le_trans _ (key + 1)).
    omega. apply Z.le_max_r.
    eapply Forall_impl; try eassumption. simpl.
    intros. omega.
  + inversion hl. constructor. omega.
    apply IHhadd. now inversion hl.
Qed.

Theorem insert_aux_good: forall key rec n,
    match insert_aux key rec (find_path key n) with
    | (le, None) => good_root n -> good_root le
    | (le, Some (rik, ri)) => forall m M, good_node m M n ->
                                    good_node (Z.min m key) rik le /\ good_node rik (Z.max M key) ri
    end.
Proof.
  intros key rec.
  apply (node_ind2 (fun n =>
                     match insert_aux key rec (find_path key n) with
                     | (le, None) => good_root n -> good_root le
                     | (le, Some (rik, ri)) =>
                       forall m M, good_node m M n ->
                              good_node (Z.min m key) rik le /\ good_node rik (Z.max M key) ri
                     end)).
  + intros *.
    edestruct find_path_leaf as (i & heq & hbounds & hbefore & hafter). rewrite heq.
    simpl.
    destruct sumbool_and as [[hilt hifst] | ].
    - intros [sorted_entries Zlength_entries]. split.
       ++ rewrite Sorted_ltk_map, <- upd_Znth_map, <- hifst, upd_Znth_triv, <- Sorted_ltk_map;
          try rewrite Zlength_map; try rewrite Znth_map; auto; rep_omega.
       ++ rewrite upd_Znth_Zlength; rep_omega.
    - assert (Zlength (sublist 0 i entries ++ (key, rec) :: sublist i (Zlength entries) entries) =
             Zlength entries + 1).
      { rewrite Zlength_app, Zlength_sublist, Zlength_cons, Zlength_sublist; rep_omega. }
      destruct Z_gt_le_dec.
       ++ intros * hgn.
          assert (hforall: Forall (fun k => Z.min m key <= k < Z.max M key) (sublist 0 i (map fst entries) ++ key :: sublist i (Zlength entries) (map fst entries))).
          { admit. }
          assert (hsorted: Sorted ltk (sublist 0 i entries ++ (key, rec) :: sublist i (Zlength entries) entries)).
          { inversion hgn.
            apply Sorted_insert; try assumption.
            destruct o; omega. }
          split.
          -- constructor.
             +++ apply Sorted_sublist; assumption. 
             +++ rewrite Zlength_sublist; rep_omega.
             +++ rewrite map_sublist.
                 eapply Forall_impl;
                 try apply Sorted_bounds_sublist; try assumption; try rep_omega.
                 simpl. intros k hk.
                 assert (Z.min m key <= fst (Znth 0 (sublist 0 i entries ++ (key, rec) :: sublist i (Zlength entries) entries))).
                 { rewrite Forall_forall in hforall. specialize (hforall (fst (Znth 0 (sublist 0 i entries ++ (key, rec) :: sublist i (Zlength entries) entries)))).
                   refine (proj1 (hforall _)).
                   rewrite <- Znth_map, map_app, map_sublist, map_cons, map_sublist by rep_omega.
                   apply Znth_In.
                   rewrite Zlength_app, Zlength_sublist, Zlength_cons, Zlength_sublist; try rewrite Zlength_map; rep_omega. }
                 omega.
          -- constructor.
             +++ apply Sorted_sublist; assumption.
             +++ rewrite Zlength_sublist; rep_omega.
             +++ apply Sorted_bounds.
                 rewrite Zlength_sublist; rep_omega.
                 apply Sorted_sublist; assumption.
                 rewrite Znth_sublist, Z.add_0_l by rep_omega. omega.
                 rewrite Forall_forall in hforall.
                 unshelve eapply (proj2 (hforall _ _)).
                 rewrite <- Znth_map by (rewrite Zlength_sublist; rep_omega). eapply sublist_In.
                 rewrite map_sublist, map_app, map_sublist, map_cons, map_sublist.
                 apply Znth_In. rewrite Zlength_sublist, Zlength_sublist;
                 try rewrite Zlength_app, Zlength_sublist, Zlength_cons, Zlength_sublist; try rewrite Zlength_map; rep_omega.
       ++ intros [sorted_entries Zlength_entries]. split.
          -- apply Sorted_insert; auto.
             intros h. destruct o; omega.
          -- rep_omega.
  + intros * hZnth *.
    edestruct find_path_internal as [i (heq & hbounds & hbefore & hafter)].
    rewrite heq. specialize (hZnth i hbounds).
    simpl.
    case_eq (insert_aux key rec (find_path key (@Znth _ ptr0 i (map snd entries)))); intros le [[ri_k ri]|] hrem; rewrite hrem in hZnth.
    - destruct Z_gt_le_dec.
      -- intros * h. 
         admit.
      -- intros (min_ptr0 & max_ptr0 & max & hZlength & hptr0 & hentries).
         simpl.
         admit.
   - intros (min_ptr0 & max_ptr0 & max & hZlength & hptr0 & hentries).
     destruct eq_dec, Z_ge_lt_dec.
     ++ simpl.
Admitted.

Corollary insert_good: forall key rec root,
    good_root root -> good_root (insert root key rec).
Proof.
  intros * h.
  unfold insert.
  pose proof (insert_aux_good key rec root) as haux.
  case_eq (insert_aux key rec (find_path key root)); intros n [[k ri]|] heq; rewrite heq in haux.
  + assert (hnode: exists m M, good_node m M root).
    {
      apply good_root_node. assumption.
      clear -heq.
      destruct root as [|ptr0]; unfold num_keys, keys; rewrite Zlength_map.
      + edestruct find_path_leaf as (i & heqpath & hb & hbefore & hafter).
        rewrite heqpath in heq. simpl in heq. destruct sumbool_and.
        discriminate. destruct Z_gt_le_dec. omega. discriminate.
      + edestruct find_path_internal as (i & heqpath & hb & hbefore & hafter).
        rewrite heqpath in heq. simpl in heq. destruct insert_aux as [new_at_i [[]|]].
        destruct Z_gt_le_dec as [h|h]. destruct Z_ge_lt_dec.
        rewrite upd_Znth_Zlength in h; omega. omega.
        discriminate. discriminate.
    }
    destruct hnode as (m & M & hnode).
    destruct (haux _ _ hnode) as [gptr0 gri].
    simpl.
    exists (Z.min m key). exists k. exists (Z.max M key).
    split3. rewrite Zlength_cons, Zlength_nil. rep_omega.
    assumption. econstructor. eassumption. constructor. omega.
  + auto.
Qed.


Require Import VST.floyd.functional_base.
Require Import VST.progs.conclib VST.floyd.sublist.

Section Values.
  Import VST.veric.val_lemmas.
  
  Definition V: Type := {p: val | is_pointer_or_null p}.
  Definition nullV: V := exist _ nullval mapsto_memory_block.is_pointer_or_null_nullval.

  Instance Inhabitant_V: Inhabitant V := nullV.

  Instance EqDecV: EqDec V.
  Proof. 
    intros [x hx] [y hy]. destruct (eq_dec x y) as [heq | hneq].
    + left. now apply exist_ext.
    + right. intro hcontr. apply hneq. inversion hcontr. reflexivity.
  Qed.
End Values.

Require FMapList FMapFacts Structures.OrderedTypeEx.
Require Import Sorting.Sorted.

Section Tests.

  Definition aux (l: list Z): list (Z * V) := map (fun k => (k, nullV)) l.
  
  Definition test_node: node :=
    internal (leaf (aux [1; 2; 3]) nullval)
             [(4, leaf (aux [4; 5; 6]) nullval);
              (7, leaf (aux [7; 8; 9]) nullval);
              (11, leaf (aux [11; 12; 13]) nullval)] nullval.

  Compute (find_path 10 test_node).
  Print insert.
  Compute (find_path 13 test_node).
  Print insert_aux.
  Definition x: V.
   refine (exist _ (Vptr 1%positive Ptrofs.zero) _). easy.
  Defined.
  
  Fixpoint insert_list (n: node) (l: list (Z * V)): node :=
    match l with
    | [] => n
    | (key, rec) :: tl => insert_list (insert n key rec) tl
    end.    

  Definition test := flatten (insert_list default (combine (upto 100) (Zrepeat 100 x))).

  Compute test.

End Tests.
