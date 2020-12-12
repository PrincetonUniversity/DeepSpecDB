Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import indices.ordered_interface.
Require Import indices.spec_BtreeIndexASI.
Require Import indices.btree_instance.
Require Import VST.msl.wand_frame.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.
Module DB_Cursor.

Import OrderedIndex.

Record db_cursor (oi: OrderedIndex.index) :=
{ 
  db_cursor_type: type;
  db_key_type: type;
  db_value_type: type;
  db_index_type:type;

  db_entry_rep: val -> val -> mpred;
  db_cursor_rep: oi.(cursor) -> val -> mpred
}.

(* =================  FUNSPECS (VOID PTRS + DB CURSOR) =============== *)

Definition create_index_spec_vp 
  (oi: OrderedIndex.index) (db: db_cursor oi): funspec :=
  WITH u:unit, gv: globals
  PRE [ ]
    PROP ()
    PARAMS() GLOBALS(gv)
    SEP (mem_mgr gv)
  POST [tptr (db_index_type oi db) ]
    EX m: oi.(t), EX pr: val,
    PROP (oi.(create_index) m)
    LOCAL(temp ret_temp pr)
    SEP (mem_mgr gv; oi.(t_repr) m pr). 

Definition put_record_spec_vp 
  (oi: OrderedIndex.index) (db: db_cursor oi): funspec :=
   WITH cur: oi.(cursor), key:oi.(key), pkey: val, record:oi.(value), gv: globals,
            e_ptr: val, ws_ptr: val
  PRE [ tptr (db_cursor_type oi db), tptr (db_key_type oi db), tptr (db_value_type oi db)]
    PROP(oi.(put_record_props) cur)
    PARAMS(ws_ptr; e_ptr; oi.(value_ptr) record) GLOBALS(gv)
    SEP(mem_mgr gv; 
          (db_cursor_rep oi db) cur ws_ptr * 
          (db_entry_rep oi db) e_ptr (oi.(key_val) key))
  POST [tvoid]
    EX newc: oi.(cursor), 
    PROP(oi.(put_record) cur key record newc)
    LOCAL()
    SEP(mem_mgr gv; (db_cursor_rep oi db) newc ws_ptr * 
          (db_entry_rep oi db) e_ptr (oi.(key_val) key)).

Definition go_to_key_spec_vp
  (oi: OrderedIndex.index) (db: db_cursor oi): funspec :=
  WITH cur:oi.(cursor), key:oi.(key), e_ptr: val, ws_ptr: val
  PRE [ tptr (db_cursor_type oi db), tptr (db_key_type oi db) ]
    PROP(oi.(go_to_key_props) cur)
    PARAMS(ws_ptr; e_ptr) GLOBALS()
    SEP((db_cursor_rep oi db) cur ws_ptr * 
      (db_entry_rep oi db) e_ptr (oi.(key_val) key))
  POST [tint]
    PROP()
    LOCAL(temp ret_temp (Val.of_bool (oi.(cursor_has_next) (oi.(go_to_key) cur key))))
    SEP((db_cursor_rep oi db) (oi.(go_to_key) cur key) ws_ptr * 
      (db_entry_rep oi db) e_ptr (oi.(key_val) key)).

Definition cardinality_spec_vp
  (oi: OrderedIndex.index) (db: db_cursor oi): funspec :=
  WITH cur: oi.(cursor), ws_ptr:val
  PRE [tptr (db_cursor_type oi db)]
    PROP()
    PARAMS(ws_ptr) GLOBALS()
    SEP((db_cursor_rep oi db) cur ws_ptr)
  POST [size_t]
    PROP()
    LOCAL(temp ret_temp (Vptrofs (Ptrofs.repr (oi.(cardinality) cur))))
    SEP((db_cursor_rep oi db) cur ws_ptr).

Definition cursor_has_next_spec_vp
  (oi: OrderedIndex.index) (db: db_cursor oi): funspec :=
  WITH cur:oi.(cursor), ws_ptr:val
  PRE [ tptr (db_cursor_type oi db) ]
    PROP(oi.(cursor_has_next_props) cur)
    PARAMS(ws_ptr) GLOBALS()
    SEP((db_cursor_rep oi db) cur ws_ptr)
  POST [tint]
    PROP()
    LOCAL(temp ret_temp (Val.of_bool (oi.(cursor_has_next) cur)))
    SEP((db_cursor_rep oi db) cur ws_ptr).

Definition move_to_next_spec_vp 
  (oi: OrderedIndex.index) (db: db_cursor oi): funspec :=
  WITH cur: oi.(cursor), ws_ptr:val
  PRE [ tptr (db_cursor_type oi db)]
    PROP(oi.(move_to_next_props) cur)
    PARAMS(ws_ptr) GLOBALS()
    SEP((db_cursor_rep oi db) cur ws_ptr)
  POST [tint]
    PROP()
    LOCAL(temp ret_temp (Val.of_bool (oi.(cursor_has_next) (oi.(move_to_next) cur))))
    SEP((db_cursor_rep oi db) (oi.(move_to_next) cur) ws_ptr).

Definition move_to_first_spec_vp
  (oi: OrderedIndex.index) (db: db_cursor oi): funspec :=
  WITH gv: globals, cur: oi.(cursor), ws_ptr: val
  PRE [ tptr (db_cursor_type oi db)]
    PROP(oi.(move_to_first_props) cur)
    PARAMS(ws_ptr) GLOBALS()
    SEP(mem_mgr gv; (db_cursor_rep oi db) cur ws_ptr)
  POST [tint]
    PROP()
    LOCAL(temp ret_temp (Val.of_bool (oi.(cursor_has_next) (oi.(move_to_first) cur))))
    SEP(mem_mgr gv; (db_cursor_rep oi db) (oi.(move_to_first) cur) ws_ptr).

Definition get_record_spec_vp
  (oi: OrderedIndex.index) (db: db_cursor oi): funspec :=
  WITH cur: oi.(cursor), ws_ptr: val
  PRE [tptr (db_cursor_type oi db)]
    PROP(oi.(get_record_props) cur)
    PARAMS(ws_ptr) GLOBALS()
    SEP((db_cursor_rep oi db) cur ws_ptr)
  POST [tptr (db_value_type oi db)]
    EX newc,
    PROP()
    LOCAL(temp ret_temp (oi.(get_record) cur))
    SEP((db_cursor_rep oi db) newc ws_ptr).

(* magic wand to allow for multiple cursors
on one data structure *)
Definition create_cursor_spec_vp
  (oi: OrderedIndex.index) (db: db_cursor oi): funspec :=
  WITH r: oi.(t), gv: globals, t_ptr: val
  PRE [tptr (db_index_type oi db)]
    PROP(oi.(create_cursor_props) r t_ptr)
    PARAMS(t_ptr) GLOBALS(gv)
    SEP(mem_mgr gv; oi.(t_repr) r t_ptr)
  POST [tptr (db_cursor_type oi db)]
    EX ws_ptr,
    PROP()
    LOCAL(temp ret_temp ws_ptr)
    SEP(mem_mgr gv; oi.(t_repr) r t_ptr; 
      (oi.(t_repr) r t_ptr -* (db_cursor_rep oi db) (oi.(create_cursor) r) ws_ptr)).

End DB_Cursor.