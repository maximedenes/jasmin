(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

From mathcomp Require Import all_ssreflect all_algebra.
Require Import
  arch_extra
  expr
  psem
  psem_facts
  sem_one_varmap
  linear
  linear_sem
  linearization_proof.
Require Import
  arm_decl
  arm_instr_decl
  arm_extra
  arm_linearization.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Definition opts :=
  {| args_size      := reg_size
  ;  set_flags      := false
  ;  is_conditional := false
  ;  has_shift      := None
  |}.
Definition arm_mov_op := MOV opts.
Definition arm_mov_eop := BaseOp (None, arm_mov_op).

Lemma spec_arm_mov_op :
  forall (lp : lprog) (s : estate) fn pc x lbl ptr ii,
    vtype x == sregsz ->
    label.encode_label (label_in_lprog lp) (fn, lbl) = Some ptr ->
    let i := LstoreLabel {| v_var := x; v_info := 1%positive; |} lbl in
    let vm := evm s in
    let s' := with_vm s (vm.[x <- pof_val (vtype x) (Vword ptr)])%vmap in
    eval_instr lp arm_mov_eop {| li_ii := ii; li_i := i |} (of_estate s fn pc)
    = ok (of_estate s' fn pc.+1).
Proof.
  move=> lp s fn pc x lbl ptr ii /eqP hty hlabel.
  rewrite /eval_instr /= hlabel /sem_sopn /=.
  rewrite /write_var /= /set_var.
  case: x hty => _ xn /= -> /=.
  by rewrite zero_extend_u wrepr_unsigned.
Qed.

Lemma spec_arm_allocate_stack_frame :
  forall (lp : lprog) (s : estate) sp_rsp ii fn pc ts sz,
    let rsp := vid sp_rsp in
    let vm := evm s in
    let '(lvs, op, ps) := arm_allocate_stack_frame (VarI rsp xH) sz in
    let i := MkLI ii (Lopn lvs op ps) in
    let ts' := pword_of_word (ts + wrepr Uptr sz) in
    let s' := with_vm s (vm.[rsp <- ok ts'])%vmap in
    (vm.[rsp])%vmap = ok (pword_of_word ts)
    -> eval_instr lp arm_mov_eop i (of_estate s fn pc)
       = ok (of_estate s' fn pc.+1).
Proof.
  move=> lp s sp_rsp ii fn pc ts sz.
  move=> /= Hvm.
  rewrite /eval_instr /= /sem_sopn /=.
  rewrite /get_gvar /get_var /on_vu /=.
  rewrite Hvm /=.
  rewrite pword_of_wordE.
  by rewrite zero_extend_u.
Qed.

Lemma spec_arm_free_stack_frame :
  forall (lp: lprog) (s: estate) sp_rsp ii fn pc ts sz,
    let rsp := vid sp_rsp in
    let vm := evm s in
    let '(lvs, op, ps) := arm_free_stack_frame (VarI rsp xH) sz in
    let i := MkLI ii (Lopn lvs op ps) in
    let ts' := pword_of_word (ts - wrepr Uptr sz) in
    let s' := with_vm s (vm.[rsp <- ok ts'])%vmap in
    (vm.[rsp])%vmap = ok (pword_of_word ts)
    -> eval_instr lp arm_mov_eop i (of_estate s fn pc)
       = ok (of_estate s' fn pc.+1).
Proof.
  move=> lp s sp_rsp ii fn pc ts sz.
  move=> /= Hvm.
  rewrite /eval_instr /= /sem_sopn /=.
  rewrite /get_gvar /get_var /on_vu /=.
  rewrite Hvm /=.
  rewrite pword_of_wordE.
  rewrite zero_extend_u.
  by rewrite wrepr_opp.
Qed.

Definition spec_arm_ensure_rsp_alignment :
  forall (lp: lprog) (s1: estate) rsp_id ws ts' ii fn pc,
    let vrsp := Var (sword Uptr) rsp_id in
    let vrspi := VarI vrsp xH in
    let rsp' := align_word ws ts' in
    get_var (evm s1) vrsp = ok (Vword ts')
    -> wf_vm (evm s1)
    -> let '(lvs, op, ps) := arm_ensure_rsp_alignment vrspi ws in
       let i := MkLI ii (Lopn lvs op ps) in
       let vm1' := (evm s1).[vrsp <- ok (pword_of_word rsp')]%vmap in
       exists vm',
         [/\ eval_instr lp arm_mov_eop i (of_estate s1 fn pc)
             = ok (of_estate (with_vm s1 vm') fn pc.+1)
         ,   vm' = vm1' [\sv_of_flags rflags]
         ,   forall x,
               Sv.In x (sv_of_flags rflags)
               -> ~ is_ok (vm'.[x]%vmap)
               -> (evm s1).[x]%vmap = vm'.[x]%vmap
         &   wf_vm vm'
         ].
Proof.
  move=> lp s1 rsp_id ws ts' sp_rsp ii fn.
  move=> vrsp vrspi al /= Hvrsp Hwm1.
  rewrite /eval_instr /= /sem_sopn /= /get_gvar /=.
  rewrite Hvrsp /=.
  rewrite zero_extend_u.
  rewrite pword_of_wordE.
  rewrite /with_vm /=.
  eexists.
  split.
  - reflexivity.
  - move=> x hin.
    rewrite !(@Fv.setP _ _ vrsp).
    case: (vrsp =P x).
    + move=> ?. by subst x.
    + done.
  - move=> x /sv_of_flagsP /mapP [f _ ->].
    by case f;
      repeat (rewrite Fv.setP_eq || rewrite Fv.setP_neq //).
  apply wf_vm_set.
  exact Hwm1.
Qed.

Lemma spec_arm_lassign :
  forall (lp : lprog) (s1 s2 : estate) x e ws ws'
         (w : word ws) (w' : word ws') ii fn pc,
    let '(lvs, op, ps) := arm_lassign x ws e in
    let i := MkLI ii (Lopn lvs op ps) in
    sem_pexpr [::] s1 e = ok (Vword w')
    -> truncate_word ws w' = ok w
    -> write_lval [::] x (Vword w) s1 = ok s2
    -> eval_instr lp arm_mov_eop i (of_estate s1 fn pc)
       = ok (of_estate s2 fn pc.+1).
Proof.
  move=> lp s1 s2 x e ws ws' w w' ii fn pc /=.
  move=> Hsem_pexpr Htruncate_word Hwrite_lval.
  rewrite /eval_instr /= /sem_sopn /=.
  rewrite to_estate_of_estate.
  rewrite Hsem_pexpr /=.
  rewrite /exec_sopn /=.
  rewrite Htruncate_word /=.
  case: ws w Htruncate_word Hwrite_lval =>
    /= ? _ Hwrite_lval;
    try by rewrite Hwrite_lval /=.
  - by apply TODO_ARM. (* x = (u64)e *)
  - by apply TODO_ARM. (* x = (u128)e *)
  - by apply TODO_ARM. (* x = (u256)e *)
Qed.

Definition h_arm_linearization_params :
  h_linearization_params arm_mov_op arm_linearization_params.
  split.
  - exact: spec_arm_mov_op.
  - exact: spec_arm_allocate_stack_frame.
  - exact: spec_arm_free_stack_frame.
  - exact: spec_arm_ensure_rsp_alignment.
  - exact: spec_arm_lassign.
Defined.
