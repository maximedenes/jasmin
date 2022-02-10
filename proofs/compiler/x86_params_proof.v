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
Require Import linearization_proof sopn psem compiler compiler_proof.
Require Import
  x86_decl
  x86_instr_decl
  x86_extra
  x86_linear_sem
  x86_linearization_proof
  x86_stack_alloc_proof.
Require Import x86_params.
Require x86_gen_proof.
Require lowering_proof.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma x86_is_move_opP : forall op vx v,
  is_move_op x86_params op ->
  exec_sopn (Oasm op) [:: vx] = ok v ->
  List.Forall2 value_uincl v [:: vx].
Proof.
  by case=> // -[] []// []//= ws vx v _;
    rewrite /exec_sopn /=;
    t_xrbindP=> w ? /to_wordI [ws' [wx [hle -> ->]]];
    rewrite /sopn_sem /=;
    match goal with
    | |- ?f (zero_extend _ _) = _ -> _ => rewrite /f
    end;
    t_xrbindP=> _ _ <- <-;
    (constructor; last by constructor);
    apply value_uincl_zero_ext.
Qed.

Lemma exec_sopn_x86_mov_op (w : word Uptr) :
  let op :=
    Oasm
      (asm_op := x86_extra.x86_extended_op)
      (BaseOp (None, x86_instr_decl.MOV Uptr))
  in
  exec_sopn op [:: Vword w ] = ok [:: Vword w ].
Proof.
  by rewrite /exec_sopn /= zero_extend_u.
Qed.

Lemma ok_x86_lp_tmp :
  exists r : reg_t, of_string (lp_tmp (lparams x86_params)) = Some r.
Proof.
  exists RAX.
  rewrite /=.
  change "RAX"%string with (to_string RAX).
  exact: to_stringK.
Qed.


Definition x86_hyps : architecture_hyps x86_params :=
  {| is_move_opP := x86_is_move_opP
   ; lower_callP := lowering_proof.lower_callP
   ; mov_ofsP := x86_mov_ofsP
   ; mov_op := x86_mov_op
   ; hlparams := h_x86_linearization_params
   ; exec_sopn_mov_op := exec_sopn_x86_mov_op
   ; assemble_cond := x86_gen.assemble_cond
   ; eval_assemble_cond := x86_gen_proof.eval_assemble_cond
   ; assemble_extra_op := x86_gen_proof.assemble_extra_op
   ; assemble_progP := x86_gen_proof.assemble_progP
   ; ok_lp_tmp := ok_x86_lp_tmp
  |}.
