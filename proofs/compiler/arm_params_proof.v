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
Require Import arch_extra sopn psem compiler compiler_proof utils.
Require Import
  arm_decl
  arm_instr_decl
  arm_extra
  arm_linearization_proof
  arm_params
  arm_stack_alloc_proof.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma arm_move_op op sz :
  is_move_op arm_params op = Some sz
  -> let
       opts := {| args_size := sz
               ;  set_flags := false
               ;  is_conditional := false
               ;  has_shift := None
               |}
     in
     op = BaseOp (None, MOV opts).
Proof.
  case: op => [[[|]][]|] // opts.
  by case: opts => ? [] [] [] //= [<-].
Qed.

Lemma arm_is_move_opP : forall op sz v vs,
  is_move_op arm_params op = Some sz ->
  exec_sopn (Oasm op) [:: v ] = ok vs ->
  List.Forall2 value_uincl vs [:: v ].
Proof.
  move=> op sz v vs H.
  rewrite (arm_move_op H).
  rewrite /exec_sopn /=.
  t_xrbindP=> w ? Hv.
  elim: (to_wordI Hv) => sz' [w' [le_sz_sz' -> ->]].
  rewrite /sopn_sem /=.
  rewrite /drop_semi_nzcv /arm_MOV_semi /=.
  rewrite /check_size_8_32.
  case: (sz <= U32)%CMP => //=.
  move=> [<-] <-.
  constructor; last done.
  exact: (value_uincl_zero_ext w' le_sz_sz').
Qed.

Definition arm_hyps : architecture_hyps arm_params :=
  {| is_move_opP := arm_is_move_opP
   ; lower_callP := TODO_ARM
   ; mov_ofsP := arm_mov_ofsP
   ; mov_op := arm_mov_op
   ; hlparams := h_arm_linearization_params
  |}.
