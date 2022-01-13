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


(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import utils.
Require Export arch_sem.
Require Import arch_decl.
Require Import arm_decl arm_instr_decl.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition eval_cond (get: rflag -> result error bool) (c: condt) :
  result error bool :=
  match c with
  | EQ_ct => get ZF
  | NE_ct => Let zf := get ZF in ok (~~ zf)
  | CS_ct => get CF
  | CC_ct => Let cf := get CF in ok (~~ cf)
  | MI_ct => get NF
  | PL_ct => Let nf := get NF in ok (~~ nf)
  | VS_ct => get VF
  | VC_ct => Let vf := get VF in ok (~~ vf)
  | HI_ct => Let cf := get CF in
             Let zf := get ZF in
             ok (cf && ~~ zf)
  | LS_ct => Let cf := get CF in
             Let zf := get ZF in
             ok (~~ cf && zf)
  | GE_ct => Let nf := get NF in
             Let vf := get VF in
             ok (nf == vf)
  | LT_ct => Let nf := get NF in
             Let vf := get VF in
             ok (nf != vf)
  | GT_ct => Let zf := get ZF in
             Let nf := get NF in
             Let vf := get VF in
             ok (~~ zf && nf == vf)
  | LE_ct => Let zf := get ZF in
             Let nf := get NF in
             Let vf := get VF in
             ok (zf || nf != vf)
  | AL_ct => ok true
  end.

Instance arm : asm register xregister rflag condt arm_op :=
  { eval_cond := eval_cond }.

Definition arm_mem := @asmmem _ _ _ _ _ arm.
Definition arm_prog := @asm_prog register _ _ _ _ _ arm_op_decl.
Definition arm_state := @asm_state _ _ _ _ _ arm.
Definition armsem := @asmsem _ _ _ _ _ arm.
