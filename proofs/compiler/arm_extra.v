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
Require Import compiler_util expr sopn utils.
Require Import arch_decl arch_extra.
Require Import arm_decl arm_instr_decl arm_sem.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Variant arm_extra_op : Type :=.

Scheme Equality for arm_extra_op.

Lemma arm_extra_op_eq_axiom : Equality.axiom arm_extra_op_beq.
Proof.
  move=> x y; apply:(iffP idP).
  + by apply: internal_arm_extra_op_dec_bl.
  by apply: internal_arm_extra_op_dec_lb.
Qed.

Definition arm_extra_op_eqMixin :=
  Equality.Mixin arm_extra_op_eq_axiom.
Canonical arm_extra_op_eqType :=
  Eval hnf in EqType arm_extra_op arm_extra_op_eqMixin.

Instance eqTC_arm_extra_op : eqTypeC arm_extra_op :=
  { ceqP := arm_extra_op_eq_axiom }.

(* Extra instructions descriptions. *)
Definition get_instr_desc (o: arm_extra_op) : instruction_desc :=
  match o with
  end.

(* Without priority 1, this instance is selected when looking for an [asmOp],
 * meaning that extra ops are the only possible ops. With that priority,
 * [arch_extra.asm_opI] is selected first and we have both base and extra ops.
*)
Instance arm_extra_op_decl : asmOp arm_extra_op | 1 :=
  { asm_op_instr := get_instr_desc }.

Definition assemble_extra
           (ii: instr_info)
           (o: arm_extra_op)
           (outx: lvals)
           (inx: pexprs)
           : cexec (asm_op_msb_t * lvals * pexprs) :=
  match o with
  end.

Instance arm_extra :
  asm_extra register xregister rflag condt arm_op arm_extra_op :=
  { to_asm := assemble_extra }.

(* This concise name is convenient in OCaml code. *)
Definition arm_extended_op :=
  @extended_op _ _ _ _ _ _ arm_extra.

Definition Oarm o : @sopn arm_extended_op _ := Oasm (BaseOp (None, o)).
