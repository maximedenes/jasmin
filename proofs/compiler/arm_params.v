
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
Require Import arch_extra sopn psem compiler.
Require Import
  arm_decl
  arm_extra
  arm_gen
  arm_instr_decl
  arm_stack_alloc
  arm_linearization
  arm_lowering.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition arm_is_move_op (o : asm_op_t) :=
  match o with
  | BaseOp (None, MOV opts) =>
      if set_flags opts || is_conditional opts || isSome (has_shift opts)
      then None
      else Some (args_size opts)
  | _ =>
      None
  end.

Definition arm_params :
  architecture_params (asm_e := arm_extra) fresh_vars lowering_options :=
  {| is_move_op := arm_is_move_op
   ; mov_ofs := arm_mov_ofs
   ; lparams := arm_linearization_params
   ; lower_prog := arm_lower_prog
   ; fvars_correct := arm_fvars_correct
   ; assemble_prog := arm_assemble_prog
  |}.
