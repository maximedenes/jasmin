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
From CoqWord Require Import ssrZ.
Require Import compiler_util expr.

Section LOWERING.

Context
  (asm_op lowering_options fresh_vars : Type)
  (eft : eqType)
  (pT : progT eft)
  (asmop : asmOp asm_op)
  (options : lowering_options)
  (warning : instr_info -> warning_msg -> instr_info)
  (fv : fresh_vars)
  (is_var_in_memory : var_i -> bool)
  (lower_i0 :
    lowering_options
    -> (instr_info -> warning_msg -> instr_info)
    -> fresh_vars
    -> (var_i -> bool)
    -> instr
    -> cmd).

Notation lower_i :=
  (lower_i0 options warning fv is_var_in_memory).

Definition lower_cmd  (c : cmd) : cmd :=
  conc_map lower_i c.

Definition lower_fd (fd : fundef) : fundef :=
  {|
    f_info := f_info fd;
    f_tyin := f_tyin fd;
    f_params := f_params fd;
    f_body := lower_cmd (f_body fd);
    f_tyout := f_tyout fd;
    f_res := f_res fd;
    f_extra := f_extra fd;
  |}.

Definition lower_prog (p : prog) :=
  map_prog lower_fd p.

End LOWERING.
