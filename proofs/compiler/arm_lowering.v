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
Require Import arm_extra arm_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ARM_LOWERING.

Context
  {eft : eqType}
  {pT : progT eft}.

Definition fresh_vars := unit.
Definition lowering_options := unit.

Definition arm_fvars_correct
  (_ : fresh_vars) {eft : eqType} {_ : progT eft} (_ : fun_decls) : bool :=
  true.

Definition lower_condition
  (ii : instr_info)
  (cond : pexpr) :
  seq instr_r * pexpr :=
  ([::], cond).

Definition lower_cmd (lower_i : instr -> cmd) (c : cmd) : cmd :=
  List.fold_right (fun i c' => lower_i i ++ c') [::] c.

Fixpoint lower_i (i : instr) : cmd :=
  let '(MkI ii ir) := i in
  match ir with
  | Cassgn _ _ _ _ =>
      [:: MkI ii ir ]
  | Copn _ _ _ _ =>
      [:: MkI ii ir ]
  | Cif e c1 c2  =>
      let '(pre, e') := lower_condition xH e in
      let c1' := lower_cmd lower_i c1 in
      let c2' := lower_cmd lower_i c2 in
      map (MkI ii) (pre ++ [:: Cif e' c1' c2' ])
  | Cfor v r c =>
      let c' := lower_cmd lower_i c in
      [:: MkI ii (Cfor v r c') ]
  | Cwhile a c0 e c1 =>
     let '(pre, e') := lower_condition xH e in
     let c0' := lower_cmd lower_i c0 in
     let c1' := lower_cmd lower_i c1 in
     [:: MkI ii (Cwhile a (c0' ++ map (MkI xH) pre) e' c1') ]
  | Ccall _ _ _ _ =>
      [:: MkI ii ir ]
  end.

Definition lower_fd (fd : fundef) : fundef :=
  {| f_info := f_info fd
   ; f_tyin := f_tyin fd
   ; f_params := f_params fd
   ; f_body := lower_cmd lower_i (f_body fd)
   ; f_tyout := f_tyout fd
   ; f_res := f_res fd
   ; f_extra := f_extra fd
  |}.

End ARM_LOWERING.

Definition arm_lower_prog
  (_ : lowering_options)
  (_ : instr_info -> warning_msg -> instr_info)
  (_ : fresh_vars)
  {eft : eqType}
  {pT : progT eft}
  (_ : var_i -> bool)
  (p : prog) :=
  map_prog lower_fd p.
