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
Require Import
  arch_decl
  asm_gen
  compiler_util
  expr
  linear
  utils.
Require Import
  arm_decl
  arm_extra
  arm_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition assemble_cond ii (e : pexpr) : cexec condt :=
  match e with
  | Pvar v =>
      Let r := of_var_e ii (gv v) in
      match r with
      | NF => ok MI_ct
      | ZF => ok EQ_ct
      | CF => ok CS_ct
      | VF => ok VS_ct
      end

  | _ => Error (E.berror ii e "Invalid condition.")
  end.

Definition assemble_i (rip : var) (i : linstr) : cexec asm_i :=
  let '{| li_ii := ii; li_i := ir; |} := i in
  match ir with
  | Lopn lvs op es =>
      Let: (op', args) := assemble_sopn assemble_cond rip ii op lvs es in
      ok (AsmOp op' args)

  | Lalign =>
      ok ALIGN

  | Llabel lbl =>
      ok (LABEL lbl)

  | Lgoto lbl =>
      ok (JMP lbl)

  | Ligoto e =>
      Let arg := assemble_word AK_mem rip ii Uptr e in
      ok (JMPI arg)

  | LstoreLabel x lbl =>
      TODO_ARM

  | Lcond cond l =>
      Let cond := assemble_cond ii cond in
      ok (Jcc l cond)
  end.

Definition assemble_c (rip : var) (lc : lcmd) : cexec (seq asm_i) :=
  mapM (assemble_i rip) lc.

Definition assemble_fd (rsp rip : var) (fd : lfundef) : cexec asm_fundef :=
  Let body := assemble_c rip (lfd_body fd) in
  ok {| asm_fd_align := lfd_align fd
     ;  asm_fd_arg := TODO_ARM
     ;  asm_fd_body := body
     ;  asm_fd_res := TODO_ARM
     ;  asm_fd_export := lfd_export fd
     |}.

Definition arm_assemble_prog (p : lprog) : cexec asm_prog :=
  let rip := {| vname := (lp_rip p); vtype := sword Uptr; |} in
  let rsp := {| vname := (lp_rsp p); vtype := sword Uptr; |} in
  Let fds := map_cfprog_gen lfd_info (assemble_fd rsp rip) (lp_funcs p) in
  ok {| asm_globs := lp_globs p; asm_funcs := fds; |}.
