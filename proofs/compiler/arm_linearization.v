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
Require Import expr linearization.
Require Import arm_decl arm_instr_decl arm_extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* Linear parameters specific to ARM M4. *)
(* Read the definition in linearization.v for more information. *)

Definition opts :=
  {| args_size      := reg_size
  ;  set_flags      := false
  ;  is_conditional := false
  ;  has_shift      := None
  |}.

Definition arm_allocate_stack_frame (rspi : var_i) (sz : Z) :=
  let rspg := Gvar rspi Slocal in
  ([:: Lvar rspi ], Oarm (ADDI opts), [:: Pvar rspg; Pconst sz ]).

Definition arm_free_stack_frame (rspi : var_i) (sz : Z) :=
  let rspg := Gvar rspi Slocal in
  ([:: Lvar rspi ], Oarm (ADDI opts), [:: Pvar rspg; Pconst (-sz) ]).

Definition arm_ensure_rsp_alignment (rspi : var_i) (al : wsize) :=
  let p0 := Pvar (Gvar rspi Slocal) in
  let p1 := Pconst (- wsize_size al) in
  ([:: Lvar rspi ], Oarm (ANDI opts), [:: p0; p1 ]).

Definition arm_lassign (x : lval) (ws : wsize) (e : pexpr) :=
  let opts :=
    {| args_size      := ws
    ;  set_flags      := false
    ;  is_conditional := false
    ;  has_shift      := None
    |} in
  ([:: x ], Oarm (MOV opts), [:: e ]).

Definition arm_linearization_params : linearization_params :=
  {|
    lp_tmp                  := "r0"%string;
    lp_allocate_stack_frame := arm_allocate_stack_frame;
    lp_free_stack_frame     := arm_free_stack_frame;
    lp_ensure_rsp_alignment := arm_ensure_rsp_alignment;
    lp_lassign              := arm_lassign;
  |}.
