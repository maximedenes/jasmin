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
From CoqWord Require Import ssrZ.
Require Import sem_type strings utils wsize.
Require Export arch_decl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Axiom TODO_ARM : forall {A}, A.

(* ARM Cortex-M4 architecture

 * The ARM Cortex-M4 processor implements the ARMv7-M ISA.
 * This is a description of the base architecture (no extensions).
 *)

(* -------------------------------------------------------------------- *)
(* Registers. *)
Variant register : Type :=
| R00 | R01 | R02 | R03         (* Lower general-purpose registers. *)
| R04 | R05 | R06 | R07         (* Lower general-purpose registers. *)
| R08 | R09 | R10 | R11 | R12   (* Higher general-purpose registers. *)
| LR                            (* Subroutine link register. *)
| SP.                           (* Stack pointer. *)

Definition register_dec_eq (r0 r1: register) : {r0 = r1} + {r0 <> r1}.
  decide equality.
Defined.

Definition register_beq (r0 r1: register) : bool :=
  if register_dec_eq r0 r1 is left _
  then true
  else false.

Lemma reg_eq_axiom : Equality.axiom register_beq.
Proof.
  move=> x y.
  apply:(iffP idP);
    last move=> <-;
    rewrite /register_beq;
    by case: register_dec_eq.
Qed.

Definition reg_eqMixin := Equality.Mixin reg_eq_axiom.
Canonical reg_eqType := EqType register reg_eqMixin.

Definition registers :=
  [:: R00; R01; R02; R03; R04; R05; R06; R07; R08; R09; R10; R11; R12;
  LR; SP ].

Lemma registers_fin_axiom : Finite.axiom registers.
Proof. by case. Qed.

Definition reg_choiceMixin :=
  PcanChoiceMixin (FinIsCount.pickleK registers_fin_axiom).
Canonical reg_choiceType :=
  Eval hnf in ChoiceType register reg_choiceMixin.

Definition reg_countMixin :=
  PcanCountMixin (FinIsCount.pickleK registers_fin_axiom).
Canonical reg_countType :=
  Eval hnf in CountType register reg_countMixin.

Definition reg_finMixin :=
  FinMixin registers_fin_axiom.
Canonical reg_finType :=
  Eval hnf in FinType register reg_finMixin.

Definition string_of_register (r: register) : string :=
  match r with
  | R00 => "r0"
  | R01 => "r1"
  | R02 => "r2"
  | R03 => "r3"
  | R04 => "r4"
  | R05 => "r5"
  | R06 => "r6"
  | R07 => "r7"
  | R08 => "r8"
  | R09 => "r9"
  | R10 => "r10"
  | R11 => "r11"
  | R12 => "r12"
  | LR  => "lr"
  | SP  => "sp"
  end.

Lemma string_of_register_inj : injective string_of_register.
Proof.
  by move=> r1 r2 /eqP h; apply/eqP; case: r1 r2 h => -[]; vm_compute.
Qed.

Instance eqTC_register : eqTypeC register :=
  { ceqP := reg_eq_axiom }.

Instance finC_register : finTypeC register :=
  { cenumP := registers_fin_axiom }.

Instance reg_toS : ToString sword32 register :=
  { category      := "register"
  ; to_string     := string_of_register
  ; strings       := [seq (string_of_register x, x)
                     | x <- enum [finType of register]]
  ; inj_to_string := string_of_register_inj
  ; stringsE      := refl_equal
  }.

(* -------------------------------------------------------------------- *)
(* Extra registers. *)
Variant xregister : Type :=.

Definition xregister_dec_eq (xr0 xr1: xregister) : {xr0 = xr1} + {xr0 <> xr1}.
  by repeat decide equality.
Defined.

Definition xregister_beq (xr0 xr1: xregister) : bool :=
  if xregister_dec_eq xr0 xr1 is left _
  then true
  else false.

Lemma xreg_eq_axiom : Equality.axiom xregister_beq.
Proof.
  move=> x y.
  apply:(iffP idP);
    last move=> <-;
    rewrite /xregister_beq;
    by case: xregister_dec_eq.
Qed.

Definition xreg_eqMixin := Equality.Mixin xreg_eq_axiom.
Canonical xreg_eqType := EqType xregister xreg_eqMixin.

Definition xregisters : seq xregister := [::].

Lemma xregisters_fin_axiom : Finite.axiom xregisters.
Proof. by case. Qed.

Definition xreg_choiceMixin :=
  PcanChoiceMixin (FinIsCount.pickleK xregisters_fin_axiom).
Canonical xreg_choiceType :=
  Eval hnf in ChoiceType xregister xreg_choiceMixin.

Definition xreg_countMixin :=
  PcanCountMixin (FinIsCount.pickleK xregisters_fin_axiom).
Canonical xreg_countType :=
  Eval hnf in CountType xregister xreg_countMixin.

Definition xreg_finMixin :=
  FinMixin xregisters_fin_axiom.
Canonical xreg_finType :=
  Eval hnf in FinType xregister xreg_finMixin.

Definition string_of_xregister (r: xregister) : string :=
  match r with
  end.

Lemma string_of_xregister_inj : injective string_of_xregister.
Proof.
  by move=> r1 r2 /eqP h; apply/eqP; case: r1 r2 h => -[]; vm_compute.
Qed.

Instance eqTC_xregister : eqTypeC xregister :=
  { ceqP := xreg_eq_axiom }.

Instance finC_xregister : finTypeC xregister :=
  { cenumP := xregisters_fin_axiom }.

Instance xreg_toS : ToString sword64 xregister :=
  { category      := "xregister"
  ; to_string     := string_of_xregister
  ; strings       := [seq (string_of_xregister x, x)
                     | x <- enum [finType of xregister]]
  ; inj_to_string := string_of_xregister_inj
  ; stringsE      := refl_equal
  }.

(* -------------------------------------------------------------------- *)
(* Flags. *)
Variant rflag : Type :=
| NF    (* Negative condition flag. *)
| ZF    (* Zero confition flag. *)
| CF    (* Carry condition flag. *)
| VF.   (* Overflow condition flag. *)

Definition rflag_dec_eq (f0 f1: rflag) : {f0 = f1} + {f0 <> f1}.
  by repeat decide equality.
Defined.

Definition rflag_beq (f0 f1: rflag) : bool :=
  if rflag_dec_eq f0 f1 is left _
  then true
  else false.

Lemma rflag_eq_axiom : Equality.axiom rflag_beq.
Proof.
  move=> x y.
  apply:(iffP idP);
    last move=> <-;
    rewrite /rflag_beq;
    by case: rflag_dec_eq.
Qed.

Definition rflag_eqMixin := Equality.Mixin rflag_eq_axiom.
Canonical rflag_eqType := EqType rflag rflag_eqMixin.

Definition rflags := [:: NF; ZF; CF; VF ].

Lemma rflags_fin_axiom : Finite.axiom rflags.
Proof. by case. Qed.

Definition rflag_choiceMixin :=
  PcanChoiceMixin (FinIsCount.pickleK rflags_fin_axiom).
Canonical rflag_choiceType :=
  Eval hnf in ChoiceType rflag rflag_choiceMixin.

Definition rflag_countMixin :=
  PcanCountMixin (FinIsCount.pickleK rflags_fin_axiom).
Canonical rflag_countType :=
  Eval hnf in CountType rflag rflag_countMixin.

Definition rflag_finMixin :=
  FinMixin rflags_fin_axiom.
Canonical rflag_finType :=
  Eval hnf in FinType rflag rflag_finMixin.

Definition string_of_rflag (f : rflag) : string :=
  match f with
  | NF => "NF"
  | ZF => "ZF"
  | CF => "CF"
  | VF => "VF"
  end.

Lemma string_of_rflag_inj : injective string_of_rflag.
Proof.
  by move=> r1 r2 /eqP h; apply/eqP; case: r1 r2 h => -[]; vm_compute.
Qed.

Instance eqTC_rflag : eqTypeC rflag :=
  { ceqP := rflag_eq_axiom }.

Instance finC_rflag : finTypeC rflag :=
  { cenumP := rflags_fin_axiom }.

Instance rflag_toS : ToString sbool rflag :=
  { category      := "rflag"
  ; to_string     := string_of_rflag
  ; strings       := [seq (string_of_rflag x, x) | x <- enum [finType of rflag]]
  ; inj_to_string := string_of_rflag_inj
  ; stringsE      := refl_equal
  }.

(* -------------------------------------------------------------------- *)
(* Conditions. *)
Variant condt : Type :=
| EQ_ct    (* Equal. *)
| NE_ct    (* Not equal. *)
| CS_ct    (* Carry set. *)
| CC_ct    (* Carry clear. *)
| MI_ct    (* Minus, negative. *)
| PL_ct    (* Plus, positive or zero. *)
| VS_ct    (* Overflow. *)
| VC_ct    (* No overflow. *)
| HI_ct    (* Unsigned higher. *)
| LS_ct    (* Unsigned lower or same. *)
| GE_ct    (* Signed greater than or equal. *)
| LT_ct    (* Signed less than. *)
| GT_ct    (* Signed greater than. *)
| LE_ct    (* Signed less than or equal. *)
| AL_ct.   (* Always. *)

Definition condt_dec_eq (c0 c1: condt) : {c0 = c1} + {c0 <> c1}.
  by repeat decide equality.
Defined.

Definition condt_beq (c0 c1: condt) : bool :=
  if condt_dec_eq c0 c1 is left _
  then true
  else false.

Lemma condt_eq_axiom : Equality.axiom condt_beq.
Proof.
  move=> x y.
  apply:(iffP idP);
    last move=> <-;
    rewrite /condt_beq;
    by case: condt_dec_eq.
Qed.

Definition condt_eqMixin := Equality.Mixin condt_eq_axiom.
Canonical condt_eqType := EqType condt condt_eqMixin.

Instance eqTC_condt : eqTypeC condt :=
  { ceqP := condt_eq_axiom }.

(* -------------------------------------------------------------------- *)
(* Register shifts.
 * Some instructions can shift a register before performing an operation.
 *)
Variant shift_kind : Type :=
| SLSL          (* Logical shift left by 0 <= n < 32 bits. *)
| SLSR          (* Logical shift left by 1 <= n < 33 bits. *)
| SASR          (* Logical shift left by 1 <= n < 33 bits. *)
| SROR          (* Logical shift left by 1 <= n < 33 bits. *)
| SRXR.         (* Rotate right one bit, with extend.
                 * - bit [0] is written to shifter_carry_out.
                 * - bits [31:1] are shifted right one bit.
                 * - CF is shifted into bit [31].
                 *)

Scheme Equality for shift_kind.

Lemma shift_kind_eq_axiom : Equality.axiom shift_kind_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_shift_kind_dec_bl.
  by apply: internal_shift_kind_dec_lb.
Qed.

Definition shift_kind_eqMixin := Equality.Mixin shift_kind_eq_axiom.
Canonical shift_kind_eqType := EqType shift_kind shift_kind_eqMixin.

Instance eqTC_shift_kind : eqTypeC shift_kind :=
  { ceqP := shift_kind_eq_axiom }.

Definition shift_kinds :=
  [:: SLSL; SLSR; SASR; SROR; SRXR ].

Lemma shift_kinds_fin_axiom : Finite.axiom shift_kinds.
Proof. by case. Qed.

Definition shift_kind_choiceMixin :=
  PcanChoiceMixin (FinIsCount.pickleK shift_kinds_fin_axiom).
Canonical shift_kind_choiceType :=
  Eval hnf in ChoiceType shift_kind shift_kind_choiceMixin.

Definition shift_kind_countMixin :=
  PcanCountMixin (FinIsCount.pickleK shift_kinds_fin_axiom).
Canonical shift_kind_countType :=
  Eval hnf in CountType shift_kind shift_kind_countMixin.

Definition shift_kind_finMixin :=
  FinMixin shift_kinds_fin_axiom.
Canonical shift_kind_finType :=
  Eval hnf in FinType shift_kind shift_kind_finMixin.

Instance finC_shift_kind : finTypeC shift_kind :=
  { cenumP := shift_kinds_fin_axiom }.

Definition string_of_shift_kind (sk : shift_kind) : string :=
  match sk with
  | SLSL => "LSL"
  | SLSR => "LSR"
  | SASR => "ASR"
  | SROR => "ROR"
  | SRXR => "RXR"
  end.

Lemma string_of_shift_kind_inj : injective string_of_shift_kind.
Proof.
  by move=> r1 r2 /eqP h; apply/eqP; case: r1 r2 h => -[]; vm_compute.
Qed.

Instance shift_kind_toS : ToString sint shift_kind :=
  { category      := "shift"
  ; to_string     := string_of_shift_kind
  ; strings       := [seq (string_of_shift_kind x, x)
                     | x <- enum [finType of shift_kind]]
  ; inj_to_string := string_of_shift_kind_inj
  ; stringsE      := refl_equal
  }.

Definition check_shift_amount (sk: shift_kind) (z: Z) : exec unit :=
  let b := match sk with
           | SLSL => (0 <=? z)%Z && (z <? 32)%Z
           | SLSR => (1 <=? z)%Z && (z <? 33)%Z
           | SASR => (1 <=? z)%Z && (z <? 33)%Z
           | SROR => (1 <=? z)%Z && (z <? 33)%Z
           | SRXR => (z == 1)%Z
           end
  in assert b ErrType.

Definition shift_op (sk: shift_kind) :
  forall (sz: wsize), word sz -> Z -> word sz :=
  match sk with
  | SLSL => wshl
  | SLSR => wshr
  | SASR => wsar
  | SROR => wror
  | SRXR => TODO_ARM
  end.

Definition shift_opZ (sk: shift_kind) (z: Z) (n: Z) : Z :=
  match sk with
  | SLSL => Z.shiftl z n
  | SLSR => Z.shiftr z n
  | SASR => Z.shiftr z n
  | SROR => TODO_ARM
  | SRXR => TODO_ARM
  end.

(* -------------------------------------------------------------------- *)

Lemma arm_reg_size_neq_xreg_size : U32 != U64.
Proof. done. Qed.

(* -------------------------------------------------------------------- *)

Definition arm_callee_saved : seq register := [::].

(* -------------------------------------------------------------------- *)
(* Architecture declaration. *)
Instance arm_decl : arch_decl register xregister rflag condt :=
  { reg_size := U32
  ; xreg_size := U64
  ; cond_eqC := _
  ; toS_r := reg_toS
  ; toS_x := xreg_toS
  ; toS_f := rflag_toS
  ; reg_size_neq_xreg_size := arm_reg_size_neq_xreg_size
  ; callee_saved := arm_callee_saved
  ; ad_rsp := SP
  }.
