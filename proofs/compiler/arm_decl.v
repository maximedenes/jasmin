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
Require oseq.
Require Import ZArith
utils
strings wsize
memory_model
(* word *)
global
oseq
Utf8
Relation_Operators
sem_type
arch_decl
HexString.

(* Import Memory. *)

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Variant register : Type :=
  | XZR | SP | PC | X of 'I_31.

(* -------------------------------------------------------------------- *)
Variant simd_register : Type :=
  | V of 'I_32.

(* -------------------------------------------------------------------- *)
Variant rflag : Type := FN | FZ | FC | FV .


(* -------------------------------------------------------------------- *)
(*TODO: page 75 document abregé ARM*)
Variant condt : Type :=
| EQ (*Equal to*)
| NE (*Not equal to*)
| CS (*Greater than, equal to, or unordered*)
| HS (*Identical to CS*)
| CC (*Less than*)
| LO (*Identical to CC*)
| MI (*Less than*)
| PL (*Greater than, equal to, or unordered*)
| VS (*Unordered*)
| VC (*Not unordered*)
| HI (*Greater than unordered*)
| LS (*Less than or equal to*)
| GE (*Greater than or equal to*)
| LT (*Less than or unordered*)
| GT (*Greater than*)
| LE (*Less than, equal to or unordered*)
| AL (*Default, always executed*)
| NV (*Always executed*)
.

(* -------------------------------------------------------------------- *)


Definition register_beq (r1 r2 : register) :=
  match r1, r2 with
  | XZR, XZR | SP, SP | PC, PC => true
  | X i, X j => i == j
  | _, _ => false
  end.

(*
Lemma register_eq_dec (r1 r2 : register) :
  {r1 = r2} + {r1 <> r2}.
Proof.
  move: r1 r2 => [|||i] [|||j].
  1,6,11: by left.
  1-12: by right.
  case Heq: (i == j).
  + left. auto.
Qed.
*)

Lemma reg_eq_axiom : Equality.axiom register_beq.
Proof.
  move=> [|||[mi i]] [|||[mj j]] /=; apply:(iffP idP) => //.
  + by move/eqP => ->.
  move => [eqm]; apply/eqP.
Admitted.

Definition reg_eqMixin := Equality.Mixin reg_eq_axiom.
Canonical reg_eqType := EqType register reg_eqMixin.

(* -------------------------------------------------------------------- *)

Definition simd_register_beq (r1 r2 : simd_register) :=
  match r1, r2 with
  | V i, V j => i == j
  end.

Lemma xreg_eq_axiom : Equality.axiom simd_register_beq.
Proof.
   move=> [[mi i]] [[mj j]] /=; apply:(iffP idP).
  + by move/eqP => ->.
  move => [eqm]; apply/eqP.
Admitted.

Definition xreg_eqMixin := Equality.Mixin xreg_eq_axiom.
Canonical xreg_eqType := EqType _ xreg_eqMixin.

(* -------------------------------------------------------------------- *)
Scheme Equality for rflag.

Lemma rflag_eq_axiom : Equality.axiom rflag_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_rflag_dec_bl.
  by apply: internal_rflag_dec_lb.
Qed.

Definition rflag_eqMixin := Equality.Mixin rflag_eq_axiom.
Canonical rflag_eqType := EqType rflag rflag_eqMixin.

(* -------------------------------------------------------------------- *)
(*Scheme Equality for scale.

Lemma scale_eq_axiom : Equality.axiom scale_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_scale_dec_bl.
  by apply: internal_scale_dec_lb.
Qed.

Definition scale_eqMixin := Equality.Mixin scale_eq_axiom.
Canonical scale_eqType := EqType scale scale_eqMixin.
*)
(* -------------------------------------------------------------------- *)
Scheme Equality for condt.

Lemma condt_eq_axiom : Equality.axiom condt_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_condt_dec_bl.
  by apply: internal_condt_dec_lb.
Qed.

Definition condt_eqMixin := Equality.Mixin condt_eq_axiom.
Canonical condt_eqType := EqType condt condt_eqMixin.

(* -------------------------------------------------------------------- *)

Definition registers :=
  (*Eval compute in*) [:: XZR; SP; PC] ++ [seq X i | i in 'I_31].

(*Maybe do something general about 'I_n.*)
Lemma registers_fin_axiom : Finite.axiom registers.
Proof.
  case => [|||i] /=.
  1-3: by rewrite count_map; elim: (enum 'I_31).
  rewrite count_uniq_mem; last first.
  + rewrite map_inj_uniq; last by move => ? ? [].
    by apply enum_uniq.
  rewrite mem_map; last by move => ? ? [].
  rewrite -(@mem_map _ _ val val_inj) val_enum_ord.
  move: i; apply ordinal_ind => i lti.
  by rewrite mem_iota /= !add0n lti.
Qed.

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

(* -------------------------------------------------------------------- *)
Definition simd_registers :=
  [seq V i | i in 'I_32].

Lemma simd_registers_fin_axiom : Finite.axiom simd_registers.
Proof.
  case => [i] /=.
  rewrite count_uniq_mem; last first.
  + rewrite map_inj_uniq; last by move => ? ? [].
    by apply enum_uniq.
  rewrite mem_map; last by move => ? ? [].
  rewrite -(@mem_map _ _ val val_inj) val_enum_ord.
  move: i; apply ordinal_ind => i lti.
  by rewrite mem_iota /= !add0n lti.
Qed.

Definition xreg_choiceMixin :=
  PcanChoiceMixin (FinIsCount.pickleK simd_registers_fin_axiom).
Canonical xreg_choiceType :=
  Eval hnf in ChoiceType simd_register xreg_choiceMixin.

Definition xreg_countMixin :=
  PcanCountMixin (FinIsCount.pickleK simd_registers_fin_axiom).
Canonical xreg_countType :=
  Eval hnf in CountType simd_register xreg_countMixin.

Definition xreg_finMixin :=
  FinMixin simd_registers_fin_axiom.
Canonical xreg_finType :=
  Eval hnf in FinType simd_register xreg_finMixin.

(* -------------------------------------------------------------------- *)
Definition rflags := [:: FN; FZ; FC; FV].

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

(* -------------------------------------------------------------------- *)
Definition arm_string_of_register r :=
  match r with
  | XZR => "XZR"
  | SP => "SP"
  | PC => "PC"
  | X i => "X " ++ HexString.of_nat i
  end%string.

Lemma cat_string_eq (a b c : string) : (append a b == append a c) -> (b == c).
Proof.
Admitted.

Lemma arm_string_of_register_inj : injective arm_string_of_register.
Proof. 
  move=> r1 r2 /eqP h; apply/eqP; case: r1 r2 h => [|||i] [|||j] //.
  rewrite /arm_string_of_register.
  move/cat_string_eq/eqP => eq_of_nat.
  apply/eqP; move: (to_nat_of_nat j).
  rewrite -eq_of_nat to_nat_of_nat.
  (*Unset Printing Notations.*)
  (*by move => ->.
Qed.
*)
Admitted.

Lemma finC_register : finTypeC register.
Proof.
Admitted.

Instance arm_reg_toS : ToString sword64 [finType of register] := 
  {| category      := "register"
   ; _finC         := finC_register
   ; to_string     := arm_string_of_register
   ; strings       := [seq (arm_string_of_register x, x) | x <- enum cfinT_finType]
   ; inj_to_string := arm_string_of_register_inj
   ; stringsE      := refl_equal
  |}.

(* -------------------------------------------------------------------- *)
Definition arm_string_of_simd_register r : string :=
  match r with
  | V i => "V " ++ HexString.of_nat i
  end.

Lemma arm_string_of_simd_register_inj : injective arm_string_of_simd_register.
Proof. 
  move=> r1 r2 /eqP h; apply/eqP; case: r1 r2 h => [i] [j].
  rewrite /arm_string_of_register.
  move/cat_string_eq/eqP => eq_of_nat.
  apply/eqP; move: (to_nat_of_nat j).
  rewrite -eq_of_nat to_nat_of_nat.
  (*by move => ->.
Qed.*)
Admitted.

Lemma finC_simd_register : finTypeC simd_register.
Proof.
Admitted.

Instance arm_xreg_toS : ToString sword256 [finType of simd_register] := 
  {| category      := "ymm_register"
   ; _finC         := finC_simd_register
   ; to_string     := arm_string_of_simd_register
   ; strings       := [seq (arm_string_of_simd_register x, x) | x <- enum cfinT_finType]
   ; inj_to_string := arm_string_of_simd_register_inj
   ; stringsE      := refl_equal
  |}.

(* -------------------------------------------------------------------- *)
Definition arm_string_of_rflag (rf : rflag) : string :=
  match rf with
  | FN => "N"
  | FZ => "Z"
  | FC => "C"
  | FV => "V"
  end%string.

Lemma arm_string_of_rflag_inj : injective arm_string_of_rflag.
Proof. 
  by move=> r1 r2 /eqP h; apply/eqP; case: r1 r2 h => -[].
Qed.

Lemma finC_rflag : finTypeC rflag.
Proof.
Admitted.

Instance arm_rflag_toS : ToString sbool [finType of rflag] := 
  {| category      := "rflag"
   ; _finC         := finC_rflag
   ; to_string     := arm_string_of_rflag
   ; strings       := [seq (arm_string_of_rflag x, x) | x <- enum cfinT_finType]
   ; inj_to_string := arm_string_of_rflag_inj
   ; stringsE      := refl_equal
  |}.

(* -------------------------------------------------------------------- *)

Lemma cond_eqC_arm : eqTypeC [eqType of condt].
Proof.
Admitted.

Instance arm_decl : (arch_decl [finType of register] [finType of simd_register] [finType of rflag] [eqType of condt]) :=
  {| xreg_size := U256
   ; cond_eqC  := cond_eqC_arm
   ; toS_r     := arm_reg_toS
   ; toS_x     := arm_xreg_toS
   ; toS_f     := arm_rflag_toS |}.



