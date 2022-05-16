(* ** Machine word *)

(* ** Imports and settings *)

From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ word.
Require Import ssrring.
Require Zquot.
Require Import Psatz ZArith utils.
Require Export wsize.
Import Utf8.
Import ssrZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.POrderTheory Order.TotalTheory.
Import ssrnat.

Local Open Scope Z_scope.

(* -------------------------------------------------------------- *)
Ltac elim_div :=
   unfold Z.div, Zmod;
     match goal with
       |  H : context[ Z.div_eucl ?X ?Y ] |-  _ =>
          generalize (Z_div_mod_full X Y) ; case: (Z.div_eucl X Y)
       |  |-  context[ Z.div_eucl ?X ?Y ] =>
          generalize (Z_div_mod_full X Y) ; case: (Z.div_eucl X Y)
     end; unfold Remainder.

Lemma mod_pq_mod_q x p q :
  0 < p → 0 < q →
  (x mod (p * q)) mod q = x mod q.
Proof.
move => hzp hzq.
have hq : q ≠ 0 by nia.
have hpq : p * q ≠ 0 by nia.
elim_div => z z0 /(_ hq); elim_div => z1 z2 /(_ hpq) => [] [?] hr1 [?] hr2; subst.
elim_div => z2 z3 /(_ hq) [heq hr3].
intuition (try nia).
suff : p * z1 + z = z2; nia.
Qed.

Lemma modulus_m a b :
  a ≤ b →
  ∃ n, modulus b.+1 = modulus n * modulus a.+1.
Proof.
move => hle.
exists (b - a)%nat; rewrite /modulus !two_power_nat_equiv -Z.pow_add_r; try lia.
rewrite (Nat2Z.inj_sub _ _ hle); f_equal; lia.
Qed.

(* -------------------------------------------------------------- *)
Definition nat7   : nat := 7.
Definition nat15  : nat := nat7.+4.+4.
Definition nat31  : nat := nat15.+4.+4.+4.+4.
Definition nat63  : nat := nat31.+4.+4.+4.+4.+4.+4.+4.+4.
Definition nat127 : nat := nat63.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.
Definition nat255 : nat := nat127.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.+4.

Definition wsize_size_minus_1 (s: wsize) : nat :=
  match s with
  | U8   => nat7
  | U16  => nat15
  | U32  => nat31
  | U64  => nat63
  | U128 => nat127
  | U256 => nat255
  end.

Coercion nat_of_wsize (sz : wsize) :=
  (wsize_size_minus_1 sz).+1.

Definition wsize_bits (s:wsize) : Z :=
  Zpos (Pos.of_succ_nat (wsize_size_minus_1 s)).

Definition wsize_size (sz: wsize) : Z :=
  Zpos match sz return positive with
  | U8   => 1
  | U16  => 2
  | U32  => 4
  | U64  => 8
  | U128 => 16
  | U256 => 32
  end.

Definition wsize_log2 sz : nat :=
  match sz with
  | U8 => 0
  | U16 => 1
  | U32 => 2
  | U64 => 3
  | U128 => 4
  | U256 => 5
  end.

Lemma wsize8 : wsize_size U8 = 1%Z. done. Qed.

Definition wbase (s: wsize) : Z :=
  modulus (wsize_size_minus_1 s).+1.

Lemma le0_wsize_size ws : 0 <= wsize_size ws.
Proof. rewrite /wsize_size; lia. Qed.
Arguments le0_wsize_size {ws}.
Hint Resolve le0_wsize_size : core.

Lemma wsize_size_is_pow2 sz :
  wsize_size sz = 2 ^ Z.of_nat (wsize_log2 sz).
Proof. by case: sz. Qed.

Lemma wsize_sizeE sz : wsize_size sz =  wsize_bits sz / 8.
Proof. by case: sz. Qed.

Lemma wsize_size_pos sz :
  0 < wsize_size sz.
Proof. done. Qed.

Lemma wsize_size_wbase s : wsize_size s < wbase U8.
Proof. by apply /ZltP; case: s; vm_compute. Qed.

Lemma wsize_size_div_wbase sz sz' : (wsize_size sz | wbase sz').
Proof.
  apply Znumtheory.Zmod_divide => //.
  by case sz; case sz'.
Qed.

Lemma mod_wbase_wsize_size z sz sz' :
  z mod wbase sz mod wsize_size sz' = z mod wsize_size sz'.
Proof. by rewrite -Znumtheory.Zmod_div_mod //; apply wsize_size_div_wbase. Qed.

Lemma wsize_cmpP sz sz' :
  wsize_cmp sz sz' = Nat.compare (wsize_size_minus_1 sz) (wsize_size_minus_1 sz').
Proof. by case: sz sz' => -[]; vm_compute. Qed.

Lemma wsize_size_m s s' :
  (s ≤ s')%CMP →
  wsize_size_minus_1 s ≤ wsize_size_minus_1 s'.
Proof.
by move=> /eqP; rewrite /cmp_le /gcmp wsize_cmpP Nat.compare_ge_iff.
Qed.

Lemma wbase_m s s' :
  (s ≤ s')%CMP →
  wbase s <= wbase s'.
Proof.
  rewrite /wbase /modulus !two_power_nat_S !two_power_nat_equiv => /wsize_size_m s_le_s'.
  apply: Z.mul_le_mono_nonneg_l; first by [].
  apply: Z.pow_le_mono_r; first by [].
  Lia.lia.
Qed.

Lemma wsize_size_le a b :
  (a ≤ b)%CMP →
  (wsize_size a | wsize_size b).
Proof.
  case: a; case: b => // _.
  1, 7, 12, 16, 19, 21: by exists 1.
  1, 6, 10, 13, 15: by exists 2.
  1, 5, 8, 10: by exists 4.
  1, 4, 6: by exists 8.
  1, 3: by exists 16.
  by exists 32.
Qed.

Coercion nat_of_pelem (pe: pelem) : nat :=
  match pe with
  | PE1 => 1
  | PE2 => 2
  | PE4 => 4
  | PE8 => nat_of_wsize U8
  | PE16 => nat_of_wsize U16
  | PE32 => nat_of_wsize U32
  | PE64 => nat_of_wsize U64
  | PE128 => nat_of_wsize U128
  end.

Definition word := fun sz =>
  [comRingType of (wsize_size_minus_1 sz).+1.-word].

Global Opaque word.

Definition wand {s} (x y: word s) : word s := wand x y.
Definition wor {s} (x y: word s) : word s := wor x y.
Definition wxor {s} (x y: word s) : word s := wxor x y.

Definition wlt {sz} (sg: signedness) : word sz → word sz → bool :=
  match sg with
  | Unsigned => λ x y, (urepr x < urepr y)%R
  | Signed => λ x y, (srepr x < srepr y)%R
  end.

Definition wle sz (sg: signedness) : word sz → word sz → bool :=
  match sg with
  | Unsigned => λ x y, (urepr x <= urepr y)%R
  | Signed => λ x y, (srepr x <= srepr y)%R
  end.

Definition wnot sz (w: word sz) : word sz :=
  wxor w (-1)%R.

Arguments wnot {sz} w.

Definition wandn sz (x y: word sz) : word sz := wand (wnot x) y.

Definition wunsigned {s} (w: word s) : Z :=
  urepr w.

Definition wsigned {s} (w: word s) : Z :=
  srepr w.

Definition wrepr s (z: Z) : word s :=
  mkword (wsize_size_minus_1 s).+1 z.

Lemma word_ext n x y h h' :
  x = y →
  @mkWord n x h = @mkWord n y h'.
Proof. by move => e; apply/val_eqP/eqP. Qed.

Lemma wunsigned_inj sz : injective (@wunsigned sz).
Proof. by move => x y /eqP /val_eqP. Qed.

Lemma wrepr_unsigned s (w: word s) : wrepr s (wunsigned w) = w.
Proof. by rewrite /wrepr /wunsigned ureprK. Qed.

Lemma wrepr_signed s (w: word s) : wrepr s (wsigned w) = w.
Proof. by rewrite /wrepr /wsigned sreprK. Qed.

Lemma wunsigned_repr s z :
  wunsigned (wrepr s z) = z mod modulus (wsize_size_minus_1 s).+1.
Proof. done. Qed.

Lemma wrepr0 sz : wrepr sz 0 = 0%R.
Proof. by apply/eqP. Qed.

Lemma wrepr1 sz : wrepr sz 1 = 1%R.
Proof. by apply/eqP;case sz. Qed.

Lemma wreprB sz : wrepr sz (wbase sz) = 0%R.
Proof. by apply/eqP;case sz. Qed.

Lemma wunsigned_range sz (p: word sz) :
  0 <= wunsigned p < wbase sz.
Proof. by have /iswordZP := isword_word p. Qed.

Lemma wrepr_mod ws k : wrepr ws (k mod wbase ws) = wrepr ws k.
Proof. by apply wunsigned_inj; rewrite !wunsigned_repr Zmod_mod. Qed.

Lemma wunsigned_repr_small ws z : 0 <= z < wbase ws -> wunsigned (wrepr ws z) = z.
Proof. move=> h; rewrite wunsigned_repr; apply: Zmod_small h. Qed.

(* TODO: the proof of [wunsigned_sub] seems far simpler, we could use the same idea *)
Lemma wunsigned_add sz (p: word sz) (n: Z) :
  0 <= wunsigned p + n < wbase sz →
  wunsigned (p + wrepr sz n) = wunsigned p + n.
Proof.
case: p => p i h.
change (toword (add_word (mkWord i) (wrepr sz n)) = p + n).
rewrite/add_word mkwordK/= /urepr/=.
rewrite Zplus_mod_idemp_r.
exact: Zmod_small.
Qed.

Lemma wunsigned0 ws : @wunsigned ws 0 = 0.
Proof. by rewrite -wrepr0 wunsigned_repr Zmod_0_l. Qed.

Lemma wunsigned_add_if ws (a b : word ws) :
  wunsigned (a + b) = 
   if wunsigned a + wunsigned b <? wbase ws then wunsigned a + wunsigned b
   else wunsigned a + wunsigned b - wbase ws.
Proof.
  move: (wunsigned_range a) (wunsigned_range b).
  rewrite /wunsigned CoqWord.word.addwE /GRing.add /= -/(wbase ws) => ha hb.
  case: ZltP => hlt. 
  + by rewrite Zmod_small //;Psatz.lia.
  by rewrite -(Z_mod_plus_full _ (-1)) Zmod_small;Psatz.lia.
Qed.

Lemma wunsigned_sub_if ws (a b : word ws) : 
  wunsigned (a - b) = 
    if wunsigned b <=? wunsigned a then wunsigned a - wunsigned b 
    else  wbase ws + wunsigned a - wunsigned b.
Proof.
  move: (wunsigned_range a) (wunsigned_range b).
  rewrite /wunsigned CoqWord.word.subwE -/(wbase ws) => ha hb.
  have -> : (word.urepr a - word.urepr b)%R = word.urepr a - word.urepr b by done.
  case: ZleP => hle. 
  + by rewrite Zmod_small //;Psatz.lia.
  by rewrite -(Z_mod_plus_full _ 1) Zmod_small;Psatz.lia.
Qed.

Lemma wunsigned_opp_if ws (a : word ws) : 
  wunsigned (-a) = if wunsigned a == 0 then 0 else wbase ws - wunsigned a.
Proof.
  have ha := wunsigned_range a.
  rewrite -(GRing.add0r (-a)%R) wunsigned_sub_if wunsigned0.
  by case: ZleP; case: eqP => //; Psatz.lia.
Qed.

Lemma wunsigned_add_mod ws ws' (w1 w2 : word ws) :
  wunsigned (w1 + w2) mod wsize_size ws' = (wunsigned w1 + wunsigned w2) mod wsize_size ws'.
Proof.
  rewrite wunsigned_add_if.
  case: ZltP => // _.
  rewrite Zminus_mod.
  rewrite (Znumtheory.Zdivide_mod _ _ (wsize_size_div_wbase _ _)) Z.sub_0_r.
  by rewrite Zmod_mod.
Qed.

Lemma wunsigned_sub_mod ws ws' (w1 w2 : word ws) :
  wunsigned (w1 - w2) mod wsize_size ws' = (wunsigned w1 - wunsigned w2) mod wsize_size ws'.
Proof.
  rewrite wunsigned_sub_if.
  case: ZleP => // _.
  rewrite -Z.add_sub_assoc Zplus_mod.
  rewrite (Znumtheory.Zdivide_mod _ _ (wsize_size_div_wbase _ _)) Z.add_0_l.
  by rewrite Zmod_mod.
Qed.

Lemma wlt_irrefl sz sg (w: word sz) :
  wlt sg w w = false.
Proof. case: sg; exact: Z.ltb_irrefl. Qed.

Lemma wle_refl sz sg (w: word sz) :
  wle sg w w = true.
Proof. case: sg; exact: Z.leb_refl. Qed.

Definition wshr sz (x: word sz) (n: Z) : word sz :=
  lsr x (Z.to_nat n).

Definition wshl sz (x: word sz) (n: Z) : word sz :=
  lsl x (Z.to_nat n).

Definition wsar sz (x: word sz) (n: Z) : word sz :=
  asr x (Z.to_nat n).

Definition wmulhu sz (x y: word sz) : word sz :=
  wrepr sz ((wunsigned x * wunsigned y) / wbase sz).

Definition wmulhs sz (x y: word sz) : word sz :=
  wrepr sz ((wsigned x * wsigned y) / wbase sz).

Lemma wmulhuE sz (x y: word sz) : wmulhu x y = wrepr sz (wunsigned x * wunsigned y ÷ wbase sz).
Proof.
    rewrite /wmulhu Zquot.Zquot_Zdiv_pos //.
    apply: Z.mul_nonneg_nonneg; apply: (proj1 (wunsigned_range _)).
Qed.

Definition wmulhrs sz (x y: word sz) : word sz :=
  let: p := Z.shiftr (wsigned x * wsigned y) (wsize_size_minus_1 sz).-1 + 1 in
  wrepr sz (Z.shiftr p 1).

Definition wmax_unsigned sz := wbase sz - 1.
Definition wmin_signed (sz: wsize) : Z := - modulus (wsize_size_minus_1 sz).
Definition wmax_signed (sz: wsize) : Z := modulus (wsize_size_minus_1 sz) - 1.

Section wsigned_range.
Local Arguments Z.add: simpl never.
Local Arguments Z.sub: simpl never.
Local Arguments Z.opp: simpl never.

Lemma wsigned_range sz (p: word sz) :
  wmin_signed sz <= wsigned p <= wmax_signed sz.
Proof.
  have := wunsigned_range p; rewrite /wunsigned.
  rewrite /wsigned sreprE; case: ltzP => /=; rewrite /wmin_signed /wmax_signed.
  + lia.
  rewrite /GRing.add /GRing.opp /= /wbase /modulus two_power_nat_S.
  lia.
Qed.

End wsigned_range.

Notation u8   := (word U8).
Notation u16  := (word U16).
Notation u32  := (word U32).
Notation u64  := (word U64).
Notation u128 := (word U128).
Notation u256 := (word U256).

Definition x86_shift_mask (s:wsize) : u8 :=
  match s with
  | U8 | U16 | U32 => wrepr U8 31
  | U64  => wrepr U8 63
  | U128 => wrepr U8 127
  | U256 => wrepr U8 255
  end%Z.

Definition wbit_n sz (w:word sz) (n:nat) : bool :=
   wbit (wunsigned w) n.

Lemma eq_from_wbit_n s (w1 w2: word s) :
  reflect (∀ i : 'I_(wsize_size_minus_1 s).+1, wbit_n w1 i = wbit_n w2 i) (w1 == w2).
Proof. apply/eq_from_wbit. Qed.

Lemma wandE s (w1 w2: word s) i :
  wbit_n (wand w1 w2) i = wbit_n w1 i && wbit_n w2 i.
Proof. by rewrite /wbit_n /wand wandE. Qed.

Lemma wxorE s (w1 w2: word s) i :
  wbit_n (wxor w1 w2) i = wbit_n w1 i (+) wbit_n w2 i.
Proof. by rewrite /wbit_n /wxor wxorE. Qed.

Lemma wN1E sz i :
  @wbit_n sz (-1)%R i = leq (S i) (wsize_size_minus_1 sz).+1.
Proof. exact: wN1E. Qed.

Lemma w0E sz i :
  @wbit_n sz 0%R i  = false.
Proof. exact: Z.testbit_0_l. Qed.

Lemma wnotE sz (w: word sz) (i: 'I_(wsize_size_minus_1 sz).+1) :
  wbit_n (wnot w) i = ~~ wbit_n w i.
Proof.
  rewrite /wnot wxorE wN1E.
  case: i => i /= ->.
  exact: addbT.
Qed.

Lemma wshrE sz (x: word sz) c i :
  wbit_n (wshr x c) i = wbit_n x (Z.to_nat c + i).
Proof. exact: wbit_lsr. Qed.

Lemma wunsigned_wshr sz (x: word sz) c :
  wunsigned (wshr x (Z.of_nat c)) = wunsigned x / 2 ^ Z.of_nat c.
Proof.
  have rhs_range : 0 <= wunsigned x / 2 ^ Z.of_nat c ∧ wunsigned x / 2 ^ Z.of_nat c < modulus sz.
  - have x_range := wunsigned_range x.
    split.
    + apply: Z.div_pos; first lia.
      apply: Z.pow_pos_nonneg; lia.
     change (modulus sz) with (wbase sz).
     elim_div => ? ? []; last nia.
     apply: Z.pow_nonzero; lia.
  rewrite -(Z.mod_small (wunsigned x / 2 ^ Z.of_nat c) (modulus sz)) //.
  rewrite -wunsigned_repr.
  congr wunsigned.
  apply/eqP/eq_from_wbit_n => i.
  rewrite /wshr Nat2Z.id /wbit_n wbit_lsr wunsigned_repr /wbit.
  rewrite Z.mod_small //.
  rewrite Z.div_pow2_bits.
  2-3: lia.
  by rewrite Nat2Z.n2zD Z.add_comm.
Qed.

Lemma wshlE sz (w: word sz) c i :
  wbit_n (wshl w c) i = (Z.to_nat c <= i <= wsize_size_minus_1 sz)%nat && wbit_n w (i - Z.to_nat c).
Proof.
  rewrite /wbit_n /wshl /=.
  case: leP => hic /=;
    last (rewrite wbit_lsl_lo //; apply/leP; lia).
  have eqi : (Z.to_nat c + (i - Z.to_nat c))%nat = i.
   * by rewrite /addn /addn_rec; zify; rewrite Nat2Z.inj_sub; lia.
  have := wbit_lsl w (Z.to_nat c) (i - Z.to_nat c).
  by rewrite eqi => ->.
Qed.

Local Ltac lia :=
  rewrite /addn /addn_rec /subn /subn_rec; Psatz.lia.

Lemma wunsigned_wshl sz (x: word sz) c :
  wunsigned (wshl x (Z.of_nat c)) = (wunsigned x * 2 ^ Z.of_nat c) mod wbase sz.
Proof.
  rewrite /wshl Nat2Z.id.
  rewrite -wunsigned_repr.
  congr wunsigned.
  apply/eqP/eq_from_wbit_n => i.
  rewrite /wbit_n wunsigned_repr /modulus two_power_nat_equiv.
  rewrite {2}/wbit Z.mod_pow2_bits_low; last first.
  - move/ltP: (ltn_ord i); lia.
  case: (@ltP i c); last first.
  - move => c_le_i.
    have i_eq : nat_of_ord i = (c + (i - c))%nat by lia.
    rewrite i_eq wbit_lsl -i_eq ltn_ord /wbit.
    rewrite Z.mul_pow2_bits; last by lia.
    congr Z.testbit.
    lia.
  move => l_lt_c.
  rewrite wbit_lsl_lo; last by apply/ltP.
  rewrite Z.mul_pow2_bits_low //; lia.
Qed.

Lemma wshl_ovf sz (w: word sz) c :
  (wsize_size_minus_1 sz < Z.to_nat c)%coq_nat →
  wshl w c = 0%R.
Proof.
  move => hc; apply/eqP/eq_from_wbit_n => i.
  rewrite wshlE {2}/wbit_n wbit0.
  case: i => i /= /leP /le_S_n hi.
  have /leP -> := hi.
  case: leP => //; lia.
Qed.

Definition lsb {s} (w: word s) : bool := wbit_n w 0.
Definition msb {s} (w: word s) : bool := wbit_n w (wsize_size_minus_1 s).

Lemma msb_wordE {s} (w : word s) : msb w = CoqWord.word.msb w.
Proof. by []. Qed.

Definition wdwordu sz (hi lo: word sz) : Z :=
  wunsigned hi * wbase sz + wunsigned lo.

Definition wdwords sz (hi lo: word sz) : Z :=
  wsigned hi * wbase sz + wunsigned lo.

Definition waddcarry sz (x y: word sz) (c: bool) :=
  let n := wunsigned x + wunsigned y + Z.b2z c in
  (wbase sz <=? n, wrepr sz n).

Definition wsubcarry sz (x y: word sz) (c: bool) :=
  let n := wunsigned x - wunsigned y - Z.b2z c in
  (n <? 0, wrepr sz n).

Definition wumul sz (x y: word sz) :=
  let n := wunsigned x * wunsigned y in
  (wrepr sz (Z.quot n (wbase sz)), wrepr sz n).

Definition wdiv {sz} (p q : word sz) : word sz :=
  let p := wunsigned p in
  let q := wunsigned q in
  wrepr sz (p / q)%Z.

Definition wdivi {sz} (p q : word sz) : word sz :=
  let p := wsigned p in
  let q := wsigned q in
  wrepr sz (Z.quot p q)%Z.

Definition wmod {sz} (p q : word sz) : word sz :=
  let p := wunsigned p in
  let q := wunsigned q in
  wrepr sz (p mod q)%Z.

Definition wmodi {sz} (p q : word sz) : word sz :=
  let p := wsigned p in
  let q := wsigned q in
  wrepr sz (Z.rem p q)%Z.

Definition zero_extend sz sz' (w: word sz') : word sz :=
  wrepr sz (wunsigned w).

Definition sign_extend sz sz' (w: word sz') : word sz :=
  wrepr sz (wsigned w).

Definition wbit sz (w i: word sz) : bool :=
  wbit_n w (Z.to_nat (wunsigned i mod wsize_bits sz)).

Definition wror sz (w:word sz) (z:Z) :=
  let i := z mod wsize_bits sz in
  wor (wshr w i) (wshl w (wsize_bits sz - i)).

Definition wrol sz (w:word sz) (z:Z) :=
  let i := z mod wsize_bits sz in
  wor (wshl w i) (wshr w (wsize_bits sz - i)).

(* -------------------------------------------------------------------*)
Lemma wsignedE sz (w: word sz) :
  wsigned w = if msb w then wunsigned w - wbase sz else wunsigned w.
Proof. done. Qed.

(* -------------------------------------------------------------------*)
Lemma msb0 sz : @msb sz 0 = false.
Proof. by case: sz. Qed.

Lemma wshr0 sz (w: word sz) : wshr w 0 = w.
Proof. by rewrite /wshr /lsr Z.shiftr_0_r ureprK. Qed.

Lemma wshl0 sz (w: word sz) : wshl w 0 = w.
Proof. by rewrite /wshl /lsl Z.shiftl_0_r ureprK. Qed.

Lemma wsar0 sz (w: word sz) : wsar w 0 = w.
Proof. by rewrite /wsar /asr Z.shiftr_0_r sreprK. Qed.

(* -------------------------------------------------------------------*)
Lemma wltuE' sz (α β: word sz) :
  wlt Unsigned α β = (wunsigned (β - α) == (wunsigned β - wunsigned α)%Z) && (β != α).
Proof.
by rewrite -[X in X && _]negbK -wltuE /= -leNgt andbC eq_sym -lt_neqAle.
Qed.

Lemma wleuE sz (w1 w2: word sz) :
  wle Unsigned w1 w2 = (wunsigned (w2 - w1) == (wunsigned w2 - wunsigned w1))%Z.
Proof.
rewrite /= le_eqVlt -/(wlt Unsigned _ _) wltuE'.
rewrite orb_andr /= [w2 == w1]eq_sym orbN andbT.
by rewrite orb_idl // => /eqP /val_inj ->; rewrite subZE !subrr.
Qed.

Lemma wltsE sz (α β: word sz) : α ≠ β →
  wlt Signed α β = (msb (α - β) != (wsigned (α - β) != (wsigned α - wsigned β)%Z)).
Proof.
move=> ne_ab; rewrite /= !msb_wordE /wsigned /srepr.
rewrite !CoqWord.word.msbE /= !subZE; set w := (_ sz);
  case: (lerP (modulus _) (val α)) => ha;
  case: (lerP (modulus _) (val β)) => hb;
  case: (lerP (modulus _) (val _)) => hab.
+ rewrite ltr_add2r eq_sym eqb_id negbK opprB !addrA subrK.
  rewrite [val (α - β)%R]subw_modE /urepr /= -/w.
  case: ltrP; first by rewrite addrK eqxx.
  by rewrite addr0 lt_eqF // ltr_subl_addr ltr_addl modulus_gt0.
+ rewrite ltr_add2r opprB !addrA subrK eq_sym eqbF_neg negbK.
  rewrite [val (α - β)%R]subw_modE /urepr -/w /=; case: ltrP.
  + by rewrite mulr1n gt_eqF // ltr_addl modulus_gt0.
  + by rewrite addr0 eqxx.
+ rewrite ltr_subl_addr (lt_le_trans (urepr_ltmod _)); last first.
    by rewrite ler_addr urepr_ge0.
  rewrite eq_sym eqb_id negbK; apply/esym.
  rewrite [val _]subw_modE /urepr -/w /= ltNge ltW /=.
  * by rewrite addr0 addrAC eqxx.
  * by rewrite (lt_le_trans hb).
+ rewrite ltr_subl_addr (lt_le_trans (urepr_ltmod _)); last first.
    by rewrite ler_addr urepr_ge0.
  rewrite eq_sym eqbF_neg negbK [val _]subw_modE /urepr -/w /=.
  rewrite ltNge ltW ?addr0; last first.
    by rewrite (lt_le_trans hb).
  by rewrite addrAC gt_eqF // ltr_subl_addr ltr_addl modulus_gt0.
+ rewrite ltr_subr_addl ltNge ltW /=; last first.
    by rewrite (lt_le_trans (urepr_ltmod _)) // ler_addl urepr_ge0.
  apply/esym/negbTE; rewrite negbK; apply/eqP/esym.
  rewrite [val _]subw_modE /urepr /= -/w; have ->/=: (val α < val β)%R.
    by have := ltr_le_add ha hb; rewrite addrC ltr_add2l.
  rewrite mulr1n addrK opprD addrA lt_eqF //= opprK.
  by rewrite ltr_addl modulus_gt0.
+ rewrite ltr_subr_addl ltNge ltW /=; last first.
    by rewrite (lt_le_trans (urepr_ltmod _)) // ler_addl urepr_ge0.
  apply/esym/negbTE; rewrite negbK eq_sym eqbF_neg negbK.
  rewrite [val _]subw_modE /urepr -/w /= opprD addrA opprK.
  by have ->//: (val α < val β)%R; apply/(lt_le_trans ha).
+ rewrite [val (α - β)%R](subw_modE α β) -/w /urepr /=.
  rewrite eq_sym eqb_id negbK; case: ltrP.
  * by rewrite mulr1n addrK eqxx.
  * by rewrite addr0 lt_eqF // ltr_subl_addr ltr_addl modulus_gt0.
+ rewrite [val (α - β)%R](subw_modE α β) -/w /urepr /=.
  rewrite eq_sym eqbF_neg negbK; case: ltrP.
  * by rewrite mulr1n gt_eqF // ltr_addl modulus_gt0.
  * by rewrite addr0 eqxx.
Qed.

Lemma wlesE' sz (α β: word sz) : α ≠ β →
  wle Signed α β = (msb (α - β) != (wsigned (α - β) != (wsigned α - wsigned β)%Z)).
Proof.
move=> ne_ab; suff ->: wle Signed α β = wlt Signed α β by rewrite wltsE.
by move=> /=; rewrite le_eqVlt orb_idl // => /eqP /srepr_inj.
Qed.

Lemma wltsE' sz (α β: word sz) : α ≠ β →
  wlt Signed β α = (msb (α - β) == (wsigned (α - β) != (wsigned α - wsigned β)%Z)).
Proof.
have ->: wlt Signed β α = ~~ (wle Signed α β) by rewrite /= ltNge.
by move=> ne_ab; rewrite wlesE' // negbK.
Qed.

Lemma wlesE sz (α β: word sz) : α ≠ β →
  wle Signed β α = (msb (α - β) == (wsigned (α - β) != (wsigned α - wsigned β)%Z)).
Proof.
move=> ne_ab; suff ->: wle Signed β α = wlt Signed β α by rewrite wltsE'.
by move=> /=; rewrite le_eqVlt orb_idl // => /eqP /srepr_inj /esym.
Qed.

(* -------------------------------------------------------------------*)
Lemma zero_extend0 sz sz' :
  @zero_extend sz sz' 0%R = 0%R.
Proof. by apply/eqP/eq_from_wbit. Qed.

Lemma zero_extend_u sz (w:word sz) : zero_extend sz w = w.
Proof. by rewrite /zero_extend wrepr_unsigned. Qed.

Lemma zero_extend_sign_extend sz sz' s (w: word s) :
 (sz ≤ sz')%CMP →
  zero_extend sz (sign_extend sz' w) = sign_extend sz w.
Proof.
move => hsz; rewrite /sign_extend; apply: word_ext.
move: (wsigned w) => {w} z.
rewrite wunsigned_repr.
case: (modulus_m (wsize_size_m hsz)) => n hn.
by rewrite hn mod_pq_mod_q.
Qed.

Lemma zero_extend_wrepr sz sz' z :
  (sz <= sz')%CMP →
  zero_extend sz (wrepr sz' z) = wrepr sz z.
Proof.
move/wsize_size_m => hle.
apply: word_ext.
rewrite /wunsigned /urepr /wrepr /=.
case: (modulus_m hle) => n -> {hle}.
exact: mod_pq_mod_q.
Qed.

Lemma zero_extend_idem s s1 s2 (w:word s) :
  (s1 <= s2)%CMP -> zero_extend s1 (zero_extend s2 w) = zero_extend s1 w.
Proof.
  by move=> hle;rewrite [X in (zero_extend _ X) = _]/zero_extend zero_extend_wrepr.
Qed.

Lemma wbit_zero_extend s s' (w: word s') i :
  wbit_n (zero_extend s w) i = (i <= wsize_size_minus_1 s)%nat && wbit_n w i.
Proof.
rewrite /zero_extend /wbit_n /wunsigned /wrepr.
move: (urepr w) => {w} z.
rewrite mkwordK.
set m := wsize_size_minus_1 _.
rewrite /CoqWord.word.wbit /=.
rewrite /modulus two_power_nat_equiv.
case: leP => hi.
+ rewrite Z.mod_pow2_bits_low //; lia.
rewrite Z.mod_pow2_bits_high //; lia.
Qed.

Lemma zero_extend1 sz sz' :
  @zero_extend sz sz' 1%R = 1%R.
Proof. 
  apply/eqP/eq_from_wbit => -[i hi].
  have := @wbit_zero_extend sz sz' 1%R i.
  by rewrite /wbit_n => ->; rewrite -ltnS hi.
Qed.

Lemma sign_extend_truncate s s' (w: word s') :
  (s ≤ s')%CMP →
  sign_extend s w = zero_extend s w.
Proof.
  rewrite /sign_extend /zero_extend /wsigned /wunsigned.
  rewrite CoqWord.word.sreprE /= /wrepr.
  move: (CoqWord.word.urepr w) => z hle.
  apply/word_ext.
  have [n ->] := modulus_m (wsize_size_m hle).
  case: ssrZ.ltzP => // hgt.
  by rewrite Zminus_mod Z_mod_mult Z.sub_0_r Zmod_mod.
Qed.

Lemma sign_extend_u sz (w: word sz) : sign_extend sz w = w.
Proof. exact: sreprK. Qed.

Lemma wbase_n0 sz : wbase sz <> 0%Z.
Proof. by case sz. Qed.

Lemma wsigned0 sz : @wsigned sz 0%R = 0%Z.
Proof. by case: sz. Qed.

Lemma wsigned1 sz : @wsigned sz 1%R = 1%Z.
Proof. by case: sz. Qed.

Lemma wsignedN1 sz : @wsigned sz (-1)%R = (-1)%Z.
Proof. by case: sz. Qed.

Lemma sign_extend0 sz sz' :
  @sign_extend sz sz' 0%R = 0%R.
Proof. by rewrite /sign_extend wsigned0 wrepr0. Qed.

Lemma wandC sz : commutative (@wand sz).
Proof.
  by move => x y; apply/eqP/eq_from_wbit => i;
  rewrite /wand !CoqWord.word.wandE andbC.
Qed.

Lemma wandA sz : associative (@wand sz).
Proof.
  by move => x y z; apply/eqP/eq_from_wbit_n => i;
  rewrite !wandE andbA.
Qed.

Lemma wand0 sz (x: word sz) : wand 0 x = 0%R.
Proof. by apply/eqP. Qed.

Lemma wandN1 sz (x: word sz) : wand (-1) x = x.
Proof.
  apply/eqP/eq_from_wbit_n => i.
  by rewrite wandE wN1E ltn_ord.
Qed.

Lemma worC sz : commutative (@wor sz).
Proof.
  by move => x y; apply/eqP/eq_from_wbit => i;
  rewrite /wor !CoqWord.word.worE orbC.
Qed.

Lemma wor0 sz (x: word sz) : wor 0 x = x.
Proof. by apply/eqP/eq_from_wbit. Qed.

Lemma wor_xx sz (x: word sz) : wor x x = x.
Proof. by apply/eqP/eq_from_wbit; rewrite /= Z.lor_diag. Qed.

Lemma wxor0 sz (x: word sz) : wxor 0 x = x.
Proof. by apply/eqP/eq_from_wbit. Qed.

Lemma wxor_xx sz (x: word sz) : wxor x x = 0%R.
Proof. by apply/eqP/eq_from_wbit; rewrite /= Z.lxor_nilpotent. Qed.

Lemma wrepr_add sz (x y: Z) :
  wrepr sz (x + y) = (wrepr sz x + wrepr sz y)%R.
Proof. by apply: word_ext; rewrite /wrepr !mkwordK Zplus_mod. Qed.

Lemma wrepr_sub sz (x y: Z) :
  wrepr sz (x - y) = (wrepr sz x - wrepr sz y)%R.
Proof. by apply: word_ext; rewrite /wrepr !mkwordK -Zminus_mod_idemp_r -Z.add_opp_r Zplus_mod. Qed.

Lemma wmulE sz (x y: word sz) : (x * y)%R = wrepr sz (wunsigned x * wunsigned y).
Proof. by rewrite /wunsigned /wrepr; apply: word_ext. Qed.

Lemma wrepr_mul sz (x y: Z) :
  wrepr sz (x * y) = (wrepr sz x * wrepr sz y)%R.
Proof. by apply: word_ext; rewrite /wrepr !mkwordK Zmult_mod. Qed.

Lemma wrepr_m1 sz :
  wrepr sz (-1) = (-1)%R.
Proof. by apply /eqP; case sz. Qed.

Lemma wrepr_opp sz (x: Z) :
  wrepr sz (- x) = (- wrepr sz x)%R.
Proof. 
  have -> : (- x) = (- x)%R by done.
  by rewrite -(mulN1r x) wrepr_mul wrepr_m1 mulN1r.
Qed.

Lemma wadd_zero_extend sz sz' (x y: word sz') :
  (sz ≤ sz')%CMP →
  zero_extend sz (x + y) = (zero_extend sz x + zero_extend sz y)%R.
Proof.
move => hle; apply: word_ext.
rewrite /wrepr !mkwordK -Zplus_mod.
rewrite /wunsigned /urepr /=.
change (x + y)%R with (add_word x y).
rewrite /add_word /= /urepr /=.
case: (modulus_m (wsize_size_m hle)) => n -> {hle}.
by rewrite mod_pq_mod_q.
Qed.

Lemma wmul_zero_extend sz sz' (x y: word sz') :
  (sz ≤ sz')%CMP →
  zero_extend sz (x * y) = (zero_extend sz x * zero_extend sz y)%R.
Proof.
move => hle; apply: word_ext.
rewrite /wrepr !mkwordK -Zmult_mod.
rewrite /wunsigned /urepr /=.
change (x * y)%R with (mul_word x y).
rewrite /mul_word /= /urepr /=.
case: (modulus_m (wsize_size_m hle)) => n -> {hle}.
by rewrite mod_pq_mod_q.
Qed.

Lemma zero_extend_m1 sz sz' :
  (sz ≤ sz')%CMP →
  @zero_extend sz sz' (-1) = (-1)%R.
Proof. exact: zero_extend_wrepr. Qed.

Lemma wopp_zero_extend sz sz' (x: word sz') : 
  (sz ≤ sz')%CMP →
  zero_extend sz (-x) = (- zero_extend sz x)%R.
Proof.
 by move=> hsz; rewrite -(mulN1r x) wmul_zero_extend // zero_extend_m1 // mulN1r.
Qed.

Lemma wsub_zero_extend sz sz' (x y : word sz'): 
  (sz ≤ sz')%CMP →
  zero_extend sz (x - y) = (zero_extend sz x - zero_extend sz y)%R.
Proof.
  by move=> hsz; rewrite wadd_zero_extend // wopp_zero_extend. 
Qed.

Lemma zero_extend_wshl sz sz' (x: word sz') c :
  (sz ≤ sz')%CMP →
  zero_extend sz (wshl x c) = wshl (zero_extend sz x) c.
Proof.
move => hle; apply/eqP/eq_from_wbit_n => i.
rewrite !(wbit_zero_extend, wshlE).
have := wsize_size_m hle.
move: i.
set m := wsize_size_minus_1 _.
set m' := wsize_size_minus_1 _.
case => i /= /leP hi hm.
have him : (i <= m)%nat by apply/leP; lia.
rewrite him andbT /=.
have him' : (i <= m')%nat by apply/leP; lia.
rewrite him' andbT.
case: leP => //= hci.
have -> // : (i - Z.to_nat c <= m)%nat.
apply/leP; rewrite /subn /subn_rec; lia.
Qed.

Lemma wand_zero_extend sz sz' (x y: word sz') :
  (sz ≤ sz')%CMP →
  wand (zero_extend sz x) (zero_extend sz y) = zero_extend sz (wand x y).
Proof.
move => hle.
apply/eqP/eq_from_wbit_n => i.
rewrite !(wbit_zero_extend, wandE).
by case: (_ <= _)%nat.
Qed.

Lemma wxor_zero_extend sz sz' (x y: word sz') :
  (sz ≤ sz')%CMP →
  wxor (zero_extend sz x) (zero_extend sz y) = zero_extend sz (wxor x y).
Proof.
move => hle.
apply/eqP/eq_from_wbit_n => i.
rewrite !(wbit_zero_extend, wxorE).
by case: (_ <= _)%nat.
Qed.

Lemma wnot_zero_extend sz sz' (x : word sz') :
  (sz ≤ sz')%CMP →
  wnot (zero_extend sz x) = zero_extend sz (wnot x).
Proof.
move => hle.
apply/eqP/eq_from_wbit_n => i.
rewrite !(wbit_zero_extend, wnotE).
have := wsize_size_m hle.
move: i.
set m := wsize_size_minus_1 _.
set m' := wsize_size_minus_1 _.
case => i /= /leP hi hm.
have him : (i <= m)%nat. by apply/leP; lia.
rewrite him /=.
have hi' : (i < m'.+1)%nat. apply /ltP. lia.
by have /= -> := @wnotE sz' x (Ordinal hi') .
Qed.

Lemma wunsigned_sub (sz : wsize) (p : word sz) (n : Z):
  0 <= wunsigned p - n < wbase sz → wunsigned (p - wrepr sz n) = wunsigned p - n.
Proof.
  move=> h.
  rewrite -{1}(wrepr_unsigned p).
  by rewrite -wrepr_sub wunsigned_repr Z.mod_small.
Qed.

(* -------------------------------------------------------------------*)
Ltac wring :=
  rewrite ?zero_extend_u; ssring.

(* -------------------------------------------------------------------*)
Lemma wdwordu0 sz (w:word sz) : wdwordu 0 w = wunsigned w.
Proof. done. Qed.

Lemma wdwords0 sz (w:word sz) :
  wdwords (if msb w then (-1)%R else 0%R) w = wsigned w.
Proof.
  rewrite wsignedE /wdwords; case: msb; rewrite ?wsigned0 ?wsignedN1; ring.
Qed.

(* -------------------------------------------------------------------*)
Lemma lsr0 n (w: n.-word) : lsr w 0 = w.
Proof. by rewrite /lsr Z.shiftr_0_r ureprK. Qed.

Lemma subword0 (ws ws' :wsize) (w: word ws') :
   CoqWord.word.subword 0 ws w = zero_extend ws w.
Proof.
  apply/eqP/eq_from_wbit_n => i.
  rewrite wbit_zero_extend.
  have := ltn_ord i.
  rewrite ltnS => -> /=.
  rewrite /subword lsr0.
  rewrite {1}/wbit_n /wunsigned mkwordK.
  rewrite /CoqWord.word.wbit /modulus two_power_nat_equiv.
  rewrite Z.mod_pow2_bits_low //.
  have /leP := ltn_ord i.
  lia.
Qed.

(* -------------------------------------------------------------------*)
Definition check_scale (s:Z) :=
  (s == 1%Z) || (s == 2%Z) || (s == 4%Z) || (s == 8%Z).

(* -------------------------------------------------------------------*)
Definition mask_word (sz:wsize) : u64 :=
  match sz with
  | U8 | U16 => wshl (-1)%R (wsize_bits sz)
  | _ => 0%R
  end.

Definition merge_word (wr: u64) (sz:wsize) (w:word sz) :=
   wxor (wand (mask_word sz) wr) (zero_extend U64 w).

(* -------------------------------------------------------------------*)
Definition split_vec {sz} ve (w : word sz) :=
  let wsz := (sz %/ ve + sz %% ve)%nat in
  [seq subword (i * ve)%nat ve w | i <- iota 0 wsz].

Definition make_vec {sz} sz' (s : seq (word sz)) :=
  wrepr sz' (wcat_r s).

Lemma make_vec_split_vec sz w :
  make_vec sz (split_vec U8 w) = w.
Proof.
have mod0: sz %% U8 = 0%nat by case: {+}sz.
have sz_even: sz = (U8 * (sz %/ U8))%nat :> nat.
+ by rewrite [LHS](divn_eq _ U8) mod0 addn0 mulnC.
rewrite /make_vec /split_vec mod0 addn0; set s := map _ _.
pose wt := (ecast ws (ws.-word) sz_even w).
pose t  := [tuple subword (i * U8) U8 wt | i < sz %/ U8].
have eq_st: wcat_r s = wcat t.
+ rewrite {}/s {}/t /=; pose F i := subword (i * U8) U8 wt.
  rewrite (map_comp F val) val_enum_ord {}/F.
  congr wcat_r; apply/eq_map => i; apply/eqP/eq_from_wbit.
  move=> j; rewrite !subwordE; congr (CoqWord.word.wbit (t2w _) _).
  apply/val_eqP/eqP => /=; apply/eq_map=> k.
  suff ->: val wt = val w by done.
  by rewrite {}/wt; case: _ / sz_even.
rewrite {}eq_st wcat_subwordK {s t}/wt; case: _ / sz_even.
by rewrite /wrepr /= ureprK.
Qed.

Lemma mkwordI n x y :
  (0 <= x < modulus n)%R ->
  (0 <= y < modulus n)%R ->
  mkword n x = mkword n y -> x = y.
Proof.
by case/andP => /ZleP ? /ZltP ? /andP[] /ZleP ? /ZltP ? [];
  rewrite !Z.mod_small.
Qed.

Lemma make_vec_inj sz (bs bs': seq u8) :
  size bs = size bs' →
  size bs = Z.to_nat (wsize_size sz) →
  make_vec sz bs = make_vec sz bs' →
  bs = bs'.
Proof.
Transparent word.
rewrite /make_vec /wrepr /word.
Opaque word.
have : (wsize_size_minus_1 sz).+1 = (8 * Z.to_nat (wsize_size sz))%nat by case: sz.
move: (wsize_size sz) => n /= ->.
move: {n} (Z.to_nat n) => n.
move => eq_size <- /mkwordI.
rewrite {2}eq_size => /(_ (wcat_subproof (in_tuple bs)) (wcat_subproof (in_tuple bs'))).
exact: wcat_rI eq_size.
Qed.

(* -------------------------------------------------------------------*)
Definition lift1_vec' ve ve' (op : word ve → word ve')
    (sz sz': wsize) (w: word sz) : word sz' :=
  make_vec sz' (map op (split_vec ve w)).

Definition lift1_vec ve (op : word ve -> word ve)
    (sz:wsize) (w:word sz) : word sz :=
  lift1_vec' op sz w.
Arguments lift1_vec : clear implicits.

Definition lift2_vec ve (op : word ve -> word ve -> word ve)
  (sz:wsize) (w1 w2:word sz) : word sz :=
  make_vec sz (map2 op (split_vec ve w1) (split_vec ve w2)).
Arguments lift2_vec : clear implicits.

(* -------------------------------------------------------------------*)
Definition wbswap sz (w: word sz) : word sz :=
  make_vec sz (rev (split_vec U8 w)).

(* -------------------------------------------------------------------*)
Definition popcnt sz (w: word sz) :=
 wrepr sz (count id (w2t w)).

(* -------------------------------------------------------------------*)
Definition pextr sz (w1 w2: word sz) :=
 wrepr sz (t2w (in_tuple (mask (w2t w2) (w2t w1)))).

(* -------------------------------------------------------------------*)
Definition halve_list A : seq A → seq A :=
  fix loop m := if m is a :: _ :: m' then a :: loop m' else m.

Definition wpmulu sz (x y: word sz) : word sz :=
  let xs := halve_list (split_vec U32 x) in
  let ys := halve_list (split_vec U32 y) in
  let f (a b: u32) : u64 := wrepr U64 (wunsigned a * wunsigned b) in
  make_vec sz (map2 f xs ys).

(* -------------------------------------------------------------------*)
Definition wpshufb1 (s : seq u8) (idx : u8) :=
  if msb idx then 0%R else
    let off := wunsigned (wand idx (wshl 1 4%Z - 1)) in
    (s`_(Z.to_nat off))%R.

Definition wpshufb (sz: wsize) (w idx: word sz) : word sz :=
  let s := split_vec 8 w in
  let i := split_vec 8 idx in
  let r := map (wpshufb1 s) i in
  make_vec sz r.

(* -------------------------------------------------------------------*)
Definition wpshufd1 (s : u128) (o : u8) (i : nat) :=
  subword 0 32 (wshr s (32 * urepr (subword (2 * i) 2 o))).

Definition wpshufd_128 (s : u128) (o : Z) : u128 :=
  let o := wrepr U8 o in
  let d := [seq wpshufd1 s o i | i <- iota 0 4] in
  wrepr U128 (wcat_r d).

Definition wpshufd_256 (s : u256) (o : Z) : u256 :=
  make_vec U256 (map (λ w, wpshufd_128 w o) (split_vec U128 s)).

Definition wpshufd sz : word sz → Z → word sz :=
  match sz with
  | U128 => wpshufd_128
  | U256 => wpshufd_256
  | _ => λ w _, w end.

(* -------------------------------------------------------------------*)

Definition wpshufl_u64 (w:u64) (z:Z) : u64 :=
  let v := split_vec U16 w in
  let j := split_vec 2 (wrepr U8 z) in
  make_vec U64 (map (λ n, v`_(Z.to_nat (urepr n)))%R j).

Definition wpshufl_u128 (w:u128) (z:Z) :=
  match split_vec 64 w with
  | [::h;l] => make_vec U128 [::(h:u64); wpshufl_u64 l z]
  | _       => w
  end.

Definition wpshufh_u128 (w:u128) (z:Z) :=
  match split_vec 64 w with
  | [::h;l] => make_vec U128 [::wpshufl_u64 h z; (l:u64)]
  | _       => w
  end.

Definition wpshufl_u256 (s:u256) (z:Z) :=
  make_vec U256 (map (λ w, wpshufl_u128 w z) (split_vec U128 s)).

Definition wpshufh_u256 (s:u256) (z:Z) :=
  make_vec U256 (map (λ w, wpshufh_u128 w z) (split_vec U128 s)).

Definition wpshuflw sz : word sz → Z → word sz :=
  match sz with
  | U128 => wpshufl_u128
  | U256 => wpshufl_u256
  | _ => λ w _, w end.

Definition wpshufhw sz : word sz → Z → word sz :=
  match sz with
  | U128 => wpshufh_u128
  | U256 => wpshufh_u256
  | _ => λ w _, w end.

(* -------------------------------------------------------------------*)

(*Section UNPCK.
  (* Interleaves two even-sized lists. *)
  Context (T: Type).
  Fixpoint unpck (qs xs ys: seq T) : seq T :=
    match xs, ys with
    | [::], _ | _, [::]
    | [:: _], _ | _, [:: _]
      => qs
    | x :: _ :: xs', y :: _ :: ys' => unpck (x :: y :: qs) xs' ys'
    end.
End UNPCK.

Definition wpunpckl sz (ve: velem) (x y: word sz) : word sz :=
  let xv := split_vec ve x in
  let yv := split_vec ve y in
  let zv := unpck [::] xv yv in
  make_vec sz (rev zv).

Definition wpunpckh sz (ve: velem) (x y: word sz) : word sz :=
  let xv := split_vec ve x in
  let yv := split_vec ve y in
  let zv := unpck [::] (rev xv) (rev yv) in
  make_vec sz zv.
*)

Fixpoint interleave {A:Type} (l1 l2: list A) :=
  match l1, l2 with
  | [::], _ => l2
  | _, [::] => l1
  | a1::l1, a2::l2 => a1::a2::interleave l1 l2
  end.

Definition interleave_gen (get:u128 -> u64) (ve:velem) (src1 src2: u128) :=
  let ve : nat :=  wsize_of_velem ve in
  let l1 := split_vec ve (get src1) in
  let l2 := split_vec ve (get src2) in
  make_vec U128 (interleave l1 l2).

Definition wpunpckl_128 := interleave_gen (subword 0 64).

Definition wpunpckl_256 ve (src1 src2 : u256) :=
  make_vec U256
    (map2 (wpunpckl_128 ve) (split_vec U128 src1) (split_vec U128 src2)).

Definition wpunpckh_128 := interleave_gen (subword 64 64).

Definition wpunpckh_256 ve (src1 src2 : u256) :=
  make_vec U256
    (map2 (wpunpckh_128 ve) (split_vec U128 src1) (split_vec U128 src2)).

Definition wpunpckl (sz:wsize) : velem -> word sz -> word sz -> word sz :=
  match sz with
  | U128 => wpunpckl_128
  | U256 => wpunpckl_256
  | _    => fun ve w1 w2 => w1
  end.

Definition wpunpckh (sz:wsize) : velem -> word sz -> word sz -> word sz :=
  match sz with
  | U128 => wpunpckh_128
  | U256 => wpunpckh_256
  | _    => fun ve w1 w2 => w1
  end.

(* -------------------------------------------------------------------*)
Section UPDATE_AT.
  Context (T: Type) (t: T).

  Fixpoint update_at (xs: seq T) (i: nat) : seq T :=
    match xs with
    | [::] => [::]
    | x :: xs' => if i is S i' then x :: update_at xs' i' else t :: xs'
    end.

End UPDATE_AT.

Definition wpinsr ve (v: u128) (w: word ve) (i: u8) : u128 :=
  let v := split_vec ve v in
  let i := Z.to_nat (wunsigned i) in
  make_vec U128 (update_at w v i).

(* -------------------------------------------------------------------*)
Definition winserti128 (v: u256) (w: u128) (i: u8) : u256 :=
  let v := split_vec U128 v in
  make_vec U256 (if lsb i then [:: v`_0 ; w ] else [:: w ; v`_1 ])%R.

(* -------------------------------------------------------------------*)
Definition wpblendd sz (w1 w2: word sz) (m: u8) : word sz :=
  let v1 := split_vec U32 w1 in
  let v2 := split_vec U32 w2 in
  let b := split_vec 1 m in
  let r := map3 (λ b v1 v2, if b == 1%R then v2 else v1) b v1 v2 in
  make_vec sz r.

(* -------------------------------------------------------------------*)
Definition wpbroadcast ve sz (w: word ve) : word sz :=
  let r := nseq (sz %/ ve) w in
  make_vec sz r.

(* -------------------------------------------------------------------*)
Fixpoint seq_dup_hi T (m: seq T) : seq T :=
  if m is _ :: a :: m' then a :: a :: seq_dup_hi m' else [::].

Fixpoint seq_dup_lo T (m: seq T) : seq T :=
  if m is a :: _ :: m' then a :: a :: seq_dup_lo m' else [::].

Definition wdup_hi ve sz (w: word sz) : word sz :=
  let v : seq (word ve) := split_vec ve w in
  make_vec sz (seq_dup_hi v).

Definition wdup_lo ve sz (w: word sz) : word sz :=
  let v : seq (word ve) := split_vec ve w in
  make_vec sz (seq_dup_lo v).

(* -------------------------------------------------------------------*)
Definition wperm2i128 (w1 w2: u256) (i: u8) : u256 :=
  let choose (n: nat) :=
      match urepr (subword n 2 i) with
      | 0 => subword 0 U128 w1
      | 1 => subword U128 U128 w1
      | 2 => subword 0 U128 w2
      | _ => subword U128 U128 w2
      end in
  let lo := if wbit_n i 3 then 0%R else choose 0%nat in
  let hi := if wbit_n i 7 then 0%R else choose 4%nat in
  make_vec U256 [:: lo ; hi ].

(* -------------------------------------------------------------------*)
Definition wpermd1 (v: seq u32) (idx: u32) :=
  let off := wunsigned idx mod 8 in
  (v`_(Z.to_nat off))%R.

Definition wpermd sz (w1 idx: word sz) : word sz :=
  let v := split_vec U32 w1 in
  let i := split_vec U32 idx in
  make_vec sz (map (wpermd1 v) i).

(* -------------------------------------------------------------------*)
Definition wpermq (w: u256) (i: u8) : u256 :=
  let v := split_vec U64 w in
  let j := split_vec 2 i in
  make_vec U256 (map (λ n, v`_(Z.to_nat (urepr n)))%R j).

(* -------------------------------------------------------------------*)
Definition wpsxldq op sz (w: word sz) (i: u8) : word sz :=
  let n : Z := (Z.min 16 (wunsigned i)) * 8 in
  lift1_vec U128 (λ w, op w n) sz w.

Definition wpslldq := wpsxldq (@wshl _).
Definition wpsrldq := wpsxldq (@wshr _).

(* -------------------------------------------------------------------*)
Definition wpcmpu1 (cmp: Z → Z → bool) ve (x y: word ve) : word ve :=
  if cmp (wunsigned x) (wunsigned y) then (-1)%R else 0%R.
Arguments wpcmpu1 cmp {ve} _ _.

Definition wpcmpeq ve sz (w1 w2: word sz) : word sz :=
  lift2_vec ve (wpcmpu1 Z.eqb) sz w1 w2.

Definition wpcmpgt ve sz (w1 w2: word sz) : word sz :=
  lift2_vec ve (wpcmpu1 Z.gtb) sz w1 w2.

(* -------------------------------------------------------------------*)
Definition wminmax1 ve (cmp : word ve -> word ve -> bool) (x y : word ve) : word ve :=
  if cmp x y then x else y.

Definition wmin sg ve sz (x y : word sz) :=
  lift2_vec ve (wminmax1 (wlt sg)) sz x y.

Definition wmax sg ve sz (x y : word sz) :=
  lift2_vec ve (wminmax1 (fun u v => wlt sg v u)) sz x y.

(* -------------------------------------------------------------------*)
Definition saturated_signed (sz: wsize) (x: Z): Z :=
 Z.max (wmin_signed sz) (Z.min (wmax_signed sz) x).

Definition wrepr_saturated_signed (sz: wsize) (x: Z) : word sz :=
 wrepr sz (saturated_signed sz x).

Fixpoint add_pairs (m: seq Z) : seq Z :=
  if m is x :: y :: z then x + y :: add_pairs z
  else [::].

Definition wpmaddubsw sz (v1 v2: word sz) : word sz :=
  let w1 := map wunsigned (split_vec VE8 v1) in
  let w2 := map wsigned (split_vec VE8 v2) in
  let result := [seq wrepr_saturated_signed sz z | z <- add_pairs (map2 *%R w1 w2) ] in
  make_vec sz result.

Definition wpmaddwd sz (v1 v2: word sz) : word sz :=
  let w1 := map wsigned (split_vec VE16 v1) in
  let w2 := map wsigned (split_vec VE16 v2) in
  let result := [seq wrepr sz z | z <- add_pairs (map2 *%R w1 w2) ] in
  make_vec sz result.

(* Test case from the documentation: VPMADDWD wraps when all inputs are min-signed *)
Local Lemma test_wpmaddwd_wraps :
  let: s16 := wrepr U16 (wmin_signed U16) in
  let: s32 := make_vec U32 [:: s16 ; s16 ] in
  let: res := wpmaddwd s32 s32 in
  let: expected := wrepr U32 (wmin_signed U32) in
  res = expected.
Proof. vm_compute. by apply/eqP. Qed.

(* -------------------------------------------------------------------*)
Definition wpack sz pe (arg: seq Z) : word sz :=
  let w := map (CoqWord.word.mkword pe) arg in
  wrepr sz (word.wcat_r w).

(* -------------------------------------------------------------------*)
Definition wpmovmskb (dsz ssz: wsize) (w : word ssz) : word dsz :=
  wrepr dsz (t2w_def [tuple of map msb (split_vec U8 w)]).

(* -------------------------------------------------------------------*)
Definition wpblendvb sz (w1 w2 m: word sz): word sz :=
  let v1 := split_vec U8 w1 in
  let v2 := split_vec U8 w2 in
  let b  := map msb (split_vec U8 m)  in
  let r := map3 (fun bi v1i v2i => if bi then v2i else v1i) b v1 v2 in
  make_vec sz r.

(* -------------------------------------------------------------------*)
Lemma pow2pos q : 0 < 2 ^ Z.of_nat q.
Proof. by rewrite -two_power_nat_equiv. Qed.

Lemma pow2nz q : 2 ^ Z.of_nat q ≠ 0.
Proof. have := pow2pos q; lia. Qed.

Lemma wbit_n_pow2m1 sz (n i: nat) :
  wbit_n (wrepr sz (2 ^ Z.of_nat n - 1)) i = (i < Nat.min n (wsize_size_minus_1 sz).+1)%nat.
Proof.
  rewrite /wbit_n /CoqWord.word.wbit wunsigned_repr /modulus two_power_nat_equiv.
  case: (le_lt_dec (wsize_size_minus_1 sz).+1 i) => hi.
  - rewrite Z.mod_pow2_bits_high; last lia.
    symmetry; apply/negbTE/negP => /ltP.
    lia.
  rewrite Z.mod_pow2_bits_low; last lia.
  rewrite /Z.sub -/(Z.pred (2 ^ Z.of_nat n)) -Z.ones_equiv.
  case: ltP => i_n.
  - apply: Z.ones_spec_low; lia.
  apply: Z.ones_spec_high; lia.
Qed.

Lemma wand_pow2nm1 sz (x: word sz) n :
  let: k := ((wsize_size_minus_1 sz).+1 - n)%nat in
  wand x (wrepr sz (2 ^ Z.of_nat n - 1)) = wshr (wshl x (Z.of_nat k)) (Z.of_nat k).
Proof.
  set k := (_ - _)%nat.
  apply/eqP/eq_from_wbit_n => i.
  rewrite wandE wshrE wshlE wbit_n_pow2m1.
  have := ltn_ord i.
  move: (nat_of_ord i) => {i} i i_bounded.
  replace (i < _)%nat with (i < n)%nat; last first.
  - apply Nat.min_case_strong => //  n_large.
    rewrite i_bounded.
    apply/ltP.
    move/ltP: i_bounded.
    Psatz.lia.
  move: i_bounded.
  subst k.
  move: (wsize_size_minus_1 _) => w.
  rewrite ltnS => /leP i_bounded.
  rewrite Nat2Z.id.
  case: ltP => i_n.
  - rewrite (andbC (_ && _)); congr andb.
    + congr (wbit_n x); lia.
    symmetry; apply/andP; split; apply/leP; lia.
  rewrite andbF.
  replace (w.+1 - n + i <= w)%nat with false; first by rewrite andbF.
  symmetry; apply/leP.
  lia.
Qed.

Section FORALL_NAT_BELOW.
  Context (P: nat → bool).

  Fixpoint forallnat_below (n: nat) : bool :=
    if n is S n' then if P n' then forallnat_below n' else false else true.

  Lemma forallnat_belowP n :
    reflect (∀ i, (i < n)%coq_nat → P i) (forallnat_below n).
  Proof.
    elim: n.
    - by constructor => i /Nat.nlt_0_r.
    move => n ih /=; case hn: P; last first.
    - constructor => /(_ n (Nat.lt_succ_diag_r n)).
      by rewrite hn.
    case: ih => ih; constructor.
    - move => i i_le_n.
      case: (i =P n); first by move => ->.
      move => i_neq_n; apply: ih; lia.
    move => K; apply: ih => i i_lt_n; apply: K; lia.
  Qed.

End FORALL_NAT_BELOW.

Lemma wbit_n_Npow2n sz n (i: 'I_(wsize_size_minus_1 sz).+1) :
  wbit_n (wrepr sz (-2 ^ Z.of_nat n)) i = (n <= i)%nat.
Proof.
  move: (i: nat) (ltn_ord i) => {i} i /ltP i_bounded.
  case: (@ltP n (wsize_size_minus_1 sz).+1) => hn.
  + apply/eqP.
    apply/forallnat_belowP: i i_bounded.
    change (
        let k := wrepr sz (- 2 ^ Z.of_nat n) in
        forallnat_below (λ i : nat, wbit_n k i == (n <= i)%nat) (wsize_size_minus_1 sz).+1
      ).
    apply/forallnat_belowP: n hn.
    by case: sz; vm_cast_no_check (erefl true).
  replace (wrepr _ _) with (0%R : word sz).
  rewrite w0E; symmetry; apply/leP; lia.
  rewrite wrepr_opp -oppr0.
  congr (-_)%R.
  apply/word_eqP.
  rewrite mkword_valK.
  apply/eqP; symmetry.
  rewrite /modulus two_power_nat_equiv.
  apply/Z.mod_divide; first exact: pow2nz.
  exists (2 ^ (Z.of_nat (n - (wsize_size_minus_1 sz).+1))).
  rewrite -Z.pow_add_r;
  first congr (2 ^ _).
  all: lia.
Qed.

Lemma wand_Npow2n sz (x: word sz) n :
  wand x (wrepr sz (- 2 ^ Z.of_nat n)) = wshl (wshr x (Z.of_nat n)) (Z.of_nat n).
Proof.
  apply/eqP/eq_from_wbit_n => i.
  rewrite wandE wshlE wshrE Nat2Z.id wbit_n_Npow2n.
  move: (nat_of_ord i) (ltn_ord i) => {i} i.
  rewrite ltnS => i_bounded.
  rewrite i_bounded andbT andbC.
  case: (@leP n i) => hni //=.
  congr (wbit_n x).
  lia.
Qed.

Lemma an_mod_bn_divn (a b n: Z) :
  n ≠ 0 →
  a * n mod (b * n) / n = a mod b.
Proof.
  by move => nnz; rewrite Zmult_mod_distr_r Z.div_mul.
Qed.

Lemma wand_modulo sz (x: word sz) n :
  wunsigned (wand x (wrepr sz (2 ^ Z.of_nat n - 1))) = wunsigned x mod 2 ^ Z.of_nat n.
Proof.
  rewrite wand_pow2nm1 wunsigned_wshr wunsigned_wshl /wbase /modulus two_power_nat_equiv.
  case: (@leP n (wsize_size_minus_1 sz).+1); last first.
  - move => k_lt_n.
    replace (_.+1 - n)%nat with 0%nat by lia.
    have [ x_pos x_bounded ] := wunsigned_range x.
    rewrite Z.mul_1_r Z.div_1_r !Z.mod_small //; split.
    1, 3: lia.
    + apply: Z.lt_trans; first exact: x_bounded.
      rewrite /wbase /modulus two_power_nat_equiv.
      apply: Z.pow_lt_mono_r; lia.
      by rewrite -two_power_nat_equiv.
  set k := _.+1.
  move => n_le_k.
  have := an_mod_bn_divn (wunsigned x) (2 ^ Z.of_nat n) (@pow2nz (k - n)%nat).
  rewrite -Z.pow_add_r.
  2-3: lia.
  replace (Z.of_nat n + Z.of_nat (k - n)) with (Z.of_nat k) by lia.
  done.
Qed.

Lemma div_mul_in_range a b m :
  0 < b →
  0 <= a < m →
  0 <= a / b * b < m.
Proof.
  move => b_pos a_range; split.
  * suff : 0 <= a / b by nia.
    apply: Z.div_pos; lia.
  elim_div; lia.
Qed.

Lemma wand_align sz (x: word sz) n :
  wunsigned (wand x (wrepr sz (-2 ^ Z.of_nat n))) = wunsigned x / 2 ^ Z.of_nat n * 2 ^ Z.of_nat n.
Proof.
  rewrite wand_Npow2n wunsigned_wshl wunsigned_wshr.
  apply: Z.mod_small.
  apply: div_mul_in_range.
  - exact: pow2pos.
  exact: wunsigned_range.
Qed.

(** Round to the multiple of [sz'] below. *)
Definition align_word (sz sz': wsize) (p: word sz) : word sz :=
  wand p (wrepr sz (-wsize_size sz')).

Lemma align_word_U8 sz (p: word sz) :
  align_word U8 p = p.
Proof. by rewrite /align_word wandC wandN1. Qed.

Lemma align_word_aligned (sz sz': wsize) (p: word sz) :
  wunsigned (align_word sz' p) mod wsize_size sz' == 0.
Proof.
  rewrite /align_word wsize_size_is_pow2 wand_align Z.mod_mul //.
  exact: pow2nz.
Qed.

Lemma align_word_range sz sz' (p: word sz) :
  wunsigned p - wsize_size sz' < wunsigned (align_word sz' p) <= wunsigned p.
Proof.
  rewrite /align_word wsize_size_is_pow2 wand_align.
  have ? := wunsigned_range p.
  have ? := pow2pos (wsize_log2 sz').
  elim_div; Psatz.lia.
Qed.

Lemma align_wordE sz sz' (p: word sz) :
  wunsigned (align_word sz' p) = wunsigned p - (wunsigned p mod wsize_size sz').
Proof.
  have nz := wsize_size_pos sz'.
  rewrite {1}(Z.div_mod (wunsigned p) (wsize_size sz')); last lia.
  rewrite /align_word wsize_size_is_pow2 wand_align.
  lia.
Qed.

(* ------------------------------------------------------------------------- *)

Definition word_uincl sz1 sz2 (w1:word sz1) (w2:word sz2) :=
  (sz1 <= sz2)%CMP && (w1 == zero_extend sz1 w2).

Lemma word_uincl_refl s (w : word s): word_uincl w w.
Proof. by rewrite /word_uincl zero_extend_u cmp_le_refl eqxx. Qed.
Hint Resolve word_uincl_refl : core.

Lemma word_uincl_eq s (w w': word s):
  word_uincl w w' → w = w'.
Proof. by move=> /andP [] _ /eqP; rewrite zero_extend_u. Qed.

Lemma word_uincl_trans s2 w2 s1 s3 w1 w3 :
   @word_uincl s1 s2 w1 w2 -> @word_uincl s2 s3 w2 w3 -> word_uincl w1 w3.
Proof.
  rewrite /word_uincl => /andP [hle1 /eqP ->] /andP [hle2 /eqP ->].
  by rewrite (cmp_le_trans hle1 hle2) zero_extend_idem // eqxx.
Qed.

Lemma word_uincl_zero_ext sz sz' (w':word sz') : (sz ≤ sz')%CMP -> word_uincl (zero_extend sz w') w'.
Proof. by move=> ?;apply /andP. Qed.

Lemma word_uincl_zero_extR sz sz' (w: word sz) :
  (sz ≤ sz')%CMP →
  word_uincl w (zero_extend sz' w).
Proof.
  move => hle; apply /andP; split; first exact: hle.
  by rewrite zero_extend_idem // zero_extend_u.
Qed.
