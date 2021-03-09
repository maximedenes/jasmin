From mathcomp Require Import all_ssreflect all_algebra.
Require Export arch_to_expr compiler_util lea.
Import Utf8 String.
Import all_ssreflect.
Import oseq xseq expr. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ASMEXPR.

Context `{asm_e : asm_extra}.

Section ToString.

Context `{tS : ToString}.

Definition invalid_name (s: string) : asm_error :=
  AsmErr_string ("Invalid " ++ category ++ " name: " ++ s) None.

Definition of_var_e ii (v: var) :=
  match of_var v with
  | Some r => ok r
  | None => 
    let s := 
      if vtype v == rtype then ("Invalid type variable for " ++ category)%string
      else ("Invalid variable name for " ++ category ++ ": " ++ vname v)%string in
    cierror ii (Cerr_assembler (AsmErr_string s None))
  end.

Lemma of_var_eP ii v r : 
  of_var_e ii v = ok r -> of_var v = Some r.
Proof. by rewrite /of_var_e; case: of_var => // ? [<-]. Qed.

Lemma of_var_eI ii v r : of_var_e ii v = ok r -> to_var r = v.
Proof. by move => /of_var_eP; apply/of_varI. Qed.

Lemma inj_of_var_e ii v1 v2 r:
  of_var_e ii v1 = ok r -> of_var_e ii v2 = ok r -> v1 = v2.
Proof. by move => /of_var_eP h1 /of_var_eP; apply: inj_of_var. Qed.

End ToString.

Definition to_reg   v : option reg_t   := of_var v.
Definition to_xreg  v : option xreg_t  := of_var v.
Definition to_rflag v : option rflag_t := of_var v.

(* -------------------------------------------------------------------- *)
Variant compiled_variable :=
| LReg   of reg_t
| LXReg  of xreg_t
| LRFlag of rflag_t
.

Definition compiled_variable_beq cv1 cv2 := 
  match cv1, cv2 with
  | LReg   r1, LReg   r2 => r1 == r2 ::>
  | LXReg  r1, LXReg  r2 => r1 == r2 ::>
  | LRFlag r1, LRFlag r2 => r1 == r2 ::>
  | _, _ => false
  end.

Lemma compiled_variable_eq_axiom : Equality.axiom compiled_variable_beq.
Proof.
  move=> [r1 | x1 | f1] [r2 | x2 | f2] /=; 
    (by constructor || by apply:(iffP idP) => [ /eqP -> | [->] ]).
Qed.

Definition compiled_variable_eqMixin     := Equality.Mixin compiled_variable_eq_axiom.
Canonical  compiled_variable_eqType      := Eval hnf in EqType compiled_variable compiled_variable_eqMixin.

Definition compile_var (v: var) : option compiled_variable :=
  match to_reg v with
  | Some r => Some (LReg r)
  | None =>
  match to_xreg v with
  | Some r => Some (LXReg r)
  | None =>
  match to_rflag v with
  | Some f => Some (LRFlag f)
  | None => None
  end end end.

Lemma compile_varI x cv :
  compile_var x = Some cv →
  match cv with
  | LReg   r => to_var r = x
  | LXReg  r => to_var r = x
  | LRFlag r => to_var r = x
  end.
Proof.
  rewrite /compile_var /to_reg /to_xreg /to_rflag.
  case heqr: (of_var x) => [ r | ].
  + by move=> [<-]; apply: of_varI.
  case heqx: (of_var x) => [ r | ].
  + by move=> [<-]; apply: of_varI.
  case heqf: (of_var x) => [ r | //].
  by move=> [<-]; apply: of_varI.
Qed.

(* -------------------------------------------------------------------- *)
(* Compilation of pexprs                                                *)
(* -------------------------------------------------------------------- *)


(* -------------------------------------------------------------------- *)
(* FIXME ARM : this should be a field of arch_decl ? *)
(*
Definition assemble_cond ii (e: pexpr) : ciexec condt :=
  match e with
  | Pvar v =>
    Let r := rflag_of_var ii v.(gv) in
    match r with
    | OF => ok O_ct
    | CF => ok B_ct
    | ZF => ok E_ct
    | SF => ok S_ct
    | PF => ok P_ct
    | DF => cierror ii (Cerr_assembler (AsmErr_string "Cannot branch on DF" None))
    end

  | Papp1 Onot (Pvar v) =>
    Let r := rflag_of_var ii v.(gv) in
    match r with
    | OF => ok NO_ct
    | CF => ok NB_ct
    | ZF => ok NE_ct
    | SF => ok NS_ct
    | PF => ok NP_ct
    | DF => cierror ii (Cerr_assembler (AsmErr_string "Cannot branch on ~~ DF" None))
    end

  | Papp2 Oor (Pvar vcf) (Pvar vzf) =>
    Let rcf := rflag_of_var ii vcf.(gv) in
    Let rzf := rflag_of_var ii vzf.(gv) in
    if ((rcf == CF) && (rzf == ZF)) then
      ok BE_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (BE)" None))

  | Papp2 Oand (Papp1 Onot (Pvar vcf)) (Papp1 Onot (Pvar vzf)) =>
    Let rcf := rflag_of_var ii vcf.(gv) in
    Let rzf := rflag_of_var ii vzf.(gv) in
    if ((rcf == CF) && (rzf == ZF)) then
      ok NBE_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (NBE)" None))

  | Pif _ (Pvar vsf) (Papp1 Onot (Pvar vof1)) (Pvar vof2) =>
    Let rsf := rflag_of_var ii vsf.(gv) in
    Let rof1 := rflag_of_var ii vof1.(gv) in
    Let rof2 := rflag_of_var ii vof2.(gv) in
    if ((rsf == SF) && (rof1 == OF) && (rof2 == OF)) then
      ok L_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (L)" None))

  | Pif _ (Pvar vsf) (Pvar vof1) (Papp1 Onot (Pvar vof2)) =>
    Let rsf := rflag_of_var ii vsf.(gv) in
    Let rof1 := rflag_of_var ii vof1.(gv) in
    Let rof2 := rflag_of_var ii vof2.(gv) in
    if ((rsf == SF) && (rof1 == OF) && (rof2 == OF)) then
      ok NL_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (NL)" None))

  | Papp2 Oor (Pvar vzf)
          (Pif _ (Pvar vsf) (Papp1 Onot (Pvar vof1)) (Pvar vof2)) =>
    Let rzf := rflag_of_var ii vzf.(gv) in
    Let rsf := rflag_of_var ii vsf.(gv) in
    Let rof1 := rflag_of_var ii vof1.(gv) in
    Let rof2 := rflag_of_var ii vof2.(gv) in
    if ((rzf == ZF) && (rsf == SF) && (rof1 == OF) && (rof2 == OF)) then
      ok LE_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (LE)" None))

  | Papp2 Oand
             (Papp1 Onot (Pvar vzf))
             (Pif _ (Pvar vsf) (Pvar vof1) (Papp1 Onot (Pvar vof2))) =>
    Let rzf := rflag_of_var ii vzf.(gv) in
    Let rsf := rflag_of_var ii vsf.(gv) in
    Let rof1 := rflag_of_var ii vof1.(gv) in
    Let rof2 := rflag_of_var ii vof2.(gv) in
    if ((rzf == ZF) && (rsf == SF) && (rof1 == OF) && (rof2 == OF)) then
      ok NLE_ct
    else cierror ii (Cerr_assembler (AsmErr_string "Invalid condition (NLE)" None))

  | _ => cierror ii (Cerr_assembler (AsmErr_cond e))
  end.

*)

Context (assemble_cond : instr_info -> pexpr -> ciexec cond_t).

(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
(* FIXME: ARM this should be rewritten *)
Definition scale_of_z' ii (z:pointer) : ciexec nat:=
  match wunsigned z return ciexec nat with
  | 1 => ok O
  | 2 => ok 0.+1
  | 4 => ok 1.+1
  | 8 => ok 2.+1
  | _ => cierror ii (Cerr_assembler (AsmErr_string "invalid scale" None))
  end%Z.

Definition reg_of_ovar ii (x:option var_i) : ciexec (option reg_t) := 
  match x with 
  | Some x => 
    Let r := of_var_e ii x in
    ok (Some r)
  | None =>
    ok None
  end.

Definition assemble_lea ii lea := 
  Let base := reg_of_ovar ii lea.(lea_base) in
  Let offset := reg_of_ovar ii lea.(lea_offset) in
  Let scale := scale_of_z' ii lea.(lea_scale) in
  ok (Areg {|
      ad_disp := lea.(lea_disp);
      ad_base := base;
      ad_scale := scale;
      ad_offset := offset 
    |}).

Definition addr_of_pexpr (rip:var) ii sz (e: pexpr) := 
  match lea.mk_lea sz e with
  | Some lea => 
     match lea.(lea_base) with
     | Some r =>
        if r.(v_var) == rip then
          Let _ := assert (lea.(lea_offset) == None) 
            (ii, Cerr_assembler (AsmErr_string "Invalid global address" (Some e))) in
           ok (Arip lea.(lea_disp))
        else assemble_lea ii lea
      | None => 
        assemble_lea ii lea
      end 
  | None => cierror ii (Cerr_assembler (AsmErr_string "lea: not able to assemble address" (Some e)))
  end.

Definition addr_of_xpexpr rip ii sz v e :=
  addr_of_pexpr rip ii sz (Papp2 (Oadd (Op_w sz)) (Plvar v) e).

Definition xreg_of_var ii (x: var) : ciexec asm_arg :=
  if to_xreg x is Some r then ok (XReg r)
  else if to_reg x is Some r then ok (Reg r)
  else cierror ii (Cerr_assembler (AsmErr_string "Not a (x)register" None)).

Definition assemble_word_load rip ii (sz:wsize) max_imm (e:pexpr) :=
  match e with
  | Papp1 (Oword_of_int sz') (Pconst z) =>
    match max_imm with
    | None =>  cierror ii (Cerr_assembler (AsmErr_string "Invalid pexpr for oprd, constant not allowed" (Some e)))
    | Some sz1 =>
      let w := wrepr sz1 z in
      let w1 := sign_extend sz w in
      let w2 := zero_extend sz (wrepr sz' z) in
      Let _ := assert (w1 == w2)
                (ii, Cerr_assembler (AsmErr_string "Invalid pexpr for oprd: out of bound constant" (Some e))) in
      ciok (Imm w)
    end
  | Pvar x =>
    Let _ := assert (is_lvar x)
              (ii, Cerr_assembler (AsmErr_string "Global variables remain" (Some e))) in
    let x := x.(gv) in
    xreg_of_var ii x
  | Pload sz' v e' =>
    if (sz == sz') then
      Let w := addr_of_xpexpr rip ii Uptr v e' in
      ok (Adr w)
    else
      cierror ii (Cerr_assembler (AsmErr_string "Invalid pexpr for word: invalid Load size" (Some e)))
  | _ => cierror ii (Cerr_assembler (AsmErr_string "Invalid pexpr for word" (Some e)))
  end.

Definition assemble_word (k:adr_kind) rip ii (sz:wsize) max_imm (e:pexpr) :=
  match k with
  | Load => assemble_word_load rip ii (sz:wsize) max_imm (e:pexpr)
  | Compute ws => 
    Let w := addr_of_pexpr rip ii ws e in
    ok (Adr w)
  end.

Definition arg_of_pexpr (k:adr_kind) rip ii (ty:stype) max_imm (e:pexpr) :=
  match ty with
  | sbool => Let c := assemble_cond ii e in ok (Condt c)
  | sword sz => assemble_word k rip ii sz max_imm e
  | sint  => cierror ii (Cerr_assembler (AsmErr_string "sint ???" (Some e)))
  | sarr _ => cierror ii (Cerr_assembler (AsmErr_string "sarr ???" (Some e)))
  end.

Definition pexpr_of_lval ii (lv:lval) : ciexec pexpr :=
  match lv with
  | Lvar x    => ok (Plvar x)
  | Lmem s x e  => ok (Pload s x e)
  | Lnone _ _
  | Laset _ _ _ _ 
  | Lasub _ _ _ _ _ => cierror ii (Cerr_assembler (AsmErr_string "pexpr_of_lval" None))
  end.

Definition nmap (T:Type) := nat -> option T.
Definition nget (T:Type) (m:nmap T) (n:nat) := m n.
Definition nset (T:Type) (m:nmap T) (n:nat) (t:T) :=
  fun x => if x == n then Some t else nget m x.
Definition nempty (T:Type) := fun n:nat => @None T.

Import arch_decl.
Definition var_of_implicit i :=
  match i with
  | IArflag f => to_var f
  | IAreg r   => to_var r
  end.

Definition compile_arg rip ii max_imm (ade: (arg_desc * stype) * pexpr) (m: nmap asm_arg) : ciexec (nmap asm_arg) :=
  let ad := ade.1 in
  let e := ade.2 in
  match ad.1 with
  | ADImplicit i =>
    Let _ :=
      assert (eq_expr (Plvar (VarI (var_of_implicit i) xH)) e)
             (ii, Cerr_assembler (AsmErr_string "compile_arg : bad implicit" (Some e))) in
    ok m
  | ADExplicit k n o =>
    Let a := arg_of_pexpr k rip ii ad.2 max_imm e in
    Let _ :=
      assert (check_oreg o a)
             (ii, Cerr_assembler (AsmErr_string "compile_arg : bad forced register" (Some e))) in
    match nget m n with
    | None => ok (nset m n a)
    | Some a' =>
      if a == a' then ok m
      else cierror ii (Cerr_assembler (AsmErr_string "compile_arg : not compatible asm_arg" (Some e)))
    end
  end.

Definition compile_args rip ii max_imm adts (es:pexprs) (m: nmap asm_arg) :=
  foldM (compile_arg rip ii max_imm) m (zip adts es).

Definition compat_imm ty a' a := 
  (a == a') || match ty, a, a' with
             | sword sz, Imm sz1 w1, Imm sz2 w2 => sign_extend sz w1 == sign_extend sz w2
             | _, _, _ => false
             end.
                
Definition check_sopn_arg rip ii max_imm (loargs : seq asm_arg) (x : pexpr) (adt : arg_desc * stype) :=
  match adt.1 with
  | ADImplicit i => eq_expr x (Plvar (VarI (var_of_implicit i) xH))
  | ADExplicit k n o =>
    match onth loargs n with
    | Some a =>
      if arg_of_pexpr k rip ii adt.2 max_imm x is Ok a' then compat_imm adt.2 a a' && check_oreg o a
      else false
    | None => false
    end
  end.

Definition check_sopn_dest rip ii max_imm (loargs : seq asm_arg) (x : pexpr) (adt : arg_desc * stype) :=
  match adt.1 with
  | ADImplicit i => eq_expr x (Plvar (VarI (var_of_implicit i) xH))
  | ADExplicit _ n o =>
    match onth loargs n with
    | Some a =>
      if arg_of_pexpr Load rip ii adt.2 max_imm x is Ok a' then (a == a') && check_oreg o a
      else false
    | None => false
    end
  end.

Definition error_imm :=
 Cerr_assembler (AsmErr_string "Invalid asm: cannot truncate the immediate to a 32 bits immediate, move it to a register first" None).

Definition assemble_x86_opn_aux rip ii op (outx : lvals) (inx : pexprs) :=
  let id := instr_desc op in
  let max_imm := id.(id_max_imm) in
  Let m := compile_args rip ii max_imm (zip id.(id_in) id.(id_tin)) inx (nempty _) in
  Let eoutx := mapM (pexpr_of_lval ii) outx in
  Let m := compile_args rip ii max_imm (zip id.(id_out) id.(id_tout)) eoutx m in
  match oseq.omap (nget m) (iota 0 id.(id_nargs)) with
  | None => cierror ii (Cerr_assembler (AsmErr_string "compile_arg : assert false nget" None))
  | Some asm_args =>
(*
    FIXME ARM
      (* This should allows to fix the problem with "MOV addr (IMM U64 w)" *)
      Let asm_args := 
        match op, asm_args with
        | MOV U64, [:: Adr a; Imm U64 w] =>
          match truncate_word U32 w with
          | Ok w' => 
            Let _ := assert (sign_extend U64 w' == w) (ii, error_imm) in
            ok [::Adr a; Imm w']
          | _ => cierror ii error_imm 
          end
        | _, _ => ok asm_args 
        end in
*)
      ok asm_args
  end.

Definition check_sopn_args rip ii max_imm (loargs : seq asm_arg) (xs : seq pexpr) (adt : seq (arg_desc * stype)) :=
  all2 (check_sopn_arg rip ii max_imm loargs) xs adt.

Definition check_sopn_dests rip ii max_imm (loargs : seq asm_arg) (outx : seq lval) (adt : seq (arg_desc * stype)) :=
  match mapM (pexpr_of_lval ii) outx with
  | Ok eoutx => all2 (check_sopn_dest rip ii max_imm loargs) eoutx adt
  | _  => false
  end.

(*
Definition is_lea ii op (outx : lvals) (inx : pexprs) := 
  match op, outx, inx with
  | LEA sz, [:: Lvar x], [:: e] => ok (Some (sz, x, e))
  | LEA _, _, _ => cierror ii (Cerr_assembler (AsmErr_string "lea: invalid lea instruction" None))
  | _, _, _ => ok None
  end.
*)
Definition assemble_op rip ii op (outx : lvals) (inx : pexprs) := 
 (* Let is_lea := is_lea ii op outx inx in
  match is_lea with
  | Some (sz, x, e) =>
    Let r := of_var_e ii x.(v_var) in 
    Let adr := addr_of_pexpr rip ii sz e in
    ok (LEA sz, [::Reg r; Adr adr])

  | None => *)
    let id := instr_desc op in
    let max_imm := id.(id_max_imm) in
    Let asm_args := assemble_x86_opn_aux rip ii op outx inx in
    let s := id.(id_str_jas) tt in
    Let _ := assert (id_check id asm_args) 
       (ii, Cerr_assembler (AsmErr_string ("assemble_x86_opn : invalid instruction (check) " ++ s) None)) in
    Let _ := assert (check_sopn_args rip ii max_imm asm_args inx (zip id.(id_in) id.(id_tin)) &&
                     check_sopn_dests rip ii max_imm asm_args outx (zip id.(id_out) id.(id_tout)))
       (ii, Cerr_assembler (AsmErr_string "assemble_x86_opn: cannot check, please repport" None)) in
    ok (op, asm_args).
 (* end. *)

Definition assemble_sopn rip ii op (outx : lvals) (inx : pexprs) :=
  match op with
  | arch_to_expr.AsmOp op => assemble_op rip ii op outx inx
  | ExtOp op => 
    match to_asm op with 
    | Some op => assemble_op rip ii op outx inx
    | None    =>  cierror ii (Cerr_assembler (AsmErr_string "assemble_sopn : invalid op" None))
    end
  end.
 
End ASMEXPR.
