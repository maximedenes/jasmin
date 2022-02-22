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

Require Import
  arch_params
  compiler_util
  expr
  psem
  psem_facts
  sem_one_varmap.
Require Import
  linearization
  linearization_proof
  stack_alloc
  stack_alloc_proof.
Require Import
  arch_decl
  arch_extra
  asm_gen
  asm_gen_proof.
Require Import
  arm_decl
  arm_extra
  arm_instr_decl
  arm_lowering
  arm_lowering_proof.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition default_opts : arith_opts :=
  {|
    args_size := reg_size;
    set_flags := false;
    is_conditional := false;
    has_shift := None;
  |}.


(* ------------------------------------------------------------------------ *)
(* Stack alloc parameters. *)

Definition addi x y ofs :=
  Copn [:: x ] AT_none (Oarm (ADDI default_opts)) [:: y; Pconst ofs ].

Definition arm_mov_ofs
  (x : lval) (_ : vptr_kind) (y : pexpr) (ofs : Z) : option instr_r :=
  Some (addi x y ofs).

Definition arm_saparams : stack_alloc_params :=
  {|
    sap_mov_ofs := arm_mov_ofs;
  |}.


(* ------------------------------------------------------------------------ *)
(* Linearization parameters. *)

Definition arm_allocate_stack_frame (rspi : var_i) (sz : Z) :=
  let rspg := Gvar rspi Slocal in
  ([:: Lvar rspi ], Oarm (ADDI default_opts), [:: Pvar rspg; Pconst sz ]).

Definition arm_free_stack_frame (rspi : var_i) (sz : Z) :=
  let rspg := Gvar rspi Slocal in
  ([:: Lvar rspi ], Oarm (ADDI default_opts), [:: Pvar rspg; Pconst (-sz) ]).

Definition arm_ensure_rsp_alignment (rspi : var_i) (al : wsize) :=
  let p0 := Pvar (Gvar rspi Slocal) in
  let p1 := Pconst (- wsize_size al) in
  ([:: Lvar rspi ], Oarm (ANDI default_opts), [:: p0; p1 ]).

Definition arm_lassign (x : lval) (ws : wsize) (e : pexpr) :=
  let opts :=
    {|
      args_size := ws;
      set_flags := false;
      is_conditional := false;
      has_shift := None;
    |}
  in
  ([:: x ], Oarm (MOV opts), [:: e ]).

Definition arm_liparams : linearization_params :=
  {|
    lip_tmp := "r0"%string;
    lip_allocate_stack_frame := arm_allocate_stack_frame;
    lip_free_stack_frame := arm_free_stack_frame;
    lip_ensure_rsp_alignment := arm_ensure_rsp_alignment;
    lip_lassign := arm_lassign;
  |}.


(* ------------------------------------------------------------------------ *)
(* Lowering parameters. *)

Definition arm_loparams : lowering_params fresh_vars lowering_options :=
  {|
    lop_lower_prog := arm_lower_prog;
    lop_fvars_correct := arm_fvars_correct;
  |}.


(* ------------------------------------------------------------------------ *)
(* Assembly generation parameters. *)

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

Definition arm_agparams : asm_gen_params :=
  {|
    agp_assemble_cond := assemble_cond;
  |}.


(* ------------------------------------------------------------------------ *)
(* Shared parameters. *)

Definition arm_is_move_op (o : asm_op_t) : bool :=
  match o with
  | BaseOp (None, MOV opts) =>
      [&& ~~ set_flags opts
        , ~~ is_conditional opts
        & ~~ has_shift opts
      ]

  | _ =>
      false
  end.

Definition arm_mov_op : arm_op :=
  MOV default_opts.

Definition arm_mov_eop : asm_op_t :=
  BaseOp (None, arm_mov_op).

Definition arm_params : architecture_params fresh_vars lowering_options :=
  {|
    ap_sap := arm_saparams;
    ap_lip := arm_liparams;
    ap_lop := arm_loparams;
    ap_agp := arm_agparams;
    ap_is_move_op := arm_is_move_op;
    ap_mov_op := arm_mov_op;
  |}.


(* ------------------------------------------------------------------------ *)
(* Stack alloc hypotheses. *)

Section STACK_ALLOC.

Context
  (P' : sprog)
  (P'_globs : p_globs P' = [::]).

Lemma addiP s1 e i x ofs w s2 :
  (Let i' := sem_pexpr [::] s1 e in to_pointer i') = ok i
  -> write_lval [::] x (Vword (i + wrepr _ ofs)) s1 = ok s2
  -> psem.sem_i P' w s1 (addi x e ofs) s2.
Proof.
  move=> he hx.
  apply psem.Eopn.
  rewrite /sem_sopn /=.
  rewrite P'_globs.
  rewrite /exec_sopn /=.
  move: he.
  t_xrbindP=> _ -> /= -> /=.
  by rewrite hx.
Qed.

End STACK_ALLOC.

Lemma arm_mov_ofsP (P': sprog) s1 e i x ofs w vpk s2 ins :
  p_globs P' = [::]
  -> (Let i' := sem_pexpr [::] s1 e in to_pointer i') = ok i
  -> sap_mov_ofs arm_saparams x vpk e ofs = Some ins
  -> write_lval [::] x (Vword (i + wrepr Uptr ofs)) s1 = ok s2
  -> psem.sem_i P' w s1 ins s2.
Proof.
  move=> P'_globs he.
  rewrite /arm_mov_ofs.
  move=> [<-].
  by apply addiP.
Qed.

Definition arm_hsaparams : h_stack_alloc_params (ap_sap arm_params) :=
  {|
    mov_ofsP := arm_mov_ofsP;
  |}.


(* ------------------------------------------------------------------------ *)
(* Linearization hypotheses. *)

Section LINEARIZATION.

Context
  (lp : lprog)
  (s : estate)
  (sp_rsp : Ident.ident)
  (ii : instr_info)
  (fn : funname)
  (pc : nat).

Let vrsp : var := mk_ptr sp_rsp.
Let vrspi : var_i := VarI vrsp xH.
Let vm := evm s.

Lemma arm_spec_lip_allocate_stack_frame ts sz :
  let args := lip_allocate_stack_frame arm_liparams (VarI vrsp xH) sz in
  let i := MkLI ii (Lopn args.1.1 args.1.2 args.2) in
  let ts' := pword_of_word (ts + wrepr Uptr sz) in
  let s' := with_vm s (vm.[vrsp <- ok ts'])%vmap in
  (vm.[vrsp])%vmap = ok (pword_of_word ts)
  -> eval_instr lp arm_mov_eop i (of_estate s fn pc)
     = ok (of_estate s' fn pc.+1).
Proof.
  move=> /= Hvm.
  rewrite /eval_instr /=.
  rewrite /sem_sopn /=.
  rewrite /get_gvar /get_var /on_vu /=.
  rewrite Hvm /=.
  rewrite pword_of_wordE.
  by rewrite zero_extend_u.
Qed.

Lemma arm_spec_lip_free_stack_frame ts sz :
  let args := lip_free_stack_frame arm_liparams (VarI vrsp xH) sz in
  let i := MkLI ii (Lopn args.1.1 args.1.2 args.2) in
  let ts' := pword_of_word (ts - wrepr Uptr sz) in
  let s' := with_vm s (vm.[vrsp <- ok ts'])%vmap in
  (vm.[vrsp])%vmap = ok (pword_of_word ts)
  -> eval_instr lp arm_mov_eop i (of_estate s fn pc)
     = ok (of_estate s' fn pc.+1).
Proof.
  move=> /= Hvm.
  rewrite /eval_instr /=.
  rewrite /sem_sopn /=.
  rewrite /get_gvar /get_var /on_vu /=.
  rewrite Hvm /=.
  rewrite pword_of_wordE.
  rewrite zero_extend_u.
  by rewrite wrepr_opp.
Qed.

Lemma arm_spec_lip_ensure_rsp_alignment ws ts' :
  let al := align_word ws ts' in
  let args := lip_ensure_rsp_alignment arm_liparams vrspi ws in
  let i := MkLI ii (Lopn args.1.1 args.1.2 args.2) in
  get_var (evm s) vrsp = ok (Vword ts')
  -> wf_vm (evm s)
  -> exists vm',
      [/\ eval_instr lp arm_mov_eop i (of_estate s fn pc)
          = ok (of_estate (with_vm s vm') fn pc.+1)
        , vm' = (evm s).[vrsp <- ok (pword_of_word al)]%vmap
              [\sv_of_flags rflags]
        , forall x,
            Sv.In x (sv_of_flags rflags)
            -> ~ is_ok (vm'.[x]%vmap)
            -> (evm s).[x]%vmap = vm'.[x]%vmap
        & wf_vm vm'
      ].
Proof.
  move=> /= Hvrsp Hwm1.
  rewrite /eval_instr /=.
  rewrite /sem_sopn /=.
  rewrite /get_gvar /=.
  rewrite Hvrsp /=.
  rewrite zero_extend_u pword_of_wordE.
  rewrite /with_vm /=.
  eexists.
  split.
  - reflexivity.
  - move=> x hin.
    rewrite !(@Fv.setP _ _ vrsp).
    case: (vrsp =P x).
    + move=> ?. by subst x.
    + done.
  - move=> x /sv_of_flagsP /mapP [f _ ->].
    by case f;
      repeat (rewrite Fv.setP_eq || rewrite Fv.setP_neq //).
  apply wf_vm_set.
  exact: Hwm1.
Qed.

Lemma arm_spec_lip_lassign (s1 s2 : estate) x e ws ws' (w : word ws) (w' : word ws') :
  let args := lip_lassign arm_liparams x ws e in
  let i := MkLI ii (Lopn args.1.1 args.1.2 args.2) in
  sem_pexpr [::] s1 e = ok (Vword w')
  -> truncate_word ws w' = ok w
  -> write_lval [::] x (Vword w) s1 = ok s2
  -> eval_instr lp arm_mov_eop i (of_estate s1 fn pc)
     = ok (of_estate s2 fn pc.+1).
Proof.
  move=> /= Hsem_pexpr Htruncate_word Hwrite_lval.
  rewrite /eval_instr /=.
  rewrite /sem_sopn /=.
  rewrite to_estate_of_estate.
  rewrite Hsem_pexpr /=.
  rewrite /exec_sopn /=.
  rewrite Htruncate_word /=.
  case: ws w Htruncate_word Hwrite_lval =>
    ws ble Hwrite_lval /=.
  1-3: by rewrite Hwrite_lval /=.
  - exact: TODO_ARM. (* x = (u64)e *)
  - exact: TODO_ARM. (* x = (u128)e *)
  - exact: TODO_ARM. (* x = (u256)e *)
Qed.

End LINEARIZATION.

Definition arm_hliparams :
  h_linearization_params arm_mov_op (ap_lip arm_params) :=
  {|
    spec_lip_allocate_stack_frame := arm_spec_lip_allocate_stack_frame;
    spec_lip_free_stack_frame := arm_spec_lip_free_stack_frame;
    spec_lip_ensure_rsp_alignment := arm_spec_lip_ensure_rsp_alignment;
    spec_lip_lassign := arm_spec_lip_lassign;
  |}.

Lemma arm_ok_lip_tmp :
  exists r : reg_t, of_string (lip_tmp (ap_lip arm_params)) = Some r.
Proof.
  exists R00.
  rewrite /=.
  change "r0"%string with (to_string R00).
  exact: to_stringK.
Qed.


(* ------------------------------------------------------------------------ *)
(* Lowering hypotheses. *)

Lemma arm_lower_callP
  (eft : eqType)
  (pT : progT eft)
  (sCP : semCallParams)
  (p : prog)
  (ev : extra_val_t)
  (options : lowering_options)
  (warning : instr_info -> warning_msg -> instr_info)
  (fv : fresh_vars)
  (is_var_in_memory : var_i -> bool)
  (_ : lop_fvars_correct arm_loparams fv (p_funcs p))
  (f : funname)
  (mem mem' : low_memory.mem)
  (va vr : seq value) :
  psem.sem_call p ev mem f va mem' vr
  -> let lprog :=
       lop_lower_prog
         arm_loparams
         options
         warning
         fv
         is_var_in_memory
         p
     in
     psem.sem_call lprog ev mem f va mem' vr.
Proof.
  exact: lower_callP.
Qed.

Definition arm_hloparams : h_lowering_params (ap_lop arm_params) :=
  {|
    hlop_lower_callP := arm_lower_callP;
  |}.


(* ------------------------------------------------------------------------ *)
(* Assembly generation hypotheses. *)

Section ASM_GEN.

(* FIXME: Is there a way of avoiding this import? *)
Import arch_sem.

Lemma arm_eval_assemble_cond ii m rf e c v :
  eqflags m rf
  -> agp_assemble_cond arm_agparams ii e = ok c
  -> sem_pexpr [::] m e = ok v
  -> let get x :=
       if rf x is Def b
       then ok b
       else undef_error
    in
    exists2 v',
      value_of_bool (eval_cond get c) = ok v' & value_uincl v v'.
Proof.
  rewrite /arm_agparams /eval_cond /=.
  case: e => //=.
  move=> x eqf.
  t_xrbindP=> r ok_r ok_c.
  move=> ok_v.
  have := gxgetflag_ex eqf ok_r ok_v.
  clear ok_r ok_v.
  case: r ok_c => -[<-] hr /=.
  all: eexists; last exact: hr.
  all: by case: (rf _).
Qed.

Lemma arm_assemble_extra_op rip ii op lvs args op' lvs' args' op'' asm_args m m' s :
  sem_sopn [::] (Oasm (ExtOp op)) m lvs args = ok m'
  -> to_asm ii op lvs args = ok (op', lvs', args')
  -> assemble_asm_op arm_agparams rip ii op' lvs' args'
     = ok (op'', asm_args)
  -> lom_eqv rip m s
  -> exists2 s', eval_op op'' asm_args s = ok s' & lom_eqv rip m' s'.
Proof. by case: op. Qed.

Definition arm_hagparams : h_asm_gen_params (ap_agp arm_params) :=
  {|
    hagp_eval_assemble_cond := arm_eval_assemble_cond;
    hagp_assemble_extra_op := arm_assemble_extra_op;
  |}.

End ASM_GEN.


(* ------------------------------------------------------------------------ *)
(* Shared hypotheses. *)

Definition arm_is_move_opP op vx v :
  ap_is_move_op arm_params op
  -> exec_sopn (Oasm op) [:: vx ] = ok v
  -> List.Forall2 value_uincl v [:: vx ].
Proof.
  case: op => //.
  move=> [[]] //.
  move=> [] //.
  move=> [ws [] [] [?|]] /andP [] //= le_ws_32 _.
  rewrite /exec_sopn /=.
  t_xrbindP=> w w'.
  move=> hvx.
  have [ws' [w'' [le_ws_ws' -> ->]]] := to_wordI hvx.
  rewrite /sopn_sem /=.
  rewrite /drop_semi_nzcv /=.
  rewrite /arm_MOV_semi /=.
  rewrite /nzcvw_of_aluop /=.
  t_xrbindP=> _ _ _ _ _ _ <- [<-] [<-] [<-] [<-] <-.
  apply List.Forall2_cons; last done.
  exact: word_uincl_zero_ext le_ws_ws'.
Qed.

Definition arm_exec_sopn_mov_op (w : word Uptr) :
  let op := Oasm (BaseOp (None, ap_mov_op arm_params)) in
  exec_sopn op [:: Vword w ] = ok [:: Vword w ].
Proof.
  by rewrite /exec_sopn /= zero_extend_u.
Qed.


(* ------------------------------------------------------------------------ *)

Definition arm_h_params : h_architecture_params arm_params :=
  {|
    hap_hsap := arm_hsaparams;
    hap_hlip := arm_hliparams;
    ok_lip_tmp := arm_ok_lip_tmp;
    hap_hlop := arm_hloparams;
    hap_hagp := arm_hagparams;
    hap_is_move_opP := arm_is_move_opP;
    exec_sopn_mov_op := arm_exec_sopn_mov_op;
  |}.
