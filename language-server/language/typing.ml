open Lsp
open LspData

module type ArchCoreWithAnalyze = sig
  open Jasmin.Prog
  module C : Jasmin.Arch_full.Core_arch
  val analyze :
    (C.reg, C.regx, C.xreg, C.rflag, C.cond, C.asm_op, C.extra_op) Jasmin.Arch_extra.extended_op Jasmin.Sopn.asmOp ->
    (unit, (C.reg, C.regx, C.xreg, C.rflag, C.cond, C.asm_op, C.extra_op) Jasmin.Arch_extra.extended_op) func ->
    (unit, (C.reg, C.regx, C.xreg, C.rflag, C.cond, C.asm_op, C.extra_op) Jasmin.Arch_extra.extended_op) func ->
    (unit, (C.reg, C.regx, C.xreg, C.rflag, C.cond, C.asm_op, C.extra_op) Jasmin.Arch_extra.extended_op) prog -> unit
end

open Jasmin.Pretyping

type global_env =
  GlobEnv : 'asm Jasmin.Pretyping.Env.env -> global_env

type program =
  Program : ('asm, 'info) Jasmin.Prog.pprog -> program

type typing_result = {
  diagnostics : Diagnostic.t list PathMap.t;
  references : References.reference_map;
  global_env : global_env;
  program : program option;
  revdeps : string PathMap.t;
}

let push_diag fname diag diagnostics =
  let update = function None -> Some [diag] | Some l -> Some (diag::l) in
  PathMap.update fname update diagnostics

let rec type_item get_ast pd asmOp (env, diagnostics, revdeps) pt ~root_fname =
  let check pt =
    match Jasmin.Location.unloc pt with
    | S.PParam  pp -> tt_param  pd env (L.loc pt) pp, diagnostics, revdeps
    | S.PFundef pf -> tt_fundef pd asmOp env (L.loc pt) pf, diagnostics, revdeps
    | S.PGlobal pg -> tt_global pd env (L.loc pt) pg, diagnostics, revdeps
    | S.Pexec   pf ->
      Env.Exec.push (L.loc pt) (fst (tt_fun env pf.pex_name)).P.f_name pf.pex_mem env, diagnostics, revdeps
    | S.Prequire (from, fs) -> 
      List.fold_left (fun acc req -> type_file_loc get_ast pd asmOp from acc ~root_fname req) (env, diagnostics, revdeps) fs
  in
  try
    check pt
  with
  | Jasmin.Pretyping.TyError (loc, code) ->
    let range = Range.of_jasmin_loc loc in
    let buf = Buffer.create 128 in
    let fmt = Format.formatter_of_buffer buf in
    Jasmin.Pretyping.pp_tyerror fmt code;
    Format.pp_print_flush fmt ();
    let message = Buffer.contents buf in
    let diag = Diagnostic.{ range; message; severity = Severity.Error } in
    let diagnostics = push_diag loc.loc_fname diag diagnostics in
    (env, diagnostics, revdeps)

and type_file_loc get_ast pd asmOp from env ~root_fname req =
  let loc = L.loc req in
  let fname = L.unloc req in
  fst (type_file get_ast pd asmOp env from (Some loc) ~root_fname ~fname)

and type_file get_ast pd asmOp (env, diagnostics, revdeps) from loc ~root_fname ~fname =
  match Env.enter_file env from loc fname with
  | None -> (env, diagnostics, revdeps), [] (* already checked *)
  | Some(env, fname) ->
    let revdeps = PathMap.add fname root_fname revdeps in
    try
      let ast = match get_ast ~fname with (* FIXME add parsing diags here *)
        | None ->
          let ast = Jasmin.Parseio.parse_program ~name:fname in (* FIXME catch parsing errors *)
          BatFile.with_file_in fname ast
        | Some ast -> ast
      in
      let diagnostics = PathMap.add fname [] diagnostics in
      let (env, diagnostics, revdeps) = List.fold_left (type_item get_ast pd asmOp ~root_fname) (env, diagnostics, revdeps) ast in
      (Env.exit_file env, diagnostics, revdeps), ast
    with Sys_error message ->
      let diagnostics = match loc with
      | None -> diagnostics
      | Some loc ->
        let fname = loc.loc_fname in
        let range = Range.of_jasmin_loc loc in
        let diag = Diagnostic.{ range; message; severity = Severity.Error } in
        push_diag fname diag diagnostics
      in
      (Env.exit_file env, diagnostics, revdeps), []

let type_program get_ast ~fname target_arch =
  let (module P : ArchCoreWithAnalyze) =
    match target_arch with
    | Jasmin.Glob_options.X86_64 ->
       (module struct
          module C = (val Jasmin.CoreArchFactory.core_arch_x86 ~use_lea:!Jasmin.Glob_options.lea ~use_set0:!Jasmin.Glob_options.set0 !Jasmin.Glob_options.call_conv)
          let analyze _ _ = assert false
        end)
    | ARM_M4 ->
       (module struct
          module C = Jasmin.CoreArchFactory.Core_arch_ARM
          let analyze _ _ = assert false
        end)
  in
  let module Arch = Jasmin.Arch_full.Arch_from_Core_arch (P.C) in
  let env =
    List.fold_left Jasmin.Pretyping.Env.add_from Jasmin.Pretyping.Env.empty
      !Jasmin.Glob_options.idirs (* FIXME do not rely on glob options *)
  in
  let diagnostics = PathMap.singleton fname [] in
  let revdeps = PathMap.empty in
  let (env, diagnostics, revdeps), ast = type_file get_ast Arch.reg_size Arch.asmOp_sopn (env, diagnostics, revdeps) None None ~root_fname:fname ~fname in
  let pprog = Jasmin.Pretyping.Env.decls env in
  let references = References.collect_references pprog in (* FIXME do this analysis on ast, before typing *)
  begin try
    let _prog = Jasmin.Compile.preprocess Arch.reg_size Arch.asmOp pprog in
    {
      diagnostics;
      references;
      global_env = GlobEnv env;
      program = Some (Program pprog);
      revdeps;
    }
  with Jasmin.Typing.TyError(loc, message) ->
    let range = Range.of_jasmin_loc loc.base_loc in
    let fname = loc.base_loc.loc_fname in
    let diag = Diagnostic.{ range; message; severity = Severity.Error } in
    let diagnostics = PathMap.singleton fname [diag] in
    {
      diagnostics;
      references;
      global_env = GlobEnv env;
      program = None;
      revdeps;
    }
  end

let find_definition ~fname global_env references pos =
  let GlobEnv env = global_env in
  References.find_definition env references ~fname pos