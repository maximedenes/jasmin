open Jasmin

module Arch =
  (val let use_set0 = true and use_lea = true in
       let call_conv = Glob_options.Linux in
       let module C : Arch_full.Core_arch =
         (val CoreArchFactory.core_arch_x86 ~use_lea ~use_set0 call_conv)
       in
       (module Arch_full.Arch_from_Core_arch (C) : Arch_full.Arch))

let load_file name =
  let open Pretyping in
  try
    name
    |> tt_file Arch.reg_size Arch.asmOp_sopn Env.empty None None
    |> fst |> Env.decls
    |> Compile.preprocess Arch.reg_size Arch.asmOp
  with TyError (loc, e) ->
    Format.eprintf "%a: %a@." Location.pp_loc loc pp_tyerror e;
    assert false
