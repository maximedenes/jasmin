open Base
open Controller
open Language
open Lsp
open LspData

let uri = Uri.make ~scheme:"file" ~path:"test_file.jazz" ()

let %test_unit "diagnostics: parsing error is detected" =
  let text = "fn foo(reg u64 bar) -> reg u64 { reg u4 r; return r; }" in
  let doc = DocumentManager.init uri ~text in
  let parse_diags = DocumentManager.parsing_diagnostics doc in
  [%test_eq: int] (List.length parse_diags) 1

let %test_unit "diagnostics: typing error is detected" =
  let text = "fn foo(reg u64 bar) -> reg u32 { reg u64 r; return r; }" in
  let doc = DocumentManager.init uri ~text in
  let get_ast uri' = if Uri.equal uri uri' then DocumentManager.get_ast doc else None in
  let diags,_,_,_ = Typing.type_program get_ast uri in
  let diags = UriMap.find_opt uri diags in
  [%test_eq: int option] (Option.map diags ~f:List.length) (Some 1)

let %test_unit "diagnostics: errors are combined correctly" =
  let text = "fn foo(reg u64 bar) -> reg u32 { reg u64 r; reg baz; return r; }" in
  let workspace = ref Workspace.empty_workspace in
  for i = 1 to 2 do
  workspace := Workspace.open_document !workspace uri ~text;
  let diags = Workspace.get_diagnostics !workspace in
  [%test_eq: int] (List.length (UriMap.bindings diags)) 1;
  let diags = UriMap.find_opt uri diags in
  [%test_eq: int option] (Option.map diags ~f:List.length) (Some 2)
  done

let %test_unit "diagnostics: parsing errors are resolved correctly" =
  let text = "fn foo(reg u64 bar) -> reg u32 { reg u64 r; reg baz; return r; }" in
  let workspace = Workspace.empty_workspace in
  let workspace = Workspace.open_document workspace uri ~text in
  let text = "fn foo(reg u64 bar) -> reg u32 { reg u64 r; reg u64 baz; return r; }" in
  let workspace = Workspace.open_document workspace uri ~text in
  let diags = Workspace.get_diagnostics workspace in
  [%test_eq: int] (List.length (UriMap.bindings diags)) 1;
  let diags = UriMap.find_opt uri diags in
  [%test_eq: int option] (Option.map diags ~f:List.length) (Some 1)

let %test_unit "diagnostics: typing errors are resolved correctly" =
  let text = "fn foo(reg u64 bar) -> reg u32 { reg u64 r; reg baz; return r; }" in
  let workspace = Workspace.empty_workspace in
  let workspace = Workspace.open_document workspace uri ~text in
  let text = "fn foo(reg u64 bar) -> reg u64 { reg u64 r; reg baz; return r; }" in
  let workspace = Workspace.open_document workspace uri ~text in
  let diags = Workspace.get_diagnostics workspace in
  [%test_eq: int] (List.length (UriMap.bindings diags)) 1;
  let diags = UriMap.find_opt uri diags in
  [%test_eq: int option] (Option.map diags ~f:List.length) (Some 1)

let %test_unit "diagnostics: all errors are resolved correctly" =
  let text = "fn foo(reg u64 bar) -> reg u32 { reg u64 r; reg baz; return r; }" in
  let workspace = Workspace.empty_workspace in
  let workspace = Workspace.open_document workspace uri ~text in
  let text = "fn foo(reg u64 bar) -> reg u64 { reg u64 r; reg u64 baz; return r; }" in
  let workspace = Workspace.open_document workspace uri ~text in
  let diags = Workspace.get_diagnostics workspace in
  [%test_eq: int] (List.length (UriMap.bindings diags)) 1;
  let diags = UriMap.find_opt uri diags in
  [%test_eq: int option] (Option.map diags ~f:List.length) (Some 0)