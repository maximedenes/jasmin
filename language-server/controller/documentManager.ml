open Lsp.LspData
open Parsing
open Language

type state = {
  ast : Jasmin.Syntax.pprogram option;
  cst : Parsing.Syntax.Concrete.node option;
  parsing_diagnostics : Diagnostic.t list;
}

let range_of_lexpos startp endp =
  let open Lexing in
  let start = Position.{ line = startp.pos_lnum-1; character = startp.pos_cnum - startp.pos_bol; } in
  let end_ = Position.{ line = endp.pos_lnum-1; character = endp.pos_cnum - endp.pos_bol; } in
  Range.{ start; end_}

let dispenser_of_token_list l =
  let d = Seq.to_dispenser (List.to_seq l) in
  fun () -> Option.get (d ())

let pos_of_loc l =
  let open Lexing in
  let open Jasmin.Location in
  let pos_fname = l.loc_fname in
  let (pos_lnum_start, pos_char_start) = l.loc_start in
  let (pos_lnum_end, pos_char_end) = l.loc_end in
  let pos_bol_start = l.loc_bchar - pos_char_start in
  let pos_bol_end = l.loc_echar - pos_char_end in
  let startp = { pos_fname; pos_lnum = pos_lnum_start; pos_cnum = l.loc_bchar; pos_bol = pos_bol_start } in
  let endp = { pos_fname; pos_lnum = pos_lnum_end; pos_cnum = l.loc_echar; pos_bol = pos_bol_end } in
  (startp, endp)

let tokens_of_cst cst =
  Syntax.Concrete.fold_skip_errors (fun acc node -> match node.green.pl_desc with Terminal x -> let (startp,endp) = pos_of_loc node.green.pl_loc in (x, startp, endp) :: acc | _ -> acc) [] cst

let init ~fname ~text =
  let input = BatIO.input_string text in
  let cst, errors = Parse.parse_program ~fname input in
  let mk_diag ((startp, endp), explanations) =
    let range = range_of_lexpos startp endp in
    let items = List.map (fun e -> let (prod, i) = e.Parse.item in Parse.string_of_symbol @@ List.nth (Jasmin.Parser.MenhirInterpreter.rhs prod) i) explanations in
    let message = "Parse error. Expected " ^ String.concat "," items in
    Diagnostic.{ range; message; severity = Severity.Error }
  in
  let parsing_diagnostics = List.map mk_diag errors in
  let startp = Lexing.{
    pos_fname = fname;
    pos_lnum  = 1;
    pos_bol   = 0;
    pos_cnum  = 0
  }
  in
  let tokens = List.rev (tokens_of_cst cst) in
  Printf.eprintf "Generating AST from %d tokens\n" (List.length tokens);
  let ast = Jasmin.Parseio.parse_program_from_tokens startp (dispenser_of_token_list tokens) in
  Printf.eprintf "AST generated\n";
  { parsing_diagnostics; ast = Some ast; cst = Some cst }

let parsing_diagnostics st = st.parsing_diagnostics
let concrete_syntax_tree st = st.cst

let get_ast st = st.ast