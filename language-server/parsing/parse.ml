module L = MenhirLib.LexerUtil
module E = MenhirLib.ErrorReports

module P = Jasmin.Parser

module I = P.MenhirInterpreter

type token = Jasmin.Parser.token =
  | WHILE
  | UNDERSCORE
  | T_U8
  | T_U64
  | T_U32
  | T_U256
  | T_U16
  | T_U128
  | T_INT
  | T_BOOL
  | TRUE
  | TO
  | SWSIZE of (Jasmin.Syntax.swsize) [@printer fun fmt _ -> fprintf fmt "SWSIZE"]
  | SVSIZE of (Jasmin.Syntax.svsize) [@printer fun fmt _ -> fprintf fmt "SVSIZE"]
  | STRING of (string)
  | STAR
  | STACK
  | SLASH
  | SHARP
  | SEMICOLON
  | RPAREN
  | ROR
  | ROL
  | RETURN
  | REQUIRE
  | REG
  | RBRACKET
  | RBRACE
  | RARROW
  | QUESTIONMARK
  | POINTER
  | PLUS
  | PIPEPIPE
  | PIPE
  | PERCENT
  | PARAM
  | NID of (string)
  | MUTABLE
  | MINUS
  | LTLT
  | LT of (Jasmin.Syntax.sign) [@printer fun fmt _ -> fprintf fmt "LT"]
  | LPAREN
  | LE of (Jasmin.Syntax.sign) [@printer fun fmt _ -> fprintf fmt "LE"]
  | LBRACKET
  | LBRACE
  | INT of (Z.t) [@printer fun fmt _ -> fprintf fmt "INT"] 
  | INLINE
  | IF
  | HAT
  | GTGT of (Jasmin.Syntax.sign) [@printer fun fmt _ -> fprintf fmt "GTGT"]
  | GT of (Jasmin.Syntax.sign) [@printer fun fmt _ -> fprintf fmt "GT"]
  | GLOBAL
  | GE of (Jasmin.Syntax.sign) [@printer fun fmt _ -> fprintf fmt "GE"]
  | FROM
  | FOR
  | FN
  | FALSE
  | EXPORT
  | EXEC
  | EQEQ
  | EQ
  | EOF
  | ELSE
  | DOWNTO
  | DOT
  | CONSTANT
  | COMMA
  | COLON
  | BANGEQ
  | BANG
  | ARRAYINIT
  | AMPAMP
  | AMP
[@@deriving show]

let terminal2token (type a) (symbol : a Jasmin.Parser.MenhirInterpreter.terminal) =
  let open Jasmin.Parser in
  match symbol with
| MenhirInterpreter.T_error -> assert false
| MenhirInterpreter.T_WHILE -> WHILE
| MenhirInterpreter.T_UNDERSCORE -> UNDERSCORE
| MenhirInterpreter.T_T_U8 -> T_U8
| MenhirInterpreter.T_T_U64 -> T_U64
| MenhirInterpreter.T_T_U32 -> T_U32
| MenhirInterpreter.T_T_U256 -> T_U256
| MenhirInterpreter.T_T_U16 -> T_U16
| MenhirInterpreter.T_T_U128 -> T_U128
| MenhirInterpreter.T_T_INT -> T_INT
| MenhirInterpreter.T_T_BOOL -> T_BOOL
| MenhirInterpreter.T_TRUE -> TRUE
| MenhirInterpreter.T_TO -> TO
| MenhirInterpreter.T_SWSIZE -> SWSIZE (`W64, `Unsigned)
| MenhirInterpreter.T_SVSIZE -> SVSIZE (`V2, `Unsigned, `W1)
| MenhirInterpreter.T_STRING -> STRING ""
| MenhirInterpreter.T_STAR -> STAR
| MenhirInterpreter.T_STACK -> STACK
| MenhirInterpreter.T_SLASH -> SLASH
| MenhirInterpreter.T_SHARP -> SHARP
| MenhirInterpreter.T_SEMICOLON -> SEMICOLON
| MenhirInterpreter.T_RPAREN -> RPAREN
| MenhirInterpreter.T_ROR -> ROR
| MenhirInterpreter.T_ROL -> ROL
| MenhirInterpreter.T_RETURN -> RETURN
| MenhirInterpreter.T_REQUIRE -> REQUIRE
| MenhirInterpreter.T_REG -> REG
| MenhirInterpreter.T_RBRACKET -> RBRACKET
| MenhirInterpreter.T_RBRACE -> RBRACE
| MenhirInterpreter.T_RARROW -> RARROW
| MenhirInterpreter.T_QUESTIONMARK -> QUESTIONMARK
| MenhirInterpreter.T_POINTER -> POINTER
| MenhirInterpreter.T_PLUS -> PLUS
| MenhirInterpreter.T_PIPEPIPE -> PIPEPIPE
| MenhirInterpreter.T_PIPE -> PIPE
| MenhirInterpreter.T_PERCENT -> PERCENT
| MenhirInterpreter.T_PARAM -> PARAM
| MenhirInterpreter.T_NID -> NID ""
| MenhirInterpreter.T_MUTABLE -> MUTABLE
| MenhirInterpreter.T_MINUS -> MINUS
| MenhirInterpreter.T_LTLT -> LTLT
| MenhirInterpreter.T_LT -> LT `Unsigned
| MenhirInterpreter.T_LPAREN -> LPAREN
| MenhirInterpreter.T_LE -> LE `Unsigned
| MenhirInterpreter.T_LBRACKET -> LBRACKET
| MenhirInterpreter.T_LBRACE -> LBRACE
| MenhirInterpreter.T_INT -> INT (Z.of_int 0)
| MenhirInterpreter.T_INLINE -> INLINE
| MenhirInterpreter.T_IF -> IF
| MenhirInterpreter.T_HAT -> HAT
| MenhirInterpreter.T_GTGT -> GTGT `Unsigned
| MenhirInterpreter.T_GT -> GT `Unsigned
| MenhirInterpreter.T_GLOBAL -> GLOBAL
| MenhirInterpreter.T_GE -> GE `Unsigned
| MenhirInterpreter.T_FROM -> FROM
| MenhirInterpreter.T_FOR -> FOR
| MenhirInterpreter.T_FN -> FN
| MenhirInterpreter.T_FALSE -> FALSE
| MenhirInterpreter.T_EXPORT -> EXPORT
| MenhirInterpreter.T_EXEC -> EXEC
| MenhirInterpreter.T_EQEQ -> EQEQ
| MenhirInterpreter.T_EQ -> EQ
| MenhirInterpreter.T_EOF -> EOF
| MenhirInterpreter.T_ELSE -> ELSE
| MenhirInterpreter.T_DOWNTO -> DOWNTO
| MenhirInterpreter.T_DOT -> DOT
| MenhirInterpreter.T_CONSTANT -> CONSTANT
| MenhirInterpreter.T_COMMA -> COMMA
| MenhirInterpreter.T_COLON -> COLON
| MenhirInterpreter.T_BANGEQ -> BANGEQ
| MenhirInterpreter.T_BANG -> BANG
| MenhirInterpreter.T_ARRAYINIT -> ARRAYINIT
| MenhirInterpreter.T_AMPAMP -> AMPAMP
| MenhirInterpreter.T_AMP -> AMP

(* -------------------------------------------------------------------- *)
let succeed v = Syntax.Concrete.mk_root v

let env checkpoint =
  match checkpoint with
  | I.HandlingError env ->
      env
  | _ ->
      assert false

let state checkpoint : int =
  match I.top (env checkpoint) with
  | Some (I.Element (s, _, _, _)) ->
      I.number s
  | None ->
      (* Hmm... The parser is in its initial state. The incremental API
         currently lacks a way of finding out the number of the initial
         state. It is usually 0, so we return 0. This is unsatisfactory
         and should be fixed in the future. *)
      0

let fail buffer (checkpoint : _ I.checkpoint) =
  let (p1,p2) = E.last buffer in
  let location = Jasmin.Location.make p1 p2 in
  (* let message = ParserMessages.message (state checkpoint) in *)
  let message = "parse error" in
  raise (Jasmin.Syntax.ParseError (location, Some message))

open MenhirLib.General
open I

module Printers = struct

  let buf = Buffer.create 16
  let print s = Buffer.add_string buf s

  let print_nt : type a. a nonterminal -> string =
    fun nt ->
    match nt with
    | N_writable -> "writable"
    | N_var -> "var"
    | N_utype -> "utype"
    | N_top_annotation -> "top_annotation"
    | N_top -> "top"
    | N_swsize -> "swsize"
    | N_svsize -> "svsize"
    | N_struct_annot -> "struct_annot"
    | N_storage -> "storage"
    | N_stor_type -> "stor_type"
    | N_simple_attribute -> "simple_attribute"
    | N_separated_nonempty_list_option_COMMA__var_ -> "separated_nonempty_list_option_COMMA__var_"
    | N_separated_nonempty_list_empty_var_ -> "separated_nonempty_list_empty_var_"
    | N_separated_nonempty_list_COMMA_var_ -> "separated_nonempty_list_COMMA_var_"
    | N_separated_nonempty_list_COMMA_range_ -> "separated_nonempty_list_COMMA_range_"
    | N_separated_nonempty_list_COMMA_plvalue_ -> "separated_nonempty_list_COMMA_plvalue_"
    | N_separated_nonempty_list_COMMA_pexpr_ -> "separated_nonempty_list_COMMA_pexpr_"
    | N_separated_nonempty_list_COMMA_annotation_ -> "separated_nonempty_list_COMMA_annotation_"
    | N_separated_nonempty_list_COMMA_annot_stor_type_ -> "separated_nonempty_list_COMMA_annot_stor_type_"
    | N_separated_nonempty_list_COMMA_annot_pvardecl_ -> "separated_nonempty_list_COMMA_annot_pvardecl_"
    | N_range -> "range"
    | N_ptype -> "ptype"
    | N_ptr -> "ptr"
    | N_prim -> "prim"
    | N_prequire1 -> "prequire1"
    | N_prequire -> "prequire"
    | N_pparam -> "pparam"
    | N_pointer -> "pointer"
    | N_plvalues -> "plvalues"
    | N_plvalue -> "plvalue"
    | N_pinstr_r -> "pinstr_r"
    | N_pinstr -> "pinstr"
    | N_pif -> "pif"
    | N_pglobal -> "pglobal"
    | N_pgexpr -> "pgexpr"
    | N_pfundef -> "pfundef"
    | N_pfunbody -> "pfunbody"
    | N_pexpr -> "pexpr"
    | N_pexec -> "pexec"
    | N_peqop -> "peqop"
    | N_pelseif -> "pelseif"
    | N_pelse -> "pelse"
    | N_pblock -> "pblock"
    | N_option_writable_ -> "option_writable_"
    | N_option_utype_ -> "option_utype_"
    | N_option_prefix_RARROW_tuple_annot_stor_type___ -> "option_prefix_RARROW_tuple_annot_stor_type___"
    | N_option_prefix_IF_pexpr__ -> "option_prefix_IF_pexpr__"
    | N_option_pointer_ -> "option_pointer_"
    | N_option_pblock_ -> "option_pblock_"
    | N_option_parens_utype__ -> "option_parens_utype__"
    | N_option_mem_ofs_ -> "option_mem_ofs_"
    | N_option_from_ -> "option_from_"
    | N_option_call_conv_ -> "option_call_conv_"
    | N_option_attribute_ -> "option_attribute_"
    | N_option_arr_access_len_ -> "option_arr_access_len_"
    | N_option_DOT_ -> "option_DOT_"
    | N_option_COMMA_ -> "option_COMMA_"
    | N_nonempty_list_prequire1_ -> "nonempty_list_prequire1_"
    | N_module_ -> "module_"
    | N_loption_separated_nonempty_list_COMMA_var__ -> "loption_separated_nonempty_list_COMMA_var__"
    | N_loption_separated_nonempty_list_COMMA_range__ -> "loption_separated_nonempty_list_COMMA_range__"
    | N_loption_separated_nonempty_list_COMMA_pexpr__ -> "loption_separated_nonempty_list_COMMA_pexpr__"
    | N_loption_separated_nonempty_list_COMMA_annotation__ -> "loption_separated_nonempty_list_COMMA_annotation__"
    | N_loption_separated_nonempty_list_COMMA_annot_stor_type__ -> "loption_separated_nonempty_list_COMMA_annot_stor_type__"
    | N_loption_separated_nonempty_list_COMMA_annot_pvardecl__ -> "loption_separated_nonempty_list_COMMA_annot_pvardecl__"
    | N_list_top_annotation_ -> "list_top_annotation_"
    | N_list_pinstr_ -> "list_pinstr_"
    | N_keyword -> "keyword"
    | N_int -> "int"
    | N_implicites -> "implicites"
    | N_from -> "from"
    | N_castop1 -> "castop1"
    | N_castop -> "castop"
    | N_cast -> "cast"
    | N_call_conv -> "call_conv"
    | N_attribute -> "attribute"
    | N_arr_access_len -> "arr_access_len"
    | N_arr_access_i -> "arr_access_i"
    | N_arr_access -> "arr_access"
    | N_annotations -> "annotations"
    | N_annotationlabel -> "annotationlabel"
    | N_annotation -> "annotation"
    | N_annot_stor_type -> "annot_stor_type"
    | N_annot_pvardecl -> "annot_pvardecl"
    | N_ptype_r -> "ptype_r"
    | N_plvalue_r -> "plvalue_r"
    | N_pexpr_r -> "pexpr_r"
    | N_pblock_r -> "pblock_r"
    | N_option_loc_castop1__ -> "option_loc_castop1"
    | N_option___anonymous_1_ -> "option___anonymous_1"
    | N_list_loc_top__ -> "list_loc_top"

  let print_terminal : type a. a terminal -> string =
    fun t -> match t with
    | T_error -> "error"
    | T_WHILE -> "WHILE"
    | T_UNDERSCORE -> "UNDERSCORE"
    | T_T_U8 -> "T_U8"
    | T_T_U64 -> "T_U64"
    | T_T_U32 -> "T_U32"
    | T_T_U256 -> "T_U256"
    | T_T_U16 -> "T_U16"
    | T_T_U128 -> "T_U128"
    | T_T_INT -> "T_INT"
    | T_T_BOOL -> "T_BOOL"
    | T_TRUE -> "TRUE"
    | T_TO -> "TO"
    | T_SWSIZE -> "SWSIZE"
    | T_SVSIZE -> "SVSIZE"
    | T_STRING -> "STRING"
    | T_STAR -> "STAR"
    | T_STACK -> "STACK"
    | T_SLASH -> "SLASH"
    | T_SHARP -> "SHARP"
    | T_SEMICOLON -> "SEMICOLON"
    | T_RPAREN -> "RPAREN"
    | T_ROR -> "ROR"
    | T_ROL -> "ROL"
    | T_RETURN -> "RETURN"
    | T_REQUIRE -> "REQUIRE"
    | T_REG -> "REG"
    | T_RBRACKET -> "RBRACKET"
    | T_RBRACE -> "RBRACE"
    | T_RARROW -> "RARROW"
    | T_QUESTIONMARK -> "QUESTIONMARK"
    | T_POINTER -> "POINTER"
    | T_PLUS -> "PLUS"
    | T_PIPEPIPE -> "PIPEPIPE"
    | T_PIPE -> "PIPE"
    | T_PERCENT -> "PERCENT"
    | T_PARAM -> "PARAM"
    | T_NID -> "NID"
    | T_MUTABLE -> "MUTABLE"
    | T_MINUS -> "MINUS"
    | T_LTLT -> "LTLT"
    | T_LT -> "LT"
    | T_LPAREN -> "LPAREN"
    | T_LE -> "LE"
    | T_LBRACKET -> "LBRACKET"
    | T_LBRACE -> "LBRACE"
    | T_INT -> "INT"
    | T_INLINE -> "INLINE"
    | T_IF -> "IF"
    | T_HAT -> "HAT"
    | T_GTGT -> "GTGT"
    | T_GT -> "GT"
    | T_GLOBAL -> "GLOBAL"
    | T_GE -> "GE"
    | T_FROM -> "FROM"
    | T_FOR -> "FOR"
    | T_FN -> "FN"
    | T_FALSE -> "FALSE"
    | T_EXPORT -> "EXPORT"
    | T_EXEC -> "EXEC"
    | T_EQEQ -> "EQEQ"
    | T_EQ -> "EQ"
    | T_EOF -> "EOF"
    | T_ELSE -> "ELSE"
    | T_DOWNTO -> "DOWNTO"
    | T_DOT -> "DOT"
    | T_CONSTANT -> "CONSTANT"
    | T_COMMA -> "COMMA"
    | T_COLON -> "COLON"
    | T_BANGEQ -> "BANGEQ"
    | T_BANG -> "BANG"
    | T_ARRAYINIT -> "ARRAYINIT"
    | T_AMPAMP -> "AMPAMP"
    | T_AMP -> "AMP"

  let print_symbol (symbol : xsymbol) =
    let s = match symbol with
    | X (T t) -> print_terminal t
    | X (N nt) -> print_nt nt
    in
    Buffer.add_string buf s

  let print_element = Some (fun e -> Buffer.add_string buf "EL")

  let reset () = Buffer.reset buf

end

module Print =
  MenhirLib.Printers.Make
    (I)
    (Printers)

type explanation = {
    item: item;
    past: (xsymbol * Lexing.position * Lexing.position) list
  }

let string_of_explanation { item } =
  Printers.reset ();
  Print.print_item item;
  Buffer.contents Printers.buf

let string_of_symbol symb =
  Printers.reset ();
  Printers.print_symbol symb;
  Buffer.contents Printers.buf

let items_current env : item list =
    (* Get the current state. *)
    match Lazy.force (stack env) with
    | Nil ->
        (* If we get here, then the stack is empty, which means the parser
           is in an initial state. This should not happen. *)
        invalid_arg "items_current" (* TEMPORARY it DOES happen! *)
    | Cons (Element (current, _, _, _), _) ->
        (* Extract the current state out of the top stack element, and
           convert it to a set of LR(0) items. Returning a set of items
           instead of an ['a lr1state] is convenient; returning [current]
           would require wrapping it in an existential type. *)
        items current

(* [is_shift_item t item] determines whether [item] justifies a shift
   transition along the terminal symbol [t]. *)

let is_shift_item (t : _ terminal) (prod, index) : bool =
 let rhs = rhs prod in
 let length = List.length rhs in
 assert (0 < index && index <= length);
 (* We test that there is one symbol after the bullet and this symbol
    is [t] or can generate a word that begins with [t]. (Note that we
    don't need to worry about the case where this symbol is nullable
    and [t] is generated by the following symbol. In that situation,
    we would have to reduce before we can shift [t].) *)
 index < length && xfirst (List.nth rhs index) t

 let rec marry past stack =
  match past, stack with
  | [], _ ->
      []
  | symbol :: past, lazy (Cons (Element (s, _, startp, endp), stack)) ->
      assert (compare_symbols symbol (X (incoming_symbol s)) = 0);
      (symbol, startp, endp) :: marry past stack
  | _ :: _, lazy Nil ->
      assert false

  let compare_explanations x1 x2 =
    let c = compare_items x1.item x2.item in
    (* TEMPORARY checking that if [c] is 0 then the positions are the same *)
    assert (
      c <> 0 || List.for_all2 (fun (_, start1, end1) (_, start2, end2) ->
        start1.Lexing.pos_cnum = start2.Lexing.pos_cnum &&
        end1.Lexing.pos_cnum = end2.Lexing.pos_cnum
      ) x1.past x2.past
    );
    c


let accumulate (t : _ terminal) env explanations =
    (* The parser is about to shift, which means it is willing to
       consume the terminal symbol [t]. In the state before the
       transition, look at the items that justify shifting [t].
       We view these items as explanations: they explain what
       we have read and what we expect to read. *)
    let stack = stack env in
    List.fold_left (fun explanations item ->
      if is_shift_item t item then
        let prod, index = item in
        let rhs = rhs prod in
        {
          item = item;
          past = List.rev (marry (List.rev (take index rhs)) stack)
        } :: explanations
      else
        explanations
    ) explanations (items_current env)

let investigate pos (checkpoint : _ checkpoint) : explanation list =
   weed compare_explanations (
     foreach_terminal_but_error (fun symbol explanations ->
       match symbol with
       | X (N _) -> assert false
       | X (T t) ->
           (* Build a dummy token for the terminal symbol [t]. *)
           let token = (terminal2token t, pos, pos) in
           (* Submit it to the parser. Accumulate explanations. *)
           match shifts (offer checkpoint token) with
           | None ->
               explanations
           | Some env ->
               accumulate t env explanations
     ) []
   )

exception Error of (Lexing.position * Lexing.position) * explanation list

let fail (inputneeded : 'a I.checkpoint) (checkpoint : 'a I.checkpoint) =
  (* The parser signals a syntax error. Note the position of the
     problematic token, which is useful. Then, go back to the
     last [InputNeeded] checkpoint and investigate. *)
  match checkpoint with
  | HandlingError env ->
      let (startp, _) as positions = I.positions env in
      (*
      errors := (positions, Some (investigate startp inputneeded)) :: !errors
      *)
      raise (Error (positions, investigate startp inputneeded))
  | _ ->
      assert false

type 'a last_reduction =
  | FoundTopAt of 'a
  | FoundInstructionAt of 'a
  | FoundNothingAt of 'a

type 'a recovery_state = {
  last_reduction : 'a last_reduction;
  new_symbols : int;
}

let rec reduce_cst n nt cst acc =
  match cst with
  | [] -> if n > 0 then raise (Failure "More symbols but empty cst")
    else [Syntax.Concrete.make_nonterminal nt acc]
  | Jasmin.Location.{ pl_desc = Syntax.Concrete.NonTerminal { kind = Error } } as symb :: cst' ->
    (* Error nodes should not count as RHS symbols *)
    reduce_cst n nt cst' (symb::acc)
  | symb :: cst' ->
    if n > 0 then reduce_cst (n-1) nt cst' (symb::acc)
    else Syntax.Concrete.make_nonterminal nt acc :: cst

let update_recovery_state_reduce inputneeded production recovery_state =
  match lhs production with
  | X (N N_top) ->
     { last_reduction = FoundTopAt inputneeded; new_symbols = 0 }
  | X (N N_pinstr) ->
     { last_reduction = FoundInstructionAt inputneeded; new_symbols = 0 }
  | _ ->
     { recovery_state with new_symbols = recovery_state.new_symbols - List.length (rhs production) + 1}

let update_recovery_state_input recovery_state =
  { recovery_state with new_symbols = recovery_state.new_symbols + 1 }

let rec take_symbols n l =
  if n > 0 then match l with
    | [] -> l
    | Jasmin.Location.{ pl_desc = Syntax.Concrete.NonTerminal { kind = Error } } as hd :: tl -> hd :: take n tl
    | hd :: tl -> hd :: take (n-1) tl
  else l

let resume_on_error recovery_state cst extra_tokens lex =
  match recovery_state.last_reduction with
  | FoundInstructionAt (checkpoint, cst') ->
     let extra_tokens', lex =
       Lexer.lex_until_before (fun t -> t = SEMICOLON || t = RBRACE) lex
     in
     let (token,_,_), lex' = Lexer.next lex in
     let lex =
       if token = SEMICOLON then lex' else lex
     in
     let extra = List.rev_map (fun (v,startp,endp) -> Syntax.Concrete.make_terminal startp endp v) extra_tokens' in
     let extra = List.rev_append extra_tokens extra in
     let error_children = List.rev_append (take_symbols recovery_state.new_symbols cst) extra in
     let error = Syntax.Concrete.(make_nonterminal Error error_children) in
     let cst = error :: cst' in
     let recovery_state = { recovery_state with new_symbols = 0 } in
     lex, checkpoint, cst, recovery_state
  | (FoundNothingAt (checkpoint, cst') | FoundTopAt (checkpoint, cst')) ->
     let extra_tokens', lex = Lexer.lex_until_before
        (function EOF | FN | (* SHARP | *) EXPORT | INLINE | PARAM | EXEC | REQUIRE | FROM (* TODO add pglobal *) -> true | _ -> false)
        lex
     in
     let extra = List.rev_map (fun (v,startp,endp) -> Syntax.Concrete.make_terminal startp endp v) extra_tokens' in
     let extra = List.rev_append extra_tokens extra in
     let error_children = List.rev_append (take_symbols recovery_state.new_symbols cst) extra in
     let error = Syntax.Concrete.(make_nonterminal Error error_children) in
     let cst = error :: cst' in
     let recovery_state = { recovery_state with new_symbols = 0 } in
     lex, checkpoint, cst, recovery_state

let extract_nonterminal symb =
  match symb with
  | I.(X T _) -> assert false
  | I.(X N nt) -> Syntax.Concrete.X nt


let rec show_green n g =
  let open Syntax.Concrete in
  match g.Jasmin.Location.pl_desc with
  | Terminal token -> String.make n ' ' ^  show_token token
  | NonTerminal { kind = Error; children } ->
    String.make n ' ' ^  "ERROR\n" ^ String.concat "\n" (List.map (show_green (n+2)) children)
  | NonTerminal { kind = X nt; children } ->
    String.make n ' ' ^ Printers.print_nt nt ^ "\n" ^ String.concat "\n" (List.map (show_green (n+2)) children)

let show_green g = show_green 0 g

let show_tree node =
  let open Syntax.Concrete in
  let show_node x =
    Format.sprintf "%s" (show_green x.green)
  in
  fold (fun acc x -> acc ^ " " ^ show_node x) "" node

let rec loop lexer inputneeded cst recovery_state extra_tokens errors (checkpoint : 'a I.checkpoint) =
  match checkpoint with
  | I.InputNeeded _env ->
      let (token, startp, endp as triple), lexer = Lexer.next lexer in
      (* The parser needs a token. Request one from the lexer,
         and offer it to the parser, which will produce a new
         checkpoint. Then, repeat. *)
      let extra_tokens = Syntax.Concrete.make_terminal startp endp token :: extra_tokens in
      let recovery_state = update_recovery_state_input recovery_state in
      loop lexer (checkpoint, cst) cst recovery_state extra_tokens errors (I.offer checkpoint triple)
  | I.Shifting _ ->
      let checkpoint = I.resume checkpoint in
      let cst = List.append extra_tokens cst in
      loop lexer inputneeded cst recovery_state [] errors checkpoint
  | I.AboutToReduce (env, production) ->
      let n = List.length (rhs production) in
      let nt = extract_nonterminal (lhs production) in
      (*
      Printf.eprintf "Reducing: %s, %d symbols\n" (match nt with Syntax.Concrete.X foo -> Printers.print_nt foo | Error -> "Error") n;
      List.iter (fun v -> Printf.eprintf "CST root before reducing: %s\n" (show_green v)) cst; *)
      let cst = reduce_cst n nt cst [] in
      let checkpoint = I.resume checkpoint in
      loop lexer inputneeded cst (update_recovery_state_reduce inputneeded production recovery_state) extra_tokens errors checkpoint
  | I.Rejected -> assert false
  | I.HandlingError env ->
    let lexer, after_error, cst, recovery_state = resume_on_error recovery_state cst extra_tokens lexer in
    (*
    Printf.eprintf "Resuming on %s\n" (show_token (Lexer.get' lexer));
    List.iter (fun v -> Printf.eprintf "CST root after recovery: %s\n" (show_green v)) cst;
    *)
    let (startp, _) as positions = positions env in
    let error = (positions, investigate startp (fst inputneeded)) in
    loop lexer inputneeded cst recovery_state [] (error::errors) after_error
  | I.Accepted v ->
    begin match cst with
    | [root] -> Syntax.Concrete.mk_root root, errors
    | _ ->
      List.iter (fun v -> Printf.eprintf "Non-unique root when accepting: %s\n" (show_green v)) cst;
      assert false
    end

let parse_program ~fname (inc : Jasmin.Utils.IO.input) =
  let ch = Jasmin.Utils.IO.to_input_channel inc in
  let lexbuf = L.init fname (Lexing.from_channel ch) in
  Lexer.initialize lexbuf;
  (* let supplier = I.lexer_lexbuf_to_supplier Jasmin.Lexer.main lexbuf in *)
  (* let buffer, supplier = E.wrap_supplier supplier in *)
  let checkpoint = P.Incremental.module_ lexbuf.lex_curr_p in
  let recovery_state = { last_reduction = FoundNothingAt (checkpoint, []); new_symbols = 0 } in
  loop Lexer.start (checkpoint, []) [] recovery_state [] [] checkpoint