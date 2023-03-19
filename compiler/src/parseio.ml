(* -------------------------------------------------------------------- *)
open Utils

module L = MenhirLib.LexerUtil
module E = MenhirLib.ErrorReports

module P = Parser

module I = P.MenhirInterpreter

(* -------------------------------------------------------------------- *)
let succeed v = v

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
  let location = Location.make p1 p2 in
  let message = "Parsing error" in
  raise (Syntax.ParseError (location, Some message))

let parse_program ?(name = "") (inc : IO.input) =
  let ch = IO.to_input_channel inc in
  let lexbuf = L.init name (Lexing.from_channel ch) in
  let supplier = I.lexer_lexbuf_to_supplier Lexer.main lexbuf in
  let buffer, supplier = E.wrap_supplier supplier in
  let checkpoint = P.Incremental.module_ lexbuf.lex_curr_p in
  I.loop_handle succeed (fail buffer) supplier checkpoint

let parse_program_from_tokens startp supplier =
  let buffer, supplier = E.wrap_supplier supplier in
  let checkpoint = P.Incremental.module_ startp in
  I.loop_handle succeed (fail buffer) supplier checkpoint