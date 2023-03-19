open MenhirLib.General
open Jasmin.Parser.MenhirInterpreter
type explanation = {
    item: item;
    past: (xsymbol * Lexing.position * Lexing.position) list
  }

val string_of_explanation : explanation -> string
val string_of_symbol : xsymbol -> string

exception Error of (Lexing.position * Lexing.position) * explanation list
val parse_program : fname:string -> Jasmin.Utils.IO.input -> Syntax.Concrete.node * ((Lexing.position * Lexing.position) * explanation list) list
