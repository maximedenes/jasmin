(* -------------------------------------------------------------------- *)
val parse_program : ?name:string -> Utils.IO.input -> Syntax.pprogram
val parse_program_from_tokens : Lexing.position -> (unit -> Parser.token * Lexing.position * Lexing.position) -> Syntax.pprogram