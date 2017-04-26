open Prog

val pp_list : 
   ('a, 'b, 'c, 'd, 'd, 'a) CamlinternalFormatBasics.format6 ->
   (Format.formatter -> 'e -> unit) ->
   Format.formatter -> 'e list -> unit

val pp_bool : Format.formatter -> bool -> unit

val pp_pprog : Format.formatter -> 'info pprog -> unit


val pp_prog : debug:bool -> Format.formatter -> 'info prog -> unit

