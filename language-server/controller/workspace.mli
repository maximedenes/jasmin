open Lsp
open LspData

type workspace

val empty_workspace : workspace
val init : root:Uri.t -> workspace

val open_document : workspace -> fname:string -> text:string -> workspace
val get_document : workspace -> fname:string -> DocumentManager.state
val close_document : workspace -> fname:string -> workspace

val get_diagnostics : workspace -> Diagnostic.t list PathMap.t

val goto_definition : workspace -> fname:string -> Position.t -> Location.t option