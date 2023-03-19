open Sexplib.Std

module Uri = struct

  include Uri

  let t_of_yojson = function
  | `String str -> Uri.of_string str
  | _ -> raise (Invalid_argument "t_of_yojson")

  let yojson_of_t uri = `String (Uri.to_string uri)

  let of_fname fname =
    Uri.make ~scheme:"file" ~path:fname ()

end

module Position = struct
  
  type t = { line : int; character : int; } [@@deriving sexp, yojson]

  let compare pos1 pos2 =
    match Int.compare pos1.line pos2.line with
    | 0 -> Int.compare pos1.character pos2.character
    | x -> x

  let to_string pos = Format.sprintf "(%i,%i)" pos.line pos.character

end

module Range = struct

  type t = {
    start : Position.t;
    end_ : Position.t; [@key "end"]
  } [@@deriving sexp, yojson]

  let of_jasmin_loc Jasmin.Location.{ loc_start; loc_end } =
    let (start_line, start_char) = loc_start in
    let (end_line, end_char) = loc_end in
    let start = Position.{ line = start_line-1; character = start_char; } in
    let end_ = Position.{ line = end_line-1; character = end_char; } in
    { start; end_}

end 

module Location = struct

  type t = {
    uri: Uri.t;
    range: Range.t;
  } [@@deriving yojson]

  let of_jasmin_loc loc =
    let uri = Uri.make ~scheme:"file" ~path:loc.Jasmin.Location.loc_fname () in
    let (l1, c1) = loc.Jasmin.Location.loc_start in
    let (l2, c2) = loc.Jasmin.Location.loc_end in
    let start = Position.{ line = l1; character = c1} in
    let end_ = Position.{ line = l2; character = c2} in
    let range = Range.{ start; end_ } in
    { uri; range }


end

module CompletionItem = struct 

  type t = {
    label : string;
    detail : string option [@yojson.option];
    documentation : string option [@yojson.option];
  } [@@deriving yojson]

end

module CompletionList = struct 

  type t = {
    isIncomplete : bool;
    items : CompletionItem.t list;
  } [@@deriving yojson]
  
end

module Severity = struct

  type t =
  | Error [@value 1]
  | Warning [@value 2]
  | Information [@value 3]
  | Hint [@value 4]
  [@@deriving sexp]

  let yojson_of_t = function
  | Error -> `Int 1
  | Warning -> `Int 2
  | Information -> `Int 3
  | Hint -> `Int 4

  let t_of_yojson = function
  | `Int 1 -> Error
  | `Int 2 -> Warning
  | `Int 3 -> Information
  | `Int 4 -> Hint
  | _ -> assert false

end

module Diagnostic = struct

  type t = {
    range : Range.t;
    message : string;
    severity : Severity.t;
  } [@@deriving sexp, yojson]

end

module Error = struct

  let parseError = -32700
  let invalidRequest = -32600
  let methodNotFound = -32601
  let invalidParams = -32602
  let internalError = -32603
  let jsonrpcReservedErrorRangeStart = -32099
  let serverNotInitialized = -32002
  let unknownErrorCode = -32001
  let lspReservedErrorRangeStart = -32899
  let requestFailed = -32803
  let serverCancelled = -32802
  let contentModified = -32801
  let requestCancelled = -32800
  let lspReservedErrorRangeEnd = -32800

end

module ServerCapabilities = struct

  type textDocumentSyncKind =
  | None
  | Full
  | Incremental

  let yojson_of_textDocumentSyncKind = function
  | None -> `Int 0
  | Full -> `Int 1
  | Incremental -> `Int 2

  let textDocumentSyncKind_of_yojson = function
  | `Int 0 -> None
  | `Int 1 -> Full
  | `Int 2 -> Incremental
  | _ -> Yojson.json_error "invalid value"

  type completionItem = {
    labelDetailsSupport : bool option [@yojson.option];
  } [@@deriving yojson]

  type completionOptions = {
    triggerCharacters : string list option [@yojson.option];
    allCommitCharacters : string list option [@yojson.option];
    resolveProvider : bool option [@yojson.option];
    completionItem : completionItem option [@yojson.option];
  } [@@deriving yojson]

  type semanticTokensLegend = {
    tokenTypes : string list;
    tokenModifiers : string list;
  } [@@deriving yojson]

  type semanticTokensOptions = {
    legend : semanticTokensLegend;
    range : bool;
    full : bool;
  } [@@deriving yojson]

  type fileOperationPatternKind =
    | File
    | Folder
    [@@deriving yojson]

  type fileOperationPatternOptions = {
    ignoreCase : bool;
  } [@@deriving yojson]

  type fileOperationPattern = {
    glob : string;
    matches : fileOperationPatternKind option; [@yojson.option]
    options : fileOperationPatternOptions option; [@yojson.option]
  } [@@deriving yojson]

  type fileOperationFilter = {
    scheme : string option; [@yojson.option]
    pattern : fileOperationPattern;
  } [@@deriving yojson]

  type fileOperationRegistrationOptions = {
    filters : fileOperationFilter list;
  } [@@deriving yojson]

  type fileOperations = {
    didCreate : fileOperationRegistrationOptions option; [@yojson.option]
    willCreate : fileOperationRegistrationOptions option; [@yojson.option]
    didRename : fileOperationRegistrationOptions option; [@yojson.option]
    willRename : fileOperationRegistrationOptions option; [@yojson.option]
    didDelete : fileOperationRegistrationOptions option; [@yojson.option]
    willDelete : fileOperationRegistrationOptions option; [@yojson.option]
  } [@@deriving yojson]

  type workspaceOptions = {
    fileOperations : fileOperations option; [@yojson.option]
  } [@@deriving yojson]

  type t = {
    textDocumentSync : textDocumentSyncKind;
    completionProvider : completionOptions;
    hoverProvider : bool;
    semanticTokensProvider : semanticTokensOptions;
    definitionProvider : bool;
    workspace : workspaceOptions;
  } [@@deriving yojson]

end

module ServerInfo = struct

    type t = {
      name: string; 
      version: string; 
    } [@@deriving yojson]

end

module ConfigurationItem = struct

  type t = {
	  scopeUri: string option; [@yojson option]
	  section: string option; [@yojson option]
  } [@@deriving yojson]

end

module ConfigurationParams = struct

  type t = { items: ConfigurationItem.t list } [@@deriving yojson]

end

module Settings = struct

  module DelegationMode = struct

  type t = 
    | None
    | Skip 
    | Delegate 

  let yojson_of_t = function
  | None -> `String "None"
  | Skip -> `String "Skip"
  | Delegate -> `String "Delegate"

  let t_of_yojson = function
  | `String "None" -> None
  | `String "Skip" -> Skip
  | `String "Delegate" -> Delegate
  | _ -> Yojson.json_error "invalid value"

  end
  
  module Mode = struct

    type t =
    | Continuous 
    | Manual
    [@@deriving yojson]
      
    let yojson_of_t = function
    | Manual -> `Int 0
    | Continuous -> `Int 1
  
    let t_of_yojson = function
    | `Int 0 -> Manual
    | `Int 1 -> Continuous
    | _ -> Yojson.json_error @@ "invalid value "
  
  end

  module Proof = struct

    type t = {
      delegation: DelegationMode.t;
      workers: int option;
      mode: Mode.t;
    } [@@deriving yojson] [@@yojson.allow_extra_fields]

  end

  type t = {
    proof: Proof.t;
  } [@@deriving yojson] [@@yojson.allow_extra_fields]

end

module TextDocumentItem = struct

  type t = {
    uri: Uri.t;
    languageId: string;
    version: int;
    text: string;
  } [@@deriving yojson]

end

module TextDocumentIdentifier = struct

  type t = {
    uri: Uri.t;
  } [@@deriving yojson]

end

module VersionedTextDocumentIdentifier = struct

  type t = {
    uri: Uri.t;
    version: int;
  } [@@deriving yojson]

end

module TextDocumentPositionParams = struct

  type t = {
    textDocument: TextDocumentIdentifier.t;
    position: Position.t;
  } [@@deriving yojson]

end

module TextDocumentContentChangeEvent = struct

  type t = {
    text: string;
  } [@@deriving yojson]
  
end