open LspData

module Notification = struct

  module Server = struct

    module PublishDiagnosticsParams = struct

      type t = {
        uri : Uri.t;
        diagnostics : Diagnostic.t list
      } [@@deriving yojson]

    end

    type t =
    | PublishDiagnostics of PublishDiagnosticsParams.t

    let yojson_of_t notification =
      let method_, params = match notification with
      | PublishDiagnostics params ->
        "textDocument/publishDiagnostics", PublishDiagnosticsParams.yojson_of_t params
      in
      JsonRpc.Notification.yojson_of_t { method_; params }      

  end

  module Client = struct

    module DidOpenTextDocumentParams = struct

      type t = {
        textDocument: TextDocumentItem.t;
      } [@@deriving yojson]

    end

    module DidChangeTextDocumentParams = struct

      type t = {
        textDocument: VersionedTextDocumentIdentifier.t;
        contentChanges: TextDocumentContentChangeEvent.t list;
      } [@@deriving yojson]

    end

    module DidCloseTextDocumentParams = struct

      type t = {
        textDocument: VersionedTextDocumentIdentifier.t;
      } [@@deriving yojson]

    end

    type t =
    | DidOpenTextDocument of DidOpenTextDocumentParams.t
    | DidChangeTextDocument of DidChangeTextDocumentParams.t
    | DidCloseTextDocument of DidCloseTextDocumentParams.t
    | UnknownNotification

    let t_of_jsonrpc JsonRpc.Notification.{ method_; params } =
      match method_ with
      | "textDocument/didOpen" ->
        DidOpenTextDocument DidOpenTextDocumentParams.(t_of_yojson params)
      | "textDocument/didChange" ->
        DidChangeTextDocument DidChangeTextDocumentParams.(t_of_yojson params)
      | "textDocument/didClose" ->
        DidCloseTextDocument DidCloseTextDocumentParams.(t_of_yojson params)
      | _ ->
        UnknownNotification

  end

end

module Request = struct

  module Client = struct

    module HoverParams = struct

      type t = {
        textDocument : TextDocumentIdentifier.t;
        position : Position.t
      } [@@deriving yojson]

    end

    module HoverResult = struct

      type t = {
        contents : string;
      } [@@deriving yojson]

    end

    module InitializeParams = struct
      
      type t = {
        processId: int option;
        rootUri: Uri.t option;
      } [@@deriving yojson] [@@yojson.allow_extra_fields]

    end

    module InitializeResult = struct
      
      type t = {
        capabilities: ServerCapabilities.t; 
        serverInfo: ServerInfo.t;
      } [@@deriving yojson]

    end

    module SemanticTokensParams = struct

      type t = {
        textDocument : TextDocumentIdentifier.t;
      } [@@deriving yojson]

    end

    module SemanticTokens = struct

      type t = {
        data : int list;
      } [@@deriving yojson]

    end

    module DefinitionParams = struct

      type t = {
        textDocument : TextDocumentIdentifier.t;
        position : Position.t;
      } [@@deriving yojson]

    end

    type 'rsp params =
    | Initialize : InitializeParams.t -> InitializeResult.t params
    | SemanticTokensFull : SemanticTokensParams.t -> SemanticTokens.t params
    | Definition : DefinitionParams.t -> Location.t option params
    | UnknownRequest : unit params
    (*
    | Hover : HoverParams.t -> (HoverParams.t, HoverResult.t) t
    *)

    type t = Pack : int * _ params -> t

    let t_of_jsonrpc JsonRpc.Request.{ id; method_; params } =
      let open Yojson.Safe.Util in
      match method_ with
      | "initialize" -> Pack (id, Initialize InitializeParams.(t_of_yojson params))
      | "textDocument/semanticTokens/full" -> Pack (id, SemanticTokensFull SemanticTokensParams.(t_of_yojson params))
      | "textDocument/definition" -> Pack (id, Definition DefinitionParams.(t_of_yojson params))
      | _ -> Pack (id, UnknownRequest)

    let yojson_of_response : type a. a params -> a -> Yojson.Safe.t =
      fun req resp ->
        match req with
        | Initialize _ -> InitializeResult.yojson_of_t resp
        | SemanticTokensFull _ -> SemanticTokens.yojson_of_t resp
        | Definition _ -> yojson_of_option Location.yojson_of_t resp
        | UnknownRequest -> yojson_of_unit ()

    type 'b dispatch = {
      f : 'a. id:int -> 'a params -> 'a * 'b
    }

    let yojson_of_result : JsonRpc.Request.t -> 'a dispatch -> Yojson.Safe.t * 'a =
      fun req foo ->
        let Pack(id, req) = t_of_jsonrpc req in
        let resp, data = foo.f ~id req in
        let resp = yojson_of_response req resp in
        let result = Ok(resp) in
        JsonRpc.Response.(yojson_of_t { id; result }), data

    (*
    let t_of_yojson (f : 'a params -> 'a) =
      let open Yojson.Safe.Util in
      let id = req |> member "id" |> to_int in
      let method_name = req |> member "method" |> to_string in
      let params = req |> member "params" in
      match method_name with
      | "initialize" -> Request (id, Initialize (InitializeParams.t_of_yojson params))
      | _ -> log @@ "Ignoring request with unknown method: " ^ method_name;
        Request (id, UnknownRequest)
        *)

        (*
    let dispatch f req =
      match req with
      | Initialize params
      *)


    (*
    type result =
    | DocumentHover of DocumentHoverResult.t option
    | Initialize of InitializeResult.t

    let yojson_of_result = function
    | DocumentHover None -> `Null
    | DocumentHover (Some result) -> DocumentHoverResult.yojson_of_t result
    | Initialize 

    type t = { id : int; result : result }

    let yojson_of_t { id; result } =
      JsonRpc.Response.(yojson_of_t { id; result = Ok (yojson_of_result result) })
      *)

  end

end