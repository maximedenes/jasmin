open Lsp
open LspData
open Protocol

let workspace = ref Workspace.empty_workspace

let server_info = ServerInfo.{
  name = "jasmin-language-server";
  version = "0.0.1";
} 

let log msg = Format.eprintf "       [%d, %f] %s\n" (Unix.getpid ()) (Unix.gettimeofday ()) msg

type lsp_event = 
  | JsonRpc of JsonRpc.t option

type event =
 | LspManagerEvent of lsp_event

type events = event Sel.event list

let lsp : event Sel.event =
  Sel.on_httpcle Unix.stdin (function
    | Ok buff ->
      begin
        log "UI req ready";
        try LspManagerEvent (JsonRpc (Some (JsonRpc.t_of_yojson (Yojson.Safe.from_string (Bytes.to_string buff)))))
        with exn ->
          log @@ "failed to decode json";
          LspManagerEvent (JsonRpc None)
      end
    | Error exn ->
        log @@ ("failed to read message: " ^ Printexc.to_string exn);
        exit 0)
  |> fst
  |> Sel.name "lsp"
  |> Sel.make_recurring

let output_json ?(trace=true) obj =
  let msg  = Yojson.Safe.pretty_to_string ~std:true obj in
  let size = String.length msg in
  let s = Printf.sprintf "Content-Length: %d\r\n\r\n%s" size msg in
  log @@ "sent: " ^ msg;
  ignore(Unix.write_substring Unix.stdout s 0 (String.length s)) (* TODO ERROR *)

let do_initialize ~id params =
  let open Settings in
  let open Yojson.Safe.Util in
  begin match params.Request.Client.InitializeParams.rootUri with
  | None -> ()
  | Some uri ->
    workspace := Workspace.init ~root:uri
  end;
  let open ServerCapabilities in
  let legend = {
    tokenTypes = Language.SemanticTokens.token_types;
    tokenModifiers = Language.SemanticTokens.token_modifiers;
  }
  in
  let semanticTokensOptions = {
    legend;
    range = false;
    full = true;
  }
  in
  let jazz_pattern = {
    glob = "**/*.jazz";
    matches = None;
    options = None;
  }
  in
  let jinc_pattern = {
    glob = "**/*.jinc";
    matches = None;
    options = None;
  }
  in
  let jazz_filter = {
    scheme = None;
    pattern = jazz_pattern;
  }
  in
  let jinc_filter = {
    scheme = None;
    pattern = jinc_pattern;
  }
  in
  let filters = [jazz_filter; jinc_filter] in
  let fileOperationRegistrationOptions = {
    filters;
  }
  in
  let fileOperations = Some {
    didCreate = Some fileOperationRegistrationOptions;
    willCreate = Some fileOperationRegistrationOptions;
    didRename = Some fileOperationRegistrationOptions;
    willRename = Some fileOperationRegistrationOptions;
    didDelete = Some fileOperationRegistrationOptions;
    willDelete = Some fileOperationRegistrationOptions;
  }
  in
  let capabilities = {
    textDocumentSync = Full;
    completionProvider = { 
      resolveProvider = Some false; 
      triggerCharacters = None; 
      allCommitCharacters = None; 
      completionItem = None 
    };
    hoverProvider = true;
    semanticTokensProvider = semanticTokensOptions;
    definitionProvider = true;
    workspace = {
      fileOperations;
    };
  } in
  let result = Request.Client.InitializeResult.{
    capabilities = capabilities; 
    serverInfo = server_info;
  }
  in
  result, []

let do_semanticsTokensFull ~id params =
  let open Settings in
  let open Yojson.Safe.Util in
  let uri = params.Request.Client.SemanticTokensParams.textDocument.uri in
  let fname = Uri.path uri in
  let doc = Workspace.get_document !workspace ~fname in
  let data = match (DocumentManager.concrete_syntax_tree doc) with
    | None -> log "semantic tokens requested but no cst"; []
    | Some cst -> Language.SemanticTokens.compute_tokens cst
  in
  let result = Request.Client.SemanticTokens.{
    data
  }
  in
  result, []

let do_definition ~id params =
  let open Settings in
  let open Yojson.Safe.Util in
  let uri = params.Request.Client.DefinitionParams.textDocument.uri in
  let pos = params.Request.Client.DefinitionParams.position in
  let fname = Uri.path uri in
  let result = Workspace.goto_definition !workspace ~fname pos in
  result, []

let do_shutdown ~id params =
  let open Yojson.Safe.Util in
  let result = Ok `Null in
  output_json JsonRpc.Response.(yojson_of_t {id; result})

let do_exit ~id params =
  exit 0

let parse_loc json =
  let open Yojson.Safe.Util in
  let line = json |> member "line" |> to_int in
  let character = json |> member "character" |> to_int in
  Position.{ line ; character }

let publish_diagnostics fname diagnostics =
  let uri = Uri.of_fname fname in
  let notification = Notification.Server.PublishDiagnostics {
    uri;
    diagnostics
  }
  in
  output_json @@ Notification.Server.(yojson_of_t notification)

let publish_all_diagnostics () =
  PathMap.iter publish_diagnostics @@ Workspace.get_diagnostics !workspace

let textDocumentDidOpen params =
  let Notification.Client.DidOpenTextDocumentParams.{ textDocument } = params in
  let fname = Uri.path textDocument.uri in
  workspace := Workspace.open_document !workspace ~fname ~text:textDocument.text;
  publish_all_diagnostics (); (* FIXME restrict to changed diagnostics *)
  []

let textDocumentDidChange params =
  let Notification.Client.DidChangeTextDocumentParams.{ textDocument; contentChanges } = params in
  begin match contentChanges with
  | [change] ->
    let fname = Uri.path textDocument.uri in
    workspace := Workspace.open_document !workspace ~fname ~text:change.text;
    publish_all_diagnostics (); (* FIXME restrict to changed diagnostics *)
  | _ -> ()
  end;
  []

(*
let textDocumentDidChange params =
  let open Yojson.Safe.Util in
  let textDocument = params |> member "textDocument" in
  let uri = textDocument |> member "uri" |> to_string in
  let contentChanges = params |> member "contentChanges" |> to_list in
  let read_edit edit =
    let text = edit |> member "text" |> to_string in
    let range = Range.t_of_yojson (edit |> member "range") in
    range, text
  in
  let textEdits = List.map read_edit contentChanges in
  let st = Hashtbl.find states uri in
  let st = Dm.DocumentManager.apply_text_edits st textEdits in
  let (st, events) = 
    if !check_mode = Settings.Mode.Continuous then 
      Dm.DocumentManager.interpret_to_end st 
    else 
      (st, [])
  in
  Hashtbl.replace states uri st;
  publish_diagnostics uri st;
  uri, events

let textDocumentHover ~id params = 
  let open Yojson.Safe.Util in
  let textDocument = params |> member "textDocument" in
  let uri = textDocument |> member "uri" |> to_string in
  let loc = params |> member "position" |> parse_loc in 
  let st = Hashtbl.find states uri in 
  match Dm.DocumentManager.hover st loc with
  (* Response: result: Hover | null *)
  | None -> output_json @@ Response.(yojson_of_t { id; result = Ok (`Null) })
  | Some (Ok contents) ->
    let result = Ok (Hover.(yojson_of_t {contents})) in
    output_json @@ Response.(yojson_of_t { id; result })
  | _ -> ()
  *)

let dispatch_request : type a. id:int -> a Request.Client.params -> a * events =
  fun ~id req ->
  match req with
  | Initialize params ->
    do_initialize ~id params (* TODO send initial diagnostics *)
  | SemanticTokensFull params ->
    do_semanticsTokensFull ~id params
  | Definition params ->
    do_definition ~id params
  | UnknownRequest -> (), []

let dispatch_notification =
  let open Notification.Client in function
  | DidOpenTextDocument params ->
    textDocumentDidOpen params
  | DidChangeTextDocument params ->
    textDocumentDidChange params
  | UnknownNotification -> []

let dispatch = Request.Client.{ f = dispatch_request }

let handle_lsp_event = function
  | JsonRpc None ->
      []
  | JsonRpc (Some rpc) ->
    match rpc with
    | Request req ->
        log @@ "ui request: " ^ req.method_;
        let resp, events = Request.Client.yojson_of_result req dispatch in
        output_json resp;
        events
    | Notification notif ->
      dispatch_notification @@ Notification.Client.t_of_jsonrpc notif
    | Response resp ->
        log @@ "got unknown response";
        []

let handle_event = function
  | LspManagerEvent e -> handle_lsp_event e


