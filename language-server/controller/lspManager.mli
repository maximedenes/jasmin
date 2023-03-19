type event
type events = event Sel.event list

val lsp : event Sel.event

val handle_event : event -> events