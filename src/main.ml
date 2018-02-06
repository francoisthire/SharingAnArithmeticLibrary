open Basic
open Cmd
open Pp


let system  = ref (module Export.Coq : Export.E)
let set_export s =
  if s = "coq" then
    system := (module Export.Coq)
  else if s = "matita" then
    system := (module Export.Matita)
  else if s = "opentheory" then
    system := (module Export.OpenTheory)
  else
    failwith (Format.sprintf "%s is not among the supported systems@." s)

let output_file = ref ""

let set_output_file s =
  output_file := s

let entries = ref []

module T = struct
  let mk_prelude _ i = ()

  let mk_declaration _ i st ty =
    match st with
    | Signature.Definable -> failwith "definable declarations are not supported (maybe it should be static)"
    | Signature.Static -> entries := Utils.Declaration(i,ty)::!entries

  let mk_definition _ i ty t =
    match ty with
    | None -> failwith "definitions should have a type"
    | Some ty -> entries := Utils.Definition(i,ty,t)::!entries

  let mk_opaque _ i ty t =
    match ty with
    | None -> failwith "Opaque definitions should have a type"
    | Some ty -> entries := Utils.Opaque(i,ty,t)::!entries

  let mk_rules l = failwith "Rules are not part of theory"

  let mk_command _ cmd = failwith "Commands are not supported"

  let mk_ending _ = ()
end

module P = Parser.Make(T)

let parse lb =
  try
    P.prelude Lexer.token lb ;
    while true do P.line Lexer.token lb done
  with
    | Lexer.EndOfFile -> ()
    | P.Error       -> Errors.fail (Lexer.get_loc lb)
                         "Unexpected token '%s'." (Lexing.lexeme lb)

let process_chan ic = parse (Lexing.from_channel ic)
let process_file name =
  (* Print.debug "Processing file %s\n" name; *)
  let ic = open_in name in
  process_chan ic;
  close_in ic

let from_stdin = ref false
let files = ref []
let add_file f = files := f :: !files

let options =
  [ "-stdin", Arg.Set from_stdin, " read from stdin";
    "-to", Arg.String set_export, "Set the exporting system. Currently, only Matita, Coq and OpenTheory are supported";
    "-o", Arg.String set_output_file, "Set outputfile."
  ]

let  _ =
  Arg.parse options add_file "usage: dkindent file [file...]";
  if !from_stdin
    then process_chan stdin
    else List.iter process_file (List.rev !files);
  let module E  = ((val !system):Export.E) in
  List.iter (E.export_entry (Basic.mk_mident "final")) !entries;
  if !output_file = "" then
    E.flush Format.std_formatter
  else
    E.flush (Format.formatter_of_out_channel (open_out !output_file))
