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
  let mk_prelude _ i =
    Env.init i

  let mk_declaration _ i st ty =
    let name = mk_name (Env.get_name ()) i in
    match st with
    | Signature.Definable -> failwith "definable declarations are not supported (maybe it should be static)"
    | Signature.Static -> entries := Utils.Declaration(name,ty)::!entries

  let mk_definition _ i ty t =
    let name = mk_name (Env.get_name ()) i in
    match ty with
    | None -> failwith "definitions should have a type"
    | Some ty -> entries := Utils.Definition(name,ty,t)::!entries

  let mk_opaque _ i ty t =
    let name = mk_name (Env.get_name ()) i in
    match ty with
    | None -> failwith "Opaque definitions should have a type"
    | Some ty -> entries := Utils.Opaque(name,ty,t)::!entries

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
    "-o", Arg.String set_output_file, "Set outputfile.";
    ("-I"      , Arg.String Basic.add_path         , "Add a directory to load path");
  ]

let  _ =
  Arg.parse options add_file "usage: dkindent file [file...]";
  if !from_stdin
    then process_chan stdin
    else List.iter process_file (List.rev !files);
  let module E  = ((val !system):Export.E) in
  let fmt =
  if !output_file = "" then
    Format.std_formatter else (Format.formatter_of_out_channel (open_out !output_file)) in
  E.init fmt;
  List.iter E.export_entry (List.rev !entries);
  E.flush ()
