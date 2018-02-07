open Basic

val compile_proofs : bool ref

type obj

type compile_decl_err

type compile_defn_err

val compile_declaration : loc -> name -> Term.term -> (obj, compile_decl_err) error

val compile_definition : loc -> name -> Term.term -> Term.term -> (obj, compile_defn_err) error

val compile_hol_obj : obj -> unit

val fail_compile_declaration : compile_decl_err -> 'a

val fail_compile_definition : compile_defn_err -> 'a

val init : Format.formatter -> unit

val export_entry : Utils.entry -> unit

val flush : unit -> unit
