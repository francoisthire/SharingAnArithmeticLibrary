open Basic

type t

type system = [`Coq | `Matita]

val init : Format.formatter -> unit

val export_entry : Utils.entry -> unit

val flush : system -> unit
