open Basic

type t

type system = [`Coq | `Matita]

val export_entry : mident -> Utils.entry -> unit

val flush : system -> Format.formatter -> unit
