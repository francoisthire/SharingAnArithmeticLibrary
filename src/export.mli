open Basic

module type E =
sig

  val init : Format.formatter -> unit

  val export_entry : Utils.entry -> unit

  val flush : unit -> unit
end

module Coq:E

module Matita:E

module OpenTheory:E
