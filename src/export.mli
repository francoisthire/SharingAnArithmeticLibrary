open Basic

module type E =
sig
  val export_entry : mident -> Utils.entry -> unit

  val flush : Format.formatter -> unit
end

module Coq:E

module Matita:E

module OpenTheory:E
