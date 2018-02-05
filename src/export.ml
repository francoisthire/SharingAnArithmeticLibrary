open Basic

module type E =
sig
  val export_entry : mident -> Utils.entry -> unit

  val flush : Format.formatter -> unit
end

module Coq =
struct
  include CiC
  let flush = flush `Coq
end

module Matita =
struct
  include CiC
  let flush = flush `Matita
end

module OpenTheory = OpenTheory
