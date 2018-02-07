open Basic

module type E =
sig
  val init : Format.formatter -> unit

  val export_entry : Utils.entry -> unit

  val flush : unit -> unit
end

module Coq =
struct
  include CiC
  let flush () = flush `Coq
end

module Matita =
struct
  include CiC
  let flush () = flush `Matita
end

module OpenTheory = Hol
