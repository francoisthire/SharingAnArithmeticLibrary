open Basic

type entry =
  | Declaration of ident * Term.term
  | Definition of ident * Term.term * Term.term
  | Opaque of ident * Term.term * Term.term
