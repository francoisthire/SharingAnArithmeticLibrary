open Basic

type entry =
  | Declaration of name * Term.term
  | Definition of name * Term.term * Term.term
  | Opaque of name * Term.term * Term.term
