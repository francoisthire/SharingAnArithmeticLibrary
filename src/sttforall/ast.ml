type tyOp   = string

type ty_var = string

type te_var = string

type name   = string

type _ty = TyVar of ty_var
         | Arrow of _ty * _ty
         | TyOp of tyOp
         | Prop

type ty  = ForallK of ty_var * ty
         | Ty of _ty

type _te = TeVar of te_var
         | Abs of te_var * _te
         | App of _te * _te
         | Forall of te_var * _ty * _te
         | Impl of _te * _te
         | AbsTy of ty_var * _te

type te  = ForallP of ty_var * te
         | Te of _te

type ty_ctx = ty_var list

type te_ctx =
  { ty:ty_var list;
    var: (te_var * ty) list;
  }

type proof_ctx =
  {
    ctx:te_ctx;
    hyp: te list
  }

type proof =
  {
    hyp:proof_ctx;
    thm:te;
    rule:rule;
  }

and rule =
  | Assume
  | ImplE of proof * proof
  | ImplI of proof
  | ForallE of proof * te
  | ForallI of proof
  | ForallTE of proof * ty
  | ForallTI of proof

type arity = int

type obj = Parameter  of name * ty
         | Definition of name * ty * te
         | Axiom      of name * te
         | Theorem    of name * te * proof
         | TyOpDef    of tyOp * arity

type ast = obj list
