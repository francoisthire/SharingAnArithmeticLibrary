open Basic
open Sttforall

type term =
  | Type
  | Prop
  | Lam of ident * term * term
  | App of term * term
  | Forall of ident * term * term
  | Impl of term * term
  | Var of ident
  | Const of name

type declaration = Axiom of name * term | Parameter of name * term

type definition = Theorem of name * term * term | Constant of name * term * term

type obj = Declaration of declaration | Definition of definition


type module_id = string

type t =
  {
    name:module_id;
    obj:obj list
  }

type ty_ctx = ident list

let logic_module = mk_mident "logic"

let list_of_sttfa_theorem_with_eq =
  [mk_ident "eq_minus_O"; mk_ident "eq_minus_S_pred"; mk_ident "eq_to_eqb_true"; mk_ident "eq_to_eqb_false"; mk_ident "eq_times_div_minus_mod"; mk_ident "eq_to_bijn"; mk_ident "eq_minus_gcd_aux"; mk_ident "eq_div_O"; mk_ident "eq_minus_gcd"; mk_ident "eq_times_plus_to_congruent"; mk_ident "eq_mod_to_divides"; mk_ident "eq_fact_pi_p"]

let is_delta_rw cst =
  match cst with
  | Term.Const(_,cst) ->
    not (mident_eq (md cst) logic_module) && Str.(string_match (regexp "eq_\\|sym_eq") (string_of_ident (id cst)) 0) && not (List.exists (fun thm -> ident_eq (id cst) thm) list_of_sttfa_theorem_with_eq)
  | _ -> false

let get_infos_of_delta_rw md id = Str.(
    let id = string_of_ident id in
    if string_match (regexp "\\(__eq__\\)\\(.*\\)") id 0 then
      let id = matched_group 2 id in
      let cst = Term.mk_Const Basic.dloc (mk_name md (mk_ident id)) in
      match Env.reduction (Reduction.NSteps 1) cst with
      | OK te -> (mk_ident id),te
      | Err err -> Errors.fail_env_error err
    else
      assert false
)

let rec arguments_needed rw =
  let ty =
    match rw with
    | Term.Const(lc,cst) ->
      begin
        match Env.get_type lc cst with
        | OK ty -> ty
        | Err err -> Errors.fail_signature_error err
      end
    | _ -> assert false
  in
  let rec aux t n =
    match t with
    | Term.App(Term.Const(_,_) as cst,_,_) when is_sttfa_const sttfa_leibniz cst -> n
    | Term.App(Term.Const(_,_) as cst, Term.Lam(_,_,_,te),[])
      when is_sttfa_const sttfa_forall_kind_prop cst -> aux te (n+1)
    | Term.App(Term.Const(_,_) as cst,_,[Term.Lam(_,_,_,te)]) when is_sttfa_const sttfa_forall cst ->
      aux te (n+1)
    | Term.App(Term.Const(_,_) as cst, t', []) when is_sttfa_const sttfa_eps cst -> aux t' n
    | _ -> Format.eprintf "debug: %a@." Pp.print_term rw; assert false
  in
  aux ty 0

let rec compile_term ty_ctx te_ctx te =
  match te with
  | Term.App(c, Term.Lam(_, var, _, ty), []) when is_sttfa_const sttfa_forall_kind_type c ->
    let ty' = compile_term (var::ty_ctx) te_ctx ty in
    Forall(var, Type, ty')
  | Term.App(c, a, []) when is_sttfa_const sttfa_p c ->
    compile_term ty_ctx te_ctx a
  | Term.Const(_,cst) when is_sttfa_const sttfa_prop te -> Prop
  | Term.App(c,left,[right]) when is_sttfa_const sttfa_arrow c ->
    let left' = compile_term ty_ctx te_ctx left in
    let right' = compile_term ty_ctx te_ctx right in
    Impl(left',right')
  | Term.App(cst, Term.Lam(_,x, Some ty, te'), []) when is_sttfa_const sttfa_forall_kind_prop cst ->
    assert (is_sttfa_const sttfa_type ty);
    Forall(x, Type, compile_term (x::ty_ctx) (te_ctx) te')
  | Term.App(cst, ty, [Term.Lam(_,id, Some tyvar, te)]) when is_sttfa_const sttfa_forall cst ->
    let ty' = compile_term ty_ctx te_ctx ty in
    let te' = compile_term ty_ctx ((id, ty')::te_ctx) te in
    Forall(id, ty', te')
  | Term.App(cst, tel, [ter]) when is_sttfa_const sttfa_impl cst ->
    let tel' = compile_term ty_ctx te_ctx tel in
    let ter' = compile_term ty_ctx te_ctx ter in
    Impl(tel',ter')
  | Term.Const(lc,cst) ->
    Const(cst)
  | Term.DB(_,var,n) ->
    Var(var)
  | Term.Lam(_,id, Some cst, te) when is_sttfa_const sttfa_type cst ->
    Lam(id, Type, compile_term (id::ty_ctx) te_ctx te)
  | Term.Lam(_,id, Some tyvar, te) ->
    let _ty' = compile_wrapped_type ty_ctx te_ctx tyvar in
    let te' = compile_term ty_ctx ((id,_ty')::te_ctx) te in
    Lam(id,_ty', te')
  | Term.Lam(_, _, None, _) -> failwith "lambda untyped are not supported"
  | Term.App(f,a,args) ->
    let f' = compile_term ty_ctx te_ctx f in
    let args' = List.map (fun x -> compile_term ty_ctx te_ctx x) (a::args) in
    List.fold_left (fun t a -> App(t,a)) f' args'
  | _ ->  Format.eprintf "debug: %a@." Pp.print_term te; assert false

and compile_wrapped_type (ty_ctx:ty_ctx) te_ctx (ty:Term.term)  =
  match ty with
  | Term.App(cst, Term.App(c,a,[]), []) when (is_sttfa_const sttfa_etap cst && is_sttfa_const sttfa_p c)  ->
    compile_term ty_ctx te_ctx a
  | Term.App(cst, a, []) when is_sttfa_const sttfa_eps cst ->
    compile_term ty_ctx te_ctx a
  | _ -> Format.printf "debug:%a@." Pp.print_term ty; assert false

let compile_declaration name ty =
      match ty with
    | Term.App(cst,a,[]) when is_sttfa_const sttfa_etap cst ->
      Parameter(name, compile_term [] [] a)
    | Term.App(cst,a,[]) when is_sttfa_const sttfa_eps cst ->
      Axiom(name, compile_term [] [] a)
    | Term.Const(_,_) when is_sttfa_const sttfa_type ty ->
      Parameter(name, Type)
    | _ -> assert false

let compile_definition name ty term =
  match ty with
  | Term.App(cst,a,[]) when is_sttfa_const sttfa_etap cst ->
    Constant(name, compile_term [] [] a, compile_term [] [] term)
  | Term.App(cst,a,[]) when is_sttfa_const sttfa_eps cst ->
    Theorem(name, compile_term [] [] a, compile_term [] [] term)
  | _ -> assert false

let ast = ref {name="";
               obj=[];
              }

let init_ast name =
  ast :=
    {
      name=string_of_ident name;
      obj=[];
    }

let get_ast () =
  let ast = !ast in
  {ast with obj = List.rev ast.obj}

let add_declaration decl =
  let ast' = !ast in
  ast := {ast' with obj = Declaration(decl)::ast'.obj}

let add_definition defn =
  let ast' = !ast in
  ast := {ast' with obj = Definition(defn)::ast'.obj}

type system = [`Coq | `Matita]

let export_entry entry =
  match entry with
  | Utils.Declaration(name,ty) ->
    add_declaration(compile_declaration name ty)
  | Utils.Definition(name,ty,te) ->
    add_definition(compile_definition name ty te)
  | Utils.Opaque(name,ty,te) -> failwith "todo"

module type Printer =
sig
  val print_name : Format.formatter -> Basic.name -> unit

  val print_ident : Format.formatter -> Basic.ident -> unit

  val print_mident : Format.formatter -> Basic.mident -> unit

  val print_term : Format.formatter -> term -> unit

  val print_declaration : Format.formatter -> declaration -> unit

  val print_definition : Format.formatter -> definition -> unit

  val print_prelude : Format.formatter -> unit -> unit
end

let replace str =
  String.map (fun x -> x) str

let rename kw id =
  if List.mem id kw then
    mk_ident @@ (string_of_ident id) ^ "_"
  else
    let id = string_of_ident id in
    if String.length id > 0 && String.sub id 0 1 = "_" then
      mk_ident @@ "Joker"^(String.sub id 1 (String.length id - 1))
  else
    mk_ident (replace id)


let rec rename_keyword kw term =
  match term with
  | Lam(id, ty, te) ->
    let id' = rename kw id in
    Lam(id', rename_keyword kw ty, rename_keyword kw te)
  | App(f,a) ->
    App(rename_keyword kw f, rename_keyword kw a)
  | Forall(id, ty, te) ->
    let id' = rename kw id in
    Forall(id', rename_keyword kw ty, rename_keyword kw te)
  | Impl(tel,ter) ->
    Impl(rename_keyword kw tel, rename_keyword kw ter)
  | Var(id) ->
    let id' = rename kw id in
    Var(id')
  | _ -> term

module CoqPrinter =
struct

  let keywords = [mk_ident "return"]

  let print_ident out id =
    Format.fprintf out "%a" Pp.print_ident id

  let print_mident out md = Format.fprintf out "%a" Pp.print_mident md

  let print_name out name =
    print_ident out (id name)

  let rec print_term out term =
    match term with
    | Type -> Format.fprintf out "Type"
    | Prop -> Format.fprintf out "Prop"
    | Lam(id, ty, term) -> Format.fprintf out "fun %a : %a => %a" print_ident id print_term ty print_term term
    | App(f,a) -> Format.fprintf out "%a %a" print_term_wp f print_term_wp a
    | Forall(id,ty,term) -> Format.fprintf out "forall %a : %a, %a" print_ident id print_term ty print_term term
    | Impl(tel,ter) -> Format.fprintf out "%a -> %a" print_term_wp tel print_term ter
    | Var(id) -> Format.fprintf out "%a" print_ident id
    | Const(name) -> Format.fprintf out "%a" print_name name

  and print_term_wp out term =
    match term with
    | Prop -> print_term out term
    | t -> Format.fprintf out "(%a)" print_term t

  let print_term out term = print_term out (rename_keyword keywords term)

  let print_declaration out decl =
    match decl with
    | Axiom(name, term) ->
      Format.fprintf out "Axiom %a : %a." print_name name print_term term
    | Parameter(name, term) ->
      Format.fprintf out "Parameter %a : %a." print_name name print_term term

  let print_definition out defn =
    match defn with
    | Theorem(name, ty, term) ->
      Format.fprintf out "Definition %a : %a := %a." print_name name print_term ty print_term term
    | Constant(name, ty, term) ->
      Format.fprintf out "Definition %a : %a := %a." print_name name print_term ty print_term term

  let print_prelude out () =
    let print_import out md = Format.fprintf out "Require Import %s.@." md in
    List.iter (print_import out) ["leibniz"]

end

module MatitaPrinter =
struct
    let keywords = [mk_ident "return"; mk_ident "and"]

  let print_ident out id =
    Format.fprintf out "%a" Pp.print_ident id

  let print_mident out md = Format.fprintf out "%a" Pp.print_mident md

  let print_name out name =
    print_ident out (id name)

  let rec print_term out term =
    match term with
    | Type -> Format.fprintf out "Type[0]"
    | Prop -> Format.fprintf out "Prop"
    | Lam(id, ty, term) -> Format.fprintf out "\\lambda %a : %a. %a" print_ident id print_term ty print_term term
    | App(f,a) -> Format.fprintf out "%a %a" print_term_wp f print_term_wp a
    | Forall(id,ty,term) -> Format.fprintf out "\\forall %a : %a. %a" print_ident id print_term ty print_term term
    | Impl(tel,ter) -> Format.fprintf out "%a \\to %a" print_term_wp tel print_term ter
    | Var(id) -> Format.fprintf out "%a" print_ident id
    | Const(name) -> Format.fprintf out "%a" print_name name

  and print_term_wp out term =
    match term with
    | Prop -> print_term out term
    | t -> Format.fprintf out "(%a)" print_term t

  let print_term out term = print_term out (rename_keyword keywords term)

  let print_declaration out decl =
    match decl with
    | Axiom(name, term) ->
      Format.fprintf out "axiom %a : %a." print_name name print_term term
    | Parameter(name, term) ->
      Format.fprintf out "axiom %a : %a." print_name name print_term term

  let print_definition out defn =
    match defn with
    | Theorem(name, ty, term) ->
      Format.fprintf out "definition %a : %a := %a." print_name name print_term ty print_term term
    | Constant(name, ty, term) ->
      Format.fprintf out "definition %a : %a := %a." print_name name print_term ty print_term term

  let print_prelude out mds =
    let print_import out md = Format.fprintf out "include \"%s\".@." md in
    List.iter (print_import out) ["basics/pts.ma";"leibniz.ma"]
end

let initial = String.uppercase_ascii "initial"

(*
let print_depends out depends =
  List.iter (fun x -> Format.fprintf out "%a@." print_declaration x) depends
  let print_depend out dep =
    match dep with
    | Declaration(decl) -> print_declaration out decl
    | DefConstant(name,ty,te) -> print_definition out (Constant(name,ty,te))
  in
  Format.fprintf out "Module Type %s.@." initial;
  List.iter (fun x -> Format.printf "%a@." print_depend x) depends;
  Format.fprintf out "End %s.@." initial


let forget_definition defn =
  match defn with
  | Theorem(n,ty,_) -> Axiom(n,ty)
  | Constant(n,ty,_) -> Parameter(n,ty)

let print_target out name defn =
  let name = String.uppercase_ascii name in
  Format.fprintf out "Module Type %s.@." name;
  Format.fprintf out "Declare Module M : %s.@." initial;
  Format.fprintf out "Import M.@.";
  List.iter (fun x -> print_declaration out x;Format.printf "@.") (List.map forget_definition defn);
  Format.fprintf out "End %s.@." name

let print_fonctor out name defn =
  let name' = String.uppercase_ascii name in
  Format.fprintf out "Module %s (M : %s) : %s.@." name initial name';
  Format.fprintf out "Module M := M.@.";
  Format.fprintf out "Import M.@.";
  List.iter (fun x -> print_definition out x; Format.printf "@.") defn;
  Format.fprintf out "End %s." name
*)

let print_obj (module P:Printer) out name obj =
  match obj with
  | Definition(defn) -> Format.fprintf out "%a@." P.print_definition defn
  | Declaration(decl) -> Format.fprintf out "%a@." P.print_declaration decl
(*
  print_depends out obj.depends;
  print_target out name obj.definition;
  print_fonctor out name obj.definition
*)

let printer : (module Printer) ref = ref ((module CoqPrinter):(module Printer))

let set_printer s : unit =
  match s with
  | `Coq -> printer := (module CoqPrinter)
  | `Matita -> printer := (module MatitaPrinter)
  | _ -> assert false

let print_ast out ast =
  let (module P) = !printer in
  P.print_prelude out ();
  List.iter (print_obj !printer out ast.name) (List.rev ast.obj)

let fmt = ref Format.std_formatter

let init f = fmt := f

let flush system =
  set_printer system;
  print_ast !fmt !ast
