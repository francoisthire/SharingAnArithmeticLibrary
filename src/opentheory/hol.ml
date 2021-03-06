open Basic

(* If someone reads this code, please send a mail to francois.thire@lsv.fr before. It needs a real clean up *)
let compile_proofs = ref true

let _ = Pp.print_db_enabled := true

let rec split l n =
  if n = 0 then
    [],l
  else
    match l with
    | [] -> assert false
    | x::l' ->
      let left,right = split l' (n-1) in
      x::left,right

let find_assoc_index x l =
  let rec find_assoc_index x l n =
    match l with
    | [] -> None
    | (y,t)::l' -> if x = y then Some(n, t) else find_assoc_index x l' (n+1)
  in
  find_assoc_index x l 0

(* TODO: suppress ctx in the last translation *)
(* TODO: Fixe the base case for compare, but the latter should return the alpha renaming *)
(* FIXME: varible capture with substitution *)
type name = mident * ident

type _ty =
  | VarTy of ident
  | Arrow of _ty * _ty
  | OpType of name * _ty list
  | Bool

type ty =
  | ForallK of ident * ty
  | Type of _ty

type ty_subst = (ident * _ty) list

type _term =
  | Forall of ident * _ty * _term
  | Impl of _term * _term
  | VarTerm of ident * int * _ty
  | Const of name * ty * ty_subst
  | App of _term * _term
  | Lam of ident * _ty * _term

type term =
  | ForallT of ident * term
  | Term of _term

type ctx = int list

type ty_ctx = ident list

type term_ctx = (ident * _ty) list

type te_subst = (ident * _term) list

type proof_ctx = (ident * term) list

type 'a dir = Fold of 'a | Unfold of 'a

type rw = Delta of name *  ty * ty_subst | Beta of _term | Gamma of _proof * _term * _term


and _proof =
  | Lemma of name * term * ty_subst
  | Assume of _term * ty_subst
  | ForallI of ident * _ty * _prooft
  | ImplI of _term * _prooft
  | ForallE of _prooft * _term
  | ImplE of _prooft * _prooft
  | RewriteU of ctx * rw dir * _prooft



and _prooft =
  {
    _term:_term;
    _proof:_proof;
  }

type proof =
  | ForallP of ident * prooft
  | RewriteF of ctx * rw dir * prooft
  | Proof of _prooft

and prooft =
  {
    term:term;
    proof:proof;
  }

type obj =
  | Cst of name * ty * term option
  | TyOp of name * _ty list
  | Thm of name * term * prooft option

let name_dedukti (md,id) = Term.mk_Const dloc (mk_name md id)

let name_eq (md,id) (md',id') = mident_eq md md' && ident_eq id id'

let alpha_eq ctx id id' =
  if ident_eq id id' then
    true
  else
    try
      id' = List.assoc id ctx
    with _ -> false

let rec _ty_eq ctx left right : bool =
  match (left,right) with
  | Bool, Bool -> true
  | VarTy x, VarTy y -> alpha_eq ctx x y
  | Arrow(tyll, tylr), Arrow(tyrl, tyrr) -> _ty_eq ctx tyll tyrl && _ty_eq ctx tylr tyrr
  | OpType(name, tys), OpType(name', tys') ->
    name_eq name name' && List.for_all2 (fun l r -> _ty_eq ctx l r) tys tys'
  | _, _ -> false

let rec ty_eq ctx left right : bool =
  match (left,right) with
  | Type(ty), Type(ty') -> _ty_eq ctx ty ty'
  | ForallK(id, ty), ForallK(id', ty') -> ty_eq ((id,id')::ctx) ty ty'
  | _, _ -> false

let rec _term_eq ctx left right =
  match (left,right) with
  | VarTerm(id, n, _ty), VarTerm(id', n',_ty') -> n = n' && _ty_eq ctx _ty _ty'
  | Const(name, ty,_), Const(name', ty',_) -> name_eq name name' && ty_eq ctx ty ty'
  | Lam(id,_ty, _te), Lam(id',_ty', _te') -> _ty_eq ctx _ty _ty' && _term_eq ctx _te _te'
  | Impl(_tel,_ter), Impl(_tel',_ter') -> _term_eq ctx _tel _tel' && _term_eq ctx _ter _ter'
  | Forall(id,_ty,_te), Forall(id',_ty',_te') -> _ty_eq ctx _ty _ty'
                                                 && _term_eq ctx _te _te'
  | App(_tel, _ter), App(_tel', _ter') ->
    _term_eq ctx _tel _tel' &&     _term_eq ctx _ter _ter'
  | _,_ -> false

let rec term_eq ctx left right =
  match (left,right) with
  | ForallT(id,term), ForallT(id',term') -> term_eq ((id,id')::ctx) term term'
  | Term(_te), Term(_te') -> _term_eq ctx _te _te'
  | _, _ -> false

type decl = loc * ident * Term.term

type compile_type_err = TypeError of Term.term

type compile_term_err = TermError of Term.term | UntypedLambda of Term.term

type compile_decl_err =
  | DeclarationError of decl
  | DeclarationTypeError of compile_type_err * decl
  | DeclarationTermError of compile_term_err * decl

type compile_proof_err = ProofError of Term.term

type compile_defn_err =
  | DefinitionError of decl * Term.term
  | DefinitionTypeError of compile_type_err * decl * Term.term
  | DefinitionTermError of compile_term_err * decl * Term.term
  | DefinitionProofError of compile_proof_err * decl * Term.term

let print_name out (md,id) =
  Format.fprintf out "%a.%a" Pp.print_ident md Pp.print_ident id

let dloc = dloc
let hol = mk_mident "sttfa"

let const_of_name (md,id) = Term.mk_Const dloc (mk_name md id)

exception CompileTypeError of compile_type_err

exception CompileTermError of compile_term_err

exception CompileProofError of compile_proof_err


let hol_module = mk_mident "sttfa"
let hol_type = mk_ident "type"
let hol_etap = mk_ident "etap"
let hol_p = mk_ident "p"
let hol_arrow = mk_ident "arrow"
let hol_forall = mk_ident "forall"
let hol_leibniz = mk_ident "leibniz"
let hol_impl = mk_ident "impl"
let hol_prop = mk_ident "bool"
let hol_eps = mk_ident "eps"
let hol_forall_kind_type = mk_ident "forallK"
let hol_forall_kind_prop = mk_ident "forallP"

let logic_module = mk_mident "logic"

let (===) = ident_eq

let rec hol__type_dedukti ty =
  match ty with
  | VarTy id ->
    (* painful to get the correct index, so this is a hack cause of Pp.subst function *)
    Term.mk_DB dloc id 1000
  | Arrow(tyl,tyr) -> Term.mk_App (name_dedukti (hol,(mk_ident "arrow")))
                        (hol__type_dedukti tyl) [(hol__type_dedukti tyr)]
  | OpType(name,tys) ->
    List.fold_left (fun term arg -> Term.mk_App term (hol__type_dedukti arg) [])
    (name_dedukti name) tys
  | Bool -> (name_dedukti (hol,(mk_ident "prop")))

let rec hol_type_dedukti ty =
  match ty with
  | ForallK(var,ty) ->
    Term.mk_App (name_dedukti (hol,(mk_ident "forall_kind_type")))
      (Term.mk_Lam dloc var (Some (name_dedukti (hol,(mk_ident "type"))))
         (hol_type_dedukti ty)) []
  | Type(ty) -> hol__type_dedukti ty

let rec print_hol__type out ty = Pp.print_term out (hol__type_dedukti ty)

let rec print_hol_type out ty = Pp.print_term out (hol_type_dedukti ty)

let rec hol__term_dedukti te =
  match te with
  | Forall(id,_ty,_te) ->
    let ty' = (hol__type_dedukti _ty) in
    Term.mk_App (name_dedukti (hol, (mk_ident "forall")))
       ty' [(Term.mk_Lam dloc id
              (Some (Term.mk_App (name_dedukti (hol, (mk_ident "eta"))) ty' []))
              (hol__term_dedukti _te))]
  | Impl(_tel,_ter) ->
    Term.mk_App (name_dedukti (hol, (mk_ident "impl")))
      (hol__term_dedukti _tel) [(hol__term_dedukti _ter)]
  | VarTerm(ident,n,_) -> Term.mk_DB dloc ident n
  | Const(name,_,_) -> name_dedukti name
  | Lam(id, _ty, _term) -> Term.mk_Lam dloc id (Some (hol__type_dedukti _ty)) (hol__term_dedukti _term)
  | App(f,a) ->
    Term.mk_App (hol__term_dedukti f) (hol__term_dedukti a) []

let rec hol_term_dedukti te =
  match te with
  | ForallT(var,te) ->
    Term.mk_App (name_dedukti (hol, (mk_ident "forall_kind_prop")))
      (Term.mk_Lam dloc var (Some (name_dedukti (hol, (mk_ident "type"))))
         (hol_term_dedukti te)) []
  | Term te -> hol__term_dedukti te

let rec print_hol__term out te = Pp.print_term out (hol__term_dedukti te)
let rec print_hol_term out te = Pp.print_term out (hol_term_dedukti te)

let is_hol_const c t =
  match t with
  | Term.Const(_, name) -> (mident_eq (md name) hol_module) &&  (id name === c)
  | _ -> false

let is_type t =
  match t with
  | Term.App(cst, ty, _) when is_hol_const hol_etap cst -> true
  | _ -> false

let is_term t =
  match t with
  | Term.App(cst, ty, _) when is_hol_const hol_eps cst -> true
  | _ -> false


let rec poly_subst_ty (subst:ty_subst) (ty:ty) : _ty =
  match ty with
  | ForallK(var, ty') ->
    assert(List.mem_assoc var subst);
    poly_subst_ty subst ty'
  | Type(ty') -> poly_subst__ty subst ty'

and poly_subst__ty (subst:ty_subst) (ty:_ty) : _ty =
  match ty with
  | VarTy(var) ->
    if List.mem_assoc var subst then
      List.assoc var subst
    else
      VarTy(var)
  | Arrow(tyl,tyr) ->
    let tyl' = poly_subst__ty subst tyl in
    let tyr' = poly_subst__ty subst tyr in
    Arrow(tyl',tyr')
  | OpType(name,tys) ->
    OpType(name, List.map (poly_subst__ty subst) tys)
  | Bool -> Bool

let merge sub subst =
  List.fold_left (fun sub (id,_ty) -> (id,poly_subst__ty subst _ty)::sub) [] sub


let rec poly_subst_te (subst:ty_subst) (te:term) : _term =
  match te with
  | ForallT(var, te') ->
    assert(List.mem_assoc var subst);
    poly_subst_te subst te'
  | Term(te') -> poly_subst__te subst te'

and poly_subst__te (subst:ty_subst) (te:_term) : _term =
  match te with
  | Forall(var,_ty, _term) ->
    let _term' = poly_subst__te subst _term in
    Forall(var, poly_subst__ty subst _ty, _term')
  | Impl(_tel, _ter) ->
    let _tel' = poly_subst__te subst _tel in
    let _ter' = poly_subst__te subst _ter in
    Impl(_tel', _ter')
  | VarTerm(id, n, _ty) ->
    let _ty' = poly_subst__ty subst _ty in
    VarTerm(id, n, _ty')
  | App(f,_a) ->
    let _a' = poly_subst__te subst _a in
    let f' = poly_subst__te subst f in
    App(f', _a')
  | Const(name, ty, sub) ->
    let subst' = merge sub subst in
    Const(name, ty, subst')
  | Lam(id, _ty, _te) ->
    let _te' = poly_subst__te subst _te in
    let _ty' = poly_subst__ty subst _ty in
    Lam(id, _ty', _te')

let rec free_variables ctx _te =
  match _te with
  | Forall(var,_ty,_term) ->
    free_variables (var::ctx) _term
  | Impl(_tel,_ter) ->
    (free_variables ctx _tel)@(free_variables ctx _ter)
  | VarTerm(id, n, _ty) ->
    if List.mem id ctx then
      []
    else
      [id]
  | App(f,a) ->
    (free_variables ctx f)@(free_variables ctx a)
  | Const _ -> []
  | Lam(id,_ty, _term) ->
    free_variables (id::ctx) _term

let rec _lift n k t =
  match t with
  | VarTerm(id, i, _ty) ->
    if i < k then
      t
    else VarTerm(id, i+n, _ty)
  | Lam(id,_ty,_te) -> Lam(id,_ty,_lift n (k+1) _te)
  | Forall(id,_ty,_te) -> Forall(id,_ty, _lift n (k+1) _te)
  | Impl(_tel, _ter) -> Impl(_lift n k _tel, _lift n k _ter)
  | App(f,a) -> App(_lift n k f, _lift n k a)
  | _ -> t

let rec lift n t =
  match t with
  | ForallT(id,te) -> ForallT(id, lift n te)
  | Term(_te) -> Term(_lift n 0 _te)

let lift_rw n k rw =
  match rw with
  | Fold(Beta(te)) -> Fold(Beta(_lift n k te))
  | Unfold(Beta(te)) -> Unfold(Beta(_lift n k te))
  | _ -> rw

let rec get_depth _term ctx =
  match _term,ctx with
  | _, [] -> 0
  | Forall(_,_,_te),0::ctx' -> 1+(get_depth _te ctx')
  | Lam(_,_,_te),0::ctx' -> 1+(get_depth _te ctx')
  | App(f,a), i::ctx' ->
    if i = 0 then
      get_depth f ctx'
    else
      get_depth a ctx'
  | Impl(_tel, _ter), i::ctx' ->
    if i = 0 then
      get_depth _tel ctx'
    else
      get_depth _ter ctx'
  | _ -> assert false

(* should only be called for equality proof *)
let rec proof_lift n k _proof _term =
  match _proof with
  | Lemma(name, term, ty_subst) -> Lemma(name, lift n term, ty_subst)
  | Assume(_term, ty_subst) -> Assume(_lift n k _term, ty_subst)
  | ForallI(id, _ty, _prooft) ->
    let _proof = proof_lift n (k+1) _prooft._proof _prooft._term in
    let _term = _lift n k _prooft._term in
    ForallI(id, _ty, {_proof;_term})
  | ImplI(_term, _prooft) ->
    let _term' = _lift n k _term in
    let _proof = proof_lift n k _prooft._proof _prooft._term in
    let _term = _lift n k _prooft._term in
    ImplI(_term', {_proof;_term})
  | ForallE(_prooft, _term) ->
    let _term' = _lift n k _term in
    let _proof = proof_lift n k _prooft._proof _prooft._term in
    let _term = _lift n k _prooft._term in
    ForallE({_proof;_term}, _term')
  | ImplE(_prooftl, _prooftr) ->
    let _proofl = proof_lift n k _prooftl._proof _prooftl._term in
    let _terml = _lift n k _prooftl._term in
    let _proofr = proof_lift n k _prooftr._proof _prooftr._term in
    let _termr = _lift n k _prooftr._term in
    let _prooftl' = {_proof=_proofl;_term=_terml} in
    let _prooftr' = {_proof=_proofr;_term=_termr} in
    ImplE(_prooftl',_prooftr')
  | RewriteU(rw_ctx, rw, _prooft) ->
    let _proof = proof_lift n k _prooft._proof _prooft._term in
    let _term = _lift n k _prooft._term in
    let rw' = lift_rw n (k+get_depth _term rw_ctx) rw in
    RewriteU(rw_ctx, rw', {_proof;_term})



let term_subst__te n u (te:_term) : _term =
  let rec term_subst__te k n u (te:_term) : _term =
    match te with
    | Forall(var,_ty,_term) ->
      let _term' = term_subst__te (k+1) n u _term in
      Forall(var, _ty, _term')
    | Impl(_tel, _ter) ->
      let _tel' = term_subst__te k n u _tel in
      let _ter' = term_subst__te k n u _ter in
      Impl(_tel', _ter')
    | VarTerm(var, i, _ty) ->
      if i < k then
        te
      else if i = k then (_lift k 0 u)
      else VarTerm(var, i-1, _ty)
    | App(f,_a) ->
      let _a' = term_subst__te k n u _a in
      let f' = term_subst__te k n u f in
      App(f',_a')
    | Const _ -> te
    | Lam(id, _ty, _te) ->
      let _te' = term_subst__te (k+1) n u _te in
      Lam(id, _ty, _te')
  in
  term_subst__te 0 n u te

let rec poly_var_of_ty (ty:ty) : ident list =
  match ty with
  | Type _ -> []
  | ForallK(id, ty') ->
    let vars = poly_var_of_ty ty' in
    id::vars

let rec poly_var_of_te (te:term) : ident list =
  match te with
  | Term _ -> []
  | ForallT(id, te') ->
    let vars = poly_var_of_te te' in
    id::vars

let mk_hol_name name = md name,id name

let rec compile_tyOp ty_ctx name args =
  let args' = List.map (compile__type ty_ctx) args in
  OpType(mk_hol_name name, args')

and compile_type (ty_ctx:ty_ctx) (ty:Term.term) : ty =
  match ty with
  | Term.App(c, Term.Lam(_, var, _, ty), []) when is_hol_const hol_forall_kind_type c ->
    let ty' = compile_type (var::ty_ctx) ty in
    ForallK(var, ty')
  | Term.App(cst, ty, []) when is_hol_const hol_p cst ->  Type (compile__type ty_ctx ty)
  | _ -> assert false

and compile__type (ty_ctx:ty_ctx) (ty:Term.term) : _ty =
  match ty with
  | Term.Const(_, name) when is_hol_const hol_prop ty -> Bool
  | Term.App(c,left,[right]) when is_hol_const hol_arrow c ->
    let left' = compile__type ty_ctx left in
    let right' = compile__type ty_ctx right in
    Arrow(left',right')
  | Term.App(Term.Const(_, name),a,args) -> compile_tyOp ty_ctx name (a::args)
  | Term.Const(_, name) -> compile_tyOp ty_ctx name []
  | Term.DB(_,var,_) ->
    if List.mem var ty_ctx then
      VarTy(var)
    else
      assert false
  | _ ->
    raise (CompileTypeError(TypeError(ty)))

let compile_eta__type (ty_ctx:ty_ctx) (ty:Term.term) : _ty =
  match ty with
  | Term.App(cst, Term.App(cst', a,[]), []) when is_hol_const hol_etap cst
    && is_hol_const hol_p cst' -> compile__type ty_ctx a
  | _ -> assert false

let compile_eta_type (ty_ctx:ty_ctx) (ty:Term.term) : ty =
  match ty with
  | Term.App(cst, a, []) when is_hol_const hol_etap cst -> compile_type ty_ctx a
  | _ -> assert false

let ty_of_const lc name =
  match Env.get_type lc name with
  | OK ty -> ty
  | Err er -> Errors.fail_signature_error er

let extract_ty_of_const lc name ty_ctx (args:Term.term list) : ty * ty_subst * Term.term list =
  let ty = ty_of_const lc name in
  let ty' = compile_eta_type ty_ctx ty in
  let poly_vars = poly_var_of_ty ty' in
  let n = List.length poly_vars in
  let poly_args,args = split args n in
  let poly_args' = List.map (compile__type ty_ctx) poly_args in
  let subst = List.combine poly_vars poly_args' in
  ty', subst, args

let rec compile__term (ty_ctx:ty_ctx) (te_ctx:term_ctx) (te:Term.term) : _term =
  let lookup_ty var =
    match find_assoc_index var te_ctx with
    | None ->
      begin
        Format.printf "Free variable: %a@." Pp.print_ident var;
        assert false
      end
    | Some(n,t) -> (n,t)
  in
  match te with
  | Term.App(cst, ty, [Term.Lam(_,id, Some tyvar, te)]) when is_hol_const hol_forall cst ->
    let ty' = compile__type ty_ctx ty in
    let te' = compile__term ty_ctx ((id, ty')::te_ctx) te in
    Forall(id, ty', te')
  | Term.App(cst, tel, [ter]) when is_hol_const hol_impl cst ->
    let tel' = compile__term ty_ctx te_ctx tel in
    let ter' = compile__term ty_ctx te_ctx ter in
    Impl(tel',ter')
  | Term.Const(lc,name) ->
    let ty = ty_of_const lc name in
    let _ty' = compile_eta__type ty_ctx ty in
    Const(mk_hol_name name, (Type _ty'), [])
  | Term.DB(_,var,n) ->
    let n',ty = lookup_ty var in
    VarTerm(var, n', ty)
  | Term.Lam(_,id, Some cst, te) when is_hol_const hol_type cst ->
    compile__term (id::ty_ctx) te_ctx te
  | Term.Lam(_,id, Some tyvar, te) ->
    let _ty' = compile_eta__type ty_ctx tyvar in
    let te' = compile__term ty_ctx ((id,_ty')::te_ctx) te in
    Lam(id,_ty', te')
  | Term.Lam(_, _, None, _) ->
    raise(CompileTermError(UntypedLambda(te)))
  | Term.App(Term.Const(lc,name),a,args) ->
    let ty',subst,args = extract_ty_of_const lc name ty_ctx (a::args) in
    let args' = List.map (compile__term ty_ctx te_ctx) args in
    List.fold_left (fun t a -> App(t,a)) (Const(mk_hol_name name, ty', subst)) args'
  | Term.App(Term.DB(_,var,n),a,args) ->
    let n',ty = lookup_ty var in
    let args' = List.map (compile__term ty_ctx te_ctx) (a::args) in
    List.fold_left (fun t a -> App(t,a))(VarTerm(var, n', ty)) args'
  | Term.App(f,a,args) ->
    let f' = compile__term ty_ctx te_ctx f in
    let args' = List.map (fun x -> compile__term ty_ctx te_ctx x) (a::args) in
    List.fold_left (fun t a -> App(t,a)) f' args'
  | _ -> raise(CompileTermError(TermError(te)))


and _ty_of_ty (ty_ctx:ty_ctx) (te_ctx:term_ctx) (ty:ty) (args:Term.term list)
  : _ty * ty_subst * _term list =
  let poly_vars = poly_var_of_ty ty in
  let n = List.length poly_vars in
  let poly_args,args = split args n in
  let poly_args' = List.map (compile__type ty_ctx) poly_args in
  let subst = List.combine poly_vars poly_args' in
  let _ty = poly_subst_ty subst ty in
  let args' = List.map (compile__term ty_ctx te_ctx) args in
  _ty, subst, args'

and compile_term (ty_ctx:ty_ctx) (te_ctx:term_ctx) (te:Term.term) : term =
  match te with
  | Term.App(cst, Term.Lam(_,x, Some ty, te'), []) when is_hol_const hol_forall_kind_prop cst ->
    assert (is_hol_const hol_type ty);
    ForallT(x,compile_term (x::ty_ctx) (te_ctx) te')
  | _ ->  Term (compile__term ty_ctx te_ctx te)

let compile_eps_term (ty_ctx:ty_ctx) (te_ctx:term_ctx) (te:Term.term) : term =
  match te with
  | Term.App(cst, a, []) when is_hol_const hol_eps cst -> compile_term ty_ctx te_ctx a
  | _ -> assert false

let list_of_hol_theorem_with_eq =
  [mk_ident "eq_minus_O"; mk_ident "eq_minus_S_pred"; mk_ident "eq_to_eqb_true"; mk_ident "eq_to_eqb_false"; mk_ident "eq_times_div_minus_mod"; mk_ident "eq_to_bijn"; mk_ident "eq_minus_gcd_aux"; mk_ident "eq_div_O"; mk_ident "eq_minus_gcd"; mk_ident "eq_times_plus_to_congruent"; mk_ident "eq_mod_to_divides"; mk_ident "eq_fact_pi_p"]

let is_delta_rw cst =
  match cst with
  | Term.Const(_,name) ->
    not (Basic.mident_eq (md name) logic_module) && Str.(string_match (regexp "eq_\\|sym_eq") (string_of_ident (id name)) 0) && not (List.exists (fun thm -> id name === thm) list_of_hol_theorem_with_eq)
  | _ -> false

let get_infos_of_delta_rw md id = Str.(
    let id = string_of_ident id in
    if string_match (regexp "\\(__eq__\\)\\(.*\\)") id 0 then
      let id = matched_group 2 id in
      let cst = Term.mk_Const dloc (mk_name md (mk_ident id)) in
      match Env.reduction (Reduction.NSteps 1) cst with
      | OK te -> (mk_ident id),te
      | Err err -> Errors.fail_env_error err
    else
      assert false
)

let beta_step left =
  match left with
  | App(Lam(id,_ty,te), u) ->
    term_subst__te 0 u te
  | _ -> assert false

let rec snf_beta _term =
  match _term with
  | Forall(id,_ty,_te) -> Forall(id,_ty,snf_beta _te)
  | Impl(_tel,_ter) ->
    Impl(snf_beta _tel, snf_beta _ter)
  | Lam(id,_ty,_te) -> Lam(id,_ty,snf_beta _te)
  | App(Lam(id,_ty,_te), u) ->
    snf_beta (beta_step _term)
  | App(f,a) ->
    let f = App(snf_beta f, snf_beta a) in
    begin
      match f with
      | App(Lam _, _) -> snf_beta f
      | _ -> f
    end
  | _ -> _term

let one_step cst = Env.unsafe_one_step cst

let rec unfold_left t =
  match t with
  | Const((md,id),ty, ty_subst) ->
    let cst = Term.mk_Const dloc (mk_name md id) in
    let te = one_step cst in
    let te'= compile_term [] [] te in
    let _te = poly_subst_te ty_subst te' in
    _te
  | App(f,a) ->
    App(unfold_left f, a)
  | _ -> t

module type Trace =
sig

  val annotate : term -> prooft -> prooft

  val _annotate : ?prectx: int list -> _term -> _prooft -> _prooft

  val _replace : ?db: bool -> _term -> int list -> _term -> _term

  val replace : term -> int list -> _term -> term
end

module Trace : Trace = struct

  type trace = ctx * rw dir

  let print_ctx fmt ctx =
    Pp.print_list " " (fun fmt d -> Format.fprintf fmt "%d" d) fmt ctx

  let bind i pl =
    match pl with
    | None -> None
    | Some(ctx, rw) -> Some(i::ctx, rw)

  let rec _compare_naive ctx left right : (ctx * rw dir option) option =
    (*
    Format.eprintf "left: %a@." print_hol__term left;
    Format.eprintf "right: %a@." print_hol__term right; *)
    (* assume barendregt convention *)
    let is_unfoldable (md,id) =
      let name = mk_name md id in
      let cst = Term.mk_Const dloc name in
      let t =  one_step cst in
      if Term.term_eq cst t then false else true
    in
    (*
    let same_lambda x _ty te u t' =
      match t' with
      | App(Lam(x',_ty',te'), _) -> ident_eq x x' && _ty_eq ctx _ty _ty'
      | _ -> false
    in *)
    let rec ctx_of_app b app =
      match app with
      | Const(name, ty, subst) ->
        if b then
          Some([], Some(Unfold(Delta(name, ty, subst))))
        else
          Some([], Some(Fold(Delta(name, ty, subst))))
      | App(Lam(x,_ty,te) as f,u) ->
        if b then
          Some([], Some(Unfold(Beta(App(f,u)))))
        else
          Some([], Some(Fold(Beta(App(f,u)))))
      | App(f,a) ->
        bind 0 (ctx_of_app b f)
        (*
        let rw = bind 0 (ctx_of_app b f) in
        begin
          match rw with
          | Some([], None) -> bind 1 (ctx_of_app b a)
          | _ -> rw
        end
        *)
      | _ -> Some ([], None)
    in
    match (left,right) with
    | VarTerm(id, n, _ty), VarTerm(id', n', _ty') when n = n' && _ty_eq ctx _ty _ty' -> None
    (*    | VarTerm(id, n, _ty), VarTerm(id', n', _ty') when alpha_eq ctx id id && _ty_eq ctx _ty _ty' -> None *)
    | Const(name, ty, subst), Const(name', ty', subst') when name_eq name name' && _ty_eq ctx (poly_subst_ty subst ty) (poly_subst_ty subst' ty') -> None
    | Lam(id, _ty, _te), Lam(id', _ty', _te') when _ty_eq ctx _ty _ty' ->
      bind 0 (_compare_naive ((id,id')::ctx) _te _te')
    | Forall(id, _ty, _te), Forall(id', _ty', _te') when _ty_eq ctx _ty _ty' ->
      bind 0 (_compare_naive ((id,id')::ctx) _te _te')
    | Impl(_tel, _ter), Impl(_tel', _ter') ->
      begin
        match _compare_naive ctx _tel _tel' with
        | None -> bind 1 (_compare_naive ctx _ter _ter')
        | Some tr -> bind 0 (Some tr)
      end
    | App(Lam(x,_ty,te) as f, u), _ (* when not (same_lambda x _ty te u right) *)->
      Some ([], Some(Fold(Beta(App(f,u)))))
    | _,App(Lam(x,_ty,te) as f, u) (* when not (same_lambda x _ty te u left) *) ->
      Some ([], Some(Unfold(Beta(App(f,u)))))
    | Const(name, _ty, subst),_ when is_unfoldable name ->
      Some ([], Some(Fold(Delta(name,_ty,subst))))
    | _,Const(name, _ty, subst) when is_unfoldable name ->
      Some ([], Some(Unfold(Delta(name,_ty,subst))))
    | App(f,a), App(f', a') ->
      begin
        match _compare_naive ctx f f' with
        | None -> bind 1 (_compare_naive ctx a a')
        | Some tr -> bind 0 (Some tr)
      end
    | App(f, a), _ ->
      ctx_of_app false left
      (*
      let rw = ctx_of_app false left in
      begin
        match rw with
        | Some([],None) -> ctx_of_app true right
        | _ -> rw
      end
      *)
    | _ , App(f, a) ->
      ctx_of_app true right
        (*
    | App(f, a), Impl(_, _) ->
      ctx_of_app false left
    | Impl(_, _), App(f, a) ->
      ctx_of_app true right
    | Forall(_,_,_), App(f, a) ->
      ctx_of_app true right
    | App(f, a), Forall(_, _, _) ->
      ctx_of_app false left
*)
    | _,_ ->
      Some ([], None)

  let _replace ?(db=false) t ctx u =
    let rec _replace k t ctx u =
      (* Format.eprintf "debug _replace: %a by %a at %a@." print_hol__term t print_hol__term u print_ctx ctx; *)
      match t, ctx with
      | _, [] -> if db then _lift k 0 u else u
      | Forall(id,_ty,_term), 0::ctx' ->
        Forall(id,_ty,_replace (k+1) _term ctx' u)
      | Impl(tel,ter), i::ctx' ->
        let tel' = if i = 0 then _replace k tel ctx' u else tel in
        let ter' = if i = 1 then _replace k ter ctx' u else ter in
        Impl(tel',ter')
      | Lam(id,ty, _te), 0::ctx' -> Lam(id,ty,_replace (k+1) _te ctx' u)
      | App(f,a), i::ctx' ->
        let f' = if i = 0 then _replace k f ctx' u else f in
        let a' = if i = 1 then _replace k a ctx' u else a in
        App(f',a')
      | _ ->  assert false
    in
    _replace 0 t ctx u

  let rec _annotate ?(prectx=[]) (_t:_term) (_pt:_prooft) : _prooft =
    (* Format.eprintf "_annotate:@. %a@.%a@." print_hol__term _t print_hol__term _pt._term; *)
    match _compare_naive [] _t _pt._term with
    | None -> {_pt with _term = _t}
    | Some (ctx,None) ->
      _backtrack ~prectx:prectx _t _pt (*
      Format.eprintf "%a@.%a@." print_hol__term _t print_hol__term _pt._term;
        failwith "are they convertible?" *)
    | Some (ctx,Some rw) ->
      let ctx = prectx@ctx in
      match rw with
      | Fold(Delta(name,_ty,subst)) ->
        (* Format.eprintf "unfold delta: %a@." print_name name; *)
        let cst = const_of_name name in
        let te = one_step cst in
        let te'= compile_term [] [] te in
        let _te = poly_subst_te subst te' in
        let _t' = _replace _t ctx _te in
        let _pt' = _annotate _t' _pt in
        let _proof = RewriteU(ctx,rw,_pt') in
        let _term = _replace _pt'._term ctx (Const(name,_ty,subst)) in
        {_term;_proof}
      | Fold(Beta(term)) ->
        (* Format.eprintf "fold beta: %a@." print_hol__term term; *)
        let _t' = _replace _t ctx (beta_step term) in
        let _pt' = _annotate _t' _pt in
        let _proof = RewriteU(ctx,rw,_pt') in
        let _term = _replace _pt'._term ctx term in
        {_term;_proof}
      | Unfold(Beta(term)) ->
        (* Format.eprintf "unfold beta: %a@." print_hol__term term; *)
        let _term = _replace _pt._term ctx (beta_step term) in
        let _proof = RewriteU(ctx,rw,_pt) in
        let pt' = {_term; _proof} in
        _annotate _t pt'
      | Unfold(Delta(name,_ty,subst)) ->
        (* Format.eprintf "fold delta: %a@." print_name name; *)
        let cst = const_of_name name in
        let te = one_step cst in
        let te'= compile_term [] [] te in
        let _te = poly_subst_te subst te' in
        let _term = _replace _pt._term ctx _te in
        let _proof = RewriteU(ctx,rw,_pt) in
        _annotate _t {_term;_proof}
      | _ -> assert false
        (*
    with e ->
      Format.eprintf "%s@." (Printexc.to_string e);
      if !bool then
        _backtrack ~prectx:prectx _t _pt
      else
        Errors.fail dloc "Contextual error: The terms %a and %a seems not to be convertible."
          print_hol__term _t print_hol__term _pt._term
     *)
  and _backtrack ?(prectx=[]) (_t:_term) (_pt:_prooft) : _prooft =
    let _term' = snf_beta _pt._term in
    if _term' = _pt._term then
      let _t' = snf_beta _t in
      if _t' = _t then
        let _t' = unfold_left _t in
        if _t' = _t then assert false (*
          (
            Format.eprintf "left: %a@.right: %a@." print_hol__term _t print_hol__term _t';
            Errors.fail dloc
              "Contextual error: The terms %a and %a seems not to be convertible."
              print_hol__term _t print_hol__term _pt._term
          ) *)
        else
          let _pt' = _annotate ~prectx:prectx _t' _pt in
        _annotate ~prectx:prectx _t _pt'
      else
        let _pt' = _annotate ~prectx:prectx _t' _pt in
        _annotate ~prectx:prectx _t _pt'
    else
      let _pt' = _annotate ~prectx:prectx _term' _pt in
      _annotate ~prectx:prectx _t _pt'


  let rec replace t ctx u =
    match t,ctx with
    | ForallT(x,te),0::ctx' -> ForallT(x,replace te ctx' u)
    | Term(_te), 0::ctx' -> Term(_replace _te ctx' u)
    | _ -> assert false

  let rec alpha_rename_type left right =
    match left,right with
    | ForallT(name, te), ForallT(name',te') ->
      ForallT(name',alpha_rename_type te te')
    | Term(t), Term(_) -> Term(t)
    | _ -> assert false


  let rec compare ctx left right : (ctx * rw dir option) option =
    match (left,right) with
    | Term(_te), Term(_te') -> bind 0 (_compare_naive ctx _te _te')
    | ForallT(id,te), ForallT(id', te') ->
      bind 0 (compare ((id,id')::ctx) te te')
    | _, _ -> Some ([], None)

  let rec annotate (t:term) (pt:prooft) : prooft =
    (* Format.eprintf "annotate:@. %a@.%a@." print_hol_term t print_hol_term pt.term; *)
    let to_trace ctx rw =
      match rw with
      | Some(rw) -> (ctx, rw)
      | None -> Format.printf "%b@." (t = pt.term);
        Errors.fail dloc "Contextual error: The terms %a and %a seems not to be convertible. They differ at position %a"
          print_hol_term t print_hol_term pt.term print_ctx ctx
    in
    match compare [] t pt.term with
    | None -> {pt with term = alpha_rename_type t pt.term}
    | Some (ctx,rw) ->
      let ctx,rw = to_trace ctx rw in
      match rw with
      | Fold(Delta(name,_ty,subst)) ->
        let cst = const_of_name name in
        let te = one_step cst in
        let te'= compile_term [] [] te in
        let _te = poly_subst_te subst te' in
        let t' = replace t ctx _te in
        let pt' = annotate t' pt in
        let proof = RewriteF(ctx,rw,pt') in
        let term = replace pt'.term ctx (Const(name,_ty,subst)) in
        {term;proof}
      | Unfold(Beta(term)) ->
        let proof = RewriteF(ctx,rw,pt) in
        let term = replace pt.term ctx (beta_step term) in
        annotate t ({term;proof})
      | Fold(Beta(term)) ->
        let t' = replace t ctx (beta_step term) in
        let pt' = annotate t' pt in
        let proof = RewriteF(ctx,rw,pt') in
        let term = replace pt'.term ctx term in
        {term;proof}
      | Unfold(Delta(name,_ty,subst)) ->
        let cst = const_of_name name in
        let te = one_step cst in
        let te'= compile_term [] [] te in
        let _te = poly_subst_te subst te' in
        let term = replace pt.term ctx _te in
        let proof = RewriteF(ctx,rw,pt) in
        annotate t {term;proof}
      | _ -> assert false


end


let rec ctx_of__term term var =
  match term with
  | Forall(id, _ty, _te) ->
    let k,b,ctx = ctx_of__term _te var in
    k+1,b,0::ctx
  | Impl(_tel, _ter) ->
    let k,bl, ctxl = ctx_of__term _tel var in
    let k',br, ctxr = ctx_of__term _ter var in
    if bl then
      if br then
        failwith "the variable appears twice"
      else
        k,bl, 0::ctxl
    else
      k',br, 1::ctxr
  | VarTerm(id, n, _ty) ->
    if ident_eq id var then
      0,true,[]
    else
      0,false,[]
  | Const _ -> 0,false, []
  | App(_tel,_ter) ->
    let k,bl, ctxl = ctx_of__term _tel var in
    let k',br, ctxr = ctx_of__term _ter var in
    if bl then
      if br then
        failwith "the variable appears twice"
      else
        k,bl,0::ctxl
    else
      k',br,1::ctxr
  | Lam(id, _ty, _te) ->
    let k,b,ctx = ctx_of__term _te var in
    k+1,b,0::ctx

let rec ctx_of_term term var =
  match term with
  | ForallT(id,te) ->
    let k,ctx = ctx_of_term te var in
    k,0::ctx
  | Term(_te) ->
    let k,b,ctx = ctx_of__term _te var in
    if b then
      k,ctx
    else
      assert false

let prefix n =
    "_"^(string_of_int n)^"_"

let pre n id = mk_ident @@ prefix n ^(string_of_ident id)

let post n id = mk_ident (string_of_ident id ^ "_" ^ (string_of_int n))

let rec alpha_rename__term bdg _term =
  let rec find_id' id n =
    let id' = post n id in
    if List.mem id' bdg then
      find_id' id (n+1)
    else
      id'
  in
  match _term with
  | Forall(id,_ty,_te) ->
    let id' =
      if List.mem id bdg then
        find_id' id 0
      else
        id
    in
    let binding, _te' = alpha_rename__term (id'::bdg)  _te in
    binding, Forall(id', _ty, _te')
  | Impl(_tel, _ter) ->
    let bindingl, _tel' = alpha_rename__term bdg _tel in
    let bindingr, _ter' = alpha_rename__term bdg _ter in
    bindingl@bindingr,Impl(_tel', _ter')
  | VarTerm(id, i, _ty) ->
    if i < List.length bdg then
      [], VarTerm(List.nth bdg i, i, _ty)
    else
      [], VarTerm(id, i, _ty)
  | App(f,a) ->
    let bindingf,f' = alpha_rename__term bdg f in
    let bindinga,a' = alpha_rename__term bdg a in
    bindingf@bindinga, App(f',a')
  | Lam(id,_ty, _te) ->
    let id' =
      if List.mem id bdg then
        find_id' id 0
      else
        id
    in
    let binding,_te' = alpha_rename__term (id'::bdg) _te in
    binding, Lam(id',_ty, _te')
  | Const _ -> [],_term

let rec alpha_rename_term bdg term =
  match term with
  | ForallT(id, te) ->
    let binding, te' = alpha_rename_term bdg te in
    binding,ForallT(id, te')
  | Term(_te) ->
    let binding, _te' = alpha_rename__term bdg _te in
    binding, Term(_te')

let rec alpha_rename__term_ctx bdg ctx _term =
  let rec find_id' id n =
    let id' = post n id in
    if List.mem id' bdg then
      find_id' id (n+1)
    else
      id'
  in
  match _term, ctx with
  | _, [] ->
    [], snd @@ alpha_rename__term bdg _term
  | Forall(id,_ty,_te), 0::ctx ->
    let id' =
      if List.mem id bdg then
        find_id' id 0
      else
        id
    in
    let binding, _te' = alpha_rename__term_ctx (id'::bdg) ctx _te in
    (id'::binding), Forall(id', _ty, _te')
  | Impl(_tel, _ter), i::ctx ->
    if i = 0 then
      let binding, _tel' = alpha_rename__term_ctx bdg ctx _tel in
      let _,_ter' = alpha_rename__term bdg _ter in
      binding, Impl(_tel', _ter')
    else if i = 1 then
      let _,_tel' = alpha_rename__term bdg _tel in
      let binding, _ter' = alpha_rename__term_ctx bdg ctx _ter in
      binding, Impl(_tel', _ter')
    else assert false
  | App(f,a), i::ctx ->
    if i = 0 then
      let binding, f' = alpha_rename__term_ctx bdg ctx f in
      let _,a' = alpha_rename__term bdg a in
      binding, App(f', a')
    else if i = 1 then
      let _,f' = alpha_rename__term bdg f in
      let binding, a' = alpha_rename__term_ctx bdg ctx a in
      binding, App(f', a')
    else assert false
  | Lam(id,_ty, _te), 0::ctx ->
    let id' =
      if List.mem id bdg then
        find_id' id 0
      else
        id
    in
    let binding,_te' = alpha_rename__term_ctx (id'::bdg) ctx _te in
    (id'::binding), Lam(id',_ty, _te')
  | _ -> assert false

let rec alpha_rename_term_ctx bdg ctx term =
  match term, ctx with
  | ForallT(id, te), 0::ctx ->
    let binding, te' = alpha_rename_term_ctx bdg ctx te in
    binding,ForallT(id, te')
  | Term(_te), 0::ctx ->
    let binding, _te' = alpha_rename__term_ctx bdg ctx _te in
    binding, Term(_te')
  | _ -> assert false

let rec alpha_rename_rw bdg rw =
  (* Format.eprintf "rw ctx: @[%a@]@." (Pp.print_list " " Pp.print_ident) bdg; *)
  match rw with
  | Fold(Delta( _)) -> rw
  | Unfold(Delta(_)) -> rw
  | Fold(Beta(te)) ->
    let te' = snd @@ alpha_rename__term bdg te in
   (*  Format.eprintf "Fold Beta@.";
       Format.eprintf "before: %a@.right: %a@." print_hol__term te print_hol__term te'; *)
    Fold(Beta(te'))
  | Unfold(Beta(te)) ->
    let te' = snd @@ alpha_rename__term bdg te in
    (* Format.eprintf "Unfold Beta@.";
       Format.eprintf "before: %a@.right: %a@." print_hol__term te print_hol__term te'; *)
    Unfold(Beta(te'))
  | Fold(Gamma(_proof, _tel, _ter)) ->
    let fake = {_proof=_proof; _term = _tel} in
    let _proof' = (snd @@ alpha_rename__prooft bdg fake)._proof in
    let _tel' = snd @@ alpha_rename__term bdg _tel in
    let _ter' = snd @@ alpha_rename__term bdg _ter in
    Fold(Gamma(_proof', _tel', _ter'))
  | Unfold(Gamma(_proof, _tel, _ter)) ->
    let fake = {_proof=_proof; _term = _tel} in
    let _proof' = (snd @@ alpha_rename__prooft bdg fake)._proof in
    let _tel' = snd @@ alpha_rename__term bdg _tel in
    let _ter' = snd @@ alpha_rename__term bdg _ter in
    (* Format.eprintf "Unfold Gamma@.";
    Format.eprintf "left before: %a@.left after: %a@." print_hol__term _tel print_hol__term _tel';
       Format.eprintf "right before: %a@.right after: %a@." print_hol__term _ter print_hol__term _ter'; *)
    Unfold(Gamma(_proof', _tel', _ter'))


and alpha_rename__prooft bdg _prooft =
  (* Format.eprintf "current term: @[%a@]@." print_hol__term _prooft._term; *)
  let rec find_id' id n =
    let id' = post n id in
    if List.mem id' bdg then
      find_id' id (n+1)
    else
      id'
  in
  let _proof =
    match _prooft._proof with
    | Lemma(name, term, ty_subst) ->
      Lemma(name, term, ty_subst)
    | Assume(_term, ty_subst) ->
      let _,_term' = alpha_rename__term bdg _term in
      Assume(_term', ty_subst)
    | ForallI(id, _ty, _prooft) ->
      let id' =
        if List.mem id bdg then
          find_id' id 0
        else
          id
      in
      let _, _prooft' = alpha_rename__prooft (id'::bdg) _prooft in
      ForallI(id', _ty, _prooft')
    | ImplI(_term, _prooft) ->
      let _,_term' = alpha_rename__term bdg _term in
      let _,_prooft' = alpha_rename__prooft bdg _prooft in
      ImplI(_term', _prooft')
    | ForallE(_prooft, _term) ->
      let _,_prooft' = alpha_rename__prooft bdg _prooft in
      (*
      Format.eprintf "before: %a@.right: %a@."
        print_hol__term _prooft._term print_hol__term _prooft'._term;
*)
      let _,_term' = alpha_rename__term bdg _term in
      ForallE(_prooft', _term')
    | ImplE(_prooftl, _prooftr) ->
      let _,_prooftl' = alpha_rename__prooft bdg _prooftl in
      let _,_prooftr' = alpha_rename__prooft bdg _prooftr in
      ImplE(_prooftl', _prooftr')
    | RewriteU(rw_ctx, rw, _prooft) ->
      let binding, term' = alpha_rename__term_ctx bdg rw_ctx _prooft._term in
      (* Format.eprintf "ctx before: @[%a@]@." (Pp.print_list " " Pp.print_ident) bdg;
      Format.eprintf "ctx after: @[%a@]@." (Pp.print_list " " Pp.print_ident) binding;
         Format.eprintf "rewriteU@.before: %a@.right: %a@."
         print_hol__term _prooft._term print_hol__term term'; *)
      let rw' = alpha_rename_rw (List.rev binding@bdg) rw in
      let binding, prooft' = alpha_rename__prooft bdg _prooft in
      RewriteU(rw_ctx, rw', prooft')
  in
  let binding,_term = alpha_rename__term bdg _prooft._term in
  (*
  Format.eprintf "ctx: @[%a@]@." (Pp.print_list " " Pp.print_ident) bdg;
  Format.eprintf "before: %a@.right: %a@." print_hol__term _prooft._term print_hol__term _term;
  *)
  binding,{_term;_proof}

let rec alpha_rename_prooft bdg prooft =
  let binding,term = alpha_rename_term bdg prooft.term in
  (* Format.eprintf "prooft@.before: %a@.right: %a@." print_hol_term prooft.term print_hol_term term; *)
  let proof =
    match prooft.proof with
    | ForallP(id, prooft) ->
      let _,prooft = alpha_rename_prooft bdg prooft in
      ForallP(id, prooft)
    | Proof(_prooft) ->
      let _,_prooft = alpha_rename__prooft bdg _prooft in
      Proof(_prooft)
    | RewriteF(rw_ctx,rw,prooft) ->
      let binding, term' = alpha_rename_term_ctx bdg rw_ctx prooft.term in
      let rw' = alpha_rename_rw (List.rev binding@bdg) rw in
      let _, prooft' = alpha_rename_prooft bdg prooft in
      RewriteF(rw_ctx, rw', prooft')
  in
  binding,{term;proof}



let rec _bound_variable_renaming ctx n _term =
  match _term with
  | Forall(id,_ty,_te) ->
    Forall(pre n id, _ty, _bound_variable_renaming (pre n id::ctx) (n+1) _te)
  | Impl(_tel, _ter) ->
    Impl(_bound_variable_renaming ctx n _tel, _bound_variable_renaming ctx n _ter)
  | VarTerm(id, i, _ty) ->
    if i < List.length ctx then
      VarTerm(List.nth ctx i, i, _ty)
    else
      VarTerm(id, i, _ty)
  | App(f,a) ->
    App(_bound_variable_renaming ctx n f, _bound_variable_renaming ctx n a)
  | Lam(id,_ty, _te) ->
    Lam(pre n id, _ty, _bound_variable_renaming (pre n id::ctx) (n+1) _te)
  | _ -> _term

let rec bound_variable_renaming  term =
  match term with
  | ForallT(id, te) -> ForallT(id, bound_variable_renaming te)
  | Term(_te) -> Term(_bound_variable_renaming [] 0 _te)

let rec with_ctx args =
  List.exists (fun t -> match t with | Term.Lam _ -> true | _ -> false) args

let rec arguments_needed rw =
  let ty =
    match rw with
    | Term.Const(lc, name) ->
      begin
        match Env.get_type lc name with
        | OK ty -> ty
        | Err err -> Errors.fail_signature_error err
      end
    | _ -> assert false
  in
  let rec aux t n =
    let is_forall_prop name =
      Basic.mident_eq (md name) hol_module && (id name) === hol_forall_kind_prop
    in
    let is_forall name =
      Basic.mident_eq (md name) hol_module && (id name) === hol_forall
    in
    match t with
    | Term.App(Term.Const(_,name),_,_) when
        (Basic.mident_eq (md name) hol_module) && (id name) === hol_leibniz -> n
    | Term.App(Term.Const(_,name),Term.Lam(_,_,_,te),[]) when is_forall_prop name -> aux te (n+1)
    | Term.App(Term.Const(_,name),_,[Term.Lam(_,_,_,te)]) when is_forall name -> aux te (n+1)
    | Term.App(Term.Const(_,name), t', [])
      when (Basic.mident_eq (md name) hol_module) && (id name) === hol_eps -> aux t' n
    | _ -> Format.eprintf "debug: %a@." Pp.print_term rw; assert false
  in
  aux ty 0

let rec compile__proof (ty_ctx:ty_ctx) (te_ctx:term_ctx) (pf_ctx:proof_ctx) proof : _prooft =
  let lift_pf_ctx n pf_ctx =
    let lift_binding n (id,te) =
      (id,lift 1 te)
    in
    List.map (lift_binding n) pf_ctx
  in
  match proof with
  | Term.App(rw, a, args) when is_delta_rw rw && List.length (a::args) > arguments_needed rw ->
    (* Format.eprintf "args: %d@." (Pp.print_list "\n" Pp.print_term) (a::args); *)
    let rec find_ctx args n =
      match args,n with
      | [],_ -> assert false
      | [_],_ -> assert false
      | ctx::r::t,0 -> [], ctx,r,t
      | x::args',_ ->
        let l,ctx,r,t = find_ctx args' (n-1) in
        x::l,ctx,r,t
    in
    let l,ctx,r,t = find_ctx (a::args) (arguments_needed rw) in
    let _pt =
      match l with
      | [] -> compile__proof ty_ctx te_ctx pf_ctx rw
      | x::t -> compile__proof ty_ctx te_ctx pf_ctx (Term.mk_App rw x t)
    in
    let left,right =
      match _pt._term with
      | App(App(_,l),r) -> l,r
      | _ -> assert false
    in
    let _pt' = compile__proof ty_ctx te_ctx pf_ctx r in
    let ctx' = compile__term ty_ctx te_ctx ctx in
    let _term' = beta_step (App(ctx', left)) in
    let _pt' = Trace._annotate _term' _pt' in
    let k,ctx =
      match ctx with
      | Term.Lam (_,id, Some ty, te) ->
        let ty' = compile__type ty_ctx ty in
        let te' = (compile_term ty_ctx ((id,ty')::te_ctx) te) in
        ctx_of_term te' id
      | _ -> Format.eprintf "debug ctx: %a@." Pp.print_term ctx ;assert false
    in
    (*
    Format.eprintf "rewriteU@.";
    Format.eprintf "before@.left %a@.right %a@." print_hol__term left print_hol__term right;
    Format.eprintf "after@.left %a@.right %a@." print_hol__term (_lift k 0 left) print_hol__term (_lift k 0 right);
    *)
    let _proof = RewriteU(ctx, Unfold(Gamma(proof_lift k 0 _pt._proof _pt._term , _lift k 0 left, _lift k 0 right)), _pt') in
    let _term = Trace._replace ~db:true _pt'._term ctx right in
    let pt = {_proof;_term} in
    compile_app ty_ctx te_ctx pf_ctx pt t
  | Term.Lam(_,x, Some ty, proof) when is_type ty ->
    let pf_ctx = lift_pf_ctx 1 pf_ctx in
    let _ty' = compile_eta__type ty_ctx ty in
    let _prooft' = compile__proof ty_ctx ((x,_ty')::te_ctx) pf_ctx proof in
    let _term = Forall(x,_ty', _prooft'._term) in
    let _proof = ForallI(x,_ty', _prooft') in
    {_term;_proof}
  | Term.Lam(_,x, Some te, proof) when is_term te ->
    let te' = compile_eps_term ty_ctx te_ctx te in
    let _prooft' = compile__proof ty_ctx te_ctx ((x,te')::pf_ctx) proof in
    let _te' =
      match te' with
      | ForallT _ -> assert false
      | Term(_te) -> _te
    in
    let _term = Impl(_te', _prooft'._term) in
    let _proof = ImplI(_te', _prooft') in
    {_term;_proof}
  | Term.DB(_,id,_) ->
    if List.mem_assoc id pf_ctx then
      let te' = List.assoc id pf_ctx in
      let _term =
        match te' with
        | ForallT _ -> assert false
        | Term(_te) -> _te
      in
      let _proof = Assume(_term,[]) in
      {_term;_proof}
    else
      (Format.eprintf "id:%a@." Pp.print_ident id; assert false)
  | Term.Const(lc, name) ->
    let te =
      match Env.get_type lc name with
      | OK ty -> ty
      | Err err -> Errors.fail_signature_error err
    in
    let te' = compile_eps_term ty_ctx te_ctx te in
    let _term =
      match te' with
      | ForallT _ -> assert false
      | Term(_te) -> _te
    in
    let _proof = Lemma(mk_hol_name name,te', []) in
    {_term;_proof}
  | Term.App(Term.Const(lc, name),a,args) ->
    let te =
      match Env.get_type lc name with
      | OK ty -> ty
      | Err err -> Errors.fail_signature_error err
    in
    let te' = compile_eps_term ty_ctx te_ctx te in
    let _te', subst, args = _te_of_te ty_ctx te_ctx te' (a::args) in
    let prooft  = {_term=_te'; _proof= Lemma(mk_hol_name name,te', subst)} in
    compile_app ty_ctx te_ctx pf_ctx prooft args
  | Term.App(Term.DB(_,var,_),a,args) ->
    let te' =
      if List.mem_assoc var pf_ctx then
        List.assoc var pf_ctx
      else
        assert false
    in
    let _te', subst, args = _te_of_te ty_ctx te_ctx te' (a::args) in
    let prooft:_prooft = {_term=_te'; _proof= Assume(_te', subst)} in
    compile_app ty_ctx te_ctx pf_ctx prooft args
  | _ -> failwith "todo proof"

and _te_of_te (ty_ctx:ty_ctx) (te_ctx:term_ctx) (te:term) (args:Term.term list) =
  let poly_vars = poly_var_of_te te in
  let n = List.length poly_vars in
  let poly_args,args = split args n in
  let poly_args' = List.map (compile__type ty_ctx) poly_args in
  let subst = List.combine poly_vars poly_args' in
  let _te = poly_subst_te subst te in
  _te, subst, args

and compile_app (ty_ctx:ty_ctx) (te_ctx:term_ctx) (pf_ctx:proof_ctx) (prooft:_prooft)
    (args:Term.term list) : _prooft =
  let rec compile_arg (prooft:_prooft) arg =
    (*  Format.eprintf "debug:  %a@." print_hol__term prooft._term;
        Format.eprintf "term: %a@." Pp.print_term arg; *)
    let _term = prooft._term in
    match _term with
    | Forall(id,_ty,_term) ->
      let _term' = compile__term ty_ctx te_ctx arg in
      let term = term_subst__te id _term' _term in
      let pt = {_term=term;_proof=ForallE(prooft, _term')} in
      let term' = snf_beta term in
      Trace._annotate term' pt
    | Impl(_tel, _telr) ->
      let prooft' = compile__proof ty_ctx te_ctx pf_ctx arg in
      let prooft' = Trace._annotate _tel prooft' in
      {_term=_telr;_proof=ImplE(prooft, prooft')}
    | App(Const(name, _ty, subst), _tes) ->
      let cst = const_of_name name in
      let te = one_step cst in
      let te'= compile_term [] [] te in
      let _te = poly_subst_te subst te' in
      let _te' = snf_beta (App(_te, _tes)) in
      let pt' = Trace._annotate _te' prooft in
      compile_arg pt' arg
    | App(VarTerm(id, i, _ty), _tes) -> assert false
    | App(f,a) ->
      let term' = unfold_step prooft._term (fun x -> x) in
      let term' = snf_beta term' in
      let pt' = Trace._annotate term' prooft in
      compile_arg pt' arg
    | Const _
    | VarTerm _ -> assert false
    | Lam _ -> assert false
  in
  List.fold_left compile_arg prooft args

and unfold_step t k =
  match t with
  | Const(name, _ty, subst) ->
    let cst = const_of_name name in
    let te = one_step cst in
    let te'= compile_term [] [] te in
    let _te = poly_subst_te subst te' in
    k _te
  | App(f,a) ->
    unfold_step f (fun f' -> k (App(f',a)))
  | _ -> assert false



let rec compile_proof (ty_ctx:ty_ctx) (te_ctx:term_ctx) (proof:Term.term) : prooft =
  match proof with
  | Term.Lam(_,x, Some ty, proof') when is_hol_const hol_type ty ->
    let prooft' = compile_proof (x::ty_ctx) te_ctx proof' in
    {term=ForallT(x,prooft'.term); proof=ForallP(x, prooft')}
  | _ ->
    let _prooft' = compile__proof ty_ctx te_ctx [] proof in
    {term=Term(_prooft'._term); proof=Proof(_prooft')}

let compile_declaration (lc:loc) (name:Basic.name) (te:Term.term) : (obj, compile_decl_err) error =
  try
    match te with
    | Term.App(cst,a,[]) when is_hol_const hol_etap cst ->
      OK(Cst(mk_hol_name name, compile_type [] a, None))
    | Term.App(cst,a,[]) when is_hol_const hol_eps cst ->
      OK(Thm(mk_hol_name name, compile_term [] [] a, None))
    | Term.Const(_, name) when is_hol_const hol_type te ->
      OK(TyOp(mk_hol_name name, []))
    | _ -> Err(DeclarationError(lc,id name,te))
  with
  | CompileTermError(err) ->
    Err(DeclarationTermError(err,(lc,id name,te)))
  | CompileTypeError(err) ->
    Err(DeclarationTypeError(err,(lc,id name,te)))

let fail_compile_declaration (err:compile_decl_err) : 'a =
  match err with
  | DeclarationError(lc,id,te) ->
    Errors.fail lc "Error while compiling the declaration '%a:%a'. It seems that the type is not recognized by the compiler." Pp.print_ident id Pp.print_term te
  | DeclarationTermError(err,(lc,id,te)) ->
    begin
      match err with
      | UntypedLambda(te) ->
        Errors.fail lc "Error while compiling the declaration '%a' as an axiom. The term %a has untyped lambdas." Pp.print_ident id Pp.print_term te
      | TermError(te) ->
        Errors.fail lc "Error while compiling the declaration '%a' as an axiom. The term %a seems not to be an hol theorem." Pp.print_ident id Pp.print_term te
    end
  | DeclarationTypeError(err,(lc,id,te)) ->
    begin
      match err with
      | TypeError(ty) ->
        Errors.fail lc "Error while compiling the declaration '%a' as a constant. The type %a seems not to be an hol type." Pp.print_ident id Pp.print_term te
    end

let rec has_beta' te =
  match te with
  | Forall(_,_,te) -> has_beta' te
  | Impl(tel,ter) -> has_beta' tel || has_beta' ter
  | VarTerm _
  | Const _ -> false
  | Lam(_,_,te) -> has_beta' te
  | App(Lam(_,_,_), _) -> true
  | App(f,a) ->
    has_beta' f || has_beta' a

let rec has_beta te =
  match te with
  | ForallT(_,te) -> has_beta te
  | Term te -> has_beta' te

let compile_definition (lc:loc) (name:Basic.name) (ty:Term.term) (te:Term.term)
  : (obj, compile_defn_err) error =
  Format.eprintf "Compilation of definition %a@." Pp.print_ident (id name);
  try
    match ty with
    | Term.App(cst,a,[]) when is_hol_const hol_etap cst ->
      let te' = compile_term [] [] te in
      OK(Cst(mk_hol_name name, compile_type [] a, Some te'))
    | Term.App(cst,a,[]) when is_hol_const hol_eps cst ->
      let thm = compile_term [] [] a in
      let proof = compile_proof [] [] te in
      let proof' = Trace.annotate thm proof in
      let _,proof'' = alpha_rename_prooft [] proof' in
      OK(Thm(mk_hol_name name, thm, Some proof''))
    | _ -> Err(DefinitionError((lc,id name,te),ty))
  with
  | CompileTermError(err) ->
    Err(DefinitionTermError(err,(lc,id name,te),ty))
  | CompileTypeError(err) ->
    Err(DefinitionTypeError(err,(lc,id name,te),ty))
  | CompileProofError(err) ->
    Err(DefinitionProofError(err,(lc,id name,te),ty))

let fail_compile_definition (err:compile_defn_err) : 'a =
  match err with
  | DefinitionError((lc,id,te),ty) ->
    Errors.fail lc "Error while compiling the definition '%a:%a:=%a'. It seems that the definition is not recognized by the compiler." Pp.print_ident id Pp.print_term te Pp.print_term ty
  | DefinitionTermError(err,(lc,id,te),ty) ->
    begin
      match err with
      | UntypedLambda(te) ->
        Errors.fail lc "Error while compiling the definition '%a'. The term %a has untyped lambdas." Pp.print_ident id Pp.print_term te
      | TermError(te) ->
        Errors.fail lc "Error while compiling the definition '%a'. The term %a seems not to be an hol theorem." Pp.print_ident id Pp.print_term te
    end
  | DefinitionTypeError(err,(lc,id,te),ty) ->
    begin
      match err with
      | TypeError(ty) ->
        Errors.fail lc "Error while compiling the definition '%a' as a constant. The type %a seems not to be an hol term." Pp.print_ident id Pp.print_term te
    end
  | DefinitionProofError(err,(lc,id,te),ty) ->
    begin
      match err with
      | ProofError(ty) ->
        Errors.fail lc "Error while compiling the definition '%a' as a proof. The term %a seems not to be an hol proof." Pp.print_ident id Pp.print_term te
    end
module OT = Openstt.OpenTheory

(* FIXME: rename this *)
let name_of_var var = OT.mk_name [] (string_of_ident var)

let compile_hol_name (md,id) =
  let md' = string_of_mident md in
  let id' = string_of_ident id in
  OT.mk_name [md'] id'


(* FIXME: ctx are unecessary. They can be useful to make some assertions *)
let rec compile_hol__type (ty_ctx:ty_ctx) (_ty:_ty) =
  match _ty with
  | VarTy(var) -> OT.mk_varType (name_of_var var)
  | Arrow(_tyl,_tyr) ->
    let _tyl' = compile_hol__type ty_ctx _tyl in
    let _tyr' = compile_hol__type ty_ctx _tyr in
    OT.mk_arrow_type _tyl' _tyr'
  | OpType(name, tys) ->
    let tyop' = OT.mk_tyOp (compile_hol_name name) in
    let tys' = List.map (compile_hol__type ty_ctx) tys in
    OT.ty_of_tyOp tyop' tys'
  | Bool -> OT.mk_bool_type ()

let rec compile_hol_type (ty_ctx:ty_ctx) (ty:ty) =
  match ty with
  | ForallK(var,te) -> compile_hol_type (var::ty_ctx) te
  | Type(te) -> compile_hol__type ty_ctx te

let rec conflict ctx _term =
  match _term with
  | App(f,a) -> conflict ctx f || conflict ctx a
  | Impl(f,a) -> conflict ctx f || conflict ctx a
  | Lam(id,ty,te) ->
    if List.mem id ctx then true
    else
      conflict (id::ctx) te
  | Forall(id,ty,te) ->
    if List.mem id ctx then true
    else
      conflict (id::ctx) te
  | Const _ -> false
  | VarTerm _ -> false


let is_hol_equal (md,id) = (Basic.mident_eq md hol) && id === hol_leibniz
(* FIXME: ctx are unecessary. They can be useful to make some assertions *)
let rec compile_hol__term (ty_ctx:ty_ctx) (te_ctx:term_ctx) term =
  match term with
  | Forall(var,_ty, _te) ->
    let _ty' = compile_hol__type ty_ctx _ty in
    let lambda = Lam(var, _ty,_te) in
    let lambda' = compile_hol__term ty_ctx te_ctx lambda in
    OT.mk_forall_term lambda' _ty'
  | Impl(_tel, _ter) ->
    let _tel' = compile_hol__term ty_ctx te_ctx _tel in
    let _ter' = compile_hol__term ty_ctx te_ctx _ter in
    OT.mk_impl_term _tel' _ter'
  | App(App(Const(name,ty, subst),l),r) when is_hol_equal name ->
    let l' = compile_hol__term ty_ctx te_ctx l in
    let r' = compile_hol__term ty_ctx te_ctx r in
    let _ty' =
      match (poly_subst_ty subst ty) with
      | Arrow(l,Arrow(_,_)) -> l
      | _ -> (* Format.eprintf "debug: %a@." print_hol_type ty; *) assert false
    in
    let _ty' = compile_hol__type ty_ctx _ty' in
    OT.mk_equal_term l' r' _ty'
  | App(f, a) ->
    let f' = compile_hol__term ty_ctx te_ctx f in
    let a' = compile_hol__term ty_ctx te_ctx a in
    OT.mk_app_term f' a'
  | VarTerm(var, n, _ty) ->
    let _ty' = compile_hol__type ty_ctx _ty in
    OT.mk_var_term (OT.mk_var (name_of_var var) _ty')
  | Const(name, ty, subst) ->
    let ty' = compile_hol__type ty_ctx (poly_subst_ty subst ty) in
    let cst = OT.const_of_name (compile_hol_name name) in
    OT.term_of_const cst ty'
  | Lam(var, _ty,_term) ->
    let _term' = compile_hol__term ty_ctx ((var, _ty)::te_ctx) _term in
    let _ty' = compile_hol__type ty_ctx _ty in
    let var' = OT.mk_var (name_of_var var) _ty' in
    OT.mk_abs_term var' _term'

let rec compile_hol_term (ty_ctx:ty_ctx) (te_ctx:term_ctx) term =
  match term with
  | ForallT(var,te) -> compile_hol_term (var::ty_ctx) te_ctx te
  | Term(te) -> compile_hol__term ty_ctx te_ctx te

let compile_ctx eq_proof (var,ctx) =
  let rec compile_ctx ctx =
    match ctx with
    | VarTerm(var', n, _ty) when var' = var -> eq_proof
    | _ -> failwith "todo compile_ctx"
  in
  compile_ctx ctx

let compile_hol_subst ty_ctx subst =
  let compile_binding (var,ty) = name_of_var var, compile_hol__type ty_ctx ty in
  List.map compile_binding subst


type ctx_proof =
  {
    prf:OT.thm OT.obj;
    left:OT.term OT.obj;
    right:OT.term OT.obj;
  }

let hol_const_of_name name _ty ty_subst =
  let cst = const_of_name name in
  let te = one_step cst in
  let te' = compile_term [] [] te in
  poly_subst_te ty_subst te'

let rec base_proof rw_proof =
  match rw_proof with
  | Unfold(Beta(left)) ->
    (* Format.eprintf "unfold beta@."; *)
    let left' = compile_hol__term [] [] left in
    let right' = compile_hol__term [] [] (beta_step left) in
    let p = OT.mk_betaConv left' in
    {prf=p; right=right';left=left'}
  | Fold(Beta(left)) ->
    (* Format.eprintf "fold beta: %a@."  print_hol__term left; *)
    let left' = compile_hol__term [] [] left in
    let right' = compile_hol__term [] [] (beta_step left) in
    {prf=OT.mk_sym (OT.mk_betaConv left'); right=left'; left=right'}
  | Unfold(Delta(name,_ty,ty_subst)) ->
    let left = compile_hol__term [] [] @@ hol_const_of_name name _ty ty_subst in
    let right = compile_hol__term [] [] @@ Const(name,_ty,ty_subst) in
    let subst = compile_hol_subst [] ty_subst in
    let pr = OT.mk_subst (OT.thm_of_const_name (compile_hol_name name)) subst [] in
    {prf=pr;left=right; right=left}
  | Fold(Delta(name,_ty,ty_subst)) ->
    (* Format.eprintf "fold delta@."; *)
    let left = compile_hol__term [] [] @@ hol_const_of_name name _ty ty_subst in
    let right = compile_hol__term [] [] @@ Const(name,_ty,ty_subst) in
    let subst = compile_hol_subst [] ty_subst in
    let pr = OT.mk_subst (OT.thm_of_const_name (compile_hol_name name)) subst [] in
    {prf=OT.mk_sym pr;left=left;right=right}
  | Unfold(Gamma(_proof,left,right)) ->
    (* Format.eprintf "unfold gamma@."; *)
    let pr = compile_hol__proof [] [] [] _proof in
    let left = compile_hol__term [] [] left in
    let right = compile_hol__term [] [] right in
    {prf=pr;left=left;right=right}
  | Fold(Gamma(_proof,left,right)) ->
    (* Format.eprintf "fold gamma@."; *)
    let pr = compile_hol__proof [] [] [] _proof in
    let left = compile_hol__term [] [] left in
    let right = compile_hol__term [] [] right in
    {prf=pr;left=left;right=right}

and compile_hol__proof (ty_ctx:ty_ctx) (te_ctx:term_ctx) (pf_ctx:proof_ctx) proof  =
  let open OT in
  match proof with
  | Lemma(name,term, subst) ->
    let proof =
      try
        thm_of_lemma (compile_hol_name name)
      with Failure _ ->
        mk_axiom (mk_hyp []) (compile_hol_term ty_ctx te_ctx term)
    in
    mk_subst proof (compile_hol_subst ty_ctx subst) []
  | Assume(_te, subst) ->
    mk_subst (OT.mk_assume (compile_hol__term ty_ctx te_ctx _te)) (compile_hol_subst ty_ctx subst) []
  | ForallI(id,_ty, _prooft) ->
    let name = name_of_var id in
    let _ty = compile_hol__type ty_ctx _ty in
    let _term = compile_hol__term ty_ctx te_ctx _prooft._term in
    let _proof = compile_hol__proof ty_ctx te_ctx pf_ctx _prooft._proof in
    mk_rule_intro_forall name _ty _term _proof
  | ImplI(_term, _prooft) ->
    let _proof = compile_hol__proof ty_ctx te_ctx pf_ctx _prooft._proof in
    let p = compile_hol__term ty_ctx te_ctx _term in
    let q = compile_hol__term ty_ctx te_ctx _prooft._term in
    mk_rule_intro_impl _proof p q
  | ForallE(_prooft,_term) ->
    let id,_ty,lam =
      match _prooft._term with
      | Forall(id,_ty,_term) -> id,_ty, Lam(id, _ty, _term)
      | _ -> assert false
    in
    let _ty' = compile_hol__type ty_ctx _ty in
    let lam' = compile_hol__term ty_ctx te_ctx lam in
    let _proof' = compile_hol__proof ty_ctx ((id, _ty)::te_ctx) pf_ctx _prooft._proof in
    let _term' = compile_hol__term ty_ctx te_ctx _term in
    mk_rule_elim_forall _proof' lam' _ty' _term'
  | ImplE(_prooftl,_prooftr) ->
    let p,q =
      match _prooftl._term with
      | Impl(p,q) -> p,q
      | _ -> assert false
    in
    let p' = compile_hol__term ty_ctx te_ctx p in
    let q' = compile_hol__term ty_ctx te_ctx q in
    let proofimpl = compile_hol__proof ty_ctx te_ctx pf_ctx _prooftl._proof in
    let proofp = compile_hol__proof ty_ctx te_ctx pf_ctx _prooftr._proof in
    mk_rule_elim_impl proofp proofimpl p' q'
  | RewriteU(ctx,rw,_pt) ->
    let eq_proof = (compile__ctx_proof (base_proof rw) ctx _pt._term).prf in
    let proof' = compile_hol__proof ty_ctx te_ctx pf_ctx _pt._proof in
    OT.mk_eqMp proof' eq_proof

and compile__ctx_proof base_proof ctx _te =
  (* Format.eprintf "debug ctx proof : %a@." print_hol__term _te; *)
  match _te, ctx with
  | _, [] -> base_proof
  | Forall(id,_ty,_te), 0::ctx' ->
    let pr = compile__ctx_proof base_proof ctx' _te in
    let ty' = compile_hol__type [] _ty in
    let prf = OT.mk_forall_equal pr.prf (name_of_var id) pr.left pr.right ty' in
    let lambda' t = OT.mk_abs_term (OT.mk_var (name_of_var id) ty') t in
    let left = OT.mk_forall_term (lambda' pr.left) ty' in
    let right = OT.mk_forall_term (lambda' pr.right) ty' in
    {prf;left;right}
  | Impl(tel,ter), i::ctx' ->
    let prl,prr =
      if i = 0 then
        let prl = compile__ctx_proof base_proof ctx' tel in
        let ter' = compile_hol__term [] [] ter in
        let prr = {prf=OT.mk_refl ter'; left=ter'; right=ter'} in
        prl,prr
      else if i = 1 then
        let prr = compile__ctx_proof base_proof ctx' ter in
        let tel' = compile_hol__term [] [] tel in
        let prl = {prf=OT.mk_refl tel'; left=tel'; right=tel'} in
        prl,prr
      else assert false
    in
    let prf = OT.mk_impl_equal prl.prf prr.prf prl.left prr.left prl.right prr.right in
    let left = OT.mk_impl_term prl.left prr.left in
    let right = OT.mk_impl_term prl.right prr.right in
    let pr = {prf;left;right} in
    pr
  | App(App(Const(name,ty, subst),l),r), i::ctx' when is_hol_equal name ->
    let prl,prr =
      if i = 0  then
        let ctx' =
        match ctx' with
          | [] -> assert false
          | _::ctx -> ctx
        in
        let prl = compile__ctx_proof base_proof ctx' l in
        let ter' = compile_hol__term [] [] r in
        let prr = {prf=OT.mk_refl ter'; left=ter'; right=ter'} in
        prl,prr
      else if i = 1 then
        let prr = compile__ctx_proof base_proof ctx' r in
        let tel' = compile_hol__term [] [] l in
        let prl = {prf=OT.mk_refl tel'; left=tel'; right=tel'} in
        prl,prr
      else assert false
    in
    let ty = match (poly_subst_ty subst ty) with Arrow(l,Arrow(_,_)) -> l | _ -> assert false in
    let ty' = compile_hol__type [] ty in
    let prf = OT.mk_equal_equal prl.left prr.left prl.right prr.right prl.prf prr.prf ty' in
    let left = OT.mk_equal_term prl.left prr.left ty' in
    let right = OT.mk_equal_term prl.right prr.right ty' in
    let pr = {prf;left;right} in
    pr
  | App(f,a), i::ctx'  ->
    if i = 0 then
      let pr = compile__ctx_proof base_proof ctx' f in
      compile_app pr (compile_hol__term [] [] a)
    else
    if i = 1 then
      let f' = compile_hol__term [] [] f in
      let prf = {prf = OT.mk_refl f'; left=f'; right=f'} in
      let pra = compile__ctx_proof base_proof ctx' a in
      { prf = OT.mk_appThm prf.prf pra.prf;
        left = OT.mk_app_term prf.left pra.left;
        right = OT.mk_app_term prf.right pra.right;
      }
    else assert false
  | Lam(id,_ty,_te), 0::ctx' ->
    let pr = compile__ctx_proof base_proof ctx' _te in
    let ty' = compile_hol__type [] _ty in
    let lambda' t = OT.mk_abs_term (OT.mk_var (name_of_var id) ty') t in
    let left = lambda' pr.left in
    let right = lambda' pr.right in
    let prf = OT.mk_absThm (OT.mk_var (name_of_var id) ty') pr.prf in
    {prf;left;right}
  | _ -> assert false

and compile_app pr arg =
  { prf = OT.mk_appThm pr.prf (OT.mk_refl arg);
    left = OT.mk_app_term pr.left arg;
    right = OT.mk_app_term pr.right arg
  }

let rec compile_ctx_proof base_proof ctx te =
  match te, ctx with
  | _, [] -> base_proof
  | ForallT(id,term), 0::ctx' -> compile_ctx_proof base_proof ctx' term
  | Term(_term), 0::ctx' -> compile__ctx_proof base_proof ctx' _term
  | _ -> assert false

let rec compile_hol_proof (ty_ctx:ty_ctx) (te_ctx:term_ctx) (pf_ctx:proof_ctx) proof =
  match proof.proof with
  | ForallP(var,pf) ->
    compile_hol_proof (var::ty_ctx) te_ctx pf_ctx pf
  | Proof(pf) ->
    compile_hol__proof ty_ctx te_ctx pf_ctx pf._proof
  | RewriteF(ctx,rw,pt) ->
    let eq_proof = (compile_ctx_proof (base_proof rw) ctx pt.term).prf in
    let proof' = compile_hol_proof ty_ctx te_ctx pf_ctx pt in
    OT.mk_eqMp proof' eq_proof


let compile_hol_const name ty term =
  match term with
  | None -> ()
  | Some term ->
    let term' = compile_hol_term [] [] term in
    OT.mk_const (compile_hol_name name) term'

let compile_hol_TyOp name tys = ()

let compile_hol_axiom name hyp term =
  let term' = compile_hol_term [] [] term in
  let hyp' = OT.mk_hyp hyp in
  let thm = OT.mk_axiom hyp' term' in
  OT.mk_thm (compile_hol_name name) term' hyp' thm


let rec alpha_rename_types left right =
  match left,right with
  | ForallT(name, te), ForallT(name',te') ->
    let subst = alpha_rename_types te te' in
    (name',name)::subst
  | Term(_), Term(_) -> []
  | _ -> assert false

let rename_types t pt =
  (* Format.eprintf "left: %a@.right: %a@." print_hol_term t print_hol_term pt.term; *)
  let subst = alpha_rename_types t pt.term in
  List.map (fun (id,id') -> name_of_var id, OT.mk_varType (name_of_var id')) subst

let compile_hol_thm name term proof_op =
  match proof_op with
  | None -> compile_hol_axiom name [] term
  | Some proof ->
    let name' = compile_hol_name name in
    let proof' = (compile_hol_proof [] [] [] proof) in
    let proof' = OT.mk_subst proof' (rename_types term proof) [] in
    OT.mk_thm name'
      (compile_hol_term [] [] term) (OT.mk_hyp []) proof'


let compile_hol_obj (obj:obj) =
  match obj with
  | Cst(name,ty,term) -> compile_hol_const name ty term
  | TyOp(name,tys) -> compile_hol_TyOp name tys
  | Thm(name,term, proof_op) -> compile_hol_thm name term proof_op

let init fmt =
  OT.set_fmt fmt;
  OT.version ()

let export_entry entry =
  match entry with
  | Utils.Declaration(name,te) ->
    begin
      match compile_declaration dloc name te with
      | OK(obj) -> compile_hol_obj obj
      | Err(err) -> fail_compile_declaration err
    end
  | Utils.Definition(name,ty,te) ->
    begin
      match compile_definition dloc name ty te with
      | OK(obj) -> compile_hol_obj obj
      | Err(err) -> fail_compile_definition err
    end
  | Utils.Opaque(name,ty,te) -> failwith "todo opaque"

let flush _ = ()
