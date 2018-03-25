Definition leibniz (A : Type) (x y : A) := forall P, P x -> P y.

Theorem from_leibniz : forall A x y, leibniz A x y -> x = y.
Proof.
  (intros **).
  (unfold leibniz in X).
  (pose proof (X (fun z => x = z))).
  (simpl in H).
  now (apply H).
Qed.

Theorem to_leibniz : forall A x y, x = y -> leibniz A x y.
Proof.
  (intros **).
  now subst.
Qed.

Theorem sym_leibniz :
  forall (A : Type) (x y : A), leibniz A x y -> leibniz A y x.
Proof.
  (unfold leibniz; intros **).
  (pose proof (X (fun z => P z -> P x))).
  (simpl in X1).
  now (apply X1).
Qed.

Definition True : Prop := forall z : Prop, z -> z.
Definition False : Prop := forall z : Prop, z.
Definition Imp : Prop -> Prop -> Prop := fun x y : Prop => x -> y.
Definition Not : Prop -> Prop := fun x : Prop => x -> False.
Definition And : Prop -> Prop -> Prop :=
  fun x y : Prop => forall z : Prop, (x -> y -> z) -> z.
Definition Or : Prop -> Prop -> Prop :=
  fun x y : Prop => forall z : Prop, (x -> z) -> (y -> z) -> z.
Definition Ex : forall A : Type, (A -> Prop) -> Prop :=
  fun (A : Type) (f : A -> Prop) =>
  forall z : Prop, (forall x : A, f x -> z) -> z.
Definition I : True := fun (z : Prop) (p : z) => p.
Definition eq : forall A : Type, A -> A -> Prop := fun _ x y => x = y.

Definition refl : forall (A : Type) (x : A), eq A x x :=
  fun _ x => eq_refl (x:=x).

Theorem eq_ind :
  forall (A : Type) (x : A) (P : A -> Prop),
  P x -> forall y : A, eq A x y -> P y.
Proof.
  (intros **).
  (apply eq_ind with (x := x); easy).
Qed.

Definition eq_rect_r :
  forall (A : Type) (a x : A), eq A x a -> forall P : A -> Prop, P a -> P x :=
  fun (A : Type) (a x : A) (p : eq A x a) =>
  eq_ind A x (fun __ : A => forall P : A -> Prop, P __ -> P x)
    (fun (P : A -> Prop) (auto : P x) => auto) a p.
Definition eq_ind_r :
  forall (A : Type) (a : A) (P : A -> Prop),
  P a -> forall x : A, eq A x a -> P x :=
  fun (A : Type) (a : A) (P : A -> Prop) (p : P a) (x0 : A) (p0 : eq A x0 a)
  => eq_rect_r A a x0 p0 (fun x01 : A => P x01) p.
Definition rewrite_l :
  forall (A : Type) (x : A) (P : A -> Prop),
  P x -> forall y : A, eq A x y -> P y :=
  fun (A : Type) (x : A) (P : A -> Prop) (Hx : P x) (y : A) (Heq : eq A x y)
  => eq_ind A x (fun __ : A => P __) Hx y Heq.
Definition sym_eq : forall (A : Type) (x y : A), eq A x y -> eq A y x :=
  fun (A : Type) (x y : A) (Heq : eq A x y) =>
  rewrite_l A x (fun __ : A => eq A __ x) (refl A x) y
    (rewrite_l A x (fun __ : A => eq A x __) (refl A x) y Heq).
Definition rewrite_r :
  forall (A : Type) (x : A) (P : A -> Prop),
  P x -> forall y : A, eq A y x -> P y :=
  fun (A : Type) (x : A) (P : A -> Prop) (Hx : P x) (y : A) (Heq : eq A y x)
  => eq_ind A x (fun __ : A => P __) Hx y (sym_eq A y x Heq).
Definition eq_coerc : forall A B : Prop, A -> eq Prop A B -> B :=
  fun (A B : Prop) (Ha : A) (Heq : eq Prop A B) =>
  eq_ind Prop A (fun x_19 : Prop => x_19) Ha B Heq.
Definition trans_eq :
  forall (A : Type) (x y z : A), eq A x y -> eq A y z -> eq A x z :=
  fun (A : Type) (x y z : A) (H1 : eq A x y) (H2 : eq A y z) =>
  eq_ind_r A y (fun x0 : A => eq A x0 z)
    (rewrite_l A x (fun __ : A => eq A __ z)
       (rewrite_l A x (fun __ : A => eq A x __) (refl A x) z
          (rewrite_r A y (fun __ : A => eq A __ z) H2 x H1)) y H1) x H1.
Definition eq_f :
  forall (A B : Type) (f : A -> B) (x y : A), eq A x y -> eq B (f x) (f y) :=
  fun (A B : Type) (f : A -> B) (x y : A) (H : eq A x y) =>
  eq_ind_r A y (fun x0 : A => eq B (f x0) (f y))
    (rewrite_l A x (fun __ : A => eq B (f __) (f y))
       (rewrite_l A x (fun __ : A => eq B (f x) (f __)) (refl B (f x)) y H) y
       H) x H.
Definition eq_f2 :
  forall (A B C : Type) (f : A -> B -> C) (x1 x2 : A) (y1 y2 : B),
  eq A x1 x2 -> eq B y1 y2 -> eq C (f x1 y1) (f x2 y2) :=
  fun (A B C : Type) (f : A -> B -> C) (x1 x2 : A) 
    (y1 y2 : B) (E1 : eq A x1 x2) (E2 : eq B y1 y2) =>
  eq_ind_r A x2 (fun x : A => eq C (f x y1) (f x2 y2))
    (eq_ind_r B y2 (fun x : B => eq C (f x2 x) (f x2 y2))
       (rewrite_l A x1 (fun __ : A => eq C (f __ y2) (f x2 y2))
          (rewrite_l B y1 (fun __ : B => eq C (f x1 __) (f x2 y2))
             (rewrite_l A x1 (fun __ : A => eq C (f x1 y1) (f __ y2))
                (rewrite_l B y1 (fun __ : B => eq C (f x1 y1) (f x1 __))
                   (refl C (f x1 y1)) y2 E2) x2 E1) y2 E2) x2 E1) y1 E2) x1
    E1.
Definition falsity : forall t : Prop, False -> t :=
  fun (t : Prop) (f : forall x : Prop, x) => f t.
Definition Not_ind : forall A Q : Prop, ((A -> False) -> Q) -> Not A -> Q :=
  fun (A Q : Prop) (F : (A -> False) -> Q) (N : Not A) => F N.
Definition absurd : forall A : Prop, A -> Not A -> False :=
  fun (A : Prop) (H : A) (Hn : Not A) =>
  Not_ind A False (fun _x_80 : A -> False => _x_80 H) Hn.
Definition not_to_not : forall A B : Prop, (A -> B) -> Not B -> Not A :=
  fun (A B : Prop) (auto : A -> B) (auto' : Not B) (auto'' : A) =>
  absurd B (auto auto'') auto'.
Definition sym_not_eq :
  forall (A : Type) (x y : A), Not (eq A x y) -> Not (eq A y x) :=
  fun (A : Type) (x y : A) (auto : Not (eq A x y)) (auto' : eq A y x) =>
  absurd (eq A x y)
    (rewrite_r A x (fun __ : A => eq A x __) (refl A x) y auto') auto.
Definition match_And_prop :
  forall A B return_ : Prop, (A -> B -> return_) -> And A B -> return_ :=
  fun (A B return_ : Prop) (case : A -> B -> return_) (and : And A B) =>
  and return_ case.
Definition proj1 : forall A B : Prop, And A B -> A :=
  fun (A B : Prop) (AB : And A B) =>
  match_And_prop A B A (fun (_x_120 : A) (_x_119 : B) => _x_120) AB.
Definition proj2 : forall A B : Prop, And A B -> B :=
  fun (A B : Prop) (AB : And A B) =>
  match_And_prop A B B (fun (_x_120 : A) (_x_119 : B) => _x_119) AB.
Definition match_Or_prop :
  forall A B return_ : Prop,
  (A -> return_) -> (B -> return_) -> Or A B -> return_ :=
  fun (A B return_ : Prop) (case_A : A -> return_) 
    (case_B : B -> return_) (or : Or A B) => or return_ case_A case_B.
Definition decidable : Prop -> Prop := fun A : Prop => Or A (Not A).
Definition match_ex_prop :
  forall (A : Type) (P : A -> Prop) (return_ : Prop),
  (forall x : A, P x -> return_) -> Ex A P -> return_ :=
  fun (A : Type) (P : A -> Prop) (return_ : Prop)
    (case : forall x : A, P x -> return_) (Ex : Ex A P) => 
  Ex return_ case.
Definition reflexive : forall A : Type, (A -> A -> Prop) -> Prop :=
  fun (A : Type) (R : A -> A -> Prop) => forall x : A, R x x.
Definition transitive : forall A : Type, (A -> A -> Prop) -> Prop :=
  fun (A : Type) (R : A -> A -> Prop) =>
  forall x y z : A, R x y -> R y z -> R x z.
Definition RC : forall A : Type, (A -> A -> Prop) -> A -> A -> Prop :=
  fun (A : Type) (R : A -> A -> Prop) (x y : A) => Or (R x y) (eq A x y).
Definition RC_reflexive :
  forall (A : Type) (R : A -> A -> Prop), reflexive A (RC A R) :=
  fun (A : Type) (R : A -> A -> Prop) (x : A) (z : Prop) 
    (l : R x x -> z) (r : eq A x x -> z) => r (refl A x).
Definition injective : forall A B : Type, (A -> B) -> Prop :=
  fun (A B : Type) (f : A -> B) =>
  forall x y : A, eq B (f x) (f y) -> eq A x y.
Definition commutative : forall A : Type, (A -> A -> A) -> Prop :=
  fun (A : Type) (f : A -> A -> A) => forall x y : A, eq A (f x y) (f y x).
Definition associative : forall A : Type, (A -> A -> A) -> Prop :=
  fun (A : Type) (f : A -> A -> A) =>
  forall x y z : A, eq A (f (f x y) z) (f x (f y z)).
Definition monotonic :
  forall A : Type, (A -> A -> Prop) -> (A -> A) -> Prop :=
  fun (A : Type) (R : A -> A -> Prop) (f : A -> A) =>
  forall x y : A, R x y -> R (f x) (f y).
Definition distributive :
  forall A : Type, (A -> A -> A) -> (A -> A -> A) -> Prop :=
  fun (A : Type) (f g : A -> A -> A) =>
  forall x y z : A, eq A (f x (g y z)) (g (f x y) (f x z)).
Definition bool : Type := bool.
Definition true : bool := true.
Definition false : bool := false.
Theorem match_bool_prop :
  forall return_ : bool -> Prop,
  return_ true -> return_ false -> forall z : bool, return_ z.
Proof.
  (intros **).
  (apply bool_ind; easy).
Qed.


Definition match_bool_type :
  forall return_ : Type, return_ -> return_ -> bool -> return_.
Proof.
  (intros **).
  (apply bool_rect).
  exact X.
  exact X0.
  exact X1.
Defined.

Theorem eq_match_bool_type_true :
  forall (return_ : Type) (case_true case_false : return_),
  leibniz return_ (match_bool_type return_ case_true case_false true)
    case_true.
Proof.
  (intros **).
  (apply to_leibniz).
  reflexivity.
Qed.

Theorem eq_match_bool_type_false :
  forall (return_ : Type) (case_true case_false : return_),
  leibniz return_ (match_bool_type return_ case_true case_false false)
    case_false.
Proof.
  (intros **).
  (apply to_leibniz).
  reflexivity.
Qed.

Definition sym_eq_match_bool_type_true :
  forall (return_ : Type) (case_true case_false : return_),
  leibniz return_ case_true
    (match_bool_type return_ case_true case_false true) :=
  fun (return_type : Type) (case_true case_false : return_type) =>
  sym_leibniz return_type
    (match_bool_type return_type case_true case_false true) case_true
    (eq_match_bool_type_true return_type case_true case_false).
Definition sym_eq_match_bool_type_false :
  forall (return_ : Type) (case_true case_false : return_),
  leibniz return_ case_false
    (match_bool_type return_ case_true case_false false) :=
  fun (return_type : Type) (case_true case_false : return_type) =>
  sym_leibniz return_type
    (match_bool_type return_type case_true case_false false) case_false
    (eq_match_bool_type_false return_type case_true case_false).
Definition bool_discr :
  forall x y : bool,
  eq bool x y ->
  match_bool_type Prop
    (match_bool_type Prop (forall P : Prop, P -> P) (forall P : Prop, P) y)
    (match_bool_type Prop (forall P : Prop, P) (forall P : Prop, P -> P) y) x :=
  fun (x y : bool) (Deq : eq bool x y) =>
  eq_ind bool x
    (fun x_13 : bool =>
     match_bool_type Prop
       (match_bool_type Prop (forall P : Prop, P -> P) 
          (forall P : Prop, P) x_13)
       (match_bool_type Prop (forall P : Prop, P) 
          (forall P : Prop, P -> P) x_13) x)
    (match_bool_prop
       (fun __ : bool =>
        match_bool_type Prop
          (match_bool_type Prop (forall P : Prop, P -> P)
             (forall P : Prop, P) __)
          (match_bool_type Prop (forall P : Prop, P)
             (forall P : Prop, P -> P) __) __)
       (sym_eq_match_bool_type_true Prop
          (match_bool_type Prop (forall P : Prop, P -> P)
             (forall P : Prop, P) true)
          (match_bool_type Prop (forall P : Prop, P)
             (forall P : Prop, P -> P) true) (fun x0 : Prop => x0)
          (sym_eq_match_bool_type_true Prop (forall P : Prop, P -> P)
             (forall P : Prop, P) (fun x0 : Prop => x0)
             (fun (P : Prop) (DH : P) => DH)))
       (sym_eq_match_bool_type_false Prop
          (match_bool_type Prop (forall P : Prop, P -> P)
             (forall P : Prop, P) false)
          (match_bool_type Prop (forall P : Prop, P)
             (forall P : Prop, P -> P) false) (fun x0 : Prop => x0)
          (sym_eq_match_bool_type_false Prop (forall P : Prop, P)
             (forall P : Prop, P -> P) (fun x0 : Prop => x0)
             (fun (P : Prop) (DH : P) => DH))) x) y Deq.
Definition not_eq_true_false : Not (eq bool true false) :=
  fun Heq : eq bool true false =>
  eq_match_bool_type_false Prop (forall P : Prop, P -> P)
    (forall P : Prop, P) (fun x : Prop => x)
    (eq_match_bool_type_true Prop
       (match_bool_type Prop (forall P : Prop, P -> P) 
          (forall P : Prop, P) false)
       (match_bool_type Prop (forall P : Prop, P) 
          (forall P : Prop, P -> P) false) (fun x : Prop => x)
       (bool_discr true false Heq)) False.
Definition notb : bool -> bool :=
  fun b : bool => match_bool_type bool false true b.
Definition andb : bool -> bool -> bool :=
  fun b1 b2 : bool => match_bool_type bool b2 false b1.
Definition andb_true_l :
  forall b1 b2 : bool, eq bool (andb b1 b2) true -> eq bool b1 true :=
  fun b1 : bool =>
  match_bool_prop
    (fun __ : bool =>
     forall b2 : bool, eq bool (andb __ b2) true -> eq bool __ true)
    (fun b2 : bool =>
     sym_eq_match_bool_type_true bool b2 false
       (fun x : bool => eq bool x true -> eq bool true true)
       (fun auto : eq bool b2 true =>
        rewrite_l bool b2 (fun __ : bool => eq bool __ true)
          (rewrite_l bool b2 (fun __ : bool => eq bool b2 __) 
             (refl bool b2) true auto) true auto))
    (fun _b2 : bool =>
     sym_eq_match_bool_type_false bool _b2 false
       (fun x : bool => eq bool x true -> eq bool false true)
       (fun auto : eq bool false true =>
        rewrite_r bool true (fun __ : bool => eq bool __ true)
          (refl bool true) false auto)) b1.
Definition andb_true_r :
  forall b1 b2 : bool, eq bool (andb b1 b2) true -> eq bool b2 true :=
  fun b1 b2 : bool =>
  match_bool_prop
    (fun __ : bool => eq bool (andb __ b2) true -> eq bool b2 true)
    (sym_eq_match_bool_type_true bool b2 false
       (fun x : bool => eq bool x true -> eq bool b2 true)
       (fun auto : eq bool b2 true =>
        rewrite_l bool b2 (fun __ : bool => eq bool b2 __) 
          (refl bool b2) true auto))
    (sym_eq_match_bool_type_false bool b2 false
       (fun x : bool => eq bool x true -> eq bool b2 true)
       (match_bool_prop
          (fun __ : bool => eq bool false true -> eq bool __ true)
          (fun auto : eq bool false true => refl bool true)
          (fun auto : eq bool false true =>
           rewrite_r bool true (fun __ : bool => eq bool __ true)
             (refl bool true) false auto) b2)) b1.
Definition true_or_false :
  forall b : bool, Or (eq bool b true) (eq bool b false) :=
  fun b : bool =>
  match_bool_prop (fun __ : bool => Or (eq bool __ true) (eq bool __ false))
    (fun (z : Prop) (l : eq bool true true -> z)
       (r : eq bool true false -> z) => l (refl bool true))
    (RC_reflexive bool (fun __ _0 : bool => eq bool false true) false) b.
Definition nat : Type := nat.
Definition O : nat := 0.
Definition S : nat -> nat := S.

Theorem match_nat_prop :
  forall return_ : nat -> Prop,
  return_ O -> (forall n : nat, return_ (S n)) -> forall z : nat, return_ z.
Proof.
  (intros **).
  (apply nat_ind; easy).
Qed.


Definition match_nat_type :
  forall return_ : Type, return_ -> (nat -> return_) -> nat -> return_.
Proof.
  (intros **).
  (pose proof nat_rect).
  (apply nat_rect).
  exact X.
  (intros **).
  (apply X0).
  exact n.
  exact X1.
Defined.

Theorem eq_match_nat_type_O :
  forall (return_type : Type) (case_O : return_type)
    (case_S : nat -> return_type),
  leibniz return_type (match_nat_type return_type case_O case_S O) case_O.
Proof.
  (intros **).
  (apply to_leibniz).
  reflexivity.
Qed.

Definition sym_eq_match_nat_type_O :
  forall (return_type : Type) (case_O : return_type)
    (case_S : nat -> return_type),
  leibniz return_type case_O (match_nat_type return_type case_O case_S O) :=
  fun (return_type : Type) (case_O : return_type)
    (case_S : nat -> return_type) =>
  sym_leibniz return_type (match_nat_type return_type case_O case_S O) case_O
    (eq_match_nat_type_O return_type case_O case_S).

Theorem eq_match_nat_type_S :
  forall (return_type : Type) (case_O : return_type)
    (case_S : nat -> return_type) (n : nat),
  leibniz return_type (match_nat_type return_type case_O case_S (S n))
    (case_S n).
Proof.
  (intros **).
  (apply to_leibniz).
  reflexivity.
Qed.

Definition sym_eq_match_nat_type_S :
  forall (return_type : Type) (case_O : return_type)
    (case_S : nat -> return_type) (n : nat),
  leibniz return_type (case_S n)
    (match_nat_type return_type case_O case_S (S n)) :=
  fun (return_type : Type) (case_O : return_type)
    (case_S : nat -> return_type) (n : nat) =>
  sym_leibniz return_type (match_nat_type return_type case_O case_S (S n))
    (case_S n) (eq_match_nat_type_S return_type case_O case_S n).
Definition filter_nat_type :
  forall return_ : Type, (nat -> return_) -> nat -> return_ := 
  fun _ x => x.

Theorem eq_filter_nat_type_O :
  forall (return_type : Type) (return_ : nat -> return_type),
  leibniz return_type (filter_nat_type return_type return_ O) (return_ O).
Proof.
  (intros **).
  (apply to_leibniz).
  reflexivity.
Qed.

Definition sym_eq_filter_nat_type_O :
  forall (return_type : Type) (return_ : nat -> return_type),
  leibniz return_type (return_ O) (filter_nat_type return_type return_ O) :=
  fun (return_type : Type) (return_ : nat -> return_type) =>
  sym_leibniz return_type (filter_nat_type return_type return_ O) 
    (return_ O) (eq_filter_nat_type_O return_type return_).
Theorem eq_filter_nat_type_S :
  forall (return_type : Type) (return_ : nat -> return_type) (n : nat),
  leibniz return_type (filter_nat_type return_type return_ (S n))
    (return_ (S n)).
Proof.
  (intros **).
  (apply to_leibniz).
  reflexivity.
Qed.

Definition sym_eq_filter_nat_type_S :
  forall (return_type : Type) (return_ : nat -> return_type) (n : nat),
  leibniz return_type (return_ (S n))
    (filter_nat_type return_type return_ (S n)) :=
  fun (return_type : Type) (return_ : nat -> return_type) (n : nat) =>
  sym_leibniz return_type (filter_nat_type return_type return_ (S n))
    (return_ (S n)) (eq_filter_nat_type_S return_type return_ n).

Theorem nat_ind :
  forall Q : nat -> Prop,
  Q O -> (forall x : nat, Q x -> Q (S x)) -> forall x : nat, Q x.
Proof.
  (intros **).
  now (apply nat_ind).
Qed.

Definition pred : nat -> nat :=
  fun n : nat => match_nat_type nat O (fun p : nat => p) n.
Definition not_zero : nat -> Prop :=
  fun n : nat => match_nat_type Prop False (fun p : nat => True) n.

Definition le : nat -> nat -> Prop := le.

Theorem le_n : forall n : nat, le n n.
Proof.
  now (apply le_n).
Qed.

Theorem le_S : forall n m : nat, le n m -> le n (S m).
Proof.
  now (apply le_S).
Qed.

Theorem match_le_prop :
  forall (n : nat) (return_ : nat -> Prop),
  return_ n ->
  (forall m : nat, return_ (S m)) -> forall m : nat, le n m -> return_ m.
Proof.
  (intros **).
  (destruct m).
  (inversion H1; now subst).
  (apply H0).
Qed.

Theorem le_ind :
  forall (n : nat) (Q : nat -> Prop),
  Q n ->
  (forall m : nat, le n m -> Q m -> Q (S m)) -> forall m : nat, le n m -> Q m.
Proof.
  (intros **).
  (eapply le_ind).
  (apply H).
  (apply H0).
  (apply H1).
Qed.

Definition lt : nat -> nat -> Prop := fun n m : nat => le (S n) m.
Definition plus : nat -> nat -> nat := Nat.add.
Definition plus_body : nat -> nat -> nat := plus.

Theorem eq_plus :
  forall n : nat,
  leibniz (nat -> nat) (plus n) (filter_nat_type (nat -> nat) plus_body n).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.

Definition sym_eq_plus :
  forall n : nat,
  leibniz (nat -> nat) (filter_nat_type (nat -> nat) plus_body n) (plus n) :=
  fun n : nat =>
  sym_leibniz (nat -> nat) (plus n)
    (filter_nat_type (nat -> nat) plus_body n) (eq_plus n).

Theorem eq_plus_body_O :
  leibniz (nat -> nat) (plus_body O) (fun m : nat => m).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.

Definition sym_eq_plus_body_O :
  leibniz (nat -> nat) (fun m : nat => m) (plus_body O) :=
  sym_leibniz (nat -> nat) (plus_body O) (fun m : nat => m) eq_plus_body_O.

Theorem eq_plus_body_S :
  forall n : nat,
  leibniz (nat -> nat) (plus_body (S n)) (fun m : nat => S (plus n m)).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.

Definition sym_eq_plus_body_S :
  forall n : nat,
  leibniz (nat -> nat) (fun m : nat => S (plus n m)) (plus_body (S n)) :=
  fun n : nat =>
  sym_leibniz (nat -> nat) (plus_body (S n)) (fun m : nat => S (plus n m))
    (eq_plus_body_S n).

Definition times : nat -> nat -> nat := Nat.mul.

Definition times_body : nat -> nat -> nat := Nat.mul.

Theorem eq_times :
  forall n : nat,
  leibniz (nat -> nat) (times n) (filter_nat_type (nat -> nat) times_body n).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.

Definition sym_eq_times :
  forall n : nat,
  leibniz (nat -> nat) (filter_nat_type (nat -> nat) times_body n) (times n) :=
  fun n : nat =>
  sym_leibniz (nat -> nat) (times n)
    (filter_nat_type (nat -> nat) times_body n) (eq_times n).
Theorem eq_times_body_O :
  leibniz (nat -> nat) (times_body O) (fun m : nat => O).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.

Definition sym_eq_times_body_O :
  leibniz (nat -> nat) (fun m : nat => O) (times_body O) :=
  sym_leibniz (nat -> nat) (times_body O) (fun m : nat => O) eq_times_body_O.

Theorem eq_times_body_S :
  forall n : nat,
  leibniz (nat -> nat) (times_body (S n)) (fun m : nat => plus m (times n m)).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.

Definition sym_eq_times_body_S :
  forall n : nat,
  leibniz (nat -> nat) (fun m : nat => plus m (times n m)) (times_body (S n)) :=
  fun n : nat =>
  sym_leibniz (nat -> nat) (times_body (S n))
    (fun m : nat => plus m (times n m)) (eq_times_body_S n).
Definition minus : nat -> nat -> nat := Nat.sub.
Definition minus_body : nat -> nat -> nat := minus.

Theorem eq_minus :
  forall n : nat,
  leibniz (nat -> nat) (minus n) (filter_nat_type (nat -> nat) minus_body n).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.

Definition sym_eq_minus :
  forall n : nat,
  leibniz (nat -> nat) (filter_nat_type (nat -> nat) minus_body n) (minus n) :=
  fun n : nat =>
  sym_leibniz (nat -> nat) (minus n)
    (filter_nat_type (nat -> nat) minus_body n) (eq_minus n).
Theorem eq_minus_body_O :
  leibniz (nat -> nat) (minus_body O) (fun m : nat => O).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.

Require Import Logic.FunctionalExtensionality.

Definition sym_eq_minus_body_O :
  leibniz (nat -> nat) (fun m : nat => O) (minus_body O) :=
  sym_leibniz (nat -> nat) (minus_body O) (fun m : nat => O) eq_minus_body_O.
Theorem eq_minus_body_S :
  forall n : nat,
  leibniz (nat -> nat) (minus_body (S n))
    (fun m : nat => match_nat_type nat (S n) (fun q : nat => minus n q) m).
Proof.
  (intros **; apply to_leibniz).
  (apply functional_extensionality).
  (intro x; destruct x).
  reflexivity.
  reflexivity.
Qed.

Definition sym_eq_minus_body_S :
  forall n : nat,
  leibniz (nat -> nat)
    (fun m : nat => match_nat_type nat (S n) (fun q : nat => minus n q) m)
    (minus_body (S n)) :=
  fun n : nat =>
  sym_leibniz (nat -> nat) (minus_body (S n))
    (fun m : nat => match_nat_type nat (S n) (fun q : nat => minus n q) m)
    (eq_minus_body_S n).
Definition nat_case :
  forall (n : nat) (P : nat -> Prop),
  (eq nat n O -> P O) -> (forall m : nat, eq nat n (S m) -> P (S m)) -> P n :=
  fun (n : nat) (P : nat -> Prop) =>
  nat_ind
    (fun _x_365 : nat =>
     (eq nat _x_365 O -> P O) ->
     (forall m : nat, eq nat _x_365 (S m) -> P (S m)) -> P _x_365)
    (fun (auto : eq nat O O -> P O)
       (auto' : forall m : nat, eq nat O (S m) -> P (S m)) =>
     auto (refl nat O))
    (fun (x_366 : nat)
       (_x_368 : (eq nat x_366 O -> P O) ->
                 (forall m : nat, eq nat x_366 (S m) -> P (S m)) -> P x_366)
       (auto : eq nat (S x_366) O -> P O)
       (auto' : forall m : nat, eq nat (S x_366) (S m) -> P (S m)) =>
     auto' x_366 (refl nat (S x_366))) n.
Definition nat_elim2 :
  forall R : nat -> nat -> Prop,
  (forall n : nat, R O n) ->
  (forall n : nat, R (S n) O) ->
  (forall n m : nat, R n m -> R (S n) (S m)) -> forall n m : nat, R n m :=
  fun (R : nat -> nat -> Prop) (ROn : forall n : nat, R O n)
    (RSO : forall n : nat, R (S n) O)
    (RSS : forall n m : nat, R n m -> R (S n) (S m)) 
    (n : nat) =>
  nat_ind (fun _x_365 : nat => forall m : nat, R _x_365 m)
    (fun m : nat => ROn m)
    (fun (n0 : nat) (Rn0m : forall m : nat, R n0 m) (m : nat) =>
     match_nat_prop (fun __ : nat => R (S n0) __) 
       (RSO n0) (fun auto : nat => RSS n0 auto (Rn0m auto)) m) n.
Definition le_gen :
  forall (P : nat -> Prop) (n : nat), (forall i : nat, le i n -> P i) -> P n :=
  fun (P : nat -> Prop) (n : nat) (auto : forall i : nat, le i n -> P i) =>
  auto n (le_n n).
Definition pred_Sn : forall n : nat, eq nat n (pred (S n)) :=
  fun n : nat =>
  sym_eq_match_nat_type_S nat O (fun p : nat => p) n
    (fun y : nat => eq nat n y) (refl nat n).
Definition injective_S : injective nat nat S :=
  fun (x y : nat) (auto : eq nat (S x) (S y)) =>
  rewrite_l nat y (fun __ : nat => eq nat __ y) (refl nat y) x
    (rewrite_r nat (pred (S x)) (fun __ : nat => eq nat y __)
       (rewrite_r nat (S y) (fun __ : nat => eq nat y (pred __)) 
          (pred_Sn y) (S x) auto) x (pred_Sn x)).
Definition S_pred : forall n : nat, lt O n -> eq nat (S (pred n)) n :=
  fun (n : nat) (posn : lt O n) =>
  match_le_prop (S O) (fun __ : nat => eq nat (S (pred __)) __)
    (rewrite_l nat O (fun __ : nat => eq nat (S __) (S O)) 
       (refl nat (S O)) (pred (S O)) (pred_Sn O))
    (fun m : nat =>
     rewrite_l nat m (fun __ : nat => eq nat (S __) (S m)) 
       (refl nat (S m)) (pred (S m)) (pred_Sn m)) n posn.
Definition plus_O_n : forall n : nat, eq nat n (plus O n) :=
  fun n : nat =>
  sym_eq_plus O (fun y : nat -> nat => eq nat n (y n))
    (sym_eq_filter_nat_type_O (nat -> nat) plus_body
       (fun y : nat -> nat => eq nat n (y n))
       (sym_eq_plus_body_O (fun y : nat -> nat => eq nat n (y n))
          (refl nat n))).
Definition plus_n_O : forall n : nat, eq nat n (plus n O) :=
  fun n : nat =>
  nat_ind (fun _x_365 : nat => eq nat _x_365 (plus _x_365 O))
    (sym_eq_plus O (fun y : nat -> nat => eq nat O (y O))
       (sym_eq_filter_nat_type_O (nat -> nat) plus_body
          (fun y : nat -> nat => eq nat O (y O))
          (sym_eq_plus_body_O (fun y : nat -> nat => eq nat O (y O))
             (refl nat O))))
    (fun (x_366 : nat) (_x_368 : eq nat x_366 (plus x_366 O)) =>
     sym_eq_plus (S x_366) (fun y : nat -> nat => eq nat (S x_366) (y O))
       (sym_eq_filter_nat_type_S (nat -> nat) plus_body x_366
          (fun y : nat -> nat => eq nat (S x_366) (y O))
          (sym_eq_plus_body_S x_366
             (fun y : nat -> nat => eq nat (S x_366) (y O))
             (rewrite_l nat x_366 (fun __ : nat => eq nat (S x_366) (S __))
                (refl nat (S x_366)) (plus x_366 O) _x_368)))) n.
Definition plus_n_Sm :
  forall n m : nat, eq nat (S (plus n m)) (plus n (S m)) :=
  fun n : nat =>
  nat_ind
    (fun _x_365 : nat =>
     forall m : nat, eq nat (S (plus _x_365 m)) (plus _x_365 (S m)))
    (fun m : nat =>
     sym_eq_plus O (fun y : nat -> nat => eq nat (S (y m)) (plus O (S m)))
       (sym_eq_plus O
          (fun y : nat -> nat =>
           eq nat (S (filter_nat_type (nat -> nat) plus_body O m)) (y (S m)))
          (sym_eq_filter_nat_type_O (nat -> nat) plus_body
             (fun y : nat -> nat =>
              eq nat (S (filter_nat_type (nat -> nat) plus_body O m))
                (y (S m)))
             (sym_eq_filter_nat_type_O (nat -> nat) plus_body
                (fun y : nat -> nat => eq nat (S (y m)) (plus_body O (S m)))
                (sym_eq_plus_body_O
                   (fun y : nat -> nat =>
                    eq nat (S (y m)) (plus_body O (S m)))
                   (sym_eq_plus_body_O
                      (fun y : nat -> nat => eq nat (S m) (y (S m)))
                      (refl nat (S m))))))))
    (fun (x_366 : nat)
       (_x_368 : forall m : nat, eq nat (S (plus x_366 m)) (plus x_366 (S m)))
       (m : nat) =>
     sym_eq_plus (S x_366)
       (fun y : nat -> nat => eq nat (S (y m)) (plus (S x_366) (S m)))
       (sym_eq_plus (S x_366)
          (fun y : nat -> nat =>
           eq nat (S (filter_nat_type (nat -> nat) plus_body (S x_366) m))
             (y (S m)))
          (sym_eq_filter_nat_type_S (nat -> nat) plus_body x_366
             (fun y : nat -> nat =>
              eq nat (S (filter_nat_type (nat -> nat) plus_body (S x_366) m))
                (y (S m)))
             (sym_eq_filter_nat_type_S (nat -> nat) plus_body x_366
                (fun y : nat -> nat =>
                 eq nat (S (y m)) (plus_body (S x_366) (S m)))
                (sym_eq_plus_body_S x_366
                   (fun y : nat -> nat =>
                    eq nat (S (y m)) (plus_body (S x_366) (S m)))
                   (sym_eq_plus_body_S x_366
                      (fun y : nat -> nat =>
                       eq nat (S (S (plus x_366 m))) (y (S m)))
                      (rewrite_r nat (plus x_366 (S m))
                         (fun __ : nat =>
                          eq nat (S __) (S (plus x_366 (S m))))
                         (rewrite_r nat (plus x_366 (S (S m)))
                            (fun __ : nat => eq nat __ (S (plus x_366 (S m))))
                            (rewrite_r nat (plus x_366 (S (S m)))
                               (fun __ : nat =>
                                eq nat (plus x_366 (S (S m))) __)
                               (refl nat (plus x_366 (S (S m))))
                               (S (plus x_366 (S m))) 
                               (_x_368 (S m))) (S (plus x_366 (S m)))
                            (_x_368 (S m))) (S (plus x_366 m)) 
                         (_x_368 m)))))))) n.
Definition commutative_plus : commutative nat plus :=
  fun n : nat =>
  nat_ind
    (fun _x_365 : nat =>
     forall y : nat, eq nat (plus _x_365 y) (plus y _x_365))
    (fun y : nat =>
     sym_eq_plus O (fun z : nat -> nat => eq nat (z y) (plus y O))
       (sym_eq_filter_nat_type_O (nat -> nat) plus_body
          (fun z : nat -> nat => eq nat (z y) (plus y O))
          (sym_eq_plus_body_O (fun z : nat -> nat => eq nat (z y) (plus y O))
             (rewrite_l nat y (fun __ : nat => eq nat y __) 
                (refl nat y) (plus y O) (plus_n_O y)))))
    (fun (x_366 : nat)
       (_x_368 : forall y : nat, eq nat (plus x_366 y) (plus y x_366))
       (y : nat) =>
     sym_eq_plus (S x_366)
       (fun z : nat -> nat => eq nat (z y) (plus y (S x_366)))
       (sym_eq_filter_nat_type_S (nat -> nat) plus_body x_366
          (fun z : nat -> nat => eq nat (z y) (plus y (S x_366)))
          (sym_eq_plus_body_S x_366
             (fun z : nat -> nat => eq nat (z y) (plus y (S x_366)))
             (rewrite_r nat (plus x_366 (S y))
                (fun __ : nat => eq nat __ (plus y (S x_366)))
                (rewrite_r nat (plus y (S x_366))
                   (fun __ : nat => eq nat __ (plus y (S x_366)))
                   (refl nat (plus y (S x_366))) (plus x_366 (S y))
                   (rewrite_l nat (S (plus x_366 y))
                      (fun __ : nat => eq nat __ (plus y (S x_366)))
                      (rewrite_r nat (plus y x_366)
                         (fun __ : nat => eq nat (S __) (plus y (S x_366)))
                         (plus_n_Sm y x_366) (plus x_366 y) 
                         (_x_368 y)) (plus x_366 (S y)) 
                      (plus_n_Sm x_366 y))) (S (plus x_366 y))
                (plus_n_Sm x_366 y))))) n.
Definition associative_plus : associative nat plus :=
  fun n : nat =>
  nat_ind
    (fun _x_365 : nat =>
     forall y z : nat,
     eq nat (plus (plus _x_365 y) z) (plus _x_365 (plus y z)))
    (fun y z : nat =>
     sym_eq_plus O
       (fun x : nat -> nat => eq nat (plus (plus O y) z) (x (plus y z)))
       (sym_eq_plus O
          (fun x : nat -> nat =>
           eq nat (plus (x y) z)
             (filter_nat_type (nat -> nat) plus_body O (plus y z)))
          (sym_eq_filter_nat_type_O (nat -> nat) plus_body
             (fun x : nat -> nat =>
              eq nat (plus (x y) z)
                (filter_nat_type (nat -> nat) plus_body O (plus y z)))
             (sym_eq_filter_nat_type_O (nat -> nat) plus_body
                (fun x : nat -> nat =>
                 eq nat (plus (plus_body O y) z) (x (plus y z)))
                (sym_eq_plus_body_O
                   (fun x : nat -> nat =>
                    eq nat (plus (plus_body O y) z) (x (plus y z)))
                   (sym_eq_plus_body_O
                      (fun x : nat -> nat => eq nat (plus (x y) z) (plus y z))
                      (refl nat (plus y z))))))))
    (fun (x_366 : nat)
       (_x_368 : forall y z : nat,
                 eq nat (plus (plus x_366 y) z) (plus x_366 (plus y z)))
       (y z : nat) =>
     sym_eq_plus (S x_366)
       (fun x : nat -> nat =>
        eq nat (plus (plus (S x_366) y) z) (x (plus y z)))
       (sym_eq_plus (S x_366)
          (fun x : nat -> nat =>
           eq nat (plus (x y) z)
             (filter_nat_type (nat -> nat) plus_body (S x_366) (plus y z)))
          (sym_eq_filter_nat_type_S (nat -> nat) plus_body x_366
             (fun x : nat -> nat =>
              eq nat (plus (x y) z)
                (filter_nat_type (nat -> nat) plus_body (S x_366) (plus y z)))
             (sym_eq_filter_nat_type_S (nat -> nat) plus_body x_366
                (fun x : nat -> nat =>
                 eq nat (plus (plus_body (S x_366) y) z) (x (plus y z)))
                (sym_eq_plus_body_S x_366
                   (fun x : nat -> nat =>
                    eq nat (plus (plus_body (S x_366) y) z) (x (plus y z)))
                   (sym_eq_plus_body_S x_366
                      (fun x : nat -> nat =>
                       eq nat (plus (x y) z) (S (plus x_366 (plus y z))))
                      (sym_eq_plus (S (plus x_366 y))
                         (fun x : nat -> nat =>
                          eq nat (x z) (S (plus x_366 (plus y z))))
                         (sym_eq_filter_nat_type_S 
                            (nat -> nat) plus_body 
                            (plus x_366 y)
                            (fun x : nat -> nat =>
                             eq nat (x z) (S (plus x_366 (plus y z))))
                            (sym_eq_plus_body_S (plus x_366 y)
                               (fun x : nat -> nat =>
                                eq nat (x z) (S (plus x_366 (plus y z))))
                               (rewrite_r nat (plus x_366 (plus y z))
                                  (fun __ : nat =>
                                   eq nat (S __) (S (plus x_366 (plus y z))))
                                  (refl nat (S (plus x_366 (plus y z))))
                                  (plus (plus x_366 y) z) 
                                  (_x_368 y z))))))))))) n.
Definition assoc_plus1 :
  forall a b c : nat, eq nat (plus c (plus b a)) (plus (plus b c) a) :=
  fun a b c : nat =>
  rewrite_r nat (plus a b)
    (fun __ : nat => eq nat (plus c __) (plus (plus b c) a))
    (rewrite_r nat (plus a (plus b c))
       (fun __ : nat => eq nat (plus c (plus a b)) __)
       (rewrite_r nat (plus a (plus b c))
          (fun __ : nat => eq nat __ (plus a (plus b c)))
          (refl nat (plus a (plus b c))) (plus c (plus a b))
          (rewrite_l nat (plus (plus a b) c)
             (fun __ : nat => eq nat (plus c (plus a b)) __)
             (commutative_plus c (plus a b)) (plus a (plus b c))
             (associative_plus a b c))) (plus (plus b c) a)
       (commutative_plus (plus b c) a)) (plus b a) 
    (commutative_plus b a).
Definition injective_plus_r :
  forall n : nat, injective nat nat (fun m : nat => plus n m) :=
  fun n : nat =>
  nat_ind
    (fun _x_365 : nat => injective nat nat (fun m : nat => plus _x_365 m))
    (sym_eq_plus O
       (fun y : nat -> nat => injective nat nat (fun m : nat => y m))
       (sym_eq_filter_nat_type_O (nat -> nat) plus_body
          (fun y : nat -> nat => injective nat nat (fun m : nat => y m))
          (sym_eq_plus_body_O
             (fun y : nat -> nat => injective nat nat (fun m : nat => y m))
             (fun (x y : nat) (auto : eq nat x y) =>
              rewrite_l nat x (fun __ : nat => eq nat x __) 
                (refl nat x) y auto))))
    (fun (x_366 : nat)
       (_x_368 : forall x y : nat,
                 eq nat (plus x_366 x) (plus x_366 y) -> eq nat x y) =>
     sym_eq_plus (S x_366)
       (fun y : nat -> nat => injective nat nat (fun m : nat => y m))
       (sym_eq_filter_nat_type_S (nat -> nat) plus_body x_366
          (fun y : nat -> nat => injective nat nat (fun m : nat => y m))
          (sym_eq_plus_body_S x_366
             (fun y : nat -> nat => injective nat nat (fun m : nat => y m))
             (fun (x y : nat)
                (auto : eq nat (S (plus x_366 x)) (S (plus x_366 y))) =>
              _x_368 x y
                (injective_S (plus x_366 x) (plus x_366 y)
                   (rewrite_r nat (plus x_366 (S x))
                      (fun __ : nat => eq nat __ (S (plus x_366 y)))
                      (rewrite_r nat (plus x_366 (S y))
                         (fun __ : nat => eq nat (plus x_366 (S x)) __)
                         (rewrite_l nat (plus x_366 (S x))
                            (fun __ : nat => eq nat (plus x_366 (S x)) __)
                            (refl nat (plus x_366 (S x))) 
                            (plus x_366 (S y))
                            (rewrite_l nat (S (plus x_366 y))
                               (fun __ : nat => eq nat (plus x_366 (S x)) __)
                               (rewrite_l nat (S (plus x_366 x))
                                  (fun __ : nat =>
                                   eq nat __ (S (plus x_366 y))) auto
                                  (plus x_366 (S x)) 
                                  (plus_n_Sm x_366 x)) 
                               (plus x_366 (S y)) 
                               (plus_n_Sm x_366 y))) 
                         (S (plus x_366 y)) (plus_n_Sm x_366 y))
                      (S (plus x_366 x)) (plus_n_Sm x_366 x))))))) n.
Definition times_Sn_m :
  forall n m : nat, eq nat (plus m (times n m)) (times (S n) m) :=
  fun n m : nat =>
  sym_eq_times (S n)
    (fun y : nat -> nat => eq nat (plus m (times n m)) (y m))
    (sym_eq_filter_nat_type_S (nat -> nat) times_body n
       (fun y : nat -> nat => eq nat (plus m (times n m)) (y m))
       (sym_eq_times_body_S n
          (fun y : nat -> nat => eq nat (plus m (times n m)) (y m))
          (refl nat (plus m (times n m))))).
Definition times_O_n : forall n : nat, eq nat O (times O n) :=
  fun n : nat =>
  sym_eq_times O (fun y : nat -> nat => eq nat O (y n))
    (sym_eq_filter_nat_type_O (nat -> nat) times_body
       (fun y : nat -> nat => eq nat O (y n))
       (sym_eq_times_body_O (fun y : nat -> nat => eq nat O (y n))
          (refl nat O))).
Definition times_n_O : forall n : nat, eq nat O (times n O) :=
  fun n : nat =>
  nat_ind (fun _x_365 : nat => eq nat O (times _x_365 O))
    (rewrite_l nat O (fun __ : nat => eq nat O __) 
       (refl nat O) (times O O) (times_O_n O))
    (fun (x_366 : nat) (_x_368 : eq nat O (times x_366 O)) =>
     rewrite_l nat (plus O (times x_366 O)) (fun __ : nat => eq nat O __)
       (rewrite_l nat O (fun __ : nat => eq nat O (plus O __))
          (rewrite_l nat O (fun __ : nat => eq nat O __) 
             (refl nat O) (plus O O) (plus_O_n O)) 
          (times x_366 O) _x_368) (times (S x_366) O) 
       (times_Sn_m x_366 O)) n.
Definition times_n_Sm :
  forall n m : nat, eq nat (plus n (times n m)) (times n (S m)) :=
  fun n : nat =>
  nat_ind
    (fun _x_365 : nat =>
     forall m : nat,
     eq nat (plus _x_365 (times _x_365 m)) (times _x_365 (S m)))
    (sym_eq_times O
       (fun y : nat -> nat =>
        forall m : nat, eq nat (plus O (times O m)) (y (S m)))
       (sym_eq_times O
          (fun y : nat -> nat =>
           forall m : nat,
           eq nat (plus O (y m))
             (filter_nat_type (nat -> nat) times_body O (S m)))
          (sym_eq_filter_nat_type_O (nat -> nat) times_body
             (fun y : nat -> nat =>
              forall m : nat,
              eq nat (plus O (y m))
                (filter_nat_type (nat -> nat) times_body O (S m)))
             (sym_eq_filter_nat_type_O (nat -> nat) times_body
                (fun y : nat -> nat =>
                 forall m : nat, eq nat (plus O (times_body O m)) (y (S m)))
                (sym_eq_times_body_O
                   (fun y : nat -> nat =>
                    forall m : nat,
                    eq nat (plus O (times_body O m)) (y (S m)))
                   (sym_eq_times_body_O
                      (fun y : nat -> nat =>
                       forall m : nat, eq nat (plus O (y m)) O)
                      (sym_eq_plus O
                         (fun y : nat -> nat =>
                          forall m : nat, eq nat (y O) O)
                         (sym_eq_filter_nat_type_O 
                            (nat -> nat) plus_body
                            (fun y : nat -> nat =>
                             forall m : nat, eq nat (y O) O)
                            (sym_eq_plus_body_O
                               (fun y : nat -> nat =>
                                forall m : nat, eq nat (y O) O)
                               (fun _m : nat => refl nat O))))))))))
    (fun (x_366 : nat)
       (_x_368 : forall m : nat,
                 eq nat (plus x_366 (times x_366 m)) (times x_366 (S m)))
       (m : nat) =>
     sym_eq_times (S x_366)
       (fun y : nat -> nat =>
        eq nat (plus (S x_366) (times (S x_366) m)) (y (S m)))
       (sym_eq_times (S x_366)
          (fun y : nat -> nat =>
           eq nat (plus (S x_366) (y m))
             (filter_nat_type (nat -> nat) times_body (S x_366) (S m)))
          (sym_eq_filter_nat_type_S (nat -> nat) times_body x_366
             (fun y : nat -> nat =>
              eq nat (plus (S x_366) (y m))
                (filter_nat_type (nat -> nat) times_body (S x_366) (S m)))
             (sym_eq_filter_nat_type_S (nat -> nat) times_body x_366
                (fun y : nat -> nat =>
                 eq nat (plus (S x_366) (times_body (S x_366) m)) (y (S m)))
                (sym_eq_times_body_S x_366
                   (fun y : nat -> nat =>
                    eq nat (plus (S x_366) (times_body (S x_366) m))
                      (y (S m)))
                   (sym_eq_times_body_S x_366
                      (fun y : nat -> nat =>
                       eq nat (plus (S x_366) (y m))
                         (plus (S m) (times x_366 (S m))))
                      (sym_eq_plus (S x_366)
                         (fun y : nat -> nat =>
                          eq nat (y (plus m (times x_366 m)))
                            (plus (S m) (times x_366 (S m))))
                         (sym_eq_filter_nat_type_S 
                            (nat -> nat) plus_body x_366
                            (fun y : nat -> nat =>
                             eq nat (y (plus m (times x_366 m)))
                               (plus (S m) (times x_366 (S m))))
                            (sym_eq_plus_body_S x_366
                               (fun y : nat -> nat =>
                                eq nat (y (plus m (times x_366 m)))
                                  (plus (S m) (times x_366 (S m))))
                               (sym_eq_plus (S m)
                                  (fun y : nat -> nat =>
                                   eq nat
                                     (S (plus x_366 (plus m (times x_366 m))))
                                     (y (times x_366 (S m))))
                                  (sym_eq_filter_nat_type_S 
                                     (nat -> nat) plus_body m
                                     (fun y : nat -> nat =>
                                      eq nat
                                        (S
                                           (plus x_366
                                              (plus m (times x_366 m))))
                                        (y (times x_366 (S m))))
                                     (sym_eq_plus_body_S m
                                        (fun y : nat -> nat =>
                                         eq nat
                                           (S
                                              (plus x_366
                                                 (plus m (times x_366 m))))
                                           (y (times x_366 (S m))))
                                        (rewrite_r nat
                                           (plus x_366
                                              (S (plus m (times x_366 m))))
                                           (fun __ : nat =>
                                            eq nat __
                                              (S (plus m (times x_366 (S m)))))
                                           (rewrite_r nat
                                              (plus m (S (times x_366 m)))
                                              (fun __ : nat =>
                                               eq nat 
                                                 (plus x_366 __)
                                                 (S
                                                 (plus m (times x_366 (S m)))))
                                              (rewrite_l nat
                                                 (plus x_366 (times x_366 m))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (plus x_366
                                                 (plus m (S (times x_366 m))))
                                                 (S (plus m __)))
                                                 (rewrite_r nat
                                                 (plus x_366
                                                 (plus m (times x_366 m)))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (plus x_366
                                                 (plus m (S (times x_366 m))))
                                                 (S __))
                                                 (rewrite_r nat
                                                 (plus x_366
                                                 (S (plus m (times x_366 m))))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (plus x_366
                                                 (plus m (S (times x_366 m))))
                                                 __)
                                                 (rewrite_r nat
                                                 (plus m (S (times x_366 m)))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (plus x_366
                                                 (plus m (S (times x_366 m))))
                                                 (plus x_366 __))
                                                 (refl nat
                                                 (plus x_366
                                                 (plus m (S (times x_366 m)))))
                                                 (S (plus m (times x_366 m)))
                                                 (plus_n_Sm m (times x_366 m)))
                                                 (S
                                                 (plus x_366
                                                 (plus m (times x_366 m))))
                                                 (plus_n_Sm x_366
                                                 (plus m (times x_366 m))))
                                                 (plus m
                                                 (plus x_366 (times x_366 m)))
                                                 (rewrite_l nat
                                                 (plus 
                                                 (plus x_366 m)
                                                 (times x_366 m))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (plus m
                                                 (plus x_366 (times x_366 m)))
                                                 __)
                                                 (assoc_plus1 
                                                 (times x_366 m) x_366 m)
                                                 (plus x_366
                                                 (plus m (times x_366 m)))
                                                 (associative_plus x_366 m
                                                 (times x_366 m))))
                                                 (times x_366 (S m))
                                                 (_x_368 m))
                                              (S (plus m (times x_366 m)))
                                              (plus_n_Sm m (times x_366 m)))
                                           (S
                                              (plus x_366
                                                 (plus m (times x_366 m))))
                                           (plus_n_Sm x_366
                                              (plus m (times x_366 m))))))))))))))))
    n.
Definition commutative_times : commutative nat times :=
  fun n : nat =>
  nat_ind
    (fun _x_365 : nat =>
     forall y : nat, eq nat (times _x_365 y) (times y _x_365))
    (sym_eq_times O
       (fun y : nat -> nat => forall z : nat, eq nat (y z) (times z O))
       (sym_eq_filter_nat_type_O (nat -> nat) times_body
          (fun y : nat -> nat => forall z : nat, eq nat (y z) (times z O))
          (sym_eq_times_body_O
             (fun y : nat -> nat => forall z : nat, eq nat (y z) (times z O))
             (fun y : nat =>
              rewrite_l nat O (fun __ : nat => eq nat O __) 
                (refl nat O) (times y O) (times_n_O y)))))
    (fun (x_366 : nat)
       (_x_368 : forall y : nat, eq nat (times x_366 y) (times y x_366))
       (y : nat) =>
     sym_eq_times (S x_366)
       (fun z : nat -> nat => eq nat (z y) (times y (S x_366)))
       (sym_eq_filter_nat_type_S (nat -> nat) times_body x_366
          (fun z : nat -> nat => eq nat (z y) (times y (S x_366)))
          (sym_eq_times_body_S x_366
             (fun z : nat -> nat => eq nat (z y) (times y (S x_366)))
             (rewrite_l nat (plus y (times y x_366))
                (fun __ : nat => eq nat (plus y (times x_366 y)) __)
                (rewrite_l nat (times x_366 y)
                   (fun __ : nat =>
                    eq nat (plus y (times x_366 y)) (plus y __))
                   (refl nat (plus y (times x_366 y))) 
                   (times y x_366) (_x_368 y)) (times y (S x_366))
                (times_n_Sm y x_366))))) n.
Definition distributive_times_plus : distributive nat times plus :=
  fun n : nat =>
  nat_ind
    (fun _x_365 : nat =>
     forall y z : nat,
     eq nat (times _x_365 (plus y z))
       (plus (times _x_365 y) (times _x_365 z)))
    (sym_eq_times O
       (fun x : nat -> nat =>
        forall y z : nat,
        eq nat (times O (plus y z)) (plus (times O y) (x z)))
       (sym_eq_times O
          (fun x : nat -> nat =>
           forall y z : nat,
           eq nat (times O (plus y z))
             (plus (x y) (filter_nat_type (nat -> nat) times_body O z)))
          (sym_eq_times O
             (fun x : nat -> nat =>
              forall y z : nat,
              eq nat (x (plus y z))
                (plus (filter_nat_type (nat -> nat) times_body O y)
                   (filter_nat_type (nat -> nat) times_body O z)))
             (sym_eq_filter_nat_type_O (nat -> nat) times_body
                (fun x : nat -> nat =>
                 forall y z : nat,
                 eq nat (x (plus y z))
                   (plus (filter_nat_type (nat -> nat) times_body O y)
                      (filter_nat_type (nat -> nat) times_body O z)))
                (sym_eq_filter_nat_type_O (nat -> nat) times_body
                   (fun x : nat -> nat =>
                    forall y z : nat,
                    eq nat (times_body O (plus y z))
                      (plus (x y)
                         (filter_nat_type (nat -> nat) times_body O z)))
                   (sym_eq_filter_nat_type_O (nat -> nat) times_body
                      (fun x : nat -> nat =>
                       forall y z : nat,
                       eq nat (times_body O (plus y z))
                         (plus (times_body O y) (x z)))
                      (sym_eq_times_body_O
                         (fun x : nat -> nat =>
                          forall y z : nat,
                          eq nat (times_body O (plus y z))
                            (plus (times_body O y) (x z)))
                         (sym_eq_times_body_O
                            (fun x : nat -> nat =>
                             forall y z : nat,
                             eq nat (times_body O (plus y z)) (plus (x y) O))
                            (sym_eq_times_body_O
                               (fun x : nat -> nat =>
                                forall y z : nat,
                                eq nat (x (plus y z)) (plus O O))
                               (sym_eq_plus O
                                  (fun x : nat -> nat =>
                                   forall y z : nat, eq nat O (x O))
                                  (sym_eq_filter_nat_type_O 
                                     (nat -> nat) plus_body
                                     (fun x : nat -> nat =>
                                      forall y z : nat, eq nat O (x O))
                                     (sym_eq_plus_body_O
                                        (fun x : nat -> nat =>
                                         forall y z : nat, eq nat O (x O))
                                        (fun _y _z : nat => refl nat O)))))))))))))
    (fun (x_366 : nat)
       (_x_368 : forall y z : nat,
                 eq nat (times x_366 (plus y z))
                   (plus (times x_366 y) (times x_366 z))) 
       (y z : nat) =>
     sym_eq_times (S x_366)
       (fun x : nat -> nat =>
        eq nat (times (S x_366) (plus y z)) (plus (times (S x_366) y) (x z)))
       (sym_eq_times (S x_366)
          (fun x : nat -> nat =>
           eq nat (times (S x_366) (plus y z))
             (plus (x y)
                (filter_nat_type (nat -> nat) times_body (S x_366) z)))
          (sym_eq_times (S x_366)
             (fun x : nat -> nat =>
              eq nat (x (plus y z))
                (plus (filter_nat_type (nat -> nat) times_body (S x_366) y)
                   (filter_nat_type (nat -> nat) times_body (S x_366) z)))
             (sym_eq_filter_nat_type_S (nat -> nat) times_body x_366
                (fun x : nat -> nat =>
                 eq nat (x (plus y z))
                   (plus
                      (filter_nat_type (nat -> nat) times_body (S x_366) y)
                      (filter_nat_type (nat -> nat) times_body (S x_366) z)))
                (sym_eq_filter_nat_type_S (nat -> nat) times_body x_366
                   (fun x : nat -> nat =>
                    eq nat (times_body (S x_366) (plus y z))
                      (plus (x y)
                         (filter_nat_type (nat -> nat) times_body (S x_366) z)))
                   (sym_eq_filter_nat_type_S (nat -> nat) times_body x_366
                      (fun x : nat -> nat =>
                       eq nat (times_body (S x_366) (plus y z))
                         (plus (times_body (S x_366) y) (x z)))
                      (sym_eq_times_body_S x_366
                         (fun x : nat -> nat =>
                          eq nat (times_body (S x_366) (plus y z))
                            (plus (times_body (S x_366) y) (x z)))
                         (sym_eq_times_body_S x_366
                            (fun x : nat -> nat =>
                             eq nat (times_body (S x_366) (plus y z))
                               (plus (x y) (plus z (times x_366 z))))
                            (sym_eq_times_body_S x_366
                               (fun x : nat -> nat =>
                                eq nat (x (plus y z))
                                  (plus (plus y (times x_366 y))
                                     (plus z (times x_366 z))))
                               (rewrite_r nat
                                  (plus y (plus z (times x_366 (plus y z))))
                                  (fun __ : nat =>
                                   eq nat __
                                     (plus (plus y (times x_366 y))
                                        (plus z (times x_366 z))))
                                  (rewrite_r nat
                                     (plus y
                                        (plus (times x_366 y)
                                           (plus z (times x_366 z))))
                                     (fun __ : nat =>
                                      eq nat
                                        (plus y
                                           (plus z (times x_366 (plus y z))))
                                        __)
                                     (rewrite_r nat
                                        (plus z
                                           (plus (times x_366 y)
                                              (times x_366 z)))
                                        (fun __ : nat =>
                                         eq nat
                                           (plus y
                                              (plus z
                                                 (times x_366 (plus y z))))
                                           (plus y __))
                                        (rewrite_l nat
                                           (times x_366 (plus y z))
                                           (fun __ : nat =>
                                            eq nat
                                              (plus y
                                                 (plus z
                                                 (times x_366 (plus y z))))
                                              (plus y (plus z __)))
                                           (refl nat
                                              (plus y
                                                 (plus z
                                                 (times x_366 (plus y z)))))
                                           (plus (times x_366 y)
                                              (times x_366 z)) 
                                           (_x_368 y z))
                                        (plus (times x_366 y)
                                           (plus z (times x_366 z)))
                                        (rewrite_l nat
                                           (plus (plus z (times x_366 y))
                                              (times x_366 z))
                                           (fun __ : nat =>
                                            eq nat
                                              (plus 
                                                 (times x_366 y)
                                                 (plus z (times x_366 z))) __)
                                           (assoc_plus1 
                                              (times x_366 z) z
                                              (times x_366 y))
                                           (plus z
                                              (plus 
                                                 (times x_366 y)
                                                 (times x_366 z)))
                                           (associative_plus z
                                              (times x_366 y) 
                                              (times x_366 z))))
                                     (plus (plus y (times x_366 y))
                                        (plus z (times x_366 z)))
                                     (associative_plus y 
                                        (times x_366 y)
                                        (plus z (times x_366 z))))
                                  (plus (plus y z) (times x_366 (plus y z)))
                                  (associative_plus y z
                                     (times x_366 (plus y z))))))))))))) n.
Definition distributive_times_plus_r :
  forall a b c : nat,
  eq nat (times (plus b c) a) (plus (times b a) (times c a)) :=
  fun a b c : nat =>
  rewrite_r nat (times a (plus b c))
    (fun __ : nat => eq nat __ (plus (times b a) (times c a)))
    (rewrite_r nat (times a b)
       (fun __ : nat => eq nat (times a (plus b c)) (plus __ (times c a)))
       (rewrite_r nat (times a c)
          (fun __ : nat => eq nat (times a (plus b c)) (plus (times a b) __))
          (rewrite_l nat (times a (plus b c))
             (fun __ : nat => eq nat (times a (plus b c)) __)
             (refl nat (times a (plus b c))) (plus (times a b) (times a c))
             (distributive_times_plus a b c)) (times c a)
          (commutative_times c a)) (times b a) (commutative_times b a))
    (times (plus b c) a) (commutative_times (plus b c) a).
Definition associative_times : associative nat times :=
  fun n : nat =>
  nat_ind
    (fun _x_365 : nat =>
     forall y z : nat,
     eq nat (times (times _x_365 y) z) (times _x_365 (times y z)))
    (sym_eq_times O
       (fun x : nat -> nat =>
        forall y z : nat, eq nat (times (times O y) z) (x (times y z)))
       (sym_eq_times O
          (fun x : nat -> nat =>
           forall y z : nat,
           eq nat (times (x y) z)
             (filter_nat_type (nat -> nat) times_body O (times y z)))
          (sym_eq_filter_nat_type_O (nat -> nat) times_body
             (fun x : nat -> nat =>
              forall y z : nat,
              eq nat (times (x y) z)
                (filter_nat_type (nat -> nat) times_body O (times y z)))
             (sym_eq_filter_nat_type_O (nat -> nat) times_body
                (fun x : nat -> nat =>
                 forall y z : nat,
                 eq nat (times (times_body O y) z) (x (times y z)))
                (sym_eq_times_body_O
                   (fun x : nat -> nat =>
                    forall y z : nat,
                    eq nat (times (times_body O y) z) (x (times y z)))
                   (sym_eq_times_body_O
                      (fun x : nat -> nat =>
                       forall y z : nat, eq nat (times (x y) z) O)
                      (sym_eq_times O
                         (fun x : nat -> nat =>
                          forall y z : nat, eq nat (x z) O)
                         (sym_eq_filter_nat_type_O 
                            (nat -> nat) times_body
                            (fun x : nat -> nat =>
                             forall y z : nat, eq nat (x z) O)
                            (sym_eq_times_body_O
                               (fun x : nat -> nat =>
                                forall y z : nat, eq nat (x z) O)
                               (fun _y _z : nat => refl nat O))))))))))
    (fun (x_366 : nat)
       (_x_368 : forall y z : nat,
                 eq nat (times (times x_366 y) z) (times x_366 (times y z)))
       (y z : nat) =>
     sym_eq_times (S x_366)
       (fun x : nat -> nat =>
        eq nat (times (times (S x_366) y) z) (x (times y z)))
       (sym_eq_times (S x_366)
          (fun x : nat -> nat =>
           eq nat (times (x y) z)
             (filter_nat_type (nat -> nat) times_body (S x_366) (times y z)))
          (sym_eq_filter_nat_type_S (nat -> nat) times_body x_366
             (fun x : nat -> nat =>
              eq nat (times (x y) z)
                (filter_nat_type (nat -> nat) times_body 
                   (S x_366) (times y z)))
             (sym_eq_filter_nat_type_S (nat -> nat) times_body x_366
                (fun x : nat -> nat =>
                 eq nat (times (times_body (S x_366) y) z) (x (times y z)))
                (sym_eq_times_body_S x_366
                   (fun x : nat -> nat =>
                    eq nat (times (times_body (S x_366) y) z) (x (times y z)))
                   (sym_eq_times_body_S x_366
                      (fun x : nat -> nat =>
                       eq nat (times (x y) z)
                         (plus (times y z) (times x_366 (times y z))))
                      (rewrite_r nat
                         (plus (times y z) (times x_366 (times y z)))
                         (fun __ : nat =>
                          eq nat __
                            (plus (times y z) (times x_366 (times y z))))
                         (refl nat
                            (plus (times y z) (times x_366 (times y z))))
                         (times (plus y (times x_366 y)) z)
                         (rewrite_l nat (times (times x_366 y) z)
                            (fun __ : nat =>
                             eq nat (times (plus y (times x_366 y)) z)
                               (plus (times y z) __))
                            (distributive_times_plus_r z y (times x_366 y))
                            (times x_366 (times y z)) 
                            (_x_368 y z))))))))) n.
Definition times_times :
  forall x y z : nat, eq nat (times x (times y z)) (times y (times x z)) :=
  fun x y z : nat =>
  rewrite_r nat (times y (times x z))
    (fun __ : nat => eq nat __ (times y (times x z)))
    (refl nat (times y (times x z))) (times x (times y z))
    (rewrite_l nat (times (times x y) z)
       (fun __ : nat => eq nat __ (times y (times x z)))
       (rewrite_l nat (times y x)
          (fun __ : nat => eq nat (times __ z) (times y (times x z)))
          (associative_times y x z) (times x y) (commutative_times y x))
       (times x (times y z)) (associative_times x y z)).
Definition times_n_1 : forall n : nat, eq nat n (times n (S O)) :=
  fun n : nat =>
  rewrite_l nat (plus n (times n O)) (fun __ : nat => eq nat n __)
    (rewrite_l nat O (fun __ : nat => eq nat n (plus n __))
       (rewrite_l nat n (fun __ : nat => eq nat n __) 
          (refl nat n) (plus n O) (plus_n_O n)) (times n O) 
       (times_n_O n)) (times n (S O)) (times_n_Sm n O).
Definition minus_S_S :
  forall n m : nat, eq nat (minus (S n) (S m)) (minus n m) :=
  fun n m : nat =>
  eq_match_nat_type_S nat (S n) (fun q : nat => minus n q) m
    (fun y : nat => eq nat (minus (S n) (S m)) y)
    (eq_minus_body_S n
       (fun y : nat -> nat => eq nat (minus (S n) (S m)) (y (S m)))
       (eq_filter_nat_type_S (nat -> nat) minus_body n
          (fun y : nat -> nat => eq nat (minus (S n) (S m)) (y (S m)))
          (eq_minus (S n)
             (fun y : nat -> nat => eq nat (minus (S n) (S m)) (y (S m)))
             (refl nat (minus (S n) (S m)))))).
Definition minus_O_n : forall n : nat, eq nat O (minus O n) :=
  fun n : nat =>
  match_nat_prop (fun __ : nat => eq nat O (minus O __))
    (sym_eq_minus O (fun y : nat -> nat => eq nat O (y O))
       (sym_eq_filter_nat_type_O (nat -> nat) minus_body
          (fun y : nat -> nat => eq nat O (y O))
          (sym_eq_minus_body_O (fun y : nat -> nat => eq nat O (y O))
             (refl nat O))))
    (sym_eq_minus O
       (fun y : nat -> nat => forall n0 : nat, eq nat O (y (S n0)))
       (sym_eq_filter_nat_type_O (nat -> nat) minus_body
          (fun y : nat -> nat => forall n0 : nat, eq nat O (y (S n0)))
          (sym_eq_minus_body_O
             (fun y : nat -> nat => forall n0 : nat, eq nat O (y (S n0)))
             (fun auto : nat => refl nat O)))) n.
Definition minus_n_O : forall n : nat, eq nat n (minus n O) :=
  fun n : nat =>
  match_nat_prop (fun __ : nat => eq nat __ (minus __ O))
    (rewrite_l nat O (fun __ : nat => eq nat O __) 
       (refl nat O) (minus O O) (minus_O_n O))
    (fun auto : nat =>
     sym_eq_minus (S auto) (fun y : nat -> nat => eq nat (S auto) (y O))
       (sym_eq_filter_nat_type_S (nat -> nat) minus_body auto
          (fun y : nat -> nat => eq nat (S auto) (y O))
          (sym_eq_minus_body_S auto
             (fun y : nat -> nat => eq nat (S auto) (y O))
             (sym_eq_match_nat_type_O nat (S auto)
                (fun q : nat => minus auto q)
                (fun y : nat => eq nat (S auto) y) 
                (refl nat (S auto)))))) n.
Definition minus_n_n : forall n : nat, eq nat O (minus n n) :=
  fun n : nat =>
  nat_ind (fun _x_365 : nat => eq nat O (minus _x_365 _x_365))
    (rewrite_l nat O (fun __ : nat => eq nat O __) 
       (refl nat O) (minus O O) (minus_O_n O))
    (fun (x_366 : nat) (_x_368 : eq nat O (minus x_366 x_366)) =>
     rewrite_r nat (minus x_366 x_366) (fun __ : nat => eq nat O __)
       (rewrite_l nat O (fun __ : nat => eq nat O __) 
          (refl nat O) (minus x_366 x_366) _x_368)
       (minus (S x_366) (S x_366)) (minus_S_S x_366 x_366)) n.
Definition eq_minus_S_pred :
  forall n m : nat, eq nat (minus n (S m)) (pred (minus n m)) :=
  nat_elim2
    (fun __ _0 : nat => eq nat (minus __ (S _0)) (pred (minus __ _0)))
    (fun _n : nat =>
     sym_eq_minus O
       (fun y : nat -> nat => eq nat (minus O (S _n)) (pred (y _n)))
       (sym_eq_minus O
          (fun y : nat -> nat =>
           eq nat (y (S _n))
             (pred (filter_nat_type (nat -> nat) minus_body O _n)))
          (sym_eq_filter_nat_type_O (nat -> nat) minus_body
             (fun y : nat -> nat =>
              eq nat (y (S _n))
                (pred (filter_nat_type (nat -> nat) minus_body O _n)))
             (sym_eq_filter_nat_type_O (nat -> nat) minus_body
                (fun y : nat -> nat =>
                 eq nat (minus_body O (S _n)) (pred (y _n)))
                (sym_eq_minus_body_O
                   (fun y : nat -> nat =>
                    eq nat (minus_body O (S _n)) (pred (y _n)))
                   (sym_eq_minus_body_O
                      (fun y : nat -> nat =>
                       eq nat (y (S _n))
                         (match_nat_type nat O (fun p : nat => p) O))
                      (sym_eq_match_nat_type_O nat O 
                         (fun p : nat => p) (fun y : nat => eq nat O y)
                         (refl nat O))))))))
    (fun n : nat =>
     sym_eq_minus (S n)
       (fun y : nat -> nat => eq nat (minus (S n) (S O)) (pred (y O)))
       (sym_eq_minus (S n)
          (fun y : nat -> nat =>
           eq nat (y (S O))
             (pred (filter_nat_type (nat -> nat) minus_body (S n) O)))
          (sym_eq_filter_nat_type_S (nat -> nat) minus_body n
             (fun y : nat -> nat =>
              eq nat (y (S O))
                (pred (filter_nat_type (nat -> nat) minus_body (S n) O)))
             (sym_eq_filter_nat_type_S (nat -> nat) minus_body n
                (fun y : nat -> nat =>
                 eq nat (minus_body (S n) (S O)) (pred (y O)))
                (sym_eq_minus_body_S n
                   (fun y : nat -> nat =>
                    eq nat (minus_body (S n) (S O)) (pred (y O)))
                   (sym_eq_minus_body_S n
                      (fun y : nat -> nat =>
                       eq nat (y (S O))
                         (pred
                            (match_nat_type nat (S n)
                               (fun q : nat => minus n q) O)))
                      (sym_eq_match_nat_type_S nat 
                         (S n) (fun q : nat => minus n q) O
                         (fun y : nat =>
                          eq nat y
                            (match_nat_type nat O 
                               (fun p : nat => p)
                               (match_nat_type nat 
                                  (S n) (fun q : nat => minus n q) O)))
                         (sym_eq_match_nat_type_O nat 
                            (S n) (fun q : nat => minus n q)
                            (fun y : nat =>
                             eq nat (minus n O)
                               (match_nat_type nat O (fun p : nat => p) y))
                            (sym_eq_match_nat_type_S nat O 
                               (fun q : nat => q) n
                               (fun y : nat => eq nat (minus n O) y)
                               (rewrite_l nat n (fun __ : nat => eq nat __ n)
                                  (refl nat n) (minus n O) 
                                  (minus_n_O n)))))))))))
    (fun n m : nat =>
     sym_eq_minus (S n)
       (fun y : nat -> nat =>
        eq nat (minus n (S m)) (pred (minus n m)) ->
        eq nat (minus (S n) (S (S m))) (pred (y (S m))))
       (sym_eq_minus (S n)
          (fun y : nat -> nat =>
           eq nat (minus n (S m)) (pred (minus n m)) ->
           eq nat (y (S (S m)))
             (pred (filter_nat_type (nat -> nat) minus_body (S n) (S m))))
          (sym_eq_filter_nat_type_S (nat -> nat) minus_body n
             (fun y : nat -> nat =>
              eq nat (minus n (S m)) (pred (minus n m)) ->
              eq nat (y (S (S m)))
                (pred (filter_nat_type (nat -> nat) minus_body (S n) (S m))))
             (sym_eq_filter_nat_type_S (nat -> nat) minus_body n
                (fun y : nat -> nat =>
                 eq nat (minus n (S m)) (pred (minus n m)) ->
                 eq nat (minus_body (S n) (S (S m))) (pred (y (S m))))
                (sym_eq_minus_body_S n
                   (fun y : nat -> nat =>
                    eq nat (minus n (S m)) (pred (minus n m)) ->
                    eq nat (minus_body (S n) (S (S m))) (pred (y (S m))))
                   (sym_eq_minus_body_S n
                      (fun y : nat -> nat =>
                       eq nat (minus n (S m)) (pred (minus n m)) ->
                       eq nat (y (S (S m)))
                         (pred
                            (match_nat_type nat (S n)
                               (fun q : nat => minus n q) 
                               (S m))))
                      (sym_eq_match_nat_type_S nat 
                         (S n) (fun q : nat => minus n q) 
                         (S m)
                         (fun y : nat =>
                          eq nat (minus n (S m)) (pred (minus n m)) ->
                          eq nat y
                            (match_nat_type nat O 
                               (fun p : nat => p)
                               (match_nat_type nat 
                                  (S n) (fun q : nat => minus n q) 
                                  (S m))))
                         (sym_eq_match_nat_type_S nat 
                            (S n) (fun q : nat => minus n q) m
                            (fun y : nat =>
                             eq nat (minus n (S m)) (pred (minus n m)) ->
                             eq nat (minus n (S m))
                               (match_nat_type nat O (fun p : nat => p) y))
                            (fun
                               auto : eq nat (minus n (S m))
                                        (match_nat_type nat O
                                           (fun p : nat => p) 
                                           (minus n m)) =>
                             rewrite_r nat
                               (match_nat_type nat O 
                                  (fun p : nat => p) 
                                  (minus n m))
                               (fun __ : nat =>
                                eq nat __
                                  (match_nat_type nat O 
                                     (fun p : nat => p) 
                                     (minus n m)))
                               (refl nat
                                  (match_nat_type nat O 
                                     (fun p : nat => p) 
                                     (minus n m))) 
                               (minus n (S m)) auto))))))))).
Definition not_eq_S :
  forall n m : nat, Not (eq nat n m) -> Not (eq nat (S n) (S m)) :=
  fun (n m : nat) (auto : Not (eq nat n m)) =>
  not_to_not (eq nat (S n) (S m)) (eq nat n m)
    (fun auto' : eq nat (S n) (S m) =>
     rewrite_l nat m (fun __ : nat => eq nat __ m) 
       (refl nat m) n
       (rewrite_r nat (pred (S n)) (fun __ : nat => eq nat m __)
          (rewrite_r nat (S m) (fun __ : nat => eq nat m (pred __))
             (pred_Sn m) (S n) auto') n (pred_Sn n))) auto.
Definition not_eq_O_S : forall n : nat, Not (eq nat O (S n)) :=
  fun (n : nat) (eqOS : eq nat O (S n)) =>
  eq_match_nat_type_O Prop False (fun p : nat => True) 
    (fun y : Prop => y)
    (eq_ind_r nat (S n) (fun x : nat => not_zero x)
       (sym_eq_match_nat_type_S Prop False (fun p : nat => True) n
          (fun y : Prop => y) I) O eqOS).
Definition lt_to_not_zero : forall n m : nat, lt n m -> not_zero m :=
  fun (n m : nat) (Hlt : lt n m) =>
  le_ind (S n) (fun x_417 : nat => not_zero x_417)
    (sym_eq_match_nat_type_S Prop False (fun p : nat => True) n
       (fun y : Prop => y) I)
    (fun (m0 : nat) (_x_419 : le (S n) m0) (_x_421 : not_zero m0) =>
     sym_eq_match_nat_type_S Prop False (fun p : nat => True) m0
       (fun y : Prop => y) I) m Hlt.
Definition le_S_S : forall n m : nat, le n m -> le (S n) (S m) :=
  fun (n m : nat) (lenm : le n m) =>
  le_ind n (fun x_417 : nat => le (S n) (S x_417)) 
    (le_n (S n))
    (fun (m0 : nat) (_x_419 : le n m0) (_x_421 : le (S n) (S m0)) =>
     le_S (S n) (S m0) _x_421) m lenm.
Definition le_O_n : forall n : nat, le O n :=
  fun n : nat =>
  nat_ind (le O) (le_n O)
    (fun (x_366 : nat) (_x_368 : le O x_366) => le_S O x_366 _x_368) n.
Definition le_n_Sn : forall n : nat, le n (S n) :=
  fun n : nat => le_S n n (le_n n).
Definition transitive_le : transitive nat le :=
  fun (a b c : nat) (leab : le a b) (lebc : le b c) =>
  le_ind b (fun x_417 : nat => le a x_417) leab
    (fun (m : nat) (_x_419 : le b m) (_x_421 : le a m) => le_S a m _x_421) c
    lebc.
Definition le_pred_n : forall n : nat, le (pred n) n :=
  fun n : nat =>
  nat_ind (fun _x_365 : nat => le (pred _x_365) _x_365)
    (eq_match_nat_type_O nat O (fun p : nat => p)
       (fun y : nat => le (match_nat_type nat O (fun p : nat => p) O) y)
       (le_n (pred O)))
    (fun (x_366 : nat) (_x_368 : le (pred x_366) x_366) =>
     eq_match_nat_type_S nat O (fun p : nat => p) x_366
       (fun y : nat => le (pred (S x_366)) (S y)) 
       (le_n_Sn (pred (S x_366)))) n.
Definition monotonic_pred : monotonic nat le pred :=
  fun (n m : nat) (lenm : le n m) =>
  le_ind n (fun x_417 : nat => le (pred n) (pred x_417)) 
    (le_n (pred n))
    (fun (m0 : nat) (_x_419 : le n m0) (_x_421 : le (pred n) (pred m0)) =>
     transitive_le (pred n) n (pred (S m0)) (le_pred_n n)
       (sym_eq_match_nat_type_S nat O (fun p : nat => p) m0
          (fun y : nat => le n y) _x_419)) m lenm.
Definition le_S_S_to_le : forall n m : nat, le (S n) (S m) -> le n m :=
  fun (n m : nat) (auto : le (S n) (S m)) =>
  eq_match_nat_type_S nat O (fun p : nat => p) m (fun y : nat => le n y)
    (eq_match_nat_type_S nat O (fun p : nat => p) n
       (fun y : nat => le y (match_nat_type nat O (fun p : nat => p) (S m)))
       (monotonic_pred (S n) (S m) auto)).
Definition monotonic_le_plus_r :
  forall n : nat, monotonic nat le (fun m : nat => plus n m) :=
  fun n a b : nat =>
  nat_ind (fun _x_365 : nat => le a b -> le (plus _x_365 a) (plus _x_365 b))
    (sym_eq_plus O (fun y : nat -> nat => le a b -> le (plus O a) (y b))
       (sym_eq_plus O
          (fun y : nat -> nat =>
           le a b -> le (y a) (filter_nat_type (nat -> nat) plus_body O b))
          (sym_eq_filter_nat_type_O (nat -> nat) plus_body
             (fun y : nat -> nat =>
              le a b -> le (y a) (filter_nat_type (nat -> nat) plus_body O b))
             (sym_eq_filter_nat_type_O (nat -> nat) plus_body
                (fun y : nat -> nat => le a b -> le (plus_body O a) (y b))
                (sym_eq_plus_body_O
                   (fun y : nat -> nat => le a b -> le (plus_body O a) (y b))
                   (sym_eq_plus_body_O
                      (fun y : nat -> nat => le a b -> le (y a) b)
                      (fun auto : le a b => auto)))))))
    (fun (m : nat) (H : le a b -> le (plus m a) (plus m b)) (leab : le a b)
     =>
     sym_eq_plus (S m) (fun y : nat -> nat => le (plus (S m) a) (y b))
       (sym_eq_plus (S m)
          (fun y : nat -> nat =>
           le (y a) (filter_nat_type (nat -> nat) plus_body (S m) b))
          (sym_eq_filter_nat_type_S (nat -> nat) plus_body m
             (fun y : nat -> nat =>
              le (y a) (filter_nat_type (nat -> nat) plus_body (S m) b))
             (sym_eq_filter_nat_type_S (nat -> nat) plus_body m
                (fun y : nat -> nat => le (plus_body (S m) a) (y b))
                (sym_eq_plus_body_S m
                   (fun y : nat -> nat => le (plus_body (S m) a) (y b))
                   (sym_eq_plus_body_S m
                      (fun y : nat -> nat => le (y a) (S (plus m b)))
                      (le_S_S (plus m a) (plus m b) (H leab)))))))) n.
Definition monotonic_le_plus_l :
  forall m : nat, monotonic nat le (fun n : nat => plus n m) :=
  fun (m x y : nat) (auto : le x y) =>
  eq_coerc (le (plus m x) (plus m y)) (le (plus x m) (plus y m))
    (monotonic_le_plus_r m x y auto)
    (rewrite_r nat (plus m x)
       (fun __ : nat => eq Prop (le (plus m x) (plus m y)) (le __ (plus y m)))
       (rewrite_r nat (plus m y)
          (fun __ : nat =>
           eq Prop (le (plus m x) (plus m y)) (le (plus m x) __))
          (refl Prop (le (plus m x) (plus m y))) (plus y m)
          (commutative_plus y m)) (plus x m) (commutative_plus x m)).
Definition le_plus :
  forall n1 n2 m1 m2 : nat,
  le n1 n2 -> le m1 m2 -> le (plus n1 m1) (plus n2 m2) :=
  fun (n1 n2 m1 m2 : nat) (len : le n1 n2) (lem : le m1 m2) =>
  transitive_le (plus n1 m1) (plus n1 m2) (plus n2 m2)
    (monotonic_le_plus_r n1 m1 m2 lem) (monotonic_le_plus_l m2 n1 n2 len).
Definition le_plus_n : forall n m : nat, le m (plus n m) :=
  fun n m : nat =>
  eq_coerc (le (plus O m) (plus n m)) (le m (plus n m))
    (monotonic_le_plus_l m O n (le_O_n n))
    (rewrite_l nat m
       (fun __ : nat => eq Prop (le __ (plus n m)) (le m (plus n m)))
       (refl Prop (le m (plus n m))) (plus O m) (plus_O_n m)).
Definition le_plus_b : forall b n m : nat, le (plus n b) m -> le n m :=
  fun (b n m : nat) (auto : le (plus n b) m) =>
  transitive_le n (plus n b) m
    (eq_coerc (le n (plus b n)) (le n (plus n b)) 
       (le_plus_n b n)
       (rewrite_r nat (plus b n)
          (fun __ : nat => eq Prop (le n (plus b n)) (le n __))
          (refl Prop (le n (plus b n))) (plus n b) 
          (commutative_plus n b))) auto.
Definition le_plus_n_r : forall n m : nat, le m (plus m n) :=
  fun n m : nat =>
  eq_coerc (le m (plus n m)) (le m (plus m n)) (le_plus_n n m)
    (rewrite_r nat (plus n m)
       (fun __ : nat => eq Prop (le m (plus n m)) (le m __))
       (refl Prop (le m (plus n m))) (plus m n) (commutative_plus m n)).
Definition le_plus_to_le :
  forall a n m : nat, le (plus a n) (plus a m) -> le n m :=
  fun a : nat =>
  nat_ind
    (fun _x_365 : nat =>
     forall n m : nat, le (plus _x_365 n) (plus _x_365 m) -> le n m)
    (fun n m : nat =>
     sym_eq_plus O (fun y : nat -> nat => le (plus O n) (y m) -> le n m)
       (sym_eq_plus O
          (fun y : nat -> nat =>
           le (y n) (filter_nat_type (nat -> nat) plus_body O m) -> le n m)
          (sym_eq_filter_nat_type_O (nat -> nat) plus_body
             (fun y : nat -> nat =>
              le (y n) (filter_nat_type (nat -> nat) plus_body O m) -> le n m)
             (sym_eq_filter_nat_type_O (nat -> nat) plus_body
                (fun y : nat -> nat => le (plus_body O n) (y m) -> le n m)
                (sym_eq_plus_body_O
                   (fun y : nat -> nat => le (plus_body O n) (y m) -> le n m)
                   (sym_eq_plus_body_O
                      (fun y : nat -> nat => le (y n) m -> le n m)
                      (fun auto : le n m => auto)))))))
    (fun (x_366 : nat)
       (_x_368 : forall n m : nat, le (plus x_366 n) (plus x_366 m) -> le n m)
       (n m : nat) =>
     sym_eq_plus (S x_366)
       (fun y : nat -> nat => le (plus (S x_366) n) (y m) -> le n m)
       (sym_eq_plus (S x_366)
          (fun y : nat -> nat =>
           le (y n) (filter_nat_type (nat -> nat) plus_body (S x_366) m) ->
           le n m)
          (sym_eq_filter_nat_type_S (nat -> nat) plus_body x_366
             (fun y : nat -> nat =>
              le (y n) (filter_nat_type (nat -> nat) plus_body (S x_366) m) ->
              le n m)
             (sym_eq_filter_nat_type_S (nat -> nat) plus_body x_366
                (fun y : nat -> nat =>
                 le (plus_body (S x_366) n) (y m) -> le n m)
                (sym_eq_plus_body_S x_366
                   (fun y : nat -> nat =>
                    le (plus_body (S x_366) n) (y m) -> le n m)
                   (sym_eq_plus_body_S x_366
                      (fun y : nat -> nat =>
                       le (y n) (S (plus x_366 m)) -> le n m)
                      (fun auto : le (S (plus x_366 n)) (S (plus x_366 m)) =>
                       eq_coerc (le (pred (S n)) (pred (S m))) 
                         (le n m)
                         (monotonic_pred (S n) (S m)
                            (_x_368 (S n) (S m)
                               (eq_coerc
                                  (le (S (plus x_366 n)) (S (plus x_366 m)))
                                  (le (plus x_366 (S n)) (plus x_366 (S m)))
                                  auto
                                  (rewrite_r nat (plus x_366 (S n))
                                     (fun __ : nat =>
                                      eq Prop (le __ (S (plus x_366 m)))
                                        (le (plus x_366 (S n))
                                           (plus x_366 (S m))))
                                     (rewrite_r nat 
                                        (plus x_366 (S m))
                                        (fun __ : nat =>
                                         eq Prop (le (plus x_366 (S n)) __)
                                           (le (plus x_366 (S n))
                                              (plus x_366 (S m))))
                                        (refl Prop
                                           (le (plus x_366 (S n))
                                              (plus x_366 (S m))))
                                        (S (plus x_366 m))
                                        (plus_n_Sm x_366 m))
                                     (S (plus x_366 n)) 
                                     (plus_n_Sm x_366 n)))))
                         (rewrite_l nat n
                            (fun __ : nat =>
                             eq Prop (le __ (pred (S m))) (le n m))
                            (rewrite_l nat m
                               (fun __ : nat => eq Prop (le n __) (le n m))
                               (refl Prop (le n m)) 
                               (pred (S m)) (pred_Sn m)) 
                            (pred (S n)) (pred_Sn n))))))))) a.
Definition le_plus_to_le_r :
  forall a n m : nat, le (plus n a) (plus m a) -> le n m :=
  fun (a n m : nat) (auto : le (plus n a) (plus m a)) =>
  le_plus_to_le a n m
    (eq_coerc (le (plus n a) (plus m a)) (le (plus a n) (plus a m)) auto
       (rewrite_r nat (plus a n)
          (fun __ : nat =>
           eq Prop (le __ (plus m a)) (le (plus a n) (plus a m)))
          (rewrite_r nat (plus a m)
             (fun __ : nat =>
              eq Prop (le (plus a n) __) (le (plus a n) (plus a m)))
             (refl Prop (le (plus a n) (plus a m))) 
             (plus m a) (commutative_plus m a)) (plus n a)
          (commutative_plus n a))).
Definition monotonic_le_times_r :
  forall n : nat, monotonic nat le (fun m : nat => times n m) :=
  fun (n x y : nat) (lexy : le x y) =>
  nat_ind (fun _x_365 : nat => le (times _x_365 x) (times _x_365 y))
    (sym_eq_times O (fun z : nat -> nat => le (times O x) (z y))
       (sym_eq_times O
          (fun z : nat -> nat =>
           le (z x) (filter_nat_type (nat -> nat) times_body O y))
          (sym_eq_filter_nat_type_O (nat -> nat) times_body
             (fun z : nat -> nat =>
              le (z x) (filter_nat_type (nat -> nat) times_body O y))
             (sym_eq_filter_nat_type_O (nat -> nat) times_body
                (fun z : nat -> nat => le (times_body O x) (z y))
                (sym_eq_times_body_O
                   (fun z : nat -> nat => le (times_body O x) (z y))
                   (sym_eq_times_body_O (fun z : nat -> nat => le (z x) O)
                      (le_O_n O)))))))
    (fun (a : nat) (lea : le (times a x) (times a y)) =>
     sym_eq_times (S a) (fun z : nat -> nat => le (times (S a) x) (z y))
       (sym_eq_times (S a)
          (fun z : nat -> nat =>
           le (z x) (filter_nat_type (nat -> nat) times_body (S a) y))
          (sym_eq_filter_nat_type_S (nat -> nat) times_body a
             (fun z : nat -> nat =>
              le (z x) (filter_nat_type (nat -> nat) times_body (S a) y))
             (sym_eq_filter_nat_type_S (nat -> nat) times_body a
                (fun z : nat -> nat => le (times_body (S a) x) (z y))
                (sym_eq_times_body_S a
                   (fun z : nat -> nat => le (times_body (S a) x) (z y))
                   (sym_eq_times_body_S a
                      (fun z : nat -> nat => le (z x) (plus y (times a y)))
                      (le_plus x y (times a x) (times a y) lexy lea))))))) n.
Definition le_times :
  forall n1 n2 m1 m2 : nat,
  le n1 n2 -> le m1 m2 -> le (times n1 m1) (times n2 m2) :=
  fun (n1 n2 m1 m2 : nat) (len : le n1 n2) (lem : le m1 m2) =>
  transitive_le (times n1 m1) (times n1 m2) (times n2 m2)
    (monotonic_le_times_r n1 m1 m2 lem)
    (eq_coerc (le (times m2 n1) (times m2 n2))
       (le (times n1 m2) (times n2 m2)) (monotonic_le_times_r m2 n1 n2 len)
       (rewrite_r nat (times n1 m2)
          (fun __ : nat =>
           eq Prop (le __ (times m2 n2)) (le (times n1 m2) (times n2 m2)))
          (rewrite_r nat (times n2 m2)
             (fun __ : nat =>
              eq Prop (le (times n1 m2) __) (le (times n1 m2) (times n2 m2)))
             (refl Prop (le (times n1 m2) (times n2 m2))) 
             (times m2 n2) (commutative_times m2 n2)) 
          (times m2 n1) (commutative_times m2 n1))).
Definition le_plus_minus_m_m : forall n m : nat, le n (plus (minus n m) m) :=
  fun n : nat =>
  nat_ind
    (fun _x_365 : nat => forall m : nat, le _x_365 (plus (minus _x_365 m) m))
    (sym_eq_minus O
       (fun y : nat -> nat => forall m : nat, le O (plus (y m) m))
       (sym_eq_filter_nat_type_O (nat -> nat) minus_body
          (fun y : nat -> nat => forall m : nat, le O (plus (y m) m))
          (sym_eq_minus_body_O
             (fun y : nat -> nat => forall m : nat, le O (plus (y m) m))
             (fun m : nat => le_plus_n_r m O))))
    (fun (a : nat) (Hind : forall m : nat, le a (plus (minus a m) m))
       (m : nat) =>
     match_nat_prop (fun __ : nat => le (S a) (plus (minus (S a) __) __))
       (sym_eq_minus (S a) (fun y : nat -> nat => le (S a) (plus (y O) O))
          (sym_eq_filter_nat_type_S (nat -> nat) minus_body a
             (fun y : nat -> nat => le (S a) (plus (y O) O))
             (sym_eq_minus_body_S a
                (fun y : nat -> nat => le (S a) (plus (y O) O))
                (sym_eq_match_nat_type_O nat (S a) 
                   (fun q : nat => minus a q)
                   (fun y : nat => le (S a) (plus y O)) 
                   (le_plus_n_r O (S a))))))
       (fun n0 : nat =>
        sym_eq_minus (S a)
          (fun y : nat -> nat => le (S a) (plus (y (S n0)) (S n0)))
          (sym_eq_filter_nat_type_S (nat -> nat) minus_body a
             (fun y : nat -> nat => le (S a) (plus (y (S n0)) (S n0)))
             (sym_eq_minus_body_S a
                (fun y : nat -> nat => le (S a) (plus (y (S n0)) (S n0)))
                (sym_eq_match_nat_type_S nat (S a) 
                   (fun q : nat => minus a q) n0
                   (fun y : nat => le (S a) (plus y (S n0)))
                   (eq_coerc (le (S a) (S (plus (minus a n0) n0)))
                      (le (S a) (plus (minus a n0) (S n0)))
                      (le_S_S a (plus (minus a n0) n0) (Hind n0))
                      (rewrite_r nat (plus (minus a n0) (S n0))
                         (fun __ : nat =>
                          eq Prop (le (S a) __)
                            (le (S a) (plus (minus a n0) (S n0))))
                         (refl Prop (le (S a) (plus (minus a n0) (S n0))))
                         (S (plus (minus a n0) n0))
                         (plus_n_Sm (minus a n0) n0))))))) m) n.
Definition le_plus_to_minus_r :
  forall a b c : nat, le (plus a b) c -> le a (minus c b) :=
  fun (a b c : nat) (H : le (plus a b) c) =>
  le_plus_to_le_r b a (minus c b)
    (transitive_le (plus a b) c (plus (minus c b) b) H
       (le_plus_minus_m_m c b)).
Definition lt_to_le : forall x y : nat, lt x y -> le x y :=
  fun (x y : nat) (auto : lt x y) =>
  le_plus_b (S O) x y
    (eq_coerc (le (S x) y) (le (plus x (S O)) y) auto
       (rewrite_r nat (plus x (S O))
          (fun __ : nat => eq Prop (le __ y) (le (plus x (S O)) y))
          (refl Prop (le (plus x (S O)) y)) (S x)
          (rewrite_r nat (plus x O)
             (fun __ : nat => eq nat (S __) (plus x (S O))) 
             (plus_n_Sm x O) x (plus_n_O x)))).
Definition transitive_lt : transitive nat lt :=
  fun (a b c : nat) (ltab : lt a b) (ltbc : lt b c) =>
  le_ind (S b) (fun x_417 : nat => lt a x_417) (le_S (S a) b ltab)
    (fun (m : nat) (_x_419 : le (S b) m) (_x_421 : lt a m) =>
     le_S (S a) m _x_421) c ltbc.
Definition lt_to_le_to_lt : forall n m p : nat, lt n m -> le m p -> lt n p :=
  fun (n m p : nat) (H : lt n m) (H1 : le m p) =>
  le_ind m (fun x_417 : nat => lt n x_417) H
    (fun (m0 : nat) (_x_419 : le m m0) (_x_421 : lt n m0) =>
     transitive_lt n m0 (S m0) _x_421
       (eq_coerc (le (S m0) (plus O (S m0))) (le (S m0) (S m0))
          (le_plus_n O (S m0))
          (rewrite_l nat (S m0)
             (fun __ : nat => eq Prop (le (S m0) __) (le (S m0) (S m0)))
             (refl Prop (le (S m0) (S m0))) (plus O (S m0)) 
             (plus_O_n (S m0))))) p H1.
Definition le_to_lt_to_lt : forall n m p : nat, le n m -> lt m p -> lt n p :=
  fun (n m p : nat) (H : le n m) =>
  le_ind n (fun x_417 : nat => lt x_417 p -> lt n p)
    (fun auto : lt n p => auto)
    (fun (m0 : nat) (_x_419 : le n m0) (_x_421 : lt m0 p -> lt n p)
       (auto : lt (S m0) p) =>
     _x_421
       (transitive_lt m0 (S m0) p
          (eq_coerc (le (S m0) (plus O (S m0))) (le (S m0) (S m0))
             (le_plus_n O (S m0))
             (rewrite_l nat (S m0)
                (fun __ : nat => eq Prop (le (S m0) __) (le (S m0) (S m0)))
                (refl Prop (le (S m0) (S m0))) (plus O (S m0))
                (plus_O_n (S m0)))) auto)) m H.
Definition lt_S_to_lt : forall n m : nat, lt (S n) m -> lt n m :=
  fun (n m : nat) (auto : lt (S n) m) =>
  transitive_lt n (S n) m
    (eq_coerc (le (S n) (plus O (S n))) (le (S n) (S n)) 
       (le_plus_n O (S n))
       (rewrite_l nat (S n)
          (fun __ : nat => eq Prop (le (S n) __) (le (S n) (S n)))
          (refl Prop (le (S n) (S n))) (plus O (S n)) 
          (plus_O_n (S n)))) auto.
Definition ltn_to_ltO : forall n m : nat, lt n m -> lt O m :=
  fun (n m : nat) (auto : lt n m) =>
  lt_to_le_to_lt O (S n) m
    (eq_coerc (le (S O) (plus n (S O))) (le (S O) (S n)) 
       (le_plus_n n (S O))
       (rewrite_l nat (S n)
          (fun __ : nat => eq Prop (le (S O) __) (le (S O) (S n)))
          (refl Prop (le (S O) (S n))) (plus n (S O))
          (rewrite_r nat (plus n O)
             (fun __ : nat => eq nat (S __) (plus n (S O))) 
             (plus_n_Sm n O) n (plus_n_O n)))) auto.
Definition lt_O_S : forall n : nat, lt O (S n) :=
  fun n : nat =>
  ltn_to_ltO n (S n)
    (eq_coerc (le (S n) (plus O (S n))) (le (S n) (S n)) 
       (le_plus_n O (S n))
       (rewrite_l nat (S n)
          (fun __ : nat => eq Prop (le (S n) __) (le (S n) (S n)))
          (refl Prop (le (S n) (S n))) (plus O (S n)) 
          (plus_O_n (S n)))).
Definition monotonic_lt_plus_r :
  forall n : nat, monotonic nat lt (fun m : nat => plus n m) :=
  fun (n x y : nat) (auto : lt x y) =>
  eq_coerc (le (plus n (S x)) (plus n y)) (le (S (plus n x)) (plus n y))
    (monotonic_le_plus_r n (S x) y auto)
    (rewrite_r nat (plus n (S x))
       (fun __ : nat =>
        eq Prop (le (plus n (S x)) (plus n y)) (le __ (plus n y)))
       (refl Prop (le (plus n (S x)) (plus n y))) 
       (S (plus n x)) (plus_n_Sm n x)).
Definition monotonic_lt_plus_l :
  forall n : nat, monotonic nat lt (fun m : nat => plus m n) :=
  fun (n x y : nat) (auto : lt x y) =>
  eq_coerc (le (plus n (S x)) (plus n y)) (le (S (plus x n)) (plus y n))
    (monotonic_le_plus_r n (S x) y auto)
    (rewrite_r nat (plus n x)
       (fun __ : nat =>
        eq Prop (le (plus n (S x)) (plus n y)) (le (S __) (plus y n)))
       (rewrite_r nat (plus n (S x))
          (fun __ : nat =>
           eq Prop (le (plus n (S x)) (plus n y)) (le __ (plus y n)))
          (rewrite_r nat (plus n y)
             (fun __ : nat =>
              eq Prop (le (plus n (S x)) (plus n y)) (le (plus n (S x)) __))
             (refl Prop (le (plus n (S x)) (plus n y))) 
             (plus y n) (commutative_plus y n)) (S (plus n x))
          (plus_n_Sm n x)) (plus x n) (commutative_plus x n)).
Definition monotonic_lt_times_r :
  forall c : nat, lt O c -> monotonic nat lt (fun t : nat => times c t) :=
  fun (c : nat) (posc : lt O c) (n m : nat) (ltnm : lt n m) =>
  le_ind (S n) (fun x_417 : nat => lt (times c n) (times c x_417))
    (eq_coerc (le (S (plus O (times c n))) (plus c (times c n)))
       (le (S (times c n)) (times c (S n)))
       (monotonic_lt_plus_l (times c n) O c posc)
       (rewrite_r nat (plus O (S (times c n)))
          (fun __ : nat =>
           eq Prop (le __ (plus c (times c n)))
             (le (S (times c n)) (times c (S n))))
          (rewrite_l nat (plus c (times c n))
             (fun __ : nat =>
              eq Prop (le (plus O (S (times c n))) (plus c (times c n)))
                (le (S (times c n)) __))
             (rewrite_l nat (S (times c n))
                (fun __ : nat =>
                 eq Prop (le __ (plus c (times c n)))
                   (le (S (times c n)) (plus c (times c n))))
                (refl Prop (le (S (times c n)) (plus c (times c n))))
                (plus O (S (times c n))) (plus_O_n (S (times c n))))
             (times c (S n)) (times_n_Sm c n)) (S (plus O (times c n)))
          (plus_n_Sm O (times c n))))
    (fun (a : nat) (__ : le (S n) a) (lt1 : le (S (times c n)) (times c a))
     =>
     transitive_le (S (times c n)) (times c a) (times c (S a)) lt1
       (eq_coerc (le (times c a) (plus (times c a) c))
          (le (times c a) (times c (S a))) (le_plus_n_r c (times c a))
          (rewrite_l nat (plus c (times c a))
             (fun __1 : nat =>
              eq Prop (le (times c a) (plus (times c a) c))
                (le (times c a) __1))
             (rewrite_r nat (plus c (times c a))
                (fun __1 : nat =>
                 eq Prop (le (times c a) __1)
                   (le (times c a) (plus c (times c a))))
                (refl Prop (le (times c a) (plus c (times c a))))
                (plus (times c a) c) (commutative_plus (times c a) c))
             (times c (S a)) (times_n_Sm c a)))) m ltnm.
Definition monotonic_lt_times_l :
  forall c : nat, lt O c -> monotonic nat lt (fun t : nat => times t c) :=
  fun (c : nat) (auto : lt O c) (x y : nat) (auto' : lt x y) =>
  eq_coerc (le (S (times c x)) (times c y)) (le (S (times x c)) (times y c))
    (monotonic_lt_times_r c auto x y auto')
    (rewrite_r nat (times c x)
       (fun __ : nat =>
        eq Prop (le (S (times c x)) (times c y)) (le (S __) (times y c)))
       (rewrite_r nat (times c y)
          (fun __ : nat =>
           eq Prop (le (S (times c x)) (times c y)) (le (S (times c x)) __))
          (refl Prop (le (S (times c x)) (times c y))) 
          (times y c) (commutative_times y c)) (times x c)
       (commutative_times x c)).
Definition lt_to_le_to_lt_times :
  forall n m p q : nat,
  lt n m -> le p q -> lt O q -> lt (times n p) (times m q) :=
  fun (n m p q : nat) (ltnm : lt n m) (lepq : le p q) (posq : lt O q) =>
  le_to_lt_to_lt (times n p) (times n q) (times m q)
    (monotonic_le_times_r n p q lepq) (monotonic_lt_times_l q posq n m ltnm).
Definition lt_times :
  forall n m p q : nat, lt n m -> lt p q -> lt (times n p) (times m q) :=
  fun (n m p q : nat) (ltnm : lt n m) (ltpq : lt p q) =>
  lt_to_le_to_lt_times n m p q ltnm (lt_to_le p q ltpq) (ltn_to_ltO p q ltpq).
Definition lt_plus_to_minus_r :
  forall a b c : nat, lt (plus a b) c -> lt a (minus c b) :=
  fun (a b c : nat) (H : lt (plus a b) c) =>
  le_plus_to_minus_r (S a) b c
    (sym_eq_plus (S a) (fun y : nat -> nat => le (y b) c)
       (sym_eq_filter_nat_type_S (nat -> nat) plus_body a
          (fun y : nat -> nat => le (y b) c)
          (sym_eq_plus_body_S a (fun y : nat -> nat => le (y b) c) H))).
Definition lt_plus_Sn_r : forall a x n : nat, lt a (plus (plus a x) (S n)) :=
  fun a x n : nat =>
  eq_coerc (le (S a) (S (plus (plus a x) n)))
    (le (S a) (plus (plus a x) (S n)))
    (le_S_S a (plus (plus a x) n)
       (eq_coerc (le a (plus a (plus x n))) (le a (plus (plus a x) n))
          (le_plus_n_r (plus x n) a)
          (rewrite_r nat (plus n (plus a x))
             (fun __ : nat => eq Prop (le a (plus a (plus x n))) (le a __))
             (rewrite_r nat (plus a (plus n x))
                (fun __ : nat => eq Prop (le a (plus a (plus x n))) (le a __))
                (rewrite_r nat (plus x n)
                   (fun __ : nat =>
                    eq Prop (le a (plus a (plus x n))) (le a (plus a __)))
                   (refl Prop (le a (plus a (plus x n)))) 
                   (plus n x) (commutative_plus n x)) 
                (plus n (plus a x))
                (rewrite_l nat (plus (plus a n) x)
                   (fun __ : nat => eq nat (plus n (plus a x)) __)
                   (assoc_plus1 x a n) (plus a (plus n x))
                   (associative_plus a n x))) (plus (plus a x) n)
             (commutative_plus (plus a x) n))))
    (rewrite_r nat (plus a (plus x (S n)))
       (fun __ : nat =>
        eq Prop (le (S a) (S (plus (plus a x) n))) (le (S a) __))
       (rewrite_r nat (plus (plus a x) (S n))
          (fun __ : nat =>
           eq Prop (le (S a) __) (le (S a) (plus a (plus x (S n)))))
          (rewrite_r nat (plus a (plus x (S n)))
             (fun __ : nat =>
              eq Prop (le (S a) __) (le (S a) (plus a (plus x (S n)))))
             (refl Prop (le (S a) (plus a (plus x (S n)))))
             (plus (plus a x) (S n)) (associative_plus a x (S n)))
          (S (plus (plus a x) n)) (plus_n_Sm (plus a x) n))
       (plus (plus a x) (S n)) (associative_plus a x (S n))).
Definition not_le_Sn_O : forall n : nat, Not (le (S n) O) :=
  fun (n : nat) (Hlen0 : le (S n) O) =>
  eq_match_nat_type_O Prop False (fun p : nat => True) 
    (fun y : Prop => y) (lt_to_not_zero n O Hlen0).
Definition not_le_to_not_le_S_S :
  forall n m : nat, Not (le n m) -> Not (le (S n) (S m)) :=
  fun (n m : nat) (auto : Not (le n m)) =>
  not_to_not (le (S n) (S m)) (le n m)
    (fun auto' : le (S n) (S m) =>
     eq_coerc (le (pred (S n)) (pred (S m))) (le n m)
       (monotonic_pred (S n) (S m) auto')
       (rewrite_l nat n
          (fun __ : nat => eq Prop (le __ (pred (S m))) (le n m))
          (rewrite_l nat m (fun __ : nat => eq Prop (le n __) (le n m))
             (refl Prop (le n m)) (pred (S m)) (pred_Sn m)) 
          (pred (S n)) (pred_Sn n))) auto.
Definition not_le_S_S_to_not_le :
  forall n m : nat, Not (le (S n) (S m)) -> Not (le n m) :=
  fun (n m : nat) (auto : Not (le (S n) (S m))) =>
  not_to_not (le n m) (le (S n) (S m))
    (fun auto' : le n m => le_S_S n m auto') auto.
Definition not_le_Sn_n : forall n : nat, Not (le (S n) n) :=
  fun n : nat =>
  nat_ind (fun _x_365 : nat => Not (le (S _x_365) _x_365)) 
    (not_le_Sn_O O)
    (fun (x_366 : nat) (_x_368 : Not (le (S x_366) x_366)) =>
     not_le_to_not_le_S_S (S x_366) x_366 _x_368) n.
Definition lt_to_not_le : forall n m : nat, lt n m -> Not (le m n) :=
  fun (n m : nat) (Hltnm : lt n m) =>
  le_ind (S n) (fun x_417 : nat => Not (le x_417 n)) 
    (not_le_Sn_n n)
    (fun (m0 : nat) (_x_419 : le (S n) m0) (_x_421 : Not (le m0 n)) =>
     not_to_not (le (S m0) n) (le m0 n)
       (fun auto : le (S m0) n => lt_to_le m0 n auto) _x_421) m Hltnm.
Definition not_le_to_lt : forall n m : nat, Not (le n m) -> lt m n :=
  nat_elim2 (fun __ _0 : nat => Not (le __ _0) -> lt _0 __)
    (fun (n : nat) (abs : Not (le O n)) =>
     falsity (lt n O)
       (absurd (le O n)
          (eq_coerc (le O (plus n O)) (le O n) (le_plus_n n O)
             (rewrite_l nat n (fun __ : nat => eq Prop (le O __) (le O n))
                (refl Prop (le O n)) (plus n O) (plus_n_O n))) abs))
    (fun (n : nat) (auto : Not (le (S n) O)) => lt_O_S n)
    (fun (n m : nat) (Hind : Not (le n m) -> lt m n)
       (HnotleSS : Not (le (S n) (S m))) =>
     le_S_S (S m) n (Hind (not_le_S_S_to_not_le n m HnotleSS))).
Definition not_lt_to_le : forall n m : nat, Not (lt n m) -> le m n :=
  fun (n m : nat) (H : Not (lt n m)) =>
  le_S_S_to_le m n
    (not_le_to_lt (S n) m
       (not_to_not (le (S n) m) (lt n m) (fun auto : le (S n) m => auto) H)).
Definition le_to_not_lt : forall n m : nat, le n m -> Not (lt m n) :=
  fun (n m : nat) (H : le n m) =>
  lt_to_not_le n (S m)
    (le_to_lt_to_lt n m (S m) H
       (eq_coerc (le (S m) (plus O (S m))) (le (S m) (S m))
          (le_plus_n O (S m))
          (rewrite_l nat (S m)
             (fun __ : nat => eq Prop (le (S m) __) (le (S m) (S m)))
             (refl Prop (le (S m) (S m))) (plus O (S m)) 
             (plus_O_n (S m))))).
Definition decidable_le : forall n m : nat, decidable (le n m) :=
  nat_elim2 (fun __ _0 : nat => decidable (le __ _0))
    (fun (n : nat) (z : Prop) (l : le O n -> z) (r : Not (le O n) -> z) =>
     l (le_O_n n))
    (fun (n : nat) (z : Prop) (l : le (S n) O -> z)
       (r : Not (le (S n) O) -> z) => r (not_le_Sn_O n))
    (fun (n m : nat) (_clearme : decidable (le n m)) =>
     match_Or_prop (le n m) (Not (le n m)) (decidable (le (S n) (S m)))
       (fun (auto : le n m) (z : Prop) (l : le (S n) (S m) -> z)
          (r : Not (le (S n) (S m)) -> z) => l (le_S_S n m auto))
       (fun (auto : Not (le n m)) (z : Prop) (l : le (S n) (S m) -> z)
          (r : Not (le (S n) (S m)) -> z) =>
        r (not_le_to_not_le_S_S n m auto)) _clearme).
Definition decidable_lt : forall n m : nat, decidable (lt n m) :=
  fun n m : nat => decidable_le (S n) m.
Definition le_to_or_lt_eq :
  forall n m : nat, le n m -> Or (lt n m) (eq nat n m) :=
  fun (n m : nat) (lenm : le n m) =>
  le_ind n (fun x_417 : nat => Or (lt n x_417) (eq nat n x_417))
    (RC_reflexive nat lt n)
    (fun (m0 : nat) (_x_419 : le n m0) (_x_421 : Or (lt n m0) (eq nat n m0))
       (z : Prop) (l : lt n (S m0) -> z) (r : eq nat n (S m0) -> z) =>
     l
       (le_to_lt_to_lt n m0 (S m0) _x_419
          (eq_coerc (le (S m0) (plus O (S m0))) (le (S m0) (S m0))
             (le_plus_n O (S m0))
             (rewrite_l nat (S m0)
                (fun __ : nat => eq Prop (le (S m0) __) (le (S m0) (S m0)))
                (refl Prop (le (S m0) (S m0))) (plus O (S m0))
                (plus_O_n (S m0)))))) m lenm.
Definition lt_O_n_elim :
  forall n : nat,
  lt O n -> forall P : nat -> Prop, (forall m : nat, P (S m)) -> P n :=
  fun n : nat =>
  nat_ind
    (fun _x_365 : nat =>
     lt O _x_365 ->
     forall P : nat -> Prop, (forall m : nat, P (S m)) -> P _x_365)
    (fun abs : lt O O =>
     falsity (forall P : nat -> Prop, (forall m : nat, P (S m)) -> P O)
       (absurd (le (S O) O) abs (not_le_Sn_O O)))
    (fun (x_366 : nat)
       (_x_368 : lt O x_366 ->
                 forall P : nat -> Prop, (forall m : nat, P (S m)) -> P x_366)
       (auto : lt O (S x_366)) (P : nat -> Prop)
       (auto' : forall m : nat, P (S m)) => auto' x_366) n.
Definition le_n_O_elim :
  forall n : nat, le n O -> forall P : nat -> Prop, P O -> P n :=
  fun n : nat =>
  match_nat_prop
    (fun __ : nat => le __ O -> forall P : nat -> Prop, P O -> P __)
    (fun (auto : le O O) (P : nat -> Prop) (auto' : P O) => auto')
    (fun (a : nat) (abs : le (S a) O) =>
     falsity (forall P : nat -> Prop, P O -> P (S a))
       (absurd (le (S a) O) abs (not_le_Sn_O a))) n.
Definition lt_to_not_eq : forall n m : nat, lt n m -> Not (eq nat n m) :=
  fun (n m : nat) (H : lt n m) =>
  not_to_not (eq nat n m) False
    (fun auto : eq nat n m =>
     absurd (le (S n) n)
       (eq_coerc (le (S n) m) (le (S n) n) H
          (rewrite_l nat n
             (fun __ : nat => eq Prop (le (S n) __) (le (S n) n))
             (refl Prop (le (S n) n)) m auto)) (not_le_Sn_n n))
    (fun auto : False => auto).
Definition le_n_O_to_eq : forall n : nat, le n O -> eq nat O n :=
  fun n : nat =>
  match_nat_prop (fun __ : nat => le __ O -> eq nat O __)
    (fun auto : le O O => refl nat O)
    (fun (a : nat) (abs : le (S a) O) =>
     falsity (eq nat O (S a)) (absurd (le (S a) O) abs (not_le_Sn_O a))) n.
Definition le_to_le_to_eq :
  forall n m : nat, le n m -> le m n -> eq nat n m :=
  nat_elim2 (fun __ _0 : nat => le __ _0 -> le _0 __ -> eq nat __ _0)
    (fun (n : nat) (auto : le O n) (auto' : le n O) =>
     sym_eq nat n O
       (sym_eq nat O n
          (eq_coerc (eq nat O n) (eq nat O n) (le_n_O_to_eq n auto')
             (refl Prop (eq nat O n)))))
    (fun (n : nat) (auto : le (S n) O) (auto' : le O (S n)) =>
     sym_eq nat O (S n) (le_n_O_to_eq (S n) auto))
    (fun (n m : nat) (auto : le n m -> le m n -> eq nat n m)
       (auto' : le (S n) (S m)) (auto'' : le (S m) (S n)) =>
     eq_f nat nat S n m
       (auto
          (eq_coerc (le (pred (S n)) (pred (S m))) 
             (le n m) (monotonic_pred (S n) (S m) auto')
             (rewrite_l nat n
                (fun __ : nat => eq Prop (le __ (pred (S m))) (le n m))
                (rewrite_l nat m (fun __ : nat => eq Prop (le n __) (le n m))
                   (refl Prop (le n m)) (pred (S m)) 
                   (pred_Sn m)) (pred (S n)) (pred_Sn n)))
          (eq_coerc (le (pred (S m)) (pred (S n))) 
             (le m n) (monotonic_pred (S m) (S n) auto'')
             (rewrite_l nat m
                (fun __ : nat => eq Prop (le __ (pred (S n))) (le m n))
                (rewrite_l nat n (fun __ : nat => eq Prop (le m __) (le m n))
                   (refl Prop (le m n)) (pred (S n)) 
                   (pred_Sn n)) (pred (S m)) (pred_Sn m))))).
Definition plus_minus :
  forall m n p : nat,
  le m n -> eq nat (plus (minus n m) p) (minus (plus n p) m) :=
  nat_elim2
    (fun __ _0 : nat =>
     forall p : nat,
     le __ _0 -> eq nat (plus (minus _0 __) p) (minus (plus _0 p) __))
    (fun (n p : nat) (auto : le O n) =>
     rewrite_l nat n
       (fun __ : nat => eq nat (plus __ p) (minus (plus n p) O))
       (rewrite_l nat (plus n p) (fun __ : nat => eq nat (plus n p) __)
          (refl nat (plus n p)) (minus (plus n p) O) 
          (minus_n_O (plus n p))) (minus n O) (minus_n_O n))
    (fun (n p : nat) (abs : le (S n) O) =>
     falsity (eq nat (plus (minus O (S n)) p) (minus (plus O p) (S n)))
       (absurd (le (S n) O) abs (not_le_Sn_O n)))
    (fun n m : nat =>
     sym_eq_minus (S m)
       (fun y : nat -> nat =>
        (forall p : nat,
         le n m -> eq nat (plus (minus m n) p) (minus (plus m p) n)) ->
        forall p : nat,
        le (S n) (S m) ->
        eq nat (plus (y (S n)) p) (minus (plus (S m) p) (S n)))
       (sym_eq_filter_nat_type_S (nat -> nat) minus_body m
          (fun y : nat -> nat =>
           (forall p : nat,
            le n m -> eq nat (plus (minus m n) p) (minus (plus m p) n)) ->
           forall p : nat,
           le (S n) (S m) ->
           eq nat (plus (y (S n)) p) (minus (plus (S m) p) (S n)))
          (sym_eq_minus_body_S m
             (fun y : nat -> nat =>
              (forall p : nat,
               le n m -> eq nat (plus (minus m n) p) (minus (plus m p) n)) ->
              forall p : nat,
              le (S n) (S m) ->
              eq nat (plus (y (S n)) p) (minus (plus (S m) p) (S n)))
             (fun
                (auto : forall p : nat,
                        le n m ->
                        eq nat (plus (minus m n) p) (minus (plus m p) n))
                (p : nat) =>
              sym_eq_match_nat_type_S nat (S m) (fun q : nat => minus m q) n
                (fun y : nat =>
                 le (S n) (S m) ->
                 eq nat (plus y p) (minus (plus (S m) p) (S n)))
                (sym_eq_minus (plus (S m) p)
                   (fun y : nat -> nat =>
                    le (S n) (S m) -> eq nat (plus (minus m n) p) (y (S n)))
                   (sym_eq_plus (S m)
                      (fun y : nat -> nat =>
                       le (S n) (S m) ->
                       eq nat (plus (minus m n) p)
                         (filter_nat_type (nat -> nat) minus_body (y p) (S n)))
                      (sym_eq_filter_nat_type_S (nat -> nat) plus_body m
                         (fun y : nat -> nat =>
                          le (S n) (S m) ->
                          eq nat (plus (minus m n) p)
                            (filter_nat_type (nat -> nat) minus_body 
                               (y p) (S n)))
                         (sym_eq_plus_body_S m
                            (fun y : nat -> nat =>
                             le (S n) (S m) ->
                             eq nat (plus (minus m n) p)
                               (filter_nat_type (nat -> nat) minus_body 
                                  (y p) (S n)))
                            (sym_eq_filter_nat_type_S 
                               (nat -> nat) minus_body 
                               (plus m p)
                               (fun y : nat -> nat =>
                                le (S n) (S m) ->
                                eq nat (plus (minus m n) p) (y (S n)))
                               (eq_plus_body_S m
                                  (fun y : nat -> nat =>
                                   le (S n) (S m) ->
                                   eq nat (plus (minus m n) p)
                                     (minus_body (y p) (S n)))
                                  (eq_filter_nat_type_S 
                                     (nat -> nat) plus_body m
                                     (fun y : nat -> nat =>
                                      le (S n) (S m) ->
                                      eq nat (plus (minus m n) p)
                                        (minus_body (y p) (S n)))
                                     (eq_plus (S m)
                                        (fun y : nat -> nat =>
                                         le (S n) (S m) ->
                                         eq nat (plus (minus m n) p)
                                           (minus_body (y p) (S n)))
                                        (sym_eq_plus 
                                           (S m)
                                           (fun y : nat -> nat =>
                                            le (S n) (S m) ->
                                            eq nat 
                                              (plus (minus m n) p)
                                              (minus_body (y p) (S n)))
                                           (sym_eq_filter_nat_type_S
                                              (nat -> nat) plus_body m
                                              (fun y : nat -> nat =>
                                               le (S n) (S m) ->
                                               eq nat 
                                                 (plus (minus m n) p)
                                                 (minus_body (y p) (S n)))
                                              (sym_eq_plus_body_S m
                                                 (fun y : nat -> nat =>
                                                 le (S n) (S m) ->
                                                 eq nat 
                                                 (plus (minus m n) p)
                                                 (minus_body (y p) (S n)))
                                                 (sym_eq_minus_body_S
                                                 (plus m p)
                                                 (fun y : nat -> nat =>
                                                 le (S n) (S m) ->
                                                 eq nat 
                                                 (plus (minus m n) p)
                                                 (y (S n)))
                                                 (sym_eq_match_nat_type_S nat
                                                 (S (plus m p))
                                                 (fun q : nat =>
                                                 minus (plus m p) q) n
                                                 (fun y : nat =>
                                                 le (S n) (S m) ->
                                                 eq nat 
                                                 (plus (minus m n) p) y)
                                                 (fun auto' : le (S n) (S m)
                                                 =>
                                                 auto p
                                                 (eq_coerc
                                                 (le 
                                                 (pred (S n)) 
                                                 (pred (S m))) 
                                                 (le n m)
                                                 (monotonic_pred 
                                                 (S n) 
                                                 (S m) auto')
                                                 (rewrite_l nat n
                                                 (fun __ : nat =>
                                                 eq Prop 
                                                 (le __ (pred (S m)))
                                                 (le n m))
                                                 (rewrite_l nat m
                                                 (fun __ : nat =>
                                                 eq Prop (le n __) (le n m))
                                                 (refl Prop (le n m))
                                                 (pred (S m)) 
                                                 (pred_Sn m)) 
                                                 (pred (S n)) 
                                                 (pred_Sn n))))))))))))))))))))).
Definition minus_plus_m_m :
  forall n m : nat, eq nat n (minus (plus n m) m) :=
  fun n m : nat =>
  eq_coerc (eq nat (plus (minus m m) n) (minus (plus m n) m))
    (eq nat n (minus (plus n m) m)) (plus_minus m m n (le_n m))
    (rewrite_l nat O
       (fun __ : nat =>
        eq Prop (eq nat (plus __ n) (minus (plus m n) m))
          (eq nat n (minus (plus n m) m)))
       (rewrite_l nat n
          (fun __ : nat =>
           eq Prop (eq nat __ (minus (plus m n) m))
             (eq nat n (minus (plus n m) m)))
          (rewrite_r nat (plus n m)
             (fun __ : nat =>
              eq Prop (eq nat n (minus __ m)) (eq nat n (minus (plus n m) m)))
             (refl Prop (eq nat n (minus (plus n m) m))) 
             (plus m n) (commutative_plus m n)) (plus O n) 
          (plus_O_n n)) (minus m m) (minus_n_n m)).
Definition plus_minus_m_m :
  forall n m : nat, le m n -> eq nat n (plus (minus n m) m) :=
  fun (n m : nat) (lemn : le m n) =>
  sym_eq nat (plus (minus n m) m) n
    (eq_coerc (eq nat (plus (minus n m) m) (minus (plus n m) m))
       (eq nat (plus (minus n m) m) n) (plus_minus m n m lemn)
       (rewrite_r nat (plus m (minus n m))
          (fun __ : nat =>
           eq Prop (eq nat (plus (minus n m) m) (minus (plus n m) m))
             (eq nat __ n))
          (rewrite_r nat (plus m (minus n m))
             (fun __ : nat =>
              eq Prop (eq nat __ (minus (plus n m) m))
                (eq nat (plus m (minus n m)) n))
             (rewrite_l nat n
                (fun __ : nat =>
                 eq Prop (eq nat (plus m (minus n m)) __)
                   (eq nat (plus m (minus n m)) n))
                (refl Prop (eq nat (plus m (minus n m)) n))
                (minus (plus n m) m) (minus_plus_m_m n m))
             (plus (minus n m) m) (commutative_plus (minus n m) m))
          (plus (minus n m) m) (commutative_plus (minus n m) m))).
Definition minus_to_plus :
  forall n m p : nat, le m n -> eq nat (minus n m) p -> eq nat n (plus m p) :=
  fun (n m p : nat) (lemn : le m n) (eqp : eq nat (minus n m) p) =>
  eq_coerc (eq nat n (plus (minus n m) m)) (eq nat n (plus m p))
    (plus_minus_m_m n m lemn)
    (rewrite_r nat (plus m (minus n m))
       (fun __ : nat => eq Prop (eq nat n __) (eq nat n (plus m p)))
       (rewrite_r nat p
          (fun __ : nat =>
           eq Prop (eq nat n (plus m __)) (eq nat n (plus m p)))
          (refl Prop (eq nat n (plus m p))) (minus n m) eqp)
       (plus (minus n m) m) (commutative_plus (minus n m) m)).
Definition plus_to_minus :
  forall n m p : nat, eq nat n (plus m p) -> eq nat (minus n m) p :=
  fun (n m p : nat) (eqp : eq nat n (plus m p)) =>
  sym_eq nat p (minus n m)
    (eq_coerc (eq nat p (minus (plus p m) m)) (eq nat p (minus n m))
       (minus_plus_m_m p m)
       (rewrite_r nat (plus m p)
          (fun __ : nat =>
           eq Prop (eq nat p (minus __ m)) (eq nat p (minus n m)))
          (rewrite_l nat n
             (fun __ : nat =>
              eq Prop (eq nat p (minus __ m)) (eq nat p (minus n m)))
             (refl Prop (eq nat p (minus n m))) (plus m p) eqp) 
          (plus p m) (commutative_plus p m))).
Definition monotonic_le_minus_l :
  forall p q n : nat, le q p -> le (minus q n) (minus p n) :=
  nat_elim2
    (fun __ _0 : nat =>
     forall n : nat, le _0 __ -> le (minus _0 n) (minus __ n))
    (fun (p q : nat) (lePO : le p O) =>
     le_n_O_elim p lePO (fun __ : nat => le (minus __ q) (minus O q))
       (le_n (minus O q)))
    (fun p q : nat =>
     sym_eq_minus (S p)
       (fun y : nat -> nat => le O (S p) -> le (minus O q) (y q))
       (sym_eq_filter_nat_type_S (nat -> nat) minus_body p
          (fun y : nat -> nat => le O (S p) -> le (minus O q) (y q))
          (sym_eq_minus_body_S p
             (fun y : nat -> nat => le O (S p) -> le (minus O q) (y q))
             (eq_plus_body_O
                (fun y : nat -> nat =>
                 le O (S p) ->
                 le (minus O q)
                   (y
                      (match_nat_type nat (S p) (fun q0 : nat => minus p q0)
                         q)))
                (eq_filter_nat_type_O (nat -> nat) plus_body
                   (fun y : nat -> nat =>
                    le O (S p) ->
                    le (minus O q)
                      (y
                         (match_nat_type nat (S p)
                            (fun q0 : nat => minus p q0) q)))
                   (eq_plus O
                      (fun y : nat -> nat =>
                       le O (S p) ->
                       le (minus O q)
                         (y
                            (match_nat_type nat (S p)
                               (fun q0 : nat => minus p q0) q)))
                      (eq_minus_body_O
                         (fun y : nat -> nat =>
                          le O (S p) ->
                          le (minus O q)
                            (plus
                               (y
                                  (match_nat_type nat 
                                     (S p) (fun q0 : nat => minus p q0) q))
                               (match_nat_type nat 
                                  (S p) (fun q0 : nat => minus p q0) q)))
                         (eq_filter_nat_type_O (nat -> nat) minus_body
                            (fun y : nat -> nat =>
                             le O (S p) ->
                             le (minus O q)
                               (plus
                                  (y
                                     (match_nat_type nat 
                                        (S p) (fun q0 : nat => minus p q0) q))
                                  (match_nat_type nat 
                                     (S p) (fun q0 : nat => minus p q0) q)))
                            (eq_minus O
                               (fun y : nat -> nat =>
                                le O (S p) ->
                                le (minus O q)
                                  (plus
                                     (y
                                        (match_nat_type nat 
                                           (S p) (fun q0 : nat => minus p q0)
                                           q))
                                     (match_nat_type nat 
                                        (S p) (fun q0 : nat => minus p q0) q)))
                               (eq_minus_body_O
                                  (fun y : nat -> nat =>
                                   le O (S p) ->
                                   le (minus O q)
                                     (plus
                                        (minus (y q)
                                           (match_nat_type nat 
                                              (S p)
                                              (fun q0 : nat => minus p q0) q))
                                        (match_nat_type nat 
                                           (S p) (fun q0 : nat => minus p q0)
                                           q)))
                                  (eq_filter_nat_type_O 
                                     (nat -> nat) minus_body
                                     (fun y : nat -> nat =>
                                      le O (S p) ->
                                      le (minus O q)
                                        (plus
                                           (minus 
                                              (y q)
                                              (match_nat_type nat 
                                                 (S p)
                                                 (fun q0 : nat => minus p q0)
                                                 q))
                                           (match_nat_type nat 
                                              (S p)
                                              (fun q0 : nat => minus p q0) q)))
                                     (eq_minus O
                                        (fun y : nat -> nat =>
                                         le O (S p) ->
                                         le (minus O q)
                                           (plus
                                              (minus 
                                                 (y q)
                                                 (match_nat_type nat 
                                                 (S p)
                                                 (fun q0 : nat => minus p q0)
                                                 q))
                                              (match_nat_type nat 
                                                 (S p)
                                                 (fun q0 : nat => minus p q0)
                                                 q)))
                                        (fun auto : le O (S p) =>
                                         le_plus_minus_m_m 
                                           (minus O q)
                                           (match_nat_type nat 
                                              (S p)
                                              (fun q0 : nat => minus p q0) q))))))))))))))
    (fun (p q : nat)
       (Hind : forall n0 : nat, le q p -> le (minus q n0) (minus p n0))
       (n : nat) =>
     match_nat_prop
       (fun __ : nat =>
        le (S q) (S p) -> le (minus (S q) __) (minus (S p) __))
       (sym_eq_minus (S q)
          (fun y : nat -> nat => le (S q) (S p) -> le (y O) (minus (S p) O))
          (sym_eq_filter_nat_type_S (nat -> nat) minus_body q
             (fun y : nat -> nat =>
              le (S q) (S p) -> le (y O) (minus (S p) O))
             (sym_eq_minus_body_S q
                (fun y : nat -> nat =>
                 le (S q) (S p) -> le (y O) (minus (S p) O))
                (sym_eq_match_nat_type_O nat (S q) 
                   (fun z : nat => minus q z)
                   (fun y : nat => le (S q) (S p) -> le y (minus (S p) O))
                   (sym_eq_minus (S p)
                      (fun y : nat -> nat => le (S q) (S p) -> le (S q) (y O))
                      (sym_eq_filter_nat_type_S (nat -> nat) minus_body p
                         (fun y : nat -> nat =>
                          le (S q) (S p) -> le (S q) (y O))
                         (sym_eq_minus_body_S p
                            (fun y : nat -> nat =>
                             le (S q) (S p) -> le (S q) (y O))
                            (sym_eq_match_nat_type_O nat 
                               (S p) (fun q0 : nat => minus p q0)
                               (fun y : nat => le (S q) (S p) -> le (S q) y)
                               (fun auto : le (S q) (S p) => auto)))))))))
       (sym_eq_minus (S q)
          (fun y : nat -> nat =>
           forall a : nat, le (S q) (S p) -> le (y (S a)) (minus (S p) (S a)))
          (sym_eq_filter_nat_type_S (nat -> nat) minus_body q
             (fun y : nat -> nat =>
              forall a : nat,
              le (S q) (S p) -> le (y (S a)) (minus (S p) (S a)))
             (sym_eq_minus_body_S q
                (fun y : nat -> nat =>
                 forall a : nat,
                 le (S q) (S p) -> le (y (S a)) (minus (S p) (S a)))
                (fun a : nat =>
                 sym_eq_match_nat_type_S nat (S q) 
                   (fun z : nat => minus q z) a
                   (fun y : nat => le (S q) (S p) -> le y (minus (S p) (S a)))
                   (sym_eq_minus (S p)
                      (fun y : nat -> nat =>
                       le (S q) (S p) -> le (minus q a) (y (S a)))
                      (sym_eq_filter_nat_type_S (nat -> nat) minus_body p
                         (fun y : nat -> nat =>
                          le (S q) (S p) -> le (minus q a) (y (S a)))
                         (sym_eq_minus_body_S p
                            (fun y : nat -> nat =>
                             le (S q) (S p) -> le (minus q a) (y (S a)))
                            (sym_eq_match_nat_type_S nat 
                               (S p) (fun q0 : nat => minus p q0) a
                               (fun y : nat =>
                                le (S q) (S p) -> le (minus q a) y)
                               (fun leSS : le (S q) (S p) =>
                                Hind a
                                  (eq_coerc (le (pred (S q)) (pred (S p)))
                                     (le q p)
                                     (monotonic_pred (S q) (S p) leSS)
                                     (rewrite_l nat q
                                        (fun __ : nat =>
                                         eq Prop (le __ (pred (S p)))
                                           (le q p))
                                        (rewrite_l nat p
                                           (fun __ : nat =>
                                            eq Prop (le q __) (le q p))
                                           (refl Prop (le q p)) 
                                           (pred (S p)) 
                                           (pred_Sn p)) 
                                        (pred (S q)) 
                                        (pred_Sn q)))))))))))) n).
Definition le_plus_to_minus :
  forall n m p : nat, le n (plus p m) -> le (minus n m) p :=
  fun (n m p : nat) (lep : le n (plus p m)) =>
  eq_coerc (le (minus n m) (minus (plus p m) m)) (le (minus n m) p)
    (monotonic_le_minus_l (plus p m) n m lep)
    (rewrite_l nat p
       (fun __ : nat => eq Prop (le (minus n m) __) (le (minus n m) p))
       (refl Prop (le (minus n m) p)) (minus (plus p m) m)
       (minus_plus_m_m p m)).
Definition monotonic_le_minus_r :
  forall p q n : nat, le q p -> le (minus n p) (minus n q) :=
  fun (p q n : nat) (lepq : le q p) =>
  le_plus_to_minus n p (minus n q)
    (transitive_le n (plus (minus n q) q) (plus (minus n q) p)
       (le_plus_minus_m_m n q) (monotonic_le_plus_r (minus n q) q p lepq)).
Definition minus_le : forall x y : nat, le (minus x y) x :=
  fun x y : nat =>
  eq_coerc (le (minus x y) (minus (plus x y) y)) (le (minus x y) x)
    (monotonic_le_minus_l (plus x y) x y (le_plus_n_r y x))
    (rewrite_l nat x
       (fun __ : nat => eq Prop (le (minus x y) __) (le (minus x y) x))
       (refl Prop (le (minus x y) x)) (minus (plus x y) y)
       (minus_plus_m_m x y)).
Definition not_eq_to_le_to_lt :
  forall n m : nat, Not (eq nat n m) -> le n m -> lt n m :=
  fun (n m : nat) (Hneq : Not (eq nat n m)) (Hle : le n m) =>
  match_Or_prop (lt n m) (eq nat n m) (lt n m) (fun auto : lt n m => auto)
    (fun Heq : eq nat n m =>
     not_le_to_lt m n
       (not_to_not (le m n) (eq nat n m)
          (fun auto : le m n =>
           rewrite_l nat n (fun __ : nat => eq nat n __) (refl nat n) m Heq)
          Hneq)) (le_to_or_lt_eq n m Hle).
Definition eq_minus_O : forall n m : nat, le n m -> eq nat (minus n m) O :=
  fun (n m : nat) (lenm : le n m) =>
  le_n_O_elim (minus n m)
    (eq_coerc (le (minus n m) (minus n n)) (le (minus n m) O)
       (monotonic_le_minus_r m n n lenm)
       (rewrite_l nat O
          (fun __ : nat => eq Prop (le (minus n m) __) (le (minus n m) O))
          (refl Prop (le (minus n m) O)) (minus n n) 
          (minus_n_n n))) (fun __ : nat => eq nat __ O) 
    (refl nat O).
Definition distributive_times_minus : distributive nat times minus :=
  fun a b c : nat =>
  match_Or_prop (lt b c) (Not (lt b c))
    (eq nat (times a (minus b c)) (minus (times a b) (times a c)))
    (fun Hbc : lt b c =>
     eq_ind_r nat O
       (fun x : nat => eq nat (times a x) (minus (times a b) (times a c)))
       (eq_ind_r nat O (fun x : nat => eq nat (times a O) x)
          (rewrite_l nat O (fun __ : nat => eq nat __ O) 
             (refl nat O) (times a O) (times_n_O a))
          (minus (times a b) (times a c))
          (eq_minus_O (times a b) (times a c)
             (monotonic_le_times_r a b c (lt_to_le b c Hbc)))) 
       (minus b c) (eq_minus_O b c (lt_to_le b c Hbc)))
    (fun Hbc : Not (lt b c) =>
     sym_eq nat (minus (times a b) (times a c)) (times a (minus b c))
       (eq_coerc
          (eq nat (minus (times a b) (times a c)) (times a (minus b c)))
          (eq nat (minus (times a b) (times a c)) (times a (minus b c)))
          (plus_to_minus (times a b) (times a c) (times a (minus b c))
             (eq_ind nat (times a (plus c (minus b c)))
                (fun x_1 : nat => eq nat (times a b) x_1)
                (eq_f nat nat (times a) b (plus c (minus b c))
                   (eq_coerc (eq nat b (plus (minus b c) c))
                      (eq nat b (plus c (minus b c)))
                      (plus_minus_m_m b c (not_lt_to_le b c Hbc))
                      (rewrite_r nat (plus c (minus b c))
                         (fun __ : nat =>
                          eq Prop (eq nat b __)
                            (eq nat b (plus c (minus b c))))
                         (refl Prop (eq nat b (plus c (minus b c))))
                         (plus (minus b c) c)
                         (commutative_plus (minus b c) c))))
                (plus (times a c) (times a (minus b c)))
                (distributive_times_plus a c (minus b c))))
          (refl Prop
             (eq nat (minus (times a b) (times a c)) (times a (minus b c))))))
    (decidable_lt b c).
Definition minus_plus :
  forall n m p : nat, eq nat (minus (minus n m) p) (minus n (plus m p)) :=
  fun n m p : nat =>
  match_Or_prop (le (plus m p) n) (Not (le (plus m p) n))
    (eq nat (minus (minus n m) p) (minus n (plus m p)))
    (fun Hlt : le (plus m p) n =>
     plus_to_minus (minus n m) p (minus n (plus m p))
       (plus_to_minus n m (plus p (minus n (plus m p)))
          (eq_ind nat (plus (plus m p) (minus n (plus m p)))
             (fun x_1 : nat => eq nat n x_1)
             (minus_to_plus n (plus m p) (minus n (plus m p)) Hlt
                (refl nat (minus n (plus m p))))
             (plus m (plus p (minus n (plus m p))))
             (associative_plus m p (minus n (plus m p))))))
    (fun Hlt : Not (le (plus m p) n) =>
     eq_ind_r nat O (fun x : nat => eq nat x (minus n (plus m p)))
       (sym_eq nat (minus n (plus m p)) O
          (eq_coerc (eq nat (minus n (plus m p)) O)
             (eq nat (minus n (plus m p)) O)
             (eq_minus_O n (plus m p)
                (transitive_le n (S n) (plus m p) 
                   (le_n_Sn n) (not_le_to_lt (plus m p) n Hlt)))
             (refl Prop (eq nat (minus n (plus m p)) O))))
       (minus (minus n m) p)
       (eq_minus_O (minus n m) p
          (eq_coerc (le (minus n m) (minus (plus p m) m)) 
             (le (minus n m) p)
             (monotonic_le_minus_l (plus p m) n m
                (eq_coerc (le n (plus m p)) (le n (plus p m))
                   (transitive_le n (S n) (plus m p) 
                      (le_n_Sn n) (not_le_to_lt (plus m p) n Hlt))
                   (rewrite_r nat (plus m p)
                      (fun __ : nat => eq Prop (le n (plus m p)) (le n __))
                      (refl Prop (le n (plus m p))) 
                      (plus p m) (commutative_plus p m))))
             (rewrite_l nat p
                (fun __ : nat =>
                 eq Prop (le (minus n m) __) (le (minus n m) p))
                (refl Prop (le (minus n m) p)) (minus (plus p m) m)
                (minus_plus_m_m p m))))) (decidable_le (plus m p) n).
Definition minus_minus :
  forall n m p : nat,
  le p m -> le m n -> eq nat (plus p (minus n m)) (minus n (minus m p)) :=
  fun (n m p : nat) (lepm : le p m) (lemn : le m n) =>
  sym_eq nat (minus n (minus m p)) (plus p (minus n m))
    (plus_to_minus n (minus m p) (plus p (minus n m))
       (eq_ind nat (plus (plus (minus m p) p) (minus n m))
          (fun x_1 : nat => eq nat n x_1)
          (eq_ind nat m (fun x_1 : nat => eq nat n (plus x_1 (minus n m)))
             (eq_ind nat (plus (minus n m) m) (fun x_1 : nat => eq nat n x_1)
                (eq_ind nat n (fun x_1 : nat => eq nat n x_1) 
                   (refl nat n) (plus (minus n m) m)
                   (plus_minus_m_m n m lemn)) (plus m (minus n m))
                (commutative_plus (minus n m) m)) 
             (plus (minus m p) p) (plus_minus_m_m m p lepm))
          (plus (minus m p) (plus p (minus n m)))
          (associative_plus (minus m p) p (minus n m)))).
Definition minus_minus_comm :
  forall a b c : nat, eq nat (minus (minus a b) c) (minus (minus a c) b) :=
  fun a b c : nat =>
  le_to_le_to_eq (minus (minus a b) c) (minus (minus a c) b)
    (eq_coerc
       (le (minus (minus a b) c) (minus (plus (minus (minus a c) b) c) c))
       (le (minus (minus a b) c) (minus (minus a c) b))
       (monotonic_le_minus_l (plus (minus (minus a c) b) c) 
          (minus a b) c
          (eq_coerc (le (minus a b) (plus (minus (minus a b) c) c))
             (le (minus a b) (plus (minus (minus a c) b) c))
             (le_plus_minus_m_m (minus a b) c)
             (rewrite_r nat (minus a (plus b c))
                (fun __ : nat =>
                 eq Prop (le (minus a b) (plus __ c))
                   (le (minus a b) (plus (minus (minus a c) b) c)))
                (rewrite_r nat (plus c (minus a (plus b c)))
                   (fun __ : nat =>
                    eq Prop (le (minus a b) __)
                      (le (minus a b) (plus (minus (minus a c) b) c)))
                   (rewrite_r nat (plus c (minus (minus a c) b))
                      (fun __ : nat =>
                       eq Prop (le (minus a b) (plus c (minus a (plus b c))))
                         (le (minus a b) __))
                      (rewrite_l nat (minus (minus a c) b)
                         (fun __ : nat =>
                          eq Prop (le (minus a b) (plus c __))
                            (le (minus a b) (plus c (minus (minus a c) b))))
                         (refl Prop
                            (le (minus a b) (plus c (minus (minus a c) b))))
                         (minus a (plus b c))
                         (rewrite_l nat (plus c b)
                            (fun __ : nat =>
                             eq nat (minus (minus a c) b) (minus a __))
                            (minus_plus a c b) (plus b c)
                            (commutative_plus c b)))
                      (plus (minus (minus a c) b) c)
                      (commutative_plus (minus (minus a c) b) c))
                   (plus (minus a (plus b c)) c)
                   (commutative_plus (minus a (plus b c)) c))
                (minus (minus a b) c) (minus_plus a b c))))
       (rewrite_l nat (minus (minus a c) b)
          (fun __ : nat =>
           eq Prop (le (minus (minus a b) c) __)
             (le (minus (minus a b) c) (minus (minus a c) b)))
          (refl Prop (le (minus (minus a b) c) (minus (minus a c) b)))
          (minus (plus (minus (minus a c) b) c) c)
          (minus_plus_m_m (minus (minus a c) b) c)))
    (eq_coerc
       (le (minus (minus a c) b) (minus (plus (minus (minus a b) c) b) b))
       (le (minus (minus a c) b) (minus (minus a b) c))
       (monotonic_le_minus_l (plus (minus (minus a b) c) b) 
          (minus a c) b
          (eq_coerc (le (minus a c) (plus (minus (minus a c) b) b))
             (le (minus a c) (plus (minus (minus a b) c) b))
             (le_plus_minus_m_m (minus a c) b)
             (rewrite_r nat (minus a (plus c b))
                (fun __ : nat =>
                 eq Prop (le (minus a c) (plus __ b))
                   (le (minus a c) (plus (minus (minus a b) c) b)))
                (rewrite_r nat (plus b (minus a (plus c b)))
                   (fun __ : nat =>
                    eq Prop (le (minus a c) __)
                      (le (minus a c) (plus (minus (minus a b) c) b)))
                   (rewrite_r nat (plus b (minus (minus a b) c))
                      (fun __ : nat =>
                       eq Prop (le (minus a c) (plus b (minus a (plus c b))))
                         (le (minus a c) __))
                      (rewrite_l nat (minus (minus a b) c)
                         (fun __ : nat =>
                          eq Prop (le (minus a c) (plus b __))
                            (le (minus a c) (plus b (minus (minus a b) c))))
                         (refl Prop
                            (le (minus a c) (plus b (minus (minus a b) c))))
                         (minus a (plus c b))
                         (rewrite_l nat (plus b c)
                            (fun __ : nat =>
                             eq nat (minus (minus a b) c) (minus a __))
                            (minus_plus a b c) (plus c b)
                            (commutative_plus b c)))
                      (plus (minus (minus a b) c) b)
                      (commutative_plus (minus (minus a b) c) b))
                   (plus (minus a (plus c b)) b)
                   (commutative_plus (minus a (plus c b)) b))
                (minus (minus a c) b) (minus_plus a c b))))
       (rewrite_l nat (minus (minus a b) c)
          (fun __ : nat =>
           eq Prop (le (minus (minus a c) b) __)
             (le (minus (minus a c) b) (minus (minus a b) c)))
          (refl Prop (le (minus (minus a c) b) (minus (minus a b) c)))
          (minus (plus (minus (minus a b) c) b) b)
          (minus_plus_m_m (minus (minus a b) c) b))).
Definition minus_le_minus_minus_comm :
  forall b c a : nat,
  le c b -> eq nat (minus a (minus b c)) (minus (plus a c) b) :=
  fun (b c a : nat) (H : le c b) =>
  eq_ind_r nat (plus (minus b c) c)
    (fun x : nat => eq nat (minus a (minus b c)) (minus (plus a c) x))
    (rewrite_r nat (plus c a)
       (fun __ : nat =>
        eq nat (minus a (minus b c)) (minus __ (plus (minus b c) c)))
       (rewrite_r nat (plus c (minus b c))
          (fun __ : nat => eq nat (minus a (minus b c)) (minus (plus c a) __))
          (rewrite_l nat (minus (minus (plus c a) c) (minus b c))
             (fun __ : nat => eq nat (minus a (minus b c)) __)
             (rewrite_r nat (minus (plus c a) c)
                (fun __ : nat =>
                 eq nat (minus __ (minus b c))
                   (minus (minus (plus c a) c) (minus b c)))
                (refl nat (minus (minus (plus c a) c) (minus b c))) a
                (rewrite_l nat (plus a c)
                   (fun __ : nat => eq nat a (minus __ c))
                   (minus_plus_m_m a c) (plus c a) 
                   (commutative_plus a c)))
             (minus (plus c a) (plus c (minus b c)))
             (minus_plus (plus c a) c (minus b c))) 
          (plus (minus b c) c) (commutative_plus (minus b c) c)) 
       (plus a c) (commutative_plus a c)) b (plus_minus_m_m b c H).
Definition minus_plus_plus_l :
  forall x y h : nat, eq nat (minus (plus x h) (plus y h)) (minus x y) :=
  fun x y h : nat =>
  rewrite_l nat (minus (minus (plus x h) y) h)
    (fun __ : nat => eq nat __ (minus x y))
    (rewrite_r nat (minus x y) (fun __ : nat => eq nat __ (minus x y))
       (refl nat (minus x y)) (minus (minus (plus x h) y) h)
       (rewrite_r nat (minus (plus x h) h)
          (fun __ : nat => eq nat (minus (minus (plus x h) y) h) (minus __ y))
          (minus_minus_comm (plus x h) y h) x (minus_plus_m_m x h)))
    (minus (plus x h) (plus y h)) (minus_plus (plus x h) y h).

From Coq.Arith Require Import EqNat.

Definition eqb : nat -> nat -> bool := PeanoNat.Nat.eqb.

Definition eqb_body : nat -> nat -> bool := eqb.

Theorem eq_eqb :
  forall n : nat,
  leibniz (nat -> bool) (eqb n) (filter_nat_type (nat -> bool) eqb_body n).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.

Definition sym_eq_eqb :
  forall n : nat,
  leibniz (nat -> bool) (filter_nat_type (nat -> bool) eqb_body n) (eqb n) :=
  fun n : nat =>
  sym_leibniz (nat -> bool) (eqb n)
    (filter_nat_type (nat -> bool) eqb_body n) (eq_eqb n).
Theorem eq_eqb_body_O :
  leibniz (nat -> bool) (eqb_body O)
    (fun m : nat => match_nat_type bool true (fun q : nat => false) m).
Proof.
  (intros **; apply to_leibniz).
  (apply functional_extensionality).
  (intro x; destruct x; reflexivity).
Qed.

Definition sym_eq_eqb_body_O :
  leibniz (nat -> bool)
    (fun m : nat => match_nat_type bool true (fun q : nat => false) m)
    (eqb_body O) :=
  sym_leibniz (nat -> bool) (eqb_body O)
    (fun m : nat => match_nat_type bool true (fun q : nat => false) m)
    eq_eqb_body_O.

Theorem eq_eqb_body_S :
  forall n : nat,
  leibniz (nat -> bool) (eqb_body (S n))
    (fun m : nat => match_nat_type bool false (fun q : nat => eqb n q) m).
Proof.
  (intros **; apply to_leibniz).
  (apply functional_extensionality).
  (intro x; destruct x; reflexivity).
Qed.

Definition sym_eq_eqb_body_S :
  forall n : nat,
  leibniz (nat -> bool)
    (fun m : nat => match_nat_type bool false (fun q : nat => eqb n q) m)
    (eqb_body (S n)) :=
  fun n : nat =>
  sym_leibniz (nat -> bool) (eqb_body (S n))
    (fun m : nat => match_nat_type bool false (fun q : nat => eqb n q) m)
    (eq_eqb_body_S n).
Definition eqb_elim :
  forall (n m : nat) (P : bool -> Prop),
  (eq nat n m -> P true) -> (Not (eq nat n m) -> P false) -> P (eqb n m) :=
  nat_elim2
    (fun __ _0 : nat =>
     forall P : bool -> Prop,
     (eq nat __ _0 -> P true) ->
     (Not (eq nat __ _0) -> P false) -> P (eqb __ _0))
    (fun n : nat =>
     match_nat_prop
       (fun __ : nat =>
        forall P : bool -> Prop,
        (eq nat O __ -> P true) ->
        (Not (eq nat O __) -> P false) -> P (eqb O __))
       (sym_eq_eqb O
          (fun y : nat -> bool =>
           forall P : bool -> Prop,
           (eq nat O O -> P true) -> (Not (eq nat O O) -> P false) -> P (y O))
          (sym_eq_filter_nat_type_O (nat -> bool) eqb_body
             (fun y : nat -> bool =>
              forall P : bool -> Prop,
              (eq nat O O -> P true) ->
              (Not (eq nat O O) -> P false) -> P (y O))
             (sym_eq_eqb_body_O
                (fun y : nat -> bool =>
                 forall P : bool -> Prop,
                 (eq nat O O -> P true) ->
                 (Not (eq nat O O) -> P false) -> P (y O))
                (sym_eq_match_nat_type_O bool true 
                   (fun q : nat => false)
                   (fun y : bool =>
                    forall P : bool -> Prop,
                    (eq nat O O -> P true) ->
                    (Not (eq nat O O) -> P false) -> P y)
                   (fun (P : bool -> Prop) (auto : eq nat O O -> P true)
                      (auto' : Not (eq nat O O) -> P false) =>
                    auto (refl nat O))))))
       (fun auto : nat =>
        sym_eq_eqb O
          (fun y : nat -> bool =>
           forall P : bool -> Prop,
           (eq nat O (S auto) -> P true) ->
           (Not (eq nat O (S auto)) -> P false) -> P (y (S auto)))
          (sym_eq_filter_nat_type_O (nat -> bool) eqb_body
             (fun y : nat -> bool =>
              forall P : bool -> Prop,
              (eq nat O (S auto) -> P true) ->
              (Not (eq nat O (S auto)) -> P false) -> P (y (S auto)))
             (sym_eq_eqb_body_O
                (fun y : nat -> bool =>
                 forall P : bool -> Prop,
                 (eq nat O (S auto) -> P true) ->
                 (Not (eq nat O (S auto)) -> P false) -> P (y (S auto)))
                (sym_eq_match_nat_type_S bool true 
                   (fun q : nat => false) auto
                   (fun y : bool =>
                    forall P : bool -> Prop,
                    (eq nat O (S auto) -> P true) ->
                    (Not (eq nat O (S auto)) -> P false) -> P y)
                   (fun (P : bool -> Prop)
                      (auto' : eq nat O (S auto) -> P true)
                      (auto'' : Not (eq nat O (S auto)) -> P false) =>
                    auto'' (not_eq_O_S auto)))))) n)
    (fun n : nat =>
     sym_eq_eqb (S n)
       (fun y : nat -> bool =>
        forall P : bool -> Prop,
        (eq nat (S n) O -> P true) ->
        (Not (eq nat (S n) O) -> P false) -> P (y O))
       (sym_eq_filter_nat_type_S (nat -> bool) eqb_body n
          (fun y : nat -> bool =>
           forall P : bool -> Prop,
           (eq nat (S n) O -> P true) ->
           (Not (eq nat (S n) O) -> P false) -> P (y O))
          (sym_eq_eqb_body_S n
             (fun y : nat -> bool =>
              forall P : bool -> Prop,
              (eq nat (S n) O -> P true) ->
              (Not (eq nat (S n) O) -> P false) -> P (y O))
             (sym_eq_match_nat_type_O bool false (fun q : nat => eqb n q)
                (fun y : bool =>
                 forall P : bool -> Prop,
                 (eq nat (S n) O -> P true) ->
                 (Not (eq nat (S n) O) -> P false) -> P y)
                (fun (P : bool -> Prop) (auto : eq nat (S n) O -> P true)
                   (auto' : Not (eq nat (S n) O) -> P false) =>
                 auto' (sym_not_eq nat O (S n) (not_eq_O_S n)))))))
    (fun n m : nat =>
     sym_eq_eqb (S n)
       (fun y : nat -> bool =>
        (forall P : bool -> Prop,
         (eq nat n m -> P true) ->
         (Not (eq nat n m) -> P false) -> P (eqb n m)) ->
        forall P : bool -> Prop,
        (eq nat (S n) (S m) -> P true) ->
        (Not (eq nat (S n) (S m)) -> P false) -> P (y (S m)))
       (sym_eq_filter_nat_type_S (nat -> bool) eqb_body n
          (fun y : nat -> bool =>
           (forall P : bool -> Prop,
            (eq nat n m -> P true) ->
            (Not (eq nat n m) -> P false) -> P (eqb n m)) ->
           forall P : bool -> Prop,
           (eq nat (S n) (S m) -> P true) ->
           (Not (eq nat (S n) (S m)) -> P false) -> P (y (S m)))
          (sym_eq_eqb_body_S n
             (fun y : nat -> bool =>
              (forall P : bool -> Prop,
               (eq nat n m -> P true) ->
               (Not (eq nat n m) -> P false) -> P (eqb n m)) ->
              forall P : bool -> Prop,
              (eq nat (S n) (S m) -> P true) ->
              (Not (eq nat (S n) (S m)) -> P false) -> P (y (S m)))
             (sym_eq_match_nat_type_S bool false (fun q : nat => eqb n q) m
                (fun y : bool =>
                 (forall P : bool -> Prop,
                  (eq nat n m -> P true) ->
                  (Not (eq nat n m) -> P false) -> P (eqb n m)) ->
                 forall P : bool -> Prop,
                 (eq nat (S n) (S m) -> P true) ->
                 (Not (eq nat (S n) (S m)) -> P false) -> P y)
                (fun
                   (auto : forall P : bool -> Prop,
                           (eq nat n m -> P true) ->
                           (Not (eq nat n m) -> P false) -> P (eqb n m))
                   (P : bool -> Prop) (auto' : eq nat (S n) (S m) -> P true)
                   (auto'' : Not (eq nat (S n) (S m)) -> P false) =>
                 auto P
                   (fun auto''' : eq nat n m =>
                    auto'
                      (rewrite_l nat n (fun __ : nat => eq nat (S n) (S __))
                         (refl nat (S n)) m auto'''))
                   (fun auto''' : Not (eq nat n m) =>
                    auto'' (not_eq_S n m auto'''))))))).
Definition eqb_n_n : forall n : nat, eq bool (eqb n n) true :=
  fun n : nat =>
  nat_ind (fun _x_365 : nat => eq bool (eqb _x_365 _x_365) true)
    (sym_eq_eqb O (fun y : nat -> bool => eq bool (y O) true)
       (sym_eq_filter_nat_type_O (nat -> bool) eqb_body
          (fun y : nat -> bool => eq bool (y O) true)
          (sym_eq_eqb_body_O (fun y : nat -> bool => eq bool (y O) true)
             (sym_eq_match_nat_type_O bool true (fun q : nat => false)
                (fun y : bool => eq bool y true) (refl bool true)))))
    (fun x_366 : nat =>
     sym_eq_eqb (S x_366)
       (fun y : nat -> bool =>
        eq bool (eqb x_366 x_366) true -> eq bool (y (S x_366)) true)
       (sym_eq_filter_nat_type_S (nat -> bool) eqb_body x_366
          (fun y : nat -> bool =>
           eq bool (eqb x_366 x_366) true -> eq bool (y (S x_366)) true)
          (sym_eq_eqb_body_S x_366
             (fun y : nat -> bool =>
              eq bool (eqb x_366 x_366) true -> eq bool (y (S x_366)) true)
             (sym_eq_match_nat_type_S bool false (fun q : nat => eqb x_366 q)
                x_366
                (fun y : bool =>
                 eq bool (eqb x_366 x_366) true -> eq bool y true)
                (fun _x_368 : eq bool (eqb x_366 x_366) true =>
                 rewrite_r bool true (fun __ : bool => eq bool __ true)
                   (refl bool true) (eqb x_366 x_366) _x_368))))) n.
Definition eqb_true_to_eq :
  forall n m : nat, eq bool (eqb n m) true -> eq nat n m :=
  fun n m : nat =>
  eqb_elim n m (fun __ : bool => eq bool __ true -> eq nat n m)
    (fun (auto : eq nat n m) (auto' : eq bool true true) =>
     rewrite_l nat n (fun __ : nat => eq nat n __) (refl nat n) m auto)
    (fun (__ : Not (eq nat n m)) (abs : eq bool false true) =>
     falsity (eq nat n m)
       (absurd (eq bool true false)
          (rewrite_r bool true (fun __1 : bool => eq bool true __1)
             (refl bool true) false abs) not_eq_true_false)).
Definition eqb_false_to_not_eq :
  forall n m : nat, eq bool (eqb n m) false -> Not (eq nat n m) :=
  fun n m : nat =>
  eqb_elim n m (fun __ : bool => eq bool __ false -> Not (eq nat n m))
    (fun (auto : eq nat n m) (auto' : eq bool true false) =>
     not_to_not (eq nat n m) (eq bool true false)
       (fun auto'' : eq nat n m =>
        rewrite_l bool true (fun __ : bool => eq bool true __)
          (refl bool true) false auto') not_eq_true_false)
    (fun (auto : Not (eq nat n m)) (auto' : eq bool false false) => auto).
Definition eq_to_eqb_true :
  forall n m : nat, eq nat n m -> eq bool (eqb n m) true :=
  fun (n m : nat) (auto : eq nat n m) =>
  rewrite_l nat n (fun __ : nat => eq bool (eqb n __) true)
    (rewrite_r bool true (fun __ : bool => eq bool __ true) 
       (refl bool true) (eqb n n) (eqb_n_n n)) m auto.
Definition not_eq_to_eqb_false :
  forall n m : nat, Not (eq nat n m) -> eq bool (eqb n m) false :=
  fun (n m : nat) (noteq : Not (eq nat n m)) =>
  eqb_elim n m (fun __ : bool => eq bool __ false)
    (fun Heq : eq nat n m =>
     falsity (eq bool true false)
       (absurd (eq nat n m)
          (rewrite_l nat n (fun __ : nat => eq nat n __) (refl nat n) m Heq)
          noteq)) (fun auto : Not (eq nat n m) => refl bool false).

From Coq.Arith Require Import Compare_dec.

Definition leb : nat -> nat -> bool := PeanoNat.Nat.leb.

Definition leb_body : nat -> nat -> bool := leb.
Theorem eq_leb :
  forall n : nat,
  leibniz (nat -> bool) (leb n) (filter_nat_type (nat -> bool) leb_body n).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.
Definition sym_eq_leb :
  forall n : nat,
  leibniz (nat -> bool) (filter_nat_type (nat -> bool) leb_body n) (leb n) :=
  fun n : nat =>
  sym_leibniz (nat -> bool) (leb n)
    (filter_nat_type (nat -> bool) leb_body n) (eq_leb n).
Theorem eq_leb_body_O :
  leibniz (nat -> bool) (leb_body O) (fun m : nat => true).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.

Definition sym_eq_leb_body_O :
  leibniz (nat -> bool) (fun m : nat => true) (leb_body O) :=
  sym_leibniz (nat -> bool) (leb_body O) (fun m : nat => true) eq_leb_body_O.
Theorem eq_leb_body_S :
  forall n : nat,
  leibniz (nat -> bool) (leb_body (S n))
    (fun m : nat => match_nat_type bool false (fun q : nat => leb n q) m).
Proof.
  (intros **; apply to_leibniz).
  (apply functional_extensionality).
  (intro x; destruct x; reflexivity).
Qed.
Definition sym_eq_leb_body_S :
  forall n : nat,
  leibniz (nat -> bool)
    (fun m : nat => match_nat_type bool false (fun q : nat => leb n q) m)
    (leb_body (S n)) :=
  fun n : nat =>
  sym_leibniz (nat -> bool) (leb_body (S n))
    (fun m : nat => match_nat_type bool false (fun q : nat => leb n q) m)
    (eq_leb_body_S n).
Definition leb_elim :
  forall (n m : nat) (P : bool -> Prop),
  (le n m -> P true) -> (Not (le n m) -> P false) -> P (leb n m) :=
  nat_elim2
    (fun __ _0 : nat =>
     forall P : bool -> Prop,
     (le __ _0 -> P true) -> (Not (le __ _0) -> P false) -> P (leb __ _0))
    (fun n : nat =>
     sym_eq_leb O
       (fun y : nat -> bool =>
        forall P : bool -> Prop,
        (le O n -> P true) -> (Not (le O n) -> P false) -> P (y n))
       (sym_eq_filter_nat_type_O (nat -> bool) leb_body
          (fun y : nat -> bool =>
           forall P : bool -> Prop,
           (le O n -> P true) -> (Not (le O n) -> P false) -> P (y n))
          (sym_eq_leb_body_O
             (fun y : nat -> bool =>
              forall P : bool -> Prop,
              (le O n -> P true) -> (Not (le O n) -> P false) -> P (y n))
             (fun (P : bool -> Prop) (auto : le O n -> P true)
                (auto' : Not (le O n) -> P false) => 
              auto (le_O_n n)))))
    (fun n : nat =>
     sym_eq_leb (S n)
       (fun y : nat -> bool =>
        forall P : bool -> Prop,
        (le (S n) O -> P true) -> (Not (le (S n) O) -> P false) -> P (y O))
       (sym_eq_filter_nat_type_S (nat -> bool) leb_body n
          (fun y : nat -> bool =>
           forall P : bool -> Prop,
           (le (S n) O -> P true) -> (Not (le (S n) O) -> P false) -> P (y O))
          (sym_eq_leb_body_S n
             (fun y : nat -> bool =>
              forall P : bool -> Prop,
              (le (S n) O -> P true) ->
              (Not (le (S n) O) -> P false) -> P (y O))
             (sym_eq_match_nat_type_O bool false (fun q : nat => leb n q)
                (fun y : bool =>
                 forall P : bool -> Prop,
                 (le (S n) O -> P true) ->
                 (Not (le (S n) O) -> P false) -> P y)
                (fun (P : bool -> Prop) (auto : le (S n) O -> P true)
                   (auto' : Not (le (S n) O) -> P false) =>
                 auto' (not_le_Sn_O n))))))
    (fun n m : nat =>
     sym_eq_leb (S n)
       (fun y : nat -> bool =>
        (forall P : bool -> Prop,
         (le n m -> P true) -> (Not (le n m) -> P false) -> P (leb n m)) ->
        forall P : bool -> Prop,
        (le (S n) (S m) -> P true) ->
        (Not (le (S n) (S m)) -> P false) -> P (y (S m)))
       (sym_eq_filter_nat_type_S (nat -> bool) leb_body n
          (fun y : nat -> bool =>
           (forall P : bool -> Prop,
            (le n m -> P true) -> (Not (le n m) -> P false) -> P (leb n m)) ->
           forall P : bool -> Prop,
           (le (S n) (S m) -> P true) ->
           (Not (le (S n) (S m)) -> P false) -> P (y (S m)))
          (sym_eq_leb_body_S n
             (fun y : nat -> bool =>
              (forall P : bool -> Prop,
               (le n m -> P true) -> (Not (le n m) -> P false) -> P (leb n m)) ->
              forall P : bool -> Prop,
              (le (S n) (S m) -> P true) ->
              (Not (le (S n) (S m)) -> P false) -> P (y (S m)))
             (sym_eq_match_nat_type_S bool false (fun q : nat => leb n q) m
                (fun y : bool =>
                 (forall P : bool -> Prop,
                  (le n m -> P true) ->
                  (Not (le n m) -> P false) -> P (leb n m)) ->
                 forall P : bool -> Prop,
                 (le (S n) (S m) -> P true) ->
                 (Not (le (S n) (S m)) -> P false) -> P y)
                (fun
                   (Hind : forall P : bool -> Prop,
                           (le n m -> P true) ->
                           (Not (le n m) -> P false) -> P (leb n m))
                   (P : bool -> Prop) (Pt : le (S n) (S m) -> P true)
                   (Pf : Not (le (S n) (S m)) -> P false) =>
                 Hind P (fun lenm : le n m => Pt (le_S_S n m lenm))
                   (fun nlenm : Not (le n m) =>
                    Pf (not_le_to_not_le_S_S n m nlenm))))))).
Definition leb_true_to_le :
  forall n m : nat, eq bool (leb n m) true -> le n m :=
  fun n m : nat =>
  leb_elim n m (fun __ : bool => eq bool __ true -> le n m)
    (fun (auto : le n m) (auto' : eq bool true true) => auto)
    (fun (__ : Not (le n m)) (abs : eq bool false true) =>
     falsity (le n m)
       (absurd (eq bool true false)
          (rewrite_r bool true (fun __1 : bool => eq bool true __1)
             (refl bool true) false abs) not_eq_true_false)).
Definition le_to_leb_true :
  forall n m : nat, le n m -> eq bool (leb n m) true :=
  fun n m : nat =>
  leb_elim n m (fun __ : bool => le n m -> eq bool __ true)
    (fun auto auto' : le n m => refl bool true)
    (fun (H : Not (le n m)) (H1 : le n m) =>
     falsity (eq bool false true) (absurd (le n m) H1 H)).
Definition not_le_to_leb_false :
  forall n m : nat, Not (le n m) -> eq bool (leb n m) false :=
  fun n m : nat =>
  leb_elim n m (fun __ : bool => Not (le n m) -> eq bool __ false)
    (fun (H : le n m) (H1 : Not (le n m)) =>
     falsity (eq bool true false) (absurd (le n m) H H1))
    (fun auto auto' : Not (le n m) => refl bool false).

Fixpoint mod_aux (p m n : nat) : nat :=
  match p with
  | 0 => m
  | Datatypes.S p =>
      if PeanoNat.Nat.leb m n then m else mod_aux p (minus m (S n)) n
  end.

Definition mod_aux_body : nat -> nat -> nat -> nat := mod_aux.

Theorem eq_mod_aux :
  forall p : nat,
  leibniz (nat -> nat -> nat) (mod_aux p)
    (filter_nat_type (nat -> nat -> nat) mod_aux_body p).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.

Definition sym_eq_mod_aux :
  forall p : nat,
  leibniz (nat -> nat -> nat)
    (filter_nat_type (nat -> nat -> nat) mod_aux_body p) 
    (mod_aux p) :=
  fun p : nat =>
  sym_leibniz (nat -> nat -> nat) (mod_aux p)
    (filter_nat_type (nat -> nat -> nat) mod_aux_body p) 
    (eq_mod_aux p).
Theorem eq_mod_aux_body_O :
  leibniz (nat -> nat -> nat) (mod_aux_body O) (fun m n : nat => m).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.
Definition sym_eq_mod_aux_body_O :
  leibniz (nat -> nat -> nat) (fun m n : nat => m) (mod_aux_body O) :=
  sym_leibniz (nat -> nat -> nat) (mod_aux_body O) 
    (fun m n : nat => m) eq_mod_aux_body_O.
Theorem eq_mod_aux_body_S :
  forall p : nat,
  leibniz (nat -> nat -> nat) (mod_aux_body (S p))
    (fun m n : nat =>
     match_bool_type nat m (mod_aux p (minus m (S n)) n) (leb m n)).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.

Definition sym_eq_mod_aux_body_S :
  forall p : nat,
  leibniz (nat -> nat -> nat)
    (fun m n : nat =>
     match_bool_type nat m (mod_aux p (minus m (S n)) n) (leb m n))
    (mod_aux_body (S p)) :=
  fun p : nat =>
  sym_leibniz (nat -> nat -> nat) (mod_aux_body (S p))
    (fun m n : nat =>
     match_bool_type nat m (mod_aux p (minus m (S n)) n) (leb m n))
    (eq_mod_aux_body_S p).
Definition mod : nat -> nat -> nat :=
  fun n m : nat => match_nat_type nat n (fun p : nat => mod_aux n n p) m.

Fixpoint div_aux (p m n : nat) : nat :=
  match p with
  | 0 => 0
  | Datatypes.S p => if leb m n then 0 else S (div_aux p (minus m (S n)) n)
  end.

Definition div_aux_body : nat -> nat -> nat -> nat := div_aux.

Theorem eq_div_aux :
  forall p : nat,
  leibniz (nat -> nat -> nat) (div_aux p)
    (filter_nat_type (nat -> nat -> nat) div_aux_body p).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.
Definition sym_eq_div_aux :
  forall p : nat,
  leibniz (nat -> nat -> nat)
    (filter_nat_type (nat -> nat -> nat) div_aux_body p) 
    (div_aux p) :=
  fun p : nat =>
  sym_leibniz (nat -> nat -> nat) (div_aux p)
    (filter_nat_type (nat -> nat -> nat) div_aux_body p) 
    (eq_div_aux p).
Theorem eq_div_aux_body_O :
  leibniz (nat -> nat -> nat) (div_aux_body O) (fun m n : nat => O).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.
Definition sym_eq_div_aux_body_O :
  leibniz (nat -> nat -> nat) (fun m n : nat => O) (div_aux_body O) :=
  sym_leibniz (nat -> nat -> nat) (div_aux_body O) 
    (fun m n : nat => O) eq_div_aux_body_O.
Theorem eq_div_aux_body_S :
  forall p : nat,
  leibniz (nat -> nat -> nat) (div_aux_body (S p))
    (fun m n : nat =>
     match_bool_type nat O (S (div_aux p (minus m (S n)) n)) (leb m n)).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.
Definition sym_eq_div_aux_body_S :
  forall p : nat,
  leibniz (nat -> nat -> nat)
    (fun m n : nat =>
     match_bool_type nat O (S (div_aux p (minus m (S n)) n)) (leb m n))
    (div_aux_body (S p)) :=
  fun p : nat =>
  sym_leibniz (nat -> nat -> nat) (div_aux_body (S p))
    (fun m n : nat =>
     match_bool_type nat O (S (div_aux p (minus m (S n)) n)) (leb m n))
    (eq_div_aux_body_S p).
Definition div : nat -> nat -> nat :=
  fun n m : nat => match_nat_type nat (S n) (fun p : nat => div_aux n n p) m.
Definition le_mod_aux_m_m :
  forall p n m : nat, le n p -> le (mod_aux p n m) m :=
  fun p : nat =>
  nat_ind
    (fun _x_365 : nat =>
     forall n m : nat, le n _x_365 -> le (mod_aux _x_365 n m) m)
    (fun n m : nat =>
     sym_eq_mod_aux O (fun y : nat -> nat -> nat => le n O -> le (y n m) m)
       (sym_eq_filter_nat_type_O (nat -> nat -> nat) mod_aux_body
          (fun y : nat -> nat -> nat => le n O -> le (y n m) m)
          (sym_eq_mod_aux_body_O
             (fun y : nat -> nat -> nat => le n O -> le (y n m) m)
             (fun lenO : le n O =>
              le_n_O_elim n lenO (fun __ : nat => le __ m) (le_O_n m)))))
    (fun q : nat =>
     sym_eq_mod_aux (S q)
       (fun y : nat -> nat -> nat =>
        (forall n m : nat, le n q -> le (mod_aux q n m) m) ->
        forall n m : nat, le n (S q) -> le (y n m) m)
       (sym_eq_filter_nat_type_S (nat -> nat -> nat) mod_aux_body q
          (fun y : nat -> nat -> nat =>
           (forall n m : nat, le n q -> le (mod_aux q n m) m) ->
           forall n m : nat, le n (S q) -> le (y n m) m)
          (sym_eq_mod_aux_body_S q
             (fun y : nat -> nat -> nat =>
              (forall n m : nat, le n q -> le (mod_aux q n m) m) ->
              forall n m : nat, le n (S q) -> le (y n m) m)
             (fun (Hind : forall n m : nat, le n q -> le (mod_aux q n m) m)
                (n m : nat) (len : le n (S q)) =>
              leb_elim n m
                (fun __ : bool =>
                 le (match_bool_type nat n (mod_aux q (minus n (S m)) m) __)
                   m)
                (sym_eq_match_bool_type_true nat n
                   (mod_aux q (minus n (S m)) m)
                   (fun y : nat => le n m -> le y m)
                   (fun auto : le n m => auto))
                (sym_eq_match_bool_type_false nat n
                   (mod_aux q (minus n (S m)) m)
                   (fun y : nat => Not (le n m) -> le y m)
                   (fun notlenm : Not (le n m) =>
                    Hind (minus n (S m)) m
                      (le_plus_to_minus n (S m) q
                         (transitive_le n (S q) (plus q (S m)) len
                            (eq_coerc (le (S q) (plus (S q) m))
                               (le (S q) (plus q (S m)))
                               (le_plus_n_r m (S q))
                               (rewrite_l nat (plus m (S q))
                                  (fun __ : nat =>
                                   eq Prop (le (S q) __)
                                     (le (S q) (plus q (S m))))
                                  (rewrite_r nat (plus q (S m))
                                     (fun __ : nat =>
                                      eq Prop (le (S q) __)
                                        (le (S q) (plus q (S m))))
                                     (refl Prop (le (S q) (plus q (S m))))
                                     (plus m (S q))
                                     (rewrite_l nat 
                                        (S (plus m q))
                                        (fun __ : nat =>
                                         eq nat __ (plus q (S m)))
                                        (rewrite_l nat 
                                           (plus q m)
                                           (fun __ : nat =>
                                            eq nat (S __) (plus q (S m)))
                                           (plus_n_Sm q m) 
                                           (plus m q) 
                                           (commutative_plus q m))
                                        (plus m (S q)) 
                                        (plus_n_Sm m q))) 
                                  (plus (S q) m) (commutative_plus m (S q))))))))))))
    p.
Definition lt_mod_m_m : forall n m : nat, lt O m -> lt (mod n m) m :=
  fun n m : nat =>
  match_nat_prop (fun __ : nat => lt O __ -> lt (mod n __) __)
    (fun abs : lt O O =>
     falsity (lt (mod n O) O) (absurd (le (S O) O) abs (not_le_Sn_O O)))
    (fun p : nat =>
     sym_eq_match_nat_type_S nat n (fun q : nat => mod_aux n n q) p
       (fun y : nat => lt O (S p) -> lt y (S p))
       (fun __ : lt O (S p) =>
        le_S_S (mod_aux n n p) p (le_mod_aux_m_m n n p (le_n n)))) m.
Definition div_aux_mod_aux :
  forall p n m : nat,
  eq nat n (plus (times (div_aux p n m) (S m)) (mod_aux p n m)) :=
  fun p : nat =>
  nat_ind
    (fun _x_365 : nat =>
     forall n m : nat,
     eq nat n (plus (times (div_aux _x_365 n m) (S m)) (mod_aux _x_365 n m)))
    (fun n m : nat =>
     sym_eq_div_aux O
       (fun y : nat -> nat -> nat =>
        eq nat n (plus (times (y n m) (S m)) (mod_aux O n m)))
       (sym_eq_filter_nat_type_O (nat -> nat -> nat) div_aux_body
          (fun y : nat -> nat -> nat =>
           eq nat n (plus (times (y n m) (S m)) (mod_aux O n m)))
          (sym_eq_div_aux_body_O
             (fun y : nat -> nat -> nat =>
              eq nat n (plus (times (y n m) (S m)) (mod_aux O n m)))
             (eq_match_nat_type_O nat O
                (fun q : nat =>
                 match_bool_type nat O (S (div_aux q (minus n (S m)) m))
                   (leb n m))
                (fun y : nat =>
                 eq nat n (plus (times y (S m)) (mod_aux O n m)))
                (sym_eq_mod_aux O
                   (fun y : nat -> nat -> nat =>
                    eq nat n
                      (plus
                         (times
                            ((fun m0 n0 : nat =>
                              match_nat_type nat O
                                (fun q : nat =>
                                 match_bool_type nat O
                                   (S (div_aux q (minus m0 (S n0)) n0))
                                   (leb m0 n0)) O) n m) 
                            (S m)) (y n m)))
                   (sym_eq_filter_nat_type_O (nat -> nat -> nat) mod_aux_body
                      (fun y : nat -> nat -> nat =>
                       eq nat n
                         (plus
                            (times
                               ((fun m0 n0 : nat =>
                                 match_nat_type nat O
                                   (fun q : nat =>
                                    match_bool_type nat O
                                      (S (div_aux q (minus m0 (S n0)) n0))
                                      (leb m0 n0)) O) n m) 
                               (S m)) (y n m)))
                      (sym_eq_mod_aux_body_O
                         (fun y : nat -> nat -> nat =>
                          eq nat n
                            (plus
                               (times
                                  ((fun m0 n0 : nat =>
                                    match_nat_type nat O
                                      (fun q : nat =>
                                       match_bool_type nat O
                                         (S (div_aux q (minus m0 (S n0)) n0))
                                         (leb m0 n0)) O) n m) 
                                  (S m)) (y n m)))
                         (sym_eq_match_nat_type_O nat O
                            (fun q : nat =>
                             match_bool_type nat O
                               (S (div_aux q (minus n (S m)) m)) 
                               (leb n m))
                            (fun y : nat =>
                             eq nat n
                               (plus
                                  (times ((fun m0 n0 : nat => y) n m) (S m))
                                  n))
                            (sym_eq_times O
                               (fun y : nat -> nat =>
                                eq nat n (plus (y (S m)) n))
                               (sym_eq_filter_nat_type_O 
                                  (nat -> nat) times_body
                                  (fun y : nat -> nat =>
                                   eq nat n (plus (y (S m)) n))
                                  (sym_eq_times_body_O
                                     (fun y : nat -> nat =>
                                      eq nat n (plus (y (S m)) n))
                                     (sym_eq_plus O
                                        (fun y : nat -> nat => eq nat n (y n))
                                        (sym_eq_filter_nat_type_O
                                           (nat -> nat) plus_body
                                           (fun y : nat -> nat =>
                                            eq nat n (y n))
                                           (sym_eq_plus_body_O
                                              (fun y : nat -> nat =>
                                               eq nat n (y n)) 
                                              (refl nat n)))))))))))))))
    (fun q : nat =>
     sym_eq_div_aux (S q)
       (fun y : nat -> nat -> nat =>
        (forall n m : nat,
         eq nat n (plus (times (div_aux q n m) (S m)) (mod_aux q n m))) ->
        forall n m : nat,
        eq nat n (plus (times (y n m) (S m)) (mod_aux (S q) n m)))
       (sym_eq_filter_nat_type_S (nat -> nat -> nat) div_aux_body q
          (fun y : nat -> nat -> nat =>
           (forall n m : nat,
            eq nat n (plus (times (div_aux q n m) (S m)) (mod_aux q n m))) ->
           forall n m : nat,
           eq nat n (plus (times (y n m) (S m)) (mod_aux (S q) n m)))
          (sym_eq_div_aux_body_S q
             (fun y : nat -> nat -> nat =>
              (forall n m : nat,
               eq nat n (plus (times (div_aux q n m) (S m)) (mod_aux q n m))) ->
              forall n m : nat,
              eq nat n (plus (times (y n m) (S m)) (mod_aux (S q) n m)))
             (fun
                (Hind : forall n m : nat,
                        eq nat n
                          (plus (times (div_aux q n m) (S m)) (mod_aux q n m)))
                (n m : nat) =>
              eq_match_nat_type_S nat O
                (fun q0 : nat =>
                 match_bool_type nat O (S (div_aux q0 (minus n (S m)) m))
                   (leb n m)) q
                (fun y : nat =>
                 eq nat n (plus (times y (S m)) (mod_aux (S q) n m)))
                (sym_eq_mod_aux (S q)
                   (fun y : nat -> nat -> nat =>
                    eq nat n
                      (plus
                         (times
                            ((fun m0 n0 : nat =>
                              match_nat_type nat O
                                (fun q0 : nat =>
                                 match_bool_type nat O
                                   (S (div_aux q0 (minus m0 (S n0)) n0))
                                   (leb m0 n0)) (S q)) n m) 
                            (S m)) (y n m)))
                   (sym_eq_filter_nat_type_S (nat -> nat -> nat) mod_aux_body
                      q
                      (fun y : nat -> nat -> nat =>
                       eq nat n
                         (plus
                            (times
                               ((fun m0 n0 : nat =>
                                 match_nat_type nat O
                                   (fun q0 : nat =>
                                    match_bool_type nat O
                                      (S (div_aux q0 (minus m0 (S n0)) n0))
                                      (leb m0 n0)) 
                                   (S q)) n m) (S m)) 
                            (y n m)))
                      (sym_eq_mod_aux_body_S q
                         (fun y : nat -> nat -> nat =>
                          eq nat n
                            (plus
                               (times
                                  ((fun m0 n0 : nat =>
                                    match_nat_type nat O
                                      (fun q0 : nat =>
                                       match_bool_type nat O
                                         (S (div_aux q0 (minus m0 (S n0)) n0))
                                         (leb m0 n0)) 
                                      (S q)) n m) 
                                  (S m)) (y n m)))
                         (sym_eq_match_nat_type_S nat O
                            (fun z : nat =>
                             match_bool_type nat O
                               (S (div_aux z (minus n (S m)) m)) 
                               (leb n m)) q
                            (fun y : nat =>
                             eq nat n
                               (plus (times y (S m))
                                  (match_bool_type nat n
                                     (mod_aux q (minus n (S m)) m) 
                                     (leb n m))))
                            (leb_elim n m
                               (fun __ : bool =>
                                eq nat n
                                  (plus
                                     (times
                                        (match_bool_type nat O
                                           (S (div_aux q (minus n (S m)) m))
                                           __) (S m))
                                     (match_bool_type nat n
                                        (mod_aux q (minus n (S m)) m) __)))
                               (sym_eq_match_bool_type_true nat O
                                  (S (div_aux q (minus n (S m)) m))
                                  (fun x : nat =>
                                   le n m ->
                                   eq nat n
                                     (plus (times x (S m))
                                        (match_bool_type nat n
                                           (mod_aux q (minus n (S m)) m) true)))
                                  (sym_eq_times O
                                     (fun y : nat -> nat =>
                                      le n m ->
                                      eq nat n
                                        (plus (y (S m))
                                           (match_bool_type nat n
                                              (mod_aux q (minus n (S m)) m)
                                              true)))
                                     (sym_eq_filter_nat_type_O 
                                        (nat -> nat) times_body
                                        (fun y : nat -> nat =>
                                         le n m ->
                                         eq nat n
                                           (plus (y (S m))
                                              (match_bool_type nat n
                                                 (mod_aux q (minus n (S m)) m)
                                                 true)))
                                        (sym_eq_times_body_O
                                           (fun y : nat -> nat =>
                                            le n m ->
                                            eq nat n
                                              (plus 
                                                 (y (S m))
                                                 (match_bool_type nat n
                                                 (mod_aux q (minus n (S m)) m)
                                                 true)))
                                           (sym_eq_match_bool_type_true nat n
                                              (mod_aux q (minus n (S m)) m)
                                              (fun y : nat =>
                                               le n m -> eq nat n (plus O y))
                                              (sym_eq_plus O
                                                 (fun y : nat -> nat =>
                                                 le n m -> eq nat n (y n))
                                                 (sym_eq_filter_nat_type_O
                                                 (nat -> nat) plus_body
                                                 (fun y : nat -> nat =>
                                                 le n m -> eq nat n (y n))
                                                 (sym_eq_plus_body_O
                                                 (fun y : nat -> nat =>
                                                 le n m -> eq nat n (y n))
                                                 (fun lenm : le n m =>
                                                 refl nat n)))))))))
                               (sym_eq_match_bool_type_false nat n
                                  (mod_aux q (minus n (S m)) m)
                                  (fun x : nat =>
                                   Not (le n m) ->
                                   eq nat n
                                     (plus
                                        (times
                                           (match_bool_type nat O
                                              (S
                                                 (div_aux q (minus n (S m)) m))
                                              false) 
                                           (S m)) x))
                                  (sym_eq_match_bool_type_false nat O
                                     (S (div_aux q (minus n (S m)) m))
                                     (fun y : nat =>
                                      Not (le n m) ->
                                      eq nat n
                                        (plus (times y (S m))
                                           (mod_aux q (minus n (S m)) m)))
                                     (sym_eq_times
                                        (S (div_aux q (minus n (S m)) m))
                                        (fun y : nat -> nat =>
                                         Not (le n m) ->
                                         eq nat n
                                           (plus (y (S m))
                                              (mod_aux q (minus n (S m)) m)))
                                        (sym_eq_filter_nat_type_S
                                           (nat -> nat) times_body
                                           (div_aux q (minus n (S m)) m)
                                           (fun y : nat -> nat =>
                                            Not (le n m) ->
                                            eq nat n
                                              (plus 
                                                 (y (S m))
                                                 (mod_aux q (minus n (S m)) m)))
                                           (sym_eq_times_body_S
                                              (div_aux q (minus n (S m)) m)
                                              (fun y : nat -> nat =>
                                               Not (le n m) ->
                                               eq nat n
                                                 (plus 
                                                 (y (S m))
                                                 (mod_aux q (minus n (S m)) m)))
                                              (sym_eq_plus 
                                                 (S m)
                                                 (fun y : nat -> nat =>
                                                 Not (le n m) ->
                                                 eq nat n
                                                 (plus
                                                 (y
                                                 (times
                                                 (div_aux q (minus n (S m)) m)
                                                 (S m)))
                                                 (mod_aux q (minus n (S m)) m)))
                                                 (sym_eq_filter_nat_type_S
                                                 (nat -> nat) plus_body m
                                                 (fun y : nat -> nat =>
                                                 Not (le n m) ->
                                                 eq nat n
                                                 (plus
                                                 (y
                                                 (times
                                                 (div_aux q (minus n (S m)) m)
                                                 (S m)))
                                                 (mod_aux q (minus n (S m)) m)))
                                                 (sym_eq_plus_body_S m
                                                 (fun y : nat -> nat =>
                                                 Not (le n m) ->
                                                 eq nat n
                                                 (plus
                                                 (y
                                                 (times
                                                 (div_aux q (minus n (S m)) m)
                                                 (S m)))
                                                 (mod_aux q (minus n (S m)) m)))
                                                 (sym_eq_plus
                                                 (S
                                                 (plus m
                                                 (times
                                                 (div_aux q (minus n (S m)) m)
                                                 (S m))))
                                                 (fun y : nat -> nat =>
                                                 Not (le n m) ->
                                                 eq nat n
                                                 (y
                                                 (mod_aux q (minus n (S m)) m)))
                                                 (sym_eq_filter_nat_type_S
                                                 (nat -> nat) plus_body
                                                 (plus m
                                                 (times
                                                 (div_aux q (minus n (S m)) m)
                                                 (S m)))
                                                 (fun y : nat -> nat =>
                                                 Not (le n m) ->
                                                 eq nat n
                                                 (y
                                                 (mod_aux q (minus n (S m)) m)))
                                                 (sym_eq_plus_body_S
                                                 (plus m
                                                 (times
                                                 (div_aux q (minus n (S m)) m)
                                                 (S m)))
                                                 (fun y : nat -> nat =>
                                                 Not (le n m) ->
                                                 eq nat n
                                                 (y
                                                 (mod_aux q (minus n (S m)) m)))
                                                 (fun lenm : Not (le n m) =>
                                                 eq_ind_r nat
                                                 (plus m
                                                 (plus
                                                 (times
                                                 (div_aux q (minus n (S m)) m)
                                                 (S m))
                                                 (mod_aux q (minus n (S m)) m)))
                                                 (fun x : nat =>
                                                 eq nat n (S x))
                                                 (eq_ind nat 
                                                 (minus n (S m))
                                                 (fun x_1 : nat =>
                                                 eq nat n (S (plus m x_1)))
                                                 (eq_coerc
                                                 (eq nat n
                                                 (plus (minus n (S m)) (S m)))
                                                 (eq nat n
                                                 (S (plus m (minus n (S m)))))
                                                 (plus_minus_m_m n 
                                                 (S m)
                                                 (not_le_to_lt n m lenm))
                                                 (rewrite_r nat
                                                 (pred (minus n m))
                                                 (fun __ : nat =>
                                                 eq Prop
                                                 (eq nat n (plus __ (S m)))
                                                 (eq nat n
                                                 (S (plus m (minus n (S m))))))
                                                 (rewrite_r nat
                                                 (pred (minus n m))
                                                 (fun __ : nat =>
                                                 eq Prop
                                                 (eq nat n
                                                 (plus 
                                                 (pred (minus n m)) 
                                                 (S m)))
                                                 (eq nat n (S (plus m __))))
                                                 (rewrite_r nat
                                                 (plus m
                                                 (S (pred (minus n m))))
                                                 (fun __ : nat =>
                                                 eq Prop
                                                 (eq nat n
                                                 (plus 
                                                 (pred (minus n m)) 
                                                 (S m))) 
                                                 (eq nat n __))
                                                 (rewrite_r nat
                                                 (plus m
                                                 (S (pred (minus n m))))
                                                 (fun __ : nat =>
                                                 eq Prop 
                                                 (eq nat n __)
                                                 (eq nat n
                                                 (plus m
                                                 (S (pred (minus n m))))))
                                                 (refl Prop
                                                 (eq nat n
                                                 (plus m
                                                 (S (pred (minus n m))))))
                                                 (plus 
                                                 (pred (minus n m)) 
                                                 (S m))
                                                 (rewrite_l nat
                                                 (S
                                                 (plus (pred (minus n m)) m))
                                                 (fun __ : nat =>
                                                 eq nat __
                                                 (plus m
                                                 (S (pred (minus n m)))))
                                                 (rewrite_l nat
                                                 (plus m (pred (minus n m)))
                                                 (fun __ : nat =>
                                                 eq nat 
                                                 (S __)
                                                 (plus m
                                                 (S (pred (minus n m)))))
                                                 (plus_n_Sm m
                                                 (pred (minus n m)))
                                                 (plus (pred (minus n m)) m)
                                                 (commutative_plus m
                                                 (pred (minus n m))))
                                                 (plus 
                                                 (pred (minus n m)) 
                                                 (S m))
                                                 (plus_n_Sm
                                                 (pred (minus n m)) m)))
                                                 (S
                                                 (plus m (pred (minus n m))))
                                                 (plus_n_Sm m
                                                 (pred (minus n m))))
                                                 (minus n (S m))
                                                 (eq_minus_S_pred n m))
                                                 (minus n (S m))
                                                 (eq_minus_S_pred n m)))
                                                 (plus
                                                 (times
                                                 (div_aux q (minus n (S m)) m)
                                                 (S m))
                                                 (mod_aux q (minus n (S m)) m))
                                                 (Hind (minus n (S m)) m))
                                                 (plus
                                                 (plus m
                                                 (times
                                                 (div_aux q (minus n (S m)) m)
                                                 (S m)))
                                                 (mod_aux q (minus n (S m)) m))
                                                 (associative_plus m
                                                 (times
                                                 (div_aux q (minus n (S m)) m)
                                                 (S m))
                                                 (mod_aux q (minus n (S m)) m)))))))))))))))))))))))
    p.
Definition div_mod :
  forall n m : nat, eq nat n (plus (times (div n m) m) (mod n m)) :=
  fun n m : nat =>
  match_nat_prop
    (fun __ : nat => eq nat n (plus (times (div n __) __) (mod n __)))
    (sym_eq_times (div n O)
       (fun y : nat -> nat => eq nat n (plus (y O) (mod n O)))
       (sym_eq_match_nat_type_O nat (S n) (fun p : nat => div_aux n n p)
          (fun y : nat =>
           eq nat n
             (plus (filter_nat_type (nat -> nat) times_body y O)
                (match_nat_type nat n (fun p : nat => mod_aux n n p) O)))
          (sym_eq_filter_nat_type_S (nat -> nat) times_body n
             (fun y : nat -> nat => eq nat n (plus (y O) (mod n O)))
             (sym_eq_times_body_S n
                (fun y : nat -> nat => eq nat n (plus (y O) (mod n O)))
                (sym_eq_match_nat_type_O nat n (fun p : nat => mod_aux n n p)
                   (fun y : nat => eq nat n (plus (plus O (times n O)) y))
                   (sym_eq_plus O
                      (fun y : nat -> nat =>
                       eq nat n (plus (y (times n O)) n))
                      (sym_eq_filter_nat_type_O (nat -> nat) plus_body
                         (fun y : nat -> nat =>
                          eq nat n (plus (y (times n O)) n))
                         (sym_eq_plus_body_O
                            (fun y : nat -> nat =>
                             eq nat n (plus (y (times n O)) n))
                            (rewrite_l nat O
                               (fun __ : nat => eq nat n (plus __ n))
                               (rewrite_r nat (plus n O)
                                  (fun __ : nat => eq nat n __)
                                  (rewrite_l nat n
                                     (fun __ : nat => eq nat n __)
                                     (refl nat n) 
                                     (plus n O) (plus_n_O n)) 
                                  (plus O n) (commutative_plus O n))
                               (times n O) (times_n_O n))))))))))
    (fun auto : nat =>
     sym_eq_match_nat_type_S nat (S n) (fun p : nat => div_aux n n p) auto
       (fun y : nat =>
        eq nat n
          (plus (times y (S auto))
             (match_nat_type nat n (fun p : nat => mod_aux n n p) (S auto))))
       (sym_eq_match_nat_type_S nat n (fun p : nat => mod_aux n n p) auto
          (fun y : nat =>
           eq nat n (plus (times (div_aux n n auto) (S auto)) y))
          (rewrite_r nat
             (plus (times (div_aux n n auto) (S auto)) (mod_aux n n auto))
             (fun __ : nat =>
              eq nat __
                (plus (times (div_aux n n auto) (S auto)) (mod_aux n n auto)))
             (refl nat
                (plus (times (div_aux n n auto) (S auto)) (mod_aux n n auto)))
             n (div_aux_mod_aux n n auto)))) m.
Definition eq_times_div_minus_mod :
  forall a b : nat, eq nat (times (div a b) b) (minus a (mod a b)) :=
  fun a b : nat =>
  eq_coerc
    (eq nat (times b (div a b))
       (minus (plus (times b (div a b)) (mod a b)) (mod a b)))
    (eq nat (times (div a b) b) (minus a (mod a b)))
    (minus_plus_m_m (times b (div a b)) (mod a b))
    (rewrite_r nat (plus (mod a b) (times b (div a b)))
       (fun __ : nat =>
        eq Prop (eq nat (times b (div a b)) (minus __ (mod a b)))
          (eq nat (times (div a b) b) (minus a (mod a b))))
       (rewrite_r nat (times b (div a b))
          (fun __ : nat =>
           eq Prop
             (eq nat (times b (div a b))
                (minus (plus (mod a b) (times b (div a b))) (mod a b)))
             (eq nat __ (minus a (mod a b))))
          (rewrite_l nat a
             (fun __ : nat =>
              eq Prop (eq nat (times b (div a b)) (minus __ (mod a b)))
                (eq nat (times b (div a b)) (minus a (mod a b))))
             (refl Prop (eq nat (times b (div a b)) (minus a (mod a b))))
             (plus (mod a b) (times b (div a b)))
             (rewrite_l nat (plus (times b (div a b)) (mod a b))
                (fun __ : nat => eq nat a __)
                (rewrite_l nat (times (div a b) b)
                   (fun __ : nat => eq nat a (plus __ (mod a b)))
                   (div_mod a b) (times b (div a b))
                   (commutative_times (div a b) b))
                (plus (mod a b) (times b (div a b)))
                (commutative_plus (times b (div a b)) (mod a b))))
          (times (div a b) b) (commutative_times (div a b) b))
       (plus (times b (div a b)) (mod a b))
       (commutative_plus (times b (div a b)) (mod a b))).
Inductive div_mod_spec : nat -> nat -> nat -> nat -> Prop :=
    dms_intro :
      forall n m q r, lt r m -> n = q * m + r -> div_mod_spec n m q r.

Theorem div_mod_spec_intro :
  forall n m q r : nat,
  lt r m -> eq nat n (plus (times q m) r) -> div_mod_spec n m q r.
Proof.
  (apply dms_intro).
Qed.

Theorem match_div_mod_spec_prop :
  forall (n m q r : nat) (return_ : Prop),
  (lt r m -> eq nat n (plus (times q m) r) -> return_) ->
  div_mod_spec n m q r -> return_.
Proof.
  (intros **).
  (eapply div_mod_spec_ind).
  (inversion H0; subst).
  (intros **).
  (apply H; easy).
  (eapply H0).
Qed.

Definition div_mod_spec_div_mod :
  forall n m : nat, lt O m -> div_mod_spec n m (div n m) (mod n m) :=
  fun (n m : nat) (posm : lt O m) =>
  div_mod_spec_intro n m (div n m) (mod n m) (lt_mod_m_m n m posm)
    (rewrite_r nat (times m (div n m))
       (fun __ : nat => eq nat n (plus __ (mod n m)))
       (rewrite_r nat (plus (mod n m) (times m (div n m)))
          (fun __ : nat => eq nat n __)
          (rewrite_l nat n (fun __ : nat => eq nat n __) 
             (refl nat n) (plus (mod n m) (times m (div n m)))
             (rewrite_l nat (plus (times m (div n m)) (mod n m))
                (fun __ : nat => eq nat n __)
                (rewrite_l nat (times (div n m) m)
                   (fun __ : nat => eq nat n (plus __ (mod n m)))
                   (div_mod n m) (times m (div n m))
                   (commutative_times (div n m) m))
                (plus (mod n m) (times m (div n m)))
                (commutative_plus (times m (div n m)) (mod n m))))
          (plus (times m (div n m)) (mod n m))
          (commutative_plus (times m (div n m)) (mod n m)))
       (times (div n m) m) (commutative_times (div n m) m)).
Definition let_clause_1078 :
  forall a b q r q1 r1 : nat,
  div_mod_spec a b q r ->
  lt r b ->
  eq nat a (plus (times q b) r) ->
  div_mod_spec a b q1 r1 ->
  lt r1 b ->
  eq nat a (plus (times q1 b) r1) ->
  le q q1 -> lt q q1 -> eq nat a (plus r (times b q)) :=
  fun (a b q r q1 r1 : nat) (_clearme : div_mod_spec a b q r) 
    (ltrb : lt r b) (spec : eq nat a (plus (times q b) r))
    (_clearme0 : div_mod_spec a b q1 r1) (ltr1b : lt r1 b)
    (spec1 : eq nat a (plus (times q1 b) r1)) (leqq1 : le q q1)
    (ltqq1 : lt q q1) =>
  rewrite_l nat (plus (times b q) r) (fun __ : nat => eq nat a __)
    (rewrite_l nat (times q b) (fun __ : nat => eq nat a (plus __ r)) spec
       (times b q) (commutative_times q b)) (plus r (times b q))
    (commutative_plus (times b q) r).
Definition let_clause_1062 :
  forall a b q r q1 r1 : nat,
  div_mod_spec a b q r ->
  lt r b ->
  eq nat a (plus (times q b) r) ->
  div_mod_spec a b q1 r1 ->
  lt r1 b ->
  eq nat a (plus (times q1 b) r1) ->
  Not (le q q1) -> eq nat a (plus r1 (times b q1)) :=
  fun (a b q r q1 r1 : nat) (_clearme : div_mod_spec a b q r) 
    (ltrb : lt r b) (spec : eq nat a (plus (times q b) r))
    (_clearme0 : div_mod_spec a b q1 r1) (ltr1b : lt r1 b)
    (spec1 : eq nat a (plus (times q1 b) r1)) (leqq1 : Not (le q q1)) =>
  rewrite_l nat (plus (times b q1) r1) (fun __ : nat => eq nat a __)
    (rewrite_l nat (times q1 b) (fun __ : nat => eq nat a (plus __ r1)) spec1
       (times b q1) (commutative_times q1 b)) (plus r1 (times b q1))
    (commutative_plus (times b q1) r1).
Definition div_mod_spec_to_eq :
  forall a b q r q1 r1 : nat,
  div_mod_spec a b q r -> div_mod_spec a b q1 r1 -> eq nat q q1 :=
  fun (a b q r q1 r1 : nat) (_clearme : div_mod_spec a b q r) =>
  match_div_mod_spec_prop a b q r (div_mod_spec a b q1 r1 -> eq nat q q1)
    (fun (ltrb : lt r b) (spec : eq nat a (plus (times q b) r))
       (_clearme0 : div_mod_spec a b q1 r1) =>
     match_div_mod_spec_prop a b q1 r1 (eq nat q q1)
       (fun (ltr1b : lt r1 b) (spec1 : eq nat a (plus (times q1 b) r1)) =>
        leb_elim q q1 (fun __ : bool => eq nat q q1)
          (fun leqq1 : le q q1 =>
           match_Or_prop (lt q q1) (eq nat q q1) (eq nat q q1)
             (fun ltqq1 : lt q q1 =>
              falsity (eq nat q q1)
                (absurd (le (S a) a)
                   (lt_to_le_to_lt a (times (S q) b) a
                      (eq_ind_r nat (plus (times q b) r)
                         (fun x : nat => lt x (times (S q) b))
                         (eq_coerc
                            (lt (plus (times q b) r) (plus (times q b) b))
                            (lt (plus (times q b) r) (times (S q) b))
                            (monotonic_lt_plus_r (times q b) r b ltrb)
                            (rewrite_r nat (times b q)
                               (fun __ : nat =>
                                eq Prop (lt (plus __ r) (plus __ b))
                                  (lt (plus __ r) (times (S q) b)))
                               (rewrite_r nat (plus r (times b q))
                                  (fun __ : nat =>
                                   eq Prop
                                     (lt (plus (times b q) r)
                                        (plus (times b q) b))
                                     (lt __ (times (S q) b)))
                                  (rewrite_l nat a
                                     (fun __ : nat =>
                                      eq Prop
                                        (lt (plus (times b q) r)
                                           (plus (times b q) b))
                                        (lt __ (times (S q) b)))
                                     (rewrite_r nat 
                                        (times b (S q))
                                        (fun __ : nat =>
                                         eq Prop
                                           (lt (plus (times b q) r)
                                              (plus (times b q) b)) 
                                           (lt a __))
                                        (rewrite_l nat 
                                           (plus b (times b q))
                                           (fun __ : nat =>
                                            eq Prop
                                              (lt 
                                                 (plus (times b q) r)
                                                 (plus (times b q) b))
                                              (lt a __))
                                           (rewrite_r nat
                                              (plus r (times b q))
                                              (fun __ : nat =>
                                               eq Prop
                                                 (lt __ (plus (times b q) b))
                                                 (lt a (plus b (times b q))))
                                              (rewrite_l nat a
                                                 (fun __ : nat =>
                                                 eq Prop
                                                 (lt __ (plus (times b q) b))
                                                 (lt a (plus b (times b q))))
                                                 (rewrite_r nat
                                                 (plus b (times b q))
                                                 (fun __ : nat =>
                                                 eq Prop 
                                                 (lt a __)
                                                 (lt a (plus b (times b q))))
                                                 (refl Prop
                                                 (lt a (plus b (times b q))))
                                                 (plus (times b q) b)
                                                 (commutative_plus
                                                 (times b q) b))
                                                 (plus r (times b q))
                                                 (let_clause_1078 a b q r q1
                                                 r1 _clearme ltrb spec
                                                 _clearme0 ltr1b spec1 leqq1
                                                 ltqq1)) 
                                              (plus (times b q) r)
                                              (commutative_plus (times b q) r))
                                           (times b (S q)) 
                                           (times_n_Sm b q)) 
                                        (times (S q) b)
                                        (commutative_times (S q) b))
                                     (plus r (times b q))
                                     (let_clause_1078 a b q r q1 r1 _clearme
                                        ltrb spec _clearme0 ltr1b spec1 leqq1
                                        ltqq1)) (plus (times b q) r)
                                  (commutative_plus (times b q) r))
                               (times q b) (commutative_times q b))) a spec)
                      (transitive_le (times (S q) b) 
                         (times q1 b) a
                         (eq_coerc (le (times b (S q)) (times b q1))
                            (le (times (S q) b) (times q1 b))
                            (monotonic_le_times_r b (S q) q1 ltqq1)
                            (rewrite_r nat (times b (S q))
                               (fun __ : nat =>
                                eq Prop (le (times b (S q)) (times b q1))
                                  (le __ (times q1 b)))
                               (rewrite_l nat (plus b (times b q))
                                  (fun __ : nat =>
                                   eq Prop (le (times b (S q)) (times b q1))
                                     (le __ (times q1 b)))
                                  (rewrite_r nat (times b q1)
                                     (fun __ : nat =>
                                      eq Prop
                                        (le (times b (S q)) (times b q1))
                                        (le (plus b (times b q)) __))
                                     (rewrite_l nat 
                                        (plus b (times b q))
                                        (fun __ : nat =>
                                         eq Prop (le __ (times b q1))
                                           (le (plus b (times b q))
                                              (times b q1)))
                                        (refl Prop
                                           (le (plus b (times b q))
                                              (times b q1))) 
                                        (times b (S q)) 
                                        (times_n_Sm b q)) 
                                     (times q1 b) 
                                     (commutative_times q1 b))
                                  (times b (S q)) 
                                  (times_n_Sm b q)) 
                               (times (S q) b) (commutative_times (S q) b)))
                         (eq_coerc (le (times q1 b) (plus (times q1 b) r1))
                            (le (times q1 b) a) (le_plus_n_r r1 (times q1 b))
                            (rewrite_r nat (times b q1)
                               (fun __ : nat =>
                                eq Prop (le __ (plus __ r1)) (le __ a))
                               (rewrite_r nat (plus r1 (times b q1))
                                  (fun __ : nat =>
                                   eq Prop (le (times b q1) __)
                                     (le (times b q1) a))
                                  (rewrite_l nat a
                                     (fun __ : nat =>
                                      eq Prop (le (times b q1) __)
                                        (le (times b q1) a))
                                     (refl Prop (le (times b q1) a))
                                     (plus r1 (times b q1))
                                     (rewrite_l nat 
                                        (plus (times b q1) r1)
                                        (fun __ : nat => eq nat a __)
                                        (rewrite_l nat 
                                           (times q1 b)
                                           (fun __ : nat =>
                                            eq nat a (plus __ r1)) spec1
                                           (times b q1)
                                           (commutative_times q1 b))
                                        (plus r1 (times b q1))
                                        (commutative_plus (times b q1) r1)))
                                  (plus (times b q1) r1)
                                  (commutative_plus (times b q1) r1))
                               (times q1 b) (commutative_times q1 b)))))
                   (not_le_Sn_n a)))
             (fun _x_172 : eq nat q q1 =>
              rewrite_l nat q (fun __ : nat => eq nat q __) 
                (refl nat q) q1 _x_172) (le_to_or_lt_eq q q1 leqq1))
          (fun leqq1 : Not (le q q1) =>
           falsity (eq nat q q1)
             (absurd (le (S a) a)
                (lt_to_le_to_lt a (times (S q1) b) a
                   (eq_ind_r nat (plus (times q1 b) r1)
                      (fun x : nat => lt x (times (S q1) b))
                      (eq_coerc
                         (lt (plus (times q1 b) r1) (plus (times q1 b) b))
                         (lt (plus (times q1 b) r1) (times (S q1) b))
                         (monotonic_lt_plus_r (times q1 b) r1 b ltr1b)
                         (rewrite_r nat (times b q1)
                            (fun __ : nat =>
                             eq Prop (lt (plus __ r1) (plus __ b))
                               (lt (plus __ r1) (times (S q1) b)))
                            (rewrite_r nat (plus r1 (times b q1))
                               (fun __ : nat =>
                                eq Prop
                                  (lt (plus (times b q1) r1)
                                     (plus (times b q1) b))
                                  (lt __ (times (S q1) b)))
                               (rewrite_l nat a
                                  (fun __ : nat =>
                                   eq Prop
                                     (lt (plus (times b q1) r1)
                                        (plus (times b q1) b))
                                     (lt __ (times (S q1) b)))
                                  (rewrite_r nat (times b (S q1))
                                     (fun __ : nat =>
                                      eq Prop
                                        (lt (plus (times b q1) r1)
                                           (plus (times b q1) b)) 
                                        (lt a __))
                                     (rewrite_l nat 
                                        (plus b (times b q1))
                                        (fun __ : nat =>
                                         eq Prop
                                           (lt (plus (times b q1) r1)
                                              (plus (times b q1) b))
                                           (lt a __))
                                        (rewrite_r nat 
                                           (plus r1 (times b q1))
                                           (fun __ : nat =>
                                            eq Prop
                                              (lt __ (plus (times b q1) b))
                                              (lt a (plus b (times b q1))))
                                           (rewrite_l nat a
                                              (fun __ : nat =>
                                               eq Prop
                                                 (lt __ (plus (times b q1) b))
                                                 (lt a (plus b (times b q1))))
                                              (rewrite_r nat
                                                 (plus b (times b q1))
                                                 (fun __ : nat =>
                                                 eq Prop 
                                                 (lt a __)
                                                 (lt a (plus b (times b q1))))
                                                 (refl Prop
                                                 (lt a (plus b (times b q1))))
                                                 (plus (times b q1) b)
                                                 (commutative_plus
                                                 (times b q1) b))
                                              (plus r1 (times b q1))
                                              (let_clause_1062 a b q r q1 r1
                                                 _clearme ltrb spec _clearme0
                                                 ltr1b spec1 leqq1))
                                           (plus (times b q1) r1)
                                           (commutative_plus (times b q1) r1))
                                        (times b (S q1)) 
                                        (times_n_Sm b q1)) 
                                     (times (S q1) b)
                                     (commutative_times (S q1) b))
                                  (plus r1 (times b q1))
                                  (let_clause_1062 a b q r q1 r1 _clearme
                                     ltrb spec _clearme0 ltr1b spec1 leqq1))
                               (plus (times b q1) r1)
                               (commutative_plus (times b q1) r1))
                            (times q1 b) (commutative_times q1 b))) a spec1)
                   (transitive_le (times (S q1) b) 
                      (times q b) a
                      (eq_coerc (le (times b (S q1)) (times b q))
                         (le (times (S q1) b) (times q b))
                         (monotonic_le_times_r b (S q1) q
                            (not_le_to_lt q q1 leqq1))
                         (rewrite_r nat (times b (S q1))
                            (fun __ : nat =>
                             eq Prop (le (times b (S q1)) (times b q))
                               (le __ (times q b)))
                            (rewrite_l nat (plus b (times b q1))
                               (fun __ : nat =>
                                eq Prop (le (times b (S q1)) (times b q))
                                  (le __ (times q b)))
                               (rewrite_r nat (times b q)
                                  (fun __ : nat =>
                                   eq Prop (le (times b (S q1)) (times b q))
                                     (le (plus b (times b q1)) __))
                                  (rewrite_l nat (plus b (times b q1))
                                     (fun __ : nat =>
                                      eq Prop (le __ (times b q))
                                        (le (plus b (times b q1)) (times b q)))
                                     (refl Prop
                                        (le (plus b (times b q1)) (times b q)))
                                     (times b (S q1)) 
                                     (times_n_Sm b q1)) 
                                  (times q b) (commutative_times q b))
                               (times b (S q1)) (times_n_Sm b q1))
                            (times (S q1) b) (commutative_times (S q1) b)))
                      (eq_coerc (le (times q b) (plus (times q b) r))
                         (le (times q b) a) (le_plus_n_r r (times q b))
                         (rewrite_r nat (times b q)
                            (fun __ : nat =>
                             eq Prop (le __ (plus __ r)) (le __ a))
                            (rewrite_r nat (plus r (times b q))
                               (fun __ : nat =>
                                eq Prop (le (times b q) __)
                                  (le (times b q) a))
                               (rewrite_l nat a
                                  (fun __ : nat =>
                                   eq Prop (le (times b q) __)
                                     (le (times b q) a))
                                  (refl Prop (le (times b q) a))
                                  (plus r (times b q))
                                  (rewrite_l nat (plus (times b q) r)
                                     (fun __ : nat => eq nat a __)
                                     (rewrite_l nat 
                                        (times q b)
                                        (fun __ : nat => eq nat a (plus __ r))
                                        spec (times b q)
                                        (commutative_times q b))
                                     (plus r (times b q))
                                     (commutative_plus (times b q) r)))
                               (plus (times b q) r)
                               (commutative_plus (times b q) r)) 
                            (times q b) (commutative_times q b)))))
                (not_le_Sn_n a)))) _clearme0) _clearme.
Definition div_mod_spec_to_eq2 :
  forall a b q r q1 r1 : nat,
  div_mod_spec a b q r -> div_mod_spec a b q1 r1 -> eq nat r r1 :=
  fun (a b q r q1 r1 : nat) (spec : div_mod_spec a b q r)
    (spec1 : div_mod_spec a b q1 r1) =>
  match_div_mod_spec_prop a b q r (eq nat r r1)
    (fun (__ : lt r b) (eqa : eq nat a (plus (times q b) r)) =>
     match_div_mod_spec_prop a b q1 r1 (eq nat r r1)
       (fun (_0 : lt r1 b) (eqa1 : eq nat a (plus (times q1 b) r1)) =>
        injective_plus_r (times q b) r r1
          (rewrite_r nat (times b q)
             (fun __1 : nat => eq nat (plus __1 r) (plus (times q b) r1))
             (rewrite_r nat (plus r (times b q))
                (fun __1 : nat => eq nat __1 (plus (times q b) r1))
                (rewrite_l nat a
                   (fun __1 : nat => eq nat __1 (plus (times q b) r1))
                   (rewrite_r nat (times b q)
                      (fun __1 : nat => eq nat a (plus __1 r1))
                      (rewrite_r nat (plus r1 (times b q))
                         (fun __1 : nat => eq nat a __1)
                         (rewrite_l nat a (fun __1 : nat => eq nat a __1)
                            (refl nat a) (plus r1 (times b q))
                            (rewrite_r nat q1
                               (fun __1 : nat =>
                                eq nat a (plus r1 (times b __1)))
                               (rewrite_l nat (plus (times b q1) r1)
                                  (fun __1 : nat => eq nat a __1)
                                  (rewrite_l nat (times q1 b)
                                     (fun __1 : nat => eq nat a (plus __1 r1))
                                     eqa1 (times b q1)
                                     (commutative_times q1 b))
                                  (plus r1 (times b q1))
                                  (commutative_plus (times b q1) r1)) q
                               (div_mod_spec_to_eq a b q r q1 r1 spec spec1)))
                         (plus (times b q) r1)
                         (commutative_plus (times b q) r1)) 
                      (times q b) (commutative_times q b))
                   (plus r (times b q))
                   (rewrite_l nat (plus (times b q) r)
                      (fun __1 : nat => eq nat a __1)
                      (rewrite_l nat (times q b)
                         (fun __1 : nat => eq nat a (plus __1 r)) eqa
                         (times b q) (commutative_times q b))
                      (plus r (times b q)) (commutative_plus (times b q) r)))
                (plus (times b q) r) (commutative_plus (times b q) r))
             (times q b) (commutative_times q b))) spec1) spec.
Definition div_times :
  forall a b : nat, lt O b -> eq nat (div (times a b) b) a :=
  fun (a b : nat) (posb : lt O b) =>
  div_mod_spec_to_eq (times a b) b (div (times a b) b) 
    (mod (times a b) b) a O (div_mod_spec_div_mod (times a b) b posb)
    (div_mod_spec_intro (times a b) b a O posb
       (rewrite_r nat (plus O (times a b))
          (fun __ : nat => eq nat (times a b) __)
          (rewrite_l nat (times a b) (fun __ : nat => eq nat (times a b) __)
             (refl nat (times a b)) (plus O (times a b))
             (plus_O_n (times a b))) (plus (times a b) O)
          (commutative_plus (times a b) O))).
Definition eq_div_O : forall n m : nat, lt n m -> eq nat (div n m) O :=
  fun (n m : nat) (ltnm : lt n m) =>
  div_mod_spec_to_eq n m (div n m) (mod n m) O n
    (div_mod_spec_div_mod n m (ltn_to_ltO n m ltnm))
    (div_mod_spec_intro n m O n ltnm
       (rewrite_r nat (times m O) (fun __ : nat => eq nat n (plus __ n))
          (rewrite_l nat O (fun __ : nat => eq nat n (plus __ n))
             (rewrite_r nat (plus n O) (fun __ : nat => eq nat n __)
                (rewrite_l nat n (fun __ : nat => eq nat n __) 
                   (refl nat n) (plus n O) (plus_n_O n)) 
                (plus O n) (commutative_plus O n)) 
             (times m O) (times_n_O m)) (times O m) 
          (commutative_times O m))).
Definition mod_O_n : forall n : nat, eq nat (mod O n) O :=
  fun n : nat =>
  sym_eq nat O (mod O n)
    (eq_coerc (eq nat O (mod O n)) (eq nat O (mod O n))
       (le_n_O_to_eq (mod O n)
          (eq_coerc
             (le
                (minus (plus (mod O n) (times n (div O n)))
                   (plus O (times n (div O n))))
                (plus (mod O n) (times n (div O n)))) 
             (le (mod O n) O)
             (minus_le (plus (mod O n) (times n (div O n)))
                (plus O (times n (div O n))))
             (rewrite_r nat (minus (mod O n) O)
                (fun __ : nat =>
                 eq Prop (le __ (plus (mod O n) (times n (div O n))))
                   (le (mod O n) O))
                (rewrite_l nat (mod O n)
                   (fun __ : nat =>
                    eq Prop (le __ (plus (mod O n) (times n (div O n))))
                      (le (mod O n) O))
                   (rewrite_l nat O
                      (fun __ : nat =>
                       eq Prop (le (mod O n) __) (le (mod O n) O))
                      (refl Prop (le (mod O n) O))
                      (plus (mod O n) (times n (div O n)))
                      (rewrite_l nat (plus (times n (div O n)) (mod O n))
                         (fun __ : nat => eq nat O __)
                         (rewrite_l nat (times (div O n) n)
                            (fun __ : nat => eq nat O (plus __ (mod O n)))
                            (div_mod O n) (times n (div O n))
                            (commutative_times (div O n) n))
                         (plus (mod O n) (times n (div O n)))
                         (commutative_plus (times n (div O n)) (mod O n))))
                   (minus (mod O n) O) (minus_n_O (mod O n)))
                (minus (plus (mod O n) (times n (div O n)))
                   (plus O (times n (div O n))))
                (minus_plus_plus_l (mod O n) O (times n (div O n))))))
       (refl Prop (eq nat O (mod O n)))).
Definition sameF_upto :
  forall A : Type, nat -> (nat -> A) -> (nat -> A) -> Prop :=
  fun (A : Type) (k : nat) (f g : nat -> A) =>
  forall i : nat, lt i k -> eq A (f i) (g i).
Definition sameF_p :
  forall A : Type, nat -> (nat -> bool) -> (nat -> A) -> (nat -> A) -> Prop :=
  fun (A : Type) (k : nat) (p : nat -> bool) (f g : nat -> A) =>
  forall i : nat, lt i k -> eq bool (p i) true -> eq A (f i) (g i).
Definition sameF_upto_le :
  forall (A : Type) (f g : nat -> A) (n m : nat),
  le n m -> sameF_upto A m f g -> sameF_upto A n f g :=
  fun (A : Type) (f g : nat -> A) (n m : nat) (lenm : le n m)
    (samef : sameF_upto A m f g) (i : nat) (ltin : lt i n) =>
  samef i (lt_to_le_to_lt i n m ltin lenm).
Definition sameF_p_le :
  forall (A : Type) (p : nat -> bool) (f g : nat -> A) (n m : nat),
  le n m -> sameF_p A m p f g -> sameF_p A n p f g :=
  fun (A : Type) (p : nat -> bool) (f g : nat -> A) 
    (n m : nat) (lenm : le n m) (samef : sameF_p A m p f g) 
    (i : nat) (ltin : lt i n) (pi : eq bool (p i) true) =>
  samef i (lt_to_le_to_lt i n m ltin lenm)
    (rewrite_r bool true (fun __ : bool => eq bool __ true) 
       (refl bool true) (p i) pi).

Fixpoint bigop (H : Type) (n : nat) :
(nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H :=
  fun p nil op f =>
  match n with
  | 0 => nil
  | Datatypes.S n =>
      if p n then op (f n) (bigop H n p nil op f) else bigop H n p nil op f
  end.

Definition bigop_body :
  forall H : Type,
  nat -> (nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H := bigop.
Theorem eq_bigop_O :
  forall H : Type,
  leibniz ((nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H)
    (bigop H O) (bigop_body H O).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.
Definition sym_eq_bigop_O :
  forall H : Type,
  leibniz ((nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H)
    (bigop_body H O) (bigop H O) :=
  fun H : Type =>
  sym_leibniz ((nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H)
    (bigop H O) (bigop_body H O) (eq_bigop_O H).
Theorem eq_bigop_S :
  forall (H : Type) (n : nat),
  leibniz ((nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H)
    (bigop H (S n)) (bigop_body H (S n)).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.
Definition sym_eq_bigop_S :
  forall (H : Type) (n : nat),
  leibniz ((nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H)
    (bigop_body H (S n)) (bigop H (S n)) :=
  fun (H : Type) (n : nat) =>
  sym_leibniz ((nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H)
    (bigop H (S n)) (bigop_body H (S n)) (eq_bigop_S H n).
Theorem eq_bigop_body_O :
  forall H : Type,
  leibniz ((nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H)
    (bigop_body H O)
    (fun (p : nat -> bool) (nil : H) (op : H -> H -> H) (f : nat -> H) => nil).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.
Definition sym_eq_bigop_body_O :
  forall H : Type,
  leibniz ((nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H)
    (fun (p : nat -> bool) (nil : H) (op : H -> H -> H) (f : nat -> H) => nil)
    (bigop_body H O) :=
  fun H : Type =>
  sym_leibniz ((nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H)
    (bigop_body H O)
    (fun (p : nat -> bool) (nil : H) (op : H -> H -> H) (f : nat -> H) => nil)
    (eq_bigop_body_O H).
Theorem eq_bigop_body_S :
  forall (H : Type) (n : nat),
  leibniz ((nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H)
    (bigop_body H (S n))
    (fun (p : nat -> bool) (nil : H) (op : H -> H -> H) (f : nat -> H) =>
     match_bool_type H (op (f n) (bigop H n p nil op f))
       (bigop H n p nil op f) (p n)).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.
Definition sym_eq_bigop_body_S :
  forall (H : Type) (n : nat),
  leibniz ((nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H)
    (fun (p : nat -> bool) (nil : H) (op : H -> H -> H) (f : nat -> H) =>
     match_bool_type H (op (f n) (bigop H n p nil op f))
       (bigop H n p nil op f) (p n)) (bigop_body H (S n)) :=
  fun (H : Type) (n : nat) =>
  sym_leibniz ((nat -> bool) -> H -> (H -> H -> H) -> (nat -> H) -> H)
    (bigop_body H (S n))
    (fun (p : nat -> bool) (nil : H) (op : H -> H -> H) (f : nat -> H) =>
     match_bool_type H (op (f n) (bigop H n p nil op f))
       (bigop H n p nil op f) (p n)) (eq_bigop_body_S H n).
Definition bigop_Strue :
  forall (B : Type) (k : nat) (p : nat -> bool) (nil : B) 
    (op : B -> B -> B) (f : nat -> B),
  eq bool (p k) true ->
  eq B (bigop B (S k) (fun i : nat => p i) nil op (fun i : nat => f i))
    (op (f k) (bigop B k (fun i : nat => p i) nil op (fun i : nat => f i))) :=
  fun (B : Type) (k : nat) (p : nat -> bool) (nil : B) 
    (op : B -> B -> B) (f : nat -> B) =>
  sym_eq_bigop_S B k
    (fun y : (nat -> bool) -> B -> (B -> B -> B) -> (nat -> B) -> B =>
     eq bool (p k) true ->
     eq B (y (fun i : nat => p i) nil op (fun i : nat => f i))
       (op (f k) (bigop B k (fun i : nat => p i) nil op (fun i : nat => f i))))
    (sym_eq_bigop_body_S B k
       (fun y : (nat -> bool) -> B -> (B -> B -> B) -> (nat -> B) -> B =>
        eq bool (p k) true ->
        eq B (y (fun i : nat => p i) nil op (fun i : nat => f i))
          (op (f k)
             (bigop B k (fun i : nat => p i) nil op (fun i : nat => f i))))
       (fun H : eq bool (p k) true =>
        eq_ind_r bool true
          (fun x : bool =>
           eq B
             (match_bool_type B
                (op (f k)
                   (bigop B k (fun i : nat => p i) nil op
                      (fun i : nat => f i)))
                (bigop B k (fun i : nat => p i) nil op (fun i : nat => f i))
                x)
             (op (f k)
                (bigop B k (fun i : nat => p i) nil op (fun i : nat => f i))))
          (eq_match_bool_type_true B
             (op (f k)
                (bigop B k (fun i : nat => p i) nil op (fun i : nat => f i)))
             (bigop B k (fun i : nat => p i) nil op (fun i : nat => f i))
             (fun y : B =>
              eq B
                (match_bool_type B
                   (op (f k)
                      (bigop B k (fun i : nat => p i) nil op
                         (fun i : nat => f i)))
                   (bigop B k (fun i : nat => p i) nil op
                      (fun i : nat => f i)) true) y)
             (refl B
                (match_bool_type B
                   (op (f k)
                      (bigop B k (fun i : nat => p i) nil op
                         (fun i : nat => f i)))
                   (bigop B k (fun i : nat => p i) nil op
                      (fun i : nat => f i)) true))) 
          (p k) H)).
Definition bigop_Sfalse :
  forall (B : Type) (k : nat) (p : nat -> bool) (nil : B) 
    (op : B -> B -> B) (f : nat -> B),
  eq bool (p k) false ->
  eq B (bigop B (S k) (fun i : nat => p i) nil op (fun i : nat => f i))
    (bigop B k (fun i : nat => p i) nil op (fun i : nat => f i)) :=
  fun (B : Type) (k : nat) (p : nat -> bool) (nil : B) 
    (op : B -> B -> B) (f : nat -> B) =>
  sym_eq_bigop_S B k
    (fun y : (nat -> bool) -> B -> (B -> B -> B) -> (nat -> B) -> B =>
     eq bool (p k) false ->
     eq B (y (fun i : nat => p i) nil op (fun i : nat => f i))
       (bigop B k (fun i : nat => p i) nil op (fun i : nat => f i)))
    (sym_eq_bigop_body_S B k
       (fun y : (nat -> bool) -> B -> (B -> B -> B) -> (nat -> B) -> B =>
        eq bool (p k) false ->
        eq B (y (fun i : nat => p i) nil op (fun i : nat => f i))
          (bigop B k (fun i : nat => p i) nil op (fun i : nat => f i)))
       (fun H : eq bool (p k) false =>
        eq_ind_r bool false
          (fun x : bool =>
           eq B
             (match_bool_type B
                (op (f k)
                   (bigop B k (fun i : nat => p i) nil op
                      (fun i : nat => f i)))
                (bigop B k (fun i : nat => p i) nil op (fun i : nat => f i))
                x)
             (bigop B k (fun i : nat => p i) nil op (fun i : nat => f i)))
          (eq_match_bool_type_false B
             (op (f k)
                (bigop B k (fun i : nat => p i) nil op (fun i : nat => f i)))
             (bigop B k (fun i : nat => p i) nil op (fun i : nat => f i))
             (fun y : B =>
              eq B
                (match_bool_type B
                   (op (f k)
                      (bigop B k (fun i : nat => p i) nil op
                         (fun i : nat => f i)))
                   (bigop B k (fun i : nat => p i) nil op
                      (fun i : nat => f i)) false) y)
             (refl B
                (match_bool_type B
                   (op (f k)
                      (bigop B k (fun i : nat => p i) nil op
                         (fun i : nat => f i)))
                   (bigop B k (fun i : nat => p i) nil op
                      (fun i : nat => f i)) false))) 
          (p k) H)).
Definition same_bigop :
  forall (B : Type) (k : nat) (p1 p2 : nat -> bool) 
    (nil : B) (op : B -> B -> B) (f g : nat -> B),
  sameF_upto bool k p1 p2 ->
  sameF_p B k p1 f g ->
  eq B (bigop B k (fun i : nat => p1 i) nil op (fun i : nat => f i))
    (bigop B k (fun i : nat => p2 i) nil op (fun i : nat => g i)) :=
  fun (B : Type) (k : nat) (p1 p2 : nat -> bool) (nil : B) 
    (op : B -> B -> B) (f g : nat -> B) =>
  nat_ind
    (fun _x_365 : nat =>
     sameF_upto bool _x_365 p1 p2 ->
     sameF_p B _x_365 p1 f g ->
     eq B (bigop B _x_365 (fun i : nat => p1 i) nil op (fun i : nat => f i))
       (bigop B _x_365 (fun i : nat => p2 i) nil op (fun i : nat => g i)))
    (sym_eq_bigop_O B
       (fun y : (nat -> bool) -> B -> (B -> B -> B) -> (nat -> B) -> B =>
        sameF_upto bool O p1 p2 ->
        sameF_p B O p1 f g ->
        eq B (bigop B O (fun i : nat => p1 i) nil op (fun i : nat => f i))
          (y (fun i : nat => p2 i) nil op (fun i : nat => g i)))
       (sym_eq_bigop_body_O B
          (fun y : (nat -> bool) -> B -> (B -> B -> B) -> (nat -> B) -> B =>
           sameF_upto bool O p1 p2 ->
           sameF_p B O p1 f g ->
           eq B (bigop B O (fun i : nat => p1 i) nil op (fun i : nat => f i))
             (y (fun i : nat => p2 i) nil op (fun i : nat => g i)))
          (eq_bigop_body_O B
             (fun y : (nat -> bool) -> B -> (B -> B -> B) -> (nat -> B) -> B
              =>
              sameF_upto bool O p1 p2 ->
              sameF_p B O p1 f g ->
              eq B
                (bigop B O (fun i : nat => p1 i) nil op (fun i : nat => f i))
                (y (fun i : nat => p1 i) nil op (fun i : nat => f i)))
             (eq_bigop_O B
                (fun
                   y : (nat -> bool) -> B -> (B -> B -> B) -> (nat -> B) -> B
                 =>
                 sameF_upto bool O p1 p2 ->
                 sameF_p B O p1 f g ->
                 eq B
                   (bigop B O (fun i : nat => p1 i) nil op
                      (fun i : nat => f i))
                   (y (fun i : nat => p1 i) nil op (fun i : nat => f i)))
                (fun (auto : sameF_upto bool O p1 p2)
                   (auto' : sameF_p B O p1 f g) =>
                 refl B
                   (bigop B O (fun i : nat => p1 i) nil op
                      (fun i : nat => f i)))))))
    (fun n : nat =>
     sym_eq_bigop_S B n
       (fun y : (nat -> bool) -> B -> (B -> B -> B) -> (nat -> B) -> B =>
        (sameF_upto bool n p1 p2 ->
         sameF_p B n p1 f g ->
         eq B (bigop B n (fun i : nat => p1 i) nil op (fun i : nat => f i))
           (bigop B n (fun i : nat => p2 i) nil op (fun i : nat => g i))) ->
        sameF_upto bool (S n) p1 p2 ->
        sameF_p B (S n) p1 f g ->
        eq B
          (bigop B (S n) (fun i : nat => p1 i) nil op (fun i : nat => f i))
          (y (fun i : nat => p2 i) nil op (fun i : nat => g i)))
       (sym_eq_bigop_S B n
          (fun y : (nat -> bool) -> B -> (B -> B -> B) -> (nat -> B) -> B =>
           (sameF_upto bool n p1 p2 ->
            sameF_p B n p1 f g ->
            eq B
              (bigop B n (fun i : nat => p1 i) nil op (fun i : nat => f i))
              (bigop B n (fun i : nat => p2 i) nil op (fun i : nat => g i))) ->
           sameF_upto bool (S n) p1 p2 ->
           sameF_p B (S n) p1 f g ->
           eq B (y (fun i : nat => p1 i) nil op (fun i : nat => f i))
             (bigop_body B (S n) (fun i : nat => p2 i) nil op
                (fun i : nat => g i)))
          (sym_eq_bigop_body_S B n
             (fun y : (nat -> bool) -> B -> (B -> B -> B) -> (nat -> B) -> B
              =>
              (sameF_upto bool n p1 p2 ->
               sameF_p B n p1 f g ->
               eq B
                 (bigop B n (fun i : nat => p1 i) nil op (fun i : nat => f i))
                 (bigop B n (fun i : nat => p2 i) nil op (fun i : nat => g i))) ->
              sameF_upto bool (S n) p1 p2 ->
              sameF_p B (S n) p1 f g ->
              eq B (y (fun i : nat => p1 i) nil op (fun i : nat => f i))
                (bigop_body B (S n) (fun i : nat => p2 i) nil op
                   (fun i : nat => g i)))
             (sym_eq_bigop_body_S B n
                (fun
                   y : (nat -> bool) -> B -> (B -> B -> B) -> (nat -> B) -> B
                 =>
                 (sameF_upto bool n p1 p2 ->
                  sameF_p B n p1 f g ->
                  eq B
                    (bigop B n (fun i : nat => p1 i) nil op
                       (fun i : nat => f i))
                    (bigop B n (fun i : nat => p2 i) nil op
                       (fun i : nat => g i))) ->
                 sameF_upto bool (S n) p1 p2 ->
                 sameF_p B (S n) p1 f g ->
                 eq B
                   ((fun (p : nat -> bool) (nil : B) 
                       (op : B -> B -> B) (f : nat -> B) =>
                     match_bool_type B (op (f n) (bigop B n p nil op f))
                       (bigop B n p nil op f) (p n)) 
                      (fun i : nat => p1 i) nil op 
                      (fun i : nat => f i))
                   (y (fun i : nat => p2 i) nil op (fun i : nat => g i)))
                (fun
                   (Hind : sameF_upto bool n p1 p2 ->
                           sameF_p B n p1 f g ->
                           eq B
                             (bigop B n (fun i : nat => p1 i) nil op
                                (fun i : nat => f i))
                             (bigop B n (fun i : nat => p2 i) nil op
                                (fun i : nat => g i)))
                   (samep : sameF_upto bool (S n) p1 p2)
                   (samef : sameF_p B (S n) p1 f g) =>
                 eq_ind_r B
                   (bigop B n (fun i : nat => p2 i) nil op
                      (fun i : nat => g i))
                   (fun x : B =>
                    eq B (match_bool_type B (op (f n) x) x (p1 n))
                      (match_bool_type B
                         (op (g n)
                            (bigop B n (fun i : nat => p2 i) nil op
                               (fun i : nat => g i)))
                         (bigop B n (fun i : nat => p2 i) nil op
                            (fun i : nat => g i)) 
                         (p2 n)))
                   (eq_ind bool (p1 n)
                      (fun x_1 : bool =>
                       eq B
                         (match_bool_type B
                            (op (f n)
                               (bigop B n (fun i : nat => p2 i) nil op
                                  (fun i : nat => g i)))
                            (bigop B n (fun i : nat => p2 i) nil op
                               (fun i : nat => g i)) 
                            (p1 n))
                         (match_bool_type B
                            (op (g n)
                               (bigop B n (fun i : nat => p2 i) nil op
                                  (fun i : nat => g i)))
                            (bigop B n (fun i : nat => p2 i) nil op
                               (fun i : nat => g i)) x_1))
                      (match_Or_prop (eq bool (p1 n) true)
                         (eq bool (p1 n) false)
                         (eq B
                            (match_bool_type B
                               (op (f n)
                                  (bigop B n (fun i : nat => p2 i) nil op
                                     (fun i : nat => g i)))
                               (bigop B n (fun i : nat => p2 i) nil op
                                  (fun i : nat => g i)) 
                               (p1 n))
                            (match_bool_type B
                               (op (g n)
                                  (bigop B n (fun i : nat => p2 i) nil op
                                     (fun i : nat => g i)))
                               (bigop B n (fun i : nat => p2 i) nil op
                                  (fun i : nat => g i)) 
                               (p1 n)))
                         (fun H1 : eq bool (p1 n) true =>
                          eq_ind_r bool true
                            (fun x : bool =>
                             eq B
                               (match_bool_type B
                                  (op (f n)
                                     (bigop B n (fun i : nat => p2 i) nil op
                                        (fun i : nat => g i)))
                                  (bigop B n (fun i : nat => p2 i) nil op
                                     (fun i : nat => g i)) x)
                               (match_bool_type B
                                  (op (g n)
                                     (bigop B n (fun i : nat => p2 i) nil op
                                        (fun i : nat => g i)))
                                  (bigop B n (fun i : nat => p2 i) nil op
                                     (fun i : nat => g i)) x))
                            (sym_eq_match_bool_type_true B
                               (op (f n)
                                  (bigop B n (fun i : nat => p2 i) nil op
                                     (fun i : nat => g i)))
                               (bigop B n (fun i : nat => p2 i) nil op
                                  (fun i : nat => g i))
                               (fun y : B =>
                                eq B y
                                  (match_bool_type B
                                     (op (g n)
                                        (bigop B n 
                                           (fun i : nat => p2 i) nil op
                                           (fun i : nat => g i)))
                                     (bigop B n (fun i : nat => p2 i) nil op
                                        (fun i : nat => g i)) true))
                               (sym_eq_match_bool_type_true B
                                  (op (g n)
                                     (bigop B n (fun i : nat => p2 i) nil op
                                        (fun i : nat => g i)))
                                  (bigop B n (fun i : nat => p2 i) nil op
                                     (fun i : nat => g i))
                                  (fun y : B =>
                                   eq B
                                     (op (f n)
                                        (bigop B n 
                                           (fun i : nat => p2 i) nil op
                                           (fun i : nat => g i))) y)
                                  (eq_ind B (f n)
                                     (fun x_1 : B =>
                                      eq B
                                        (op (f n)
                                           (bigop B n 
                                              (fun i : nat => p2 i) nil op
                                              (fun i : nat => g i)))
                                        (op x_1
                                           (bigop B n 
                                              (fun i : nat => p2 i) nil op
                                              (fun i : nat => g i))))
                                     (refl B
                                        (op (f n)
                                           (bigop B n 
                                              (fun i : nat => p2 i) nil op
                                              (fun i : nat => g i)))) 
                                     (g n) (samef n (le_n (S n)) H1))))
                            (p1 n) H1)
                         (fun H1 : eq bool (p1 n) false =>
                          eq_ind_r bool false
                            (fun x : bool =>
                             eq B
                               (match_bool_type B
                                  (op (f n)
                                     (bigop B n (fun i : nat => p2 i) nil op
                                        (fun i : nat => g i)))
                                  (bigop B n (fun i : nat => p2 i) nil op
                                     (fun i : nat => g i)) x)
                               (match_bool_type B
                                  (op (g n)
                                     (bigop B n (fun i : nat => p2 i) nil op
                                        (fun i : nat => g i)))
                                  (bigop B n (fun i : nat => p2 i) nil op
                                     (fun i : nat => g i)) x))
                            (sym_eq_match_bool_type_false B
                               (op (f n)
                                  (bigop B n (fun i : nat => p2 i) nil op
                                     (fun i : nat => g i)))
                               (bigop B n (fun i : nat => p2 i) nil op
                                  (fun i : nat => g i))
                               (fun y : B =>
                                eq B y
                                  (match_bool_type B
                                     (op (g n)
                                        (bigop B n 
                                           (fun i : nat => p2 i) nil op
                                           (fun i : nat => g i)))
                                     (bigop B n (fun i : nat => p2 i) nil op
                                        (fun i : nat => g i)) false))
                               (sym_eq_match_bool_type_false B
                                  (op (g n)
                                     (bigop B n (fun i : nat => p2 i) nil op
                                        (fun i : nat => g i)))
                                  (bigop B n (fun i : nat => p2 i) nil op
                                     (fun i : nat => g i))
                                  (fun y : B =>
                                   eq B
                                     (bigop B n (fun i : nat => p2 i) nil op
                                        (fun i : nat => g i)) y)
                                  (refl B
                                     (bigop B n (fun i : nat => p2 i) nil op
                                        (fun i : nat => g i))))) 
                            (p1 n) H1) (true_or_false (p1 n))) 
                      (p2 n) (samep n (le_n (S n))))
                   (bigop B n (fun i : nat => p1 i) nil op
                      (fun i : nat => f i))
                   (Hind
                      (sameF_upto_le bool p1 p2 n 
                         (S n)
                         (eq_coerc (le (pred (S n)) (S n)) 
                            (le n (S n)) (le_pred_n (S n))
                            (rewrite_l nat n
                               (fun __ : nat =>
                                eq Prop (le __ (S n)) (le n (S n)))
                               (refl Prop (le n (S n))) 
                               (pred (S n)) (pred_Sn n))) samep)
                      (sameF_p_le B p1 f g n (S n)
                         (eq_coerc (le (pred (S n)) (S n)) 
                            (le n (S n)) (le_pred_n (S n))
                            (rewrite_l nat n
                               (fun __ : nat =>
                                eq Prop (le __ (S n)) (le n (S n)))
                               (refl Prop (le n (S n))) 
                               (pred (S n)) (pred_Sn n))) samef))))))) k.
Definition bigop_false :
  forall (B : Type) (n : nat) (nil : B) (op : B -> B -> B) (f : nat -> B),
  eq B (bigop B n (fun i : nat => false) nil op (fun i : nat => f i)) nil :=
  fun (B : Type) (n : nat) (nil : B) (op : B -> B -> B) (f : nat -> B) =>
  nat_ind
    (fun _x_365 : nat =>
     eq B (bigop B _x_365 (fun i : nat => false) nil op (fun i : nat => f i))
       nil)
    (eq_bigop_body_O B
       (fun y : (nat -> bool) -> B -> (B -> B -> B) -> (nat -> B) -> B =>
        eq B (bigop B O (fun i : nat => false) nil op (fun i : nat => f i))
          (y (fun i : nat => false) nil op (fun i : nat => f i)))
       (eq_bigop_O B
          (fun y : (nat -> bool) -> B -> (B -> B -> B) -> (nat -> B) -> B =>
           eq B
             (bigop B O (fun i : nat => false) nil op (fun i : nat => f i))
             (y (fun i : nat => false) nil op (fun i : nat => f i)))
          (refl B
             (bigop B O (fun i : nat => false) nil op (fun i : nat => f i)))))
    (fun (n1 : nat)
       (Hind : eq B
                 (bigop B n1 (fun i : nat => false) nil op
                    (fun i : nat => f i)) nil) =>
     eq_ind_r B
       (bigop B n1 (fun i : nat => false) nil op (fun i : nat => f i))
       (fun x : B => eq B x nil)
       (rewrite_r B nil (fun __ : B => eq B __ nil) 
          (refl B nil)
          (bigop B n1 (fun i : nat => false) nil op (fun i : nat => f i))
          Hind)
       (bigop B (S n1) (fun i : nat => false) nil op (fun i : nat => f i))
       (bigop_Sfalse B n1 (fun __ : nat => false) nil op f (refl bool false)))
    n.

Inductive Aop : forall A : Type, A -> Prop :=
    mk_aop :
      forall A nil op,
      (forall a, eq A (op nil a) a) ->
      (forall a, eq A (op a nil) a) ->
      (forall a b c, eq A (op a (op b c)) (op (op a b) c)) -> Aop A nil.

Theorem mk_Aop :
  forall (A : Type) (nil : A) (op : A -> A -> A),
  (forall a : A, eq A (op nil a) a) ->
  (forall a : A, eq A (op a nil) a) ->
  (forall a b c : A, eq A (op a (op b c)) (op (op a b) c)) -> Aop A nil.
Proof.
  (apply mk_aop).
Qed.

Definition assoc :
  forall a b c : nat, eq nat (times a (times b c)) (times (times a b) c) :=
  fun a b c : nat =>
  sym_eq nat (times (times a b) c) (times a (times b c))
    (associative_times a b c).
Definition timesA : Aop nat (S O) :=
  mk_Aop nat (S O) times
    (fun a : nat =>
     sym_eq_times (S O) (fun y : nat -> nat => eq nat (y a) a)
       (sym_eq_filter_nat_type_S (nat -> nat) times_body O
          (fun y : nat -> nat => eq nat (y a) a)
          (sym_eq_times_body_S O (fun y : nat -> nat => eq nat (y a) a)
             (sym_eq_times O (fun y : nat -> nat => eq nat (plus a (y a)) a)
                (sym_eq_filter_nat_type_O (nat -> nat) times_body
                   (fun y : nat -> nat => eq nat (plus a (y a)) a)
                   (sym_eq_times_body_O
                      (fun y : nat -> nat => eq nat (plus a (y a)) a)
                      (sym_eq nat a (plus a O) (plus_n_O a))))))))
    (fun n : nat => sym_eq nat n (times n (S O)) (times_n_1 n))
    (fun a b c : nat =>
     sym_eq nat (times (times a b) c) (times a (times b c))
       (associative_times a b c)).
Definition bigop_I_gen :
  forall (a b : nat) (p : nat -> bool) (f : nat -> nat),
  le a b ->
  eq nat
    (bigop nat (minus b a) (fun i : nat => p (plus i a)) 
       (S O) times (fun i : nat => f (plus i a)))
    (bigop nat b (fun i : nat => andb (leb a i) (p i)) 
       (S O) times (fun i : nat => f i)) :=
  fun a b : nat =>
  nat_ind
    (fun _x_365 : nat =>
     forall (p : nat -> bool) (f : nat -> nat),
     le a _x_365 ->
     eq nat
       (bigop nat (minus _x_365 a) (fun i : nat => p (plus i a)) 
          (S O) times (fun i : nat => f (plus i a)))
       (bigop nat _x_365 (fun i : nat => andb (leb a i) (p i)) 
          (S O) times (fun i : nat => f i)))
    (fun (p : nat -> bool) (f : nat -> nat) =>
     sym_eq_bigop_O nat
       (fun
          y : (nat -> bool) ->
              nat -> (nat -> nat -> nat) -> (nat -> nat) -> nat =>
        le a O ->
        eq nat
          (bigop nat (minus O a) (fun i : nat => p (plus i a)) 
             (S O) times (fun i : nat => f (plus i a)))
          (y (fun i : nat => andb (leb a i) (p i)) 
             (S O) times (fun i : nat => f i)))
       (sym_eq_bigop_body_O nat
          (fun
             y : (nat -> bool) ->
                 nat -> (nat -> nat -> nat) -> (nat -> nat) -> nat =>
           le a O ->
           eq nat
             (bigop nat (minus O a) (fun i : nat => p (plus i a)) 
                (S O) times (fun i : nat => f (plus i a)))
             (y (fun i : nat => andb (leb a i) (p i)) 
                (S O) times (fun i : nat => f i)))
          (eq_bigop_body_O nat
             (fun
                y : (nat -> bool) ->
                    nat -> (nat -> nat -> nat) -> (nat -> nat) -> nat =>
              le a O ->
              eq nat
                (bigop nat (minus O a) (fun i : nat => p (plus i a)) 
                   (S O) times (fun i : nat => f (plus i a)))
                (y (fun i : nat => p (plus i a)) (S O) times
                   (fun i : nat => f (plus i a))))
             (eq_bigop_O nat
                (fun
                   y : (nat -> bool) ->
                       nat -> (nat -> nat -> nat) -> (nat -> nat) -> nat =>
                 le a O ->
                 eq nat
                   (bigop nat (minus O a) (fun i : nat => p (plus i a)) 
                      (S O) times (fun i : nat => f (plus i a)))
                   (y (fun i : nat => p (plus i a)) 
                      (S O) times (fun i : nat => f (plus i a))))
                (eq_minus_body_O
                   (fun y : nat -> nat =>
                    le a O ->
                    eq nat
                      (bigop nat (minus O a) (fun i : nat => p (plus i a))
                         (S O) times (fun i : nat => f (plus i a)))
                      (bigop nat (y a) (fun i : nat => p (plus i a)) 
                         (S O) times (fun i : nat => f (plus i a))))
                   (eq_filter_nat_type_O (nat -> nat) minus_body
                      (fun y : nat -> nat =>
                       le a O ->
                       eq nat
                         (bigop nat (minus O a) (fun i : nat => p (plus i a))
                            (S O) times (fun i : nat => f (plus i a)))
                         (bigop nat (y a) (fun i : nat => p (plus i a)) 
                            (S O) times (fun i : nat => f (plus i a))))
                      (eq_minus O
                         (fun y : nat -> nat =>
                          le a O ->
                          eq nat
                            (bigop nat (minus O a)
                               (fun i : nat => p (plus i a)) 
                               (S O) times (fun i : nat => f (plus i a)))
                            (bigop nat (y a) (fun i : nat => p (plus i a))
                               (S O) times (fun i : nat => f (plus i a))))
                         (fun auto : le a O =>
                          refl nat
                            (bigop nat (minus O a)
                               (fun i : nat => p (plus i a)) 
                               (S O) times (fun i : nat => f (plus i a)))))))))))
    (fun (b0 : nat)
       (Hind : forall (p : nat -> bool) (f : nat -> nat),
               le a b0 ->
               eq nat
                 (bigop nat (minus b0 a) (fun i : nat => p (plus i a)) 
                    (S O) times (fun i : nat => f (plus i a)))
                 (bigop nat b0 (fun i : nat => andb (leb a i) (p i)) 
                    (S O) times (fun i : nat => f i))) 
       (p : nat -> bool) (f : nat -> nat) (lea : le a (S b0)) =>
     match_Or_prop (lt a (S b0)) (eq nat a (S b0))
       (eq nat
          (bigop nat (minus (S b0) a) (fun i : nat => p (plus i a)) 
             (S O) times (fun i : nat => f (plus i a)))
          (bigop nat (S b0) (fun i : nat => andb (leb a i) (p i)) 
             (S O) times (fun i : nat => f i)))
       (fun Ha : lt a (S b0) =>
        match_Or_prop (eq bool (p b0) true) (eq bool (p b0) false)
          (eq nat
             (bigop nat (minus (S b0) a) (fun i : nat => p (plus i a)) 
                (S O) times (fun i : nat => f (plus i a)))
             (bigop nat (S b0) (fun i : nat => andb (leb a i) (p i)) 
                (S O) times (fun i : nat => f i)))
          (fun Hcase : eq bool (p b0) true =>
           eq_ind_r nat
             (times (f b0)
                (bigop nat b0 (fun i : nat => andb (leb a i) (p i)) 
                   (S O) times (fun i : nat => f i)))
             (fun x : nat =>
              eq nat
                (bigop nat (minus (S b0) a) (fun i : nat => p (plus i a))
                   (S O) times (fun i : nat => f (plus i a))) x)
             (eq_ind_r nat (S (minus b0 a))
                (fun x : nat =>
                 eq nat
                   (bigop nat x (fun i : nat => p (plus i a)) 
                      (S O) times (fun i : nat => f (plus i a)))
                   (times (f b0)
                      (bigop nat b0 (fun i : nat => andb (leb a i) (p i))
                         (S O) times (fun i : nat => f i))))
                (eq_ind_r nat
                   (times (f (plus (minus b0 a) a))
                      (bigop nat (minus b0 a) (fun i : nat => p (plus i a))
                         (S O) times (fun i : nat => f (plus i a))))
                   (fun x : nat =>
                    eq nat x
                      (times (f b0)
                         (bigop nat b0 (fun i : nat => andb (leb a i) (p i))
                            (S O) times (fun i : nat => f i))))
                   (eq_f2 nat nat nat times (f (plus (minus b0 a) a)) 
                      (f b0)
                      (bigop nat (minus b0 a) (fun i : nat => p (plus i a))
                         (S O) times (fun i : nat => f (plus i a)))
                      (bigop nat b0 (fun i : nat => andb (leb a i) (p i))
                         (S O) times (fun i : nat => f i))
                      (eq_f nat nat f (plus (minus b0 a) a) b0
                         (eq_ind nat b0 (fun x_1 : nat => eq nat x_1 b0)
                            (refl nat b0) (plus (minus b0 a) a)
                            (plus_minus_m_m b0 a (le_S_S_to_le a b0 Ha))))
                      (Hind p f (le_S_S_to_le a b0 Ha)))
                   (bigop nat (S (minus b0 a)) (fun i : nat => p (plus i a))
                      (S O) times (fun i : nat => f (plus i a)))
                   (bigop_Strue nat (minus b0 a)
                      (fun __ : nat => p (plus __ a)) 
                      (S O) times (fun __ : nat => f (plus __ a))
                      (eq_ind nat b0 (fun x_1 : nat => eq bool (p x_1) true)
                         (rewrite_r bool true
                            (fun __ : bool => eq bool __ true)
                            (refl bool true) (p b0) Hcase)
                         (plus (minus b0 a) a)
                         (plus_minus_m_m b0 a (le_S_S_to_le a b0 Ha)))))
                (minus (S b0) a)
                (match_nat_prop
                   (fun __ : nat =>
                    le __ b0 -> eq nat (minus (S b0) __) (S (minus b0 __)))
                   (fun auto : le O b0 =>
                    rewrite_l nat (S b0)
                      (fun __ : nat => eq nat __ (S (minus b0 O)))
                      (rewrite_l nat b0
                         (fun __ : nat => eq nat (S b0) (S __))
                         (refl nat (S b0)) (minus b0 O) 
                         (minus_n_O b0)) (minus (S b0) O) 
                      (minus_n_O (S b0)))
                   (sym_eq_minus (S b0)
                      (fun y : nat -> nat =>
                       forall n : nat,
                       le (S n) b0 -> eq nat (y (S n)) (S (minus b0 (S n))))
                      (sym_eq_filter_nat_type_S (nat -> nat) minus_body b0
                         (fun y : nat -> nat =>
                          forall n : nat,
                          le (S n) b0 ->
                          eq nat (y (S n)) (S (minus b0 (S n))))
                         (fun a1 : nat =>
                          sym_eq_minus_body_S b0
                            (fun y : nat -> nat =>
                             le (S a1) b0 ->
                             eq nat (y (S a1)) (S (minus b0 (S a1))))
                            (sym_eq_match_nat_type_S nat 
                               (S b0) (fun q : nat => minus b0 q) a1
                               (fun y : nat =>
                                le (S a1) b0 ->
                                eq nat y (S (minus b0 (S a1))))
                               (fun lta1 : le (S a1) b0 =>
                                eq_ind_r nat (pred (minus b0 a1))
                                  (fun x : nat => eq nat (minus b0 a1) (S x))
                                  (eq_ind_r nat (minus b0 a1)
                                     (fun x : nat => eq nat (minus b0 a1) x)
                                     (refl nat (minus b0 a1))
                                     (S (pred (minus b0 a1)))
                                     (S_pred (minus b0 a1)
                                        (lt_plus_to_minus_r O a1 b0
                                           (sym_eq_plus O
                                              (fun y : nat -> nat =>
                                               le (S (y a1)) b0)
                                              (sym_eq_filter_nat_type_O
                                                 (nat -> nat) plus_body
                                                 (fun y : nat -> nat =>
                                                 le (S (y a1)) b0)
                                                 (sym_eq_plus_body_O
                                                 (fun y : nat -> nat =>
                                                 le (S (y a1)) b0) lta1))))))
                                  (minus b0 (S a1)) 
                                  (eq_minus_S_pred b0 a1)))))) a
                   (le_S_S_to_le a b0 Ha)))
             (bigop nat (S b0) (fun i : nat => andb (leb a i) (p i)) 
                (S O) times (fun i : nat => f i))
             (bigop_Strue nat b0 (fun __ : nat => andb (leb a __) (p __))
                (S O) times f
                (eq_ind_r bool true
                   (fun x : bool => eq bool (andb (leb a b0) x) true)
                   (eq_ind_r bool true
                      (fun x : bool => eq bool (andb x true) true)
                      (eq_match_bool_type_true bool true false
                         (fun y : bool =>
                          eq bool (match_bool_type bool true false true) y)
                         (refl bool (andb true true))) 
                      (leb a b0) (le_to_leb_true a b0 (le_S_S_to_le a b0 Ha)))
                   (p b0) Hcase)))
          (fun Hcase : eq bool (p b0) false =>
           eq_ind_r nat
             (bigop nat b0 (fun i : nat => andb (leb a i) (p i)) 
                (S O) times (fun i : nat => f i))
             (fun x : nat =>
              eq nat
                (bigop nat (minus (S b0) a) (fun i : nat => p (plus i a))
                   (S O) times (fun i : nat => f (plus i a))) x)
             (eq_ind_r nat (S (minus b0 a))
                (fun x : nat =>
                 eq nat
                   (bigop nat x (fun i : nat => p (plus i a)) 
                      (S O) times (fun i : nat => f (plus i a)))
                   (bigop nat b0 (fun i : nat => andb (leb a i) (p i)) 
                      (S O) times (fun i : nat => f i)))
                (eq_ind_r nat
                   (bigop nat (minus b0 a) (fun i : nat => p (plus i a))
                      (S O) times (fun i : nat => f (plus i a)))
                   (fun x : nat =>
                    eq nat x
                      (bigop nat b0 (fun i : nat => andb (leb a i) (p i))
                         (S O) times (fun i : nat => f i)))
                   (Hind p f (le_S_S_to_le a b0 Ha))
                   (bigop nat (S (minus b0 a)) (fun i : nat => p (plus i a))
                      (S O) times (fun i : nat => f (plus i a)))
                   (bigop_Sfalse nat (minus b0 a)
                      (fun __ : nat => p (plus __ a)) 
                      (S O) times (fun __ : nat => f (plus __ a))
                      (eq_ind nat b0 (fun x_1 : nat => eq bool (p x_1) false)
                         (rewrite_r bool false
                            (fun __ : bool => eq bool __ false)
                            (refl bool false) (p b0) Hcase)
                         (plus (minus b0 a) a)
                         (plus_minus_m_m b0 a (le_S_S_to_le a b0 Ha)))))
                (minus (S b0) a)
                (match_nat_prop
                   (fun __ : nat =>
                    le __ b0 -> eq nat (minus (S b0) __) (S (minus b0 __)))
                   (fun auto : le O b0 =>
                    rewrite_l nat (S b0)
                      (fun __ : nat => eq nat __ (S (minus b0 O)))
                      (rewrite_l nat b0
                         (fun __ : nat => eq nat (S b0) (S __))
                         (refl nat (S b0)) (minus b0 O) 
                         (minus_n_O b0)) (minus (S b0) O) 
                      (minus_n_O (S b0)))
                   (sym_eq_minus (S b0)
                      (fun y : nat -> nat =>
                       forall n : nat,
                       le (S n) b0 -> eq nat (y (S n)) (S (minus b0 (S n))))
                      (sym_eq_filter_nat_type_S (nat -> nat) minus_body b0
                         (fun y : nat -> nat =>
                          forall n : nat,
                          le (S n) b0 ->
                          eq nat (y (S n)) (S (minus b0 (S n))))
                         (fun a1 : nat =>
                          sym_eq_minus_body_S b0
                            (fun y : nat -> nat =>
                             le (S a1) b0 ->
                             eq nat (y (S a1)) (S (minus b0 (S a1))))
                            (sym_eq_match_nat_type_S nat 
                               (S b0) (fun q : nat => minus b0 q) a1
                               (fun y : nat =>
                                le (S a1) b0 ->
                                eq nat y (S (minus b0 (S a1))))
                               (fun lta1 : le (S a1) b0 =>
                                eq_ind_r nat (pred (minus b0 a1))
                                  (fun x : nat => eq nat (minus b0 a1) (S x))
                                  (eq_ind_r nat (minus b0 a1)
                                     (fun x : nat => eq nat (minus b0 a1) x)
                                     (refl nat (minus b0 a1))
                                     (S (pred (minus b0 a1)))
                                     (S_pred (minus b0 a1)
                                        (lt_plus_to_minus_r O a1 b0
                                           (sym_eq_plus O
                                              (fun y : nat -> nat =>
                                               le (S (y a1)) b0)
                                              (sym_eq_filter_nat_type_O
                                                 (nat -> nat) plus_body
                                                 (fun y : nat -> nat =>
                                                 le (S (y a1)) b0)
                                                 (sym_eq_plus_body_O
                                                 (fun y : nat -> nat =>
                                                 le (S (y a1)) b0) lta1))))))
                                  (minus b0 (S a1)) 
                                  (eq_minus_S_pred b0 a1)))))) a
                   (le_S_S_to_le a b0 Ha)))
             (bigop nat (S b0) (fun i : nat => andb (leb a i) (p i)) 
                (S O) times (fun i : nat => f i))
             (bigop_Sfalse nat b0 (fun __ : nat => andb (leb a __) (p __))
                (S O) times f
                (eq_ind_r bool false
                   (fun x : bool => eq bool (andb (leb a b0) x) false)
                   (match_bool_prop
                      (fun __ : bool => eq bool (andb __ false) false)
                      (eq_match_bool_type_true bool false false
                         (fun y : bool =>
                          eq bool (match_bool_type bool false false true) y)
                         (refl bool (andb true false)))
                      (eq_match_bool_type_false bool false false
                         (fun y : bool =>
                          eq bool (match_bool_type bool false false false) y)
                         (refl bool (andb false false))) 
                      (leb a b0)) (p b0) Hcase))) 
          (true_or_false (p b0)))
       (fun Ha : eq nat a (S b0) =>
        eq_ind nat a
          (fun x_1 : nat =>
           eq nat
             (bigop nat (minus x_1 a) (fun i : nat => p (plus i a)) 
                (S O) times (fun i : nat => f (plus i a)))
             (bigop nat x_1 (fun i : nat => andb (leb a i) (p i)) 
                (S O) times (fun i : nat => f i)))
          (eq_ind nat O
             (fun x_1 : nat =>
              eq nat
                (bigop nat x_1 (fun i : nat => p (plus i a)) 
                   (S O) times (fun i : nat => f (plus i a)))
                (bigop nat a (fun i : nat => andb (leb a i) (p i)) 
                   (S O) times (fun i : nat => f i)))
             (sym_eq_bigop_O nat
                (fun
                   y : (nat -> bool) ->
                       nat -> (nat -> nat -> nat) -> (nat -> nat) -> nat =>
                 eq nat
                   (y (fun i : nat => p (plus i a)) 
                      (S O) times (fun i : nat => f (plus i a)))
                   (bigop nat a (fun i : nat => andb (leb a i) (p i)) 
                      (S O) times (fun i : nat => f i)))
                (sym_eq_bigop_body_O nat
                   (fun
                      y : (nat -> bool) ->
                          nat -> (nat -> nat -> nat) -> (nat -> nat) -> nat
                    =>
                    eq nat
                      (y (fun i : nat => p (plus i a)) 
                         (S O) times (fun i : nat => f (plus i a)))
                      (bigop nat a (fun i : nat => andb (leb a i) (p i))
                         (S O) times (fun i : nat => f i)))
                   (eq_ind nat
                      (bigop nat a (fun i : nat => false) 
                         (S O) times (fun i : nat => f i))
                      (fun x_1 : nat =>
                       eq nat x_1
                         (bigop nat a (fun i : nat => andb (leb a i) (p i))
                            (S O) times (fun i : nat => f i)))
                      (same_bigop nat a (fun __ : nat => false)
                         (fun __ : nat => andb (leb a __) (p __)) 
                         (S O) times f f
                         (fun (i : nat) (ltia : lt i a) =>
                          eq_ind_r bool false
                            (fun x : bool => eq bool false (andb x (p i)))
                            (sym_eq_match_bool_type_false bool 
                               (p i) false (fun y : bool => eq bool false y)
                               (refl bool false)) 
                            (leb a i)
                            (not_le_to_leb_false a i (lt_to_not_le i a ltia)))
                         (fun (i : nat) (auto : lt i a)
                            (auto' : eq bool false true) => 
                          refl nat (f i))) (S O)
                      (bigop_false nat a (S O) times f)))) 
             (minus a a) (minus_n_n a)) (S b0) Ha)
       (le_to_or_lt_eq a (S b0) lea)) b.

Inductive ACop : forall A : Type, A -> Prop :=
    mk_acop :
      forall A nil op,
      (forall a, eq A (op nil a) a) ->
      (forall a, eq A (op a nil) a) ->
      (forall a b c, eq A (op a (op b c)) (op (op a b) c)) ->
      (forall a b, eq A (op a b) (op b a)) -> ACop A nil.

Theorem mk_ACop :
  forall (A : Type) (nil : A) (op : A -> A -> A),
  (forall a : A, eq A (op nil a) a) ->
  (forall a : A, eq A (op a nil) a) ->
  (forall a b c : A, eq A (op a (op b c)) (op (op a b) c)) ->
  (forall a b : A, eq A (op a b) (op b a)) -> ACop A nil.
Proof.
  (apply mk_acop).
Qed.

Definition timesAC : ACop nat (S O) :=
  mk_ACop nat (S O) times
    (fun a : nat =>
     sym_eq_times (S O) (fun y : nat -> nat => eq nat (y a) a)
       (sym_eq_filter_nat_type_S (nat -> nat) times_body O
          (fun y : nat -> nat => eq nat (y a) a)
          (sym_eq_times_body_S O (fun y : nat -> nat => eq nat (y a) a)
             (sym_eq_times O (fun y : nat -> nat => eq nat (plus a (y a)) a)
                (sym_eq_filter_nat_type_O (nat -> nat) times_body
                   (fun y : nat -> nat => eq nat (plus a (y a)) a)
                   (sym_eq_times_body_O
                      (fun y : nat -> nat => eq nat (plus a (y a)) a)
                      (sym_eq nat a (plus a O) (plus_n_O a))))))))
    (fun n : nat => sym_eq nat n (times n (S O)) (times_n_1 n))
    (fun a b c : nat =>
     sym_eq nat (times (times a b) c) (times a (times b c))
       (associative_times a b c)) commutative_times.
Definition bigop_diff :
  forall (p : nat -> bool) (f : nat -> nat) (i n : nat),
  lt i n ->
  eq bool (p i) true ->
  eq nat (bigop nat n (fun x : nat => p x) (S O) times (fun x : nat => f x))
    (times (f i)
       (bigop nat n (fun x : nat => andb (notb (eqb i x)) (p x)) 
          (S O) times (fun x : nat => f x))) :=
  fun (p : nat -> bool) (f : nat -> nat) (i n : nat) =>
  nat_ind
    (fun _x_365 : nat =>
     lt i _x_365 ->
     eq bool (p i) true ->
     eq nat
       (bigop nat _x_365 (fun x : nat => p x) (S O) times
          (fun x : nat => f x))
       (times (f i)
          (bigop nat _x_365 (fun x : nat => andb (notb (eqb i x)) (p x))
             (S O) times (fun x : nat => f x))))
    (fun ltO : lt i O =>
     falsity
       (eq bool (p i) true ->
        eq nat
          (bigop nat O (fun x : nat => p x) (S O) times (fun x : nat => f x))
          (times (f i)
             (bigop nat O (fun x : nat => andb (notb (eqb i x)) (p x)) 
                (S O) times (fun x : nat => f x))))
       (absurd (le (S i) O) ltO (not_le_Sn_O i)))
    (fun (n0 : nat)
       (Hind : lt i n0 ->
               eq bool (p i) true ->
               eq nat
                 (bigop nat n0 (fun x : nat => p x) 
                    (S O) times (fun x : nat => f x))
                 (times (f i)
                    (bigop nat n0
                       (fun x : nat => andb (notb (eqb i x)) (p x)) 
                       (S O) times (fun x : nat => f x))))
       (lein : lt i (S n0)) (pi : eq bool (p i) true) =>
     match_Or_prop (lt i n0) (eq nat i n0)
       (eq nat
          (bigop nat (S n0) (fun x : nat => p x) (S O) times
             (fun x : nat => f x))
          (times (f i)
             (bigop nat (S n0) (fun x : nat => andb (notb (eqb i x)) (p x))
                (S O) times (fun x : nat => f x))))
       (fun Hi : lt i n0 =>
        match_Or_prop (eq bool (p n0) true) (eq bool (p n0) false)
          (eq nat
             (bigop nat (S n0) (fun x : nat => p x) 
                (S O) times (fun x : nat => f x))
             (times (f i)
                (bigop nat (S n0)
                   (fun x : nat => andb (notb (eqb i x)) (p x)) 
                   (S O) times (fun x : nat => f x))))
          (fun pn : eq bool (p n0) true =>
           eq_ind_r nat
             (times (f n0)
                (bigop nat n0 (fun i0 : nat => p i0) 
                   (S O) times (fun i0 : nat => f i0)))
             (fun x : nat =>
              eq nat x
                (times (f i)
                   (bigop nat (S n0)
                      (fun x0 : nat => andb (notb (eqb i x0)) (p x0)) 
                      (S O) times (fun x0 : nat => f x0))))
             (eq_ind_r nat
                (times (f n0)
                   (bigop nat n0
                      (fun i0 : nat => andb (notb (eqb i i0)) (p i0)) 
                      (S O) times (fun i0 : nat => f i0)))
                (fun x : nat =>
                 eq nat
                   (times (f n0)
                      (bigop nat n0 (fun i0 : nat => p i0) 
                         (S O) times (fun i0 : nat => f i0))) 
                   (times (f i) x))
                (eq_ind_r nat
                   (times (times (f i) (f n0))
                      (bigop nat n0
                         (fun i0 : nat =>
                          match_bool_type bool (p i0) false
                            (match_bool_type bool false true (eqb i i0)))
                         (S O) times (fun i0 : nat => f i0)))
                   (fun x : nat =>
                    eq nat
                      (times (f n0)
                         (bigop nat n0 (fun i0 : nat => p i0) 
                            (S O) times (fun i0 : nat => f i0))) x)
                   (eq_ind_r nat (times (f n0) (f i))
                      (fun x : nat =>
                       eq nat
                         (times (f n0)
                            (bigop nat n0 (fun i0 : nat => p i0) 
                               (S O) times (fun i0 : nat => f i0)))
                         (times x
                            (bigop nat n0
                               (fun i0 : nat =>
                                match_bool_type bool 
                                  (p i0) false
                                  (match_bool_type bool false true (eqb i i0)))
                               (S O) times (fun i0 : nat => f i0))))
                      (eq_ind nat
                         (times (f n0)
                            (times (f i)
                               (bigop nat n0
                                  (fun i0 : nat =>
                                   match_bool_type bool 
                                     (p i0) false
                                     (match_bool_type bool false true
                                        (eqb i i0))) 
                                  (S O) times (fun i0 : nat => f i0))))
                         (fun x_1 : nat =>
                          eq nat
                            (times (f n0)
                               (bigop nat n0 (fun i0 : nat => p i0) 
                                  (S O) times (fun i0 : nat => f i0))) x_1)
                         (eq_ind_r nat
                            (times (f i)
                               (bigop nat n0
                                  (fun x : nat => andb (notb (eqb i x)) (p x))
                                  (S O) times (fun x : nat => f x)))
                            (fun x : nat =>
                             eq nat (times (f n0) x)
                               (times (f n0)
                                  (times (f i)
                                     (bigop nat n0
                                        (fun i0 : nat =>
                                         match_bool_type bool 
                                           (p i0) false
                                           (match_bool_type bool false true
                                              (eqb i i0))) 
                                        (S O) times 
                                        (fun i0 : nat => f i0)))))
                            (refl nat
                               (times (f n0)
                                  (times (f i)
                                     (bigop nat n0
                                        (fun x : nat =>
                                         andb (notb (eqb i x)) (p x)) 
                                        (S O) times 
                                        (fun x : nat => f x)))))
                            (bigop nat n0 (fun x : nat => p x) 
                               (S O) times (fun x : nat => f x))
                            (Hind Hi
                               (rewrite_r bool true
                                  (fun __ : bool => eq bool __ true)
                                  (refl bool true) 
                                  (p i) pi)))
                         (times (times (f n0) (f i))
                            (bigop nat n0
                               (fun i0 : nat =>
                                match_bool_type bool 
                                  (p i0) false
                                  (match_bool_type bool false true (eqb i i0)))
                               (S O) times (fun i0 : nat => f i0)))
                         (assoc (f n0) (f i)
                            (bigop nat n0
                               (fun i0 : nat =>
                                match_bool_type bool 
                                  (p i0) false
                                  (match_bool_type bool false true (eqb i i0)))
                               (S O) times (fun i0 : nat => f i0))))
                      (times (f i) (f n0)) (commutative_times (f i) (f n0)))
                   (times (f i)
                      (times (f n0)
                         (bigop nat n0
                            (fun i0 : nat =>
                             match_bool_type bool 
                               (p i0) false
                               (match_bool_type bool false true (eqb i i0)))
                            (S O) times (fun i0 : nat => f i0))))
                   (assoc (f i) (f n0)
                      (bigop nat n0
                         (fun i0 : nat =>
                          match_bool_type bool (p i0) false
                            (match_bool_type bool false true (eqb i i0)))
                         (S O) times (fun i0 : nat => f i0))))
                (bigop nat (S n0)
                   (fun i0 : nat => andb (notb (eqb i i0)) (p i0)) 
                   (S O) times (fun i0 : nat => f i0))
                (bigop_Strue nat n0
                   (fun __ : nat => andb (notb (eqb i __)) (p __)) 
                   (S O) times f
                   (rewrite_r bool true
                      (fun __ : bool =>
                       eq bool (andb (notb (eqb i n0)) __) true)
                      (rewrite_r bool true (fun __ : bool => eq bool __ true)
                         (refl bool true) (andb (notb (eqb i n0)) true)
                         (rewrite_l bool (p n0)
                            (fun __ : bool =>
                             eq bool (andb (notb (eqb i n0)) true) __)
                            (rewrite_l bool (p n0)
                               (fun __ : bool =>
                                eq bool (andb (notb (eqb i n0)) __) (p n0))
                               (eq_ind_r bool false
                                  (fun x : bool =>
                                   eq bool (andb (notb x) (p n0)) (p n0))
                                  (sym_eq_match_bool_type_false bool false
                                     true
                                     (fun y : bool =>
                                      eq bool
                                        (match_bool_type bool (p n0) false y)
                                        (p n0))
                                     (eq_match_bool_type_true bool 
                                        (p n0) false
                                        (fun y : bool =>
                                         eq bool
                                           (match_bool_type bool 
                                              (p n0) false true) y)
                                        (eq_match_bool_type_false bool false
                                           true
                                           (fun y : bool =>
                                            eq bool
                                              (match_bool_type bool 
                                                 (p n0) false true)
                                              (match_bool_type bool 
                                                 (p n0) false y))
                                           (eq_match_bool_type_false bool
                                              false true
                                              (fun y : bool =>
                                               eq bool
                                                 (match_bool_type bool 
                                                 (p n0) false y)
                                                 (match_bool_type bool 
                                                 (p n0) false
                                                 (match_bool_type bool false
                                                 true false)))
                                              (refl bool
                                                 (andb (notb false) (p n0)))))))
                                  (eqb i n0)
                                  (not_eq_to_eqb_false i n0
                                     (lt_to_not_eq i n0 Hi))) true pn) true
                            pn)) (p n0) pn)))
             (bigop nat (S n0) (fun i0 : nat => p i0) 
                (S O) times (fun i0 : nat => f i0))
             (bigop_Strue nat n0 p (S O) times f
                (rewrite_r bool true (fun __ : bool => eq bool __ true)
                   (refl bool true) (p n0) pn)))
          (fun pn : eq bool (p n0) false =>
           eq_ind_r nat
             (bigop nat n0 (fun i0 : nat => p i0) 
                (S O) times (fun i0 : nat => f i0))
             (fun x : nat =>
              eq nat x
                (times (f i)
                   (bigop nat (S n0)
                      (fun x0 : nat => andb (notb (eqb i x0)) (p x0)) 
                      (S O) times (fun x0 : nat => f x0))))
             (eq_ind_r nat
                (bigop nat n0 (fun i0 : nat => andb (notb (eqb i i0)) (p i0))
                   (S O) times (fun i0 : nat => f i0))
                (fun x : nat =>
                 eq nat
                   (bigop nat n0 (fun i0 : nat => p i0) 
                      (S O) times (fun i0 : nat => f i0)) 
                   (times (f i) x))
                (eq_ind_r nat
                   (times (f i)
                      (bigop nat n0
                         (fun x : nat => andb (notb (eqb i x)) (p x)) 
                         (S O) times (fun x : nat => f x)))
                   (fun x : nat =>
                    eq nat x
                      (times (f i)
                         (bigop nat n0
                            (fun i0 : nat => andb (notb (eqb i i0)) (p i0))
                            (S O) times (fun i0 : nat => f i0))))
                   (refl nat
                      (times (f i)
                         (bigop nat n0
                            (fun x : nat => andb (notb (eqb i x)) (p x))
                            (S O) times (fun x : nat => f x))))
                   (bigop nat n0 (fun x : nat => p x) 
                      (S O) times (fun x : nat => f x))
                   (Hind Hi
                      (rewrite_r bool true (fun __ : bool => eq bool __ true)
                         (refl bool true) (p i) pi)))
                (bigop nat (S n0)
                   (fun i0 : nat => andb (notb (eqb i i0)) (p i0)) 
                   (S O) times (fun i0 : nat => f i0))
                (bigop_Sfalse nat n0
                   (fun __ : nat => andb (notb (eqb i __)) (p __)) 
                   (S O) times f
                   (rewrite_r bool false
                      (fun __ : bool =>
                       eq bool (andb (notb (eqb i n0)) __) false)
                      (rewrite_r bool false
                         (fun __ : bool => eq bool __ false)
                         (refl bool false) (andb (notb (eqb i n0)) false)
                         (rewrite_l bool (p n0)
                            (fun __ : bool =>
                             eq bool (andb (notb (eqb i n0)) false) __)
                            (rewrite_l bool (p n0)
                               (fun __ : bool =>
                                eq bool (andb (notb (eqb i n0)) __) (p n0))
                               (eq_ind_r bool false
                                  (fun x : bool =>
                                   eq bool (andb (notb x) (p n0)) (p n0))
                                  (sym_eq_match_bool_type_false bool false
                                     true
                                     (fun y : bool =>
                                      eq bool
                                        (match_bool_type bool (p n0) false y)
                                        (p n0))
                                     (eq_match_bool_type_true bool 
                                        (p n0) false
                                        (fun y : bool =>
                                         eq bool
                                           (match_bool_type bool 
                                              (p n0) false true) y)
                                        (eq_match_bool_type_false bool false
                                           true
                                           (fun y : bool =>
                                            eq bool
                                              (match_bool_type bool 
                                                 (p n0) false true)
                                              (match_bool_type bool 
                                                 (p n0) false y))
                                           (eq_match_bool_type_false bool
                                              false true
                                              (fun y : bool =>
                                               eq bool
                                                 (match_bool_type bool 
                                                 (p n0) false y)
                                                 (match_bool_type bool 
                                                 (p n0) false
                                                 (match_bool_type bool false
                                                 true false)))
                                              (refl bool
                                                 (andb (notb false) (p n0)))))))
                                  (eqb i n0)
                                  (not_eq_to_eqb_false i n0
                                     (lt_to_not_eq i n0 Hi))) false pn) false
                            pn)) (p n0) pn)))
             (bigop nat (S n0) (fun i0 : nat => p i0) 
                (S O) times (fun i0 : nat => f i0))
             (bigop_Sfalse nat n0 p (S O) times f
                (rewrite_r bool false (fun __ : bool => eq bool __ false)
                   (refl bool false) (p n0) pn))) 
          (true_or_false (p n0)))
       (fun Hi : eq nat i n0 =>
        eq_ind nat i
          (fun x_1 : nat =>
           eq nat
             (bigop nat (S x_1) (fun x : nat => p x) 
                (S O) times (fun x : nat => f x))
             (times (f i)
                (bigop nat (S x_1)
                   (fun x : nat => andb (notb (eqb i x)) (p x)) 
                   (S O) times (fun x : nat => f x))))
          (eq_ind_r nat
             (times (f i)
                (bigop nat i (fun i0 : nat => p i0) 
                   (S O) times (fun i0 : nat => f i0)))
             (fun x : nat =>
              eq nat x
                (times (f i)
                   (bigop nat (S i)
                      (fun x0 : nat => andb (notb (eqb i x0)) (p x0)) 
                      (S O) times (fun x0 : nat => f x0))))
             (eq_f nat nat (times (f i))
                (bigop nat i (fun i0 : nat => p i0) 
                   (S O) times (fun i0 : nat => f i0))
                (bigop nat (S i) (fun x : nat => andb (notb (eqb i x)) (p x))
                   (S O) times (fun x : nat => f x))
                (eq_ind_r nat
                   (bigop nat i
                      (fun i0 : nat => andb (notb (eqb i i0)) (p i0)) 
                      (S O) times (fun i0 : nat => f i0))
                   (fun x : nat =>
                    eq nat
                      (bigop nat i (fun i0 : nat => p i0) 
                         (S O) times (fun i0 : nat => f i0)) x)
                   (same_bigop nat i p
                      (fun __ : nat => andb (notb (eqb i __)) (p __)) 
                      (S O) times f f
                      (fun (k : nat) (ltki : lt k i) =>
                       eq_ind_r bool false
                         (fun x : bool => eq bool (p k) (andb (notb x) (p k)))
                         (sym_eq_match_bool_type_false bool false true
                            (fun y : bool =>
                             eq bool (p k)
                               (match_bool_type bool (p k) false y))
                            (sym_eq_match_bool_type_true bool 
                               (p k) false (fun y : bool => eq bool (p k) y)
                               (refl bool (p k)))) 
                         (eqb i k)
                         (not_eq_to_eqb_false i k
                            (not_to_not (eq nat i k) 
                               (le (S i) i)
                               (fun auto : eq nat i k =>
                                eq_coerc (le (S k) i) 
                                  (le (S i) i) ltki
                                  (rewrite_l nat i
                                     (fun __ : nat =>
                                      eq Prop (le (S __) i) (le (S i) i))
                                     (refl Prop (le (S i) i)) k auto))
                               (not_le_Sn_n i))))
                      (fun (i0 : nat) (auto : lt i0 i)
                         (auto' : eq bool (p i0) true) => 
                       refl nat (f i0)))
                   (bigop nat (S i)
                      (fun i0 : nat => andb (notb (eqb i i0)) (p i0)) 
                      (S O) times (fun i0 : nat => f i0))
                   (bigop_Sfalse nat i
                      (fun __ : nat => andb (notb (eqb i __)) (p __)) 
                      (S O) times f
                      (eq_ind_r bool true
                         (fun x : bool => eq bool (andb (notb x) (p i)) false)
                         (eq_match_bool_type_false bool 
                            (p i) false
                            (fun y : bool =>
                             eq bool
                               (match_bool_type bool 
                                  (p i) false
                                  (match_bool_type bool false true true)) y)
                            (eq_match_bool_type_true bool false true
                               (fun y : bool =>
                                eq bool
                                  (match_bool_type bool 
                                     (p i) false
                                     (match_bool_type bool false true true))
                                  (match_bool_type bool (p i) false y))
                               (refl bool (andb (notb true) (p i)))))
                         (eqb i i) (eq_to_eqb_true i i (refl nat i))))))
             (bigop nat (S i) (fun i0 : nat => p i0) 
                (S O) times (fun i0 : nat => f i0))
             (bigop_Strue nat i p (S O) times f
                (rewrite_r bool true (fun __ : bool => eq bool __ true)
                   (refl bool true) (p i) pi))) n0 Hi)
       (le_to_or_lt_eq i n0 (le_S_S_to_le i n0 lein))) n.
Definition sub_hk :
  (nat -> nat) ->
  (nat -> nat) ->
  nat ->
  nat ->
  (nat -> bool) -> (nat -> bool) -> (nat -> nat) -> (nat -> nat) -> Prop :=
  fun (h k : nat -> nat) (n1 n2 : nat) (p1 p2 : nat -> bool)
    (f1 f2 : nat -> nat) =>
  forall i : nat,
  lt i n1 ->
  eq bool (p1 i) true ->
  And (And (lt (h i) n2) (eq bool (p2 (h i)) true)) (eq nat (k (h i)) i).
Definition iso :
  nat ->
  nat ->
  (nat -> bool) -> (nat -> bool) -> (nat -> nat) -> (nat -> nat) -> Prop :=
  fun (n1 n2 : nat) (p1 p2 : nat -> bool) (f1 f2 : nat -> nat) =>
  Ex (nat -> nat)
    (fun h : nat -> nat =>
     Ex (nat -> nat)
       (fun k : nat -> nat =>
        And
          (And
             (forall i : nat,
              lt i n1 -> eq bool (p1 i) true -> eq nat (f1 i) (f2 (h i)))
             (sub_hk h k n1 n2 p1 p2 f1 f2)) (sub_hk k h n2 n1 p2 p1 f2 f1))).
Definition sub_hkO :
  forall (h k : nat -> nat) (n1 n2 : nat) (p1 p2 : nat -> bool)
    (f1 f2 : nat -> nat), eq nat n1 O -> sub_hk h k n1 n2 p1 p2 f1 f2 :=
  fun (h k : nat -> nat) (n1 n2 : nat) (p1 p2 : nat -> bool)
    (f1 f2 : nat -> nat) (up0 : eq nat n1 O) (i : nat) 
    (lti : lt i n1) =>
  eq_ind_r nat O
    (fun x : nat =>
     eq bool (p1 i) true ->
     And (And (lt (h i) n2) (eq bool (p2 (h i)) true)) (eq nat (k (h i)) i))
    (falsity
       (eq bool (p1 i) true ->
        And (And (lt (h i) n2) (eq bool (p2 (h i)) true))
          (eq nat (k (h i)) i))
       (absurd (le (S i) O)
          (eq_coerc (le (S i) n1) (le (S i) O) lti
             (rewrite_r nat O
                (fun __ : nat => eq Prop (le (S i) __) (le (S i) O))
                (refl Prop (le (S i) O)) n1 up0)) 
          (not_le_Sn_O i))) n1 up0.
Definition sub0_to_false :
  forall (h k : nat -> nat) (n1 n2 : nat) (p1 p2 : nat -> bool)
    (f1 f2 : nat -> nat),
  eq nat n1 O ->
  sub_hk h k n2 n1 p2 p1 f2 f1 ->
  forall i : nat, lt i n2 -> eq bool (p2 i) false :=
  fun (h k : nat -> nat) (n1 n2 : nat) (p1 p2 : nat -> bool)
    (f1 f2 : nat -> nat) (up0 : eq nat n1 O)
    (sub : sub_hk h k n2 n1 p2 p1 f2 f1) (i : nat) 
    (lti : lt i n2) =>
  match_Or_prop (eq bool (p2 i) true) (eq bool (p2 i) false)
    (eq bool (p2 i) false)
    (fun ptrue : eq bool (p2 i) true =>
     match_And_prop (And (lt (h i) n1) (eq bool (p1 (h i)) true))
       (eq nat (k (h i)) i) (eq bool (p2 i) false)
       (fun _clearme : And (lt (h i) n1) (eq bool (p1 (h i)) true) =>
        match_And_prop (lt (h i) n1) (eq bool (p1 (h i)) true)
          (eq nat (k (h i)) i -> eq bool (p2 i) false)
          (fun hi : lt (h i) n1 =>
           falsity
             (eq bool (p1 (h i)) true ->
              eq nat (k (h i)) i -> eq bool (p2 i) false)
             (absurd (le (S (h i)) O)
                (eq_coerc (le (S (h i)) n1) (le (S (h i)) O) hi
                   (rewrite_r nat O
                      (fun __ : nat =>
                       eq Prop (le (S (h i)) __) (le (S (h i)) O))
                      (refl Prop (le (S (h i)) O)) n1 up0))
                (not_le_Sn_O (h i)))) _clearme) (sub i lti ptrue))
    (fun auto : eq bool (p2 i) false =>
     rewrite_r bool false (fun __ : bool => eq bool __ false)
       (refl bool false) (p2 i) auto) (true_or_false (p2 i)).
Definition sub_lt :
  forall (e : nat -> nat) (p : nat -> bool) (n m : nat),
  le n m -> sub_hk (fun x : nat => x) (fun x : nat => x) n m p p e e :=
  fun (e : nat -> nat) (f : nat -> bool) (n m : nat) 
    (lenm : le n m) (i : nat) (lti : lt i n) (fi : eq bool (f i) true)
    (z : Prop) (f1 : And (lt i m) (eq bool (f i) true) -> eq nat i i -> z) =>
  f1
    (fun (z0 : Prop) (f2 : lt i m -> eq bool (f i) true -> z0) =>
     f2 (lt_to_le_to_lt i n m lti lenm)
       (rewrite_r bool true (fun __ : bool => eq bool __ true)
          (refl bool true) (f i) fi)) (refl nat i).
Definition transitive_sub :
  forall (h1 k1 h2 k2 : nat -> nat) (n1 n2 n3 : nat) 
    (p1 p2 p3 : nat -> bool) (f1 f2 f3 : nat -> nat),
  sub_hk h1 k1 n1 n2 p1 p2 f1 f2 ->
  sub_hk h2 k2 n2 n3 p2 p3 f2 f3 ->
  sub_hk (fun x : nat => h2 (h1 x)) (fun x : nat => k1 (k2 x)) n1 n3 p1 p3 f1
    f3 :=
  fun (h1 k1 h2 k2 : nat -> nat) (n1 n2 n3 : nat) 
    (p1 p2 p3 : nat -> bool) (f1 f2 f3 : nat -> nat)
    (sub1 : sub_hk h1 k1 n1 n2 p1 p2 f1 f2)
    (sub2 : sub_hk h2 k2 n2 n3 p2 p3 f2 f3) (i : nat) 
    (lti : lt i n1) (fi : eq bool (p1 i) true) =>
  match_And_prop (And (lt (h1 i) n2) (eq bool (p2 (h1 i)) true))
    (eq nat (k1 (h1 i)) i)
    (And (And (lt (h2 (h1 i)) n3) (eq bool (p3 (h2 (h1 i))) true))
       (eq nat (k1 (k2 (h2 (h1 i)))) i))
    (fun _clearme : And (lt (h1 i) n2) (eq bool (p2 (h1 i)) true) =>
     match_And_prop (lt (h1 i) n2) (eq bool (p2 (h1 i)) true)
       (eq nat (k1 (h1 i)) i ->
        And (And (lt (h2 (h1 i)) n3) (eq bool (p3 (h2 (h1 i))) true))
          (eq nat (k1 (k2 (h2 (h1 i)))) i))
       (fun (lth1i : lt (h1 i) n2) (fh1i : eq bool (p2 (h1 i)) true)
          (ei : eq nat (k1 (h1 i)) i) =>
        match_And_prop
          (And (lt (h2 (h1 i)) n3) (eq bool (p3 (h2 (h1 i))) true))
          (eq nat (k2 (h2 (h1 i))) (h1 i))
          (And (And (lt (h2 (h1 i)) n3) (eq bool (p3 (h2 (h1 i))) true))
             (eq nat (k1 (k2 (h2 (h1 i)))) i))
          (fun
             _clearme0 : And (lt (h2 (h1 i)) n3)
                           (eq bool (p3 (h2 (h1 i))) true) =>
           match_And_prop (lt (h2 (h1 i)) n3) (eq bool (p3 (h2 (h1 i))) true)
             (eq nat (k2 (h2 (h1 i))) (h1 i) ->
              And (And (lt (h2 (h1 i)) n3) (eq bool (p3 (h2 (h1 i))) true))
                (eq nat (k1 (k2 (h2 (h1 i)))) i))
             (fun (H1 : lt (h2 (h1 i)) n3)
                (H2 : eq bool (p3 (h2 (h1 i))) true)
                (H3 : eq nat (k2 (h2 (h1 i))) (h1 i)) 
                (z : Prop)
                (f : And (lt (h2 (h1 i)) n3) (eq bool (p3 (h2 (h1 i))) true) ->
                     eq nat (k1 (k2 (h2 (h1 i)))) i -> z) =>
              f
                (fun (z0 : Prop)
                   (f20 : lt (h2 (h1 i)) n3 ->
                          eq bool (p3 (h2 (h1 i))) true -> z0) =>
                 f20 H1
                   (rewrite_r bool true (fun __ : bool => eq bool __ true)
                      (refl bool true) (p3 (h2 (h1 i))) H2))
                (rewrite_r nat (h1 i) (fun __ : nat => eq nat (k1 __) i)
                   (rewrite_r nat i (fun __ : nat => eq nat __ i)
                      (refl nat i) (k1 (h1 i)) ei) 
                   (k2 (h2 (h1 i))) H3)) _clearme0) 
          (sub2 (h1 i) lth1i fh1i)) _clearme) (sub1 i lti fi).
Definition let_clause_10471 :
  forall (n1 n2 : nat) (p1 p2 : nat -> bool) (f1 f2 : nat -> nat),
  iso n1 n2 p1 p2 f1 f2 ->
  forall h : nat -> nat,
  Ex (nat -> nat)
    (fun k : nat -> nat =>
     And
       (And
          (forall i : nat,
           lt i n1 -> eq bool (p1 i) true -> eq nat (f1 i) (f2 (h i)))
          (sub_hk h k n1 n2 p1 p2 f1 f2)) (sub_hk k h n2 n1 p2 p1 f2 f1)) ->
  forall k : nat -> nat,
  And
    (And
       (forall i : nat,
        lt i n1 -> eq bool (p1 i) true -> eq nat (f1 i) (f2 (h i)))
       (sub_hk h k n1 n2 p1 p2 f1 f2)) (sub_hk k h n2 n1 p2 p1 f2 f1) ->
  And
    (forall i : nat,
     lt i n1 -> eq bool (p1 i) true -> eq nat (f1 i) (f2 (h i)))
    (sub_hk h k n1 n2 p1 p2 f1 f2) ->
  (forall i : nat, lt i n1 -> eq bool (p1 i) true -> eq nat (f1 i) (f2 (h i))) ->
  forall i m : nat,
  (forall f : nat -> bool,
   le O n1 ->
   sub_hk h k O m p1 f f1 f2 ->
   sub_hk k h m O f p1 f2 f1 ->
   eq nat
     (bigop nat O (fun i0 : nat => p1 i0) (S O) times (fun i0 : nat => f1 i0))
     (bigop nat m (fun i0 : nat => f i0) (S O) times (fun i0 : nat => f2 i0))) ->
  forall p20 : nat -> bool,
  le O n1 ->
  sub_hk h k O (S m) p1 p20 f1 f2 ->
  sub_hk k h (S m) O p20 p1 f2 f1 ->
  forall x2571 x2572 : nat,
  eq nat x2571 (plus (times x2572 (div x2571 x2572)) (mod x2571 x2572)) :=
  fun (n1 n2 : nat) (p1 p2 : nat -> bool) (f1 f2 : nat -> nat)
    (_clearme : iso n1 n2 p1 p2 f1 f2) (h : nat -> nat)
    (_clearme0 : Ex (nat -> nat)
                   (fun k : nat -> nat =>
                    And
                      (And
                         (forall i : nat,
                          lt i n1 ->
                          eq bool (p1 i) true -> eq nat (f1 i) (f2 (h i)))
                         (sub_hk h k n1 n2 p1 p2 f1 f2))
                      (sub_hk k h n2 n1 p2 p1 f2 f1))) 
    (k : nat -> nat)
    (_clearme1 : And
                   (And
                      (forall i : nat,
                       lt i n1 ->
                       eq bool (p1 i) true -> eq nat (f1 i) (f2 (h i)))
                      (sub_hk h k n1 n2 p1 p2 f1 f2))
                   (sub_hk k h n2 n1 p2 p1 f2 f1))
    (_clearme2 : And
                   (forall i : nat,
                    lt i n1 ->
                    eq bool (p1 i) true -> eq nat (f1 i) (f2 (h i)))
                   (sub_hk h k n1 n2 p1 p2 f1 f2))
    (same : forall i : nat,
            lt i n1 -> eq bool (p1 i) true -> eq nat (f1 i) (f2 (h i)))
    (i m : nat)
    (Hind : forall f : nat -> bool,
            le O n1 ->
            sub_hk h k O m p1 f f1 f2 ->
            sub_hk k h m O f p1 f2 f1 ->
            eq nat
              (bigop nat O (fun i0 : nat => p1 i0) 
                 (S O) times (fun i0 : nat => f1 i0))
              (bigop nat m (fun i0 : nat => f i0) 
                 (S O) times (fun i0 : nat => f2 i0))) 
    (p20 : nat -> bool) (__ : le O n1)
    (sub1 : sub_hk h k O (S m) p1 p20 f1 f2)
    (sub2 : sub_hk k h (S m) O p20 p1 f2 f1) (x2571 x2572 : nat) =>
  rewrite_l nat (times (div x2571 x2572) x2572)
    (fun __1 : nat => eq nat x2571 (plus __1 (mod x2571 x2572)))
    (div_mod x2571 x2572) (times x2572 (div x2571 x2572))
    (commutative_times (div x2571 x2572) x2572).
Definition bigop_iso :
  forall (n1 n2 : nat) (p1 p2 : nat -> bool) (f1 f2 : nat -> nat),
  iso n1 n2 p1 p2 f1 f2 ->
  eq nat
    (bigop nat n1 (fun i : nat => p1 i) (S O) times (fun i : nat => f1 i))
    (bigop nat n2 (fun i : nat => p2 i) (S O) times (fun i : nat => f2 i)) :=
  fun (n1 n2 : nat) (p1 p2 : nat -> bool) (f1 f2 : nat -> nat)
    (_clearme : iso n1 n2 p1 p2 f1 f2) =>
  match_ex_prop (nat -> nat)
    (fun h : nat -> nat =>
     Ex (nat -> nat)
       (fun k : nat -> nat =>
        And
          (And
             (forall i : nat,
              lt i n1 -> eq bool (p1 i) true -> eq nat (f1 i) (f2 (h i)))
             (sub_hk h k n1 n2 p1 p2 f1 f2)) (sub_hk k h n2 n1 p2 p1 f2 f1)))
    (eq nat
       (bigop nat n1 (fun i : nat => p1 i) (S O) times (fun i : nat => f1 i))
       (bigop nat n2 (fun i : nat => p2 i) (S O) times (fun i : nat => f2 i)))
    (fun (h : nat -> nat)
       (_clearme0 : Ex (nat -> nat)
                      (fun k : nat -> nat =>
                       And
                         (And
                            (forall i : nat,
                             lt i n1 ->
                             eq bool (p1 i) true -> eq nat (f1 i) (f2 (h i)))
                            (sub_hk h k n1 n2 p1 p2 f1 f2))
                         (sub_hk k h n2 n1 p2 p1 f2 f1))) =>
     match_ex_prop (nat -> nat)
       (fun k : nat -> nat =>
        And
          (And
             (forall i : nat,
              lt i n1 -> eq bool (p1 i) true -> eq nat (f1 i) (f2 (h i)))
             (sub_hk h k n1 n2 p1 p2 f1 f2)) (sub_hk k h n2 n1 p2 p1 f2 f1))
       (eq nat
          (bigop nat n1 (fun i : nat => p1 i) (S O) times
             (fun i : nat => f1 i))
          (bigop nat n2 (fun i : nat => p2 i) (S O) times
             (fun i : nat => f2 i)))
       (fun (k : nat -> nat)
          (_clearme1 : And
                         (And
                            (forall i : nat,
                             lt i n1 ->
                             eq bool (p1 i) true -> eq nat (f1 i) (f2 (h i)))
                            (sub_hk h k n1 n2 p1 p2 f1 f2))
                         (sub_hk k h n2 n1 p2 p1 f2 f1)) =>
        match_And_prop
          (And
             (forall i : nat,
              lt i n1 -> eq bool (p1 i) true -> eq nat (f1 i) (f2 (h i)))
             (sub_hk h k n1 n2 p1 p2 f1 f2)) (sub_hk k h n2 n1 p2 p1 f2 f1)
          (eq nat
             (bigop nat n1 (fun i : nat => p1 i) (S O) times
                (fun i : nat => f1 i))
             (bigop nat n2 (fun i : nat => p2 i) (S O) times
                (fun i : nat => f2 i)))
          (fun
             _clearme2 : And
                           (forall i : nat,
                            lt i n1 ->
                            eq bool (p1 i) true -> eq nat (f1 i) (f2 (h i)))
                           (sub_hk h k n1 n2 p1 p2 f1 f2) =>
           match_And_prop
             (forall i : nat,
              lt i n1 -> eq bool (p1 i) true -> eq nat (f1 i) (f2 (h i)))
             (sub_hk h k n1 n2 p1 p2 f1 f2)
             (sub_hk k h n2 n1 p2 p1 f2 f1 ->
              eq nat
                (bigop nat n1 (fun i : nat => p1 i) 
                   (S O) times (fun i : nat => f1 i))
                (bigop nat n2 (fun i : nat => p2 i) 
                   (S O) times (fun i : nat => f2 i)))
             (fun
                same : forall i : nat,
                       lt i n1 ->
                       eq bool (p1 i) true -> eq nat (f1 i) (f2 (h i)) =>
              le_gen
                (fun __ : nat =>
                 sub_hk h k __ n2 p1 p2 f1 f2 ->
                 sub_hk k h n2 __ p2 p1 f2 f1 ->
                 eq nat
                   (bigop nat __ (fun i : nat => p1 i) 
                      (S O) times (fun i : nat => f1 i))
                   (bigop nat n2 (fun i : nat => p2 i) 
                      (S O) times (fun i : nat => f2 i))) n1
                (fun i : nat =>
                 nat_ind
                   (fun _x_365 : nat =>
                    forall f : nat -> bool,
                    le _x_365 n1 ->
                    sub_hk h k _x_365 n2 p1 f f1 f2 ->
                    sub_hk k h n2 _x_365 f p1 f2 f1 ->
                    eq nat
                      (bigop nat _x_365 (fun i0 : nat => p1 i0) 
                         (S O) times (fun i0 : nat => f1 i0))
                      (bigop nat n2 (fun i0 : nat => f i0) 
                         (S O) times (fun i0 : nat => f2 i0)))
                   (nat_ind
                      (fun _x_365 : nat =>
                       forall f : nat -> bool,
                       le O n1 ->
                       sub_hk h k O _x_365 p1 f f1 f2 ->
                       sub_hk k h _x_365 O f p1 f2 f1 ->
                       eq nat
                         (bigop nat O (fun i0 : nat => p1 i0) 
                            (S O) times (fun i0 : nat => f1 i0))
                         (bigop nat _x_365 (fun i0 : nat => f i0) 
                            (S O) times (fun i0 : nat => f2 i0)))
                      (fun f : nat -> bool =>
                       sym_eq_bigop_O nat
                         (fun
                            y : (nat -> bool) ->
                                nat ->
                                (nat -> nat -> nat) -> (nat -> nat) -> nat =>
                          le O n1 ->
                          sub_hk h k O O p1 f f1 f2 ->
                          sub_hk k h O O f p1 f2 f1 ->
                          eq nat
                            (bigop nat O (fun iO : nat => p1 iO) 
                               (S O) times (fun iO : nat => f1 iO))
                            (y (fun iO : nat => f iO) 
                               (S O) times (fun iO : nat => f2 iO)))
                         (sym_eq_bigop_body_O nat
                            (fun
                               y : (nat -> bool) ->
                                   nat ->
                                   (nat -> nat -> nat) -> (nat -> nat) -> nat
                             =>
                             le O n1 ->
                             sub_hk h k O O p1 f f1 f2 ->
                             sub_hk k h O O f p1 f2 f1 ->
                             eq nat
                               (bigop nat O (fun iO : nat => p1 iO) 
                                  (S O) times (fun iO : nat => f1 iO))
                               (y (fun iO : nat => f iO) 
                                  (S O) times (fun iO : nat => f2 iO)))
                            (eq_bigop_body_O nat
                               (fun
                                  y : (nat -> bool) ->
                                      nat ->
                                      (nat -> nat -> nat) ->
                                      (nat -> nat) -> nat =>
                                le O n1 ->
                                sub_hk h k O O p1 f f1 f2 ->
                                sub_hk k h O O f p1 f2 f1 ->
                                eq nat
                                  (bigop nat O (fun iO : nat => p1 iO) 
                                     (S O) times (fun iO : nat => f1 iO))
                                  (y (fun iO : nat => p1 iO) 
                                     (S O) times (fun iO : nat => f1 iO)))
                               (eq_bigop_O nat
                                  (fun
                                     y : (nat -> bool) ->
                                         nat ->
                                         (nat -> nat -> nat) ->
                                         (nat -> nat) -> nat =>
                                   le O n1 ->
                                   sub_hk h k O O p1 f f1 f2 ->
                                   sub_hk k h O O f p1 f2 f1 ->
                                   eq nat
                                     (bigop nat O 
                                        (fun iO : nat => p1 iO) 
                                        (S O) times 
                                        (fun iO : nat => f1 iO))
                                     (y (fun iO : nat => p1 iO) 
                                        (S O) times 
                                        (fun iO : nat => f1 iO)))
                                  (fun (auto : le O n1)
                                     (auto' : sub_hk h k O O p1 f f1 f2)
                                     (auto'' : sub_hk k h O O f p1 f2 f1) =>
                                   refl nat
                                     (bigop nat O 
                                        (fun i0 : nat => p1 i0) 
                                        (S O) times 
                                        (fun i0 : nat => f1 i0)))))))
                      (fun (m : nat)
                         (Hind : forall f : nat -> bool,
                                 le O n1 ->
                                 sub_hk h k O m p1 f f1 f2 ->
                                 sub_hk k h m O f p1 f2 f1 ->
                                 eq nat
                                   (bigop nat O (fun i0 : nat => p1 i0) 
                                      (S O) times 
                                      (fun i0 : nat => f1 i0))
                                   (bigop nat m (fun i0 : nat => f i0) 
                                      (S O) times 
                                      (fun i0 : nat => f2 i0)))
                         (p20 : nat -> bool) (__ : le O n1)
                         (sub1 : sub_hk h k O (S m) p1 p20 f1 f2)
                         (sub2 : sub_hk k h (S m) O p20 p1 f2 f1) =>
                       eq_ind_r nat
                         (bigop nat m (fun i0 : nat => p20 i0) 
                            (S O) times (fun i0 : nat => f2 i0))
                         (fun x : nat =>
                          eq nat
                            (bigop nat O (fun i0 : nat => p1 i0) 
                               (S O) times (fun i0 : nat => f1 i0)) x)
                         (Hind p20 (le_O_n n1)
                            (sub_hkO h k O m p1 p20 f1 f2 (refl nat O))
                            (transitive_sub (fun x : nat => x)
                               (fun x : nat => x) k h m 
                               (S m) O p20 p20 p1 f2 f2 f1
                               (sub_lt f2 p20 m (S m) (le_n_Sn m)) sub2))
                         (bigop nat (S m) (fun i0 : nat => p20 i0) 
                            (S O) times (fun i0 : nat => f2 i0))
                         (bigop_Sfalse nat m p20 (S O) times f2
                            (sub0_to_false k h O (S m) p1 p20 f1 f2
                               (refl nat O) sub2 m
                               (eq_coerc
                                  (lt (mod m O)
                                     (plus
                                        (plus (mod m O) (times O (div m O)))
                                        (S O))) (lt m (S m))
                                  (lt_plus_Sn_r (mod m O) 
                                     (times O (div m O)) O)
                                  (rewrite_l nat m
                                     (fun __1 : nat =>
                                      eq Prop (lt (mod m O) (plus __1 (S O)))
                                        (lt m (S m)))
                                     (rewrite_l nat m
                                        (fun __1 : nat =>
                                         eq Prop (lt __1 (plus m (S O)))
                                           (lt m (S m)))
                                        (rewrite_l nat 
                                           (S m)
                                           (fun __1 : nat =>
                                            eq Prop (lt m __1) (lt m (S m)))
                                           (refl Prop (lt m (S m)))
                                           (plus m (S O))
                                           (rewrite_r nat 
                                              (plus m O)
                                              (fun __1 : nat =>
                                               eq nat (S __1) (plus m (S O)))
                                              (plus_n_Sm m O) m 
                                              (plus_n_O m))) 
                                        (mod m O)
                                        (rewrite_r nat 
                                           (plus O (mod m O))
                                           (fun __1 : nat => eq nat m __1)
                                           (rewrite_l nat 
                                              (plus (mod m O) O)
                                              (fun __1 : nat => eq nat m __1)
                                              (rewrite_r nat
                                                 (times O (div m O))
                                                 (fun __1 : nat =>
                                                 eq nat m
                                                 (plus (mod m O) __1))
                                                 (rewrite_l nat
                                                 (plus 
                                                 (times O (div m O))
                                                 (mod m O))
                                                 (fun __1 : nat =>
                                                 eq nat m __1)
                                                 (let_clause_10471 n1 n2 p1
                                                 p2 f1 f2 _clearme h
                                                 _clearme0 k _clearme1
                                                 _clearme2 same i m Hind p20
                                                 __ sub1 sub2 m O)
                                                 (plus 
                                                 (mod m O)
                                                 (times O (div m O)))
                                                 (commutative_plus
                                                 (times O (div m O))
                                                 (mod m O))) O
                                                 (times_O_n (div m O)))
                                              (plus O (mod m O))
                                              (commutative_plus (mod m O) O))
                                           (mod m O) 
                                           (plus_O_n (mod m O))))
                                     (plus (mod m O) (times O (div m O)))
                                     (rewrite_l nat
                                        (plus (times O (div m O)) (mod m O))
                                        (fun __1 : nat => eq nat m __1)
                                        (let_clause_10471 n1 n2 p1 p2 f1 f2
                                           _clearme h _clearme0 k _clearme1
                                           _clearme2 same i m Hind p20 __
                                           sub1 sub2 m O)
                                        (plus (mod m O) (times O (div m O)))
                                        (commutative_plus 
                                           (times O (div m O)) 
                                           (mod m O)))))))) n2)
                   (fun (n : nat)
                      (Hind : forall f : nat -> bool,
                              le n n1 ->
                              sub_hk h k n n2 p1 f f1 f2 ->
                              sub_hk k h n2 n f p1 f2 f1 ->
                              eq nat
                                (bigop nat n (fun i0 : nat => p1 i0) 
                                   (S O) times (fun i0 : nat => f1 i0))
                                (bigop nat n2 (fun i0 : nat => f i0) 
                                   (S O) times (fun i0 : nat => f2 i0)))
                      (p20 : nat -> bool) (ltn : le (S n) n1)
                      (sub1 : sub_hk h k (S n) n2 p1 p20 f1 f2)
                      (sub2 : sub_hk k h n2 (S n) p20 p1 f2 f1) =>
                    match_Or_prop (eq bool (p1 n) true)
                      (eq bool (p1 n) false)
                      (eq nat
                         (bigop nat (S n) (fun i0 : nat => p1 i0) 
                            (S O) times (fun i0 : nat => f1 i0))
                         (bigop nat n2 (fun i0 : nat => p20 i0) 
                            (S O) times (fun i0 : nat => f2 i0)))
                      (fun p1n : eq bool (p1 n) true =>
                       eq_ind_r nat
                         (times (f1 n)
                            (bigop nat n (fun i0 : nat => p1 i0) 
                               (S O) times (fun i0 : nat => f1 i0)))
                         (fun x : nat =>
                          eq nat x
                            (bigop nat n2 (fun i0 : nat => p20 i0) 
                               (S O) times (fun i0 : nat => f2 i0)))
                         (match_And_prop
                            (And (lt (h n) n2) (eq bool (p20 (h n)) true))
                            (eq nat (k (h n)) n)
                            (eq nat
                               (times (f1 n)
                                  (bigop nat n (fun i0 : nat => p1 i0) 
                                     (S O) times (fun i0 : nat => f1 i0)))
                               (bigop nat n2 (fun i0 : nat => p20 i0) 
                                  (S O) times (fun i0 : nat => f2 i0)))
                            (fun
                               _clearme3 : And (lt (h n) n2)
                                             (eq bool (p20 (h n)) true) =>
                             match_And_prop (lt (h n) n2)
                               (eq bool (p20 (h n)) true)
                               (eq nat (k (h n)) n ->
                                eq nat
                                  (times (f1 n)
                                     (bigop nat n 
                                        (fun i0 : nat => p1 i0) 
                                        (S O) times 
                                        (fun i0 : nat => f1 i0)))
                                  (bigop nat n2 (fun i0 : nat => p20 i0)
                                     (S O) times (fun i0 : nat => f2 i0)))
                               (fun (hn : lt (h n) n2)
                                  (p2hn : eq bool (p20 (h n)) true)
                                  (eqn : eq nat (k (h n)) n) =>
                                eq_ind_r nat
                                  (times (f2 (h n))
                                     (bigop nat n2
                                        (fun x : nat =>
                                         andb (notb (eqb (h n) x)) (p20 x))
                                        (S O) times 
                                        (fun x : nat => f2 x)))
                                  (fun x : nat =>
                                   eq nat
                                     (times (f1 n)
                                        (bigop nat n 
                                           (fun i0 : nat => p1 i0) 
                                           (S O) times
                                           (fun i0 : nat => f1 i0))) x)
                                  (eq_ind_r nat (f2 (h n))
                                     (fun x : nat =>
                                      eq nat
                                        (times x
                                           (bigop nat n
                                              (fun i0 : nat => p1 i0) 
                                              (S O) times
                                              (fun i0 : nat => f1 i0)))
                                        (times (f2 (h n))
                                           (bigop nat n2
                                              (fun x0 : nat =>
                                               andb 
                                                 (notb (eqb (h n) x0))
                                                 (p20 x0)) 
                                              (S O) times
                                              (fun x0 : nat => f2 x0))))
                                     (eq_f nat nat 
                                        (times (f2 (h n)))
                                        (bigop nat n 
                                           (fun i0 : nat => p1 i0) 
                                           (S O) times
                                           (fun i0 : nat => f1 i0))
                                        (bigop nat n2
                                           (fun x : nat =>
                                            andb (notb (eqb (h n) x)) (p20 x))
                                           (S O) times 
                                           (fun x : nat => f2 x))
                                        (Hind
                                           (fun __ : nat =>
                                            andb (notb (eqb (h n) __))
                                              (p20 __)) 
                                           (lt_to_le n n1 ltn)
                                           (fun (i0 : nat) 
                                              (ltin : lt i0 n)
                                              (p1i : eq bool (p1 i0) true) =>
                                            match_And_prop
                                              (And 
                                                 (lt (h i0) n2)
                                                 (eq bool (p20 (h i0)) true))
                                              (eq nat (k (h i0)) i0)
                                              (And
                                                 (And 
                                                 (lt (h i0) n2)
                                                 (eq bool
                                                 (andb
                                                 (notb (eqb (h n) (h i0)))
                                                 (p20 (h i0))) true))
                                                 (eq nat (k (h i0)) i0))
                                              (fun
                                                 _clearme4 : 
                                                 And 
                                                 (lt (h i0) n2)
                                                 (eq bool (p20 (h i0)) true)
                                               =>
                                               match_And_prop 
                                                 (lt (h i0) n2)
                                                 (eq bool (p20 (h i0)) true)
                                                 (eq nat (k (h i0)) i0 ->
                                                 And
                                                 (And 
                                                 (lt (h i0) n2)
                                                 (eq bool
                                                 (andb
                                                 (notb (eqb (h n) (h i0)))
                                                 (p20 (h i0))) true))
                                                 (eq nat (k (h i0)) i0))
                                                 (fun 
                                                 (h1i : lt (h i0) n2)
                                                 (p2h1i : 
                                                 eq bool 
                                                 (p20 (h i0)) true)
                                                 (eqi : eq nat (k (h i0)) i0)
                                                 (z : Prop)
                                                 (f : 
                                                 And 
                                                 (lt (h i0) n2)
                                                 (eq bool
                                                 (andb
                                                 (notb (eqb (h n) (h i0)))
                                                 (p20 (h i0))) true) ->
                                                 eq nat (k (h i0)) i0 -> z)
                                                 =>
                                                 f
                                                 (fun 
                                                 (z0 : Prop)
                                                 (f20 : 
                                                 lt (h i0) n2 ->
                                                 eq bool
                                                 (andb
                                                 (notb (eqb (h n) (h i0)))
                                                 (p20 (h i0))) true -> z0) =>
                                                 f20 h1i
                                                 (eq_ind_r bool false
                                                 (fun x : bool =>
                                                 eq bool
                                                 (andb (notb x) (p20 (h i0)))
                                                 true)
                                                 (sym_eq_match_bool_type_false
                                                 bool false true
                                                 (fun y : bool =>
                                                 eq bool
                                                 (match_bool_type bool
                                                 (p20 (h i0)) false y) true)
                                                 (sym_eq_match_bool_type_true
                                                 bool 
                                                 (p20 (h i0)) false
                                                 (fun y : bool =>
                                                 eq bool y true)
                                                 (rewrite_r bool true
                                                 (fun __ : bool =>
                                                 eq bool __ true)
                                                 (refl bool true)
                                                 (p20 (h i0)) p2h1i)))
                                                 (eqb (h n) (h i0))
                                                 (not_eq_to_eqb_false 
                                                 (h n) 
                                                 (h i0)
                                                 (not_to_not
                                                 (eq nat (h n) (h i0))
                                                 (eq nat i0 n)
                                                 (fun
                                                 auto : eq nat (h n) (h i0)
                                                 =>
                                                 rewrite_r nat n
                                                 (fun __ : nat => eq nat __ n)
                                                 (refl nat n) i0
                                                 (rewrite_l nat 
                                                 (k (h n))
                                                 (fun __ : nat => eq nat __ n)
                                                 eqn i0
                                                 (rewrite_r nat 
                                                 (h i0)
                                                 (fun __ : nat =>
                                                 eq nat (k __) i0) eqi 
                                                 (h n) auto)))
                                                 (lt_to_not_eq i0 n ltin)))))
                                                 (rewrite_r nat i0
                                                 (fun __ : nat =>
                                                 eq nat __ i0) 
                                                 (refl nat i0) 
                                                 (k (h i0)) eqi)) _clearme4)
                                              (sub1 i0 
                                                 (le_S (S i0) n ltin) p1i))
                                           (fun (j : nat) 
                                              (ltj : lt j n2)
                                              (p2j : 
                                               eq bool
                                                 (andb 
                                                 (notb (eqb (h n) j)) 
                                                 (p20 j)) true) =>
                                            match_And_prop
                                              (And 
                                                 (lt (k j) (S n))
                                                 (eq bool (p1 (k j)) true))
                                              (eq nat (h (k j)) j)
                                              (And
                                                 (And 
                                                 (lt (k j) n)
                                                 (eq bool (p1 (k j)) true))
                                                 (eq nat (h (k j)) j))
                                              (fun
                                                 _clearme4 : 
                                                 And 
                                                 (lt (k j) (S n))
                                                 (eq bool (p1 (k j)) true) =>
                                               match_And_prop
                                                 (lt (k j) (S n))
                                                 (eq bool (p1 (k j)) true)
                                                 (eq nat (h (k j)) j ->
                                                 And
                                                 (And 
                                                 (lt (k j) n)
                                                 (eq bool (p1 (k j)) true))
                                                 (eq nat (h (k j)) j))
                                                 (fun 
                                                 (ltkj : lt (k j) (S n))
                                                 (p1kj : 
                                                 eq bool 
                                                 (p1 (k j)) true)
                                                 (eqj : eq nat (h (k j)) j)
                                                 (z : Prop)
                                                 (f : 
                                                 And 
                                                 (lt (k j) n)
                                                 (eq bool (p1 (k j)) true) ->
                                                 eq nat (h (k j)) j -> z) =>
                                                 f
                                                 (fun 
                                                 (z0 : Prop)
                                                 (f20 : 
                                                 lt (k j) n ->
                                                 eq bool (p1 (k j)) true ->
                                                 z0) =>
                                                 f20
                                                 (match_Or_prop 
                                                 (lt (k j) n)
                                                 (eq nat (k j) n)
                                                 (lt (k j) n)
                                                 (fun auto : lt (k j) n =>
                                                 auto)
                                                 (fun eqkj : eq nat (k j) n
                                                 =>
                                                 falsity 
                                                 (lt (k j) n)
                                                 (eqb_elim 
                                                 (h n) j
                                                 (fun __ : bool =>
                                                 eq bool
                                                 (andb (notb __) (p20 j))
                                                 true -> False)
                                                 (sym_eq_match_bool_type_true
                                                 bool false true
                                                 (fun y : bool =>
                                                 eq nat (h n) j ->
                                                 eq bool
                                                 (match_bool_type bool
                                                 (p20 j) false y) true ->
                                                 False)
                                                 (sym_eq_match_bool_type_false
                                                 bool 
                                                 (p20 j) false
                                                 (fun y : bool =>
                                                 eq nat (h n) j ->
                                                 eq bool y true -> False)
                                                 (fun 
                                                 (auto : eq nat (h n) j)
                                                 (auto' : eq bool false true)
                                                 =>
                                                 absurd 
                                                 (eq bool true false)
                                                 (rewrite_r bool true
                                                 (fun __ : bool =>
                                                 eq bool true __)
                                                 (refl bool true) false auto')
                                                 not_eq_true_false)))
                                                 (sym_eq_match_bool_type_false
                                                 bool false true
                                                 (fun y : bool =>
                                                 Not (eq nat (h n) j) ->
                                                 eq bool
                                                 (match_bool_type bool
                                                 (p20 j) false y) true ->
                                                 False)
                                                 (sym_eq_match_bool_type_true
                                                 bool 
                                                 (p20 j) false
                                                 (fun y : bool =>
                                                 Not (eq nat (h n) j) ->
                                                 eq bool y true -> False)
                                                 (fun
                                                 (auto : 
                                                 Not (eq nat (h n) j))
                                                 (auto' : 
                                                 eq bool 
                                                 (p20 j) true) =>
                                                 absurd 
                                                 (eq nat (h n) j)
                                                 (rewrite_r nat j
                                                 (fun __ : nat => eq nat __ j)
                                                 (refl nat j) 
                                                 (h n)
                                                 (rewrite_l nat 
                                                 (k j)
                                                 (fun __ : nat =>
                                                 eq nat (h __) j) eqj n eqkj))
                                                 auto))) p2j))
                                                 (le_to_or_lt_eq 
                                                 (k j) n
                                                 (le_S_S_to_le (k j) n ltkj)))
                                                 (rewrite_r bool true
                                                 (fun __ : bool =>
                                                 eq bool __ true)
                                                 (refl bool true) 
                                                 (p1 (k j)) p1kj))
                                                 (rewrite_r nat j
                                                 (fun __ : nat => eq nat __ j)
                                                 (refl nat j) 
                                                 (h (k j)) eqj)) _clearme4)
                                              (sub2 j ltj
                                                 (andb_true_r
                                                 (notb (eqb (h n) j)) 
                                                 (p20 j) p2j))))) 
                                     (f1 n)
                                     (same n ltn
                                        (rewrite_r bool true
                                           (fun __ : bool => eq bool __ true)
                                           (refl bool true) 
                                           (p1 n) p1n)))
                                  (bigop nat n2 (fun x : nat => p20 x) 
                                     (S O) times (fun x : nat => f2 x))
                                  (bigop_diff p20 f2 
                                     (h n) n2 hn
                                     (rewrite_r bool true
                                        (fun __ : bool => eq bool __ true)
                                        (refl bool true) 
                                        (p20 (h n)) p2hn))) _clearme3)
                            (sub1 n (le_n (S n)) p1n))
                         (bigop nat (S n) (fun i0 : nat => p1 i0) 
                            (S O) times (fun i0 : nat => f1 i0))
                         (bigop_Strue nat n p1 (S O) times f1
                            (rewrite_r bool true
                               (fun __ : bool => eq bool __ true)
                               (refl bool true) (p1 n) p1n)))
                      (fun p1n : eq bool (p1 n) false =>
                       eq_ind_r nat
                         (bigop nat n (fun i0 : nat => p1 i0) 
                            (S O) times (fun i0 : nat => f1 i0))
                         (fun x : nat =>
                          eq nat x
                            (bigop nat n2 (fun i0 : nat => p20 i0) 
                               (S O) times (fun i0 : nat => f2 i0)))
                         (Hind p20 (lt_to_le n n1 ltn)
                            (transitive_sub (fun x : nat => x)
                               (fun x : nat => x) h k n 
                               (S n) n2 p1 p1 p20 f1 f1 f2
                               (sub_lt f1 p1 n (S n) (le_n_Sn n)) sub1)
                            (fun (i0 : nat) (lti : lt i0 n2)
                               (p2i : eq bool (p20 i0) true) =>
                             match_And_prop
                               (And (lt (k i0) (S n))
                                  (eq bool (p1 (k i0)) true))
                               (eq nat (h (k i0)) i0)
                               (And
                                  (And (lt (k i0) n)
                                     (eq bool (p1 (k i0)) true))
                                  (eq nat (h (k i0)) i0))
                               (fun
                                  _clearme3 : And 
                                                (lt (k i0) (S n))
                                                (eq bool (p1 (k i0)) true) =>
                                match_And_prop (lt (k i0) (S n))
                                  (eq bool (p1 (k i0)) true)
                                  (eq nat (h (k i0)) i0 ->
                                   And
                                     (And (lt (k i0) n)
                                        (eq bool (p1 (k i0)) true))
                                     (eq nat (h (k i0)) i0))
                                  (fun (ltki : lt (k i0) (S n))
                                     (p1ki : eq bool (p1 (k i0)) true)
                                     (eqi : eq nat (h (k i0)) i0) 
                                     (z : Prop)
                                     (f : And (lt (k i0) n)
                                            (eq bool (p1 (k i0)) true) ->
                                          eq nat (h (k i0)) i0 -> z) =>
                                   f
                                     (fun (z0 : Prop)
                                        (f20 : lt (k i0) n ->
                                               eq bool (p1 (k i0)) true -> z0)
                                      =>
                                      f20
                                        (match_Or_prop 
                                           (lt (k i0) n) 
                                           (eq nat (k i0) n) 
                                           (lt (k i0) n)
                                           (fun auto : lt (k i0) n => auto)
                                           (fun eqki : eq nat (k i0) n =>
                                            falsity 
                                              (lt (k i0) n)
                                              (absurd 
                                                 (eq bool true false)
                                                 (rewrite_l bool true
                                                 (fun __ : bool =>
                                                 eq bool true __)
                                                 (refl bool true) false
                                                 (rewrite_l bool 
                                                 (p1 n)
                                                 (fun __ : bool =>
                                                 eq bool __ false) p1n true
                                                 (rewrite_l nat 
                                                 (k i0)
                                                 (fun __ : nat =>
                                                 eq bool (p1 __) true) p1ki n
                                                 eqki))) not_eq_true_false))
                                           (le_to_or_lt_eq 
                                              (k i0) n
                                              (le_S_S_to_le (k i0) n ltki)))
                                        (rewrite_r bool true
                                           (fun __ : bool => eq bool __ true)
                                           (refl bool true) 
                                           (p1 (k i0)) p1ki))
                                     (rewrite_r nat i0
                                        (fun __ : nat => eq nat __ i0)
                                        (refl nat i0) 
                                        (h (k i0)) eqi)) _clearme3)
                               (sub2 i0 lti p2i)))
                         (bigop nat (S n) (fun i0 : nat => p1 i0) 
                            (S O) times (fun i0 : nat => f1 i0))
                         (bigop_Sfalse nat n p1 (S O) times f1
                            (rewrite_r bool false
                               (fun __ : bool => eq bool __ false)
                               (refl bool false) (p1 n) p1n)))
                      (true_or_false (p1 n))) i p2)) _clearme2) _clearme1)
       _clearme0) _clearme.


Definition exp : nat -> nat -> nat := Nat.pow.
Definition exp_body : nat -> nat -> nat := exp.

Theorem eq_exp :
  forall n m : nat,
  leibniz nat (exp n m) (filter_nat_type nat (exp_body n) m).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.

Definition sym_eq_exp :
  forall n m : nat,
  leibniz nat (filter_nat_type nat (exp_body n) m) (exp n m) :=
  fun n m : nat =>
  sym_leibniz nat (exp n m) (filter_nat_type nat (exp_body n) m) (eq_exp n m).
Theorem eq_exp_body_O : forall n : nat, leibniz nat (exp_body n O) (S O).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.

Definition sym_eq_exp_body_O :
  forall n : nat, leibniz nat (S O) (exp_body n O) :=
  fun n : nat => sym_leibniz nat (exp_body n O) (S O) (eq_exp_body_O n).
Theorem eq_exp_body_S :
  forall n m : nat, leibniz nat (exp_body n (S m)) (times (exp n m) n).
Proof.
  (intros **; apply to_leibniz).
  (simpl).
  (unfold exp_body).
  (apply commutative_times).
Qed.

Definition sym_eq_exp_body_S :
  forall n m : nat, leibniz nat (times (exp n m) n) (exp_body n (S m)) :=
  fun n m : nat =>
  sym_leibniz nat (exp_body n (S m)) (times (exp n m) n) (eq_exp_body_S n m).
Definition lt_O_exp : forall n m : nat, lt O n -> lt O (exp n m) :=
  fun n m : nat =>
  nat_ind (fun _x_365 : nat => lt O n -> lt O (exp n _x_365))
    (sym_eq_exp n O (fun y : nat => lt O n -> lt O y)
       (sym_eq_filter_nat_type_O nat (exp_body n)
          (fun y : nat => lt O n -> lt O y)
          (sym_eq_exp_body_O n (fun y : nat => lt O n -> lt O y)
             (fun auto : le (S O) n => lt_O_S O))))
    (fun a : nat =>
     sym_eq_exp n (S a)
       (fun y : nat => (lt O n -> lt O (exp n a)) -> lt O n -> lt O y)
       (sym_eq_filter_nat_type_S nat (exp_body n) a
          (fun y : nat => (lt O n -> lt O (exp n a)) -> lt O n -> lt O y)
          (sym_eq_exp_body_S n a
             (fun y : nat => (lt O n -> lt O (exp n a)) -> lt O n -> lt O y)
             (fun (Hind : le (S O) n -> le (S O) (exp n a))
                (posn : le (S O) n) =>
              eq_times_body_O
                (fun y : nat -> nat => le (S (y (S O))) (times (exp n a) n))
                (eq_filter_nat_type_O (nat -> nat) times_body
                   (fun y : nat -> nat =>
                    le (S (y (S O))) (times (exp n a) n))
                   (eq_times O
                      (fun y : nat -> nat =>
                       le (S (y (S O))) (times (exp n a) n))
                      (eq_plus_body_O
                         (fun y : nat -> nat =>
                          le (S (y (times O (S O)))) (times (exp n a) n))
                         (eq_filter_nat_type_O (nat -> nat) plus_body
                            (fun y : nat -> nat =>
                             le (S (y (times O (S O)))) (times (exp n a) n))
                            (eq_plus O
                               (fun y : nat -> nat =>
                                le (S (y (times O (S O))))
                                  (times (exp n a) n))
                               (eq_plus_body_S O
                                  (fun y : nat -> nat =>
                                   le (y (times O (S O))) (times (exp n a) n))
                                  (eq_filter_nat_type_S 
                                     (nat -> nat) plus_body O
                                     (fun y : nat -> nat =>
                                      le (y (times O (S O)))
                                        (times (exp n a) n))
                                     (eq_plus (S O)
                                        (fun y : nat -> nat =>
                                         le (y (times O (S O)))
                                           (times (exp n a) n))
                                        (eq_times_body_S O
                                           (fun y : nat -> nat =>
                                            le (y (S O)) (times (exp n a) n))
                                           (eq_filter_nat_type_S 
                                              (nat -> nat) times_body O
                                              (fun y : nat -> nat =>
                                               le 
                                                 (y (S O))
                                                 (times (exp n a) n))
                                              (eq_times 
                                                 (S O)
                                                 (fun y : nat -> nat =>
                                                 le 
                                                 (y (S O))
                                                 (times (exp n a) n))
                                                 (le_times 
                                                 (S O) 
                                                 (exp n a) 
                                                 (S O) n 
                                                 (Hind posn) posn))))))))))))))))
    m.
Definition exp_pi_l :
  forall (n a : nat) (f : nat -> nat),
  eq nat
    (times (exp a n)
       (bigop nat n (fun i : nat => true) (S O) times (fun i : nat => f i)))
    (bigop nat n (fun i : nat => true) (S O) times
       (fun i : nat => times a (f i))) :=
  fun (n a : nat) (f : nat -> nat) =>
  nat_ind
    (fun _x_365 : nat =>
     eq nat
       (times (exp a _x_365)
          (bigop nat _x_365 (fun i : nat => true) 
             (S O) times (fun i : nat => f i)))
       (bigop nat _x_365 (fun i : nat => true) (S O) times
          (fun i : nat => times a (f i))))
    (sym_eq_bigop_O nat
       (fun
          y : (nat -> bool) ->
              nat -> (nat -> nat -> nat) -> (nat -> nat) -> nat =>
        eq nat
          (times (exp a O)
             (bigop nat O (fun i : nat => true) (S O) times
                (fun i : nat => f i)))
          (y (fun i : nat => true) (S O) times (fun i : nat => times a (f i))))
       (sym_eq_bigop_body_O nat
          (fun
             y : (nat -> bool) ->
                 nat -> (nat -> nat -> nat) -> (nat -> nat) -> nat =>
           eq nat
             (times (exp a O)
                (bigop nat O (fun i : nat => true) 
                   (S O) times (fun i : nat => f i)))
             (y (fun i : nat => true) (S O) times
                (fun i : nat => times a (f i))))
          (eq_times_body_O
             (fun y : nat -> nat =>
              eq nat
                (times (exp a O)
                   (bigop nat O (fun i : nat => true) 
                      (S O) times (fun i : nat => f i))) 
                (S (y (S O))))
             (eq_filter_nat_type_O (nat -> nat) times_body
                (fun y : nat -> nat =>
                 eq nat
                   (times (exp a O)
                      (bigop nat O (fun i : nat => true) 
                         (S O) times (fun i : nat => f i))) 
                   (S (y (S O))))
                (eq_times O
                   (fun y : nat -> nat =>
                    eq nat
                      (times (exp a O)
                         (bigop nat O (fun i : nat => true) 
                            (S O) times (fun i : nat => f i))) 
                      (S (y (S O))))
                   (eq_plus_body_O
                      (fun y : nat -> nat =>
                       eq nat
                         (times (exp a O)
                            (bigop nat O (fun i : nat => true) 
                               (S O) times (fun i : nat => f i)))
                         (S (y (times O (S O)))))
                      (eq_filter_nat_type_O (nat -> nat) plus_body
                         (fun y : nat -> nat =>
                          eq nat
                            (times (exp a O)
                               (bigop nat O (fun i : nat => true) 
                                  (S O) times (fun i : nat => f i)))
                            (S (y (times O (S O)))))
                         (eq_plus O
                            (fun y : nat -> nat =>
                             eq nat
                               (times (exp a O)
                                  (bigop nat O (fun i : nat => true) 
                                     (S O) times (fun i : nat => f i)))
                               (S (y (times O (S O)))))
                            (eq_plus_body_S O
                               (fun y : nat -> nat =>
                                eq nat
                                  (times (exp a O)
                                     (bigop nat O 
                                        (fun i : nat => true) 
                                        (S O) times 
                                        (fun i : nat => f i)))
                                  (y (times O (S O))))
                               (eq_filter_nat_type_S 
                                  (nat -> nat) plus_body O
                                  (fun y : nat -> nat =>
                                   eq nat
                                     (times (exp a O)
                                        (bigop nat O 
                                           (fun i : nat => true) 
                                           (S O) times 
                                           (fun i : nat => f i)))
                                     (y (times O (S O))))
                                  (eq_plus (S O)
                                     (fun y : nat -> nat =>
                                      eq nat
                                        (times (exp a O)
                                           (bigop nat O 
                                              (fun i : nat => true) 
                                              (S O) times
                                              (fun i : nat => f i)))
                                        (y (times O (S O))))
                                     (eq_times_body_S O
                                        (fun y : nat -> nat =>
                                         eq nat
                                           (times 
                                              (exp a O)
                                              (bigop nat O
                                                 (fun i : nat => true) 
                                                 (S O) times
                                                 (fun i : nat => f i)))
                                           (y (S O)))
                                        (eq_filter_nat_type_S 
                                           (nat -> nat) times_body O
                                           (fun y : nat -> nat =>
                                            eq nat
                                              (times 
                                                 (exp a O)
                                                 (bigop nat O
                                                 (fun i : nat => true) 
                                                 (S O) times
                                                 (fun i : nat => f i)))
                                              (y (S O)))
                                           (eq_times 
                                              (S O)
                                              (fun y : nat -> nat =>
                                               eq nat
                                                 (times 
                                                 (exp a O)
                                                 (bigop nat O
                                                 (fun i : nat => true) 
                                                 (S O) times
                                                 (fun i : nat => f i)))
                                                 (y (S O)))
                                              (eq_match_nat_type_O nat 
                                                 (S O)
                                                 (fun k : nat =>
                                                 match_bool_type nat
                                                 (times 
                                                 (times a (f k))
                                                 (bigop nat k
                                                 (fun i : nat => true) 
                                                 (S O) times
                                                 (fun i : nat =>
                                                 times a (f i))))
                                                 (bigop nat k
                                                 (fun i : nat => true) 
                                                 (S O) times
                                                 (fun i : nat =>
                                                 times a (f i))) true)
                                                 (fun y : nat =>
                                                 eq nat
                                                 (times 
                                                 (exp a O)
                                                 (bigop nat O
                                                 (fun i : nat => true) 
                                                 (S O) times
                                                 (fun i : nat => f i)))
                                                 (times (S O) y))
                                                 (eq_exp_body_O a
                                                 (fun y : nat =>
                                                 eq nat
                                                 (times 
                                                 (exp a O)
                                                 (bigop nat O
                                                 (fun i : nat => true) 
                                                 (S O) times
                                                 (fun i : nat => f i)))
                                                 (times y
                                                 ((fun 
                                                 (p : nat -> bool)
                                                 (nil : nat)
                                                 (op : nat -> nat -> nat)
                                                 (f0 : nat -> nat) =>
                                                 match_nat_type nat nil
                                                 (fun k : nat =>
                                                 match_bool_type nat
                                                 (op 
                                                 (f0 k)
                                                 (bigop nat k p nil op f0))
                                                 (bigop nat k p nil op f0)
                                                 (p k)) O)
                                                 (fun i : nat => true) 
                                                 (S O) times
                                                 (fun i : nat =>
                                                 times a (f i)))))
                                                 (eq_filter_nat_type_O nat
                                                 (exp_body a)
                                                 (fun y : nat =>
                                                 eq nat
                                                 (times 
                                                 (exp a O)
                                                 (bigop nat O
                                                 (fun i : nat => true) 
                                                 (S O) times
                                                 (fun i : nat => f i)))
                                                 (times y
                                                 ((fun 
                                                 (p : nat -> bool)
                                                 (nil : nat)
                                                 (op : nat -> nat -> nat)
                                                 (f0 : nat -> nat) =>
                                                 match_nat_type nat nil
                                                 (fun k : nat =>
                                                 match_bool_type nat
                                                 (op 
                                                 (f0 k)
                                                 (bigop nat k p nil op f0))
                                                 (bigop nat k p nil op f0)
                                                 (p k)) O)
                                                 (fun i : nat => true) 
                                                 (S O) times
                                                 (fun i : nat =>
                                                 times a (f i)))))
                                                 (eq_exp a O
                                                 (fun y : nat =>
                                                 eq nat
                                                 (times 
                                                 (exp a O)
                                                 (bigop nat O
                                                 (fun i : nat => true) 
                                                 (S O) times
                                                 (fun i : nat => f i)))
                                                 (times y
                                                 ((fun 
                                                 (p : nat -> bool)
                                                 (nil : nat)
                                                 (op : nat -> nat -> nat)
                                                 (f0 : nat -> nat) =>
                                                 match_nat_type nat nil
                                                 (fun k : nat =>
                                                 match_bool_type nat
                                                 (op 
                                                 (f0 k)
                                                 (bigop nat k p nil op f0))
                                                 (bigop nat k p nil op f0)
                                                 (p k)) O)
                                                 (fun i : nat => true) 
                                                 (S O) times
                                                 (fun i : nat =>
                                                 times a (f i)))))
                                                 (sym_eq_match_nat_type_O nat
                                                 (S O)
                                                 (fun k : nat =>
                                                 match_bool_type nat
                                                 (times 
                                                 (times a (f k))
                                                 (bigop nat k
                                                 (fun i : nat => true) 
                                                 (S O) times
                                                 (fun i : nat =>
                                                 times a (f i))))
                                                 (bigop nat k
                                                 (fun i : nat => true) 
                                                 (S O) times
                                                 (fun i : nat =>
                                                 times a (f i))) true)
                                                 (fun y : nat =>
                                                 eq nat
                                                 (times 
                                                 (exp a O)
                                                 (bigop nat O
                                                 (fun i : nat => true) 
                                                 (S O) times
                                                 (fun i : nat => f i)))
                                                 (times (exp a O) y))
                                                 (eq_bigop_body_O nat
                                                 (fun
                                                 y : 
                                                 (nat -> bool) ->
                                                 nat ->
                                                 (nat -> nat -> nat) ->
                                                 (nat -> nat) -> nat =>
                                                 eq nat
                                                 (times 
                                                 (exp a O)
                                                 (bigop nat O
                                                 (fun i : nat => true) 
                                                 (S O) times
                                                 (fun i : nat => f i)))
                                                 (times 
                                                 (exp a O)
                                                 (y (fun i : nat => true)
                                                 (S O) times
                                                 (fun i : nat => f i))))
                                                 (eq_bigop_O nat
                                                 (fun
                                                 y : 
                                                 (nat -> bool) ->
                                                 nat ->
                                                 (nat -> nat -> nat) ->
                                                 (nat -> nat) -> nat =>
                                                 eq nat
                                                 (times 
                                                 (exp a O)
                                                 (bigop nat O
                                                 (fun i : nat => true) 
                                                 (S O) times
                                                 (fun i : nat => f i)))
                                                 (times 
                                                 (exp a O)
                                                 (y (fun i : nat => true)
                                                 (S O) times
                                                 (fun i : nat => f i))))
                                                 (refl nat
                                                 (times 
                                                 (exp a O)
                                                 (bigop nat O
                                                 (fun i : nat => true) 
                                                 (S O) times
                                                 (fun i : nat => f i)))))))))))))))))))))))))
    (fun (i : nat)
       (Hind : eq nat
                 (times (exp a i)
                    (bigop nat i (fun i0 : nat => true) 
                       (S O) times (fun i0 : nat => f i0)))
                 (bigop nat i (fun i0 : nat => true) 
                    (S O) times (fun i0 : nat => times a (f i0)))) =>
     eq_ind_r nat
       (times (f i)
          (bigop nat i (fun i0 : nat => true) (S O) times
             (fun i0 : nat => f i0)))
       (fun x : nat =>
        eq nat (times (exp a (S i)) x)
          (bigop nat (S i) (fun i0 : nat => true) 
             (S O) times (fun i0 : nat => times a (f i0))))
       (eq_ind_r nat
          (times (times a (f i))
             (bigop nat i (fun i0 : nat => true) (S O) times
                (fun i0 : nat => times a (f i0))))
          (fun x : nat =>
           eq nat
             (times (exp a (S i))
                (times (f i)
                   (bigop nat i (fun i0 : nat => true) 
                      (S O) times (fun i0 : nat => f i0)))) x)
          (eq_ind nat
             (times (exp a i)
                (bigop nat i (fun i0 : nat => true) 
                   (S O) times (fun i0 : nat => f i0)))
             (fun x_1 : nat =>
              eq nat
                (times (exp a (S i))
                   (times (f i)
                      (bigop nat i (fun i0 : nat => true) 
                         (S O) times (fun i0 : nat => f i0))))
                (times (times a (f i)) x_1))
             (eq_ind nat
                (times (times (exp a (S i)) (f i))
                   (bigop nat i (fun i0 : nat => true) 
                      (S O) times (fun i0 : nat => f i0)))
                (fun x_1 : nat =>
                 eq nat x_1
                   (times (times a (f i))
                      (times (exp a i)
                         (bigop nat i (fun i0 : nat => true) 
                            (S O) times (fun i0 : nat => f i0)))))
                (eq_ind nat
                   (times (times (times a (f i)) (exp a i))
                      (bigop nat i (fun i0 : nat => true) 
                         (S O) times (fun i0 : nat => f i0)))
                   (fun x_1 : nat =>
                    eq nat
                      (times (times (exp a (S i)) (f i))
                         (bigop nat i (fun i0 : nat => true) 
                            (S O) times (fun i0 : nat => f i0))) x_1)
                   (eq_f2 nat nat nat times (times (exp a (S i)) (f i))
                      (times (times a (f i)) (exp a i))
                      (bigop nat i (fun i0 : nat => true) 
                         (S O) times (fun i0 : nat => f i0))
                      (bigop nat i (fun i0 : nat => true) 
                         (S O) times (fun i0 : nat => f i0))
                      (sym_eq_exp a (S i)
                         (fun y : nat =>
                          eq nat (times y (f i))
                            (times (times a (f i)) (exp a i)))
                         (sym_eq_filter_nat_type_S nat 
                            (exp_body a) i
                            (fun y : nat =>
                             eq nat (times y (f i))
                               (times (times a (f i)) (exp a i)))
                            (sym_eq_exp_body_S a i
                               (fun y : nat =>
                                eq nat (times y (f i))
                                  (times (times a (f i)) (exp a i)))
                               (rewrite_r nat (times a (exp a i))
                                  (fun __ : nat =>
                                   eq nat (times __ (f i))
                                     (times (times a (f i)) (exp a i)))
                                  (rewrite_r nat
                                     (times (f i) (times a (exp a i)))
                                     (fun __ : nat =>
                                      eq nat __
                                        (times (times a (f i)) (exp a i)))
                                     (rewrite_r nat
                                        (times a (times (f i) (exp a i)))
                                        (fun __ : nat =>
                                         eq nat __
                                           (times (times a (f i)) (exp a i)))
                                        (rewrite_r nat
                                           (times (exp a i) (times a (f i)))
                                           (fun __ : nat =>
                                            eq nat
                                              (times a
                                                 (times (f i) (exp a i))) __)
                                           (rewrite_r nat
                                              (times a
                                                 (times (exp a i) (f i)))
                                              (fun __ : nat =>
                                               eq nat
                                                 (times a
                                                 (times (f i) (exp a i))) __)
                                              (rewrite_r nat
                                                 (times (f i) (exp a i))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (times a
                                                 (times (f i) (exp a i)))
                                                 (times a __))
                                                 (refl nat
                                                 (times a
                                                 (times (f i) (exp a i))))
                                                 (times (exp a i) (f i))
                                                 (commutative_times 
                                                 (exp a i) 
                                                 (f i)))
                                              (times 
                                                 (exp a i) 
                                                 (times a (f i)))
                                              (times_times (exp a i) a (f i)))
                                           (times (times a (f i)) (exp a i))
                                           (commutative_times 
                                              (times a (f i)) 
                                              (exp a i)))
                                        (times (f i) (times a (exp a i)))
                                        (times_times (f i) a (exp a i)))
                                     (times (times a (exp a i)) (f i))
                                     (commutative_times 
                                        (times a (exp a i)) 
                                        (f i))) (times (exp a i) a)
                                  (commutative_times (exp a i) a)))))
                      (refl nat
                         (bigop nat i (fun i0 : nat => true) 
                            (S O) times (fun i0 : nat => f i0))))
                   (times (times a (f i))
                      (times (exp a i)
                         (bigop nat i (fun i0 : nat => true) 
                            (S O) times (fun i0 : nat => f i0))))
                   (associative_times (times a (f i)) 
                      (exp a i)
                      (bigop nat i (fun i0 : nat => true) 
                         (S O) times (fun i0 : nat => f i0))))
                (times (exp a (S i))
                   (times (f i)
                      (bigop nat i (fun i0 : nat => true) 
                         (S O) times (fun i0 : nat => f i0))))
                (associative_times (exp a (S i)) (f i)
                   (bigop nat i (fun i0 : nat => true) 
                      (S O) times (fun i0 : nat => f i0))))
             (bigop nat i (fun i0 : nat => true) (S O) times
                (fun i0 : nat => times a (f i0))) Hind)
          (bigop nat (S i) (fun i0 : nat => true) 
             (S O) times (fun i0 : nat => times a (f i0)))
          (bigop_Strue nat i (fun __ : nat => true) 
             (S O) times (fun __ : nat => times a (f __)) 
             (refl bool true)))
       (bigop nat (S i) (fun i0 : nat => true) (S O) times
          (fun i0 : nat => f i0))
       (bigop_Strue nat i (fun __ : nat => true) (S O) times f
          (refl bool true))) n.
Definition exp_pi_bc :
  forall (a b c : nat) (f : nat -> nat),
  eq nat
    (times (exp a (minus c b))
       (bigop nat (minus c b) (fun i : nat => true) 
          (S O) times (fun i : nat => f (plus i b))))
    (bigop nat (minus c b) (fun i : nat => true) (S O) times
       (fun i : nat => times a (f (plus i b)))) :=
  fun (a b c : nat) (f : nat -> nat) =>
  exp_pi_l (minus c b) a (fun __ : nat => f (plus __ b)).

Inductive divides : nat -> nat -> Prop :=
    quot : forall n m q, eq nat m (times n q) -> divides n m.

Theorem quotient : forall n m q : nat, eq nat m (times n q) -> divides n m.
Proof.
  (apply quot).
Qed.

Theorem match_divides_prop :
  forall (n m : nat) (return_type : Prop),
  (forall q : nat, eq nat m (times n q) -> return_type) ->
  divides n m -> return_type.
Proof.
  (intros **).
  (eapply divides_ind).
  (intros **).
  (inversion H0; subst).
  (eapply H).
  (apply H2).
  (apply H0).
Qed.

Definition reflexive_divides : reflexive nat divides :=
  fun x : nat =>
  quotient x x (S O)
    (rewrite_r nat (times x (S O))
       (fun __ : nat => eq nat __ (times x (S O))) 
       (refl nat (times x (S O))) x (times_n_1 x)).
Definition divides_to_div_mod_spec :
  forall n m : nat, lt O n -> divides n m -> div_mod_spec m n (div m n) O :=
  fun (n m : nat) (posn : lt O n) (_clearme : divides n m) =>
  match_divides_prop n m (div_mod_spec m n (div m n) O)
    (fun (q : nat) (eqm : eq nat m (times n q)) =>
     div_mod_spec_intro m n (div m n) O posn
       (eq_ind_r nat (times n q)
          (fun x : nat => eq nat x (plus (times (div x n) n) O))
          (eq_ind_r nat (times q n)
             (fun x : nat => eq nat x (plus (times (div x n) n) O))
             (eq_ind_r nat q
                (fun x : nat => eq nat (times q n) (plus (times x n) O))
                (rewrite_r nat (times n q)
                   (fun __ : nat => eq nat __ (plus (times q n) O))
                   (rewrite_l nat m
                      (fun __ : nat => eq nat __ (plus (times q n) O))
                      (rewrite_r nat (times n q)
                         (fun __ : nat => eq nat m (plus __ O))
                         (rewrite_l nat m
                            (fun __ : nat => eq nat m (plus __ O))
                            (rewrite_l nat m (fun __ : nat => eq nat m __)
                               (refl nat m) (plus m O) 
                               (plus_n_O m)) (times n q) eqm) 
                         (times q n) (commutative_times q n)) 
                      (times n q) eqm) (times q n) 
                   (commutative_times q n)) (div (times q n) n)
                (div_times q n posn)) (times n q) 
             (commutative_times n q)) m eqm)) _clearme.
Definition divides_to_mod_O :
  forall n m : nat, lt O n -> divides n m -> eq nat (mod m n) O :=
  fun (n m : nat) (posn : lt O n) (divnm : divides n m) =>
  div_mod_spec_to_eq2 m n (div m n) (mod m n) (div m n) O
    (div_mod_spec_div_mod m n posn) (divides_to_div_mod_spec n m posn divnm).
Definition mod_O_to_divides :
  forall n m : nat, lt O n -> eq nat (mod m n) O -> divides n m :=
  fun (n m : nat) (auto : lt O n) (auto' : eq nat (mod m n) O) =>
  quotient n m (div m n)
    (rewrite_l nat (times n (div m n))
       (fun __ : nat => eq nat __ (times n (div m n)))
       (refl nat (times n (div m n))) m
       (rewrite_r nat (minus m O)
          (fun __ : nat => eq nat (times n (div m n)) __)
          (rewrite_l nat (mod m n)
             (fun __ : nat => eq nat (times n (div m n)) (minus m __))
             (rewrite_l nat (times (div m n) n)
                (fun __ : nat => eq nat __ (minus m (mod m n)))
                (eq_times_div_minus_mod m n) (times n (div m n))
                (commutative_times (div m n) n)) O auto') m 
          (minus_n_O m))).
Definition divides_n_O : forall n : nat, divides n O :=
  fun n : nat =>
  quotient n O O
    (rewrite_r nat (times n O) (fun __ : nat => eq nat __ (times n O))
       (refl nat (times n O)) O (times_n_O n)).
Definition divides_n_n : forall n : nat, divides n n :=
  fun n : nat => reflexive_divides n.
Definition eq_mod_to_divides :
  forall n m q : nat,
  lt O q -> eq nat (mod n q) (mod m q) -> divides q (minus n m) :=
  fun (n m q : nat) (posq : lt O q) (eqmod : eq nat (mod n q) (mod m q)) =>
  leb_elim n m (fun __ : bool => divides q (minus n m))
    (fun nm : le n m =>
     eq_coerc (divides q O) (divides q (minus n m)) 
       (divides_n_O q)
       (rewrite_r nat O
          (fun __ : nat => eq Prop (divides q O) (divides q __))
          (refl Prop (divides q O)) (minus n m)
          (sym_eq nat O (minus n m)
             (eq_coerc (eq nat (minus O (minus m n)) (minus (plus O n) m))
                (eq nat O (minus n m)) (minus_le_minus_minus_comm m n O nm)
                (rewrite_l nat O
                   (fun __ : nat =>
                    eq Prop (eq nat __ (minus (plus O n) m))
                      (eq nat O (minus n m)))
                   (rewrite_l nat n
                      (fun __ : nat =>
                       eq Prop (eq nat O (minus __ m)) (eq nat O (minus n m)))
                      (refl Prop (eq nat O (minus n m))) 
                      (plus O n) (plus_O_n n)) (minus O (minus m n))
                   (minus_O_n (minus m n)))))))
    (fun nm : Not (le n m) =>
     quotient q (minus n m) (minus (div n q) (div m q))
       (eq_ind_r nat (minus (times q (div n q)) (times q (div m q)))
          (fun x : nat => eq nat (minus n m) x)
          (eq_ind_r nat (times (div n q) q)
             (fun x : nat => eq nat (minus n m) (minus x (times q (div m q))))
             (eq_ind_r nat (times (div m q) q)
                (fun x : nat =>
                 eq nat (minus n m) (minus (times (div n q) q) x))
                (eq_ind_r nat (minus n (mod n q))
                   (fun x : nat =>
                    eq nat (minus n m) (minus x (times (div m q) q)))
                   (eq_ind_r nat
                      (minus n (plus (mod n q) (times (div m q) q)))
                      (fun x : nat => eq nat (minus n m) x)
                      (eq_ind_r nat (mod m q)
                         (fun x : nat =>
                          eq nat (minus n m)
                            (minus n (plus x (times (div m q) q))))
                         (eq_ind_r nat (plus (times (div m q) q) (mod m q))
                            (fun x : nat => eq nat (minus n m) (minus n x))
                            (eq_ind nat m
                               (fun x_1 : nat =>
                                eq nat (minus n m) (minus n x_1))
                               (refl nat (minus n m))
                               (plus (times (div m q) q) (mod m q))
                               (div_mod m q))
                            (plus (mod m q) (times (div m q) q))
                            (commutative_plus (mod m q) (times (div m q) q)))
                         (mod n q) eqmod)
                      (minus (minus n (mod n q)) (times (div m q) q))
                      (minus_plus n (mod n q) (times (div m q) q)))
                   (times (div n q) q)
                   (rewrite_r nat (times q (div n q))
                      (fun __ : nat => eq nat __ (minus n (mod n q)))
                      (rewrite_l nat (times q (div n q))
                         (fun __ : nat => eq nat (times q (div n q)) __)
                         (refl nat (times q (div n q))) 
                         (minus n (mod n q))
                         (rewrite_l nat (times (div n q) q)
                            (fun __ : nat => eq nat __ (minus n (mod n q)))
                            (eq_times_div_minus_mod n q) 
                            (times q (div n q))
                            (commutative_times (div n q) q)))
                      (times (div n q) q) (commutative_times (div n q) q)))
                (times q (div m q)) (commutative_times q (div m q)))
             (times q (div n q)) (commutative_times q (div n q)))
          (times q (minus (div n q) (div m q)))
          (distributive_times_minus q (div n q) (div m q)))).
Definition let_clause_1531 :
  forall n m : nat,
  lt O m -> divides n m -> forall d : nat, eq nat m (times n O) -> eq nat m O :=
  fun (n m : nat) (posm : lt O m) (_clearme : divides n m) 
    (d : nat) (eqm : eq nat m (times n O)) =>
  rewrite_r nat (times n O) (fun __ : nat => eq nat m __) eqm O (times_n_O n).
Definition let_clause_15311 :
  forall n m : nat,
  lt O m ->
  divides n m ->
  forall d p : nat, eq nat m (times n (S p)) -> eq nat m (plus n (times n p)) :=
  fun (n m : nat) (posm : lt O m) (_clearme : divides n m) 
    (d p : nat) (eqm : eq nat m (times n (S p))) =>
  rewrite_r nat (times n (S p)) (fun __ : nat => eq nat m __) eqm
    (plus n (times n p)) (times_n_Sm n p).
Definition divides_to_le :
  forall n m : nat, lt O m -> divides n m -> le n m :=
  fun (n m : nat) (posm : lt O m) (_clearme : divides n m) =>
  match_divides_prop n m (le n m)
    (fun d : nat =>
     match_nat_prop (fun __ : nat => eq nat m (times n __) -> le n m)
       (fun eqm : eq nat m (times n O) =>
        falsity (le n m)
          (absurd (le (S m) O)
             (eq_coerc (le (S O) m) (le (S m) O) posm
                (rewrite_l nat m
                   (fun __ : nat => eq Prop (le (S __) m) (le (S m) O))
                   (rewrite_l nat m
                      (fun __ : nat => eq Prop (le (S m) m) (le (S m) __))
                      (refl Prop (le (S m) m)) O
                      (let_clause_1531 n m posm _clearme d eqm)) O
                   (let_clause_1531 n m posm _clearme d eqm)))
             (not_le_Sn_O m)))
       (fun (p : nat) (eqm : eq nat m (times n (S p))) =>
        eq_ind_r nat (times n (S p)) (fun x : nat => le n x)
          (eq_coerc (le n (plus n (times n p))) (le n (times n (S p)))
             (le_plus_n_r (times n p) n)
             (rewrite_l nat (plus n (times n p))
                (fun __ : nat =>
                 eq Prop (le n (plus n (times n p))) (le n __))
                (rewrite_l nat m
                   (fun __ : nat =>
                    eq Prop (le n (plus n (times n p))) (le n __))
                   (rewrite_l nat m
                      (fun __ : nat => eq Prop (le n __) (le n m))
                      (refl Prop (le n m)) (plus n (times n p))
                      (let_clause_15311 n m posm _clearme d p eqm))
                   (plus n (times n p))
                   (let_clause_15311 n m posm _clearme d p eqm))
                (times n (S p)) (times_n_Sm n p))) m eqm) d) _clearme.
Definition dividesb : nat -> nat -> bool := fun n m : nat => eqb (mod m n) O.
Definition dividesb_true_to_divides :
  forall n m : nat, eq bool (dividesb n m) true -> divides n m :=
  fun n m : nat =>
  match_Or_prop (lt O n) (eq nat O n)
    (eq bool (dividesb n m) true -> divides n m)
    (fun (posn : lt O n) (divbnm : eq bool (dividesb n m) true) =>
     mod_O_to_divides n m posn (eqb_true_to_eq (mod m n) O divbnm))
    (fun eqnO : eq nat O n =>
     eq_ind nat O
       (fun x_1 : nat => eq bool (dividesb x_1 m) true -> divides x_1 m)
       (sym_eq_match_nat_type_O nat m (fun p : nat => mod_aux m m p)
          (fun y : nat => eq bool (eqb y O) true -> divides O m)
          (fun eqbmO : eq bool (eqb m O) true =>
           eq_ind_r nat O (fun x : nat => divides O x) 
             (divides_n_n O) m (eqb_true_to_eq m O eqbmO))) n eqnO)
    (le_to_or_lt_eq O n (le_O_n n)).
Definition dividesb_false_to_not_divides :
  forall n m : nat, eq bool (dividesb n m) false -> Not (divides n m) :=
  fun n m : nat =>
  match_Or_prop (lt O n) (eq nat O n)
    (eq bool (dividesb n m) false -> Not (divides n m))
    (fun (posn : lt O n) (ndivbnm : eq bool (dividesb n m) false) =>
     not_to_not (divides n m) (eq nat (mod m n) O)
       (divides_to_mod_O n m posn) (eqb_false_to_not_eq (mod m n) O ndivbnm))
    (fun eqnO : eq nat O n =>
     eq_ind nat O
       (fun x_1 : nat =>
        eq bool (dividesb x_1 m) false -> Not (divides x_1 m))
       (sym_eq_match_nat_type_O nat m (fun p : nat => mod_aux m m p)
          (fun y : nat => eq bool (eqb y O) false -> Not (divides O m))
          (nat_case m
             (fun __ : nat => eq bool (eqb __ O) false -> Not (divides O __))
             (sym_eq_eqb O
                (fun y : nat -> bool =>
                 eq nat m O -> eq bool (y O) false -> Not (divides O O))
                (sym_eq_filter_nat_type_O (nat -> bool) eqb_body
                   (fun y : nat -> bool =>
                    eq nat m O -> eq bool (y O) false -> Not (divides O O))
                   (sym_eq_eqb_body_O
                      (fun y : nat -> bool =>
                       eq nat m O -> eq bool (y O) false -> Not (divides O O))
                      (sym_eq_match_nat_type_O bool true
                         (fun q : nat => false)
                         (fun y : bool =>
                          eq nat m O -> eq bool y false -> Not (divides O O))
                         (fun (auto : eq nat m O)
                            (auto' : eq bool true false) =>
                          not_to_not (divides O O) 
                            (eq bool true false)
                            (fun auto'' : divides O O =>
                             rewrite_l bool true
                               (fun __ : bool => eq bool true __)
                               (refl bool true) false auto')
                            not_eq_true_false)))))
             (fun (a : nat) (__ : eq nat m (S a))
                (_0 : eq bool (eqb (S a) O) false)
                (_clearme : divides O (S a)) =>
              match_divides_prop O (S a) False
                (fun (q : nat) (auto : eq nat (S a) (times O q)) =>
                 absurd (eq nat O (S a))
                   (rewrite_r nat n (fun __1 : nat => eq nat __1 (S a))
                      (rewrite_l nat (S a)
                         (fun __1 : nat => eq nat __1 (S a)) 
                         (refl nat (S a)) n
                         (rewrite_l nat O (fun __1 : nat => eq nat (S a) __1)
                            (rewrite_r nat (times q O)
                               (fun __1 : nat => eq nat (S a) __1)
                               (rewrite_l nat (times O q)
                                  (fun __1 : nat => eq nat (S a) __1) auto
                                  (times q O) (commutative_times O q)) O
                               (times_n_O q)) n eqnO)) O eqnO) 
                   (not_eq_O_S a)) _clearme))) n eqnO)
    (le_to_or_lt_eq O n (le_O_n n)).
Definition decidable_divides : forall n m : nat, decidable (divides n m) :=
  fun n m : nat =>
  match_Or_prop (eq bool (dividesb n m) true) (eq bool (dividesb n m) false)
    (decidable (divides n m))
    (fun (auto : eq bool (dividesb n m) true) (z : Prop)
       (l : divides n m -> z) (r : Not (divides n m) -> z) =>
     l
       (dividesb_true_to_divides n m
          (rewrite_r bool true (fun __ : bool => eq bool __ true)
             (refl bool true) (dividesb n m) auto)))
    (fun (auto : eq bool (dividesb n m) false) (z : Prop)
       (l : divides n m -> z) (r : Not (divides n m) -> z) =>
     r
       (dividesb_false_to_not_divides n m
          (rewrite_r bool false (fun __ : bool => eq bool __ false)
             (refl bool false) (dividesb n m) auto)))
    (true_or_false (dividesb n m)).
Definition divides_to_dividesb_true :
  forall n m : nat, lt O n -> divides n m -> eq bool (dividesb n m) true :=
  fun (n m : nat) (posn : lt O n) (divnm : divides n m) =>
  match_Or_prop (eq bool (dividesb n m) true) (eq bool (dividesb n m) false)
    (eq bool (dividesb n m) true)
    (fun auto : eq bool (dividesb n m) true =>
     rewrite_r bool true (fun __ : bool => eq bool __ true) 
       (refl bool true) (dividesb n m) auto)
    (fun ndivbnm : eq bool (dividesb n m) false =>
     falsity (eq bool (dividesb n m) true)
       (absurd (divides n m) divnm
          (dividesb_false_to_not_divides n m
             (rewrite_r bool false (fun __ : bool => eq bool __ false)
                (refl bool false) (dividesb n m) ndivbnm))))
    (true_or_false (dividesb n m)).
Definition not_divides_to_dividesb_false :
  forall n m : nat,
  lt O n -> Not (divides n m) -> eq bool (dividesb n m) false :=
  fun (n m : nat) (posn : lt O n) =>
  match_Or_prop (eq bool (dividesb n m) true) (eq bool (dividesb n m) false)
    (Not (divides n m) -> eq bool (dividesb n m) false)
    (fun (divbnm : eq bool (dividesb n m) true) (ndivnm : Not (divides n m))
     =>
     falsity (eq bool (dividesb n m) false)
       (absurd (divides n m)
          (dividesb_true_to_divides n m
             (rewrite_r bool true (fun __ : bool => eq bool __ true)
                (refl bool true) (dividesb n m) divbnm)) ndivnm))
    (fun (auto : eq bool (dividesb n m) false) (auto' : Not (divides n m)) =>
     rewrite_r bool false (fun __ : bool => eq bool __ false)
       (refl bool false) (dividesb n m) auto) (true_or_false (dividesb n m)).
Definition prime : nat -> Prop :=
  fun n : nat =>
  And (lt (S O) n) (forall m : nat, divides m n -> lt (S O) m -> eq nat m n).
Definition prime_to_lt_O : forall p : nat, prime p -> lt O p :=
  fun (p : nat) (_clearme : prime p) =>
  match_And_prop (lt (S O) p)
    (forall m : nat, divides m p -> lt (S O) m -> eq nat m p) 
    (lt O p)
    (fun (lt1p : lt (S O) p)
       (auto : forall m : nat, divides m p -> lt (S O) m -> eq nat m p) =>
     lt_S_to_lt O p lt1p) _clearme.
Definition prime_to_lt_SO : forall p : nat, prime p -> lt (S O) p :=
  fun (p : nat) (_clearme : prime p) =>
  match_And_prop (lt (S O) p)
    (forall m : nat, divides m p -> lt (S O) m -> eq nat m p) 
    (lt (S O) p)
    (fun (lt1p : lt (S O) p)
       (auto : forall m : nat, divides m p -> lt (S O) m -> eq nat m p) =>
     lt1p) _clearme.
Definition injn : (nat -> nat) -> nat -> Prop :=
  fun (f : nat -> nat) (n : nat) =>
  forall i j : nat, le i n -> le j n -> eq nat (f i) (f j) -> eq nat i j.
Definition injn_Sn_n :
  forall (f : nat -> nat) (n : nat), injn f (S n) -> injn f n :=
  fun (f : nat -> nat) (n : nat) (H : injn f (S n)) 
    (i j : nat) (lei : le i n) (lej : le j n) (eqf : eq nat (f i) (f j)) =>
  H i j (le_S i n lei) (le_S j n lej)
    (rewrite_l nat (f i) (fun __ : nat => eq nat (f i) __) 
       (refl nat (f i)) (f j) eqf).
Definition permut : (nat -> nat) -> nat -> Prop :=
  fun (f : nat -> nat) (m : nat) =>
  And (forall i : nat, le i m -> le (f i) m) (injn f m).
Definition transpose : nat -> nat -> nat -> nat :=
  fun i j n : nat =>
  match_bool_type nat j (match_bool_type nat i n (eqb n j)) (eqb n i).
Definition transpose_i_j_i : forall i j : nat, eq nat (transpose i j i) j :=
  fun i j : nat =>
  eq_ind_r bool true
    (fun x : bool =>
     eq nat (match_bool_type nat j (match_bool_type nat i i (eqb i j)) x) j)
    (eq_match_bool_type_true nat j (match_bool_type nat i i (eqb i j))
       (fun y : nat =>
        eq nat
          (match_bool_type nat j (match_bool_type nat i i (eqb i j)) true) y)
       (refl nat
          (match_bool_type nat j (match_bool_type nat i i (eqb i j)) true)))
    (eqb i i) (eqb_n_n i).
Definition transpose_i_j_j : forall i j : nat, eq nat (transpose i j j) i :=
  fun i j : nat =>
  match_Or_prop (eq bool (eqb j i) true) (eq bool (eqb j i) false)
    (eq nat
       (match_bool_type nat j (match_bool_type nat i j (eqb j j)) (eqb j i))
       i)
    (fun Hc : eq bool (eqb j i) true =>
     eq_ind_r bool true
       (fun x : bool =>
        eq nat (match_bool_type nat j (match_bool_type nat i j (eqb j j)) x)
          i)
       (sym_eq_match_bool_type_true nat j (match_bool_type nat i j (eqb j j))
          (fun y : nat => eq nat y i)
          (eq_ind_r nat i (fun x : nat => eq nat x i) 
             (refl nat i) j (eqb_true_to_eq j i Hc))) 
       (eqb j i) Hc)
    (fun Hc : eq bool (eqb j i) false =>
     eq_ind_r bool false
       (fun x : bool =>
        eq nat (match_bool_type nat j (match_bool_type nat i j (eqb j j)) x)
          i)
       (eq_ind_r bool true
          (fun x : bool =>
           eq nat (match_bool_type nat j (match_bool_type nat i j x) false) i)
          (sym_eq_match_bool_type_false nat j (match_bool_type nat i j true)
             (fun y : nat => eq nat y i)
             (eq_match_bool_type_true nat i j
                (fun y : nat => eq nat (match_bool_type nat i j true) y)
                (eq_match_bool_type_false nat j
                   (match_bool_type nat i j true)
                   (fun y : nat => eq nat (match_bool_type nat i j true) y)
                   (eq_match_bool_type_false nat j
                      (match_bool_type nat i j true)
                      (fun y : nat =>
                       eq nat y
                         (match_bool_type nat j
                            (match_bool_type nat i j true) false))
                      (refl nat
                         (match_bool_type nat j
                            (match_bool_type nat i j true) false))))))
          (eqb j j) (eqb_n_n j)) (eqb j i) Hc) (true_or_false (eqb j i)).
Definition transpose_i_j_j_i :
  forall i j n : nat, eq nat (transpose i j n) (transpose j i n) :=
  fun i j n : nat =>
  match_Or_prop (eq bool (eqb n i) true) (eq bool (eqb n i) false)
    (eq nat
       (match_bool_type nat j (match_bool_type nat i n (eqb n j)) (eqb n i))
       (match_bool_type nat i (match_bool_type nat j n (eqb n i)) (eqb n j)))
    (fun Hni : eq bool (eqb n i) true =>
     eq_ind_r bool true
       (fun x : bool =>
        eq nat (match_bool_type nat j (match_bool_type nat i n (eqb n j)) x)
          (match_bool_type nat i (match_bool_type nat j n x) (eqb n j)))
       (match_Or_prop (eq bool (eqb n j) true) (eq bool (eqb n j) false)
          (eq nat
             (match_bool_type nat j (match_bool_type nat i n (eqb n j)) true)
             (match_bool_type nat i (match_bool_type nat j n true) (eqb n j)))
          (fun Hnj : eq bool (eqb n j) true =>
           eq_ind_r bool true
             (fun x : bool =>
              eq nat (match_bool_type nat j (match_bool_type nat i n x) true)
                (match_bool_type nat i (match_bool_type nat j n true) x))
             (sym_eq_match_bool_type_true nat j
                (match_bool_type nat i n true)
                (fun y : nat =>
                 eq nat y
                   (match_bool_type nat i (match_bool_type nat j n true) true))
                (sym_eq_match_bool_type_true nat i
                   (match_bool_type nat j n true) 
                   (fun y : nat => eq nat j y)
                   (eq_ind nat n (fun x_1 : nat => eq nat j x_1)
                      (eq_ind nat n (fun x_1 : nat => eq nat x_1 n)
                         (refl nat n) j (eqb_true_to_eq n j Hnj)) i
                      (eqb_true_to_eq n i Hni)))) 
             (eqb n j) Hnj)
          (fun Hnj : eq bool (eqb n j) false =>
           eq_ind_r bool false
             (fun x : bool =>
              eq nat (match_bool_type nat j (match_bool_type nat i n x) true)
                (match_bool_type nat i (match_bool_type nat j n true) x))
             (sym_eq_match_bool_type_false nat i n
                (fun y : nat =>
                 eq nat (match_bool_type nat j y true)
                   (match_bool_type nat i (match_bool_type nat j n true)
                      false))
                (sym_eq_match_bool_type_false nat i
                   (match_bool_type nat j n true)
                   (fun y : nat => eq nat (match_bool_type nat j n true) y)
                   (sym_eq_match_bool_type_true nat j n
                      (fun y : nat => eq nat (match_bool_type nat j n true) y)
                      (sym_eq_match_bool_type_true nat j n
                         (fun y : nat => eq nat y j) 
                         (refl nat j))))) (eqb n j) Hnj)
          (true_or_false (eqb n j))) (eqb n i) Hni)
    (fun Hni : eq bool (eqb n i) false =>
     eq_ind_r bool false
       (fun x : bool =>
        eq nat (match_bool_type nat j (match_bool_type nat i n (eqb n j)) x)
          (match_bool_type nat i (match_bool_type nat j n x) (eqb n j)))
       (match_Or_prop (eq bool (eqb n j) true) (eq bool (eqb n j) false)
          (eq nat
             (match_bool_type nat j (match_bool_type nat i n (eqb n j)) false)
             (match_bool_type nat i (match_bool_type nat j n false) (eqb n j)))
          (fun Hnj : eq bool (eqb n j) true =>
           eq_ind_r bool true
             (fun x : bool =>
              eq nat
                (match_bool_type nat j (match_bool_type nat i n x) false)
                (match_bool_type nat i (match_bool_type nat j n false) x))
             (sym_eq_match_bool_type_false nat j
                (match_bool_type nat i n true)
                (fun y : nat =>
                 eq nat y
                   (match_bool_type nat i (match_bool_type nat j n false)
                      true))
                (sym_eq_match_bool_type_false nat j n
                   (fun y : nat =>
                    eq nat (match_bool_type nat i n true)
                      (match_bool_type nat i y true))
                   (sym_eq_match_bool_type_true nat i n
                      (fun y : nat => eq nat (match_bool_type nat i n true) y)
                      (sym_eq_match_bool_type_true nat i n
                         (fun y : nat => eq nat y i) 
                         (refl nat i))))) (eqb n j) Hnj)
          (fun Hnj : eq bool (eqb n j) false =>
           eq_ind_r bool false
             (fun x : bool =>
              eq nat
                (match_bool_type nat j (match_bool_type nat i n x) false)
                (match_bool_type nat i (match_bool_type nat j n false) x))
             (sym_eq_match_bool_type_false nat i n
                (fun y : nat =>
                 eq nat (match_bool_type nat j y false)
                   (match_bool_type nat i (match_bool_type nat j n false)
                      false))
                (sym_eq_match_bool_type_false nat j n
                   (fun y : nat =>
                    eq nat (match_bool_type nat j n false)
                      (match_bool_type nat i y false))
                   (sym_eq_match_bool_type_false nat j n
                      (fun y : nat =>
                       eq nat y (match_bool_type nat i n false))
                      (sym_eq_match_bool_type_false nat i n
                         (fun y : nat => eq nat n y) 
                         (refl nat n))))) (eqb n j) Hnj)
          (true_or_false (eqb n j))) (eqb n i) Hni) 
    (true_or_false (eqb n i)).
Definition transpose_transpose :
  forall i j n : nat, eq nat (transpose i j (transpose i j n)) n :=
  fun i j n : nat =>
  match_Or_prop (eq bool (eqb n i) true) (eq bool (eqb n i) false)
    (eq nat
       (match_bool_type nat j
          (match_bool_type nat i
             (match_bool_type nat j (match_bool_type nat i n (eqb n j))
                (eqb n i))
             (eqb
                (match_bool_type nat j (match_bool_type nat i n (eqb n j))
                   (eqb n i)) j))
          (eqb
             (match_bool_type nat j (match_bool_type nat i n (eqb n j))
                (eqb n i)) i)) n)
    (fun Hni : eq bool (eqb n i) true =>
     eq_ind_r bool true
       (fun x : bool =>
        eq nat
          (match_bool_type nat j
             (match_bool_type nat i
                (match_bool_type nat j (match_bool_type nat i n (eqb n j)) x)
                (eqb
                   (match_bool_type nat j (match_bool_type nat i n (eqb n j))
                      x) j))
             (eqb
                (match_bool_type nat j (match_bool_type nat i n (eqb n j)) x)
                i)) n)
       (sym_eq_match_bool_type_true nat j (match_bool_type nat i n (eqb n j))
          (fun y : nat =>
           eq nat
             (match_bool_type nat j
                (match_bool_type nat i
                   (match_bool_type nat j (match_bool_type nat i n (eqb n j))
                      true)
                   (eqb
                      (match_bool_type nat j
                         (match_bool_type nat i n (eqb n j)) true) j))
                (eqb y i)) n)
          (sym_eq_match_bool_type_true nat j
             (match_bool_type nat i n (eqb n j))
             (fun y : nat =>
              eq nat
                (match_bool_type nat j
                   (match_bool_type nat i
                      (match_bool_type nat j
                         (match_bool_type nat i n (eqb n j)) true) 
                      (eqb y j)) (eqb j i)) n)
             (sym_eq_match_bool_type_true nat j
                (match_bool_type nat i n (eqb n j))
                (fun y : nat =>
                 eq nat
                   (match_bool_type nat j (match_bool_type nat i y (eqb j j))
                      (eqb j i)) n)
                (match_Or_prop (eq bool (eqb j i) true)
                   (eq bool (eqb j i) false)
                   (eq nat
                      (match_bool_type nat j
                         (match_bool_type nat i j (eqb j j)) 
                         (eqb j i)) n)
                   (fun Hji : eq bool (eqb j i) true =>
                    eq_ind_r bool true
                      (fun x : bool =>
                       eq nat
                         (match_bool_type nat j
                            (match_bool_type nat i j (eqb j j)) x) n)
                      (sym_eq_match_bool_type_true nat j
                         (match_bool_type nat i j (eqb j j))
                         (fun y : nat => eq nat y n)
                         (eq_ind_r nat i (fun x : nat => eq nat j x)
                            (eqb_true_to_eq j i Hji) n
                            (eqb_true_to_eq n i Hni))) 
                      (eqb j i) Hji)
                   (fun Hji : eq bool (eqb j i) false =>
                    eq_ind_r bool false
                      (fun x : bool =>
                       eq nat
                         (match_bool_type nat j
                            (match_bool_type nat i j (eqb j j)) x) n)
                      (sym_eq_match_bool_type_false nat j
                         (match_bool_type nat i j (eqb j j))
                         (fun y : nat => eq nat y n)
                         (eq_ind_r bool true
                            (fun x : bool =>
                             eq nat (match_bool_type nat i j x) n)
                            (sym_eq_match_bool_type_true nat i j
                               (fun y : nat => eq nat y n)
                               (sym_eq nat n i (eqb_true_to_eq n i Hni)))
                            (eqb j j) (eqb_n_n j))) 
                      (eqb j i) Hji) (true_or_false (eqb j i)))))) 
       (eqb n i) Hni)
    (fun Hni : eq bool (eqb n i) false =>
     eq_ind_r bool false
       (fun x : bool =>
        eq nat
          (match_bool_type nat j
             (match_bool_type nat i
                (match_bool_type nat j (match_bool_type nat i n (eqb n j)) x)
                (eqb
                   (match_bool_type nat j (match_bool_type nat i n (eqb n j))
                      x) j))
             (eqb
                (match_bool_type nat j (match_bool_type nat i n (eqb n j)) x)
                i)) n)
       (sym_eq_match_bool_type_false nat j
          (match_bool_type nat i n (eqb n j))
          (fun y : nat =>
           eq nat
             (match_bool_type nat j
                (match_bool_type nat i
                   (match_bool_type nat j (match_bool_type nat i n (eqb n j))
                      false)
                   (eqb
                      (match_bool_type nat j
                         (match_bool_type nat i n (eqb n j)) false) j))
                (eqb y i)) n)
          (sym_eq_match_bool_type_false nat j
             (match_bool_type nat i n (eqb n j))
             (fun y : nat =>
              eq nat
                (match_bool_type nat j
                   (match_bool_type nat i
                      (match_bool_type nat j
                         (match_bool_type nat i n (eqb n j)) false) 
                      (eqb y j)) (eqb (match_bool_type nat i n (eqb n j)) i))
                n)
             (sym_eq_match_bool_type_false nat j
                (match_bool_type nat i n (eqb n j))
                (fun y : nat =>
                 eq nat
                   (match_bool_type nat j
                      (match_bool_type nat i y
                         (eqb (match_bool_type nat i n (eqb n j)) j))
                      (eqb (match_bool_type nat i n (eqb n j)) i)) n)
                (match_Or_prop (eq bool (eqb n j) true)
                   (eq bool (eqb n j) false)
                   (eq nat
                      (match_bool_type nat j
                         (match_bool_type nat i
                            (match_bool_type nat i n (eqb n j))
                            (eqb (match_bool_type nat i n (eqb n j)) j))
                         (eqb (match_bool_type nat i n (eqb n j)) i)) n)
                   (fun Hnj : eq bool (eqb n j) true =>
                    eq_ind_r bool true
                      (fun x : bool =>
                       eq nat
                         (match_bool_type nat j
                            (match_bool_type nat i
                               (match_bool_type nat i n x)
                               (eqb (match_bool_type nat i n x) j))
                            (eqb (match_bool_type nat i n x) i)) n)
                      (sym_eq_match_bool_type_true nat i n
                         (fun y : nat =>
                          eq nat
                            (match_bool_type nat j
                               (match_bool_type nat i
                                  (match_bool_type nat i n true)
                                  (eqb (match_bool_type nat i n true) j))
                               (eqb y i)) n)
                         (sym_eq_match_bool_type_true nat i n
                            (fun y : nat =>
                             eq nat
                               (match_bool_type nat j
                                  (match_bool_type nat i
                                     (match_bool_type nat i n true) 
                                     (eqb y j)) (eqb i i)) n)
                            (sym_eq_match_bool_type_true nat i n
                               (fun y : nat =>
                                eq nat
                                  (match_bool_type nat j
                                     (match_bool_type nat i y (eqb i j))
                                     (eqb i i)) n)
                               (eq_ind_r bool true
                                  (fun x : bool =>
                                   eq nat
                                     (match_bool_type nat j
                                        (match_bool_type nat i i (eqb i j)) x)
                                     n)
                                  (sym_eq_match_bool_type_true nat j
                                     (match_bool_type nat i i (eqb i j))
                                     (fun y : nat => eq nat y n)
                                     (sym_eq nat n j (eqb_true_to_eq n j Hnj)))
                                  (eqb i i) (eqb_n_n i))))) 
                      (eqb n j) Hnj)
                   (fun Hnj : eq bool (eqb n j) false =>
                    eq_ind_r bool false
                      (fun x : bool =>
                       eq nat
                         (match_bool_type nat j
                            (match_bool_type nat i
                               (match_bool_type nat i n x)
                               (eqb (match_bool_type nat i n x) j))
                            (eqb (match_bool_type nat i n x) i)) n)
                      (sym_eq_match_bool_type_false nat i n
                         (fun y : nat =>
                          eq nat
                            (match_bool_type nat j
                               (match_bool_type nat i
                                  (match_bool_type nat i n false)
                                  (eqb (match_bool_type nat i n false) j))
                               (eqb y i)) n)
                         (sym_eq_match_bool_type_false nat i n
                            (fun y : nat =>
                             eq nat
                               (match_bool_type nat j
                                  (match_bool_type nat i
                                     (match_bool_type nat i n false)
                                     (eqb y j)) (eqb n i)) n)
                            (sym_eq_match_bool_type_false nat i n
                               (fun y : nat =>
                                eq nat
                                  (match_bool_type nat j
                                     (match_bool_type nat i y (eqb n j))
                                     (eqb n i)) n)
                               (eq_ind_r bool false
                                  (fun x : bool =>
                                   eq nat
                                     (match_bool_type nat j
                                        (match_bool_type nat i n (eqb n j)) x)
                                     n)
                                  (eq_ind_r bool false
                                     (fun x : bool =>
                                      eq nat
                                        (match_bool_type nat j
                                           (match_bool_type nat i n x) false)
                                        n)
                                     (eq_match_bool_type_false nat i n
                                        (fun y : nat =>
                                         eq nat
                                           (match_bool_type nat j
                                              (match_bool_type nat i n false)
                                              false) y)
                                        (eq_match_bool_type_false nat j
                                           (match_bool_type nat i n false)
                                           (fun y : nat =>
                                            eq nat
                                              (match_bool_type nat j
                                                 (match_bool_type nat i n
                                                 false) false) y)
                                           (refl nat
                                              (match_bool_type nat j
                                                 (match_bool_type nat i n
                                                 false) false)))) 
                                     (eqb n j) Hnj) 
                                  (eqb n i) Hni)))) 
                      (eqb n j) Hnj) (true_or_false (eqb n j)))))) 
       (eqb n i) Hni) (true_or_false (eqb n i)).
Definition injective_transpose :
  forall i j : nat, injective nat nat (transpose i j) :=
  fun (i j x y : nat) (auto : eq nat (transpose i j x) (transpose i j y)) =>
  rewrite_r nat y (fun __ : nat => eq nat __ y) (refl nat y) x
    (rewrite_l nat (transpose i j (transpose i j x))
       (fun __ : nat => eq nat __ y)
       (rewrite_r nat (transpose i j y)
          (fun __ : nat => eq nat (transpose i j __) y)
          (transpose_transpose i j y) (transpose i j x) auto) x
       (transpose_transpose i j x)).
Definition permut_S_to_permut_transpose :
  forall (f : nat -> nat) (m : nat),
  permut f (S m) -> permut (fun n : nat => transpose (f (S m)) (S m) (f n)) m :=
  fun (f : nat -> nat) (m : nat) (_clearme : permut f (S m)) =>
  match_And_prop (forall i : nat, le i (S m) -> le (f i) (S m))
    (injn f (S m))
    (permut (fun n : nat => transpose (f (S m)) (S m) (f n)) m)
    (fun (permf1 : forall i : nat, le i (S m) -> le (f i) (S m))
       (permf2 : injn f (S m)) (z : Prop)
       (f2 : (forall x : nat,
              le x m -> le (transpose (f (S m)) (S m) (f x)) m) ->
             injn (fun n : nat => transpose (f (S m)) (S m) (f n)) m -> z) =>
     f2
       (fun (i : nat) (leim : le i m) =>
        eq_ind_r bool false
          (fun x : bool =>
           le
             (match_bool_type nat (S m)
                (match_bool_type nat (f (S m)) (f i) (eqb (f i) (S m))) x) m)
          (sym_eq_match_bool_type_false nat (S m)
             (match_bool_type nat (f (S m)) (f i) (eqb (f i) (S m)))
             (fun y : nat => le y m)
             (match_Or_prop (lt (f i) (S m)) (eq nat (f i) (S m))
                (le (match_bool_type nat (f (S m)) (f i) (eqb (f i) (S m))) m)
                (fun Hfi : lt (f i) (S m) =>
                 eq_ind_r bool false
                   (fun x : bool =>
                    le (match_bool_type nat (f (S m)) (f i) x) m)
                   (sym_eq_match_bool_type_false nat 
                      (f (S m)) (f i) (fun y : nat => le y m)
                      (le_S_S_to_le (f i) m Hfi)) 
                   (eqb (f i) (S m))
                   (not_eq_to_eqb_false (f i) (S m)
                      (lt_to_not_eq (f i) (S m) Hfi)))
                (fun Hfi : eq nat (f i) (S m) =>
                 eq_ind_r bool true
                   (fun x : bool =>
                    le (match_bool_type nat (f (S m)) (f i) x) m)
                   (sym_eq_match_bool_type_true nat 
                      (f (S m)) (f i) (fun y : nat => le y m)
                      (match_Or_prop (lt (f (S m)) (S m))
                         (eq nat (f (S m)) (S m)) 
                         (le (f (S m)) m)
                         (fun H : lt (f (S m)) (S m) =>
                          le_S_S_to_le (f (S m)) m H)
                         (fun H : eq nat (f (S m)) (S m) =>
                          falsity (le (f (S m)) m)
                            (absurd (eq nat i (S m))
                               (permf2 i (S m) (le_S i m leim) 
                                  (le_n (S m))
                                  (rewrite_l nat (f i)
                                     (fun __ : nat => eq nat (f i) (f __))
                                     (rewrite_r nat 
                                        (f i)
                                        (fun __ : nat => eq nat (f i) __)
                                        (refl nat (f i)) 
                                        (f (f i))
                                        (rewrite_r nat 
                                           (S m)
                                           (fun __ : nat =>
                                            eq nat (f (f i)) __)
                                           (rewrite_r nat 
                                              (S m)
                                              (fun __ : nat =>
                                               eq nat (f __) (S m)) H 
                                              (f i) Hfi) 
                                           (f i) Hfi)) 
                                     (S m) Hfi))
                               (not_to_not (eq nat i (S m)) 
                                  (le (S m) m)
                                  (fun auto : eq nat i (S m) =>
                                   eq_coerc (le i m) 
                                     (le (S m) m) leim
                                     (rewrite_l nat i
                                        (fun __ : nat =>
                                         eq Prop (le i m) (le __ m))
                                        (refl Prop (le i m)) 
                                        (S m) auto))
                                  (lt_to_not_le m (S m) (le_n (S m))))))
                         (le_to_or_lt_eq (f (S m)) 
                            (S m) (permf1 (S m) (le_n (S m))))))
                   (eqb (f i) (S m)) (eq_to_eqb_true (f i) (S m) Hfi))
                (le_to_or_lt_eq (f i) (S m) (permf1 i (le_S i m leim)))))
          (eqb (f i) (f (S m)))
          (not_eq_to_eqb_false (f i) (f (S m))
             (fun H : eq nat (f i) (f (S m)) =>
              absurd (eq nat i (S m))
                (permf2 i (S m) (le_S i m leim) (le_n (S m)) H)
                (lt_to_not_eq i (S m) (le_S_S i m leim)))))
       (fun (a b : nat) (leam : le a m) (lebm : le b m)
          (H : eq nat (transpose (f (S m)) (S m) (f a))
                 (transpose (f (S m)) (S m) (f b))) =>
        permf2 a b (le_S a m leam) (le_S b m lebm)
          (injective_transpose (f (S m)) (S m) (f a) (f b) H))) _clearme.
Definition bijn : (nat -> nat) -> nat -> Prop :=
  fun (f : nat -> nat) (n : nat) =>
  forall m : nat,
  le m n -> Ex nat (fun p : nat => And (le p n) (eq nat (f p) m)).
Definition eq_to_bijn :
  forall (f g : nat -> nat) (n : nat),
  (forall i : nat, le i n -> eq nat (f i) (g i)) -> bijn f n -> bijn g n :=
  fun (f g : nat -> nat) (n : nat)
    (H : forall i : nat, le i n -> eq nat (f i) (g i)) 
    (bijf : bijn f n) (i : nat) (lein : le i n) =>
  match_ex_prop nat (fun p : nat => And (le p n) (eq nat (f p) i))
    (Ex nat (fun p : nat => And (le p n) (eq nat (g p) i)))
    (fun (a : nat) (_clearme : And (le a n) (eq nat (f a) i)) =>
     match_And_prop (le a n) (eq nat (f a) i)
       (Ex nat (fun p : nat => And (le p n) (eq nat (g p) i)))
       (fun (lean : le a n) (fa : eq nat (f a) i) 
          (z : Prop)
          (f2 : forall x : nat, And (le x n) (eq nat (g x) i) -> z) =>
        f2 a
          (fun (z0 : Prop) (f3 : le a n -> eq nat (g a) i -> z0) =>
           f3 lean
             (eq_ind nat (f a) (fun x_1 : nat => eq nat (g a) x_1)
                (sym_eq nat (f a) (g a) (H a lean)) i fa))) _clearme)
    (bijf i lein).
Definition bijn_n_Sn :
  forall (f : nat -> nat) (n : nat),
  bijn f n -> eq nat (f (S n)) (S n) -> bijn f (S n) :=
  fun (f : nat -> nat) (n : nat) (bijf : bijn f n)
    (fS : eq nat (f (S n)) (S n)) (i : nat) (lein : le i (S n)) =>
  match_Or_prop (lt i (S n)) (eq nat i (S n))
    (Ex nat (fun p : nat => And (le p (S n)) (eq nat (f p) i)))
    (fun Hi : lt i (S n) =>
     match_ex_prop nat (fun p : nat => And (le p n) (eq nat (f p) i))
       (Ex nat (fun p : nat => And (le p (S n)) (eq nat (f p) i)))
       (fun (a : nat) (_clearme : And (le a n) (eq nat (f a) i)) =>
        match_And_prop (le a n) (eq nat (f a) i)
          (Ex nat (fun p : nat => And (le p (S n)) (eq nat (f p) i)))
          (fun (lean : le a n) (fa : eq nat (f a) i) 
             (z : Prop)
             (f4 : forall x : nat, And (le x (S n)) (eq nat (f x) i) -> z) =>
           f4 a
             (fun (z0 : Prop) (f5 : le a (S n) -> eq nat (f a) i -> z0) =>
              f5 (le_S a n lean)
                (rewrite_r nat i (fun __ : nat => eq nat __ i) 
                   (refl nat i) (f a) fa))) _clearme)
       (bijf i (le_S_S_to_le i n Hi)))
    (fun (Hi : eq nat i (S n)) (z : Prop)
       (f6 : forall x : nat, And (le x (S n)) (eq nat (f x) i) -> z) =>
     f6 i
       (fun (z0 : Prop) (f7 : le i (S n) -> eq nat (f i) i -> z0) =>
        f7
          (eq_coerc (le i i) (le i (S n)) (le_n i)
             (rewrite_l nat i (fun __ : nat => eq Prop (le i i) (le i __))
                (refl Prop (le i i)) (S n) Hi))
          (rewrite_r nat i (fun __ : nat => eq nat __ i) 
             (refl nat i) (f i)
             (rewrite_r nat (S n) (fun __ : nat => eq nat (f i) __)
                (rewrite_r nat (S n) (fun __ : nat => eq nat (f __) (S n)) fS
                   i Hi) i Hi)))) (le_to_or_lt_eq i (S n) lein).
Definition bijn_fg :
  forall (f g : nat -> nat) (n : nat),
  bijn f n -> bijn g n -> bijn (fun p : nat => f (g p)) n :=
  fun (f g : nat -> nat) (n : nat) (bijf : bijn f n) 
    (bijg : bijn g n) (i : nat) (lein : le i n) =>
  match_ex_prop nat (fun p : nat => And (le p n) (eq nat (f p) i))
    (Ex nat (fun p : nat => And (le p n) (eq nat (f (g p)) i)))
    (fun (a : nat) (_clearme : And (le a n) (eq nat (f a) i)) =>
     match_And_prop (le a n) (eq nat (f a) i)
       (Ex nat (fun p : nat => And (le p n) (eq nat (f (g p)) i)))
       (fun (lean : le a n) (ga : eq nat (f a) i) =>
        match_ex_prop nat (fun p : nat => And (le p n) (eq nat (g p) a))
          (Ex nat (fun p : nat => And (le p n) (eq nat (f (g p)) i)))
          (fun (b : nat) (_clearme0 : And (le b n) (eq nat (g b) a)) =>
           match_And_prop (le b n) (eq nat (g b) a)
             (Ex nat (fun p : nat => And (le p n) (eq nat (f (g p)) i)))
             (fun (lebn : le b n) (gb : eq nat (g b) a) 
                (z : Prop)
                (f2 : forall x : nat, And (le x n) (eq nat (f (g x)) i) -> z)
              =>
              f2 b
                (fun (z0 : Prop) (f3 : le b n -> eq nat (f (g b)) i -> z0) =>
                 f3 lebn
                   (rewrite_r nat a (fun __ : nat => eq nat (f __) i)
                      (rewrite_r nat i (fun __ : nat => eq nat __ i)
                         (refl nat i) (f a) ga) (g b) gb))) _clearme0)
          (bijg a lean)) _clearme) (bijf i lein).
Definition bijn_transpose :
  forall n i j : nat, le i n -> le j n -> bijn (transpose i j) n :=
  fun (n i j : nat) (lein : le i n) (lejn : le j n) (a : nat) (lean : le a n)
  =>
  match_Or_prop (eq bool (eqb a i) true) (eq bool (eqb a i) false)
    (Ex nat (fun p : nat => And (le p n) (eq nat (transpose i j p) a)))
    (fun (Hi : eq bool (eqb a i) true) (z : Prop)
       (f3 : forall x : nat, And (le x n) (eq nat (transpose i j x) a) -> z)
     =>
     f3 j
       (fun (z0 : Prop) (f4 : le j n -> eq nat (transpose i j j) a -> z0) =>
        f4 lejn
          (eq_ind_r nat i (fun x : nat => eq nat x a)
             (sym_eq nat a i (eqb_true_to_eq a i Hi)) 
             (transpose i j j) (transpose_i_j_j i j))))
    (fun Hi : eq bool (eqb a i) false =>
     match_Or_prop (eq bool (eqb a j) true) (eq bool (eqb a j) false)
       (Ex nat (fun p : nat => And (le p n) (eq nat (transpose i j p) a)))
       (fun (Hj : eq bool (eqb a j) true) (z : Prop)
          (f5 : forall x : nat,
                And (le x n) (eq nat (transpose i j x) a) -> z) =>
        f5 i
          (fun (z0 : Prop) (f : le i n -> eq nat (transpose i j i) a -> z0)
           =>
           f lein
             (eq_ind_r nat j (fun x : nat => eq nat x a)
                (sym_eq nat a j (eqb_true_to_eq a j Hj)) 
                (transpose i j i) (transpose_i_j_i i j))))
       (fun (Hj : eq bool (eqb a j) false) (z : Prop)
          (f7 : forall x : nat,
                And (le x n) (eq nat (transpose i j x) a) -> z) =>
        f7 a
          (fun (z0 : Prop) (f : le a n -> eq nat (transpose i j a) a -> z0)
           =>
           f lean
             (eq_ind_r bool false
                (fun x : bool =>
                 eq nat
                   (match_bool_type nat j (match_bool_type nat i a (eqb a j))
                      x) a)
                (eq_ind_r bool false
                   (fun x : bool =>
                    eq nat
                      (match_bool_type nat j (match_bool_type nat i a x)
                         false) a)
                   (eq_match_bool_type_false nat i a
                      (fun y : nat =>
                       eq nat
                         (match_bool_type nat j
                            (match_bool_type nat i a false) false) y)
                      (eq_match_bool_type_false nat j
                         (match_bool_type nat i a false)
                         (fun y : nat =>
                          eq nat
                            (match_bool_type nat j
                               (match_bool_type nat i a false) false) y)
                         (refl nat
                            (match_bool_type nat j
                               (match_bool_type nat i a false) false))))
                   (eqb a j) Hj) (eqb a i) Hi))) (true_or_false (eqb a j)))
    (true_or_false (eqb a i)).
Definition permut_to_bijn :
  forall (n : nat) (f : nat -> nat), permut f n -> bijn f n :=
  fun n : nat =>
  nat_ind
    (fun _x_365 : nat =>
     forall f : nat -> nat, permut f _x_365 -> bijn f _x_365)
    (fun (f : nat -> nat)
       (_clearme : And (forall i : nat, le i O -> le (f i) O)
                     (forall i j : nat,
                      le i O -> le j O -> eq nat (f i) (f j) -> eq nat i j))
     =>
     match_And_prop (forall i : nat, le i O -> le (f i) O)
       (forall i j : nat,
        le i O -> le j O -> eq nat (f i) (f j) -> eq nat i j)
       (forall m : nat,
        le m O -> Ex nat (fun p : nat => And (le p O) (eq nat (f p) m)))
       (fun (H : forall i : nat, le i O -> le (f i) O)
          (H1 : forall i j : nat,
                le i O -> le j O -> eq nat (f i) (f j) -> eq nat i j)
          (m : nat) (lem0 : le m O) (z : Prop)
          (f8 : forall x : nat, And (le x O) (eq nat (f x) m) -> z) =>
        f8 O
          (fun (z0 : Prop) (f80 : le O O -> eq nat (f O) m -> z0) =>
           f80 (le_O_n O)
             (le_n_O_elim m lem0 (eq nat (f O))
                (sym_eq nat O (f O) (le_n_O_to_eq (f O) (H O (le_O_n O)))))))
       _clearme)
    (fun (m : nat) (Hind : forall f : nat -> nat, permut f m -> bijn f m)
       (f : nat -> nat) (permf : permut f (S m)) =>
     eq_to_bijn
       (fun p : nat =>
        transpose (f (S m)) (S m) (transpose (f (S m)) (S m) (f p))) f 
       (S m)
       (fun (i : nat) (lei : le i (S m)) =>
        transpose_transpose (f (S m)) (S m) (f i))
       (bijn_fg (transpose (f (S m)) (S m))
          (fun __ : nat => transpose (f (S m)) (S m) (f __)) 
          (S m)
          (match_And_prop (forall i : nat, le i (S m) -> le (f i) (S m))
             (injn f (S m)) (bijn (transpose (f (S m)) (S m)) (S m))
             (fun (lef : forall i : nat, le i (S m) -> le (f i) (S m))
                (__ : injn f (S m)) =>
              bijn_transpose (S m) (f (S m)) (S m) 
                (lef (S m) (le_n (S m))) (le_n (S m))) permf)
          (bijn_n_Sn (fun __ : nat => transpose (f (S m)) (S m) (f __)) m
             (Hind (fun __ : nat => transpose (f (S m)) (S m) (f __))
                (permut_S_to_permut_transpose f m permf))
             (eq_ind_r bool true
                (fun x : bool =>
                 eq nat
                   (match_bool_type nat (S m)
                      (match_bool_type nat (f (S m)) 
                         (f (S m)) (eqb (f (S m)) (S m))) x) 
                   (S m))
                (eq_match_bool_type_true nat (S m)
                   (match_bool_type nat (f (S m)) 
                      (f (S m)) (eqb (f (S m)) (S m)))
                   (fun y : nat =>
                    eq nat
                      (match_bool_type nat (S m)
                         (match_bool_type nat (f (S m)) 
                            (f (S m)) (eqb (f (S m)) (S m))) true) y)
                   (refl nat
                      (match_bool_type nat (S m)
                         (match_bool_type nat (f (S m)) 
                            (f (S m)) (eqb (f (S m)) (S m))) true)))
                (eqb (f (S m)) (f (S m))) (eqb_n_n (f (S m))))))) n.

Fixpoint invert_permut (n : nat) (f : nat -> nat) 
(m : nat) : nat :=
  match n with
  | 0 => if eqb m (f 0) then 0 else 0
  | Datatypes.S n => if eqb m (f (S n)) then S n else invert_permut n f m
  end.

Definition invert_permut_body : nat -> (nat -> nat) -> nat -> nat :=
  invert_permut.
Theorem eq_invert_permut :
  forall n : nat,
  leibniz ((nat -> nat) -> nat -> nat) (invert_permut n)
    (filter_nat_type ((nat -> nat) -> nat -> nat) invert_permut_body n).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.

Definition sym_eq_invert_permut :
  forall n : nat,
  leibniz ((nat -> nat) -> nat -> nat)
    (filter_nat_type ((nat -> nat) -> nat -> nat) invert_permut_body n)
    (invert_permut n) :=
  fun n : nat =>
  sym_leibniz ((nat -> nat) -> nat -> nat) (invert_permut n)
    (filter_nat_type ((nat -> nat) -> nat -> nat) invert_permut_body n)
    (eq_invert_permut n).
Theorem eq_invert_permut_body_O :
  leibniz ((nat -> nat) -> nat -> nat) (invert_permut_body O)
    (fun (f : nat -> nat) (m : nat) => match_bool_type nat O O (eqb m (f O))).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.
Definition sym_eq_invert_permut_body_O :
  leibniz ((nat -> nat) -> nat -> nat)
    (fun (f : nat -> nat) (m : nat) => match_bool_type nat O O (eqb m (f O)))
    (invert_permut_body O) :=
  sym_leibniz ((nat -> nat) -> nat -> nat) (invert_permut_body O)
    (fun (f : nat -> nat) (m : nat) => match_bool_type nat O O (eqb m (f O)))
    eq_invert_permut_body_O.
Theorem eq_invert_permut_body_S :
  forall n : nat,
  leibniz ((nat -> nat) -> nat -> nat) (invert_permut_body (S n))
    (fun (f : nat -> nat) (m : nat) =>
     match_bool_type nat (S n) (invert_permut n f m) (eqb m (f (S n)))).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.
Definition sym_eq_invert_permut_body_S :
  forall n : nat,
  leibniz ((nat -> nat) -> nat -> nat)
    (fun (f : nat -> nat) (m : nat) =>
     match_bool_type nat (S n) (invert_permut n f m) (eqb m (f (S n))))
    (invert_permut_body (S n)) :=
  fun n : nat =>
  sym_leibniz ((nat -> nat) -> nat -> nat) (invert_permut_body (S n))
    (fun (f : nat -> nat) (m : nat) =>
     match_bool_type nat (S n) (invert_permut n f m) (eqb m (f (S n))))
    (eq_invert_permut_body_S n).
Definition invert_permut_f :
  forall (f : nat -> nat) (n m : nat),
  le m n -> injn f n -> eq nat (invert_permut n f (f m)) m :=
  fun (f : nat -> nat) (n m : nat) (lenm : le m n) =>
  le_ind m
    (fun x_417 : nat =>
     injn f x_417 -> eq nat (invert_permut x_417 f (f m)) m)
    (match_nat_prop
       (fun __ : nat => injn f __ -> eq nat (invert_permut __ f (f __)) __)
       (sym_eq_invert_permut O
          (fun y : (nat -> nat) -> nat -> nat =>
           injn f O -> eq nat (y f (f O)) O)
          (sym_eq_filter_nat_type_O ((nat -> nat) -> nat -> nat)
             invert_permut_body
             (fun y : (nat -> nat) -> nat -> nat =>
              injn f O -> eq nat (y f (f O)) O)
             (sym_eq_invert_permut_body_O
                (fun y : (nat -> nat) -> nat -> nat =>
                 injn f O -> eq nat (y f (f O)) O)
                (eq_ind_r bool true
                   (fun x : bool =>
                    (forall i j : nat,
                     le i O -> le j O -> eq nat (f i) (f j) -> eq nat i j) ->
                    eq nat (match_bool_type nat O O x) O)
                   (fun
                      auto : forall i j : nat,
                             le i O ->
                             le j O -> eq nat (f i) (f j) -> eq nat i j =>
                    eq_match_bool_type_true nat O O
                      (fun y : nat => eq nat (match_bool_type nat O O true) y)
                      (refl nat (match_bool_type nat O O true)))
                   (eqb (f O) (f O)) (eqb_n_n (f O))))))
       (fun a : nat =>
        sym_eq_invert_permut (S a)
          (fun y : (nat -> nat) -> nat -> nat =>
           injn f (S a) -> eq nat (y f (f (S a))) (S a))
          (sym_eq_filter_nat_type_S ((nat -> nat) -> nat -> nat)
             invert_permut_body a
             (fun y : (nat -> nat) -> nat -> nat =>
              injn f (S a) -> eq nat (y f (f (S a))) (S a))
             (sym_eq_invert_permut_body_S a
                (fun y : (nat -> nat) -> nat -> nat =>
                 injn f (S a) -> eq nat (y f (f (S a))) (S a))
                (eq_ind_r bool true
                   (fun x : bool =>
                    (forall i j : nat,
                     le i (S a) ->
                     le j (S a) -> eq nat (f i) (f j) -> eq nat i j) ->
                    eq nat
                      (match_bool_type nat (S a)
                         (invert_permut a f (f (S a))) x) 
                      (S a))
                   (fun
                      auto : forall i j : nat,
                             le i (S a) ->
                             le j (S a) -> eq nat (f i) (f j) -> eq nat i j
                    =>
                    eq_match_bool_type_true nat (S a)
                      (invert_permut a f (f (S a)))
                      (fun y : nat =>
                       eq nat
                         (match_bool_type nat (S a)
                            (invert_permut a f (f (S a))) true) y)
                      (refl nat
                         (match_bool_type nat (S a)
                            (invert_permut a f (f (S a))) true)))
                   (eqb (f (S a)) (f (S a))) (eqb_n_n (f (S a))))))) m)
    (fun m0 : nat =>
     sym_eq_invert_permut (S m0)
       (fun y : (nat -> nat) -> nat -> nat =>
        le m m0 ->
        (injn f m0 -> eq nat (invert_permut m0 f (f m)) m) ->
        injn f (S m0) -> eq nat (y f (f m)) m)
       (sym_eq_filter_nat_type_S ((nat -> nat) -> nat -> nat)
          invert_permut_body m0
          (fun y : (nat -> nat) -> nat -> nat =>
           le m m0 ->
           (injn f m0 -> eq nat (invert_permut m0 f (f m)) m) ->
           injn f (S m0) -> eq nat (y f (f m)) m)
          (sym_eq_invert_permut_body_S m0
             (fun y : (nat -> nat) -> nat -> nat =>
              le m m0 ->
              (injn f m0 -> eq nat (invert_permut m0 f (f m)) m) ->
              injn f (S m0) -> eq nat (y f (f m)) m)
             (fun (lem : le m m0)
                (H : injn f m0 -> eq nat (invert_permut m0 f (f m)) m)
                (H1 : injn f (S m0)) =>
              eq_ind_r bool false
                (fun x : bool =>
                 eq nat
                   (match_bool_type nat (S m0) (invert_permut m0 f (f m)) x)
                   m)
                (sym_eq_match_bool_type_false nat 
                   (S m0) (invert_permut m0 f (f m))
                   (fun y : nat => eq nat y m) (H (injn_Sn_n f m0 H1)))
                (eqb (f m) (f (S m0)))
                (not_eq_to_eqb_false (f m) (f (S m0))
                   (fun eqf : eq nat (f m) (f (S m0)) =>
                    absurd (eq nat m (S m0))
                      (H1 m (S m0) (le_S m m0 lem) 
                         (le_n (S m0))
                         (rewrite_l nat (f m)
                            (fun __ : nat => eq nat (f m) __)
                            (refl nat (f m)) (f (S m0)) eqf))
                      (lt_to_not_eq m (S m0) (le_S_S m m0 lem)))))))) n lenm.
Definition let_clause_1063 :
  forall (f : nat -> nat) (n : nat),
  permut f n ->
  forall i j : nat,
  le i n ->
  le j n ->
  forall a : nat,
  And (le a n) (eq nat (f a) i) ->
  le a n ->
  eq nat (f a) i ->
  forall b : nat,
  And (le b n) (eq nat (f b) j) ->
  le b n ->
  eq nat (f b) j ->
  (forall i0 : nat, le i0 n -> le (f i0) n) ->
  injn f n -> eq nat a b -> eq nat (f a) j :=
  fun (f : nat -> nat) (n : nat) (permf : permut f n) 
    (i j : nat) (lein : le i n) (lejn : le j n) (a : nat)
    (_clearme : And (le a n) (eq nat (f a) i)) (lean : le a n)
    (fa : eq nat (f a) i) (b : nat)
    (_clearme0 : And (le b n) (eq nat (f b) j)) (lebn : le b n)
    (fb : eq nat (f b) j) (__ : forall i0 : nat, le i0 n -> le (f i0) n)
    (injf : injn f n) (auto : eq nat a b) =>
  rewrite_r nat b (fun __1 : nat => eq nat (f __1) j) fb a auto.
Definition let_clause_1068 :
  forall (f : nat -> nat) (n : nat),
  permut f n ->
  forall i j : nat,
  le i n ->
  le j n ->
  forall a : nat,
  And (le a n) (eq nat (f a) i) ->
  le a n ->
  eq nat (f a) i ->
  forall b : nat,
  And (le b n) (eq nat (f b) j) ->
  le b n ->
  eq nat (f b) j ->
  (forall i0 : nat, le i0 n -> le (f i0) n) ->
  injn f n -> eq nat a b -> eq nat (f a) i :=
  fun (f : nat -> nat) (n : nat) (permf : permut f n) 
    (i j : nat) (lein : le i n) (lejn : le j n) (a : nat)
    (_clearme : And (le a n) (eq nat (f a) i)) (lean : le a n)
    (fa : eq nat (f a) i) (b : nat)
    (_clearme0 : And (le b n) (eq nat (f b) j)) (lebn : le b n)
    (fb : eq nat (f b) j) (__ : forall i0 : nat, le i0 n -> le (f i0) n)
    (injf : injn f n) (auto : eq nat a b) =>
  rewrite_l nat j (fun __1 : nat => eq nat (f a) __1)
    (let_clause_1063 f n permf i j lein lejn a _clearme lean fa b _clearme0
       lebn fb __ injf auto) i
    (rewrite_l nat (f a) (fun __1 : nat => eq nat __1 i) fa j
       (let_clause_1063 f n permf i j lein lejn a _clearme lean fa b
          _clearme0 lebn fb __ injf auto)).
Definition injective_invert_permut :
  forall (f : nat -> nat) (n : nat), permut f n -> injn (invert_permut n f) n :=
  fun (f : nat -> nat) (n : nat) (permf : permut f n) 
    (i j : nat) (lein : le i n) (lejn : le j n) =>
  match_ex_prop nat (fun p : nat => And (le p n) (eq nat (f p) i))
    (eq nat (invert_permut n f i) (invert_permut n f j) -> eq nat i j)
    (fun (a : nat) (_clearme : And (le a n) (eq nat (f a) i)) =>
     match_And_prop (le a n) (eq nat (f a) i)
       (eq nat (invert_permut n f i) (invert_permut n f j) -> eq nat i j)
       (fun (lean : le a n) (fa : eq nat (f a) i) =>
        match_ex_prop nat (fun p : nat => And (le p n) (eq nat (f p) j))
          (eq nat (invert_permut n f i) (invert_permut n f j) -> eq nat i j)
          (fun (b : nat) (_clearme0 : And (le b n) (eq nat (f b) j)) =>
           match_And_prop (le b n) (eq nat (f b) j)
             (eq nat (invert_permut n f i) (invert_permut n f j) ->
              eq nat i j)
             (fun (lebn : le b n) (fb : eq nat (f b) j) =>
              match_And_prop (forall i1 : nat, le i1 n -> le (f i1) n)
                (injn f n)
                (eq nat (invert_permut n f i) (invert_permut n f j) ->
                 eq nat i j)
                (fun (__ : forall i0 : nat, le i0 n -> le (f i0) n)
                   (injf : injn f n) =>
                 eq_ind nat (f a)
                   (fun x_1 : nat =>
                    eq nat (invert_permut n f x_1) (invert_permut n f j) ->
                    eq nat x_1 j)
                   (eq_ind nat (f b)
                      (fun x_1 : nat =>
                       eq nat (invert_permut n f (f a))
                         (invert_permut n f x_1) -> 
                       eq nat (f a) x_1)
                      (eq_ind_r nat a
                         (fun x : nat =>
                          eq nat x (invert_permut n f (f b)) ->
                          eq nat (f a) (f b))
                         (eq_ind_r nat b
                            (fun x : nat => eq nat a x -> eq nat (f a) (f b))
                            (fun auto : eq nat a b =>
                             rewrite_r nat i
                               (fun __1 : nat => eq nat __1 (f b))
                               (rewrite_l nat a
                                  (fun __1 : nat => eq nat i (f __1))
                                  (rewrite_r nat i
                                     (fun __1 : nat => eq nat i __1)
                                     (refl nat i) 
                                     (f a)
                                     (let_clause_1068 f n permf i j lein lejn
                                        a _clearme lean fa b _clearme0 lebn
                                        fb __ injf auto)) b auto) 
                               (f a)
                               (let_clause_1068 f n permf i j lein lejn a
                                  _clearme lean fa b _clearme0 lebn fb __
                                  injf auto)) (invert_permut n f (f b))
                            (invert_permut_f f n b lebn injf))
                         (invert_permut n f (f a))
                         (invert_permut_f f n a lean injf)) j fb) i fa) permf)
             _clearme0) (permut_to_bijn n f permf j lejn)) _clearme)
    (permut_to_bijn n f permf i lein).
Definition permut_invert_permut :
  forall (f : nat -> nat) (n : nat),
  permut f n -> permut (invert_permut n f) n :=
  fun (f : nat -> nat) (n : nat) (permf : permut f n) 
    (z : Prop)
    (f9 : (forall x : nat, le x n -> le (invert_permut n f x) n) ->
          injn (invert_permut n f) n -> z) =>
  f9
    (fun (i : nat) (lein : le i n) =>
     nat_ind (fun _x_365 : nat => le (invert_permut _x_365 f i) _x_365)
       (sym_eq_invert_permut O
          (fun y : (nat -> nat) -> nat -> nat => le (y f i) O)
          (sym_eq_filter_nat_type_O ((nat -> nat) -> nat -> nat)
             invert_permut_body
             (fun y : (nat -> nat) -> nat -> nat => le (y f i) O)
             (sym_eq_invert_permut_body_O
                (fun y : (nat -> nat) -> nat -> nat => le (y f i) O)
                (match_bool_prop
                   (fun __ : bool => le (match_bool_type nat O O __) O)
                   (eq_match_bool_type_true nat O O
                      (fun y : nat => le (match_bool_type nat O O true) y)
                      (le_n (match_bool_type nat O O true)))
                   (eq_match_bool_type_false nat O O
                      (fun y : nat => le (match_bool_type nat O O false) y)
                      (le_n (match_bool_type nat O O false))) 
                   (eqb i (f O))))))
       (fun n1 : nat =>
        sym_eq_invert_permut (S n1)
          (fun y : (nat -> nat) -> nat -> nat =>
           le (invert_permut n1 f i) n1 -> le (y f i) (S n1))
          (sym_eq_filter_nat_type_S ((nat -> nat) -> nat -> nat)
             invert_permut_body n1
             (fun y : (nat -> nat) -> nat -> nat =>
              le (invert_permut n1 f i) n1 -> le (y f i) (S n1))
             (sym_eq_invert_permut_body_S n1
                (fun y : (nat -> nat) -> nat -> nat =>
                 le (invert_permut n1 f i) n1 -> le (y f i) (S n1))
                (fun Hind : le (invert_permut n1 f i) n1 =>
                 match_bool_prop
                   (fun __ : bool =>
                    le (match_bool_type nat (S n1) (invert_permut n1 f i) __)
                      (S n1))
                   (eq_match_bool_type_true nat (S n1) 
                      (invert_permut n1 f i)
                      (fun y : nat =>
                       le
                         (match_bool_type nat (S n1) 
                            (invert_permut n1 f i) true) y)
                      (le_n
                         (match_bool_type nat (S n1) 
                            (invert_permut n1 f i) true)))
                   (sym_eq_match_bool_type_false nat 
                      (S n1) (invert_permut n1 f i)
                      (fun y : nat => le y (S n1))
                      (le_S (invert_permut n1 f i) n1 Hind))
                   (eqb i (f (S n1))))))) n)
    (injective_invert_permut f n permf).
Definition f_invert_permut :
  forall (f : nat -> nat) (n m : nat),
  le m n -> permut f n -> eq nat (f (invert_permut n f m)) m :=
  fun (f : nat -> nat) (n m : nat) (lemn : le m n) (permf : permut f n) =>
  match_And_prop (forall i : nat, le i n -> le (invert_permut n f i) n)
    (injn (invert_permut n f) n) (eq nat (f (invert_permut n f m)) m)
    (fun (Hle : forall i : nat, le i n -> le (invert_permut n f i) n)
       (Hinj : injn (invert_permut n f) n) =>
     match_And_prop (forall i : nat, le i n -> le (f i) n) 
       (injn f n) (eq nat (f (invert_permut n f m)) m)
       (fun (lef : forall i : nat, le i n -> le (f i) n) (injf : injn f n) =>
        injective_invert_permut f n permf (f (invert_permut n f m)) m
          (lef (invert_permut n f m) (Hle m lemn)) lemn
          (invert_permut_f f n (invert_permut n f m) (Hle m lemn) injf))
       permf) (permut_invert_permut f n permf).

Fixpoint gcd_aux (p m n : nat) : nat :=
  match p with
  | 0 => m
  | Datatypes.S p => if dividesb n m then n else gcd_aux p n (mod m n)
  end.

Definition gcd_aux_body : nat -> nat -> nat -> nat := gcd_aux.

Theorem eq_gcd_aux :
  forall p : nat,
  leibniz (nat -> nat -> nat) (gcd_aux p)
    (filter_nat_type (nat -> nat -> nat) gcd_aux_body p).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.

Definition sym_eq_gcd_aux :
  forall p : nat,
  leibniz (nat -> nat -> nat)
    (filter_nat_type (nat -> nat -> nat) gcd_aux_body p) 
    (gcd_aux p) :=
  fun p : nat =>
  sym_leibniz (nat -> nat -> nat) (gcd_aux p)
    (filter_nat_type (nat -> nat -> nat) gcd_aux_body p) 
    (eq_gcd_aux p).
Theorem eq_gcd_aux_body_O :
  leibniz (nat -> nat -> nat) (gcd_aux_body O) (fun m n : nat => m).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.
Definition sym_eq_gcd_aux_body_O :
  leibniz (nat -> nat -> nat) (fun m n : nat => m) (gcd_aux_body O) :=
  sym_leibniz (nat -> nat -> nat) (gcd_aux_body O) 
    (fun m n : nat => m) eq_gcd_aux_body_O.
Theorem eq_gcd_aux_body_S :
  forall p : nat,
  leibniz (nat -> nat -> nat) (gcd_aux_body (S p))
    (fun m n : nat =>
     match_bool_type nat n (gcd_aux p n (mod m n)) (dividesb n m)).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.

Definition sym_eq_gcd_aux_body_S :
  forall p : nat,
  leibniz (nat -> nat -> nat)
    (fun m n : nat =>
     match_bool_type nat n (gcd_aux p n (mod m n)) (dividesb n m))
    (gcd_aux_body (S p)) :=
  fun p : nat =>
  sym_leibniz (nat -> nat -> nat) (gcd_aux_body (S p))
    (fun m n : nat =>
     match_bool_type nat n (gcd_aux p n (mod m n)) (dividesb n m))
    (eq_gcd_aux_body_S p).
Definition gcd : nat -> nat -> nat :=
  fun n m : nat =>
  match_bool_type nat (gcd_aux n m n) (gcd_aux m n m) (leb n m).
Definition commutative_gcd : forall n m : nat, eq nat (gcd n m) (gcd m n) :=
  fun n m : nat =>
  leb_elim n m
    (fun __ : bool =>
     eq nat (match_bool_type nat (gcd_aux n m n) (gcd_aux m n m) __)
       (match_bool_type nat (gcd_aux m n m) (gcd_aux n m n) (leb m n)))
    (fun lenm : le n m =>
     match_Or_prop (lt n m) (eq nat n m)
       (eq nat (match_bool_type nat (gcd_aux n m n) (gcd_aux m n m) true)
          (match_bool_type nat (gcd_aux m n m) (gcd_aux n m n) (leb m n)))
       (fun ltnm : lt n m =>
        eq_ind_r bool false
          (fun x : bool =>
           eq nat (match_bool_type nat (gcd_aux n m n) (gcd_aux m n m) true)
             (match_bool_type nat (gcd_aux m n m) (gcd_aux n m n) x))
          (sym_eq_match_bool_type_false nat (gcd_aux m n m) 
             (gcd_aux n m n)
             (fun y : nat =>
              eq nat
                (match_bool_type nat (gcd_aux n m n) (gcd_aux m n m) true) y)
             (eq_match_bool_type_true nat (gcd_aux n m n) 
                (gcd_aux m n m)
                (fun y : nat =>
                 eq nat
                   (match_bool_type nat (gcd_aux n m n) (gcd_aux m n m) true)
                   y)
                (refl nat
                   (match_bool_type nat (gcd_aux n m n) (gcd_aux m n m) true))))
          (leb m n) (not_le_to_leb_false m n (lt_to_not_le n m ltnm)))
       (fun eqnm : eq nat n m =>
        eq_ind_r nat m
          (fun x : nat =>
           eq nat (match_bool_type nat (gcd_aux x m x) (gcd_aux m x m) true)
             (match_bool_type nat (gcd_aux m x m) (gcd_aux x m x) (leb m x)))
          (match_bool_prop
             (fun __ : bool =>
              eq nat
                (match_bool_type nat (gcd_aux m m m) (gcd_aux m m m) true)
                (match_bool_type nat (gcd_aux m m m) (gcd_aux m m m) __))
             (refl nat
                (match_bool_type nat (gcd_aux m m m) (gcd_aux m m m) true))
             (sym_eq_match_bool_type_false nat (gcd_aux m m m)
                (gcd_aux m m m)
                (fun y : nat =>
                 eq nat
                   (match_bool_type nat (gcd_aux m m m) (gcd_aux m m m) true)
                   y)
                (eq_match_bool_type_true nat (gcd_aux m m m) 
                   (gcd_aux m m m)
                   (fun y : nat =>
                    eq nat
                      (match_bool_type nat (gcd_aux m m m) 
                         (gcd_aux m m m) true) y)
                   (refl nat
                      (match_bool_type nat (gcd_aux m m m) 
                         (gcd_aux m m m) true)))) 
             (leb m m)) n eqnm) (le_to_or_lt_eq n m lenm))
    (fun notlenm : Not (le n m) =>
     eq_ind_r bool true
       (fun x : bool =>
        eq nat (match_bool_type nat (gcd_aux n m n) (gcd_aux m n m) false)
          (match_bool_type nat (gcd_aux m n m) (gcd_aux n m n) x))
       (sym_eq_match_bool_type_false nat (gcd_aux n m n) 
          (gcd_aux m n m)
          (fun y : nat =>
           eq nat y
             (match_bool_type nat (gcd_aux m n m) (gcd_aux n m n) true))
          (sym_eq_match_bool_type_true nat (gcd_aux m n m) 
             (gcd_aux n m n) (fun y : nat => eq nat (gcd_aux m n m) y)
             (eq_match_bool_type_false nat (gcd_aux n m n) 
                (gcd_aux m n m) (fun y : nat => eq nat (gcd_aux m n m) y)
                (eq_match_bool_type_false nat (gcd_aux n m n) 
                   (gcd_aux m n m)
                   (fun y : nat =>
                    eq nat y
                      (match_bool_type nat (gcd_aux n m n) 
                         (gcd_aux m n m) false))
                   (refl nat
                      (match_bool_type nat (gcd_aux n m n) 
                         (gcd_aux m n m) false)))))) 
       (leb m n)
       (le_to_leb_true m n
          (transitive_le m (S m) n (le_n_Sn m) (not_le_to_lt n m notlenm)))).
Definition gcd_O_l : forall m : nat, eq nat (gcd O m) m :=
  fun m : nat =>
  eq_match_bool_type_true nat m (gcd_aux m O m)
    (fun y : nat => eq nat (gcd O m) y)
    (eq_leb_body_O
       (fun y : nat -> bool =>
        eq nat (gcd O m) (match_bool_type nat m (gcd_aux m O m) (y m)))
       (eq_filter_nat_type_O (nat -> bool) leb_body
          (fun y : nat -> bool =>
           eq nat (gcd O m) (match_bool_type nat m (gcd_aux m O m) (y m)))
          (eq_leb O
             (fun y : nat -> bool =>
              eq nat (gcd O m) (match_bool_type nat m (gcd_aux m O m) (y m)))
             (eq_gcd_aux_body_O
                (fun y : nat -> nat -> nat =>
                 eq nat (gcd O m)
                   (match_bool_type nat (y m O) (gcd_aux m O m) (leb O m)))
                (eq_filter_nat_type_O (nat -> nat -> nat) gcd_aux_body
                   (fun y : nat -> nat -> nat =>
                    eq nat (gcd O m)
                      (match_bool_type nat (y m O) (gcd_aux m O m) (leb O m)))
                   (eq_gcd_aux O
                      (fun y : nat -> nat -> nat =>
                       eq nat (gcd O m)
                         (match_bool_type nat (y m O) 
                            (gcd_aux m O m) (leb O m))) 
                      (refl nat (gcd O m)))))))).
Definition divides_mod_to_divides :
  forall p m n : nat,
  lt O n -> divides p (mod m n) -> divides p n -> divides p m :=
  fun (p m n : nat) (posn : lt O n) (_clearme : divides p (mod m n)) =>
  match_divides_prop p (mod m n) (divides p n -> divides p m)
    (fun (q1 : nat) (eq1 : eq nat (mod m n) (times p q1))
       (_clearme0 : divides p n) =>
     match_divides_prop p n (divides p m)
       (fun (q2 : nat) (eq2 : eq nat n (times p q2)) =>
        quotient p m (plus (times q2 (div m n)) q1)
          (eq_ind_r nat (plus (times p (times q2 (div m n))) (times p q1))
             (fun x : nat => eq nat m x)
             (eq_ind nat (mod m n)
                (fun x_1 : nat =>
                 eq nat m (plus (times p (times q2 (div m n))) x_1))
                (eq_ind nat (times (times p q2) (div m n))
                   (fun x_1 : nat => eq nat m (plus x_1 (mod m n)))
                   (eq_ind nat n
                      (fun x_1 : nat =>
                       eq nat m (plus (times x_1 (div m n)) (mod m n)))
                      (rewrite_r nat (plus (mod m n) (times n (div m n)))
                         (fun __ : nat => eq nat m __)
                         (rewrite_l nat m (fun __ : nat => eq nat m __)
                            (refl nat m) (plus (mod m n) (times n (div m n)))
                            (rewrite_l nat
                               (plus (times n (div m n)) (mod m n))
                               (fun __ : nat => eq nat m __)
                               (rewrite_l nat (times (div m n) n)
                                  (fun __ : nat =>
                                   eq nat m (plus __ (mod m n)))
                                  (div_mod m n) (times n (div m n))
                                  (commutative_times (div m n) n))
                               (plus (mod m n) (times n (div m n)))
                               (commutative_plus (times n (div m n))
                                  (mod m n))))
                         (plus (times n (div m n)) (mod m n))
                         (commutative_plus (times n (div m n)) (mod m n)))
                      (times p q2) eq2) (times p (times q2 (div m n)))
                   (associative_times p q2 (div m n))) 
                (times p q1) eq1) (times p (plus (times q2 (div m n)) q1))
             (distributive_times_plus p (times q2 (div m n)) q1))) _clearme0)
    _clearme.
Definition divides_to_gcd_aux :
  forall p m n : nat,
  lt O p -> lt O n -> divides n m -> eq nat (gcd_aux p m n) n :=
  fun (p m n : nat) (posp : lt O p) =>
  lt_O_n_elim p posp
    (fun __ : nat => lt O n -> divides n m -> eq nat (gcd_aux __ m n) n)
    (fun l : nat =>
     sym_eq_gcd_aux (S l)
       (fun y : nat -> nat -> nat =>
        lt O n -> divides n m -> eq nat (y m n) n)
       (sym_eq_filter_nat_type_S (nat -> nat -> nat) gcd_aux_body l
          (fun y : nat -> nat -> nat =>
           lt O n -> divides n m -> eq nat (y m n) n)
          (sym_eq_gcd_aux_body_S l
             (fun y : nat -> nat -> nat =>
              lt O n -> divides n m -> eq nat (y m n) n)
             (fun (posn : lt O n) (divnm : divides n m) =>
              eq_ind_r bool true
                (fun x : bool =>
                 eq nat (match_bool_type nat n (gcd_aux l n (mod m n)) x) n)
                (sym_eq_match_bool_type_true nat n
                   (gcd_aux l n
                      (match_nat_type nat m (fun p0 : nat => mod_aux m m p0)
                         n)) (fun y : nat => eq nat y n) 
                   (refl nat n)) (dividesb n m)
                (divides_to_dividesb_true n m posn divnm))))).
Definition not_divides_to_gcd_aux :
  forall p m n : nat,
  lt O n ->
  Not (divides n m) -> eq nat (gcd_aux (S p) m n) (gcd_aux p n (mod m n)) :=
  fun p m n : nat =>
  sym_eq_gcd_aux (S p)
    (fun y : nat -> nat -> nat =>
     lt O n -> Not (divides n m) -> eq nat (y m n) (gcd_aux p n (mod m n)))
    (sym_eq_filter_nat_type_S (nat -> nat -> nat) gcd_aux_body p
       (fun y : nat -> nat -> nat =>
        lt O n -> Not (divides n m) -> eq nat (y m n) (gcd_aux p n (mod m n)))
       (sym_eq_gcd_aux_body_S p
          (fun y : nat -> nat -> nat =>
           lt O n ->
           Not (divides n m) -> eq nat (y m n) (gcd_aux p n (mod m n)))
          (fun (lenm : lt O n) (divnm : Not (divides n m)) =>
           eq_ind_r bool false
             (fun x : bool =>
              eq nat (match_bool_type nat n (gcd_aux p n (mod m n)) x)
                (gcd_aux p n (mod m n)))
             (sym_eq_match_bool_type_false nat n
                (gcd_aux p n
                   (match_nat_type nat m (fun p0 : nat => mod_aux m m p0) n))
                (fun y : nat =>
                 eq nat y
                   (gcd_aux p n
                      (match_nat_type nat m (fun p0 : nat => mod_aux m m p0)
                         n)))
                (refl nat
                   (gcd_aux p n
                      (match_nat_type nat m (fun p0 : nat => mod_aux m m p0)
                         n)))) (dividesb n m)
             (not_divides_to_dividesb_false n m lenm divnm)))).
Definition divides_gcd_aux_mn :
  forall p m n : nat,
  lt O n ->
  le n m ->
  le n p -> And (divides (gcd_aux p m n) m) (divides (gcd_aux p m n) n) :=
  fun p : nat =>
  nat_ind
    (fun _x_365 : nat =>
     forall m n : nat,
     lt O n ->
     le n m ->
     le n _x_365 ->
     And (divides (gcd_aux _x_365 m n) m) (divides (gcd_aux _x_365 m n) n))
    (fun (m n : nat) (posn : lt O n) (lenm : le n m) (lenO : le n O) =>
     falsity (And (divides (gcd_aux O m n) m) (divides (gcd_aux O m n) n))
       (absurd (lt O n) posn (le_to_not_lt n O lenO)))
    (fun (q : nat)
       (Hind : forall m n : nat,
               lt O n ->
               le n m ->
               le n q ->
               And (divides (gcd_aux q m n) m) (divides (gcd_aux q m n) n))
       (m n : nat) (posn : lt O n) (lenm : le n m) 
       (lenS : le n (S q)) =>
     match_Or_prop (divides n m) (Not (divides n m))
       (And (divides (gcd_aux (S q) m n) m) (divides (gcd_aux (S q) m n) n))
       (fun divnm : divides n m =>
        eq_ind_r nat n (fun x : nat => And (divides x m) (divides x n))
          (fun (z : Prop) (f : divides n m -> divides n n -> z) =>
           f divnm (divides_n_n n)) (gcd_aux (S q) m n)
          (divides_to_gcd_aux (S q) m n (lt_O_S q) posn divnm))
       (fun ndivnm : Not (divides n m) =>
        eq_ind_r nat (gcd_aux q n (mod m n))
          (fun x : nat => And (divides x m) (divides x n))
          (match_And_prop (divides (gcd_aux q n (mod m n)) n)
             (divides (gcd_aux q n (mod m n)) (mod m n))
             (And (divides (gcd_aux q n (mod m n)) m)
                (divides (gcd_aux q n (mod m n)) n))
             (fun (H : divides (gcd_aux q n (mod m n)) n)
                (H1 : divides (gcd_aux q n (mod m n)) (mod m n)) 
                (z : Prop)
                (f : divides (gcd_aux q n (mod m n)) m ->
                     divides (gcd_aux q n (mod m n)) n -> z) =>
              f
                (divides_mod_to_divides (gcd_aux q n (mod m n)) m n posn H1 H)
                H)
             (Hind n (mod m n)
                (match_Or_prop (lt O (mod m n)) (eq nat O (mod m n))
                   (lt O (mod m n)) (fun auto : lt O (mod m n) => auto)
                   (fun modO : eq nat O (mod m n) =>
                    falsity (lt O (mod m n))
                      (absurd (divides n m)
                         (mod_O_to_divides n m posn
                            (rewrite_l nat O (fun __ : nat => eq nat __ O)
                               (refl nat O) (mod m n) modO)) ndivnm))
                   (le_to_or_lt_eq O (mod m n) (le_O_n (mod m n))))
                (lt_to_le (mod m n) n (lt_mod_m_m m n posn))
                (le_S_S_to_le (mod m n) q
                   (transitive_le (S (mod m n)) n 
                      (S q) (lt_mod_m_m m n posn) lenS))))
          (gcd_aux (S q) m n) (not_divides_to_gcd_aux q m n posn ndivnm))
       (decidable_divides n m)) p.
Definition divides_gcd_nm :
  forall n m : nat, And (divides (gcd n m) m) (divides (gcd n m) n) :=
  fun n m : nat =>
  match_Or_prop (lt O n) (eq nat O n)
    (And (divides (gcd n m) m) (divides (gcd n m) n))
    (fun posn : lt O n =>
     match_Or_prop (lt O m) (eq nat O m)
       (And (divides (gcd n m) m) (divides (gcd n m) n))
       (fun posm : lt O m =>
        leb_elim n m
          (fun __ : bool =>
           And
             (divides
                (match_bool_type nat (gcd_aux n m n) (gcd_aux m n m) __) m)
             (divides
                (match_bool_type nat (gcd_aux n m n) (gcd_aux m n m) __) n))
          (sym_eq_match_bool_type_true nat (gcd_aux n m n) 
             (gcd_aux m n m)
             (fun y : nat =>
              le n m ->
              And
                (divides
                   (match_bool_type nat (gcd_aux n m n) (gcd_aux m n m) true)
                   m) (divides y n))
             (sym_eq_match_bool_type_true nat (gcd_aux n m n) 
                (gcd_aux m n m)
                (fun y : nat =>
                 le n m -> And (divides y m) (divides (gcd_aux n m n) n))
                (fun lenm : le n m =>
                 divides_gcd_aux_mn n m n posn lenm (le_n n))))
          (sym_eq_match_bool_type_false nat (gcd_aux n m n) 
             (gcd_aux m n m)
             (fun y : nat =>
              Not (le n m) ->
              And
                (divides
                   (match_bool_type nat (gcd_aux n m n) (gcd_aux m n m) false)
                   m) (divides y n))
             (sym_eq_match_bool_type_false nat (gcd_aux n m n)
                (gcd_aux m n m)
                (fun y : nat =>
                 Not (le n m) ->
                 And (divides y m) (divides (gcd_aux m n m) n))
                (fun notlt : Not (le n m) =>
                 match_And_prop (divides (gcd_aux m n m) n)
                   (divides (gcd_aux m n m) m)
                   (And (divides (gcd_aux m n m) m)
                      (divides (gcd_aux m n m) n))
                   (fun (auto : divides (gcd_aux m n m) n)
                      (auto' : divides (gcd_aux m n m) m) 
                      (z : Prop)
                      (f : divides (gcd_aux m n m) m ->
                           divides (gcd_aux m n m) n -> z) => 
                    f auto' auto)
                   (divides_gcd_aux_mn m n m posm
                      (transitive_le m (S m) n (le_n_Sn m)
                         (not_le_to_lt n m notlt)) 
                      (le_n m))))))
       (fun eqmO : eq nat O m =>
        eq_ind nat O
          (fun x_1 : nat =>
           And (divides (gcd n x_1) x_1) (divides (gcd n x_1) n))
          (fun (z : Prop)
             (f : divides (gcd n O) O -> divides (gcd n O) n -> z) =>
           f (divides_n_O (gcd n O))
             (eq_coerc (divides (gcd n O) (gcd n O)) 
                (divides (gcd n O) n) (divides_n_n (gcd n O))
                (rewrite_r nat n
                   (fun __ : nat =>
                    eq Prop (divides (gcd n O) __) (divides (gcd n O) n))
                   (refl Prop (divides (gcd n O) n)) 
                   (gcd n O)
                   (rewrite_l nat (gcd O n)
                      (fun __ : nat => eq nat (gcd n O) __)
                      (commutative_gcd n O) n (gcd_O_l n))))) m eqmO)
       (le_to_or_lt_eq O m (le_O_n m)))
    (fun eqnO : eq nat O n =>
     eq_ind nat O
       (fun x_1 : nat =>
        And (divides (gcd x_1 m) m) (divides (gcd x_1 m) x_1))
       (fun (z : Prop) (f : divides (gcd O m) m -> divides (gcd O m) O -> z)
        =>
        f
          (eq_match_bool_type_true nat m (gcd_aux m O m)
             (fun y : nat =>
              divides
                (match_bool_type nat (gcd_aux O m O) 
                   (gcd_aux m O m) (leb O m)) y)
             (eq_leb_body_O
                (fun y : nat -> bool =>
                 divides
                   (match_bool_type nat (gcd_aux O m O) 
                      (gcd_aux m O m) (leb O m))
                   (match_bool_type nat m (gcd_aux m O m) (y m)))
                (eq_filter_nat_type_O (nat -> bool) leb_body
                   (fun y : nat -> bool =>
                    divides
                      (match_bool_type nat (gcd_aux O m O) 
                         (gcd_aux m O m) (leb O m))
                      (match_bool_type nat m (gcd_aux m O m) (y m)))
                   (eq_leb O
                      (fun y : nat -> bool =>
                       divides
                         (match_bool_type nat (gcd_aux O m O) 
                            (gcd_aux m O m) (leb O m))
                         (match_bool_type nat m (gcd_aux m O m) (y m)))
                      (eq_gcd_aux_body_O
                         (fun y : nat -> nat -> nat =>
                          divides (gcd O m)
                            (match_bool_type nat (y m O) 
                               (gcd_aux m O m) (leb O m)))
                         (eq_filter_nat_type_O (nat -> nat -> nat)
                            gcd_aux_body
                            (fun y : nat -> nat -> nat =>
                             divides (gcd O m)
                               (match_bool_type nat 
                                  (y m O) (gcd_aux m O m) 
                                  (leb O m)))
                            (eq_gcd_aux O
                               (fun y : nat -> nat -> nat =>
                                divides (gcd O m)
                                  (match_bool_type nat 
                                     (y m O) (gcd_aux m O m) 
                                     (leb O m))) (divides_n_n (gcd O m)))))))))
          (divides_n_O (gcd O m))) n eqnO) (le_to_or_lt_eq O n (le_O_n n)).
Definition divides_gcd_l : forall n m : nat, divides (gcd n m) n :=
  fun n m : nat =>
  proj2 (divides (gcd n m) m) (divides (gcd n m) n) (divides_gcd_nm n m).
Definition divides_gcd_r : forall n m : nat, divides (gcd n m) m :=
  fun n m : nat =>
  proj1 (divides (gcd n m) m) (divides (gcd n m) n) (divides_gcd_nm n m).
Definition let_clause_1544 :
  forall p q : nat,
  (forall m n : nat,
   lt O n ->
   le n m ->
   le n q ->
   Ex nat
     (fun a : nat =>
      Ex nat
        (fun b : nat =>
         Or (eq nat (minus (times a n) (times b m)) (gcd_aux q m n))
           (eq nat (minus (times b m) (times a n)) (gcd_aux q m n))))) ->
  forall m n : nat,
  lt O n ->
  le n m ->
  le n (S q) ->
  Not (divides n m) ->
  forall a : nat,
  Ex nat
    (fun b : nat =>
     Or
       (eq nat (minus (times a (mod m n)) (times b n))
          (gcd_aux q n (mod m n)))
       (eq nat (minus (times b n) (times a (mod m n)))
          (gcd_aux q n (mod m n)))) ->
  forall b : nat,
  Or (eq nat (minus (times a (mod m n)) (times b n)) (gcd_aux q n (mod m n)))
    (eq nat (minus (times b n) (times a (mod m n))) (gcd_aux q n (mod m n))) ->
  eq nat (minus (times a (mod m n)) (times b n)) (gcd_aux q n (mod m n)) ->
  eq nat (minus (times a (mod m n)) (times n b)) (gcd_aux q n (mod m n)) :=
  fun (p q : nat)
    (Hind : forall m n : nat,
            lt O n ->
            le n m ->
            le n q ->
            Ex nat
              (fun a : nat =>
               Ex nat
                 (fun b : nat =>
                  Or (eq nat (minus (times a n) (times b m)) (gcd_aux q m n))
                    (eq nat (minus (times b m) (times a n)) (gcd_aux q m n)))))
    (m n : nat) (posn : lt O n) (lenm : le n m) (lenS : le n (S q))
    (ndivnm : Not (divides n m)) (a : nat)
    (_clearme : Ex nat
                  (fun b : nat =>
                   Or
                     (eq nat (minus (times a (mod m n)) (times b n))
                        (gcd_aux q n (mod m n)))
                     (eq nat (minus (times b n) (times a (mod m n)))
                        (gcd_aux q n (mod m n))))) 
    (b : nat)
    (_clearme0 : Or
                   (eq nat (minus (times a (mod m n)) (times b n))
                      (gcd_aux q n (mod m n)))
                   (eq nat (minus (times b n) (times a (mod m n)))
                      (gcd_aux q n (mod m n))))
    (H : eq nat (minus (times a (mod m n)) (times b n))
           (gcd_aux q n (mod m n))) =>
  rewrite_l nat (times b n)
    (fun __ : nat =>
     eq nat (minus (times a (mod m n)) __) (gcd_aux q n (mod m n))) H
    (times n b) (commutative_times b n).
Definition let_clause_15441 :
  forall p q : nat,
  (forall m n : nat,
   lt O n ->
   le n m ->
   le n q ->
   Ex nat
     (fun a : nat =>
      Ex nat
        (fun b : nat =>
         Or (eq nat (minus (times a n) (times b m)) (gcd_aux q m n))
           (eq nat (minus (times b m) (times a n)) (gcd_aux q m n))))) ->
  forall m n : nat,
  lt O n ->
  le n m ->
  le n (S q) ->
  Not (divides n m) ->
  forall a : nat,
  Ex nat
    (fun b : nat =>
     Or
       (eq nat (minus (times a (mod m n)) (times b n))
          (gcd_aux q n (mod m n)))
       (eq nat (minus (times b n) (times a (mod m n)))
          (gcd_aux q n (mod m n)))) ->
  forall b : nat,
  Or (eq nat (minus (times a (mod m n)) (times b n)) (gcd_aux q n (mod m n)))
    (eq nat (minus (times b n) (times a (mod m n))) (gcd_aux q n (mod m n))) ->
  eq nat (minus (times b n) (times a (mod m n))) (gcd_aux q n (mod m n)) ->
  eq nat (minus (times n b) (times a (mod m n))) (gcd_aux q n (mod m n)) :=
  fun (p q : nat)
    (Hind : forall m n : nat,
            lt O n ->
            le n m ->
            le n q ->
            Ex nat
              (fun a : nat =>
               Ex nat
                 (fun b : nat =>
                  Or (eq nat (minus (times a n) (times b m)) (gcd_aux q m n))
                    (eq nat (minus (times b m) (times a n)) (gcd_aux q m n)))))
    (m n : nat) (posn : lt O n) (lenm : le n m) (lenS : le n (S q))
    (ndivnm : Not (divides n m)) (a : nat)
    (_clearme : Ex nat
                  (fun b : nat =>
                   Or
                     (eq nat (minus (times a (mod m n)) (times b n))
                        (gcd_aux q n (mod m n)))
                     (eq nat (minus (times b n) (times a (mod m n)))
                        (gcd_aux q n (mod m n))))) 
    (b : nat)
    (_clearme0 : Or
                   (eq nat (minus (times a (mod m n)) (times b n))
                      (gcd_aux q n (mod m n)))
                   (eq nat (minus (times b n) (times a (mod m n)))
                      (gcd_aux q n (mod m n))))
    (H : eq nat (minus (times b n) (times a (mod m n)))
           (gcd_aux q n (mod m n))) =>
  rewrite_l nat (times b n)
    (fun __ : nat =>
     eq nat (minus __ (times a (mod m n))) (gcd_aux q n (mod m n))) H
    (times n b) (commutative_times b n).
Definition eq_minus_gcd_aux :
  forall p m n : nat,
  lt O n ->
  le n m ->
  le n p ->
  Ex nat
    (fun a : nat =>
     Ex nat
       (fun b : nat =>
        Or (eq nat (minus (times a n) (times b m)) (gcd_aux p m n))
          (eq nat (minus (times b m) (times a n)) (gcd_aux p m n)))) :=
  fun p : nat =>
  nat_ind
    (fun _x_365 : nat =>
     forall m n : nat,
     lt O n ->
     le n m ->
     le n _x_365 ->
     Ex nat
       (fun a : nat =>
        Ex nat
          (fun b : nat =>
           Or (eq nat (minus (times a n) (times b m)) (gcd_aux _x_365 m n))
             (eq nat (minus (times b m) (times a n)) (gcd_aux _x_365 m n)))))
    (fun (m n : nat) (posn : lt O n) (lenm : le n m) (lenO : le n O) =>
     falsity
       (Ex nat
          (fun a : nat =>
           Ex nat
             (fun b : nat =>
              Or (eq nat (minus (times a n) (times b m)) (gcd_aux O m n))
                (eq nat (minus (times b m) (times a n)) (gcd_aux O m n)))))
       (absurd (lt O n) posn (le_to_not_lt n O lenO)))
    (fun (q : nat)
       (Hind : forall m n : nat,
               lt O n ->
               le n m ->
               le n q ->
               Ex nat
                 (fun a : nat =>
                  Ex nat
                    (fun b : nat =>
                     Or
                       (eq nat (minus (times a n) (times b m))
                          (gcd_aux q m n))
                       (eq nat (minus (times b m) (times a n))
                          (gcd_aux q m n))))) (m n : nat) 
       (posn : lt O n) (lenm : le n m) (lenS : le n (S q)) =>
     match_Or_prop (divides n m) (Not (divides n m))
       (Ex nat
          (fun a : nat =>
           Ex nat
             (fun b : nat =>
              Or (eq nat (minus (times a n) (times b m)) (gcd_aux (S q) m n))
                (eq nat (minus (times b m) (times a n)) (gcd_aux (S q) m n)))))
       (fun divnm : divides n m =>
        eq_ind_r nat n
          (fun x : nat =>
           Ex nat
             (fun a : nat =>
              Ex nat
                (fun b : nat =>
                 Or (eq nat (minus (times a n) (times b m)) x)
                   (eq nat (minus (times b m) (times a n)) x))))
          (fun (z : Prop)
             (f : forall x : nat,
                  Ex nat
                    (fun b : nat =>
                     Or (eq nat (minus (times x n) (times b m)) n)
                       (eq nat (minus (times b m) (times x n)) n)) -> z) =>
           f (S O)
             (fun (z0 : Prop)
                (f2 : forall x : nat,
                      Or (eq nat (minus (times (S O) n) (times x m)) n)
                        (eq nat (minus (times x m) (times (S O) n)) n) -> z0)
              =>
              f2 O
                (fun (z1 : Prop)
                   (l : eq nat (minus (times (S O) n) (times O m)) n -> z1)
                   (r : eq nat (minus (times O m) (times (S O) n)) n -> z1)
                 =>
                 l
                   (rewrite_r nat (times n (S O))
                      (fun __ : nat => eq nat (minus __ (times O m)) n)
                      (rewrite_l nat (plus n (times n O))
                         (fun __ : nat => eq nat (minus __ (times O m)) n)
                         (rewrite_l nat O
                            (fun __ : nat =>
                             eq nat (minus (plus n __) (times O m)) n)
                            (rewrite_l nat n
                               (fun __ : nat =>
                                eq nat (minus __ (times O m)) n)
                               (rewrite_r nat (times m O)
                                  (fun __ : nat => eq nat (minus n __) n)
                                  (rewrite_l nat O
                                     (fun __ : nat => eq nat (minus n __) n)
                                     (rewrite_l nat n
                                        (fun __ : nat => eq nat __ n)
                                        (refl nat n) 
                                        (minus n O) 
                                        (minus_n_O n)) 
                                     (times m O) (times_n_O m)) 
                                  (times O m) (commutative_times O m))
                               (plus n O) (plus_n_O n)) 
                            (times n O) (times_n_O n)) 
                         (times n (S O)) (times_n_Sm n O)) 
                      (times (S O) n) (commutative_times (S O) n)))))
          (gcd_aux (S q) m n)
          (divides_to_gcd_aux (S q) m n (lt_O_S q) posn divnm))
       (fun ndivnm : Not (divides n m) =>
        eq_ind_r nat (gcd_aux q n (mod m n))
          (fun x : nat =>
           Ex nat
             (fun a : nat =>
              Ex nat
                (fun b : nat =>
                 Or (eq nat (minus (times a n) (times b m)) x)
                   (eq nat (minus (times b m) (times a n)) x))))
          (match_ex_prop nat
             (fun a : nat =>
              Ex nat
                (fun b : nat =>
                 Or
                   (eq nat (minus (times a (mod m n)) (times b n))
                      (gcd_aux q n (mod m n)))
                   (eq nat (minus (times b n) (times a (mod m n)))
                      (gcd_aux q n (mod m n)))))
             (Ex nat
                (fun a : nat =>
                 Ex nat
                   (fun b : nat =>
                    Or
                      (eq nat (minus (times a n) (times b m))
                         (gcd_aux q n (mod m n)))
                      (eq nat (minus (times b m) (times a n))
                         (gcd_aux q n (mod m n))))))
             (fun (a : nat)
                (_clearme : Ex nat
                              (fun b : nat =>
                               Or
                                 (eq nat
                                    (minus (times a (mod m n)) (times b n))
                                    (gcd_aux q n (mod m n)))
                                 (eq nat
                                    (minus (times b n) (times a (mod m n)))
                                    (gcd_aux q n (mod m n))))) =>
              match_ex_prop nat
                (fun b : nat =>
                 Or
                   (eq nat (minus (times a (mod m n)) (times b n))
                      (gcd_aux q n (mod m n)))
                   (eq nat (minus (times b n) (times a (mod m n)))
                      (gcd_aux q n (mod m n))))
                (Ex nat
                   (fun a0 : nat =>
                    Ex nat
                      (fun b : nat =>
                       Or
                         (eq nat (minus (times a0 n) (times b m))
                            (gcd_aux q n (mod m n)))
                         (eq nat (minus (times b m) (times a0 n))
                            (gcd_aux q n (mod m n))))))
                (fun (b : nat)
                   (_clearme0 : Or
                                  (eq nat
                                     (minus (times a (mod m n)) (times b n))
                                     (gcd_aux q n (mod m n)))
                                  (eq nat
                                     (minus (times b n) (times a (mod m n)))
                                     (gcd_aux q n (mod m n)))) =>
                 match_Or_prop
                   (eq nat (minus (times a (mod m n)) (times b n))
                      (gcd_aux q n (mod m n)))
                   (eq nat (minus (times b n) (times a (mod m n)))
                      (gcd_aux q n (mod m n)))
                   (Ex nat
                      (fun a0 : nat =>
                       Ex nat
                         (fun b0 : nat =>
                          Or
                            (eq nat (minus (times a0 n) (times b0 m))
                               (gcd_aux q n (mod m n)))
                            (eq nat (minus (times b0 m) (times a0 n))
                               (gcd_aux q n (mod m n))))))
                   (fun
                      H : eq nat (minus (times a (mod m n)) (times b n))
                            (gcd_aux q n (mod m n)) =>
                    eq_ind nat (minus (times a (mod m n)) (times b n))
                      (fun x_1 : nat =>
                       Ex nat
                         (fun a0 : nat =>
                          Ex nat
                            (fun b0 : nat =>
                             Or
                               (eq nat (minus (times a0 n) (times b0 m)) x_1)
                               (eq nat (minus (times b0 m) (times a0 n)) x_1))))
                      (fun (z : Prop)
                         (f : forall x : nat,
                              Ex nat
                                (fun b0 : nat =>
                                 Or
                                   (eq nat (minus (times x n) (times b0 m))
                                      (minus (times a (mod m n)) (times b n)))
                                   (eq nat (minus (times b0 m) (times x n))
                                      (minus (times a (mod m n)) (times b n)))) ->
                              z) =>
                       f (plus b (times a (div m n)))
                         (fun (z0 : Prop)
                            (f0 : forall x : nat,
                                  Or
                                    (eq nat
                                       (minus
                                          (times (plus b (times a (div m n)))
                                             n) (times x m))
                                       (minus (times a (mod m n)) (times b n)))
                                    (eq nat
                                       (minus (times x m)
                                          (times (plus b (times a (div m n)))
                                             n))
                                       (minus (times a (mod m n)) (times b n))) ->
                                  z0) =>
                          f0 a
                            (fun (z1 : Prop)
                               (l : eq nat
                                      (minus
                                         (times (plus b (times a (div m n)))
                                            n) (times a m))
                                      (minus (times a (mod m n)) (times b n)) ->
                                    z1)
                               (r : eq nat
                                      (minus (times a m)
                                         (times (plus b (times a (div m n)))
                                            n))
                                      (minus (times a (mod m n)) (times b n)) ->
                                    z1) =>
                             r
                               (eq_ind nat (plus (times a (div m n)) b)
                                  (fun x_1 : nat =>
                                   eq nat (minus (times a m) (times x_1 n))
                                     (minus (times a (mod m n)) (times b n)))
                                  (eq_ind_r nat
                                     (plus (times (times a (div m n)) n)
                                        (times b n))
                                     (fun x : nat =>
                                      eq nat (minus (times a m) x)
                                        (minus (times a (mod m n))
                                           (times b n)))
                                     (eq_ind_r nat
                                        (plus (times (div m n) n) (mod m n))
                                        (fun x : nat =>
                                         eq nat
                                           (minus 
                                              (times a x)
                                              (plus
                                                 (times (times a (div m n)) n)
                                                 (times b n)))
                                           (minus 
                                              (times a (mod m n)) 
                                              (times b n)))
                                        (eq_ind_r nat
                                           (times a (times (div m n) n))
                                           (fun x : nat =>
                                            eq nat
                                              (minus
                                                 (times a
                                                 (plus 
                                                 (times (div m n) n)
                                                 (mod m n)))
                                                 (plus x (times b n)))
                                              (minus 
                                                 (times a (mod m n))
                                                 (times b n)))
                                           (eq_ind nat
                                              (plus 
                                                 (mod m n)
                                                 (times (div m n) n))
                                              (fun x_1 : nat =>
                                               eq nat
                                                 (minus 
                                                 (times a x_1)
                                                 (plus
                                                 (times a (times (div m n) n))
                                                 (times b n)))
                                                 (minus 
                                                 (times a (mod m n))
                                                 (times b n)))
                                              (eq_ind_r nat
                                                 (plus 
                                                 (times a (mod m n))
                                                 (times a (times (div m n) n)))
                                                 (fun x : nat =>
                                                 eq nat
                                                 (minus x
                                                 (plus
                                                 (times a (times (div m n) n))
                                                 (times b n)))
                                                 (minus 
                                                 (times a (mod m n))
                                                 (times b n)))
                                                 (eq_ind nat
                                                 (minus
                                                 (minus
                                                 (plus 
                                                 (times a (mod m n))
                                                 (times a (times (div m n) n)))
                                                 (times a (times (div m n) n)))
                                                 (times b n))
                                                 (fun x_1 : nat =>
                                                 eq nat x_1
                                                 (minus 
                                                 (times a (mod m n))
                                                 (times b n)))
                                                 (eq_ind nat
                                                 (plus
                                                 (times a (times (div m n) n))
                                                 (times a (mod m n)))
                                                 (fun x_1 : nat =>
                                                 eq nat
                                                 (minus
                                                 (minus x_1
                                                 (times a (times (div m n) n)))
                                                 (times b n))
                                                 (minus 
                                                 (times a (mod m n))
                                                 (times b n)))
                                                 (eq_ind nat
                                                 (plus
                                                 (minus
                                                 (times a (times (div m n) n))
                                                 (times a (times (div m n) n)))
                                                 (times a (mod m n)))
                                                 (fun x_1 : nat =>
                                                 eq nat
                                                 (minus x_1 (times b n))
                                                 (minus 
                                                 (times a (mod m n))
                                                 (times b n)))
                                                 (rewrite_r nat
                                                 (times n (div m n))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (minus
                                                 (plus
                                                 (minus 
                                                 (times a __)
                                                 (times a (times (div m n) n)))
                                                 (times a (mod m n)))
                                                 (times b n))
                                                 (minus 
                                                 (times a (mod m n))
                                                 (times b n)))
                                                 (rewrite_r nat
                                                 (times n (times a (div m n)))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (minus
                                                 (plus
                                                 (minus __
                                                 (times a (times (div m n) n)))
                                                 (times a (mod m n)))
                                                 (times b n))
                                                 (minus 
                                                 (times a (mod m n))
                                                 (times b n)))
                                                 (rewrite_r nat
                                                 (times n (div m n))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (minus
                                                 (plus
                                                 (minus
                                                 (times n (times a (div m n)))
                                                 (times a __))
                                                 (times a (mod m n)))
                                                 (times b n))
                                                 (minus 
                                                 (times a (mod m n))
                                                 (times b n)))
                                                 (rewrite_r nat
                                                 (times n (times a (div m n)))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (minus
                                                 (plus
                                                 (minus
                                                 (times n (times a (div m n)))
                                                 __) 
                                                 (times a (mod m n)))
                                                 (times b n))
                                                 (minus 
                                                 (times a (mod m n))
                                                 (times b n)))
                                                 (rewrite_l nat O
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (minus
                                                 (plus __ (times a (mod m n)))
                                                 (times b n))
                                                 (minus 
                                                 (times a (mod m n))
                                                 (times b n)))
                                                 (rewrite_l nat
                                                 (times a (mod m n))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (minus __ (times b n))
                                                 (minus 
                                                 (times a (mod m n))
                                                 (times b n)))
                                                 (rewrite_r nat 
                                                 (times n b)
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (minus 
                                                 (times a (mod m n)) __)
                                                 (minus 
                                                 (times a (mod m n))
                                                 (times b n)))
                                                 (rewrite_r nat
                                                 (gcd_aux q n (mod m n))
                                                 (fun __ : nat =>
                                                 eq nat __
                                                 (minus 
                                                 (times a (mod m n))
                                                 (times b n)))
                                                 (rewrite_r nat 
                                                 (times n b)
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (gcd_aux q n (mod m n))
                                                 (minus 
                                                 (times a (mod m n)) __))
                                                 (rewrite_r nat
                                                 (gcd_aux q n (mod m n))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (gcd_aux q n (mod m n)) __)
                                                 (refl nat
                                                 (gcd_aux q n (mod m n)))
                                                 (minus 
                                                 (times a (mod m n))
                                                 (times n b))
                                                 (let_clause_1544 p q Hind m
                                                 n posn lenm lenS ndivnm a
                                                 _clearme b _clearme0 H))
                                                 (times b n)
                                                 (commutative_times b n))
                                                 (minus 
                                                 (times a (mod m n))
                                                 (times n b))
                                                 (let_clause_1544 p q Hind m
                                                 n posn lenm lenS ndivnm a
                                                 _clearme b _clearme0 H))
                                                 (times b n)
                                                 (commutative_times b n))
                                                 (plus O (times a (mod m n)))
                                                 (plus_O_n
                                                 (times a (mod m n))))
                                                 (minus
                                                 (times n (times a (div m n)))
                                                 (times n (times a (div m n))))
                                                 (minus_n_n
                                                 (times n (times a (div m n)))))
                                                 (times a (times n (div m n)))
                                                 (times_times a n (div m n)))
                                                 (times (div m n) n)
                                                 (commutative_times 
                                                 (div m n) n))
                                                 (times a (times n (div m n)))
                                                 (times_times a n (div m n)))
                                                 (times (div m n) n)
                                                 (commutative_times 
                                                 (div m n) n))
                                                 (minus
                                                 (plus
                                                 (times a (times (div m n) n))
                                                 (times a (mod m n)))
                                                 (times a (times (div m n) n)))
                                                 (plus_minus
                                                 (times a (times (div m n) n))
                                                 (times a (times (div m n) n))
                                                 (times a (mod m n))
                                                 (le_n
                                                 (times a (times (div m n) n)))))
                                                 (plus 
                                                 (times a (mod m n))
                                                 (times a (times (div m n) n)))
                                                 (commutative_plus
                                                 (times a (times (div m n) n))
                                                 (times a (mod m n))))
                                                 (minus
                                                 (plus 
                                                 (times a (mod m n))
                                                 (times a (times (div m n) n)))
                                                 (plus
                                                 (times a (times (div m n) n))
                                                 (times b n)))
                                                 (minus_plus
                                                 (plus 
                                                 (times a (mod m n))
                                                 (times a (times (div m n) n)))
                                                 (times a (times (div m n) n))
                                                 (times b n)))
                                                 (times a
                                                 (plus 
                                                 (mod m n)
                                                 (times (div m n) n)))
                                                 (distributive_times_plus a
                                                 (mod m n)
                                                 (times (div m n) n)))
                                              (plus 
                                                 (times (div m n) n)
                                                 (mod m n))
                                              (commutative_plus 
                                                 (mod m n)
                                                 (times (div m n) n)))
                                           (times (times a (div m n)) n)
                                           (associative_times a (div m n) n))
                                        m (div_mod m n))
                                     (times (plus (times a (div m n)) b) n)
                                     (distributive_times_plus_r n
                                        (times a (div m n)) b))
                                  (plus b (times a (div m n)))
                                  (commutative_plus (times a (div m n)) b)))))
                      (gcd_aux q n (mod m n)) H)
                   (fun
                      H : eq nat (minus (times b n) (times a (mod m n)))
                            (gcd_aux q n (mod m n)) =>
                    eq_ind nat (minus (times b n) (times a (mod m n)))
                      (fun x_1 : nat =>
                       Ex nat
                         (fun a0 : nat =>
                          Ex nat
                            (fun b0 : nat =>
                             Or
                               (eq nat (minus (times a0 n) (times b0 m)) x_1)
                               (eq nat (minus (times b0 m) (times a0 n)) x_1))))
                      (fun (z : Prop)
                         (f : forall x : nat,
                              Ex nat
                                (fun b0 : nat =>
                                 Or
                                   (eq nat (minus (times x n) (times b0 m))
                                      (minus (times b n) (times a (mod m n))))
                                   (eq nat (minus (times b0 m) (times x n))
                                      (minus (times b n) (times a (mod m n))))) ->
                              z) =>
                       f (plus b (times a (div m n)))
                         (fun (z0 : Prop)
                            (f0 : forall x : nat,
                                  Or
                                    (eq nat
                                       (minus
                                          (times (plus b (times a (div m n)))
                                             n) (times x m))
                                       (minus (times b n) (times a (mod m n))))
                                    (eq nat
                                       (minus (times x m)
                                          (times (plus b (times a (div m n)))
                                             n))
                                       (minus (times b n) (times a (mod m n)))) ->
                                  z0) =>
                          f0 a
                            (fun (z1 : Prop)
                               (l : eq nat
                                      (minus
                                         (times (plus b (times a (div m n)))
                                            n) (times a m))
                                      (minus (times b n) (times a (mod m n))) ->
                                    z1)
                               (r : eq nat
                                      (minus (times a m)
                                         (times (plus b (times a (div m n)))
                                            n))
                                      (minus (times b n) (times a (mod m n))) ->
                                    z1) =>
                             l
                               (eq_ind_r nat
                                  (plus (times b n)
                                     (times (times a (div m n)) n))
                                  (fun x : nat =>
                                   eq nat (minus x (times a m))
                                     (minus (times b n) (times a (mod m n))))
                                  (eq_ind_r nat
                                     (plus (times (div m n) n) (mod m n))
                                     (fun x : nat =>
                                      eq nat
                                        (minus
                                           (plus (times b n)
                                              (times (times a (div m n)) n))
                                           (times a x))
                                        (minus (times b n)
                                           (times a (mod m n))))
                                     (eq_ind_r nat
                                        (plus (times a (times (div m n) n))
                                           (times a (mod m n)))
                                        (fun x : nat =>
                                         eq nat
                                           (minus
                                              (plus 
                                                 (times b n)
                                                 (times (times a (div m n)) n))
                                              x)
                                           (minus 
                                              (times b n) 
                                              (times a (mod m n))))
                                        (eq_ind_r nat
                                           (times a (times (div m n) n))
                                           (fun x : nat =>
                                            eq nat
                                              (minus 
                                                 (plus (times b n) x)
                                                 (plus
                                                 (times a (times (div m n) n))
                                                 (times a (mod m n))))
                                              (minus 
                                                 (times b n)
                                                 (times a (mod m n))))
                                           (eq_ind nat
                                              (minus
                                                 (minus
                                                 (plus 
                                                 (times b n)
                                                 (times a (times (div m n) n)))
                                                 (times a (times (div m n) n)))
                                                 (times a (mod m n)))
                                              (fun x_1 : nat =>
                                               eq nat x_1
                                                 (minus 
                                                 (times b n)
                                                 (times a (mod m n))))
                                              (eq_ind nat
                                                 (plus
                                                 (times a (times (div m n) n))
                                                 (times b n))
                                                 (fun x_1 : nat =>
                                                 eq nat
                                                 (minus
                                                 (minus x_1
                                                 (times a (times (div m n) n)))
                                                 (times a (mod m n)))
                                                 (minus 
                                                 (times b n)
                                                 (times a (mod m n))))
                                                 (eq_ind nat
                                                 (plus
                                                 (minus
                                                 (times a (times (div m n) n))
                                                 (times a (times (div m n) n)))
                                                 (times b n))
                                                 (fun x_1 : nat =>
                                                 eq nat
                                                 (minus x_1
                                                 (times a (mod m n)))
                                                 (minus 
                                                 (times b n)
                                                 (times a (mod m n))))
                                                 (rewrite_r nat
                                                 (times n (div m n))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (minus
                                                 (plus
                                                 (minus 
                                                 (times a __)
                                                 (times a (times (div m n) n)))
                                                 (times b n))
                                                 (times a (mod m n)))
                                                 (minus 
                                                 (times b n)
                                                 (times a (mod m n))))
                                                 (rewrite_r nat
                                                 (times n (times a (div m n)))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (minus
                                                 (plus
                                                 (minus __
                                                 (times a (times (div m n) n)))
                                                 (times b n))
                                                 (times a (mod m n)))
                                                 (minus 
                                                 (times b n)
                                                 (times a (mod m n))))
                                                 (rewrite_r nat
                                                 (times n (div m n))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (minus
                                                 (plus
                                                 (minus
                                                 (times n (times a (div m n)))
                                                 (times a __)) 
                                                 (times b n))
                                                 (times a (mod m n)))
                                                 (minus 
                                                 (times b n)
                                                 (times a (mod m n))))
                                                 (rewrite_r nat
                                                 (times n (times a (div m n)))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (minus
                                                 (plus
                                                 (minus
                                                 (times n (times a (div m n)))
                                                 __) 
                                                 (times b n))
                                                 (times a (mod m n)))
                                                 (minus 
                                                 (times b n)
                                                 (times a (mod m n))))
                                                 (rewrite_l nat O
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (minus 
                                                 (plus __ (times b n))
                                                 (times a (mod m n)))
                                                 (minus 
                                                 (times b n)
                                                 (times a (mod m n))))
                                                 (rewrite_r nat 
                                                 (times n b)
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (minus 
                                                 (plus O __)
                                                 (times a (mod m n)))
                                                 (minus 
                                                 (times b n)
                                                 (times a (mod m n))))
                                                 (rewrite_l nat 
                                                 (times n b)
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (minus __
                                                 (times a (mod m n)))
                                                 (minus 
                                                 (times b n)
                                                 (times a (mod m n))))
                                                 (rewrite_r nat
                                                 (gcd_aux q n (mod m n))
                                                 (fun __ : nat =>
                                                 eq nat __
                                                 (minus 
                                                 (times b n)
                                                 (times a (mod m n))))
                                                 (rewrite_r nat 
                                                 (times n b)
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (gcd_aux q n (mod m n))
                                                 (minus __
                                                 (times a (mod m n))))
                                                 (rewrite_r nat
                                                 (gcd_aux q n (mod m n))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (gcd_aux q n (mod m n)) __)
                                                 (refl nat
                                                 (gcd_aux q n (mod m n)))
                                                 (minus 
                                                 (times n b)
                                                 (times a (mod m n)))
                                                 (let_clause_15441 p q Hind m
                                                 n posn lenm lenS ndivnm a
                                                 _clearme b _clearme0 H))
                                                 (times b n)
                                                 (commutative_times b n))
                                                 (minus 
                                                 (times n b)
                                                 (times a (mod m n)))
                                                 (let_clause_15441 p q Hind m
                                                 n posn lenm lenS ndivnm a
                                                 _clearme b _clearme0 H))
                                                 (plus O (times n b))
                                                 (plus_O_n (times n b)))
                                                 (times b n)
                                                 (commutative_times b n))
                                                 (minus
                                                 (times n (times a (div m n)))
                                                 (times n (times a (div m n))))
                                                 (minus_n_n
                                                 (times n (times a (div m n)))))
                                                 (times a (times n (div m n)))
                                                 (times_times a n (div m n)))
                                                 (times (div m n) n)
                                                 (commutative_times 
                                                 (div m n) n))
                                                 (times a (times n (div m n)))
                                                 (times_times a n (div m n)))
                                                 (times (div m n) n)
                                                 (commutative_times 
                                                 (div m n) n))
                                                 (minus
                                                 (plus
                                                 (times a (times (div m n) n))
                                                 (times b n))
                                                 (times a (times (div m n) n)))
                                                 (plus_minus
                                                 (times a (times (div m n) n))
                                                 (times a (times (div m n) n))
                                                 (times b n)
                                                 (le_n
                                                 (times a (times (div m n) n)))))
                                                 (plus 
                                                 (times b n)
                                                 (times a (times (div m n) n)))
                                                 (commutative_plus
                                                 (times a (times (div m n) n))
                                                 (times b n)))
                                              (minus
                                                 (plus 
                                                 (times b n)
                                                 (times a (times (div m n) n)))
                                                 (plus
                                                 (times a (times (div m n) n))
                                                 (times a (mod m n))))
                                              (minus_plus
                                                 (plus 
                                                 (times b n)
                                                 (times a (times (div m n) n)))
                                                 (times a (times (div m n) n))
                                                 (times a (mod m n))))
                                           (times (times a (div m n)) n)
                                           (associative_times a (div m n) n))
                                        (times a
                                           (plus (times (div m n) n)
                                              (mod m n)))
                                        (distributive_times_plus a
                                           (times (div m n) n) 
                                           (mod m n))) m 
                                     (div_mod m n))
                                  (times (plus b (times a (div m n))) n)
                                  (distributive_times_plus_r n b
                                     (times a (div m n)))))))
                      (gcd_aux q n (mod m n)) H) _clearme0) _clearme)
             (Hind n (mod m n)
                (match_Or_prop (lt O (mod m n)) (eq nat O (mod m n))
                   (lt O (mod m n)) (fun auto : lt O (mod m n) => auto)
                   (fun modO : eq nat O (mod m n) =>
                    falsity (lt O (mod m n))
                      (absurd (divides n m)
                         (mod_O_to_divides n m posn
                            (rewrite_l nat O (fun __ : nat => eq nat __ O)
                               (refl nat O) (mod m n) modO)) ndivnm))
                   (le_to_or_lt_eq O (mod m n) (le_O_n (mod m n))))
                (lt_to_le (mod m n) n (lt_mod_m_m m n posn))
                (le_S_S_to_le (mod m n) q
                   (transitive_le (S (mod m n)) n 
                      (S q) (lt_mod_m_m m n posn) lenS))))
          (gcd_aux (S q) m n) (not_divides_to_gcd_aux q m n posn ndivnm))
       (decidable_divides n m)) p.
Definition let_clause_1549 :
  forall m n : nat,
  lt O n -> eq nat O m -> forall x1106 : nat, eq nat x1106 (minus x1106 m) :=
  fun (m n : nat) (posn : lt O n) (eqm0 : eq nat O m) (x1106 : nat) =>
  rewrite_l nat O (fun __ : nat => eq nat x1106 (minus x1106 __))
    (minus_n_O x1106) m eqm0.
Definition let_clause_15491 :
  forall m n : nat,
  eq nat O n -> forall x1106 : nat, eq nat x1106 (minus x1106 n) :=
  fun (m n : nat) (eqn0 : eq nat O n) (x1106 : nat) =>
  rewrite_l nat O (fun __ : nat => eq nat x1106 (minus x1106 __))
    (minus_n_O x1106) n eqn0.
Definition let_clause_1551 :
  forall m n : nat, eq nat O n -> forall x347 : nat, eq nat n (times x347 n) :=
  fun (m n : nat) (eqn0 : eq nat O n) (x347 : nat) =>
  rewrite_l nat O (fun __ : nat => eq nat n (times x347 __))
    (rewrite_l nat O (fun __ : nat => eq nat __ (times x347 O))
       (times_n_O x347) n eqn0) n eqn0.
Definition eq_minus_gcd :
  forall m n : nat,
  Ex nat
    (fun a : nat =>
     Ex nat
       (fun b : nat =>
        Or (eq nat (minus (times a n) (times b m)) (gcd n m))
          (eq nat (minus (times b m) (times a n)) (gcd n m)))) :=
  fun m n : nat =>
  match_Or_prop (lt O n) (eq nat O n)
    (Ex nat
       (fun a : nat =>
        Ex nat
          (fun b : nat =>
           Or (eq nat (minus (times a n) (times b m)) (gcd n m))
             (eq nat (minus (times b m) (times a n)) (gcd n m)))))
    (fun posn : lt O n =>
     match_Or_prop (lt O m) (eq nat O m)
       (Ex nat
          (fun a : nat =>
           Ex nat
             (fun b : nat =>
              Or (eq nat (minus (times a n) (times b m)) (gcd n m))
                (eq nat (minus (times b m) (times a n)) (gcd n m)))))
       (fun posm : lt O m =>
        leb_elim n m
          (fun __ : bool =>
           Ex nat
             (fun a : nat =>
              Ex nat
                (fun b : nat =>
                 Or
                   (eq nat (minus (times a n) (times b m))
                      (match_bool_type nat (gcd_aux n m n) (gcd_aux m n m) __))
                   (eq nat (minus (times b m) (times a n))
                      (match_bool_type nat (gcd_aux n m n) (gcd_aux m n m) __)))))
          (sym_eq_match_bool_type_true nat (gcd_aux n m n) 
             (gcd_aux m n m)
             (fun y : nat =>
              le n m ->
              Ex nat
                (fun a : nat =>
                 Ex nat
                   (fun b : nat =>
                    Or
                      (eq nat (minus (times a n) (times b m))
                         (match_bool_type nat (gcd_aux n m n) 
                            (gcd_aux m n m) true))
                      (eq nat (minus (times b m) (times a n)) y))))
             (sym_eq_match_bool_type_true nat (gcd_aux n m n) 
                (gcd_aux m n m)
                (fun y : nat =>
                 le n m ->
                 Ex nat
                   (fun a : nat =>
                    Ex nat
                      (fun b : nat =>
                       Or (eq nat (minus (times a n) (times b m)) y)
                         (eq nat (minus (times b m) (times a n))
                            (gcd_aux n m n)))))
                (fun lenm : le n m =>
                 eq_minus_gcd_aux n m n posn lenm (le_n n))))
          (sym_eq_match_bool_type_false nat (gcd_aux n m n) 
             (gcd_aux m n m)
             (fun y : nat =>
              Not (le n m) ->
              Ex nat
                (fun a : nat =>
                 Ex nat
                   (fun b : nat =>
                    Or
                      (eq nat (minus (times a n) (times b m))
                         (match_bool_type nat (gcd_aux n m n) 
                            (gcd_aux m n m) false))
                      (eq nat (minus (times b m) (times a n)) y))))
             (sym_eq_match_bool_type_false nat (gcd_aux n m n)
                (gcd_aux m n m)
                (fun y : nat =>
                 Not (le n m) ->
                 Ex nat
                   (fun a : nat =>
                    Ex nat
                      (fun b : nat =>
                       Or (eq nat (minus (times a n) (times b m)) y)
                         (eq nat (minus (times b m) (times a n))
                            (gcd_aux m n m)))))
                (fun nlenm : Not (le n m) =>
                 match_ex_prop nat
                   (fun a : nat =>
                    Ex nat
                      (fun b : nat =>
                       Or
                         (eq nat (minus (times a m) (times b n))
                            (gcd_aux m n m))
                         (eq nat (minus (times b n) (times a m))
                            (gcd_aux m n m))))
                   (Ex nat
                      (fun a : nat =>
                       Ex nat
                         (fun b : nat =>
                          Or
                            (eq nat (minus (times a n) (times b m))
                               (gcd_aux m n m))
                            (eq nat (minus (times b m) (times a n))
                               (gcd_aux m n m)))))
                   (fun (a : nat)
                      (_clearme : Ex nat
                                    (fun b : nat =>
                                     Or
                                       (eq nat
                                          (minus (times a m) (times b n))
                                          (gcd_aux m n m))
                                       (eq nat
                                          (minus (times b n) (times a m))
                                          (gcd_aux m n m)))) =>
                    match_ex_prop nat
                      (fun b : nat =>
                       Or
                         (eq nat (minus (times a m) (times b n))
                            (gcd_aux m n m))
                         (eq nat (minus (times b n) (times a m))
                            (gcd_aux m n m)))
                      (Ex nat
                         (fun a0 : nat =>
                          Ex nat
                            (fun b : nat =>
                             Or
                               (eq nat (minus (times a0 n) (times b m))
                                  (gcd_aux m n m))
                               (eq nat (minus (times b m) (times a0 n))
                                  (gcd_aux m n m)))))
                      (fun (b : nat)
                         (_clearme0 : Or
                                        (eq nat
                                           (minus (times a m) (times b n))
                                           (gcd_aux m n m))
                                        (eq nat
                                           (minus (times b n) (times a m))
                                           (gcd_aux m n m))) =>
                       match_Or_prop
                         (eq nat (minus (times a m) (times b n))
                            (gcd_aux m n m))
                         (eq nat (minus (times b n) (times a m))
                            (gcd_aux m n m))
                         (Ex nat
                            (fun a0 : nat =>
                             Ex nat
                               (fun b0 : nat =>
                                Or
                                  (eq nat (minus (times a0 n) (times b0 m))
                                     (gcd_aux m n m))
                                  (eq nat (minus (times b0 m) (times a0 n))
                                     (gcd_aux m n m)))))
                         (fun
                            (H : eq nat (minus (times a m) (times b n))
                                   (gcd_aux m n m)) 
                            (z : Prop)
                            (f : forall x : nat,
                                 Ex nat
                                   (fun b0 : nat =>
                                    Or
                                      (eq nat
                                         (minus (times x n) (times b0 m))
                                         (gcd_aux m n m))
                                      (eq nat
                                         (minus (times b0 m) (times x n))
                                         (gcd_aux m n m))) -> z) =>
                          f b
                            (fun (z0 : Prop)
                               (f2 : forall x : nat,
                                     Or
                                       (eq nat
                                          (minus (times b n) (times x m))
                                          (gcd_aux m n m))
                                       (eq nat
                                          (minus (times x m) (times b n))
                                          (gcd_aux m n m)) -> z0) =>
                             f2 a
                               (fun (z1 : Prop)
                                  (l : eq nat (minus (times b n) (times a m))
                                         (gcd_aux m n m) -> z1)
                                  (r : eq nat (minus (times a m) (times b n))
                                         (gcd_aux m n m) -> z1) =>
                                r
                                  (rewrite_r nat (times m a)
                                     (fun __ : nat =>
                                      eq nat (minus __ (times b n))
                                        (gcd_aux m n m))
                                     (rewrite_r nat 
                                        (times n b)
                                        (fun __ : nat =>
                                         eq nat (minus (times m a) __)
                                           (gcd_aux m n m))
                                        (rewrite_r nat 
                                           (gcd_aux m n m)
                                           (fun __ : nat =>
                                            eq nat __ (gcd_aux m n m))
                                           (refl nat (gcd_aux m n m))
                                           (minus (times m a) (times n b))
                                           (rewrite_l nat 
                                              (times b n)
                                              (fun __ : nat =>
                                               eq nat 
                                                 (minus (times m a) __)
                                                 (gcd_aux m n m))
                                              (rewrite_l nat 
                                                 (times a m)
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (minus __ (times b n))
                                                 (gcd_aux m n m)) H
                                                 (times m a)
                                                 (commutative_times a m))
                                              (times n b)
                                              (commutative_times b n)))
                                        (times b n) 
                                        (commutative_times b n)) 
                                     (times a m) (commutative_times a m)))))
                         (fun
                            (H : eq nat (minus (times b n) (times a m))
                                   (gcd_aux m n m)) 
                            (z : Prop)
                            (f : forall y : nat,
                                 Ex nat
                                   (fun b0 : nat =>
                                    Or
                                      (eq nat
                                         (minus (times y n) (times b0 m))
                                         (gcd_aux m n m))
                                      (eq nat
                                         (minus (times b0 m) (times y n))
                                         (gcd_aux m n m))) -> z) =>
                          f b
                            (fun (z0 : Prop)
                               (f2 : forall x : nat,
                                     Or
                                       (eq nat
                                          (minus (times b n) (times x m))
                                          (gcd_aux m n m))
                                       (eq nat
                                          (minus (times x m) (times b n))
                                          (gcd_aux m n m)) -> z0) =>
                             f2 a
                               (fun (z1 : Prop)
                                  (l : eq nat (minus (times b n) (times a m))
                                         (gcd_aux m n m) -> z1)
                                  (r : eq nat (minus (times a m) (times b n))
                                         (gcd_aux m n m) -> z1) =>
                                l
                                  (rewrite_r nat (times n b)
                                     (fun __ : nat =>
                                      eq nat (minus __ (times a m))
                                        (gcd_aux m n m))
                                     (rewrite_r nat 
                                        (times m a)
                                        (fun __ : nat =>
                                         eq nat (minus (times n b) __)
                                           (gcd_aux m n m))
                                        (rewrite_r nat 
                                           (gcd_aux m n m)
                                           (fun __ : nat =>
                                            eq nat __ (gcd_aux m n m))
                                           (refl nat (gcd_aux m n m))
                                           (minus (times n b) (times m a))
                                           (rewrite_l nat 
                                              (times a m)
                                              (fun __ : nat =>
                                               eq nat 
                                                 (minus (times n b) __)
                                                 (gcd_aux m n m))
                                              (rewrite_l nat 
                                                 (times b n)
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (minus __ (times a m))
                                                 (gcd_aux m n m)) H
                                                 (times n b)
                                                 (commutative_times b n))
                                              (times m a)
                                              (commutative_times a m)))
                                        (times a m) 
                                        (commutative_times a m)) 
                                     (times b n) (commutative_times b n)))))
                         _clearme0) _clearme)
                   (eq_minus_gcd_aux m n m posm
                      (transitive_le m (S m) n (le_n_Sn m)
                         (not_le_to_lt n m nlenm)) 
                      (le_n m))))))
       (fun eqm0 : eq nat O m =>
        eq_ind_r nat m
          (fun x : nat =>
           Ex nat
             (fun a : nat =>
              Ex nat
                (fun b : nat =>
                 Or (eq nat (minus (times a n) (times b m)) (gcd n m))
                   (eq nat (minus (times b m) (times a n)) (gcd n m)))))
          (fun (z : Prop)
             (f : forall x : nat,
                  Ex nat
                    (fun b : nat =>
                     Or (eq nat (minus (times x n) (times b m)) (gcd n m))
                       (eq nat (minus (times b m) (times x n)) (gcd n m))) ->
                  z) =>
           f (S O)
             (fun (z0 : Prop)
                (f2 : forall y : nat,
                      Or
                        (eq nat (minus (times (S O) n) (times y m)) (gcd n m))
                        (eq nat (minus (times y m) (times (S O) n)) (gcd n m)) ->
                      z0) =>
              f2 O
                (fun (z1 : Prop)
                   (l : eq nat (minus (times (S O) n) (times O m)) (gcd n m) ->
                        z1)
                   (r : eq nat (minus (times O m) (times (S O) n)) (gcd n m) ->
                        z1) =>
                 l
                   (eq_coerc (eq nat n (minus n O))
                      (eq nat (minus (times (S O) n) (times O m)) (gcd n m))
                      (minus_n_O n)
                      (rewrite_r nat m
                         (fun __ : nat =>
                          eq Prop (eq nat n (minus n __))
                            (eq nat (minus (times (S O) n) (times O m))
                               (gcd n m)))
                         (rewrite_l nat n
                            (fun __ : nat =>
                             eq Prop (eq nat n __)
                               (eq nat (minus (times (S O) n) (times O m))
                                  (gcd n m)))
                            (rewrite_r nat m
                               (fun __ : nat =>
                                eq Prop (eq nat n n)
                                  (eq nat
                                     (minus (times (S __) n) (times O m))
                                     (gcd n m)))
                               (rewrite_r nat (times n (S m))
                                  (fun __ : nat =>
                                   eq Prop (eq nat n n)
                                     (eq nat (minus __ (times O m)) (gcd n m)))
                                  (rewrite_l nat (plus n (times n m))
                                     (fun __ : nat =>
                                      eq Prop (eq nat n n)
                                        (eq nat (minus __ (times O m))
                                           (gcd n m)))
                                     (rewrite_r nat 
                                        (times m n)
                                        (fun __ : nat =>
                                         eq Prop (eq nat n n)
                                           (eq nat
                                              (minus (plus n __) (times O m))
                                              (gcd n m)))
                                        (rewrite_l nat m
                                           (fun __ : nat =>
                                            eq Prop 
                                              (eq nat n n)
                                              (eq nat
                                                 (minus 
                                                 (plus n __) 
                                                 (times O m)) 
                                                 (gcd n m)))
                                           (rewrite_r nat 
                                              (plus m n)
                                              (fun __ : nat =>
                                               eq Prop 
                                                 (eq nat n n)
                                                 (eq nat
                                                 (minus __ (times O m))
                                                 (gcd n m)))
                                              (rewrite_l nat n
                                                 (fun __ : nat =>
                                                 eq Prop 
                                                 (eq nat n n)
                                                 (eq nat
                                                 (minus __ (times O m))
                                                 (gcd n m)))
                                                 (rewrite_r nat m
                                                 (fun __ : nat =>
                                                 eq Prop 
                                                 (eq nat n n)
                                                 (eq nat
                                                 (minus n (times __ m))
                                                 (gcd n m)))
                                                 (rewrite_l nat m
                                                 (fun __ : nat =>
                                                 eq Prop 
                                                 (eq nat n n)
                                                 (eq nat 
                                                 (minus n __) 
                                                 (gcd n m)))
                                                 (rewrite_l nat n
                                                 (fun __ : nat =>
                                                 eq Prop 
                                                 (eq nat n n)
                                                 (eq nat __ (gcd n m)))
                                                 (rewrite_r nat 
                                                 (gcd m n)
                                                 (fun __ : nat =>
                                                 eq Prop 
                                                 (eq nat n n) 
                                                 (eq nat n __))
                                                 (rewrite_r nat n
                                                 (fun __ : nat =>
                                                 eq Prop 
                                                 (eq nat n n) 
                                                 (eq nat n __))
                                                 (refl Prop (eq nat n n))
                                                 (gcd m n)
                                                 (rewrite_l nat O
                                                 (fun __ : nat =>
                                                 eq nat (gcd __ n) n)
                                                 (gcd_O_l n) m eqm0))
                                                 (gcd n m)
                                                 (commutative_gcd n m))
                                                 (minus n m)
                                                 (let_clause_1549 m n posn
                                                 eqm0 n)) 
                                                 (times m m)
                                                 (rewrite_l nat O
                                                 (fun __ : nat =>
                                                 eq nat m (times m __))
                                                 (rewrite_l nat O
                                                 (fun __ : nat =>
                                                 eq nat __ (times m O))
                                                 (times_n_O m) m eqm0) m eqm0))
                                                 O eqm0) 
                                                 (plus m n)
                                                 (rewrite_l nat O
                                                 (fun __ : nat =>
                                                 eq nat n (plus __ n))
                                                 (plus_O_n n) m eqm0))
                                              (plus n m)
                                              (commutative_plus n m))
                                           (times m n)
                                           (rewrite_l nat O
                                              (fun __ : nat =>
                                               eq nat m (times __ n))
                                              (rewrite_l nat O
                                                 (fun __ : nat =>
                                                 eq nat __ (times O n))
                                                 (times_O_n n) m eqm0) m eqm0))
                                        (times n m) 
                                        (commutative_times n m))
                                     (times n (S m)) 
                                     (times_n_Sm n m)) 
                                  (times (S m) n) 
                                  (commutative_times (S m) n)) O eqm0)
                            (minus n m) (let_clause_1549 m n posn eqm0 n)) O
                         eqm0))))) O eqm0) (le_to_or_lt_eq O m (le_O_n m)))
    (fun eqn0 : eq nat O n =>
     eq_ind_r nat n
       (fun x : nat =>
        Ex nat
          (fun a : nat =>
           Ex nat
             (fun b : nat =>
              Or (eq nat (minus (times a n) (times b m)) (gcd n m))
                (eq nat (minus (times b m) (times a n)) (gcd n m)))))
       (fun (z : Prop)
          (f : forall x : nat,
               Ex nat
                 (fun b : nat =>
                  Or (eq nat (minus (times x n) (times b m)) (gcd n m))
                    (eq nat (minus (times b m) (times x n)) (gcd n m))) -> z)
        =>
        f O
          (fun (z0 : Prop)
             (f0 : forall x : nat,
                   Or (eq nat (minus (times O n) (times x m)) (gcd n m))
                     (eq nat (minus (times x m) (times O n)) (gcd n m)) -> z0)
           =>
           f0 (S O)
             (fun (z1 : Prop)
                (l : eq nat (minus (times O n) (times (S O) m)) (gcd n m) ->
                     z1)
                (r : eq nat (minus (times (S O) m) (times O n)) (gcd n m) ->
                     z1) =>
              r
                (eq_coerc (eq nat m (minus m O))
                   (eq nat (minus (times (S O) m) (times O n)) (gcd n m))
                   (minus_n_O m)
                   (rewrite_r nat m
                      (fun __ : nat =>
                       eq Prop (eq nat m (minus m O))
                         (eq nat (minus (times (S O) m) (times O n)) __))
                      (rewrite_r nat n
                         (fun __ : nat =>
                          eq Prop (eq nat m (minus m __))
                            (eq nat (minus (times (S O) m) (times O n)) m))
                         (rewrite_l nat m
                            (fun __ : nat =>
                             eq Prop (eq nat m __)
                               (eq nat (minus (times (S O) m) (times O n)) m))
                            (rewrite_r nat n
                               (fun __ : nat =>
                                eq Prop (eq nat m m)
                                  (eq nat
                                     (minus (times (S __) m) (times O n)) m))
                               (rewrite_r nat (times m (S n))
                                  (fun __ : nat =>
                                   eq Prop (eq nat m m)
                                     (eq nat (minus __ (times O n)) m))
                                  (rewrite_l nat (plus m (times m n))
                                     (fun __ : nat =>
                                      eq Prop (eq nat m m)
                                        (eq nat (minus __ (times O n)) m))
                                     (rewrite_l nat n
                                        (fun __ : nat =>
                                         eq Prop (eq nat m m)
                                           (eq nat
                                              (minus (plus m __) (times O n))
                                              m))
                                        (rewrite_l nat m
                                           (fun __ : nat =>
                                            eq Prop 
                                              (eq nat m m)
                                              (eq nat 
                                                 (minus __ (times O n)) m))
                                           (rewrite_r nat n
                                              (fun __ : nat =>
                                               eq Prop 
                                                 (eq nat m m)
                                                 (eq nat
                                                 (minus m (times __ n)) m))
                                              (rewrite_l nat n
                                                 (fun __ : nat =>
                                                 eq Prop 
                                                 (eq nat m m)
                                                 (eq nat (minus m __) m))
                                                 (rewrite_l nat m
                                                 (fun __ : nat =>
                                                 eq Prop 
                                                 (eq nat m m) 
                                                 (eq nat __ m))
                                                 (refl Prop (eq nat m m))
                                                 (minus m n)
                                                 (let_clause_15491 m n eqn0 m))
                                                 (times n n)
                                                 (let_clause_1551 m n eqn0 n))
                                              O eqn0) 
                                           (plus m n)
                                           (rewrite_l nat O
                                              (fun __ : nat =>
                                               eq nat m (plus m __))
                                              (plus_n_O m) n eqn0))
                                        (times m n)
                                        (let_clause_1551 m n eqn0 m))
                                     (times m (S n)) 
                                     (times_n_Sm m n)) 
                                  (times (S n) m) 
                                  (commutative_times (S n) m)) O eqn0)
                            (minus m n) (let_clause_15491 m n eqn0 m)) O eqn0)
                      (gcd n m)
                      (rewrite_l nat O (fun __ : nat => eq nat (gcd __ m) m)
                         (gcd_O_l m) n eqn0)))))) O eqn0)
    (le_to_or_lt_eq O n (le_O_n n)).
Definition let_clause_1545 :
  forall m n : nat,
  eq nat (gcd m n) O ->
  divides O n ->
  forall q1 : nat,
  eq nat n (times O q1) ->
  divides O m -> forall q2 : nat, eq nat m (times O q2) -> eq nat m O :=
  fun (m n : nat) (H : eq nat (gcd m n) O) (_clearme : divides O n)
    (q1 : nat) (H1 : eq nat n (times O q1)) (_clearme0 : divides O m)
    (q2 : nat) (H2 : eq nat m (times O q2)) =>
  rewrite_r nat (times q2 O) (fun __ : nat => eq nat m __)
    (rewrite_l nat (times O q2) (fun __ : nat => eq nat m __) H2 
       (times q2 O) (commutative_times O q2)) O (times_n_O q2).
Definition gcd_O_to_eq_O :
  forall m n : nat, eq nat (gcd m n) O -> And (eq nat m O) (eq nat n O) :=
  fun (m n : nat) (H : eq nat (gcd m n) O) =>
  match_And_prop (divides O n) (divides O m) (And (eq nat m O) (eq nat n O))
    (fun _clearme : divides O n =>
     match_divides_prop O n (divides O m -> And (eq nat m O) (eq nat n O))
       (fun (q1 : nat) (H1 : eq nat n (times O q1)) (_clearme0 : divides O m)
        =>
        match_divides_prop O m (And (eq nat m O) (eq nat n O))
          (fun (q2 : nat) (H2 : eq nat m (times O q2)) 
             (z : Prop) (f : eq nat m O -> eq nat n O -> z) =>
           f
             (rewrite_l nat m (fun __ : nat => eq nat m __) 
                (refl nat m) O
                (rewrite_r nat (times q2 O) (fun __ : nat => eq nat m __)
                   (rewrite_l nat (times O q2) (fun __ : nat => eq nat m __)
                      H2 (times q2 O) (commutative_times O q2)) O
                   (times_n_O q2)))
             (rewrite_r nat m (fun __ : nat => eq nat __ O)
                (rewrite_l nat m (fun __ : nat => eq nat m __) 
                   (refl nat m) O
                   (let_clause_1545 m n H _clearme q1 H1 _clearme0 q2 H2)) n
                (rewrite_r nat (times m q1) (fun __ : nat => eq nat n __)
                   (rewrite_r nat O (fun __ : nat => eq nat n (times __ q1))
                      H1 m
                      (let_clause_1545 m n H _clearme q1 H1 _clearme0 q2 H2))
                   m
                   (rewrite_r nat O (fun __ : nat => eq nat m (times __ q1))
                      (rewrite_r nat O
                         (fun __ : nat => eq nat __ (times O q1))
                         (times_O_n q1) m
                         (let_clause_1545 m n H _clearme q1 H1 _clearme0 q2
                            H2)) m
                      (let_clause_1545 m n H _clearme q1 H1 _clearme0 q2 H2)))))
          _clearme0) _clearme)
    (eq_ind nat (gcd m n)
       (fun x_1 : nat => And (divides x_1 n) (divides x_1 m))
       (divides_gcd_nm m n) O H).
Definition let_clause_1571 :
  forall m n : nat,
  lt O n -> eq nat (gcd m n) O -> eq nat m O -> eq nat n O -> eq nat m n :=
  fun (m n : nat) (posn : lt O n) (H : eq nat (gcd m n) O)
    (auto : eq nat m O) (auto' : eq nat n O) =>
  rewrite_r nat O (fun __ : nat => eq nat m __) auto n auto'.
Definition let_clause_1572 :
  forall m n : nat,
  lt O n -> eq nat (gcd m n) O -> eq nat m O -> eq nat n O -> eq nat m O :=
  fun (m n : nat) (posn : lt O n) (H : eq nat (gcd m n) O)
    (auto : eq nat m O) (auto' : eq nat n O) =>
  rewrite_r nat n (fun __ : nat => eq nat __ O) auto' m
    (let_clause_1571 m n posn H auto auto').
Definition lt_O_gcd : forall m n : nat, lt O n -> lt O (gcd m n) :=
  fun (m n : nat) (posn : lt O n) =>
  nat_case (gcd m n) (lt O)
    (fun H : eq nat (gcd m n) O =>
     match_And_prop (eq nat m O) (eq nat n O) (lt O O)
       (fun (auto : eq nat m O) (auto' : eq nat n O) =>
        eq_coerc (lt O n) (lt O O) posn
          (rewrite_l nat m (fun __ : nat => eq Prop (lt __ n) (lt O O))
             (rewrite_l nat m (fun __ : nat => eq Prop (lt m __) (lt O O))
                (rewrite_l nat m (fun __ : nat => eq Prop (lt m m) (lt __ O))
                   (rewrite_l nat m
                      (fun __ : nat => eq Prop (lt m m) (lt m __))
                      (refl Prop (lt m m)) O
                      (let_clause_1572 m n posn H auto auto')) O
                   (let_clause_1572 m n posn H auto auto')) n
                (let_clause_1571 m n posn H auto auto')) O
             (let_clause_1572 m n posn H auto auto'))) 
       (gcd_O_to_eq_O m n H))
    (fun (m0 : nat) (auto : eq nat (gcd m n) (S m0)) => lt_O_S m0).
Definition prime_to_gcd_1 :
  forall n m : nat, prime n -> Not (divides n m) -> eq nat (gcd n m) (S O) :=
  fun (n m : nat) (_clearme : prime n) =>
  match_And_prop (lt (S O) n)
    (forall m1 : nat, divides m1 n -> lt (S O) m1 -> eq nat m1 n)
    (Not (divides n m) -> eq nat (gcd n m) (S O))
    (fun (lt1n : lt (S O) n)
       (primen : forall m0 : nat, divides m0 n -> lt (S O) m0 -> eq nat m0 n)
       (ndivnm : Not (divides n m)) =>
     le_to_le_to_eq (gcd n m) (S O)
       (not_lt_to_le (S O) (gcd n m)
          (not_to_not (lt (S O) (gcd n m)) (eq nat (gcd n m) n)
             (primen (gcd n m) (divides_gcd_l n m))
             (not_to_not (eq nat (gcd n m) n) (divides n m)
                (fun auto : eq nat (gcd n m) n =>
                 eq_coerc (divides (gcd n m) m) (divides n m)
                   (divides_gcd_r n m)
                   (rewrite_r nat n
                      (fun __ : nat => eq Prop (divides __ m) (divides n m))
                      (refl Prop (divides n m)) (gcd n m) auto)) ndivnm)))
       (lt_O_gcd n m
          (not_eq_to_le_to_lt O m
             (not_to_not (eq nat O m) (divides n m)
                (fun auto : eq nat O m =>
                 eq_coerc (divides n O) (divides n m) 
                   (divides_n_O n)
                   (rewrite_r nat m
                      (fun __ : nat => eq Prop (divides n __) (divides n m))
                      (refl Prop (divides n m)) O auto)) ndivnm) 
             (le_O_n m)))) _clearme.
Definition divides_times_to_divides :
  forall p n m : nat,
  prime p -> divides p (times n m) -> Or (divides p n) (divides p m) :=
  fun (p n m : nat) (primp : prime p) (_clearme : divides p (times n m)) =>
  match_divides_prop p (times n m) (Or (divides p n) (divides p m))
    (fun (c : nat) (nm : eq nat (times n m) (times p c)) =>
     match_Or_prop (divides p n) (Not (divides p n))
       (Or (divides p n) (divides p m))
       (fun (auto : divides p n) (z : Prop) (l : divides p n -> z)
          (r : divides p m -> z) => l auto)
       (fun (ndivpn : Not (divides p n)) (z : Prop) 
          (l : divides p n -> z) (r : divides p m -> z) =>
        r
          (match_ex_prop nat
             (fun a : nat =>
              Ex nat
                (fun b : nat =>
                 Or (eq nat (minus (times a n) (times b p)) (S O))
                   (eq nat (minus (times b p) (times a n)) (S O))))
             (divides p m)
             (fun (a : nat)
                (_clearme0 : Ex nat
                               (fun b : nat =>
                                Or
                                  (eq nat (minus (times a n) (times b p))
                                     (S O))
                                  (eq nat (minus (times b p) (times a n))
                                     (S O)))) =>
              match_ex_prop nat
                (fun b : nat =>
                 Or (eq nat (minus (times a n) (times b p)) (S O))
                   (eq nat (minus (times b p) (times a n)) (S O)))
                (divides p m)
                (fun (b : nat)
                   (_clearme1 : Or
                                  (eq nat (minus (times a n) (times b p))
                                     (S O))
                                  (eq nat (minus (times b p) (times a n))
                                     (S O))) =>
                 match_Or_prop (eq nat (minus (times a n) (times b p)) (S O))
                   (eq nat (minus (times b p) (times a n)) (S O))
                   (divides p m)
                   (fun H : eq nat (minus (times a n) (times b p)) (S O) =>
                    quotient p m (minus (times a c) (times b m))
                      (eq_ind_r nat
                         (minus (times p (times a c)) (times p (times b m)))
                         (fun x : nat => eq nat m x)
                         (eq_ind nat (times (times p a) c)
                            (fun x_1 : nat =>
                             eq nat m (minus x_1 (times p (times b m))))
                            (eq_ind_r nat (times a p)
                               (fun x : nat =>
                                eq nat m
                                  (minus (times x c) (times p (times b m))))
                               (eq_ind_r nat (times a (times p c))
                                  (fun x : nat =>
                                   eq nat m (minus x (times p (times b m))))
                                  (eq_ind nat (times n m)
                                     (fun x_1 : nat =>
                                      eq nat m
                                        (minus (times a x_1)
                                           (times p (times b m))))
                                     (eq_ind nat (times (times a n) m)
                                        (fun x_1 : nat =>
                                         eq nat m
                                           (minus x_1 (times p (times b m))))
                                        (eq_ind nat 
                                           (times (times p b) m)
                                           (fun x_1 : nat =>
                                            eq nat m
                                              (minus 
                                                 (times (times a n) m) x_1))
                                           (eq_ind nat 
                                              (times m (times a n))
                                              (fun x_1 : nat =>
                                               eq nat m
                                                 (minus x_1
                                                 (times (times p b) m)))
                                              (eq_ind_r nat
                                                 (times m (times p b))
                                                 (fun x : nat =>
                                                 eq nat m
                                                 (minus 
                                                 (times m (times a n)) x))
                                                 (eq_ind nat
                                                 (times m
                                                 (minus 
                                                 (times a n) 
                                                 (times p b)))
                                                 (fun x_1 : nat =>
                                                 eq nat m x_1)
                                                 (rewrite_r nat 
                                                 (times n a)
                                                 (fun __ : nat =>
                                                 eq nat m
                                                 (times m
                                                 (minus __ (times p b))))
                                                 (rewrite_l nat m
                                                 (fun __ : nat => eq nat m __)
                                                 (refl nat m)
                                                 (times m
                                                 (minus 
                                                 (times n a) 
                                                 (times p b)))
                                                 (rewrite_r nat 
                                                 (S O)
                                                 (fun __ : nat =>
                                                 eq nat m (times m __))
                                                 (times_n_1 m)
                                                 (minus 
                                                 (times n a) 
                                                 (times p b))
                                                 (rewrite_l nat 
                                                 (times b p)
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (minus (times n a) __) 
                                                 (S O))
                                                 (rewrite_l nat 
                                                 (times a n)
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (minus __ (times b p)) 
                                                 (S O)) H 
                                                 (times n a)
                                                 (commutative_times a n))
                                                 (times p b)
                                                 (commutative_times b p))))
                                                 (times a n)
                                                 (commutative_times a n))
                                                 (minus 
                                                 (times m (times a n))
                                                 (times m (times p b)))
                                                 (distributive_times_minus m
                                                 (times a n) 
                                                 (times p b)))
                                                 (times (times p b) m)
                                                 (commutative_times
                                                 (times p b) m))
                                              (times (times a n) m)
                                              (commutative_times m
                                                 (times a n)))
                                           (times p (times b m))
                                           (associative_times p b m))
                                        (times a (times n m))
                                        (associative_times a n m))
                                     (times p c) nm) 
                                  (times (times a p) c)
                                  (associative_times a p c)) 
                               (times p a) (commutative_times p a))
                            (times p (times a c)) 
                            (associative_times p a c))
                         (times p (minus (times a c) (times b m)))
                         (distributive_times_minus p (times a c) (times b m))))
                   (fun H : eq nat (minus (times b p) (times a n)) (S O) =>
                    quotient p m (minus (times b m) (times a c))
                      (eq_ind_r nat
                         (minus (times p (times b m)) (times p (times a c)))
                         (fun x : nat => eq nat m x)
                         (eq_ind nat (times (times p b) m)
                            (fun x_1 : nat =>
                             eq nat m (minus x_1 (times p (times a c))))
                            (eq_ind nat (times (times p a) c)
                               (fun x_1 : nat =>
                                eq nat m (minus (times (times p b) m) x_1))
                               (eq_ind nat (times a p)
                                  (fun x_1 : nat =>
                                   eq nat m
                                     (minus (times (times p b) m)
                                        (times x_1 c)))
                                  (eq_ind_r nat (times a (times p c))
                                     (fun x : nat =>
                                      eq nat m
                                        (minus (times (times p b) m) x))
                                     (eq_ind nat (times n m)
                                        (fun x_1 : nat =>
                                         eq nat m
                                           (minus 
                                              (times (times p b) m)
                                              (times a x_1)))
                                        (eq_ind nat 
                                           (times (times a n) m)
                                           (fun x_1 : nat =>
                                            eq nat m
                                              (minus 
                                                 (times (times p b) m) x_1))
                                           (eq_ind nat 
                                              (times m (times p b))
                                              (fun x_1 : nat =>
                                               eq nat m
                                                 (minus x_1
                                                 (times (times a n) m)))
                                              (eq_ind_r nat
                                                 (times m (times a n))
                                                 (fun x : nat =>
                                                 eq nat m
                                                 (minus 
                                                 (times m (times p b)) x))
                                                 (eq_ind nat
                                                 (times m
                                                 (minus 
                                                 (times p b) 
                                                 (times a n)))
                                                 (fun x_1 : nat =>
                                                 eq nat m x_1)
                                                 (rewrite_r nat 
                                                 (times n a)
                                                 (fun __ : nat =>
                                                 eq nat m
                                                 (times m
                                                 (minus (times p b) __)))
                                                 (rewrite_l nat m
                                                 (fun __ : nat => eq nat m __)
                                                 (refl nat m)
                                                 (times m
                                                 (minus 
                                                 (times p b) 
                                                 (times n a)))
                                                 (rewrite_r nat 
                                                 (S O)
                                                 (fun __ : nat =>
                                                 eq nat m (times m __))
                                                 (times_n_1 m)
                                                 (minus 
                                                 (times p b) 
                                                 (times n a))
                                                 (rewrite_l nat 
                                                 (times a n)
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (minus (times p b) __) 
                                                 (S O))
                                                 (rewrite_l nat 
                                                 (times b p)
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (minus __ (times a n)) 
                                                 (S O)) H 
                                                 (times p b)
                                                 (commutative_times b p))
                                                 (times n a)
                                                 (commutative_times a n))))
                                                 (times a n)
                                                 (commutative_times a n))
                                                 (minus 
                                                 (times m (times p b))
                                                 (times m (times a n)))
                                                 (distributive_times_minus m
                                                 (times p b) 
                                                 (times a n)))
                                                 (times (times a n) m)
                                                 (commutative_times
                                                 (times a n) m))
                                              (times (times p b) m)
                                              (commutative_times m
                                                 (times p b)))
                                           (times a (times n m))
                                           (associative_times a n m))
                                        (times p c) nm) 
                                     (times (times a p) c)
                                     (associative_times a p c)) 
                                  (times p a) (commutative_times a p))
                               (times p (times a c))
                               (associative_times p a c))
                            (times p (times b m)) 
                            (associative_times p b m))
                         (times p (minus (times b m) (times a c)))
                         (distributive_times_minus p (times b m) (times a c))))
                   _clearme1) _clearme0)
             (eq_ind nat (gcd p n)
                (fun x_1 : nat =>
                 Ex nat
                   (fun a : nat =>
                    Ex nat
                      (fun b : nat =>
                       Or (eq nat (minus (times a n) (times b p)) x_1)
                         (eq nat (minus (times b p) (times a n)) x_1))))
                (eq_ind_r nat (gcd n p)
                   (fun x : nat =>
                    Ex nat
                      (fun a : nat =>
                       Ex nat
                         (fun b : nat =>
                          Or (eq nat (minus (times a n) (times b p)) x)
                            (eq nat (minus (times b p) (times a n)) x))))
                   (eq_minus_gcd p n) (gcd p n) (commutative_gcd p n)) 
                (S O) (prime_to_gcd_1 p n primp ndivpn))))
       (decidable_divides p n)) _clearme.
Definition congruent : nat -> nat -> nat -> Prop :=
  fun n m p : nat => eq nat (mod n p) (mod m p).
Definition congruent_n_n : forall n p : nat, congruent n n p :=
  fun n p : nat => refl nat (mod n p).
Definition transitive_congruent :
  forall p : nat, transitive nat (fun n m : nat => congruent n m p) :=
  fun (p x y z : nat) (auto : congruent x y p) (auto' : congruent y z p) =>
  rewrite_l nat (mod x p) (fun __ : nat => eq nat (mod x p) __)
    (refl nat (mod x p)) (mod z p)
    (rewrite_r nat (mod y p) (fun __ : nat => eq nat __ (mod z p)) auto'
       (mod x p) auto).
Definition mod_mod :
  forall n p : nat, lt O p -> eq nat (mod n p) (mod (mod n p) p) :=
  fun (n p : nat) (posp : lt O p) =>
  eq_ind_r nat (plus (times (div (mod n p) p) p) (mod (mod n p) p))
    (fun x : nat => eq nat x (mod (mod n p) p))
    (eq_ind_r nat O
       (fun x : nat =>
        eq nat (plus (times x p) (mod (mod n p) p)) (mod (mod n p) p))
       (rewrite_r nat (times p O)
          (fun __ : nat =>
           eq nat (plus __ (mod (mod n p) p)) (mod (mod n p) p))
          (rewrite_l nat O
             (fun __ : nat =>
              eq nat (plus __ (mod (mod n p) p)) (mod (mod n p) p))
             (rewrite_l nat (mod (mod n p) p)
                (fun __ : nat => eq nat __ (mod (mod n p) p))
                (refl nat (mod (mod n p) p)) (plus O (mod (mod n p) p))
                (plus_O_n (mod (mod n p) p))) (times p O) 
             (times_n_O p)) (times O p) (commutative_times O p))
       (div (mod n p) p) (eq_div_O (mod n p) p (lt_mod_m_m n p posp)))
    (mod n p) (div_mod (mod n p) p).
Definition congruent_n_mod_n :
  forall n p : nat, lt O p -> congruent n (mod n p) p :=
  fun (n p : nat) (posp : lt O p) => mod_mod n p posp.
Definition eq_times_plus_to_congruent :
  forall n m p r : nat,
  lt O p -> eq nat n (plus (times r p) m) -> congruent n m p :=
  fun (n m p r : nat) (posp : lt O p) (Hn : eq nat n (plus (times r p) m)) =>
  div_mod_spec_to_eq2 n p (div n p) (mod n p) (plus r (div m p)) 
    (mod m p) (div_mod_spec_div_mod n p posp)
    (div_mod_spec_intro n p (plus r (div m p)) (mod m p)
       (lt_mod_m_m m p posp)
       (eq_ind_r nat (times p (plus r (div m p)))
          (fun x : nat => eq nat n (plus x (mod m p)))
          (eq_ind_r nat (plus (times p r) (times p (div m p)))
             (fun x : nat => eq nat n (plus x (mod m p)))
             (eq_ind_r nat (times r p)
                (fun x : nat =>
                 eq nat n (plus (plus x (times p (div m p))) (mod m p)))
                (eq_ind_r nat (times (div m p) p)
                   (fun x : nat =>
                    eq nat n (plus (plus (times r p) x) (mod m p)))
                   (eq_ind_r nat
                      (plus (times r p) (plus (times (div m p) p) (mod m p)))
                      (fun x : nat => eq nat n x)
                      (rewrite_r nat (times p r)
                         (fun __ : nat =>
                          eq nat n
                            (plus __ (plus (times (div m p) p) (mod m p))))
                         (rewrite_r nat (times p (div m p))
                            (fun __ : nat =>
                             eq nat n (plus (times p r) (plus __ (mod m p))))
                            (rewrite_r nat
                               (plus (mod m p) (times p (div m p)))
                               (fun __ : nat =>
                                eq nat n (plus (times p r) __))
                               (rewrite_l nat m
                                  (fun __ : nat =>
                                   eq nat n (plus (times p r) __))
                                  (rewrite_r nat (plus m (times p r))
                                     (fun __ : nat => eq nat n __)
                                     (rewrite_l nat n
                                        (fun __ : nat => eq nat n __)
                                        (refl nat n) 
                                        (plus m (times p r))
                                        (rewrite_l nat 
                                           (plus (times p r) m)
                                           (fun __ : nat => eq nat n __)
                                           (rewrite_l nat 
                                              (times r p)
                                              (fun __ : nat =>
                                               eq nat n (plus __ m)) Hn
                                              (times p r)
                                              (commutative_times r p))
                                           (plus m (times p r))
                                           (commutative_plus (times p r) m)))
                                     (plus (times p r) m)
                                     (commutative_plus (times p r) m))
                                  (plus (mod m p) (times p (div m p)))
                                  (rewrite_l nat
                                     (plus (times p (div m p)) (mod m p))
                                     (fun __ : nat => eq nat m __)
                                     (rewrite_l nat 
                                        (times (div m p) p)
                                        (fun __ : nat =>
                                         eq nat m (plus __ (mod m p)))
                                        (div_mod m p) 
                                        (times p (div m p))
                                        (commutative_times (div m p) p))
                                     (plus (mod m p) (times p (div m p)))
                                     (commutative_plus 
                                        (times p (div m p)) 
                                        (mod m p))))
                               (plus (times p (div m p)) (mod m p))
                               (commutative_plus (times p (div m p))
                                  (mod m p))) (times (div m p) p)
                            (commutative_times (div m p) p)) 
                         (times r p) (commutative_times r p))
                      (plus (plus (times r p) (times (div m p) p)) (mod m p))
                      (associative_plus (times r p) 
                         (times (div m p) p) (mod m p))) 
                   (times p (div m p)) (commutative_times p (div m p)))
                (times p r) (commutative_times p r))
             (times p (plus r (div m p)))
             (distributive_times_plus p r (div m p)))
          (times (plus r (div m p)) p)
          (commutative_times (plus r (div m p)) p))).
Definition divides_to_congruent :
  forall n m p : nat,
  lt O p -> le m n -> divides p (minus n m) -> congruent n m p :=
  fun (n m p : nat) (posp : lt O p) (lemn : le m n)
    (_clearme : divides p (minus n m)) =>
  match_divides_prop p (minus n m) (congruent n m p)
    (fun (q : nat) (Hdiv : eq nat (minus n m) (times p q)) =>
     eq_times_plus_to_congruent n m p q posp
       (eq_ind_r nat (plus m (times q p)) (fun x : nat => eq nat n x)
          (minus_to_plus n m (times q p) lemn
             (rewrite_r nat (times p q)
                (fun __ : nat => eq nat __ (times q p))
                (rewrite_r nat (times p q)
                   (fun __ : nat => eq nat (times p q) __)
                   (refl nat (times p q)) (times q p) 
                   (commutative_times q p)) (minus n m) Hdiv))
          (plus (times q p) m) (commutative_plus (times q p) m))) _clearme.
Definition congruent_to_divides :
  forall n m p : nat, lt O p -> congruent n m p -> divides p (minus n m) :=
  fun (n m p : nat) (posp : lt O p) (Hcong : congruent n m p) =>
  quotient p (minus n m) (minus (div n p) (div m p))
    (eq_ind_r nat (times (minus (div n p) (div m p)) p)
       (fun x : nat => eq nat (minus n m) x)
       (eq_ind_r nat (plus (times (div n p) p) (mod n p))
          (fun x : nat =>
           eq nat (minus x m) (times (minus (div n p) (div m p)) p))
          (eq_ind_r nat (plus (times (div m p) p) (mod m p))
             (fun x : nat =>
              eq nat (minus (plus (times (div n p) p) (mod n p)) x)
                (times (minus (div n p) (div m p)) p))
             (rewrite_r nat (times p (div n p))
                (fun __ : nat =>
                 eq nat
                   (minus (plus __ (mod n p))
                      (plus (times (div m p) p) (mod m p)))
                   (times (minus (div n p) (div m p)) p))
                (rewrite_r nat (plus (mod n p) (times p (div n p)))
                   (fun __ : nat =>
                    eq nat (minus __ (plus (times (div m p) p) (mod m p)))
                      (times (minus (div n p) (div m p)) p))
                   (rewrite_l nat n
                      (fun __ : nat =>
                       eq nat (minus __ (plus (times (div m p) p) (mod m p)))
                         (times (minus (div n p) (div m p)) p))
                      (rewrite_r nat (times p (div m p))
                         (fun __ : nat =>
                          eq nat (minus n (plus __ (mod m p)))
                            (times (minus (div n p) (div m p)) p))
                         (rewrite_l nat (mod n p)
                            (fun __ : nat =>
                             eq nat (minus n (plus (times p (div m p)) __))
                               (times (minus (div n p) (div m p)) p))
                            (rewrite_r nat
                               (plus (mod n p) (times p (div m p)))
                               (fun __ : nat =>
                                eq nat (minus n __)
                                  (times (minus (div n p) (div m p)) p))
                               (rewrite_l nat
                                  (minus (minus n (mod n p))
                                     (times p (div m p)))
                                  (fun __ : nat =>
                                   eq nat __
                                     (times (minus (div n p) (div m p)) p))
                                  (rewrite_l nat (times p (div n p))
                                     (fun __ : nat =>
                                      eq nat (minus __ (times p (div m p)))
                                        (times (minus (div n p) (div m p)) p))
                                     (rewrite_l nat
                                        (times p (minus (div n p) (div m p)))
                                        (fun __ : nat =>
                                         eq nat __
                                           (times 
                                              (minus (div n p) (div m p)) p))
                                        (rewrite_r nat
                                           (times p
                                              (minus (div n p) (div m p)))
                                           (fun __ : nat =>
                                            eq nat
                                              (times p
                                                 (minus (div n p) (div m p)))
                                              __)
                                           (refl nat
                                              (times p
                                                 (minus (div n p) (div m p))))
                                           (times 
                                              (minus (div n p) (div m p)) p)
                                           (commutative_times
                                              (minus (div n p) (div m p)) p))
                                        (minus (times p (div n p))
                                           (times p (div m p)))
                                        (distributive_times_minus p 
                                           (div n p) 
                                           (div m p))) 
                                     (minus n (mod n p))
                                     (rewrite_l nat 
                                        (times (div n p) p)
                                        (fun __ : nat =>
                                         eq nat __ (minus n (mod n p)))
                                        (eq_times_div_minus_mod n p)
                                        (times p (div n p))
                                        (commutative_times (div n p) p)))
                                  (minus n
                                     (plus (mod n p) (times p (div m p))))
                                  (minus_plus n (mod n p) (times p (div m p))))
                               (plus (times p (div m p)) (mod n p))
                               (commutative_plus (times p (div m p))
                                  (mod n p))) (mod m p) Hcong)
                         (times (div m p) p) (commutative_times (div m p) p))
                      (plus (mod n p) (times p (div n p)))
                      (rewrite_l nat (plus (times p (div n p)) (mod n p))
                         (fun __ : nat => eq nat n __)
                         (rewrite_l nat (times (div n p) p)
                            (fun __ : nat => eq nat n (plus __ (mod n p)))
                            (div_mod n p) (times p (div n p))
                            (commutative_times (div n p) p))
                         (plus (mod n p) (times p (div n p)))
                         (commutative_plus (times p (div n p)) (mod n p))))
                   (plus (times p (div n p)) (mod n p))
                   (commutative_plus (times p (div n p)) (mod n p)))
                (times (div n p) p) (commutative_times (div n p) p)) m
             (div_mod m p)) n (div_mod n p))
       (times p (minus (div n p) (div m p)))
       (commutative_times p (minus (div n p) (div m p)))).
Definition let_clause_1034 :
  forall n m p : nat,
  lt O p ->
  forall x2515 x2516 : nat,
  eq nat x2515 (plus (mod x2515 x2516) (times x2516 (div x2515 x2516))) :=
  fun (n m p : nat) (posp : lt O p) (x2515 x2516 : nat) =>
  rewrite_l nat (plus (times x2516 (div x2515 x2516)) (mod x2515 x2516))
    (fun __ : nat => eq nat x2515 __)
    (rewrite_l nat (times (div x2515 x2516) x2516)
       (fun __ : nat => eq nat x2515 (plus __ (mod x2515 x2516)))
       (div_mod x2515 x2516) (times x2516 (div x2515 x2516))
       (commutative_times (div x2515 x2516) x2516))
    (plus (mod x2515 x2516) (times x2516 (div x2515 x2516)))
    (commutative_plus (times x2516 (div x2515 x2516)) (mod x2515 x2516)).
Definition let_clause_73 :
  forall n m p : nat,
  lt O p ->
  forall x134 x135 x136 : nat,
  eq nat (plus x134 (plus x135 x136)) (plus x135 (plus x134 x136)) :=
  fun (n m p : nat) (posp : lt O p) (x134 x135 x136 : nat) =>
  rewrite_l nat (plus (plus x135 x134) x136)
    (fun __ : nat => eq nat (plus x134 (plus x135 x136)) __)
    (assoc_plus1 x136 x135 x134) (plus x135 (plus x134 x136))
    (associative_plus x135 x134 x136).
Definition mod_times :
  forall n m p : nat,
  lt O p -> eq nat (mod (times n m) p) (mod (times (mod n p) (mod m p)) p) :=
  fun (n m p : nat) (posp : lt O p) =>
  eq_times_plus_to_congruent (times n m) (times (mod n p) (mod m p)) p
    (plus
       (plus (times (times (div n p) p) (div m p))
          (times (div n p) (mod m p))) (times (mod n p) (div m p))) posp
    (trans_eq nat (times n m)
       (times (plus (times (div n p) p) (mod n p))
          (plus (times (div m p) p) (mod m p)))
       (plus
          (times
             (plus
                (plus (times (times (div n p) p) (div m p))
                   (times (div n p) (mod m p))) (times (mod n p) (div m p)))
             p) (times (mod n p) (mod m p)))
       (rewrite_r nat (times p (div n p))
          (fun __ : nat =>
           eq nat (times n m)
             (times (plus __ (mod n p)) (plus (times (div m p) p) (mod m p))))
          (rewrite_r nat (plus (mod n p) (times p (div n p)))
             (fun __ : nat =>
              eq nat (times n m)
                (times __ (plus (times (div m p) p) (mod m p))))
             (rewrite_l nat n
                (fun __ : nat =>
                 eq nat (times n m)
                   (times __ (plus (times (div m p) p) (mod m p))))
                (rewrite_r nat (times p (div m p))
                   (fun __ : nat =>
                    eq nat (times n m) (times n (plus __ (mod m p))))
                   (rewrite_r nat (plus (mod m p) (times p (div m p)))
                      (fun __ : nat => eq nat (times n m) (times n __))
                      (rewrite_l nat m
                         (fun __ : nat => eq nat (times n m) (times n __))
                         (refl nat (times n m))
                         (plus (mod m p) (times p (div m p)))
                         (let_clause_1034 n m p posp m p))
                      (plus (times p (div m p)) (mod m p))
                      (commutative_plus (times p (div m p)) (mod m p)))
                   (times (div m p) p) (commutative_times (div m p) p))
                (plus (mod n p) (times p (div n p)))
                (let_clause_1034 n m p posp n p))
             (plus (times p (div n p)) (mod n p))
             (commutative_plus (times p (div n p)) (mod n p)))
          (times (div n p) p) (commutative_times (div n p) p))
       (trans_eq nat
          (times (plus (times (div n p) p) (mod n p))
             (plus (times (div m p) p) (mod m p)))
          (plus
             (plus
                (plus (times (times (div n p) p) (times (div m p) p))
                   (times (times (div n p) p) (mod m p)))
                (times (mod n p) (times (div m p) p)))
             (times (mod n p) (mod m p)))
          (plus
             (times
                (plus
                   (plus (times (times (div n p) p) (div m p))
                      (times (div n p) (mod m p)))
                   (times (mod n p) (div m p))) p)
             (times (mod n p) (mod m p)))
          (eq_ind_r nat
             (plus
                (times (times (div n p) p)
                   (plus (times (div m p) p) (mod m p)))
                (times (mod n p) (plus (times (div m p) p) (mod m p))))
             (fun x : nat =>
              eq nat x
                (plus
                   (plus
                      (plus (times (times (div n p) p) (times (div m p) p))
                         (times (times (div n p) p) (mod m p)))
                      (times (mod n p) (times (div m p) p)))
                   (times (mod n p) (mod m p))))
             (eq_ind_r nat
                (plus (times (times (div n p) p) (times (div m p) p))
                   (times (times (div n p) p) (mod m p)))
                (fun x : nat =>
                 eq nat
                   (plus x
                      (times (mod n p) (plus (times (div m p) p) (mod m p))))
                   (plus
                      (plus
                         (plus
                            (times (times (div n p) p) (times (div m p) p))
                            (times (times (div n p) p) (mod m p)))
                         (times (mod n p) (times (div m p) p)))
                      (times (mod n p) (mod m p))))
                (eq_ind_r nat
                   (plus (times (mod n p) (times (div m p) p))
                      (times (mod n p) (mod m p)))
                   (fun x : nat =>
                    eq nat
                      (plus
                         (plus
                            (times (times (div n p) p) (times (div m p) p))
                            (times (times (div n p) p) (mod m p))) x)
                      (plus
                         (plus
                            (plus
                               (times (times (div n p) p) (times (div m p) p))
                               (times (times (div n p) p) (mod m p)))
                            (times (mod n p) (times (div m p) p)))
                         (times (mod n p) (mod m p))))
                   (rewrite_l nat
                      (plus
                         (plus
                            (plus
                               (times (times (div n p) p) (times (div m p) p))
                               (times (times (div n p) p) (mod m p)))
                            (times (mod n p) (times (div m p) p)))
                         (times (mod n p) (mod m p)))
                      (fun __ : nat =>
                       eq nat __
                         (plus
                            (plus
                               (plus
                                  (times (times (div n p) p)
                                     (times (div m p) p))
                                  (times (times (div n p) p) (mod m p)))
                               (times (mod n p) (times (div m p) p)))
                            (times (mod n p) (mod m p))))
                      (refl nat
                         (plus
                            (plus
                               (plus
                                  (times (times (div n p) p)
                                     (times (div m p) p))
                                  (times (times (div n p) p) (mod m p)))
                               (times (mod n p) (times (div m p) p)))
                            (times (mod n p) (mod m p))))
                      (plus
                         (plus
                            (times (times (div n p) p) (times (div m p) p))
                            (times (times (div n p) p) (mod m p)))
                         (plus (times (mod n p) (times (div m p) p))
                            (times (mod n p) (mod m p))))
                      (associative_plus
                         (plus
                            (times (times (div n p) p) (times (div m p) p))
                            (times (times (div n p) p) (mod m p)))
                         (times (mod n p) (times (div m p) p))
                         (times (mod n p) (mod m p))))
                   (times (mod n p) (plus (times (div m p) p) (mod m p)))
                   (distributive_times_plus (mod n p) 
                      (times (div m p) p) (mod m p)))
                (times (times (div n p) p)
                   (plus (times (div m p) p) (mod m p)))
                (distributive_times_plus (times (div n p) p)
                   (times (div m p) p) (mod m p)))
             (times (plus (times (div n p) p) (mod n p))
                (plus (times (div m p) p) (mod m p)))
             (distributive_times_plus_r (plus (times (div m p) p) (mod m p))
                (times (div n p) p) (mod n p)))
          (eq_f2 nat nat nat plus
             (plus
                (plus (times (times (div n p) p) (times (div m p) p))
                   (times (times (div n p) p) (mod m p)))
                (times (mod n p) (times (div m p) p)))
             (times
                (plus
                   (plus (times (times (div n p) p) (div m p))
                      (times (div n p) (mod m p)))
                   (times (mod n p) (div m p))) p)
             (times (mod n p) (mod m p)) (times (mod n p) (mod m p))
             (eq_ind nat (times (times (times (div n p) p) (div m p)) p)
                (fun x_1 : nat =>
                 eq nat
                   (plus (plus x_1 (times (times (div n p) p) (mod m p)))
                      (times (mod n p) (times (div m p) p)))
                   (times
                      (plus
                         (plus (times (times (div n p) p) (div m p))
                            (times (div n p) (mod m p)))
                         (times (mod n p) (div m p))) p))
                (eq_ind_r nat (times (div n p) (times p (mod m p)))
                   (fun x : nat =>
                    eq nat
                      (plus
                         (plus
                            (times (times (times (div n p) p) (div m p)) p) x)
                         (times (mod n p) (times (div m p) p)))
                      (times
                         (plus
                            (plus (times (times (div n p) p) (div m p))
                               (times (div n p) (mod m p)))
                            (times (mod n p) (div m p))) p))
                   (eq_ind_r nat (times (mod m p) p)
                      (fun x : nat =>
                       eq nat
                         (plus
                            (plus
                               (times (times (times (div n p) p) (div m p)) p)
                               (times (div n p) x))
                            (times (mod n p) (times (div m p) p)))
                         (times
                            (plus
                               (plus (times (times (div n p) p) (div m p))
                                  (times (div n p) (mod m p)))
                               (times (mod n p) (div m p))) p))
                      (eq_ind nat (times (times (div n p) (mod m p)) p)
                         (fun x_1 : nat =>
                          eq nat
                            (plus
                               (plus
                                  (times
                                     (times (times (div n p) p) (div m p)) p)
                                  x_1) (times (mod n p) (times (div m p) p)))
                            (times
                               (plus
                                  (plus (times (times (div n p) p) (div m p))
                                     (times (div n p) (mod m p)))
                                  (times (mod n p) (div m p))) p))
                         (eq_ind_r nat
                            (plus
                               (times
                                  (plus (times (times (div n p) p) (div m p))
                                     (times (div n p) (mod m p))) p)
                               (times (times (mod n p) (div m p)) p))
                            (fun x : nat =>
                             eq nat
                               (plus
                                  (plus
                                     (times
                                        (times (times (div n p) p) (div m p))
                                        p)
                                     (times (times (div n p) (mod m p)) p))
                                  (times (mod n p) (times (div m p) p))) x)
                            (rewrite_r nat (times p (div n p))
                               (fun __ : nat =>
                                eq nat
                                  (plus
                                     (plus (times (times __ (div m p)) p)
                                        (times (times (div n p) (mod m p)) p))
                                     (times (mod n p) (times (div m p) p)))
                                  (plus
                                     (times
                                        (plus
                                           (times 
                                              (times (div n p) p) 
                                              (div m p))
                                           (times (div n p) (mod m p))) p)
                                     (times (times (mod n p) (div m p)) p)))
                               (rewrite_r nat
                                  (times (div m p) (times p (div n p)))
                                  (fun __ : nat =>
                                   eq nat
                                     (plus
                                        (plus (times __ p)
                                           (times 
                                              (times (div n p) (mod m p)) p))
                                        (times (mod n p) (times (div m p) p)))
                                     (plus
                                        (times
                                           (plus
                                              (times 
                                                 (times (div n p) p)
                                                 (div m p))
                                              (times (div n p) (mod m p))) p)
                                        (times (times (mod n p) (div m p)) p)))
                                  (rewrite_r nat
                                     (times p (times (div m p) (div n p)))
                                     (fun __ : nat =>
                                      eq nat
                                        (plus
                                           (plus (times __ p)
                                              (times
                                                 (times (div n p) (mod m p))
                                                 p))
                                           (times 
                                              (mod n p) 
                                              (times (div m p) p)))
                                        (plus
                                           (times
                                              (plus
                                                 (times 
                                                 (times (div n p) p)
                                                 (div m p))
                                                 (times (div n p) (mod m p)))
                                              p)
                                           (times 
                                              (times (mod n p) (div m p)) p)))
                                     (rewrite_r nat
                                        (times (div n p) (div m p))
                                        (fun __ : nat =>
                                         eq nat
                                           (plus
                                              (plus 
                                                 (times (times p __) p)
                                                 (times
                                                 (times (div n p) (mod m p))
                                                 p))
                                              (times 
                                                 (mod n p)
                                                 (times (div m p) p)))
                                           (plus
                                              (times
                                                 (plus
                                                 (times 
                                                 (times (div n p) p)
                                                 (div m p))
                                                 (times (div n p) (mod m p)))
                                                 p)
                                              (times
                                                 (times (mod n p) (div m p))
                                                 p)))
                                        (rewrite_r nat
                                           (times p
                                              (times p
                                                 (times (div n p) (div m p))))
                                           (fun __ : nat =>
                                            eq nat
                                              (plus
                                                 (plus __
                                                 (times
                                                 (times (div n p) (mod m p))
                                                 p))
                                                 (times 
                                                 (mod n p)
                                                 (times (div m p) p)))
                                              (plus
                                                 (times
                                                 (plus
                                                 (times 
                                                 (times (div n p) p)
                                                 (div m p))
                                                 (times (div n p) (mod m p)))
                                                 p)
                                                 (times
                                                 (times (mod n p) (div m p))
                                                 p)))
                                           (rewrite_r nat
                                              (times p
                                                 (times (div n p) (mod m p)))
                                              (fun __ : nat =>
                                               eq nat
                                                 (plus
                                                 (plus
                                                 (times p
                                                 (times p
                                                 (times (div n p) (div m p))))
                                                 __)
                                                 (times 
                                                 (mod n p)
                                                 (times (div m p) p)))
                                                 (plus
                                                 (times
                                                 (plus
                                                 (times 
                                                 (times (div n p) p)
                                                 (div m p))
                                                 (times (div n p) (mod m p)))
                                                 p)
                                                 (times
                                                 (times (mod n p) (div m p))
                                                 p)))
                                              (rewrite_l nat
                                                 (times p
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (times (div n p) (mod m p))))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (plus __
                                                 (times 
                                                 (mod n p)
                                                 (times (div m p) p)))
                                                 (plus
                                                 (times
                                                 (plus
                                                 (times 
                                                 (times (div n p) p)
                                                 (div m p))
                                                 (times (div n p) (mod m p)))
                                                 p)
                                                 (times
                                                 (times (mod n p) (div m p))
                                                 p)))
                                                 (rewrite_r nat
                                                 (times p (div m p))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (plus
                                                 (times p
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (times (div n p) (mod m p))))
                                                 (times (mod n p) __))
                                                 (plus
                                                 (times
                                                 (plus
                                                 (times 
                                                 (times (div n p) p)
                                                 (div m p))
                                                 (times (div n p) (mod m p)))
                                                 p)
                                                 (times
                                                 (times (mod n p) (div m p))
                                                 p)))
                                                 (rewrite_r nat
                                                 (times p
                                                 (times (mod n p) (div m p)))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (plus
                                                 (times p
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (times (div n p) (mod m p))))
                                                 __)
                                                 (plus
                                                 (times
                                                 (plus
                                                 (times 
                                                 (times (div n p) p)
                                                 (div m p))
                                                 (times (div n p) (mod m p)))
                                                 p)
                                                 (times
                                                 (times (mod n p) (div m p))
                                                 p)))
                                                 (rewrite_r nat
                                                 (times (div m p) (mod n p))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (plus
                                                 (times p
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (times (div n p) (mod m p))))
                                                 (times p __))
                                                 (plus
                                                 (times
                                                 (plus
                                                 (times 
                                                 (times (div n p) p)
                                                 (div m p))
                                                 (times (div n p) (mod m p)))
                                                 p)
                                                 (times
                                                 (times (mod n p) (div m p))
                                                 p)))
                                                 (rewrite_r nat
                                                 (plus
                                                 (times p
                                                 (times (div m p) (mod n p)))
                                                 (times p
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (times (div n p) (mod m p)))))
                                                 (fun __ : nat =>
                                                 eq nat __
                                                 (plus
                                                 (times
                                                 (plus
                                                 (times 
                                                 (times (div n p) p)
                                                 (div m p))
                                                 (times (div n p) (mod m p)))
                                                 p)
                                                 (times
                                                 (times (mod n p) (div m p))
                                                 p)))
                                                 (rewrite_l nat
                                                 (times p
                                                 (plus
                                                 (times (div m p) (mod n p))
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (times (div n p) (mod m p)))))
                                                 (fun __ : nat =>
                                                 eq nat __
                                                 (plus
                                                 (times
                                                 (plus
                                                 (times 
                                                 (times (div n p) p)
                                                 (div m p))
                                                 (times (div n p) (mod m p)))
                                                 p)
                                                 (times
                                                 (times (mod n p) (div m p))
                                                 p)))
                                                 (rewrite_r nat
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (plus
                                                 (times (div m p) (mod n p))
                                                 (times (div n p) (mod m p))))
                                                 (fun __ : nat =>
                                                 eq nat 
                                                 (times p __)
                                                 (plus
                                                 (times
                                                 (plus
                                                 (times 
                                                 (times (div n p) p)
                                                 (div m p))
                                                 (times (div n p) (mod m p)))
                                                 p)
                                                 (times
                                                 (times (mod n p) (div m p))
                                                 p)))
                                                 (rewrite_r nat
                                                 (plus
                                                 (times (div n p) (mod m p))
                                                 (times (div m p) (mod n p)))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (times p
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 __))
                                                 (plus
                                                 (times
                                                 (plus
                                                 (times 
                                                 (times (div n p) p)
                                                 (div m p))
                                                 (times (div n p) (mod m p)))
                                                 p)
                                                 (times
                                                 (times (mod n p) (div m p))
                                                 p)))
                                                 (rewrite_r nat
                                                 (times p (div n p))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (times p
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (plus
                                                 (times (div n p) (mod m p))
                                                 (times (div m p) (mod n p)))))
                                                 (plus
                                                 (times
                                                 (plus 
                                                 (times __ (div m p))
                                                 (times (div n p) (mod m p)))
                                                 p)
                                                 (times
                                                 (times (mod n p) (div m p))
                                                 p)))
                                                 (rewrite_r nat
                                                 (times 
                                                 (div m p)
                                                 (times p (div n p)))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (times p
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (plus
                                                 (times (div n p) (mod m p))
                                                 (times (div m p) (mod n p)))))
                                                 (plus
                                                 (times
                                                 (plus __
                                                 (times (div n p) (mod m p)))
                                                 p)
                                                 (times
                                                 (times (mod n p) (div m p))
                                                 p)))
                                                 (rewrite_r nat
                                                 (times p
                                                 (times (div m p) (div n p)))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (times p
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (plus
                                                 (times (div n p) (mod m p))
                                                 (times (div m p) (mod n p)))))
                                                 (plus
                                                 (times
                                                 (plus __
                                                 (times (div n p) (mod m p)))
                                                 p)
                                                 (times
                                                 (times (mod n p) (div m p))
                                                 p)))
                                                 (rewrite_r nat
                                                 (times (div n p) (div m p))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (times p
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (plus
                                                 (times (div n p) (mod m p))
                                                 (times (div m p) (mod n p)))))
                                                 (plus
                                                 (times
                                                 (plus 
                                                 (times p __)
                                                 (times (div n p) (mod m p)))
                                                 p)
                                                 (times
                                                 (times (mod n p) (div m p))
                                                 p)))
                                                 (rewrite_r nat
                                                 (times p
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (times (div n p) (mod m p))))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (times p
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (plus
                                                 (times (div n p) (mod m p))
                                                 (times (div m p) (mod n p)))))
                                                 (plus __
                                                 (times
                                                 (times (mod n p) (div m p))
                                                 p)))
                                                 (rewrite_r nat
                                                 (times (div m p) (mod n p))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (times p
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (plus
                                                 (times (div n p) (mod m p))
                                                 (times (div m p) (mod n p)))))
                                                 (plus
                                                 (times p
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (times (div n p) (mod m p))))
                                                 (times __ p)))
                                                 (rewrite_r nat
                                                 (times p
                                                 (times (div m p) (mod n p)))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (times p
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (plus
                                                 (times (div n p) (mod m p))
                                                 (times (div m p) (mod n p)))))
                                                 (plus
                                                 (times p
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (times (div n p) (mod m p))))
                                                 __))
                                                 (rewrite_r nat
                                                 (plus
                                                 (times p
                                                 (times (div m p) (mod n p)))
                                                 (times p
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (times (div n p) (mod m p)))))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (times p
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (plus
                                                 (times (div n p) (mod m p))
                                                 (times (div m p) (mod n p)))))
                                                 __)
                                                 (rewrite_l nat
                                                 (times p
                                                 (plus
                                                 (times (div m p) (mod n p))
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (times (div n p) (mod m p)))))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (times p
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (plus
                                                 (times (div n p) (mod m p))
                                                 (times (div m p) (mod n p)))))
                                                 __)
                                                 (rewrite_r nat
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (plus
                                                 (times (div m p) (mod n p))
                                                 (times (div n p) (mod m p))))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (times p
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (plus
                                                 (times (div n p) (mod m p))
                                                 (times (div m p) (mod n p)))))
                                                 (times p __))
                                                 (rewrite_r nat
                                                 (plus
                                                 (times (div n p) (mod m p))
                                                 (times (div m p) (mod n p)))
                                                 (fun __ : nat =>
                                                 eq nat
                                                 (times p
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (plus
                                                 (times (div n p) (mod m p))
                                                 (times (div m p) (mod n p)))))
                                                 (times p
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 __)))
                                                 (refl nat
                                                 (times p
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (plus
                                                 (times (div n p) (mod m p))
                                                 (times (div m p) (mod n p))))))
                                                 (plus
                                                 (times (div m p) (mod n p))
                                                 (times (div n p) (mod m p)))
                                                 (commutative_plus
                                                 (times (div m p) (mod n p))
                                                 (times (div n p) (mod m p))))
                                                 (plus
                                                 (times (div m p) (mod n p))
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (times (div n p) (mod m p))))
                                                 (let_clause_73 n m p posp
                                                 (times (div m p) (mod n p))
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (times (div n p) (mod m p))))
                                                 (plus
                                                 (times p
                                                 (times (div m p) (mod n p)))
                                                 (times p
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (times (div n p) (mod m p)))))
                                                 (distributive_times_plus p
                                                 (times (div m p) (mod n p))
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (times (div n p) (mod m p)))))
                                                 (plus
                                                 (times p
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (times (div n p) (mod m p))))
                                                 (times p
                                                 (times (div m p) (mod n p))))
                                                 (commutative_plus
                                                 (times p
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (times (div n p) (mod m p))))
                                                 (times p
                                                 (times (div m p) (mod n p)))))
                                                 (times
                                                 (times (div m p) (mod n p))
                                                 p)
                                                 (commutative_times
                                                 (times (div m p) (mod n p))
                                                 p))
                                                 (times (mod n p) (div m p))
                                                 (commutative_times 
                                                 (mod n p) 
                                                 (div m p)))
                                                 (times
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (times (div n p) (mod m p)))
                                                 p)
                                                 (commutative_times
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (times (div n p) (mod m p)))
                                                 p))
                                                 (times (div m p) (div n p))
                                                 (commutative_times 
                                                 (div m p) 
                                                 (div n p)))
                                                 (times 
                                                 (div m p)
                                                 (times p (div n p)))
                                                 (times_times 
                                                 (div m p) p 
                                                 (div n p)))
                                                 (times 
                                                 (times p (div n p))
                                                 (div m p))
                                                 (commutative_times
                                                 (times p (div n p))
                                                 (div m p)))
                                                 (times (div n p) p)
                                                 (commutative_times 
                                                 (div n p) p))
                                                 (plus
                                                 (times (div m p) (mod n p))
                                                 (times (div n p) (mod m p)))
                                                 (commutative_plus
                                                 (times (div m p) (mod n p))
                                                 (times (div n p) (mod m p))))
                                                 (plus
                                                 (times (div m p) (mod n p))
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (times (div n p) (mod m p))))
                                                 (let_clause_73 n m p posp
                                                 (times (div m p) (mod n p))
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (times (div n p) (mod m p))))
                                                 (plus
                                                 (times p
                                                 (times (div m p) (mod n p)))
                                                 (times p
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (times (div n p) (mod m p)))))
                                                 (distributive_times_plus p
                                                 (times (div m p) (mod n p))
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (times (div n p) (mod m p)))))
                                                 (plus
                                                 (times p
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (times (div n p) (mod m p))))
                                                 (times p
                                                 (times (div m p) (mod n p))))
                                                 (commutative_plus
                                                 (times p
                                                 (plus
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (times (div n p) (mod m p))))
                                                 (times p
                                                 (times (div m p) (mod n p)))))
                                                 (times (mod n p) (div m p))
                                                 (commutative_times 
                                                 (mod n p) 
                                                 (div m p)))
                                                 (times 
                                                 (mod n p)
                                                 (times p (div m p)))
                                                 (times_times 
                                                 (mod n p) p 
                                                 (div m p)))
                                                 (times (div m p) p)
                                                 (commutative_times 
                                                 (div m p) p))
                                                 (plus
                                                 (times p
                                                 (times p
                                                 (times (div n p) (div m p))))
                                                 (times p
                                                 (times (div n p) (mod m p))))
                                                 (distributive_times_plus p
                                                 (times p
                                                 (times (div n p) (div m p)))
                                                 (times (div n p) (mod m p))))
                                              (times
                                                 (times (div n p) (mod m p))
                                                 p)
                                              (commutative_times
                                                 (times (div n p) (mod m p))
                                                 p))
                                           (times
                                              (times p
                                                 (times (div n p) (div m p)))
                                              p)
                                           (commutative_times
                                              (times p
                                                 (times (div n p) (div m p)))
                                              p)) 
                                        (times (div m p) (div n p))
                                        (commutative_times 
                                           (div m p) 
                                           (div n p)))
                                     (times (div m p) (times p (div n p)))
                                     (times_times (div m p) p (div n p)))
                                  (times (times p (div n p)) (div m p))
                                  (commutative_times 
                                     (times p (div n p)) 
                                     (div m p))) (times (div n p) p)
                               (commutative_times (div n p) p))
                            (times
                               (plus
                                  (plus (times (times (div n p) p) (div m p))
                                     (times (div n p) (mod m p)))
                                  (times (mod n p) (div m p))) p)
                            (distributive_times_plus_r p
                               (plus (times (times (div n p) p) (div m p))
                                  (times (div n p) (mod m p)))
                               (times (mod n p) (div m p))))
                         (times (div n p) (times (mod m p) p))
                         (associative_times (div n p) (mod m p) p))
                      (times p (mod m p)) (commutative_times p (mod m p)))
                   (times (times (div n p) p) (mod m p))
                   (associative_times (div n p) p (mod m p)))
                (times (times (div n p) p) (times (div m p) p))
                (associative_times (times (div n p) p) (div m p) p))
             (refl nat (times (mod n p) (mod m p)))))).
Definition congruent_times :
  forall n m n1 m1 p : nat,
  lt O p ->
  congruent n n1 p ->
  congruent m m1 p -> congruent (times n m) (times n1 m1) p :=
  fun (n m n1 m1 p : nat) (posp : lt O p) (Hcongn : congruent n n1 p)
    (Hcongm : congruent m m1 p) =>
  eq_ind_r nat (mod (times (mod n p) (mod m p)) p)
    (fun x : nat => eq nat x (mod (times n1 m1) p))
    (eq_ind_r nat (mod n1 p)
       (fun x : nat =>
        eq nat (mod (times x (mod m p)) p) (mod (times n1 m1) p))
       (eq_ind_r nat (mod m1 p)
          (fun x : nat =>
           eq nat (mod (times (mod n1 p) x) p) (mod (times n1 m1) p))
          (sym_eq nat (mod (times n1 m1) p)
             (mod (times (mod n1 p) (mod m1 p)) p) 
             (mod_times n1 m1 p posp)) (mod m p) Hcongm) 
       (mod n p) Hcongn) (mod (times n m) p) (mod_times n m p posp).

From Coq.Arith Require Import Factorial.
Definition fact : nat -> nat := fact.
Definition fact_body : nat -> nat := fact.
Theorem eq_fact :
  forall n : nat, leibniz nat (fact n) (filter_nat_type nat fact_body n).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.
Definition sym_eq_fact :
  forall n : nat, leibniz nat (filter_nat_type nat fact_body n) (fact n) :=
  fun n : nat =>
  sym_leibniz nat (fact n) (filter_nat_type nat fact_body n) (eq_fact n).
Theorem eq_fact_body_O : leibniz nat (fact_body O) (S O).
Proof.
  (intros **; apply to_leibniz).
  reflexivity.
Qed.
Definition sym_eq_fact_body_O : leibniz nat (S O) (fact_body O) :=
  sym_leibniz nat (fact_body O) (S O) eq_fact_body_O.
Theorem eq_fact_body_S :
  forall n : nat, leibniz nat (fact_body (S n)) (times (fact n) (S n)).
Proof.
  (intros **; apply to_leibniz).
  (rewrite commutative_times).
  reflexivity.
Qed.
Definition sym_eq_fact_body_S :
  forall n : nat, leibniz nat (times (fact n) (S n)) (fact_body (S n)) :=
  fun n : nat =>
  sym_leibniz nat (fact_body (S n)) (times (fact n) (S n)) (eq_fact_body_S n).
Definition prime_to_not_divides_fact :
  forall p : nat,
  prime p -> forall n : nat, lt n p -> Not (divides p (fact n)) :=
  fun (p : nat) (primep : prime p) (n : nat) =>
  nat_ind (fun _x_365 : nat => lt _x_365 p -> Not (divides p (fact _x_365)))
    (sym_eq_fact O (fun y : nat => lt O p -> Not (divides p y))
       (sym_eq_filter_nat_type_O nat fact_body
          (fun y : nat => lt O p -> Not (divides p y))
          (sym_eq_fact_body_O (fun y : nat => lt O p -> Not (divides p y))
             (fun (__ : le (S O) p) (divp : divides p (S O)) =>
              absurd (le p (S O)) (divides_to_le p (S O) (lt_O_S O) divp)
                (lt_to_not_le (S O) p (prime_to_lt_SO p primep))))))
    (fun n1 : nat =>
     sym_eq_fact (S n1)
       (fun y : nat =>
        (lt n1 p -> Not (divides p (fact n1))) ->
        lt (S n1) p -> Not (divides p y))
       (sym_eq_filter_nat_type_S nat fact_body n1
          (fun y : nat =>
           (lt n1 p -> Not (divides p (fact n1))) ->
           lt (S n1) p -> Not (divides p y))
          (sym_eq_fact_body_S n1
             (fun y : nat =>
              (lt n1 p -> Not (divides p (fact n1))) ->
              lt (S n1) p -> Not (divides p y))
             (fun (Hind : lt n1 p -> Not (divides p (fact n1)))
                (ltn1 : lt (S n1) p)
                (Hdiv : divides p (times (fact n1) (S n1))) =>
              match_Or_prop (divides p (fact n1)) 
                (divides p (S n1)) False
                (fun Hdiv0 : divides p (fact n1) =>
                 absurd (divides p (fact n1)) Hdiv0
                   (Hind (lt_to_le (S n1) p ltn1)))
                (fun Hdiv0 : divides p (S n1) =>
                 absurd (le p (S n1))
                   (divides_to_le p (S n1) (lt_O_S n1) Hdiv0)
                   (lt_to_not_le (S n1) p ltn1))
                (divides_times_to_divides p (fact n1) (S n1) primep Hdiv)))))
    n.
Definition permut_mod :
  forall p a : nat,
  prime p ->
  Not (divides p a) -> permut (fun n : nat => mod (times a n) p) (pred p) :=
  fun (p a : nat) (primep : prime p) (ndiv : Not (divides p a)) 
    (z : Prop)
    (f : (forall x : nat, le x (pred p) -> le (mod (times a x) p) (pred p)) ->
         injn (fun n : nat => mod (times a n) p) (pred p) -> z) =>
  f
    (fun (i : nat) (lei : le i (pred p)) =>
     le_S_S_to_le (mod (times a i) p) (pred p)
       (transitive_le (S (mod (times a i) p)) p (S (pred p))
          (lt_mod_m_m (times a i) p (prime_to_lt_O p primep))
          (eq_ind_r nat p (fun x : nat => le p x) 
             (le_n p) (S (pred p)) (S_pred p (prime_to_lt_O p primep)))))
    (fun (i j : nat) (lei : le i (pred p)) (lej : le j (pred p))
       (H : eq nat (mod (times a i) p) (mod (times a j) p)) =>
     match_Or_prop (lt i j) (Not (lt i j)) (eq nat i j)
       (fun ltij : lt i j =>
        falsity (eq nat i j)
          (absurd (lt (minus j i) p)
             (eq_ind nat (S (pred p)) (fun x_1 : nat => lt (minus j i) x_1)
                (le_S_S (minus j i) (pred p)
                   (le_plus_to_minus j i (pred p)
                      (transitive_le j (pred p) (plus (pred p) i) lej
                         (le_plus_n_r i (pred p))))) p
                (S_pred p (prime_to_lt_O p primep)))
             (le_to_not_lt p (minus j i)
                (divides_to_le p (minus j i)
                   (lt_plus_to_minus_r O i j
                      (sym_eq_plus O (fun y : nat -> nat => le (S (y i)) j)
                         (sym_eq_filter_nat_type_O 
                            (nat -> nat) plus_body
                            (fun y : nat -> nat => le (S (y i)) j)
                            (sym_eq_plus_body_O
                               (fun y : nat -> nat => le (S (y i)) j) ltij))))
                   (match_Or_prop (divides p a) (divides p (minus j i))
                      (divides p (minus j i))
                      (fun Hdiv : divides p a =>
                       falsity (divides p (minus j i))
                         (absurd (divides p a) Hdiv ndiv))
                      (fun auto : divides p (minus j i) => auto)
                      (divides_times_to_divides p a 
                         (minus j i) primep
                         (eq_ind_r nat (minus (times a j) (times a i))
                            (fun x : nat => divides p x)
                            (eq_mod_to_divides (times a j) 
                               (times a i) p (prime_to_lt_O p primep)
                               (rewrite_l nat (mod (times a i) p)
                                  (fun __ : nat =>
                                   eq nat __ (mod (times a i) p))
                                  (refl nat (mod (times a i) p))
                                  (mod (times a j) p) H))
                            (times a (minus j i))
                            (distributive_times_minus a j i))))))))
       (fun Hij : Not (lt i j) =>
        match_Or_prop (lt j i) (eq nat j i) (eq nat i j)
          (fun Hij0 : lt j i =>
           falsity (eq nat i j)
             (absurd (lt (minus i j) p)
                (eq_ind nat (S (pred p))
                   (fun x_1 : nat => lt (minus i j) x_1)
                   (le_S_S (minus i j) (pred p)
                      (le_plus_to_minus i j (pred p)
                         (transitive_le i (pred p) 
                            (plus (pred p) j) lei 
                            (le_plus_n_r j (pred p))))) p
                   (S_pred p (prime_to_lt_O p primep)))
                (le_to_not_lt p (minus i j)
                   (divides_to_le p (minus i j)
                      (lt_plus_to_minus_r O j i
                         (sym_eq_plus O
                            (fun y : nat -> nat => le (S (y j)) i)
                            (sym_eq_filter_nat_type_O 
                               (nat -> nat) plus_body
                               (fun y : nat -> nat => le (S (y j)) i)
                               (sym_eq_plus_body_O
                                  (fun y : nat -> nat => le (S (y j)) i) Hij0))))
                      (match_Or_prop (divides p a) 
                         (divides p (minus i j)) (divides p (minus i j))
                         (fun Hdiv : divides p a =>
                          falsity (divides p (minus i j))
                            (absurd (divides p a) Hdiv ndiv))
                         (fun auto : divides p (minus i j) => auto)
                         (divides_times_to_divides p a 
                            (minus i j) primep
                            (eq_ind_r nat (minus (times a i) (times a j))
                               (fun x : nat => divides p x)
                               (eq_mod_to_divides 
                                  (times a i) (times a j) p
                                  (prime_to_lt_O p primep)
                                  (rewrite_l nat (mod (times a i) p)
                                     (fun __ : nat =>
                                      eq nat (mod (times a i) p) __)
                                     (refl nat (mod (times a i) p))
                                     (mod (times a j) p) H))
                               (times a (minus i j))
                               (distributive_times_minus a i j))))))))
          (fun Hij0 : eq nat j i =>
           rewrite_r nat i (fun __ : nat => eq nat i __) (refl nat i) j Hij0)
          (le_to_or_lt_eq j i (not_lt_to_le i j Hij))) 
       (decidable_lt i j)).
Definition eq_fact_pi_p :
  forall n : nat,
  eq nat (fact n)
    (bigop nat (minus (S n) (S O)) (fun i : nat => true) 
       (S O) times (fun i : nat => plus i (S O))) :=
  fun n : nat =>
  nat_ind
    (fun _x_365 : nat =>
     eq nat (fact _x_365)
       (bigop nat (minus (S _x_365) (S O)) (fun i : nat => true) 
          (S O) times (fun i : nat => plus i (S O))))
    (sym_eq_minus (S O)
       (fun y : nat -> nat =>
        eq nat (fact O)
          (bigop nat (y (S O)) (fun i : nat => true) 
             (S O) times (fun i : nat => plus i (S O))))
       (sym_eq_filter_nat_type_S (nat -> nat) minus_body O
          (fun y : nat -> nat =>
           eq nat (fact O)
             (bigop nat (y (S O)) (fun i : nat => true) 
                (S O) times (fun i : nat => plus i (S O))))
          (sym_eq_minus_body_S O
             (fun y : nat -> nat =>
              eq nat (fact O)
                (bigop nat (y (S O)) (fun i : nat => true) 
                   (S O) times (fun i : nat => plus i (S O))))
             (sym_eq_match_nat_type_S nat (S O) (fun q : nat => minus O q) O
                (fun y : nat =>
                 eq nat (fact O)
                   (bigop nat y (fun i : nat => true) 
                      (S O) times (fun i : nat => plus i (S O))))
                (sym_eq_minus O
                   (fun y : nat -> nat =>
                    eq nat (fact O)
                      (bigop nat (y O) (fun i : nat => true) 
                         (S O) times (fun i : nat => plus i (S O))))
                   (sym_eq_filter_nat_type_O (nat -> nat) minus_body
                      (fun y : nat -> nat =>
                       eq nat (fact O)
                         (bigop nat (y O) (fun i : nat => true) 
                            (S O) times (fun i : nat => plus i (S O))))
                      (sym_eq_minus_body_O
                         (fun y : nat -> nat =>
                          eq nat (fact O)
                            (bigop nat (y O) (fun i : nat => true) 
                               (S O) times (fun i : nat => plus i (S O))))
                         (sym_eq_bigop_O nat
                            (fun
                               y : (nat -> bool) ->
                                   nat ->
                                   (nat -> nat -> nat) -> (nat -> nat) -> nat
                             =>
                             eq nat (fact O)
                               (y (fun i : nat => true) 
                                  (S O) times (fun i : nat => plus i (S O))))
                            (sym_eq_bigop_body_O nat
                               (fun
                                  y : (nat -> bool) ->
                                      nat ->
                                      (nat -> nat -> nat) ->
                                      (nat -> nat) -> nat =>
                                eq nat (fact O)
                                  (y (fun i : nat => true) 
                                     (S O) times
                                     (fun i : nat => plus i (S O))))
                               (eq_fact_body_O
                                  (fun y : nat => eq nat (fact O) y)
                                  (eq_filter_nat_type_O nat fact_body
                                     (fun y : nat => eq nat (fact O) y)
                                     (eq_fact O
                                        (fun y : nat => eq nat (fact O) y)
                                        (refl nat (fact O))))))))))))))
    (fun n1 : nat =>
     sym_eq_fact (S n1)
       (fun y : nat =>
        eq nat (fact n1)
          (bigop nat (minus (S n1) (S O)) (fun i : nat => true) 
             (S O) times (fun i : nat => plus i (S O))) ->
        eq nat y
          (bigop nat (minus (S (S n1)) (S O)) (fun i : nat => true) 
             (S O) times (fun i : nat => plus i (S O))))
       (sym_eq_filter_nat_type_S nat fact_body n1
          (fun y : nat =>
           eq nat (fact n1)
             (bigop nat (minus (S n1) (S O)) (fun i : nat => true) 
                (S O) times (fun i : nat => plus i (S O))) ->
           eq nat y
             (bigop nat (minus (S (S n1)) (S O)) (fun i : nat => true) 
                (S O) times (fun i : nat => plus i (S O))))
          (sym_eq_fact_body_S n1
             (fun y : nat =>
              eq nat (fact n1)
                (bigop nat (minus (S n1) (S O)) (fun i : nat => true) 
                   (S O) times (fun i : nat => plus i (S O))) ->
              eq nat y
                (bigop nat (minus (S (S n1)) (S O)) 
                   (fun i : nat => true) (S O) times
                   (fun i : nat => plus i (S O))))
             (fun
                Hind : eq nat (fact n1)
                         (bigop nat (minus (S n1) (S O))
                            (fun i : nat => true) 
                            (S O) times (fun i : nat => plus i (S O))) =>
              eq_ind_r nat (times (S n1) (fact n1))
                (fun x : nat =>
                 eq nat x
                   (bigop nat (minus (S (S n1)) (S O)) 
                      (fun i : nat => true) (S O) times
                      (fun i : nat => plus i (S O))))
                (sym_eq_minus (S (S n1))
                   (fun y : nat -> nat =>
                    eq nat (times (S n1) (fact n1))
                      (bigop nat (y (S O)) (fun i : nat => true) 
                         (S O) times (fun i : nat => plus i (S O))))
                   (sym_eq_filter_nat_type_S (nat -> nat) minus_body 
                      (S n1)
                      (fun y : nat -> nat =>
                       eq nat (times (S n1) (fact n1))
                         (bigop nat (y (S O)) (fun i : nat => true) 
                            (S O) times (fun i : nat => plus i (S O))))
                      (sym_eq_minus_body_S (S n1)
                         (fun y : nat -> nat =>
                          eq nat (times (S n1) (fact n1))
                            (bigop nat (y (S O)) (fun i : nat => true) 
                               (S O) times (fun i : nat => plus i (S O))))
                         (sym_eq_match_nat_type_S nat 
                            (S (S n1)) (fun q : nat => minus (S n1) q) O
                            (fun y : nat =>
                             eq nat (times (S n1) (fact n1))
                               (bigop nat y (fun i : nat => true) 
                                  (S O) times (fun i : nat => plus i (S O))))
                            (sym_eq_minus (S n1)
                               (fun y : nat -> nat =>
                                eq nat (times (S n1) (fact n1))
                                  (bigop nat (y O) 
                                     (fun i : nat => true) 
                                     (S O) times
                                     (fun i : nat => plus i (S O))))
                               (sym_eq_filter_nat_type_S 
                                  (nat -> nat) minus_body n1
                                  (fun y : nat -> nat =>
                                   eq nat (times (S n1) (fact n1))
                                     (bigop nat (y O) 
                                        (fun i : nat => true) 
                                        (S O) times
                                        (fun i : nat => plus i (S O))))
                                  (sym_eq_minus_body_S n1
                                     (fun y : nat -> nat =>
                                      eq nat (times (S n1) (fact n1))
                                        (bigop nat 
                                           (y O) (fun i : nat => true) 
                                           (S O) times
                                           (fun i : nat => plus i (S O))))
                                     (sym_eq_match_nat_type_O nat 
                                        (S n1) (fun q : nat => minus n1 q)
                                        (fun y : nat =>
                                         eq nat (times (S n1) (fact n1))
                                           (bigop nat y 
                                              (fun i : nat => true) 
                                              (S O) times
                                              (fun i : nat => plus i (S O))))
                                        (eq_ind_r nat
                                           (times 
                                              (plus n1 (S O))
                                              (bigop nat n1
                                                 (fun i : nat => true) 
                                                 (S O) times
                                                 (fun i : nat => plus i (S O))))
                                           (fun x : nat =>
                                            eq nat (times (S n1) (fact n1)) x)
                                           (eq_ind nat 
                                              (S (plus n1 O))
                                              (fun x_1 : nat =>
                                               eq nat
                                                 (times (S n1) (fact n1))
                                                 (times x_1
                                                 (bigop nat n1
                                                 (fun i : nat => true) 
                                                 (S O) times
                                                 (fun i : nat => plus i (S O)))))
                                              (eq_ind nat n1
                                                 (fun x_1 : nat =>
                                                 eq nat
                                                 (times (S n1) (fact n1))
                                                 (times 
                                                 (S x_1)
                                                 (bigop nat n1
                                                 (fun i : nat => true) 
                                                 (S O) times
                                                 (fun i : nat => plus i (S O)))))
                                                 (eq_f nat nat 
                                                 (times (S n1)) 
                                                 (fact n1)
                                                 (bigop nat n1
                                                 (fun i : nat => true) 
                                                 (S O) times
                                                 (fun i : nat => plus i (S O)))
                                                 (eq_ind nat
                                                 (minus (S n1) (S O))
                                                 (fun x_1 : nat =>
                                                 eq nat 
                                                 (fact n1)
                                                 (bigop nat x_1
                                                 (fun i : nat => true) 
                                                 (S O) times
                                                 (fun i : nat => plus i (S O))))
                                                 Hind n1
                                                 (sym_eq_minus 
                                                 (S n1)
                                                 (fun y : nat -> nat =>
                                                 eq nat (y (S O)) n1)
                                                 (sym_eq_filter_nat_type_S
                                                 (nat -> nat) minus_body n1
                                                 (fun y : nat -> nat =>
                                                 eq nat (y (S O)) n1)
                                                 (sym_eq_minus_body_S n1
                                                 (fun y : nat -> nat =>
                                                 eq nat (y (S O)) n1)
                                                 (sym_eq_match_nat_type_S nat
                                                 (S n1)
                                                 (fun q : nat => minus n1 q)
                                                 O
                                                 (fun y : nat => eq nat y n1)
                                                 (rewrite_l nat n1
                                                 (fun __ : nat =>
                                                 eq nat __ n1) 
                                                 (refl nat n1) 
                                                 (minus n1 O) 
                                                 (minus_n_O n1))))))))
                                                 (plus n1 O) 
                                                 (plus_n_O n1))
                                              (plus n1 (S O))
                                              (plus_n_Sm n1 O))
                                           (bigop nat 
                                              (S n1) 
                                              (fun i : nat => true) 
                                              (S O) times
                                              (fun i : nat => plus i (S O)))
                                           (bigop_Strue nat n1
                                              (fun __ : nat => true) 
                                              (S O) times
                                              (fun __ : nat => plus __ (S O))
                                              (refl bool true)))))))))))
                (times (fact n1) (S n1)) (commutative_times (fact n1) (S n1))))))
    n.
Definition congruent_pi :
  forall (f : nat -> nat) (n p : nat),
  lt O p ->
  congruent
    (bigop nat n (fun i : nat => true) (S O) times (fun i : nat => f i))
    (bigop nat n (fun i : nat => true) (S O) times
       (fun i : nat => mod (f i) p)) p :=
  fun (f : nat -> nat) (n : nat) =>
  nat_ind
    (fun _x_365 : nat =>
     forall p : nat,
     lt O p ->
     congruent
       (bigop nat _x_365 (fun i : nat => true) (S O) times
          (fun i : nat => f i))
       (bigop nat _x_365 (fun i : nat => true) (S O) times
          (fun i : nat => mod (f i) p)) p)
    (fun p : nat =>
     sym_eq_bigop_O nat
       (fun
          y : (nat -> bool) ->
              nat -> (nat -> nat -> nat) -> (nat -> nat) -> nat =>
        lt O p ->
        congruent
          (bigop nat O (fun i : nat => true) (S O) times (fun i : nat => f i))
          (y (fun i : nat => true) (S O) times (fun i : nat => mod (f i) p))
          p)
       (sym_eq_bigop_body_O nat
          (fun
             y : (nat -> bool) ->
                 nat -> (nat -> nat -> nat) -> (nat -> nat) -> nat =>
           lt O p ->
           congruent
             (bigop nat O (fun i : nat => true) (S O) times
                (fun i : nat => f i))
             (y (fun i : nat => true) (S O) times
                (fun i : nat => mod (f i) p)) p)
          (eq_bigop_body_O nat
             (fun
                y : (nat -> bool) ->
                    nat -> (nat -> nat -> nat) -> (nat -> nat) -> nat =>
              lt O p ->
              congruent
                (bigop nat O (fun i : nat => true) 
                   (S O) times (fun i : nat => f i))
                (y (fun i : nat => true) (S O) times (fun i : nat => f i)) p)
             (eq_bigop_O nat
                (fun
                   y : (nat -> bool) ->
                       nat -> (nat -> nat -> nat) -> (nat -> nat) -> nat =>
                 lt O p ->
                 congruent
                   (bigop nat O (fun i : nat => true) 
                      (S O) times (fun i : nat => f i))
                   (y (fun i : nat => true) (S O) times (fun i : nat => f i))
                   p)
                (fun auto : lt O p =>
                 congruent_n_n
                   (bigop nat O (fun i : nat => true) 
                      (S O) times (fun i : nat => f i)) p)))))
    (fun (n1 : nat)
       (Hind : forall p : nat,
               lt O p ->
               congruent
                 (bigop nat n1 (fun i : nat => true) 
                    (S O) times (fun i : nat => f i))
                 (bigop nat n1 (fun i : nat => true) 
                    (S O) times (fun i : nat => mod (f i) p)) p) 
       (p : nat) (posp : lt O p) =>
     eq_ind_r nat
       (times (f n1)
          (bigop nat n1 (fun i : nat => true) (S O) times
             (fun i : nat => f i)))
       (fun x : nat =>
        congruent x
          (bigop nat (S n1) (fun i : nat => true) 
             (S O) times (fun i : nat => mod (f i) p)) p)
       (sym_eq_bigop_S nat n1
          (fun
             y : (nat -> bool) ->
                 nat -> (nat -> nat -> nat) -> (nat -> nat) -> nat =>
           congruent
             (times (f n1)
                (bigop nat n1 (fun i : nat => true) 
                   (S O) times (fun i : nat => f i)))
             (y (fun i : nat => true) (S O) times
                (fun i : nat => mod (f i) p)) p)
          (sym_eq_bigop_body_S nat n1
             (fun
                y : (nat -> bool) ->
                    nat -> (nat -> nat -> nat) -> (nat -> nat) -> nat =>
              congruent
                (times (f n1)
                   (bigop nat n1 (fun i : nat => true) 
                      (S O) times (fun i : nat => f i)))
                (y (fun i : nat => true) (S O) times
                   (fun i : nat => mod (f i) p)) p)
             (sym_eq_match_bool_type_true nat
                (times (mod (f n1) p)
                   (bigop nat n1 (fun i : nat => true) 
                      (S O) times (fun i : nat => mod (f i) p)))
                (bigop nat n1 (fun i : nat => true) 
                   (S O) times (fun i : nat => mod (f i) p))
                (fun y : nat =>
                 congruent
                   (times (f n1)
                      (bigop nat n1 (fun i : nat => true) 
                         (S O) times (fun i : nat => f i))) y p)
                (congruent_times (f n1)
                   (bigop nat n1 (fun i : nat => true) 
                      (S O) times (fun i : nat => f i)) 
                   (mod (f n1) p)
                   (bigop nat n1 (fun i : nat => true) 
                      (S O) times (fun i : nat => mod (f i) p)) p posp
                   (congruent_n_mod_n (f n1) p posp) 
                   (Hind p posp)))))
       (bigop nat (S n1) (fun i : nat => true) (S O) times
          (fun i : nat => f i))
       (bigop_Strue nat n1 (fun __ : nat => true) 
          (S O) times f (refl bool true))) n.
Definition congruent_exp_pred_SO :
  forall p a : nat,
  prime p -> Not (divides p a) -> congruent (exp a (pred p)) (S O) p :=
  fun (p a : nat) (primep : prime p) (ndiv : Not (divides p a)) =>
  divides_to_congruent (exp a (pred p)) (S O) p (prime_to_lt_O p primep)
    (lt_O_exp a (pred p)
       (match_nat_prop (fun __ : nat => Not (divides p __) -> lt O __)
          (fun _clearme : Not (divides p O) =>
           Not_ind (divides p O) (lt O O)
             (fun div0 : divides p O -> False =>
              falsity (lt O O)
                (div0
                   (quotient p O O
                      (rewrite_l nat O (fun __ : nat => eq nat O __)
                         (refl nat O) (times p O) 
                         (times_n_O p))))) _clearme)
          (fun (auto : nat) (auto' : Not (divides p (S auto))) => lt_O_S auto)
          a ndiv))
    (match_Or_prop (divides p (minus (exp a (pred p)) (S O)))
       (divides p (fact (pred p))) (divides p (minus (exp a (pred p)) (S O)))
       (fun auto : divides p (minus (exp a (pred p)) (S O)) => auto)
       (fun Hdiv : divides p (fact (pred p)) =>
        falsity (divides p (minus (exp a (pred p)) (S O)))
          (absurd (divides p (fact (pred p))) Hdiv
             (prime_to_not_divides_fact p primep (pred p)
                (le_S_S_to_le (S (pred p)) p
                   (eq_ind_r nat p (fun x : nat => le (S x) (S p))
                      (le_n (S p)) (S (pred p))
                      (S_pred p (prime_to_lt_O p primep)))))))
       (divides_times_to_divides p (minus (exp a (pred p)) (S O))
          (fact (pred p)) primep
          (eq_ind_r nat
             (times (fact (pred p)) (minus (exp a (pred p)) (S O)))
             (fun x : nat => divides p x)
             (eq_ind_r nat
                (minus (times (fact (pred p)) (exp a (pred p)))
                   (times (fact (pred p)) (S O)))
                (fun x : nat => divides p x)
                (eq_ind nat (fact (pred p))
                   (fun x_1 : nat =>
                    divides p
                      (minus (times (fact (pred p)) (exp a (pred p))) x_1))
                   (eq_ind_r nat
                      (bigop nat (minus (S (pred p)) (S O))
                         (fun i : nat => true) (S O) times
                         (fun i : nat => plus i (S O)))
                      (fun x : nat =>
                       divides p (minus (times x (exp a (pred p))) x))
                      (eq_ind_r nat
                         (times (exp a (pred p))
                            (bigop nat (minus (S (pred p)) (S O))
                               (fun i : nat => true) 
                               (S O) times (fun i : nat => plus i (S O))))
                         (fun x : nat =>
                          divides p
                            (minus x
                               (bigop nat (minus (S (pred p)) (S O))
                                  (fun i : nat => true) 
                                  (S O) times (fun i : nat => plus i (S O)))))
                         (eq_ind_r nat (minus (S (pred p)) (S O))
                            (fun x : nat =>
                             divides p
                               (minus
                                  (times (exp a x)
                                     (bigop nat (minus (S (pred p)) (S O))
                                        (fun i : nat => true) 
                                        (S O) times
                                        (fun i : nat => plus i (S O))))
                                  (bigop nat (minus (S (pred p)) (S O))
                                     (fun i : nat => true) 
                                     (S O) times
                                     (fun i : nat => plus i (S O)))))
                            (eq_ind_r nat
                               (bigop nat (minus (S (pred p)) (S O))
                                  (fun i : nat => true) 
                                  (S O) times
                                  (fun i : nat => times a (plus i (S O))))
                               (fun x : nat =>
                                divides p
                                  (minus x
                                     (bigop nat (minus (S (pred p)) (S O))
                                        (fun i : nat => true) 
                                        (S O) times
                                        (fun i : nat => plus i (S O)))))
                               (congruent_to_divides
                                  (bigop nat (minus (S (pred p)) (S O))
                                     (fun i : nat => true) 
                                     (S O) times
                                     (fun i : nat => times a (plus i (S O))))
                                  (bigop nat (minus (S (pred p)) (S O))
                                     (fun i : nat => true) 
                                     (S O) times
                                     (fun i : nat => plus i (S O))) p
                                  (prime_to_lt_O p primep)
                                  (transitive_congruent p
                                     (bigop nat (minus (S (pred p)) (S O))
                                        (fun i : nat => true) 
                                        (S O) times
                                        (fun i : nat =>
                                         times a (plus i (S O))))
                                     (bigop nat (minus (S (pred p)) (S O))
                                        (fun i : nat => true) 
                                        (S O) times
                                        (fun i : nat =>
                                         mod (times a (plus i (S O))) p))
                                     (bigop nat (minus (S (pred p)) (S O))
                                        (fun i : nat => true) 
                                        (S O) times
                                        (fun i : nat => plus i (S O)))
                                     (congruent_pi
                                        (fun m : nat =>
                                         times a (plus m (S O)))
                                        (minus (S (pred p)) (S O)) p
                                        (prime_to_lt_O p primep))
                                     (eq_ind nat
                                        (bigop nat 
                                           (minus (S (pred p)) (S O))
                                           (fun i : nat => true) 
                                           (S O) times
                                           (fun i : nat => plus i (S O)))
                                        (fun x_1 : nat =>
                                         congruent x_1
                                           (bigop nat
                                              (minus (S (pred p)) (S O))
                                              (fun i : nat => true) 
                                              (S O) times
                                              (fun i : nat => plus i (S O)))
                                           p)
                                        (congruent_n_n
                                           (bigop nat
                                              (minus (S (pred p)) (S O))
                                              (fun i : nat => true) 
                                              (S O) times
                                              (fun i : nat => plus i (S O)))
                                           p)
                                        (bigop nat 
                                           (minus (S (pred p)) (S O))
                                           (fun i : nat => true) 
                                           (S O) times
                                           (fun i : nat =>
                                            mod (times a (plus i (S O))) p))
                                        (eq_ind_r nat
                                           (bigop nat 
                                              (S (pred p))
                                              (fun i : nat =>
                                               andb (leb (S O) i) true) 
                                              (S O) times 
                                              (fun i : nat => i))
                                           (fun x : nat =>
                                            eq nat x
                                              (bigop nat
                                                 (minus (S (pred p)) (S O))
                                                 (fun i : nat => true) 
                                                 (S O) times
                                                 (fun i : nat =>
                                                 mod 
                                                 (times a (plus i (S O))) p)))
                                           (eq_ind_r nat
                                              (bigop nat 
                                                 (S (pred p))
                                                 (fun i : nat =>
                                                 andb (leb (S O) i) true)
                                                 (S O) times
                                                 (fun i : nat =>
                                                 mod (times a i) p))
                                              (fun x : nat =>
                                               eq nat
                                                 (bigop nat 
                                                 (S (pred p))
                                                 (fun i : nat =>
                                                 andb (leb (S O) i) true)
                                                 (S O) times
                                                 (fun i : nat => i)) x)
                                              (sym_eq nat
                                                 (bigop nat 
                                                 (S (pred p))
                                                 (fun i : nat =>
                                                 andb (leb (S O) i) true)
                                                 (S O) times
                                                 (fun i : nat =>
                                                 mod (times a i) p))
                                                 (bigop nat 
                                                 (S (pred p))
                                                 (fun i : nat =>
                                                 andb (leb (S O) i) true)
                                                 (S O) times
                                                 (fun i : nat => i))
                                                 (bigop_iso 
                                                 (S (pred p)) 
                                                 (S (pred p))
                                                 (fun __ : nat =>
                                                 andb (leb (S O) __) true)
                                                 (fun __ : nat =>
                                                 andb (leb (S O) __) true)
                                                 (fun __ : nat =>
                                                 mod (times a __) p)
                                                 (fun __ : nat => __)
                                                 (fun 
                                                 (z : Prop)
                                                 (f : 
                                                 forall x : nat -> nat,
                                                 Ex 
                                                 (nat -> nat)
                                                 (fun k : nat -> nat =>
                                                 And
                                                 (And
                                                 (forall i : nat,
                                                 lt i (S (pred p)) ->
                                                 eq bool
                                                 (andb (leb (S O) i) true)
                                                 true ->
                                                 eq nat 
                                                 (mod (times a i) p) 
                                                 (x i))
                                                 (sub_hk x k 
                                                 (S (pred p)) 
                                                 (S (pred p))
                                                 (fun _0 : nat =>
                                                 andb (leb (S O) _0) true)
                                                 (fun _0 : nat =>
                                                 andb (leb (S O) _0) true)
                                                 (fun _0 : nat =>
                                                 mod (times a _0) p)
                                                 (fun _0 : nat => _0)))
                                                 (sub_hk k x 
                                                 (S (pred p)) 
                                                 (S (pred p))
                                                 (fun _0 : nat =>
                                                 andb (leb (S O) _0) true)
                                                 (fun _0 : nat =>
                                                 andb (leb (S O) _0) true)
                                                 (fun _0 : nat => _0)
                                                 (fun _0 : nat =>
                                                 mod (times a _0) p))) -> z)
                                                 =>
                                                 f
                                                 (fun i : nat =>
                                                 mod (times a i) p)
                                                 (fun 
                                                 (z0 : Prop)
                                                 (f2 : 
                                                 forall y : nat -> nat,
                                                 And
                                                 (And
                                                 (forall i : nat,
                                                 lt i (S (pred p)) ->
                                                 eq bool
                                                 (andb (leb (S O) i) true)
                                                 true ->
                                                 eq nat 
                                                 (mod (times a i) p)
                                                 (mod (times a i) p))
                                                 (sub_hk
                                                 (fun i : nat =>
                                                 mod (times a i) p) y
                                                 (S (pred p)) 
                                                 (S (pred p))
                                                 (fun _0 : nat =>
                                                 andb (leb (S O) _0) true)
                                                 (fun _0 : nat =>
                                                 andb (leb (S O) _0) true)
                                                 (fun _0 : nat =>
                                                 mod (times a _0) p)
                                                 (fun _0 : nat => _0)))
                                                 (sub_hk y
                                                 (fun i : nat =>
                                                 mod (times a i) p)
                                                 (S (pred p)) 
                                                 (S (pred p))
                                                 (fun _0 : nat =>
                                                 andb (leb (S O) _0) true)
                                                 (fun _0 : nat =>
                                                 andb (leb (S O) _0) true)
                                                 (fun _0 : nat => _0)
                                                 (fun _0 : nat =>
                                                 mod (times a _0) p)) -> z0)
                                                 =>
                                                 f2
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun i : nat =>
                                                 mod (times a i) p))
                                                 (fun 
                                                 (z1 : Prop)
                                                 (f0 : 
                                                 And
                                                 (forall i : nat,
                                                 lt i (S (pred p)) ->
                                                 eq bool
                                                 (andb (leb (S O) i) true)
                                                 true ->
                                                 eq nat 
                                                 (mod (times a i) p)
                                                 (mod (times a i) p))
                                                 (sub_hk
                                                 (fun i : nat =>
                                                 mod (times a i) p)
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun i : nat =>
                                                 mod (times a i) p))
                                                 (S (pred p)) 
                                                 (S (pred p))
                                                 (fun _0 : nat =>
                                                 andb (leb (S O) _0) true)
                                                 (fun _0 : nat =>
                                                 andb (leb (S O) _0) true)
                                                 (fun _0 : nat =>
                                                 mod (times a _0) p)
                                                 (fun _0 : nat => _0)) ->
                                                 sub_hk
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun i : nat =>
                                                 mod (times a i) p))
                                                 (fun i : nat =>
                                                 mod (times a i) p)
                                                 (S (pred p)) 
                                                 (S (pred p))
                                                 (fun _0 : nat =>
                                                 andb (leb (S O) _0) true)
                                                 (fun _0 : nat =>
                                                 andb (leb (S O) _0) true)
                                                 (fun _0 : nat => _0)
                                                 (fun _0 : nat =>
                                                 mod (times a _0) p) -> z1)
                                                 =>
                                                 f0
                                                 (fun 
                                                 (z2 : Prop)
                                                 (f20 : 
                                                 (forall x : nat,
                                                 lt x (S (pred p)) ->
                                                 eq bool
                                                 (andb (leb (S O) x) true)
                                                 true ->
                                                 eq nat 
                                                 (mod (times a x) p)
                                                 (mod (times a x) p)) ->
                                                 sub_hk
                                                 (fun i : nat =>
                                                 mod (times a i) p)
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun i : nat =>
                                                 mod (times a i) p))
                                                 (S (pred p)) 
                                                 (S (pred p))
                                                 (fun _0 : nat =>
                                                 andb (leb (S O) _0) true)
                                                 (fun _0 : nat =>
                                                 andb (leb (S O) _0) true)
                                                 (fun _0 : nat =>
                                                 mod (times a _0) p)
                                                 (fun _0 : nat => _0) -> z2)
                                                 =>
                                                 f20
                                                 (fun 
                                                 (i : nat)
                                                 (lti : lt i (S (pred p)))
                                                 (__ : 
                                                 eq bool
                                                 (andb (leb (S O) i) true)
                                                 true) =>
                                                 refl nat (mod (times a i) p))
                                                 (fun 
                                                 (i : nat)
                                                 (lti : lt i (S (pred p)))
                                                 (posi : 
                                                 eq bool
                                                 (andb (leb (S O) i) true)
                                                 true) 
                                                 (z3 : Prop)
                                                 (f3 : 
                                                 And
                                                 (lt 
                                                 (mod (times a i) p)
                                                 (S (pred p)))
                                                 (eq bool
                                                 (andb
                                                 (leb 
                                                 (S O) 
                                                 (mod (times a i) p)) true)
                                                 true) ->
                                                 eq nat
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun i0 : nat =>
                                                 mod (times a i0) p)
                                                 (mod (times a i) p)) i -> z3)
                                                 =>
                                                 f3
                                                 (fun 
                                                 (z4 : Prop)
                                                 (f4 : 
                                                 lt 
                                                 (mod (times a i) p)
                                                 (S (pred p)) ->
                                                 eq bool
                                                 (andb
                                                 (leb 
                                                 (S O) 
                                                 (mod (times a i) p)) true)
                                                 true -> z4) =>
                                                 f4
                                                 (eq_ind_r nat p
                                                 (fun x : nat =>
                                                 lt (mod (times a i) p) x)
                                                 (lt_mod_m_m 
                                                 (times a i) p
                                                 (prime_to_lt_O p primep))
                                                 (S (pred p))
                                                 (S_pred p
                                                 (prime_to_lt_O p primep)))
                                                 (eq_ind_r bool true
                                                 (fun x : bool =>
                                                 eq bool (andb x true) true)
                                                 (eq_match_bool_type_true
                                                 bool true false
                                                 (fun y : bool =>
                                                 eq bool (andb true true) y)
                                                 (refl bool (andb true true)))
                                                 (leb 
                                                 (S O) 
                                                 (mod (times a i) p))
                                                 (le_to_leb_true 
                                                 (S O) 
                                                 (mod (times a i) p)
                                                 (match_Or_prop
                                                 (lt O (mod (times a i) p))
                                                 (eq nat O
                                                 (mod (times a i) p))
                                                 (le 
                                                 (S O) 
                                                 (mod (times a i) p))
                                                 (fun
                                                 auto : 
                                                 lt O 
                                                 (mod (times a i) p) => auto)
                                                 (fun
                                                 H : 
                                                 eq nat O 
                                                 (mod (times a i) p) =>
                                                 falsity
                                                 (le 
                                                 (S O) 
                                                 (mod (times a i) p))
                                                 (absurd
                                                 (divides p (times a i))
                                                 (mod_O_to_divides p
                                                 (times a i)
                                                 (prime_to_lt_O p primep)
                                                 (sym_eq nat O
                                                 (mod (times a i) p) H))
                                                 (not_to_not
                                                 (divides p (times a i))
                                                 (divides p a)
                                                 (fun
                                                 Hdiv : divides p (times a i)
                                                 =>
                                                 match_Or_prop 
                                                 (divides p a) 
                                                 (divides p i) 
                                                 (divides p a)
                                                 (fun auto : divides p a =>
                                                 auto)
                                                 (fun divpi : divides p i =>
                                                 falsity 
                                                 (divides p a)
                                                 (absurd 
                                                 (lt i (S (pred p))) lti
                                                 (le_to_not_lt 
                                                 (S (pred p)) i
                                                 (eq_ind_r nat p
                                                 (fun x : nat => le x i)
                                                 (divides_to_le p i
                                                 (leb_true_to_le 
                                                 (S O) i
                                                 (andb_true_l 
                                                 (leb (S O) i) true posi))
                                                 divpi) 
                                                 (S (pred p))
                                                 (S_pred p
                                                 (prime_to_lt_O p primep))))))
                                                 (divides_times_to_divides p
                                                 a i primep Hdiv)) ndiv)))
                                                 (le_to_or_lt_eq O
                                                 (mod (times a i) p)
                                                 (le_O_n (mod (times a i) p)))))))
                                                 (invert_permut_f
                                                 (fun i0 : nat =>
                                                 mod (times a i0) p) 
                                                 (pred p) i
                                                 (le_S_S_to_le i (pred p) lti)
                                                 (match_And_prop
                                                 (forall i1 : nat,
                                                 le i1 (pred p) ->
                                                 le 
                                                 (mod (times a i1) p)
                                                 (pred p))
                                                 (injn
                                                 (fun n : nat =>
                                                 mod (times a n) p) 
                                                 (pred p))
                                                 (injn
                                                 (fun i0 : nat =>
                                                 mod (times a i0) p) 
                                                 (pred p))
                                                 (fun
                                                 (auto : 
                                                 forall i0 : nat,
                                                 le i0 (pred p) ->
                                                 le 
                                                 (mod (times a i0) p)
                                                 (pred p))
                                                 (auto' : 
                                                 injn
                                                 (fun n : nat =>
                                                 mod (times a n) p) 
                                                 (pred p)) => auto')
                                                 (permut_mod p a primep ndiv)))))
                                                 (match_And_prop
                                                 (forall i : nat,
                                                 le i (pred p) ->
                                                 le
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun n : nat =>
                                                 mod (times a n) p) i)
                                                 (pred p))
                                                 (injn
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun n : nat =>
                                                 mod (times a n) p)) 
                                                 (pred p))
                                                 (sub_hk
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun i : nat =>
                                                 mod (times a i) p))
                                                 (fun i : nat =>
                                                 mod (times a i) p)
                                                 (S (pred p)) 
                                                 (S (pred p))
                                                 (fun _0 : nat =>
                                                 andb (leb (S O) _0) true)
                                                 (fun _0 : nat =>
                                                 andb (leb (S O) _0) true)
                                                 (fun _0 : nat => _0)
                                                 (fun _0 : nat =>
                                                 mod (times a _0) p))
                                                 (fun
                                                 (le_invert_permut : 
                                                 forall i : nat,
                                                 le i (pred p) ->
                                                 le
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun n : nat =>
                                                 mod (times a n) p) i)
                                                 (pred p))
                                                 (inj_inv_permut : 
                                                 injn
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun n : nat =>
                                                 mod (times a n) p)) 
                                                 (pred p)) 
                                                 (i : nat)
                                                 (lti : lt i (S (pred p)))
                                                 (posi : 
                                                 eq bool
                                                 (andb (leb (S O) i) true)
                                                 true) 
                                                 (z2 : Prop)
                                                 (f5 : 
                                                 And
                                                 (lt
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun i0 : nat =>
                                                 mod (times a i0) p) i)
                                                 (S (pred p)))
                                                 (eq bool
                                                 (andb
                                                 (leb 
                                                 (S O)
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun i0 : nat =>
                                                 mod (times a i0) p) i)) true)
                                                 true) ->
                                                 eq nat
                                                 (mod
                                                 (times a
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun i0 : nat =>
                                                 mod (times a i0) p) i)) p) i ->
                                                 z2) =>
                                                 f5
                                                 (fun 
                                                 (z3 : Prop)
                                                 (f6 : 
                                                 lt
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun i0 : nat =>
                                                 mod (times a i0) p) i)
                                                 (S (pred p)) ->
                                                 eq bool
                                                 (andb
                                                 (leb 
                                                 (S O)
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun i0 : nat =>
                                                 mod (times a i0) p) i)) true)
                                                 true -> z3) =>
                                                 f6
                                                 (le_S_S
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun i0 : nat =>
                                                 mod (times a i0) p) i)
                                                 (pred p)
                                                 (le_invert_permut i
                                                 (le_S_S_to_le i (pred p) lti)))
                                                 (eq_ind_r bool true
                                                 (fun x : bool =>
                                                 eq bool (andb x true) true)
                                                 (eq_match_bool_type_true
                                                 bool true false
                                                 (fun y : bool =>
                                                 eq bool (andb true true) y)
                                                 (refl bool (andb true true)))
                                                 (leb 
                                                 (S O)
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun i0 : nat =>
                                                 mod (times a i0) p) i))
                                                 (le_to_leb_true 
                                                 (S O)
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun i0 : nat =>
                                                 mod (times a i0) p) i)
                                                 (match_Or_prop
                                                 (lt O
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun i0 : nat =>
                                                 mod (times a i0) p) i))
                                                 (eq nat O
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun i0 : nat =>
                                                 mod (times a i0) p) i))
                                                 (le 
                                                 (S O)
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun i0 : nat =>
                                                 mod (times a i0) p) i))
                                                 (fun
                                                 auto : 
                                                 lt O
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun i0 : nat =>
                                                 mod (times a i0) p) i) =>
                                                 auto)
                                                 (fun
                                                 H : 
                                                 eq nat O
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun i0 : nat =>
                                                 mod (times a i0) p) i) =>
                                                 falsity
                                                 (le 
                                                 (S O)
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun i0 : nat =>
                                                 mod (times a i0) p) i))
                                                 (eq_ind_r nat O
                                                 (fun x : nat =>
                                                 eq nat x
                                                 (mod
                                                 (times a
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun i0 : nat =>
                                                 mod (times a i0) p) i)) p) ->
                                                 False)
                                                 (eq_ind_r nat i
                                                 (fun x : nat =>
                                                 eq nat O x -> False)
                                                 (fun eq0i : eq nat O i =>
                                                 eq_ind nat O
                                                 (fun x_1 : nat =>
                                                 eq bool
                                                 (andb (leb (S O) x_1) true)
                                                 true -> False)
                                                 (sym_eq_leb 
                                                 (S O)
                                                 (fun y : nat -> bool =>
                                                 eq bool 
                                                 (andb (y O) true) true ->
                                                 False)
                                                 (sym_eq_filter_nat_type_S
                                                 (nat -> bool) leb_body O
                                                 (fun y : nat -> bool =>
                                                 eq bool 
                                                 (andb (y O) true) true ->
                                                 False)
                                                 (sym_eq_leb_body_S O
                                                 (fun y : nat -> bool =>
                                                 eq bool 
                                                 (andb (y O) true) true ->
                                                 False)
                                                 (sym_eq_match_nat_type_O
                                                 bool false
                                                 (fun q : nat => leb O q)
                                                 (fun y : bool =>
                                                 eq bool (andb y true) true ->
                                                 False)
                                                 (sym_eq_match_bool_type_false
                                                 bool true false
                                                 (fun y : bool =>
                                                 eq bool y true -> False)
                                                 (fun H0 : eq bool false true
                                                 =>
                                                 eq_match_bool_type_true Prop
                                                 (forall P : Prop, P)
                                                 (forall P : Prop, P -> P)
                                                 (fun y : Prop => y)
                                                 (eq_match_bool_type_false
                                                 Prop
                                                 (match_bool_type Prop
                                                 (forall P : Prop, P -> P)
                                                 (forall P : Prop, P) true)
                                                 (match_bool_type Prop
                                                 (forall P : Prop, P)
                                                 (forall P : Prop, P -> P)
                                                 true) 
                                                 (fun y : Prop => y)
                                                 (bool_discr false true H0))
                                                 False)))))) i eq0i posi)
                                                 (mod
                                                 (times a
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun i0 : nat =>
                                                 mod (times a i0) p) i)) p)
                                                 (f_invert_permut
                                                 (fun i0 : nat =>
                                                 mod (times a i0) p) 
                                                 (pred p) i
                                                 (le_S_S_to_le i (pred p) lti)
                                                 (permut_mod p a primep ndiv)))
                                                 (mod (times a O) p)
                                                 (eq_ind nat O
                                                 (fun x_1 : nat =>
                                                 eq nat (mod x_1 p) O)
                                                 (rewrite_r nat O
                                                 (fun __ : nat => eq nat __ O)
                                                 (refl nat O) 
                                                 (mod O p) 
                                                 (mod_O_n p)) 
                                                 (times a O) 
                                                 (times_n_O a))
                                                 (eq_f nat nat
                                                 (fun i0 : nat =>
                                                 mod (times a i0) p) O
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun i0 : nat =>
                                                 mod (times a i0) p) i)
                                                 (rewrite_l nat O
                                                 (fun __ : nat => eq nat O __)
                                                 (refl nat O)
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun i0 : nat =>
                                                 mod (times a i0) p) i) H))))
                                                 (le_to_or_lt_eq O
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun i0 : nat =>
                                                 mod (times a i0) p) i)
                                                 (le_O_n
                                                 (invert_permut 
                                                 (pred p)
                                                 (fun i0 : nat =>
                                                 mod (times a i0) p) i)))))))
                                                 (f_invert_permut
                                                 (fun __ : nat =>
                                                 mod (times a __) p) 
                                                 (pred p) i
                                                 (le_S_S_to_le i (pred p) lti)
                                                 (permut_mod p a primep ndiv)))
                                                 (permut_invert_permut
                                                 (fun n : nat =>
                                                 mod (times a n) p) 
                                                 (pred p)
                                                 (permut_mod p a primep ndiv))))))))
                                              (bigop nat
                                                 (minus (S (pred p)) (S O))
                                                 (fun i : nat => true) 
                                                 (S O) times
                                                 (fun i : nat =>
                                                 mod 
                                                 (times a (plus i (S O))) p))
                                              (bigop_I_gen 
                                                 (S O) 
                                                 (S (pred p))
                                                 (fun __ : nat => true)
                                                 (fun __ : nat =>
                                                 mod (times a __) p)
                                                 (lt_O_S (pred p))))
                                           (bigop nat
                                              (minus (S (pred p)) (S O))
                                              (fun i : nat => true) 
                                              (S O) times
                                              (fun i : nat => plus i (S O)))
                                           (bigop_I_gen 
                                              (S O) 
                                              (S (pred p))
                                              (fun __ : nat => true)
                                              (fun __ : nat => __)
                                              (lt_O_S (pred p)))))))
                               (times (exp a (minus (S (pred p)) (S O)))
                                  (bigop nat (minus (S (pred p)) (S O))
                                     (fun i : nat => true) 
                                     (S O) times
                                     (fun i : nat => plus i (S O))))
                               (exp_pi_bc a (S O) 
                                  (S (pred p)) (fun __ : nat => __)))
                            (pred p)
                            (rewrite_r nat (minus (pred p) O)
                               (fun __ : nat => eq nat (pred p) __)
                               (rewrite_l nat (pred p)
                                  (fun __ : nat => eq nat (pred p) __)
                                  (refl nat (pred p)) 
                                  (minus (pred p) O) 
                                  (minus_n_O (pred p)))
                               (minus (S (pred p)) (S O))
                               (minus_S_S (pred p) O)))
                         (times
                            (bigop nat (minus (S (pred p)) (S O))
                               (fun i : nat => true) 
                               (S O) times (fun i : nat => plus i (S O)))
                            (exp a (pred p)))
                         (commutative_times
                            (bigop nat (minus (S (pred p)) (S O))
                               (fun i : nat => true) 
                               (S O) times (fun i : nat => plus i (S O)))
                            (exp a (pred p)))) (fact (pred p))
                      (eq_fact_pi_p (pred p))) (times (fact (pred p)) (S O))
                   (times_n_1 (fact (pred p))))
                (times (fact (pred p)) (minus (exp a (pred p)) (S O)))
                (distributive_times_minus (fact (pred p)) 
                   (exp a (pred p)) (S O)))
             (times (minus (exp a (pred p)) (S O)) (fact (pred p)))
             (commutative_times (minus (exp a (pred p)) (S O))
                (fact (pred p)))))).
