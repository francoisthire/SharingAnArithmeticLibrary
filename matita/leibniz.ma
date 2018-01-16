(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "basics/pts.ma".
include "basics/logic.ma".

definition leibniz (A:Type[0]) (x : A) (y:A) : Prop := \forall P. P x \to P y.

theorem from_leibniz : ∀A.∀x.∀y. leibniz A x y → x = y.
#A #x #y #P >(P (\lambda z. x = z)) @refl
qed.

theorem to_leibniz : ∀A.∀x.∀y. x = y → leibniz A x y.
#A #x #y #eq #P #h cases eq @h
qed.

theorem sym_leibniz : ∀A.∀x.∀y. leibniz A x y → leibniz A y x.
#A #x #y #H #P >(from_leibniz A x y H) #h @h
qed.
