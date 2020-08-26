/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.adjunction.basic
import category_theory.opposites

/-!
# Opposite adjunctions

This file contains constructions to relate adjunctions of functors to adjunctions of their
opposites.

## Tags
adjunction, opposite
-/

open category_theory

universes v₁ v₂ u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

namespace adjunction

/-- If `G.op` is adjoint to `F.op` then `F` is adjoint to `G`. -/
def adjoint_of_op_adjoint_op (F : C ⥤ D) (G : D ⥤ C) (h : G.op ⊣ F.op) : F ⊣ G :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
  ((h.hom_equiv (opposite.op Y) (opposite.op X)).trans (op_equiv _ _)).symm.trans (op_equiv _ _) }

/-- If `G` is adjoint to `F.op` then `F` is adjoint to `G.unop`. -/
def adjoint_unop_of_adjoint_op (F : C ⥤ D) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G ⊣ F.op) : F ⊣ G.unop :=
adjoint_of_op_adjoint_op F G.unop (h.of_nat_iso_left G.op_unop_iso.symm)

/-- If `G.op` is adjoint to `F` then `F.unop` is adjoint to `G`. -/
def unop_adjoint_of_op_adjoint (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : D ⥤ C) (h : G.op ⊣ F) : F.unop ⊣ G :=
adjoint_of_op_adjoint_op _ _ (h.of_nat_iso_right F.op_unop_iso.symm)

/-- If `G` is adjoint to `F` then `F.unop` is adjoint to `G.unop`. -/
def unop_adjoint_unop_of_adjoint (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G ⊣ F) : F.unop ⊣ G.unop :=
adjoint_unop_of_adjoint_op F.unop G (h.of_nat_iso_right F.op_unop_iso.symm)

/-- If `G` is adjoint to `F` then `F.op` is adjoint to `G.op`. -/
def op_adjoint_op_of_adjoint (F : C ⥤ D) (G : D ⥤ C) (h : G ⊣ F) : F.op ⊣ G.op :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
  (op_equiv _ Y).trans ((h.hom_equiv _ _).symm.trans (op_equiv X (opposite.op _)).symm) }

/-- If `G` is adjoint to `F.unop` then `F` is adjoint to `G.op`. -/
def adjoint_op_of_adjoint_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : D ⥤ C) (h : G ⊣ F.unop) : F ⊣ G.op :=
(op_adjoint_op_of_adjoint F.unop _ h).of_nat_iso_left F.op_unop_iso

/-- If `G.unop` is adjoint to `F` then `F.op` is adjoint to `G`. -/
def op_adjoint_of_unop_adjoint (F : C ⥤ D) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G.unop ⊣ F) : F.op ⊣ G :=
(op_adjoint_op_of_adjoint _ G.unop h).of_nat_iso_right G.op_unop_iso

/-- If `G.unop` is adjoint to `F.unop` then `F` is adjoint to `G`. -/
def adjoint_of_unop_adjoint_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G.unop ⊣ F.unop) : F ⊣ G :=
(adjoint_op_of_adjoint_unop _ _ h).of_nat_iso_right G.op_unop_iso

end adjunction
