/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import linear_algebra.free_module
import linear_algebra.matrix.basis
import linear_algebra.matrix.diagonal
import linear_algebra.matrix.to_linear_equiv
import linear_algebra.matrix.reindex
import linear_algebra.multilinear
import linear_algebra.dual
import ring_theory.algebra_tower
import ring_theory.matrix_algebra

/-!
# Determinant of families of vectors

This file defines the determinant of an endomorphism, and of a family of vectors
with respect to some basis. For the determinant of a matrix, see the file
`linear_algebra.matrix.determinant`.

## Main definitions

In the list below, and in all this file, `R` is a commutative ring (semiring
is sometimes enough), `M` and its variations are `R`-modules, `ι`, `κ`, `n` and `m` are finite
types used for indexing.

 * `basis.det`: the determinant of a family of vectors with respect to a basis,
   as a multilinear map
 * `linear_map.det`: the determinant of an endomorphism `f : End R M` as a
   multiplicative homomorphism (if `M` does not have a finite `R`-basis, the
   result is `1` instead)

## Tags

basis, det, determinant
-/

noncomputable theory

open_locale big_operators
open_locale matrix

open linear_map
open submodule

universes u v w

open linear_map matrix

variables {R : Type*} [comm_ring R]
variables {M : Type*} [add_comm_group M] [module R M]
variables {M' : Type*} [add_comm_group M'] [module R M']
variables {ι : Type*} [decidable_eq ι] [fintype ι]
variables (e : basis ι R M)

section conjugate

variables {A : Type*} [integral_domain A]
variables {m n : Type*} [fintype m] [fintype n]

/-- If `R^m` and `R^n` are linearly equivalent, then `m` and `n` are also equivalent. -/
def equiv_of_pi_lequiv_pi {R : Type*} [integral_domain R]
  (e : (m → R) ≃ₗ[R] (n → R)) : m ≃ n :=
basis.index_equiv (basis.of_equiv_fun e.symm) (pi.basis_fun _ _)

/-- If `M` and `M'` are each other's inverse matrices, they are square matrices up to
equivalence of types. -/
def matrix.equiv_of_inv [decidable_eq m] [decidable_eq n]
  {M : matrix m n A} {M' : matrix n m A}
  (hMM' : M ⬝ M' = 1) (hM'M : M' ⬝ M = 1) :
  m ≃ n :=
let e : (m → A) ≃ₗ[A] (n → A) :=
{ to_fun := matrix.to_lin' M',
  inv_fun := M.to_lin',
  left_inv := λ x, by rw [← matrix.to_lin'_mul_apply, hMM', matrix.to_lin'_one, id_apply],
  right_inv := λ x, by rw [← matrix.to_lin'_mul_apply, hM'M, matrix.to_lin'_one, id_apply],
  .. matrix.to_lin' M' } in
equiv_of_pi_lequiv_pi e

/-- If `M'` is a two-sided inverse for `M` (indexed differently), `det (M ⬝ N ⬝ M') = det N`. -/
lemma matrix.det_conjugate
  [decidable_eq m] [decidable_eq n]
  {M : matrix m n A} {M' : matrix n m A} {N : matrix n n A}
  (hMM' : M ⬝ M' = 1) (hM'M : M' ⬝ M = 1) :
  det (M ⬝ N ⬝ M') = det N :=
begin
  letI := classical.dec_eq A,
  -- Although `m` and `n` are different a priori, we will show they have the same cardinality.
  -- This turns the problem into one for square matrices, which is easy.
  let e : m ≃ n := matrix.equiv_of_inv hMM' hM'M,
  have : det (matrix.reindex_linear_equiv e (equiv.refl _) M ⬝ N ⬝
              matrix.reindex_linear_equiv (equiv.refl _) e M') =
         det N,
  { rw [det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul, ← matrix.reindex_linear_equiv_mul,
        matrix.reindex_linear_equiv_refl_refl, hM'M, linear_equiv.refl_apply, det_one, one_mul] },
  convert this,
  rw [← matrix.det_reindex_linear_equiv_self e (M ⬝ N ⬝ M'),
      matrix.reindex_linear_equiv_mul e (equiv.refl n) e,
      matrix.reindex_linear_equiv_mul e (equiv.refl n) (equiv.refl n),
      matrix.reindex_linear_equiv_refl_refl, linear_equiv.refl_apply]
end

end conjugate

namespace linear_map

/-! ### Determinant of a linear map -/

variables {A : Type*} [integral_domain A] [module A M]
variables {κ : Type*} [fintype κ]

/-- The determinant of `linear_map.to_matrix` does not depend on the choice of basis. -/
lemma det_to_matrix_eq_det_to_matrix [decidable_eq κ]
  (b : basis ι A M) (c : basis κ A M) (f : M →ₗ[A] M) :
  det (linear_map.to_matrix b b f) = det (linear_map.to_matrix c c f) :=
by rw [← linear_map_to_matrix_mul_basis_to_matrix c b c,
       ← basis_to_matrix_mul_linear_map_to_matrix b c b,
       matrix.det_conjugate]; rw [basis.to_matrix_mul_to_matrix, basis.to_matrix_self]

/-- The determinant of an endomorphism given a basis.

See `linear_map.det` for a version that populates the basis non-computably.
-/
def det_aux : trunc (basis ι A M) → (M →ₗ[A] M) →* A :=
trunc.lift
  (λ b : basis ι A M,
    (monoid_hom.of (matrix.det)).comp (to_matrix_alg_equiv b : (M →ₗ[A] M) →* matrix ι ι A))
  (λ b c, monoid_hom.ext $ det_to_matrix_eq_det_to_matrix b c)

/-- Unfold lemma for `det_aux`.

See also `det_aux_def'` which allows you to vary the basis.
-/
lemma det_aux_def (b : basis ι A M) (f : M →ₗ[A] M) :
  linear_map.det_aux (trunc.mk b) f = matrix.det (linear_map.to_matrix b b f) :=
rfl

attribute [irreducible] linear_map.det_aux

lemma det_aux_def' {ι' : Type*} [fintype ι'] [decidable_eq ι']
  (tb : trunc $ basis ι A M) (b' : basis ι' A M) (f : M →ₗ[A] M) :
  linear_map.det_aux tb f = matrix.det (linear_map.to_matrix b' b' f) :=
by { apply trunc.induction_on tb, intro b, rw [det_aux_def, det_to_matrix_eq_det_to_matrix b b'] }

@[simp]
lemma det_aux_id (b : trunc $ basis ι A M) : linear_map.det_aux b (linear_map.id) = 1 :=
(linear_map.det_aux b).map_one

@[simp]
lemma det_aux_comp (b : trunc $ basis ι A M) (f g : M →ₗ[A] M) :
  linear_map.det_aux b (f.comp g) = linear_map.det_aux b f * linear_map.det_aux b g :=
(linear_map.det_aux b).map_mul f g

section
open_locale classical

/-- The determinant of an endomorphism independent of basis.

If there is no finite basis on `M`, the result is `1` instead.
-/
protected def det : (M →ₗ[A] M) →* A :=
if H : ∃ (s : set M) (b : basis s A M), s.finite
then @linear_map.det_aux _ _ _ _ H.some_spec.some_spec.some _ _ _ (trunc.mk H.some_spec.some)
else 1

lemma coe_det [decidable_eq M] : ⇑(linear_map.det : (M →ₗ[A] M) →* A) =
  if H : ∃ (s : set M) (b : basis s A M), s.finite
  then @linear_map.det_aux _ _ _ _ H.some_spec.some_spec.some _ _ _ (trunc.mk H.some_spec.some)
  else 1 :=
by { ext, unfold linear_map.det,
     split_ifs,
     { congr }, -- use the correct `decidable_eq` instance
     refl }

end

attribute [irreducible] linear_map.det

-- Auxiliary lemma, the `simp` normal form goes in the other direction
-- (using `linear_map.det_to_matrix`)
lemma det_eq_det_to_matrix_of_finite_set [decidable_eq M]
  {s : set M} (b : basis s A M) (hs : fintype s) (f : M →ₗ[A] M) :
  f.det = matrix.det (linear_map.to_matrix b b f) :=
have ∃ (s : set M) (b : basis s A M), s.finite,
from ⟨s, b, ⟨hs⟩⟩,
by rw [linear_map.coe_det, dif_pos, det_aux_def' _ b]; assumption

@[simp] lemma det_to_matrix
  (b : basis ι A M) (f : M →ₗ[A] M) :
  matrix.det (to_matrix b b f) = f.det :=
by { haveI := classical.dec_eq M,
     rw [det_eq_det_to_matrix_of_finite_set b.reindex_range (set.fintype_range _),
         det_to_matrix_eq_det_to_matrix b] }

@[simp]
lemma det_comp (f g : M →ₗ[A] M) : (f.comp g).det = f.det * g.det :=
linear_map.det.map_mul f g

@[simp]
lemma det_id : (linear_map.id : M →ₗ[A] M).det = 1 :=
linear_map.det.map_one

lemma det_zero {ι : Type*} [fintype ι] [nonempty ι] (b : basis ι A M) :
  linear_map.det (0 : M →ₗ[A] M) = 0 :=
by { haveI := classical.dec_eq ι,
     rw [← det_to_matrix b, linear_equiv.map_zero, det_zero],
     assumption }

end linear_map

-- Cannot be stated using `linear_map.det` because `f` is not an endomorphism.
lemma linear_equiv.is_unit_det (f : M ≃ₗ[R] M') (v : basis ι R M) (v' : basis ι R M') :
  is_unit (linear_map.to_matrix v v' f).det :=
begin
  apply is_unit_det_of_left_inverse,
  simpa using (linear_map.to_matrix_comp v v' v f.symm f).symm
end

/-- Builds a linear equivalence from a linear map whose determinant in some bases is a unit. -/
@[simps]
def linear_equiv.of_is_unit_det {f : M →ₗ[R] M'} {v : basis ι R M} {v' : basis ι R M'}
  (h : is_unit (linear_map.to_matrix v v' f).det) : M ≃ₗ[R] M' :=
{ to_fun := f,
  map_add' := f.map_add,
  map_smul' := f.map_smul,
  inv_fun := to_lin v' v (to_matrix v v' f)⁻¹,
  left_inv := λ x,
    calc to_lin v' v (to_matrix v v' f)⁻¹ (f x)
        = to_lin v v ((to_matrix v v' f)⁻¹ ⬝ to_matrix v v' f) x :
      by { rw [to_lin_mul v v' v, to_lin_to_matrix, linear_map.comp_apply] }
    ... = x : by simp [h],
  right_inv := λ x,
    calc f (to_lin v' v (to_matrix v v' f)⁻¹ x)
        = to_lin v' v' (to_matrix v v' f ⬝ (to_matrix v v' f)⁻¹) x :
      by { rw [to_lin_mul v' v v', linear_map.comp_apply, to_lin_to_matrix v v'] }
    ... = x : by simp [h] }

/-- The determinant of a family of vectors with respect to some basis, as an alternating
multilinear map. -/
def basis.det : alternating_map R M R ι :=
{ to_fun := λ v, det (e.to_matrix v),
  map_add' := begin
    intros v i x y,
    simp only [e.to_matrix_update, linear_equiv.map_add],
    apply det_update_column_add
  end,
  map_smul' := begin
    intros u i c x,
    simp only [e.to_matrix_update, algebra.id.smul_eq_mul, linear_equiv.map_smul],
    apply det_update_column_smul
  end,
  map_eq_zero_of_eq' := begin
    intros v i j h hij,
    rw [←function.update_eq_self i v, h, ←det_transpose, e.to_matrix_update,
        ←update_row_transpose, ←e.to_matrix_transpose_apply],
    apply det_zero_of_row_eq hij,
    rw [update_row_ne hij.symm, update_row_self],
  end }

lemma basis.det_apply (v : ι → M) : e.det v = det (e.to_matrix v) := rfl

lemma basis.det_self : e.det e = 1 :=
by simp [e.det_apply]

lemma is_basis.iff_det {v : ι → M} :
  linear_independent R v ∧ span R (set.range v) = ⊤ ↔ is_unit (e.det v) :=
begin
  split,
  { rintro ⟨hli, hspan⟩,
    set v' := basis.mk hli hspan with v'_eq,
    rw e.det_apply,
    convert linear_equiv.is_unit_det (linear_equiv.refl _ _) v' e using 2,
    ext i j,
    simp },
  { intro h,
    rw [basis.det_apply, basis.to_matrix_eq_to_matrix_constr] at h,
    set v' := basis.map e (linear_equiv.of_is_unit_det h) with v'_def,
    have : ⇑ v' = v,
    { ext i, rw [v'_def, basis.map_apply, linear_equiv.of_is_unit_det_apply, e.constr_basis] },
    rw ← this,
    exact ⟨v'.linear_independent, v'.span_eq⟩ },
end
