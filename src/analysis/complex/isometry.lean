/-
Copyright (c) 2021 François Sunatori. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde, Yakov Pechersky, Heather Macbeth, Kevin Buzzard, Greg Price, François Sunatori
-/
import analysis.complex.basic
import data.complex.exponential
import data.real.sqrt
import analysis.normed_space.linear_isometry

/-!
# Isometries of the Complex Plane

Classification of isometries in the complex plane.

## References

* [Isometries of the Complex Plane](http://helmut.knaust.info/mediawiki/images/b/b5/Iso.pdf)
-/

-- https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/linear_isometry_complex
-- https://github.com/leanprover-community/mathlib/pull/6923

open complex

local notation `|` x `|` := complex.abs x

@[simp]
lemma linear_isometry.id_apply (z : ℂ) : (linear_isometry.id : ℂ →ₗᵢ[ℝ] ℂ) z = z := rfl

@[simp]
lemma linear_isometry.id_to_linear_map : (linear_isometry.id.to_linear_map : ℂ →ₗ[ℝ] ℂ) = linear_map.id := rfl

lemma hf_re (f : ℂ →ₗᵢ[ℝ] ℂ) (h₃ : ∀ z, z + conj z = f z + conj (f z)) (z : ℂ) : (f z).re = z.re :=
begin
  simpa [ext_iff, add_re, add_im, conj_re, conj_im, ←two_mul,
         (show (2 : ℝ) ≠ 0, by simp [two_ne_zero'])] using (h₃ z).symm
end

lemma hf_im {f : ℂ →ₗᵢ[ℝ] ℂ} (h₁ :  ∀ z, |f z| = |z|) (h₂ : ∀ z, (f z).re = z.re) (z : ℂ) :
  (f z).im = z.im ∨ (f z).im = -z.im :=
begin
  specialize h₁ z,
  simp [complex.abs] at h₁,
  rwa [real.sqrt_inj (norm_sq_nonneg _) (norm_sq_nonneg _), norm_sq_apply (f z), norm_sq_apply z,
    h₂, add_left_cancel_iff, mul_self_eq_mul_self_iff] at h₁,
end

lemma linear_isometry.l0 {f : ℂ →ₗᵢ[ℝ] ℂ} (h : f 1 = 1) (z : ℂ) : ∥f z - 1∥ = ∥z - 1∥ := begin
  rw ←linear_isometry.norm_map f (z - 1),
  rw linear_isometry.map_sub,
  rw h,
end

lemma linear_isometry.l1 {f : ℂ →ₗᵢ[ℝ] ℂ} (h : f 1 = 1) (z : ℂ) : z + conj z = f z + conj (f z) :=
begin
  have := linear_isometry.l0 h z,
  apply_fun λ x, x ^ 2 at this,
  simp only [norm_eq_abs, ←norm_sq_eq_abs] at this,
  rw [←of_real_inj, ←mul_conj, ←mul_conj] at this,
  rw [conj.map_sub, conj.map_sub] at this,
  simp only [sub_mul, mul_sub, one_mul, mul_one] at this,
  rw [mul_conj, norm_sq_eq_abs, ←norm_eq_abs, linear_isometry.norm_map] at this,
  rw [mul_conj, norm_sq_eq_abs, ←norm_eq_abs] at this,
  simp only [sub_sub, sub_right_inj, mul_one, of_real_pow, ring_hom.map_one, norm_eq_abs] at this,
  simp only [add_sub, sub_left_inj] at this,
  rw [add_comm, ←this, add_comm],
end

lemma linear_isometry.re {f : ℂ →ₗᵢ[ℝ] ℂ} (h : f 1 = 1) (z : ℂ) : (f z).re = z.re := begin
  apply hf_re,
  intro z,
  apply linear_isometry.l1 h,
end

lemma linear_isometry_complex_aux (f : ℂ →ₗᵢ[ℝ] ℂ) (h : f 1 = 1) :
  (∀ z, f z = z) ∨ (∀ z, f z = conj z) := by {
  have h0 : f I = I ∨ f I = -I,
  { have : |f I| = 1,
    { rw [←norm_eq_abs, linear_isometry.norm_map, norm_eq_abs, abs_I] },
    simp only [ext_iff, ←and_or_distrib_left, neg_re, I_re, neg_im, neg_zero],
    split,
    { rw ←I_re,
      rw linear_isometry.re h },
    { apply hf_im,
      { intro z, rw [←norm_eq_abs, ←norm_eq_abs, linear_isometry.norm_map] },
      { intro z, rw linear_isometry.re h, } } },
  refine or.imp (λ h1, _) (λ h1 z, _) h0,
  { suffices : f.to_linear_map = linear_isometry.id.to_linear_map,
    { simp [this, ←linear_isometry.coe_to_linear_map, linear_map.id_apply] },
    apply is_basis.ext is_basis_one_I,
    intro i,
    fin_cases i,
    { simp [h] },
    { simp only [matrix.head_cons, linear_isometry.coe_to_linear_map,
        linear_isometry.id_to_linear_map, linear_map.id_coe, id.def, matrix.cons_val_one],
      exact h1, } },
  { suffices : f.to_linear_map = conj_li.to_linear_map,
    { rw [←linear_isometry.coe_to_linear_map, this],
      simp only [linear_isometry.coe_to_linear_map],
      refl },
    apply is_basis.ext is_basis_one_I,
    intro i,
    fin_cases i,
    { simp only [h, linear_isometry.coe_to_linear_map, matrix.cons_val_zero],
      change 1 = conj 1,
      ext; simp },
    { simp only [matrix.head_cons, linear_isometry.coe_to_linear_map,
        linear_isometry.id_to_linear_map, linear_map.id_coe, id.def, matrix.cons_val_one],
      change f I = conj I,
      rw conj_I,
      exact h1, } },
}

lemma linear_isometry_complex (f : ℂ →ₗᵢ[ℝ] ℂ) :
  ∃ a : ℂ, |a| = 1 ∧ ((∀ z, f z = a * z) ∨ (∀ z, f z = a * conj z)) := by {
  let a := f 1,
  use a,
  split,
    {
      change ∥a∥ = 1,
      simp only [a],
      rw linear_isometry.norm_map,
      simp,
    },
    {
      let g : ℂ →ₗᵢ[ℝ] ℂ :=
        { to_fun := λ z, a⁻¹ * f z,
          map_add' := by {
            intros x y,
            rw linear_isometry.map_add,
            rw mul_add,
          },
          map_smul' := by {
            intros m x,
            rw linear_isometry.map_smul,
            rw algebra.mul_smul_comm,
          },
          norm_map' := by {
            intros x,
            simp,
            change ∥f 1∥⁻¹ * ∥f x∥ = ∥x∥,
            iterate 2 { rw linear_isometry.norm_map },
            simp,
          },
        },
      have hg0 : g 0 = 0 := g.map_zero,
      have hg1 : g 1 = 1 := by {
        change a⁻¹ * a = 1,
        rw inv_mul_cancel,
        rw ← norm_sq_pos,
        rw norm_sq_eq_abs,
        change 0 < ∥a∥ ^ 2,
        rw linear_isometry.norm_map,
        simp,
        apply zero_lt_one,
      },
      have h : (∀ z, g z = z) ∨ (∀ z, g z = conj z) := linear_isometry_complex_aux g hg1,
      change (∀ z, a⁻¹ * f z = z) ∨ (∀ z, a⁻¹ * f z = conj z) at h,
      have ha : a ≠ 0 := by {
        rw ← norm_sq_pos,
        rw norm_sq_eq_abs,
        change 0 < ∥a∥ ^ 2,
        rw linear_isometry.norm_map,
        simp,
        apply zero_lt_one,
      },
      have ha_inv : a⁻¹ ≠ 0 := by {
        exact inv_ne_zero ha,
      },
      conv in (_ = _) {
        rw ← mul_right_inj' ha_inv, rw ← mul_assoc, rw inv_mul_cancel ha, rw one_mul,
      },
      conv {
        congr,
        skip,
        find (_ = _) {
          rw ← mul_right_inj' ha_inv, rw ← mul_assoc, rw inv_mul_cancel ha, rw one_mul,
        }
      },
      exact h,
    },
}
