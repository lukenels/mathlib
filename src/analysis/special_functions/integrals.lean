/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/
import measure_theory.interval_integral

/-!
# Integration of specific interval integrals

This file contains proofs of the integrals of various specific functions. This includes:
* Integrals of simple functions, such as `id`, `pow`, `exp`, `inv`
* Integrals of some trigonometric functions, such as `sin`, `cos`, `1 / (1 + x^2)`
* The integral of `cos x ^ 2 - sin x ^ 2`
* Reduction formulae for the integrals of `sin x ^ n` and `cos x ^ n` for `n ≥ 2`
* The computation of `∫ x in 0..π, sin x ^ n` as a product for even and odd `n` (used in proving the
  Wallis product for pi)

With these lemmas, many simple integrals can be computed by `simp` or `norm_num`.
See `test/integration.lean` for specific examples.

This file also contains some facts about the interval integrability of specific functions.

This file is still being developed.

## Tags

integrate, integration, integrable, integrability
-/

open real nat set finset
open_locale real big_operators
variables {a b : ℝ} (n : ℕ)

namespace interval_integral
open measure_theory
variables {f : ℝ → ℝ} {μ ν : measure ℝ} [locally_finite_measure μ] (c d : ℝ)

/-! ### Interval integrability -/

@[simp]
lemma interval_integrable_pow : interval_integrable (λ x, x^n) μ a b :=
(continuous_pow n).interval_integrable a b

@[simp]
lemma interval_integrable_id : interval_integrable (λ x, x) μ a b :=
continuous_id.interval_integrable a b

@[simp]
lemma interval_integrable_const : interval_integrable (λ x, c) μ a b :=
continuous_const.interval_integrable a b

@[simp]
lemma interval_integrable.const_mul (h : interval_integrable f ν a b) :
  interval_integrable (λ x, c * f x) ν a b :=
by convert h.smul c

@[simp]
lemma interval_integrable.mul_const (h : interval_integrable f ν a b) :
  interval_integrable (λ x, f x * c) ν a b :=
by simp only [mul_comm, interval_integrable.const_mul c h]

@[simp]
lemma interval_integrable.div (h : interval_integrable f ν a b) :
  interval_integrable (λ x, f x / c) ν a b :=
interval_integrable.mul_const c⁻¹ h

lemma interval_integrable_one_div (h : ∀ x : ℝ, x ∈ interval a b → f x ≠ 0)
  (hf : continuous_on f (interval a b)) :
  interval_integrable (λ x, 1 / f x) μ a b :=
(continuous_on_const.div hf h).interval_integrable

@[simp]
lemma interval_integrable_inv (h : ∀ x : ℝ, x ∈ interval a b → f x ≠ 0)
  (hf : continuous_on f (interval a b)) :
  interval_integrable (λ x, (f x)⁻¹) μ a b :=
by simpa only [one_div] using interval_integrable_one_div h hf

@[simp]
lemma interval_integrable_exp : interval_integrable exp μ a b :=
continuous_exp.interval_integrable a b

@[simp]
lemma interval_integrable_sin : interval_integrable sin μ a b :=
continuous_sin.interval_integrable a b

@[simp]
lemma interval_integrable_cos : interval_integrable cos μ a b :=
continuous_cos.interval_integrable a b

lemma interval_integrable_one_div_one_add_sq : interval_integrable (λ x : ℝ, 1 / (1 + x^2)) μ a b :=
begin
  refine (continuous_const.div _ (λ x, _)).interval_integrable a b,
  { continuity },
  { nlinarith },
end

@[simp]
lemma interval_integrable_inv_one_add_sq : interval_integrable (λ x : ℝ, (1 + x^2)⁻¹) μ a b :=
by simpa only [one_div] using interval_integrable_one_div_one_add_sq

/-! ### Integral of a function scaled by a constant -/

@[simp]
lemma integral_const_mul : ∫ x in a..b, c * f x = c * ∫ x in a..b, f x :=
integral_smul c

@[simp]
lemma integral_mul_const : ∫ x in a..b, f x * c = (∫ x in a..b, f x) * c :=
by simp only [mul_comm, integral_const_mul]

@[simp]
lemma integral_div : ∫ x in a..b, f x / c = (∫ x in a..b, f x) / c :=
integral_mul_const c⁻¹

/-! ### Integrals of the form `c * ∫ x in a..b, f (c * x + d)` -/

@[simp]
lemma mul_integral_comp_mul_right : c * ∫ x in a..b, f (x * c) = ∫ x in a*c..b*c, f x :=
smul_integral_comp_mul_right f c

@[simp]
lemma mul_integral_comp_mul_left : c * ∫ x in a..b, f (c * x) = ∫ x in c*a..c*b, f x :=
smul_integral_comp_mul_left f c

@[simp]
lemma inv_mul_integral_comp_div : c⁻¹ * ∫ x in a..b, f (x / c) = ∫ x in a/c..b/c, f x :=
inv_smul_integral_comp_div f c

@[simp]
lemma mul_integral_comp_mul_add : c * ∫ x in a..b, f (c * x + d) = ∫ x in c*a+d..c*b+d, f x :=
smul_integral_comp_mul_add f c d

@[simp]
lemma mul_integral_comp_add_mul : c * ∫ x in a..b, f (d + c * x) = ∫ x in d+c*a..d+c*b, f x :=
smul_integral_comp_add_mul f c d

@[simp]
lemma inv_mul_integral_comp_div_add : c⁻¹ * ∫ x in a..b, f (x / c + d) = ∫ x in a/c+d..b/c+d, f x :=
inv_smul_integral_comp_div_add f c d

@[simp]
lemma inv_mul_integral_comp_add_div : c⁻¹ * ∫ x in a..b, f (d + x / c) = ∫ x in d+a/c..d+b/c, f x :=
inv_smul_integral_comp_add_div f c d

@[simp]
lemma mul_integral_comp_mul_sub : c * ∫ x in a..b, f (c * x - d) = ∫ x in c*a-d..c*b-d, f x :=
smul_integral_comp_mul_sub f c d

@[simp]
lemma mul_integral_comp_sub_mul : c * ∫ x in a..b, f (d - c * x) = ∫ x in d-c*b..d-c*a, f x :=
smul_integral_comp_sub_mul f c d

@[simp]
lemma inv_mul_integral_comp_div_sub : c⁻¹ * ∫ x in a..b, f (x / c - d) = ∫ x in a/c-d..b/c-d, f x :=
inv_smul_integral_comp_div_sub f c d

@[simp]
lemma inv_mul_integral_comp_sub_div : c⁻¹ * ∫ x in a..b, f (d - x / c) = ∫ x in d-b/c..d-a/c, f x :=
inv_smul_integral_comp_sub_div f c d

end interval_integral

open interval_integral

/-! ### Integrals of simple functions -/

@[simp]
lemma integral_pow : ∫ x in a..b, x ^ n = (b ^ (n + 1) - a ^ (n + 1)) / (n + 1) :=
begin
  have hderiv : deriv (λ x : ℝ, x ^ (n + 1) / (n + 1)) = λ x, x ^ n,
  { ext,
    have hne : (n + 1 : ℝ) ≠ 0 := by exact_mod_cast succ_ne_zero n,
    simp [mul_div_assoc, mul_div_cancel' _ hne] },
  rw integral_deriv_eq_sub' _ hderiv;
  norm_num [div_sub_div_same, continuous_on_pow],
end

@[simp]
lemma integral_id : ∫ x in a..b, x = (b ^ 2 - a ^ 2) / 2 :=
by simpa using integral_pow 1

@[simp]
lemma integral_one : ∫ x in a..b, (1 : ℝ) = b - a :=
by simp only [mul_one, smul_eq_mul, integral_const]

@[simp]
lemma integral_exp : ∫ x in a..b, exp x = exp b - exp a :=
by rw integral_deriv_eq_sub'; norm_num [continuous_on_exp]

@[simp]
lemma integral_inv (h : (0:ℝ) ∉ interval a b) : ∫ x in a..b, x⁻¹ = log (b / a) :=
begin
  have h' := λ x hx, ne_of_mem_of_not_mem hx h,
  rw [integral_deriv_eq_sub' _ deriv_log' (λ x hx, differentiable_at_log (h' x hx))
        (continuous_on_inv'.mono $ subset_compl_singleton_iff.mpr h),
      log_div (h' b right_mem_interval) (h' a left_mem_interval)],
end

@[simp]
lemma integral_inv_of_pos (ha : 0 < a) (hb : 0 < b) : ∫ x in a..b, x⁻¹ = log (b / a) :=
integral_inv $ not_mem_interval_of_lt ha hb

@[simp]
lemma integral_inv_of_neg (ha : a < 0) (hb : b < 0) : ∫ x in a..b, x⁻¹ = log (b / a) :=
integral_inv $ not_mem_interval_of_gt ha hb

lemma integral_one_div (h : (0:ℝ) ∉ interval a b) : ∫ x : ℝ in a..b, 1/x = log (b / a) :=
by simp only [one_div, integral_inv h]

lemma integral_one_div_of_pos (ha : 0 < a) (hb : 0 < b) : ∫ x : ℝ in a..b, 1/x = log (b / a) :=
by simp only [one_div, integral_inv_of_pos ha hb]

lemma integral_one_div_of_neg (ha : a < 0) (hb : b < 0) : ∫ x : ℝ in a..b, 1/x = log (b / a) :=
by simp only [one_div, integral_inv_of_neg ha hb]

@[simp]
lemma integral_sin : ∫ x in a..b, sin x = cos a - cos b :=
by rw integral_deriv_eq_sub' (λ x, -cos x); norm_num [continuous_on_sin]

@[simp]
lemma integral_cos : ∫ x in a..b, cos x = sin b - sin a :=
by rw integral_deriv_eq_sub'; norm_num [continuous_on_cos]

lemma integral_cos_sq_sub_sin_sq :
  ∫ x in a..b, cos x ^ 2 - sin x ^ 2 = sin b * cos b - sin a * cos a :=
by simpa only [sq, sub_eq_add_neg, neg_mul_eq_mul_neg] using integral_deriv_mul_eq_sub
  (λ x hx, has_deriv_at_sin x) (λ x hx, has_deriv_at_cos x) continuous_on_cos continuous_on_sin.neg

@[simp]
lemma integral_inv_one_add_sq : ∫ x : ℝ in a..b, (1 + x^2)⁻¹ = arctan b - arctan a :=
begin
  simp only [← one_div],
  refine integral_deriv_eq_sub' _ _ _ (continuous_const.div _ (λ x, _)).continuous_on,
  { norm_num },
  { norm_num },
  { continuity },
  { nlinarith },
end

lemma integral_one_div_one_add_sq : ∫ x : ℝ in a..b, 1 / (1 + x^2) = arctan b - arctan a :=
by simp only [one_div, integral_inv_one_add_sq]

/-! ### Integral of `sin x ^ n` -/

lemma integral_sin_pow_aux :
  ∫ x in a..b, sin x ^ (n + 2) = sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b
    + (n + 1) * (∫ x in a..b, sin x ^ n) - (n + 1) * ∫ x in a..b, sin x ^ (n + 2) :=
begin
  let C := sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b,
  have h : ∀ α β γ : ℝ, α * (β * α * γ) = β * (α * α * γ) := λ α β γ, by ring,
  have hu : ∀ x ∈ _, has_deriv_at (λ y, sin y ^ (n + 1)) ((n + 1) * cos x * sin x ^ n) x :=
    λ x hx, by simpa [mul_right_comm] using (has_deriv_at_sin x).pow,
  have hv : ∀ x ∈ interval a b, has_deriv_at (-cos) (sin x) x :=
    λ x hx, by simpa only [neg_neg] using (has_deriv_at_cos x).neg,
  have H := integral_mul_deriv_eq_deriv_mul hu hv _ _,
  calc  ∫ x in a..b, sin x ^ (n + 2)
      = ∫ x in a..b, sin x ^ (n + 1) * sin x : by simp only [pow_succ']
  ... = C + (n + 1) * ∫ x in a..b, cos x ^ 2 * sin x ^ n : by simp [H, h, sq]
  ... = C + (n + 1) * ∫ x in a..b, sin x ^ n - sin x ^ (n + 2) : by simp [cos_sq', sub_mul,
                                                                          ← pow_add, add_comm]
  ... = C + (n + 1) * (∫ x in a..b, sin x ^ n) - (n + 1) * ∫ x in a..b, sin x ^ (n + 2) :
    by rw [integral_sub, mul_sub, add_sub_assoc]; apply continuous.interval_integrable; continuity,
  all_goals { apply continuous.continuous_on, continuity },
end

/-- The reduction formula for the integral of `sin x ^ n` for any natural `n ≥ 2`. -/
lemma integral_sin_pow :
  ∫ x in a..b, sin x ^ (n + 2) = (sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b) / (n + 2)
    + (n + 1) / (n + 2) * ∫ x in a..b, sin x ^ n :=
begin
  have : (n : ℝ) + 2 ≠ 0 := by exact_mod_cast succ_ne_zero n.succ,
  field_simp,
  convert eq_sub_iff_add_eq.mp (integral_sin_pow_aux n),
  ring,
end

@[simp]
lemma integral_sin_sq : ∫ x in a..b, sin x ^ 2 = (sin a * cos a - sin b * cos b + b - a) / 2 :=
by field_simp [integral_sin_pow, add_sub_assoc]

theorem integral_sin_pow_odd :
  ∫ x in 0..π, sin x ^ (2 * n + 1) = 2 * ∏ i in range n, (2 * i + 2) / (2 * i + 3) :=
begin
  induction n with k ih, { norm_num },
  rw [prod_range_succ_comm, mul_left_comm, ← ih, mul_succ, integral_sin_pow],
  norm_cast,
  simp [-cast_add] with field_simps,
end

theorem integral_sin_pow_even :
  ∫ x in 0..π, sin x ^ (2 * n) = π * ∏ i in range n, (2 * i + 1) / (2 * i + 2) :=
begin
  induction n with k ih, { simp },
  rw [prod_range_succ_comm, mul_left_comm, ← ih, mul_succ, integral_sin_pow],
  norm_cast,
  simp [-cast_add] with field_simps,
end

lemma integral_sin_pow_pos : 0 < ∫ x in 0..π, sin x ^ n :=
begin
  rcases even_or_odd' n with ⟨k, (rfl | rfl)⟩;
  simp only [integral_sin_pow_even, integral_sin_pow_odd];
  refine mul_pos (by norm_num [pi_pos]) (prod_pos (λ n hn, div_pos _ _));
  norm_cast;
  linarith,
end

lemma integral_sin_pow_antimono :
  ∫ x in 0..π, sin x ^ (n + 1) ≤ ∫ x in 0..π, sin x ^ n :=
begin
  refine integral_mono_on _ _ pi_pos.le (λ x hx, _),
  { exact ((continuous_pow (n + 1)).comp continuous_sin).interval_integrable 0 π },
  { exact ((continuous_pow n).comp continuous_sin).interval_integrable 0 π },
  { refine pow_le_pow_of_le_one (sin_nonneg_of_mem_Icc _) (sin_le_one x) (nat.le_add_right n 1),
    rwa interval_of_le pi_pos.le at hx },
end

/-! ### Integral of `cos x ^ n` -/

lemma integral_cos_pow_aux :
  ∫ x in a..b, cos x ^ (n + 2) = cos b ^ (n + 1) * sin b - cos a ^ (n + 1) * sin a
    + (n + 1) * (∫ x in a..b, cos x ^ n) - (n + 1) * ∫ x in a..b, cos x ^ (n + 2) :=
begin
  let C := cos b ^ (n + 1) * sin b - cos a ^ (n + 1) * sin a,
  have h : ∀ α β γ : ℝ, α * (β * α * γ) = β * (α * α * γ) := λ α β γ, by ring,
  have hu : ∀ x ∈ _, has_deriv_at (λ y, cos y ^ (n + 1)) (-(n + 1) * sin x * cos x ^ n) x :=
    λ x hx, by simpa [mul_right_comm, -neg_add_rev] using (has_deriv_at_cos x).pow,
  have hv : ∀ x ∈ interval a b, has_deriv_at sin (cos x) x := λ x hx, has_deriv_at_sin x,
  have H := integral_mul_deriv_eq_deriv_mul hu hv _ _,
  calc  ∫ x in a..b, cos x ^ (n + 2)
      = ∫ x in a..b, cos x ^ (n + 1) * cos x : by simp only [pow_succ']
  ... = C + (n + 1) * ∫ x in a..b, sin x ^ 2 * cos x ^ n : by simp [H, h, sq, -neg_add_rev]
  ... = C + (n + 1) * ∫ x in a..b, cos x ^ n - cos x ^ (n + 2) : by simp [sin_sq, sub_mul,
                                                                          ← pow_add, add_comm]
  ... = C + (n + 1) * (∫ x in a..b, cos x ^ n) - (n + 1) * ∫ x in a..b, cos x ^ (n + 2) :
    by rw [integral_sub, mul_sub, add_sub_assoc]; apply continuous.interval_integrable; continuity,
  all_goals { apply continuous.continuous_on, continuity },
end

/-- The reduction formula for the integral of `cos x ^ n` for any natural `n ≥ 2`. -/
lemma integral_cos_pow :
  ∫ x in a..b, cos x ^ (n + 2) = (cos b ^ (n + 1) * sin b - cos a ^ (n + 1) * sin a) / (n + 2)
    + (n + 1) / (n + 2) * ∫ x in a..b, cos x ^ n :=
begin
  have : (n : ℝ) + 2 ≠ 0 := by exact_mod_cast succ_ne_zero n.succ,
  field_simp,
  convert eq_sub_iff_add_eq.mp (integral_cos_pow_aux n),
  ring,
end

@[simp]
lemma integral_cos_sq : ∫ x in a..b, cos x ^ 2 = (cos b * sin b - cos a * sin a + b - a) / 2 :=
by field_simp [integral_cos_pow, add_sub_assoc]
