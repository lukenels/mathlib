/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import data.finsupp.basic
import data.multiset.antidiagonal

/-!
# The `finsupp` counterpart of `multiset.antidiagonal`.

The antidiagonal of `s : α →₀ ℕ` consists of
all pairs `(t₁, t₂) : (α →₀ ℕ) × (α →₀ ℕ)` such that `t₁ + t₂ = s`.
-/

noncomputable theory
open_locale classical big_operators

namespace finsupp

open finset
variables {α : Type*}

/-- The `finsupp` counterpart of `multiset.antidiagonal`: the antidiagonal of
`s : α →₀ ℕ` consists of all pairs `(t₁, t₂) : (α →₀ ℕ) × (α →₀ ℕ)` such that `t₁ + t₂ = s`.
The finitely supported function `antidiagonal s` is equal to the multiplicities of these pairs. -/
def antidiagonal (f : α →₀ ℕ) : ((α →₀ ℕ) × (α →₀ ℕ)) →₀ ℕ :=
(f.to_multiset.antidiagonal.map (prod.map multiset.to_finsupp multiset.to_finsupp)).to_finsupp

@[simp] lemma mem_antidiagonal_support {f : α →₀ ℕ} {p : (α →₀ ℕ) × (α →₀ ℕ)} :
  p ∈ (antidiagonal f).support ↔ p.1 + p.2 = f :=
begin
  rcases p with ⟨p₁, p₂⟩,
  simp [antidiagonal, ← and.assoc, ← finsupp.to_multiset.apply_eq_iff_eq]
end

lemma swap_mem_antidiagonal_support {n : α →₀ ℕ} {f : (α →₀ ℕ) × (α →₀ ℕ)} :
  f.swap ∈ (antidiagonal n).support ↔ f ∈ (antidiagonal n).support :=
by simp only [mem_antidiagonal_support, add_comm, prod.swap]

lemma antidiagonal_support_filter_fst_eq (f g : α →₀ ℕ)
  [D : Π (p : (α →₀ ℕ) × (α →₀ ℕ)), decidable (p.1 = g)] :
  (antidiagonal f).support.filter (λ p, p.1 = g) = if g ≤ f then {(g, f - g)} else ∅ :=
begin
  ext ⟨a, b⟩,
  suffices : a = g → (a + b = f ↔ g ≤ f ∧ b = f - g),
  { simpa [apply_ite ((∈) (a, b)), ← and.assoc, @and.right_comm _ (a = _), and.congr_left_iff] },
  unfreezingI {rintro rfl}, split,
  { rintro rfl, exact ⟨le_add_right le_rfl, (nat_add_sub_cancel_left _ _).symm⟩ },
  { rintro ⟨h, rfl⟩, exact nat_add_sub_of_le h }
end

lemma antidiagonal_support_filter_snd_eq (f g : α →₀ ℕ)
  [D : Π (p : (α →₀ ℕ) × (α →₀ ℕ)), decidable (p.2 = g)] :
  (antidiagonal f).support.filter (λ p, p.2 = g) = if g ≤ f then {(f - g, g)} else ∅ :=
begin
  ext ⟨a, b⟩,
  suffices : b = g → (a + b = f ↔ g ≤ f ∧ a = f - g),
  { simpa [apply_ite ((∈) (a, b)), ← and.assoc, and.congr_left_iff] },
  unfreezingI {rintro rfl}, split,
  { rintro rfl, exact ⟨le_add_left le_rfl, (nat_add_sub_cancel _ _).symm⟩ },
  { rintro ⟨h, rfl⟩, exact nat_sub_add_cancel h }
end

@[simp] lemma antidiagonal_zero : antidiagonal (0 : α →₀ ℕ) = single (0,0) 1 :=
by rw [← multiset.to_finsupp_singleton]; refl

@[to_additive]
lemma prod_antidiagonal_support_swap {M : Type*} [comm_monoid M] (n : α →₀ ℕ)
  (f : (α →₀ ℕ) → (α →₀ ℕ) → M) :
  ∏ p in (antidiagonal n).support, f p.1 p.2 = ∏ p in (antidiagonal n).support, f p.2 p.1 :=
finset.prod_bij (λ p hp, p.swap) (λ p, swap_mem_antidiagonal_support.2) (λ p hp, rfl)
  (λ p₁ p₂ _ _ h, prod.swap_injective h)
  (λ p hp, ⟨p.swap, swap_mem_antidiagonal_support.2 hp, p.swap_swap.symm⟩)

/-- The set `{m : α →₀ ℕ | m ≤ n}` as a `finset`. -/
def Iic_finset (n : α →₀ ℕ) : finset (α →₀ ℕ) :=
(antidiagonal n).support.image prod.fst

@[simp] lemma mem_Iic_finset {m n : α →₀ ℕ} : m ∈ Iic_finset n ↔ m ≤ n :=
by simp [Iic_finset, le_iff_exists_add, eq_comm]

@[simp] lemma coe_Iic_finset (n : α →₀ ℕ) : ↑(Iic_finset n) = set.Iic n :=
by { ext, simp }

/-- Let `n : α →₀ ℕ` be a finitely supported function.
The set of `m : α →₀ ℕ` that are coordinatewise less than or equal to `n`,
is a finite set. -/
lemma finite_le_nat (n : α →₀ ℕ) : set.finite {m | m ≤ n} :=
by simpa using (Iic_finset n).finite_to_set

/-- Let `n : α →₀ ℕ` be a finitely supported function.
The set of `m : α →₀ ℕ` that are coordinatewise less than or equal to `n`,
but not equal to `n` everywhere, is a finite set. -/
lemma finite_lt_nat (n : α →₀ ℕ) : set.finite {m | m < n} :=
(finite_le_nat n).subset $ λ m, le_of_lt

end finsupp
