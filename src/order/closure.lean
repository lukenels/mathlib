/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import order.basic
import order.preorder_hom
import order.galois_connection
import tactic.monotonicity

/-!
# Closure operators on a partial order

We define (bundled) closure operators on a partial order as an monotone (increasing), extensive
(inflationary) and idempotent function.
We define closed elements for the operator as elements which are fixed by it.

Note that there is close connection to Galois connections and Galois insertions: every closure
operator induces a Galois insertion (from the set of closed elements to the underlying type), and
every Galois connection induces a closure operator (namely the composition). In particular,
a Galois insertion can be seen as a general case of a closure operator, where the inclusion is given
by coercion, see `closure_operator.gi`.

## References

* https://en.wikipedia.org/wiki/Closure_operator#Closure_operators_on_partially_ordered_sets

-/
universes u v

variables (α : Type u) [partial_order α]

/--
A closure operator on the partial order `α` is a monotone function which is extensive (every `x`
is less than its closure) and idempotent.
-/
structure closure_operator extends α →ₘ α :=
(le_closure' : ∀ x, x ≤ to_fun x)
(idempotent' : ∀ x, to_fun (to_fun x) = to_fun x)

instance : has_coe_to_fun (closure_operator α) :=
{ F := _, coe := λ c, c.to_fun }

/-- See Note [custom simps projection] -/
def closure_operator.simps.apply (f : closure_operator α) : α → α := f

initialize_simps_projections closure_operator (to_preorder_hom_to_fun → apply, -to_preorder_hom)

namespace closure_operator

/-- The identity function as a closure operator. -/
@[simps]
def id : closure_operator α :=
{ to_fun := λ x, x,
  monotone' := λ _ _ h, h,
  le_closure' := λ _, le_refl _,
  idempotent' := λ _, rfl }

instance : inhabited (closure_operator α) := ⟨id α⟩

variables {α} (c : closure_operator α)

@[ext] lemma ext :
  ∀ (c₁ c₂ : closure_operator α), (c₁ : α → α) = (c₂ : α → α) → c₁ = c₂
| ⟨⟨c₁, _⟩, _, _⟩ ⟨⟨c₂, _⟩, _, _⟩ h := by { congr, exact h }

/-- Constructor for a closure operator using the weaker idempotency axiom: `f (f x) ≤ f x`. -/
@[simps]
def mk' (f : α → α) (hf₁ : monotone f) (hf₂ : ∀ x, x ≤ f x) (hf₃ : ∀ x, f (f x) ≤ f x) :
  closure_operator α :=
{ to_fun := f,
  monotone' := hf₁,
  le_closure' := hf₂,
  idempotent' := λ x, le_antisymm (hf₃ x) (hf₁ (hf₂ x)) }

/-- Convenience constructor for a closure operator using the weaker minimality axiom:
`x ≤ f y → f x ≤ f y`, which is sometimes easier to prove in practice. -/
@[simps]
def mk₂ (f : α → α) (hf : ∀ x, x ≤ f x) (hmin : ∀ ⦃x y⦄, x ≤ f y → f x ≤ f y) :
  closure_operator α :=
{ to_fun := f,
  monotone' := λ x y hxy, hmin (le_trans hxy (hf y)),
  le_closure' := hf,
  idempotent' := λ x, le_antisymm (hmin (le_refl _)) (hf _) }

/-- Expanded out version of `mk₂`. `p` implies being closed. This constructor should be used when
you already know a sufficient condition for being closed and using `mem_mk₃_closed` will avoid you
the (slight) hassle of having to prove it both inside and outside the constructor. -/
@[simps]
def mk₃ (f : α → α) (p : α → Prop) (hf : ∀ x, x ≤ f x) (hfp : ∀ x, p (f x))
  (hmin : ∀ ⦃x y⦄, x ≤ y → p y → f x ≤ y) :
  closure_operator α :=
mk₂ f hf (λ x y hxy, hmin hxy (hfp y))

/-- This lemma shows that the image of `x` of a closure operator built from the `mk₃` constructor
respects `p`, the property that was fed into it. -/
lemma closure_mem_mk₃ {f : α → α} {p : α → Prop} {hf : ∀ x, x ≤ f x} {hfp : ∀ x, p (f x)}
  {hmin : ∀ ⦃x y⦄, x ≤ y → p y → f x ≤ y} (x : α) :
  p (mk₃ f p hf hfp hmin x) :=
hfp x

/-- Analogue of `closure_le_closed_iff_le` but with the `p` that was fed into the `mk₃` constructor.
-/
lemma closure_le_mk₃_iff {f : α → α} {p : α → Prop} {hf : ∀ x, x ≤ f x} {hfp : ∀ x, p (f x)}
  {hmin : ∀ ⦃x y⦄, x ≤ y → p y → f x ≤ y} {x y : α} (hxy : x ≤ y) (hy : p y) :
  mk₃ f p hf hfp hmin x ≤ y :=
hmin hxy hy

@[mono] lemma monotone : monotone c := c.monotone'
/--
Every element is less than its closure. This property is sometimes referred to as extensivity or
inflationarity.
-/
lemma le_closure (x : α) : x ≤ c x := c.le_closure' x
@[simp] lemma idempotent (x : α) : c (c x) = c x := c.idempotent' x

lemma le_closure_iff (x y : α) : x ≤ c y ↔ c x ≤ c y :=
⟨λ h, c.idempotent y ▸ c.monotone h, λ h, le_trans (c.le_closure x) h⟩

@[simp] lemma closure_top {α : Type u} [order_top α] (c : closure_operator α) : c ⊤ = ⊤ :=
le_antisymm le_top (c.le_closure _)

lemma closure_inf_le {α : Type u} [semilattice_inf α] (c : closure_operator α) (x y : α) :
  c (x ⊓ y) ≤ c x ⊓ c y :=
c.monotone.map_inf_le _ _

lemma closure_sup_closure_le {α : Type u} [semilattice_sup α] (c : closure_operator α) (x y : α) :
  c x ⊔ c y ≤ c (x ⊔ y) :=
c.monotone.le_map_sup _ _

/-- An element `x` is closed for the closure operator `c` if it is a fixed point for it. -/
def closed : set α := λ x, c x = x

lemma mem_closed_iff (x : α) : x ∈ c.closed ↔ c x = x := iff.rfl
lemma mem_closed_iff_closure_le (x : α) : x ∈ c.closed ↔ c x ≤ x :=
⟨le_of_eq, λ h, le_antisymm h (c.le_closure x)⟩
lemma closure_eq_self_of_mem_closed {x : α} (h : x ∈ c.closed) : c x = x := h

@[simp] lemma closure_is_closed (x : α) : c x ∈ c.closed := c.idempotent x

/-- The set of closed elements for `c` is exactly its range. -/
lemma closed_eq_range_close : c.closed = set.range c :=
set.ext $ λ x, ⟨λ h, ⟨x, h⟩, by { rintro ⟨y, rfl⟩, apply c.idempotent }⟩

/-- Send an `x` to an element of the set of closed elements (by taking the closure). -/
def to_closed (x : α) : c.closed := ⟨c x, c.closure_is_closed x⟩

lemma top_mem_closed {α : Type u} [order_top α] (c : closure_operator α) : ⊤ ∈ c.closed :=
c.closure_top

@[simp] lemma closure_le_closed_iff_le (x : α) {y : α} (hy : c.closed y) : c x ≤ y ↔ x ≤ y :=
by rw [←c.closure_eq_self_of_mem_closed hy, ←le_closure_iff]

/-- A closure operator is equal to the closure operator obtained by feeding `c.closed` into the
`mk₃` constructor. -/
lemma eq_mk₃_closed (c : closure_operator α) :
  c = mk₃ c c.closed c.le_closure c.closure_is_closed
  (λ x y hxy hy, (c.closure_le_closed_iff_le x hy).2 hxy) :=
by { ext, refl }

/-- This lemma shows that the `p` fed into the `mk₃` constructor implies being closed. -/
lemma mem_mk₃_closed {f : α → α} {p : α → Prop} {hf : ∀ x, x ≤ f x} {hfp : ∀ x, p (f x)}
  {hmin : ∀ ⦃x y⦄, x ≤ y → p y → f x ≤ y} {x : α} (hx : p x) :
  x ∈ (mk₃ f p hf hfp hmin).closed :=
le_antisymm (hmin (le_refl _) hx) (hf _)

@[simp] lemma closure_sup_closure_left {α : Type u} [semilattice_sup α] (c : closure_operator α)
  (x y : α) :
  c (c x ⊔ y) = c (x ⊔ y) :=
le_antisymm ((le_closure_iff c _ _).1 (sup_le (c.monotone le_sup_left)
  (le_trans le_sup_right (le_closure _ _)))) (c.monotone (sup_le_sup_right (le_closure _ _) _))

@[simp] lemma closure_sup_closure_right {α : Type u} [semilattice_sup α] (c : closure_operator α)
  (x y : α) :
  c (x ⊔ c y) = c (x ⊔ y) :=
by rw [sup_comm, closure_sup_closure_left, sup_comm]

@[simp] lemma closure_sup_closure {α : Type u} [semilattice_sup α] (c : closure_operator α)
  (x y : α) :
  c (c x ⊔ c y) = c (x ⊔ y) :=
by rw [closure_sup_closure_left, closure_sup_closure_right]

@[simp] lemma closure_supr_closure {α : Type u} {ι : Type v} [complete_lattice α]
  (c : closure_operator α) (x : ι → α) :
  c (⨆ i, c (x i)) = c (⨆ i, x i) :=
le_antisymm ((le_closure_iff c _ _).1 (supr_le (λ i, c.monotone
  (le_supr _ _)))) (c.monotone (supr_le_supr (λ i, c.le_closure _)))

@[simp] lemma closure_bsupr_closure {α : Type u} [complete_lattice α] (c : closure_operator α)
  (p : α → Prop) :
  c (⨆ x (H : p x), c x) = c (⨆ x (H : p x), x) :=
le_antisymm ((le_closure_iff c _ _).1 (bsupr_le (λ x hx, c.monotone
  (le_bsupr_of_le x hx (le_refl x))))) (c.monotone (bsupr_le_bsupr (λ x hx, le_closure _ _)))

/-- The set of closed elements has a Galois insertion to the underlying type. -/
def gi : galois_insertion c.to_closed coe :=
{ choice := λ x hx, ⟨x, le_antisymm hx (c.le_closure x)⟩,
  gc := λ x y, (c.closure_le_closed_iff_le _ y.2),
  le_l_u := λ x, c.le_closure _,
  choice_eq := λ x hx, le_antisymm (c.le_closure x) hx }

end closure_operator

variables {α} (c : closure_operator α)

/--
Every Galois connection induces a closure operator given by the composition. This is the partial
order version of the statement that every adjunction induces a monad.
-/
@[simps]
def galois_connection.closure_operator {β : Type u} [preorder β]
  {l : α → β} {u : β → α} (gc : galois_connection l u) :
  closure_operator α :=
{ to_fun := λ x, u (l x),
  monotone' := λ x y h, gc.monotone_u (gc.monotone_l h),
  le_closure' := gc.le_u_l,
  idempotent' := λ x, le_antisymm (gc.monotone_u (gc.l_u_le _)) (gc.le_u_l _) }

/--
The Galois insertion associated to a closure operator can be used to reconstruct the closure
operator.

Note that the inverse in the opposite direction does not hold in general.
-/
@[simp]
lemma closure_operator_gi_self : c.gi.gc.closure_operator = c :=
by { ext x, refl }
