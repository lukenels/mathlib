
import order.closure
import group_theory.submonoid.basic

open set submonoid

variables {M : Type*} [mul_one_class M]

def submonoid.closure : closure_operator (set M) (submonoid M) :=
{ to_fun := λ s, Inf {S : submonoid M | s ⊆ ↑S},
  le_closure' := λ s x hx, mem_Inf.2 $ λ S hS, hS hx,
  idempotent' := begin

  end }
