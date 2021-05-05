import order.closure
import group_theory.submonoid.basic

open set submonoid

variables {M : Type*} [mul_one_class M]

def submonoid.neo_closure : closure_operator (set M) (submonoid M) :=
closure_operator.mk₂
  (λ s, Inf {S : submonoid M | s ⊆ ↑S})
  (λ S, submonoid.simps.coe S)
--  (λ s x hx, mem_Inf.2 $ λ S hS, hS hx)
--  (λ s t hst, Inf_le hst)
