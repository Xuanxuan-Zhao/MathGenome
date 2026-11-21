import MathGenome.Internal.Specs.D07.Ch13.PolynomialFunctions
import MathGenome.Internal.D07.Ch13.PowerIdentity
import Mathlib.LinearAlgebra.Lagrange

/-! Formal polynomials versus functions on a finite field. -/

universe u

namespace D07.Ch13.PolynomialFunctions

open Polynomial
open Specs.D07.Ch13.PolynomialFunctions

theorem nonzero_vanishing_polynomial : NonzeroVanishingPolynomial.{u} := by
  intro F _ _ q hq
  have hqgt : 1 < q := hq ▸ Fintype.one_lt_card
  refine ⟨FiniteField.X_pow_card_sub_X_ne_zero F hqgt, ?_⟩
  intro a
  rw [eval_sub, eval_pow, eval_X,
    D07.Ch13.PowerIdentity.power_identity F q hq a, sub_self]

theorem unique_representative : UniqueRepresentative.{u} := by
  intro F _ _ q hq h
  classical
  have hinj : Set.InjOn (fun a : F => a) (Finset.univ : Finset F) :=
    fun _ _ _ _ hab => hab
  refine ⟨Lagrange.interpolate Finset.univ (fun a : F => a) h, ⟨?_, ?_⟩, ?_⟩
  · simpa only [Finset.card_univ, hq] using Lagrange.degree_interpolate_lt h hinj
  · intro a
    exact Lagrange.eval_interpolate_at_node h hinj (Finset.mem_univ a)
  · intro f hf
    apply Lagrange.eq_interpolate_of_eval_eq h hinj
    · simpa only [Finset.card_univ, hq] using hf.1
    · intro a _
      exact hf.2 a

end D07.Ch13.PolynomialFunctions
