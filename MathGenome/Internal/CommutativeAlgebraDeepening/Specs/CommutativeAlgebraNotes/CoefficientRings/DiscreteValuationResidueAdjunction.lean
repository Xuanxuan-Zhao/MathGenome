import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

namespace CommutativeAlgebraNotes.CoefficientRings.Specs

universe u v w

open IsLocalRing

/-- A simple extension of the specified residue field lifts to an injective local map of
discrete valuation rings with the same rational prime as uniformizer. -/
def discreteValuationResidueAdjunctionType : Prop :=
  ∀ (p : ℕ) (_ : p.Prime)
    (D : Type u) [CommRing D] [IsDomain D] [IsDiscreteValuationRing D],
    maximalIdeal D = Ideal.span {(p : D)} →
    ∀ (k₀ : Type v) [Field k₀] [CharP k₀ p] (e₀ : ResidueField D ≃+* k₀)
      (k₁ : Type w) [Field k₁] [Algebra k₀ k₁] (a : k₁),
      IntermediateField.adjoin k₀ ({a} : Set k₁) = ⊤ →
      ∃ (D' : Type u) (_ : CommRing D') (_ : IsDomain D') (_ : IsDiscreteValuationRing D'),
        ∃ (f : D →+* D') (_ : IsLocalHom f),
          Function.Injective f ∧ maximalIdeal D' = Ideal.span {(p : D')} ∧
            ∃ e₁ : ResidueField D' ≃+* k₁,
              e₁.toRingHom.comp (ResidueField.map f) = (algebraMap k₀ k₁).comp e₀.toRingHom

end CommutativeAlgebraNotes.CoefficientRings.Specs
