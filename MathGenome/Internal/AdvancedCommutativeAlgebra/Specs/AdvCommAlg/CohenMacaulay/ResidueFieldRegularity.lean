import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.ResidueDimensionRegularReduction
import Mathlib.RingTheory.RegularLocalRing.Defs

/-! The residue-field criterion of CM-19, including its two boundary steps.
Finiteness means equality to a natural number in `WithBot ℕ∞`. -/
universe u
open CategoryTheory
namespace AdvCommAlg.CohenMacaulay.Specs

def residueField_projectiveDimension_zeroType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) = 0 →
      IsLocalRing.maximalIdeal R = ⊥ ∧ IsRegularLocalRing R

def exists_regular_minimalGeneratorType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (n : ℕ), 0 < n →
    projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
      (n : WithBot ℕ∞) →
    ∃ x : R, x ∈ IsLocalRing.maximalIdeal R ∧
      x ∉ (IsLocalRing.maximalIdeal R) ^ 2 ∧ IsSMulRegular R x

def regularLocal_iff_residueField_finite_projectiveDimensionType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    IsRegularLocalRing R ↔ ∃ n : ℕ,
      projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
        (n : WithBot ℕ∞)

end AdvCommAlg.CohenMacaulay.Specs
