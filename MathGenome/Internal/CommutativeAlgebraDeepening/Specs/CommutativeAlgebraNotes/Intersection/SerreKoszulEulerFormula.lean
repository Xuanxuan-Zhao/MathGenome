import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.DegreeMultiplicity
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.Construction
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.RingTheory.FiniteLength

namespace Specs.CommutativeAlgebraNotes.Intersection.SerreKoszulEulerFormula

open CategoryTheory
open _root_.AdvCommAlg.Koszul (coefficientComplex listIdeal)
open P103.Specs.Ch06.DimensionConventions (moduleDimensionValue)
open Specs.CommutativeAlgebraNotes.Intersection.DegreeMultiplicity (degreeMultiplicity)

universe u v

/-- The dimension of a nonzero coefficient module is bounded by the number
of generators in the list. -/
def dimensionBoundType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (E : Type v) [AddCommGroup E] [Module A E] [Module.Finite A E] (z : List A),
    listIdeal z ≤ IsLocalRing.maximalIdeal A →
    IsFiniteLength A (E ⧸ (listIdeal z • (⊤ : Submodule A E))) →
    Nontrivial E → moduleDimensionValue A E ≤ (z.length : WithBot ℕ∞)

/-- Finiteness of the length of every homology module, including degrees
above the length of the list. -/
def homologyFiniteLengthType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (E : Type v) [AddCommGroup E] [Module A E] [Module.Finite A E] (z : List A),
    listIdeal z ≤ IsLocalRing.maximalIdeal A →
    IsFiniteLength A (E ⧸ (listIdeal z • (⊤ : Submodule A E))) →
    ∀ i : ℕ, IsFiniteLength A ((coefficientComplex E z).homology i)

/-- The alternating sum of homology lengths equals the multiplicity taken
in the degree given by the length of the list. -/
def serreKoszulEulerFormulaType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (E : Type v) [AddCommGroup E] [Module A E] [Module.Finite A E] (z : List A),
    listIdeal z ≤ IsLocalRing.maximalIdeal A →
    IsFiniteLength A (E ⧸ (listIdeal z • (⊤ : Submodule A E))) →
    ((∑ i ∈ Finset.range (z.length + 1), (-1 : ℤ) ^ i *
      ((Module.length A ((coefficientComplex E z).homology i)).toNat : ℤ) : ℤ) : ℚ) =
        degreeMultiplicity (listIdeal z) E z.length

def positiveIntegerType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (E : Type v) [AddCommGroup E] [Module A E] [Module.Finite A E] (z : List A),
    listIdeal z ≤ IsLocalRing.maximalIdeal A →
    IsFiniteLength A (E ⧸ (listIdeal z • (⊤ : Submodule A E))) →
    Nontrivial E → moduleDimensionValue A E = (z.length : WithBot ℕ∞) →
    ∃ n : ℤ, 0 < n ∧ degreeMultiplicity (listIdeal z) E z.length = (n : ℚ)

def zeroOfDimensionLTType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (E : Type v) [AddCommGroup E] [Module A E] [Module.Finite A E] (z : List A),
    listIdeal z ≤ IsLocalRing.maximalIdeal A →
    IsFiniteLength A (E ⧸ (listIdeal z • (⊤ : Submodule A E))) →
    moduleDimensionValue A E < (z.length : WithBot ℕ∞) →
    degreeMultiplicity (listIdeal z) E z.length = 0

/-- Additivity in the coefficient module in degree `z.length`. -/
def additivityType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (z : List A) (S : ShortComplex (ModuleCat.{v} A))
    [Module.Finite A S.X₁] [Module.Finite A S.X₂] [Module.Finite A S.X₃],
    S.ShortExact → listIdeal z ≤ IsLocalRing.maximalIdeal A →
    IsFiniteLength A (S.X₁ ⧸ (listIdeal z • (⊤ : Submodule A S.X₁))) →
    IsFiniteLength A (S.X₂ ⧸ (listIdeal z • (⊤ : Submodule A S.X₂))) →
    IsFiniteLength A (S.X₃ ⧸ (listIdeal z • (⊤ : Submodule A S.X₃))) →
    degreeMultiplicity (listIdeal z) S.X₂ z.length =
      degreeMultiplicity (listIdeal z) S.X₁ z.length +
      degreeMultiplicity (listIdeal z) S.X₃ z.length

end Specs.CommutativeAlgebraNotes.Intersection.SerreKoszulEulerFormula
