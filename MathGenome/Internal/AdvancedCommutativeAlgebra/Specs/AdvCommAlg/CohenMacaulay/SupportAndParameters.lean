import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.Definitions
import Mathlib.RingTheory.FiniteLength

/-! Independent statements of CM-02, paper.tex:3252–3280.
The dimension is the support dimension from CM-01. Parameters are finite
ordered lists; the empty list is allowed. No CM hypothesis is imposed.
`IsFiniteLength` means existence of a finite composition series.
-/

universe u
namespace AdvCommAlg.CohenMacaulay.Specs

def IsSystemOfParametersType := ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M], List R → Prop

noncomputable def IsSystemOfParametersValue : IsSystemOfParametersType.{u} :=
  fun R _ _ M _ _ x =>
    (∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R) ∧
    (x.length : WithBot ℕ∞) = dimensionValue R M ∧
    IsFiniteLength R (M ⧸ (Ideal.ofList x • (⊤ : Submodule R M)))

/-- The support formula holds even without local or Noetherian assumptions. -/
def support_quotientType : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (J : Ideal R),
    Module.support R (M ⧸ (J • (⊤ : Submodule R M))) =
      Module.support R M ∩ PrimeSpectrum.zeroLocus (J : Set R)

def quotient_nontrivialType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (J : Ideal R), J ≤ IsLocalRing.maximalIdeal R →
    Nontrivial (M ⧸ (J • (⊤ : Submodule R M)))

def finiteLength_quotient_iff_support_singletonType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (J : Ideal R), J ≤ IsLocalRing.maximalIdeal R →
    (IsFiniteLength R (M ⧸ (J • (⊤ : Submodule R M))) ↔
      Module.support R (M ⧸ (J • (⊤ : Submodule R M))) = {IsLocalRing.closedPoint R})

def exists_systemOfParametersType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M],
    ∃ x : List R, IsSystemOfParametersValue R M x

def dimension_le_length_of_finiteLength_quotientType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (x : List R), (∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R) →
    IsFiniteLength R (M ⧸ (Ideal.ofList x • (⊤ : Submodule R M))) →
    dimensionValue R M ≤ (x.length : WithBot ℕ∞)

def isLeast_parameter_lengthType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M],
    ∃ d : ℕ, dimensionValue R M = (d : WithBot ℕ∞) ∧
      IsLeast {n : ℕ | ∃ x : List R, x.length = n ∧
        (∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R) ∧
        IsFiniteLength R (M ⧸ (Ideal.ofList x • (⊤ : Submodule R M)))} d

def dimension_zero_iff_finiteLengthType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M],
    dimensionValue R M = 0 ↔ IsFiniteLength R M

def systemOfParameters_nil_iffType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M],
    IsSystemOfParametersValue R M [] ↔ dimensionValue R M = 0

def dimension_quotient_regularType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (x : R), x ∈ IsLocalRing.maximalIdeal R →
    Function.Injective (fun m : M => x • m) →
    Nontrivial (QuotSMulTop x M) ∧
      dimensionValue R (QuotSMulTop x M) + 1 = dimensionValue R M

end AdvCommAlg.CohenMacaulay.Specs
