import MathGenome.Internal.Specs.D07.Ch14.PolynomialRootAction
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
K07.14.cubic_splitting_example, paper.tex:4264–4271.
All fields are embedded in the same complex overfield. The real cube root
is fixed explicitly; ζ ranges over BOTH primitive cube roots. The root
numbering is a, ζa, ζ²a, and the S₃ identification must realize this action.
These are full propositions, with no assumed degree, Galois certificate,
subfield classification or existence of the requested automorphisms.
-/
namespace Specs.D07.Ch14.CubicSplittingExample

open Polynomial IntermediateField

noncomputable def a : ℝ := (2 : ℝ) ^ (3 : ℝ)⁻¹

noncomputable def cubic : ℚ[X] := X ^ 3 - C 2

noncomputable def L (ζ : ℂ) : IntermediateField ℚ ℂ := adjoin ℚ {(a : ℂ), ζ}

noncomputable def alpha (ζ : ℂ) : L ζ :=
  ⟨a, subset_adjoin ℚ _ (by simp)⟩
noncomputable def zeta (ζ : ℂ) : L ζ :=
  ⟨ζ, subset_adjoin ℚ _ (by simp)⟩

noncomputable def root (ζ : ℂ) (i : Fin 3) : L ζ := zeta ζ ^ i.val * alpha ζ
noncomputable def cubicField (ζ : ℂ) (i : Fin 3) : IntermediateField ℚ (L ζ) :=
  adjoin ℚ {root ζ i}
noncomputable def quadraticField (ζ : ℂ) : IntermediateField ℚ (L ζ) :=
  adjoin ℚ {zeta ζ}

def RealCubeRoot : Prop := a ^ 3 = 2 ∧ 0 < a

def PolynomialFacts : Prop :=
  Irreducible cubic ∧ cubic.Separable ∧ cubic.natDegree = 3

def RootDescription : Prop :=
  ∀ ζ : ℂ, IsPrimitiveRoot ζ 3 →
    Function.Injective (root ζ) ∧
      ∀ x : L ζ, aeval x cubic = 0 ↔ ∃ i : Fin 3, x = root ζ i

def SplittingField : Prop :=
  ∀ ζ : ℂ, IsPrimitiveRoot ζ 3 → Polynomial.IsSplittingField ℚ (L ζ) cubic

def DegreeSix : Prop :=
  ∀ ζ : ℂ, IsPrimitiveRoot ζ 3 →
    FiniteDimensional ℚ (L ζ) ∧ Module.finrank ℚ (L ζ) = 6 ∧ IsGalois ℚ (L ζ)

def CubicDegrees : Prop :=
  ∀ ζ : ℂ, IsPrimitiveRoot ζ 3 →
    ∀ i : Fin 3, FiniteDimensional ℚ (cubicField ζ i) ∧
      Module.finrank ℚ (cubicField ζ i) = 3

def QuadraticDegree : Prop :=
  ∀ ζ : ℂ, IsPrimitiveRoot ζ 3 →
    FiniteDimensional ℚ (quadraticField ζ) ∧
      Module.finrank ℚ (quadraticField ζ) = 2

def CubicClassification : Prop :=
  ∀ ζ : ℂ, IsPrimitiveRoot ζ 3 →
    Function.Injective (cubicField ζ) ∧
      ∀ E : IntermediateField ℚ (L ζ),
        Module.finrank ℚ E = 3 ↔ ∃ i : Fin 3, E = cubicField ζ i

/-- S₃ is the full permutation group on the displayed three roots. A₃
means its actual alternating subgroup, pulled back through this same map. -/
def GaloisGroupAndAlternatingFixedField : Prop :=
  ∀ ζ : ℂ, IsPrimitiveRoot ζ 3 →
    ∃ ρ : (L ζ ≃ₐ[ℚ] L ζ) ≃* Equiv.Perm (Fin 3),
      (∀ σ i, σ (root ζ i) = root ζ (ρ σ i)) ∧
      IntermediateField.fixedField
        ((alternatingGroup (Fin 3)).comap ρ.toMonoidHom) = quadraticField ζ

def CubicStabilizers : Prop :=
  ∀ ζ : ℂ, IsPrimitiveRoot ζ 3 → ∀ i : Fin 3,
    Nat.card (cubicField ζ i).fixingSubgroup = 2 ∧
    IntermediateField.fixedField (cubicField ζ i).fixingSubgroup = cubicField ζ i ∧
    ∀ σ : L ζ ≃ₐ[ℚ] L ζ,
      σ ∈ (cubicField ζ i).fixingSubgroup ↔ σ (root ζ i) = root ζ i

def Intersections : Prop :=
  ∀ ζ : ℂ, IsPrimitiveRoot ζ 3 → ∀ i j : Fin 3, i ≠ j →
    cubicField ζ i ⊓ cubicField ζ j = ⊥

def Compositum : Prop :=
  ∀ ζ : ℂ, IsPrimitiveRoot ζ 3 → cubicField ζ 0 ⊔ cubicField ζ 1 = ⊤

def RealFieldNotNormal : Prop :=
  ∀ ζ : ℂ, IsPrimitiveRoot ζ 3 → ¬ Normal ℚ (cubicField ζ 0)

/-- The source's explicit generators really exist, and their stated orders
are assertions to prove rather than hypotheses in the group identification. -/
def RotationAndConjugation : Prop :=
  ∀ ζ : ℂ, IsPrimitiveRoot ζ 3 →
    ∃ r s : L ζ ≃ₐ[ℚ] L ζ,
      r (alpha ζ) = zeta ζ * alpha ζ ∧ r (zeta ζ) = zeta ζ ∧
      orderOf r = 3 ∧ s (alpha ζ) = alpha ζ ∧
      s (zeta ζ) = zeta ζ ^ 2 ∧ orderOf s = 2 ∧
      (∀ x : L ζ, (s x : ℂ) = star (x : ℂ)) ∧
      IntermediateField.fixedField (Subgroup.zpowers r) = quadraticField ζ

end Specs.D07.Ch14.CubicSplittingExample
