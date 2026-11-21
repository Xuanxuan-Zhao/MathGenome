import MathGenome.Internal.Specs.D07.Ch15.QuadraticTowerIff
import MathGenome.Internal.Specs.D07.Ch14.PolynomialRootAction
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Normal.Closure

/-! Independent obligations for paper.tex:4524–4553. The chosen complex
splitting field includes nonreal conjugates. Constructibility means an actual
finite real quadratic tower, using the shared definition. -/
noncomputable section

universe u

namespace Specs.D07.Ch15.DegreeObstructionQuarticS4Counterexample
open Polynomial IntermediateField
open D07.Ch15.StraightedgeCompass

/-- The integral model used for reduction. -/
def quarticInt : ℤ[X] := X ^ 4 - X - 1
/-- The original rational quartic. -/
def quartic : ℚ[X] := X ^ 4 - X - 1
/-- The pair-product cubic resolvent. -/
def resolvent : ℚ[X] := X ^ 3 + C 4 * X - 1

/-- The three unordered partitions into pairs, in the displayed source order. -/
def pairProducts {F : Type*} [CommRing F] (r : Fin 4 → F) : Fin 3 → F :=
  ![r 0 * r 1 + r 2 * r 3,
    r 0 * r 2 + r 1 * r 3,
    r 0 * r 3 + r 1 * r 2]

noncomputable def complexSplittingField : IntermediateField ℚ ℂ :=
  adjoin ℚ (quartic.rootSet ℂ)

def ReductionIrreducible : Prop :=
  Irreducible (quarticInt.map (Int.castRingHom (ZMod 2)))
def QuarticIrreducible : Prop := Irreducible quartic

def ExactlyTwoRealRoots : Prop :=
  ∃ a b : ℝ, a ∈ Set.Ioo (-1) 0 ∧ b ∈ Set.Ioo 1 2 ∧
    ∀ x : ℝ, aeval x quartic = 0 ↔ x = a ∨ x = b

def ResolventIrreducible : Prop := Irreducible resolvent

/-- Any numbering of the four distinct roots gives the stated three distinct
resolvent roots, their factorization, and their individual equations. -/
def ResolventRoots : Prop :=
  ∀ (F : Type u) [Field F] [Algebra ℚ F] (r : Fin 4 → F),
    Function.Injective r →
    quartic.map (algebraMap ℚ F) = ∏ i, (X - C (r i)) →
    Function.Injective (pairProducts r) ∧
      resolvent.map (algebraMap ℚ F) = ∏ i, (X - C (pairProducts r i)) ∧
      ∀ i, aeval (pairProducts r i) resolvent = 0

/-- Complex conjugation restricted to the splitting field is a single
transposition on the actual four roots. -/
def RealConjugationTransposition : Prop :=
  ∃ σ : complexSplittingField ≃ₐ[ℚ] complexSplittingField,
    (∀ z : complexSplittingField, (σ z : ℂ) = star (z : ℂ)) ∧
    ∃ a b : quartic.rootSet complexSplittingField, a ≠ b ∧
      Ch14.PolynomialRootAction.rootPermutationValue ℚ complexSplittingField quartic σ =
        Equiv.swap a b

/-- The group is the full symmetric group in its root action, in every
splitting-field realization with its specified rational embedding. -/
def GaloisGroupS4 : Prop :=
  ∀ (F : Type u) [Field F] [Algebra ℚ F] [quartic.IsSplittingField ℚ F],
    ∃ b : Fin 4 ≃ quartic.rootSet F,
      ∃ e : (F ≃ₐ[ℚ] F) ≃* Equiv.Perm (Fin 4),
        ∀ σ i, (b (e σ i)).val = σ (b i).val

def SplittingDegree : Prop :=
  ∀ (F : Type u) [Field F] [Algebra ℚ F] [quartic.IsSplittingField ℚ F],
    Module.finrank ℚ F = 24

def RealRootDegree : Prop :=
  ∀ a : ℝ, aeval a quartic = 0 → Module.finrank ℚ ℚ⟮a⟯ = 4

/-- Equality of actual intermediate fields inside the same complex overfield;
ℚ(a) on the left is the real simple field, with all its complex embeddings. -/
def RealRootNormalClosure : Prop :=
  ∀ a : ℝ, aeval a quartic = 0 →
    normalClosure ℚ ℚ⟮a⟯ ℂ = complexSplittingField

def RealRootNotConstructible : Prop :=
  ∀ a : ℝ, aeval a quartic = 0 →
    ¬ ∃ M : IntermediateField ℚ ℝ,
      QuadraticTower ⊥ M ∧ a ∈ M

/-- Every intermediate field is quantified over; no endpoint, normality,
or separability assumptions are added. Degree two automatically gives a
proper nontrivial intermediate field once the degree-four result is proved. -/
def NoQuadraticIntermediate : Prop :=
  ∀ a : ℝ, aeval a quartic = 0 →
    ∀ E : IntermediateField ℚ ℚ⟮a⟯, Module.finrank ℚ E ≠ 2

end Specs.D07.Ch15.DegreeObstructionQuarticS4Counterexample
