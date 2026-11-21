import MathGenome.Internal.Specs.D07.Ch20.ArtinSchreier
import MathGenome.Internal.Specs.D07.Ch13.Existence
import Mathlib.FieldTheory.Finite.Trace

/-! Independent statements for K07.20.finite_artin_schreier, paper.tex:6046–6066.
The prime field is ZMod p and trace is the multiplication-operator trace.
The arbitrary finite field of characteristic p represents F_(p^r), for every
positive r. All scalar maps and embedded root fields use the specified algebra.
-/
noncomputable section
universe u v
namespace Specs.D07.Ch20.FiniteArtinSchreier
open Polynomial
open ArtinSchreierTranslationDichotomy (asPolynomial)

def AbsoluteTraceCriterion : Prop :=
  ∀ (K : Type u) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] (a : K),
    Irreducible (asPolynomial K p a) ↔ Algebra.trace (ZMod p) K a ≠ 0

def TraceZeroSplitting : Prop :=
  ∀ (K : Type u) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] (a : K),
    Algebra.trace (ZMod p) K a = 0 →
    ∃ θ : K, θ ^ p - θ = a ∧
      Function.Injective (fun c : ZMod p => θ + ZMod.cast c) ∧
      asPolynomial K p a = ∏ c : ZMod p, (X - C (θ + ZMod.cast c)) ∧
      (asPolynomial K p a).roots.card = p

def SplittingFieldDescription : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Finite K] [Algebra K L]
    (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K] (a : K)
    [Polynomial.IsSplittingField K L (asPolynomial K p a)],
    Algebra.trace (ZMod p) K a ≠ 0 →
    Finite L ∧ FiniteDimensional K L ∧ Module.finrank K L = p ∧
      Nat.card L = Nat.card K ^ p ∧ IsGalois K L ∧
      IsCyclic (L ≃ₐ[K] L) ∧ Nat.card (L ≃ₐ[K] L) = p

/-- Equality of actual subfields in the chosen algebraic closure identifies
this splitting field with F_(q^p), including the prescribed F_q embedding. -/
def EmbeddedSplittingField : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Finite K] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω]
    (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K] (a : K),
    Algebra.trace (ZMod p) K a ≠ 0 →
    IntermediateField.adjoin K ((asPolynomial K p a).rootSet Ω) =
      Specs.D07.Ch13.Existence.rootFieldValue K Ω (Nat.card K) p

def PrimeFieldExample : Prop :=
  Algebra.trace (ZMod 2) (ZMod 2) 1 = 1 ∧
    Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X])

def FourElementExample : Prop :=
  ∀ (K : Type u) [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) K],
    Nat.card K = 4 →
    Algebra.trace (ZMod 2) K 1 = 0 ∧
      (X ^ 2 + X + 1 : K[X]).Splits ∧
      (X ^ 2 + X + 1 : K[X]).roots.card = 2

/-- The counterexample has no root but has exactly two distinct monic
irreducible quadratic factors, over every copy of F_4. -/
def HigherPowerCounterexample : Prop :=
  ∀ (K : Type u) [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) K],
    Nat.card K = 4 →
    (∀ x : K, x ^ 4 = x) ∧
    (∀ x : K, (X ^ 4 - X - 1 : K[X]).eval x ≠ 0) ∧
    ∃ g h : K[X], g.Monic ∧ h.Monic ∧ g.natDegree = 2 ∧ h.natDegree = 2 ∧
      Irreducible g ∧ Irreducible h ∧ g ≠ h ∧
      (X ^ 4 - X - 1 : K[X]) = g * h

def QuarticOverPrimeField : Prop :=
  Irreducible (X ^ 4 + X + 1 : (ZMod 2)[X])

/-- Roots of the irreducible quartic generate a field of size 16 over F_2.
Over every embedded F_4 their minimal polynomials have degree two. -/
def QuarticRootDegrees : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Finite K]
    [CharP K 2] [Algebra (ZMod 2) K] [Algebra K L]
    [Algebra (ZMod 2) L] [IsScalarTower (ZMod 2) K L],
    Nat.card K = 4 → ∀ θ : L, θ ^ 4 + θ + 1 = 0 →
    (minpoly (ZMod 2) θ).natDegree = 4 ∧
      Finite (IntermediateField.adjoin (ZMod 2) {θ}) ∧
      Nat.card (IntermediateField.adjoin (ZMod 2) {θ}) = 16 ∧
      Polynomial.IsSplittingField (ZMod 2) (IntermediateField.adjoin (ZMod 2) {θ})
        (X ^ 4 + X + 1) ∧
      (minpoly K θ).natDegree = 2

end Specs.D07.Ch20.FiniteArtinSchreier
