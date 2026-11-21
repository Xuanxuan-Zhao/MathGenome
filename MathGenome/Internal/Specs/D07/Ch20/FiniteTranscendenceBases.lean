import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Localization.FractionRing

/-!
Independent statements for K07.20.finite_transcendence_bases,
paper.tex:6119–6145. Finite generation is as a field (`EssFiniteType`),
and finite algebraic degree is `Module.Finite`, never finiteness of the set.
The cardinal transcendence degree is identified with a natural number before
using `Cardinal.toNat`. Empty tuples and arbitrary characteristics are allowed.
All three embeddings of a field tower are specified and compatible.

The rational function field is the fraction field of the formal polynomial
ring. The generated-field version also covers independent tuples in any ambient
extension. In the final statement, the equations are nonzero polynomials:
a zero polynomial cannot certify that its root is algebraic.
-/

universe u v w

namespace Specs.D07.Ch20.FiniteTranscendenceBases

/-- A finite transcendence tuple with finite algebraic residual extension. -/
def FiniteBasisExists : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    Algebra.EssFiniteType K L →
    ∃ (r : ℕ) (a : Fin r → L),
      AlgebraicIndependent K a ∧
      Algebra.IsAlgebraic (IntermediateField.adjoin K (Set.range a)) L ∧
      Module.Finite (IntermediateField.adjoin K (Set.range a)) L ∧
      Algebra.trdeg K L = (r : Cardinal.{v})

/-- The common tuple length is the canonical transcendence degree. Algebraicity
suffices for this identification; finite degree is supplied in the other statements. -/
def IndependentTupleLength : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (r : ℕ) (a : Fin r → L),
    AlgebraicIndependent K a →
    Algebra.IsAlgebraic (IntermediateField.adjoin K (Set.range a)) L →
      Algebra.trdeg K L = (r : Cardinal.{v}) ∧ (Algebra.trdeg K L).toNat = r

/-- Every independent tuple with finite residual degree has the same length. -/
def BasisLengthUnique : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (r s : ℕ) (a : Fin r → L) (b : Fin s → L),
    AlgebraicIndependent K a →
    Module.Finite (IntermediateField.adjoin K (Set.range a)) L →
    AlgebraicIndependent K b →
    Module.Finite (IntermediateField.adjoin K (Set.range b)) L → r = s

/-- Finite algebraic extension preserves finite field generation and degree.
Lifts compare cardinal degrees in unrelated universes. -/
def FiniteExtensionInvariance : Prop :=
  ∀ (K : Type u) (L : Type v) (E : Type w) [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra L E] [Algebra K E] [IsScalarTower K L E],
    Algebra.EssFiniteType K L → Module.Finite L E →
      Algebra.EssFiniteType K E ∧
      Cardinal.lift.{w} (Algebra.trdeg K L) =
        Cardinal.lift.{v} (Algebra.trdeg K E) ∧
      (Algebra.trdeg K E).toNat = (Algebra.trdeg K L).toNat

/-- K(a_1,...,a_r) has transcendence degree r for independent a_i. -/
def RationalAdjoinDegree : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (r : ℕ) (a : Fin r → L),
    AlgebraicIndependent K a →
      Algebra.EssFiniteType K (IntermediateField.adjoin K (Set.range a)) ∧
      Algebra.trdeg K (IntermediateField.adjoin K (Set.range a)) = (r : Cardinal.{v}) ∧
      (Algebra.trdeg K (IntermediateField.adjoin K (Set.range a))).toNat = r

/-- The formula for the canonical rational function field in r indeterminates. -/
def RationalFunctionFieldDegree : Prop :=
  ∀ (K : Type u) [Field K] (r : ℕ),
    Algebra.EssFiniteType K (FractionRing (MvPolynomial (Fin r) K)) ∧
    Algebra.trdeg K (FractionRing (MvPolynomial (Fin r) K)) = (r : Cardinal.{u}) ∧
    (Algebra.trdeg K (FractionRing (MvPolynomial (Fin r) K))).toNat = r

/-- Adjoining roots of finitely many nonzero polynomial equations changes only
the finite algebraic step, and leaves transcendence degree unchanged. -/
def AdjoiningRootsPreservesDegree : Prop :=
  ∀ (K : Type u) (L : Type v) (E : Type w) [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra L E] [Algebra K E] [IsScalarTower K L E]
    (m : ℕ) (b : Fin m → E) (p : Fin m → Polynomial L),
    Algebra.EssFiniteType K L →
    (∀ i, p i ≠ 0) → (∀ i, Polynomial.aeval (b i) (p i) = 0) →
      Module.Finite L (IntermediateField.adjoin L (Set.range b)) ∧
      Algebra.IsAlgebraic L (IntermediateField.adjoin L (Set.range b)) ∧
      Algebra.EssFiniteType K (IntermediateField.adjoin L (Set.range b)) ∧
      Cardinal.lift.{w} (Algebra.trdeg K L) =
        Cardinal.lift.{v} (Algebra.trdeg K (IntermediateField.adjoin L (Set.range b))) ∧
      (Algebra.trdeg K (IntermediateField.adjoin L (Set.range b))).toNat =
        (Algebra.trdeg K L).toNat

end Specs.D07.Ch20.FiniteTranscendenceBases
