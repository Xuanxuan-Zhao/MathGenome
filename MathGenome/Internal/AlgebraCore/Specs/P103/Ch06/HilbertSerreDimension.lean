import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.HilbertSerreLength
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.DimensionConventions
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.LinearGradedNormalization
import Mathlib.RingTheory.TensorProduct.Basic

/-!
Theorem 6.10, paper.tex:1152–1164.  The grading is the accepted internal
integer grading; only the algebra has vanishing negative pieces.  The
structural field is identified with A₀ by `Connected`, and the module's
k-action is restriction of its A-action (`IsScalarTower`).

The series below has the actual k-dimensions as coefficients.  Its rational
presentation uses the Laurent-series convention from Lemma 6.9.  No field
cardinality assumption or faithfulness hypothesis is imposed.
-/
namespace P103.HilbertSerreDimension

open P103.Graded
open P103.Specs.Ch06.LinearGradedNormalization

universe u v w x
variable (k : Type u) {A : Type v} {M : Type w}
  [Field k] [CommRing A] [Algebra k A]
  [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]

/-- The actual homogeneous k-vector space, including negative degrees. -/
def fieldComponent (G : NonnegativeGrading A) (U : ModuleGrading G M)
    (hzero : Connected k G) (j : ℤ) : Submodule k M where
  __ := U.piece j
  smul_mem' a m hm := by
    have ha : algebraMap k A a ∈ G.piece 0 := (hzero _).mpr ⟨a, rfl⟩
    change a • m ∈ U.piece j
    rw [← IsScalarTower.algebraMap_smul A a m]
    simpa only [zero_vadd] using
      (SetLike.GradedSMul.smul_mem (A := G.piece) (B := U.piece) ha hm)

noncomputable def fieldHilbertFunction (G : NonnegativeGrading A)
    (U : ModuleGrading G M) (hzero : Connected k G) (j : ℤ) : ℤ :=
  (Module.finrank k (fieldComponent k G U hzero j) : ℤ)

end P103.HilbertSerreDimension

namespace Specs.P103.HilbertSerreDimension

open _root_.P103.Graded _root_.P103.HilbertSerreLength
open _root_.P103.HilbertSerreDimension
open _root_.P103.Specs.Ch06.LinearGradedNormalization
open _root_.P103.Specs.Ch06.DimensionConventions

universe u v w x

/-- The annihilator is homogeneous, with no finiteness assumption. -/
def annihilatorHomogeneousType : Prop :=
  ∀ {A : Type v} {M : Type w} [CommRing A] [AddCommGroup M] [Module A M]
    (G : NonnegativeGrading A) (_U : ModuleGrading G M),
    ∀ a ∈ Module.annihilator A M, ∀ i : ℤ,
      (DirectSum.decompose G.piece a i : A) ∈ Module.annihilator A M

/-- Finiteness of the dimension of every nonzero finite module in scope. -/
def finiteDimensionType : Prop :=
  ∀ (k : Type u) {A : Type v} {M : Type w}
    [Field k] [CommRing A] [Algebra k A]
    [AddCommGroup M] [Module A M] [Nontrivial M] [Module.Finite A M]
    (G : NonnegativeGrading A),
    Connected k G → Specs.P103.Graded.standardValue G →
      ∃ d : ℕ, moduleDimensionValue A M = (d : WithBot ℕ∞)

/-- Identifies Lemma 6.9's length coefficients with actual k-dimensions.
Finiteness is asserted separately, so `finrank` cannot hide infinite pieces. -/
def finiteComponentsType : Prop :=
  ∀ (k : Type u) {A : Type v} {M : Type w}
    [Field k] [CommRing A] [Nontrivial A] [Algebra k A]
    [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [Module.Finite A M] (G : NonnegativeGrading A) (U : ModuleGrading G M)
    (hzero : Connected k G), Specs.P103.Graded.standardValue G →
      (∀ j, Module.Finite k (fieldComponent k G U hzero j)) ∧
      fieldHilbertFunction k G U hzero = hilbertFunction G U

/-- Ordinary normalization proves dimension invariance for the faithful
affine algebra after any field extension, in particular k ⊂ k(u). -/
def baseChangeDimensionType : Prop :=
  ∀ (k : Type u) (K : Type v) (C : Type x)
    [Field k] [Field K] [Algebra k K] [CommRing C] [Nontrivial C]
    [Algebra k C] [Algebra.FiniteType k C],
    ringKrullDim (TensorProduct k K C) = ringKrullDim C

/-- Rationality over the structural field before identifying the exponent
with Krull dimension. This is a bridge to the accepted Artinian-base result. -/
def rationalType : Prop :=
  ∀ (k : Type u) {A : Type v} {M : Type w}
    [Field k] [CommRing A] [Nontrivial A] [Algebra k A]
    [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [Module.Finite A M] (G : NonnegativeGrading A) (U : ModuleGrading G M)
    (hzero : Connected k G), Specs.P103.Graded.standardValue G →
      (∀ j, Module.Finite k (fieldComponent k G U hzero j)) ∧
      ∃ (b : ℤ) (p : Polynomial ℤ) (e : ℕ) (q : Polynomial ℚ),
        RationalPresentation (fieldHilbertFunction k G U hzero) b p e ∧
        (e = 0 ∨ p.eval 1 ≠ 0) ∧
        EventuallyPolynomial (fieldHilbertFunction k G U hzero) q ∧
        (e = 0 → q = 0 ∧ ∃ J : ℤ, ∀ j ≥ J,
          fieldHilbertFunction k G U hzero j = 0) ∧
        (0 < e → q ≠ 0 ∧ q.natDegree = e - 1)

/-- The full nonzero-module assertion, including d = 0.  Nontriviality of
A follows from that of M and is made explicit for the connected field.
`d` is the dimension of A/Ann(M), not a chosen normalization rank. -/
def hilbertSerreType : Prop :=
  ∀ (k : Type u) {A : Type v} {M : Type w}
    [Field k] [CommRing A] [Nontrivial A] [Algebra k A]
    [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [Nontrivial M] [Module.Finite A M]
    (G : NonnegativeGrading A) (U : ModuleGrading G M)
    (hzero : Connected k G), Specs.P103.Graded.standardValue G →
      (∀ j, Module.Finite k (fieldComponent k G U hzero j)) ∧
      ∃ (d : ℕ) (b : ℤ) (p : Polynomial ℤ) (q : Polynomial ℚ),
        moduleDimensionValue A M = (d : WithBot ℕ∞) ∧
        RationalPresentation (fieldHilbertFunction k G U hzero) b p d ∧
        (d = 0 ∨ p.eval 1 ≠ 0) ∧
        EventuallyPolynomial (fieldHilbertFunction k G U hzero) q ∧
        (d = 0 → q = 0 ∧ ∃ J : ℤ, ∀ j ≥ J, U.piece j = ⊥) ∧
        (0 < d → q ≠ 0 ∧ q.natDegree = d - 1)

/-- The complete zero-module boundary convention, with the zero eventual
polynomial stated explicitly. -/
def zeroType : Prop :=
  ∀ (k : Type u) {A : Type v} {M : Type w}
    [Field k] [CommRing A] [Algebra k A]
    [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [Subsingleton M] (G : NonnegativeGrading A) (U : ModuleGrading G M)
    (hzero : Connected k G),
      moduleDimensionValue A M = ⊥ ∧
      fieldHilbertFunction k G U hzero = 0 ∧
      EventuallyPolynomial (fieldHilbertFunction k G U hzero) 0

end Specs.P103.HilbertSerreDimension
