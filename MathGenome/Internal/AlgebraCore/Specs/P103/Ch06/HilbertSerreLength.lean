import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.GradedInterfaces
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Polynomial.HilbertPoly

/-!
Independent statements for paper.tex, Lemma 6.9 (1136–1149).
The scalar ring is the actual degree-zero piece, as in the accepted grading
interface. No nontriviality, positivity of generator count, or nonnegative
module grading is imposed.

A Laurent series is represented by its integer-indexed coefficients. A rational
presentation consists of a lower bound b and an ordinary integer polynomial p:
H = t^b p(t)/(1-t)^e. This is expressed by equality of formal power series after
removing t^b. Every Laurent polynomial numerator has such a presentation, and
its value at 1 is p(1). This avoids choosing an arbitrary truncation of negative
degrees. The eventual polynomial is a polynomial over Q evaluated on integers.
-/
namespace P103.HilbertSerreLength
open P103.Graded

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- Restriction of scalars along the inclusion A₀ → A. -/
instance baseModule (G : NonnegativeGrading A) : Module (Base G) M :=
  Module.compHom M (algebraMap (Base G) A)

/-- The j-th homogeneous piece as a module over the actual base A₀. -/
def component (G : NonnegativeGrading A) (U : ModuleGrading G M) (j : ℤ) :
    Submodule (Base G) M where
  __ := U.piece j
  smul_mem' b m hm := by
    change (b : A) • m ∈ U.piece j
    simpa using (SetLike.GradedSMul.smul_mem (A := G.piece) (B := U.piece)
      (i := (0 : ℤ)) (j := j) b.2 hm :
      (b : A) • m ∈ U.piece (0 + j))

/-- Coefficients of H_M. Finiteness of the pieces is a separate conclusion;
`toNat` here does not assume or certify it. -/
noncomputable def hilbertFunction (G : NonnegativeGrading A) (U : ModuleGrading G M)
    (j : ℤ) : ℤ := ((Module.length (Base G) (component G U j)).toNat : ℤ)

/-- Coefficient model of a formal Laurent series bounded below. -/
def BoundedBelow (h : ℤ → ℤ) : Prop := ∃ b : ℤ, ∀ j < b, h j = 0

/-- The power series obtained by removing a possible negative grading shift. -/
noncomputable def shiftedSeries (h : ℤ → ℤ) (b : ℤ) : PowerSeries ℤ :=
  PowerSeries.mk (fun n => h (b + n))

/-- H = t^b p(t)/(1-t)^e, with integer Laurent numerator t^b p(t). -/
def RationalPresentation (h : ℤ → ℤ) (b : ℤ) (p : Polynomial ℤ) (e : ℕ) : Prop :=
  (∀ j < b, h j = 0) ∧
    shiftedSeries h b * (1 - PowerSeries.X) ^ e = (p : PowerSeries ℤ)

/-- Eventual agreement, allowing arbitrary integer thresholds and shifts. -/
def EventuallyPolynomial (h : ℤ → ℤ) (q : Polynomial ℚ) : Prop :=
  ∃ J : ℤ, ∀ j ≥ J, (h j : ℚ) = q.eval (j : ℚ)

end P103.HilbertSerreLength

namespace Specs.P103.HilbertSerreLength
open _root_.P103.Graded _root_.P103.HilbertSerreLength

/-- The complete degreewise finite-length conclusion. -/
def finiteLengthType : Prop :=
  ∀ {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (G : NonnegativeGrading A) (U : ModuleGrading G M)
    [IsArtinianRing (Base G)] [Module.Finite A M],
    Specs.P103.Graded.standardValue G →
      ∀ j : ℤ, IsFiniteLength (Base G) (component G U j)

def boundedBelowType : Prop :=
  ∀ {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (G : NonnegativeGrading A) (U : ModuleGrading G M) [Module.Finite A M],
    BoundedBelow (hilbertFunction G U)

/-- No minimality of the denominator is required for existence. -/
def rationalType : Prop :=
  ∀ {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (G : NonnegativeGrading A) (U : ModuleGrading G M)
    [IsArtinianRing (Base G)] [Module.Finite A M],
    Specs.P103.Graded.standardValue G →
      ∃ (b : ℤ) (p : Polynomial ℤ) (e : ℕ),
        RationalPresentation (hilbertFunction G U) b p e

/-- A full analytic consequence for every rational presentation, so it also
covers every choice of reduced numerator and denominator. If e>0 and p(1)≠0,
then no factor 1-t cancels; natDegree together with q≠0 states degree e-1. -/
def coefficientTheoremType : Prop :=
  ∀ (h : ℤ → ℤ) (b : ℤ) (p : Polynomial ℤ) (e : ℕ),
    RationalPresentation h b p e →
      ∃ q : Polynomial ℚ, EventuallyPolynomial h q ∧
        (e = 0 → q = 0 ∧ ∃ J : ℤ, ∀ j ≥ J, h j = 0) ∧
        (0 < e → p.eval 1 ≠ 0 →
          q ≠ 0 ∧ q.natDegree = e - 1 ∧
            q.leadingCoeff = ((p.eval 1 : ℤ) : ℚ) / ((e - 1).factorial : ℚ))

/-- Explicit zero-module boundary case; also applies to a zero base since
unitality makes every module over a zero algebra trivial. -/
def zeroType : Prop :=
  ∀ {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (G : NonnegativeGrading A) (U : ModuleGrading G M) [Subsingleton M],
    hilbertFunction G U = 0

/-- Boundary case with an empty family of degree-one generators. -/
def zeroGeneratorsType : Prop :=
  ∀ {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (G : NonnegativeGrading A) (U : ModuleGrading G M) [Module.Finite A M],
    Algebra.adjoin (Base G) (∅ : Set A) = ⊤ →
      ∃ (b : ℤ) (p : Polynomial ℤ), RationalPresentation (hilbertFunction G U) b p 0

def zeroBaseType : Prop :=
  ∀ {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (G : NonnegativeGrading A) (U : ModuleGrading G M) [Subsingleton (Base G)],
    hilbertFunction G U = 0

/-- The Hilbert–Serre conclusion assembled for each finite graded module,
including a reduced presentation and its actual eventual polynomial. -/
def hilbertSerreType : Prop :=
  ∀ {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (G : NonnegativeGrading A) (U : ModuleGrading G M)
    [IsArtinianRing (Base G)] [Module.Finite A M],
    Specs.P103.Graded.standardValue G →
      (∀ j : ℤ, IsFiniteLength (Base G) (component G U j)) ∧
      ∃ (b : ℤ) (p : Polynomial ℤ) (e : ℕ) (q : Polynomial ℚ),
        RationalPresentation (hilbertFunction G U) b p e ∧
        (e = 0 ∨ p.eval 1 ≠ 0) ∧
        EventuallyPolynomial (hilbertFunction G U) q ∧
        (e = 0 → q = 0 ∧ ∃ J : ℤ, ∀ j ≥ J, hilbertFunction G U j = 0) ∧
        (0 < e → q ≠ 0 ∧ q.natDegree = e - 1 ∧
          q.leadingCoeff = ((p.eval 1 : ℤ) : ℚ) / ((e - 1).factorial : ℚ))

end Specs.P103.HilbertSerreLength
