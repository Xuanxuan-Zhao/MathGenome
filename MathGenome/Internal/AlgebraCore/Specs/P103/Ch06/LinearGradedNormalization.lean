import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.GradedInterfaces
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Defs

/-! The degree-one normalization step of paper.tex:1158.  The degree-zero
piece is identified with the image of the specified field, and standardness
uses the already fixed internal grading interface.  No domain or reducedness
hypothesis is imposed. -/
namespace P103.Specs.Ch06.LinearGradedNormalization

open P103.Graded
universe u v

/-- The structural field is exactly the degree-zero piece. -/
def Connected (k : Type u) {C : Type v} [Field k] [CommRing C]
    [Algebra k C] (G : NonnegativeGrading C) : Prop :=
  ∀ c : C, c ∈ G.piece 0 ↔ ∃ a : k, algebraMap k C a = c

/-- Degree preservation from the standard polynomial grading. -/
def IsGraded {k : Type u} {C : Type v} [Field k] [CommRing C]
    [Algebra k C] (G : NonnegativeGrading C) {d : ℕ}
    (g : MvPolynomial (Fin d) k →ₐ[k] C) : Prop :=
  ∀ (n : ℕ) (f : MvPolynomial (Fin d) k), f.IsHomogeneous n →
    g f ∈ G.piece (n : ℤ)

def normalization_mapType : Prop :=
  ∀ (k : Type u) (C : Type v) [Field k] [Infinite k] [CommRing C]
    [Nontrivial C] [Algebra k C] (G : NonnegativeGrading C),
    Connected k G → Specs.P103.Graded.standardValue G →
    ∃ (d : ℕ) (g : MvPolynomial (Fin d) k →ₐ[k] C),
      Function.Injective g ∧ g.Finite ∧ IsGraded G g ∧
      (∀ i, g (MvPolynomial.X i) ∈ G.piece 1) ∧
      ringKrullDim C = (d : WithBot ℕ∞)

def normalization_elementsType : Prop :=
  ∀ (k : Type u) (C : Type v) [Field k] [Infinite k] [CommRing C]
    [Nontrivial C] [Algebra k C] (G : NonnegativeGrading C),
    Connected k G → Specs.P103.Graded.standardValue G →
    ∃ (d : ℕ) (y : Fin d → C),
      (∀ i, y i ∈ G.piece 1) ∧ AlgebraicIndependent k y ∧
      Module.Finite (Algebra.adjoin k (Set.range y)) C ∧
      ringKrullDim C = (d : WithBot ℕ∞)

/-- Explicitly record the zero-dimensional boundary case. -/
def dimension_zeroType : Prop :=
  ∀ (k : Type u) (C : Type v) [Field k] [Infinite k] [CommRing C]
    [Nontrivial C] [Algebra k C] (G : NonnegativeGrading C),
    Connected k G → Specs.P103.Graded.standardValue G →
    ringKrullDim C = 0 → Module.Finite k C

end P103.Specs.Ch06.LinearGradedNormalization
