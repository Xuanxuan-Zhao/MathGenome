import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RootSystems
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Set.Card

/-! Abstract, Euclidean statements for the rank-two part of LA-E01, and the
root-string facts used in LA-E02. No Lie algebra realization is assumed. -/
namespace LieAlgebrasAndRepresentations
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Cartan number, with the root being evaluated first. -/
noncomputable def rootCartan (b a : E) : ℝ :=
  2 * inner ℝ b a / inner ℝ a a

/-- The four reduced crystallographic types of rank two. -/
inductive RankTwoKind where
  | A₁A₁ | A₂ | B₂ | G₂
  deriving DecidableEq

/-- Exact coefficient models, in a short-root/long-root basis. -/
def rankTwoCoefficients : RankTwoKind → Finset (ℤ × ℤ)
  | .A₁A₁ => {(1,0), (-1,0), (0,1), (0,-1)}
  | .A₂ => {(1,0), (-1,0), (0,1), (0,-1), (1,1), (-1,-1)}
  | .B₂ => {(1,0), (-1,0), (0,1), (0,-1), (1,1), (-1,-1), (2,1), (-2,-1)}
  | .G₂ => {(1,0), (-1,0), (0,1), (0,-1), (1,1), (-1,-1), (2,1), (-2,-1),
      (3,1), (-3,-1), (3,2), (-3,-2)}

def rankTwoCount : RankTwoKind → ℕ
  | .A₁A₁ => 4
  | .A₂ => 6
  | .B₂ => 8
  | .G₂ => 12

/-- The coordinate model embedded in its Euclidean space. -/
def rankTwoRootSet (k : RankTwoKind) (a b : E) : Set E :=
  (fun p : ℤ × ℤ => p.1 • a + p.2 • b) '' (rankTwoCoefficients k : Set (ℤ × ℤ))

/-- The Gram matrix fixes one positive scale for each irreducible model;
for the orthogonal type the two lengths are independent. -/
def rankTwoGram (k : RankTwoKind) (a b : E) : Prop :=
  match k with
  | .A₁A₁ => inner ℝ a b = 0
  | .A₂ => inner ℝ b b = inner ℝ a a ∧ 2 * inner ℝ a b = -inner ℝ b b
  | .B₂ => inner ℝ b b = 2 * inner ℝ a a ∧ 2 * inner ℝ a b = -inner ℝ b b
  | .G₂ => inner ℝ b b = 3 * inner ℝ a a ∧ 2 * inner ℝ a b = -inner ℝ b b

/-- An exact normal form, including its metric. The independent spanning
basis identifies the displayed coefficient model with the original root set.
Its Gram matrix gives the isometry after positive rescaling on each component. -/
def RankTwoModel (R : Set E) (k : RankTwoKind) : Prop :=
  ∃ a ∈ R, ∃ b ∈ R, LinearIndependent ℝ ![a,b] ∧
    Submodule.span ℝ ({a,b} : Set E) = ⊤ ∧
    rankTwoGram k a b ∧ R = rankTwoRootSet k a b

namespace RankTwoSpecs
universe u

def cartanRestrictionsType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (R : Set E), RootAxioms R → ∀ a ∈ R, ∀ b ∈ R,
  LinearIndependent ℝ ![a, b] →
    (rootCartan a b, rootCartan b a) ∈
      ({(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1), (-1, -2), (-2, -1),
        (1, 3), (3, 1), (-1, -3), (-3, -1)} : Set (ℝ × ℝ))

/-- Angle restriction in an equivalent exact algebraic form: the squared
cosine is 0, 1/4, 1/2 or 3/4. -/
def angleRestrictionType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (R : Set E), RootAxioms R → ∀ a ∈ R, ∀ b ∈ R,
  LinearIndependent ℝ ![a, b] →
    Real.cos (InnerProductGeometry.angle a b) ^ 2 ∈ ({0, 1/4, 1/2, 3/4} : Set ℝ)

def lengthRestrictionType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (R : Set E), RootAxioms R → ∀ a ∈ R, ∀ b ∈ R,
  inner ℝ a b ≠ 0 →
    inner ℝ a a = inner ℝ b b ∨
    inner ℝ a a = 2 * inner ℝ b b ∨
    inner ℝ b b = 2 * inner ℝ a a ∨
    inner ℝ a a = 3 * inner ℝ b b ∨
    inner ℝ b b = 3 * inner ℝ a a

/-- Positive inner product gives a difference root, including all distinct
roots, not just a preselected rank-two basis. -/
def differenceRootType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (R : Set E), RootAxioms R → ∀ a ∈ R, ∀ b ∈ R,
  a ≠ b → 0 < inner ℝ a b → a - b ∈ R

def sumRootType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (R : Set E), RootAxioms R → ∀ a ∈ R, ∀ b ∈ R,
  a ≠ -b → inner ℝ a b < 0 → a + b ∈ R

/-- The entire string is unbroken, has at most four roots, and its endpoints
satisfy the Cartan-number formula. -/
def rootStringType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (R : Set E), RootAxioms R → ∀ a ∈ R, ∀ b ∈ R,
  LinearIndependent ℝ ![a, b] → ∃ p q : ℕ,
    p + q ≤ 3 ∧ rootCartan b a = (q : ℝ) - (p : ℝ) ∧
    ∀ z : ℤ, b + z • a ∈ R ↔ -(q : ℤ) ≤ z ∧ z ≤ (p : ℤ)

/-- Exhaustion and uniqueness as exact metric coordinate normal forms. -/
def classificationType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (R : Set E), IsRootSystem R → Module.finrank ℝ E = 2 →
    ∃! k : RankTwoKind, RankTwoModel R k

def rootCountType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ (R : Set E) (k : RankTwoKind), RankTwoModel R k → R.ncard = rankTwoCount k

/-- The normal forms determine actual linear equivalences of root sets.
The two scale factors agree on each irreducible type; for A₁ ⊔ A₁ they
act separately on its orthogonal basis lines. Matching these Gram entries
and the spanning basis determines the metric on the entire space. -/
def metricEquivalenceType.{v} : Prop :=
  ∀ {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F],
  ∀ (R : Set E) (S : Set F) (k : RankTwoKind),
  RankTwoModel R k → RankTwoModel S k →
  ∃ (f : E ≃ₗ[ℝ] F) (a b : E) (s t : ℝ),
    a ∈ R ∧ b ∈ R ∧ LinearIndependent ℝ ![a,b] ∧
    Submodule.span ℝ ({a,b} : Set E) = ⊤ ∧ rankTwoGram k a b ∧
    f '' R = S ∧ 0 < s ∧ 0 < t ∧ (k ≠ .A₁A₁ → s = t) ∧
    inner ℝ (f a) (f a) = s * inner ℝ a a ∧
    inner ℝ (f b) (f b) = t * inner ℝ b b ∧
    inner ℝ (f a) (f b) = s * inner ℝ a b

end RankTwoSpecs
end LieAlgebrasAndRepresentations
