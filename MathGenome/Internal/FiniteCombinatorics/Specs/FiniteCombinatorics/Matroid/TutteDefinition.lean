import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.Foundation
import Mathlib.Combinatorics.Matroid.Sum
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finset.Powerset

/-! W77: the rank-subset polynomial in two variables over ℤ.
The variables indexed by 0 and 1 are x and y. Grounds, rather than
ambient types, are finite. The disjoint sum uses the explicit inclusions
`Sum.inl` and `Sum.inr`, so element indices are retained. -/
namespace FiniteCombinatorics.Matroid
open Set
universe u v w

/-- Integer-coefficient polynomials in the two variables x (0), y (1). -/
abbrev TuttePolynomial := MvPolynomial (Fin 2) ℤ

namespace Expected

/-- The nonnegative rank deficit in the x exponent. -/
noncomputable def rankDeficit {α : Type u} (M : _root_.Matroid α) [M.Finite]
    (A : Set α) : ℕ :=
  (M.eRk M.E).toNat - (M.eRk A).toNat

/-- The nonnegative cardinality deficit in the y exponent, on subsets of E. -/
noncomputable def rankNullity {α : Type u} (M : _root_.Matroid α) [M.Finite]
    (A : Set α) : ℕ :=
  A.ncard - (M.eRk A).toNat

/-- Sum over exactly all subsets of the finite ground, including ∅. -/
noncomputable def tutte {α : Type u} (M : _root_.Matroid α) [M.Finite] :
    TuttePolynomial := by
  classical
  exact ∑ A ∈ M.ground_finite.toFinset.powerset,
    (MvPolynomial.X 0 - 1) ^ rankDeficit M (A : Set α) *
    (MvPolynomial.X 1 - 1) ^ rankNullity M (A : Set α)

/-- Simultaneous substitution, also into other commutative rings (e.g. ℤ[t]). -/
noncomputable def tutteSubstitute {R : Type w} [CommRing R]
    (P : TuttePolynomial) (x y : R) : R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) (fun i => if i = 0 then x else y) P

/-- Integer evaluation of the Tutte polynomial. -/
noncomputable def tutteEvaluate {α : Type u} (M : _root_.Matroid α) [M.Finite]
    (x y : ℤ) : ℤ := tutteSubstitute (tutte M) x y

/-- The canonical Mathlib direct sum, with two disjoint indexed ground sets. -/
def directSum {α : Type u} {β : Type v} (M : _root_.Matroid α)
    (N : _root_.Matroid β) : _root_.Matroid (α ⊕ β) := M.sum N

instance directSumFinite {α : Type u} {β : Type v}
    (M : _root_.Matroid α) (N : _root_.Matroid β) [M.Finite] [N.Finite] :
    (directSum M N).Finite := by
  constructor
  rw [directSum, _root_.Matroid.sum_ground]
  exact (M.ground_finite.image Sum.inl).union (N.ground_finite.image Sum.inr)

def rankDeficitType := ∀ {α : Type u}, (M : _root_.Matroid α) → [M.Finite] → Set α → ℕ

def rankNullityType := ∀ {α : Type u}, (M : _root_.Matroid α) → [M.Finite] → Set α → ℕ

def tutteType := ∀ {α : Type u}, (M : _root_.Matroid α) → [M.Finite] → TuttePolynomial

def tutteSubstituteType := ∀ {R : Type w}, [CommRing R] → TuttePolynomial → R → R → R

def tutteEvaluateType := ∀ {α : Type u}, (M : _root_.Matroid α) → [M.Finite] → ℤ → ℤ → ℤ

def directSumType := ∀ {α : Type u} {β : Type v},
  _root_.Matroid α → _root_.Matroid β → _root_.Matroid (α ⊕ β)

def rankDeficitCast : Prop := ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite]
  (A : Set α), A ⊆ M.E → (rankDeficit M A : ℤ) = rank M M.E - rank M A

def rankNullityCast : Prop := ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite]
  (A : Set α), A ⊆ M.E → (rankNullity M A : ℤ) = (A.ncard : ℤ) - rank M A

def tutteEmpty : Prop := ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite],
  M.E = ∅ → tutte M = 1

def tutteSubstituteVariables : Prop := ∀ {R : Type w} [CommRing R] (x y : R),
  tutteSubstitute (MvPolynomial.X 0) x y = x ∧
  tutteSubstitute (MvPolynomial.X 1) x y = y

def tutteSubstituteSum : Prop := ∀ {α : Type u} {R : Type w} [CommRing R]
  (M : _root_.Matroid α) [M.Finite] (x y : R),
  tutteSubstitute (tutte M) x y =
    ∑ A ∈ M.ground_finite.toFinset.powerset,
      (x - 1) ^ rankDeficit M (A : Set α) * (y - 1) ^ rankNullity M (A : Set α)

def directSumIsFinite : Prop := ∀ {α : Type u} {β : Type v}
  (M : _root_.Matroid α) (N : _root_.Matroid β) [M.Finite] [N.Finite],
  (directSum M N).Finite

def directSumGround : Prop := ∀ {α : Type u} {β : Type v}
  (M : _root_.Matroid α) (N : _root_.Matroid β),
  (directSum M N).E = Sum.inl '' M.E ∪ Sum.inr '' N.E

def directSumGroundDisjoint : Prop := ∀ {α : Type u} {β : Type v}
  (M : _root_.Matroid α) (N : _root_.Matroid β),
  Disjoint (Sum.inl '' M.E : Set (α ⊕ β)) (Sum.inr '' N.E)

def directSumIndep : Prop := ∀ {α : Type u} {β : Type v}
  (M : _root_.Matroid α) (N : _root_.Matroid β) (I : Set (α ⊕ β)),
  (directSum M N).Indep I ↔ M.Indep (Sum.inl ⁻¹' I) ∧ N.Indep (Sum.inr ⁻¹' I)

def directSumRank : Prop := ∀ {α : Type u} {β : Type v}
  (M : _root_.Matroid α) (N : _root_.Matroid β) [M.Finite] [N.Finite]
  (A : Set (α ⊕ β)), A ⊆ (directSum M N).E →
  rank (directSum M N) A = rank M (Sum.inl ⁻¹' A) + rank N (Sum.inr ⁻¹' A)

end Expected
end FiniteCombinatorics.Matroid
