import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold

/-! Independent finite matroid model specifications for paper.tex, Chapter 9.
The ambient type need not be finite: only the actual ground set is finite.
The common ground is explicit even when the family has no members. -/
namespace P205.Matroids

/-- Real coordinates indexed by the actual matroid ground, without ambient junk coordinates. -/
abbrev Coordinates {α : Type*} (M : Matroid α) := M.E → ℝ

/-- A finite family on one specified finite ground; no member is required when `k = 0`. -/
structure Family (α : Type*) (k : ℕ) where
  ground : Set α
  ground_finite : ground.Finite
  matroid : Fin k → Matroid α
  ground_eq : ∀ i, (matroid i).E = ground

instance {α : Type*} {k : ℕ} (F : Family α k) (i : Fin k) : (F.matroid i).Finite :=
  ⟨F.ground_eq i ▸ F.ground_finite⟩

end P205.Matroids

namespace Specs.P205.Matroids
open _root_.P205.Matroids
open scoped BigOperators
noncomputable section
universe u

def rankType := ∀ {α : Type u}, Matroid α → Set α → ℕ

def rankValue : rankType.{u} :=
  fun {_α} M S => (M.eRk S).toNat

def subsetSumType := ∀ {α : Type u} (M : Matroid α) [M.Finite], Coordinates M → Set α → ℝ

def subsetSumValue : subsetSumType.{u} :=
  fun {α} M _ x S => by
  classical
  letI := M.ground_finite.fintype
  exact ∑ e : M.E, if (e : α) ∈ S then x e else 0

def indicatorType := ∀ {α : Type u} (M : Matroid α), Set α → Coordinates M

def indicatorValue : indicatorType.{u} :=
  fun {α} M S e => by
  classical
  exact if (e : α) ∈ S then 1 else 0

def dotType := ∀ {α : Type u} (M : Matroid α) [M.Finite], Coordinates M → Coordinates M → ℝ

def dotValue : dotType.{u} :=
  fun {α} M _ w x => by
  classical
  letI := M.ground_finite.fintype
  exact ∑ e : M.E, w e * x e

def rankInequalitiesType := ∀ {α : Type u} (M : Matroid α) [M.Finite], Set (Coordinates M)

def rankInequalitiesValue : rankInequalitiesType.{u} :=
  fun {α} M _ => {x | (∀ e, 0 ≤ x e) ∧
  ∀ S : Set α, S ⊆ M.E → subsetSumValue M x S ≤ (rankValue M S : ℝ)}

def baseInequalitiesType := ∀ {α : Type u} (M : Matroid α) [M.Finite], Set (Coordinates M)

def baseInequalitiesValue : baseInequalitiesType.{u} :=
  fun {_α} M _ => {x | x ∈ rankInequalitiesValue M ∧
  subsetSumValue M x M.E = (rankValue M M.E : ℝ)}

def independentIndicatorsType := ∀ {α : Type u} (M : Matroid α), Set (Coordinates M)

def independentIndicatorsValue : independentIndicatorsType.{u} :=
  fun {α} M => {x | ∃ I : Set α, M.Indep I ∧ x = indicatorValue M I}

def basisIndicatorsType := ∀ {α : Type u} (M : Matroid α), Set (Coordinates M)

def basisIndicatorsValue : basisIndicatorsType.{u} :=
  fun {α} M => {x | ∃ B : Set α, M.IsBase B ∧ x = indicatorValue M B}

def AssignableType := ∀ {α : Type u} {k : ℕ}, Family α k → Set α → Prop

def AssignableValue : AssignableType.{u} :=
  fun {α} {k} F I => ∃ parts : Fin k → Set α,
  (∀ i, (F.matroid i).Indep (parts i)) ∧ I = ⋃ i, parts i

def assignableSubsetsType := ∀ {α : Type u} {k : ℕ}, Family α k → Set α → Finset (Finset α)

def assignableSubsetsValue : assignableSubsetsType.{u} :=
  fun {α} {k} F S => by
  classical
  exact F.ground_finite.toFinset.powerset.filter
    (fun I => (↑I : Set α) ⊆ S ∧ AssignableValue F (↑I : Set α))

def qType := ∀ {α : Type u} {k : ℕ}, Family α k → Set α → ℕ

def qValue : qType.{u} :=
  fun {_α} {_k} F S => (assignableSubsetsValue F S).sup Finset.card

/-- Full proposition, without an assumed certificate. -/
def RankCanonical : Prop :=
  ∀ {α : Type u} (M : Matroid α) (S : Set α),
  rankValue M S = (M.eRk S).toNat

/-- Full proposition, without an assumed certificate. -/
def RankMaximum : Prop :=
  ∀ {α : Type u} (M : Matroid α) [M.Finite] (S : Set α), S ⊆ M.E →
  (∃ I : Set α, I ⊆ S ∧ M.Indep I ∧ I.ncard = rankValue M S) ∧
  (∀ J : Set α, J ⊆ S → M.Indep J → J.ncard ≤ rankValue M S)

/-- Full proposition, without an assumed certificate. -/
def BasisRank : Prop :=
  ∀ {α : Type u} (M : Matroid α) [M.Finite] (I S : Set α), S ⊆ M.E →
  (M.IsBasis I S ↔ I ⊆ S ∧ M.Indep I ∧ I.ncard = rankValue M S)

/-- Full proposition, without an assumed certificate. -/
def BaseRank : Prop :=
  ∀ {α : Type u} (M : Matroid α) [M.Finite] (B : Set α),
  M.IsBase B ↔ M.Indep B ∧ B.ncard = rankValue M M.E

/-- Full proposition, without an assumed certificate. -/
def IndependentRank : Prop :=
  ∀ {α : Type u} (M : Matroid α) [M.Finite] (I : Set α), I ⊆ M.E →
  (M.Indep I ↔ rankValue M I = I.ncard)

/-- Full proposition, without an assumed certificate. -/
def BasisExists : Prop :=
  ∀ {α : Type u} (M : Matroid α) [M.Finite] (S : Set α), S ⊆ M.E →
  ∃ I : Set α, M.IsBasis I S ∧ I.Finite ∧ I.ncard = rankValue M S

/-- Full proposition, without an assumed certificate. -/
def BaseExists : Prop :=
  ∀ {α : Type u} (M : Matroid α) [M.Finite],
  ∃ B : Set α, M.IsBase B ∧ B.Finite ∧ B.ncard = rankValue M M.E

/-- Full proposition, without an assumed certificate. -/
def RankEmpty : Prop :=
  ∀ {α : Type u} (M : Matroid α), rankValue M ∅ = 0

/-- Full proposition, without an assumed certificate. -/
def EmptyGroundBase : Prop :=
  ∀ {α : Type u} (M : Matroid α), M.E = ∅ →
  ∀ B : Set α, M.IsBase B ↔ B = ∅

/-- Full proposition, without an assumed certificate. -/
def IndicatorSum : Prop :=
  ∀ {α : Type u} (M : Matroid α) [M.Finite] (I S : Set α),
  subsetSumValue M (indicatorValue M I) S = ((I ∩ S ∩ M.E).ncard : ℝ)

/-- Full proposition, without an assumed certificate. -/
def IndicatorDot : Prop :=
  ∀ {α : Type u} (M : Matroid α) [M.Finite] (w : Coordinates M) (I : Set α),
  dotValue M w (indicatorValue M I) = subsetSumValue M w I

/-- Full proposition, without an assumed certificate. -/
def EmptyCoordinates : Prop :=
  ∀ {α : Type u} (M : Matroid α), M.E = ∅ →
  ∀ x y : Coordinates M, x = y

/-- Full proposition, without an assumed certificate. -/
def AssignableGround : Prop :=
  ∀ {α : Type u} {k : ℕ} (F : Family α k) (I : Set α),
  AssignableValue F I → I ⊆ F.ground

/-- Full proposition, without an assumed certificate. -/
def AssignableEmpty : Prop :=
  ∀ {α : Type u} {k : ℕ} (F : Family α k), AssignableValue F ∅

/-- Full proposition, without an assumed certificate. -/
def AssignableZero : Prop :=
  ∀ {α : Type u} (F : Family α 0) (I : Set α),
  AssignableValue F I ↔ I = ∅

/-- Full proposition, without an assumed certificate. -/
def QMaximum : Prop :=
  ∀ {α : Type u} {k : ℕ} (F : Family α k) (S : Set α),
  (∃ I : Set α, I ⊆ S ∧ AssignableValue F I ∧ I.ncard = qValue F S) ∧
  (∀ I : Set α, I ⊆ S → AssignableValue F I → I.ncard ≤ qValue F S)

/-- Full proposition, without an assumed certificate. -/
def QEmpty : Prop :=
  ∀ {α : Type u} {k : ℕ} (F : Family α k), qValue F ∅ = 0

/-- Full proposition, without an assumed certificate. -/
def QZero : Prop :=
  ∀ {α : Type u} (F : Family α 0) (S : Set α), qValue F S = 0

end
end Specs.P205.Matroids
