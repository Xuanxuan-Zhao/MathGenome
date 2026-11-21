import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Examples.SpheresAndTori
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Field

/-! The literal antipodal quotient, with the coinduced quotient topology.
The charts use all of R^n, in the ordering obtained by deleting coordinate i.
All definitions and statements include n = 0. -/
namespace SmoothManifolds.ProjectiveData
open ModelData AtlasData SphereTorusData Set
open scoped BigOperators

/-- The antipodal involution on the shared sum-of-squares sphere. -/
def antipode {n : ℕ} (x : Sphere n) : Sphere n :=
  ⟨-x.val, by simpa [squareSum] using x.property⟩

@[simp] theorem antipode_antipode {n : ℕ} (x : Sphere n) :
    antipode (antipode x) = x := by apply Subtype.ext; simp [antipode]

/-- Exactly the two-point antipodal orbits, including S^0. -/
def antipodalSetoid (n : ℕ) : Setoid (Sphere n) where
  r x y := x = y ∨ x = antipode y
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      rintro x y (h | h)
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h, antipode_antipode])
    trans := by
      rintro x y z (h | h) (k | k)
      · exact Or.inl (h.trans k)
      · exact Or.inr (h.trans k)
      · exact Or.inr (by rw [h, k])
      · exact Or.inl (by rw [h, k, antipode_antipode]) }

abbrev RealProjectiveSpace (n : ℕ) := Quotient (antipodalSetoid n)

def projectiveProjection {n : ℕ} : Sphere n → RealProjectiveSpace n :=
  Quotient.mk (antipodalSetoid n)

/-- Ratios are invariant even where the denominator vanishes; only the
nonvanishing locus is used as a chart domain. -/
noncomputable def projectiveRatios {n : ℕ} (i : Fin (n + 1)) :
    RealProjectiveSpace n → Euclidean n :=
  Quotient.lift (fun x => fun j => x.val (i.succAbove j) / x.val i) (by
    rintro x y (h | h)
    · rw [h]
    · rw [h]; funext j; simp [antipode])

def projectiveLocus {n : ℕ} (i : Fin (n + 1)) : Set (RealProjectiveSpace n) :=
  projectiveProjection '' {x : Sphere n | x.val i ≠ 0}

/-- The representative with i-th coordinate 1. -/
def insertOne {n : ℕ} (i : Fin (n + 1)) (y : Euclidean n) : Euclidean (n + 1) :=
  i.insertNth 1 y

/-- Normalize the representative to the actual sphere before taking its orbit. -/
noncomputable def normalizedRepresentative {n : ℕ} (i : Fin (n + 1))
    (y : Euclidean n) : Sphere n :=
  ⟨fun j => insertOne i y j / Real.sqrt (1 + squareSum y), by
    have hnonneg : 0 ≤ squareSum y := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hpos : 0 < 1 + squareSum y := by positivity
    have hs : (Real.sqrt (1 + squareSum y)) ^ 2 = 1 + squareSum y :=
      Real.sq_sqrt hpos.le
    change (∑ j, (insertOne i y j / Real.sqrt (1 + squareSum y)) ^ 2) = 1
    simp_rw [div_pow]
    rw [← Finset.sum_div, hs]
    have hi : (∑ j, (insertOne i y j) ^ 2) = 1 + squareSum y := by
      rw [Fin.sum_univ_succAbove _ i]
      simp [insertOne, squareSum]
    rw [hi, div_self hpos.ne']⟩

noncomputable def projectiveInverse {n : ℕ} (i : Fin (n + 1))
    (y : Euclidean n) : RealProjectiveSpace n :=
  projectiveProjection (normalizedRepresentative i y)

/-- Ambient rational expression for the transition from chart i to chart j. -/
noncomputable def projectiveTransition {n : ℕ} (i j : Fin (n + 1)) (y : Euclidean n) :
    Euclidean n := fun k => insertOne i y (j.succAbove k) / insertOne i y j

def projectiveOverlap {n : ℕ} (i j : Fin (n + 1)) : Set (Euclidean n) :=
  {y | insertOne i y j ≠ 0}

/-- Maps are specified on their complete domains, with no artificial restriction
on the image of a ratio chart. -/
def IsProjectiveChart {n : ℕ} (i : Fin (n + 1))
    (c : ModelChart n .euclidean (RealProjectiveSpace n)) : Prop :=
  c.source = projectiveLocus i ∧ c.target = univ ∧
    (∀ p ∈ c.source, (c p).val = projectiveRatios i p) ∧
    (∀ y, c.symm y = projectiveInverse i y.val)

def projectiveAtlas (n : ℕ) : Set (ModelChart n .euclidean (RealProjectiveSpace n)) :=
  {c | ∃ i, IsProjectiveChart i c}

end SmoothManifolds.ProjectiveData

namespace Specs.SmoothManifolds.Examples.RealProjectiveSpace
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.SphereTorusData
  _root_.SmoothManifolds.ProjectiveData Set Topology

/-- The space has precisely the quotient topology and exactly antipodal fibers;
its quotient map is open, and it has the required separation/countability. -/
def projectiveTopologyType : Prop :=
  ∀ n : ℕ, IsOpenQuotientMap (@projectiveProjection n) ∧
    (∀ x y : Sphere n, projectiveProjection x = projectiveProjection y ↔
      x = y ∨ x = antipode y) ∧
    T2Space (RealProjectiveSpace n) ∧ SecondCountableTopology (RealProjectiveSpace n)

/-- Each requested ratio chart exists on its full nonzero-coordinate locus. -/
def projectiveChartsType : Prop :=
  ∀ (n : ℕ) (i : Fin (n + 1)), ∃ c, IsProjectiveChart i c

/-- Both the nonvanishing denominator and the precise rational transition
are asserted, together with smoothness on their entire open domain. -/
def projectiveTransitionsType : Prop :=
  ∀ (n : ℕ) (i j : Fin (n + 1)),
    IsOpen (projectiveOverlap i j) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (projectiveTransition i j) (projectiveOverlap i j) ∧
    ∀ p ∈ projectiveLocus i, p ∈ projectiveLocus j →
      projectiveRatios i p ∈ projectiveOverlap i j ∧
      projectiveRatios j p = projectiveTransition i j (projectiveRatios i p)

/-- The specified charts cover and generate the natural boundaryless maximal
smooth structure, on the same antipodal quotient as above. -/
def projectiveManifoldType : Prop :=
  ∀ n : ℕ, IsContDiffAtlas (⊤ : ℕ∞) (projectiveAtlas n) ∧
    ∃ P : SmoothManifold n .euclidean (RealProjectiveSpace n),
      P.topologicalManifold.atlas = projectiveAtlas n ∧
      P.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (projectiveAtlas n)

def projectiveZeroType : Prop := Nonempty (RealProjectiveSpace 0 ≃ₜ PUnit.{1})

/-- Public name and exact canonical representation for later direction spaces. -/
def RealProjectiveSpaceType := ℕ → Type
abbrev RealProjectiveSpaceValue : RealProjectiveSpaceType :=
  _root_.SmoothManifolds.ProjectiveData.RealProjectiveSpace

end Specs.SmoothManifolds.Examples.RealProjectiveSpace
