import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.PartitionConventions
import Mathlib.Topology.Algebra.Module.Basic

/-!
Independent interface for paper.tex, d10:15:patching.
An equation is represented by its set of solutions at each point. Affine
stability means closure under every finite real affine combination; negative
coefficients are allowed. The local maps have the actual subspace domains U i.
No extension of a local map, separation axiom, completeness, countability, or
local convexity is assumed. The products alone are extended by zero.
-/

open Set
universe u v w

namespace Specs.D10Topology.Ch15.AffinePatching

/-- Closure under all finite affine combinations, including the empty case. -/
def AffineStable {E : Type w} [AddCommGroup E] [Module ℝ E] (A : Set E) : Prop :=
  ∀ (n : ℕ) (c : Fin n → ℝ) (z : Fin n → E),
    (∑ j, c j) = 1 → (∀ j, z j ∈ A) → (∑ j, c j • z j) ∈ A

noncomputable def weightedExtension {X : Type u} {E : Type w}
    [AddCommGroup E] [Module ℝ E] (U : Set X) (φ : X → ℝ) (s : U → E) : X → E :=
  by
  classical
  exact fun x => if h : x ∈ U then φ x • s ⟨x, h⟩ else 0

noncomputable def affinePatch {X : Type u} {I : Type v} {E : Type w}
    [AddCommGroup E] [Module ℝ E] (U : I → Set X)
    (φ : I → X → Icc (0 : ℝ) 1) (s : ∀ i, U i → E) : X → E :=
  fun x => ∑ᶠ i, weightedExtension (U i) (fun y => (φ i y : ℝ)) (s i) x

def affineStableType : Type (w + 1) :=
  {E : Type w} → [AddCommGroup E] → [Module ℝ E] → Set E → Prop

def affineStableValue : affineStableType := fun A =>
  ∀ (n : ℕ) (c : Fin n → ℝ) (z : Fin n → _),
    (∑ j, c j) = 1 → (∀ j, z j ∈ A) → (∑ j, c j • z j) ∈ A

def weightedExtensionType : Type (max u w + 1) :=
  {X : Type u} → {E : Type w} → [AddCommGroup E] → [Module ℝ E] →
    (U : Set X) → (X → ℝ) → (U → E) → X → E

noncomputable def weightedExtensionValue : weightedExtensionType := by
  classical
  exact fun U φ s x => if h : x ∈ U then φ x • s ⟨x, h⟩ else 0

def affinePatchType : Type (max u v w + 1) :=
  {X : Type u} → {I : Type v} → {E : Type w} → [AddCommGroup E] → [Module ℝ E] →
    (U : I → Set X) → (I → X → Icc (0 : ℝ) 1) → (∀ i, U i → E) → X → E

noncomputable def affinePatchValue : affinePatchType := fun U φ s x =>
  ∑ᶠ i, weightedExtension (U i) (fun y => (φ i y : ℝ)) (s i) x

/-- The exact piecewise interpretation, with no choice of extension. -/
def weightedExtension_values : Prop :=
  ∀ {X : Type u} {E : Type w} [AddCommGroup E] [Module ℝ E]
    (U : Set X) (φ : X → ℝ) (s : U → E) (x : X),
    (∀ h : x ∈ U, weightedExtension U φ s x = φ x • s ⟨x, h⟩) ∧
    (x ∉ U → weightedExtension U φ s x = 0) ∧
    (φ x = 0 → weightedExtension U φ s x = 0)

/-- Closed-support subordination ensures continuity across the boundary. -/
def weightedExtension_continuous : Prop :=
  ∀ {X : Type u} {E : Type w} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace X] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] (U : Set X) (φ : X → ℝ) (s : U → E),
    IsOpen U → Continuous φ → closure {x | φ x ≠ 0} ⊆ U → Continuous s →
    Continuous (weightedExtension U φ s)

/-- Independence of the finite set used to evaluate the pointwise sum. -/
def affinePatch_eq_sum : Prop :=
  ∀ {X : Type u} {I : Type v} {E : Type w} [AddCommGroup E] [Module ℝ E]
    (U : I → Set X) (φ : I → X → Icc (0 : ℝ) 1) (s : ∀ i, U i → E)
    (x : X) (t : Finset I),
    (∀ i, i ∉ t → (φ i x : ℝ) = 0) →
    affinePatch U φ s x =
      ∑ i ∈ t, weightedExtension (U i) (fun y => (φ i y : ℝ)) (s i) x

/-- The same finite sum works throughout an open neighborhood of each point. -/
def affinePatch_locally_sum : Prop :=
  ∀ {X : Type u} {I : Type v} {E : Type w} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace X]
    (U : I → Set X) (φ : I → X → Icc (0 : ℝ) 1) (s : ∀ i, U i → E),
    PartitionConventions.SubordinatePartitionOfUnity U φ →
    ∀ x, ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ ∃ t : Finset I,
      ∀ y ∈ N, (∀ i, i ∉ t → (φ i y : ℝ) = 0) ∧
        (∑ i ∈ t, (φ i y : ℝ)) = 1 ∧
        affinePatch U φ s y =
          ∑ i ∈ t, weightedExtension (U i) (fun z => (φ i z : ℝ)) (s i) y

/-- The continuous patched map solves the same equation at every point. -/
def affine_patching : Prop :=
  ∀ {X : Type u} {I : Type v} {E : Type w} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace X] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E]
    (U : I → Set X) (φ : I → X → Icc (0 : ℝ) 1) (s : ∀ i, U i → E)
    (S : X → Set E),
    (∀ i, IsOpen (U i)) → (⋃ i, U i) = univ →
    PartitionConventions.SubordinatePartitionOfUnity U φ →
    (∀ i, Continuous (s i)) → (∀ i (x : U i), s i x ∈ S x.val) →
    (∀ x, AffineStable (S x)) →
    Continuous (affinePatch U φ s) ∧ ∀ x, affinePatch U φ s x ∈ S x

end Specs.D10Topology.Ch15.AffinePatching
