import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.EntourageCalculus
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Bases.Finite

/-! The family and weighted-sum portions of paper.tex,
`d10:12:pseudometric` and `d10:12:countable-pseudometrics`.
No topology, separation, or nonemptiness of X is assumed.
The zero-distance quotient is allocated to PseudometricQuotient. -/
open Set Filter
open scoped Uniformity Topology
universe u v
namespace Specs.D10Topology.Ch12.PseudometricFamilies

/-- The coarsest uniformity imposing all the pseudometric tests.
Mathlib orders uniformities in the reverse direction to entourage inclusion. -/
@[instance_reducible]
def familyUniformity {X : Type u} {I : Type v} (p : I → PseudoMetricSpace X) :
    UniformSpace X := ⨅ i, (p i).toUniformSpace

def familyUniformityType := {X : Type u} → {I : Type v} →
  (I → PseudoMetricSpace X) → UniformSpace X
def familyUniformityValue : familyUniformityType := @familyUniformity

/-- A finite intersection with independently chosen positive radii. -/
def familyEntourage {X : Type u} {I : Type v} (p : I → PseudoMetricSpace X)
    (F : Set I) (ε : I → ℝ) : Set (X × X) :=
  ⋂ i ∈ F, {xy | @dist X (p i).toDist xy.1 xy.2 < ε i}
def familyEntourageType := {X : Type u} → {I : Type v} →
  (I → PseudoMetricSpace X) → Set I → (I → ℝ) → Set (X × X)
def familyEntourageValue : familyEntourageType := @familyEntourage

/-- Lean's index n corresponds to the paper's index n+1 (starting at 1). -/
noncomputable def weightedDistance {X : Type u} (p : ℕ → PseudoMetricSpace X)
    (x y : X) : ℝ :=
  ∑' n : ℕ, (2 : ℝ)⁻¹ ^ (n + 1) * min 1 (@dist X (p n).toDist x y)
def weightedDistanceType := {X : Type u} → (ℕ → PseudoMetricSpace X) → X → X → ℝ
noncomputable def weightedDistanceValue : weightedDistanceType := @weightedDistance

def SeparatesPairs {X : Type u} {I : Type v} (p : I → PseudoMetricSpace X) : Prop :=
  ∀ x y, x ≠ y → ∃ i, 0 < @dist X (p i).toDist x y
def separatesPairsType := {X : Type u} → {I : Type v} → (I → PseudoMetricSpace X) → Prop
def separatesPairsValue : separatesPairsType := @SeparatesPairs

/-- Zero distance on every pair, on arbitrary (including empty) types. -/
@[instance_reducible]
def zeroPseudometric (X : Type u) : PseudoMetricSpace X where
  dist _ _ := 0
  dist_self _ := rfl
  dist_comm _ _ := rfl
  dist_triangle _ _ _ := by simp

def zeroPseudometricType := (X : Type u) → PseudoMetricSpace X
def zeroPseudometricValue : zeroPseudometricType := zeroPseudometric

/-- Finite families, including n=0, extended by zero pseudometrics. -/
@[instance_reducible]
def zeroPadding {X : Type u} {n : ℕ} (p : Fin n → PseudoMetricSpace X)
    (k : ℕ) : PseudoMetricSpace X :=
  if h : k < n then p ⟨k, h⟩ else zeroPseudometric X
def zeroPaddingType := {X : Type u} → {n : ℕ} →
  (Fin n → PseudoMetricSpace X) → ℕ → PseudoMetricSpace X
def zeroPaddingValue : zeroPaddingType := @zeroPadding

/-- These finite intersections are exactly an entourage basis, including F=∅. -/
def family_uniformity_basis : Prop :=
  ∀ {X : Type u} {I : Type v} (p : I → PseudoMetricSpace X) (U : Set (X × X)),
  U ∈ @uniformity X (familyUniformity p) ↔
    ∃ F : Set I, F.Finite ∧ ∃ ε : I → ℝ, (∀ i ∈ F, 0 < ε i) ∧
      familyEntourage p F ε ⊆ U

def family_empty : Prop :=
  ∀ {X : Type u} {I : Type v} [IsEmpty I] (p : I → PseudoMetricSpace X),
    familyUniformity p = ⊤

def weighted_summable : Prop :=
  ∀ {X : Type u} (p : ℕ → PseudoMetricSpace X) (x y : X),
    Summable (fun n : ℕ => (2 : ℝ)⁻¹ ^ (n + 1) * min 1 (@dist X (p n).toDist x y))

def weighted_pseudometric_axioms : Prop :=
  ∀ {X : Type u} (p : ℕ → PseudoMetricSpace X),
    Ch09.MetricConventions.PseudometricAxioms (weightedDistance p)

def weighted_bounded : Prop :=
  ∀ {X : Type u} (p : ℕ → PseudoMetricSpace X) (x y : X),
    0 ≤ weightedDistance p x y ∧ weightedDistance p x y ≤ 1

def weighted_zero_iff : Prop :=
  ∀ {X : Type u} (p : ℕ → PseudoMetricSpace X) (x y : X),
    weightedDistance p x y = 0 ↔ ∀ n, @dist X (p n).toDist x y = 0

/-- Actual equality of uniform structures, with the specified distance formula. -/
def weighted_uniformity : Prop :=
  ∀ {X : Type u} (p : ℕ → PseudoMetricSpace X),
    ∃ d : PseudoMetricSpace X,
      (@dist X d.toDist) = weightedDistance p ∧ d.toUniformSpace = familyUniformity p

def weighted_metric_iff : Prop :=
  ∀ {X : Type u} (p : ℕ → PseudoMetricSpace X),
    Ch09.MetricConventions.MetricAxioms (weightedDistance p) ↔ SeparatesPairs p

def zero_uniformity : Prop :=
  ∀ (X : Type u), (zeroPseudometric X).toUniformSpace = ⊤

def zero_padding_uniformity : Prop :=
  ∀ {X : Type u} {n : ℕ} (p : Fin n → PseudoMetricSpace X),
    familyUniformity (zeroPadding p) = familyUniformity p

def finite_weighted_uniformity : Prop :=
  ∀ {X : Type u} {n : ℕ} (p : Fin n → PseudoMetricSpace X),
    ∃ d : PseudoMetricSpace X,
      (@dist X d.toDist) = weightedDistance (zeroPadding p) ∧
      d.toUniformSpace = familyUniformity p ∧
      (Ch09.MetricConventions.MetricAxioms (@dist X d.toDist) ↔ SeparatesPairs p)

/-- Any finite indexing type can be enumerated and zero-padded, without an
inhabitedness assumption on either the index type or X. -/
def finite_indexed_uniformity : Prop :=
  ∀ {X : Type u} {I : Type v} [Finite I] (p : I → PseudoMetricSpace X),
    ∃ (n : ℕ) (e : Fin n ≃ I) (d : PseudoMetricSpace X),
      (@dist X d.toDist) = weightedDistance (zeroPadding (fun j => p (e j))) ∧
      d.toUniformSpace = familyUniformity p ∧
      (Ch09.MetricConventions.MetricAxioms (@dist X d.toDist) ↔ SeparatesPairs p)

def empty_weighted_distance : Prop :=
  ∀ (X : Type u), weightedDistance (fun _ => zeroPseudometric X) = fun _ _ => 0

end Specs.D10Topology.Ch12.PseudometricFamilies
