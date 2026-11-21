import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.MapClasses
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Count

/-! Independent statements for paper.tex:1143–1163. Coordinates are measured in
all ambient dimensions, with the usual product Lebesgue measure (the empty
product is counting measure on the one-point zero-dimensional space). -/
namespace SmoothManifolds.SardData
open ModelData AtlasData MapData MapClassData Set
universe u v

/-- Nullity tested in every member of an atlas, with no measurability assumption. -/
def NullInCharts {n : ℕ} {a : ModelKind} {N : Type v} [TopologicalSpace N]
    (A : Set (ModelChart n a N)) (s : Set N) : Prop :=
  ∀ d ∈ A, MeasureTheory.volume ((fun y => (d y).val) '' (s ∩ d.source)) = 0

/-- Nullity in the given maximal smooth structure. -/
def IsNull {n : ℕ} {a : ModelKind} {N : Type v} [TopologicalSpace N]
    (T : SmoothManifold n a N) (s : Set N) : Prop :=
  NullInCharts T.smoothStructure.val s

/-- Critical values of the full tangent differential; boundary normals are retained. -/
def criticalValues {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N) : Set N :=
  f '' {p | ¬ IsSubmersionAt S T f p}

end SmoothManifolds.SardData

namespace Specs.SmoothManifolds.Ch04.Sard
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.MapClassData _root_.SmoothManifolds.SardData Set
universe u v

def NullInChartsType := {n : ℕ} → {a : ModelKind} → {N : Type v} →
  [TopologicalSpace N] → Set (ModelChart n a N) → Set N → Prop
def NullInChartsValue : NullInChartsType := @SardData.NullInCharts

def IsNullType := {n : ℕ} → {a : ModelKind} → {N : Type v} →
  [TopologicalSpace N] → SmoothManifold n a N → Set N → Prop
def IsNullValue : IsNullType := @SardData.IsNull

def criticalValuesType := {m n : ℕ} → {a b : ModelKind} → {M : Type u} → {N : Type v} →
  [TopologicalSpace M] → [TopologicalSpace N] →
  SmoothManifold m a M → SmoothManifold n b N → (M → N) → Set N
def criticalValuesValue : criticalValuesType := @SardData.criticalValues

/-- The zero-dimensional coordinate convention is exactly counting measure. -/
def coordinate_volume_zero_eq_countType : Prop :=
  (MeasureTheory.volume : MeasureTheory.Measure (Euclidean 0)) = MeasureTheory.Measure.count

/-- Any covering family of compatible smooth charts gives the same null sets. -/
def nullInCharts_iffType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {N : Type v} [TopologicalSpace N]
    (T : SmoothManifold n a N) (A : Set (ModelChart n a N)),
    IsAtlas A →
    (∀ e ∈ A, ∀ d ∈ T.smoothStructure.val, ContDiffCompatible (⊤ : ℕ∞) e d) →
    ∀ s : Set N, NullInCharts A s ↔ IsNull T s

/-- A compatible chart, even with a different permitted model kind, preserves nullity.
Smooth identity-coordinate germs express compatibility on the overlap. -/
def compatible_chart_nullType : Prop :=
  ∀ {n : ℕ} {a b : ModelKind} {N : Type v} [TopologicalSpace N]
    (T : SmoothManifold n a N) (s : Set N), IsNull T s →
    ∀ e : ModelChart n b N,
    (∀ d ∈ T.smoothStructure.val, ∀ p ∈ d.source, p ∈ e.source →
      ChartContDiffAt (⊤ : ℕ∞) d e id p) →
    MeasureTheory.volume ((fun y => (e y).val) '' (s ∩ e.source)) = 0

def sardType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N),
    IsSmoothMap S T f → IsNull T (criticalValues S T f)

def image_null_of_dimension_ltType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N),
    IsSmoothMap S T f → m < n → IsNull T (Set.range f)

def regularValues_denseType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N),
    IsSmoothMap S T f → 0 < n → Dense {y | IsRegularValue S T f y}

def criticalValues_target_zeroType : Prop :=
  ∀ {m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold 0 b N) (f : M → N),
    IsSmoothMap S T f → criticalValues S T f = ∅

end Specs.SmoothManifolds.Ch04.Sard
