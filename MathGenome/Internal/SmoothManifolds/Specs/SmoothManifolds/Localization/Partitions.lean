import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.SmoothMaps
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.LocallyFinite
import Mathlib.Algebra.BigOperators.Finprod

/-! Independent statements for M01.06. All smoothness is expressed using the
shared ambient-extension convention, including at boundary points. -/
namespace SmoothManifolds.PartitionData
open ModelData AtlasData Set Filter
open scoped Topology
universe u v w

/-- Scalar specialization of the shared Euclidean-valued smooth map test.
`Fin 1 → ℝ` is the canonical one-dimensional coordinate space. -/
def ScalarContDiffAt {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (r : ℕ∞) (A : Set (ModelChart n a M)) (f : M → ℝ) (x : M) : Prop :=
  MapData.ManifoldContDiffToEuclideanAt r A (fun y (_ : Fin 1) => f y) x

def ScalarContDiff {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (r : ℕ∞) (A : Set (ModelChart n a M)) (f : M → ℝ) : Prop :=
  ∀ x, ScalarContDiffAt r A f x

abbrev ScalarSmooth {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (A : Set (ModelChart n a M)) (f : M → ℝ) := ScalarContDiff (⊤ : ℕ∞) A f

/-- Closed supports, rather than just nonzero loci, form a locally finite family. -/
def IsSmoothPartition {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {ι : Type v} (A : Set (ModelChart n a M)) (ρ : ι → M → ℝ) : Prop :=
  (∀ i, ScalarSmooth A (ρ i)) ∧ (∀ i x, 0 ≤ ρ i x) ∧
    LocallyFinite (fun i => sectionSupport (ρ i)) ∧
    ∀ x, ∑ᶠ i, ρ i x = 1

/-- Subordination includes the entire closed support. -/
def IsSubordinate {M : Type u} [TopologicalSpace M] {ι : Type v}
    (U : ι → Set M) (ρ : ι → M → ℝ) : Prop :=
  ∀ i, ModelData.sectionSupport (ρ i) ⊆ U i

noncomputable def groupWeights {M : Type u} {ι : Type v} {κ : Type w}
    (q : ι → κ) (ρ : ι → M → ℝ) : κ → M → ℝ :=
  fun k x => ∑ᶠ i : {i // q i = k}, ρ i.val x

/-- The cutoff is exactly one on an open neighborhood of the whole set. -/
def IsCutoff {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (A U : Set M) (χ : M → ℝ) : Prop :=
  ScalarSmooth S.smoothStructure.val χ ∧
    (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧
    (∃ V : Set M, IsOpen V ∧ A ⊆ V ∧ EqOn χ (fun _ => 1) V) ∧
    sectionSupport χ ⊆ U

end SmoothManifolds.PartitionData

namespace Specs.SmoothManifolds.Localization.Partitions
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.PartitionData
open Set Filter
open scoped Topology
universe u v w

-- The public definitions are aliases of precisely these canonical data.
def ScalarContDiffAtType :=
  {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    ℕ∞ → Set (ModelChart n a M) → (M → ℝ) → M → Prop
def ScalarContDiffAtValue : ScalarContDiffAtType := @PartitionData.ScalarContDiffAt

def ScalarContDiffType :=
  {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    ℕ∞ → Set (ModelChart n a M) → (M → ℝ) → Prop
def ScalarContDiffValue : ScalarContDiffType := @PartitionData.ScalarContDiff

def ScalarSmoothType :=
  {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    Set (ModelChart n a M) → (M → ℝ) → Prop
def ScalarSmoothValue : ScalarSmoothType := @PartitionData.ScalarSmooth

def IsSmoothPartitionType :=
  {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    {ι : Type v} → Set (ModelChart n a M) → (ι → M → ℝ) → Prop
def IsSmoothPartitionValue : IsSmoothPartitionType := @PartitionData.IsSmoothPartition

def IsSubordinateType :=
  {M : Type u} → [TopologicalSpace M] → {ι : Type v} →
    (ι → Set M) → (ι → M → ℝ) → Prop
def IsSubordinateValue : IsSubordinateType := @PartitionData.IsSubordinate

def groupWeightsType :=
  {M : Type u} → {ι : Type v} → {κ : Type w} →
    (ι → κ) → (ι → M → ℝ) → κ → M → ℝ
noncomputable def groupWeightsValue : groupWeightsType := @PartitionData.groupWeights

def IsCutoffType :=
  {n : ℕ} → {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
    SmoothManifold n a M → Set M → Set M → (M → ℝ) → Prop
def IsCutoffValue : IsCutoffType := @PartitionData.IsCutoff

section Calculus

def scalarContDiffAt_iffType :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M],
  ∀ (r : ℕ∞) (A : Set (ModelChart n a M)) (f : M → ℝ) (x : M),
    ScalarContDiffAt r A f x ↔
      ContinuousAt f x ∧ ∀ e ∈ A, x ∈ e.source →
        ∃ U : Set (Euclidean n), IsOpen U ∧ (e x).val ∈ U ∧
          ∃ F : Euclidean n → ℝ, ContDiffOn ℝ r F U ∧
            (fun y => F (e y).val) =ᶠ[𝓝 x] f

def scalarContDiff_constType :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M],
  ∀ (r : ℕ∞) (A : Set (ModelChart n a M)) (c : ℝ),
    ScalarContDiff r A (fun _ => c)

def scalarContDiff_addType :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M],
  ∀ {r : ℕ∞} {A : Set (ModelChart n a M)} {f g : M → ℝ},
    ScalarContDiff r A f → ScalarContDiff r A g →
      ScalarContDiff r A (fun x => f x + g x)

def scalarContDiff_mulType :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M],
  ∀ {r : ℕ∞} {A : Set (ModelChart n a M)} {f g : M → ℝ},
    ScalarContDiff r A f → ScalarContDiff r A g →
      ScalarContDiff r A (fun x => f x * g x)

def scalarContDiff_invType :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M],
  ∀ {r : ℕ∞} {A : Set (ModelChart n a M)} {f : M → ℝ},
    ScalarContDiff r A f → (∀ x, f x ≠ 0) →
      ScalarContDiff r A (fun x => (f x)⁻¹)

/-- Smoothness of locally finite sums for the source's local-extension notion. -/
def scalarContDiff_finsumType :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M],
  ∀ {r : ℕ∞} {A : Set (ModelChart n a M)} {ι : Type v} {f : ι → M → ℝ},
    (∀ i, ScalarContDiff r A (f i)) →
    LocallyFinite (fun i => sectionSupport (f i)) →
      ScalarContDiff r A (fun x => ∑ᶠ i, f i x)

end Calculus

/-- Local ambient bump on either model, including its zero-dimensional case. -/
def exists_model_bumpType :=
  ∀ (n : ℕ) (a : ModelKind) (x : ModelSpace n a)
    (U : Set (ModelSpace n a)), IsOpen U → x ∈ U →
    ∃ f : ModelSpace n a → ℝ,
      ModelSmoothOn univ (fun y => f y.val) ∧
      (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧
      f =ᶠ[𝓝 x] (fun _ => 1) ∧
      sectionSupport f ⊆ U ∧ IsCompact (sectionSupport f)

/-- Transported chart bumps extend smoothly by zero, with compact support. -/
def exists_local_bumpType :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (x : M) (U : Set M), IsOpen U → x ∈ U →
    ∃ f : M → ℝ, ScalarSmooth S.smoothStructure.val f ∧
      (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧
      f =ᶠ[𝓝 x] (fun _ => 1) ∧
      sectionSupport f ⊆ U ∧ IsCompact (sectionSupport f)

/-- Indexed by the original cover; unused indices can have weight zero.
This includes the empty cover when the manifold is empty. -/
def exists_smooth_partitionType :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) {ι : Type v} (U : ι → Set M),
    (∀ i, IsOpen (U i)) → (∀ x, ∃ i, x ∈ U i) →
    ∃ ρ : ι → M → ℝ,
      IsSmoothPartition S.smoothStructure.val ρ ∧ IsSubordinate U ρ

/-- Grouping retains smoothness, local finiteness, and closed-support subordination. -/
def group_smooth_partitionType :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {A : Set (ModelChart n a M)} {ι : Type v} {κ : Type w}
    {ρ : ι → M → ℝ} (q : ι → κ) (U : κ → Set M),
    IsSmoothPartition A ρ → (∀ i, sectionSupport (ρ i) ⊆ U (q i)) →
    IsSmoothPartition A (groupWeights q ρ) ∧ IsSubordinate U (groupWeights q ρ)

def exists_smooth_cutoffType :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (A U : Set M),
    IsClosed A → IsOpen U → A ⊆ U → ∃ χ : M → ℝ, IsCutoff S A U χ

def exists_compactly_supported_smooth_cutoffType :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (A U : Set M),
    IsCompact A → IsOpen U → A ⊆ U →
    ∃ χ : M → ℝ, IsCutoff S A U χ ∧ IsCompact (sectionSupport χ)

end Specs.SmoothManifolds.Localization.Partitions
