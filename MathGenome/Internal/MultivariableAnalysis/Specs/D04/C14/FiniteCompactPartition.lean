import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.EmbeddedManifoldCharts
import Mathlib.Topology.Algebra.Support

/-! Independent statements of finite compact localization (d04:14:partition, scope).
The functions are represented by globally smooth ambient extensions. Topological
supports and neighborhoods are taken in the subtype M. Arbitrary relative open
refinements and arbitrarily chosen charts at the points of K are permitted.
Neither compactness of M nor positive dimension nor absence of boundary is assumed. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace Specs.D04.C14.FiniteCompactPartition
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
namespace Model

def PartitionNear {n : ℕ} (M : Set (E n)) (K : Set M)
    {ι : Type*} (U : ι → Set M) (m : ℕ) (a : Fin m → ι)
    (f : Fin m → E n → ℝ) : Prop :=
  (∀ i, ContDiff ℝ ∞ (f i)) ∧
  (∀ i (x : M), 0 ≤ f i x) ∧
  (∀ i, IsCompact (tsupport (fun x : M => f i x)) ∧
    tsupport (fun x : M => f i x) ⊆ U (a i)) ∧
  (∃ V : Set M, IsOpen V ∧ K ⊆ V ∧
    ∀ x ∈ V, ∑ i, f i x = 1) ∧
  (∀ x : M, (∑ i, f i x) ∈ Icc (0 : ℝ) 1)
end Model

/-- A caller may prescribe a chart and any further relative open neighborhood
at each point of K, before the weights are constructed. This is the support
control used for the small rectangles and half-boxes in Stokes. -/
def finite_partition_refinedType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}, IsEmbeddedManifold r k M →
  ∀ (K : Set M), IsCompact K →
  ∀ {ι : Type} (U : ι → Set M), (∀ a, IsOpen (U a)) → K ⊆ ⋃ a, U a →
  ∀ (c : K → EmbeddedChart r k n M),
    (∀ p, (p.val : E n) ∈ (c p).ambient) →
  ∀ (W : K → Set M), (∀ p, IsOpen (W p)) → (∀ p, p.val ∈ W p) →
  ∃ (m : ℕ) (a : Fin m → ι) (p : Fin m → K) (f : Fin m → E n → ℝ),
    Model.PartitionNear M K U m a f ∧
    ∀ i, tsupport (fun x : M => f i x) ⊆
      W (p i) ∩ Subtype.val ⁻¹' (c (p i)).ambient

/-- The ordinary finite partition theorem, with one chart for every support. -/
def finite_partitionType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}, IsEmbeddedManifold r k M →
  ∀ (K : Set M), IsCompact K →
  ∀ {ι : Type} (U : ι → Set M), (∀ a, IsOpen (U a)) → K ⊆ ⋃ a, U a →
  ∃ (m : ℕ) (a : Fin m → ι) (f : Fin m → E n → ℝ),
    Model.PartitionNear M K U m a f ∧
    ∀ i, ∃ c : EmbeddedChart r k n M,
      tsupport (fun x : M => f i x) ⊆ Subtype.val ⁻¹' c.ambient

/-- The same theorem with the paper's ambient compact set and relative-open
cover predicates. The inverse images merely view those subsets inside M. -/
def finite_partition_ambientType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}, IsEmbeddedManifold r k M →
  ∀ (K : Set (E n)), Compact K → K ⊆ M →
  ∀ {ι : Type} (U : ι → Set (E n)),
    (∀ a, RelativelyOpen M (U a)) → K ⊆ ⋃ a, U a →
  ∃ (m : ℕ) (a : Fin m → ι) (f : Fin m → E n → ℝ),
    Model.PartitionNear M (Subtype.val ⁻¹' K) (fun a => Subtype.val ⁻¹' U a) m a f ∧
    ∀ i, ∃ c : EmbeddedChart r k n M,
      tsupport (fun x : M => f i x) ⊆ Subtype.val ⁻¹' c.ambient

end Specs.D04.C14.FiniteCompactPartition
