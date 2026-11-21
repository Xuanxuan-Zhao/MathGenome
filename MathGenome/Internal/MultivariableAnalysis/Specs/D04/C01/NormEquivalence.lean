import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.EuclideanInterfaces
import Mathlib.Analysis.Normed.Module.Seminorm.Norm
import Mathlib.Analysis.Asymptotics.Lemmas

/-! Independent statements for d04:01:norm-equivalence.
A real norm is represented by a real seminorm together with definiteness.
No continuity, topology compatibility, or comparison bound is assumed.
The induced topology is constructed from the seminorm itself. -/
noncomputable section
open Filter Topology Asymptotics
namespace Specs.D04.C01.NormEquivalence.Model
open Specs.D04.C01.EuclideanInterfaces.Model

/-- Definiteness turns an absolutely homogeneous subadditive seminorm into a norm. -/
def IsNorm {n : ℕ} (N : Seminorm ℝ (E n)) : Prop :=
  ∀ x, N x = 0 → x = 0

/-- The topology induced by the distance N(x-y), built without using Euclidean continuity. -/
def normTopology {n : ℕ} (N : Seminorm ℝ (E n)) : TopologicalSpace (E n) :=
  N.toAddGroupSeminorm.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace

end Specs.D04.C01.NormEquivalence.Model
namespace Specs.D04.C01.NormEquivalence
open Specs.D04.C01.EuclideanInterfaces.Model Model

def norm_equivalenceType : Prop :=
  ∀ {n : ℕ} (N : Seminorm ℝ (E n)), IsNorm N →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x, c * ‖x‖ ≤ N x ∧ N x ≤ C * ‖x‖

def norm_equivalence_zeroType : Prop :=
  ∀ (N : Seminorm ℝ (E 0)) (x : E 0), 1 * ‖x‖ ≤ N x ∧ N x ≤ 1 * ‖x‖

def norm_topology_eqType : Prop :=
  ∀ {n : ℕ} (N : Seminorm ℝ (E n)), IsNorm N →
    normTopology N = (inferInstance : TopologicalSpace (E n))

/-- All filter limits, including sequences and limits on restricted domains. -/
def norm_tendsto_iffType : Prop :=
  ∀ {n : ℕ} (N : Seminorm ℝ (E n)), IsNorm N →
    ∀ {α : Type} (l : Filter α) (f : α → E n) (a : E n),
      Tendsto f l (@nhds _ (normTopology N) a) ↔ Tendsto f l (𝓝 a)

def norm_compact_iffType : Prop :=
  ∀ {n : ℕ} (N : Seminorm ℝ (E n)), IsNorm N → ∀ K : Set (E n),
    @IsCompact _ (normTopology N) K ↔ Compact K

/-- Any natural little-o order, along any filter on increments, with both source
and target norms changed. In particular this covers relative remainder conditions. -/
def norm_littleO_iffType : Prop :=
  ∀ {n m : ℕ} (N : Seminorm ℝ (E n)) (M : Seminorm ℝ (E m)),
    IsNorm N → IsNorm M → ∀ (l : Filter (E n)) (r : E n → E m) (k : ℕ),
      (fun h => M (r h)) =o[l] (fun h => (N h) ^ k) ↔
        r =o[l] (fun h => ‖h‖ ^ k)

/-- The same proposed linear map and the same order of the remainder work for
any norms. The filter here is explicitly the punctured neighborhood induced by N. -/
def norm_derivative_remainder_iffType : Prop :=
  ∀ {n m : ℕ} (N : Seminorm ℝ (E n)) (M : Seminorm ℝ (E m)),
    IsNorm N → IsNorm M → ∀ (f : E n → E m) (a : E n)
      (A : E n →ₗ[ℝ] E m) (k : ℕ),
      (fun h => M (f (a + h) - f a - A h))
        =o[@nhdsWithin _ (normTopology N) 0 {0}ᶜ] (fun h => (N h) ^ k) ↔
      (fun h => f (a + h) - f a - A h)
        =o[𝓝[≠] 0] (fun h => ‖h‖ ^ k)

end Specs.D04.C01.NormEquivalence
