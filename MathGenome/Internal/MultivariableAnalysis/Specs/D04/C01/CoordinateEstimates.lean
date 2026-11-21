import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.EuclideanInterfaces
import Mathlib.Topology.MetricSpace.Cauchy

/-! Independent propositions for `d04:01:coordinate-estimates`.
The reference objects are the shared Euclidean interface's objects. The norm
bounds hold even in dimension zero, which strengthens the positive-dimensional
statement. Bounded subsequences are allocated to `D04.C01.BoundedSubsequence`.
-/

open Filter Topology
namespace Specs.D04.C01.CoordinateEstimates
open Specs.D04.C01.EuclideanInterfaces.Model

def maxNorm_le_normType : Prop :=
  ∀ {n : ℕ} (x : E n), maxNorm x ≤ ‖x‖

def norm_le_sqrt_mul_maxNormType : Prop :=
  ∀ {n : ℕ} (x : E n), ‖x‖ ≤ Real.sqrt (n : ℝ) * maxNorm x

def norm_triangleType : Prop :=
  ∀ {n : ℕ} (x y : E n), ‖x + y‖ ≤ ‖x‖ + ‖y‖

def norm_reverse_triangleType : Prop :=
  ∀ {n : ℕ} (x y : E n), |‖x‖ - ‖y‖| ≤ ‖x - y‖

def tendsto_iff_coordinate_tendstoType : Prop :=
  ∀ {n : ℕ} (s : ℕ → E n) (x : E n),
    Tendsto s atTop (𝓝 x) ↔ ∀ i : Fin n, Tendsto (fun k => s k i) atTop (𝓝 (x i))

def norm_tendsto_iff_coordinate_tendstoType : Prop :=
  ∀ {n : ℕ} (s : ℕ → E n) (x : E n),
    Tendsto (fun k => ‖s k - x‖) atTop (𝓝 0) ↔
      ∀ i : Fin n, Tendsto (fun k => s k i) atTop (𝓝 (x i))

def cauchySeq_iff_coordinate_cauchySeqType : Prop :=
  ∀ {n : ℕ} (s : ℕ → E n),
    CauchySeq s ↔ ∀ i : Fin n, CauchySeq (fun k => s k i)

def cauchySeq_has_limitType : Prop :=
  ∀ {n : ℕ} (s : ℕ → E n), CauchySeq s →
    ∃ x : E n, Tendsto s atTop (𝓝 x)

def euclidean_completeType : Prop :=
  ∀ n : ℕ, CompleteSpace (E n)

end Specs.D04.C01.CoordinateEstimates
