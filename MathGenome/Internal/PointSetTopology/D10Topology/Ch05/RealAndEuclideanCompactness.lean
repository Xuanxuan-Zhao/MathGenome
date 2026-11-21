import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.RealAndEuclideanCompactness
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.Compactness
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.Products
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Compact real intervals and Euclidean Heine–Borel, using the chapter 5
open-cover notion of subspace compactness. The coordinate homeomorphism
identifies the Euclidean topology with the chapter 3 finite product topology;
the norm formula and boundedness equivalence identify the precise metric
meaning of boundedness. No positive-dimension or nonemptiness condition is used.
-/

open Set

namespace D10Topology.Ch05

theorem real_interval_compact (a b : ℝ) : SubspaceCompact (Icc a b) :=
  (subspaceCompact_iff_isCompact _).mpr isCompact_Icc

theorem euclidean_product_homeomorph (n : ℕ) :
    @IsHomeomorph (EuclideanSpace ℝ (Fin n)) (Fin n → ℝ)
      inferInstance (Ch03.productTopology (fun _ => inferInstance))
      (fun x i => x i) := by
  rw [Ch03.productTopology_eq_pi]
  exact (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isHomeomorph

theorem euclidean_norm_formula (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ = Real.sqrt (∑ i : Fin n, (x i) ^ 2) := by
  simpa only [Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_eq x

theorem euclidean_bounded_iff_norm_bound (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) :
    Bornology.IsBounded K ↔ ∃ R : ℝ, ∀ x ∈ K, ‖x‖ ≤ R :=
  isBounded_iff_forall_norm_le

theorem heine_borel (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) :
    SubspaceCompact K ↔ IsClosed K ∧ ∃ R : ℝ, ∀ x ∈ K, ‖x‖ ≤ R := by
  rw [subspaceCompact_iff_isCompact, Metric.isCompact_iff_isClosed_bounded,
    euclidean_bounded_iff_norm_bound]

end D10Topology.Ch05
