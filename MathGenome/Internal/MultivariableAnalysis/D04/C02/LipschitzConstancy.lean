import MathGenome.Internal.MultivariableAnalysis.D04.C02.SegmentMeanValue
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.LipschitzConstancy
import Mathlib.Analysis.Calculus.MeanValue

/-! The three conclusions of d04:02:zero-derivative. -/
noncomputable section
open Set Filter Topology
namespace D04

/-- The uniform derivative bound gives the same Lipschitz constant on a
convex open domain; differentiability does not require a continuous derivative. -/
theorem lipschitz_of_totalDerivative_bound {n m : ℕ}
    (U : Set (E n)) (f : E n → E m) (M : ℝ)
    (hU : IsOpen U) (hconv : ConvexSet U) (hf : TotalDifferentiableOn U f)
    (_hM : 0 ≤ M) (hbound : ∀ x ∈ U, ‖totalDerivative f x‖ ≤ M) :
    ∀ x ∈ U, ∀ y ∈ U, ‖f y - f x‖ ≤ M * ‖y - x‖ := by
  intro x hx y hy
  have hs : segment ℝ x y ⊆ U := hconv.segment_subset hx hy
  exact segment_mean_value_bound U f x y M hU hs
    (((totalDifferentiableOn_iff U f hU).mp hf).continuousOn.mono hs)
    (fun z hz _ _ => hf z (hs hz)) (fun z hz _ _ => hbound z (hs hz))

/-- The connected-open constancy theorem uses pairwise equality, so no
basepoint or nonempty-domain hypothesis is needed. -/
theorem constant_of_totalDerivative_zero {n m : ℕ}
    (U : Set (E n)) (f : E n → E m)
    (hU : IsOpen U) (hconn : Connected U) (hf : TotalDifferentiableOn U f)
    (hzero : ∀ x ∈ U, totalDerivative f x = 0) :
    ∀ x ∈ U, ∀ y ∈ U, f x = f y := by
  intro x hx y hy
  exact hU.is_const_of_fderiv_eq_zero hconn
    ((totalDifferentiableOn_iff U f hU).mp hf) hzero hx hy

/-- Continuity of the derivative bounds it near each point. Restrict to
an open convex ball and apply the uniform Lipschitz estimate. -/
theorem locally_lipschitz_of_crOn_one {n m : ℕ}
    (U : Set (E n)) (f : E n → E m) (hU : IsOpen U) (hf : CrOn 1 U f) :
    ∀ a ∈ U, ∃ r > 0, Metric.ball a r ⊆ U ∧
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ x ∈ Metric.ball a r, ∀ y ∈ Metric.ball a r,
          ‖f y - f x‖ ≤ M * ‖y - x‖ := by
  intro a ha
  have hf' : TotalDifferentiableOn U f ∧ ContinuousOn (totalDerivative f) U := hf
  have hc : ContinuousAt (fun x => ‖totalDerivative f x‖) a :=
    (hf'.2.continuousAt (hU.mem_nhds ha)).norm
  have hb : ∀ᶠ x in 𝓝 a, ‖totalDerivative f x‖ < ‖totalDerivative f a‖ + 1 :=
    hc.eventually_lt_const (lt_add_one _)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hU.mem_nhds ha) hb)
  have hsub : Metric.ball a r ⊆ U := fun x hx => (hball hx).1
  refine ⟨r, hr, hsub, ‖totalDerivative f a‖ + 1,
    le_of_lt (add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one), ?_⟩
  apply lipschitz_of_totalDerivative_bound (Metric.ball a r) f
    (‖totalDerivative f a‖ + 1) Metric.isOpen_ball (convex_ball a r)
  · exact (totalDifferentiableOn_iff _ f Metric.isOpen_ball).mpr
      (((totalDifferentiableOn_iff U f hU).mp hf'.1).mono hsub)
  · exact le_of_lt (add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one)
  · intro x hx
    exact (hball hx).2.le

end D04
