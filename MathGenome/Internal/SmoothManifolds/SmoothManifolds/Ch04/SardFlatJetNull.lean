import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch04.SardFlatJetNull
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Tactic.Positivity

open Set MeasureTheory Metric
open scoped ContDiff NNReal ENNReal Topology

namespace SardFlatJet

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A coarse Taylor bound, obtained by successive mean value estimates.
The factorial improvement is unnecessary for nullity. -/
lemma norm_iteratedFDeriv_le_pow (r j : ℕ) {U : Set E} {f : E → F}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    {x y : E} (hseg : segment ℝ x y ⊆ U) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z ∈ segment ℝ x y, ‖iteratedFDeriv ℝ (j + r) f z‖ ≤ C)
    (hzero : ∀ i, j ≤ i → i < j + r → iteratedFDeriv ℝ i f x = 0) :
    ‖iteratedFDeriv ℝ j f y‖ ≤ C * ‖y - x‖ ^ r := by
  induction r generalizing j y with
  | zero => simpa using hbound y (right_mem_segment ℝ x y)
  | succ r ih =>
    have hder : ∀ z ∈ segment ℝ x y,
        DifferentiableAt ℝ (iteratedFDeriv ℝ j f) z := by
      intro z hz
      exact ((hf z (hseg hz)).contDiffAt (hU.mem_nhds (hseg hz))).differentiableAt_iteratedFDeriv
        (by exact_mod_cast (show (j : ℕ∞) < ⊤ from WithTop.coe_lt_top j))
    have hb : ∀ z ∈ segment ℝ x y,
        ‖fderiv ℝ (iteratedFDeriv ℝ j f) z‖ ≤ C * ‖y - x‖ ^ r := by
      intro z hz
      rw [norm_fderiv_iteratedFDeriv]
      have hsub : segment ℝ x z ⊆ segment ℝ x y :=
        (convex_segment x y).segment_subset (left_mem_segment ℝ x y) hz
      have hi := ih (j + 1) (hseg := hsub.trans hseg)
        (hbound := fun w hw => by
          have he : j + 1 + r = j + Nat.succ r := by omega
          rw [he]
          exact hbound w (hsub hw))
        (hzero := fun i hji hir => hzero i (by omega) (by omega))
      exact hi.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le_of_mem_segment hz) r) hC)
    have hm := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le hder hb
      (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
    rw [hzero j le_rfl (by omega), sub_zero] at hm
    simpa [pow_succ, mul_assoc] using hm

/-- Taylor's estimate at a point where the first `k` derivatives vanish. -/
lemma norm_sub_le_pow_of_flat {U : Set E} {f : E → F}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (k : ℕ)
    {x y : E} (hseg : segment ℝ x y ⊆ U) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z ∈ segment ℝ x y, ‖iteratedFDeriv ℝ (k + 1) f z‖ ≤ C)
    (hzero : ∀ i, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i f x = 0) :
    ‖f y - f x‖ ≤ C * ‖y - x‖ ^ (k + 1) := by
  have hder : ∀ z ∈ segment ℝ x y, DifferentiableAt ℝ f z := by
    intro z hz
    exact (hf.differentiableOn (by simp) z (hseg hz)).differentiableAt (hU.mem_nhds (hseg hz))
  have hb : ∀ z ∈ segment ℝ x y, ‖fderiv ℝ f z‖ ≤ C * ‖y - x‖ ^ k := by
    intro z hz
    rw [← norm_iteratedFDeriv_one]
    have hsub : segment ℝ x z ⊆ segment ℝ x y :=
      (convex_segment x y).segment_subset (left_mem_segment ℝ x y) hz
    have hi := norm_iteratedFDeriv_le_pow k 1 hU hf (hsub.trans hseg) hC
      (fun w hw => by
        rw [Nat.add_comm 1 k]
        exact hbound w (hsub hw))
      (fun i hi hik => hzero i hi (by omega))
    exact hi.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le_of_mem_segment hz) k) hC)
  have hm := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le hder hb
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa [pow_succ, mul_assoc] using hm

/-- Locally on the flat stratum, `f` is Hölder with exponent `k+1`. -/
lemma locally_holder_on_vanishingJets {m n : ℕ} {U : Set (Fin m → ℝ)}
    {f : (Fin m → ℝ) → (Fin n → ℝ)} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (k : ℕ) (x : Fin m → ℝ) (hx : x ∈ vanishingJets U f k) :
    ∃ C : ℝ≥0, ∃ t ∈ 𝓝[vanishingJets U f k] x, HolderOnWith C (k + 1) f t := by
  have hcont := ((hf x hx.1).contDiffAt (hU.mem_nhds hx.1)).differentiableAt_iteratedFDeriv
    (m := k + 1) (by exact_mod_cast (show ((k + 1 : ℕ) : ℕ∞) < ⊤ from WithTop.coe_lt_top _)) |>.continuousAt
  have hn : ∀ᶠ z in 𝓝 x, ‖iteratedFDeriv ℝ (k + 1) f z‖ <
      ‖iteratedFDeriv ℝ (k + 1) f x‖ + 1 :=
    hcont.norm.eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hn (hU.mem_nhds hx.1))
  let C : ℝ≥0 := ⟨‖iteratedFDeriv ℝ (k + 1) f x‖ + 1, by positivity⟩
  refine ⟨C, ball x ε ∩ vanishingJets U f k,
    Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hε)) self_mem_nhdsWithin, ?_⟩
  intro y hy z hz
  have hseg := (convex_ball x ε).segment_subset hz.1 hy.1
  have hb : ∀ w ∈ segment ℝ z y, ‖iteratedFDeriv ℝ (k + 1) f w‖ ≤ (C : ℝ) :=
    fun w hw => (hball (hseg hw)).1.le
  have he := norm_sub_le_pow_of_flat hU hf k
    (fun w hw => (hball (hseg hw)).2) C.coe_nonneg hb hz.2.2
  have hd : dist (f y) (f z) ≤ (C : ℝ) * dist y z ^ (k + 1) := by
    simpa only [dist_eq_norm] using he
  have hexp : (((k : ℝ≥0) + 1 : ℝ≥0) : ℝ) = ((k + 1 : ℕ) : ℝ) := by simp
  rw [hexp, ENNReal.rpow_natCast]
  simpa only [edist_dist, ENNReal.ofReal_mul C.coe_nonneg,
    ENNReal.ofReal_pow (dist_nonneg), ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hd

/-- Hausdorff dimension packages the cube covering estimate, including its countable
localization; no measurability of the flat set or its image is needed. -/
theorem flat_jet_image_null : SardFlatJetSpecs.flatJetImageNull := by
  intro m n k hn hdim U f hU hf
  have hholder := dimH_image_le_of_locally_holder_on
    (show (0 : ℝ≥0) < k + 1 by positivity)
    (locally_holder_on_vanishingJets hU hf k)
  have hs : dimH (vanishingJets U f k) ≤ (m : ℝ≥0∞) := by
    calc
      _ ≤ dimH (univ : Set (Fin m → ℝ)) := dimH_mono (subset_univ _)
      _ = m := Real.dimH_univ_pi_fin m
  have hlt : (m : ℝ≥0∞) / (k + 1) < n := by
    rw [ENNReal.div_lt_iff (by simp) (by simp)]
    exact_mod_cast (show m < n * (k + 1) by simpa [Nat.mul_comm] using hdim)
  have hsmall : dimH (f '' vanishingJets U f k) < (n : ℝ≥0) :=
    hholder.trans_lt ((ENNReal.div_le_div_right hs _).trans_lt hlt)
  have hnull := hausdorffMeasure_of_dimH_lt hsmall
  rw [NNReal.coe_natCast] at hnull
  have hv : (Measure.hausdorffMeasure (n : ℝ) : Measure (Fin n → ℝ)) = volume := by
    simpa only [Fintype.card_fin] using (hausdorffMeasure_pi_real (ι := Fin n))
  rwa [hv] at hnull

end SardFlatJet
