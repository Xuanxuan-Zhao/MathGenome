import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Topology.TietzeExtension
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import MathGenome.Internal.LinearPDE.P201.Heat.GaussianKernel
import MathGenome.Internal.LinearPDE.P201Specs.Heat.HeatBallMeanValue
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Piecewise
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace P201.Heat
open P201Specs.Heat (SpaceTime spaceTimeMeasure)

abbrev heatBall : P201Specs.Heat.heatBallType := P201Specs.Heat.heatBall
abbrev heatBallWeight : P201Specs.Heat.heatBallWeightType := P201Specs.Heat.heatBallWeight
abbrev IsClassicalCaloricOn : P201Specs.Heat.isClassicalCaloricOnType :=
  @P201Specs.Heat.IsClassicalCaloricOn
abbrev HeatBallMeanValueIdentity : P201Specs.Heat.heatBallMeanValueIdentityType :=
  @P201Specs.Heat.HeatBallMeanValueIdentity

lemma mem_heatBall {n : ℕ} {r : ℝ} {z₀ z : SpaceTime n} :
    z ∈ heatBall n r z₀ ↔
      z.2 < z₀.2 ∧ r ^ (-(n : ℤ)) < gaussianKernel n (z₀.2 - z.2) (z₀.1 - z.1) :=
  Iff.rfl

lemma gaussian_continuousAt_backward {n : ℕ} {z₀ z : SpaceTime n}
    (ht : z.2 < z₀.2) :
    ContinuousAt (fun w : SpaceTime n =>
      gaussianKernel n (z₀.2 - w.2) (z₀.1 - w.1)) z := by
  unfold gaussianKernel P201Specs.Heat.gaussianKernel
  apply ContinuousAt.mul
  · apply ContinuousAt.rpow_const
    · fun_prop
    · exact Or.inl (by positivity)
  · apply Real.continuous_exp.continuousAt.comp
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact ne_of_gt (mul_pos (by norm_num) (sub_pos.mpr ht))

theorem heatBallOpen : P201Specs.Heat.heatBallOpenStatement := by
  intro n r z₀
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have htime : {w : SpaceTime n | w.2 < z₀.2} ∈ 𝓝 z :=
    (isOpen_lt continuous_snd continuous_const).mem_nhds hz.1
  have hlevel : {w : SpaceTime n | r ^ (-(n : ℤ)) <
      gaussianKernel n (z₀.2 - w.2) (z₀.1 - w.1)} ∈ 𝓝 z :=
    (gaussian_continuousAt_backward hz.1).preimage_mem_nhds (Ioi_mem_nhds hz.2)
  exact inter_mem htime hlevel

lemma heatBall_measurableSet (n : ℕ) (r : ℝ) (z₀ : SpaceTime n) :
    MeasurableSet (heatBall n r z₀) :=
  (heatBallOpen n r z₀).measurableSet

lemma radius_threshold_rpow {n : ℕ} {r : ℝ} (hr : 0 < r) :
    (r ^ 2 : ℝ) ^ (-(n : ℝ) / 2) = r ^ (-(n : ℤ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * (-(n : ℝ) / 2) = -(n : ℝ) by ring]
  exact Real.rpow_neg_natCast r n

/-- The Gaussian superlevel inequality in logarithmic radial coordinates. -/
lemma gaussian_superlevel_iff {n : ℕ} {τ c : ℝ} (hτ : 0 < τ) (hc : 0 < c)
    (x : Space n) :
    c < gaussianKernel n τ x ↔
      ‖x‖ ^ 2 < 4 * τ *
        (Real.log ((4 * Real.pi * τ) ^ (-(n : ℝ) / 2)) - Real.log c) := by
  have hb : 0 < (4 * Real.pi * τ) ^ (-(n : ℝ) / 2) := Real.rpow_pos_of_pos (by positivity) _
  unfold gaussianKernel P201Specs.Heat.gaussianKernel
  rw [← Real.log_lt_log_iff hc (mul_pos hb (Real.exp_pos _)),
    Real.log_mul hb.ne' (Real.exp_pos _).ne', Real.log_exp]
  have h4τ : 0 < 4 * τ := by positivity
  constructor
  · intro h
    have h' : ‖x‖ ^ 2 / (4 * τ) <
        Real.log ((4 * Real.pi * τ) ^ (-(n : ℝ) / 2)) - Real.log c := by
      simp only [neg_div] at *
      linarith
    have := (div_lt_iff₀ h4τ).mp h'
    nlinarith
  · intro h
    have h' : ‖x‖ ^ 2 / (4 * τ) <
        Real.log ((4 * Real.pi * τ) ^ (-(n : ℝ) / 2)) - Real.log c :=
      (div_lt_iff₀ h4τ).mpr (by nlinarith)
    simp only [neg_div] at *
    linarith

lemma heatBall_mem_iff_norm_sq {n : ℕ} {r : ℝ} (hr : 0 < r) (z₀ z : SpaceTime n) :
    z ∈ heatBall n r z₀ ↔ z.2 < z₀.2 ∧
      ‖z₀.1 - z.1‖ ^ 2 < 2 * (n : ℝ) * (z₀.2 - z.2) *
        Real.log (r ^ 2 / (4 * Real.pi * (z₀.2 - z.2))) := by
  rw [mem_heatBall]
  apply and_congr_right
  intro ht
  rw [gaussian_superlevel_iff (sub_pos.mpr ht) (by positivity)]
  have hb : 0 < 4 * Real.pi * (z₀.2 - z.2) := by positivity
  rw [Real.log_rpow hb, Real.log_zpow, Real.log_div (by positivity) hb.ne', Real.log_pow]
  push_cast
  ring_nf

lemma heatBall_backwardTime_bound {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r)
    {z₀ z : SpaceTime n} (hz : z ∈ heatBall n r z₀) :
    z₀.2 - z.2 < r ^ 2 / (4 * Real.pi) := by
  have hτ : 0 < z₀.2 - z.2 := sub_pos.mpr hz.1
  have hb : 0 < 4 * Real.pi * (z₀.2 - z.2) := by positivity
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have he : Real.exp (-‖z₀.1 - z.1‖ ^ 2 / (4 * (z₀.2 - z.2))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by
      apply div_nonpos_of_nonpos_of_nonneg
      · exact neg_nonpos.mpr (sq_nonneg _)
      · positivity)
  have hlevel : r ^ (-(n : ℤ)) <
      (4 * Real.pi * (z₀.2 - z.2)) ^ (-(n : ℝ) / 2) := by
    have h := hz.2
    change r ^ (-(n : ℤ)) <
      (4 * Real.pi * (z₀.2 - z.2)) ^ (-(n : ℝ) / 2) * _ at h
    exact h.trans_le ((mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (mul_one _))
  rw [← radius_threshold_rpow hr] at hlevel
  have hbase := (Real.rpow_lt_rpow_iff_of_neg (by positivity : 0 < r ^ 2) hb
    (by linarith : -(n : ℝ) / 2 < 0)).mp hlevel
  apply (lt_div_iff₀ (by positivity : 0 < 4 * Real.pi)).mpr
  nlinarith

lemma heatBall_space_bound {n : ℕ} {r : ℝ} (hr : 0 < r)
    {z₀ z : SpaceTime n} (hz : z ∈ heatBall n r z₀) :
    ‖z₀.1 - z.1‖ ^ 2 < (n : ℝ) * r ^ 2 / (2 * Real.pi) := by
  have h := ((heatBall_mem_iff_norm_sq hr z₀ z).mp hz).2
  have hτ : 0 < z₀.2 - z.2 := sub_pos.mpr hz.1
  have hb : 0 < 4 * Real.pi * (z₀.2 - z.2) := by positivity
  have hlog := Real.log_le_sub_one_of_pos
    (div_pos (sq_pos_of_pos hr) hb)
  have hlog' : Real.log (r ^ 2 / (4 * Real.pi * (z₀.2 - z.2))) ≤
      r ^ 2 / (4 * Real.pi * (z₀.2 - z.2)) := by linarith
  have hprod := mul_le_mul_of_nonneg_left hlog'
    (by positivity : 0 ≤ 2 * (n : ℝ) * (z₀.2 - z.2))
  have he : 2 * (n : ℝ) * (z₀.2 - z.2) *
      (r ^ 2 / (4 * Real.pi * (z₀.2 - z.2))) =
      (n : ℝ) * r ^ 2 / (2 * Real.pi) := by
    field_simp
    ring
  rw [he] at hprod
  exact h.trans_le hprod

lemma heatBall_mono {n : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (z₀ : SpaceTime n) : heatBall n a z₀ ⊆ heatBall n b z₀ := by
  have h : b ^ (-(n : ℤ)) ≤ a ^ (-(n : ℤ)) := by
    rw [← Real.rpow_neg_natCast b n, ← Real.rpow_neg_natCast a n]
    exact Real.rpow_le_rpow_of_nonpos ha hab (neg_nonpos.mpr (Nat.cast_nonneg n))
  exact fun _ hz => ⟨hz.1, h.trans_lt hz.2⟩

lemma heatBall_subset_compact_product {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r)
    (z₀ : SpaceTime n) :
    heatBall n r z₀ ⊆
      Metric.closedBall z₀.1 ((n : ℝ) * r ^ 2 / (2 * Real.pi) + 1) ×ˢ
        Icc (z₀.2 - r ^ 2 / (4 * Real.pi)) z₀.2 := by
  intro z hz
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
    have h := heatBall_space_bound hr hz
    have hn' : 0 ≤ (n : ℝ) * r ^ 2 / (2 * Real.pi) := by positivity
    nlinarith [sq_nonneg (‖z₀.1 - z.1‖ - 1)]
  · have h := heatBall_backwardTime_bound hn hr hz
    exact ⟨by linarith, hz.1.le⟩

lemma heatBall_isCompact_closure {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r)
    (z₀ : SpaceTime n) : IsCompact (closure (heatBall n r z₀)) := by
  have hc := (isCompact_closedBall z₀.1 ((n : ℝ) * r ^ 2 / (2 * Real.pi) + 1)).prod
    (isCompact_Icc : IsCompact (Icc (z₀.2 - r ^ 2 / (4 * Real.pi)) z₀.2))
  exact hc.of_isClosed_subset isClosed_closure
    (closure_minimal (heatBall_subset_compact_product hn hr z₀) hc.isClosed)

lemma heatBall_space_linear_bound {n : ℕ} {r : ℝ} (hr : 0 < r)
    {z₀ z : SpaceTime n} (hz : z ∈ heatBall n r z₀) :
    ‖z₀.1 - z.1‖ < ((n : ℝ) + 1) * r := by
  have h := heatBall_space_bound hr hz
  have hc : (n : ℝ) * r ^ 2 / (2 * Real.pi) ≤ (n : ℝ) * r ^ 2 :=
    div_le_self (by positivity) (by linarith [Real.two_le_pi])
  have hn : (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hc' := mul_le_mul_of_nonneg_right hn (sq_nonneg r)
  apply (sq_lt_sq₀ (norm_nonneg _) (by positivity : 0 ≤ ((n : ℝ) + 1) * r)).mp
  nlinarith

/-- Heat balls shrink to their top, in the actual product topology. -/
lemma heatBall_shrinking {n : ℕ} (hn : 1 ≤ n) (z₀ : SpaceTime n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ → heatBall n r z₀ ⊆ Metric.ball z₀ ε := by
  refine ⟨min 1 (ε / ((n : ℝ) + 1)), by positivity, ?_⟩
  intro r hr hrδ z hz
  have hr1 : r < 1 := hrδ.trans_le (min_le_left _ _)
  have hrε : ((n : ℝ) + 1) * r < ε := by
    have h := (lt_div_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mp
      (hrδ.trans_le (min_le_right _ _))
    nlinarith
  have hspace := (heatBall_space_linear_bound hr hz).trans hrε
  have htime := heatBall_backwardTime_bound hn hr hz
  have hdiv : r ^ 2 / (4 * Real.pi) ≤ r ^ 2 :=
    div_le_self (sq_nonneg r) (by linarith [Real.two_le_pi])
  have ht : z₀.2 - z.2 < ε := by
    have hsq : r ^ 2 ≤ r := by
      nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hr1.le)]
    have hnr : r ≤ ((n : ℝ) + 1) * r := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    linarith
  rw [Metric.mem_ball, dist_comm, Prod.dist_eq, max_lt_iff]
  exact ⟨by simpa [dist_eq_norm] using hspace,
    by simpa [Real.dist_eq, abs_of_pos (sub_pos.mpr hz.1)] using ht⟩

lemma heatBall_bounded_of_continuousOn_closure {n : ℕ} (hn : 1 ≤ n) {r : ℝ}
    (hr : 0 < r) (z₀ : SpaceTime n) {u : SpaceTime n → ℝ}
    (hu : ContinuousOn u (closure (heatBall n r z₀))) :
    ∃ M : ℝ, ∀ z ∈ heatBall n r z₀, ‖u z‖ ≤ M := by
  obtain ⟨M, hM⟩ := (heatBall_isCompact_closure hn hr z₀).exists_bound_of_continuousOn hu
  exact ⟨M, fun z hz => hM z (subset_closure hz)⟩

/-- The axial slice persists for every backward time smaller than r²/(4π). -/
lemma heatBall_center_mem {n : ℕ} (hn : 1 ≤ n) {r τ : ℝ} (hr : 0 < r)
    (hτ : 0 < τ) (hτr : τ < r ^ 2 / (4 * Real.pi)) (z₀ : SpaceTime n) :
    (z₀.1, z₀.2 - τ) ∈ heatBall n r z₀ := by
  refine ⟨by dsimp; linarith, ?_⟩
  change r ^ (-(n : ℤ)) < gaussianKernel n (z₀.2 - (z₀.2 - τ)) (z₀.1 - z₀.1)
  rw [sub_sub_cancel, sub_self]
  unfold gaussianKernel P201Specs.Heat.gaussianKernel
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    neg_zero, zero_div, Real.exp_zero, mul_one]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hb : 4 * Real.pi * τ < r ^ 2 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 4 * Real.pi)).mp hτr
    nlinarith
  have hp := Real.rpow_lt_rpow_of_neg (by positivity : 0 < 4 * Real.pi * τ) hb
    (by linarith : -(n : ℝ) / 2 < 0)
  have he := radius_threshold_rpow (n := n) hr
  rwa [he] at hp

theorem heatBallTopInClosure : P201Specs.Heat.heatBallTopInClosureStatement := by
  intro n hn r hr z₀
  rw [Metric.mem_closure_iff]
  intro ε hε
  let τ : ℝ := min ε (r ^ 2 / (4 * Real.pi)) / 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτε : τ < ε := by
    dsimp [τ]
    have := min_le_left ε (r ^ 2 / (4 * Real.pi))
    linarith
  have hτr : τ < r ^ 2 / (4 * Real.pi) := by
    dsimp [τ]
    have := min_le_right ε (r ^ 2 / (4 * Real.pi))
    have : 0 < r ^ 2 / (4 * Real.pi) := by positivity
    linarith [min_le_right ε (r ^ 2 / (4 * Real.pi))]
  refine ⟨(z₀.1, z₀.2 - τ), heatBall_center_mem hn hr hτ hτr z₀, ?_⟩
  simpa [Prod.dist_eq, Real.dist_eq, sub_sub_cancel, abs_of_pos hτ] using And.intro hε hτε

theorem heatBallWeightNonnegative : P201Specs.Heat.heatBallWeightNonnegativeStatement := by
  intro n r hr z₀ z
  unfold P201Specs.Heat.heatBallWeight
  positivity


/-- A square-root form of the Gaussian superlevel inequality. -/
lemma gaussian_superlevel_half_bound {n : ℕ} {r τ : ℝ} (hr : 0 < r) (hτ : 0 < τ)
    (x : Space n) (hx : r ^ (-(n : ℤ)) < gaussianKernel n τ x) :
    1 ≤ r ^ ((n : ℝ) / 2) * (4 * Real.pi * τ) ^ (-(n : ℝ) / 4) *
      Real.exp (-‖x‖ ^ 2 / (8 * τ)) := by
  have h := (gaussian_superlevel_iff hτ (by positivity) x).mp hx
  rw [Real.log_rpow (by positivity), Real.log_zpow] at h
  push_cast at h
  rw [Real.rpow_def_of_pos hr, Real.rpow_def_of_pos (by positivity),
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  have hdiv : ‖x‖ ^ 2 / (8 * τ) <
      (n : ℝ) / 2 * Real.log r + (-(n : ℝ) / 4) * Real.log (4 * Real.pi * τ) := by
    apply (div_lt_iff₀ (by positivity : 0 < 8 * τ)).mpr
    nlinarith [h]
  simp only [neg_div]
  nlinarith

/-- The polynomial factor can be absorbed in a Gaussian with larger variance. -/
lemma gaussian_quadratic_bound {τ : ℝ} (hτ : 0 < τ) {a : ℝ} :
    (a / τ ^ 2) * Real.exp (-a / (8 * τ)) ≤
      (16 / τ) * Real.exp (-a / (16 * τ)) := by
  have he : (a / (16 * τ)) * Real.exp (-(a / (16 * τ))) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one _).trans
      (Real.exp_le_one_iff.mpr (by norm_num))
  have hm := mul_le_mul_of_nonneg_right he
    (show 0 ≤ (16 / τ) * Real.exp (-a / (16 * τ)) by positivity)
  convert hm using 1
  · rw [show -a / (8 * τ) = -(a / (16 * τ)) + -a / (16 * τ) by ring,
      Real.exp_add]
    field_simp
  · ring

/-- Pointwise integrable Gaussian envelope for the raw heat-ball density. -/
lemma heatBall_raw_density_bound {n : ℕ} {r τ : ℝ} (hr : 0 < r) (hτ : 0 < τ)
    (x : Space n) (hx : r ^ (-(n : ℤ)) < gaussianKernel n τ x) :
    ‖x‖ ^ 2 / τ ^ 2 ≤
      (16 * r ^ ((n : ℝ) / 2) * (4 * Real.pi) ^ (-(n : ℝ) / 4) /
        (16 * Real.pi) ^ (-(n : ℝ) / 2)) *
      (τ ^ ((n : ℝ) / 4 - 1) * gaussianKernel n (4 * τ) x) := by
  have hh := gaussian_superlevel_half_bound hr hτ x hx
  have hq := gaussian_quadratic_bound hτ (a := ‖x‖ ^ 2)
  calc
    ‖x‖ ^ 2 / τ ^ 2 ≤
        (r ^ ((n : ℝ) / 2) * (4 * Real.pi * τ) ^ (-(n : ℝ) / 4)) *
          ((‖x‖ ^ 2 / τ ^ 2) * Real.exp (-‖x‖ ^ 2 / (8 * τ))) := by
      have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ ‖x‖ ^ 2 / τ ^ 2)
      nlinarith only [hm]
    _ ≤ (r ^ ((n : ℝ) / 2) * (4 * Real.pi * τ) ^ (-(n : ℝ) / 4)) *
        ((16 / τ) * Real.exp (-‖x‖ ^ 2 / (16 * τ))) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ = _ := by
      unfold gaussianKernel P201Specs.Heat.gaussianKernel
      rw [show 4 * Real.pi * (4 * τ) = (16 * Real.pi) * τ by ring,
        Real.mul_rpow (by positivity : 0 ≤ 4 * Real.pi) hτ.le,
        Real.mul_rpow (by positivity : 0 ≤ 16 * Real.pi) hτ.le]
      rw [show 4 * (4 * τ) = 16 * τ by ring]
      have ht : τ ^ ((n : ℝ) / 4 - 1) * τ ^ (-(n : ℝ) / 2) =
          τ ^ (-(n : ℝ) / 4) / τ := by
        rw [← Real.rpow_add hτ,
          show (n : ℝ) / 4 - 1 + -(n : ℝ) / 2 = -(n : ℝ) / 4 - 1 by ring,
          Real.rpow_sub hτ, Real.rpow_one]
      rw [show τ ^ ((n : ℝ) / 4 - 1) *
          ((16 * Real.pi) ^ (-(n : ℝ) / 2) * τ ^ (-(n : ℝ) / 2) *
            Real.exp (-‖x‖ ^ 2 / (16 * τ))) =
          (16 * Real.pi) ^ (-(n : ℝ) / 2) *
            (τ ^ ((n : ℝ) / 4 - 1) * τ ^ (-(n : ℝ) / 2)) *
            Real.exp (-‖x‖ ^ 2 / (16 * τ)) by ring, ht]
      field_simp

/-- The Gaussian envelope is integrable down to time zero in every n ≥ 1. -/
lemma heatBall_gaussian_envelope_integrable {n : ℕ} (hn : 1 ≤ n) {T : ℝ} (hT : 0 < T) :
    Integrable (fun z : SpaceTime n =>
      z.2 ^ ((n : ℝ) / 4 - 1) * gaussianKernel n (4 * z.2) z.1)
      ((spatialMeasure n).prod (volume.restrict (Ioo 0 T))) := by
  have hm : Measurable (fun z : SpaceTime n =>
      z.2 ^ ((n : ℝ) / 4 - 1) * gaussianKernel n (4 * z.2) z.1) := by
    unfold gaussianKernel P201Specs.Heat.gaussianKernel
    fun_prop
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
    have hτpos : 0 < τ := hτ.1
    exact (gaussian_integrable_aux n (by positivity : 0 < 4 * τ)).const_mul _
  · have hp : IntegrableOn (fun τ : ℝ => τ ^ ((n : ℝ) / 4 - 1)) (Ioo 0 T) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hT).mpr (by
        have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        linarith)
    apply hp.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
    have hτpos : 0 < τ := hτ.1
    symm
    have hnn (x : Space n) :
        0 ≤ τ ^ ((n : ℝ) / 4 - 1) * gaussianKernel n (4 * τ) x := by
      unfold gaussianKernel P201Specs.Heat.gaussianKernel
      positivity
    simp_rw [Real.norm_of_nonneg (hnn _)]
    rw [integral_const_mul, gaussian_mass_aux n (by positivity : 0 < 4 * τ), mul_one]


theorem heatBallWeightIntegrable : P201Specs.Heat.heatBallWeightIntegrableStatement := by
  intro n hn r hr z₀
  let T := r ^ 2 / (4 * Real.pi)
  let S : Set (SpaceTime n) := univ ×ˢ Ioo 0 T
  let f : SpaceTime n → ℝ := fun z =>
    z.2 ^ ((n : ℝ) / 4 - 1) * gaussianKernel n (4 * z.2) z.1
  have hS : MeasurableSet S := MeasurableSet.univ.prod measurableSet_Ioo
  have hfi : IntegrableOn f S (spaceTimeMeasure n) := by
    have hi := heatBall_gaussian_envelope_integrable hn
      (show 0 < T by dsimp [T]; positivity)
    simpa only [IntegrableOn, S, f, spaceTimeMeasure, ← Measure.prod_restrict,
      Measure.restrict_univ]
      using hi
  have hi := (integrable_indicator_iff hS).mpr hfi
  have hmp : MeasurePreserving (fun z : SpaceTime n => z₀ - z)
      (spaceTimeMeasure n) (spaceTimeMeasure n) :=
    ((spatialMeasure n).measurePreserving_sub_left z₀.1).prod
      (volume.measurePreserving_sub_left z₀.2)
  have ht : Integrable (fun z => S.indicator f (z₀ - z)) (spaceTimeMeasure n) :=
    hmp.integrable_comp_of_integrable hi
  let C : ℝ := (1 / (4 * r ^ n)) *
    (16 * r ^ ((n : ℝ) / 2) * (4 * Real.pi) ^ (-(n : ℝ) / 4) /
      (16 * Real.pi) ^ (-(n : ℝ) / 2))
  have hdom := (ht.const_mul C).restrict (s := heatBall n r z₀)
  apply hdom.mono'
  · have hm : Measurable (heatBallWeight n r z₀) := by
      unfold heatBallWeight P201Specs.Heat.heatBallWeight
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (heatBall_measurableSet n r z₀)] with z hz
    have hτ : 0 < z₀.2 - z.2 := sub_pos.mpr hz.1
    have hzin : z₀ - z ∈ S :=
      ⟨mem_univ _, hτ, heatBall_backwardTime_bound hn hr hz⟩
    rw [Real.norm_of_nonneg (heatBallWeightNonnegative n r hr z₀ z),
      indicator_of_mem hzin]
    simpa only [C, f, heatBallWeight, P201Specs.Heat.heatBallWeight, Prod.fst_sub,
      Prod.snd_sub, mul_assoc] using
      mul_le_mul_of_nonneg_left (heatBall_raw_density_bound hr hτ (z₀.1 - z.1) hz.2)
        (by positivity : 0 ≤ 1 / (4 * r ^ n))




lemma gaussian_second_moment (n : ℕ) (hn : 1 ≤ n) :
    (∫ x : Space n, ‖x‖ ^ 2 * Real.exp (-‖x‖ ^ 2 / 4)) =
      2 * n * (4 * Real.pi) ^ ((n : ℝ) / 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : Module.finrank ℝ (Space n) = n := by
    simp [Space, P201Specs.Space]
  have : Nontrivial (Space n) := Module.finrank_pos_iff.mp (by omega : 0 < Module.finrank ℝ (Space n))
  have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by simpa only [Nat.cast_one] using (Nat.cast_sub (R := ℝ) hn)
  have hq0 : -1 < (n : ℝ) - 1 := by linarith
  have hq2 : -1 < (n : ℝ) + 1 := by linarith
  have h0 := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (n : ℝ) - 1)
    (b := 1/4) (by norm_num) hq0 (by norm_num)
  have h2 := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (n : ℝ) + 1)
    (b := 1/4) (by norm_num) hq2 (by norm_num)
  have e0 : (∫ y in Ioi (0 : ℝ), y ^ (n - 1) * Real.exp (-y ^ 2 / 4)) =
      (1 / 4 : ℝ) ^ (-(n : ℝ) / 2) * (1/2) * Real.Gamma ((n : ℝ) / 2) := by
    convert h0 using 1
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      dsimp only
      rw [← Real.rpow_natCast y (n-1), hc, Real.rpow_two]
      congr 2 <;> ring
    · congr 2 <;> ring
  have e2 : (∫ y in Ioi (0 : ℝ), y ^ (n - 1) * (y ^ 2 * Real.exp (-y ^ 2 / 4))) =
      (1 / 4 : ℝ) ^ (-((n : ℝ) + 2) / 2) * (1/2) * Real.Gamma (((n : ℝ) + 2) / 2) := by
    convert h2 using 1
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      dsimp only
      rw [← Real.rpow_natCast y (n-1), hc, ← Real.rpow_two y,
        ← mul_assoc, ← Real.rpow_add hy]
      congr 2 <;> ring
    · congr 2 <;> ring
  have hratio : (∫ y in Ioi (0 : ℝ), y ^ (n - 1) * (y ^ 2 * Real.exp (-y ^ 2 / 4))) =
      2 * n * (∫ y in Ioi (0 : ℝ), y ^ (n - 1) * Real.exp (-y ^ 2 / 4)) := by
    rw [e0, e2, show ((n : ℝ) + 2) / 2 = (n : ℝ) / 2 + 1 by ring,
      Real.Gamma_add_one (by positivity : (n : ℝ) / 2 ≠ 0),
      show -((n : ℝ) + 2) / 2 = -(n : ℝ) / 2 + -1 by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 1/4), Real.rpow_neg_one]
    norm_num
    ring
  have hi0 := integral_fun_norm_addHaar (volume : Measure (Space n))
    (fun y : ℝ => Real.exp (-y ^ 2 / 4))
  have hi2 := integral_fun_norm_addHaar (volume : Measure (Space n))
    (fun y : ℝ => y ^ 2 * Real.exp (-y ^ 2 / 4))
  simp only [hd, nsmul_eq_mul, smul_eq_mul] at hi0 hi2
  have hmain : (∫ x : Space n, ‖x‖ ^ 2 * Real.exp (-‖x‖ ^ 2 / 4)) =
      2 * n * (∫ x : Space n, Real.exp (-‖x‖ ^ 2 / 4)) := by
    rw [hi2, hratio, hi0]
    ring
  rw [hmain]
  congr 1
  convert GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Space n)
    (b := 1/4) (by norm_num) using 1
  · congr 1; funext x; congr 1; ring
  · rw [hd]; congr 1; field_simp

lemma gaussian_second_moment_integrable (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun x : Space n => ‖x‖ ^ 2 * Real.exp (-‖x‖ ^ 2 / 4)) := by
  by_contra h
  have he := integral_undef h
  rw [gaussian_second_moment n hn] at he
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have : 0 < 2 * (n : ℝ) * (4 * Real.pi) ^ ((n : ℝ) / 2) := by positivity
  linarith


/-- Maximum backward time after the spatial scaling y = sqrt(τ) x. -/
def heatBallScaledTime (n : ℕ) (r : ℝ) (x : Space n) : ℝ :=
  (r ^ 2 / (4 * Real.pi)) * Real.exp (-‖x‖ ^ 2 / (2 * n))

lemma heatBallScaledTime_pos {n : ℕ} {r : ℝ} (hr : 0 < r) (x : Space n) :
    0 < heatBallScaledTime n r x := by
  unfold heatBallScaledTime
  positivity

lemma heatBall_scaled_superlevel {n : ℕ} (hn : 1 ≤ n) {r τ : ℝ}
    (hr : 0 < r) (hτ : 0 < τ) (x : Space n) :
    r ^ (-(n : ℤ)) < gaussianKernel n τ (Real.sqrt τ • x) ↔
      τ < heatBallScaledTime n r x := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [gaussian_superlevel_iff hτ (by positivity), norm_smul,
    Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr hτ), mul_pow,
    Real.sq_sqrt hτ.le, Real.log_rpow (by positivity), Real.log_zpow]
  push_cast
  rw [show 4 * τ = τ * 4 by ring, mul_assoc, mul_lt_mul_iff_right₀ hτ]
  rw [← Real.log_lt_log_iff hτ (heatBallScaledTime_pos hr x)]
  unfold heatBallScaledTime
  rw [Real.log_mul (by positivity : r ^ 2 / (4 * Real.pi) ≠ 0)
      (Real.exp_ne_zero _), Real.log_exp,
    Real.log_div (by positivity) (by positivity), Real.log_pow,
    Real.log_mul (by positivity : 4 * Real.pi ≠ 0) hτ.ne']
  have he : 4 * (-(n : ℝ) / 2 * (Real.log (4 * Real.pi) + Real.log τ) -
      -(n : ℝ) * Real.log r) =
      (2 * Real.log r - Real.log (4 * Real.pi) - Real.log τ) * (2 * n) := by ring
  rw [he, ← div_lt_iff₀ (by positivity : 0 < 2 * (n : ℝ))]
  push_cast
  simp only [neg_div]
  constructor <;> intro h <;> linarith

lemma heatBallScaledTime_power {n : ℕ} (hn : 1 ≤ n) {r : ℝ}
    (hr : 0 < r) (x : Space n) :
    (heatBallScaledTime n r x) ^ ((n : ℝ) / 2) =
      (r ^ n * (4 * Real.pi) ^ (-(n : ℝ) / 2)) * Real.exp (-‖x‖ ^ 2 / 4) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold heatBallScaledTime
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.div_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le,
    show (↑(2 : ℕ) : ℝ) * ((n : ℝ) / 2) = n by push_cast; ring,
    Real.rpow_natCast, ← Real.exp_mul,
    show -(n : ℝ) / 2 = -((n : ℝ) / 2) by ring,
    Real.rpow_neg (by positivity : 0 ≤ 4 * Real.pi)]
  congr 1
  · simp only [div_eq_mul_inv]
    congr 1
    field_simp
    ring


/-- Density in the coordinates (x,τ) with y = sqrt(τ) x. -/
def heatBallScaledDensity (n : ℕ) (r : ℝ) (z : SpaceTime n) : ℝ :=
  (Ioo 0 (heatBallScaledTime n r z.1)).indicator
    (fun τ : ℝ => ‖z.1‖ ^ 2 * τ ^ ((n : ℝ) / 2 - 1)) z.2

def heatBallScaledConstant (n : ℕ) (r : ℝ) : ℝ :=
  (2 / (n : ℝ)) * r ^ n * (4 * Real.pi) ^ (-(n : ℝ) / 2)

lemma heatBallScaledDensity_nonneg {n : ℕ} {r : ℝ} (z : SpaceTime n) :
    0 ≤ heatBallScaledDensity n r z := by
  unfold heatBallScaledDensity
  by_cases hz : z.2 ∈ Ioo 0 (heatBallScaledTime n r z.1)
  · rw [indicator_of_mem hz]
    have hτ : 0 < z.2 := hz.1
    positivity
  · rw [indicator_of_notMem hz]

lemma heatBallScaledDensity_measurable (n : ℕ) (r : ℝ) :
    Measurable (heatBallScaledDensity n r) := by
  have hA : Measurable (fun z : SpaceTime n => heatBallScaledTime n r z.1) := by
    unfold heatBallScaledTime
    fun_prop
  have hs : MeasurableSet {z : SpaceTime n |
      0 < z.2 ∧ z.2 < heatBallScaledTime n r z.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd hA)
  unfold heatBallScaledDensity Set.indicator
  exact Measurable.ite hs (by fun_prop) measurable_const

lemma heatBallScaledDensity_time_integrable {n : ℕ} (hn : 1 ≤ n) {r : ℝ}
    (hr : 0 < r) (x : Space n) :
    Integrable (fun τ : ℝ => heatBallScaledDensity n r (x,τ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : -1 < (n : ℝ) / 2 - 1 := by linarith
  unfold heatBallScaledDensity
  dsimp only
  apply (integrable_indicator_iff measurableSet_Ioo).mpr
  exact ((intervalIntegral.integrableOn_Ioo_rpow_iff
    (heatBallScaledTime_pos hr x)).mpr hp).const_mul _

lemma heatBallScaledDensity_time_integral {n : ℕ} (hn : 1 ≤ n) {r : ℝ}
    (hr : 0 < r) (x : Space n) :
    (∫ τ : ℝ, heatBallScaledDensity n r (x,τ)) =
      heatBallScaledConstant n r * (‖x‖ ^ 2 * Real.exp (-‖x‖ ^ 2 / 4)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : -1 < (n : ℝ) / 2 - 1 := by linarith
  unfold heatBallScaledDensity
  dsimp only
  rw [integral_indicator measurableSet_Ioo, integral_const_mul,
    ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (heatBallScaledTime_pos hr x).le,
    integral_rpow (Or.inl hp),
    show (n : ℝ) / 2 - 1 + 1 = (n : ℝ) / 2 by ring,
    Real.zero_rpow (by positivity : (n : ℝ) / 2 ≠ 0), sub_zero,
    heatBallScaledTime_power hn hr]
  unfold heatBallScaledConstant
  ring

lemma heatBallScaledDensity_integrable {n : ℕ} (hn : 1 ≤ n) {r : ℝ}
    (hr : 0 < r) :
    Integrable (heatBallScaledDensity n r) (spaceTimeMeasure n) := by
  apply (integrable_prod_iff (heatBallScaledDensity_measurable n r).aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (heatBallScaledDensity_time_integrable hn hr), ?_⟩
  have hg := (gaussian_second_moment_integrable n hn).const_mul
    (heatBallScaledConstant n r)
  convert hg using 1
  funext x
  simp_rw [Real.norm_of_nonneg (heatBallScaledDensity_nonneg _)]
  exact heatBallScaledDensity_time_integral hn hr x

lemma heatBallScaledDensity_integral {n : ℕ} (hn : 1 ≤ n) {r : ℝ}
    (hr : 0 < r) :
    (∫ z, heatBallScaledDensity n r z ∂spaceTimeMeasure n) = 4 * r ^ n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [integral_prod _ (heatBallScaledDensity_integrable hn hr)]
  simp_rw [heatBallScaledDensity_time_integral hn hr]
  rw [integral_const_mul, gaussian_second_moment n hn]
  unfold heatBallScaledConstant
  rw [show -(n : ℝ) / 2 = -((n : ℝ) / 2) by ring,
    Real.rpow_neg (by positivity : 0 ≤ 4 * Real.pi)]
  field_simp
  norm_num


/-- Raw heat-ball density in backward coordinates about the origin. -/
def heatBallBackwardDensity (n : ℕ) (r : ℝ) (z : SpaceTime n) : ℝ :=
  {w : SpaceTime n | 0 < w.2 ∧ r ^ (-(n : ℤ)) < gaussianKernel n w.2 w.1}.indicator
    (fun w => ‖w.1‖ ^ 2 / w.2 ^ 2) z

lemma heatBallScaledDensity_slice_eq {n : ℕ} (hn : 1 ≤ n) {r τ : ℝ}
    (hr : 0 < r) (hτ : 0 < τ) (x : Space n) :
    heatBallScaledDensity n r (x, τ) =
      (Real.sqrt τ) ^ n * heatBallBackwardDensity n r (Real.sqrt τ • x, τ) := by
  have hs : (Real.sqrt τ) ^ n = τ ^ ((n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hτ.le]
    congr 1
    ring
  unfold heatBallScaledDensity heatBallBackwardDensity
  dsimp only
  have he : ((Real.sqrt τ • x, τ) ∈ {w : SpaceTime n |
      0 < w.2 ∧ r ^ (-(n : ℤ)) < gaussianKernel n w.2 w.1}) ↔
      τ ∈ Ioo 0 (heatBallScaledTime n r x) := by
    simp only [mem_ofPred_eq, mem_Ioo]
    exact and_congr_right (fun _ => heatBall_scaled_superlevel hn hr hτ x)
  by_cases hmem : τ ∈ Ioo 0 (heatBallScaledTime n r x)
  · rw [indicator_of_mem hmem, indicator_of_mem (he.mpr hmem),
      norm_smul, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr hτ),
      mul_pow, Real.sq_sqrt hτ.le, hs,
      Real.rpow_sub hτ, Real.rpow_one]
    field_simp
  · rw [indicator_of_notMem hmem, indicator_of_notMem (fun h => hmem (he.mp h)), mul_zero]

lemma heatBallBackwardDensity_slice_integral {n : ℕ} (hn : 1 ≤ n) {r : ℝ}
    (hr : 0 < r) (τ : ℝ) :
    (∫ x : Space n, heatBallBackwardDensity n r (x,τ)) =
      ∫ x : Space n, heatBallScaledDensity n r (x,τ) := by
  by_cases hτ : 0 < τ
  · simp_rw [heatBallScaledDensity_slice_eq hn hr hτ]
    rw [integral_const_mul,
      Measure.integral_comp_smul_of_nonneg (volume : Measure (Space n))
        (fun x : Space n => heatBallBackwardDensity n r (x,τ))
        (Real.sqrt τ) (hR := (Real.sqrt_nonneg _))]
    have hd : Module.finrank ℝ (Space n) = n := by simp [Space, P201Specs.Space]
    rw [hd, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  · have e1 : (fun x : Space n => heatBallBackwardDensity n r (x,τ)) = 0 := by
      funext x
      simp [heatBallBackwardDensity, Set.indicator, hτ]
    have e2 : (fun x : Space n => heatBallScaledDensity n r (x,τ)) = 0 := by
      funext x
      simp [heatBallScaledDensity, Set.indicator, hτ]
    rw [e1, e2]

lemma heatBallBackwardDensity_translate {n : ℕ} {r : ℝ} (hr : 0 < r)
    (z₀ z : SpaceTime n) :
    heatBallBackwardDensity n r z =
      (4 * r ^ n) * ((heatBall n r z₀).indicator (heatBallWeight n r z₀)) (z₀ - z) := by
  have he : (z₀ - z ∈ heatBall n r z₀) ↔
      z ∈ {w : SpaceTime n | 0 < w.2 ∧ r ^ (-(n : ℤ)) < gaussianKernel n w.2 w.1} := by
    rw [mem_heatBall]
    simp only [Prod.snd_sub, Prod.fst_sub, sub_sub_cancel, mem_ofPred_eq]
    exact and_congr_left (fun _ => by constructor <;> intro h <;> linarith)
  by_cases hz : z ∈ {w : SpaceTime n | 0 < w.2 ∧ r ^ (-(n : ℤ)) < gaussianKernel n w.2 w.1}
  · unfold heatBallBackwardDensity
    rw [indicator_of_mem hz, indicator_of_mem (he.mpr hz)]
    unfold heatBallWeight P201Specs.Heat.heatBallWeight
    simp only [Prod.snd_sub, Prod.fst_sub, sub_sub_cancel]
    field_simp
  · unfold heatBallBackwardDensity
    rw [indicator_of_notMem hz, indicator_of_notMem (fun h => hz (he.mp h)), mul_zero]

lemma heatBallBackwardDensity_integrable {n : ℕ} (hn : 1 ≤ n) {r : ℝ}
    (hr : 0 < r) : Integrable (heatBallBackwardDensity n r) (spaceTimeMeasure n) := by
  let z₀ : SpaceTime n := (0,0)
  have hi := (integrable_indicator_iff (heatBall_measurableSet n r z₀)).mpr
    (heatBallWeightIntegrable n hn r hr z₀)
  have hmp : MeasurePreserving (fun z : SpaceTime n => z₀ - z)
      (spaceTimeMeasure n) (spaceTimeMeasure n) :=
    ((spatialMeasure n).measurePreserving_sub_left z₀.1).prod
      (volume.measurePreserving_sub_left z₀.2)
  have ht := (hmp.integrable_comp_of_integrable hi).const_mul (4 * r ^ n)
  convert ht using 1
  funext z
  exact heatBallBackwardDensity_translate hr z₀ z

lemma heatBallBackwardDensity_integral {n : ℕ} (hn : 1 ≤ n) {r : ℝ}
    (hr : 0 < r) :
    (∫ z, heatBallBackwardDensity n r z ∂spaceTimeMeasure n) = 4 * r ^ n := by
  rw [integral_prod_symm _ (heatBallBackwardDensity_integrable hn hr)]
  simp_rw [heatBallBackwardDensity_slice_integral hn hr]
  rw [← integral_prod_symm _ (heatBallScaledDensity_integrable hn hr),
    heatBallScaledDensity_integral hn hr]

theorem heatBallWeightMass : P201Specs.Heat.heatBallWeightMassStatement := by
  intro n hn r hr z₀
  have hmp : MeasurePreserving (fun z : SpaceTime n => z₀ - z)
      (spaceTimeMeasure n) (spaceTimeMeasure n) :=
    ((spatialMeasure n).measurePreserving_sub_left z₀.1).prod
      (volume.measurePreserving_sub_left z₀.2)
  have hi : (∫ z, heatBallBackwardDensity n r z ∂spaceTimeMeasure n) =
      (4 * r ^ n) * (∫ z in heatBall n r z₀, heatBallWeight n r z₀ z ∂spaceTimeMeasure n) := by
    simp_rw [heatBallBackwardDensity_translate hr z₀]
    rw [integral_const_mul,
      hmp.integral_comp (MeasurableEquiv.subLeft z₀).measurableEmbedding,
      integral_indicator (heatBall_measurableSet n r z₀)]
  rw [heatBallBackwardDensity_integral hn hr] at hi
  have hc : 0 < 4 * r ^ n := by positivity
  nlinarith [hi]


/-- The truncated heat potential profile, with zero value and slope at the level 1. -/
def heatPotentialProfile (v : ℝ) : ℝ := if 1 < v then v - 1 - Real.log v else 0

def heatPotentialProfileSlope (v : ℝ) : ℝ := if 1 < v then 1 - v⁻¹ else 0

lemma heatPotentialProfile_of_le {v : ℝ} (hv : v ≤ 1) :
    heatPotentialProfile v = 0 := by simp [heatPotentialProfile, not_lt.mpr hv]

lemma heatPotentialProfile_of_gt {v : ℝ} (hv : 1 < v) :
    heatPotentialProfile v = v - 1 - Real.log v := by simp [heatPotentialProfile, hv]

lemma heatPotentialProfile_nonneg (v : ℝ) : 0 ≤ heatPotentialProfile v := by
  by_cases hv : 1 < v
  · rw [heatPotentialProfile_of_gt hv]
    linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < v)]
  · simp [heatPotentialProfile, hv]

lemma heatPotentialProfile_le_self {v : ℝ} (hv : 0 ≤ v) :
    heatPotentialProfile v ≤ v := by
  by_cases h : 1 < v
  · rw [heatPotentialProfile_of_gt h]
    linarith [Real.log_nonneg h.le]
  · simpa [heatPotentialProfile, h]

lemma hasDerivAt_heatPotentialProfile (v : ℝ) :
    HasDerivAt heatPotentialProfile (heatPotentialProfileSlope v) v := by
  rcases lt_trichotomy v 1 with hv | rfl | hv
  · have heq : heatPotentialProfile =ᶠ[𝓝 v] (fun _ => (0 : ℝ)) := by
      filter_upwards [eventually_lt_nhds hv] with x hx
      simp [heatPotentialProfile, not_lt.mpr hx.le]
    simpa [heatPotentialProfileSlope, not_lt.mpr hv.le] using
      (hasDerivAt_const v (0 : ℝ)).congr_of_eventuallyEq heq
  · have hl : HasDerivWithinAt heatPotentialProfile 0 (Iic 1) 1 := by
      apply (hasDerivAt_const 1 (0 : ℝ)).hasDerivWithinAt.congr
      · intro x hx
        exact heatPotentialProfile_of_le hx
      · simp [heatPotentialProfile]
    have hlog : HasDerivAt (fun v : ℝ => v - 1 - Real.log v) 0 1 := by
      convert ((hasDerivAt_id (1 : ℝ)).sub_const 1).sub
        (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)) using 1 <;> norm_num
      ext v
      rfl
    have hr : HasDerivWithinAt heatPotentialProfile 0 (Ici 1) 1 := by
      apply hlog.hasDerivWithinAt.congr
      · intro x hx
        rcases (show 1 ≤ x from hx).eq_or_lt with hx | hx
        · subst x
          simp [heatPotentialProfile]
        · exact heatPotentialProfile_of_gt hx
      · simp [heatPotentialProfile]
    simpa [Iic_union_Ici, heatPotentialProfileSlope] using hl.union hr
  · have heq : heatPotentialProfile =ᶠ[𝓝 v] (fun x => x - 1 - Real.log x) := by
      filter_upwards [eventually_gt_nhds hv] with x hx
      exact heatPotentialProfile_of_gt hx
    have hd := ((hasDerivAt_id v).sub_const 1).sub
      (Real.hasDerivAt_log (by linarith : v ≠ 0))
    simpa [heatPotentialProfileSlope, hv] using hd.congr_of_eventuallyEq heq

lemma continuous_heatPotentialProfile : Continuous heatPotentialProfile :=
  continuous_iff_continuousAt.mpr fun v => (hasDerivAt_heatPotentialProfile v).continuousAt

lemma continuous_heatPotentialProfileSlope : Continuous heatPotentialProfileSlope := by
  change Continuous ((Ioi (1 : ℝ)).piecewise (fun v => 1 - v⁻¹) (fun _ => 0))
  apply continuous_piecewise
  · intro x hx
    have hx' : x = 1 := by simpa only [frontier_Ioi, mem_singleton_iff] using hx
    subst x
    norm_num
  · rw [closure_Ioi]
    apply continuousOn_const.sub
    apply continuousOn_id.inv₀
    intro x hx
    change 1 ≤ x at hx
    change x ≠ 0
    linarith
  · exact continuousOn_const

lemma contDiff_heatPotentialProfile : ContDiff ℝ 1 heatPotentialProfile := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun v => (hasDerivAt_heatPotentialProfile v).differentiableAt, ?_⟩
  have hd : deriv heatPotentialProfile = heatPotentialProfileSlope :=
    funext fun v => (hasDerivAt_heatPotentialProfile v).deriv
  rw [hd]
  exact continuous_heatPotentialProfileSlope

lemma hasDerivAt_heatPotentialProfileSlope {v : ℝ} (hv : v ≠ 1) :
    HasDerivAt heatPotentialProfileSlope (if 1 < v then 1 / v ^ 2 else 0) v := by
  rcases lt_or_gt_of_ne hv with hv | hv
  · have heq : heatPotentialProfileSlope =ᶠ[𝓝 v] (fun _ => (0 : ℝ)) := by
      filter_upwards [eventually_lt_nhds hv] with x hx
      simp [heatPotentialProfileSlope, not_lt.mpr hx.le]
    simpa [not_lt.mpr hv.le] using
      (hasDerivAt_const v (0 : ℝ)).congr_of_eventuallyEq heq
  · have heq : heatPotentialProfileSlope =ᶠ[𝓝 v] (fun x => 1 - x⁻¹) := by
      filter_upwards [eventually_gt_nhds hv] with x hx
      simp [heatPotentialProfileSlope, hx]
    have hd := (hasDerivAt_const v (1 : ℝ)).sub ((hasDerivAt_id v).inv (by linarith : v ≠ 0))
    convert hd.congr_of_eventuallyEq heq using 1
    simp [hv]
    ring



lemma tendsto_scaled_heatPotentialProfile {v : ℝ} (hv : 0 ≤ v) :
    Tendsto (fun a : ℝ => a * heatPotentialProfile (v / a)) (𝓝[>] 0) (𝓝 v) := by
  rcases hv.eq_or_lt with rfl | hv
  · convert (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 0)) using 1 <;>
      norm_num [heatPotentialProfile]
  have ha : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hlog : Tendsto (fun a : ℝ => a * Real.log a) (𝓝[>] 0) (𝓝 0) := by
    simpa [Real.rpow_one, mul_comm] using
      (tendsto_log_mul_rpow_nhdsGT_zero (r := 1) (by norm_num))
  have hform : (fun a : ℝ => a * heatPotentialProfile (v / a)) =ᶠ[𝓝[>] 0]
      (fun a => v - a - a * Real.log v + a * Real.log a) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hv : ∀ᶠ a : ℝ in 𝓝 (0 : ℝ), a < v).filter_mono
        nhdsWithin_le_nhds] with a ha hav
    have ha' : 0 < a := ha
    have hh : 1 < v / a := (lt_div_iff₀ ha').mpr (by linarith)
    rw [heatPotentialProfile_of_gt hh, Real.log_div hv.ne' ha'.ne']
    field_simp
    ring
  apply Tendsto.congr' hform.symm
  convert (((tendsto_const_nhds.sub ha).sub (ha.mul_const (Real.log v))).add hlog) using 1 <;>
    simp

lemma tendsto_integral_scaled_heatPotentialProfile {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {g : α → ℝ} (hg : Integrable g μ) (hg₀ : ∀ᵐ x ∂μ, 0 ≤ g x) :
    Tendsto (fun a : ℝ => ∫ x, a * heatPotentialProfile (g x / a) ∂μ)
      (𝓝[>] 0) (𝓝 (∫ x, g x ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (bound := g)
  · exact Eventually.of_forall fun a =>
      (continuous_heatPotentialProfile.comp_aestronglyMeasurable
        ((continuous_id.div_const a).comp_aestronglyMeasurable hg.aestronglyMeasurable)).const_mul a
  · filter_upwards [self_mem_nhdsWithin] with a ha
    filter_upwards [hg₀] with x hx
    have ha' : 0 < a := ha
    rw [Real.norm_of_nonneg (mul_nonneg ha'.le (heatPotentialProfile_nonneg _))]
    calc
      a * heatPotentialProfile (g x / a) ≤ a * (g x / a) :=
        mul_le_mul_of_nonneg_left (heatPotentialProfile_le_self (div_nonneg hx ha'.le)) ha'.le
      _ = g x := by field_simp
  · exact hg
  · filter_upwards [hg₀] with x hx
    exact tendsto_scaled_heatPotentialProfile hx



lemma gaussian_parabolic_scaling (n : ℕ) {τ : ℝ} (hτ : 0 < τ) (x : Space n) :
    gaussianKernel n τ (Real.sqrt τ • x) =
      τ ^ (-(n : ℝ) / 2) * gaussianKernel n 1 x := by
  unfold gaussianKernel P201Specs.Heat.gaussianKernel
  rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt hτ.le, Real.mul_rpow (by positivity : 0 ≤ 4 * Real.pi) hτ.le]
  rw [show -(τ * ‖x‖ ^ 2) / (4 * τ) = -‖x‖ ^ 2 / (4 * (1 : ℝ)) by field_simp]
  simp only [mul_one]
  ring

lemma sqrt_pow_eq_rpow (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    Real.sqrt τ ^ n = τ ^ ((n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hτ.le]
  congr 1
  ring

lemma integral_parabolic_scaling (n : ℕ) {τ : ℝ} (hτ : 0 < τ)
    (f : Space n → ℝ) :
    (∫ y, f y ∂spatialMeasure n) =
      τ ^ ((n : ℝ) / 2) * ∫ x, f (Real.sqrt τ • x) ∂spatialMeasure n := by
  have hs := (spatialMeasure n).integral_comp_smul_of_nonneg f (Real.sqrt τ)
    (hR := Real.sqrt_nonneg _)
  simp only [Space, P201Specs.Space, finrank_euclideanSpace, Fintype.card_fin,
    smul_eq_mul, sqrt_pow_eq_rpow n hτ] at hs
  have hp : τ ^ ((n : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hτ _).ne'
  rw [hs]
  field_simp

lemma integral_heatPotentialProfile_gaussian (n : ℕ) {τ : ℝ} (hτ : 0 < τ)
    (b : ℝ) :
    (∫ y, heatPotentialProfile (b * gaussianKernel n τ y) ∂spatialMeasure n) =
      ∫ x, τ ^ ((n : ℝ) / 2) *
        heatPotentialProfile (b * gaussianKernel n 1 x / τ ^ ((n : ℝ) / 2))
          ∂spatialMeasure n := by
  rw [integral_parabolic_scaling n hτ, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [gaussian_parabolic_scaling n hτ]
  congr 2
  rw [show -(n : ℝ) / 2 = -((n : ℝ) / 2) by ring, Real.rpow_neg hτ.le]
  ring



lemma tendsto_positive_half_dimension_power {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun τ : ℝ => τ ^ ((n : ℝ) / 2)) (𝓝[>] 0) (𝓝[>] 0) := by
  have hp : 0 < (n : ℝ) / 2 := by exact_mod_cast (show (0 : ℝ) < n / 2 by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    linarith)
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, ?_⟩
  · convert ((Real.continuous_rpow_const hp.le).tendsto 0).mono_left
      nhdsWithin_le_nhds using 1
    rw [Real.zero_rpow hp.ne']
  · filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact Real.rpow_pos_of_pos hτ _

lemma tendsto_integral_heatPotentialProfile_gaussian {n : ℕ} (hn : 1 ≤ n)
    {b : ℝ} (hb : 0 ≤ b) :
    Tendsto (fun τ : ℝ =>
      ∫ y, heatPotentialProfile (b * gaussianKernel n τ y) ∂spatialMeasure n)
      (𝓝[>] 0) (𝓝 b) := by
  have hi := tendsto_integral_scaled_heatPotentialProfile (spatialMeasure n)
    ((gaussian_integrable_aux n (t := 1) (by norm_num)).const_mul b)
    (ae_of_all _ (fun x => mul_nonneg hb (gaussianNonnegative n hn 1 (by norm_num) x)))
  have hc := hi.comp (tendsto_positive_half_dimension_power hn)
  have hmass : (∫ x, b * gaussianKernel n 1 x ∂spatialMeasure n) = b := by
    rw [integral_const_mul, gaussian_mass_aux n (by norm_num), mul_one]
  rw [hmass] at hc
  apply hc.congr'
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  exact (integral_heatPotentialProfile_gaussian n hτ b).symm

lemma integral_heatPotentialProfile_translate {n : ℕ} {τ : ℝ} (hτ : 0 < τ)
    (b : ℝ) (z₀ : SpaceTime n) (u : SpaceTime n → ℝ) :
    (∫ y, u (y, z₀.2 - τ) * heatPotentialProfile
      (b * gaussianKernel n τ (z₀.1 - y)) ∂spatialMeasure n) =
      ∫ x, u (z₀.1 - Real.sqrt τ • x, z₀.2 - τ) *
        (τ ^ ((n : ℝ) / 2) *
          heatPotentialProfile (b * gaussianKernel n 1 x / τ ^ ((n : ℝ) / 2)))
          ∂spatialMeasure n := by
  rw [← integral_sub_left_eq_self (fun y : Space n =>
      u (y, z₀.2 - τ) * heatPotentialProfile
        (b * gaussianKernel n τ (z₀.1 - y))) (spatialMeasure n) z₀.1]
  simp only [sub_sub_cancel]
  rw [integral_parabolic_scaling n hτ, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [gaussian_parabolic_scaling n hτ]
  rw [show -(n : ℝ) / 2 = -((n : ℝ) / 2) by ring, Real.rpow_neg hτ.le]
  rw [show b * ((τ ^ ((n : ℝ) / 2))⁻¹ * gaussianKernel n 1 x) =
      b * gaussianKernel n 1 x / τ ^ ((n : ℝ) / 2) by ring]
  ring

lemma tendsto_integral_heatPotentialProfile_top {n : ℕ} (hn : 1 ≤ n)
    {b : ℝ} (hb : 0 ≤ b) (z₀ : SpaceTime n) (u : SpaceTime n → ℝ)
    (hu : Continuous u) (hbound : ∃ M : ℝ, ∀ z, ‖u z‖ ≤ M) :
    Tendsto (fun τ : ℝ => ∫ y, u (y, z₀.2 - τ) * heatPotentialProfile
      (b * gaussianKernel n τ (z₀.1 - y)) ∂spatialMeasure n)
      (𝓝[>] 0) (𝓝 (b * u z₀)) := by
  obtain ⟨M, hM⟩ := hbound
  have hM₀ : 0 ≤ M := (norm_nonneg (u z₀)).trans (hM z₀)
  have hgauss (x : Space n) : 0 ≤ gaussianKernel n 1 x :=
    gaussianNonnegative n hn 1 (by norm_num) x
  have hc := tendsto_integral_filter_of_dominated_convergence
    (μ := spatialMeasure n) (l := 𝓝[>] (0 : ℝ))
    (F := fun τ x => u (z₀.1 - Real.sqrt τ • x, z₀.2 - τ) *
      (τ ^ ((n : ℝ) / 2) * heatPotentialProfile
        (b * gaussianKernel n 1 x / τ ^ ((n : ℝ) / 2))))
    (f := fun x => u z₀ * (b * gaussianKernel n 1 x))
    (fun x => M * (b * gaussianKernel n 1 x)) ?_ ?_ ?_ ?_
  · have hmass : (∫ x, u z₀ * (b * gaussianKernel n 1 x) ∂spatialMeasure n) = u z₀ * b := by
      rw [integral_const_mul, integral_const_mul, gaussian_mass_aux n (by norm_num), mul_one]
    rw [hmass] at hc
    rw [mul_comm b]
    apply hc.congr'
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact (integral_heatPotentialProfile_translate hτ b z₀ u).symm
  · filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hg : Continuous (gaussianKernel n 1) := by
      unfold gaussianKernel P201Specs.Heat.gaussianKernel
      fun_prop
    exact ((hu.comp (by fun_prop)).mul
      ((continuous_const.mul (continuous_heatPotentialProfile.comp
        ((continuous_const.mul hg).div_const _))))).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with τ hτ
    filter_upwards [] with x
    have hτ' : 0 < τ ^ ((n : ℝ) / 2) := Real.rpow_pos_of_pos hτ _
    have hgx := hgauss x
    rw [norm_mul, Real.norm_of_nonneg
      (mul_nonneg hτ'.le (heatPotentialProfile_nonneg _))]
    apply mul_le_mul (hM _) ?_
      (mul_nonneg hτ'.le (heatPotentialProfile_nonneg _)) hM₀
    calc
      τ ^ ((n : ℝ) / 2) * heatPotentialProfile
          (b * gaussianKernel n 1 x / τ ^ ((n : ℝ) / 2)) ≤
          τ ^ ((n : ℝ) / 2) *
            (b * gaussianKernel n 1 x / τ ^ ((n : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left
          (heatPotentialProfile_le_self (by positivity)) hτ'.le
      _ = b * gaussianKernel n 1 x := by field_simp
  · exact ((gaussian_integrable_aux n (t := 1) (by norm_num)).const_mul b).const_mul M
  · filter_upwards [] with x
    have hz : Tendsto (fun τ : ℝ => (z₀.1 - Real.sqrt τ • x, z₀.2 - τ))
        (𝓝[>] 0) (𝓝 z₀) := by
      have hpath : Continuous (fun τ : ℝ => (z₀.1 - Real.sqrt τ • x, z₀.2 - τ)) := by
        fun_prop
      simpa using (hpath.tendsto 0).mono_left nhdsWithin_le_nhds
    exact (hu.continuousAt.tendsto.comp hz).mul
      ((tendsto_scaled_heatPotentialProfile (mul_nonneg hb (hgauss x))).comp
        (tendsto_positive_half_dimension_power hn))



lemma laplacian_eq_sum_fderiv {n : ℕ} {u : P201Specs.Space n → ℝ}
    {x : P201Specs.Space n} (hu : ContDiffAt ℝ 2 u x) :
    P201Specs.laplacian u x = ∑ i : Fin n,
      fderiv ℝ (fderiv ℝ u) x (P201Specs.coordinate n i) (P201Specs.coordinate n i) := by
  classical
  apply Finset.sum_congr rfl
  intro i hi
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  change P102.U4.partialWord u (({i,i} : Multiset (Fin n)).sort (· ≤ ·)) x = _
  have hsort : ({i,i} : Multiset (Fin n)).sort (· ≤ ·) = [i,i] := by
    rw [Multiset.insert_eq_cons, Multiset.sort_cons i {i} (· ≤ ·) (by simp), Multiset.sort_singleton]
  rw [hsort]
  simp only [P102.U4.partialWord]
  rw [fderiv_clm_apply hd (differentiableAt_const (P201Specs.coordinate n i))]
  simp

lemma caloric_hasStrictFDerivAt {n : ℕ} {u : P201Specs.Heat.SpaceTime n → ℝ}
    {S : Set (P201Specs.Heat.SpaceTime n)} (hS : IsOpen S)
    (hu : P201Specs.Heat.IsClassicalCaloricOn u S) {z : P201Specs.Heat.SpaceTime n}
    (hz : z ∈ S) :
    HasStrictFDerivAt u
      ((fderiv ℝ (fun x => u (x,z.2)) z.1).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ (deriv (fun t => u (z.1,t)) z.2))) z := by
  apply hasStrictFDerivAt_uncurry_coprod
    (f := fun x t => u (x,t))
    (f₁ := fun x t => fderiv ℝ (fun y => u (y,t)) x)
    (f₂ := fun x t => ContinuousLinearMap.toSpanSingleton ℝ (deriv (fun s => u (x,s)) t))
  · filter_upwards [hS.mem_nhds hz] with v hv
    exact ((hu.2.2.2.2 v hv).2.1.differentiableAt (by norm_num)).hasFDerivAt
  · filter_upwards [hS.mem_nhds hz] with v hv
    exact (hu.2.2.2.2 v hv).1.hasDerivAt.hasFDerivAt
  · exact hu.2.2.1.continuousAt (hS.mem_nhds hz)
  · exact (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuousAt.comp
      (hu.2.1.continuousAt (hS.mem_nhds hz))

lemma caloric_contDiffOn_one {n : ℕ} {u : P201Specs.Heat.SpaceTime n → ℝ}
    {S : Set (P201Specs.Heat.SpaceTime n)} (hS : IsOpen S)
    (hu : P201Specs.Heat.IsClassicalCaloricOn u S) : ContDiffOn ℝ 1 u S := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen hS]
  refine ⟨fun z hz => (caloric_hasStrictFDerivAt hS hu hz).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  apply contDiffOn_zero.mpr
  have h : ContinuousOn (fun z =>
      (fderiv ℝ (fun x => u (x,z.2)) z.1).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ (deriv (fun t => u (z.1,t)) z.2))) S :=
    hu.2.2.1.continuousLinearMapCoprod ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp_continuousOn
      hu.2.1)
  exact h.congr (fun z hz => (caloric_hasStrictFDerivAt hS hu hz).hasFDerivAt.fderiv)

lemma laplacian_eq_sum_partialWord {n : ℕ} (u : P201Specs.Space n → ℝ)
    (x : P201Specs.Space n) : P201Specs.laplacian u x =
    ∑ i : Fin n, P102.U4.partialWord u [i,i] x := by
  classical
  apply Finset.sum_congr rfl
  intro i hi
  change P102.U4.partialWord u (({i,i} : Multiset (Fin n)).sort (· ≤ ·)) x = _
  rw [Multiset.insert_eq_cons, Multiset.sort_cons i {i} (· ≤ ·) (by simp), Multiset.sort_singleton]

lemma integral_test_mul_laplacian {n : ℕ} (Ω : TopologicalSpace.Opens (P201Specs.Space n))
    {u : P201Specs.Space n → ℝ} (hu : ContDiffOn ℝ 2 u Ω)
    (φ : P201Specs.Test ℝ Ω) :
    (∫ x, φ x * P201Specs.laplacian u x) =
      ∫ x, u x * P201Specs.laplacian φ x := by
  classical
  have hi (i : Fin n) : Integrable (fun x => φ x * P102.U4.partialWord u [i,i] x) := by
    have hd : LocallyIntegrableOn (P102.U4.partialWord u [i,i]) Ω volume :=
      (P102.U4.partialWord_contDiffOn Ω hu [i,i] 0 (by simp)).continuousOn.locallyIntegrableOn
        Ω.isOpen.measurableSet
    exact φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hd
  have hj (i : Fin n) : Integrable (fun x => u x * P102.U4.partialWord φ [i,i] x) := by
    have hc : P102.U4.partialWord φ [i,i] =
        (P102.U4.testPartialWord Ω [i,i] φ) := (P102.U4.testPartialWord_coe Ω [i,i] φ).symm
    rw [hc]
    exact ((P102.U4.testPartialWord Ω [i,i] φ).integrable_bilin
      (ContinuousLinearMap.mul ℝ ℝ)
      (hu.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)).congr
        (Filter.Eventually.of_forall (fun x => mul_comm _ _))
  simp_rw [laplacian_eq_sum_partialWord, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hi i), integral_finsetSum _ (fun i _ => hj i)]
  apply Finset.sum_congr rfl
  intro i hi
  have h := P102.U4.integral_test_mul_partialWord Ω [i,i] hu φ
  simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, neg_one_sq, one_mul,
    P102.U4.testPartialWord_coe, mul_comm] using h

lemma integrable_compact_mul_of_continuousOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {S : Set E} {u q : E → ℝ} (hu : ContinuousOn u S) (hq : Continuous q)
    (hqc : HasCompactSupport q) (hqs : tsupport q ⊆ S) :
    Integrable (fun x => q x * u x) μ := by
  apply (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_left q u).trans (subset_tsupport q))).mp
  exact (hq.continuousOn.mul (hu.mono hqs)).integrableOn_compact hqc

lemma integral_compact_mul_hasLineDerivAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {S : Set E} {u u' q : E → ℝ} {v : E}
    (hu : ContinuousOn u S) (hu' : ContinuousOn u' S)
    (hdu : ∀ x ∈ S, HasLineDerivAt ℝ u (u' x) x v)
    (hq : ContDiff ℝ 1 q) (hqc : HasCompactSupport q) (hqs : tsupport q ⊆ S) :
    (∫ x, q x * u' x ∂μ) = -∫ x, fderiv ℝ q x v * u x ∂μ := by
  apply integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℝ)
  · exact integrable_compact_mul_of_continuousOn hu
      ((hq.fderiv_right (m := 0) (by norm_num)).continuous.clm_apply continuous_const)
      (hqc.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hqs)
  · exact integrable_compact_mul_of_continuousOn hu' hq.continuous hqc hqs
  · exact integrable_compact_mul_of_continuousOn hu hq.continuous hqc hqs
  · intro x hx
    exact (hq.differentiable (by norm_num) x).hasFDerivAt.hasLineDerivAt v
  · intro x hx
    exact hdu x (hqs hx)

lemma integral_compact_mul_secondLineDerivAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {S : Set E} {u u' u'' q : E → ℝ} {v : E}
    (hu : ContinuousOn u S) (hu' : ContinuousOn u' S) (hu'' : ContinuousOn u'' S)
    (hdu : ∀ x ∈ S, HasLineDerivAt ℝ u (u' x) x v)
    (hdu' : ∀ x ∈ S, HasLineDerivAt ℝ u' (u'' x) x v)
    (hq : ContDiff ℝ 2 q) (hqc : HasCompactSupport q) (hqs : tsupport q ⊆ S) :
    (∫ x, q x * u'' x ∂μ) = ∫ x, u x * fderiv ℝ (fun y => fderiv ℝ q y v) x v ∂μ := by
  have hdq : ContDiff ℝ 1 (fun x => fderiv ℝ q x v) :=
    (hq.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have h₁ := integral_compact_mul_hasLineDerivAt (μ := μ) hu' hu'' hdu'
    (hq.of_le (by norm_num) : ContDiff ℝ 1 q) hqc hqs
  have h₂ := integral_compact_mul_hasLineDerivAt (μ := μ) hu hu' hdu
    hdq (hqc.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hqs)
  rw [h₁, h₂, neg_neg]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x => mul_comm _ _))

lemma hasLineDerivAt_space {n : ℕ} {u : P201Specs.Heat.SpaceTime n → ℝ}
    {z : P201Specs.Heat.SpaceTime n} {v : P201Specs.Space n}
    (hu : DifferentiableAt ℝ (fun x => u (x,z.2)) z.1) :
    HasLineDerivAt ℝ u (fderiv ℝ (fun x => u (x,z.2)) z.1 v) z (v,0) := by
  have h := hu.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
    (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z.1) (by simp)
  simpa [HasLineDerivAt, Function.comp_def, Prod.add_def] using h

lemma hasLineDerivAt_time {n : ℕ} {u : P201Specs.Heat.SpaceTime n → ℝ}
    {z : P201Specs.Heat.SpaceTime n}
    (hu : DifferentiableAt ℝ (fun t => u (z.1,t)) z.2) :
    HasLineDerivAt ℝ u (deriv (fun t => u (z.1,t)) z.2) z (0,1) := by
  have h := hu.hasDerivAt.comp_of_eq (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add z.2) (by simp)
  simpa [HasLineDerivAt, Function.comp_def, Prod.add_def] using h

lemma hasLineDerivAt_space_fderiv {n : ℕ} {u : P201Specs.Heat.SpaceTime n → ℝ}
    {z : P201Specs.Heat.SpaceTime n} {v : P201Specs.Space n}
    (hu : ContDiffAt ℝ 2 (fun x => u (x,z.2)) z.1) :
    HasLineDerivAt ℝ (fun w => fderiv ℝ (fun x => u (x,w.2)) w.1 v)
      (fderiv ℝ (fderiv ℝ (fun x => u (x,z.2))) z.1 v v) z (v,0) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ (fun x => u (x,z.2))) z.1 :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h := hasLineDerivAt_space (v := v)
    (u := fun w => fderiv ℝ (fun x => u (x,w.2)) w.1 v)
    (hd.clm_apply (differentiableAt_const v))
  simpa [fderiv_clm_apply hd (differentiableAt_const v), fderiv_const,
    ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply] using h

lemma integral_caloric_compact_test {n : ℕ} {u q : P201Specs.Heat.SpaceTime n → ℝ}
    {S : Set (P201Specs.Heat.SpaceTime n)}
    (hu : P201Specs.Heat.IsClassicalCaloricOn u S)
    (hq : ContDiff ℝ 2 q) (hqc : HasCompactSupport q) (hqs : tsupport q ⊆ S) :
    (∫ z, u z * fderiv ℝ q z (0,1) ∂P201Specs.Heat.spaceTimeMeasure n) +
      ∑ i : Fin n, ∫ z, u z *
        fderiv ℝ (fun w => fderiv ℝ q w (P201Specs.coordinate n i,0)) z
          (P201Specs.coordinate n i,0) ∂P201Specs.Heat.spaceTimeMeasure n = 0 := by
  classical
  let ut := fun z : P201Specs.Heat.SpaceTime n => deriv (fun t => u (z.1,t)) z.2
  let ui := fun i (z : P201Specs.Heat.SpaceTime n) =>
    fderiv ℝ (fun x => u (x,z.2)) z.1 (P201Specs.coordinate n i)
  let uii := fun i (z : P201Specs.Heat.SpaceTime n) =>
    fderiv ℝ (fderiv ℝ (fun x => u (x,z.2))) z.1
      (P201Specs.coordinate n i) (P201Specs.coordinate n i)
  have hui (i : Fin n) : ContinuousOn (ui i) S :=
    hu.2.2.1.clm_apply continuousOn_const
  have huii (i : Fin n) : ContinuousOn (uii i) S :=
    (hu.2.2.2.1.clm_apply continuousOn_const).clm_apply continuousOn_const
  have ht := integral_compact_mul_hasLineDerivAt (μ := P201Specs.Heat.spaceTimeMeasure n)
    hu.1 hu.2.1 (fun z hz => hasLineDerivAt_time (hu.2.2.2.2 z hz).1)
    (hq.of_le (by norm_num) : ContDiff ℝ 1 q) hqc hqs
  have hs (i : Fin n) := integral_compact_mul_secondLineDerivAt
    (μ := P201Specs.Heat.spaceTimeMeasure n) hu.1 (hui i) (huii i)
    (fun z hz => hasLineDerivAt_space ((hu.2.2.2.2 z hz).2.1.differentiableAt (by norm_num)))
    (fun z hz => hasLineDerivAt_space_fderiv (hu.2.2.2.2 z hz).2.1) hq hqc hqs
  have hPDE : (fun z => q z * ut z) = fun z => ∑ i : Fin n, q z * uii i z := by
    funext z
    by_cases hz : z ∈ S
    · have he := (hu.2.2.2.2 z hz).2.2
      rw [laplacian_eq_sum_fderiv (hu.2.2.2.2 z hz).2.1] at he
      simp only [ut, he, Finset.mul_sum, uii]
    · have hqz : q z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hqs h))
      simp [hqz]
  have hi (i : Fin n) : Integrable (fun z => q z * uii i z)
      (P201Specs.Heat.spaceTimeMeasure n) :=
    integrable_compact_mul_of_continuousOn (huii i) hq.continuous hqc hqs
  have he : (∫ z, q z * ut z ∂P201Specs.Heat.spaceTimeMeasure n) =
      ∑ i : Fin n, ∫ z, q z * uii i z ∂P201Specs.Heat.spaceTimeMeasure n := by
    rw [hPDE, integral_finsetSum _ (fun i _ => hi i)]
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i _ => hs i)
  rw [← hsum, ← he]
  have ht' : (∫ z, q z * ut z ∂P201Specs.Heat.spaceTimeMeasure n) =
      -(∫ z, u z * fderiv ℝ q z (0,1) ∂P201Specs.Heat.spaceTimeMeasure n) := by
    simpa only [ut, mul_comm] using ht
  rw [ht']
  ring



lemma exists_bounded_continuous_extension_of_isCompact {X : Type*} [TopologicalSpace X]
    [NormalSpace X] [T2Space X] {K : Set X} (hK : IsCompact K) {u : X → ℝ}
    (hu : ContinuousOn u K) :
    ∃ v : X → ℝ, Continuous v ∧ (∃ M : ℝ, ∀ x, ‖v x‖ ≤ M) ∧ EqOn v u K := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hu
  let B := max M 0
  have hB : 0 ≤ B := le_max_right _ _
  let f : C(K, ℝ) := ⟨fun x => u x, continuousOn_iff_continuous_domRestrict.mp hu⟩
  have hfrange : ∀ x, f x ∈ Icc (-B) B := by
    intro x
    exact abs_le.mp ((hM x x.prop).trans (le_max_left _ _))
  obtain ⟨g, hg, hgf⟩ := f.exists_restrict_eq_forall_mem_of_closed hfrange
    (nonempty_Icc.mpr (by linarith : -B ≤ B)) hK.isClosed
  refine ⟨g, g.continuous, ⟨B, fun x => ?_⟩, ?_⟩
  · exact abs_le.mpr (hg x)
  · intro x hx
    exact congrArg (fun w : C(K, ℝ) => w ⟨x,hx⟩) hgf

lemma exists_bounded_continuous_heatBall_extension {n : ℕ} (hn : 1 ≤ n)
    {r : ℝ} (hr : 0 < r) (z₀ : P201Specs.Heat.SpaceTime n)
    {u : P201Specs.Heat.SpaceTime n → ℝ}
    (hu : ContinuousOn u (closure (heatBall n r z₀))) :
    ∃ v : P201Specs.Heat.SpaceTime n → ℝ, Continuous v ∧
      (∃ M : ℝ, ∀ z, ‖v z‖ ≤ M) ∧ EqOn v u (closure (heatBall n r z₀)) :=
  exists_bounded_continuous_extension_of_isCompact (heatBall_isCompact_closure hn hr z₀) hu

lemma heatPotentialProfile_mul_eqOn_heatBall {n : ℕ} {r : ℝ} {z₀ z : P201Specs.Heat.SpaceTime n}
    (hr : 0 < r) (hz : z.2 < z₀.2)
    {u v : P201Specs.Heat.SpaceTime n → ℝ} (hvu : EqOn v u (closure (heatBall n r z₀))) :
    v z * heatPotentialProfile (r ^ n * gaussianKernel n (z₀.2-z.2) (z₀.1-z.1)) =
      u z * heatPotentialProfile (r ^ n * gaussianKernel n (z₀.2-z.2) (z₀.1-z.1)) := by
  by_cases h : 1 < r ^ n * gaussianKernel n (z₀.2-z.2) (z₀.1-z.1)
  · have hG : r ^ (-(n : ℤ)) < gaussianKernel n (z₀.2-z.2) (z₀.1-z.1) := by
      simp only [zpow_neg, zpow_natCast]
      exact (inv_lt_iff_one_lt_mul₀ (pow_pos hr n)).mpr (by simpa [mul_comm] using h)
    have hmem : z ∈ heatBall n r z₀ := ⟨hz, hG⟩
    rw [hvu (subset_closure hmem)]
  · simp [heatPotentialProfile, h]

lemma tendsto_integral_heatPotentialProfile_top_of_continuousOn {n : ℕ} (hn : 1 ≤ n)
    {r : ℝ} (hr : 0 < r) (z₀ : P201Specs.Heat.SpaceTime n)
    (u : P201Specs.Heat.SpaceTime n → ℝ)
    (hu : ContinuousOn u (closure (heatBall n r z₀))) :
    Filter.Tendsto (fun τ : ℝ => ∫ y, u (y,z₀.2-τ) * heatPotentialProfile
      (r ^ n * gaussianKernel n τ (z₀.1-y)) ∂spatialMeasure n)
      (𝓝[>] 0) (𝓝 (r ^ n * u z₀)) := by
  obtain ⟨v, hv, hb, hvu⟩ := exists_bounded_continuous_heatBall_extension hn hr z₀ hu
  have ht := tendsto_integral_heatPotentialProfile_top hn (pow_nonneg hr.le n) z₀ v hv hb
  rw [hvu (heatBallTopInClosure n hn r hr z₀)] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  change 0 < τ at hτ
  apply integral_congr_ae
  filter_upwards [] with y
  have hp := heatPotentialProfile_mul_eqOn_heatBall hr
    (z := (y,z₀.2-τ)) (by dsimp; linarith) hvu
  simpa using hp



lemma heatPotentialProfile_support_subset {X : Type*} (g : X → ℝ) :
    Function.support (fun x => heatPotentialProfile (g x)) ⊆ {x | 1 < g x} := by
  intro x hx
  by_contra hg
  exact hx (heatPotentialProfile_of_le (le_of_not_gt hg))

lemma heatPotentialProfileSlope_support_subset {X : Type*} (g : X → ℝ) :
    Function.support (fun x => heatPotentialProfileSlope (g x)) ⊆ {x | 1 < g x} := by
  intro x hx
  by_contra hg
  change ¬1 < g x at hg
  exact hx (by simp [heatPotentialProfileSlope, hg])

lemma heatBall_threshold_iff {n : ℕ} {r : ℝ} (hr : 0 < r) (v : ℝ) :
    r ^ (-(n : ℤ)) < v ↔ 1 < r ^ n * v := by
  rw [zpow_neg, zpow_natCast, ← one_div,
    div_lt_iff₀ (pow_pos hr _), mul_comm v]

lemma heatPotential_slice_support {n : ℕ} {r τ : ℝ} (hr : 0 < r) (hτ : 0 < τ)
    (z₀ : SpaceTime n) :
    Function.support (fun x : Space n =>
      heatPotentialProfile (r ^ n * gaussianKernel n τ (z₀.1 - x))) ⊆
      {x | (x, z₀.2 - τ) ∈ heatBall n r z₀} := by
  intro x hx
  have hlevel := heatPotentialProfile_support_subset
    (fun x : Space n => r ^ n * gaussianKernel n τ (z₀.1 - x)) hx
  refine ⟨by dsimp; linarith, ?_⟩
  change r ^ (-(n : ℤ)) < gaussianKernel n (z₀.2 - (z₀.2 - τ)) (z₀.1 - x)
  rw [sub_sub_cancel, heatBall_threshold_iff hr]
  exact hlevel

lemma heatPotentialSlope_slice_support {n : ℕ} {r τ : ℝ} (hr : 0 < r) (hτ : 0 < τ)
    (z₀ : SpaceTime n) :
    Function.support (fun x : Space n =>
      heatPotentialProfileSlope (r ^ n * gaussianKernel n τ (z₀.1 - x))) ⊆
      {x | (x, z₀.2 - τ) ∈ heatBall n r z₀} := by
  intro x hx
  have hlevel := heatPotentialProfileSlope_support_subset
    (fun x : Space n => r ^ n * gaussianKernel n τ (z₀.1 - x)) hx
  refine ⟨by dsimp; linarith, ?_⟩
  change r ^ (-(n : ℤ)) < gaussianKernel n (z₀.2 - (z₀.2 - τ)) (z₀.1 - x)
  rw [sub_sub_cancel, heatBall_threshold_iff hr]
  exact hlevel

lemma heatBall_slice_tsupport_of_support_subset {n : ℕ} {r τ : ℝ}
    (z₀ : SpaceTime n) {f : Space n → ℝ}
    (hf : Function.support f ⊆ {x | (x, z₀.2 - τ) ∈ heatBall n r z₀}) :
    tsupport f ⊆ {x | (x, z₀.2 - τ) ∈ closure (heatBall n r z₀)} := by
  apply closure_minimal
  · intro x hx
    exact subset_closure (hf hx)
  · exact isClosed_closure.preimage (by fun_prop)

lemma heatBall_slice_hasCompactSupport_of_support_subset {n : ℕ} {r τ : ℝ}
    (hr : 0 < r) (z₀ : SpaceTime n) {f : Space n → ℝ}
    (hf : Function.support f ⊆ {x | (x, z₀.2 - τ) ∈ heatBall n r z₀}) :
    HasCompactSupport f := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall z₀.1 (((n : ℝ) + 1) * r))
  intro x hx
  rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
  exact (heatBall_space_linear_bound hr (hf hx)).le

lemma heatPotential_slice_hasCompactSupport {n : ℕ} {r τ : ℝ}
    (hr : 0 < r) (hτ : 0 < τ) (z₀ : SpaceTime n) :
    HasCompactSupport (fun x : Space n =>
      heatPotentialProfile (r ^ n * gaussianKernel n τ (z₀.1 - x))) :=
  heatBall_slice_hasCompactSupport_of_support_subset hr z₀
    (heatPotential_slice_support hr hτ z₀)

lemma heatPotential_slice_tsupport {n : ℕ} {r τ : ℝ}
    (hr : 0 < r) (hτ : 0 < τ) (z₀ : SpaceTime n) :
    tsupport (fun x : Space n =>
      heatPotentialProfile (r ^ n * gaussianKernel n τ (z₀.1 - x))) ⊆
      {x | (x, z₀.2 - τ) ∈ closure (heatBall n r z₀)} :=
  heatBall_slice_tsupport_of_support_subset z₀
    (heatPotential_slice_support hr hτ z₀)

lemma heatPotential_slice_deriv_tsupport {n : ℕ} {r τ : ℝ}
    (hr : 0 < r) (hτ : 0 < τ) (z₀ : SpaceTime n) (v : Space n) :
    tsupport (fun x : Space n => fderiv ℝ
      (fun y : Space n => heatPotentialProfile (r ^ n * gaussianKernel n τ (z₀.1 - y))) x v) ⊆
      {x | (x, z₀.2 - τ) ∈ closure (heatBall n r z₀)} :=
  (tsupport_fderiv_apply_subset ℝ v).trans (heatPotential_slice_tsupport hr hτ z₀)

lemma heatPotential_slice_deriv_hasCompactSupport {n : ℕ} {r τ : ℝ}
    (hr : 0 < r) (hτ : 0 < τ) (z₀ : SpaceTime n) (v : Space n) :
    HasCompactSupport (fun x : Space n => fderiv ℝ
      (fun y : Space n => heatPotentialProfile (r ^ n * gaussianKernel n τ (z₀.1 - y))) x v) :=
  HasCompactSupport.fderiv_apply ℝ (heatPotential_slice_hasCompactSupport hr hτ z₀) v

lemma heatPotential_slice_contDiff (n : ℕ) (r τ : ℝ) (x₀ : Space n) :
    ContDiff ℝ 1 (fun x : Space n => heatPotentialProfile (r ^ n * gaussianKernel n τ (x₀ - x))) := by
  apply contDiff_heatPotentialProfile.comp
  unfold gaussianKernel P201Specs.Heat.gaussianKernel
  exact contDiff_const.mul (contDiff_const.mul
    (((contDiff_norm_sq ℝ).comp (contDiff_const.sub contDiff_id)).neg.div_const (4 * τ)).exp)



/-- Compactly supported version of FTC allowing a countable set of corners. -/
lemma integral_eq_zero_of_hasDerivAt_off_countable
    {f f' : ℝ → ℝ} {s : Set ℝ} (hs : s.Countable)
    (hc : Continuous f) (hk : HasCompactSupport f)
    (hd : ∀ x ∉ s, HasDerivAt f (f' x) x) (hi : Integrable f') :
    (∫ x, f' x) = 0 := by
  obtain ⟨R, hR, hzero⟩ := hk.exists_pos_le_norm
  have hRle : -R ≤ R := by linarith
  have hexterior : ∀ᵐ x : ℝ, x ∉ Icc (-R) R → f' x = 0 := by
    filter_upwards [hs.ae_notMem (volume : Measure ℝ)] with x hx hxi
    have hnorm : R < ‖x‖ := by
      rw [Real.norm_eq_abs, lt_abs]
      simp only [mem_Icc, not_and_or, not_le] at hxi
      rcases hxi with hx | hx
      · exact Or.inr (by linarith)
      · exact Or.inl hx
    have he : f =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [(continuous_norm.continuousAt (x := x)).eventually (lt_mem_nhds hnorm)] with y hy
      exact hzero y hy.le
    have hz : HasDerivAt f 0 x := (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq he
    exact (hd x hx).unique hz
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero hexterior]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hRle]
  have hftc := integral_eq_of_hasDerivAt_off_countable_of_le f f' hRle hs hc.continuousOn
    (fun x hx => hd x hx.2) hi.intervalIntegrable
  rw [hftc, hzero R (by simpa using le_abs_self R), hzero (-R) (by simpa using le_abs_self R)]
  simp

/-- Fubini version of the compact-support FTC, with an exceptional set on each line. -/
lemma integral_eq_zero_of_hasDerivAt_slices
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    {F F' : α × ℝ → ℝ} (hi : Integrable F' (μ.prod volume))
    (hslice : ∀ᵐ a ∂μ, ∃ s : Set ℝ, s.Countable ∧
      Continuous (fun t => F (a, t)) ∧ HasCompactSupport (fun t => F (a, t)) ∧
      ∀ t ∉ s, HasDerivAt (fun t => F (a, t)) (F' (a, t)) t) :
    (∫ z, F' z ∂(μ.prod volume)) = 0 := by
  rw [integral_prod _ hi]
  have hs : ∀ᵐ a ∂μ, (∫ t, F' (a, t)) = 0 := by
    filter_upwards [hslice, hi.prod_right_ae] with a ha hia
    obtain ⟨s, hs, hc, hk, hd⟩ := ha
    exact integral_eq_zero_of_hasDerivAt_off_countable hs hc hk hd hia
  simp only [integral_congr_ae hs, integral_zero]

/-- Green's identity on a line, allowing a C¹ compactly supported test potential whose
second derivative has countably many exceptional points. Regularity of the other function
is only required on the support of the potential and of its first derivative. -/
lemma integral_mul_secondDeriv_eq_secondDeriv_mul
    {f f' f'' g g' g'' : ℝ → ℝ} {s : Set ℝ} (hs : s.Countable)
    (hg : ∀ x, HasDerivAt g (g' x) x) (hgc : Continuous g')
    (hg' : ∀ x ∉ s, HasDerivAt g' (g'' x) x)
    (hgk : HasCompactSupport g) (hg'k : HasCompactSupport g')
    (hf : ∀ x ∈ tsupport g ∪ tsupport g', HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ tsupport g ∪ tsupport g', HasDerivAt f' (f'' x) x)
    (hleft : Integrable (fun x => f x * g'' x))
    (hright : Integrable (fun x => f'' x * g x)) :
    (∫ x, f x * g'' x) = ∫ x, f'' x * g x := by
  let W : ℝ → ℝ := fun x => f x * g' x - f' x * g x
  have hWout {x : ℝ} (hx : x ∉ tsupport g ∪ tsupport g') :
      W =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    have hgout := notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (Or.inl h))
    have hg'out := notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (Or.inr h))
    filter_upwards [hgout, hg'out] with y hy hy'
    simp [W, hy, hy']
  have hWc : Continuous W := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ tsupport g ∪ tsupport g'
    · exact ((hf x hx).continuousAt.mul hgc.continuousAt).sub
        ((hf' x hx).continuousAt.mul (hg x).continuousAt)
    · exact continuousAt_const.congr (hWout hx).symm
  have hWk : HasCompactSupport W := by
    exact (hg'k.mul_left).sub (hgk.mul_left)
  have hWd : ∀ x ∉ s, HasDerivAt W (f x * g'' x - f'' x * g x) x := by
    intro x hxs
    by_cases hx : x ∈ tsupport g ∪ tsupport g'
    · convert ((hf x hx).mul (hg' x hxs)).sub ((hf' x hx).mul (hg x)) using 1; ring
    · have hgx : g x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (Or.inl h))
      have hg'x : g'' x = 0 := by
        have he := notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (Or.inr h))
        exact (hg' x hxs).unique ((hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq he)
      simpa only [hgx, hg'x, mul_zero, sub_zero] using
        (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq (hWout hx)
  have hWi := hleft.sub hright
  have h := integral_eq_zero_of_hasDerivAt_off_countable hs hWc hWk hWd hWi
  rw [integral_sub hleft hright, sub_eq_zero] at h
  exact h

/-- Integrate an integrable Euclidean function by isolating any coordinate. -/
lemma integral_euclidean_coordinate_slices {m : ℕ}
    (i : Fin (m + 1)) {F : EuclideanSpace ℝ (Fin (m + 1)) → ℝ}
    (hF : Integrable F) :
    (∫ x, F x) = ∫ y : Fin m → ℝ, ∫ t : ℝ, F (WithLp.toLp 2 (i.insertNth t y)) := by
  let e : ℝ × (Fin m → ℝ) ≃ᵐ (Fin (m + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm
  have he : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm _
  have hp : MeasurePreserving (@WithLp.toLp 2 (Fin (m + 1) → ℝ)) :=
    PiLp.volume_preserving_toLp _
  have hem := e.measurableEmbedding
  have hpm := (MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ)).measurableEmbedding
  have h1 : Integrable (fun v : Fin (m + 1) → ℝ => F (WithLp.toLp 2 v)) :=
    (hp.integrable_comp_emb hpm).mpr hF
  have h2 : Integrable (fun z : ℝ × (Fin m → ℝ) =>
      F (WithLp.toLp 2 (i.insertNth z.1 z.2))) := by
    simpa only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Function.comp_def, Fin.insertNthEquiv, Equiv.coe_fn_mk] using
      (he.integrable_comp_emb hem).mpr h1
  calc
    (∫ x, F x) = ∫ v : Fin (m + 1) → ℝ, F (WithLp.toLp 2 v) :=
      (hp.integral_comp hpm _).symm
    _ = ∫ z : ℝ × (Fin m → ℝ), F (WithLp.toLp 2 (i.insertNth z.1 z.2)) := by
      simpa only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Function.comp_def, Fin.insertNthEquiv, Equiv.coe_fn_mk] using
        (he.integral_comp' (fun v => F (WithLp.toLp 2 v))).symm
    _ = _ := integral_prod_symm _ h2

/-- Coordinate slices of an integrable Euclidean function are integrable almost everywhere. -/
lemma integrable_euclidean_coordinate_slices {m : ℕ}
    (i : Fin (m + 1)) {F : EuclideanSpace ℝ (Fin (m + 1)) → ℝ}
    (hF : Integrable F) :
    ∀ᵐ y : Fin m → ℝ, Integrable (fun t : ℝ => F (WithLp.toLp 2 (i.insertNth t y))) := by
  let e : ℝ × (Fin m → ℝ) ≃ᵐ (Fin (m + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm
  have he : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm _
  have hp : MeasurePreserving (@WithLp.toLp 2 (Fin (m + 1) → ℝ)) :=
    PiLp.volume_preserving_toLp _
  have h1 : Integrable (fun v : Fin (m + 1) → ℝ => F (WithLp.toLp 2 v)) :=
    (hp.integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ)).measurableEmbedding).mpr hF
  have h2 : Integrable (fun z : ℝ × (Fin m → ℝ) =>
      F (WithLp.toLp 2 (i.insertNth z.1 z.2))) := by
    simpa only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Function.comp_def,
      Fin.insertNthEquiv, Equiv.coe_fn_mk] using
      (he.integrable_comp_emb e.measurableEmbedding).mpr h1
  exact h2.prod_left_ae

/-- Coordinatewise spatial Green identity for a compactly supported C¹ potential whose
second coordinate derivative can fail at countably many points on each coordinate line.
In particular a spherical interface has two exceptional points per line. -/
lemma integral_euclidean_mul_secondDeriv_eq_secondDeriv_mul {m : ℕ}
    (i : Fin (m + 1))
    {f f' f'' g g' g'' : EuclideanSpace ℝ (Fin (m + 1)) → ℝ}
    (s : (Fin m → ℝ) → Set ℝ) (hs : ∀ y, (s y).Countable)
    (hg : ∀ y t, HasDerivAt (fun t => g (WithLp.toLp 2 (i.insertNth t y)))
      (g' (WithLp.toLp 2 (i.insertNth t y))) t)
    (hgc : ∀ y, Continuous (fun t => g' (WithLp.toLp 2 (i.insertNth t y))))
    (hg' : ∀ y t, t ∉ s y → HasDerivAt (fun t => g' (WithLp.toLp 2 (i.insertNth t y)))
      (g'' (WithLp.toLp 2 (i.insertNth t y))) t)
    (hgk : ∀ y, HasCompactSupport (fun t => g (WithLp.toLp 2 (i.insertNth t y))))
    (hg'k : ∀ y, HasCompactSupport (fun t => g' (WithLp.toLp 2 (i.insertNth t y))))
    (hf : ∀ y t, t ∈ tsupport (fun t => g (WithLp.toLp 2 (i.insertNth t y))) ∪
        tsupport (fun t => g' (WithLp.toLp 2 (i.insertNth t y))) →
      HasDerivAt (fun t => f (WithLp.toLp 2 (i.insertNth t y)))
        (f' (WithLp.toLp 2 (i.insertNth t y))) t)
    (hf' : ∀ y t, t ∈ tsupport (fun t => g (WithLp.toLp 2 (i.insertNth t y))) ∪
        tsupport (fun t => g' (WithLp.toLp 2 (i.insertNth t y))) →
      HasDerivAt (fun t => f' (WithLp.toLp 2 (i.insertNth t y)))
        (f'' (WithLp.toLp 2 (i.insertNth t y))) t)
    (hleft : Integrable (fun x => f x * g'' x))
    (hright : Integrable (fun x => f'' x * g x)) :
    (∫ x, f x * g'' x) = ∫ x, f'' x * g x := by
  rw [integral_euclidean_coordinate_slices i hleft,
    integral_euclidean_coordinate_slices i hright]
  apply integral_congr_ae
  filter_upwards [integrable_euclidean_coordinate_slices i hleft,
    integrable_euclidean_coordinate_slices i hright] with y hly hry
  exact integral_mul_secondDeriv_eq_secondDeriv_mul (hs y) (hg y) (hgc y) (hg' y)
    (hgk y) (hg'k y) (hf y) (hf' y) hly hry



lemma norm_sq_sub_coordinateInsertion {m : ℕ} (i : Fin (m + 1))
    (x : EuclideanSpace ℝ (Fin (m + 1))) (y : Fin m → ℝ) (t : ℝ) :
    ‖x - WithLp.toLp 2 (i.insertNth t y)‖ ^ 2 =
      (x i - t) ^ 2 + ∑ j : Fin m, (x (i.succAbove j) - y j) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succAbove _ i]
  simp only [PiLp.sub_apply, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove, Real.norm_eq_abs, sq_abs]

lemma gaussian_eq_gaussian_iff_norm_sq {n : ℕ} {τ : ℝ} (hτ : 0 < τ)
    (x y : Space n) : gaussianKernel n τ x = gaussianKernel n τ y ↔ ‖x‖ ^ 2 = ‖y‖ ^ 2 := by
  unfold gaussianKernel P201Specs.Heat.gaussianKernel
  rw [mul_right_inj' (Real.rpow_pos_of_pos (by positivity : 0 < 4 * Real.pi * τ) _).ne',
    Real.exp_injective.eq_iff]
  constructor <;> intro h
  · have ht : 4 * τ ≠ 0 := by positivity
    apply neg_injective
    exact (div_left_inj' ht).mp h
  · rw [h]

lemma gaussian_levelSet_coordinate_finite {m : ℕ} (i : Fin (m + 1))
    {τ : ℝ} (hτ : 0 < τ) (c : ℝ)
    (x : Space (m + 1)) (y : Fin m → ℝ) :
    {t : ℝ | gaussianKernel (m + 1) τ (x - WithLp.toLp 2 (i.insertNth t y)) = c}.Finite := by
  let S : Set ℝ := {t : ℝ |
    gaussianKernel (m + 1) τ (x - WithLp.toLp 2 (i.insertNth t y)) = c}
  by_cases hS : S.Nonempty
  · obtain ⟨a, ha⟩ := hS
    apply (Set.toFinite ({a, 2 * x i - a} : Set ℝ)).subset
    intro t ht
    have hG := ht.trans ha.symm
    have hn := (gaussian_eq_gaussian_iff_norm_sq hτ _ _).mp hG
    rw [norm_sq_sub_coordinateInsertion, norm_sq_sub_coordinateInsertion] at hn
    have he : (x i - t) ^ 2 = (x i - a) ^ 2 := by linarith
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp he) with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by simp only [mem_singleton_iff]; linarith)
  · change S.Finite
    rw [Set.not_nonempty_iff_eq_empty.mp hS]
    exact Set.finite_empty



lemma gaussian_spatial_contDiff (n : ℕ) (τ : ℝ) :
    ContDiff ℝ ∞ (gaussianKernel n τ) := by
  unfold gaussianKernel P201Specs.Heat.gaussianKernel
  exact contDiff_const.mul (((contDiff_norm_sq ℝ).neg.div_const (4 * τ)).exp)

lemma heatPotential_coordinate_deriv (n : ℕ) (b τ : ℝ) (x : Space n) (i : Fin n) :
    fderiv ℝ (fun y => heatPotentialProfile (b * gaussianKernel n τ y)) x (coordinate n i) =
      heatPotentialProfileSlope (b * gaussianKernel n τ x) * b *
        fderiv ℝ (gaussianKernel n τ) x (coordinate n i) := by
  have hg := ((gaussian_spatial_contDiff n τ).differentiable (by simp) x).hasFDerivAt.const_mul b
  have hd := (hasDerivAt_heatPotentialProfile _).comp_hasFDerivAt x hg
  change HasFDerivAt (fun y => heatPotentialProfile (b * gaussianKernel n τ y)) _ x at hd
  rw [hd.fderiv]
  simp
  ring

lemma heatPotential_coordinate_second_deriv (n : ℕ) (b τ : ℝ) (x : Space n) (i : Fin n)
    (hx : b * gaussianKernel n τ x ≠ 1) :
    fderiv ℝ (fun y => fderiv ℝ
      (fun v => heatPotentialProfile (b * gaussianKernel n τ v)) y (coordinate n i)) x
      (coordinate n i) =
      (if 1 < b * gaussianKernel n τ x then 1 / (b * gaussianKernel n τ x) ^ 2 else 0) *
        b ^ 2 * (fderiv ℝ (gaussianKernel n τ) x (coordinate n i)) ^ 2 +
      heatPotentialProfileSlope (b * gaussianKernel n τ x) * b *
        fderiv ℝ (fun y => fderiv ℝ (gaussianKernel n τ) y (coordinate n i)) x
          (coordinate n i) := by
  simp_rw [heatPotential_coordinate_deriv]
  have hg := ((gaussian_spatial_contDiff n τ).differentiable (by simp) x).hasFDerivAt
  have hq := (hasDerivAt_heatPotentialProfileSlope hx).comp_hasFDerivAt x (hg.const_mul b)
  have hgc : DifferentiableAt ℝ
      (fun y => fderiv ℝ (gaussianKernel n τ) y (coordinate n i)) x := by
    simp_rw [gaussian_coordinate_deriv]
    have hc : HasFDerivAt (fun y : Space n => y i)
        (PiLp.proj 2 (fun _ : Fin n => ℝ) i) x :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).hasFDerivAt
    exact ((gaussian_spatial_contDiff n τ).differentiable (by simp) x).mul
      (by simpa only [div_eq_mul_inv, Pi.neg_apply] using hc.differentiableAt.neg.mul_const ((2 * τ)⁻¹))
  have hd := (hq.mul_const b).mul hgc.hasFDerivAt
  change HasFDerivAt (fun y => heatPotentialProfileSlope (b * gaussianKernel n τ y) * b *
    fderiv ℝ (gaussianKernel n τ) y (coordinate n i)) _ x at hd
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, Function.comp_apply]
  ring

lemma heatPotential_time_deriv (n : ℕ) (b : ℝ) {τ : ℝ} (hτ : 0 < τ) (x : Space n) :
    deriv (fun θ => heatPotentialProfile (b * gaussianKernel n θ x)) τ =
      heatPotentialProfileSlope (b * gaussianKernel n τ x) * b *
        deriv (fun θ => gaussianKernel n θ x) τ := by
  have hg : DifferentiableAt ℝ (fun θ => gaussianKernel n θ x) τ := by
    unfold gaussianKernel P201Specs.Heat.gaussianKernel
    apply DifferentiableAt.mul
    · apply DifferentiableAt.rpow_const
      · fun_prop
      · exact Or.inl (by positivity)
    · apply DifferentiableAt.exp
      apply DifferentiableAt.div
      · exact differentiableAt_const _
      · fun_prop
      · positivity
  have hd := (hasDerivAt_heatPotentialProfile _).comp τ (hg.hasDerivAt.const_mul b)
  simpa only [mul_assoc, Function.comp_def] using hd.deriv

lemma gaussian_coordinate_deriv_sq_sum (n : ℕ) (τ : ℝ) (x : Space n) :
    (∑ i : Fin n, (fderiv ℝ (gaussianKernel n τ) x (coordinate n i)) ^ 2) =
      gaussianKernel n τ x ^ 2 * (‖x‖ ^ 2 / (4 * τ ^ 2)) := by
  simp_rw [gaussian_coordinate_deriv, mul_pow, div_pow, neg_sq]
  rw [← Finset.mul_sum, ← Finset.sum_div, PiLp.norm_sq_eq_of_L2]
  simp only [Real.norm_eq_abs, sq_abs]
  ring

lemma gaussian_coordinate_second_deriv_sum (n : ℕ) (τ : ℝ) (x : Space n) :
    (∑ i : Fin n, fderiv ℝ
      (fun y => fderiv ℝ (gaussianKernel n τ) y (coordinate n i)) x (coordinate n i)) =
      gaussianKernel n τ x * (-(n : ℝ) / (2 * τ) + ‖x‖ ^ 2 / (4 * τ ^ 2)) := by
  simp_rw [gaussian_coordinate_second_deriv]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_div, PiLp.norm_sq_eq_of_L2]
  simp only [Real.norm_eq_abs, sq_abs, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  ring

lemma heatPotential_spatial_time_identity (n : ℕ) {b τ : ℝ} (hb : 0 < b) (hτ : 0 < τ)
    (x : Space n) (hx : b * gaussianKernel n τ x ≠ 1) :
    (∑ i : Fin n, fderiv ℝ
      (fun y => fderiv ℝ (fun v => heatPotentialProfile (b * gaussianKernel n τ v)) y
        (coordinate n i)) x (coordinate n i)) -
      deriv (fun θ => heatPotentialProfile (b * gaussianKernel n θ x)) τ =
      if 1 < b * gaussianKernel n τ x then ‖x‖ ^ 2 / (4 * τ ^ 2) else 0 := by
  simp_rw [heatPotential_coordinate_second_deriv n b τ x _ hx]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    gaussian_coordinate_deriv_sq_sum, gaussian_coordinate_second_deriv_sum,
    heatPotential_time_deriv n b hτ, gaussian_time_deriv n hτ]
  have hG : 0 < gaussianKernel n τ x := by
    unfold gaussianKernel P201Specs.Heat.gaussianKernel
    positivity
  by_cases h : 1 < b * gaussianKernel n τ x
  · simp only [h, ↓reduceIte]
    field_simp
    ring
  · simp only [h, ↓reduceIte, heatPotentialProfileSlope, zero_mul, zero_add]
    ring


lemma IsClassicalCaloricOn.mono {n : ℕ} {u : SpaceTime n → ℝ}
    {S T : Set (SpaceTime n)} (h : IsClassicalCaloricOn u T) (hST : S ⊆ T) :
    IsClassicalCaloricOn u S := by
  rcases h with ⟨h₀, h₁, h₂, h₃, h₄⟩
  exact ⟨h₀.mono hST, h₁.mono hST, h₂.mono hST, h₃.mono hST,
    fun z hz => h₄ z (hST hz)⟩

/-- Reduces the neighborhood version to the version with only past regularity. -/
lemma heatBallMeanValueNeighborhood_of_oneSided
    (h : P201Specs.Heat.heatBallMeanValueOneSidedStatement) :
    P201Specs.Heat.heatBallMeanValueNeighborhoodStatement := by
  intro n hn r hr z₀ u hu
  rcases hu with ⟨U, _, hU, hu⟩
  exact h n hn r hr z₀ u (hu.1.mono hU)
    (IsClassicalCaloricOn.mono hu (fun _ hz => hU hz.1))

/-- Pull the prefactor outside the integral; this is the exact source formula. -/
lemma meanValueIdentity_iff_weighted {n : ℕ} (u : SpaceTime n → ℝ)
    (r : ℝ) (z₀ : SpaceTime n) :
    HeatBallMeanValueIdentity u r z₀ ↔
      u z₀ = ∫ z in heatBall n r z₀, u z * heatBallWeight n r z₀ z
        ∂spaceTimeMeasure n := by
  unfold HeatBallMeanValueIdentity P201Specs.Heat.HeatBallMeanValueIdentity
    heatBallWeight P201Specs.Heat.heatBallWeight
  rw [← integral_const_mul]
  simp only [mul_left_comm]

/-- The remaining integrability problem is entirely the one for the weight. -/
lemma heatBall_bounded_integrable {n : ℕ} {r : ℝ} (hr : 0 < r)
    (z₀ : SpaceTime n) (u : SpaceTime n → ℝ)
    (hu : AEStronglyMeasurable u ((spaceTimeMeasure n).restrict (heatBall n r z₀)))
    (hbound : ∃ M : ℝ, ∀ z ∈ heatBall n r z₀, ‖u z‖ ≤ M)
    (hw : Integrable (heatBallWeight n r z₀)
      ((spaceTimeMeasure n).restrict (heatBall n r z₀))) :
    Integrable (fun z => u z * (‖z₀.1 - z.1‖ ^ 2 / (z₀.2 - z.2) ^ 2))
      ((spaceTimeMeasure n).restrict (heatBall n r z₀)) := by
  obtain ⟨M, hM⟩ := hbound
  have hb : ∀ᵐ z ∂(spaceTimeMeasure n).restrict (heatBall n r z₀), ‖u z‖ ≤ M := by
    filter_upwards [ae_restrict_mem (heatBall_measurableSet n r z₀)] with z hz
    exact hM z hz
  have hint := (hw.bdd_mul hu hb).const_mul (4 * r ^ n)
  convert hint using 1
  funext z
  unfold heatBallWeight P201Specs.Heat.heatBallWeight
  field_simp

theorem heatBallBoundedIntegral : P201Specs.Heat.heatBallBoundedIntegralStatement := by
  intro n hn r hr z₀ u hu hb
  exact heatBall_bounded_integrable hr z₀ u hu hb
    (heatBallWeightIntegrable n hn r hr z₀)


/-- A normalized nonnegative density controls the error of a weighted average. -/
lemma integral_error_bound_of_probability_density {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {w u : α → ℝ} {u₀ ε : ℝ}
    (hw : Integrable w μ) (hw₀ : ∀ᵐ x ∂μ, 0 ≤ w x) (hw₁ : (∫ x, w x ∂μ) = 1)
    (hu : AEStronglyMeasurable u μ) (hb : ∀ᵐ x ∂μ, ‖u x - u₀‖ ≤ ε) :
    ‖(∫ x, u x * w x ∂μ) - u₀‖ ≤ ε := by
  have hd := hw.bdd_mul (hu.sub aestronglyMeasurable_const) hb
  have hi : Integrable (fun x => u x * w x) μ := by
    convert hd.add (hw.const_mul u₀) using 1
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hid : (fun x => (u x - u₀) * w x) = (fun x => u x * w x - u₀ * w x) := by
    funext x
    ring
  have heq : (∫ x, (u x - u₀) * w x ∂μ) = (∫ x, u x * w x ∂μ) - u₀ := by
    rw [hid, integral_sub hi (hw.const_mul u₀), integral_const_mul, hw₁, mul_one]
  rw [← heq]
  calc
    ‖∫ x, (u x - u₀) * w x ∂μ‖ ≤ ∫ x, ‖(u x - u₀) * w x‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, ε * w x ∂μ := by
      apply integral_mono_ae hd.norm (hw.const_mul ε)
      filter_upwards [hw₀, hb] with x hx hbx
      rw [norm_mul, Real.norm_of_nonneg hx]
      exact mul_le_mul_of_nonneg_right hbx hx
    _ = ε := by rw [integral_const_mul, hw₁, mul_one]

/-- Final assembly, conditional only on normalization and scale invariance.
Neither of those two analytic assertions is claimed by this reduction. -/
lemma heatBallMeanValue_of_mass_and_scale {n : ℕ} (hn : 1 ≤ n) {b : ℝ} (hb : 0 < b)
    (z₀ : SpaceTime n) (u : SpaceTime n → ℝ)
    (hu : ContinuousOn u (closure (heatBall n b z₀)))
    (hw : ∀ a : ℝ, 0 < a → Integrable (heatBallWeight n a z₀)
      ((spaceTimeMeasure n).restrict (heatBall n a z₀)))
    (hm : ∀ a : ℝ, 0 < a →
      (∫ z in heatBall n a z₀, heatBallWeight n a z₀ z ∂spaceTimeMeasure n) = 1)
    (hs : ∀ a : ℝ, 0 < a → a ≤ b →
      (∫ z in heatBall n a z₀, u z * heatBallWeight n a z₀ z ∂spaceTimeMeasure n) =
      (∫ z in heatBall n b z₀, u z * heatBallWeight n b z₀ z ∂spaceTimeMeasure n)) :
    HeatBallMeanValueIdentity u b z₀ := by
  rw [meanValueIdentity_iff_weighted]
  apply eq_of_forall_dist_le
  intro ε hε
  have htop := hu z₀ (heatBallTopInClosure n hn b hb z₀)
  obtain ⟨η, hη, hclose⟩ := Metric.continuousWithinAt_iff.mp htop ε hε
  obtain ⟨δ, hδ, hsmall⟩ := heatBall_shrinking hn z₀ hη
  let a := min b δ / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a ≤ b := by
    dsimp [a]
    linarith [min_le_left b δ]
  have haδ : a < δ := by
    dsimp [a]
    linarith [min_le_right b δ]
  have hsub : heatBall n a z₀ ⊆ closure (heatBall n b z₀) :=
    fun z hz => subset_closure (heatBall_mono ha hab z₀ hz)
  have hum : AEStronglyMeasurable u
      ((spaceTimeMeasure n).restrict (heatBall n a z₀)) :=
    (hu.mono hsub).aestronglyMeasurable (heatBall_measurableSet n a z₀)
  have hbound : ∀ᵐ z ∂(spaceTimeMeasure n).restrict (heatBall n a z₀), ‖u z - u z₀‖ ≤ ε := by
    filter_upwards [ae_restrict_mem (heatBall_measurableSet n a z₀)] with z hz
    have hdist := Metric.mem_ball.mp (hsmall a ha haδ hz)
    simpa [dist_eq_norm] using (hclose (hsub hz) hdist).le
  have havg := integral_error_bound_of_probability_density
    ((spaceTimeMeasure n).restrict (heatBall n a z₀))
    (hw a ha) (ae_of_all _ (heatBallWeightNonnegative n a ha z₀)) (hm a ha) hum hbound
  rw [hs a ha hab] at havg
  simpa [dist_eq_norm, norm_sub_rev] using havg


lemma tendsto_setIntegral_time_cut {X : Type*} [MeasurableSpace X]
    (μ : Measure (X × ℝ)) {S : Set (X × ℝ)} (hS : MeasurableSet S)
    {T : ℝ} (hT : ∀ z ∈ S, z.2 < T) {f : X × ℝ → ℝ}
    (hf : IntegrableOn f S μ) :
    Tendsto (fun δ : ℝ => ∫ z in S ∩ {z | z.2 ≤ T - δ}, f z ∂μ)
      (𝓝[>] 0) (𝓝 (∫ z in S, f z ∂μ)) := by
  have hm (δ : ℝ) : MeasurableSet {z : X × ℝ | z.2 ≤ T - δ} :=
    measurableSet_le measurable_snd measurable_const
  have hc := tendsto_integral_filter_of_dominated_convergence
    (μ := μ.restrict S) (l := 𝓝[>] (0 : ℝ))
    (F := fun δ => {z : X × ℝ | z.2 ≤ T - δ}.indicator f)
    (f := f) (fun z => ‖f z‖) ?_ ?_ hf.norm ?_
  · apply hc.congr'
    exact Eventually.of_forall fun δ => by
      dsimp only
      rw [integral_indicator (hm δ), Measure.restrict_restrict (hm δ), inter_comm]
  · exact Eventually.of_forall fun δ => hf.aestronglyMeasurable.indicator (hm δ)
  · exact Eventually.of_forall fun δ => ae_of_all _ fun z => norm_indicator_le_norm_self _ _
  · filter_upwards [ae_restrict_mem hS] with z hz
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_lt_nhds (sub_pos.mpr (hT z hz)) :
      ∀ᶠ δ : ℝ in 𝓝 0, δ < T - z.2).filter_mono nhdsWithin_le_nhds] with δ hδ
    rw [indicator_of_mem (by change z.2 ≤ T - δ; linarith : z ∈ {z : X × ℝ | z.2 ≤ T - δ})]

lemma tendsto_heatBall_integral_time_cut {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r)
    (z₀ : SpaceTime n) {u : SpaceTime n → ℝ}
    (hu : ContinuousOn u (closure (heatBall n r z₀))) :
    Tendsto (fun δ : ℝ => ∫ z in heatBall n r z₀ ∩ {z | z.2 ≤ z₀.2 - δ},
      u z * (‖z₀.1 - z.1‖ ^ 2 / (4 * (z₀.2 - z.2) ^ 2)) ∂spaceTimeMeasure n)
      (𝓝[>] 0) (𝓝 (∫ z in heatBall n r z₀,
        u z * (‖z₀.1 - z.1‖ ^ 2 / (4 * (z₀.2 - z.2) ^ 2)) ∂spaceTimeMeasure n)) := by
  apply tendsto_setIntegral_time_cut (spaceTimeMeasure n) (heatBall_measurableSet n r z₀)
    (fun z hz => hz.1)
  have hi := heatBall_bounded_integrable hr z₀ u
    ((hu.mono subset_closure).aestronglyMeasurable (heatBall_measurableSet n r z₀))
    (heatBall_bounded_of_continuousOn_closure hn hr z₀ hu)
    (heatBallWeightIntegrable n hn r hr z₀)
  unfold IntegrableOn
  convert hi.const_mul (1/4 : ℝ) using 1
  funext z
  simp only [div_mul_eq_div_div]
  ring



lemma heatPotentialProfile_eq_zero_of_time_ge {n : ℕ} (hn : 1 ≤ n) {r τ : ℝ}
    (hr : 0 < r) (hτ : r ^ 2 / (4 * Real.pi) ≤ τ) (z₀ : SpaceTime n) (x : Space n) :
    heatPotentialProfile (r ^ n * gaussianKernel n τ (z₀.1 - x)) = 0 := by
  have hT : 0 < r ^ 2 / (4 * Real.pi) := by positivity
  by_contra hne
  have hm := heatPotential_slice_support hr (hT.trans_le hτ) z₀ hne
  have hb := heatBall_backwardTime_bound hn hr hm
  dsimp only at hb
  rw [sub_sub_cancel] at hb
  linarith

lemma integral_heatPotentialProfile_eq_zero_of_time_ge {n : ℕ} (hn : 1 ≤ n) {r τ : ℝ}
    (hr : 0 < r) (hτ : r ^ 2 / (4 * Real.pi) ≤ τ) (z₀ : SpaceTime n)
    (u : SpaceTime n → ℝ) :
    (∫ x, u (x, z₀.2 - τ) * heatPotentialProfile
      (r ^ n * gaussianKernel n τ (z₀.1 - x)) ∂spatialMeasure n) = 0 := by
  simp_rw [heatPotentialProfile_eq_zero_of_time_ge hn hr hτ, mul_zero]
  exact integral_zero _ _

lemma continuousOn_integral_heatPotentialProfile {n : ℕ} {r : ℝ} (hr : 0 < r)
    (z₀ : SpaceTime n) (u : SpaceTime n → ℝ) (hu : Continuous u) :
    ContinuousOn (fun τ : ℝ => ∫ x, u (x, z₀.2 - τ) * heatPotentialProfile
      (r ^ n * gaussianKernel n τ (z₀.1 - x)) ∂spatialMeasure n) (Ioi 0) := by
  let R : ℝ := ((n : ℝ) + 1) * r
  apply continuousOn_integral_of_compact_support
    (k := Metric.closedBall z₀.1 R) (isCompact_closedBall _ _)
  · intro z hz
    have hτ : 0 < z.1 := hz.1
    have hg : ContinuousAt (fun p : ℝ × Space n =>
        gaussianKernel n p.1 (z₀.1 - p.2)) z := by
      unfold gaussianKernel P201Specs.Heat.gaussianKernel
      apply ContinuousAt.mul
      · apply ContinuousAt.rpow_const
        · fun_prop
        · exact Or.inl (by positivity)
      · apply Real.continuous_exp.continuousAt.comp
        apply ContinuousAt.div
        · fun_prop
        · fun_prop
        · positivity
    exact ((hu.continuousAt.comp (by fun_prop)).mul
      (continuous_heatPotentialProfile.continuousAt.comp
        (continuousAt_const.mul hg))).continuousWithinAt
  · intro τ x hτ hx
    have hzero : heatPotentialProfile (r ^ n * gaussianKernel n τ (z₀.1 - x)) = 0 := by
      by_contra hne
      have hm := heatPotential_slice_support hr hτ z₀ hne
      have hb := heatBall_space_linear_bound hr hm
      apply hx
      rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
      exact hb.le
    simp only [hzero, mul_zero]

lemma tendsto_integral_heatPotentialProfile_bottom {n : ℕ} (hn : 1 ≤ n) {r : ℝ}
    (hr : 0 < r) (z₀ : SpaceTime n) (u : SpaceTime n → ℝ) (hu : Continuous u) :
    Tendsto (fun τ : ℝ => ∫ x, u (x, z₀.2 - τ) * heatPotentialProfile
      (r ^ n * gaussianKernel n τ (z₀.1 - x)) ∂spatialMeasure n)
      (𝓝 (r ^ 2 / (4 * Real.pi))) (𝓝 0) := by
  have hT : 0 < r ^ 2 / (4 * Real.pi) := by positivity
  have hc := (continuousOn_integral_heatPotentialProfile hr z₀ u hu).continuousAt
    (Ioi_mem_nhds hT)
  have ht := hc.tendsto
  rw [integral_heatPotentialProfile_eq_zero_of_time_ge hn hr le_rfl] at ht
  exact ht

lemma tendsto_integral_heatPotentialProfile_bottom_of_continuousOn {n : ℕ} (hn : 1 ≤ n)
    {r : ℝ} (hr : 0 < r) (z₀ : SpaceTime n) (u : SpaceTime n → ℝ)
    (hu : ContinuousOn u (closure (heatBall n r z₀))) :
    Tendsto (fun τ : ℝ => ∫ x, u (x, z₀.2 - τ) * heatPotentialProfile
      (r ^ n * gaussianKernel n τ (z₀.1 - x)) ∂spatialMeasure n)
      (𝓝 (r ^ 2 / (4 * Real.pi))) (𝓝 0) := by
  obtain ⟨v, hv, _, hvu⟩ := exists_bounded_continuous_heatBall_extension hn hr z₀ hu
  have ht := tendsto_integral_heatPotentialProfile_bottom hn hr z₀ v hv
  apply ht.congr'
  filter_upwards [eventually_gt_nhds (show 0 < r ^ 2 / (4 * Real.pi) by positivity)] with τ hτ
  apply integral_congr_ae
  filter_upwards [] with x
  have hp := heatPotentialProfile_mul_eqOn_heatBall hr
    (z := (x,z₀.2-τ)) (by dsimp; linarith) hvu
  simpa using hp



lemma gaussian_sub_symm (n : ℕ) (τ : ℝ) (x y : Space n) :
    gaussianKernel n τ (x - y) = gaussianKernel n τ (y - x) := by
  unfold gaussianKernel P201Specs.Heat.gaussianKernel
  rw [norm_sub_rev]

lemma heatPotential_centered_spatial_time_identity (n : ℕ) {b τ : ℝ}
    (hb : 0 < b) (hτ : 0 < τ) (x₀ x : Space n)
    (hx : b * gaussianKernel n τ (x₀ - x) ≠ 1) :
    (∑ i : Fin n, fderiv ℝ
      (fun y => fderiv ℝ (fun v => heatPotentialProfile (b * gaussianKernel n τ (x₀ - v))) y
        (coordinate n i)) x (coordinate n i)) -
      deriv (fun θ => heatPotentialProfile (b * gaussianKernel n θ (x₀ - x))) τ =
      if 1 < b * gaussianKernel n τ (x₀ - x) then ‖x₀ - x‖ ^ 2 / (4 * τ ^ 2) else 0 := by
  simp_rw [gaussian_sub_symm n _ x₀]
  have h1 (y : Space n) : fderiv ℝ
      (fun v => heatPotentialProfile (b * gaussianKernel n τ (v - x₀))) y =
      fderiv ℝ (fun v => heatPotentialProfile (b * gaussianKernel n τ v)) (y - x₀) :=
    fderiv_comp_sub (𝕜 := ℝ) (f := fun v => heatPotentialProfile (b * gaussianKernel n τ v)) (x := y) x₀
  simp_rw [h1]
  have h2 (i : Fin n) : fderiv ℝ
      (fun y => fderiv ℝ (fun v => heatPotentialProfile (b * gaussianKernel n τ v))
        (y - x₀) (coordinate n i)) x =
      fderiv ℝ (fun y => fderiv ℝ (fun v => heatPotentialProfile (b * gaussianKernel n τ v))
        y (coordinate n i)) (x - x₀) :=
    fderiv_comp_sub (𝕜 := ℝ)
      (f := fun y => fderiv ℝ (fun v => heatPotentialProfile (b * gaussianKernel n τ v))
        y (coordinate n i)) (x := x) x₀
  simp_rw [h2]
  simpa only [gaussian_sub_symm n τ x₀ x, norm_sub_rev] using
    heatPotential_spatial_time_identity n hb hτ (x - x₀)
      (by rwa [gaussian_sub_symm n τ x₀ x] at hx)

lemma contDiffAt_heatPotentialProfile_of_ne_one {v : ℝ} (hv : v ≠ 1) :
    ContDiffAt ℝ ∞ heatPotentialProfile v := by
  rcases lt_or_gt_of_ne hv with hv | hv
  · have heq : heatPotentialProfile =ᶠ[𝓝 v] (fun _ => (0 : ℝ)) := by
      filter_upwards [eventually_lt_nhds hv] with y hy
      exact heatPotentialProfile_of_le hy.le
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · have heq : heatPotentialProfile =ᶠ[𝓝 v] (fun y => y - 1 - Real.log y) := by
      filter_upwards [eventually_gt_nhds hv] with y hy
      exact heatPotentialProfile_of_gt hy
    have hc : ContDiffAt ℝ ∞ (fun y : ℝ => y - 1 - Real.log y) v := by
      fun_prop (disch := linarith)
    exact hc.congr_of_eventuallyEq heq

lemma heatPotential_centered_contDiffAt {n : ℕ} (b τ : ℝ) (x₀ x : Space n)
    (hx : b * gaussianKernel n τ (x₀ - x) ≠ 1) :
    ContDiffAt ℝ ∞
      (fun y => heatPotentialProfile (b * gaussianKernel n τ (x₀ - y))) x := by
  have hg : ContDiffAt ℝ ∞ (fun y => b * gaussianKernel n τ (x₀ - y)) x := by
    exact contDiffAt_const.mul ((gaussian_spatial_contDiff n τ).contDiffAt.comp x
      (contDiffAt_const.sub contDiffAt_id))
  exact (contDiffAt_heatPotentialProfile_of_ne_one hx).comp x hg



lemma gaussian_levelSet_measure_zero {n : ℕ} (hn : 1 ≤ n) {τ : ℝ} (hτ : 0 < τ)
    {b : ℝ} (hb : b ≠ 0) (x₀ : Space n) :
    (spatialMeasure n) {x : Space n | b * gaussianKernel n τ (x₀ - x) = 1} = 0 := by
  have hd : Module.finrank ℝ (Space n) = n := by simp [Space, P201Specs.Space]
  have : Nontrivial (Space n) :=
    Module.finrank_pos_iff.mp (by omega : 0 < Module.finrank ℝ (Space n))
  by_cases hS : {x : Space n | b * gaussianKernel n τ (x₀ - x) = 1}.Nonempty
  · obtain ⟨a, ha⟩ := hS
    apply measure_mono_null (t := Metric.sphere x₀ ‖x₀ - a‖) ?_
      (Measure.addHaar_sphere (spatialMeasure n) _ _)
    intro x hx
    have hG : gaussianKernel n τ (x₀ - x) = gaussianKernel n τ (x₀ - a) :=
      mul_left_cancel₀ hb (hx.trans ha.symm)
    have hnorm := (gaussian_eq_gaussian_iff_norm_sq hτ _ _).mp hG
    rw [Metric.mem_sphere, dist_comm, dist_eq_norm]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hnorm
  · rw [Set.not_nonempty_iff_eq_empty.mp hS, measure_empty]

lemma ae_gaussian_level_ne_one {n : ℕ} (hn : 1 ≤ n) {τ : ℝ} (hτ : 0 < τ)
    {b : ℝ} (hb : b ≠ 0) (x₀ : Space n) :
    ∀ᵐ x ∂spatialMeasure n, b * gaussianKernel n τ (x₀ - x) ≠ 1 := by
  rw [ae_iff]
  simpa only [not_not] using gaussian_levelSet_measure_zero hn hτ hb x₀

lemma ae_prod_gaussian_level_ne_one {n : ℕ} (hn : 1 ≤ n) {b : ℝ} (hb : b ≠ 0)
    (x₀ : Space n) (a d : ℝ) (ha : 0 < a) :
    ∀ᵐ z ∂(volume.restrict (Icc a d)).prod (spatialMeasure n),
      b * gaussianKernel n z.1 (x₀ - z.2) ≠ 1 := by
  apply (Measure.ae_prod_iff_ae_ae ?_).mpr
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
    exact ae_gaussian_level_ne_one hn (ha.trans_le hτ.1) hb x₀
  · have hm : Measurable (fun z : ℝ × Space n =>
        b * gaussianKernel n z.1 (x₀ - z.2)) := by
      unfold gaussianKernel P201Specs.Heat.gaussianKernel
      fun_prop
    exact (measurableSet_eq_fun hm measurable_const).compl



/-- Endpoint assembly for the truncated heat potential proof. The strip identity is
an explicit analytic premise, not an asserted consequence of caloricity here. -/
lemma heatBallMeanValue_of_truncated_potential {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r)
    (z₀ : SpaceTime n) (u : SpaceTime n → ℝ)
    (hu : ContinuousOn u (closure (heatBall n r z₀)))
    (htrunc : ∀ δ : ℝ, 0 < δ → δ < r ^ 2 / (4 * Real.pi) →
      (∫ y, u (y, z₀.2 - δ) * heatPotentialProfile
        (r ^ n * gaussianKernel n δ (z₀.1 - y)) ∂spatialMeasure n) =
      ∫ z in heatBall n r z₀ ∩ {z | z.2 ≤ z₀.2 - δ},
        u z * (‖z₀.1 - z.1‖ ^ 2 / (4 * (z₀.2 - z.2) ^ 2)) ∂spaceTimeMeasure n) :
    HeatBallMeanValueIdentity u r z₀ := by
  have htop := tendsto_integral_heatPotentialProfile_top_of_continuousOn hn hr z₀ u hu
  have hint := tendsto_heatBall_integral_time_cut hn hr z₀ hu
  have heq : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      (∫ y, u (y, z₀.2 - δ) * heatPotentialProfile
        (r ^ n * gaussianKernel n δ (z₀.1 - y)) ∂spatialMeasure n) =
      ∫ z in heatBall n r z₀ ∩ {z | z.2 ≤ z₀.2 - δ},
        u z * (‖z₀.1 - z.1‖ ^ 2 / (4 * (z₀.2 - z.2) ^ 2)) ∂spaceTimeMeasure n := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by positivity : (0 : ℝ) < r ^ 2 / (4 * Real.pi))).filter_mono
        nhdsWithin_le_nhds] with δ hδ hδT
    exact htrunc δ hδ hδT
  have hmass := tendsto_nhds_unique (htop.congr' heq) hint
  have hraw : (∫ z in heatBall n r z₀,
      u z * (‖z₀.1 - z.1‖ ^ 2 / (4 * (z₀.2 - z.2) ^ 2)) ∂spaceTimeMeasure n) =
      (1/4 : ℝ) * ∫ z in heatBall n r z₀,
        u z * (‖z₀.1 - z.1‖ ^ 2 / (z₀.2 - z.2) ^ 2) ∂spaceTimeMeasure n := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [div_mul_eq_div_div]
    ring
  rw [hraw] at hmass
  unfold HeatBallMeanValueIdentity P201Specs.Heat.HeatBallMeanValueIdentity
  have hp : r ^ n ≠ 0 := pow_ne_zero _ hr.ne'
  calc
    u z₀ = (r ^ n)⁻¹ * (r ^ n * u z₀) := by field_simp
    _ = _ := by rw [hmass]; ring



lemma differentiableAt_heatPotential_time (n : ℕ) (b : ℝ) {τ : ℝ} (hτ : 0 < τ)
    (x : Space n) :
    DifferentiableAt ℝ (fun θ => heatPotentialProfile (b * gaussianKernel n θ x)) τ := by
  apply (hasDerivAt_heatPotentialProfile _).differentiableAt.comp τ
  apply DifferentiableAt.const_mul
  unfold gaussianKernel P201Specs.Heat.gaussianKernel
  apply DifferentiableAt.mul
  · apply DifferentiableAt.rpow_const
    · fun_prop
    · exact Or.inl (by positivity)
  · apply DifferentiableAt.exp
    apply DifferentiableAt.div
    · exact differentiableAt_const _
    · fun_prop
    · positivity

lemma hasDerivAt_heatPotential_product {n : ℕ} {r : ℝ} (hr : 0 < r)
    (z₀ : SpaceTime n) {u : SpaceTime n → ℝ}
    (hu : IsClassicalCaloricOn u {z ∈ closure (heatBall n r z₀) | z.2 < z₀.2})
    (y : Space n) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun θ => u (y,z₀.2-θ) *
      heatPotentialProfile (r ^ n * gaussianKernel n θ (z₀.1-y)))
      (u (y,z₀.2-τ) * deriv (fun θ => heatPotentialProfile
        (r ^ n * gaussianKernel n θ (z₀.1-y))) τ -
        deriv (fun t => u (y,t)) (z₀.2-τ) *
          heatPotentialProfile (r ^ n * gaussianKernel n τ (z₀.1-y))) τ := by
  let Q := fun θ => heatPotentialProfile (r ^ n * gaussianKernel n θ (z₀.1-y))
  have hQ : HasDerivAt Q (deriv Q τ) τ :=
    (differentiableAt_heatPotential_time n (r^n) hτ (z₀.1-y)).hasDerivAt
  by_cases hz : (y,z₀.2-τ) ∈ closure (heatBall n r z₀)
  · have hpoint : (y,z₀.2-τ) ∈ {z ∈ closure (heatBall n r z₀) | z.2 < z₀.2} :=
      ⟨hz, by dsimp; linarith⟩
    have hut := (hu.2.2.2.2 _ hpoint).1.hasDerivAt.comp_of_eq τ
      ((hasDerivAt_id τ).const_sub z₀.2) (by rfl)
    convert hut.mul hQ using 1
    · ext θ
      rfl
    · dsimp [Q]
      ring
  · have hQzero : Q =ᶠ[𝓝 τ] (fun _ => (0 : ℝ)) := by
      have hpath : Continuous (fun θ : ℝ => (y,z₀.2-θ)) := by fun_prop
      have hpre := hpath.continuousAt.preimage_mem_nhds
        (isClosed_closure.isOpen_compl.mem_nhds hz)
      filter_upwards [Ioi_mem_nhds hτ, hpre] with θ hθ hθout
      by_contra hne
      apply hθout
      exact subset_closure (heatPotential_slice_support hr hθ z₀ hne)
    have hval : Q τ = 0 := hQzero.self_of_nhds
    have hder : deriv Q τ = 0 :=
      ((hasDerivAt_const τ (0 : ℝ)).congr_of_eventuallyEq hQzero).deriv
    have hprod : (fun θ => u (y,z₀.2-θ) * Q θ) =ᶠ[𝓝 τ] (fun _ => (0 : ℝ)) := by
      filter_upwards [hQzero] with θ hθ
      simp [hθ]
    change HasDerivAt (fun θ => u (y,z₀.2-θ) * Q θ)
      (u (y,z₀.2-τ) * deriv Q τ - deriv (fun t => u (y,t)) (z₀.2-τ) * Q τ) τ
    simpa only [hval, hder, mul_zero, sub_zero] using
      (hasDerivAt_const τ (0 : ℝ)).congr_of_eventuallyEq hprod

lemma heatPotential_slice_mul_integrable {n : ℕ} {r : ℝ} (hr : 0 < r)
    (z₀ : SpaceTime n) {u : SpaceTime n → ℝ}
    (hu : IsClassicalCaloricOn u {z ∈ closure (heatBall n r z₀) | z.2 < z₀.2})
    {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun y => u (y,z₀.2-τ) *
      heatPotentialProfile (r ^ n * gaussianKernel n τ (z₀.1-y))) (spatialMeasure n) := by
  have huc : ContinuousOn (fun y => u (y,z₀.2-τ))
      {y | (y,z₀.2-τ) ∈ closure (heatBall n r z₀)} :=
    hu.1.comp (by fun_prop) (fun y hy => ⟨hy, by dsimp; linarith⟩)
  exact (integrable_compact_mul_of_continuousOn huc
    (heatPotential_slice_contDiff n r τ z₀.1).continuous
    (heatPotential_slice_hasCompactSupport hr hτ z₀)
    (heatPotential_slice_tsupport hr hτ z₀)).congr
      (Filter.Eventually.of_forall (fun y => mul_comm _ _))

lemma integral_heatPotential_product_time {n : ℕ} {r δ T : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hδT : δ ≤ T) (z₀ : SpaceTime n) {u : SpaceTime n → ℝ}
    (hu : IsClassicalCaloricOn u {z ∈ closure (heatBall n r z₀) | z.2 < z₀.2})
    (y : Space n)
    (hi : IntervalIntegrable (fun τ => u (y,z₀.2-τ) * deriv (fun θ => heatPotentialProfile
        (r ^ n * gaussianKernel n θ (z₀.1-y))) τ -
        deriv (fun t => u (y,t)) (z₀.2-τ) *
          heatPotentialProfile (r ^ n * gaussianKernel n τ (z₀.1-y))) volume δ T) :
    (∫ τ in δ..T, u (y,z₀.2-τ) * deriv (fun θ => heatPotentialProfile
        (r ^ n * gaussianKernel n θ (z₀.1-y))) τ -
        deriv (fun t => u (y,t)) (z₀.2-τ) *
          heatPotentialProfile (r ^ n * gaussianKernel n τ (z₀.1-y))) =
      u (y,z₀.2-T) * heatPotentialProfile (r ^ n * gaussianKernel n T (z₀.1-y)) -
      u (y,z₀.2-δ) * heatPotentialProfile (r ^ n * gaussianKernel n δ (z₀.1-y)) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hi
  intro τ hτ
  rw [uIcc_of_le hδT] at hτ
  exact hasDerivAt_heatPotential_product hr z₀ hu y (hδ.trans_le hτ.1)

lemma integral_heatPotential_product_strip {n : ℕ} {r δ T : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hδT : δ ≤ T) (z₀ : SpaceTime n) {u : SpaceTime n → ℝ}
    (hu : IsClassicalCaloricOn u {z ∈ closure (heatBall n r z₀) | z.2 < z₀.2})
    (hi : Integrable (fun z : SpaceTime n => u (z.1,z₀.2-z.2) *
        deriv (fun θ => heatPotentialProfile (r ^ n * gaussianKernel n θ (z₀.1-z.1))) z.2 -
        deriv (fun t => u (z.1,t)) (z₀.2-z.2) *
          heatPotentialProfile (r ^ n * gaussianKernel n z.2 (z₀.1-z.1)))
        ((spatialMeasure n).prod (volume.restrict (Ioc δ T)))) :
    (∫ τ in δ..T, ∫ y, u (y,z₀.2-τ) * deriv (fun θ => heatPotentialProfile
        (r ^ n * gaussianKernel n θ (z₀.1-y))) τ -
        deriv (fun t => u (y,t)) (z₀.2-τ) *
          heatPotentialProfile (r ^ n * gaussianKernel n τ (z₀.1-y)) ∂spatialMeasure n) =
      (∫ y, u (y,z₀.2-T) * heatPotentialProfile
        (r ^ n * gaussianKernel n T (z₀.1-y)) ∂spatialMeasure n) -
      (∫ y, u (y,z₀.2-δ) * heatPotentialProfile
        (r ^ n * gaussianKernel n δ (z₀.1-y)) ∂spatialMeasure n) := by
  rw [intervalIntegral.integral_of_le hδT, ← integral_prod_symm _ hi, integral_prod _ hi]
  have he : (fun y => ∫ τ in Ioc δ T, u (y,z₀.2-τ) * deriv (fun θ => heatPotentialProfile
        (r ^ n * gaussianKernel n θ (z₀.1-y))) τ -
        deriv (fun t => u (y,t)) (z₀.2-τ) *
          heatPotentialProfile (r ^ n * gaussianKernel n τ (z₀.1-y))) =ᵐ[spatialMeasure n]
      fun y => u (y,z₀.2-T) * heatPotentialProfile
        (r ^ n * gaussianKernel n T (z₀.1-y)) -
      u (y,z₀.2-δ) * heatPotentialProfile
        (r ^ n * gaussianKernel n δ (z₀.1-y)) := by
    filter_upwards [hi.prod_right_ae] with y hy
    rw [← intervalIntegral.integral_of_le hδT]
    exact integral_heatPotential_product_time hr hδ hδT z₀ hu y
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hδT).mpr hy)
  rw [integral_congr_ae he,
    integral_sub (heatPotential_slice_mul_integrable hr z₀ hu (hδ.trans_le hδT))
      (heatPotential_slice_mul_integrable hr z₀ hu hδ)]



lemma heatPotential_coordinate_second_deriv_simplified (n : ℕ) {b τ : ℝ}
    (hb : 0 < b) (hτ : 0 < τ) (x : Space n) (i : Fin n)
    (hx : b * gaussianKernel n τ x ≠ 1) :
    fderiv ℝ (fun y => fderiv ℝ (fun v => heatPotentialProfile (b * gaussianKernel n τ v)) y
      (coordinate n i)) x (coordinate n i) =
      if 1 < b * gaussianKernel n τ x then
        b * gaussianKernel n τ x * ((x i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ)) + 1 / (2 * τ)
      else 0 := by
  rw [heatPotential_coordinate_second_deriv n b τ x i hx,
    gaussian_coordinate_deriv, gaussian_coordinate_second_deriv]
  have hG : 0 < gaussianKernel n τ x := by
    unfold gaussianKernel P201Specs.Heat.gaussianKernel
    positivity
  by_cases h : 1 < b * gaussianKernel n τ x
  · simp only [h, ↓reduceIte, heatPotentialProfileSlope]
    field_simp
    ring
  · simp only [h, ↓reduceIte, heatPotentialProfileSlope, zero_mul, zero_add]

lemma heatPotential_centered_coordinate_second_deriv_simplified (n : ℕ) {b τ : ℝ}
    (hb : 0 < b) (hτ : 0 < τ) (x₀ x : Space n) (i : Fin n)
    (hx : b * gaussianKernel n τ (x₀ - x) ≠ 1) :
    fderiv ℝ (fun y => fderiv ℝ
      (fun v => heatPotentialProfile (b * gaussianKernel n τ (x₀ - v))) y
      (coordinate n i)) x (coordinate n i) =
      if 1 < b * gaussianKernel n τ (x₀ - x) then
        b * gaussianKernel n τ (x₀ - x) *
          ((x₀ i - x i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ)) + 1 / (2 * τ)
      else 0 := by
  simp_rw [gaussian_sub_symm n _ x₀]
  have h1 (y : Space n) : fderiv ℝ
      (fun v => heatPotentialProfile (b * gaussianKernel n τ (v - x₀))) y =
      fderiv ℝ (fun v => heatPotentialProfile (b * gaussianKernel n τ v)) (y - x₀) :=
    fderiv_comp_sub (𝕜 := ℝ) (f := fun v => heatPotentialProfile (b * gaussianKernel n τ v))
      (x := y) x₀
  simp_rw [h1]
  have h2 : fderiv ℝ
      (fun y => fderiv ℝ (fun v => heatPotentialProfile (b * gaussianKernel n τ v))
        (y - x₀) (coordinate n i)) x =
      fderiv ℝ (fun y => fderiv ℝ (fun v => heatPotentialProfile (b * gaussianKernel n τ v))
        y (coordinate n i)) (x - x₀) :=
    fderiv_comp_sub (𝕜 := ℝ)
      (f := fun y => fderiv ℝ (fun v => heatPotentialProfile (b * gaussianKernel n τ v))
        y (coordinate n i)) (x := x) x₀
  rw [h2]
  have h := heatPotential_coordinate_second_deriv_simplified n hb hτ (x - x₀) i
    (by rwa [gaussian_sub_symm n τ x₀ x] at hx)
  simpa only [PiLp.sub_apply, sub_sq_comm] using h



lemma hasDerivAt_coordinateInsertion {m : ℕ} (i : Fin (m + 1)) (y : Fin m → ℝ) (t : ℝ) :
    HasDerivAt (fun t => WithLp.toLp 2 (i.insertNth t y)) (coordinate (m + 1) i) t := by
  have hp : HasDerivAt (fun t : ℝ => (i.insertNth t y : Fin (m + 1) → ℝ)) (Pi.single i (1 : ℝ)) t := by
    have he : (fun t : ℝ => (i.insertNth t y : Fin (m + 1) → ℝ)) =
        Function.update (i.insertNth 0 y : Fin (m + 1) → ℝ) i := by
      funext a
      exact (Fin.update_insertNth (α := fun _ : Fin (m + 1) => ℝ) i 0 a y).symm
    rw [he]
    exact hasDerivAt_update (i.insertNth 0 y) i t
  have hd := (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) (E := fun _ : Fin (m + 1) => ℝ) 2 (i.insertNth t y)).comp_hasDerivAt t hp
  have heq : coordinate (m + 1) i = WithLp.toLp 2 (Pi.single i (1 : ℝ)) := by
    ext j
    simp [coordinate, P201Specs.coordinate, P102.U4.coordinateVector,
      EuclideanSpace.basisFun_apply, Pi.single_apply]
  rw [heq]
  change HasDerivAt (fun t : ℝ => WithLp.toLp 2 (i.insertNth t y : Fin (m + 1) → ℝ))
    (WithLp.toLp 2 (Pi.single i (1 : ℝ))) t at hd
  exact hd

lemma isClosedEmbedding_coordinateInsertion {m : ℕ} (i : Fin (m + 1)) (y : Fin m → ℝ) :
    Topology.IsClosedEmbedding (fun t : ℝ => WithLp.toLp 2 (i.insertNth t y : Fin (m + 1) → ℝ)) := by
  have hi : Isometry (fun t : ℝ => (i.insertNth t y : Fin (m + 1) → ℝ)) := by
    apply Isometry.of_dist_eq
    intro a b
    simp
  exact (PiLp.homeomorph 2 (fun _ : Fin (m + 1) => ℝ)).symm.isClosedEmbedding.comp
    hi.isClosedEmbedding

lemma hasDerivAt_comp_coordinateInsertion {m : ℕ} (i : Fin (m + 1)) (y : Fin m → ℝ) (t : ℝ)
    {f : Space (m + 1) → ℝ}
    (hf : DifferentiableAt ℝ f (WithLp.toLp 2 (i.insertNth t y))) :
    HasDerivAt (fun t => f (WithLp.toLp 2 (i.insertNth t y)))
      (fderiv ℝ f (WithLp.toLp 2 (i.insertNth t y)) (coordinate (m + 1) i)) t :=
  hf.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_coordinateInsertion i y t)



lemma heatBall_time_cut_integral_backward {n : ℕ} (hn : 1 ≤ n) {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (z₀ : SpaceTime n) (u : SpaceTime n → ℝ)
    (hu : ContinuousOn u (closure (heatBall n r z₀))) :
    (∫ z in heatBall n r z₀ ∩ {z | z.2 ≤ z₀.2 - δ},
      u z * (‖z₀.1 - z.1‖ ^ 2 / (4 * (z₀.2 - z.2) ^ 2)) ∂spaceTimeMeasure n) =
    ∫ τ in Ioc δ (r ^ 2 / (4 * Real.pi)), ∫ y,
      u (y, z₀.2 - τ) *
        (if 1 < r ^ n * gaussianKernel n τ (z₀.1 - y) then
          ‖z₀.1 - y‖ ^ 2 / (4 * τ ^ 2) else 0) ∂spatialMeasure n := by
  let T := r ^ 2 / (4 * Real.pi)
  let S : Set (SpaceTime n) := heatBall n r z₀ ∩ {z | z.2 ≤ z₀.2 - δ}
  let f : SpaceTime n → ℝ := fun z => u z *
    (‖z₀.1 - z.1‖ ^ 2 / (4 * (z₀.2 - z.2) ^ 2))
  let H : SpaceTime n → ℝ := fun z => u (z.1, z₀.2 - z.2) *
    (if 1 < r ^ n * gaussianKernel n z.2 (z₀.1 - z.1) then
      ‖z₀.1 - z.1‖ ^ 2 / (4 * z.2 ^ 2) else 0)
  let R : SpaceTime n → SpaceTime n := fun z => (z.1, z₀.2 - z.2)
  have hmS : MeasurableSet S :=
    (heatBall_measurableSet n r z₀).inter (measurableSet_le measurable_snd measurable_const)
  have hmp : MeasurePreserving R (spaceTimeMeasure n) (spaceTimeMeasure n) :=
    (MeasurePreserving.id (spatialMeasure n)).prod (volume.measurePreserving_sub_left z₀.2)
  let e : SpaceTime n ≃ᵐ SpaceTime n :=
    (MeasurableEquiv.refl (Space n)).prodCongr (MeasurableEquiv.subLeft z₀.2)
  have hR (z : SpaceTime n) : R z ∈ S ↔
      z.2 ∈ Icc δ T ∧ 1 < r ^ n * gaussianKernel n z.2 (z₀.1 - z.1) := by
    constructor
    · intro hz
      have ht : 0 < z.2 := by have := hz.1.1; dsimp [R] at this; linarith
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have := hz.2; dsimp [R] at this; linarith
      · have hb := heatBall_backwardTime_bound hn hr hz.1
        simpa only [R, Prod.snd, sub_sub_cancel] using hb.le
      · have hl := hz.1.2
        simpa only [R, Prod.fst, Prod.snd, sub_sub_cancel, heatBall_threshold_iff hr] using hl
    · intro hz
      have ht : 0 < z.2 := hδ.trans_le hz.1.1
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · dsimp [R]; linarith
      · change r ^ (-(n : ℤ)) < gaussianKernel n (z₀.2 - (z₀.2-z.2)) (z₀.1-z.1)
        rw [sub_sub_cancel, heatBall_threshold_iff hr]
        exact hz.2
      · change z₀.2-z.2 ≤ z₀.2-δ
        linarith [hz.1.1]
  have heq : (fun z => S.indicator f (R z)) = (univ ×ˢ Icc δ T).indicator H := by
    funext z
    by_cases ht : z.2 ∈ Icc δ T
    · by_cases hl : 1 < r ^ n * gaussianKernel n z.2 (z₀.1-z.1)
      · rw [indicator_of_mem ((hR z).mpr ⟨ht,hl⟩),
          indicator_of_mem (show z ∈ univ ×ˢ Icc δ T from ⟨mem_univ _,ht⟩)]
        simp [f, H, R, hl]
      · rw [indicator_of_notMem (fun h => hl ((hR z).mp h).2),
          indicator_of_mem (show z ∈ univ ×ˢ Icc δ T from ⟨mem_univ _,ht⟩)]
        simp [H, hl]
    · rw [indicator_of_notMem (fun h => ht ((hR z).mp h).1),
        indicator_of_notMem (fun h => ht h.2)]
  have hfi : Integrable (S.indicator f) (spaceTimeMeasure n) := by
    apply (integrable_indicator_iff hmS).mpr
    have hi := heatBall_bounded_integrable hr z₀ u
      ((hu.mono subset_closure).aestronglyMeasurable (heatBall_measurableSet n r z₀))
      (heatBall_bounded_of_continuousOn_closure hn hr z₀ hu)
      (heatBallWeightIntegrable n hn r hr z₀)
    have he : (fun z => (1/4 : ℝ) *
        (u z * (‖z₀.1-z.1‖^2 / (z₀.2-z.2)^2))) = f := by
      funext z
      dsimp [f]
      simp only [div_mul_eq_div_div]
      ring
    rw [← he]
    have hbase : IntegrableOn (fun z => (1/4 : ℝ) *
        (u z * (‖z₀.1-z.1‖^2 / (z₀.2-z.2)^2))) (heatBall n r z₀)
          (spaceTimeMeasure n) := hi.const_mul (1/4 : ℝ)
    exact hbase.mono_set inter_subset_left
  have hHi : Integrable ((univ ×ˢ Icc δ T).indicator H) (spaceTimeMeasure n) := by
    rw [← heq]
    exact hmp.integrable_comp_of_integrable hfi
  have hHr : Integrable H ((spatialMeasure n).prod (volume.restrict (Icc δ T))) := by
    have hi := (integrable_indicator_iff
      (MeasurableSet.univ.prod measurableSet_Icc)).mp hHi
    simpa only [IntegrableOn, spaceTimeMeasure, ← Measure.prod_restrict,
      Measure.restrict_univ] using hi
  calc
    (∫ z in S, f z ∂spaceTimeMeasure n) = ∫ z, S.indicator f (R z) ∂spaceTimeMeasure n := by
      rw [hmp.integral_comp e.measurableEmbedding, integral_indicator hmS]
    _ = ∫ z in univ ×ˢ Icc δ T, H z ∂spaceTimeMeasure n := by
      rw [heq, integral_indicator (MeasurableSet.univ.prod measurableSet_Icc)]
    _ = ∫ τ in Icc δ T, ∫ y, H (y,τ) ∂spatialMeasure n := by
      rw [← integral_prod_symm _ hHr]
      change (∫ z, H z ∂(((spatialMeasure n).prod volume).restrict (univ ×ˢ Icc δ T))) = _
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    _ = _ := by rw [integral_Icc_eq_integral_Ioc]



lemma heatBall_past_slice_isCompact {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r)
    (z₀ : SpaceTime n) (τ : ℝ) :
    IsCompact {x : Space n | (x,z₀.2-τ) ∈ closure (heatBall n r z₀)} := by
  apply ((heatBall_isCompact_closure hn hr z₀).image continuous_fst).of_isClosed_subset
  · exact isClosed_closure.preimage (by fun_prop)
  · intro x hx
    exact ⟨(x,z₀.2-τ), hx, rfl⟩

lemma continuousOn_heatBall_past_slice {n : ℕ} {r τ : ℝ}
    (hτ : 0 < τ) (z₀ : SpaceTime n) {f : SpaceTime n → ℝ}
    (hf : ContinuousOn f {z ∈ closure (heatBall n r z₀) | z.2 < z₀.2}) :
    ContinuousOn (fun x : Space n => f (x,z₀.2-τ))
      {x : Space n | (x,z₀.2-τ) ∈ closure (heatBall n r z₀)} := by
  exact hf.comp (by fun_prop) (fun x hx => ⟨hx, by dsimp; linarith⟩)

lemma integrable_heatBall_slice_mul_indicator {n : ℕ} (hn : 1 ≤ n) {r τ : ℝ}
    (hr : 0 < r) (hτ : 0 < τ) (z₀ : SpaceTime n)
    {f : SpaceTime n → ℝ} {g : Space n → ℝ}
    (hf : ContinuousOn f {z ∈ closure (heatBall n r z₀) | z.2 < z₀.2})
    (hg : Continuous g) :
    Integrable (fun x : Space n => f (x,z₀.2-τ) *
      {y : Space n | (y,z₀.2-τ) ∈ heatBall n r z₀}.indicator g x) (spatialMeasure n) := by
  let S : Set (Space n) := {x | (x,z₀.2-τ) ∈ heatBall n r z₀}
  let K : Set (Space n) := {x | (x,z₀.2-τ) ∈ closure (heatBall n r z₀)}
  have hmS : MeasurableSet S :=
    (heatBall_measurableSet n r z₀).preimage (by fun_prop)
  have hi : IntegrableOn (fun x : Space n => f (x,z₀.2-τ) * g x) K (spatialMeasure n) :=
    ((continuousOn_heatBall_past_slice hτ z₀ hf).mul hg.continuousOn).integrableOn_compact
      (heatBall_past_slice_isCompact hn hr z₀ τ)
  have hiS := hi.mono_set (show S ⊆ K from fun x hx => subset_closure hx)
  have hgi := (integrable_indicator_iff hmS).mpr hiS
  convert hgi using 1
  funext x
  by_cases hx : x ∈ S <;> simp [S, hx, indicator_of_mem, indicator_of_notMem]

lemma integrable_heatPotential_mul_source {n : ℕ} {r τ : ℝ}
    (hr : 0 < r) (hτ : 0 < τ) (z₀ : SpaceTime n)
    {f : SpaceTime n → ℝ}
    (hf : ContinuousOn f {z ∈ closure (heatBall n r z₀) | z.2 < z₀.2}) :
    Integrable (fun x : Space n => heatPotentialProfile
      (r ^ n * gaussianKernel n τ (z₀.1-x)) * f (x,z₀.2-τ)) (spatialMeasure n) := by
  apply integrable_compact_mul_of_continuousOn
    (continuousOn_heatBall_past_slice hτ z₀ hf)
    (heatPotential_slice_contDiff n r τ z₀.1).continuous
    (heatPotential_slice_hasCompactSupport hr hτ z₀)
    (heatPotential_slice_tsupport hr hτ z₀)

lemma integrable_heatPotential_mul_caloric_second {n : ℕ} {r τ : ℝ}
    (hr : 0 < r) (hτ : 0 < τ) (z₀ : SpaceTime n)
    {u : SpaceTime n → ℝ}
    (hu : IsClassicalCaloricOn u {z ∈ closure (heatBall n r z₀) | z.2 < z₀.2})
    (v : Space n) :
    Integrable (fun x : Space n => heatPotentialProfile
      (r ^ n * gaussianKernel n τ (z₀.1-x)) *
      fderiv ℝ (fderiv ℝ (fun y => u (y,z₀.2-τ))) x v v) (spatialMeasure n) := by
  exact integrable_heatPotential_mul_source hr hτ z₀
    ((hu.2.2.2.1.clm_apply continuousOn_const).clm_apply continuousOn_const)


lemma integrable_source_mul_heatPotential_second {n : ℕ} (hn : 1 ≤ n) {r τ : ℝ}
    (hr : 0 < r) (hτ : 0 < τ) (z₀ : SpaceTime n)
    {f : SpaceTime n → ℝ}
    (hf : ContinuousOn f {z ∈ closure (heatBall n r z₀) | z.2 < z₀.2})
    (i : Fin n) :
    Integrable (fun x : Space n => f (x,z₀.2-τ) *
      fderiv ℝ (fun y => fderiv ℝ
        (fun v => heatPotentialProfile (r ^ n * gaussianKernel n τ (z₀.1 - v))) y
        (coordinate n i)) x (coordinate n i)) (spatialMeasure n) := by
  let S : Set (Space n) := {x | (x,z₀.2-τ) ∈ heatBall n r z₀}
  let H : Space n → ℝ := fun x => r ^ n * gaussianKernel n τ (z₀.1-x) *
    ((z₀.1 i - x i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ)) + 1 / (2 * τ)
  have hH : Continuous H := by
    unfold H gaussianKernel P201Specs.Heat.gaussianKernel
    fun_prop
  have hi := integrable_heatBall_slice_mul_indicator hn hr hτ z₀ hf hH
  apply hi.congr
  filter_upwards [ae_gaussian_level_ne_one hn hτ (pow_ne_zero n hr.ne') z₀.1] with x hx
  rw [heatPotential_centered_coordinate_second_deriv_simplified n (pow_pos hr _) hτ z₀.1 x i hx]
  have hm : x ∈ S ↔ 1 < r ^ n * gaussianKernel n τ (z₀.1-x) := by
    constructor
    · intro hm
      have hl := hm.2
      change r ^ (-(n : ℤ)) < gaussianKernel n (z₀.2-(z₀.2-τ)) (z₀.1-x) at hl
      rw [sub_sub_cancel, heatBall_threshold_iff hr] at hl
      exact hl
    · intro hl
      refine ⟨by dsimp; linarith, ?_⟩
      change r ^ (-(n : ℤ)) < gaussianKernel n (z₀.2-(z₀.2-τ)) (z₀.1-x)
      rw [sub_sub_cancel, heatBall_threshold_iff hr]
      exact hl
  by_cases hl : 1 < r ^ n * gaussianKernel n τ (z₀.1-x)
  · rw [if_pos hl, indicator_of_mem (hm.mpr hl)]
  · rw [if_neg hl, indicator_of_notMem (fun h => hl (hm.mp h))]



lemma integrable_on_time_strip_of_continuous_spatial_support {n : ℕ} {δ T : ℝ}
    {K : Set (Space n)} (hK : IsCompact K) {f : SpaceTime n → ℝ}
    (hc : ContinuousOn f (univ ×ˢ Icc δ T))
    (hz : ∀ z : SpaceTime n, z.2 ∈ Ioc δ T → z.1 ∉ K → f z = 0) :
    Integrable f ((spatialMeasure n).prod (volume.restrict (Ioc δ T))) := by
  have hi : IntegrableOn f (K ×ˢ Icc δ T)
      ((spatialMeasure n).prod (volume.restrict (Ioc δ T))) :=
    (hc.mono (prod_mono (subset_univ _) Subset.rfl)).integrableOn_compact (hK.prod isCompact_Icc)
  apply hi.integrable_of_ae_notMem_eq_zero
  have hat : ∀ᵐ z : SpaceTime n ∂(spatialMeasure n).prod (volume.restrict (Ioc δ T)),
      z.2 ∈ Ioc δ T :=
    (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Ioc)).mpr
      (ae_of_all _ (fun y => ae_restrict_mem measurableSet_Ioc))
  filter_upwards [hat] with z hzt hzout
  apply hz z hzt
  intro hzK
  exact hzout ⟨hzK, ⟨hzt.1.le,hzt.2⟩⟩

lemma integrable_heatBall_strip_mul {n : ℕ} (hn : 1 ≤ n) {r δ T : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (z₀ : SpaceTime n) {f g : SpaceTime n → ℝ}
    (hf : ContinuousOn f {z ∈ closure (heatBall n r z₀) | z.2 < z₀.2})
    (hg : ContinuousOn g (univ ×ˢ Icc δ T))
    (hs : ∀ z : SpaceTime n, z.2 ∈ Ioc δ T → g z ≠ 0 →
      (z.1,z₀.2-z.2) ∈ heatBall n r z₀) :
    Integrable (fun z : SpaceTime n => f (z.1,z₀.2-z.2) * g z)
      ((spatialMeasure n).prod (volume.restrict (Ioc δ T))) := by
  let K : Set (SpaceTime n) := closure (heatBall n r z₀) ∩ {z | z.2 ≤ z₀.2-δ}
  have hK : IsCompact K := (heatBall_isCompact_closure hn hr z₀).inter_right
    (isClosed_le continuous_snd continuous_const)
  have hfK : ContinuousOn f K := hf.mono (fun z hz => ⟨hz.1, by
    have ht := hz.2
    change z.2 ≤ z₀.2-δ at ht
    linarith⟩)
  obtain ⟨v, hv, _, hvf⟩ := exists_bounded_continuous_extension_of_isCompact hK hfK
  have hi : Integrable (fun z : SpaceTime n => v (z.1,z₀.2-z.2) * g z)
      ((spatialMeasure n).prod (volume.restrict (Ioc δ T))) := by
    apply integrable_on_time_strip_of_continuous_spatial_support
      (isCompact_closedBall z₀.1 (((n : ℝ)+1)*r))
    · exact (hv.comp (by fun_prop)).continuousOn.mul hg
    · intro z hzt hzout
      have hgz : g z = 0 := by
        by_contra hne
        have hE := hs z hzt hne
        apply hzout
        rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
        exact (heatBall_space_linear_bound hr hE).le
      simp [hgz]
  apply hi.congr
  have hat : ∀ᵐ z : SpaceTime n ∂(spatialMeasure n).prod (volume.restrict (Ioc δ T)),
      z.2 ∈ Ioc δ T :=
    (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Ioc)).mpr
      (ae_of_all _ (fun y => ae_restrict_mem measurableSet_Ioc))
  filter_upwards [hat] with z hzt
  by_cases hgz : g z = 0
  · simp [hgz]
  · have hzK : (z.1,z₀.2-z.2) ∈ K := ⟨subset_closure (hs z hzt hgz), by
      change z₀.2-z.2 ≤ z₀.2-δ
      linarith [hzt.1]⟩
    rw [hvf hzK]

lemma continuousOn_gaussian_backward_strip {n : ℕ} {δ T : ℝ} (hδ : 0 < δ)
    (x₀ : Space n) :
    ContinuousOn (fun z : SpaceTime n => gaussianKernel n z.2 (x₀-z.1))
      (univ ×ˢ Icc δ T) := by
  intro z hz
  have ht : 0 < z.2 := hδ.trans_le hz.2.1
  apply ContinuousAt.continuousWithinAt
  unfold gaussianKernel P201Specs.Heat.gaussianKernel
  apply ContinuousAt.mul
  · apply ContinuousAt.rpow_const
    · fun_prop
    · left
      positivity
  · apply Real.continuous_exp.continuousAt.comp
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · positivity

lemma continuousOn_heatPotential_time_deriv_strip {n : ℕ} {r δ T : ℝ}
    (hδ : 0 < δ) (z₀ : SpaceTime n) :
    ContinuousOn (fun z : SpaceTime n => deriv (fun θ => heatPotentialProfile
      (r ^ n * gaussianKernel n θ (z₀.1-z.1))) z.2) (univ ×ˢ Icc δ T) := by
  have hG := continuousOn_gaussian_backward_strip (n := n) (T := T) hδ z₀.1
  have hc : ContinuousOn (fun z : SpaceTime n =>
      heatPotentialProfileSlope (r ^ n * gaussianKernel n z.2 (z₀.1-z.1)) * r ^ n *
      (gaussianKernel n z.2 (z₀.1-z.1) *
        (-(n : ℝ) / (2*z.2) + ‖z₀.1-z.1‖ ^ 2 / (4*z.2 ^ 2))))
      (univ ×ˢ Icc δ T) := by
    intro z hz
    have ht : 0 < z.2 := hδ.trans_le hz.2.1
    apply ContinuousAt.continuousWithinAt
    have hGz := (hG z hz)
    have hGa : ContinuousAt (fun z : SpaceTime n => gaussianKernel n z.2 (z₀.1-z.1)) z := by
      unfold gaussianKernel P201Specs.Heat.gaussianKernel
      apply ContinuousAt.mul
      · apply ContinuousAt.rpow_const
        · fun_prop
        · left
          positivity
      · apply Real.continuous_exp.continuousAt.comp
        apply ContinuousAt.div
        · fun_prop
        · fun_prop
        · positivity
    have hSl := continuous_heatPotentialProfileSlope.continuousAt.comp (hGa.const_mul (r^n))
    fun_prop (disch := positivity)
  exact hc.congr (fun z hz => by
    rw [heatPotential_time_deriv n (r^n) (hδ.trans_le hz.2.1),
      gaussian_time_deriv n (hδ.trans_le hz.2.1)])

lemma heatPotential_time_deriv_slice_support {n : ℕ} {r τ : ℝ}
    (hr : 0 < r) (hτ : 0 < τ) (z₀ : SpaceTime n) :
    Function.support (fun y : Space n => deriv (fun θ => heatPotentialProfile
      (r ^ n * gaussianKernel n θ (z₀.1-y))) τ) ⊆
      {y | (y,z₀.2-τ) ∈ heatBall n r z₀} := by
  intro y hy
  have hs : heatPotentialProfileSlope (r ^ n * gaussianKernel n τ (z₀.1-y)) ≠ 0 := by
    intro hz
    apply hy
    change deriv (fun θ => heatPotentialProfile (r ^ n * gaussianKernel n θ (z₀.1-y))) τ = 0
    rw [heatPotential_time_deriv n (r^n) hτ, hz, zero_mul, zero_mul]
  exact heatPotentialSlope_slice_support hr hτ z₀ hs

lemma heatPotential_product_derivative_strip_integrable {n : ℕ} (hn : 1 ≤ n)
    {r δ T : ℝ} (hr : 0 < r) (hδ : 0 < δ) (z₀ : SpaceTime n)
    {u : SpaceTime n → ℝ}
    (hu : IsClassicalCaloricOn u {z ∈ closure (heatBall n r z₀) | z.2 < z₀.2}) :
    Integrable (fun z : SpaceTime n => u (z.1,z₀.2-z.2) *
        deriv (fun θ => heatPotentialProfile (r ^ n * gaussianKernel n θ (z₀.1-z.1))) z.2 -
        deriv (fun t => u (z.1,t)) (z₀.2-z.2) *
          heatPotentialProfile (r ^ n * gaussianKernel n z.2 (z₀.1-z.1)))
        ((spatialMeasure n).prod (volume.restrict (Ioc δ T))) := by
  have h₁ := integrable_heatBall_strip_mul hn hr hδ z₀ hu.1
    (continuousOn_heatPotential_time_deriv_strip (r := r) (T := T) hδ z₀)
    (fun z hz hne => heatPotential_time_deriv_slice_support hr (hδ.trans hz.1) z₀ hne)
  have h₂ := integrable_heatBall_strip_mul hn hr hδ z₀ hu.2.1
    (continuous_heatPotentialProfile.comp_continuousOn
      ((continuousOn_gaussian_backward_strip (n := n) (T := T) hδ z₀.1).const_mul (r^n)))
    (fun z hz hne => heatPotential_slice_support hr (hδ.trans hz.1) z₀ hne)
  exact h₁.sub h₂

lemma integral_heatPotential_product_strip_of_caloric {n : ℕ} (hn : 1 ≤ n)
    {r δ T : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hδT : δ ≤ T) (z₀ : SpaceTime n)
    {u : SpaceTime n → ℝ}
    (hu : IsClassicalCaloricOn u {z ∈ closure (heatBall n r z₀) | z.2 < z₀.2}) :
    (∫ τ in δ..T, ∫ y, u (y,z₀.2-τ) * deriv (fun θ => heatPotentialProfile
        (r ^ n * gaussianKernel n θ (z₀.1-y))) τ -
        deriv (fun t => u (y,t)) (z₀.2-τ) *
          heatPotentialProfile (r ^ n * gaussianKernel n τ (z₀.1-y)) ∂spatialMeasure n) =
      (∫ y, u (y,z₀.2-T) * heatPotentialProfile
        (r ^ n * gaussianKernel n T (z₀.1-y)) ∂spatialMeasure n) -
      (∫ y, u (y,z₀.2-δ) * heatPotentialProfile
        (r ^ n * gaussianKernel n δ (z₀.1-y)) ∂spatialMeasure n) :=
  integral_heatPotential_product_strip hr hδ hδT z₀ hu
    (heatPotential_product_derivative_strip_integrable hn hr hδ z₀ hu)



lemma heatPotential_slice_time_deriv_support {n : ℕ} {r τ : ℝ}
    (hr : 0 < r) (hτ : 0 < τ) (z₀ : SpaceTime n) :
    Function.support (fun x : Space n => deriv
      (fun θ => heatPotentialProfile (r ^ n * gaussianKernel n θ (z₀.1-x))) τ) ⊆
      {x | (x,z₀.2-τ) ∈ heatBall n r z₀} := by
  intro x hx
  have hs : heatPotentialProfileSlope (r ^ n * gaussianKernel n τ (z₀.1-x)) ≠ 0 := by
    intro hs
    apply hx
    dsimp only
    rw [heatPotential_time_deriv n (r ^ n) hτ, hs]
    simp
  exact heatPotentialSlope_slice_support hr hτ z₀ hs

lemma heatPotential_slice_time_deriv_continuous {n : ℕ} {r τ : ℝ}
    (hτ : 0 < τ) (z₀ : SpaceTime n) :
    Continuous (fun x : Space n => deriv
      (fun θ => heatPotentialProfile (r ^ n * gaussianKernel n θ (z₀.1-x))) τ) := by
  have he : (fun x : Space n => deriv
      (fun θ => heatPotentialProfile (r ^ n * gaussianKernel n θ (z₀.1-x))) τ) =
      fun x : Space n => heatPotentialProfileSlope (r ^ n * gaussianKernel n τ (z₀.1-x)) *
        r ^ n * (gaussianKernel n τ (z₀.1-x) *
          (-(n : ℝ) / (2 * τ) + ‖z₀.1-x‖ ^ 2 / (4 * τ ^ 2))) := by
    funext x
    rw [heatPotential_time_deriv n (r ^ n) hτ, gaussian_time_deriv n hτ]
  rw [he]
  have hg : Continuous (fun x : Space n => gaussianKernel n τ (z₀.1-x)) := by
    unfold gaussianKernel P201Specs.Heat.gaussianKernel
    fun_prop
  exact (((continuous_heatPotentialProfileSlope.comp (continuous_const.mul hg)).mul
    continuous_const).mul (hg.mul (by fun_prop)))

lemma integrable_source_mul_heatPotential_time_deriv {n : ℕ} {r τ : ℝ}
    (hr : 0 < r) (hτ : 0 < τ) (z₀ : SpaceTime n)
    {f : SpaceTime n → ℝ}
    (hf : ContinuousOn f {z ∈ closure (heatBall n r z₀) | z.2 < z₀.2}) :
    Integrable (fun x : Space n => f (x,z₀.2-τ) * deriv
      (fun θ => heatPotentialProfile (r ^ n * gaussianKernel n θ (z₀.1-x))) τ)
      (spatialMeasure n) := by
  have hs := heatPotential_slice_time_deriv_support hr hτ z₀
  have hi := integrable_compact_mul_of_continuousOn
    (μ := spatialMeasure n) (continuousOn_heatBall_past_slice hτ z₀ hf)
    (heatPotential_slice_time_deriv_continuous hτ z₀)
    (heatBall_slice_hasCompactSupport_of_support_subset hr z₀ hs)
    (heatBall_slice_tsupport_of_support_subset z₀ hs)
  simpa only [mul_comm] using hi

lemma integral_heatPotential_mul_caloric_time_eq_sum {n : ℕ} {r τ : ℝ}
    (hr : 0 < r) (hτ : 0 < τ) (z₀ : SpaceTime n)
    {u : SpaceTime n → ℝ}
    (hu : IsClassicalCaloricOn u {z ∈ closure (heatBall n r z₀) | z.2 < z₀.2}) :
    (∫ x : Space n, heatPotentialProfile (r ^ n * gaussianKernel n τ (z₀.1-x)) *
      deriv (fun t => u (x,t)) (z₀.2-τ) ∂spatialMeasure n) =
      ∑ i : Fin n, ∫ x : Space n, heatPotentialProfile
        (r ^ n * gaussianKernel n τ (z₀.1-x)) *
        fderiv ℝ (fderiv ℝ (fun y => u (y,z₀.2-τ))) x
          (coordinate n i) (coordinate n i) ∂spatialMeasure n := by
  rw [← integral_finsetSum _ (fun i _ =>
    integrable_heatPotential_mul_caloric_second hr hτ z₀ hu (coordinate n i))]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hq : heatPotentialProfile (r ^ n * gaussianKernel n τ (z₀.1-x)) = 0
  · simp [hq]
  · have hx := heatPotential_slice_support hr hτ z₀ hq
    have hxS : (x,z₀.2-τ) ∈ {z ∈ closure (heatBall n r z₀) | z.2 < z₀.2} :=
      ⟨subset_closure hx, by dsimp; linarith⟩
    have hPDE := (hu.2.2.2.2 (x,z₀.2-τ) hxS).2.2
    rw [laplacian_eq_sum_fderiv (hu.2.2.2.2 (x,z₀.2-τ) hxS).2.1] at hPDE
    dsimp only at hPDE
    rw [hPDE, Finset.mul_sum]



lemma integral_mul_coordinate_second_fderiv_eq_swap {m : ℕ}
    (i : Fin (m + 1)) {u q : Space (m + 1) → ℝ}
    (hq : ContDiff ℝ 1 q) (hqk : HasCompactSupport q)
    (s : (Fin m → ℝ) → Set ℝ) (hs : ∀ y, (s y).Countable)
    (hq2 : ∀ y t, t ∉ s y → ContDiffAt ℝ 2 q (WithLp.toLp 2 (i.insertNth t y)))
    (hu : ∀ x ∈ tsupport q, ContDiffAt ℝ 2 u x)
    (hleft : Integrable (fun x => u x * fderiv ℝ
      (fun y => fderiv ℝ q y (coordinate (m + 1) i)) x (coordinate (m + 1) i)))
    (hright : Integrable (fun x => fderiv ℝ
      (fun y => fderiv ℝ u y (coordinate (m + 1) i)) x (coordinate (m + 1) i) * q x)) :
    (∫ x, u x * fderiv ℝ (fun y => fderiv ℝ q y (coordinate (m + 1) i)) x
      (coordinate (m + 1) i)) =
      ∫ x, fderiv ℝ (fun y => fderiv ℝ u y (coordinate (m + 1) i)) x
        (coordinate (m + 1) i) * q x := by
  have hcont (y : Fin m → ℝ) : Continuous (fun t : ℝ => WithLp.toLp 2
      (i.insertNth t y : Fin (m + 1) → ℝ)) :=
    (isClosedEmbedding_coordinateInsertion i y).continuous
  have hloc (y : Fin m → ℝ) (t : ℝ)
      (ht : t ∈ tsupport (fun t => q (WithLp.toLp 2 (i.insertNth t y))) ∪
        tsupport (fun t => fderiv ℝ q (WithLp.toLp 2 (i.insertNth t y)) (coordinate (m + 1) i))) :
      WithLp.toLp 2 (i.insertNth t y) ∈ tsupport q := by
    rcases ht with ht | ht
    · exact tsupport_comp_subset_preimage q (hcont y) ht
    · exact tsupport_fderiv_apply_subset ℝ (coordinate (m + 1) i)
        (tsupport_comp_subset_preimage
          (fun x => fderiv ℝ q x (coordinate (m + 1) i)) (hcont y) ht)
  apply integral_euclidean_mul_secondDeriv_eq_secondDeriv_mul i s hs
      (f' := fun x => fderiv ℝ u x (coordinate (m + 1) i))
      (g' := fun x => fderiv ℝ q x (coordinate (m + 1) i))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ hleft hright
  · intro y t
    exact hasDerivAt_comp_coordinateInsertion i y t (hq.differentiable (by norm_num) _)
  · intro y
    exact ((hq.continuous_fderiv (by norm_num)).clm_apply continuous_const).comp (hcont y)
  · intro y t ht
    apply hasDerivAt_comp_coordinateInsertion i y t
      (f := fun x => fderiv ℝ q x (coordinate (m + 1) i))
    have hd : DifferentiableAt ℝ (fderiv ℝ q) (WithLp.toLp 2 (i.insertNth t y)) :=
      ((hq2 y t ht).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    exact hd.clm_apply (differentiableAt_const _)
  · intro y
    exact hqk.comp_isClosedEmbedding (isClosedEmbedding_coordinateInsertion i y)
  · intro y
    exact (hqk.fderiv_apply ℝ (coordinate (m + 1) i)).comp_isClosedEmbedding
      (isClosedEmbedding_coordinateInsertion i y)
  · intro y t ht
    exact hasDerivAt_comp_coordinateInsertion i y t ((hu _ (hloc y t ht)).differentiableAt (by norm_num))
  · intro y t ht
    apply hasDerivAt_comp_coordinateInsertion i y t
      (f := fun x => fderiv ℝ u x (coordinate (m + 1) i))
    have hd : DifferentiableAt ℝ (fderiv ℝ u) (WithLp.toLp 2 (i.insertNth t y)) :=
      ((hu _ (hloc y t ht)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    exact hd.clm_apply (differentiableAt_const _)

lemma coordinate_second_fderiv_eq_of_contDiffAt {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ 2 u x) (v : Space n) :
    fderiv ℝ (fun y => fderiv ℝ u y v) x v = fderiv ℝ (fderiv ℝ u) x v v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp

set_option maxHeartbeats 2000000 in
lemma heatPotential_spatial_green_coordinate {n : ℕ} (hn : 1 ≤ n) {r τ : ℝ}
    (hr : 0 < r) (hτ : 0 < τ) (z₀ : SpaceTime n) {u : SpaceTime n → ℝ}
    (hu : IsClassicalCaloricOn u {z ∈ closure (heatBall n r z₀) | z.2 < z₀.2})
    (i : Fin n) :
    (∫ x : Space n, u (x,z₀.2-τ) * fderiv ℝ
      (fun y => fderiv ℝ (fun v => heatPotentialProfile (r ^ n * gaussianKernel n τ (z₀.1-v))) y
        (coordinate n i)) x (coordinate n i)) =
    ∫ x : Space n, heatPotentialProfile (r ^ n * gaussianKernel n τ (z₀.1-x)) *
      fderiv ℝ (fderiv ℝ (fun y => u (y,z₀.2-τ))) x (coordinate n i) (coordinate n i) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  let q : Space (m + 1) → ℝ := fun x =>
    heatPotentialProfile (r ^ (m + 1) * gaussianKernel (m + 1) τ (z₀.1-x))
  let U : Space (m + 1) → ℝ := fun x => u (x,z₀.2-τ)
  have huloc : ∀ x ∈ tsupport q, ContDiffAt ℝ 2 U x := by
    intro x hx
    have hxE := heatPotential_slice_tsupport hr hτ z₀ hx
    exact (hu.2.2.2.2 (x,z₀.2-τ) ⟨hxE, by dsimp; linarith⟩).2.1
  have hconv (x : Space (m + 1)) :
      fderiv ℝ (fun y => fderiv ℝ U y (coordinate (m + 1) i)) x (coordinate (m + 1) i) * q x =
        q x * fderiv ℝ (fderiv ℝ U) x (coordinate (m + 1) i) (coordinate (m + 1) i) := by
    by_cases hx : q x = 0
    · simp [hx]
    · rw [coordinate_second_fderiv_eq_of_contDiffAt (huloc x (subset_tsupport q hx))]
      ring
  have hright : Integrable (fun x => fderiv ℝ
      (fun y => fderiv ℝ U y (coordinate (m + 1) i)) x (coordinate (m + 1) i) * q x) :=
    (integrable_heatPotential_mul_caloric_second hr hτ z₀ hu (coordinate (m + 1) i)).congr
      (ae_of_all _ fun x => (hconv x).symm)
  let s : (Fin m → ℝ) → Set ℝ := fun y => {t : ℝ |
    gaussianKernel (m + 1) τ (z₀.1 - WithLp.toLp 2 (i.insertNth t y)) = (r ^ (m + 1))⁻¹}
  have hs (y : Fin m → ℝ) : (s y).Countable :=
    (gaussian_levelSet_coordinate_finite i hτ _ z₀.1 y).countable
  have hq2 (y : Fin m → ℝ) (t : ℝ) (ht : t ∉ s y) :
      ContDiffAt ℝ 2 q (WithLp.toLp 2 (i.insertNth t y)) := by
    have hne : r ^ (m + 1) * gaussianKernel (m + 1) τ
        (z₀.1 - WithLp.toLp 2 (i.insertNth t y)) ≠ 1 := by
      intro h
      have hg : gaussianKernel (m + 1) τ (z₀.1 - WithLp.toLp 2 (i.insertNth t y)) =
          (r ^ (m + 1))⁻¹ := by
        apply (mul_left_cancel₀ (pow_ne_zero (m + 1) hr.ne'))
        rw [h, mul_inv_cancel₀ (pow_ne_zero (m + 1) hr.ne')]
      exact ht hg
    exact (heatPotential_centered_contDiffAt (r ^ (m + 1)) τ z₀.1 _ hne).of_le (by simp)
  have h := integral_mul_coordinate_second_fderiv_eq_swap i
    (heatPotential_slice_contDiff (m + 1) r τ z₀.1)
    (heatPotential_slice_hasCompactSupport hr hτ z₀) s hs hq2 huloc
    (integrable_source_mul_heatPotential_second hn hr hτ z₀ hu.1 i) hright
  exact h.trans (integral_congr_ae (ae_of_all _ hconv))



lemma integral_heatPotential_product_derivative_eq_neg_density {n : ℕ} (hn : 1 ≤ n)
    {r τ : ℝ} (hr : 0 < r) (hτ : 0 < τ) (z₀ : SpaceTime n)
    {u : SpaceTime n → ℝ}
    (hu : IsClassicalCaloricOn u {z ∈ closure (heatBall n r z₀) | z.2 < z₀.2}) :
    (∫ y, u (y,z₀.2-τ) * deriv (fun θ => heatPotentialProfile
        (r ^ n * gaussianKernel n θ (z₀.1-y))) τ -
        deriv (fun t => u (y,t)) (z₀.2-τ) *
          heatPotentialProfile (r ^ n * gaussianKernel n τ (z₀.1-y)) ∂spatialMeasure n) =
      -(∫ y, u (y,z₀.2-τ) *
        (if 1 < r ^ n * gaussianKernel n τ (z₀.1-y) then
          ‖z₀.1-y‖ ^ 2 / (4 * τ ^ 2) else 0) ∂spatialMeasure n) := by
  let Q : Space n → ℝ := fun x => heatPotentialProfile
    (r ^ n * gaussianKernel n τ (z₀.1-x))
  let Qt : Space n → ℝ := fun x => deriv (fun θ => heatPotentialProfile
    (r ^ n * gaussianKernel n θ (z₀.1-x))) τ
  let Qii : Fin n → Space n → ℝ := fun i x =>
    fderiv ℝ (fun y => fderiv ℝ Q y (coordinate n i)) x (coordinate n i)
  let U : Space n → ℝ := fun x => u (x,z₀.2-τ)
  let Ut : Space n → ℝ := fun x => deriv (fun t => u (x,t)) (z₀.2-τ)
  let D : Space n → ℝ := fun x => if 1 < r ^ n * gaussianKernel n τ (z₀.1-x) then
    ‖z₀.1-x‖ ^ 2 / (4 * τ ^ 2) else 0
  have hQt : Integrable (fun x => U x * Qt x) (spatialMeasure n) :=
    integrable_source_mul_heatPotential_time_deriv hr hτ z₀ hu.1
  have hUt : Integrable (fun x => Ut x * Q x) (spatialMeasure n) := by
    simpa only [mul_comm] using (integrable_heatPotential_mul_source hr hτ z₀ hu.2.1)
  have hQii (i : Fin n) : Integrable (fun x => U x * Qii i x) (spatialMeasure n) :=
    integrable_source_mul_heatPotential_second hn hr hτ z₀ hu.1 i
  have hpoint : (fun x => (∑ i : Fin n, U x * Qii i x) - U x * Qt x) =ᵐ[spatialMeasure n]
      (fun x => U x * D x) := by
    filter_upwards [ae_gaussian_level_ne_one hn hτ (pow_ne_zero n hr.ne') z₀.1] with x hx
    rw [← Finset.mul_sum, ← mul_sub]
    exact congrArg (U x * ·) (heatPotential_centered_spatial_time_identity n
      (pow_pos hr _) hτ z₀.1 x hx)
  have hD : (∫ x, U x * D x ∂spatialMeasure n) =
      (∑ i : Fin n, ∫ x, U x * Qii i x ∂spatialMeasure n) -
        ∫ x, U x * Qt x ∂spatialMeasure n := by
    rw [← integral_congr_ae hpoint, integral_sub (integrable_finsetSum _ (fun i _ => hQii i)) hQt,
      integral_finsetSum _ (fun i _ => hQii i)]
  have hgreen : (∑ i : Fin n, ∫ x, U x * Qii i x ∂spatialMeasure n) =
      ∫ x, Ut x * Q x ∂spatialMeasure n := by
    simp_rw [show ∀ i : Fin n, (∫ x, U x * Qii i x ∂spatialMeasure n) =
        ∫ x, Q x * fderiv ℝ (fderiv ℝ U) x (coordinate n i) (coordinate n i)
          ∂spatialMeasure n from fun i => heatPotential_spatial_green_coordinate hn hr hτ z₀ hu i]
    have h := integral_heatPotential_mul_caloric_time_eq_sum hr hτ z₀ hu
    simpa only [Q, U, Ut, mul_comm] using h.symm
  change (∫ x, U x * Qt x - Ut x * Q x ∂spatialMeasure n) =
    -(∫ x, U x * D x ∂spatialMeasure n)
  rw [integral_sub hQt hUt, hD, hgreen]
  ring

lemma heatBall_truncated_potential_identity {n : ℕ} (hn : 1 ≤ n) {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hδT : δ < r ^ 2 / (4 * Real.pi))
    (z₀ : SpaceTime n) {u : SpaceTime n → ℝ}
    (huc : ContinuousOn u (closure (heatBall n r z₀)))
    (hu : IsClassicalCaloricOn u {z ∈ closure (heatBall n r z₀) | z.2 < z₀.2}) :
    (∫ y, u (y,z₀.2-δ) * heatPotentialProfile
      (r ^ n * gaussianKernel n δ (z₀.1-y)) ∂spatialMeasure n) =
      ∫ z in heatBall n r z₀ ∩ {z | z.2 ≤ z₀.2-δ},
        u z * (‖z₀.1-z.1‖ ^ 2 / (4 * (z₀.2-z.2) ^ 2)) ∂spaceTimeMeasure n := by
  let T := r ^ 2 / (4 * Real.pi)
  have ht := integral_heatPotential_product_strip_of_caloric hn hr hδ hδT.le z₀ hu
  rw [integral_heatPotentialProfile_eq_zero_of_time_ge hn hr le_rfl, zero_sub] at ht
  have he : (∫ τ in δ..T, ∫ y, u (y,z₀.2-τ) * deriv (fun θ => heatPotentialProfile
        (r ^ n * gaussianKernel n θ (z₀.1-y))) τ -
        deriv (fun t => u (y,t)) (z₀.2-τ) *
          heatPotentialProfile (r ^ n * gaussianKernel n τ (z₀.1-y)) ∂spatialMeasure n) =
      -(∫ τ in Ioc δ T, ∫ y, u (y,z₀.2-τ) *
        (if 1 < r ^ n * gaussianKernel n τ (z₀.1-y) then
          ‖z₀.1-y‖ ^ 2 / (4 * τ ^ 2) else 0) ∂spatialMeasure n) := by
    rw [intervalIntegral.integral_of_le hδT.le, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro τ hτ
    exact integral_heatPotential_product_derivative_eq_neg_density hn hr
      (hδ.trans hτ.1) z₀ hu
  rw [he] at ht
  have h := neg_injective ht
  rw [heatBall_time_cut_integral_backward hn hr hδ z₀ u huc]
  exact h.symm

theorem heatBallMeanValueOneSided : P201Specs.Heat.heatBallMeanValueOneSidedStatement := by
  intro n hn r hr z₀ u huc hu
  apply heatBallMeanValue_of_truncated_potential hn hr z₀ u huc
  intro δ hδ hδT
  exact heatBall_truncated_potential_identity hn hr hδ hδT z₀ huc hu

theorem heatBallMeanValueNeighborhood : P201Specs.Heat.heatBallMeanValueNeighborhoodStatement :=
  heatBallMeanValueNeighborhood_of_oneSided heatBallMeanValueOneSided


end P201.Heat
