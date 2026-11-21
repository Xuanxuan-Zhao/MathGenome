import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.HolomorphicDependence
import MathGenome.Internal.ODEDynamics.D13Unified.Ch03.ContractionIteration
import MathGenome.Internal.ODEDynamics.D13Unified.Ch06.HolomorphicLimits
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Joint holomorphic local dependence for complex ODEs,
including varying initial time and uniqueness of local solution germs. -/

namespace D13Unified.Ch06.HolomorphicDependence

open Filter Metric Set
open scoped Topology
open D13Unified.Ch06.HolomorphicLimits

/-- Substitution of a one-variable analytic curve into a coordinate power
series. Normal convergence follows from the existing summable majorant. -/
theorem analyticAt_comp_coordinateHolomorphic {d n : ℕ}
    {V : Set (State d)} {f : State d → State n} (hf : CoordinateHolomorphicOn V f)
    {q : ℂ → State d} {z : ℂ} (hq : AnalyticAt ℂ q z) (hqV : q z ∈ V) :
    AnalyticAt ℂ (f ∘ q) z := by
  obtain ⟨r, hr, _, hcomp⟩ := hf (q z) hqV
  apply AnalyticAt.pi
  intro i
  obtain ⟨c, hc⟩ := hcomp i
  obtain ⟨u, hu, hub⟩ := coordinate_series_majorant (q z) r c hr
    (fun w hw => (hc w hw).1)
  obtain ⟨s, hs, hqs⟩ := Metric.continuousAt_iff.mp hq.continuousAt (r / 2) (half_pos hr)
  have hqnear : ∀ t ∈ ball z s, q t ∈ ball (q z) (r / 2) := by
    intro t ht
    exact hqs (mem_ball.mp ht)
  let A := {t | AnalyticAt ℂ q t}
  let W := ball z s ∩ A
  have hW : IsOpen W := isOpen_ball.inter (isOpen_analyticAt ℂ q)
  have hzW : z ∈ W := ⟨mem_ball_self hs, hq⟩
  have hdiff : DifferentiableOn ℂ
      (fun t => ∑' α, c α * ∏ j : Fin d, (q t j - q z j) ^ α j) W := by
    refine Complex.differentiableOn_tsum_of_summable_norm hu ?_ hW ?_
    · intro α t ht
      exact ((analyticAt_coordinate_term (q z) c α (q t)).comp
        ht.2).differentiableAt.differentiableWithinAt
    · intro α t ht
      exact hub α _ (hqnear t ht.1)
  apply (hdiff.analyticAt (hW.mem_nhds hzW)).congr
  filter_upwards [hW.mem_nhds hzW] with t ht
  exact (hc _ (ball_subset_ball (half_le_self hr.le) (hqnear t ht.1))).2.tsum_eq

/-- Composition preserves the paper's literal multivariate definition. No
identification with several-variable Frechet analyticity is assumed. -/
theorem coordinateHolomorphicOn_comp {d k n : ℕ}
    {U : Set (State d)} {V : Set (State k)}
    {f : State d → State n} {g : State k → State d}
    (hf : CoordinateHolomorphicOn U f) (hg : CoordinateHolomorphicOn V g)
    (hV : IsOpen V) (hmap : MapsTo g V U) :
    CoordinateHolomorphicOn V (f ∘ g) := by
  apply coordinateHolomorphicOn_of_continuous_lineAnalytic hV
    (hf.continuousOn.comp hg.continuousOn hmap)
  intro a v t ht
  exact analyticAt_comp_coordinateHolomorphic hf
    ((hg.analyticOnNhd_affineLine a v) t ht) (hmap ht)

/-- Formal complex analytic power series imply the exact coordinate-series
representation required here, through the proved line/Cauchy bridge. -/
theorem coordinateHolomorphicOn_of_analyticOnNhd {d n : ℕ}
    {V : Set (State d)} {f : State d → State n}
    (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f V) :
    CoordinateHolomorphicOn V f := by
  apply coordinateHolomorphicOn_of_continuous_lineAnalytic hV hf.continuousOn
  intro a v z hz
  exact (hf _ hz).comp (analyticAt_affineLine a v z)

lemma continuous_stateCoordinates (n m : ℕ) :
    Continuous (stateCoordinates (n := n) (m := m)) := by
  exact continuous_pi fun i => continuous_apply _

lemma continuous_parameterCoordinates (n m : ℕ) :
    Continuous (parameterCoordinates (n := n) (m := m)) := by
  exact continuous_pi fun i => continuous_apply _

lemma continuous_finTail (d : ℕ) :
    Continuous (Fin.tail : State (d + 1) → State d) := by
  exact continuous_pi fun i => continuous_apply _

lemma isOpen_fixedProduct {n m : ℕ} (z₀ : ℂ) (w₀ : State n) (p₀ : State m)
    (a b c : ℝ) : IsOpen (fixedProduct z₀ w₀ p₀ a b c) := by
  exact (isOpen_ball.preimage (continuous_apply 0)).inter
    ((isOpen_ball.preimage ((continuous_stateCoordinates n m).comp (continuous_finTail _))).inter
      (isOpen_ball.preimage
        ((continuous_parameterCoordinates n m).comp (continuous_finTail _))))

lemma isOpen_movingProduct {n m : ℕ} (z₀ : ℂ) (w₀ : State n) (p₀ : State m)
    (a e b c : ℝ) : IsOpen (movingProduct z₀ w₀ p₀ a e b c) := by
  exact (isOpen_ball.preimage (continuous_apply 0)).inter
    ((isOpen_ball.preimage ((continuous_apply 0).comp (continuous_finTail _))).inter
      ((isOpen_ball.preimage ((continuous_stateCoordinates n m).comp
        ((continuous_finTail _).comp (continuous_finTail _)))).inter
      (isOpen_ball.preimage ((continuous_parameterCoordinates n m).comp
        ((continuous_finTail _).comp (continuous_finTail _))))))

/-- A moving-time family contains the fixed-time result by restriction to
η = z₀. The restriction preserves the full coordinate-series representation
and retains germ uniqueness for every nearby initial state and parameter. -/
theorem fixedTimeConclusion_of_movingTimeConclusion {n m : ℕ}
    {U : Set (FieldPoint n m)} {f : FieldPoint n m → State n}
    {z₀ : ℂ} {w₀ : State n} {p₀ : State m}
    (h : MovingTimeConclusion U f z₀ w₀ p₀) :
    FixedTimeConclusion U f z₀ w₀ p₀ := by
  obtain ⟨a, e, b, c, ha, he, _, hb, hc, W, hW, hdata⟩ := h
  refine ⟨a, b, c, ha, hb, hc, fun z ξ p => W z z₀ ξ p, ?_,
    hdata z₀ (mem_ball_self he)⟩
  let Q : FieldPoint n m → MovingPoint n m :=
    fun q => Fin.cons (q 0) (Fin.cons z₀ (Fin.tail q))
  have hQ : AnalyticOnNhd ℂ Q (fixedProduct z₀ w₀ p₀ a b c) := by
    intro q _
    apply AnalyticAt.pi
    intro i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · exact (ContinuousLinearMap.proj (R := ℂ) 0).analyticAt q
    · exact analyticAt_const
    · exact (ContinuousLinearMap.proj (R := ℂ) k.succ).analyticAt q
  have hmap : MapsTo Q (fixedProduct z₀ w₀ p₀ a b c)
      (movingProduct z₀ w₀ p₀ a e b c) := by
    intro q hq
    exact ⟨hq.1, mem_ball_self he, hq.2⟩
  exact coordinateHolomorphicOn_comp hW
    (coordinateHolomorphicOn_of_analyticOnNhd (isOpen_fixedProduct _ _ _ _ _ _) hQ)
    (isOpen_fixedProduct _ _ _ _ _ _) hmap

/-- Restrict the coordinate representation to any smaller open domain. -/
theorem coordinateHolomorphicOn_mono {d n : ℕ}
    {U V : Set (State d)} {f : State d → State n}
    (hf : CoordinateHolomorphicOn U f) (hV : IsOpen V) (hVU : V ⊆ U) :
    CoordinateHolomorphicOn V f := by
  apply coordinateHolomorphicOn_of_continuous_lineAnalytic hV (hf.continuousOn.mono hVU)
  intro a v t ht
  exact (hf.analyticOnNhd_affineLine a v) t (hVU ht)

/-- A bounded coordinate-holomorphic map is Lipschitz on a smaller ball.
This uses the Schwarz lemma only on actual complex lines and so requires no
unproved identification of coordinate and Frechet analytic representations. -/
theorem norm_sub_le_of_coordinateHolomorphicOn_ball {d n : ℕ}
    {f : State d → State n} {a : State d} {R M : ℝ}
    (hR : 0 < R) (hf : CoordinateHolomorphicOn (ball a R) f)
    (hb : ∀ w ∈ ball a R, ‖f w - f a‖ ≤ M)
    {x y : State d} (hx : x ∈ ball a (R / 4)) (hy : y ∈ ball a (R / 4)) :
    ‖f y - f x‖ ≤ (4 * M / R) * ‖y - x‖ := by
  by_cases hxy : y = x
  · simp [hxy]
  have hv : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hvR : ‖y - x‖ < R / 2 := by
    calc
      ‖y - x‖ ≤ ‖y - a‖ + ‖x - a‖ := by
        simpa only [norm_sub_rev a x] using norm_sub_le_norm_sub_add_norm_sub y a x
      _ < R / 4 + R / 4 := add_lt_add (mem_ball_iff_norm.mp hy) (mem_ball_iff_norm.mp hx)
      _ = R / 2 := by ring
  let ρ := R / (2 * ‖y - x‖)
  have hρ : 0 < ρ := div_pos hR (mul_pos (by norm_num) hv)
  have hρ1 : 1 < ρ := (lt_div_iff₀ (mul_pos (by norm_num) hv)).mpr (by linarith)
  have hmap : MapsTo (affineLine x (y - x)) (ball 0 ρ) (ball a R) := by
    intro t ht
    rw [mem_ball_iff_norm] at ht ⊢
    simp only [sub_zero] at ht
    have ht' : ‖t‖ * ‖y - x‖ < R / 2 := by
      have hh := (mul_lt_mul_of_pos_right ht hv)
      dsimp [ρ] at hh
      have heq : R / (2 * ‖y - x‖) * ‖y - x‖ = R / 2 := by
        field_simp
      rwa [heq] at hh
    calc
      ‖affineLine x (y - x) t - a‖ ≤ ‖x - a‖ + ‖t • (y - x)‖ := by
        have heq : affineLine x (y-x) t - a = (x-a) + t • (y-x) := by
          simp only [affineLine]; abel
        rw [heq]
        exact norm_add_le _ _
      _ = ‖x - a‖ + ‖t‖ * ‖y - x‖ := by rw [norm_smul]
      _ < R / 4 + R / 2 := add_lt_add (mem_ball_iff_norm.mp hx) ht'
      _ < R := by linarith
  have hdiff : DifferentiableOn ℂ (f ∘ affineLine x (y-x)) (ball 0 ρ) := by
    intro t ht
    exact ((hf.analyticOnNhd_affineLine x (y-x)) t (hmap ht)).differentiableAt.differentiableWithinAt
  have hmaps : MapsTo (f ∘ affineLine x (y-x)) (ball 0 ρ)
      (closedBall ((f ∘ affineLine x (y-x)) 0) (2*M)) := by
    intro t ht
    rw [mem_closedBall_iff_norm]
    simp only [Function.comp_apply, affineLine, zero_smul, add_zero]
    calc
      ‖f (x + t • (y-x)) - f x‖ ≤ ‖f (x + t • (y-x)) - f a‖ + ‖f x - f a‖ :=
        by simpa only [norm_sub_rev (f a) (f x)] using
          norm_sub_le_norm_sub_add_norm_sub (f (x + t • (y-x))) (f a) (f x)
      _ ≤ M + M := add_le_add (hb _ (hmap ht))
        (hb x (ball_subset_ball (by linarith) hx))
      _ = 2*M := by ring
  have hs := Complex.dist_le_div_mul_dist_of_mapsTo_ball hdiff hmaps
    (show (1 : ℂ) ∈ ball 0 ρ by simpa [mem_ball_iff_norm] using hρ1)
  simp only [Function.comp_apply, affineLine, one_smul, zero_smul, add_zero,
    add_sub_cancel, dist_eq_norm, sub_zero, norm_one, mul_one] at hs
  convert hs using 1
  dsimp [ρ]
  field_simp
  ring

/-- Joint local boundedness and Lipschitz control follow from the original
coordinate-holomorphy hypothesis. The constants hold on an actual open ball
inside the original domain, uniformly in all its coordinates. -/
theorem exists_local_bound_lipschitz {d n : ℕ}
    {U : Set (State d)} {f : State d → State n} (hU : IsOpen U)
    (hf : CoordinateHolomorphicOn U f) {a : State d} (ha : a ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ball a r ⊆ U ∧
      ∃ M L : NNReal, (∀ x ∈ ball a r, ‖f x‖ ≤ M) ∧
        LipschitzOnWith L f (ball a r) := by
  have hcont : ContinuousAt f a := hf.continuousOn.continuousAt (hU.mem_nhds ha)
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.mp hcont 1 (by norm_num)
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU a ha
  let R := min δ ε
  have hR : 0 < R := lt_min hδ hε
  have hRU : ball a R ⊆ U := (ball_subset_ball (min_le_right _ _)).trans hεU
  have hb : ∀ x ∈ ball a R, ‖f x - f a‖ ≤ (1 : ℝ) := by
    intro x hx
    rw [← dist_eq_norm]
    exact (hδf ((mem_ball.mp hx).trans_le (min_le_left _ _))).le
  let M : NNReal := ⟨‖f a‖ + 1, by positivity⟩
  let L : NNReal := ⟨4 / R, by positivity⟩
  refine ⟨R / 4, by positivity, (ball_subset_ball (by linarith)).trans hRU, M, L, ?_, ?_⟩
  · intro x hx
    calc
      ‖f x‖ ≤ ‖f x - f a‖ + ‖f a‖ := by
        simpa only [sub_add_cancel] using norm_add_le (f x - f a) (f a)
      _ ≤ 1 + ‖f a‖ := add_le_add (hb x (ball_subset_ball (by linarith) hx)) le_rfl
      _ = (M : ℝ) := by change 1 + ‖f a‖ = ‖f a‖ + 1; ring
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [dist_eq_norm, dist_eq_norm]
    change ‖f x - f y‖ ≤ (4 / R) * ‖x - y‖
    simpa only [mul_one] using norm_sub_le_of_coordinateHolomorphicOn_ball hR
      (coordinateHolomorphicOn_mono hf isOpen_ball hRU) hb hy hx

/-- A complex differential uniqueness estimate on a sufficiently small
closed disc. The maximum is attained on the whole disc, and the complex
mean-value inequality applies along its real straight segments. -/
theorem eqOn_closedBall_of_deriv_sub_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {u v u' v' : ℂ → E} {η : ℂ} {r L : ℝ}
    (hr : 0 < r) (hL : 0 ≤ L) (hsmall : L * r < 1)
    (hu : ∀ z ∈ closedBall η r, HasDerivAt u (u' z) z)
    (hv : ∀ z ∈ closedBall η r, HasDerivAt v (v' z) z)
    (hb : ∀ z ∈ closedBall η r, ‖u' z - v' z‖ ≤ L * ‖u z - v z‖)
    (hinit : u η = v η) : EqOn u v (closedBall η r) := by
  let D : ℂ → E := fun z => u z - v z
  have hD : ∀ z ∈ closedBall η r, HasDerivAt D (u' z - v' z) z :=
    fun z hz => (hu z hz).sub (hv z hz)
  obtain ⟨q, hq, hmax⟩ := (isCompact_closedBall η r).exists_isMaxOn
    ⟨η, mem_closedBall_self hr.le⟩ (HasDerivAt.continuousOn hD).norm
  have hbound : ∀ z ∈ closedBall η r, ‖u' z - v' z‖ ≤ L * ‖D q‖ := by
    intro z hz
    exact (hb z hz).trans (mul_le_mul_of_nonneg_left (hmax hz) hL)
  have hmean := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (hD z hz).hasDerivWithinAt) hbound (convex_closedBall η r)
    (mem_closedBall_self hr.le) hq
  have hDη : D η = 0 := sub_eq_zero.mpr hinit
  rw [hDη, sub_zero] at hmean
  have hM : ‖D q‖ ≤ L * ‖D q‖ * r := hmean.trans
    (mul_le_mul_of_nonneg_left (mem_closedBall_iff_norm.mp hq)
      (mul_nonneg hL (norm_nonneg _)))
  have hzero : ‖D q‖ = 0 := by nlinarith [norm_nonneg (D q)]
  intro z hz
  exact sub_eq_zero.mp (norm_eq_zero.mp ((norm_nonneg (D z)).antisymm'
    (by simpa [hzero] using hmax hz)))

lemma norm_fieldPoint_state_sub_le {n m : ℕ} (z : ℂ) (u v : State n) (p : State m) :
    ‖fieldPoint z u p - fieldPoint z v p‖ ≤ ‖u - v‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [fieldPoint]
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simpa only [Pi.sub_apply, fieldPoint, Fin.cons_succ, Fin.append_left] using
        norm_le_pi_norm (u-v) k
    · simp [fieldPoint]

lemma continuousAt_fieldPoint_curve {n m : ℕ} {u : ℂ → State n} {η : ℂ}
    (hu : ContinuousAt u η) (p : State m) :
    ContinuousAt (fun z => fieldPoint z (u z) p) η := by
  apply continuousAt_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuousAt_id
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simpa only [fieldPoint, Fin.cons_succ, Fin.append_left, Function.comp_def] using
        (continuous_apply k).continuousAt.comp hu
    · simpa only [fieldPoint, Fin.cons_succ, Fin.append_right] using
        (continuousAt_const : ContinuousAt (fun _ : ℂ => p k) η)

/-- Local holomorphic solution germs of the original field are unique.
The existence of a solution is not assumed as a certificate for any field:
this compares two arbitrary curves which actually satisfy the complex ODE. -/
theorem solution_germ_unique {n m : ℕ}
    {U : Set (FieldPoint n m)} {f : FieldPoint n m → State n}
    (hU : IsOpen U) (hf : CoordinateHolomorphicOn U f)
    {V W : Set ℂ} {u v : ℂ → State n} {η : ℂ} {p : State m}
    (hV : IsOpen V) (hW : IsOpen W) (hηV : η ∈ V) (hηW : η ∈ W)
    (hu : ∀ z ∈ V, fieldPoint z (u z) p ∈ U ∧
      HasDerivAt u (f (fieldPoint z (u z) p)) z)
    (hv : ∀ z ∈ W, fieldPoint z (v z) p ∈ U ∧
      HasDerivAt v (f (fieldPoint z (v z) p)) z)
    (hinit : u η = v η) : u =ᶠ[𝓝 η] v := by
  let a := fieldPoint η (u η) p
  obtain ⟨R, hR, _, M, L, _, hLip⟩ := exists_local_bound_lipschitz hU hf (hu η hηV).1
  have hgu := (continuousAt_fieldPoint_curve (hu η hηV).2.continuousAt p).preimage_mem_nhds
    (ball_mem_nhds a hR)
  have hgv := (continuousAt_fieldPoint_curve (hv η hηW).2.continuousAt p).preimage_mem_nhds
    (show ball a R ∈ 𝓝 (fieldPoint η (v η) p) by rw [← hinit]; exact ball_mem_nhds a hR)
  have hN : V ∩ W ∩ ((fun z => fieldPoint z (u z) p) ⁻¹' ball a R) ∩
      ((fun z => fieldPoint z (v z) p) ⁻¹' ball a R) ∈ 𝓝 η :=
    inter_mem (inter_mem (inter_mem (hV.mem_nhds hηV) (hW.mem_nhds hηW)) hgu) hgv
  obtain ⟨δ, hδ, hδN⟩ := Metric.mem_nhds_iff.mp hN
  have hLp : 0 < (L : ℝ) + 1 := by positivity
  obtain ⟨r, hr, hrsmall⟩ := exists_between (lt_min hδ (one_div_pos.mpr hLp))
  have hrδ : r < δ := hrsmall.trans_le (min_le_left _ _)
  have hrl : (L : ℝ) * r < 1 := by
    have hh := (lt_div_iff₀ hLp).mp (hrsmall.trans_le (min_le_right _ _))
    nlinarith
  have hsub : closedBall η r ⊆ V ∩ W ∩ ((fun z => fieldPoint z (u z) p) ⁻¹' ball a R) ∩
      ((fun z => fieldPoint z (v z) p) ⁻¹' ball a R) :=
    (closedBall_subset_ball hrδ).trans hδN
  have heq : EqOn u v (closedBall η r) := by
    apply eqOn_closedBall_of_deriv_sub_le hr (NNReal.coe_nonneg L) hrl
      (fun z hz => (hu z (hsub hz).1.1.1).2)
      (fun z hz => (hv z (hsub hz).1.1.2).2) _ hinit
    intro z hz
    exact (hLip.norm_sub_le (hsub hz).1.2 (hsub hz).2).trans
      (mul_le_mul_of_nonneg_left (norm_fieldPoint_state_sub_le z (u z) (v z) p)
        (NNReal.coe_nonneg L))
  exact Filter.eventuallyEq_iff_exists_mem.mpr ⟨ball η r, ball_mem_nhds η hr,
    fun z hz => heq (ball_subset_closedBall hz)⟩


/-- Addition preserves the literal coordinate power-series notion. -/
theorem _root_.D13Unified.Ch06.HolomorphicLimits.CoordinateHolomorphicOn.add {d n : ℕ} {V : Set (State d)}
    {f g : State d → State n} (hf : CoordinateHolomorphicOn V f)
    (hg : CoordinateHolomorphicOn V g) (hV : IsOpen V) :
    CoordinateHolomorphicOn V (f + g) := by
  apply coordinateHolomorphicOn_of_continuous_lineAnalytic hV
    (hf.continuousOn.add hg.continuousOn)
  intro a v z hz
  exact ((hf.analyticOnNhd_affineLine a v) z hz).add
    ((hg.analyticOnNhd_affineLine a v) z hz)

/-- Real scalar multiplication is sufficient for convexity of the holomorphic
function space used for Bochner integration. -/
theorem _root_.D13Unified.Ch06.HolomorphicLimits.CoordinateHolomorphicOn.real_smul {d n : ℕ} {V : Set (State d)}
    {f : State d → State n} (hf : CoordinateHolomorphicOn V f)
    (hV : IsOpen V) (c : ℝ) : CoordinateHolomorphicOn V (c • f) := by
  apply coordinateHolomorphicOn_of_continuous_lineAnalytic hV
    (hf.continuousOn.const_smul c)
  intro a v z hz
  exact ((hf.analyticOnNhd_affineLine a v) z hz).const_smul

/-- Extend a continuous map on a compact set by zero. Only its values on
that set will be used; holomorphy is required on an open subset inside it. -/
noncomputable def compactExtension {d n : ℕ} (K : Set (State d))
    (u : C(K, State n)) (q : State d) : State n :=
  by classical exact if hq : q ∈ K then u ⟨q, hq⟩ else 0

@[simp] lemma compactExtension_apply {d n : ℕ} {K : Set (State d)}
    (u : C(K, State n)) {q : State d} (hq : q ∈ K) :
    compactExtension K u q = u ⟨q, hq⟩ := by
  simp [compactExtension, hq]

/-- Holomorphic maps on an open subset of a compact set form a closed set
in the sup norm. This uses the accepted several-variable uniform-limit
result, including its absolutely convergent coordinate-series conclusion. -/
theorem isClosed_coordinateHolomorphic_compactExtension {d n : ℕ}
    {K V : Set (State d)} (hK : IsCompact K) (hV : IsOpen V) (hVK : V ⊆ K) :
    IsClosed {u : C(K, State n) | CoordinateHolomorphicOn V (compactExtension K u)} := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply IsSeqClosed.isClosed
  intro F u hF hlim
  apply holomorphic_limit d n V (fun j => compactExtension K (F j))
    (compactExtension K u) hV hF
  intro S hSV _
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hnorm := Metric.tendsto_nhds.mp hlim ε hε
  filter_upwards [hnorm] with j hj q hq
  rw [compactExtension_apply _ (hVK (hSV hq)), compactExtension_apply _ (hVK (hSV hq))]
  exact (ContinuousMap.dist_apply_le_dist (f := u) (g := F j) (⟨q, hVK (hSV hq)⟩ : K)).trans_lt
    (by simpa only [dist_comm] using hj)

/-- The same space is convex over the reals, as needed for the closed-convex
Bochner integration theorem. -/
theorem convex_coordinateHolomorphic_compactExtension {d n : ℕ}
    {K V : Set (State d)} (hV : IsOpen V) (hVK : V ⊆ K) :
    Convex ℝ {u : C(K, State n) | CoordinateHolomorphicOn V (compactExtension K u)} := by
  intro u hu v hv a b _ _ _
  have hh := (hu.real_smul hV a).add (hv.real_smul hV b) hV
  apply coordinateHolomorphicOn_of_continuous_lineAnalytic hV
  · apply hh.continuousOn.congr
    intro q hq
    simp [compactExtension_apply _ (hVK hq)]
  · intro x y z hz
    apply ((hh.analyticOnNhd_affineLine x y) z hz).congr
    filter_upwards [(hV.preimage (continuous_affineLine x y)).mem_nhds hz] with t ht
    simp [Function.comp_apply, compactExtension_apply _ (hVK ht)]

/-- Integration of a continuous family in the compact function space
preserves joint coordinate holomorphy on every open subset of that compact.
The measure is any probability measure, so in particular normalized length
on the unit interval is permitted. -/
theorem coordinateHolomorphic_compactExtension_integral {d n : ℕ}
    {K V : Set (State d)} [CompactSpace K] (hK : IsCompact K) (hV : IsOpen V) (hVK : V ⊆ K)
    {A : Type*} [MeasurableSpace A] {μ : MeasureTheory.Measure A}
    [MeasureTheory.IsProbabilityMeasure μ]
    {F : A → C(K, State n)} (hFi : MeasureTheory.Integrable F μ)
    (hF : ∀ᵐ t ∂μ, CoordinateHolomorphicOn V (compactExtension K (F t))) :
    CoordinateHolomorphicOn V (compactExtension K (∫ t, F t ∂μ)) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact (convex_coordinateHolomorphic_compactExtension hV hVK).integral_mem
    (isClosed_coordinateHolomorphic_compactExtension hK hV hVK) hF hFi


/-- Equality on the domain preserves coordinate holomorphy. -/
theorem _root_.D13Unified.Ch06.HolomorphicLimits.CoordinateHolomorphicOn.congr
    {d n : ℕ} {V : Set (State d)} {f g : State d → State n}
    (hf : CoordinateHolomorphicOn V f) (hfg : EqOn f g V) :
    CoordinateHolomorphicOn V g := by
  intro a ha
  obtain ⟨r, hr, hsub, hc⟩ := hf a ha
  refine ⟨r, hr, hsub, fun i => ?_⟩
  obtain ⟨c, hc⟩ := hc i
  refine ⟨c, fun q hq => ?_⟩
  simpa only [hfg (hsub hq)] using hc q hq

/-- A jointly continuous family, each member holomorphic in the complex
variables, has a holomorphic integral over the real unit interval.
The continuity hypothesis includes the interval's endpoints. -/
theorem coordinateHolomorphicOn_intervalIntegral {d n : ℕ}
    {V : Set (State d)} (hV : IsOpen V) {G : ℝ → State d → State n}
    (hG : ContinuousOn (Function.uncurry G) (univ ×ˢ V))
    (hGh : ∀ t, CoordinateHolomorphicOn V (G t)) :
    CoordinateHolomorphicOn V (fun q => ∫ t in (0 : ℝ)..1, G t q) := by
  classical
  intro a ha
  obtain ⟨R, hR, hRV⟩ := Metric.isOpen_iff.mp hV a ha
  let r := R / 2
  have hr : 0 < r := half_pos hR
  let K := closedBall a r
  let B := ball a r
  have hKV : K ⊆ V := (closedBall_subset_ball (half_lt_self hR)).trans hRV
  have hBK : B ⊆ K := ball_subset_closedBall
  have hK : IsCompact K := isCompact_closedBall _ _
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : ℝ → C(K, State n) := fun t =>
    ⟨fun q => G t q, hG.comp_continuous (continuous_const.prodMk continuous_subtype_val)
      (fun q => ⟨mem_univ _, hKV q.2⟩)⟩
  have hF : Continuous F := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact hG.comp_continuous (continuous_id.prodMap continuous_subtype_val)
      (fun q => ⟨mem_univ _, hKV q.2.2⟩)
  let μ := MeasureTheory.volume.restrict (Icc (0 : ℝ) 1)
  let : MeasureTheory.IsProbabilityMeasure μ := ⟨by simp [μ, Real.volume_Icc]⟩
  have hFi : MeasureTheory.Integrable F μ := hF.integrableOn_Icc
  have hhol : CoordinateHolomorphicOn B (compactExtension K (∫ t, F t ∂μ)) := by
    apply coordinateHolomorphic_compactExtension_integral hK isOpen_ball hBK hFi
    apply Filter.Eventually.of_forall
    intro t
    exact (coordinateHolomorphicOn_mono (hGh t) isOpen_ball (hBK.trans hKV)).congr
      (fun q hq => by rw [compactExtension_apply _ (hBK hq)]; rfl)
  have heq : EqOn (compactExtension K (∫ t, F t ∂μ))
      (fun q => ∫ t in (0 : ℝ)..1, G t q) B := by
    intro q hq
    rw [compactExtension_apply _ (hBK hq), ContinuousMap.integral_apply hFi]
    change (∫ t in Icc (0 : ℝ) 1, G t q) = _
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  obtain ⟨s, hs, hsB, hc⟩ := (hhol.congr heq) a (mem_ball_self hr)
  exact ⟨s, hs, hsB.trans (hBK.trans hKV), hc⟩

/-- A radial primitive, with the same straight-segment parametrization as
in the source's complex Picard iteration. -/
noncomputable def radialPrimitive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : ℂ → E) (η z : ℂ) : E :=
  (z - η) • ∫ t in (0 : ℝ)..1, g (η + (t : ℂ) * (z - η))

@[simp] theorem radialPrimitive_self {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (g : ℂ → E) (η : ℂ) : radialPrimitive g η η = 0 := by
  simp [radialPrimitive]

/-- The straight-segment primitive has complex derivative `g`, on the
whole disc where `g` is holomorphic. A genuine complex primitive and the
real fundamental theorem identify the radial formula; no real-time ODE
regularity is substituted for complex differentiation. -/
theorem hasDerivAt_radialPrimitive_of_mem_ball {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {g : ℂ → E} {a η z : ℂ} {r : ℝ}
    (hg : DifferentiableOn ℂ g (ball a r)) (hη : η ∈ ball a r)
    (hz : z ∈ ball a r) :
    HasDerivAt (radialPrimitive g η) (g z) z := by
  obtain ⟨P, hP⟩ := hg.isExactOn_ball
  have heq : ∀ w ∈ ball a r, radialPrimitive g η w = P w - P η := by
    intro w hw
    have hseg : ∀ t ∈ Icc (0 : ℝ) 1, η + (t : ℂ) * (w - η) ∈ ball a r := by
      intro t ht
      simpa only [AffineMap.lineMap_apply, Complex.real_smul, smul_eq_mul,
        vsub_eq_sub, vadd_eq_add, add_comm] using
        (convex_ball a r).lineMap_mem hη hw ht
    have hcont : ContinuousOn (fun t : ℝ => g (η + (t : ℂ) * (w - η))) (Icc 0 1) :=
      hg.continuousOn.comp (by fun_prop) hseg
    have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => P (η + (t : ℂ) * (w - η)))
          ((w - η) • g (η + (t : ℂ) * (w - η))) t := by
      intro t ht
      have hp := ((hP _ (hseg t (by simpa using ht))).hasFDerivAt.restrictScalars ℝ).comp t
        ((Complex.ofRealCLM.hasFDerivAt).mul_const (w - η) |>.const_add η)
      simpa [Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply,
        ContinuousLinearMap.coe_restrictScalars] using hp.hasDerivAt
    rw [radialPrimitive, ← intervalIntegral.integral_smul]
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (show ContinuousOn (fun t : ℝ => (w - η) • g (η + (t : ℂ) * (w - η)))
        (uIcc 0 1) from by rw [uIcc_of_le zero_le_one]; exact continuousOn_const.smul hcont).intervalIntegrable
  have hev : radialPrimitive g η =ᶠ[𝓝 z] (fun w => P w - P η) :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨ball a r, isOpen_ball.mem_nhds hz, heq⟩
  exact ((hP z hz).sub_const (P η)).congr_of_eventuallyEq hev

/-- Specialization to a disc centered at the initial time. -/
theorem hasDerivAt_radialPrimitive {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {g : ℂ → E} {η z : ℂ} {r : ℝ}
    (hr : 0 < r) (hg : DifferentiableOn ℂ g (ball η r)) (hz : z ∈ ball η r) :
    HasDerivAt (radialPrimitive g η) (g z) z :=
  hasDerivAt_radialPrimitive_of_mem_ball hg (mem_ball_self hr) hz


/-- The radial primitive is jointly holomorphic on any open domain stable
under contraction of its first coordinate towards the fixed initial time.
Other coordinates are independent complex variables throughout. -/
theorem coordinateHolomorphicOn_radialPrimitive {d n : ℕ}
    {V : Set (State (d + 1))} {g : State (d + 1) → State n}
    (hV : IsOpen V) (hg : CoordinateHolomorphicOn V g) (η : ℂ)
    (hstar : ∀ q ∈ V, ∀ t ∈ Icc (0 : ℝ) 1,
      Fin.cons (η + (t : ℂ) * (q 0 - η)) (Fin.tail q) ∈ V) :
    CoordinateHolomorphicOn V (fun q =>
      radialPrimitive (fun z => g (Fin.cons z (Fin.tail q))) η (q 0)) := by
  let θ : ℝ → ℝ := fun t => (projIcc 0 1 zero_le_one t : ℝ)
  have hθ : Continuous θ := continuous_subtype_val.comp continuous_projIcc
  have hθmem : ∀ t, θ t ∈ Icc (0 : ℝ) 1 := fun t => (projIcc 0 1 zero_le_one t).2
  let Q : ℝ → State (d + 1) → State (d + 1) := fun t q =>
    Fin.cons (η + (θ t : ℂ) * (q 0 - η)) (Fin.tail q)
  have hQ : Continuous (Function.uncurry Q) := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_const.add ((Complex.continuous_ofReal.comp (hθ.comp continuous_fst)).mul
        (((continuous_apply 0).comp continuous_snd).sub continuous_const))
    · change Continuous (fun p : ℝ × State (d + 1) => p.2 j.succ)
      exact (continuous_apply j.succ).comp continuous_snd
  have hQa : ∀ t, AnalyticOnNhd ℂ (Q t) V := by
    intro t q _
    apply AnalyticAt.pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact analyticAt_const.add (analyticAt_const.mul
        ((ContinuousLinearMap.proj (R := ℂ) 0).analyticAt q |>.sub analyticAt_const))
    · exact (ContinuousLinearMap.proj (R := ℂ) j.succ).analyticAt q
  have hmap : ∀ t, MapsTo (Q t) V V := fun t q hq => hstar q hq (θ t) (hθmem t)
  have hint : CoordinateHolomorphicOn V (fun q => ∫ t in (0 : ℝ)..1, g (Q t q)) := by
    apply coordinateHolomorphicOn_intervalIntegral hV
    · exact hg.continuousOn.comp hQ.continuousOn (fun q hq => hmap q.1 hq.2)
    · intro t
      exact coordinateHolomorphicOn_comp hg
        (coordinateHolomorphicOn_of_analyticOnNhd hV (hQa t)) hV (hmap t)
  apply coordinateHolomorphicOn_of_continuous_lineAnalytic hV
  · have hscalar : Continuous (fun q : State (d + 1) => q 0 - η) :=
      (continuous_apply 0).sub continuous_const
    have hc := hscalar.continuousOn.smul hint.continuousOn
    apply hc.congr
    intro q _
    dsimp [radialPrimitive]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp [Q, θ]
    rw [projIcc_of_mem zero_le_one (by simpa using ht)]
  · intro a v z hz
    have hs : AnalyticAt ℂ (fun t => affineLine a v t 0 - η) z :=
      (((ContinuousLinearMap.proj (R := ℂ) 0).analyticAt _).comp
        (analyticAt_affineLine a v z)).sub analyticAt_const
    apply (hs.smul ((hint.analyticOnNhd_affineLine a v) z hz)).congr
    apply Filter.Eventually.of_forall
    intro t
    dsimp [Function.comp_def, radialPrimitive]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp [Q, θ]
    rw [projIcc_of_mem zero_le_one (by simpa using hs)]

/-- Uniform bounds for the integrand give the expected segment-length
bound for the primitive, including at the initial time. -/
theorem norm_radialPrimitive_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {g : ℂ → E} {η z : ℂ} {M : ℝ}
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖g (η + (t : ℂ) * (z - η))‖ ≤ M) :
    ‖radialPrimitive g η z‖ ≤ ‖z - η‖ * M := by
  rw [radialPrimitive, norm_smul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := M)
    (f := fun t : ℝ => g (η + (t : ℂ) * (z - η)))
    (fun t ht => hb t (by simpa only [uIcc_of_le zero_le_one] using
      (uIoc_subset_uIcc ht : t ∈ uIcc (0 : ℝ) 1)))
  simpa only [sub_zero, abs_one, mul_one] using hi

/-- The radial primitive is jointly holomorphic on any open domain stable
under contraction of its first coordinate towards the varying initial time.
Other coordinates are independent complex variables throughout. -/
theorem coordinateHolomorphicOn_movingRadialPrimitive {d n : ℕ}
    {V : Set (State (d + 2))} {g : State (d + 2) → State n}
    (hV : IsOpen V) (hg : CoordinateHolomorphicOn V g) 
    (hstar : ∀ q ∈ V, ∀ t ∈ Icc (0 : ℝ) 1,
      Fin.cons ((Fin.tail q 0) + (t : ℂ) * (q 0 - (Fin.tail q 0))) (Fin.tail q) ∈ V) :
    CoordinateHolomorphicOn V (fun q =>
      radialPrimitive (fun z => g (Fin.cons z (Fin.tail q))) (Fin.tail q 0) (q 0)) := by
  let θ : ℝ → ℝ := fun t => (projIcc 0 1 zero_le_one t : ℝ)
  have hθ : Continuous θ := continuous_subtype_val.comp continuous_projIcc
  have hθmem : ∀ t, θ t ∈ Icc (0 : ℝ) 1 := fun t => (projIcc 0 1 zero_le_one t).2
  let Q : ℝ → State (d + 2) → State (d + 2) := fun t q =>
    Fin.cons ((Fin.tail q 0) + (θ t : ℂ) * (q 0 - (Fin.tail q 0))) (Fin.tail q)
  have hQ : Continuous (Function.uncurry Q) := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (((continuous_apply 1).comp continuous_snd)).add ((Complex.continuous_ofReal.comp (hθ.comp continuous_fst)).mul
        (((continuous_apply 0).comp continuous_snd).sub ((continuous_apply 1).comp continuous_snd)))
    · change Continuous (fun p : ℝ × State (d + 2) => p.2 j.succ)
      exact (continuous_apply j.succ).comp continuous_snd
  have hQa : ∀ t, AnalyticOnNhd ℂ (Q t) V := by
    intro t q _
    apply AnalyticAt.pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ((ContinuousLinearMap.proj (R := ℂ) 1).analyticAt q).add (analyticAt_const.mul
        ((ContinuousLinearMap.proj (R := ℂ) 0).analyticAt q |>.sub ((ContinuousLinearMap.proj (R := ℂ) 1).analyticAt q)))
    · exact (ContinuousLinearMap.proj (R := ℂ) j.succ).analyticAt q
  have hmap : ∀ t, MapsTo (Q t) V V := fun t q hq => hstar q hq (θ t) (hθmem t)
  have hint : CoordinateHolomorphicOn V (fun q => ∫ t in (0 : ℝ)..1, g (Q t q)) := by
    apply coordinateHolomorphicOn_intervalIntegral hV
    · exact hg.continuousOn.comp hQ.continuousOn (fun q hq => hmap q.1 hq.2)
    · intro t
      exact coordinateHolomorphicOn_comp hg
        (coordinateHolomorphicOn_of_analyticOnNhd hV (hQa t)) hV (hmap t)
  apply coordinateHolomorphicOn_of_continuous_lineAnalytic hV
  · have hscalar : Continuous (fun q : State (d + 2) => q 0 - (Fin.tail q 0)) :=
      (continuous_apply 0).sub (continuous_apply 1)
    have hc := hscalar.continuousOn.smul hint.continuousOn
    apply hc.congr
    intro q _
    dsimp [radialPrimitive]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp [Q, θ]
    rw [projIcc_of_mem zero_le_one (by simpa using ht)]
  · intro a v z hz
    have hs : AnalyticAt ℂ (fun t => affineLine a v t 0 - Fin.tail (affineLine a v t) 0) z :=
      (((ContinuousLinearMap.proj (R := ℂ) 0).analyticAt _).comp
        (analyticAt_affineLine a v z)).sub
      (((ContinuousLinearMap.proj (R := ℂ) 1).analyticAt _).comp (analyticAt_affineLine a v z))
    apply (hs.smul ((hint.analyticOnNhd_affineLine a v) z hz)).congr
    apply Filter.Eventually.of_forall
    intro t
    dsimp [Function.comp_def, radialPrimitive]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp [Q, θ]
    rw [projIcc_of_mem zero_le_one (by simpa using hs)]


/-- A genuine product of terminal and initial time discs is stable under
radial segments when the initial time disc is no larger. -/
lemma movingProduct_radial_mem {n m : ℕ} {z₀ : ℂ} {w₀ : State n} {p₀ : State m}
    {a e b c : ℝ} (hea : e ≤ a) {q : MovingPoint n m}
    (hq : q ∈ movingProduct z₀ w₀ p₀ a e b c) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Fin.cons (Fin.tail q 0 + (t : ℂ) * (q 0 - Fin.tail q 0)) (Fin.tail q) ∈
      movingProduct z₀ w₀ p₀ a e b c := by
  refine ⟨?_, by simpa only [Fin.tail_cons] using hq.2⟩
  have hη : Fin.tail q 0 ∈ ball z₀ a := ball_subset_ball hea hq.2.1
  change Fin.tail q 0 + (t : ℂ) * (q 0 - Fin.tail q 0) ∈ ball z₀ a
  simpa only [AffineMap.lineMap_apply, Complex.real_smul, smul_eq_mul,
    vsub_eq_sub, vadd_eq_add, add_comm] using
    (convex_ball z₀ a).lineMap_mem hη hq.1 ht


namespace ComplexPicard
variable {K E : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

noncomputable def rangeMaps (w₀ : E) (R : ℝ) : Set C(K,E) :=
  {u | ∀ q, ‖u q - w₀‖ ≤ R}

lemma isClosed_rangeMaps (w₀ : E) (R : ℝ) : IsClosed (rangeMaps (K := K) w₀ R) := by
  simp only [rangeMaps, Set.ofPred_forall]
  apply isClosed_iInter
  intro q
  apply isClosed_le
  · exact ((continuous_eval_const q).sub continuous_const).norm
  · exact continuous_const

abbrev RangeMap (w₀ : E) (R : ℝ) := (rangeMaps (K := K) w₀ R)

noncomputable def integrand {w₀ : E} {R : ℝ}
    (ρ : ℝ × K → K) (hρ : Continuous ρ)
    (G : K × closedBall w₀ R → E) (hG : Continuous G)
    (u : RangeMap (K := K) w₀ R) (t : ℝ) : C(K,E) where
  toFun q := G (ρ (t,q), ⟨u.1 (ρ (t,q)), by simpa [mem_closedBall, dist_eq_norm] using u.2 (ρ (t,q))⟩)
  continuous_toFun := by
    apply hG.comp
    exact (hρ.comp (continuous_const.prodMk continuous_id)).prodMk
      ((u.1.continuous.comp (hρ.comp (continuous_const.prodMk continuous_id))).subtype_mk _)

lemma continuous_integrand {w₀ : E} {R : ℝ}
    (ρ : ℝ × K → K) (hρ : Continuous ρ)
    (G : K × closedBall w₀ R → E) (hG : Continuous G)
    (u : RangeMap (K := K) w₀ R) : Continuous (integrand ρ hρ G hG u) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply hG.comp
  exact hρ.prodMk ((u.1.continuous.comp hρ).subtype_mk _)

noncomputable def operator {w₀ : E} {R : ℝ}
    (X : C(K,E)) (c : C(K,ℂ))
    (ρ : ℝ × K → K) (hρ : Continuous ρ)
    (G : K × closedBall w₀ R → E) (hG : Continuous G)
    (u : RangeMap (K := K) w₀ R) : C(K,E) :=
  X + ⟨fun q => c q • (∫ t in (0:ℝ)..1, integrand ρ hρ G hG u t) q,
    c.continuous.smul (map_continuous _)⟩

lemma operator_apply {w₀ : E} {R : ℝ}
    (X : C(K,E)) (c : C(K,ℂ))
    (ρ : ℝ × K → K) (hρ : Continuous ρ)
    (G : K × closedBall w₀ R → E) (hG : Continuous G)
    (u : RangeMap (K := K) w₀ R) (q : K) :
    operator X c ρ hρ G hG u q = X q + c q •
      ∫ t in (0:ℝ)..1, integrand ρ hρ G hG u t q := by
  change X q + c q • ((∫ t in (0:ℝ)..1, integrand ρ hρ G hG u t) q) = _
  congr 2
  exact ((ContinuousMap.evalCLM ℝ (M := E) q).intervalIntegral_comp_comm
    ((continuous_integrand ρ hρ G hG u).intervalIntegrable 0 1)).symm

lemma operator_mem {w₀ : E} {R a b M : ℝ}
    (X : C(K,E)) (c : C(K,ℂ))
    (ρ : ℝ × K → K) (hρ : Continuous ρ)
    (G : K × closedBall w₀ R → E) (hG : Continuous G)
    (ha : 0 ≤ a) (_hM : 0 ≤ M)
    (hX : ∀ q, ‖X q - w₀‖ ≤ b) (hc : ∀ q, ‖c q‖ ≤ a)
    (hbound : ∀ q w, ‖G (q,w)‖ ≤ M) (hsmall : b + a * M ≤ R)
    (u : RangeMap (K := K) w₀ R) : operator X c ρ hρ G hG u ∈ rangeMaps w₀ R := by
  intro q
  rw [operator_apply]
  calc
    ‖X q + c q • (∫ t in (0:ℝ)..1, integrand ρ hρ G hG u t q) - w₀‖ ≤
        ‖X q - w₀‖ + ‖c q • (∫ t in (0:ℝ)..1, integrand ρ hρ G hG u t q)‖ := by
      convert norm_add_le (X q - w₀) (c q • (∫ t in (0:ℝ)..1, integrand ρ hρ G hG u t q)) using 1 <;> abel_nf
    _ ≤ b + a * M := by
      apply add_le_add (hX q)
      rw [norm_smul]
      apply mul_le_mul (hc q) _ (norm_nonneg _) ha
      simpa only [sub_zero, abs_one, mul_one] using
        intervalIntegral.norm_integral_le_of_norm_le_const
          (a := (0:ℝ)) (b := 1) (f := fun t => integrand ρ hρ G hG u t q)
          (fun t _ => by exact hbound (ρ (t,q)) _)
    _ ≤ R := hsmall

lemma operator_lipschitz {w₀ : E} {R a L : ℝ}
    (X : C(K,E)) (c : C(K,ℂ))
    (ρ : ℝ × K → K) (hρ : Continuous ρ)
    (G : K × closedBall w₀ R → E) (hG : Continuous G)
    (ha : 0 ≤ a) (hL : 0 ≤ L) (hc : ∀ q, ‖c q‖ ≤ a)
    (hLip : ∀ q u v, ‖G (q,u) - G (q,v)‖ ≤ L * ‖(u:E) - v‖)
    (u v : RangeMap (K := K) w₀ R) :
    ‖operator X c ρ hρ G hG u - operator X c ρ hρ G hG v‖ ≤
      (a * L) * ‖u.1 - v.1‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro q
  simp only [ContinuousMap.sub_apply, operator_apply]
  have hiu : IntervalIntegrable (fun t => integrand ρ hρ G hG u t q)
      MeasureTheory.volume 0 1 :=
    ((continuous_eval_const q).comp (continuous_integrand ρ hρ G hG u)).intervalIntegrable 0 1
  have hiv : IntervalIntegrable (fun t => integrand ρ hρ G hG v t q)
      MeasureTheory.volume 0 1 :=
    ((continuous_eval_const q).comp (continuous_integrand ρ hρ G hG v)).intervalIntegrable 0 1
  rw [add_sub_add_left_eq_sub, ← smul_sub, ← intervalIntegral.integral_sub hiu hiv]
  rw [norm_smul]
  rw [mul_assoc]
  apply mul_le_mul (hc q) _ (norm_nonneg _) ha
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (C := L * ‖u.1 - v.1‖)
    (f := fun t => integrand ρ hρ G hG u t q - integrand ρ hρ G hG v t q)
    (fun t _ => by
      apply (hLip (ρ (t,q)) _ _).trans
      exact mul_le_mul_of_nonneg_left
        (ContinuousMap.norm_coe_le_norm (u.1-v.1) (ρ (t,q))) hL)
  simpa only [sub_zero, abs_one, mul_one] using hi

/-- A Picard operator on a compact base has a fixed point preserving any
closed invariant regularity class. The state range is part of the constructed
Banach space, so every field evaluation stays in the controlled box. -/
theorem exists_fixedPoint {w₀ : E} {R a b M L : ℝ}
    (X : C(K,E)) (c : C(K,ℂ))
    (ρ : ℝ × K → K) (hρ : Continuous ρ)
    (G : K × closedBall w₀ R → E) (hG : Continuous G)
    (ha : 0 ≤ a) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hX : ∀ q, ‖X q - w₀‖ ≤ b) (hc : ∀ q, ‖c q‖ ≤ a)
    (hbound : ∀ q w, ‖G (q,w)‖ ≤ M)
    (hLip : ∀ q u v, ‖G (q,u) - G (q,v)‖ ≤ L * ‖(u:E) - v‖)
    (hsmall : b + a * M ≤ R) (hcontract : a * L < 1)
    (P : Set C(K,E)) (hP : IsClosed P) (hXP : X ∈ P)
    (hpres : ∀ u : RangeMap (K := K) w₀ R, u.1 ∈ P →
      operator X c ρ hρ G hG u ∈ P) :
    ∃ u : RangeMap (K := K) w₀ R, u.1 ∈ P ∧ operator X c ρ hρ G hG u = u.1 := by
  let S : Set C(K,E) := rangeMaps w₀ R ∩ P
  have hS : IsClosed S := (isClosed_rangeMaps w₀ R).inter hP
  let : CompleteSpace S := hS.isComplete.completeSpace_coe
  have hXR : X ∈ rangeMaps w₀ R := by
    intro q
    exact (hX q).trans ((le_add_of_nonneg_right (mul_nonneg ha hM)).trans hsmall)
  let : Nonempty S := ⟨⟨X, hXR, hXP⟩⟩
  let F : S → S := fun u =>
    ⟨operator X c ρ hρ G hG ⟨u.1,u.2.1⟩,
      operator_mem X c ρ hρ G hG ha hM hX hc hbound hsmall ⟨u.1,u.2.1⟩,
      hpres ⟨u.1,u.2.1⟩ u.2.2⟩
  have hF : ContractingWith ⟨a*L,mul_nonneg ha hL⟩ F := by
    constructor
    · exact hcontract
    · apply LipschitzWith.of_dist_le_mul
      intro u v
      simp only [Subtype.dist_eq, dist_eq_norm]
      change ‖operator X c ρ hρ G hG ⟨u.1,u.2.1⟩ -
          operator X c ρ hρ G hG ⟨v.1,v.2.1⟩‖ ≤ (a*L) * ‖u.1-v.1‖
      exact operator_lipschitz X c ρ hρ G hG ha hL hc hLip _ _
  let u := hF.fixedPoint F
  refine ⟨⟨u.1,u.2.1⟩,u.2.2,?_⟩
  exact congrArg Subtype.val hF.fixedPoint_isFixedPt

end ComplexPicard

/-- The natural centre in terminal-time, initial-time, initial-state and parameter coordinates. -/
def movingCenter {n m : ℕ} (z₀ : ℂ) (w₀ : State n) (p₀ : State m) : MovingPoint n m :=
  Fin.cons z₀ (fieldPoint z₀ w₀ p₀)

lemma norm_fieldPoint_sub_le {n m : ℕ} {z z₀ : ℂ} {w w₀ : State n} {p p₀ : State m}
    {r : ℝ} (hr : 0 ≤ r) (hz : ‖z-z₀‖ ≤ r) (hw : ‖w-w₀‖ ≤ r) (hp : ‖p-p₀‖ ≤ r) :
    ‖fieldPoint z w p - fieldPoint z₀ w₀ p₀‖ ≤ r := by
  apply (pi_norm_le_iff_of_nonneg hr).mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [fieldPoint] using hz
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simpa [fieldPoint] using (norm_le_pi_norm (w-w₀) k).trans hw
    · simpa [fieldPoint] using (norm_le_pi_norm (p-p₀) k).trans hp

lemma movingCoordinates_norm_le {n m : ℕ} {q : MovingPoint n m}
    {z₀ : ℂ} {w₀ : State n} {p₀ : State m} {r : ℝ}
    (hq : q ∈ closedBall (movingCenter z₀ w₀ p₀) r) :
    ‖q 0-z₀‖ ≤ r ∧ ‖Fin.tail q 0-z₀‖ ≤ r ∧
      ‖stateCoordinates (Fin.tail (Fin.tail q))-w₀‖ ≤ r ∧
      ‖parameterCoordinates (Fin.tail (Fin.tail q))-p₀‖ ≤ r := by
  rw [mem_closedBall_iff_norm] at hq
  have hfirst (i : Fin (n+m+2)) : ‖q i-movingCenter z₀ w₀ p₀ i‖ ≤ r :=
    (norm_le_pi_norm (q-movingCenter z₀ w₀ p₀) i).trans hq
  refine ⟨by simpa [movingCenter] using hfirst 0,
    by simpa [movingCenter, fieldPoint, Fin.tail] using hfirst (Fin.succ 0), ?_, ?_⟩
  · apply (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans hq)).mpr
    intro i
    simpa [stateCoordinates, movingCenter, fieldPoint, Fin.tail] using hfirst (Fin.succ (Fin.succ (Fin.castAdd m i)))
  · apply (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans hq)).mpr
    intro i
    simpa [parameterCoordinates, movingCenter, fieldPoint, Fin.tail] using hfirst (Fin.succ (Fin.succ (Fin.natAdd n i)))

lemma movingProduct_eq_ball {n m : ℕ} (z₀ : ℂ) (w₀ : State n) (p₀ : State m)
    {r : ℝ} (hr : 0 < r) :
    movingProduct z₀ w₀ p₀ r r r r = ball (movingCenter z₀ w₀ p₀) r := by
  ext q
  simp only [movingProduct, mem_ofPred_eq, mem_ball_iff_norm]
  constructor
  · rintro ⟨hz,hη,hw,hp⟩
    apply (pi_norm_lt_iff hr).mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [movingCenter] using hz
    · refine Fin.cases ?_ (fun k => ?_) j
      · simpa [movingCenter, fieldPoint, Fin.tail] using hη
      · refine Fin.addCases (fun k => ?_) (fun k => ?_) k
        · simpa [movingCenter, fieldPoint, stateCoordinates, Fin.tail] using
            (norm_le_pi_norm (stateCoordinates (Fin.tail (Fin.tail q))-w₀) k).trans_lt hw
        · simpa [movingCenter, fieldPoint, parameterCoordinates, Fin.tail] using
            (norm_le_pi_norm (parameterCoordinates (Fin.tail (Fin.tail q))-p₀) k).trans_lt hp
  · intro hq
    have hfirst (i : Fin (n+m+2)) : ‖q i-movingCenter z₀ w₀ p₀ i‖ < r :=
      (norm_le_pi_norm (q-movingCenter z₀ w₀ p₀) i).trans_lt hq
    refine ⟨by simpa [movingCenter] using hfirst 0,
      by simpa [movingCenter, fieldPoint, Fin.tail] using hfirst (Fin.succ 0), ?_, ?_⟩
    · apply (pi_norm_lt_iff hr).mpr
      intro i
      simpa [stateCoordinates, movingCenter, fieldPoint, Fin.tail] using hfirst (Fin.succ (Fin.succ (Fin.castAdd m i)))
    · apply (pi_norm_lt_iff hr).mpr
      intro i
      simpa [parameterCoordinates, movingCenter, fieldPoint, Fin.tail] using hfirst (Fin.succ (Fin.succ (Fin.natAdd n i)))

lemma coordinateHolomorphicOn_movingFieldMap {n m : ℕ}
    {V : Set (MovingPoint n m)} {u : MovingPoint n m → State n}
    (hV : IsOpen V) (hu : CoordinateHolomorphicOn V u) :
    CoordinateHolomorphicOn V (fun q => fieldPoint (q 0) (u q)
      (parameterCoordinates (Fin.tail (Fin.tail q)))) := by
  apply coordinateHolomorphicOn_of_continuous_lineAnalytic hV
  · apply continuousOn_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (continuous_apply 0).continuousOn
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simpa [fieldPoint, Function.comp_def] using ((continuous_apply k).comp_continuousOn hu.continuousOn)
      · simpa [fieldPoint, parameterCoordinates, Fin.tail] using (continuous_apply (Fin.succ (Fin.succ (Fin.natAdd n k)))).continuousOn (s := V)
  · intro a v z hz
    apply AnalyticAt.pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ((ContinuousLinearMap.proj (R:=ℂ) 0).analyticAt _).comp (analyticAt_affineLine a v z)
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simpa [fieldPoint, Function.comp_def] using ((ContinuousLinearMap.proj (R:=ℂ) k).analyticAt _).comp
          ((hu.analyticOnNhd_affineLine a v) z hz)
      · simpa [fieldPoint, parameterCoordinates, Fin.tail, Function.comp_def] using ((ContinuousLinearMap.proj (R:=ℂ) (Fin.succ (Fin.succ (Fin.natAdd n k)))).analyticAt _).comp
          (analyticAt_affineLine a v z)

/-- Radial interpolation changes only the terminal-time coordinate. -/
def movingSegment {n m : ℕ} (t : ℝ) (q : MovingPoint n m) : MovingPoint n m :=
  Fin.cons (Fin.tail q 0 + (t : ℂ)*(q 0-Fin.tail q 0)) (Fin.tail q)

lemma movingSegment_mem_closedBall {n m : ℕ} {q : MovingPoint n m}
    {z₀ : ℂ} {w₀ : State n} {p₀ : State m} {r : ℝ}
    (hq : q ∈ closedBall (movingCenter z₀ w₀ p₀) r) {t : ℝ} (ht : t ∈ Icc 0 1) :
    movingSegment t q ∈ closedBall (movingCenter z₀ w₀ p₀) r := by
  have hb := movingCoordinates_norm_le hq
  have hr : 0 ≤ r := (norm_nonneg _).trans hb.1
  rw [mem_closedBall_iff_norm] at hq ⊢
  apply (pi_norm_le_iff_of_nonneg hr).mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · have hmem := (convex_closedBall z₀ r).lineMap_mem
      (mem_closedBall_iff_norm.mpr hb.2.1) (mem_closedBall_iff_norm.mpr hb.1) ht
    simpa [movingSegment, movingCenter, AffineMap.lineMap_apply, Complex.real_smul,
      smul_eq_mul, vsub_eq_sub, vadd_eq_add, add_comm] using mem_closedBall_iff_norm.mp hmem
  · simpa [movingSegment, movingCenter, Fin.tail] using
      (norm_le_pi_norm (q-movingCenter z₀ w₀ p₀) j.succ).trans hq

lemma movingSegment_mem_ball {n m : ℕ} {q : MovingPoint n m}
    {z₀ : ℂ} {w₀ : State n} {p₀ : State m} {r : ℝ} (hr : 0 < r)
    (hq : q ∈ ball (movingCenter z₀ w₀ p₀) r) {t : ℝ} (ht : t ∈ Icc 0 1) :
    movingSegment t q ∈ ball (movingCenter z₀ w₀ p₀) r := by
  have hb : q ∈ movingProduct z₀ w₀ p₀ r r r r := (movingProduct_eq_ball z₀ w₀ p₀ hr).symm ▸ hq
  rw [mem_ball_iff_norm] at hq ⊢
  apply (pi_norm_lt_iff hr).mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · have hmem := (convex_ball z₀ r).lineMap_mem hb.2.1 hb.1 ht
    simpa [movingSegment, movingCenter, AffineMap.lineMap_apply, Complex.real_smul,
      smul_eq_mul, vsub_eq_sub, vadd_eq_add, add_comm] using mem_ball_iff_norm.mp hmem
  · simpa [movingSegment, movingCenter, Fin.tail] using
      (norm_le_pi_norm (q-movingCenter z₀ w₀ p₀) j.succ).trans_lt hq

noncomputable def movingRetraction {n m : ℕ} {z₀ : ℂ} {w₀ : State n} {p₀ : State m} {r : ℝ}
    (t : ℝ) (q : closedBall (movingCenter z₀ w₀ p₀) r) :
    closedBall (movingCenter z₀ w₀ p₀) r :=
  ⟨movingSegment (projIcc 0 1 zero_le_one t) q,
    movingSegment_mem_closedBall q.2 (projIcc 0 1 zero_le_one t).2⟩

lemma continuous_movingRetraction {n m : ℕ} {z₀ : ℂ} {w₀ : State n} {p₀ : State m} {r : ℝ} :
    Continuous (Function.uncurry (movingRetraction (n:=n) (m:=m) (z₀:=z₀) (w₀:=w₀) (p₀:=p₀) (r:=r))) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [movingSegment, Fin.cons_zero, Fin.tail]
    have hc (i : Fin (n+m+2)) : Continuous (fun a : ℝ × closedBall (movingCenter z₀ w₀ p₀) r => (a.2 : MovingPoint n m) i) :=
      (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)
    exact (hc (Fin.succ 0)).add ((Complex.continuous_ofReal.comp
      (continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst))).mul
      ((hc 0).sub (hc (Fin.succ 0))))
  · simp only [movingSegment, Fin.cons_succ, Fin.tail]
    exact (continuous_apply j.succ).comp (continuous_subtype_val.comp continuous_snd)


/-- The original data of the moving-time problem, in the canonical coordinates. -/
def movingPoint {n m : ℕ} (z η : ℂ) (ξ : State n) (p : State m) : MovingPoint n m :=
  Fin.cons z (fieldPoint η ξ p)

@[simp] lemma stateCoordinates_append {n m : ℕ} (ξ : State n) (p : State m) :
    stateCoordinates (Fin.append ξ p) = ξ := by
  ext i
  simp [stateCoordinates]

@[simp] lemma parameterCoordinates_append {n m : ℕ} (ξ : State n) (p : State m) :
    parameterCoordinates (Fin.append ξ p) = p := by
  ext i
  simp [parameterCoordinates]

@[simp] lemma movingPoint_coordinates {n m : ℕ} (q : MovingPoint n m) :
    movingPoint (q 0) (Fin.tail q 0) (stateCoordinates (Fin.tail (Fin.tail q)))
      (parameterCoordinates (Fin.tail (Fin.tail q))) = q := by
  ext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · rfl
  · rfl
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · simp [movingPoint, fieldPoint, stateCoordinates, Fin.tail]
    · simp [movingPoint, fieldPoint, parameterCoordinates, Fin.tail]

lemma analyticAt_movingPoint_slice {n m : ℕ} (η : ℂ) (ξ : State n) (p : State m) (z : ℂ) :
    AnalyticAt ℂ (fun t => movingPoint t η ξ p) z := by
  apply AnalyticAt.pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact analyticAt_id
  · exact analyticAt_const

lemma analyticAt_fieldPoint {n m : ℕ} {z : ℂ → ℂ} {w : ℂ → State n}
    {p : ℂ → State m} {a : ℂ} (hz : AnalyticAt ℂ z a)
    (hw : AnalyticAt ℂ w a) (hp : AnalyticAt ℂ p a) :
    AnalyticAt ℂ (fun t => fieldPoint (z t) (w t) (p t)) a := by
  apply AnalyticAt.pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hz
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa only [fieldPoint, Fin.cons_succ, Fin.append_left, Function.comp_def, ContinuousLinearMap.proj_apply] using
        ((ContinuousLinearMap.proj (R := ℂ) j).analyticAt _).comp hw
    · simpa only [fieldPoint, Fin.cons_succ, Fin.append_right, Function.comp_def, ContinuousLinearMap.proj_apply] using
        ((ContinuousLinearMap.proj (R := ℂ) j).analyticAt _).comp hp

/-- A jointly holomorphic fixed point of the radial integral equation gives
all differential identities and local germ uniqueness in the original domain. -/
theorem movingTimeConclusion_of_integral_fixedPoint {n m : ℕ}
    {U : Set (FieldPoint n m)} {f : FieldPoint n m → State n}
    (hU : IsOpen U) (hf : CoordinateHolomorphicOn U f)
    {z₀ : ℂ} {w₀ : State n} {p₀ : State m} {a e b c : ℝ}
    (ha : 0 < a) (he : 0 < e) (hea : e ≤ a) (hb : 0 < b) (hc : 0 < c)
    {u : MovingPoint n m → State n}
    (hu : CoordinateHolomorphicOn (movingProduct z₀ w₀ p₀ a e b c) u)
    (hgraph : ∀ q ∈ movingProduct z₀ w₀ p₀ a e b c,
      fieldPoint (q 0) (u q) (parameterCoordinates (Fin.tail (Fin.tail q))) ∈ U)
    (hfix : ∀ q ∈ movingProduct z₀ w₀ p₀ a e b c,
      u q = stateCoordinates (Fin.tail (Fin.tail q)) +
        radialPrimitive (fun t => f (fieldPoint t (u (Fin.cons t (Fin.tail q)))
          (parameterCoordinates (Fin.tail (Fin.tail q))))) (Fin.tail q 0) (q 0)) :
    MovingTimeConclusion U f z₀ w₀ p₀ := by
  let W : ℂ → ℂ → State n → State m → State n :=
    fun z η ξ p => u (movingPoint z η ξ p)
  refine ⟨a, e, b, c, ha, he, hea, hb, hc, W, ?_, ?_⟩
  · exact hu.congr (fun q _ => by simp [W])
  · intro η hη ξ hξ p hp
    have hηa : η ∈ ball z₀ a := ball_subset_ball hea hη
    have hmem : ∀ t ∈ ball z₀ a,
        movingPoint t η ξ p ∈ movingProduct z₀ w₀ p₀ a e b c := by
      intro t ht
      simpa [movingProduct, movingPoint, fieldPoint] using And.intro ht (And.intro hη (And.intro hξ hp))
    let g : ℂ → State n := fun t => f (fieldPoint t (W t η ξ p) p)
    have heq : ∀ t ∈ ball z₀ a,
        W t η ξ p = ξ + radialPrimitive g η t := by
      intro t ht
      simpa [W, movingPoint, fieldPoint, g] using hfix _ (hmem t ht)
    have hinit : W η η ξ p = ξ := by simpa using heq η hηa
    have hgf : DifferentiableOn ℂ g (ball z₀ a) := by
      intro t ht
      have hua := analyticAt_comp_coordinateHolomorphic hu
        (analyticAt_movingPoint_slice η ξ p t) (hmem t ht)
      have hga : AnalyticAt ℂ (fun z => fieldPoint z (W z η ξ p) p) t :=
        analyticAt_fieldPoint analyticAt_id hua analyticAt_const
      exact (analyticAt_comp_coordinateHolomorphic hf hga
        (by simpa [W, movingPoint, fieldPoint] using hgraph _ (hmem t ht))).differentiableAt.differentiableWithinAt
    have hsol : ∀ t ∈ ball z₀ a, fieldPoint t (W t η ξ p) p ∈ U ∧
        HasDerivAt (fun z => W z η ξ p) (f (fieldPoint t (W t η ξ p) p)) t := by
      intro t ht
      refine ⟨by simpa [W, movingPoint, fieldPoint] using hgraph _ (hmem t ht), ?_⟩
      have hder := (hasDerivAt_radialPrimitive_of_mem_ball hgf hηa ht).const_add ξ
      exact hder.congr_of_eventuallyEq
        (Filter.eventuallyEq_iff_exists_mem.mpr ⟨ball z₀ a, isOpen_ball.mem_nhds ht, heq⟩)
    refine ⟨hinit, hsol, ?_⟩
    intro V v hV hηV hvi hv
    exact solution_germ_unique hU hf hV isOpen_ball hηV hηa hv hsol (hvi.trans hinit.symm)


/-- Uniform radii can be chosen without excluding zero field or Lipschitz bounds. -/
lemma exists_small_picard_radius {δ : ℝ} (hδ : 0 < δ) (M L : NNReal) :
    ∃ a : ℝ, 0 < a ∧ a ≤ δ / 2 ∧ a + 2 * a * (M : ℝ) ≤ δ / 2 ∧
      2 * a * (L : ℝ) < 1 := by
  have hM : 0 ≤ (M : ℝ) := M.coe_nonneg
  have hL : 0 ≤ (L : ℝ) := L.coe_nonneg
  have hpos : 0 < min (δ / (2 * (1 + 2 * (M : ℝ))))
      (1 / (2 * ((L : ℝ) + 1))) := by positivity
  obtain ⟨a, ha, ham⟩ := exists_between hpos
  have hma : a * (2 * (1 + 2 * (M : ℝ))) < δ :=
    (lt_div_iff₀ (by positivity : 0 < 2 * (1 + 2 * (M : ℝ)))).mp
      (ham.trans_le (min_le_left _ _))
  have hla : a * (2 * ((L : ℝ) + 1)) < 1 :=
    (lt_div_iff₀ (by positivity : 0 < 2 * ((L : ℝ) + 1))).mp
      (ham.trans_le (min_le_right _ _))
  refine ⟨a, ha, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg ha.le hM]
  · nlinarith
  · nlinarith


/-- The abstract compact-space Picard map is exactly the straight-segment
complex integral at every point of its closed product. -/
theorem movingPicardOperator_apply {n m : ℕ}
    {z₀ : ℂ} {w₀ : State n} {p₀ : State m} {r R : ℝ}
    {f : FieldPoint n m → State n}
    (X : C(closedBall (movingCenter z₀ w₀ p₀) r, State n))
    (c : C(closedBall (movingCenter z₀ w₀ p₀) r, ℂ))
    (G : closedBall (movingCenter z₀ w₀ p₀) r × closedBall w₀ R → State n)
    (hG : Continuous G)
    (hX : ∀ q, X q = stateCoordinates (Fin.tail (Fin.tail q.1)))
    (hc : ∀ q, c q = q.1 0 - Fin.tail q.1 0)
    (hGval : ∀ q w, G (q,w) =
      f (fieldPoint (q.1 0) w (parameterCoordinates (Fin.tail (Fin.tail q.1)))))
    (u : ComplexPicard.RangeMap (K := closedBall (movingCenter z₀ w₀ p₀) r) w₀ R)
    (q : closedBall (movingCenter z₀ w₀ p₀) r) :
    ComplexPicard.operator X c (Function.uncurry movingRetraction)
      continuous_movingRetraction G hG u q =
      stateCoordinates (Fin.tail (Fin.tail q.1)) +
      radialPrimitive (fun z => f (fieldPoint z
        (compactExtension (closedBall (movingCenter z₀ w₀ p₀) r) u.1 (Fin.cons z (Fin.tail q.1)))
        (parameterCoordinates (Fin.tail (Fin.tail q.1))))) (Fin.tail q.1 0) (q.1 0) := by
  rw [ComplexPicard.operator_apply, hX, hc]
  dsimp only [radialPrimitive]
  congr 2
  apply intervalIntegral.integral_congr
  intro t ht
  have htI : t ∈ Icc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
  have hseg := movingSegment_mem_closedBall q.2 htI
  have hρ : movingRetraction t q = ⟨movingSegment t q.1,hseg⟩ := by
    apply Subtype.ext
    change movingSegment (projIcc 0 1 zero_le_one t) q.1 = movingSegment t q.1
    rw [projIcc_of_mem zero_le_one htI]
  simp only [ComplexPicard.integrand, ContinuousMap.coe_mk, Function.uncurry, hρ]
  rw [hGval]
  change f (fieldPoint ((movingSegment t q.1) 0)
    (u.1 ⟨movingSegment t q.1,hseg⟩)
    (parameterCoordinates (Fin.tail (Fin.tail (movingSegment t q.1))))) =
    f (fieldPoint ((movingSegment t q.1) 0)
      (compactExtension (closedBall (movingCenter z₀ w₀ p₀) r) u.1 (movingSegment t q.1))
      (parameterCoordinates (Fin.tail (Fin.tail (movingSegment t q.1)))))
  rw [compactExtension_apply _ hseg]

/-- The actual moving-time Picard operator preserves the exact coordinate
power-series regularity class; only its evaluations in the original field
are used. -/
theorem movingPicardOperator_holomorphic {n m : ℕ}
    {z₀ : ℂ} {w₀ : State n} {p₀ : State m} {r R : ℝ}
    (hr : 0 < r)
    {U : Set (FieldPoint n m)} {f : FieldPoint n m → State n}
    (hf : CoordinateHolomorphicOn U f)
    (hgraph : ∀ q ∈ closedBall (movingCenter z₀ w₀ p₀) r,
      ∀ w ∈ closedBall w₀ R,
      fieldPoint (q 0) w (parameterCoordinates (Fin.tail (Fin.tail q))) ∈ U)
    (X : C(closedBall (movingCenter z₀ w₀ p₀) r, State n))
    (c : C(closedBall (movingCenter z₀ w₀ p₀) r, ℂ))
    (G : closedBall (movingCenter z₀ w₀ p₀) r × closedBall w₀ R → State n)
    (hG : Continuous G)
    (hX : ∀ q, X q = stateCoordinates (Fin.tail (Fin.tail q.1)))
    (hc : ∀ q, c q = q.1 0 - Fin.tail q.1 0)
    (hGval : ∀ q w, G (q,w) =
      f (fieldPoint (q.1 0) w (parameterCoordinates (Fin.tail (Fin.tail q.1)))))
    (u : ComplexPicard.RangeMap (K := closedBall (movingCenter z₀ w₀ p₀) r) w₀ R)
    (hu : CoordinateHolomorphicOn (ball (movingCenter z₀ w₀ p₀) r)
      (compactExtension (closedBall (movingCenter z₀ w₀ p₀) r) u.1)) :
    CoordinateHolomorphicOn (ball (movingCenter z₀ w₀ p₀) r)
      (compactExtension (closedBall (movingCenter z₀ w₀ p₀) r)
        (ComplexPicard.operator X c (Function.uncurry movingRetraction)
          continuous_movingRetraction G hG u)) := by
  let K := closedBall (movingCenter z₀ w₀ p₀) r
  let V := ball (movingCenter z₀ w₀ p₀) r
  let g : MovingPoint n m → State n := fun q =>
    f (fieldPoint (q 0) (compactExtension K u.1 q)
      (parameterCoordinates (Fin.tail (Fin.tail q))))
  have hg : CoordinateHolomorphicOn V g := by
    apply coordinateHolomorphicOn_comp hf
      (coordinateHolomorphicOn_movingFieldMap isOpen_ball hu) isOpen_ball
    intro q hq
    have hqK : q ∈ K := ball_subset_closedBall hq
    have hw : u.1 ⟨q,hqK⟩ ∈ closedBall w₀ R :=
      mem_closedBall_iff_norm.mpr (u.2 _)
    change fieldPoint (q 0) (compactExtension K u.1 q)
      (parameterCoordinates (Fin.tail (Fin.tail q))) ∈ U
    rw [compactExtension_apply _ hqK]
    exact hgraph q hqK (u.1 ⟨q,hqK⟩) hw
  let X₀ : MovingPoint n m → State n :=
    fun q => stateCoordinates (Fin.tail (Fin.tail q))
  have hX₀ : CoordinateHolomorphicOn V X₀ := by
    apply coordinateHolomorphicOn_of_analyticOnNhd isOpen_ball
    intro q _
    apply AnalyticAt.pi
    intro i
    exact (ContinuousLinearMap.proj (R:=ℂ) (Fin.succ (Fin.succ (Fin.castAdd m i)))).analyticAt q
  have hprimitive := coordinateHolomorphicOn_movingRadialPrimitive isOpen_ball hg
    (fun q hq t ht => movingSegment_mem_ball hr hq ht)
  apply (hX₀.add hprimitive isOpen_ball).congr
  intro q hq
  have hqK : q ∈ K := ball_subset_closedBall hq
  rw [compactExtension_apply _ hqK, ComplexPicard.operator_apply, hX, hc]
  change X₀ q + radialPrimitive (fun z => g (Fin.cons z (Fin.tail q))) (Fin.tail q 0) (q 0) = _
  dsimp only [X₀, radialPrimitive]
  congr 2
  apply intervalIntegral.integral_congr
  intro t ht
  have htI : t ∈ Icc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
  have hseg : movingSegment t q ∈ K := movingSegment_mem_closedBall hqK htI
  have hρ : movingRetraction t ⟨q,hqK⟩ = ⟨movingSegment t q,hseg⟩ := by
    apply Subtype.ext
    change movingSegment (projIcc 0 1 zero_le_one t) q = movingSegment t q
    rw [projIcc_of_mem zero_le_one htI]
  simp only [ComplexPicard.integrand, ContinuousMap.coe_mk, Function.uncurry, hρ]
  rw [hGval]
  change g (movingSegment t q) = f (fieldPoint ((movingSegment t q) 0)
    (u.1 ⟨movingSegment t q,hseg⟩)
    (parameterCoordinates (Fin.tail (Fin.tail (movingSegment t q)))))
  dsimp only [g]
  rw [compactExtension_apply _ hseg]


lemma continuous_fieldPoint {A : Type*} [TopologicalSpace A] {n m : ℕ}
    {z : A → ℂ} {w : A → State n} {p : A → State m}
    (hz : Continuous z) (hw : Continuous w) (hp : Continuous p) :
    Continuous (fun a => fieldPoint (z a) (w a) (p a)) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hz
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simpa [fieldPoint, Function.comp_def] using (continuous_apply k).comp hw
    · simpa [fieldPoint, Function.comp_def] using (continuous_apply k).comp hp

lemma coordinateHolomorphicOn_movingInitial {n m : ℕ}
    {V : Set (MovingPoint n m)} (hV : IsOpen V) :
    CoordinateHolomorphicOn V (fun q => stateCoordinates (Fin.tail (Fin.tail q))) := by
  apply coordinateHolomorphicOn_of_analyticOnNhd hV
  intro q _
  apply AnalyticAt.pi
  intro i
  exact (ContinuousLinearMap.proj (R:=ℂ) (Fin.succ (Fin.succ (Fin.castAdd m i)))).analyticAt q

/-- A bounded Lipschitz holomorphic field on a controlled ball has a jointly
holomorphic family on a small genuine product of complex neighborhoods. -/
theorem movingTimeConclusion_of_bounds {n m : ℕ}
    {U : Set (FieldPoint n m)} {f : FieldPoint n m → State n}
    {z₀ : ℂ} {w₀ : State n} {p₀ : State m}
    (hU : IsOpen U) (hf : CoordinateHolomorphicOn U f)
    {δ R a : ℝ} {M L : NNReal}
    (ha : 0 < a) (haR : a ≤ R) (hRδ : R < δ)
    (hδU : ball (fieldPoint z₀ w₀ p₀) δ ⊆ U)
    (hbound : ∀ q ∈ ball (fieldPoint z₀ w₀ p₀) δ, ‖f q‖ ≤ (M : ℝ))
    (hLip : LipschitzOnWith L f (ball (fieldPoint z₀ w₀ p₀) δ))
    (hsmall : a + 2*a*(M : ℝ) ≤ R) (hcontract : 2*a*(L : ℝ) < 1) :
    MovingTimeConclusion U f z₀ w₀ p₀ := by
  classical
  let K := closedBall (movingCenter z₀ w₀ p₀) a
  let V := ball (movingCenter z₀ w₀ p₀) a
  have hK : IsCompact K := isCompact_closedBall _ _
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hV : IsOpen V := isOpen_ball
  have hVK : V ⊆ K := ball_subset_closedBall
  have hR : 0 ≤ R := ha.le.trans haR
  let X : C(K, State n) := ⟨fun q => stateCoordinates (Fin.tail (Fin.tail q.val)),
    (continuous_stateCoordinates n m).comp ((continuous_finTail _).comp
      ((continuous_finTail _).comp continuous_subtype_val))⟩
  let c : C(K, ℂ) := ⟨fun q => q.val 0 - Fin.tail q.val 0,
    ((continuous_apply 0).comp continuous_subtype_val).sub
      ((continuous_apply 1).comp continuous_subtype_val)⟩
  let ρ : ℝ × K → K := Function.uncurry movingRetraction
  have hρ : Continuous ρ := continuous_movingRetraction
  let G : K × closedBall w₀ R → State n := fun qw =>
    f (fieldPoint (qw.1.val 0) qw.2.val (parameterCoordinates (Fin.tail (Fin.tail qw.1.val))))
  have hgraph (q : K) (w : closedBall w₀ R) :
      fieldPoint (q.val 0) w.val (parameterCoordinates (Fin.tail (Fin.tail q.val))) ∈
        ball (fieldPoint z₀ w₀ p₀) δ := by
    have hq := movingCoordinates_norm_le q.2
    apply mem_ball_iff_norm.mpr
    apply lt_of_le_of_lt _ hRδ
    exact norm_fieldPoint_sub_le hR (hq.1.trans haR)
      (mem_closedBall_iff_norm.mp w.2) (hq.2.2.2.trans haR)
  have hG : Continuous G := by
    apply hf.continuousOn.comp_continuous
      (continuous_fieldPoint ((continuous_apply 0).comp (continuous_subtype_val.comp continuous_fst))
        (continuous_subtype_val.comp continuous_snd) ?_)
      (fun qw => hδU (hgraph qw.1 qw.2))
    apply continuous_pi
    intro i
    exact (continuous_apply (Fin.succ (Fin.succ (Fin.natAdd n i)))).comp
      (continuous_subtype_val.comp continuous_fst)
  have hX : ∀ q, ‖X q - w₀‖ ≤ a := fun q => (movingCoordinates_norm_le q.2).2.2.1
  have hc : ∀ q, ‖c q‖ ≤ 2*a := by
    intro q
    have hq := movingCoordinates_norm_le q.2
    calc
      ‖c q‖ ≤ ‖q.val 0-z₀‖+‖Fin.tail q.val 0-z₀‖ := by
        dsimp [c]
        simpa only [norm_sub_rev z₀ (Fin.tail q.val 0)] using
          norm_sub_le_norm_sub_add_norm_sub (q.val 0) z₀ (Fin.tail q.val 0)
      _ ≤ a+a := add_le_add hq.1 hq.2.1
      _ = 2*a := by ring
  have hGb : ∀ q w, ‖G (q,w)‖ ≤ (M:ℝ) := fun q w => hbound _ (hgraph q w)
  have hGL : ∀ q u v, ‖G (q,u)-G (q,v)‖ ≤ (L:ℝ)*‖u.val-v.val‖ := by
    intro q u v
    exact (hLip.norm_sub_le (hgraph q u) (hgraph q v)).trans
      (mul_le_mul_of_nonneg_left (norm_fieldPoint_state_sub_le (q.val 0) u.val v.val
        (parameterCoordinates (Fin.tail (Fin.tail q.val)))) L.property)
  let P : Set C(K, State n) := {u | CoordinateHolomorphicOn V (compactExtension K u)}
  have hP : IsClosed P := isClosed_coordinateHolomorphic_compactExtension hK hV hVK
  have hXP : X ∈ P := by
    apply (coordinateHolomorphicOn_movingInitial hV).congr
    intro q hq
    rw [compactExtension_apply _ (hVK hq)]
    rfl
  have hpres : ∀ u : ComplexPicard.RangeMap (K:=K) w₀ R, u.val ∈ P →
      ComplexPicard.operator X c ρ hρ G hG u ∈ P := by
    intro u hu
    exact movingPicardOperator_holomorphic ha hf
      (fun q hq w hw => hδU (hgraph ⟨q,hq⟩ ⟨w,hw⟩))
      X c G hG (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) u hu
  obtain ⟨u, hu, hfix⟩ := ComplexPicard.exists_fixedPoint X c ρ hρ G hG
    (by positivity : 0 ≤ 2*a) M.property L.property hX hc hGb hGL hsmall hcontract P hP hXP hpres
  apply movingTimeConclusion_of_integral_fixedPoint hU hf ha ha le_rfl ha ha
    (u := compactExtension K u.val)
  · exact (movingProduct_eq_ball z₀ w₀ p₀ ha).symm ▸ hu
  · intro q hq
    have hqK := hVK ((movingProduct_eq_ball z₀ w₀ p₀ ha) ▸ hq)
    rw [compactExtension_apply _ hqK]
    exact hδU (hgraph ⟨q,hqK⟩ ⟨u.val ⟨q,hqK⟩, mem_closedBall_iff_norm.mpr (u.2 _)⟩)
  · intro q hq
    have hqV : q ∈ V := by change q ∈ ball (movingCenter z₀ w₀ p₀) a; rwa [← movingProduct_eq_ball z₀ w₀ p₀ ha]
    have hqK : q ∈ K := hVK hqV
    have hpoint := congrArg (fun F : C(K, State n) => F ⟨q,hqK⟩) hfix
    rw [ComplexPicard.operator_apply] at hpoint
    rw [compactExtension_apply _ hqK]
    apply hpoint.symm.trans
    change X ⟨q,hqK⟩ + c ⟨q,hqK⟩ • _ = _
    dsimp only [X, ContinuousMap.coe_mk]
    congr 1
    dsimp only [c, ContinuousMap.coe_mk, radialPrimitive]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
    have hsegK : movingSegment t q ∈ K := movingSegment_mem_closedBall hqK ht'
    have hρt : ρ (t,⟨q,hqK⟩) = ⟨movingSegment t q,hsegK⟩ := by
      apply Subtype.ext
      change movingSegment (projIcc 0 1 zero_le_one t) q = movingSegment t q
      rw [projIcc_of_mem zero_le_one ht']
    simp only [ComplexPicard.integrand, ContinuousMap.coe_mk, hρt]
    dsimp only [G]
    change f (fieldPoint (movingSegment t q 0) (u.val ⟨movingSegment t q,hsegK⟩)
      (parameterCoordinates (Fin.tail (Fin.tail (movingSegment t q))))) =
      f (fieldPoint (movingSegment t q 0) (compactExtension K u.val (movingSegment t q))
      (parameterCoordinates (Fin.tail (Fin.tail (movingSegment t q)))))
    rw [compactExtension_apply _ hsegK]


/-- The source theorem, with complex initial time allowed to vary on an
actual product neighborhood; its fixed-time form follows by restriction. -/
theorem holomorphic_dependence :
    Specs.D13Unified.Ch06.HolomorphicDependence.holomorphic_dependence_type := by
  intro n m U f z₀ w₀ p₀ hU h₀ hf
  obtain ⟨δ, hδ, hδU, M, L, hbound, hLip⟩ := exists_local_bound_lipschitz hU hf h₀
  obtain ⟨a, ha, haR, hsmall, hcontract⟩ := exists_small_picard_radius hδ M L
  have hmoving : MovingTimeConclusion U f z₀ w₀ p₀ :=
    movingTimeConclusion_of_bounds hU hf ha haR (half_lt_self hδ) hδU hbound hLip
      hsmall hcontract
  exact ⟨fixedTimeConclusion_of_movingTimeConclusion hmoving, hmoving⟩

end D13Unified.Ch06.HolomorphicDependence
