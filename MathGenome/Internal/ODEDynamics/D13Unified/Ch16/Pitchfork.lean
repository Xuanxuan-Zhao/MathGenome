import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.Pitchfork
import MathGenome.Internal.ODEDynamics.D13Unified.Ch16.SimplePersistence
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Asymptotics.Prod
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The symmetric pitchfork theorem and its squared-state reduction.
The analytic helpers retain the actual parameter and state derivatives. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace D13Unified.Ch16.Pitchfork
open Specs.D13Unified.Ch16.SimplePersistence
open Specs.D13Unified.Ch16.Pitchfork

/-- Odd symmetry retains the zero equilibrium before any division. -/
theorem zero_of_oddOn {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (ho : OddOn f U) {μ : ℝ} (hμ : (μ,0) ∈ U) : f (μ,0) = 0 := by
  have h := ho μ 0 hμ (by simpa using hμ)
  simp only [neg_zero] at h
  linarith

/-- The desingularized quotient has an exact factorization, including x=0. -/
theorem factor_dslope (g : ℝ → ℝ) (h0 : g 0 = 0) (x : ℝ) :
    g x = x * dslope g 0 x := by
  simpa only [sub_zero, smul_eq_mul, h0] using (sub_smul_dslope g 0 x).symm

/-- Oddness of the original family yields evenness of its quotient. This
identity needs no differentiability away from the chosen value at zero. -/
theorem dslope_even {g : ℝ → ℝ} (ho : Function.Odd g) :
    Function.Even (dslope g 0) := by
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · have h0 : g 0 = 0 := by
      have h := ho 0
      simp only [neg_zero] at h
      linarith
    simp [dslope_of_ne _ hx, dslope_of_ne _ (neg_ne_zero.mpr hx), slope_def_field,
      ho x, h0]

/-- Counting the roots of a squared-state equation does not use an
asymptotic normal form: the equation is exact. -/
theorem square_eq_iff (x t : ℝ) (ht : 0 ≤ t) :
    x^2 = t ↔ x = Real.sqrt t ∨ x = -Real.sqrt t := by
  constructor
  · intro hx
    have hs := Real.sq_sqrt ht
    have : (x - Real.sqrt t) * (x + Real.sqrt t) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  · rintro (rfl | rfl) <;> simpa using Real.sq_sqrt ht

/-- The root zero is retained, and the nonzero roots occur precisely when
the squared amplitude is positive. -/
theorem zero_or_square_eq_iff (x t : ℝ) :
    (x = 0 ∨ x^2 = t) ↔
      x = 0 ∨ (0 < t ∧ (x = Real.sqrt t ∨ x = -Real.sqrt t)) := by
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hx : x = 0
      · exact Or.inl hx
      · have ht : 0 < t := by rw [← h]; exact sq_pos_of_ne_zero hx
        exact Or.inr ⟨ht, (square_eq_iff x t ht.le).mp h⟩
  · rintro (h | ⟨ht,h⟩)
    · exact Or.inl h
    · exact Or.inr ((square_eq_iff x t ht.le).mpr h)

/-- A differentiable curve through zero with nonzero derivative has its
predicted sign on both sides, in one fixed neighborhood. -/
theorem sign_near_simple_zero {g : ℝ → ℝ} {c : ℝ}
    (h0 : g 0 = 0) (hg : HasDerivAt g c 0) (hc : c ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ μ ∈ Metric.ball 0 ε, μ ≠ 0 → 0 < g μ * (c*μ) := by
  have hcont : ContinuousAt (fun μ => dslope g 0 μ * c) 0 :=
    (continuousAt_dslope_same.mpr hg.differentiableAt).mul continuousAt_const
  have hpos : 0 < dslope g 0 0 * c := by
    rw [dslope_same, hg.deriv]
    exact mul_self_pos.mpr hc
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp (hcont (isOpen_Ioi.mem_nhds hpos))
  refine ⟨ε,hε,fun μ hμ hn => ?_⟩
  have hp : 0 < dslope g 0 μ * c := hball (by simpa [Metric.mem_ball] using hμ)
  rw [factor_dslope g h0 μ]
  have ht := mul_pos hp (sq_pos_of_ne_zero hn)
  nlinarith [ht]

/-- Differentiating in the state loses one order of regularity, on the
same open domain, with the actual Fréchet derivative. -/
theorem stateDerivative_contDiffOn {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    {m n : ℕ∞ω} (hU : IsOpen U) (hf : ContDiffOn ℝ n f U) (hmn : m+1 ≤ n) :
    ContDiffOn ℝ m (stateDerivative f) U :=
  (hf.fderiv_of_isOpen hU hmn).clm_apply contDiffOn_const

/-- The original hypotheses already determine the type of the persistent
zero branch; the nonzero branches require the squared-state reduction. -/
theorem zero_branch_sign {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (h00 : (0,0) ∈ U) (hf : ContDiffOn ℝ 5 f U)
    (hx : stateDerivative f (0,0) = 0) (ha : mixedCoefficient f ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ μ ∈ Metric.ball 0 ε, μ ≠ 0 →
      0 < stateDerivative f (μ,0) * (mixedCoefficient f * μ) := by
  have hs : ContDiffOn ℝ 4 (stateDerivative f) U :=
    stateDerivative_contDiffOn hU hf (by norm_num)
  have hd := ((hs (0,0) h00).contDiffAt (hU.mem_nhds h00)).differentiableAt
    (by norm_num)
  have hp : HasDerivAt (fun μ : ℝ => ((μ,0) : ℝ × ℝ)) (1,0) 0 :=
    (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have hd' : HasDerivAt (fun μ => stateDerivative f (μ,0)) (mixedCoefficient f) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hp rfl
  exact sign_near_simple_zero hx hd' ha

/-- Differentiate an actual zero graph. The equation is locally zero on an
open interval, and the linear derivative is decomposed in the two coordinates. -/
theorem zero_graph_derivative {H : ℝ × ℝ → ℝ} {V : Set (ℝ × ℝ)}
    {s : ℝ → ℝ} {α β a b : ℝ}
    (hV : IsOpen V) (hH : ContDiffOn ℝ 1 H V)
    (hgraph : IsLocalZeroGraph H V s α β)
    (ha : fderiv ℝ H (0,0) (1,0) = a)
    (hb : stateDerivative H (0,0) = b) (hbn : b ≠ 0) :
    HasDerivAt s (-a/b) 0 := by
  rcases hgraph with ⟨hα,hβ,hs0,hbox,hs,hroot⟩
  have hα0 : (0 : ℝ) ∈ Metric.ball 0 α := Metric.mem_ball_self hα
  have hβ0 : (0 : ℝ) ∈ Metric.ball 0 β := Metric.mem_ball_self hβ
  have h00 : (0,0) ∈ V := hbox ⟨hα0,hβ0⟩
  have hsd : HasDerivAt s (deriv s 0) 0 :=
    ((hs 0 hα0).contDiffAt (Metric.ball_mem_nhds 0 hα)).differentiableAt (by simp) |>.hasDerivAt
  have hHd : HasFDerivAt H (fderiv ℝ H (0,0)) (0,0) :=
    ((hH (0,0) h00).contDiffAt (hV.mem_nhds h00)).differentiableAt (by simp) |>.hasFDerivAt
  have hpair : HasDerivAt (fun μ : ℝ => (μ,s μ)) (1,deriv s 0) 0 :=
    (hasDerivAt_id (0 : ℝ)).prodMk hsd
  have hd := hHd.comp_hasDerivAt_of_eq 0 hpair (by simp [hs0])
  have heq : (fun μ => H (μ,s μ)) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [Metric.ball_mem_nhds 0 hα] with μ hμ
    exact ((hroot μ hμ).2 (s μ) (hroot μ hμ).1).mpr rfl
  have hz : fderiv ℝ H (0,0) (1,deriv s 0) = 0 :=
    (hd.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const 0 0)
  have hlin : fderiv ℝ H (0,0) (1,deriv s 0) = a + deriv s 0 * b := by
    have hp : (1,deriv s 0) = ((1,0) : ℝ × ℝ) + deriv s 0 • ((0,1) : ℝ × ℝ) := by ext <;> simp
    rw [hp, map_add, map_smul, ha]
    change a + deriv s 0 * stateDerivative H (0,0) = _
    rw [hb]
  have hs' : deriv s 0 = -a/b := by
    apply (eq_div_iff hbn).mpr
    linarith [hz,hlin]
  rwa [hs'] at hsd

/-- The allowed persistence premise supplies the implicit squared-amplitude
curve once its C¹ equation and the two partial derivatives have been proved.
This does not assume the original pitchfork conclusion. -/
theorem reduced_equation_graph
    (hpersist : Specs.D13Unified.Ch16.SimplePersistence.flowPersistence)
    (H : ℝ × ℝ → ℝ) (V : Set (ℝ × ℝ))
    (hV : IsOpen V) (h00 : (0,0) ∈ V) (hH : ContDiffOn ℝ 1 H V)
    (hzero : H (0,0) = 0) (a b : ℝ)
    (ha : fderiv ℝ H (0,0) (1,0) = a)
    (hb : stateDerivative H (0,0) = b) (hbn : b ≠ 0) :
    ∃ s : ℝ → ℝ, ∃ α β : ℝ,
      IsLocalZeroGraph H V s α β ∧ HasDerivAt s (-a/b) 0 := by
  obtain ⟨s,α,β,hg,_⟩ := hpersist H V hV h00 hH hzero (by simpa [hb] using hbn)
  exact ⟨s,α,β,hg,zero_graph_derivative hV hH hg ha hb hbn⟩

/-- Transfer the supplied scalar-flow test to any simple equilibrium of
an actual family slice, retaining exactly its original shifted domain. -/
theorem scalar_stability_at
    (hscalar : Specs.D13Unified.Ch16.SimplePersistence.scalarFlowStability)
    (hslice : Specs.D13Unified.Ch16.SimplePersistence.stateDerivativeSlice)
    {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    {μ p : ℝ} (hp : (μ,p) ∈ U) (heq : f (μ,p) = 0) :
    ScalarStabilityAt f U μ p := by
  let V : Set ℝ := {y | (μ,p+y) ∈ U}
  let g : ℝ → ℝ := fun y => f (μ,p+y)
  have hV : IsOpen V := hU.preimage
    (continuous_const.prodMk (continuous_const.add continuous_id))
  have hg : ContDiffOn ℝ 1 g V := hf.comp
    (contDiffOn_const.prodMk (contDiffOn_const.add contDiffOn_id)) (fun _ h => h)
  let F : _root_.D13Unified.AutonomousODE ℝ :=
    { domain := V
      isOpen_domain := hV
      field := fun y => g y
      continuous_field := hg.continuousOn.domRestrict }
  have heval : ∀ y ∈ V,
      Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue F y = g y := by
    intro y hy
    simp [Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue, F, hy]
  have hF : ContDiffOn ℝ 1
      (Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue F) F.domain :=
    hg.congr heval
  have h0 : (0 : ℝ) ∈ F.domain := by simpa [F,V] using hp
  have heqF : Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue F 0 = 0 := by
    rw [heval 0 h0]
    simpa [g] using heq
  have hdf := ((hf (μ,p) hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hds := hslice f (μ,p) hdf
  have hshift : HasDerivAt (fun y : ℝ => p+y) 1 0 := by
    convert (hasDerivAt_const (0 : ℝ) p).add (hasDerivAt_id (0 : ℝ)) using 1 <;> first | rfl | simp
  have hdg : HasDerivAt g (stateDerivative f (μ,p)) 0 := by
    convert hds.comp_of_eq 0 hshift (by simp) using 1 <;> first | rfl | simp
  have hdF : deriv (Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue F) 0 =
      stateDerivative f (μ,p) := by
    apply HasDerivAt.deriv
    exact hdg.congr_of_eventuallyEq
      (Filter.eventually_of_mem (hV.mem_nhds h0) fun y hy => heval y hy)
  refine ⟨F,rfl,heval,hF,h0,heqF,?_,?_⟩
  · simpa only [hdF] using (hscalar F hF h0 heqF).1
  · simpa only [hdF] using (hscalar F hF h0 heqF).2

/-- Differentiate the exact squared-state factorization at any admissible
point. Both partial derivatives are checked by the supplied slice premise. -/
theorem stateDerivative_of_factor
    (hslice : Specs.D13Unified.Ch16.SimplePersistence.stateDerivativeSlice)
    {f H : ℝ × ℝ → ℝ} {μ x : ℝ}
    (hdf : DifferentiableAt ℝ f (μ,x))
    (hdH : DifferentiableAt ℝ H (μ,x^2))
    (hfactor : (fun y => f (μ,y)) =ᶠ[𝓝 x] fun y => y * H (μ,y^2)) :
    stateDerivative f (μ,x) = H (μ,x^2) + 2*x^2*stateDerivative H (μ,x^2) := by
  have hh : HasDerivAt (fun y => H (μ,y^2))
      (stateDerivative H (μ,x^2) * (2*x)) x := by
    convert (hslice H (μ,x^2) hdH).comp_of_eq x ((hasDerivAt_id x).pow 2) rfl using 1 <;>
      first | rfl | simp
  have hprod := (hasDerivAt_id x).mul hh
  have hder := hprod.congr_of_eventuallyEq hfactor
  have heq := (hslice f (μ,x) hdf).unique hder
  dsimp only [id_eq] at heq
  linarith only [heq]

/-- Pointwise passage from the reduced zero graph to all original roots.
No root is lost through division by the state. -/
theorem zeros_of_reduction {f H : ℝ × ℝ → ℝ} {μ x t : ℝ}
    (hfactor : f (μ,x) = x * H (μ,x^2)) (hroot : H (μ,x^2) = 0 ↔ x^2 = t) :
    f (μ,x) = 0 ↔ x = 0 ∨ (0 < t ∧ (x = Real.sqrt t ∨ x = -Real.sqrt t)) := by
  rw [hfactor, mul_eq_zero, hroot, zero_or_square_eq_iff]

/-- Two strict sign products can be composed, including the case in which
all the factors are negative. -/
theorem same_sign_trans {d b c : ℝ} (hdb : 0 < d*b) (hbc : 0 < b*c) :
    0 < d*c := by
  rcases mul_pos_iff.mp hdb with ⟨hd,hb⟩ | ⟨hd,hb⟩
  · have hc : 0 < c := (mul_pos_iff.mp hbc).resolve_right (by rintro ⟨h,_⟩; linarith) |>.2
    exact mul_pos hd hc
  · have hc : c < 0 := (mul_pos_iff.mp hbc).resolve_left (by rintro ⟨h,_⟩; linarith) |>.2
    exact mul_pos_of_neg_of_neg hd hc

/-- At a nonzero root, the reduced derivative criterion and the predicted
side of existence give precisely the opposite sign to the zero branch. -/
theorem nonzero_branch_sign {d h a b μ t : ℝ}
    (ht : 0 < t) (hside : 0 < t * (-a*μ/b))
    (hHb : 0 < h*b) (hd : d = 2*t*h) : 0 < d * (-a*μ) := by
  have hc : 0 < -a*μ/b := (mul_pos_iff.mp hside).resolve_right
    (by rintro ⟨h,_⟩; linarith) |>.2
  have hb : b ≠ 0 := by intro hb; simp [hb] at hHb
  have hbc : 0 < b * (-a*μ) := by
    have h := mul_pos hc (sq_pos_of_ne_zero hb)
    have heq : (-a*μ/b) * b^2 = b * (-a*μ) := by field_simp
    rwa [heq] at h
  have hhc := same_sign_trans hHb hbc
  rw [hd]
  nlinarith [mul_pos ht hhc]

/-- Complete geometric and stability conclusion from a genuine C¹
squared-state reduction. The additional reduction data are internal hypotheses
of this lemma, NOT additional hypotheses of the original target. The Taylor construction below supplies
these data from C⁵ regularity and oddness. -/
theorem pitchfork_of_reduction
    (hpersist : Specs.D13Unified.Ch16.SimplePersistence.flowPersistence)
    (hscalar : Specs.D13Unified.Ch16.SimplePersistence.scalarFlowStability)
    (hslice : Specs.D13Unified.Ch16.SimplePersistence.stateDerivativeSlice)
    {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (h00 : (0,0) ∈ U) (hf : ContDiffOn ℝ 5 f U)
    (hx0 : stateDerivative f (0,0) = 0)
    (ha : mixedCoefficient f ≠ 0) (hb : cubicCoefficient f ≠ 0)
    (H : ℝ × ℝ → ℝ) (V : Set (ℝ × ℝ))
    (hV : IsOpen V) (hV0 : (0,0) ∈ V) (hH : ContDiffOn ℝ 1 H V)
    (hH0 : H (0,0) = 0)
    (hHa : fderiv ℝ H (0,0) (1,0) = mixedCoefficient f)
    (hHb : stateDerivative H (0,0) = cubicCoefficient f)
    (Rμ Rx : ℝ) (hRμ : 0 < Rμ) (hRx : 0 < Rx)
    (hbox : Metric.ball 0 Rμ ×ˢ Metric.ball 0 Rx ⊆ U)
    (hfactor : ∀ μ ∈ Metric.ball 0 Rμ, ∀ x ∈ Metric.ball 0 Rx,
      f (μ,x) = x * H (μ,x^2)) :
    Conclusion f U (mixedCoefficient f) (cubicCoefficient f) := by
  let a := mixedCoefficient f
  let b := cubicCoefficient f
  obtain ⟨s,α₀,β,hg,htype⟩ := hpersist H V hV hV0 hH hH0 (by simpa [hHb] using hb)
  have hds := zero_graph_derivative hV hH hg hHa hHb hb
  obtain ⟨hα₀,hβ,hs0,hHV,hsmooth,hroot⟩ := hg
  have hcont : ContinuousAt s 0 :=
    (hsmooth 0 (Metric.mem_ball_self hα₀)).contDiffAt
      (Metric.ball_mem_nhds 0 hα₀) |>.continuousAt
  have hc : -a/b ≠ 0 := div_ne_zero (neg_ne_zero.mpr ha) hb
  obtain ⟨εs,hεs,hssign⟩ := sign_near_simple_zero hs0 hds hc
  obtain ⟨εz,hεz,hzsign⟩ := zero_branch_sign hU h00 hf hx0 ha
  let ρ := min (min Rx β) 1 / 2
  have hmin : 0 < min (min Rx β) 1 := lt_min (lt_min hRx hβ) zero_lt_one
  have hρ : 0 < ρ := half_pos hmin
  have hhalf : ρ < min (min Rx β) 1 := half_lt_self hmin
  have hρRx : ρ < Rx := hhalf.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hρβ : ρ < β := hhalf.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hρ1 : ρ < 1 := hhalf.trans_le (min_le_right _ _)
  have hρsq : ρ^2 < β := lt_trans (by nlinarith) hρβ
  have hsmall : ∀ᶠ μ in 𝓝 0, |s μ| < ρ^2 :=
    hcont.abs (isOpen_Iio.mem_nhds (by simpa [hs0] using sq_pos_of_pos hρ))
  have hevent : ∀ᶠ μ in 𝓝 0,
      μ ∈ Metric.ball 0 α₀ ∧ μ ∈ Metric.ball 0 Rμ ∧ |s μ| < ρ^2 ∧
      (μ ≠ 0 → 0 < s μ * (-a*μ/b)) ∧
      (μ ≠ 0 → 0 < stateDerivative f (μ,0) * (a*μ)) := by
    filter_upwards [Metric.ball_mem_nhds 0 hα₀, Metric.ball_mem_nhds 0 hRμ,
      hsmall, Metric.ball_mem_nhds 0 hεs, Metric.ball_mem_nhds 0 hεz] with μ hμα hμR hμs hμεs hμεz
    refine ⟨hμα,hμR,hμs,?_,hzsign μ hμεz⟩
    intro hn
    convert hssign μ hμεs hn using 1; ring
  obtain ⟨α,hα,hall⟩ := Metric.eventually_nhds_iff.mp hevent
  have hdata : ∀ μ ∈ Metric.ball 0 α,
      μ ∈ Metric.ball 0 α₀ ∧ μ ∈ Metric.ball 0 Rμ ∧ |s μ| < ρ^2 ∧
      (μ ≠ 0 → 0 < s μ * (-a*μ/b)) ∧
      (μ ≠ 0 → 0 < stateDerivative f (μ,0) * (a*μ)) := by
    intro μ hμ
    exact hall (by simpa only [Metric.mem_ball] using hμ)
  have hxRx : ∀ x : ℝ, x ∈ Metric.ball 0 ρ → x ∈ Metric.ball 0 Rx :=
    fun _ hx => Metric.ball_subset_ball hρRx.le hx
  have hxβ : ∀ x : ℝ, x ∈ Metric.ball 0 ρ → x^2 ∈ Metric.ball 0 β := by
    intro x hx
    have habs : |x| < ρ := by simpa [Metric.mem_ball, Real.dist_eq] using hx
    have hx2 : x^2 < ρ^2 := by nlinarith [sq_abs x, abs_nonneg x]
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sq_nonneg x)] using hx2.trans hρsq
  have hf1 : ContDiffOn ℝ 1 f U := hf.of_le (by norm_num)
  refine ⟨s,α,ρ,hα,hρ,?_,?_,hs0,hds,?_⟩
  · intro z hz
    exact hbox ⟨(hdata z.1 hz.1).2.1,hxRx z.2 hz.2⟩
  · exact hsmooth.mono (fun μ hμ => (hdata μ hμ).1)
  · intro μ hμ
    obtain ⟨hμα,hμR,hμs,hss,hzs⟩ := hdata μ hμ
    have hiff : 0 < s μ ↔ 0 < -a*μ/b := by
      by_cases hn : μ = 0
      · simp [hn,hs0]
      · rcases mul_pos_iff.mp (hss hn) with h | h <;> constructor <;> intro ht <;> linarith [h.1,h.2]
    have hzero : f (μ,0) = 0 := by
      rw [hfactor μ hμR 0 (Metric.mem_ball_self hRx), zero_mul]
    have hsource0 : (μ,0) ∈ U := hbox ⟨hμR,Metric.mem_ball_self hRx⟩
    refine ⟨hzero,hss,?_,?_,?_⟩
    · intro hside
      have hsp : 0 < s μ := hiff.mpr hside
      refine ⟨Real.sqrt_pos.mpr hsp,?_⟩
      have hsq := Real.sq_sqrt hsp.le
      have hslt : s μ < ρ^2 := (le_abs_self (s μ)).trans_lt hμs
      nlinarith [Real.sqrt_nonneg (s μ)]
    · intro x hx
      have heq : H (μ,x^2) = 0 ↔ x^2 = s μ := (hroot μ hμα).2 (x^2) (hxβ x hx)
      rw [zeros_of_reduction (hfactor μ hμR x (hxRx x hx)) heq, hiff]
    · intro hn
      refine ⟨hzs hn,scalar_stability_at hscalar hslice hU hf1 hsource0 hzero,?_⟩
      intro x hx hxn hfx
      have hxV : (μ,x^2) ∈ V := hHV ⟨hμα,hxβ x hx⟩
      have hxU : (μ,x) ∈ U := hbox ⟨hμR,hxRx x hx⟩
      have hHzero : H (μ,x^2) = 0 := by
        have hp := hfactor μ hμR x (hxRx x hx)
        rw [hfx] at hp
        exact (mul_eq_zero.mp hp.symm).resolve_left hxn
      have hxs : x^2 = s μ := ((hroot μ hμα).2 (x^2) (hxβ x hx)).mp hHzero
      have hder : stateDerivative f (μ,x) =
          2*s μ*stateDerivative H (μ,s μ) := by
        have hdf := ((hf1 (μ,x) hxU).contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
        have hdH := ((hH (μ,x^2) hxV).contDiffAt (hV.mem_nhds hxV)).differentiableAt (by simp)
        have heventf : (fun y => f (μ,y)) =ᶠ[𝓝 x] fun y => y * H (μ,y^2) := by
          filter_upwards [Metric.isOpen_ball.mem_nhds (hxRx x hx)] with y hy
          exact hfactor μ hμR y hy
        rw [stateDerivative_of_factor hslice hdf hdH heventf, hHzero, zero_add, hxs]
      refine ⟨nonzero_branch_sign (by rw [← hxs]; exact sq_pos_of_ne_zero hxn)
        (hss hn) (by simpa [hHb] using htype μ hμα) hder,
        scalar_stability_at hscalar hslice hU hf1 hxU hfx⟩

/-- Multiplying the square-root composition by its squared-state variable
removes the derivative singularity at the boundary. Only continuity of C is
needed for the derivative at s=0. This supports the third-order Taylor route
to the C¹ reduction constructed below. -/
theorem weighted_sqrt_hasFDerivAt_zero {C : ℝ × ℝ → ℝ} {μ : ℝ}
    (hC : ContinuousAt C (μ,0)) :
    HasFDerivAt (fun z : ℝ × ℝ => z.2 * C (z.1,Real.sqrt |z.2|))
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (C (μ,0))) (μ,0) := by
  have hphi : ContinuousAt (fun z : ℝ × ℝ => (z.1,Real.sqrt |z.2|)) (μ,0) :=
    continuousAt_fst.prodMk continuousAt_snd.abs.sqrt
  have hcomp : ContinuousAt (fun z : ℝ × ℝ => C (z.1,Real.sqrt |z.2|)) (μ,0) := by
    exact hC.comp_of_eq hphi (by simp)
  have hsmall : (fun z : ℝ × ℝ => C (z.1,Real.sqrt |z.2|) - C (μ,0))
      =o[𝓝 (μ,0)] (fun _ => (1 : ℝ)) := by
    apply (Asymptotics.isLittleO_one_iff ℝ).mpr
    convert hcomp.tendsto.sub (tendsto_const_nhds (x := C (μ,0))) using 1; simp
  have hstate : (fun z : ℝ × ℝ => z.2) =O[𝓝 (μ,0)] (fun z => z - (μ,0)) := by
    convert (Asymptotics.isBigO_snd_prod' (f' := fun z : ℝ × ℝ => z - (μ,0))
      (l := 𝓝 (μ,0))) using 1
    ext z
    simp
  have hrem : (fun z : ℝ × ℝ => z.2 * (C (z.1,Real.sqrt |z.2|) - C (μ,0)))
      =o[𝓝 (μ,0)] (fun z => z - (μ,0)) := by
    simpa only [smul_eq_mul, one_smul, mul_comm] using hsmall.smul_isBigO hstate
  apply HasFDerivAt.of_isLittleO
  convert hrem using 1
  ext z
  simp only [zero_mul, sub_zero, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  change z.2 * C (z.1,Real.sqrt |z.2|) - (z.2 - 0) * C (μ,0) =
    z.2 * (C (z.1,Real.sqrt |z.2|) - C (μ,0))
  ring

def sqrtAbsMap (z : ℝ × ℝ) : ℝ × ℝ := (z.1, Real.sqrt |z.2|)

def weightedSqrtDerivative (C : ℝ × ℝ → ℝ)
    (C' : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ)) (z : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  (z.2 * C' (sqrtAbsMap z) (1,0)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
  (C (sqrtAbsMap z) + Real.sqrt |z.2| / 2 * C' (sqrtAbsMap z) (0,1)) •
    ContinuousLinearMap.snd ℝ ℝ ℝ

private theorem sqrtAbs_hasFDerivAt {z : ℝ × ℝ} (hz : z.2 ≠ 0) :
    HasFDerivAt (fun z : ℝ × ℝ => Real.sqrt |z.2|)
      ((Real.sqrt |z.2| / (2*z.2)) • ContinuousLinearMap.snd ℝ ℝ ℝ) z := by
  have hs := ((hasFDerivAt_snd (𝕜 := ℝ) (p := z)).abs hz).sqrt (abs_ne_zero.mpr hz)
  have heq : (Real.sqrt |z.2| / (2*z.2)) • ContinuousLinearMap.snd ℝ ℝ ℝ =
      (1 / (2 * Real.sqrt |z.2|)) • (SignType.sign z.2 : ℝ) •
        ContinuousLinearMap.snd ℝ ℝ ℝ := by
    rw [smul_smul]
    congr 1
    have hr : Real.sqrt |z.2| ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (abs_pos.mpr hz))
    have hr2 := Real.sq_sqrt (abs_nonneg z.2)
    rcases hz.lt_or_gt with hneg | hpos
    · simp only [sign_neg hneg, SignType.coe_neg, SignType.coe_one]
      have ha := abs_of_neg hneg
      field_simp
      nlinarith
    · simp only [sign_pos hpos, SignType.coe_one]
      have ha := abs_of_pos hpos
      field_simp
      nlinarith
  rw [heq]
  exact hs

theorem weighted_sqrt_hasFDerivAt
    {C : ℝ × ℝ → ℝ} {C' : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ)} {z : ℝ × ℝ}
    (hC : HasFDerivAt C (C' (sqrtAbsMap z)) (sqrtAbsMap z)) :
    HasFDerivAt (fun z : ℝ × ℝ => z.2 * C (sqrtAbsMap z))
      (weightedSqrtDerivative C C' z) z := by
  by_cases hz : z.2 = 0
  · have hzz : z = (z.1,0) := Prod.ext rfl hz
    rw [hzz]
    have h := weighted_sqrt_hasFDerivAt_zero (μ := z.1)
      (by simpa [sqrtAbsMap, hz] using hC.continuousAt)
    have heq : weightedSqrtDerivative C C' (z.1,0) =
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (C (z.1,0))) := by
      apply ContinuousLinearMap.ext
      intro v
      simp [weightedSqrtDerivative, sqrtAbsMap, mul_comm]
    rw [heq]
    exact h
  · have hp : HasFDerivAt sqrtAbsMap
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
          ((Real.sqrt |z.2| / (2*z.2)) • ContinuousLinearMap.snd ℝ ℝ ℝ)) z :=
      (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).prodMk (sqrtAbs_hasFDerivAt hz)
    have hw := (hasFDerivAt_snd (𝕜 := ℝ) (p := z)).mul (hC.comp z hp)
    have heq : weightedSqrtDerivative C C' z =
        z.2 • ((C' (sqrtAbsMap z)).comp
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
          ((Real.sqrt |z.2| / (2*z.2)) • ContinuousLinearMap.snd ℝ ℝ ℝ))) +
        C (sqrtAbsMap z) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
      apply ContinuousLinearMap.ext
      intro v
      change z.2 * C' (sqrtAbsMap z) (1,0) * v.1 +
        (C (sqrtAbsMap z) + Real.sqrt |z.2| / 2 * C' (sqrtAbsMap z) (0,1)) * v.2 =
        z.2 * C' (sqrtAbsMap z) (v.1, (Real.sqrt |z.2| / (2*z.2)) * v.2) +
          C (sqrtAbsMap z) * v.2
      have he : ((v.1, (Real.sqrt |z.2| / (2*z.2)) * v.2) : ℝ × ℝ) =
          v.1 • ((1,0) : ℝ × ℝ) +
            ((Real.sqrt |z.2| / (2*z.2)) * v.2) • ((0,1) : ℝ × ℝ) := by ext <;> simp
      rw [he, map_add, map_smul, map_smul]
      simp only [smul_eq_mul]
      field_simp
      ring
    rw [heq]
    exact hw

theorem continuous_weightedSqrtDerivative {C : ℝ × ℝ → ℝ}
    {C' : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ)} (hC : Continuous C) (hC' : Continuous C') :
    Continuous (weightedSqrtDerivative C C') := by
  have hp : Continuous sqrtAbsMap := continuous_fst.prodMk continuous_snd.abs.sqrt
  exact ((continuous_snd.mul ((hC'.comp hp).clm_apply continuous_const)).smul
    continuous_const).add
      (((hC.comp hp).add ((continuous_snd.abs.sqrt.div_const 2).mul
        ((hC'.comp hp).clm_apply continuous_const))).smul continuous_const)

/-- Multiplication by the squared state cancels the square-root singularity. -/
theorem weighted_sqrt_contDiff {C : ℝ × ℝ → ℝ} (hC : ContDiff ℝ 1 C) :
    ContDiff ℝ 1 (fun z : ℝ × ℝ => z.2 * C (z.1, Real.sqrt |z.2|)) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨weightedSqrtDerivative C (fderiv ℝ C),
    continuous_weightedSqrtDerivative hC.continuous (hC.continuous_fderiv (by simp)), ?_⟩
  intro z
  exact weighted_sqrt_hasFDerivAt ((hC.differentiable (by simp)) _).hasFDerivAt


 theorem stateDerivative_eventuallyEq {f g : ℝ × ℝ → ℝ} {z : ℝ × ℝ}
    (h : f =ᶠ[𝓝 z] g) : stateDerivative f =ᶠ[𝓝 z] stateDerivative g := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0,1)) hy

 theorem mixedCoefficient_congr {f g : ℝ × ℝ → ℝ}
    (h : f =ᶠ[𝓝 (0,0)] g) : mixedCoefficient f = mixedCoefficient g := by
  exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (1,0))
    (stateDerivative_eventuallyEq h).fderiv_eq

 theorem cubicCoefficient_congr {f g : ℝ × ℝ → ℝ}
    (h : f =ᶠ[𝓝 (0,0)] g) : cubicCoefficient f = cubicCoefficient g := by
  unfold cubicCoefficient
  rw [(stateDerivative_eventuallyEq (stateDerivative_eventuallyEq
    (stateDerivative_eventuallyEq h))).eq_of_nhds]

 theorem coefficient_even_of_odd_factor {g C : ℝ × ℝ → ℝ} {A : ℝ → ℝ}
    (ho : ∀ μ x, g (μ,-x) = -g (μ,x))
    (hfac : ∀ μ x, g (μ,x) = x*A μ + x^3*C (μ,x)) :
    ∀ μ x, C (μ,-x) = C (μ,x) := by
  intro μ x
  by_cases hx : x = 0
  · simp [hx]
  · have h := ho μ x
    rw [hfac μ (-x), hfac μ x] at h
    have hpow : x^3 ≠ 0 := pow_ne_zero 3 hx
    apply (mul_left_cancel₀ hpow)
    nlinarith only [h]

 theorem factor_via_squared_state {g C : ℝ × ℝ → ℝ} {A : ℝ → ℝ}
    (ho : ∀ μ x, g (μ,-x) = -g (μ,x))
    (hfac : ∀ μ x, g (μ,x) = x*A μ + x^3*C (μ,x)) :
    ∀ μ x, g (μ,x) = x * (A μ + x^2*C (μ,Real.sqrt |x^2|)) := by
  intro μ x
  have he := coefficient_even_of_odd_factor ho hfac μ x
  have hs : Real.sqrt |x^2| = |x| := by
    rw [abs_of_nonneg (sq_nonneg x), Real.sqrt_sq_eq_abs]
  rw [hs]
  have habs : C (μ,|x|) = C (μ,x) := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, he]
  rw [habs, hfac μ x]
  ring


theorem reduction_of_cubic_factor {g C : ℝ × ℝ → ℝ}
    (hg : ContDiff ℝ 5 g) (ho : ∀ μ x, g (μ,-x) = -g (μ,x))
    (hC : ContDiff ℝ 1 C)
    (hfac : ∀ μ x, g (μ,x) = x*stateDerivative g (μ,0) + x^3*C (μ,x))
    (hC0 : C (0,0) = cubicCoefficient g) :
    ∃ H : ℝ × ℝ → ℝ, ContDiff ℝ 1 H ∧
      H (0,0) = stateDerivative g (0,0) ∧
      fderiv ℝ H (0,0) (1,0) = mixedCoefficient g ∧
      stateDerivative H (0,0) = cubicCoefficient g ∧
      ∀ μ x, g (μ,x) = x*H (μ,x^2) := by
  have hW := weighted_sqrt_contDiff hC
  have hD : ContDiff ℝ 4 (stateDerivative g) :=
    contDiffOn_univ.mp (stateDerivative_contDiffOn isOpen_univ hg.contDiffOn (by norm_num))
  let A : ℝ → ℝ := fun μ => stateDerivative g (μ,0)
  let W : ℝ × ℝ → ℝ := fun z => z.2*C (z.1,Real.sqrt |z.2|)
  let H : ℝ × ℝ → ℝ := fun z => A z.1 + W z
  have hAs : ContDiff ℝ 1 A :=
    (hD.of_le (by norm_num)).comp (contDiff_id.prodMk contDiff_const)
  have hAd : HasDerivAt A (mixedCoefficient g) 0 := by
    have hp : HasDerivAt (fun μ : ℝ => ((μ,0) : ℝ × ℝ)) (1,0) 0 :=
      (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 0)
    exact hD.differentiable (by norm_num) (0,0) |>.hasFDerivAt.comp_hasDerivAt_of_eq 0 hp rfl
  have hWd := weighted_sqrt_hasFDerivAt_zero (hC.continuous.continuousAt (x := (0,0)))
  have hHd : HasFDerivAt H
      ((ContinuousLinearMap.toSpanSingleton ℝ (mixedCoefficient g)).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (C (0,0))) (0,0) := by
    exact (hAd.hasFDerivAt.comp (0,0) (hasFDerivAt_fst : HasFDerivAt
      (Prod.fst : ℝ×ℝ→ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ) (0,0))).add hWd
  refine ⟨H, (hAs.comp contDiff_fst).add hW, by simp [H,W,A], ?_, ?_, ?_⟩
  · rw [hHd.fderiv]
    simp
  · unfold stateDerivative
    rw [hHd.fderiv]
    simpa using hC0
  · exact factor_via_squared_state ho hfac


/-- Extend a locally C5 real function on a product neighborhood without changing its germ. -/
theorem local_C5_extension {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (h0 : (0,0) ∈ U) (hf : ContDiffOn ℝ 5 f U) :
    ∃ g : ℝ × ℝ → ℝ, ContDiff ℝ 5 g ∧ g =ᶠ[𝓝 (0,0)] f := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  let c : ContDiffBump ((0,0) : ℝ × ℝ) :=
    { rIn := r/4
      rOut := r/2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  have hsupport : tsupport c ⊆ U := by
    rw [c.tsupport_eq]
    intro z hz
    apply hball
    have hz' : dist z (0,0) ≤ r/2 := hz
    show dist z (0,0) < r
    linarith
  refine ⟨fun z => c z * f z, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ U
    · exact c.contDiffAt.mul ((hf z hz).contDiffAt (hU.mem_nhds hz))
    · have hs : z ∉ tsupport c := fun hs => hz (hsupport hs)
      have he : c =ᶠ[𝓝 z] 0 := by rwa [notMem_tsupport_iff_eventuallyEq] at hs
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [he] with y hy
      simp only [Pi.zero_apply] at hy
      simp [hy]
  · filter_upwards [c.eventuallyEq_one] with z hz
    simp only [Pi.one_apply] at hz
    simp [hz]

open Specs.D13Unified.Ch16.Pitchfork
open Specs.D13Unified.Ch16.SimplePersistence

/-- A globally odd C5 representative agrees with the given locally odd family near the origin. -/
theorem local_odd_C5_extension {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (h0 : (0,0) ∈ U) (hf : ContDiffOn ℝ 5 f U)
    (ho : OddOn f U) :
    ∃ g : ℝ × ℝ → ℝ, ContDiff ℝ 5 g ∧
      (∀ μ x : ℝ, g (μ,-x) = -g (μ,x)) ∧
      g =ᶠ[𝓝 (0,0)] f := by
  obtain ⟨g,hg,heq⟩ := local_C5_extension hU h0 hf
  let R : ℝ × ℝ → ℝ × ℝ := fun z => (z.1,-z.2)
  have hR : ContDiff ℝ 5 R := contDiff_fst.prodMk contDiff_snd.neg
  have hRt : Tendsto R (𝓝 ((0,0) : ℝ × ℝ)) (𝓝 (0,0)) := by
    simpa [R] using hR.continuous.continuousAt.tendsto (x := ((0,0) : ℝ × ℝ))
  refine ⟨fun z => (g z - g (R z))/2, (hg.sub (hg.comp hR)).div_const 2, ?_, ?_⟩
  · intro μ x
    dsimp [R]
    rw [neg_neg]
    ring
  · filter_upwards [heq, heq.comp_tendsto hRt, hU.mem_nhds h0,
      hRt.eventually (hU.mem_nhds h0)] with z hz hzR hzU hzRU
    change g z = f z at hz
    change g (R z) = f (R z) at hzR
    rw [hz,hzR]
    have hodd := ho z.1 z.2 hzU hzRU
    change f (R z) = -f z at hodd
    rw [hodd]
    ring

/-- The global representative may be chosen equal on one fixed product box in U. -/
theorem local_odd_C5_extension_box {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (h0 : (0,0) ∈ U) (hf : ContDiffOn ℝ 5 f U)
    (ho : OddOn f U) :
    ∃ g : ℝ × ℝ → ℝ, ∃ α ρ : ℝ, ContDiff ℝ 5 g ∧
      (∀ μ x : ℝ, g (μ,-x) = -g (μ,x)) ∧ 0 < α ∧ 0 < ρ ∧
      Metric.ball 0 α ×ˢ Metric.ball 0 ρ ⊆ U ∧
      (∀ μ ∈ Metric.ball 0 α, ∀ x ∈ Metric.ball 0 ρ, g (μ,x) = f (μ,x)) ∧
      g =ᶠ[𝓝 (0,0)] f := by
  obtain ⟨g,hg,hgo,heq⟩ := local_odd_C5_extension hU h0 hf ho
  have hev : {z | z ∈ U ∧ g z = f z} ∈ 𝓝 ((0,0) : ℝ × ℝ) :=
    inter_mem (hU.mem_nhds h0) heq
  obtain ⟨A,hA,B,hB,hAB⟩ := mem_nhds_prod_iff.mp hev
  obtain ⟨α,hα,hαA⟩ := Metric.mem_nhds_iff.mp hA
  obtain ⟨ρ,hρ,hρB⟩ := Metric.mem_nhds_iff.mp hB
  exact ⟨g,α,ρ,hg,hgo,hα,hρ,fun z hz => (hAB ⟨hαA hz.1,hρB hz.2⟩).1,
    fun μ hμ x hx => (hAB ⟨hαA hμ,hρB hx⟩).2,heq⟩



namespace TaylorFactor
open MeasureTheory

lemma contDiff_intervalIntegral
    {F : (ℝ × ℝ) → ℝ → ℝ}
    {F' : (ℝ × ℝ) → ℝ → ((ℝ × ℝ) →L[ℝ] ℝ)}
    (hF : Continuous F.uncurry) (hF' : Continuous F'.uncurry)
    (hd : ∀ z t, HasFDerivAt (fun w => F w t) (F' z t) z) :
    ContDiff ℝ 1 (fun z => ∫ t in (0 : ℝ)..1, F z t) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨fun z => ∫ t in (0 : ℝ)..1, F' z t, ?_, ?_⟩
  · exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) hF' 0 1
  · intro z₀
    have hc : IsCompact (Metric.closedBall z₀ 1 ×ˢ Icc (0 : ℝ) 1) :=
      (isCompact_closedBall z₀ 1).prod isCompact_Icc
    have hcn : ContinuousOn (fun p : (ℝ × ℝ) × ℝ => ‖F' p.1 p.2‖)
        (Metric.closedBall z₀ 1 ×ˢ Icc (0 : ℝ) 1) := hF'.norm.continuousOn
    obtain ⟨M,hM⟩ := hc.bddAbove_image hcn
    have hbound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Metric.closedBall z₀ 1, ‖F' z t‖ ≤ M := by
      intro t ht z hz
      exact hM (mem_image_of_mem (fun p : (ℝ × ℝ) × ℝ => ‖F' p.1 p.2‖) (show (z,t) ∈ Metric.closedBall z₀ 1 ×ˢ Icc (0 : ℝ) 1 from ⟨hz,ht⟩))
    have hFt : ∀ z, Continuous (F z) := fun z => hF.comp (continuous_const.prodMk continuous_id)
    have hF't : ∀ z, Continuous (F' z) := fun z => hF'.comp (continuous_const.prodMk continuous_id)
    apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (s := Metric.closedBall z₀ 1) (bound := fun _ => M)
      (Metric.closedBall_mem_nhds z₀ (by norm_num))
    · exact Eventually.of_forall (fun z => (hFt z).aestronglyMeasurable)
    · exact (hFt z₀).intervalIntegrable 0 1
    · exact (hF't z₀).aestronglyMeasurable
    · apply ae_of_all
      intro t ht z hz
      exact hbound t (by simpa only [uIoc, min_eq_left zero_le_one, max_eq_right zero_le_one] using Ioc_subset_Icc_self ht) z hz
    · exact intervalIntegrable_const
    · exact ae_of_all _ (fun t _ z _ => hd z t)

def stateScale (t : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (t • ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] lemma stateScale_apply (t : ℝ) (z : ℝ × ℝ) :
    stateScale t z = (z.1,t*z.2) := rfl

lemma continuous_stateScale : Continuous stateScale := by
  have heq : stateScale = fun t : ℝ =>
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (0 : (ℝ × ℝ) →L[ℝ] ℝ)) +
      t • ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) := by
    funext t
    ext z <;> simp [stateScale]
  rw [heq]
  fun_prop

lemma contDiff_cubicIntegral {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ 1 G) :
    ContDiff ℝ 1 (fun z : ℝ × ℝ =>
      ∫ t in (0 : ℝ)..1, (1-t)^2 * G (z.1,t*z.2)) := by
  let F : (ℝ × ℝ) → ℝ → ℝ := fun z t => (1-t)^2 * G (z.1,t*z.2)
  let F' : (ℝ × ℝ) → ℝ → ((ℝ × ℝ) →L[ℝ] ℝ) :=
    fun z t => (1-t)^2 • ((fderiv ℝ G (stateScale t z)).comp (stateScale t))
  have hfd : Continuous (fderiv ℝ G) := (contDiff_one_iff_fderiv.mp hG).2
  have ht : Continuous (fun p : (ℝ × ℝ) × ℝ => stateScale p.2) :=
    continuous_stateScale.comp continuous_snd
  have he : Continuous (fun p : (ℝ × ℝ) × ℝ => stateScale p.2 p.1) :=
    ht.clm_apply continuous_fst
  apply contDiff_intervalIntegral (F' := F')
  · exact ((continuous_const.sub continuous_snd).pow 2).mul (hG.continuous.comp he)
  · exact ((continuous_const.sub continuous_snd).pow 2).smul ((hfd.comp he).clm_comp ht)
  · intro z t
    exact (((hG.differentiable_one (stateScale t z)).hasFDerivAt.comp z
      (stateScale t).hasFDerivAt).const_mul ((1-t)^2))

open Specs.D13Unified.Ch16.SimplePersistence

lemma stateDerivative_contDiff {f : ℝ × ℝ → ℝ} {m n : ℕ∞ω}
    (hf : ContDiff ℝ n f) (hmn : m+1 ≤ n) :
    ContDiff ℝ m (stateDerivative f) :=
  (hf.fderiv_right hmn).clm_apply contDiff_const

def cubicIntegral (G : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (1-t)^2 * G (z.1,t*z.2)

def cubicRemainder (f : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  cubicIntegral (stateDerivative (stateDerivative (stateDerivative f))) z / 4 +
  cubicIntegral (stateDerivative (stateDerivative (stateDerivative f))) (z.1,-z.2) / 4

lemma contDiff_cubicRemainder {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 5 f) :
    ContDiff ℝ 1 (cubicRemainder f) := by
  have h1 : ContDiff ℝ 4 (stateDerivative f) := stateDerivative_contDiff hf (by norm_num)
  have h2 : ContDiff ℝ 3 (stateDerivative (stateDerivative f)) :=
    stateDerivative_contDiff h1 (by norm_num)
  have h3 : ContDiff ℝ 2 (stateDerivative (stateDerivative (stateDerivative f))) :=
    stateDerivative_contDiff h2 (by norm_num)
  have hc := contDiff_cubicIntegral (h3.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num))
  exact (hc.div_const 4).add ((hc.comp (contDiff_fst.prodMk contDiff_snd.neg)).div_const 4)


lemma integral_cubic_weight : (∫ t in (0 : ℝ)..1, (1-t)^2) = 1/3 := by
  have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s-s^2+s^3/3) ((1-t)^2) t := by
    intro t
    convert (((hasDerivAt_id t).sub ((hasDerivAt_id t).pow 2)).add
      (((hasDerivAt_id t).pow 3).div_const 3)) using 1 <;> simp [id, Pi.sub_def, Pi.add_def, Pi.pow_def] <;> ring
  have hi : IntervalIntegrable (fun t : ℝ => (1-t)^2) volume 0 1 :=
    (show Continuous (fun t : ℝ => (1-t)^2) by fun_prop).intervalIntegrable 0 1
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi

lemma cubicIntegral_state_zero (G : ℝ × ℝ → ℝ) (μ : ℝ) :
    cubicIntegral G (μ,0) = G (μ,0)/3 := by
  simp only [cubicIntegral, mul_zero]
  rw [intervalIntegral.integral_mul_const, integral_cubic_weight]
  ring

lemma cubicRemainder_state_zero (f : ℝ × ℝ → ℝ) (μ : ℝ) :
    cubicRemainder f (μ,0) = stateDerivative (stateDerivative (stateDerivative f)) (μ,0)/6 := by
  simp only [cubicRemainder, neg_zero, cubicIntegral_state_zero]
  ring


end TaylorFactor

lemma iteratedFDeriv_two_state {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 3 g) (z : ℝ × ℝ) :
    iteratedFDeriv ℝ 2 g z (fun _ => (0,1)) = stateDerivative (stateDerivative g) z := by
  have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 g) z :=
    hg.differentiable_iteratedFDeriv (by norm_num) z
  rw [hdiff.iteratedFDeriv_succ_apply_left']
  change fderiv ℝ (fun y => iteratedFDeriv ℝ 1 g y (fun _ => (0,1))) z (0,1) = _
  simp only [iteratedFDeriv_one_apply]
  rfl

lemma iteratedFDeriv_three_state {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 3 g) (z : ℝ × ℝ) :
    iteratedFDeriv ℝ 3 g z (fun _ => (0,1)) =
      stateDerivative (stateDerivative (stateDerivative g)) z := by
  have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 g) z :=
    hg.differentiable_iteratedFDeriv (by norm_num) z
  rw [hdiff.iteratedFDeriv_succ_apply_left']
  change fderiv ℝ (fun y => iteratedFDeriv ℝ 2 g y (fun _ => (0,1))) z (0,1) = _
  simp only [iteratedFDeriv_two_state hg]
  rfl

lemma iteratedFDeriv_state_smul {g : ℝ × ℝ → ℝ} (n : ℕ) (z : ℝ × ℝ) (x : ℝ) :
    iteratedFDeriv ℝ n g z (fun _ => (0,x)) =
      x^n * iteratedFDeriv ℝ n g z (fun _ => (0,1)) := by
  have hp : (fun _ : Fin n => ((0,x) : ℝ × ℝ)) = fun _ => x • ((0,1) : ℝ × ℝ) := by
    funext i
    ext <;> simp
  rw [hp, ContinuousMultilinearMap.map_smul_univ]
  simp

lemma taylor_cubic_raw {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 3 g) (μ x : ℝ) :
    g (μ,x) = g (μ,0) + x*stateDerivative g (μ,0) +
      x^2/2*stateDerivative (stateDerivative g) (μ,0) +
      x^3/2*TaylorFactor.cubicIntegral
        (stateDerivative (stateDerivative (stateDerivative g))) (μ,x) := by
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := g) (x := ((μ,0) : ℝ × ℝ)) (y := ((0,x) : ℝ × ℝ)) (n := 2)
    (fun t ht => hg.contDiffAt)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.factorial_zero, Nat.factorial_one, Nat.factorial_two, Nat.cast_one, Nat.cast_ofNat,
    inv_one, one_smul, iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply] at ht
  simp only [Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul, add_zero, zero_add, mul_zero] at ht
  have h1 : fderiv ℝ g (μ,0) (0,x) = x*stateDerivative g (μ,0) := by
    have hp : ((0,x) : ℝ × ℝ) = x • ((0,1) : ℝ × ℝ) := by ext <;> simp
    rw [hp, map_smul]
    rfl
  simp_rw [iteratedFDeriv_state_smul 2 _ x, iteratedFDeriv_state_smul 3 _ x, iteratedFDeriv_two_state hg,
    iteratedFDeriv_three_state hg] at ht
  rw [h1] at ht
  have hint : (∫ t in (0 : ℝ)..1, (1-t)^2 *
      (x^3 * stateDerivative (stateDerivative (stateDerivative g)) (μ,t*x))) =
      x^3 * TaylorFactor.cubicIntegral
        (stateDerivative (stateDerivative (stateDerivative g))) (μ,x) := by
    rw [TaylorFactor.cubicIntegral, ← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    ring
  rw [hint] at ht
  linarith only [ht]

lemma cubic_factor_of_odd {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 3 g)
    (ho : ∀ μ x, g (μ,-x) = -g (μ,x)) (μ x : ℝ) :
    g (μ,x) = x*stateDerivative g (μ,0) + x^3*TaylorFactor.cubicRemainder g (μ,x) := by
  have hp := taylor_cubic_raw hg μ x
  have hn := taylor_cubic_raw hg μ (-x)
  rw [ho μ x] at hn
  unfold TaylorFactor.cubicRemainder
  dsimp only
  nlinarith only [hp,hn]


/-- The symmetric pitchfork theorem for the original local family and domain. -/
theorem pitchfork : Specs.D13Unified.Ch16.Pitchfork.pitchfork := by
  intro f U hU h00 hf ho hx0 ha hb
  obtain ⟨g,Rμ,Rx,hg,hgo,hRμ,hRx,hbox,hgf,hgerm⟩ :=
    local_odd_C5_extension_box hU h00 hf ho
  let C := TaylorFactor.cubicRemainder g
  have hC : ContDiff ℝ 1 C := TaylorFactor.contDiff_cubicRemainder hg
  have hfac : ∀ μ x, g (μ,x) = x*stateDerivative g (μ,0) + x^3*C (μ,x) :=
    cubic_factor_of_odd (hg.of_le (by norm_num)) hgo
  have hC0 : C (0,0) = cubicCoefficient g :=
    TaylorFactor.cubicRemainder_state_zero g 0
  obtain ⟨H,hH,hH0,hHa,hHb,hfactor⟩ := reduction_of_cubic_factor hg hgo hC hfac hC0
  have hsg : stateDerivative g (0,0) = stateDerivative f (0,0) :=
    (stateDerivative_eventuallyEq hgerm).eq_of_nhds
  have hag : mixedCoefficient g = mixedCoefficient f := mixedCoefficient_congr hgerm
  have hbg : cubicCoefficient g = cubicCoefficient f := cubicCoefficient_congr hgerm
  apply pitchfork_of_reduction
    _root_.D13Unified.Ch16.SimplePersistence.flow_persistence
    _root_.D13Unified.Ch16.SimplePersistence.scalar_flow_stability
    _root_.D13Unified.Ch16.SimplePersistence.state_derivative_slice
    hU h00 hf hx0 ha hb H univ isOpen_univ (mem_univ _) hH.contDiffOn
    (hH0.trans (hsg.trans hx0)) (hHa.trans hag) (hHb.trans hbg)
    Rμ Rx hRμ hRx hbox
  intro μ hμ x hx
  rw [← hgf μ hμ x hx]
  exact hfactor μ x

end D13Unified.Ch16.Pitchfork
