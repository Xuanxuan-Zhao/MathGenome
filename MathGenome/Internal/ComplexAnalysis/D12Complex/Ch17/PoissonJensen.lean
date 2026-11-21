import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch17.PoissonJensen
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.LocalQuotientsArithmetic
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Topology.Perfect
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
open Complex Metric Set Filter Real InnerProductSpace MeromorphicOn
open scoped Topology ComplexConjugate Classical

namespace D12Complex.PoissonJensen

lemma accPt_closedBall {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ closedBall 0 R) :
    AccPt z (𝓟 (closedBall (0 : ℂ) R)) := by
  have h := (isOpen_ball (x := (0 : ℂ)) (ε := R)).perfect_closure
  rw [closure_ball 0 hR.ne'] at h
  exact h.acc z hz

/-- The numerator of a disk Green factor has no zero on the closed disk. -/
lemma green_numerator_ne_zero {R : ℝ} (hR : 0 < R) {a z : ℂ}
    (ha : ‖a‖ < R) (hz : ‖z‖ ≤ R) :
    (R : ℂ) ^ 2 - conj a * z ≠ 0 := by
  intro he
  have hn := congrArg norm (sub_eq_zero.mp he)
  have hlt : ‖a‖ * ‖z‖ < R ^ 2 := by
    calc
      _ ≤ ‖a‖ * R := mul_le_mul_of_nonneg_left hz (norm_nonneg _)
      _ < R * R := mul_lt_mul_of_pos_right ha hR
      _ = _ := by ring
  have hnorm : ‖(R : ℂ) ^ 2‖ = R ^ 2 := by simp [norm_pow, abs_of_pos hR]
  rw [hnorm, norm_mul, norm_conj] at hn
  linarith

lemma green_at_zero {R : ℝ} (hR : 0 < R) {a : ℂ} (ha : a ≠ 0) :
    green R 0 a = Real.log (R / ‖a‖) := by
  unfold green
  congr 1
  simp only [mul_zero, sub_zero, zero_sub, norm_div, norm_pow, norm_real,
    Real.norm_eq_abs, abs_of_pos hR, norm_mul, norm_neg]
  field_simp

lemma green_eq_log_sub {R : ℝ} (hR : 0 < R) {a z : ℂ}
    (ha : ‖a‖ < R) (hz : ‖z‖ ≤ R) (hza : z ≠ a) :
    green R z a = Real.log ‖(R : ℂ) ^ 2 - conj a * z‖ -
      Real.log R - Real.log ‖z - a‖ := by
  rw [green, norm_div, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hR,
    Real.log_div (norm_ne_zero_iff.mpr (green_numerator_ne_zero hR ha hz))
      (mul_ne_zero hR.ne' (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hza))),
    Real.log_mul hR.ne' (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hza))]
  ring

/-- Boundary modulus identity for the numerator of a Green factor. -/
lemma norm_green_numerator_boundary {R : ℝ} (_hR : 0 < R) {a ζ : ℂ}
    (hζ : ‖ζ‖ = R) :
    ‖(R : ℂ) ^ 2 - conj a * ζ‖ = R * ‖ζ - a‖ := by
  have he : (R : ℂ) ^ 2 = ζ * conj ζ := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ, Complex.ofReal_pow]
  have hf : (R : ℂ) ^ 2 - conj a * ζ = ζ * conj (ζ - a) := by
    rw [map_sub, he]
    ring
  rw [hf, norm_mul, norm_conj, hζ]

lemma log_distance_poisson {R : ℝ} (hR : 0 < R) {a z : ℂ}
    (ha : ‖a‖ < R) (hz : z ∈ ball (0 : ℂ) R) :
    circleAverage (fun ζ => (herglotzRieszKernel 0 z ζ).re * Real.log ‖ζ - a‖) 0 R =
      Real.log ‖(R : ℂ) ^ 2 - conj a * z‖ - Real.log R := by
  let u : ℂ → ℝ := fun w => Real.log ‖(R : ℂ) ^ 2 - conj a * w‖ - Real.log R
  have hu : HarmonicOnNhd u (closedBall 0 R) := by
    intro w hw
    have hn := green_numerator_ne_zero hR ha (show ‖w‖ ≤ R by simpa using hw)
    have han : AnalyticAt ℂ (fun w : ℂ => (R : ℂ) ^ 2 - conj a * w) w := by fun_prop
    exact (han.harmonicAt_log_norm hn).sub (harmonicAt_const _)
  change _ = u z
  rw [← hu.circleAverage_re_herglotzRieszKernel_smul hz]
  apply circleAverage_congr_sphere
  intro ζ hζ
  have hnζ : ‖ζ‖ = R := by simpa [abs_of_pos hR] using hζ
  have hne : ζ - a ≠ 0 := by
    intro h
    have : ζ = a := sub_eq_zero.mp h
    subst ζ
    exact ha.ne hnζ
  change _ = (herglotzRieszKernel 0 z ζ).re * u ζ
  dsimp [u]
  rw [norm_green_numerator_boundary hR hnζ,
    Real.log_mul hR.ne' (norm_ne_zero_iff.mpr hne)]
  ring

lemma weighted_log_distance_integrable {R : ℝ} (hR : 0 < R) {a z : ℂ}
    (ha : ‖a‖ < R) (hz : ‖z‖ < R) :
    CircleIntegrable (fun ζ => (herglotzRieszKernel 0 z ζ).re * Real.log ‖ζ - a‖) 0 R := by
  apply ContinuousOn.circleIntegrable hR.le
  intro ζ hζ
  have hnζ : ‖ζ‖ = R := by simpa using hζ
  have hza : ζ - a ≠ 0 := sub_ne_zero.mpr (by intro h; subst ζ; exact ha.ne hnζ)
  have hzz : ζ - z ≠ 0 := sub_ne_zero.mpr (by intro h; subst ζ; exact hz.ne hnζ)
  apply ContinuousAt.continuousWithinAt
  simp only [herglotzRieszKernel_fun_def, sub_zero]
  exact (Complex.continuous_re.continuousAt.comp
    ((continuousAt_id.add continuousAt_const).div
      (continuousAt_id.sub continuousAt_const) hzz)).mul
    ((continuousAt_id.sub continuousAt_const).norm.log (norm_ne_zero_iff.mpr hza))

lemma finitePart_ne_zero {F : ℂ → RiemannSphere} {a : ℂ}
    (hfin : F a ≠ sphereInfty) (hn : F a ≠ sphereFinite 0) : scalarFinitePart F a ≠ 0 := by
  rcases sphere_eq_infty_or_finite (F a) with h | ⟨c, hc⟩
  · exact (hfin h).elim
  · simpa [scalarFinitePart, hc] using (show c ≠ 0 by intro h; apply hn; simpa [h] using hc)

lemma regular_order_zero {U : Set ℂ} {F : ℂ → RiemannSphere}
    (hF : ScalarMeromorphicOn U F) {a : ℂ} (ha : a ∈ U)
    (hfin : F a ≠ sphereInfty) (hn : F a ≠ sphereFinite 0) :
    meromorphicOrderAt (scalarFinitePart F) a = 0 := by
  have han := scalarMeromorphicOn_finite_analytic U F hF a ha hfin
  rw [han.meromorphicOrderAt_eq, han.analyticOrderAt_eq_zero.mpr (finitePart_ne_zero hfin hn)]
  rfl

lemma disk_meromorphic {U : Set ℂ} {F : ℂ → RiemannSphere} {R : ℝ}
    (hF : ScalarMeromorphicOn U F) (hsub : closedBall (0 : ℂ) R ⊆ U) :
    MeromorphicOn (scalarFinitePart F) (closedBall 0 R) :=
  fun a ha => LocalQuotientsArithmetic.scalar_meromorphicAt U F hF a (hsub ha)

lemma disk_orders_finite {U : Set ℂ} {F : ℂ → RiemannSphere} {R : ℝ}
    (hF : ScalarMeromorphicOn U F) (hR : 0 < R) (hsub : closedBall (0 : ℂ) R ⊆ U)
    (hb : ∀ ζ ∈ sphere (0 : ℂ) R, F ζ ≠ sphereInfty ∧ F ζ ≠ sphereFinite 0) :
    ∀ a ∈ closedBall (0 : ℂ) R, meromorphicOrderAt (scalarFinitePart F) a ≠ ⊤ := by
  have hp : (R : ℂ) ∈ sphere (0 : ℂ) R := by simp [mem_sphere_iff_norm, abs_of_pos hR]
  have hc := sphere_subset_closedBall hp
  have ho := regular_order_zero hF (hsub hc) (hb _ hp).1 (hb _ hp).2
  intro a ha
  exact (disk_meromorphic hF hsub).meromorphicOrderAt_ne_top_of_isPreconnected
    (convex_closedBall (0 : ℂ) R).isPreconnected hc ha (by rw [ho]; exact WithTop.coe_ne_top)

lemma disk_order_eq {U : Set ℂ} {F : ℂ → RiemannSphere} {R : ℝ}
    (hF : ScalarMeromorphicOn U F) (hR : 0 < R) (hsub : closedBall (0 : ℂ) R ⊆ U)
    (hb : ∀ ζ ∈ sphere (0 : ℂ) R, F ζ ≠ sphereInfty ∧ F ζ ≠ sphereFinite 0)
    {a : ℂ} (ha : a ∈ closedBall (0 : ℂ) R) :
    meromorphicOrderAt (scalarFinitePart F) a = (diskDivisor F R a : WithTop ℤ) := by
  rw [diskDivisor, divisor_apply (disk_meromorphic hF hsub) ha,
    WithTop.coe_untop₀_of_ne_top (disk_orders_finite hF hR hsub hb a ha)]

lemma disk_divisor_boundary {U : Set ℂ} {F : ℂ → RiemannSphere} {R : ℝ}
    (hF : ScalarMeromorphicOn U F) (hsub : closedBall (0 : ℂ) R ⊆ U)
    (hb : ∀ ζ ∈ sphere (0 : ℂ) R, F ζ ≠ sphereInfty ∧ F ζ ≠ sphereFinite 0)
    {a : ℂ} (ha : a ∈ sphere (0 : ℂ) R) : diskDivisor F R a = 0 := by
  rw [diskDivisor, divisor_apply (disk_meromorphic hF hsub) (sphere_subset_closedBall ha),
    regular_order_zero hF (hsub (sphere_subset_closedBall ha)) (hb _ ha).1 (hb _ ha).2]
  rfl

lemma disk_divisor_support_interior {U : Set ℂ} {F : ℂ → RiemannSphere} {R : ℝ}
    (hF : ScalarMeromorphicOn U F) (hsub : closedBall (0 : ℂ) R ⊆ U)
    (hb : ∀ ζ ∈ sphere (0 : ℂ) R, F ζ ≠ sphereInfty ∧ F ζ ≠ sphereFinite 0) :
    (diskDivisor F R).support ⊆ ball 0 R := by
  intro a ha
  have hc := (diskDivisor F R).supportWithinDomain ha
  by_contra hn
  have hs : a ∈ sphere (0 : ℂ) R := by
    simp only [mem_closedBall, mem_ball, mem_sphere] at *
    exact le_antisymm hc (le_of_not_gt hn)
  exact ha (disk_divisor_boundary hF hsub hb hs)

lemma kernel_mul_circleIntegrable {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : ‖z‖ < R)
    {φ : ℂ → ℝ} (hφ : ContinuousOn φ (sphere (0 : ℂ) R)) :
    CircleIntegrable (fun ζ => (herglotzRieszKernel 0 z ζ).re * φ ζ) 0 R := by
  apply ContinuousOn.circleIntegrable hR.le
  apply ContinuousOn.mul _ hφ
  intro ζ hζ
  have hnζ : ‖ζ‖ = R := by simpa using hζ
  have hzz : ζ - z ≠ 0 := sub_ne_zero.mpr (by intro h; subst ζ; exact hz.ne hnζ)
  apply ContinuousAt.continuousWithinAt
  simp only [herglotzRieszKernel_fun_def, sub_zero]
  exact Complex.continuous_re.continuousAt.comp
    ((continuousAt_id.add continuousAt_const).div
      (continuousAt_id.sub continuousAt_const) hzz)

theorem integrands_integrable :
    Specs.D12Complex.Ch17.PoissonJensen.integrands_integrable_type := by
  intro U F R hF hR hsub hb
  have hc : ContinuousOn (fun ζ => Real.log ‖scalarFinitePart F ζ‖) (sphere (0 : ℂ) R) := by
    intro ζ hζ
    have han := scalarMeromorphicOn_finite_analytic U F hF ζ
      (hsub (sphere_subset_closedBall hζ)) (hb ζ hζ).1
    exact (han.continuousAt.norm.log
      (norm_ne_zero_iff.mpr (finitePart_ne_zero (hb ζ hζ).1 (hb ζ hζ).2))).continuousWithinAt
  refine ⟨hc.circleIntegrable hR.le, ?_⟩
  intro z hz
  have hi := kernel_mul_circleIntegrable hR (show ‖z‖ < R by simpa using hz) hc
  simpa only [CircleIntegrable, herglotzRieszKernel_fun_def, sub_zero] using hi

/-- Poisson–Jensen with the integer-valued divisor, prior to splitting its
positive and negative parts. All evaluation points have their actual values. -/
lemma poisson_jensen_signed {U : Set ℂ} {F : ℂ → RiemannSphere} {R : ℝ}
    (hF : ScalarMeromorphicOn U F) (hR : 0 < R) (hsub : closedBall (0 : ℂ) R ⊆ U)
    (hb : ∀ ζ ∈ sphere (0 : ℂ) R, F ζ ≠ sphereInfty ∧ F ζ ≠ sphereFinite 0)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) (hfin : F z ≠ sphereInfty)
    (hn : F z ≠ sphereFinite 0) :
    Real.log ‖scalarFinitePart F z‖ = boundaryPoisson F R z -
      ∑ᶠ a : ℂ, (diskDivisor F R a : ℝ) * green R z a := by
  let f := scalarFinitePart F
  let D := diskDivisor F R
  have hf : MeromorphicOn f (closedBall 0 R) := disk_meromorphic hF hsub
  have hD : D.support.Finite := D.finiteSupport (isCompact_closedBall 0 R)
  let S := hD.toFinset
  have hS {a : ℂ} : a ∈ S ↔ D a ≠ 0 := by simp [S, Function.mem_support]
  have hSint {a : ℂ} (ha : a ∈ S) : ‖a‖ < R := by
    have := disk_divisor_support_interior hF hsub hb (hS.mp ha)
    simpa using this
  obtain ⟨g, hg, hg0, heq⟩ := hf.extract_zeros_poles
    (fun a => disk_orders_finite hF hR hsub hb a a.2) hD
  have hlog {x : ℂ} (hx : x ∈ closedBall (0 : ℂ) R)
      (hxa : AnalyticAt ℂ f x) (hx0 : f x ≠ 0) :
      Real.log ‖f x‖ = (∑ a ∈ S, (D a : ℝ) * Real.log ‖x - a‖) + Real.log ‖g x‖ := by
    have he := MeromorphicOn.log_norm_meromorphicTrailingCoeffAt_extract_zeros_poles
      hD hx (accPt_closedBall hR hx) (hf x hx) (hg x hx) (hg0 ⟨x, hx⟩) heq
    rw [hxa.meromorphicTrailingCoeffAt_of_ne_zero hx0] at he
    rw [finsum_eq_sum_of_support_subset (s := S)] at he
    · exact he
    · intro a ha
      by_contra h
      have hd : D a = 0 := by exact not_not.mp (mt hS.mpr h)
      simp [hd] at ha
  have hzR : ‖z‖ < R := by simpa using hz
  have hzc : z ∈ closedBall (0 : ℂ) R := ball_subset_closedBall hz
  have hza : AnalyticAt ℂ f z := scalarMeromorphicOn_finite_analytic U F hF z (hsub hzc) hfin
  have hgH : HarmonicOnNhd (fun x => Real.log ‖g x‖) (closedBall 0 R) :=
    fun x hx => (hg x hx).harmonicAt_log_norm (hg0 ⟨x, hx⟩)
  have hi (a : ℂ) (ha : a ∈ S) : CircleIntegrable
      (fun ζ => (D a : ℝ) * ((herglotzRieszKernel 0 z ζ).re * Real.log ‖ζ - a‖)) 0 R :=
    (weighted_log_distance_integrable hR (hSint ha) hzR).const_mul _
  have hgi : CircleIntegrable (fun ζ => (herglotzRieszKernel 0 z ζ).re * Real.log ‖g ζ‖) 0 R :=
    kernel_mul_circleIntegrable hR hzR (fun ζ hζ =>
      (hgH ζ (sphere_subset_closedBall hζ)).1.continuousAt.continuousWithinAt)
  have hsum : boundaryPoisson F R z =
      (∑ a ∈ S, (D a : ℝ) *
        (Real.log ‖(R : ℂ) ^ 2 - conj a * z‖ - Real.log R)) + Real.log ‖g z‖ := by
    have hbp : boundaryPoisson F R z =
        circleAverage (fun ζ => (herglotzRieszKernel 0 z ζ).re * Real.log ‖f ζ‖) 0 R := by
      simp only [boundaryPoisson, circleAverage_def, herglotzRieszKernel_fun_def,
        sub_zero, smul_eq_mul, f]
    rw [hbp]
    calc
      _ = circleAverage (fun ζ => (∑ a ∈ S,
          (D a : ℝ) * ((herglotzRieszKernel 0 z ζ).re * Real.log ‖ζ - a‖)) +
          (herglotzRieszKernel 0 z ζ).re * Real.log ‖g ζ‖) 0 R := by
        apply circleAverage_congr_sphere
        intro ζ hζ
        have hζ' : ζ ∈ sphere (0 : ℂ) R := by simpa [abs_of_pos hR] using hζ
        dsimp only
        rw [hlog (sphere_subset_closedBall hζ')
          (scalarMeromorphicOn_finite_analytic U F hF ζ
            (hsub (sphere_subset_closedBall hζ')) (hb ζ hζ').1)
          (finitePart_ne_zero (hb ζ hζ').1 (hb ζ hζ').2), mul_add, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = (∑ a ∈ S, circleAverage (fun ζ => (D a : ℝ) *
          ((herglotzRieszKernel 0 z ζ).re * Real.log ‖ζ - a‖)) 0 R) +
          Real.log ‖g z‖ := by
        rw [circleAverage_fun_add (CircleIntegrable.fun_sum S hi) hgi,
          circleAverage_fun_sum hi]
        congr 1
        exact hgH.circleAverage_re_herglotzRieszKernel_smul hz
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro a ha
        rw [show (fun ζ => (D a : ℝ) * ((herglotzRieszKernel 0 z ζ).re * Real.log ‖ζ - a‖)) =
          (fun ζ => (D a : ℝ) • ((herglotzRieszKernel 0 z ζ).re * Real.log ‖ζ - a‖)) by rfl,
          circleAverage_fun_smul, log_distance_poisson hR (hSint ha) hz]
        rfl
  have horder : D z = 0 := by
    dsimp [D, diskDivisor]
    rw [divisor_apply hf hzc, regular_order_zero hF (hsub hzc) hfin hn]
    rfl
  rw [finsum_eq_sum_of_support_subset (s := S)]
  · rw [hlog hzc hza (finitePart_ne_zero hfin hn), hsum]
    have he : (∑ a ∈ S, (D a : ℝ) * green R z a) =
        (∑ a ∈ S, (D a : ℝ) * (Real.log ‖(R : ℂ) ^ 2 - conj a * z‖ - Real.log R)) -
        (∑ a ∈ S, (D a : ℝ) * Real.log ‖z - a‖) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      have hne : z ≠ a := by intro h; subst a; exact (hS.mp ha) horder
      rw [green_eq_log_sub hR (hSint ha) (by simpa using hzc) hne]
      ring
    rw [he]
    ring
  · intro a ha
    by_contra h
    have hd : D a = 0 := by exact not_not.mp (mt hS.mpr h)
    change (D a : ℝ) * green R z a ≠ 0 at ha
    exact ha (by simp [hd])

lemma multiplicity_support {F : ℂ → RiemannSphere} {R : ℝ} :
    Function.support (zeroMultiplicity F R) ⊆ (diskDivisor F R).support ∧
    Function.support (poleMultiplicity F R) ⊆ (diskDivisor F R).support := by
  constructor
  all_goals
    intro a ha hd
    apply ha
    simp only [zeroMultiplicity, poleMultiplicity, hd, Int.toNat_zero, neg_zero]

lemma disk_divisor_pole_iff {U : Set ℂ} {F : ℂ → RiemannSphere} {R : ℝ}
    (hF : ScalarMeromorphicOn U F) (hR : 0 < R) (hsub : closedBall (0 : ℂ) R ⊆ U)
    (hb : ∀ ζ ∈ sphere (0 : ℂ) R, F ζ ≠ sphereInfty ∧ F ζ ≠ sphereFinite 0)
    {a : ℂ} (ha : a ∈ closedBall (0 : ℂ) R) :
    F a = sphereInfty ↔ diskDivisor F R a < 0 := by
  have he : F a = LocalQuotientsArithmetic.fill (scalarFinitePart F) a :=
    LocalQuotientsArithmetic.scalar_eq_fill U F hF (hsub ha)
  rw [he, LocalQuotientsArithmetic.fill_eq_infty_iff, disk_order_eq hF hR hsub hb ha]
  exact WithTop.coe_lt_coe

lemma disk_divisor_zero_iff {U : Set ℂ} {F : ℂ → RiemannSphere} {R : ℝ}
    (hF : ScalarMeromorphicOn U F) (hR : 0 < R) (hsub : closedBall (0 : ℂ) R ⊆ U)
    (hb : ∀ ζ ∈ sphere (0 : ℂ) R, F ζ ≠ sphereInfty ∧ F ζ ≠ sphereFinite 0)
    {a : ℂ} (ha : a ∈ closedBall (0 : ℂ) R) :
    0 < diskDivisor F R a ↔ F a = sphereFinite 0 := by
  by_cases hinf : F a = sphereInfty
  · have hd := (disk_divisor_pole_iff hF hR hsub hb ha).mp hinf
    simp only [hinf, show sphereInfty ≠ sphereFinite 0 from (OnePoint.coe_ne_infty 0).symm,
      iff_false]
    omega
  · have han := scalarMeromorphicOn_finite_analytic U F hF a (hsub ha) hinf
    have ho := disk_order_eq hF hR hsub hb ha
    have hdn : 0 ≤ diskDivisor F R a := by
      have := han.meromorphicOrderAt_nonneg
      rw [ho] at this
      exact WithTop.coe_le_coe.mp this
    have hd0 : diskDivisor F R a = 0 ↔ scalarFinitePart F a ≠ 0 := by
      have he := han.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff
      rw [ho] at he
      simpa using he
    have hc : F a = sphereFinite (scalarFinitePart F a) := by
      rcases sphere_eq_infty_or_finite (F a) with h | ⟨c, hc⟩
      · exact (hinf h).elim
      · simp [scalarFinitePart, hc]
    constructor
    · intro hd
      have hf0 : scalarFinitePart F a = 0 := by
        by_contra hn
        have := hd0.mpr hn
        omega
      simpa [hf0] using hc
    · intro he
      have hf0 : scalarFinitePart F a = 0 := by simp [scalarFinitePart, he]
      have hne : diskDivisor F R a ≠ 0 := by
        intro h
        exact (hd0.mp h) hf0
      omega

/-- Both supports are finite and consist exactly of the interior zeros and
poles. Their weights are the positive and negative local orders. -/
theorem finite_divisor : Specs.D12Complex.Ch17.PoissonJensen.finite_divisor_type := by
  intro U F R hF hR hsub hb
  have hD := (diskDivisor F R).finiteSupport (isCompact_closedBall 0 R)
  have hI := disk_divisor_support_interior hF hsub hb
  refine ⟨hD.subset multiplicity_support.1, hD.subset multiplicity_support.2,
    multiplicity_support.1.trans hI, multiplicity_support.2.trans hI, ?_⟩
  intro a ha
  refine ⟨disk_order_eq hF hR hsub hb ha, ?_, ?_⟩
  · have ht : 0 < (diskDivisor F R a).toNat ↔ 0 < diskDivisor F R a := by omega
    exact ht.trans (disk_divisor_zero_iff hF hR hsub hb ha)
  · have ht : 0 < (-diskDivisor F R a).toNat ↔ diskDivisor F R a < 0 := by omega
    exact ht.trans (disk_divisor_pole_iff hF hR hsub hb ha).symm

lemma signed_sum_eq_difference (F : ℂ → RiemannSphere) (R : ℝ) (φ : ℂ → ℝ) :
    (∑ᶠ a : ℂ, (diskDivisor F R a : ℝ) * φ a) =
      (∑ᶠ a : ℂ, (zeroMultiplicity F R a : ℝ) * φ a) -
      (∑ᶠ a : ℂ, (poleMultiplicity F R a : ℝ) * φ a) := by
  have hD := (diskDivisor F R).finiteSupport (isCompact_closedBall 0 R)
  have hz : (fun a : ℂ => (zeroMultiplicity F R a : ℝ) * φ a).HasFiniteSupport := by
    apply (hD.subset multiplicity_support.1).subset
    intro a ha
    contrapose! ha
    simp only [Function.mem_support, not_not] at ha ⊢
    simp [ha]
  have hp : (fun a : ℂ => (poleMultiplicity F R a : ℝ) * φ a).HasFiniteSupport := by
    apply (hD.subset multiplicity_support.2).subset
    intro a ha
    contrapose! ha
    simp only [Function.mem_support, not_not] at ha ⊢
    simp [ha]
  rw [← finsum_sub_distrib hz hp]
  apply finsum_congr
  intro a
  have hi : ((diskDivisor F R a).toNat : ℤ) - ((-diskDivisor F R a).toNat : ℤ) =
      diskDivisor F R a := by omega
  have hr : (diskDivisor F R a : ℝ) =
      (zeroMultiplicity F R a : ℝ) - (poleMultiplicity F R a : ℝ) := by
    exact_mod_cast hi.symm
  rw [hr, sub_mul]

theorem poisson_jensen : Specs.D12Complex.Ch17.PoissonJensen.poisson_jensen_type := by
  intro U F R hF hR hsub hb z hz hfin hn
  have he := poisson_jensen_signed hF hR hsub hb hz hfin hn
  rw [signed_sum_eq_difference] at he
  linarith

lemma boundaryPoisson_at_zero (F : ℂ → RiemannSphere) {R : ℝ} (hR : 0 < R) :
    boundaryPoisson F R 0 = boundaryMean F R := by
  unfold boundaryPoisson boundaryMean
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  simp [circleMap_eq_center_iff, hR.ne']

/-- Center specialization, with the exact normalization log(R/|a|) and the
opposite signs for zeros and poles. -/
theorem jensen : Specs.D12Complex.Ch17.PoissonJensen.jensen_type := by
  intro U F R hF hR hsub hb hfin hn
  have hz : (0 : ℂ) ∈ ball (0 : ℂ) R := by simpa using hR
  have he := poisson_jensen U F R hF hR hsub hb 0 hz hfin hn
  rw [boundaryPoisson_at_zero F hR] at he
  have hdz : diskDivisor F R 0 = 0 := by
    rw [diskDivisor, divisor_apply (disk_meromorphic hF hsub) (ball_subset_closedBall hz),
      regular_order_zero hF (hsub (ball_subset_closedBall hz)) hfin hn]
    rfl
  have hzsum : (∑ᶠ a : ℂ, (zeroMultiplicity F R a : ℝ) * green R 0 a) =
      ∑ᶠ a : ℂ, (zeroMultiplicity F R a : ℝ) * Real.log (R / ‖a‖) := by
    apply finsum_congr
    intro a
    by_cases ha : a = 0
    · subst a
      simp [zeroMultiplicity, hdz]
    · rw [green_at_zero hR ha]
  have hpsum : (∑ᶠ a : ℂ, (poleMultiplicity F R a : ℝ) * green R 0 a) =
      ∑ᶠ a : ℂ, (poleMultiplicity F R a : ℝ) * Real.log (R / ‖a‖) := by
    apply finsum_congr
    intro a
    by_cases ha : a = 0
    · subst a
      simp [poleMultiplicity, hdz]
    · rw [green_at_zero hR ha]
  rw [hzsum, hpsum] at he
  linarith

end D12Complex.PoissonJensen
