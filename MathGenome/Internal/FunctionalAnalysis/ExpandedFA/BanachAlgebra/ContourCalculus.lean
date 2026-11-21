import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Separation.Basic
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Topology.Instances.Int
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Asymptotics.Lemmas
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.ContourCalculus
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.NeumannResolvent
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.NonemptySpectrum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
Contour-integral foundations and fixed-contour estimates for Riesz–Dunford
calculus. No existence or Cauchy theorem is assumed by these definitions.
-/

noncomputable section

namespace ExpandedFA.BanachAlgebra.ContourCalculus

open Set MeasureTheory Filter
open scoped Topology

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]

lemma C1Arc.continuousOn_path (γ : C1Arc) : ContinuousOn γ.path (Icc 0 1) :=
  γ.smooth.continuousOn

lemma C1Arc.continuousOn_velocity (γ : C1Arc) : ContinuousOn γ.velocity (Icc 0 1) :=
  γ.smooth.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl

lemma Cycle.path_mem_trace (Γ : Cycle) (i : Fin Γ.count) {t : ℝ} (ht : t ∈ Icc 0 1) :
    (Γ.arc i).path t ∈ Γ.trace :=
  mem_iUnion.mpr ⟨i, mem_image_of_mem _ ht⟩

lemma Cycle.isCompact_trace (Γ : Cycle) : IsCompact Γ.trace :=
  isCompact_iUnion fun i => isCompact_Icc.image_of_continuousOn (Γ.arc i).continuousOn_path

lemma Cycle.length_nonneg (Γ : Cycle) : 0 ≤ Γ.length :=
  Finset.sum_nonneg fun _i _ => intervalIntegral.integral_nonneg_of_forall zero_le_one
    (fun _ => norm_nonneg _)

/-- Continuous vector integrands really are integrable on every arc. -/
lemma cycle_integrable (Γ : Cycle) {h : ℂ → X} (hh : ContinuousOn h Γ.trace)
    (i : Fin Γ.count) :
    IntervalIntegrable (fun t => (Γ.arc i).velocity t • h ((Γ.arc i).path t))
      volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
  exact (Γ.arc i).continuousOn_velocity.smul
    (hh.comp (Γ.arc i).continuousOn_path (fun t ht => Γ.path_mem_trace i ht))

lemma cycleIntegral_sub [CompleteSpace X] (Γ : Cycle) {h k : ℂ → X}
    (hh : ContinuousOn h Γ.trace) (hk : ContinuousOn k Γ.trace) :
    cycleIntegral Γ (fun z => h z - k z) = cycleIntegral Γ h - cycleIntegral Γ k := by
  simp only [cycleIntegral, smul_sub, intervalIntegral.integral_sub
    (cycle_integrable Γ hh _) (cycle_integrable Γ hk _), Finset.sum_sub_distrib]

/-- A Banach-valued ML estimate, with the actual arc length. -/
lemma norm_cycleIntegral_le (Γ : Cycle) {h : ℂ → X} {C : ℝ}
    (hh : ContinuousOn h Γ.trace) (_hC : 0 ≤ C)
    (hbound : ∀ z ∈ Γ.trace, ‖h z‖ ≤ C) :
    ‖cycleIntegral Γ h‖ ≤ Γ.length * C := by
  calc
    ‖cycleIntegral Γ h‖ ≤ ∑ i, ‖∫ t in (0 : ℝ)..1,
        (Γ.arc i).velocity t • h ((Γ.arc i).path t)‖ := norm_sum_le _ _
    _ ≤ ∑ i, (∫ t in (0 : ℝ)..1, ‖(Γ.arc i).velocity t‖) * C := by
      apply Finset.sum_le_sum
      intro i _
      calc
        ‖∫ t in (0 : ℝ)..1, (Γ.arc i).velocity t • h ((Γ.arc i).path t)‖
            ≤ ∫ t in (0 : ℝ)..1, ‖(Γ.arc i).velocity t • h ((Γ.arc i).path t)‖ :=
          intervalIntegral.norm_integral_le_integral_norm zero_le_one
        _ ≤ ∫ t in (0 : ℝ)..1, ‖(Γ.arc i).velocity t‖ * C := by
          apply intervalIntegral.integral_mono_on zero_le_one
            (cycle_integrable Γ hh i).norm
            (((Γ.arc i).continuousOn_velocity.norm.mul continuousOn_const).intervalIntegrable_of_Icc zero_le_one)
          intro t ht
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_left (hbound _ (Γ.path_mem_trace i ht)) (norm_nonneg _)
        _ = (∫ t in (0 : ℝ)..1, ‖(Γ.arc i).velocity t‖) * C :=
          intervalIntegral.integral_mul_const _ _
    _ = Γ.length * C := (Finset.sum_mul ..).symm

/-- The integral of a derivative telescopes on an endpoint-matched finite cycle. -/
lemma cycleIntegral_derivative_eq_zero [CompleteSpace X] (Γ : Cycle)
    {H H' : ℂ → X} (hH' : ContinuousOn H' Γ.trace)
    (hH : ∀ z ∈ Γ.trace, HasDerivAt H (H' z) z) :
    cycleIntegral Γ H' = 0 := by
  have hcont : ContinuousOn H Γ.trace :=
    fun z hz => (hH z hz).continuousAt.continuousWithinAt
  have hi (i : Fin Γ.count) :
      (∫ t in (0 : ℝ)..1, (Γ.arc i).velocity t • H' ((Γ.arc i).path t)) =
        H ((Γ.arc i).path 1) - H ((Γ.arc i).path 0) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
      (hcont.comp (Γ.arc i).continuousOn_path (fun t ht => Γ.path_mem_trace i ht))
      _ (cycle_integrable Γ hH' i)
    intro t ht
    have hd := (Γ.arc i).smooth.differentiableOn_one t (Ioo_subset_Icc_self ht)
    have hγ := hd.hasDerivWithinAt.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    exact (hH _ (Γ.path_mem_trace i (Ioo_subset_Icc_self ht))).scomp t hγ
  simp only [cycleIntegral, hi, Finset.sum_sub_distrib]
  have hs : (∑ i, H ((Γ.arc i).path 1)) = ∑ i, H ((Γ.arc i).path 0) := by
    simpa only [Γ.joins] using Equiv.sum_comp Γ.next (fun i => H ((Γ.arc i).path 0))
  exact sub_eq_zero.mpr hs

/-- The reciprocal kernel is continuous wherever its pole misses the trace. -/
lemma continuousOn_cycle_kernel (Γ : Cycle) {z : ℂ} (hz : z ∉ Γ.trace) :
    ContinuousOn (fun w => (w - z)⁻¹) Γ.trace := by
  exact (continuous_id.continuousOn.sub continuousOn_const).inv₀
    (fun w hw => sub_ne_zero.mpr (fun h => hz (by
      change w = z at h
      exact h ▸ hw)))

/-- The logarithm of a quotient supplies a single-valued primitive for the
kernel difference when the two poles are sufficiently close. -/
lemma Cycle.winding_eq_of_close (Γ : Cycle) {z z₀ : ℂ}
    (hclose : ∀ w ∈ Γ.trace, ‖z - z₀‖ < ‖w - z₀‖) :
    Γ.winding z = Γ.winding z₀ := by
  have hz₀ : z₀ ∉ Γ.trace := by
    intro hz₀
    have := hclose z₀ hz₀
    simp only [sub_self, norm_zero] at this
    exact (norm_nonneg _).not_gt this
  have hz : z ∉ Γ.trace := by
    intro hz
    exact (hclose z hz).false
  have hp : ∀ w ∈ Γ.trace,
      HasDerivAt (fun v : ℂ => Complex.log (1 + (z₀ - z) / (v - z₀)))
        ((w - z)⁻¹ - (w - z₀)⁻¹) w := by
    intro w hw
    have hw₀ : w - z₀ ≠ 0 := sub_ne_zero.mpr (fun h => hz₀ (h ▸ hw))
    have hwz : w - z ≠ 0 := sub_ne_zero.mpr (fun h => hz (h ▸ hw))
    have hsmall : ‖(z₀ - z) / (w - z₀)‖ < 1 := by
      rw [norm_div, norm_sub_rev z₀ z]
      exact (div_lt_one (norm_pos_iff.mpr hw₀)).mpr (hclose w hw)
    have hlog := Complex.mem_slitPlane_of_norm_lt_one hsmall
    have hd := (Complex.hasDerivAt_log hlog).comp w
      (((hasDerivAt_const w (z₀ - z)).div ((hasDerivAt_id w).sub_const z₀) hw₀).const_add 1)
    have hfrac : 1 + (z₀ - z) / (w - z₀) = (w - z) / (w - z₀) := by
      field_simp
      <;> ring
    simp only [id_eq, Pi.div_apply, zero_mul, mul_one, zero_sub] at hd
    rw [hfrac] at hd
    convert hd using 1
    · rfl
    · field_simp [hw₀, hwz]
      <;> ring
  have hi := cycleIntegral_derivative_eq_zero Γ
    ((continuousOn_cycle_kernel Γ hz).sub (continuousOn_cycle_kernel Γ hz₀)) hp
  change cycleIntegral Γ (fun w => (w - z)⁻¹ - (w - z₀)⁻¹) = 0 at hi
  rw [cycleIntegral_sub Γ (continuousOn_cycle_kernel Γ hz)
    (continuousOn_cycle_kernel Γ hz₀)] at hi
  exact congrArg (fun q : ℂ => (2 * Real.pi * Complex.I : ℂ)⁻¹ * q)
    (sub_eq_zero.mp hi)

/-- Winding is locally constant off the trace, without an integrality premise. -/
lemma Cycle.winding_eventually_eq (Γ : Cycle) {z : ℂ} (hz : z ∉ Γ.trace) :
    ∀ᶠ w in 𝓝 z, Γ.winding w = Γ.winding z := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp Γ.isCompact_trace.isClosed.isOpen_compl z hz
  filter_upwards [Metric.ball_mem_nhds z hr] with w hw
  apply Γ.winding_eq_of_close
  intro v hv
  have hvdist : r ≤ dist v z := le_of_not_gt (fun h => hball h hv)
  simpa only [dist_eq_norm] using (Metric.mem_ball.mp hw).trans_le hvdist

/-- The zero-index part of the complement is open; this is the domain used
in the entire-function proof of homological Cauchy. -/
lemma Cycle.isOpen_zero_winding (Γ : Cycle) :
    IsOpen {z : ℂ | z ∉ Γ.trace ∧ Γ.winding z = 0} := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  filter_upwards [Γ.isCompact_trace.isClosed.isOpen_compl.mem_nhds hz.1,
    Γ.winding_eventually_eq hz.1] with w hw he
  exact ⟨hw, he.trans hz.2⟩

/-- Outside a disk containing the trace, log(1-w/z) is a primitive of the
reciprocal kernel. Thus the exterior winding vanishes exactly. -/
lemma Cycle.winding_eq_zero_of_norm_lt (Γ : Cycle) {z : ℂ}
    (hz : z ≠ 0) (hbound : ∀ w ∈ Γ.trace, ‖w‖ < ‖z‖) :
    Γ.winding z = 0 := by
  have htrace : z ∉ Γ.trace := fun h => (hbound z h).false
  have hp : ∀ w ∈ Γ.trace,
      HasDerivAt (fun v : ℂ => Complex.log (1 + -v / z)) ((w - z)⁻¹) w := by
    intro w hw
    have hsmall : ‖-w / z‖ < 1 := by
      rw [norm_div, norm_neg]
      exact (div_lt_one (norm_pos_iff.mpr hz)).mpr (hbound w hw)
    have hd := (Complex.hasDerivAt_log (Complex.mem_slitPlane_of_norm_lt_one hsmall)).comp w
      (((hasDerivAt_id w).neg.div_const z).const_add 1)
    have hwz : w - z ≠ 0 := sub_ne_zero.mpr (fun h => htrace (h ▸ hw))
    have hfrac : 1 + -w / z = -(w - z) / z := by
      field_simp
      <;> ring
    rw [hfrac] at hd
    convert hd using 1
    · rfl
    · field_simp [hz, hwz]
      <;> ring
  rw [Cycle.winding, cycleIntegral_derivative_eq_zero Γ
    (continuousOn_cycle_kernel Γ htrace) hp, mul_zero]

/-- The filled trace, including all nonzero-index components, is compact. -/
lemma Cycle.isCompact_filledTrace (Γ : Cycle) :
    IsCompact {z : ℂ | z ∈ Γ.trace ∨ Γ.winding z ≠ 0} := by
  have hclosed : IsClosed {z : ℂ | z ∈ Γ.trace ∨ Γ.winding z ≠ 0} := by
    convert Γ.isOpen_zero_winding.isClosed_compl using 1
    ext z
    simp only [mem_ofPred_eq, mem_compl_iff, not_and_or, not_not]
  apply Metric.isCompact_of_isClosed_isBounded hclosed
  obtain ⟨R, hR⟩ := Γ.isCompact_trace.exists_bound_of_continuousOn
    (continuous_id.continuousOn : ContinuousOn (fun z : ℂ => z) Γ.trace)
  apply Metric.isBounded_iff_subset_closedBall 0 |>.mpr
  refine ⟨max R 0, ?_⟩
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hn
  have hnorm : max R 0 < ‖z‖ := lt_of_not_ge hn
  have hne : z ≠ 0 := norm_pos_iff.mp ((le_max_right R 0).trans_lt hnorm)
  have hb : ∀ w ∈ Γ.trace, ‖w‖ < ‖z‖ :=
    fun w hw => (hR w hw).trans_lt ((le_max_left R 0).trans_lt hnorm)
  rcases hz with hz | hz
  · exact (hb z hz).false
  · exact hz (Γ.winding_eq_zero_of_norm_lt hne hb)

/-- Functionals commute with finite contour integrals, with the original scalar-linear dual. -/
lemma dual_cycleIntegral [CompleteSpace X] (Γ : Cycle) (ℓ : X →L[ℂ] ℂ)
    {h : ℂ → X} (hh : ContinuousOn h Γ.trace) :
    ℓ (cycleIntegral Γ h) = cycleIntegral Γ (fun z => ℓ (h z)) := by
  simp only [cycleIntegral, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← ℓ.intervalIntegral_comp_comm (cycle_integrable Γ hh i)]
  simp only [map_smul]

abbrev contourValue : Spec.ContourValueType.{u} := Spec.ContourValueValue

variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

lemma continuousOn_resolvent_trace (Γ : Cycle) (a : A)
    (hΓ : Γ.trace ⊆ algebraResolventSet ℂ A a) :
    ContinuousOn (algebraResolvent ℂ A a) Γ.trace := by
  change ContinuousOn (fun z => Ring.inverse (algebraMap ℂ A z - a)) Γ.trace
  exact (analyticOnNhd_inverse (𝕜 := ℂ) (A := A)).continuousOn.comp
    ((continuous_algebraMap ℂ A).sub continuous_const).continuousOn
    (fun z hz => hΓ hz)

lemma contour_integrand_continuous (Γ : Cycle) (a : A) {f : ℂ → ℂ}
    (hΓ : Γ.trace ⊆ algebraResolventSet ℂ A a) (hf : ContinuousOn f Γ.trace) :
    ContinuousOn (fun z => f z • algebraResolvent ℂ A a z) Γ.trace :=
  hf.smul (continuousOn_resolvent_trace Γ a hΓ)

/-- Quantitative dependence on the scalar function along a fixed contour. -/
theorem contour_norm_estimate : Spec.ContourNormEstimate.{u} := by
  intro A _ _ _ Γ a f g M ε hΓ hf hg hM hε hres hfg
  have hcf := contour_integrand_continuous Γ a hΓ hf
  have hcg := contour_integrand_continuous Γ a hΓ hg
  change ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ • cycleIntegral Γ
      (fun z => f z • algebraResolvent ℂ A a z) -
    (2 * Real.pi * Complex.I : ℂ)⁻¹ • cycleIntegral Γ
      (fun z => g z • algebraResolvent ℂ A a z)‖ ≤ _
  rw [← smul_sub, ← cycleIntegral_sub Γ hcf hcg, norm_smul]
  have hb : ∀ z ∈ Γ.trace,
      ‖f z • algebraResolvent ℂ A a z - g z • algebraResolvent ℂ A a z‖ ≤ M * ε := by
    intro z hz
    rw [← sub_smul, norm_smul]
    calc
      ‖f z - g z‖ * ‖algebraResolvent ℂ A a z‖ ≤ ε * M :=
        mul_le_mul (hfg z hz) (hres z hz) (norm_nonneg _) hε
      _ = M * ε := mul_comm _ _
  calc
    _ ≤ ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ * (Γ.length * (M * ε)) :=
      mul_le_mul_of_nonneg_left (norm_cycleIntegral_le Γ (hcf.sub hcg)
        (mul_nonneg hM hε) hb) (norm_nonneg _)
    _ = _ := by ring

/-- Uniform convergence on the fixed compact trace gives convergence in algebra norm. -/
theorem fixed_contour_convergence : Spec.FixedContourConvergence.{u} := by
  intro A _ _ _ Γ a f F hΓ hf hF hlim
  obtain ⟨M₀, hM₀⟩ := Γ.isCompact_trace.exists_bound_of_continuousOn
    (continuousOn_resolvent_trace Γ a hΓ)
  let M : ℝ := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hres : ∀ z ∈ Γ.trace, ‖algebraResolvent ℂ A a z‖ ≤ M :=
    fun z hz => (hM₀ z hz).trans (le_max_left _ _)
  let C : ℝ := ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ * Γ.length * M
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (norm_nonneg _) Γ.length_nonneg) hM
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hδ : 0 < ε / (C + 1) := div_pos hε (by positivity)
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hlim) _ hδ] with n hn
  rw [dist_eq_norm]
  have hb := contour_norm_estimate A Γ a (F n) f M (ε / (C + 1))
    hΓ (hF n) hf hM hδ.le hres (fun z hz => by
      have h := hn z hz
      rw [dist_comm, dist_eq_norm] at h
      exact h.le)
  change ‖contourValue A Γ a (F n) - contourValue A Γ a f‖ ≤
    C * (ε / (C + 1)) at hb
  apply hb.trans_lt
  calc
    C * (ε / (C + 1)) < (C + 1) * (ε / (C + 1)) :=
      mul_lt_mul_of_pos_right (lt_add_one C) hδ
    _ = ε := mul_div_cancel₀ _ (by positivity : C + 1 ≠ 0)

/-! Reusable reductions to geometric existence and scalar homological Cauchy.
The unconditional proofs of both ingredients appear below. -/

lemma cycleIntegral_congr (Γ : Cycle) {h k : ℂ → X} (hk : EqOn h k Γ.trace) :
    cycleIntegral Γ h = cycleIntegral Γ k := by
  apply Finset.sum_congr rfl
  intro i _
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  dsimp only
  rw [hk (Γ.path_mem_trace i ht)]

lemma Cycle.Admissible.winding_eq_one {Γ : Cycle} {K U : Set ℂ}
    (hΓ : Γ.Admissible K U) {z : ℂ} (hz : z ∈ K) : Γ.winding z = 1 := by
  obtain ⟨V, _, hKV, _, hV⟩ := hΓ.2.2.1
  exact hV z (hKV hz)

lemma Cycle.Admissible.mono_domain {Γ : Cycle} {K U V : Set ℂ}
    (hΓ : Γ.Admissible K U) (hUV : U ⊆ V) : Γ.Admissible K V := by
  refine ⟨fun z hz => ⟨hUV (hΓ.1 hz).1, (hΓ.1 hz).2⟩,
    hΓ.2.1, hΓ.2.2.1, ?_⟩
  exact fun z hz => hΓ.2.2.2 z (fun hzU => hz (hUV hzU))

/-- Transfer the scalar equal-index Cauchy theorem to any complex Banach space. -/
lemma vector_cauchy_of_scalar [CompleteSpace X] (hCauchy : Spec.HomologicalCauchy)
    (U : Set ℂ) (Γ Δ : Cycle) (h : ℂ → X) (hU : IsOpen U)
    (hΓ : Γ.trace ⊆ U) (hΔ : Δ.trace ⊆ U)
    (hwind : ∀ z ∉ U, Γ.winding z = Δ.winding z)
    (hh : DifferentiableOn ℂ h U) : cycleIntegral Γ h = cycleIntegral Δ h := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  intro ℓ
  rw [dual_cycleIntegral Γ ℓ (hh.continuousOn.mono hΓ),
    dual_cycleIntegral Δ ℓ (hh.continuousOn.mono hΔ)]
  exact hCauchy U Γ Δ (fun z => ℓ (h z)) hU hΓ hΔ hwind
    (ℓ.differentiable.comp_differentiableOn hh)

/-- Reduction of the full fixed-domain independence statement to scalar Cauchy. -/
theorem cycle_independence_of_cauchy (hCauchy : Spec.HomologicalCauchy) :
    Spec.CycleIndependence.{u} := by
  intro A _ _ hA a U f hU _hfU hf Γ Δ hΓ hΔ
  let : CompleteSpace A := hA.1
  let K : Set ℂ := algebraSpectrum ℂ A a
  have hopen : IsOpen (U \ K) := hU.sdiff (spectrum.isClosed a)
  have hres : DifferentiableOn ℂ (algebraResolvent ℂ A a) (U \ K) :=
    (algebra_resolvent_analytic A hA a).differentiableOn.mono (fun _ hz => not_not.mp hz.2)
  have hw : ∀ z ∉ U \ K, Γ.winding z = Δ.winding z := by
    intro z hz
    by_cases hzK : z ∈ K
    · rw [hΓ.winding_eq_one hzK, hΔ.winding_eq_one hzK]
    · have hzU : z ∉ U := fun hzU => hz ⟨hzU, hzK⟩
      rw [hΓ.2.2.2 z hzU, hΔ.2.2.2 z hzU]
  have he := vector_cauchy_of_scalar hCauchy (U \ K) Γ Δ
    (fun z => f z • algebraResolvent ℂ A a z) hopen hΓ.1 hΔ.1 hw
    ((hf.mono sdiff_subset).smul hres)
  exact congrArg (fun x : A => (2 * Real.pi * Complex.I : ℂ)⁻¹ • x) he

/-- Changing the germ requires a common smaller admissible contour. -/
theorem neighborhood_independence_of_cycles
    (hexists : Spec.AdmissibleCyclesExist) (hind : Spec.CycleIndependence.{u}) :
    Spec.NeighborhoodIndependence.{u} := by
  intro A _ _ hA a U V W f g hU hV hW hKW hWUV hf hg hfg Γ Δ hΓ hΔ
  obtain ⟨Λ, hΛ⟩ := hexists (algebraSpectrum ℂ A a) W
    (algebra_spectrum_properties A hA a).2.1 hW hKW
  have hΛU := hΛ.mono_domain (fun z hz => (hWUV hz).1)
  have hΛV := hΛ.mono_domain (fun z hz => (hWUV hz).2)
  calc
    _ = Spec.ContourValueValue A Λ a f :=
      hind A hA a U f hU (fun z hz => (hWUV (hKW hz)).1) hf Γ Λ hΓ hΛU
    _ = Spec.ContourValueValue A Λ a g := by
      apply congrArg (fun x : A => (2 * Real.pi * Complex.I : ℂ)⁻¹ • x)
      apply cycleIntegral_congr
      intro z hz
      dsimp only
      rw [hfg (hΛ.1 hz).1]
    _ = _ := hind A hA a V g hV (fun z hz => (hWUV (hKW hz)).2) hg Λ Δ hΛV hΔ

abbrev selectedCycle : Spec.SelectedCycleType := Spec.SelectedCycleValue

/-- Total representation of f(a); admissibility and the formula are subsequent obligations. -/
abbrev holomorphicValue : Spec.HolomorphicValueType.{u} := Spec.HolomorphicValueValue

/-- Geometric existence justifies the total choice of contour. -/
theorem selected_cycle_admissible_of_exists (hexists : Spec.AdmissibleCyclesExist) :
    Spec.SelectedCycleAdmissible.{u} := by
  intro A _ _ hA a U hU hKU
  exact Classical.epsilon_spec
    (hexists _ U (algebra_spectrum_properties A hA a).2.1 hU hKU)

/-- Geometric existence and cycle independence give the defining formula. -/
theorem holomorphic_formula_of_cycles (hexists : Spec.AdmissibleCyclesExist)
    (hind : Spec.CycleIndependence.{u}) : Spec.HolomorphicFormula.{u} := by
  intro A _ _ hA a U f hU hKU hf Γ hΓ
  exact hind A hA a U f hU hKU hf _ Γ
    (selected_cycle_admissible_of_exists hexists A hA a U hU hKU) hΓ

end ExpandedFA.BanachAlgebra.ContourCalculus



noncomputable section
namespace ExpandedFA.BanachAlgebra.ContourCalculus
open Set MeasureTheory Filter
open scoped Topology
universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]

def C1Arc.reverse (γ : C1Arc) : C1Arc where
  path t := γ.path (1 - t)
  smooth := γ.smooth.comp ((contDiff_const.sub contDiff_id).contDiffOn)
    (fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩)

lemma C1Arc.velocity_reverse (γ : C1Arc) {t : ℝ} (ht : t ∈ Icc 0 1) :
    γ.reverse.velocity t = -γ.velocity (1 - t) := by
  have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hd := (γ.smooth.differentiableOn_one (1 - t) ht').hasDerivWithinAt.scomp t
    (((hasDerivAt_id t).const_sub 1).hasDerivWithinAt)
    (show MapsTo (fun t : ℝ => 1 - t) (Icc 0 1) (Icc 0 1) from
      fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩)
  simpa [C1Arc.velocity, C1Arc.reverse, Function.comp_def] using
    hd.derivWithin (uniqueDiffOn_Icc_zero_one t ht)

def Cycle.reverse (Γ : Cycle) : Cycle where
  count := Γ.count
  arc i := (Γ.arc i).reverse
  next := Γ.next.symm
  joins i := by
    simp only [C1Arc.reverse, sub_self, sub_zero]
    simpa using (Γ.joins (Γ.next.symm i)).symm

lemma Cycle.trace_reverse (Γ : Cycle) : Γ.reverse.trace = Γ.trace := by
  ext z
  simp only [Cycle.trace, mem_iUnion, mem_image]
  constructor
  · rintro ⟨i, t, ht, hz⟩
    refine ⟨i, 1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, hz⟩
  · rintro ⟨i, t, ht, hz⟩
    refine ⟨i, 1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    simpa only [Cycle.reverse, C1Arc.reverse, sub_sub_cancel] using hz

lemma cycleIntegral_reverse (Γ : Cycle) (h : ℂ → X) :
    cycleIntegral Γ.reverse h = -cycleIntegral Γ h := by
  change (∑ i : Fin Γ.count, ∫ t in (0 : ℝ)..1,
    (Γ.arc i).reverse.velocity t • h ((Γ.arc i).reverse.path t)) =
    -(∑ i : Fin Γ.count, ∫ t in (0 : ℝ)..1, (Γ.arc i).velocity t • h ((Γ.arc i).path t))
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∫ t in (0 : ℝ)..1, -((Γ.arc i).velocity (1 - t) • h ((Γ.arc i).path (1 - t))) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      change (Γ.arc i).reverse.velocity t • h ((Γ.arc i).path (1 - t)) = _
      rw [C1Arc.velocity_reverse _ ht, neg_smul]
    _ = -(∫ t in (0 : ℝ)..1, (Γ.arc i).velocity t • h ((Γ.arc i).path t)) := by
      rw [intervalIntegral.integral_neg]
      congr 1
      simpa using intervalIntegral.integral_comp_sub_left
        (fun t => (Γ.arc i).velocity t • h ((Γ.arc i).path t)) (a := 0) (b := 1) 1

lemma Cycle.winding_reverse (Γ : Cycle) (z : ℂ) : Γ.reverse.winding z = -Γ.winding z := by
  simp [Cycle.winding, cycleIntegral_reverse]

end ExpandedFA.BanachAlgebra.ContourCalculus

namespace ExpandedFA.BanachAlgebra.ContourCalculus
open Set MeasureTheory Filter
open scoped Topology
universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Disjoint union of the finite arc lists, retaining each successor permutation. -/
def Cycle.append (Γ Δ : Cycle) : Cycle where
  count := Γ.count + Δ.count
  arc i := Sum.elim Γ.arc Δ.arc (finSumFinEquiv.symm i)
  next := (finSumFinEquiv.symm.trans (Equiv.sumCongr Γ.next Δ.next)).trans finSumFinEquiv
  joins i := by
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    cases i with
    | inl i => simpa using Γ.joins i
    | inr i => simpa using Δ.joins i

lemma cycleIntegral_append (Γ Δ : Cycle) (h : ℂ → X) :
    cycleIntegral (Γ.append Δ) h = cycleIntegral Γ h + cycleIntegral Δ h := by
  change (∑ i : Fin (Γ.count + Δ.count), ∫ t in (0 : ℝ)..1,
    ((Γ.append Δ).arc i).velocity t • h (((Γ.append Δ).arc i).path t)) = _
  rw [Fin.sum_univ_add]
  simp [Cycle.append, cycleIntegral]

lemma Cycle.trace_append (Γ Δ : Cycle) : (Γ.append Δ).trace = Γ.trace ∪ Δ.trace := by
  ext z
  simp only [Cycle.trace, mem_iUnion, mem_union]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    cases i with
    | inl i => exact Or.inl ⟨i, by simpa [Cycle.append] using hi⟩
    | inr i => exact Or.inr ⟨i, by simpa [Cycle.append] using hi⟩
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact ⟨finSumFinEquiv (Sum.inl i), by simpa [Cycle.append] using hi⟩
    · exact ⟨finSumFinEquiv (Sum.inr i), by simpa [Cycle.append] using hi⟩

lemma Cycle.winding_append (Γ Δ : Cycle) (z : ℂ) :
    (Γ.append Δ).winding z = Γ.winding z + Δ.winding z := by
  simp [Cycle.winding, cycleIntegral_append, mul_add]

/-- The equal-index formulation follows from null-homologous Cauchy on one cycle. -/
lemma homologicalCauchy_of_null
    (hnull : ∀ (U : Set ℂ) (Γ : Cycle) (h : ℂ → ℂ), IsOpen U →
      Γ.trace ⊆ U → (∀ z ∉ U, Γ.winding z = 0) →
      DifferentiableOn ℂ h U → cycleIntegral Γ h = 0) : Spec.HomologicalCauchy := by
  intro U Γ Δ h hU hΓ hΔ hw hh
  have htrace : (Γ.append Δ.reverse).trace ⊆ U := by
    rw [Cycle.trace_append, Cycle.trace_reverse]
    exact union_subset hΓ hΔ
  have hwind : ∀ z ∉ U, (Γ.append Δ.reverse).winding z = 0 := by
    intro z hz
    rw [Cycle.winding_append, Cycle.winding_reverse, hw z hz, add_neg_cancel]
  have hi := hnull U (Γ.append Δ.reverse) h hU htrace hwind hh
  rw [cycleIntegral_append, cycleIntegral_reverse, ← sub_eq_add_neg] at hi
  exact sub_eq_zero.mp hi

end ExpandedFA.BanachAlgebra.ContourCalculus


noncomputable section
namespace ExpandedFA.BanachAlgebra.ContourCalculus
open Set MeasureTheory Filter
open scoped Topology

@[simp] lemma empty_trace : Cycle.empty.trace = ∅ := by
  simp [Cycle.trace, Cycle.empty]

@[simp] lemma empty_cycleIntegral {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (h : ℂ → X) : cycleIntegral Cycle.empty h = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  exact Fin.elim0 i

@[simp] lemma empty_winding (z : ℂ) : Cycle.empty.winding z = 0 := by
  simp [Cycle.winding]

lemma empty_admissible (U : Set ℂ) : Cycle.empty.Admissible ∅ U := by
  refine ⟨by simp, ?_, ⟨∅, isOpen_empty, by simp, by simp, by simp⟩, ?_⟩
  · intro z hz
    exact Or.inl (empty_winding z)
  · intro z hz
    exact empty_winding z

/-- A balanced finite family of arcs admits an endpoint-matching permutation. -/
def cycleOfBalancedArcs {ι : Type*} [Fintype ι]
    (γ : ι → C1Arc)
    (hbalanced : ∀ z : ℂ,
      Fintype.card {i : ι // (γ i).path 1 = z} =
        Fintype.card {i : ι // (γ i).path 0 = z}) : Cycle := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let p : Equiv.Perm ι :=
    Equiv.ofFiberEquiv (fun z => Fintype.equivOfCardEq (hbalanced z))
  have hp : ∀ i, (γ (p i)).path 0 = (γ i).path 1 :=
    Equiv.ofFiberEquiv_map (fun z => Fintype.equivOfCardEq (hbalanced z))
  exact {
    count := Fintype.card ι
    arc := fun i => γ (e.symm i)
    next := (e.symm.trans p).trans e
    joins := fun i => by simpa using (hp (e.symm i)).symm
  }

lemma cycleOfBalancedArcs_trace {ι : Type*} [Fintype ι]
    (γ : ι → C1Arc) (hbalanced : ∀ z : ℂ,
      Fintype.card {i : ι // (γ i).path 1 = z} =
        Fintype.card {i : ι // (γ i).path 0 = z}) :
    (cycleOfBalancedArcs γ hbalanced).trace = ⋃ i, (γ i).path '' Icc 0 1 := by
  ext z
  simp only [Cycle.trace, cycleOfBalancedArcs, mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨_, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨Fintype.equivFin ι i, by simpa using hi⟩

lemma cycleOfBalancedArcs_integral {ι : Type*} [Fintype ι]
    (γ : ι → C1Arc) (hbalanced : ∀ z : ℂ,
      Fintype.card {i : ι // (γ i).path 1 = z} =
        Fintype.card {i : ι // (γ i).path 0 = z})
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (h : ℂ → X) :
    cycleIntegral (cycleOfBalancedArcs γ hbalanced) h =
      ∑ i, ∫ t in (0 : ℝ)..1, (γ i).velocity t • h ((γ i).path t) := by
  classical
  dsimp [cycleIntegral, cycleOfBalancedArcs]
  exact Equiv.sum_comp (Fintype.equivFin ι).symm
    (fun i : ι => ∫ t in (0 : ℝ)..1, (γ i).velocity t • h ((γ i).path t))

/-- The uniform closed buffer needed for small grid cells in the geometric construction. -/
lemma compact_uniform_buffer {K U : Set ℂ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ K ⊆ U :=
  hK.exists_cthickening_subset_open hU hKU

end ExpandedFA.BanachAlgebra.ContourCalculus


noncomputable section
open Set Filter
open scoped Topology

namespace ExpandedFA.BanachAlgebra.ContourCalculus

lemma dslope_symm (f : ℂ → ℂ) (x y : ℂ) : dslope f x y = dslope f y x := by
  by_cases h : x = y
  · subst y; rfl
  rw [dslope_of_ne _ (Ne.symm h), dslope_of_ne _ h, slope_def_field, slope_def_field]
  field_simp
  <;> ring

lemma continuousAt_dslope_pair_diagonal {f : ℂ → ℂ} {a : ℂ}
    (hstrict : HasStrictDerivAt f (deriv f a) a)
    (hderiv : ContinuousAt (deriv f) a) :
    ContinuousAt (fun p : ℂ × ℂ => dslope f p.1 p.2) (a, a) := by
  classical
  let E : ℂ × ℂ → ℂ := fun p =>
    (f p.1 - f p.2 - (p.1 - p.2) * deriv f a) / (p.1 - p.2)
  have hE : Tendsto E (𝓝 (a, a)) (𝓝 0) := by
    simpa only [E, smul_eq_mul] using (hasDerivAtFilter_iff_isLittleO.mp hstrict).tendsto_div_nhds_zero
  have hfirst : Tendsto (fun p : ℂ × ℂ => deriv f p.1) (𝓝 (a,a)) (𝓝 (deriv f a)) :=
    hderiv.tendsto.comp continuous_fst.continuousAt
  have hsecond : Tendsto (fun p : ℂ × ℂ => deriv f a + E p)
      (𝓝 (a,a)) (𝓝 (deriv f a)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hE
  have hif := hfirst.if' (p := fun p : ℂ × ℂ => p.1 = p.2) hsecond
  rw [ContinuousAt, dslope_same]
  apply hif.congr'
  apply Eventually.of_forall
  intro p
  dsimp only
  split_ifs with heq
  · rw [heq, dslope_same]
  · rw [dslope_of_ne _ (Ne.symm heq), slope_def_field]
    dsimp only [E]
    field_simp [sub_ne_zero.mpr heq]
    <;> ring

lemma continuousOn_dslope_pair {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    ContinuousOn (fun p : ℂ × ℂ => dslope f p.1 p.2) (U ×ˢ U) := by
  intro p hp
  have hfx : ContinuousAt f p.1 := (hf.differentiableAt (hU.mem_nhds hp.1)).continuousAt
  have hfy : ContinuousAt f p.2 := (hf.differentiableAt (hU.mem_nhds hp.2)).continuousAt
  by_cases heq : p.1 = p.2
  · have hstrict : HasStrictDerivAt f (deriv f p.1) p.1 :=
      (hf.contDiffOn hU : ContDiffOn ℂ 1 f U).contDiffAt (hU.mem_nhds hp.1) |>.hasStrictDerivAt (by simp)
    have hderiv : ContinuousAt (deriv f) p.1 :=
      (hf.deriv hU).continuousOn.continuousAt (hU.mem_nhds hp.1)
    have hpdiag : p = (p.1,p.1) := by ext <;> simp [heq]
    rw [hpdiag]
    exact (continuousAt_dslope_pair_diagonal hstrict hderiv).continuousWithinAt
  · have hquot : ContinuousAt
        (fun p : ℂ × ℂ => (f p.2 - f p.1) / (p.2 - p.1)) p :=
      ((hfy.comp continuous_snd.continuousAt).sub (hfx.comp continuous_fst.continuousAt)).div
        (continuous_snd.continuousAt.sub continuous_fst.continuousAt) (sub_ne_zero.mpr (Ne.symm heq))
    apply ContinuousAt.continuousWithinAt
    apply hquot.congr_of_eventuallyEq
    filter_upwards [(continuous_fst.continuousAt.sub continuous_snd.continuousAt).eventually_ne
      (sub_ne_zero.mpr heq)] with q hq
    rw [dslope_of_ne _ (sub_ne_zero.mp hq).symm, slope_def_field]

end ExpandedFA.BanachAlgebra.ContourCalculus

namespace ExpandedFA.BanachAlgebra.ContourCalculus
open MeasureTheory Metric

lemma continuousOn_parametric_intervalIntegral {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] {F : X → ℝ → ℂ} {U : Set X}
    {a b : ℝ} (hF : ContinuousOn F.uncurry (U ×ˢ Set.uIcc a b)) :
    ContinuousOn (fun z => ∫ t in a..b, F z t) U := by
  intro z hz
  have hc : ∀ᶠ w in 𝓝[U] z, ContinuousOn (F w) (Set.uIcc a b) := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hw,ht⟩)
  have hu : TendstoUniformlyOn F (F z) (𝓝[U] z) (Set.uIcc a b) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    obtain ⟨V, hV, hv⟩ := isCompact_uIcc.mem_uniformity_of_prod hF hz (dist_mem_uniformity hε)
    filter_upwards [hV] with w hw t ht
    simpa only [Set.mem_ofPred_eq, dist_comm] using hv w hw t ht
  exact hu.tendsto_intervalIntegral_of_continuousOn hc

end ExpandedFA.BanachAlgebra.ContourCalculus

namespace ExpandedFA.BanachAlgebra.ContourCalculus
open MeasureTheory

lemma continuousOn_parametric_cycleIntegral (Γ : Cycle) {F : ℂ → ℂ → ℂ} {U : Set ℂ}
    (hF : ContinuousOn F.uncurry (U ×ˢ Γ.trace)) :
    ContinuousOn (fun z => cycleIntegral Γ (F z)) U := by
  unfold cycleIntegral
  apply continuousOn_finsetSum
  intro i hi
  apply continuousOn_parametric_intervalIntegral
  simp only [Set.uIcc_of_le zero_le_one]
  have hpath : ContinuousOn (fun p : ℂ × ℝ => (Γ.arc i).path p.2)
      (U ×ˢ Icc 0 1) :=
    (Γ.arc i).continuousOn_path.comp continuous_snd.continuousOn (fun p hp => hp.2)
  have hvel : ContinuousOn (fun p : ℂ × ℝ => (Γ.arc i).velocity p.2)
      (U ×ˢ Icc 0 1) :=
    (Γ.arc i).continuousOn_velocity.comp continuous_snd.continuousOn (fun p hp => hp.2)
  exact hvel.smul (hF.comp (continuous_fst.continuousOn.prodMk hpath)
    (fun p hp => ⟨hp.1, Γ.path_mem_trace i hp.2⟩))

lemma continuousOn_cycleIntegral_dslope (Γ : Cycle) {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hΓ : Γ.trace ⊆ U) (hf : DifferentiableOn ℂ f U) :
    ContinuousOn (fun z => cycleIntegral Γ (dslope f z)) U :=
  continuousOn_parametric_cycleIntegral Γ
    ((continuousOn_dslope_pair hU hf).mono (Set.prod_mono Subset.rfl hΓ))

end ExpandedFA.BanachAlgebra.ContourCalculus

namespace ExpandedFA.BanachAlgebra.ContourCalculus

lemma differentiableOn_dslope_first {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {w : ℂ} (hw : w ∈ U) :
    DifferentiableOn ℂ (fun z => dslope f z w) U := by
  have hswap : (fun z => dslope f z w) = dslope f w :=
    funext fun z => dslope_symm f z w
  rw [hswap]
  exact (Complex.differentiableOn_dslope (hU.mem_nhds hw)).mpr hf

end ExpandedFA.BanachAlgebra.ContourCalculus





noncomputable section
namespace ExpandedFA.BanachAlgebra.ContourCalculus
open Set MeasureTheory Filter Metric
open scoped Topology

lemma cauchyKernel_tendsto_zero (Γ : Cycle) {h : ℂ → ℂ}
    (hh : ContinuousOn h Γ.trace) :
    Tendsto (fun z => cycleIntegral Γ (fun w => h w * (w-z)⁻¹))
      (cocompact ℂ) (𝓝 0) := by
  obtain ⟨R₀, hR₀⟩ := Γ.isCompact_trace.exists_bound_of_continuousOn
    (continuous_id.continuousOn : ContinuousOn (fun w : ℂ => w) Γ.trace)
  obtain ⟨M₀, hM₀⟩ := Γ.isCompact_trace.exists_bound_of_continuousOn hh
  let R : ℝ := max R₀ 0
  let M : ℝ := max M₀ 0
  have hR : ∀ w ∈ Γ.trace, ‖w‖ ≤ R := fun w hw => (hR₀ w hw).trans (le_max_left _ _)
  have hM : ∀ w ∈ Γ.trace, ‖h w‖ ≤ M := fun w hw => (hM₀ w hw).trans (le_max_left _ _)
  have hMpos : 0 ≤ M := le_max_right _ _
  have hlim : Tendsto (fun z : ℂ => (Γ.length * M) * (‖z‖ - R)⁻¹)
      (cocompact ℂ) (𝓝 0) := by
    simpa only [mul_zero, sub_eq_add_neg, Pi.inv_apply] using
      (tendsto_atTop_add_const_right (cocompact ℂ) (-R) (tendsto_norm_cocompact_atTop (E := ℂ))).inv_tendsto_atTop.const_mul (Γ.length * M)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [(tendsto_norm_cocompact_atTop (E := ℂ)).eventually_gt_atTop R] with z hz
  have hd : 0 < ‖z‖ - R := sub_pos.mpr hz
  have hztrace : z ∉ Γ.trace := fun hw => (hR z hw).not_gt hz
  have hdist : ∀ w ∈ Γ.trace, ‖z‖ - R ≤ ‖w-z‖ := by
    intro w hw
    calc
      ‖z‖ - R ≤ ‖z‖ - ‖w‖ := sub_le_sub_left (hR w hw) _
      _ ≤ ‖z-w‖ := norm_sub_norm_le z w
      _ = ‖w-z‖ := norm_sub_rev _ _
  have hb := norm_cycleIntegral_le Γ (hh.mul (continuousOn_cycle_kernel Γ hztrace))
    (mul_nonneg hMpos (inv_nonneg.mpr hd.le)) (fun w hw => ?_)
  · exact hb.trans_eq (by ring)
  · change ‖h w * (w-z)⁻¹‖ ≤ _
    rw [norm_mul, norm_inv]
    exact mul_le_mul (hM w hw) (inv_anti₀ hd (hdist w hw)) (by positivity) hMpos

lemma cycleIntegral_add_scalar (Γ : Cycle) {h k : ℂ → ℂ}
    (hh : ContinuousOn h Γ.trace) (hk : ContinuousOn k Γ.trace) :
    cycleIntegral Γ (fun w => h w + k w) = cycleIntegral Γ h + cycleIntegral Γ k := by
  simp only [cycleIntegral, smul_add, intervalIntegral.integral_add
    (cycle_integrable Γ hh _) (cycle_integrable Γ hk _), Finset.sum_add_distrib]

lemma cycleIntegral_eq_zero_of_eventually_cauchyKernel_eq_zero (Γ : Cycle) {h : ℂ → ℂ}
    (hh : ContinuousOn h Γ.trace)
    (hzero : ∀ᶠ z in cocompact ℂ, cycleIntegral Γ (fun w => h w * (w-z)⁻¹) = 0) :
    cycleIntegral Γ h = 0 := by
  have hwh : ContinuousOn (fun w => w * h w) Γ.trace := continuous_id.continuousOn.mul hh
  have hlim := cauchyKernel_tendsto_zero Γ hwh
  have heq : (fun z => cycleIntegral Γ (fun w => (w * h w) * (w-z)⁻¹)) =ᶠ[cocompact ℂ]
      (fun _ => cycleIntegral Γ h) := by
    have hout : ∀ᶠ z in cocompact ℂ, z ∉ Γ.trace := Γ.isCompact_trace.compl_mem_cocompact
    filter_upwards [hout, hzero] with z hz hzero
    have hc : ContinuousOn (fun w => h w * (w-z)⁻¹) Γ.trace :=
      hh.mul (continuousOn_cycle_kernel Γ hz)
    calc
      _ = cycleIntegral Γ (fun w => z * (h w * (w-z)⁻¹) + h w) := by
        apply cycleIntegral_congr
        intro w hw
        have hne : w-z ≠ 0 := sub_ne_zero.mpr (fun he => hz (he ▸ hw))
        field_simp
        <;> ring
      _ = z * cycleIntegral Γ (fun w => h w * (w-z)⁻¹) + cycleIntegral Γ h := by
        rw [cycleIntegral_add_scalar Γ (h := fun w => z * (h w * (w-z)⁻¹))
          (k := h) (continuousOn_const.mul hc) hh]
        congr 1
        simp only [cycleIntegral, smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t ht
        ring
      _ = _ := by rw [hzero, mul_zero, zero_add]
  exact tendsto_nhds_unique tendsto_const_nhds (hlim.congr' heq)

end ExpandedFA.BanachAlgebra.ContourCalculus




noncomputable section
open Set Filter
open scoped Topology

namespace ExpandedFA.BanachAlgebra.ContourCalculus
open MeasureTheory
open scoped Interval

lemma intervalIntegral_swap_of_continuousOn {F : ℝ → ℝ → ℂ} {a b c d : ℝ}
    (hF : ContinuousOn F.uncurry (Set.uIcc a b ×ˢ Set.uIcc c d)) :
    (∫ x in a..b, ∫ t in c..d, F x t) = ∫ t in c..d, ∫ x in a..b, F x t := by
  apply intervalIntegral_intervalIntegral_swap
  exact (hF.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
    (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)

lemma wedgeIntegral_parametric_intervalIntegral {F : ℂ → ℝ → ℂ}
    {z w : ℂ} {a b : ℝ}
    (hF : ContinuousOn F.uncurry (Complex.Rectangle z w ×ˢ Set.uIcc a b)) :
    Complex.wedgeIntegral z w (fun v => ∫ t in a..b, F v t) =
      ∫ t in a..b, Complex.wedgeIntegral z w (fun v => F v t) := by
  have hh : ContinuousOn
      (fun p : ℝ × ℝ => F (p.1 + z.im * Complex.I) p.2)
      (Set.uIcc z.re w.re ×ˢ Set.uIcc a b) := by
    apply hF.comp (f := fun p : ℝ × ℝ => ((p.1 : ℂ) + z.im * Complex.I, p.2)) (by fun_prop)
    intro p hp
    constructor
    · exact ⟨by simpa using hp.1, by simp⟩
    · exact hp.2
  have hv : ContinuousOn
      (fun p : ℝ × ℝ => F (w.re + p.1 * Complex.I) p.2)
      (Set.uIcc z.im w.im ×ˢ Set.uIcc a b) := by
    apply hF.comp (f := fun p : ℝ × ℝ => ((w.re : ℂ) + p.1 * Complex.I, p.2)) (by fun_prop)
    intro p hp
    constructor
    · exact ⟨by simp, by simpa using hp.1⟩
    · exact hp.2
  have hht : IntervalIntegrable
      (fun t => ∫ x in z.re..w.re, F (x + z.im * Complex.I) t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_parametric_intervalIntegral
    exact hh.comp continuous_swap.continuousOn (fun p hp => ⟨hp.2,hp.1⟩)
  have hvt : IntervalIntegrable
      (fun t => ∫ y in z.im..w.im, F (w.re + y * Complex.I) t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_parametric_intervalIntegral
    exact hv.comp continuous_swap.continuousOn (fun p hp => ⟨hp.2,hp.1⟩)
  have hvi : IntervalIntegrable (fun t => Complex.I •
      ∫ y in z.im..w.im, F (w.re + y * Complex.I) t) volume a b := by
    simpa only [smul_eq_mul] using hvt.const_mul Complex.I
  simp only [Complex.wedgeIntegral]
  rw [intervalIntegral.integral_add hht hvi, intervalIntegral.integral_smul]
  rw [intervalIntegral_swap_of_continuousOn (F := fun x t => F (x + z.im * Complex.I) t) hh,
    intervalIntegral_swap_of_continuousOn (F := fun y t => F (w.re + y * Complex.I) t) hv]

end ExpandedFA.BanachAlgebra.ContourCalculus

namespace ExpandedFA.BanachAlgebra.ContourCalculus
open MeasureTheory

lemma differentiableOn_parametric_intervalIntegral {F : ℂ → ℝ → ℂ} {U : Set ℂ}
    {a b : ℝ} (hU : IsOpen U)
    (hF : ContinuousOn F.uncurry (U ×ˢ Set.uIcc a b))
    (hd : ∀ t ∈ Set.uIcc a b, DifferentiableOn ℂ (fun z => F z t) U) :
    DifferentiableOn ℂ (fun z => ∫ t in a..b, F z t) U := by
  apply (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp
  refine ⟨?_, continuousOn_parametric_intervalIntegral hF⟩
  intro z w hzw
  have hrect : Complex.Rectangle w z = Complex.Rectangle z w := by
    simp only [Complex.Rectangle, Set.uIcc_comm]
  rw [wedgeIntegral_parametric_intervalIntegral (hF.mono (Set.prod_mono hzw Subset.rfl)),
    wedgeIntegral_parametric_intervalIntegral (hF.mono (Set.prod_mono (hrect ▸ hzw) Subset.rfl)),
    ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro t ht
  exact (hd t ht).isConservativeOn z w hzw

end ExpandedFA.BanachAlgebra.ContourCalculus

namespace ExpandedFA.BanachAlgebra.ContourCalculus
open MeasureTheory

lemma differentiableOn_parametric_cycleIntegral (Γ : Cycle) {F : ℂ → ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hF : ContinuousOn F.uncurry (U ×ˢ Γ.trace))
    (hd : ∀ w ∈ Γ.trace, DifferentiableOn ℂ (fun z => F z w) U) :
    DifferentiableOn ℂ (fun z => cycleIntegral Γ (F z)) U := by
  unfold cycleIntegral
  apply DifferentiableOn.fun_sum
  intro i hi
  apply differentiableOn_parametric_intervalIntegral hU
  · simp only [Set.uIcc_of_le zero_le_one]
    have hpath : ContinuousOn (fun p : ℂ × ℝ => (Γ.arc i).path p.2)
        (U ×ˢ Icc 0 1) :=
      (Γ.arc i).continuousOn_path.comp continuous_snd.continuousOn (fun p hp => hp.2)
    have hvel : ContinuousOn (fun p : ℂ × ℝ => (Γ.arc i).velocity p.2)
        (U ×ˢ Icc 0 1) :=
      (Γ.arc i).continuousOn_velocity.comp continuous_snd.continuousOn (fun p hp => hp.2)
    exact hvel.smul (hF.comp (continuous_fst.continuousOn.prodMk hpath)
      (fun p hp => ⟨hp.1, Γ.path_mem_trace i hp.2⟩))
  · intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact (hd _ (Γ.path_mem_trace i ht)).const_smul ((Γ.arc i).velocity t)

lemma differentiableOn_cycleIntegral_dslope (Γ : Cycle) {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hΓ : Γ.trace ⊆ U) (hf : DifferentiableOn ℂ f U) :
    DifferentiableOn ℂ (fun z => cycleIntegral Γ (dslope f z)) U := by
  apply differentiableOn_parametric_cycleIntegral Γ (F := dslope f) hU
    ((continuousOn_dslope_pair hU hf).mono (Set.prod_mono Subset.rfl hΓ))
  intro w hw
  exact differentiableOn_dslope_first hU hf (hΓ hw)

end ExpandedFA.BanachAlgebra.ContourCalculus



noncomputable section
namespace ExpandedFA.BanachAlgebra.ContourCalculus
open Set MeasureTheory Filter
open scoped Topology

def C1Arc.affine (γ : C1Arc) (c s : ℂ) : C1Arc where
  path t := c + s * γ.path t
  smooth := contDiffOn_const.add (contDiffOn_const.mul γ.smooth)

lemma C1Arc.velocity_affine (γ : C1Arc) (c s : ℂ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    (γ.affine c s).velocity t = s * γ.velocity t := by
  have hd := ((γ.smooth.differentiableOn_one t ht).hasDerivWithinAt.const_mul s).const_add c
  exact hd.derivWithin (uniqueDiffOn_Icc_zero_one t ht)

def Cycle.affine (Γ : Cycle) (c s : ℂ) : Cycle where
  count := Γ.count
  arc i := (Γ.arc i).affine c s
  next := Γ.next
  joins i := congrArg (fun w => c + s * w) (Γ.joins i)

lemma Cycle.trace_affine (Γ : Cycle) (c s : ℂ) :
    (Γ.affine c s).trace = (fun w => c + s * w) '' Γ.trace := by
  simp [Cycle.trace, Cycle.affine, C1Arc.affine, image_iUnion, image_image, Function.comp_def]

lemma Cycle.winding_affine (Γ : Cycle) (c s z : ℂ) (hs : s ≠ 0) :
    (Γ.affine c s).winding z = Γ.winding ((z-c)/s) := by
  unfold Cycle.winding
  congr 1
  change (∑ i : Fin Γ.count, ∫ t in (0 : ℝ)..1,
    ((Γ.arc i).affine c s).velocity t • (((Γ.arc i).affine c s).path t - z)⁻¹) = _
  apply Finset.sum_congr rfl
  intro i _
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  change ((Γ.arc i).affine c s).velocity t *
    (c + s * (Γ.arc i).path t - z)⁻¹ =
    (Γ.arc i).velocity t * ((Γ.arc i).path t - (z-c)/s)⁻¹
  rw [C1Arc.velocity_affine _ c s ht]
  have heq : c + s * (Γ.arc i).path t - z = s * ((Γ.arc i).path t - (z-c)/s) := by
    field_simp
    <;> ring
  rw [heq, mul_inv_rev]
  calc
    _ = (s * s⁻¹) * ((Γ.arc i).velocity t * ((Γ.arc i).path t - (z-c)/s)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hs, one_mul]

end ExpandedFA.BanachAlgebra.ContourCalculus


noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace ExpandedFA.BanachAlgebra.ContourCalculus

lemma cycleIntegral_mul_const (Γ : Cycle) (h : ℂ → ℂ) (c : ℂ) :
    cycleIntegral Γ (fun w => h w * c) = cycleIntegral Γ h * c := by
  simp only [cycleIntegral, smul_eq_mul, ← mul_assoc,
    intervalIntegral.integral_mul_const, Finset.sum_mul]

lemma cycleIntegral_const_mul (Γ : Cycle) (h : ℂ → ℂ) (c : ℂ) :
    cycleIntegral Γ (fun w => c * h w) = c * cycleIntegral Γ h := by
  simpa only [mul_comm c] using cycleIntegral_mul_const Γ h c

lemma differentiableOn_cycleCauchyKernel (Γ : Cycle) {h : ℂ → ℂ}
    (hh : ContinuousOn h Γ.trace) :
    DifferentiableOn ℂ (fun z => cycleIntegral Γ (fun w => h w * (w-z)⁻¹))
      Γ.traceᶜ := by
  apply differentiableOn_parametric_cycleIntegral Γ Γ.isCompact_trace.isClosed.isOpen_compl
  · exact (hh.comp continuous_snd.continuousOn (fun p hp => hp.2)).mul
      ((continuous_snd.continuousOn.sub continuous_fst.continuousOn).inv₀
        (fun p hp => sub_ne_zero.mpr (fun he => hp.1 (he ▸ hp.2))))
  · intro w hw
    apply DifferentiableOn.const_mul
    apply DifferentiableOn.inv
      ((differentiableOn_const (c := w)).sub differentiableOn_id)
    intro z hz
    change w - z ≠ 0
    exact sub_ne_zero.mpr (fun he => hz (he ▸ hw))

lemma cycleIntegral_dslope_eq_cauchyKernel (Γ : Cycle) {h : ℂ → ℂ}
    (hh : ContinuousOn h Γ.trace) {z : ℂ} (hz : z ∉ Γ.trace) (hw : Γ.winding z = 0) :
    cycleIntegral Γ (dslope h z) =
      cycleIntegral Γ (fun w => h w * (w - z)⁻¹) := by
  have hk := continuousOn_cycle_kernel Γ hz
  have hzero : cycleIntegral Γ (fun w => (w - z)⁻¹) = 0 := by
    exact (mul_eq_zero.mp hw).resolve_left (inv_ne_zero Complex.two_pi_I_ne_zero)
  calc
    _ = cycleIntegral Γ (fun w => h w * (w - z)⁻¹ - h z * (w - z)⁻¹) := by
      apply cycleIntegral_congr Γ
      intro w hw
      have hwz : w ≠ z := fun he => hz (he ▸ hw)
      rw [dslope_of_ne _ hwz, slope_def_field, div_eq_mul_inv, sub_mul]
    _ = cycleIntegral Γ (fun w => h w * (w - z)⁻¹) -
        cycleIntegral Γ (fun w => h z * (w - z)⁻¹) :=
      cycleIntegral_sub Γ (hh.mul hk) (continuousOn_const.mul hk)
    _ = _ := by rw [cycleIntegral_const_mul Γ _ (h z), hzero, mul_zero, sub_zero]

lemma differentiable_dixon_extension (Γ : Cycle) {h : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hΓ : Γ.trace ⊆ U)
    (hnull : ∀ z ∉ U, Γ.winding z = 0) (hh : ContinuousOn h Γ.trace)
    (hD : DifferentiableOn ℂ (fun z => cycleIntegral Γ (dslope h z)) U) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      EqOn F (fun z => cycleIntegral Γ (fun w => h w * (w-z)⁻¹))
        {z : ℂ | z ∉ Γ.trace ∧ Γ.winding z = 0} := by
  classical
  refine ⟨(fun z => if z ∈ U then cycleIntegral Γ (dslope h z)
    else cycleIntegral Γ (fun w => h w * (w-z)⁻¹)), ?_, ?_⟩
  · intro z
    by_cases hzU : z ∈ U
    · apply (hD.differentiableAt (hU.mem_nhds hzU)).congr_of_eventuallyEq
      filter_upwards [hU.mem_nhds hzU] with w hw
      simp only [ite_eq_left hw]
    · have hz : z ∉ Γ.trace := fun hz => hzU (hΓ hz)
      have hZ := Γ.isOpen_zero_winding
      have hzin : z ∈ {z : ℂ | z ∉ Γ.trace ∧ Γ.winding z = 0} := ⟨hz, hnull z hzU⟩
      apply ((differentiableOn_cycleCauchyKernel Γ hh).differentiableAt
        (Γ.isCompact_trace.isClosed.isOpen_compl.mem_nhds hz)).congr_of_eventuallyEq
      filter_upwards [hZ.mem_nhds hzin] with w hw
      split_ifs with hwU
      · exact cycleIntegral_dslope_eq_cauchyKernel Γ hh hw.1 hw.2
      · rfl
  · intro z hz
    dsimp only
    split_ifs with hzU
    · exact cycleIntegral_dslope_eq_cauchyKernel Γ hh hz.1 hz.2
    · rfl


/-- The scalar homological Cauchy theorem, first for zero index outside a domain. -/
lemma cycleIntegral_eq_zero_of_null_winding (U : Set ℂ) (Γ : Cycle) (h : ℂ → ℂ)
    (hU : IsOpen U) (hΓ : Γ.trace ⊆ U)
    (hnull : ∀ z ∉ U, Γ.winding z = 0) (hh : DifferentiableOn ℂ h U) :
    cycleIntegral Γ h = 0 := by
  have hc := hh.continuousOn.mono hΓ
  obtain ⟨F, hF, hFE⟩ := differentiable_dixon_extension Γ hU hΓ hnull hc
    (differentiableOn_cycleIntegral_dslope Γ hU hΓ hh)
  have he : F =ᶠ[cocompact ℂ]
      (fun z => cycleIntegral Γ (fun w => h w * (w-z)⁻¹)) := by
    filter_upwards [Γ.isCompact_filledTrace.compl_mem_cocompact] with z hz
    apply hFE
    simpa only [mem_compl_iff, mem_ofPred_eq, not_or, not_not] using hz
  have hFzero : F = Function.const ℂ (0 : ℂ) :=
    hF.eq_const_of_tendsto_cocompact ((cauchyKernel_tendsto_zero Γ hc).congr' he.symm)
  apply cycleIntegral_eq_zero_of_eventually_cauchyKernel_eq_zero Γ hc
  filter_upwards [he] with z hz
  rw [← hz, hFzero]
  rfl

/-- Scalar Cauchy on arbitrary finite C¹ cycles with the same exterior indices. -/
theorem homological_cauchy : Spec.HomologicalCauchy :=
  homologicalCauchy_of_null cycleIntegral_eq_zero_of_null_winding

universe u

/-- Fixed-domain contour independence, using scalar homological Cauchy and dual separation. -/
theorem cycle_independence : Spec.CycleIndependence.{u} :=
  cycle_independence_of_cauchy homological_cauchy


/-- Every supplied admissible cycle witnesses the admissibility of the chosen cycle. -/
theorem holomorphic_formula : Spec.HolomorphicFormula.{u} := by
  intro A _ _ hA a U f hU hKU hf Γ hΓ
  exact cycle_independence A hA a U f hU hKU hf _ Γ
    (by
      unfold Spec.SelectedCycleValue
      exact Classical.epsilon_spec
        (show ∃ Λ : Cycle, Λ.Admissible (algebraSpectrum ℂ A a) U from ⟨Γ, hΓ⟩)) hΓ

end ExpandedFA.BanachAlgebra.ContourCalculus




noncomputable section
namespace ExpandedFA.BanachAlgebra.ContourCalculus
open Set MeasureTheory Filter
open scoped Topology

/-- The affine oriented line segment. -/
def C1Arc.line (a b : ℂ) : C1Arc where
  path t := a + t • (b - a)
  smooth := (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn

@[simp] lemma C1Arc.line_path_zero (a b : ℂ) : (C1Arc.line a b).path 0 = a := by
  simp [C1Arc.line]
@[simp] lemma C1Arc.line_path_one (a b : ℂ) : (C1Arc.line a b).path 1 = b := by
  simp [C1Arc.line]

lemma C1Arc.line_velocity (a b : ℂ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    (C1Arc.line a b).velocity t = b - a := by
  apply HasDerivWithinAt.derivWithin
    (f' := b - a) _ (uniqueDiffOn_Icc_zero_one t ht)
  simpa [C1Arc.velocity, C1Arc.line] using
    ((((hasDerivAt_id t).smul_const (b - a)).const_add a).hasDerivWithinAt :
      HasDerivWithinAt (fun t : ℝ => a + t • (b - a)) _ (Icc 0 1) t)

def diamondArcs : Fin 4 → C1Arc :=
  ![C1Arc.line 1 Complex.I, C1Arc.line Complex.I (-1),
    C1Arc.line (-1) (-Complex.I), C1Arc.line (-Complex.I) 1]

/-- Four positively oriented affine sides of the diamond with vertices 1,i,-1,-i. -/
def diamondCycle : Cycle where
  count := 4
  arc := diamondArcs
  next := finRotate 4
  joins i := by
    fin_cases i <;> norm_num [finRotate_apply, diamondArcs]

/-- Exact logarithmic integral on the first quadrant side. -/
lemma first_quadrant_side_integral :
    (∫ t in (0 : ℝ)..1,
      (Complex.I - 1) * (1 + (t : ℂ) * (Complex.I - 1))⁻¹) =
      (Real.pi / 2 : ℝ) * Complex.I := by
  let H : ℝ → ℂ := fun t => Complex.log (1 + (t : ℂ) * (Complex.I - 1))
  have hslit (t : ℝ) (ht : t ∈ Icc 0 1) :
      1 + (t : ℂ) * (Complex.I - 1) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.sub_re, Complex.I_re, zero_sub, Complex.ofReal_im, Complex.sub_im,
      Complex.I_im, Complex.one_im, sub_zero, mul_neg, mul_one, zero_mul, sub_zero,
      Complex.add_im, Complex.mul_im, zero_add, mul_zero, add_zero]
    by_cases ht0 : t = 0
    · exact Or.inl (by simp [ht0])
    · exact Or.inr (by simpa using ht0)
  have hd (t : ℝ) (ht : t ∈ Icc 0 1) :
      HasDerivAt H ((Complex.I - 1) *
        (1 + (t : ℂ) * (Complex.I - 1))⁻¹) t := by
    have hinner := (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (Complex.I - 1) |>.const_add 1
    convert (Complex.hasDerivAt_log (hslit t ht)).scomp t hinner using 1 <;> simp [H, mul_comm, Function.comp_def]
  have hc : ContinuousOn H (Icc 0 1) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hi : IntervalIntegrable (fun t : ℝ =>
      (Complex.I - 1) * (1 + (t : ℂ) * (Complex.I - 1))⁻¹) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    apply continuousOn_const.mul
    apply ((Complex.continuous_ofReal.continuousOn.mul continuousOn_const).const_add 1).inv₀
    intro t ht
    exact Complex.slitPlane_ne_zero (hslit t ht)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hc
    (fun t ht => hd t (Ioo_subset_Icc_self ht)) hi
  simpa [H, Complex.log_I, Complex.log_one] using h

lemma line_integral_inv_rotate (c : ℂ) (hc : c ≠ 0) :
    (∫ t in (0 : ℝ)..1,
      (C1Arc.line c (c * Complex.I)).velocity t *
        ((C1Arc.line c (c * Complex.I)).path t)⁻¹) =
      (Real.pi / 2 : ℝ) * Complex.I := by
  rw [← first_quadrant_side_integral]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  dsimp only
  rw [C1Arc.line_velocity c (c * Complex.I) ht]
  have hpath : (C1Arc.line c (c * Complex.I)).path t =
      c * (1 + (t : ℂ) * (Complex.I - 1)) := by
    simp only [C1Arc.line, Complex.real_smul]
    ring
  rw [hpath, mul_inv_rev]
  calc
    (c * Complex.I - c) * ((1 + (t : ℂ) * (Complex.I - 1))⁻¹ * c⁻¹) =
        (c * c⁻¹) * ((Complex.I - 1) *
          (1 + (t : ℂ) * (Complex.I - 1))⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hc, one_mul]

lemma diamondCycle_integral_inv : cycleIntegral diamondCycle (fun z => z⁻¹) =
    (2 * Real.pi : ℂ) * Complex.I := by
  dsimp only [cycleIntegral, diamondCycle, diamondArcs]
  simp only [Fin.sum_univ_four, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
  dsimp only [Matrix.vecHead, Matrix.vecTail, Matrix.vecCons, Fin.cons]
  simp only [Function.comp_apply, Fin.cons_zero, Fin.cons_succ]
  have h₁ := line_integral_inv_rotate 1 one_ne_zero
  have h₂ := line_integral_inv_rotate Complex.I Complex.I_ne_zero
  have h₃ := line_integral_inv_rotate (-1) (neg_ne_zero.mpr one_ne_zero)
  have h₄ := line_integral_inv_rotate (-Complex.I) (neg_ne_zero.mpr Complex.I_ne_zero)
  simp only [one_mul, Complex.I_mul_I, neg_mul, neg_neg] at h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]
  push_cast
  ring

lemma diamondCycle_winding_zero : diamondCycle.winding 0 = 1 := by
  simp only [Cycle.winding, sub_zero, diamondCycle_integral_inv]
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  exact inv_mul_cancel₀ hpi

/-- The real ℓ¹ gauge, whose unit sphere is the reference diamond. -/
def diamondGauge (z : ℂ) : ℝ := |z.re| + |z.im|

lemma diamondCycle_trace : diamondCycle.trace = {z : ℂ | diamondGauge z = 1} := by
  ext z
  simp only [Cycle.trace, mem_iUnion, mem_image]
  change (∃ i : Fin 4, ∃ t ∈ Icc (0 : ℝ) 1, (diamondArcs i).path t = z) ↔
    diamondGauge z = 1
  constructor
  · rintro ⟨i, t, ht, rfl⟩
    rcases ht with ⟨ht0, ht1⟩
    fin_cases i <;>
      norm_num [diamondArcs, C1Arc.line, diamondGauge, Complex.real_smul,
        abs_of_nonneg ht0, abs_of_nonpos (neg_nonpos.mpr ht0),
        abs_of_nonneg (sub_nonneg.mpr ht1), abs_of_nonpos (sub_nonpos.mpr ht1)] <;>
      first
      | (rw [abs_of_nonneg (by linarith)]; linarith)
      | (rw [abs_of_nonpos (by linarith)]; linarith)
  · intro hz
    change |z.re| + |z.im| = 1 at hz
    by_cases hre : 0 ≤ z.re
    · by_cases him : 0 ≤ z.im
      · refine ⟨0, z.im, ⟨him, ?_⟩, ?_⟩
        · rw [abs_of_nonneg hre, abs_of_nonneg him] at hz
          linarith
        · apply Complex.ext <;>
            simp [diamondArcs, C1Arc.line, Complex.real_smul]
          · rw [abs_of_nonneg hre, abs_of_nonneg him] at hz
            linarith
      · have him' : z.im ≤ 0 := le_of_not_ge him
        refine ⟨3, z.re, ⟨hre, ?_⟩, ?_⟩
        · rw [abs_of_nonneg hre, abs_of_nonpos him'] at hz
          linarith
        · apply Complex.ext <;>
            simp [diamondArcs, C1Arc.line, Complex.real_smul]
          · rw [abs_of_nonneg hre, abs_of_nonpos him'] at hz
            linarith
    · have hre' : z.re ≤ 0 := le_of_not_ge hre
      by_cases him : 0 ≤ z.im
      · refine ⟨1, -z.re, ⟨neg_nonneg.mpr hre', ?_⟩, ?_⟩
        · rw [abs_of_nonpos hre', abs_of_nonneg him] at hz
          linarith
        · apply Complex.ext <;>
            simp [diamondArcs, C1Arc.line, Complex.real_smul]
          · rw [abs_of_nonpos hre', abs_of_nonneg him] at hz
            linarith
      · have him' : z.im ≤ 0 := le_of_not_ge him
        refine ⟨2, -z.im, ⟨neg_nonneg.mpr him', ?_⟩, ?_⟩
        · rw [abs_of_nonpos hre', abs_of_nonpos him'] at hz
          linarith
        · apply Complex.ext <;>
            simp [diamondArcs, C1Arc.line, Complex.real_smul]
          · rw [abs_of_nonpos hre', abs_of_nonpos him'] at hz
            linarith

/-- Local constancy of index gives constancy on any connected piece missing the trace. -/
lemma Cycle.winding_eq_on_preconnected (Γ : Cycle) {S : Set ℂ}
    (hS : IsPreconnected S) (hdisj : Disjoint S Γ.trace)
    {x y : ℂ} (hx : x ∈ S) (hy : y ∈ S) : Γ.winding x = Γ.winding y := by
  let f : S → ℂ := fun z => Γ.winding z
  have hloc : IsLocallyConstant f := by
    apply (IsLocallyConstant.iff_eventually_eq f).mpr
    intro z
    have hz : (z : ℂ) ∉ Γ.trace := fun h => Set.disjoint_left.mp hdisj z.property h
    exact continuous_subtype_val.continuousAt.tendsto.eventually (Γ.winding_eventually_eq hz)
  letI : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS
  exact hloc.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩

lemma diamondGauge_convexOn : ConvexOn ℝ (univ : Set ℂ) diamondGauge := by
  have hr := (convexOn_norm (convex_univ : Convex ℝ (univ : Set ℝ))).comp_linearMap
    Complex.reCLM.toLinearMap
  have hi := (convexOn_norm (convex_univ : Convex ℝ (univ : Set ℝ))).comp_linearMap
    Complex.imCLM.toLinearMap
  convert hr.add hi using 1 <;> rfl

lemma diamond_interior_convex : Convex ℝ {z : ℂ | diamondGauge z < 1} := by
  simpa only [mem_univ, true_and] using diamondGauge_convexOn.convex_lt 1

lemma diamondCycle_winding_eq_one {z : ℂ} (hz : diamondGauge z < 1) :
    diamondCycle.winding z = 1 := by
  rw [← diamondCycle_winding_zero]
  apply diamondCycle.winding_eq_on_preconnected diamond_interior_convex.isPreconnected ?_ hz
    (by simp [diamondGauge])
  rw [Set.disjoint_left, diamondCycle_trace]
  intro w hw htrace
  exact hw.ne htrace

/-- A half-plane containing the trace supplies a logarithmic primitive. -/
lemma Cycle.winding_eq_zero_of_halfplane (Γ : Cycle) {z c : ℂ} (hc : c ≠ 0)
    (hsep : ∀ w ∈ Γ.trace, 0 < (c * (w - z)).re) : Γ.winding z = 0 := by
  have hz : z ∉ Γ.trace := by
    intro hz
    simpa using hsep z hz
  have hp : ∀ w ∈ Γ.trace,
      HasDerivAt (fun v : ℂ => Complex.log (c * (v - z))) ((w - z)⁻¹) w := by
    intro w hw
    have hwz : w - z ≠ 0 := by
      intro h
      simpa [h] using hsep w hw
    have hd := (Complex.hasDerivAt_log (Or.inl (hsep w hw))).comp w
      (((hasDerivAt_id w).sub_const z).const_mul c)
    convert hd using 1
    · rfl
    · field_simp [hc, hwz]
  rw [Cycle.winding, cycleIntegral_derivative_eq_zero Γ (continuousOn_cycle_kernel Γ hz) hp,
    mul_zero]

lemma diamondCycle_winding_eq_zero {z : ℂ} (hz : 1 < diamondGauge z) :
    diamondCycle.winding z = 0 := by
  have htrace : ∀ w ∈ diamondCycle.trace, |w.re| + |w.im| = 1 := by
    intro w hw
    rw [diamondCycle_trace] at hw
    exact hw
  change 1 < |z.re| + |z.im| at hz
  by_cases hre : 0 ≤ z.re
  · by_cases him : 0 ≤ z.im
    · rw [abs_of_nonneg hre, abs_of_nonneg him] at hz
      apply diamondCycle.winding_eq_zero_of_halfplane (c := -1 + Complex.I) (by
        intro h; have := congrArg Complex.re h; norm_num at this)
      intro w hw
      have hw' := htrace w hw
      norm_num
      linarith [le_abs_self w.re, le_abs_self w.im]
    · have him' : z.im ≤ 0 := le_of_not_ge him
      rw [abs_of_nonneg hre, abs_of_nonpos him'] at hz
      apply diamondCycle.winding_eq_zero_of_halfplane (c := -1 - Complex.I) (by
        intro h; have := congrArg Complex.re h; norm_num at this)
      intro w hw
      have hw' := htrace w hw
      norm_num
      linarith [le_abs_self w.re, neg_le_abs w.im]
  · have hre' : z.re ≤ 0 := le_of_not_ge hre
    by_cases him : 0 ≤ z.im
    · rw [abs_of_nonpos hre', abs_of_nonneg him] at hz
      apply diamondCycle.winding_eq_zero_of_halfplane (c := 1 + Complex.I) (by
        intro h; have := congrArg Complex.re h; norm_num at this)
      intro w hw
      have hw' := htrace w hw
      norm_num
      linarith [neg_le_abs w.re, le_abs_self w.im]
    · have him' : z.im ≤ 0 := le_of_not_ge him
      rw [abs_of_nonpos hre', abs_of_nonpos him'] at hz
      apply diamondCycle.winding_eq_zero_of_halfplane (c := 1 - Complex.I) (by
        intro h; have := congrArg Complex.re h; norm_num at this)
      intro w hw
      have hw' := htrace w hw
      norm_num
      linarith [neg_le_abs w.re, neg_le_abs w.im]

lemma diamondCycle_positive : diamondCycle.Positive := by
  intro z hz
  have hne : diamondGauge z ≠ 1 := by
    simpa only [diamondCycle_trace, mem_ofPred_eq] using hz
  rcases lt_or_gt_of_ne hne with h | h
  · exact Or.inr (diamondCycle_winding_eq_one h)
  · exact Or.inl (diamondCycle_winding_eq_zero h)

lemma continuous_diamondGauge : Continuous diamondGauge :=
  Complex.continuous_re.abs.add Complex.continuous_im.abs

/-- The reference square is admissible whenever its interior contains K and its
closed interior is contained in U. -/
lemma diamondCycle_admissible {K U : Set ℂ}
    (hK : K ⊆ {z : ℂ | diamondGauge z < 1})
    (hU : {z : ℂ | diamondGauge z ≤ 1} ⊆ U) :
    diamondCycle.Admissible K U := by
  refine ⟨?_, diamondCycle_positive, ?_, ?_⟩
  · intro z hz
    have he : diamondGauge z = 1 := by simpa only [diamondCycle_trace, mem_ofPred_eq] using hz
    exact ⟨hU he.le, fun hzK => (hK hzK).ne he⟩
  · refine ⟨{z : ℂ | diamondGauge z < 1},
      isOpen_lt continuous_diamondGauge continuous_const, hK, ?_, ?_⟩
    · rw [Set.disjoint_left]
      intro z hz htr
      have he : diamondGauge z = 1 := by simpa only [diamondCycle_trace, mem_ofPred_eq] using htr
      exact hz.ne he
    · exact fun z hz => diamondCycle_winding_eq_one hz
  · intro z hz
    exact diamondCycle_winding_eq_zero (lt_of_not_ge (fun h => hz (hU h)))

/-- Local constancy extends an index computation across canceled internal edges. -/
lemma Cycle.positive_of_dense (Γ : Cycle) {D : Set ℂ} (hD : Dense D)
    (h : ∀ z ∈ D, z ∉ Γ.trace → Γ.winding z = 0 ∨ Γ.winding z = 1) : Γ.Positive := by
  intro z hz
  have hn : {w : ℂ | Γ.winding w = Γ.winding z ∧ w ∉ Γ.trace} ∈ 𝓝 z :=
    (Γ.winding_eventually_eq hz).and (Γ.isCompact_trace.isClosed.isOpen_compl.mem_nhds hz)
  obtain ⟨w, hwD, hweq, hwtrace⟩ := hD.inter_nhds_nonempty hn
  simpa only [hweq] using h w hwD hwtrace

/-- The neighborhood clause follows from pointwise index one on K. -/
lemma Cycle.admissible_of_pointwise (Γ : Cycle) {K U : Set ℂ}
    (htrace : Γ.trace ⊆ U \ K) (hpositive : Γ.Positive)
    (hone : ∀ z ∈ K, Γ.winding z = 1)
    (hzero : ∀ z ∉ U, Γ.winding z = 0) : Γ.Admissible K U := by
  refine ⟨htrace, hpositive, ?_, hzero⟩
  let V : Set ℂ := {z | z ∉ Γ.trace ∧ Γ.winding z = 1}
  have hopen : IsOpen V := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    filter_upwards [Γ.isCompact_trace.isClosed.isOpen_compl.mem_nhds hz.1,
      Γ.winding_eventually_eq hz.1] with w hw he
    exact ⟨hw, he.trans hz.2⟩
  refine ⟨V, hopen, ?_, ?_, ?_⟩
  · intro z hz
    exact ⟨fun ht => (htrace ht).2 hz, hone z hz⟩
  · exact Set.disjoint_left.mpr (fun z hz htr => hz.1 htr)
  · exact fun z hz => hz.2

end ExpandedFA.BanachAlgebra.ContourCalculus



noncomputable section
namespace ExpandedFA.BanachAlgebra.ContourCalculus
open Set MeasureTheory Filter
open scoped Topology

lemma card_fiber_partition {ι : Type*} [Fintype ι] (p q : ι → Prop)
    [DecidablePred p] [DecidablePred q] :
    Fintype.card {i : {j // p j} // q i} +
      Fintype.card {i : {j // ¬p j} // q i} = Fintype.card {i // q i} := by
  classical
  let e : {i // q i} ≃ ({i : {j // p j} // q i} ⊕ {i : {j // ¬p j} // q i}) := {
    toFun i := if h : p i then Sum.inl ⟨⟨i,h⟩,i.property⟩ else Sum.inr ⟨⟨i,h⟩,i.property⟩
    invFun := Sum.elim (fun j : {i : {k // p k} // q i} => ⟨j.val.val,j.property⟩)
      (fun j : {i : {k // ¬p k} // q i} => ⟨j.val.val,j.property⟩)
    left_inv i := by dsimp only; split_ifs <;> rfl
    right_inv i := by
      rcases i with i | i
      · rcases i with ⟨⟨i,hi⟩,hqi⟩
        simp only [Sum.elim_inl, Subtype.coe_mk, hi, ↓reduceDIte]
      · rcases i with ⟨⟨i,hi⟩,hqi⟩
        simp only [Sum.elim_inr, Subtype.coe_mk, hi, ↓reduceDIte]
  }
  simpa only [Fintype.card_sum] using (Fintype.card_congr e).symm

lemma balanced_arcs_after_removal {ι : Type*} [Fintype ι]
    (γ : ι → C1Arc) (p : ι → Prop) [DecidablePred p]
    (hbalanced : ∀ z : ℂ,
      Fintype.card {i : ι // (γ i).path 1 = z} =
        Fintype.card {i : ι // (γ i).path 0 = z})
    (pair : Equiv.Perm {i // p i})
    (hpair : ∀ i : {i // p i}, (γ (pair i)).path 0 = (γ i).path 1) :
    ∀ z : ℂ,
      Fintype.card {i : {j // ¬p j} // (γ i).path 1 = z} =
        Fintype.card {i : {j // ¬p j} // (γ i).path 0 = z} := by
  classical
  intro z
  have hremoved : Fintype.card {i : {j // p j} // (γ i).path 1 = z} =
      Fintype.card {i : {j // p j} // (γ i).path 0 = z} := by
    apply Fintype.card_congr (pair.subtypeEquiv _)
    intro i
    rw [hpair i]
  have he := card_fiber_partition p (fun i => (γ i).path 1 = z)
  have hs := card_fiber_partition p (fun i => (γ i).path 0 = z)
  rw [← hbalanced z, ← he, ← hremoved] at hs
  exact Nat.add_left_cancel hs.symm

end ExpandedFA.BanachAlgebra.ContourCalculus

namespace ExpandedFA.BanachAlgebra.ContourCalculus
open Set MeasureTheory

lemma C1Arc.integral_reverse {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (γ : C1Arc) (h : ℂ → X) :
    (∫ t in (0 : ℝ)..1, γ.reverse.velocity t • h (γ.reverse.path t)) =
      -(∫ t in (0 : ℝ)..1, γ.velocity t • h (γ.path t)) := by
  calc
    _ = ∫ t in (0 : ℝ)..1, -(γ.velocity (1 - t) • h (γ.path (1 - t))) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      change γ.reverse.velocity t • h (γ.path (1 - t)) = _
      rw [C1Arc.velocity_reverse _ ht, neg_smul]
    _ = -(∫ t in (0 : ℝ)..1, γ.velocity t • h (γ.path t)) := by
      rw [intervalIntegral.integral_neg]
      congr 1
      simpa using intervalIntegral.integral_comp_sub_left
        (fun t => γ.velocity t • h (γ.path t)) (a := 0) (b := 1) 1

lemma sum_reversed_arcs_eq_zero {ι X : Type*} [Fintype ι]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    (γ : ι → C1Arc) (pair : Equiv.Perm ι)
    (hpair : ∀ i, γ (pair i) = (γ i).reverse) (h : ℂ → X) :
    (∑ i, ∫ t in (0 : ℝ)..1, (γ i).velocity t • h ((γ i).path t)) = 0 := by
  classical
  let s : X := ∑ i, ∫ t in (0 : ℝ)..1, (γ i).velocity t • h ((γ i).path t)
  have hs : s = -s := by
    calc
      _ = ∑ i, ∫ t in (0 : ℝ)..1, (γ (pair i)).velocity t • h ((γ (pair i)).path t) :=
        (Equiv.sum_comp pair _).symm
      _ = ∑ i, -(∫ t in (0 : ℝ)..1, (γ i).velocity t • h ((γ i).path t)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hpair i, C1Arc.integral_reverse]
      _ = _ := Finset.sum_neg_distrib ..
  have htwo : (2 : ℂ) • s = 0 := by
    rw [two_smul]
    nth_rw 1 [hs]
    exact neg_add_cancel s
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

lemma sum_arcs_remove_reversed {ι X : Type*} [Fintype ι]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    (γ : ι → C1Arc) (p : ι → Prop) [DecidablePred p]
    (pair : Equiv.Perm {i // p i})
    (hpair : ∀ i : {i // p i}, γ (pair i) = (γ i).reverse) (h : ℂ → X) :
    (∑ i, ∫ t in (0 : ℝ)..1, (γ i).velocity t • h ((γ i).path t)) =
      ∑ i : {j // ¬p j}, ∫ t in (0 : ℝ)..1, (γ i).velocity t • h ((γ i).path t) := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype p]
  rw [sum_reversed_arcs_eq_zero (fun i : {i // p i} => γ i) pair hpair h, zero_add]

end ExpandedFA.BanachAlgebra.ContourCalculus

namespace ExpandedFA.BanachAlgebra.ContourCalculus

lemma balanced_arcs_of_matching_permutation {ι : Type*} [Fintype ι]
    (γ : ι → C1Arc) (next : Equiv.Perm ι)
    (hnext : ∀ i, (γ (next i)).path 0 = (γ i).path 1) :
    ∀ z : ℂ, Fintype.card {i : ι // (γ i).path 1 = z} =
      Fintype.card {i : ι // (γ i).path 0 = z} := by
  classical
  intro z
  apply Fintype.card_congr (next.subtypeEquiv _)
  intro i
  rw [hnext i]

lemma balanced_arcs_family_of_cycles {ι : Type*} [Fintype ι] (Γ : ι → Cycle) :
    ∀ z : ℂ,
      Fintype.card {j : (Σ i, Fin (Γ i).count) // ((Γ j.1).arc j.2).path 1 = z} =
        Fintype.card {j : (Σ i, Fin (Γ i).count) // ((Γ j.1).arc j.2).path 0 = z} := by
  apply balanced_arcs_of_matching_permutation
    (fun j : (Σ i, Fin (Γ i).count) => (Γ j.1).arc j.2)
    (Equiv.sigmaCongrRight fun i => (Γ i).next)
  intro j
  exact ((Γ j.1).joins j.2).symm

end ExpandedFA.BanachAlgebra.ContourCalculus



noncomputable section
namespace ExpandedFA.BanachAlgebra.ContourCalculus
open Set MeasureTheory Filter
open scoped Topology

def unitSquareCycle : Cycle :=
  diamondCycle.affine ((1 + Complex.I) / 2) ((1 + Complex.I) / 2)

lemma squareScale_ne_zero : (1 + Complex.I) / 2 ≠ (0 : ℂ) := by
  norm_num [Complex.ext_iff]

lemma diamondGauge_squareCoordinates (z : ℂ) :
    diamondGauge ((z - (1 + Complex.I)/2) / ((1 + Complex.I)/2)) =
      |z.re + z.im - 1| + |z.im - z.re| := by
  have heq : ((z - (1 + Complex.I)/2) / ((1 + Complex.I)/2)) =
      (z.re + z.im - 1 : ℝ) + (z.im - z.re : ℝ) * Complex.I := by
    apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im, Complex.normSq_apply] <;> ring
  rw [heq]
  simp [diamondGauge]

lemma unitSquareCycle_winding_eq_one {z : ℂ}
    (hx0 : 0 < z.re) (hx1 : z.re < 1) (hy0 : 0 < z.im) (hy1 : z.im < 1) :
    unitSquareCycle.winding z = 1 := by
  rw [unitSquareCycle, Cycle.winding_affine _ _ _ _ squareScale_ne_zero]
  apply diamondCycle_winding_eq_one
  rw [diamondGauge_squareCoordinates]
  by_cases hsum : 0 ≤ z.re + z.im - 1
  · rw [abs_of_nonneg hsum]
    by_cases hxy : z.re ≤ z.im
    · rw [abs_of_nonneg (sub_nonneg.mpr hxy)]; linarith
    · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge hxy))]; linarith
  · rw [abs_of_nonpos (le_of_not_ge hsum)]
    by_cases hxy : z.re ≤ z.im
    · rw [abs_of_nonneg (sub_nonneg.mpr hxy)]; linarith
    · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge hxy))]; linarith

lemma unitSquareCycle_winding_eq_zero {z : ℂ}
    (hz : z.re < 0 ∨ 1 < z.re ∨ z.im < 0 ∨ 1 < z.im) :
    unitSquareCycle.winding z = 0 := by
  rw [unitSquareCycle, Cycle.winding_affine _ _ _ _ squareScale_ne_zero]
  apply diamondCycle_winding_eq_zero
  rw [diamondGauge_squareCoordinates]
  rcases hz with hx | hx | hy | hy
  · linarith [neg_le_abs (z.re+z.im-1), le_abs_self (z.im-z.re)]
  · linarith [le_abs_self (z.re+z.im-1), neg_le_abs (z.im-z.re)]
  · linarith [neg_le_abs (z.re+z.im-1), neg_le_abs (z.im-z.re)]
  · linarith [le_abs_self (z.re+z.im-1), le_abs_self (z.im-z.re)]

lemma unitSquareCycle_trace_subset : unitSquareCycle.trace ⊆
    {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ 1} := by
  intro z hz
  rw [unitSquareCycle, Cycle.trace_affine] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rw [diamondCycle_trace] at hw
  change |w.re| + |w.im| = 1 at hw
  norm_num
  constructor
  · linarith [neg_le_abs w.re, le_abs_self w.im]
  constructor
  · linarith [le_abs_self w.re, neg_le_abs w.im]
  constructor
  · linarith [neg_le_abs w.re, neg_le_abs w.im]
  · linarith [le_abs_self w.re, le_abs_self w.im]

end ExpandedFA.BanachAlgebra.ContourCalculus



noncomputable section
namespace ExpandedFA.BanachAlgebra.ContourCalculus
open Set MeasureTheory Filter

@[ext] lemma C1Arc.ext {γ η : C1Arc} (h : γ.path = η.path) : γ = η := by
  cases γ
  cases η
  cases h
  rfl

lemma C1Arc.line_reverse (a b : ℂ) : (C1Arc.line a b).reverse = C1Arc.line b a := by
  apply C1Arc.ext
  funext t
  simp only [C1Arc.line, C1Arc.reverse, Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
  ring

lemma C1Arc.affine_line (a b c s : ℂ) :
    (C1Arc.line a b).affine c s = C1Arc.line (c + s * a) (c + s * b) := by
  apply C1Arc.ext
  funext t
  simp only [C1Arc.line, C1Arc.affine, Complex.real_smul]
  ring

def gridVertex (δ : ℝ) (q : ℤ × ℤ) : ℂ :=
  (δ : ℂ) * ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I)

/-- Top, left, bottom, right edges, each in positive orientation. -/
def gridSide (δ : ℝ) (q : ℤ × ℤ) : Fin 4 → C1Arc :=
  ![C1Arc.line (gridVertex δ (q.1 + 1, q.2 + 1)) (gridVertex δ (q.1, q.2 + 1)),
    C1Arc.line (gridVertex δ (q.1, q.2 + 1)) (gridVertex δ q),
    C1Arc.line (gridVertex δ q) (gridVertex δ (q.1 + 1, q.2)),
    C1Arc.line (gridVertex δ (q.1 + 1, q.2)) (gridVertex δ (q.1 + 1, q.2 + 1))]

def gridNeighbor (q : ℤ × ℤ) : Fin 4 → ℤ × ℤ :=
  ![(q.1, q.2 + 1), (q.1 - 1, q.2), (q.1, q.2 - 1), (q.1 + 1, q.2)]

def gridOpposite (i : Fin 4) : Fin 4 := i + 2

@[simp] lemma gridOpposite_involutive (i : Fin 4) : gridOpposite (gridOpposite i) = i := by
  fin_cases i <;> norm_num [gridOpposite]

@[simp] lemma gridNeighbor_opposite (q : ℤ × ℤ) (i : Fin 4) :
    gridNeighbor (gridNeighbor q i) (gridOpposite i) = q := by
  rcases q with ⟨m,n⟩
  fin_cases i <;> norm_num [gridNeighbor, gridOpposite]

lemma gridSide_neighbor_reverse (δ : ℝ) (q : ℤ × ℤ) (i : Fin 4) :
    gridSide δ (gridNeighbor q i) (gridOpposite i) = (gridSide δ q i).reverse := by
  rcases q with ⟨m,n⟩
  fin_cases i <;> norm_num [gridSide, gridNeighbor, gridOpposite] <;>
    rw [C1Arc.line_reverse]

def gridSidePair : Equiv.Perm ((ℤ × ℤ) × Fin 4) where
  toFun e := (gridNeighbor e.1 e.2, gridOpposite e.2)
  invFun e := (gridNeighbor e.1 e.2, gridOpposite e.2)
  left_inv e := by rcases e with ⟨q,i⟩; simp
  right_inv e := by rcases e with ⟨q,i⟩; simp

@[simp] lemma gridSidePair_apply (q : ℤ × ℤ) (i : Fin 4) :
    gridSidePair (q,i) = (gridNeighbor q i, gridOpposite i) := rfl

lemma gridSidePair_reverse (δ : ℝ) (e : (ℤ × ℤ) × Fin 4) :
    gridSide δ (gridSidePair e).1 (gridSidePair e).2 = (gridSide δ e.1 e.2).reverse :=
  gridSide_neighbor_reverse δ e.1 e.2

end ExpandedFA.BanachAlgebra.ContourCalculus


noncomputable section
namespace ExpandedFA.BanachAlgebra.ContourCalculus
open Set Filter MeasureTheory Metric
open scoped Topology

/-- A closed axis-aligned cell in the square lattice of mesh δ. -/
def gridCell (δ : ℝ) (q : ℤ × ℤ) : Set ℂ :=
  Icc (δ * (q.1 : ℝ)) (δ * ((q.1 : ℝ) + 1)) ×ℂ
    Icc (δ * (q.2 : ℝ)) (δ * ((q.2 : ℝ) + 1))

/-- All closed grid cells that meet a set, including every incident cell at an edge or vertex. -/
def gridCellsMeeting (δ : ℝ) (K : Set ℂ) : Set (ℤ × ℤ) :=
  {q | ∃ z ∈ K, z ∈ gridCell δ q}

lemma gridCell_cover (δ : ℝ) (hδ : 0 < δ) (z : ℂ) :
    ∃ q : ℤ × ℤ, z ∈ gridCell δ q := by
  refine ⟨(⌊z.re / δ⌋, ⌊z.im / δ⌋), ?_⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simpa only [mul_comm] using (le_div_iff₀ hδ).mp (Int.floor_le (z.re / δ))
  · apply le_of_lt
    simpa only [mul_comm] using
      (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (z.re / δ))
  · simpa only [mul_comm] using (le_div_iff₀ hδ).mp (Int.floor_le (z.im / δ))
  · apply le_of_lt
    simpa only [mul_comm] using
      (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (z.im / δ))

lemma gridCell_dist_le {δ : ℝ} {q : ℤ × ℤ} {z w : ℂ}
    (hz : z ∈ gridCell δ q) (hw : w ∈ gridCell δ q) : dist z w ≤ 2 * δ := by
  have hx : |z.re - w.re| ≤ δ := abs_le.mpr ⟨by nlinarith [hz.1.1, hz.1.2, hw.1.1, hw.1.2],
    by nlinarith [hz.1.1, hz.1.2, hw.1.1, hw.1.2]⟩
  have hy : |z.im - w.im| ≤ δ := abs_le.mpr ⟨by nlinarith [hz.2.1, hz.2.2, hw.2.1, hw.2.2],
    by nlinarith [hz.2.1, hz.2.2, hw.2.1, hw.2.2]⟩
  calc
    dist z w = ‖z-w‖ := dist_eq_norm _ _
    _ ≤ |(z-w).re| + |(z-w).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 * δ := by simpa only [Complex.sub_re, Complex.sub_im] using (by linarith :
      |z.re-w.re| + |z.im-w.im| ≤ 2*δ)

lemma gridCellsMeeting_finite {δ : ℝ} (hδ : 0 < δ) {K : Set ℂ}
    (hK : IsCompact K) : (gridCellsMeeting δ K).Finite := by
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn
    (continuous_id.continuousOn : ContinuousOn (fun z : ℂ => z) K)
  have hcoord {m : ℤ} {x : ℝ} (hx : |x| ≤ R)
      (hm : δ * (m : ℝ) ≤ x ∧ x ≤ δ * ((m : ℝ) + 1)) :
      ⌈-R/δ-1⌉ ≤ m ∧ m ≤ ⌊R/δ⌋ := by
    constructor
    · apply Int.ceil_le.mpr
      have hlow := (abs_le.mp hx).1
      have hd := (div_le_iff₀ hδ).mpr (by nlinarith : -R ≤ ((m : ℝ)+1)*δ)
      linarith
    · apply Int.le_floor.mpr
      apply (le_div_iff₀ hδ).mpr
      nlinarith [(abs_le.mp hx).2]
  apply ((Set.finite_Icc (⌈-R/δ-1⌉ : ℤ) ⌊R/δ⌋).prod
    (Set.finite_Icc (⌈-R/δ-1⌉ : ℤ) ⌊R/δ⌋)).subset
  intro q hq
  obtain ⟨z, hzK, hzq⟩ := hq
  exact ⟨hcoord ((Complex.abs_re_le_norm z).trans (hR z hzK)) hzq.1,
    hcoord ((Complex.abs_im_le_norm z).trans (hR z hzK)) hzq.2⟩

lemma gridCellsMeeting_cover {δ : ℝ} (hδ : 0 < δ) (K : Set ℂ) :
    K ⊆ ⋃ q ∈ gridCellsMeeting δ K, gridCell δ q := by
  intro z hz
  obtain ⟨q, hq⟩ := gridCell_cover δ hδ z
  exact mem_iUnion.mpr ⟨q, mem_iUnion.mpr ⟨⟨z, hz, hq⟩, hq⟩⟩

lemma compact_grid_cover {K U : Set ℂ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ (gridCellsMeeting δ K).Finite ∧
      K ⊆ ⋃ q ∈ gridCellsMeeting δ K, gridCell δ q ∧
      ∀ q ∈ gridCellsMeeting δ K, gridCell δ q ⊆ U := by
  obtain ⟨r, hr, hbuffer⟩ := compact_uniform_buffer hK hU hKU
  let δ := r/2
  have hδ : 0 < δ := half_pos hr
  refine ⟨δ, hδ, gridCellsMeeting_finite hδ hK, gridCellsMeeting_cover hδ K, ?_⟩
  intro q hq w hw
  obtain ⟨z, hzK, hzq⟩ := hq
  apply hbuffer
  apply mem_cthickening_of_dist_le w z r K hzK
  exact (gridCell_dist_le hw hzq).trans_eq (by dsimp [δ]; ring)

end ExpandedFA.BanachAlgebra.ContourCalculus



noncomputable section
namespace ExpandedFA.BanachAlgebra.ContourCalculus
open Set MeasureTheory Filter

/-- Oriented sides attached to cells in the finite family. -/
abbrev GridSideIndex (S : Finset (ℤ × ℤ)) := S × Fin 4

def GridSideInternal (S : Finset (ℤ × ℤ)) (e : GridSideIndex S) : Prop :=
  gridNeighbor e.1 e.2 ∈ S

/-- Pair every canceled edge with the same edge belonging to its adjacent cell. -/
def internalGridSidePair (S : Finset (ℤ × ℤ)) :
    Equiv.Perm {e : GridSideIndex S // GridSideInternal S e} where
  toFun e := ⟨(⟨gridNeighbor e.val.1 e.val.2, e.property⟩, gridOpposite e.val.2), by
    simpa only [GridSideInternal, gridNeighbor_opposite] using e.val.1.property⟩
  invFun e := ⟨(⟨gridNeighbor e.val.1 e.val.2, e.property⟩, gridOpposite e.val.2), by
    simpa only [GridSideInternal, gridNeighbor_opposite] using e.val.1.property⟩
  left_inv e := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact gridNeighbor_opposite e.val.1 e.val.2
    · exact gridOpposite_involutive e.val.2
  right_inv e := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact gridNeighbor_opposite e.val.1 e.val.2
    · exact gridOpposite_involutive e.val.2

lemma internalGridSidePair_reverse (S : Finset (ℤ × ℤ)) (δ : ℝ)
    (e : {e : GridSideIndex S // GridSideInternal S e}) :
    gridSide δ (internalGridSidePair S e).val.1 (internalGridSidePair S e).val.2 =
      (gridSide δ e.val.1 e.val.2).reverse :=
  gridSide_neighbor_reverse δ e.val.1 e.val.2

/-- Neighbor pairing has no fixed oriented side. -/
lemma internalGridSidePair_ne_self (S : Finset (ℤ × ℤ))
    (e : {e : GridSideIndex S // GridSideInternal S e}) : internalGridSidePair S e ≠ e := by
  intro he
  have hi := congrArg (fun x : {e : GridSideIndex S // GridSideInternal S e} => x.val.2) he
  change gridOpposite e.val.2 = e.val.2 at hi
  generalize e.val.2 = i at hi
  fin_cases i <;> norm_num [gridOpposite] at hi

end ExpandedFA.BanachAlgebra.ContourCalculus



noncomputable section
namespace ExpandedFA.BanachAlgebra.ContourCalculus
open Set Filter
open scoped Topology

lemma dense_avoiding_finite_coordinates {P Q : Set ℝ} (hP : P.Finite) (hQ : Q.Finite) :
    Dense {z : ℂ | z.re ∉ P ∧ z.im ∉ Q} := by
  have hPD : Dense Pᶜ := by
    convert dense_univ.sdiff_finite hP using 1
    ext x
    simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_univ, true_and]
  have hQD : Dense Qᶜ := by
    convert dense_univ.sdiff_finite hQ using 1
    ext x
    simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_univ, true_and]
  exact (hPD.prod hQD).preimage Complex.equivRealProdCLM.toHomeomorph.isOpenMap

lemma Cycle.winding_eq_of_dense (Γ : Cycle) {D V : Set ℂ} {z c : ℂ}
    (hD : Dense D) (hz : z ∉ Γ.trace) (hV : V ∈ 𝓝 z)
    (heq : ∀ w ∈ D ∩ V, Γ.winding w = c) : Γ.winding z = c := by
  obtain ⟨w, hwD, hwV, hw⟩ := hD.inter_nhds_nonempty
    (inter_mem hV (Γ.winding_eventually_eq hz))
  exact hw.symm.trans (heq w ⟨hwD,hwV⟩)


end ExpandedFA.BanachAlgebra.ContourCalculus


noncomputable section
namespace ExpandedFA.BanachAlgebra.ContourCalculus
open Set Filter MeasureTheory Metric
open scoped Topology

lemma gridCell_isCompact (δ : ℝ) (q : ℤ × ℤ) : IsCompact (gridCell δ q) :=
  isCompact_Icc.reProdIm isCompact_Icc

lemma gridCell_interior (δ : ℝ) (q : ℤ × ℤ) :
    interior (gridCell δ q) =
      Ioo (δ * (q.1 : ℝ)) (δ * ((q.1 : ℝ)+1)) ×ℂ
        Ioo (δ * (q.2 : ℝ)) (δ * ((q.2 : ℝ)+1)) := by
  rw [gridCell, Complex.interior_reProdIm, interior_Icc, interior_Icc]

lemma gridCell_closure_interior {δ : ℝ} (hδ : 0 < δ) (q : ℤ × ℤ) :
    closure (interior (gridCell δ q)) = gridCell δ q := by
  rw [gridCell_interior, Complex.closure_reProdIm,
    closure_Ioo (by nlinarith : δ*(q.1:ℝ) ≠ δ*((q.1:ℝ)+1)),
    closure_Ioo (by nlinarith : δ*(q.2:ℝ) ≠ δ*((q.2:ℝ)+1))]
  rfl

lemma gridInterval_unique {δ : ℝ} (hδ : 0 < δ) {m n : ℤ} {x : ℝ}
    (hm : δ*(m:ℝ) < x ∧ x < δ*((m:ℝ)+1))
    (hn : δ*(n:ℝ) ≤ x ∧ x ≤ δ*((n:ℝ)+1)) : m = n := by
  have hmn : (m:ℝ) < (n:ℝ)+1 :=
    (mul_lt_mul_iff_right₀ hδ).mp (hm.1.trans_le hn.2)
  have hnm : (n:ℝ) < (m:ℝ)+1 :=
    (mul_lt_mul_iff_right₀ hδ).mp (hn.1.trans_lt hm.2)
  have hmni : m < n+1 := by exact_mod_cast hmn
  have hnmi : n < m+1 := by exact_mod_cast hnm
  omega

lemma gridCell_interior_unique {δ : ℝ} (hδ : 0 < δ) {q r : ℤ × ℤ} {z : ℂ}
    (hz : z ∈ interior (gridCell δ q)) (hr : z ∈ gridCell δ r) : q = r := by
  rw [gridCell_interior] at hz
  exact Prod.ext (gridInterval_unique hδ hz.1 hr.1) (gridInterval_unique hδ hz.2 hr.2)

lemma gridCell_interiors_disjoint {δ : ℝ} (hδ : 0 < δ) {q r : ℤ × ℤ}
    (hqr : q ≠ r) : Disjoint (interior (gridCell δ q)) (interior (gridCell δ r)) := by
  apply Set.disjoint_left.mpr
  intro z hz hr
  exact hqr (gridCell_interior_unique hδ hz (interior_subset hr))

end ExpandedFA.BanachAlgebra.ContourCalculus



noncomputable section
namespace ExpandedFA.BanachAlgebra.ContourCalculus
open Set MeasureTheory Filter

lemma gridSide_mem_closedCell (δ : ℝ) (q : ℤ × ℤ) (i : Fin 4)
    (hδ : 0 ≤ δ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    (gridSide δ q i).path t ∈
      Icc (δ * (q.1 : ℝ)) (δ * ((q.1 : ℝ) + 1)) ×ℂ
        Icc (δ * (q.2 : ℝ)) (δ * ((q.2 : ℝ) + 1)) := by
  have hδt0 := mul_nonneg hδ ht.1
  have hδt1 := mul_le_of_le_one_right hδ ht.2
  rcases q with ⟨m,n⟩
  change (δ * (m : ℝ) ≤ ((gridSide δ (m,n) i).path t).re ∧
    ((gridSide δ (m,n) i).path t).re ≤ δ * ((m : ℝ) + 1)) ∧
    (δ * (n : ℝ) ≤ ((gridSide δ (m,n) i).path t).im ∧
    ((gridSide δ (m,n) i).path t).im ≤ δ * ((n : ℝ) + 1))
  fin_cases i <;> norm_num [gridSide, C1Arc.line, gridVertex, Complex.real_smul] <;>
    (repeat' constructor) <;> nlinarith

lemma gridSide_mem_neighborClosedCell (δ : ℝ) (q : ℤ × ℤ) (i : Fin 4)
    (hδ : 0 ≤ δ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    (gridSide δ q i).path t ∈
      Icc (δ * ((gridNeighbor q i).1 : ℝ)) (δ * (((gridNeighbor q i).1 : ℝ) + 1)) ×ℂ
        Icc (δ * ((gridNeighbor q i).2 : ℝ)) (δ * (((gridNeighbor q i).2 : ℝ) + 1)) := by
  have heq : (gridSide δ q i).path t =
      (gridSide δ (gridNeighbor q i) (gridOpposite i)).path (1 - t) := by
    rw [gridSide_neighbor_reverse]
    simp [C1Arc.reverse]
  rw [heq]
  exact gridSide_mem_closedCell δ (gridNeighbor q i) (gridOpposite i) hδ
    ⟨by linarith [ht.2], by linarith [ht.1]⟩

end ExpandedFA.BanachAlgebra.ContourCalculus



noncomputable section
namespace ExpandedFA.BanachAlgebra.ContourCalculus
open Set MeasureTheory Filter
open scoped Topology

lemma gridSides_balanced (δ : ℝ) (S : Finset (ℤ × ℤ)) :
    ∀ z : ℂ,
      Fintype.card {e : GridSideIndex S // (gridSide δ e.1 e.2).path 1 = z} =
        Fintype.card {e : GridSideIndex S // (gridSide δ e.1 e.2).path 0 = z} := by
  apply balanced_arcs_of_matching_permutation
    (fun e : GridSideIndex S => gridSide δ e.1 e.2)
    (Equiv.prodCongr (Equiv.refl S) (finRotate 4))
  rintro ⟨q,i⟩
  change (gridSide δ q (finRotate 4 i)).path 0 = (gridSide δ q i).path 1
  rw [finRotate_apply]
  fin_cases i <;> norm_num [gridSide, C1Arc.line]

/-- The finite grid boundary after removing paired internal sides. -/
def gridBoundaryCycle (δ : ℝ) (S : Finset (ℤ × ℤ)) : Cycle := by
  classical
  exact cycleOfBalancedArcs
    (fun e : {e : GridSideIndex S // ¬ GridSideInternal S e} => gridSide δ e.val.1 e.val.2)
    (balanced_arcs_after_removal
      (fun e : GridSideIndex S => gridSide δ e.1 e.2) (GridSideInternal S)
      (gridSides_balanced δ S) (internalGridSidePair S) (fun e => by
        change (gridSide δ (internalGridSidePair S e).val.1
          (internalGridSidePair S e).val.2).path 0 = _
        rw [internalGridSidePair_reverse]
        simp only [C1Arc.reverse, sub_zero]))

lemma gridBoundaryCycle_trace (δ : ℝ) (S : Finset (ℤ × ℤ)) :
    (gridBoundaryCycle δ S).trace =
      ⋃ e : {e : GridSideIndex S // ¬ GridSideInternal S e},
        (gridSide δ e.val.1 e.val.2).path '' Icc 0 1 := by
  classical
  unfold gridBoundaryCycle
  exact cycleOfBalancedArcs_trace _ _

lemma gridBoundaryCycle_integral_sides {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (δ : ℝ) (S : Finset (ℤ × ℤ)) (h : ℂ → X) :
    cycleIntegral (gridBoundaryCycle δ S) h =
      ∑ e : GridSideIndex S, ∫ t in (0 : ℝ)..1,
        (gridSide δ e.1 e.2).velocity t • h ((gridSide δ e.1 e.2).path t) := by
  classical
  unfold gridBoundaryCycle
  rw [cycleOfBalancedArcs_integral]
  exact (sum_arcs_remove_reversed
    (fun e : GridSideIndex S => gridSide δ e.1 e.2) (GridSideInternal S)
    (internalGridSidePair S) (internalGridSidePair_reverse S δ) h).symm

end ExpandedFA.BanachAlgebra.ContourCalculus



noncomputable section
namespace ExpandedFA.BanachAlgebra.ContourCalculus
open Set MeasureTheory Filter
open scoped Topology

def gridTileCycle (δ : ℝ) (q : ℤ × ℤ) : Cycle :=
  unitSquareCycle.affine (gridVertex δ q) δ

lemma gridTileCycle_arc (δ : ℝ) (q : ℤ × ℤ) (i : Fin 4) :
    (gridTileCycle δ q).arc i = gridSide δ q i := by
  rcases q with ⟨m,n⟩
  fin_cases i <;>
    dsimp [gridTileCycle, unitSquareCycle, Cycle.affine, diamondCycle, diamondArcs, gridSide]
  all_goals rw [C1Arc.affine_line, C1Arc.affine_line]
  all_goals congr 1 <;> simp only [gridVertex] <;> push_cast <;> ring_nf <;> simp [Complex.I_sq] <;> ring

lemma gridTileCycle_winding_one (δ : ℝ) (q : ℤ × ℤ) (hδ : 0 < δ) {z : ℂ}
    (hx0 : δ*(q.1:ℝ) < z.re) (hx1 : z.re < δ*((q.1:ℝ)+1))
    (hy0 : δ*(q.2:ℝ) < z.im) (hy1 : z.im < δ*((q.2:ℝ)+1)) :
    (gridTileCycle δ q).winding z = 1 := by
  rw [gridTileCycle, Cycle.winding_affine _ _ _ _ (Complex.ofReal_ne_zero.mpr hδ.ne')]
  apply unitSquareCycle_winding_eq_one
  all_goals simp only [gridVertex, Complex.div_ofReal_re, Complex.div_ofReal_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.intCast_re, Complex.intCast_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, add_zero, zero_add, sub_zero]
  · exact div_pos (sub_pos.mpr hx0) hδ
  · exact (div_lt_one hδ).mpr (by nlinarith)
  · exact div_pos (sub_pos.mpr hy0) hδ
  · exact (div_lt_one hδ).mpr (by nlinarith)

lemma gridTileCycle_winding_zero (δ : ℝ) (q : ℤ × ℤ) (hδ : 0 < δ) {z : ℂ}
    (hz : z.re < δ*(q.1:ℝ) ∨ δ*((q.1:ℝ)+1) < z.re ∨
      z.im < δ*(q.2:ℝ) ∨ δ*((q.2:ℝ)+1) < z.im) :
    (gridTileCycle δ q).winding z = 0 := by
  rw [gridTileCycle, Cycle.winding_affine _ _ _ _ (Complex.ofReal_ne_zero.mpr hδ.ne')]
  apply unitSquareCycle_winding_eq_zero
  simp only [gridVertex, Complex.div_ofReal_re, Complex.div_ofReal_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.intCast_re, Complex.intCast_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, add_zero, zero_add, sub_zero]
  rcases hz with hx | hx | hy | hy
  · exact Or.inl (div_neg_of_neg_of_pos (sub_neg.mpr hx) hδ)
  · exact Or.inr (Or.inl ((one_lt_div hδ).mpr (by nlinarith)))
  · exact Or.inr (Or.inr (Or.inl (div_neg_of_neg_of_pos (sub_neg.mpr hy) hδ)))
  · exact Or.inr (Or.inr (Or.inr ((one_lt_div hδ).mpr (by nlinarith))))

end ExpandedFA.BanachAlgebra.ContourCalculus



noncomputable section
namespace ExpandedFA.BanachAlgebra.ContourCalculus
open Set MeasureTheory Filter

lemma gridSide_boundary_coordinate (δ : ℝ) (q : ℤ × ℤ) (i : Fin 4) (t : ℝ) :
    ((gridSide δ q i).path t).re = δ * (q.1 : ℝ) ∨
    ((gridSide δ q i).path t).re = δ * ((q.1 : ℝ) + 1) ∨
    ((gridSide δ q i).path t).im = δ * (q.2 : ℝ) ∨
    ((gridSide δ q i).path t).im = δ * ((q.2 : ℝ) + 1) := by
  rcases q with ⟨m,n⟩
  fin_cases i
  · apply Or.inr (Or.inr (Or.inr _))
    simp [gridSide, C1Arc.line, gridVertex, Complex.real_smul]
  · apply Or.inl
    simp [gridSide, C1Arc.line, gridVertex, Complex.real_smul]
  · apply Or.inr (Or.inr (Or.inl _))
    simp [gridSide, C1Arc.line, gridVertex, Complex.real_smul]
  · apply Or.inr (Or.inl _)
    simp [gridSide, C1Arc.line, gridVertex, Complex.real_smul]

end ExpandedFA.BanachAlgebra.ContourCalculus



noncomputable section
namespace ExpandedFA.BanachAlgebra.ContourCalculus
open Set MeasureTheory Filter
open scoped Topology

lemma gridTileCycle_winding_zero_of_notMem {δ : ℝ} (hδ : 0 < δ)
    {q : ℤ × ℤ} {z : ℂ} (hz : z ∉ gridCell δ q) :
    (gridTileCycle δ q).winding z = 0 := by
  apply gridTileCycle_winding_zero δ q hδ
  by_contra hn
  push_neg at hn
  exact hz ⟨⟨hn.1, hn.2.1⟩, ⟨hn.2.2.1, hn.2.2.2⟩⟩

lemma gridTileCycle_winding_one_of_mem_interior {δ : ℝ} (hδ : 0 < δ)
    {q : ℤ × ℤ} {z : ℂ} (hz : z ∈ interior (gridCell δ q)) :
    (gridTileCycle δ q).winding z = 1 := by
  rw [gridCell_interior] at hz
  exact gridTileCycle_winding_one δ q hδ hz.1.1 hz.1.2 hz.2.1 hz.2.2

lemma gridTile_winding_sum_one {δ : ℝ} (hδ : 0 < δ) (S : Finset (ℤ × ℤ))
    {q : ℤ × ℤ} (hq : q ∈ S) {z : ℂ} (hz : z ∈ interior (gridCell δ q)) :
    (∑ r ∈ S, (gridTileCycle δ r).winding z) = 1 := by
  rw [Finset.sum_eq_single q]
  · exact gridTileCycle_winding_one_of_mem_interior hδ hz
  · intro r hr hrq
    apply gridTileCycle_winding_zero_of_notMem hδ
    exact fun hzr => hrq (gridCell_interior_unique hδ hz hzr).symm
  · exact fun hn => (hn hq).elim

lemma gridTile_winding_sum_zero {δ : ℝ} (hδ : 0 < δ) (S : Finset (ℤ × ℤ))
    {z : ℂ} (hz : ∀ q ∈ S, z ∉ gridCell δ q) :
    (∑ r ∈ S, (gridTileCycle δ r).winding z) = 0 :=
  Finset.sum_eq_zero (fun q hq => gridTileCycle_winding_zero_of_notMem hδ (hz q hq))

lemma gridTile_winding_sum_zero_or_one {δ : ℝ} (hδ : 0 < δ) (S : Finset (ℤ × ℤ))
    {z : ℂ}
    (hcoord : ∀ q ∈ S, z.re ≠ δ*(q.1:ℝ) ∧ z.re ≠ δ*((q.1:ℝ)+1) ∧
      z.im ≠ δ*(q.2:ℝ) ∧ z.im ≠ δ*((q.2:ℝ)+1)) :
    (∑ r ∈ S, (gridTileCycle δ r).winding z) = 0 ∨
      (∑ r ∈ S, (gridTileCycle δ r).winding z) = 1 := by
  by_cases hex : ∃ q ∈ S, z ∈ gridCell δ q
  · obtain ⟨q, hq, hz⟩ := hex
    right
    apply gridTile_winding_sum_one hδ S hq
    rw [gridCell_interior]
    have hn := hcoord q hq
    exact ⟨⟨lt_of_le_of_ne hz.1.1 hn.1.symm, lt_of_le_of_ne hz.1.2 hn.2.1⟩,
      ⟨lt_of_le_of_ne hz.2.1 hn.2.2.1.symm, lt_of_le_of_ne hz.2.2 hn.2.2.2⟩⟩
  · left
    exact gridTile_winding_sum_zero hδ S (fun q hq hz => hex ⟨q, hq, hz⟩)

lemma dense_grid_coordinates (δ : ℝ) (S : Finset (ℤ × ℤ)) :
    Dense {z : ℂ | ∀ q ∈ S, z.re ≠ δ*(q.1:ℝ) ∧ z.re ≠ δ*((q.1:ℝ)+1) ∧
      z.im ≠ δ*(q.2:ℝ) ∧ z.im ≠ δ*((q.2:ℝ)+1)} := by
  let P : Set ℝ := (range fun q : S => δ*(q.val.1:ℝ)) ∪
    (range fun q : S => δ*((q.val.1:ℝ)+1))
  let Q : Set ℝ := (range fun q : S => δ*(q.val.2:ℝ)) ∪
    (range fun q : S => δ*((q.val.2:ℝ)+1))
  have hP : P.Finite := (finite_range _).union (finite_range _)
  have hQ : Q.Finite := (finite_range _).union (finite_range _)
  apply (dense_avoiding_finite_coordinates hP hQ).mono
  intro z hz q hq
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro he
    exact hz.1 (Or.inl (mem_range.mpr ⟨⟨q,hq⟩, he.symm⟩))
  · intro he
    exact hz.1 (Or.inr (mem_range.mpr ⟨⟨q,hq⟩, he.symm⟩))
  · intro he
    exact hz.2 (Or.inl (mem_range.mpr ⟨⟨q,hq⟩, he.symm⟩))
  · intro he
    exact hz.2 (Or.inr (mem_range.mpr ⟨⟨q,hq⟩, he.symm⟩))

end ExpandedFA.BanachAlgebra.ContourCalculus



noncomputable section
namespace ExpandedFA.BanachAlgebra.ContourCalculus
open Set MeasureTheory Filter
open scoped Topology

lemma gridBoundaryCycle_integral {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (δ : ℝ) (S : Finset (ℤ × ℤ)) (h : ℂ → X) :
    cycleIntegral (gridBoundaryCycle δ S) h = ∑ q ∈ S, cycleIntegral (gridTileCycle δ q) h := by
  classical
  rw [gridBoundaryCycle_integral_sides]
  change (∑ e : S × Fin 4, ∫ t in (0 : ℝ)..1,
    (gridSide δ e.1 e.2).velocity t • h ((gridSide δ e.1 e.2).path t)) = _
  rw [Fintype.sum_prod_type]
  change (∑ q : S, ∑ i : Fin 4, ∫ t in (0 : ℝ)..1,
    (gridSide δ q i).velocity t • h ((gridSide δ q i).path t)) = _
  rw [Finset.sum_coe_sort S (fun q : ℤ × ℤ => ∑ i : Fin 4, ∫ t in (0 : ℝ)..1,
    (gridSide δ q i).velocity t • h ((gridSide δ q i).path t))]
  apply Finset.sum_congr rfl
  intro q hq
  change (∑ i : Fin 4, ∫ t in (0 : ℝ)..1,
    (gridSide δ q i).velocity t • h ((gridSide δ q i).path t)) =
    ∑ i : Fin 4, ∫ t in (0 : ℝ)..1,
      ((gridTileCycle δ q).arc i).velocity t • h (((gridTileCycle δ q).arc i).path t)
  simp only [gridTileCycle_arc]

lemma gridBoundaryCycle_winding (δ : ℝ) (S : Finset (ℤ × ℤ)) (z : ℂ) :
    (gridBoundaryCycle δ S).winding z = ∑ q ∈ S, (gridTileCycle δ q).winding z := by
  classical
  simp only [Cycle.winding, gridBoundaryCycle_integral, Finset.mul_sum]

end ExpandedFA.BanachAlgebra.ContourCalculus



noncomputable section
namespace ExpandedFA.BanachAlgebra.ContourCalculus
open Set MeasureTheory Filter

/-- Every retained side lies in U and misses K, since a side touching K
would have a selected cell on each side and would be canceled. -/
lemma gridBoundaryCycle_trace_subset {δ : ℝ} {S : Finset (ℤ × ℤ)} {K U : Set ℂ}
    (hδ : 0 ≤ δ) (hU : ∀ q ∈ S, gridCell δ q ⊆ U)
    (hK : ∀ q, (∃ z ∈ K, z ∈ gridCell δ q) → q ∈ S) :
    (gridBoundaryCycle δ S).trace ⊆ U \ K := by
  intro z hz
  rw [gridBoundaryCycle_trace] at hz
  obtain ⟨e, t, ht, rfl⟩ := mem_iUnion.mp hz
  have hown : (gridSide δ e.val.1 e.val.2).path t ∈ gridCell δ e.val.1 :=
    gridSide_mem_closedCell δ e.val.1 e.val.2 hδ ht
  have hneighbor : (gridSide δ e.val.1 e.val.2).path t ∈
      gridCell δ (gridNeighbor e.val.1 e.val.2) :=
    gridSide_mem_neighborClosedCell δ e.val.1 e.val.2 hδ ht
  refine ⟨hU e.val.1 e.val.1.property hown, ?_⟩
  intro hzK
  apply e.property
  exact hK _ ⟨_, hzK, hneighbor⟩

end ExpandedFA.BanachAlgebra.ContourCalculus


noncomputable section
namespace ExpandedFA.BanachAlgebra.ContourCalculus
open Set Filter
open scoped Topology

lemma Cycle.winding_eq_of_mem_closure (Γ : Cycle) {z c : ℂ} {D : Set ℂ}
    (hz : z ∉ Γ.trace) (hcl : z ∈ closure D)
    (hD : ∀ w ∈ D, Γ.winding w = c) : Γ.winding z = c := by
  obtain ⟨w, hwD, hw⟩ :=
    ((mem_closure_iff_frequently.mp hcl).and_eventually (Γ.winding_eventually_eq hz)).exists
  exact hw.symm.trans (hD w hwD)

lemma Cycle.winding_mem_of_mem_closure (Γ : Cycle) {z : ℂ} {D C : Set ℂ}
    (hz : z ∉ Γ.trace) (hcl : z ∈ closure D)
    (hD : ∀ w ∈ D, Γ.winding w ∈ C) : Γ.winding z ∈ C := by
  obtain ⟨w, hwD, hw⟩ :=
    ((mem_closure_iff_frequently.mp hcl).and_eventually (Γ.winding_eventually_eq hz)).exists
  exact hw ▸ hD w hwD

lemma dense_compl_gridCell_frontiers (δ : ℝ) (S : Finset (ℤ × ℤ)) :
    Dense {z : ℂ | ∀ q ∈ S, z ∉ frontier (gridCell δ q)} := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (dense_univ : Dense (Set.univ : Set ℂ))
  | @insert q S hq ih =>
    have heq : {z : ℂ | ∀ r ∈ insert q S, z ∉ frontier (gridCell δ r)} =
        (frontier (gridCell δ q))ᶜ ∩ {z : ℂ | ∀ r ∈ S, z ∉ frontier (gridCell δ r)} := by
      ext z
      simp only [mem_ofPred_eq, Finset.mem_insert, forall_eq_or_imp, mem_inter_iff, mem_compl_iff]
    rw [heq]
    have hd : Dense (frontier (gridCell δ q))ᶜ :=
      interior_eq_empty_iff_dense_compl.mp (interior_frontier (gridCell_isCompact δ q).isClosed)
    exact hd.inter_of_isOpen_left ih isClosed_frontier.isOpen_compl

end ExpandedFA.BanachAlgebra.ContourCalculus



noncomputable section
namespace ExpandedFA.BanachAlgebra.ContourCalculus
open Set MeasureTheory Filter
open scoped Topology
universe u

lemma gridBoundaryCycle_positive {δ : ℝ} (hδ : 0 < δ) (S : Finset (ℤ × ℤ)) :
    (gridBoundaryCycle δ S).Positive := by
  apply Cycle.positive_of_dense _ (dense_grid_coordinates δ S)
  intro z hz _
  rw [gridBoundaryCycle_winding]
  exact gridTile_winding_sum_zero_or_one hδ S hz

lemma gridBoundaryCycle_winding_one_of_mem_cell {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (ℤ × ℤ)) {q : ℤ × ℤ} (hq : q ∈ S) {z : ℂ}
    (hz : z ∈ gridCell δ q) (hn : z ∉ (gridBoundaryCycle δ S).trace) :
    (gridBoundaryCycle δ S).winding z = 1 := by
  apply Cycle.winding_eq_of_mem_closure _ hn
    (show z ∈ closure (interior (gridCell δ q)) by
      rw [gridCell_closure_interior hδ]; exact hz)
  intro w hw
  rw [gridBoundaryCycle_winding]
  exact gridTile_winding_sum_one hδ S hq hw

/-- Compact sets in arbitrary open subsets admit finite positive contour boundaries. -/
theorem admissible_cycles_exist : Spec.AdmissibleCyclesExist := by
  intro K U hK hU hKU
  obtain ⟨δ, hδ, hfin, _hcover, hcellsU⟩ := compact_grid_cover hK hU hKU
  let S : Finset (ℤ × ℤ) := hfin.toFinset
  have hS (q : ℤ × ℤ) : q ∈ S ↔ q ∈ gridCellsMeeting δ K := hfin.mem_toFinset
  have htr : (gridBoundaryCycle δ S).trace ⊆ U \ K :=
    gridBoundaryCycle_trace_subset hδ.le
      (fun q hq => hcellsU q ((hS q).mp hq))
      (fun q hq => (hS q).mpr hq)
  refine ⟨gridBoundaryCycle δ S, ?_⟩
  apply Cycle.admissible_of_pointwise _ htr (gridBoundaryCycle_positive hδ S)
  · intro z hzK
    obtain ⟨q, hzq⟩ := gridCell_cover δ hδ z
    exact gridBoundaryCycle_winding_one_of_mem_cell hδ S
      ((hS q).mpr ⟨z, hzK, hzq⟩) hzq (fun ht => (htr ht).2 hzK)
  · intro z hzU
    rw [gridBoundaryCycle_winding]
    exact gridTile_winding_sum_zero hδ S (fun q hq hzq =>
      hzU (hcellsU q ((hS q).mp hq) hzq))

/-- The total choice is admissible on every original holomorphy neighborhood. -/
theorem selected_cycle_admissible : Spec.SelectedCycleAdmissible.{u} :=
  selected_cycle_admissible_of_exists admissible_cycles_exist

/-- The value depends only on the holomorphic germ on a neighborhood of the spectrum. -/
theorem neighborhood_independence : Spec.NeighborhoodIndependence.{u} :=
  neighborhood_independence_of_cycles admissible_cycles_exist cycle_independence

end ExpandedFA.BanachAlgebra.ContourCalculus
