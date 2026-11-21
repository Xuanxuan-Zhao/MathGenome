import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.IntervalExtremizers
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.IntervalL1Constants
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.Ascoli
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarLpDuality
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.Maps.Proper.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace ExpandedFA.PartIV.IntervalExtremizers
open ExpandedFA.Sobolev.OneDimensional

variable {𝕜 : Type} [RCLike 𝕜]

@[simp] theorem extension_apply (f : C(Segment, 𝕜)) (x : Segment) :
    extension f x = f x := by simp [extension, projIcc_val]

theorem extension_continuous (f : C(Segment, 𝕜)) : Continuous (extension f) :=
  f.continuous.comp continuous_projIcc

/-- Continuing constantly outside the interval is a bounded linear operation. -/
def extensionCLM : C(Segment, 𝕜) →L[𝕜] (ℝ →ᵇ 𝕜) :=
  (BoundedContinuousFunction.compContinuousCLM 𝕜 𝕜
    ⟨projIcc 0 1 (by norm_num), continuous_projIcc⟩).comp
    (ContinuousMap.linearIsometryBoundedOfCompact Segment 𝕜 𝕜).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem extensionCLM_apply (f : C(Segment, 𝕜)) (x : ℝ) :
    extensionCLM f x = extension f x := rfl

/-- The continuous inclusion in Lq, including q=∞. -/
def inclusion (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    C(Segment, 𝕜) →L[𝕜] Lp 𝕜 q intervalMeasure :=
  (BoundedContinuousFunction.toLp q intervalMeasure 𝕜).comp extensionCLM

@[simp] theorem norm_inclusion (q : ℝ≥0∞) [Fact (1 ≤ q)] (f : C(Segment, 𝕜)) :
    ‖inclusion q f‖ = normQ q f := by
  rw [Lp.norm_def]
  congr 1
  exact eLpNorm_congr_ae (BoundedContinuousFunction.coeFn_toLp q intervalMeasure 𝕜
    (extensionCLM f))

theorem normQ_continuous (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    Continuous (normQ (𝕜 := 𝕜) q) := by
  simpa only [norm_inclusion] using (inclusion (𝕜 := 𝕜) q).continuous.norm

@[simp] theorem normQ_zero (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    normQ (𝕜 := 𝕜) q 0 = 0 := by rw [← norm_inclusion, map_zero, norm_zero]

theorem normQ_nonneg (q : ℝ≥0∞) (f : C(Segment, 𝕜)) : 0 ≤ normQ q f :=
  ENNReal.toReal_nonneg

@[simp] theorem normQ_smul (q : ℝ≥0∞) [Fact (1 ≤ q)] (c : 𝕜)
    (f : C(Segment, 𝕜)) : normQ q (c • f) = ‖c‖ * normQ q f := by
  simp only [← norm_inclusion, map_smul, norm_smul]

/-- At infinity the target norm is the original closed-interval supremum. -/
theorem normQ_top (f : C(Segment, 𝕜)) :
    normQ ∞ f = ExpandedFA.PartIV.IntervalL1.supNorm (extension f) := by
  rw [normQ, ExpandedFA.PartIV.IntervalL1.supNorm_eq_essentialSup
    (extension_continuous f).continuousOn, ENNReal.toReal_ofReal
      (ExpandedFA.PartIV.IntervalL1.supNorm_nonneg (extension_continuous f).continuousOn)]

theorem normQ_eq_zero_iff (q : ℝ≥0∞) [Fact (1 ≤ q)] (f : C(Segment, 𝕜)) :
    normQ q f = 0 ↔ f = 0 := by
  constructor
  · intro h
    have hi : inclusion q f = 0 := norm_eq_zero.mp ((norm_inclusion q f).trans h)
    have ha : extension f =ᵐ[intervalMeasure] 0 :=
      (BoundedContinuousFunction.coeFn_toLp q intervalMeasure 𝕜 (extensionCLM f)).symm.trans
        (hi ▸ Lp.coeFn_zero 𝕜 q intervalMeasure)
    have hb := ExpandedFA.PartIV.IntervalL1.continuous_norm_bound_of_ae (C := 0)
      (extension_continuous f).continuousOn (ha.mono (fun x hx => by simp [hx]))
    ext x
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa using hb x x.property) (norm_nonneg _)
  · rintro rfl
    exact normQ_zero q

theorem normQ_pos_iff (q : ℝ≥0∞) [Fact (1 ≤ q)] (f : C(Segment, 𝕜)) :
    0 < normQ q f ↔ f ≠ 0 := by
  rw [lt_iff_le_and_ne]
  constructor
  · rintro ⟨_, hn⟩ hzero
    exact hn (by simp [hzero])
  · intro hn
    exact ⟨normQ_nonneg q f, fun h => hn ((normQ_eq_zero_iff q f).mp h.symm)⟩

/-- Any function with zero mean or zero trace is bounded by its oscillation.
The estimate also handles complex-valued functions: it does not use a real
zero of a mean-zero function. -/
theorem bound_of_oscillation {f : C(Segment, 𝕜)} {M : ℝ}
    {b : Constraint} (hb : Satisfies b f)
    (h : ∀ x y : Segment, ‖f x - f y‖ ≤ M) : ∀ x : Segment, ‖f x‖ ≤ M := by
  intro x
  cases b with
  | zeroTrace =>
    have hzero : f 0 = 0 := by
      simpa [Satisfies, extension, projIcc_left] using hb.1
    simpa [hzero] using h x 0
  | meanZero =>
    have hmean : ∫ t in (0 : ℝ)..1, extension f t = 0 := hb
    have he : (∫ t in (0 : ℝ)..1, f x - extension f t) = f x := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const
        ((extension_continuous f).intervalIntegrable 0 1), hmean]
      simp
    rw [← he]
    calc
      ‖∫ t in (0 : ℝ)..1, f x - extension f t‖ ≤ ∫ t in (0 : ℝ)..1, M := by
        apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num) _ intervalIntegrable_const
        exact Filter.Eventually.of_forall (fun t ht => by
          simpa only [extension, projIcc_of_mem (by norm_num) ⟨ht.1.le, ht.2⟩] using
            h x ⟨t, ⟨ht.1.le, ht.2⟩⟩)
      _ = M := by simp

/-- A derivative bound yields the manuscript's Hölder modulus, including
exponent one at p=∞. -/
theorem derivativeBall_increment {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p)
    {b : Constraint} {f : C(Segment, 𝕜)} (hf : f ∈ derivativeBall 𝕜 p b)
    (x y : Segment) :
    ‖f x - f y‖ ≤ |(x : ℝ) - y| ^ (1 - reciprocalExponent p) := by
  obtain ⟨_, u, hu, hdu⟩ := hf
  have hx : (x : ℝ) ∈ closure (ExpandedFA.PartIV.IntervalL1.unitInterval : Set ℝ) := by
    simpa [ExpandedFA.PartIV.IntervalL1.unitInterval, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] using x.property
  have hy : (y : ℝ) ∈ closure (ExpandedFA.PartIV.IntervalL1.unitInterval : Set ℝ) := by
    simpa [ExpandedFA.PartIV.IntervalL1.unitInterval, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] using y.property
  have hh := holder_estimate 𝕜 _ ordConnected_Ioo p hp u (extension f) hu x hx y hy
  simp only [extension_apply] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_right hdu (Real.rpow_nonneg (abs_nonneg _) _)).trans_eq
    (one_mul _))

theorem holderExponent_pos {p : ℝ≥0∞} (hp : 1 < p) :
    0 < 1 - reciprocalExponent p := by
  by_cases ht : p = ∞
  · simp [ht, reciprocalExponent]
  · have hr : 1 < p.toReal := by
      exact (ENNReal.toReal_lt_toReal (by simp) ht).mpr hp
    dsimp [reciprocalExponent]
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr hr)

/-- Uniform boundedness on the closed interval, for both constraints. -/
theorem derivativeBall_bound {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p)
    {b : Constraint} {f : C(Segment, 𝕜)} (hf : f ∈ derivativeBall 𝕜 p b) :
    ∀ x : Segment, ‖f x‖ ≤ 1 := by
  apply bound_of_oscillation hf.1
  intro x y
  apply (derivativeBall_increment hp hf x y).trans
  apply Real.rpow_le_one (abs_nonneg _)
  · rw [abs_le]
    constructor <;> linarith [x.property.1, x.property.2, y.property.1, y.property.2]
  · exact (holderExponent_pos hp).le

/-- Hölder control supplies equicontinuity in the actual compact-domain sense. -/
theorem derivativeBall_equicontinuous {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p)
    (b : Constraint) : Equicontinuous
      (fun (f : derivativeBall 𝕜 p b) (x : Segment) => f.val x) := by
  intro x
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have hc : Continuous (fun y : Segment => |(x : ℝ) - y| ^ (1 - reciprocalExponent p)) :=
    ((continuous_const.sub continuous_subtype_val).abs).rpow_const
      (fun _ => Or.inr (holderExponent_pos hp).le)
  have hz : |(x : ℝ) - x| ^ (1 - reciprocalExponent p) = 0 := by
    simp [Real.zero_rpow (holderExponent_pos hp).ne']
  have he : ∀ᶠ (y : Segment) in 𝓝 x, |(x : ℝ) - y| ^ (1 - reciprocalExponent p) < ε := by
    have ht : Tendsto (fun y : Segment => |(x : ℝ) - y| ^ (1 - reciprocalExponent p))
        (𝓝 x) (𝓝 (0 : ℝ)) := by simpa only [hz] using hc.tendsto x
    exact ht.eventually (eventually_lt_nhds hε)
  filter_upwards [he] with y hy f
  rw [dist_eq_norm]
  exact (derivativeBall_increment hp f.property x y).trans_lt hy

/-- The compactness part of the direct method that follows solely from the
source's Hölder estimate and Arzelà–Ascoli. Closedness is an additional claim:
it must preserve the derivative norm bound in the limit. -/
theorem derivativeBall_compact_closure {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p) (b : Constraint) : IsCompact (closure (derivativeBall 𝕜 p b)) := by
  apply (ExpandedFA.PartV.Ascoli.arzela_ascoli 𝕜 Segment (derivativeBall 𝕜 p b)).mpr
  exact ⟨⟨1, zero_le_one, fun f hf => derivativeBall_bound hp hf⟩,
    derivativeBall_equicontinuous hp b⟩

/-- A compact derivative ball gives a maximizer of every required Lq norm.
The positive competitor prevents selection of the zero function. -/
theorem exists_positive_maximizer {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {b : Constraint} (hc : IsCompact (derivativeBall 𝕜 p b))
    (hn : ∃ f ∈ derivativeBall 𝕜 p b, 0 < normQ q f) :
    ∃ f ∈ derivativeBall 𝕜 p b, 0 < normQ q f ∧
      ∀ g ∈ derivativeBall 𝕜 p b, normQ q g ≤ normQ q f := by
  obtain ⟨g, hg, hgp⟩ := hn
  obtain ⟨f, hf, hmax⟩ := hc.exists_isMaxOn ⟨g, hg⟩ (normQ_continuous q).continuousOn
  exact ⟨f, hf, hgp.trans_le (hmax hg), hmax⟩

/-- The remaining normalization and finite-zero-space bridges are stated as
explicit hypotheses of this reduction, not assumed in the final source claim.
They are independent of the compactness/lower-semicontinuity argument. -/
theorem attained_of_compact_and_normalization {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (b : Constraint)
    (hc : IsCompact (derivativeBall 𝕜 p b))
    (hn : ∃ f ∈ derivativeBall 𝕜 p b, 0 < normQ q f)
    (hscale : ∀ (u : IntervalW1p 𝕜 p) (f : C(Segment, 𝕜)),
      Realizes u f → Satisfies b f →
        ∃ g ∈ derivativeBall 𝕜 p b, normQ q f ≤ normQ q g * ‖derivativeLp u‖)
    (hz : ∀ (u : IntervalW1p 𝕜 p) (f : C(Segment, 𝕜)),
      Realizes u f → Satisfies b f → FiniteZeroSpace b u) :
    Attained 𝕜 p q b := by
  obtain ⟨f, hf, hpos, hmax⟩ := exists_positive_maximizer hc hn
  obtain ⟨hb, u, hu, hdu⟩ := hf
  have hbound : ∀ (v : IntervalW1p 𝕜 p) (g : C(Segment, 𝕜)),
      Realizes v g → Satisfies b g → normQ q g ≤ normQ q f * ‖derivativeLp v‖ := by
    intro v g hv hg
    obtain ⟨k, hk, hkg⟩ := hscale v g hv hg
    exact hkg.trans (mul_le_mul_of_nonneg_right (hmax k hk) (norm_nonneg _))
  have heq : normQ q f = normQ q f * ‖derivativeLp u‖ :=
    le_antisymm (hbound u f hu hb)
      (by simpa using mul_le_mul_of_nonneg_left hdu hpos.le)
  have hdpos : 0 < ‖derivativeLp u‖ := by
    by_contra hd
    have hd0 : ‖derivativeLp u‖ = 0 := le_antisymm (le_of_not_gt hd) (norm_nonneg _)
    rw [hd0, mul_zero] at heq
    exact hpos.ne' heq
  exact ⟨normQ q f, hpos, u, f, hu, hb, hz u f hu hb,
    (normQ_pos_iff q f).mp hpos, hdpos, hpos, heq, hbound⟩

/-- Continuous representatives are determined by the underlying Lp class. -/
theorem realizes_of_represents {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : IntervalW1p 𝕜 p) (f : C(Segment, 𝕜))
    (hv : Represents (baseLp u) (extension f)) : Realizes u f := by
  obtain ⟨F, hF⟩ := representative_existence 𝕜 _ ordConnected_Ioo p u
  have he := representative_uniqueness 𝕜 _ p (baseLp u) F (extension f)
    hF.1 (extension_continuous f).continuousOn hF.2.1 hv
  refine ⟨(extension_continuous f).continuousOn, hv, ?_, ?_⟩
  · intro a ha b hb
    apply (hF.2.2.1 a ha b hb).congr
    intro x hx
    apply he
    have hx' := uIcc_subset_Icc (Ioo_subset_Icc_self ha) (Ioo_subset_Icc_self hb) hx
    simpa [ExpandedFA.PartIV.IntervalL1.unitInterval, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] using hx'
  · intro x hx y hy
    refine ⟨(hF.2.2.2 x hx y hy).1, ?_⟩
    rw [← he hx, ← he hy]
    exact (hF.2.2.2 x hx y hy).2

@[simp] theorem extension_smul (c : 𝕜) (f : C(Segment, 𝕜)) :
    extension (c • f) = c • extension f := rfl

/-- Scalar multiplication acts on the same accepted weak derivative graph. -/
theorem realizes_smul {p : ℝ≥0∞} [Fact (1 ≤ p)] {u : IntervalW1p 𝕜 p}
    {f : C(Segment, 𝕜)} (hu : Realizes u f) (c : 𝕜) : Realizes (c • u) (c • f) := by
  apply realizes_of_represents
  have hc : baseLp (c • u) = c • baseLp u := rfl
  rw [hc]
  filter_upwards [Lp.coeFn_smul c (baseLp u), hu.2.1] with x hx hxu
  change (c • baseLp u) x = c • extension f (x 0)
  rw [hx]
  change c • baseLp u x = c • extension f (x 0)
  rw [hxu]

@[simp] theorem derivativeLp_smul {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (c : 𝕜) (u : IntervalW1p 𝕜 p) : derivativeLp (c • u) = c • derivativeLp u := rfl

theorem satisfies_smul {b : Constraint} {f : C(Segment, 𝕜)}
    (hf : Satisfies b f) (c : 𝕜) : Satisfies b (c • f) := by
  cases b with
  | meanZero =>
    change (∫ x in (0 : ℝ)..1, c • extension f x) = 0
    rw [intervalIntegral.integral_smul, show (∫ x in (0 : ℝ)..1, extension f x) = 0 from hf,
      smul_zero]
  | zeroTrace =>
    change c • extension f 0 = 0 ∧ c • extension f 1 = 0
    simp [hf.1, hf.2]

/-- The only function in either constraint class with zero derivative is zero. -/
theorem eq_zero_of_derivative_norm_eq_zero {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p)
    {u : IntervalW1p 𝕜 p} {f : C(Segment, 𝕜)} (hu : Realizes u f)
    {b : Constraint} (hf : Satisfies b f) (hd : ‖derivativeLp u‖ = 0) : f = 0 := by
  have hb : ∀ x : Segment, ‖f x‖ ≤ 0 := by
    apply bound_of_oscillation hf
    intro x y
    have hx : (x : ℝ) ∈ closure (ExpandedFA.PartIV.IntervalL1.unitInterval : Set ℝ) := by
      simpa [ExpandedFA.PartIV.IntervalL1.unitInterval, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] using x.property
    have hy : (y : ℝ) ∈ closure (ExpandedFA.PartIV.IntervalL1.unitInterval : Set ℝ) := by
      simpa [ExpandedFA.PartIV.IntervalL1.unitInterval, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] using y.property
    simpa only [extension_apply, hd, zero_mul] using
      holder_estimate 𝕜 _ ordConnected_Ioo p hp u (extension f) hu x hx y hy
  ext x
  exact norm_eq_zero.mp (le_antisymm (hb x) (norm_nonneg _))

/-- Normalize by the derivative norm; zero-derivative functions are handled
separately, so normalization does not discard the zero case. -/
theorem derivative_normalization {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : 1 < p) (b : Constraint) (u : IntervalW1p 𝕜 p) (f : C(Segment, 𝕜))
    (hu : Realizes u f) (hf : Satisfies b f) :
    ∃ g ∈ derivativeBall 𝕜 p b, normQ q f ≤ normQ q g * ‖derivativeLp u‖ := by
  by_cases hd : ‖derivativeLp u‖ = 0
  · have hz := eq_zero_of_derivative_norm_eq_zero hp hu hf hd
    refine ⟨f, ⟨hf, u, hu, by simp [hd]⟩, ?_⟩
    simp [hz]
  · let c : 𝕜 := (‖derivativeLp u‖⁻¹ : ℝ)
    have hdn : 0 < ‖derivativeLp u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
    have hc : ‖c‖ = ‖derivativeLp u‖⁻¹ := by
      simp [c, RCLike.norm_ofReal]
    refine ⟨c • f, ⟨satisfies_smul hf c, c • u, realizes_smul hu c, ?_⟩, ?_⟩
    · rw [derivativeLp_smul, norm_smul, hc, inv_mul_cancel₀ hd]
    · rw [normQ_smul, hc]
      exact le_of_eq (by field_simp)

theorem finiteZeroSpace_of_satisfies {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {u : IntervalW1p 𝕜 p} {f : C(Segment, 𝕜)} (hu : Realizes u f)
    {b : Constraint} (hf : Satisfies b f) : FiniteZeroSpace b u := by
  intro hb hp
  subst b
  exact ExpandedFA.Sobolev.Trace.interval_zeroSpace_of_endpoints hp (by norm_num)
    u (extension f) hu hf.1 hf.2

/-- Lq maxima give exactly the best constant once the derivative ball is
compact. All analytic normalization and trace bridges above are now discharged. -/
theorem attained_of_compact {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : 1 < p) (b : Constraint) (hc : IsCompact (derivativeBall 𝕜 p b))
    (hn : ∃ f ∈ derivativeBall 𝕜 p b, 0 < normQ q f) : Attained 𝕜 p q b :=
  attained_of_compact_and_normalization b hc hn (derivative_normalization hp b)
    (fun _ _ hu hf => finiteZeroSpace_of_satisfies hu hf)

/-- Both constraints are closed for uniform convergence. -/
theorem satisfies_isClosed (b : Constraint) :
    IsClosed {f : C(Segment, 𝕜) | Satisfies b f} := by
  cases b with
  | zeroTrace =>
    have h0 : Continuous (fun f : C(Segment, 𝕜) => extension f 0) := by
      simpa [extension, projIcc_left] using
        (show Continuous (fun f : C(Segment, 𝕜) => f 0) from by fun_prop)
    have h1 : Continuous (fun f : C(Segment, 𝕜) => extension f 1) := by
      simpa [extension, projIcc_right] using
        (show Continuous (fun f : C(Segment, 𝕜) => f 1) from by fun_prop)
    exact (isClosed_eq h0 continuous_const).inter (isClosed_eq h1 continuous_const)
  | meanZero =>
    have hc := (MeasureTheory.continuous_integral (μ := intervalMeasure)
      (G := 𝕜)).comp (inclusion (𝕜 := 𝕜) 1).continuous
    have hi (f : C(Segment, 𝕜)) :
        (∫ x, inclusion 1 f x ∂intervalMeasure) = ExpandedFA.PartIV.IntervalL1.mean (extension f) := by
      calc
        _ = ∫ x, extension f x ∂intervalMeasure := integral_congr_ae
          (BoundedContinuousFunction.coeFn_toLp 1 intervalMeasure 𝕜 (extensionCLM f))
        _ = _ := by
          unfold ExpandedFA.PartIV.IntervalL1.mean
          rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
            integral_Ioc_eq_integral_Ioo]
    change Continuous (fun f : C(Segment, 𝕜) => ∫ x, inclusion 1 f x ∂intervalMeasure) at hc
    have hm : Continuous (fun f : C(Segment, 𝕜) => ExpandedFA.PartIV.IntervalL1.mean (extension f)) :=
      hc.congr hi
    exact isClosed_eq hm continuous_const

/-- A Lipschitz function on the compact segment is in every required Sobolev
space. The integration-by-parts bridge uses the actual distributional graph. -/
theorem realizes_of_lipschitz {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : C(Segment, 𝕜))
    {K : ℝ≥0} (hf : LipschitzWith K f) : ∃ u : IntervalW1p 𝕜 p, Realizes u f := by
  let F := extension f
  have hF : LipschitzWith K F := by
    intro x y
    simpa only [mul_one, F, extension, Function.comp_def] using
      (hf.comp (LipschitzWith.projIcc (by norm_num : (0 : ℝ) ≤ 1))) x y
  have hfm : MemLp F p intervalMeasure :=
    MemLp.of_bound hF.continuous.aestronglyMeasurable ‖f‖
      (Eventually.of_forall fun x => f.norm_coe_le_norm _)
  have hgm : MemLp (deriv F) p intervalMeasure :=
    MemLp.of_bound (aestronglyMeasurable_deriv F _) K
      (Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hF)
  let hvm := hfm.comp_measurePreserving
    (coordinate_measurePreserving ExpandedFA.PartIV.IntervalL1.unitInterval)
  let hwm := hgm.comp_measurePreserving
    (coordinate_measurePreserving ExpandedFA.PartIV.IntervalL1.unitInterval)
  let v := hvm.toLp (fun z : ExpandedFA.Distributions.Domain 1 => F (z 0))
  let w := hwm.toLp (fun z : ExpandedFA.Distributions.Domain 1 => deriv F (z 0))
  have hv : Represents v F := hvm.coeFn_toLp
  have hw : w =ᵐ[volume.restrict (lineDomain ExpandedFA.PartIV.IntervalL1.unitInterval :
      Set (ExpandedFA.Distributions.Domain 1))] (fun z => deriv F (z 0)) := hwm.coeFn_toLp
  have hd : ExpandedFA.Sobolev.lpDistribution w =
      -(ExpandedFA.Sobolev.lpDistribution v).comp
        (ExpandedFA.Distributions.testPartialCLM [0]) := by
    ext φ
    simp only [ExpandedFA.Sobolev.lpDistribution_apply, neg_apply, ContinuousLinearMap.comp_apply]
    change (∫ z, φ z * w z ∂volume.restrict (lineDomain ExpandedFA.PartIV.IntervalL1.unitInterval :
        Set (ExpandedFA.Distributions.Domain 1))) =
      -(∫ z, ExpandedFA.Distributions.testPartialCLM [0] φ z * v z
        ∂volume.restrict (lineDomain ExpandedFA.PartIV.IntervalL1.unitInterval :
          Set (ExpandedFA.Distributions.Domain 1)))
    calc
      _ = ∫ z, φ z * deriv F (z 0) ∂volume.restrict
          (lineDomain ExpandedFA.PartIV.IntervalL1.unitInterval :
            Set (ExpandedFA.Distributions.Domain 1)) :=
        integral_congr_ae (hw.mono fun _ h => by rw [h])
      _ = _ := by
        rw [integral_test_mul_deriv_lipschitzOn hF.lipschitzOnWith]
        congr 1
        exact integral_congr_ae (hv.symm.mono fun z h => congrArg
          (fun c => ExpandedFA.Distributions.testPartialCLM [0] φ z * c) h)
  refine ⟨ofWeakDerivative v w hd, realizes_of_represents _ f ?_⟩
  simpa only [ofWeakDerivative_base] using hv

/-- The infinity derivative ball is precisely the constrained 1-Lipschitz
ball. No reflexivity or weak compactness of L∞ is asserted or used. -/
theorem mem_derivativeBall_top_iff (b : Constraint) (f : C(Segment, 𝕜)) :
    f ∈ derivativeBall 𝕜 ∞ b ↔ Satisfies b f ∧ LipschitzWith 1 f := by
  constructor
  · rintro ⟨hb, u, hu, hdu⟩
    refine ⟨hb, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    have hl := lipschitz_bound 𝕜 _ ordConnected_Ioo u (extension f) hu
    have hx : (x : ℝ) ∈ closure (ExpandedFA.PartIV.IntervalL1.unitInterval : Set ℝ) := by
      simpa [ExpandedFA.PartIV.IntervalL1.unitInterval, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] using x.property
    have hy : (y : ℝ) ∈ closure (ExpandedFA.PartIV.IntervalL1.unitInterval : Set ℝ) := by
      simpa [ExpandedFA.PartIV.IntervalL1.unitInterval, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] using y.property
    simpa only [extension_apply, NNReal.coe_one, one_mul, Subtype.dist_eq] using
      (hl.dist_le_mul x hx y hy).trans
        (mul_le_mul_of_nonneg_right hdu (dist_nonneg : 0 ≤ dist (x : ℝ) (y : ℝ)))
  · rintro ⟨hb, hl⟩
    obtain ⟨u, hu⟩ := realizes_of_lipschitz (p := ∞) f hl
    refine ⟨hb, u, hu, ?_⟩
    apply optimal_lipschitz_constant 𝕜 _ ordConnected_Ioo u (extension f) 1 hu.2.1
    have he : LipschitzWith 1 (extension f) := by
      intro x y
      simpa only [mul_one, extension, Function.comp_def] using
        (hl.comp (LipschitzWith.projIcc (by norm_num : (0 : ℝ) ≤ 1))) x y
    exact he.lipschitzOnWith

theorem derivativeBall_top_isClosed (b : Constraint) :
    IsClosed (derivativeBall 𝕜 ∞ b) := by
  have hc : Continuous (fun f : C(Segment, 𝕜) => (f : Segment → 𝕜)) := by fun_prop
  have hl := (isClosed_setOfPred_lipschitzWith (α := Segment) (β := 𝕜) 1).preimage hc
  have he : derivativeBall 𝕜 ∞ b =
      {f : C(Segment, 𝕜) | Satisfies b f} ∩ {f | LipschitzWith 1 f} := by
    ext f
    exact mem_derivativeBall_top_iff b f
  rw [he]
  exact (satisfies_isClosed b).inter hl

theorem derivativeBall_top_isCompact (b : Constraint) :
    IsCompact (derivativeBall 𝕜 ∞ b) := by
  simpa only [(derivativeBall_top_isClosed (𝕜 := 𝕜) b).closure_eq] using
    derivativeBall_compact_closure (𝕜 := 𝕜) (p := ∞) (by simp) b

/-- Nonzero Lipschitz test functions exist in each constraint class over
both scalar fields. Centering the coordinate function avoids an implicit
real-valued intermediate-value argument for the complex mean-zero case. -/
theorem exists_nonzero_lipschitz (b : Constraint) :
    ∃ f : C(Segment, 𝕜), Satisfies b f ∧ f ≠ 0 ∧ LipschitzWith 1 f := by
  have hcoe : LipschitzWith 1 (fun x : Segment => (x : ℝ)) :=
    LipschitzWith.of_dist_le_mul (by intro x y; simp [Subtype.dist_eq])
  cases b with
  | zeroTrace =>
    let f : C(Segment, 𝕜) :=
      ⟨fun x => (ExpandedFA.PartIV.IntervalL1.triangularTent x : 𝕜),
        RCLike.continuous_ofReal.comp
          (ExpandedFA.PartIV.IntervalL1.triangularTent_lipschitz.continuous.comp continuous_subtype_val)⟩
    have hl : LipschitzWith 1 f := by
      simpa only [f, mul_one, Function.comp_def, ContinuousMap.coe_mk] using (RCLike.lipschitzWith_ofReal (K := 𝕜)).comp
        (ExpandedFA.PartIV.IntervalL1.triangularTent_lipschitz.comp hcoe)
    refine ⟨f, ?_, ?_, hl⟩
    · constructor <;> norm_num [extension, projIcc_left, projIcc_right, f,
        ExpandedFA.PartIV.IntervalL1.triangularTent]
    · intro hf
      have hv := congrArg (fun g : C(Segment, 𝕜) => g ⟨1 / 2, by norm_num⟩) hf
      norm_num [f, ExpandedFA.PartIV.IntervalL1.triangularTent] at hv
  | meanZero =>
    let a : C(Segment, 𝕜) := ⟨fun x => ((x : ℝ) : 𝕜), by fun_prop⟩
    let m := ExpandedFA.PartIV.IntervalL1.mean (extension a)
    let f : C(Segment, 𝕜) := a - ContinuousMap.const Segment m
    have ha : LipschitzWith 1 a := by
      simpa only [a, mul_one, Function.comp_def, ContinuousMap.coe_mk] using (RCLike.lipschitzWith_ofReal (K := 𝕜)).comp hcoe
    have hl : LipschitzWith 1 f := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa [f, dist_eq_norm, sub_sub_sub_cancel_right] using ha.dist_le_mul x y
    refine ⟨f, ?_, ?_, hl⟩
    · change (∫ x in (0 : ℝ)..1, extension a x - m) = 0
      rw [intervalIntegral.integral_sub ((extension_continuous a).intervalIntegrable 0 1)
        intervalIntegrable_const]
      simp [m, ExpandedFA.PartIV.IntervalL1.mean]
    · intro hf
      have h0 := congrArg (fun g : C(Segment, 𝕜) => g 0) hf
      have h1 := congrArg (fun g : C(Segment, 𝕜) => g 1) hf
      have hm : m = 0 := by simpa [f, a] using h0.symm
      simpa [f, a, hm] using h1

/-- Each derivative ball contains a function of strictly positive Lq norm. -/
theorem derivativeBall_positive {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : 1 < p) (b : Constraint) : ∃ f ∈ derivativeBall 𝕜 p b, 0 < normQ q f := by
  obtain ⟨f, hb, hf, hl⟩ := exists_nonzero_lipschitz (𝕜 := 𝕜) b
  obtain ⟨u, hu⟩ := realizes_of_lipschitz (p := p) f hl
  obtain ⟨g, hg, hfg⟩ := derivative_normalization (q := q) hp b u f hu hb
  refine ⟨g, hg, ?_⟩
  have hpq : 0 < normQ q f := (normQ_pos_iff q f).mpr hf
  have hprod : 0 < normQ q g * ‖derivativeLp u‖ := hpq.trans_le hfg
  exact (mul_pos_iff.mp hprod).elim (fun h => h.1)
    (fun h => False.elim ((normQ_nonneg q g).not_gt h.1))

/-- Complete attainment at p=∞, uniformly for every finite or infinite q. -/
theorem extremizers_top (q : ℝ≥0∞) [Fact (1 ≤ q)] (b : Constraint) : Attained 𝕜 ∞ q b :=
  attained_of_compact (by simp) b (derivativeBall_top_isCompact b)
    (derivativeBall_positive (by simp) b)

open ExpandedFA.Sobolev ExpandedFA.Distributions ExpandedFA.FunctionSpaces

abbrev intervalDomain := lineDomain ExpandedFA.PartIV.IntervalL1.unitInterval
abbrev domainMeasure : Measure (Domain 1) := volume.restrict (intervalDomain : Set (Domain 1))

def domainInclusion (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    C(Segment, 𝕜) →L[𝕜] DomainLp 𝕜 intervalDomain p :=
  (Lp.compMeasurePreservingₗᵢ 𝕜 (fun z : Domain 1 => z 0)
    (coordinate_measurePreserving ExpandedFA.PartIV.IntervalL1.unitInterval)).toContinuousLinearMap.comp
    (inclusion p)

theorem domainInclusion_represents (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : C(Segment, 𝕜)) :
    Represents (domainInclusion p f) (extension f) := by
  apply (Lp.coeFn_compMeasurePreserving (inclusion p f)
    (coordinate_measurePreserving ExpandedFA.PartIV.IntervalL1.unitInterval)).trans
  exact (coordinate_measurePreserving ExpandedFA.PartIV.IntervalL1.unitInterval).quasiMeasurePreserving.ae_eq_comp
    (BoundedContinuousFunction.coeFn_toLp p intervalMeasure 𝕜 (extensionCLM f))

theorem domainInclusion_eq_base {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {u : IntervalW1p 𝕜 p} {f : C(Segment, 𝕜)} (hu : Realizes u f) :
    domainInclusion p f = baseLp u := by
  apply Lp.ext
  exact (domainInclusion_represents p f).trans hu.2.1.symm

theorem pairing_test {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    [ENNReal.HolderConjugate r p]
    (g : DomainLp 𝕜 intervalDomain p) (φ : Tests 𝕜 intervalDomain) :
    ScalarLpIntegralPairingSpec.IntegralPairingValue domainMeasure r p g (testToDomainLp (p := r) φ) =
      lpDistribution g φ := by
  rw [(lp_pairing_integral domainMeasure r p g _).2, lpDistribution_apply]
  exact integral_congr_ae ((testToDomainLp_coe (p := r) φ).mono fun z h => by dsimp only; rw [h])

def testBaseIntegral (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    [ENNReal.HolderConjugate p r] (φ : Tests 𝕜 intervalDomain) :
    C(Segment, 𝕜) →L[𝕜] 𝕜 :=
  (ScalarLpIntegralPairingSpec.IntegralPairingValue domainMeasure p r (testToDomainLp (p := r) φ)).comp
    (domainInclusion p)

theorem testBaseIntegral_eq {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    [ENNReal.HolderConjugate p r] (φ : Tests 𝕜 intervalDomain) (f : C(Segment, 𝕜)) :
    testBaseIntegral p r φ f = lpDistribution (domainInclusion p f) φ := by
  rw [testBaseIntegral, ContinuousLinearMap.comp_apply,
    (lp_pairing_integral domainMeasure p r _ _).2, lpDistribution_apply]
  apply integral_congr_ae
  filter_upwards [testToDomainLp_coe (p := r) φ] with z hz
  rw [hz, mul_comm]


/-- Encode the weak derivative by a norm-bounded functional on the conjugate
Lp space. The identities retain the original distributional derivative graph. -/
theorem derivativeBall_eq_weakDual_lift
    {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    [ENNReal.HolderConjugate p r] [ENNReal.HolderConjugate r p]
    (hr : r ≠ ∞) (b : Constraint) :
    derivativeBall 𝕜 p b = {f : C(Segment, 𝕜) | Satisfies b f} ∩
      {f | ∃ L : WeakDual 𝕜 (DomainLp 𝕜 intervalDomain r),
        ‖L.toStrongDual‖ ≤ 1 ∧
        ∀ φ : Tests 𝕜 intervalDomain, L (testToDomainLp (p := r) φ) =
          -testBaseIntegral p r (testPartialCLM [0] φ) f} := by
  ext f
  constructor
  · rintro ⟨hb, u, hu, hdu⟩
    refine ⟨hb, StrongDual.toWeakDual (ScalarLpIntegralPairingSpec.IntegralPairingValue domainMeasure r p (derivativeLp u)),
      (lp_pairing_norm_bound domainMeasure r p (derivativeLp u)).trans hdu, ?_⟩
    intro φ
    change ScalarLpIntegralPairingSpec.IntegralPairingValue domainMeasure r p (derivativeLp u)
      (testToDomainLp (p := r) φ) = _
    rw [pairing_test, testBaseIntegral_eq, domainInclusion_eq_base hu]
    have hd := u.property firstIndex
    change lpDistribution (derivativeLp u) =
      distributionDerivative 𝕜 1 intervalDomain
        (multiIndexWord (natIndex firstIndex)) (lpDistribution (baseLp u)) at hd
    rw [multiIndexWord_firstIndex, distributionDerivative_cons, distributionDerivative_nil] at hd
    exact congrArg (fun T => T φ) hd
  · rintro ⟨hb, L, hL, htest⟩
    obtain ⟨g, hg, _⟩ := lp_duality_sigmaFinite domainMeasure r p hr L.toStrongDual
    have heq (φ : Tests 𝕜 intervalDomain) :
        lpDistribution g φ = L (testToDomainLp (p := r) φ) := by
      rw [← pairing_test (r := r) g φ,
        (lp_pairing_integral domainMeasure r p g _).2]
      exact (hg.1 _).2.symm
    have hd : lpDistribution g =
        -(lpDistribution (domainInclusion p f)).comp (testPartialCLM [0]) := by
      ext φ
      simp only [neg_apply, ContinuousLinearMap.comp_apply]
      rw [heq, htest, testBaseIntegral_eq]
    let u := ofWeakDerivative (domainInclusion p f) g hd
    refine ⟨hb, u, realizes_of_represents u f ?_, ?_⟩
    · simpa only [u, ofWeakDerivative_base] using domainInclusion_represents p f
    · simpa only [u, ofWeakDerivative_derivative, hg.2] using hL

/-- A compact weak-star unit ball makes any family of continuous test
equations closed after eliminating the dual-functional variable. -/
theorem isClosed_exists_weakDual_unitBall
    {𝕜 E X ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [TopologicalSpace X]
    (v : ι → E) (rhs : ι → X → 𝕜) (hrhs : ∀ i, Continuous (rhs i)) :
    IsClosed {x : X | ∃ L : WeakDual 𝕜 E,
      ‖L.toStrongDual‖ ≤ 1 ∧ ∀ i, L (v i) = rhs i x} := by
  let B : Set (WeakDual 𝕜 E) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual 𝕜 E) 1
  have hB : IsCompact B := WeakDual.isCompact_closedBall 0 1
  let : CompactSpace B := isCompact_iff_compactSpace.mp hB
  have hclosed : IsClosed {a : X × B | ∀ i, a.2.val (v i) = rhs i a.1} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro i
    exact isClosed_eq
      ((WeakDual.eval_continuous (v i)).comp (continuous_subtype_val.comp continuous_snd))
      ((hrhs i).comp continuous_fst)
  have hi := isClosedMap_fst_of_compactSpace _ hclosed
  convert hi using 1
  ext x
  constructor
  · rintro ⟨L, hL, heq⟩
    refine ⟨(x, ⟨L, ?_⟩), heq, rfl⟩
    simpa only [B, mem_preimage, Metric.mem_closedBall, dist_zero_right] using hL
  · rintro ⟨⟨y, L⟩, heq, rfl⟩
    refine ⟨L.val, ?_, heq⟩
    simpa only [B, mem_preimage, Metric.mem_closedBall, dist_zero_right] using L.property

/-- Banach–Alaoglu and scalar Lp duality preserve the derivative unit bound
under uniform limits for every p>1. The predual exponent is finite even when
p=∞; no reflexivity assumption occurs. -/
theorem derivativeBall_isClosed {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p) (b : Constraint) :
    IsClosed (derivativeBall 𝕜 p b) := by
  let r := (1 - p⁻¹)⁻¹
  have hp1 : p⁻¹ ≤ 1 := by simpa using ENNReal.inv_le_one.mpr hp.le
  have hc : ENNReal.HolderConjugate r p := by
    apply ENNReal.holderConjugate_iff.mpr
    simp only [r, inv_inv]
    exact tsub_add_cancel_of_le hp1
  let := hc
  let : ENNReal.HolderConjugate p r := hc.symm
  let : Fact (1 ≤ r) := ⟨ENNReal.HolderConjugate.one_le r p⟩
  have hr : r ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one r p).mpr hp.ne'
  rw [derivativeBall_eq_weakDual_lift (r := r) hr b]
  apply (satisfies_isClosed b).inter
  exact isClosed_exists_weakDual_unitBall (testToDomainLp (p := r))
    (fun φ f => -testBaseIntegral p r (testPartialCLM [0] φ) f)
    (fun φ => (testBaseIntegral p r (testPartialCLM [0] φ)).continuous.neg)


/-- Reduction of the full assigned result to finite-p closedness alone.
Relative compactness, all endpoint cases, nontriviality, normalization,
optimality and finite-p closure-defined zero trace are already proved above. -/
theorem extremizers_of_finite_closed
    (hclosed : ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)],
      1 < p → p ≠ ∞ → ∀ b : Constraint, IsClosed (derivativeBall 𝕜 p b)) :
    Specs.ExpandedFA.PartIV.IntervalExtremizers.Extremizers := by
  intro 𝕜 _ p _ hp q _ b
  by_cases ht : p = ∞
  · subst p
    exact extremizers_top q b
  · apply attained_of_compact hp b _ (derivativeBall_positive hp b)
    simpa only [(hclosed 𝕜 p hp ht b).closure_eq] using derivativeBall_compact_closure
      (𝕜 := 𝕜) hp b

/-- Independently completed endpoint part of the source assertion. -/
theorem top_extremizers : Specs.ExpandedFA.PartIV.IntervalExtremizers.TopExtremizers := by
  intro 𝕜 _ q _ b
  exact extremizers_top q b

/-- Full attainment for both constraints, both scalar fields, and all the
finite and infinite exponents in the source. -/
theorem extremizers : Specs.ExpandedFA.PartIV.IntervalExtremizers.Extremizers := by
  apply extremizers_of_finite_closed
  intro 𝕜 _ p _ hp _ b
  exact derivativeBall_isClosed hp b

end ExpandedFA.PartIV.IntervalExtremizers
