import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.IntervalL2Constants
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.IntervalL1Constants
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Fourier.AddCircle

noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
open ExpandedFA.Sobolev.OneDimensional
open ExpandedFA.PartIV.IntervalL1 (mean)

namespace ExpandedFA.PartIV.IntervalL2
variable {𝕜 : Type} [RCLike 𝕜]

lemma representative_continuous {u : H1 𝕜} {f : ℝ → 𝕜}
    (hf : PrimitiveRepresentative u f) : ContinuousOn f (Icc (0 : ℝ) 1) := by
  have hc : closure (ExpandedFA.PartIV.IntervalL1.unitInterval : Set ℝ) = Icc (0 : ℝ) 1 :=
    closure_Ioo (by norm_num)
  exact hc ▸ hf.1

lemma representative_memLp {u : H1 𝕜} {f : ℝ → 𝕜}
    (hf : PrimitiveRepresentative u f) :
    MemLp f 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
  (lineFunction_memLp (baseLp u)).ae_eq
    (represents_lineFunction_ae (baseLp u) hf.2.1)

lemma representative_l2Norm {u : H1 𝕜} {f : ℝ → 𝕜}
    (hf : PrimitiveRepresentative u f) : l2Norm f = ‖baseLp u‖ := by
  change (eLpNorm f 2 (volume.restrict (ExpandedFA.PartIV.IntervalL1.unitInterval : Set ℝ))).toReal = _
  rw [← eLpNorm_congr_ae (represents_lineFunction_ae (baseLp u) hf.2.1)]
  exact lineFunction_norm _

lemma derivative_l2Norm (u : H1 𝕜) :
    l2Norm (lineFunction (derivativeLp u)) = ‖derivativeLp u‖ :=
  lineFunction_norm _

lemma l2Norm_sq {f : ℝ → 𝕜}
    (hf : MemLp f 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) = l2Norm f ^ 2 := by
  let F := hf.toLp f
  have he : (∫ x, ‖F x‖ ^ 2 ∂volume.restrict (Ioo (0 : ℝ) 1)) =
      ∫ x, ‖f x‖ ^ 2 ∂volume.restrict (Ioo (0 : ℝ) 1) :=
    integral_congr_ae (hf.coeFn_toLp.mono (fun _ h => by exact congrArg (fun a : 𝕜 => ‖a‖ ^ 2) h))
  have hn : ‖F‖ ^ 2 = ∫ x, ‖F x‖ ^ 2 ∂volume.restrict (Ioo (0 : ℝ) 1) := by
    rw [← @inner_self_eq_norm_sq ℝ]
    rw [L2.inner_def]
    simp
  rw [he, Lp.norm_toLp] at hn
  simpa [l2Norm, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo] using hn.symm

theorem norm_identification :
    Specs.ExpandedFA.PartIV.IntervalL2Constants.NormIdentification := by
  intro 𝕜 _ u f hf
  exact ⟨representative_l2Norm hf, derivative_l2Norm u, l2Norm_sq (representative_memLp hf)⟩

theorem zero_trace_identification :
    Specs.ExpandedFA.PartIV.IntervalL2Constants.ZeroTraceIdentification := by
  intro 𝕜 _ u f hf
  exact ExpandedFA.Sobolev.Trace.interval_zeroSpace_iff_endpoints
    (by norm_num) (by norm_num) u f hf

/-- The primitive representative is AC up to both endpoints, not only
on compact subintervals of the interior. -/
lemma representative_absolutelyContinuous {u : H1 𝕜} {f : ℝ → 𝕜}
    (hf : PrimitiveRepresentative u f) : AbsolutelyContinuousOnInterval f 0 1 := by
  have hc : closure (ExpandedFA.PartIV.IntervalL1.unitInterval : Set ℝ) = Icc (0 : ℝ) 1 :=
    closure_Ioo (by norm_num)
  have h0 : (0 : ℝ) ∈ closure (ExpandedFA.PartIV.IntervalL1.unitInterval : Set ℝ) := by
    rw [hc]; norm_num
  have he : EqOn (fun x => canonicalPrimitive (derivativeLp u) x + f 0) f (Icc 0 1) := by
    intro x hx
    have hp := canonicalPrimitive_sub_eq ordConnected_Ioo (derivativeLp u) (hc.symm ▸ hx) h0
    have hz : canonicalPrimitive (derivativeLp u) 0 = 0 := by simp [canonicalPrimitive]
    rw [hz, sub_zero] at hp
    have h := (hf.2.2.2 x (hc.symm ▸ hx) 0 h0).2
    rw [← hp] at h
    exact (sub_eq_iff_eq_add.mp h).symm
  have hp : AbsolutelyContinuousOnInterval (canonicalPrimitive (derivativeLp u)) 0 1 :=
    integral_primitive_absolutelyContinuous
      (fun a b => (extendedLineFunction_locallyIntegrable (derivativeLp u)).integrableOn_isCompact
        isCompact_uIcc |>.intervalIntegrable) 0 1 0
  have hp' : AbsolutelyContinuousOnInterval
      (fun x => canonicalPrimitive (derivativeLp u) x + f 0) 0 1 := by
    convert! hp.add ((LipschitzWith.const (f 0)).lipschitzOnWith.absolutelyContinuousOnInterval) using 1
  exact hp'.congr (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using he)

/-- The classical a.e. derivative is the actual density from the H¹ graph. -/
lemma representative_ae_hasDerivAt {u : H1 𝕜} {f : ℝ → 𝕜}
    (hf : PrimitiveRepresentative u f) :
    ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1),
      HasDerivAt f (lineFunction (derivativeLp u) x) x := by
  have hc : closure (ExpandedFA.PartIV.IntervalL1.unitInterval : Set ℝ) = Icc (0 : ℝ) 1 :=
    closure_Ioo (by norm_num)
  have h0 : (0 : ℝ) ∈ closure (ExpandedFA.PartIV.IntervalL1.unitInterval : Set ℝ) := by
    rw [hc]; norm_num
  have he : ∀ y ∈ Ioo (0 : ℝ) 1,
      f y = canonicalPrimitive (derivativeLp u) y + f 0 := by
    intro y hy
    have hp := canonicalPrimitive_sub_eq ordConnected_Ioo (derivativeLp u) (subset_closure hy) h0
    have hz : canonicalPrimitive (derivativeLp u) 0 = 0 := by simp [canonicalPrimitive]
    rw [hz, sub_zero] at hp
    have h := (hf.2.2.2 y (subset_closure hy) 0 h0).2
    rw [← hp] at h
    exact sub_eq_iff_eq_add.mp h
  have hd := canonicalPrimitive_ae_hasDerivAt (derivativeLp u)
  change ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1), _ at hd
  filter_upwards [hd, ae_restrict_mem measurableSet_Ioo] with x hx hxi
  apply (hx.add_const (f 0)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hxi] with y hy
  exact he y hy

/-- FTC with an interval-integrable specified derivative. In particular this
works for complex AC functions; differentiability everywhere is not needed. -/
lemma integral_eq_sub_of_ac {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f g : ℝ → E} {a b : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : IntervalIntegrable g volume a b)
    (hd : ∀ᵐ x ∂volume, x ∈ Icc a b → HasDerivAt f (g x) x) :
    (∫ x in a..b, g x) = f b - f a := by
  let G := (Icc a b).indicator g
  have hGi : Integrable G volume := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hg
  have hD : ∀ᵐ x ∂volume, x ∈ uIcc a b → HasDerivAt f (G x) x := by
    filter_upwards [hd] with x hx hxi
    have hxi' : x ∈ Icc a b := by simpa only [uIcc_of_le hab] using hxi
    simpa only [G, indicator_of_mem hxi'] using hx hxi'
  rw [← integral_eq_sub_of_absolutelyContinuous_of_ae_hasDerivAt hf hGi.locallyIntegrable hD]
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [uIcc_of_le hab] at hx
  exact (indicator_of_mem hx g).symm

/-- Integration by parts for AC scalar functions with their specified a.e.
derivatives. The assumptions are exactly AC and L¹, including complex scalars. -/
lemma integral_mul_eq_boundary_sub {f g f' g' : ℝ → 𝕜} {a b : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hfi : IntervalIntegrable f' volume a b) (hgi : IntervalIntegrable g' volume a b)
    (hfd : ∀ᵐ x ∂volume, x ∈ Icc a b → HasDerivAt f (f' x) x)
    (hgd : ∀ᵐ x ∂volume, x ∈ Icc a b → HasDerivAt g (g' x) x) :
    (∫ x in a..b, f x * g' x) = f b * g b - f a * g a -
      ∫ x in a..b, f' x * g x := by
  have h₁ := hfi.mul_continuousOn hg.continuousOn
  have h₂ := hgi.continuousOn_mul hf.continuousOn
  have hp : AbsolutelyContinuousOnInterval (fun x => f x * g x) a b := by
    convert! hf.smul hg using 1
  have hd : ∀ᵐ x ∂volume, x ∈ Icc a b →
      HasDerivAt (fun x => f x * g x) (f' x * g x + f x * g' x) x := by
    filter_upwards [hfd, hgd] with x hx hy hxi
    exact (hx hxi).mul (hy hxi)
  have he := integral_eq_sub_of_ac hab hp (h₁.add h₂) hd
  rw [intervalIntegral.integral_add h₁ h₂] at he
  exact eq_sub_of_add_eq' he

/-- Promote an existing weak W¹,¹ graph when both entries have L²
representatives. The distributional derivative is inherited, not assumed. -/
lemma promote_to_H1 (u : ExpandedFA.PartIV.IntervalL1.W11 𝕜) (f : ℝ → 𝕜)
    (hf : PrimitiveRepresentative u f)
    (hfm : MemLp f 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hgm : MemLp (lineFunction (derivativeLp u)) 2
      (volume.restrict (Ioo (0 : ℝ) 1))) :
    ∃ v : H1 𝕜, PrimitiveRepresentative v f ∧
      lineFunction (derivativeLp v) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
        lineFunction (derivativeLp u) := by
  let hv := hfm.comp_measurePreserving (coordinate_measurePreserving ExpandedFA.PartIV.IntervalL1.unitInterval)
  let hg := hgm.comp_measurePreserving (coordinate_measurePreserving ExpandedFA.PartIV.IntervalL1.unitInterval)
  let v := hv.toLp (fun z : ExpandedFA.Distributions.Domain 1 => f (z 0))
  let g := hg.toLp (fun z : ExpandedFA.Distributions.Domain 1 =>
    lineFunction (derivativeLp u) (z 0))
  have hvf : Represents v f := hv.coeFn_toLp
  have hge := hg.coeFn_toLp
  have hue := represents_of_lineFunction_ae (derivativeLp u)
    (Filter.EventuallyEq.rfl : lineFunction (derivativeLp u) =ᵐ[
      volume.restrict (ExpandedFA.PartIV.IntervalL1.unitInterval : Set ℝ)] lineFunction (derivativeLp u))
  have heq {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
      (v : ExpandedFA.Sobolev.DomainLp 𝕜 (lineDomain ExpandedFA.PartIV.IntervalL1.unitInterval) p)
      (w : ExpandedFA.Sobolev.DomainLp 𝕜 (lineDomain ExpandedFA.PartIV.IntervalL1.unitInterval) q)
      (h : v =ᵐ[volume.restrict (lineDomain ExpandedFA.PartIV.IntervalL1.unitInterval :
        Set (ExpandedFA.Distributions.Domain 1))] w) :
      ExpandedFA.Sobolev.lpDistribution v = ExpandedFA.Sobolev.lpDistribution w := by
    ext φ
    simp only [ExpandedFA.Sobolev.lpDistribution_apply]
    apply integral_congr_ae
    exact h.mono (fun z hz => congrArg (fun a => φ z * a) hz)
  have hbase := heq v (baseLp u) (hvf.trans hf.2.1.symm)
  have hder := heq g (derivativeLp u) (hge.trans hue.symm)
  have hd : ExpandedFA.Sobolev.lpDistribution g =
      -(ExpandedFA.Sobolev.lpDistribution v).comp
        (ExpandedFA.Distributions.testPartialCLM [0]) := by
    rw [hbase, hder]
    have h := u.property ExpandedFA.Sobolev.OneDimensional.firstIndex
    change ExpandedFA.Sobolev.lpDistribution (derivativeLp u) =
      ExpandedFA.Distributions.distributionDerivative 𝕜 1
        (lineDomain ExpandedFA.PartIV.IntervalL1.unitInterval)
        (ExpandedFA.Distributions.multiIndexWord
          (ExpandedFA.Sobolev.natIndex firstIndex))
        (ExpandedFA.Sobolev.lpDistribution (baseLp u)) at h
    simpa only [multiIndexWord_firstIndex,
      ExpandedFA.Distributions.distributionDerivative_cons,
      ExpandedFA.Distributions.distributionDerivative_nil] using h
  let w : H1 𝕜 := ofWeakDerivative v g hd
  have hwb : baseLp w = v := ofWeakDerivative_base _ _ _
  have hwd : derivativeLp w = g := ofWeakDerivative_derivative _ _ _
  obtain ⟨F, hF⟩ := representative_existence 𝕜 ExpandedFA.PartIV.IntervalL1.unitInterval ordConnected_Ioo 2 w
  have hsame := representative_uniqueness 𝕜 ExpandedFA.PartIV.IntervalL1.unitInterval 2 v F f
    hF.1 hf.1 (hwb ▸ hF.2.1) hvf
  refine ⟨w, ⟨hf.1, hwb.symm ▸ hvf, hf.2.2.1, ?_⟩, ?_⟩
  · intro x hx y hy
    rw [← hsame hx, ← hsame hy]
    exact hF.2.2.2 x hx y hy
  · rw [hwd]
    exact (linePoint_measurePreserving ExpandedFA.PartIV.IntervalL1.unitInterval).quasiMeasurePreserving.ae hge

/-- Bounded-interval Lipschitz functions belong to the original H¹ graph,
with their classical a.e. derivative. This uses the accepted W¹,¹ construction. -/
lemma lipschitz_realization {f : ℝ → 𝕜} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∃ u : H1 𝕜, PrimitiveRepresentative u f ∧
      lineFunction (derivativeLp u) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] deriv f := by
  obtain ⟨v, hv, hdv⟩ := ExpandedFA.PartIV.IntervalL1.lipschitz_realization hf
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image
    (hf.continuous.continuousOn : ContinuousOn f (Icc (0 : ℝ) 1)).norm
  have hfm : MemLp f 2 (volume.restrict (Ioo (0 : ℝ) 1)) := by
    apply MemLp.of_bound hf.continuous.aestronglyMeasurable B
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hB ⟨x, Ioo_subset_Icc_self hx, rfl⟩
  have hgm : MemLp (deriv f) 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
    MemLp.of_bound (aestronglyMeasurable_deriv f _) K
      (Filter.Eventually.of_forall (fun _ => norm_deriv_le_of_lipschitz hf))
  obtain ⟨u, hu, hdu⟩ := promote_to_H1 v f hv hfm (hgm.ae_eq hdv.symm)
  exact ⟨u, hu, hdu.trans hdv⟩

def sine (𝕜 : Type) [RCLike 𝕜] (x : ℝ) : 𝕜 := (Real.sin (Real.pi * x) : 𝕜)
def cosine (𝕜 : Type) [RCLike 𝕜] (x : ℝ) : 𝕜 := (Real.cos (Real.pi * x) : 𝕜)

lemma sine_lipschitz : ∃ K, LipschitzWith K (sine 𝕜) := by
  refine ⟨‖Real.pi‖₊, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  calc
    dist (sine 𝕜 x) (sine 𝕜 y) =
        dist (Real.sin (Real.pi * x)) (Real.sin (Real.pi * y)) := by
      simp only [sine, dist_eq_norm, ← RCLike.ofReal_sub, RCLike.norm_ofReal, Real.norm_eq_abs]
    _ ≤ dist (Real.pi * x) (Real.pi * y) := by
      simpa using Real.lipschitzWith_sin.dist_le_mul (Real.pi * x) (Real.pi * y)
    _ = _ := by simp [Real.dist_eq, ← mul_sub, abs_mul]

lemma cosine_lipschitz : ∃ K, LipschitzWith K (cosine 𝕜) := by
  refine ⟨‖Real.pi‖₊, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  calc
    dist (cosine 𝕜 x) (cosine 𝕜 y) =
        dist (Real.cos (Real.pi * x)) (Real.cos (Real.pi * y)) := by
      simp only [cosine, dist_eq_norm, ← RCLike.ofReal_sub, RCLike.norm_ofReal, Real.norm_eq_abs]
    _ ≤ dist (Real.pi * x) (Real.pi * y) := by
      simpa using Real.lipschitzWith_cos.dist_le_mul (Real.pi * x) (Real.pi * y)
    _ = _ := by simp [Real.dist_eq, ← mul_sub, abs_mul]

lemma sine_memLp : MemLp (sine 𝕜) 2 (volume.restrict (Ioo (0 : ℝ) 1)) := by
  obtain ⟨K, h⟩ := sine_lipschitz (𝕜 := 𝕜)
  apply MemLp.of_bound h.continuous.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun x => by
    simpa [sine, RCLike.norm_ofReal, Real.norm_eq_abs] using Real.abs_sin_le_one (Real.pi * x))

lemma cosine_memLp : MemLp (cosine 𝕜) 2 (volume.restrict (Ioo (0 : ℝ) 1)) := by
  obtain ⟨K, h⟩ := cosine_lipschitz (𝕜 := 𝕜)
  apply MemLp.of_bound h.continuous.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun x => by
    simpa [cosine, RCLike.norm_ofReal, Real.norm_eq_abs] using Real.abs_cos_le_one (Real.pi * x))

lemma hasDerivAt_sine (x : ℝ) :
    HasDerivAt (sine 𝕜) ((Real.pi : 𝕜) * cosine 𝕜 x) x := by
  have h := (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).hasFDerivAt.comp_hasDerivAt x
    ((Real.hasDerivAt_sin (Real.pi * x)).comp x ((hasDerivAt_id x).const_mul Real.pi))
  unfold sine cosine
  simpa [RCLike.algebraMap_eq_ofReal, mul_comm, Function.comp_def] using h

lemma hasDerivAt_cosine (x : ℝ) :
    HasDerivAt (cosine 𝕜) (-(Real.pi : 𝕜) * sine 𝕜 x) x := by
  have h := (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).hasFDerivAt.comp_hasDerivAt x
    ((Real.hasDerivAt_cos (Real.pi * x)).comp x ((hasDerivAt_id x).const_mul Real.pi))
  unfold sine cosine
  simpa [RCLike.algebraMap_eq_ofReal, mul_comm, Function.comp_def] using h

lemma sine_sq_integral : (∫ x in (0 : ℝ)..1, Real.sin (Real.pi * x) ^ 2) = 1 / 2 := by
  rw [intervalIntegral.integral_comp_mul_left (fun x : ℝ => Real.sin x ^ 2) Real.pi_ne_zero]
  simp only [integral_sin_sq, mul_zero, mul_one, Real.sin_zero, Real.sin_pi, zero_mul, sub_zero, zero_add, smul_eq_mul]
  field_simp

lemma cosine_sq_integral : (∫ x in (0 : ℝ)..1, Real.cos (Real.pi * x) ^ 2) = 1 / 2 := by
  rw [intervalIntegral.integral_comp_mul_left (fun x : ℝ => Real.cos x ^ 2) Real.pi_ne_zero]
  simp only [integral_cos_sq, mul_zero, mul_one, Real.sin_zero, Real.sin_pi, sub_zero, zero_add, smul_eq_mul]
  field_simp

lemma sine_norm_sq : l2Norm (sine 𝕜) ^ 2 = 1 / 2 := by
  rw [← l2Norm_sq sine_memLp]
  simpa [sine, RCLike.norm_ofReal, sq_abs] using sine_sq_integral

lemma cosine_norm_sq : l2Norm (cosine 𝕜) ^ 2 = 1 / 2 := by
  rw [← l2Norm_sq cosine_memLp]
  simpa [cosine, RCLike.norm_ofReal, sq_abs] using cosine_sq_integral

lemma cosine_mean : mean (cosine 𝕜) = 0 := by
  unfold cosine mean
  rw [RCLike.intervalIntegral_ofReal]
  have h : (∫ x in (0 : ℝ)..1, Real.cos (Real.pi * x)) = 0 := by
    rw [intervalIntegral.integral_comp_mul_left Real.cos Real.pi_ne_zero]
    simp [integral_cos]
  simp [h]

lemma l2Norm_nonneg (f : ℝ → 𝕜) : 0 ≤ l2Norm f := ENNReal.toReal_nonneg

lemma l2Norm_congr {f g : ℝ → 𝕜}
    (h : f =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] g) : l2Norm f = l2Norm g := by
  exact congrArg ENNReal.toReal (eLpNorm_congr_ae h)

lemma l2Norm_const_mul (c : 𝕜) (f : ℝ → 𝕜) :
    l2Norm (fun x => c * f x) = ‖c‖ * l2Norm f := by
  change (eLpNorm (c • f) 2 (volume.restrict (Ioo (0 : ℝ) 1))).toReal = _
  rw [eLpNorm_const_smul, ENNReal.toReal_mul]
  simp [l2Norm]

lemma trig_norm_eq : l2Norm (sine 𝕜) = l2Norm (cosine 𝕜) := by
  nlinarith [sine_norm_sq (𝕜 := 𝕜), cosine_norm_sq (𝕜 := 𝕜),
    l2Norm_nonneg (sine 𝕜), l2Norm_nonneg (cosine 𝕜)]

lemma trig_norm_pos : 0 < l2Norm (sine 𝕜) := by
  nlinarith [sine_norm_sq (𝕜 := 𝕜), l2Norm_nonneg (sine 𝕜)]

/-- A genuine zero-trace Sobolev optimizer, with its exact derivative norm. -/
lemma sine_witness : ∃ u : H1 𝕜, PrimitiveRepresentative u (sine 𝕜) ∧
    ZeroTrace u ∧ 0 < ‖derivativeLp u‖ ∧
    l2Norm (sine 𝕜) = Real.pi⁻¹ * ‖derivativeLp u‖ := by
  obtain ⟨K, hK⟩ := sine_lipschitz (𝕜 := 𝕜)
  obtain ⟨u, hu, hd⟩ := lipschitz_realization hK
  have hder : lineFunction (derivativeLp u) =ᵐ[
      volume.restrict (Ioo (0 : ℝ) 1)] (fun x => (Real.pi : 𝕜) * cosine 𝕜 x) :=
    hd.trans (Filter.Eventually.of_forall (fun x => (hasDerivAt_sine x).deriv))
  have hn : ‖derivativeLp u‖ = Real.pi * l2Norm (sine 𝕜) := by
    rw [← derivative_l2Norm, l2Norm_congr hder, l2Norm_const_mul,
      RCLike.norm_ofReal, abs_of_pos Real.pi_pos, ← trig_norm_eq]
  refine ⟨u, hu, ?_, ?_, ?_⟩
  · apply (zero_trace_identification 𝕜 u (sine 𝕜) hu).mpr
    simp [sine]
  · rw [hn]
    exact mul_pos Real.pi_pos trig_norm_pos
  · rw [hn, ← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero, one_mul]

/-- A genuine mean-zero Sobolev optimizer, with its exact derivative norm. -/
lemma cosine_witness : ∃ u : H1 𝕜, PrimitiveRepresentative u (cosine 𝕜) ∧
    0 < ‖derivativeLp u‖ ∧
    l2Norm (fun x => cosine 𝕜 x - mean (cosine 𝕜)) = Real.pi⁻¹ * ‖derivativeLp u‖ := by
  obtain ⟨K, hK⟩ := cosine_lipschitz (𝕜 := 𝕜)
  obtain ⟨u, hu, hd⟩ := lipschitz_realization hK
  have hder : lineFunction (derivativeLp u) =ᵐ[
      volume.restrict (Ioo (0 : ℝ) 1)] (fun x => -(Real.pi : 𝕜) * sine 𝕜 x) :=
    hd.trans (Filter.Eventually.of_forall (fun x => (hasDerivAt_cosine x).deriv))
  have hn : ‖derivativeLp u‖ = Real.pi * l2Norm (sine 𝕜) := by
    rw [← derivative_l2Norm, l2Norm_congr hder, l2Norm_const_mul, norm_neg,
      RCLike.norm_ofReal, abs_of_pos Real.pi_pos]
  refine ⟨u, hu, ?_, ?_⟩
  · rw [hn]
    exact mul_pos Real.pi_pos trig_norm_pos
  · simp only [cosine_mean, sub_zero]
    rw [hn, ← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero, one_mul, trig_norm_eq]

theorem mean_sharp : Specs.ExpandedFA.PartIV.IntervalL2Constants.MeanSharp := by
  intro 𝕜 _ C hC
  obtain ⟨u, hu, hp, he⟩ := cosine_witness (𝕜 := 𝕜)
  exact ⟨u, cosine 𝕜, hu, hp, he ▸ mul_lt_mul_of_pos_right hC hp⟩

theorem zero_sharp : Specs.ExpandedFA.PartIV.IntervalL2Constants.ZeroSharp := by
  intro 𝕜 _ C hC
  obtain ⟨u, hu, hz, hp, he⟩ := sine_witness (𝕜 := 𝕜)
  exact ⟨u, sine 𝕜, hu, hz, hp, he ▸ mul_lt_mul_of_pos_right hC hp⟩

/-- Every sine multiple, including zero, is an optimizer in the original
space; the endpoint condition follows from the representative. -/
lemma sine_optimizer_sufficient {u : H1 𝕜} {f : ℝ → 𝕜}
    (hf : PrimitiveRepresentative u f) (hopt : SineOptimizer f) :
    ZeroTrace u ∧ l2Norm f = Real.pi⁻¹ * ‖derivativeLp u‖ := by
  obtain ⟨b, hb⟩ := hopt
  obtain ⟨v, hv, _, _, he⟩ := sine_witness (𝕜 := 𝕜)
  have huv : u = b • v := by
    apply ExpandedFA.Sobolev.sobolev_underlying_injective 𝕜 1
      (lineDomain ExpandedFA.PartIV.IntervalL1.unitInterval) 1 2
    apply Lp.ext
    filter_upwards [hf.2.1, hv.2.1, Lp.coeFn_smul b (baseLp v),
      ae_restrict_mem (lineDomain ExpandedFA.PartIV.IntervalL1.unitInterval).isOpen.measurableSet]
      with z hfu hgv hsm hz
    change (baseLp u) z = (b • baseLp v) z
    simp only [hsm, hfu, Pi.smul_apply, smul_eq_mul, hgv]
    exact hb (Ioo_subset_Icc_self hz)
  have hnorm : l2Norm f = ‖b‖ * l2Norm (sine 𝕜) := by
    rw [← l2Norm_const_mul]
    apply l2Norm_congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hb (Ioo_subset_Icc_self hx)
  refine ⟨(zero_trace_identification 𝕜 u f hf).mpr ?_, ?_⟩
  · constructor
    · simpa using hb (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
    · simpa using hb (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
  · have hd : derivativeLp (b • v) = b • derivativeLp v := rfl
    rw [huv, hd, norm_smul, hnorm, he]
    ring

/-- The optimizer form is unchanged by altering values outside [0,1]. -/
lemma l2Norm_of_eqOn {f g : ℝ → 𝕜} (h : EqOn f g (Icc (0 : ℝ) 1)) :
    l2Norm f = l2Norm g := by
  apply l2Norm_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact h (Ioo_subset_Icc_self hx)

/-- Every constant plus a cosine multiple is an optimizer, for both scalar
fields and with zero coefficients allowed. -/
lemma cosine_optimizer_sufficient {u : H1 𝕜} {f : ℝ → 𝕜}
    (hf : PrimitiveRepresentative u f) (hopt : CosineOptimizer f) :
    l2Norm (fun x => f x - mean f) = Real.pi⁻¹ * ‖derivativeLp u‖ := by
  obtain ⟨a, b, hb⟩ := hopt
  obtain ⟨v, hv, _, he⟩ := cosine_witness (𝕜 := 𝕜)
  obtain ⟨w, hw, hdw⟩ := lipschitz_realization (LipschitzWith.const a)
  have hw0 : derivativeLp w = 0 := by
    apply norm_eq_zero.mp
    rw [← derivative_l2Norm, l2Norm_congr hdw]
    simp [l2Norm]
  have huv : u = w + b • v := by
    apply ExpandedFA.Sobolev.sobolev_underlying_injective 𝕜 1
      (lineDomain ExpandedFA.PartIV.IntervalL1.unitInterval) 1 2
    apply Lp.ext
    filter_upwards [hf.2.1, hw.2.1, hv.2.1,
      Lp.coeFn_add (baseLp w) (b • baseLp v), Lp.coeFn_smul b (baseLp v),
      ae_restrict_mem (lineDomain ExpandedFA.PartIV.IntervalL1.unitInterval).isOpen.measurableSet]
      with z hfu hgw hgv hadd hsm hz
    change (baseLp u) z = (baseLp w + b • baseLp v) z
    simp only [hadd, hfu, Pi.add_apply, hgw, hsm, Pi.smul_apply, smul_eq_mul, hgv]
    exact hb (Ioo_subset_Icc_self hz)
  have hm : mean f = a := by
    have heq : mean f = mean (fun x => a + b * cosine 𝕜 x) := by
      apply intervalIntegral.integral_congr
      simpa only [cosine, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hb
    have hci : IntervalIntegrable (cosine 𝕜) volume 0 1 := by
      obtain ⟨K, hK⟩ := cosine_lipschitz (𝕜 := 𝕜)
      exact hK.continuous.intervalIntegrable 0 1
    rw [heq, mean, intervalIntegral.integral_add intervalIntegrable_const (hci.const_mul b),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
    change (1 - 0 : ℝ) • a + b * mean (cosine 𝕜) = a
    simp [cosine_mean]
  have hnorm : l2Norm (fun x => f x - mean f) = ‖b‖ * l2Norm (cosine 𝕜) := by
    rw [← l2Norm_const_mul]
    apply l2Norm_of_eqOn
    intro x hx
    change f x - mean f = b * cosine 𝕜 x
    rw [hb hx, hm]
    simp only [cosine]
    ring
  have hd : derivativeLp (w + b • v) = b • derivativeLp v := by
    change derivativeLp w + b • derivativeLp v = _
    rw [hw0, zero_add]
  simp only [cosine_mean, sub_zero] at he
  rw [huv, hd, norm_smul, hnorm, he]
  ring

theorem mean_optimizer_sufficiency :
    Specs.ExpandedFA.PartIV.IntervalL2Constants.MeanOptimizerSufficiency := by
  intro 𝕜 _ u f hf ho
  exact cosine_optimizer_sufficient hf ho

theorem zero_optimizer_sufficiency :
    Specs.ExpandedFA.PartIV.IntervalL2Constants.ZeroOptimizerSufficiency := by
  intro 𝕜 _ u f hf ho
  exact sine_optimizer_sufficient hf ho

/-- The spectral comparison behind both period-two reflection proofs.
Here `a n` is the squared modulus of the normalized Fourier coefficient.
Both sums must have the same normalization. Equality leaves only ±1. -/
lemma integer_spectral_gap (a : ℤ → ℝ) (A B : ℝ)
    (ha : ∀ n, 0 ≤ a n) (ha0 : a 0 = 0) (hs : HasSum a A)
    (ht : HasSum (fun n : ℤ => Real.pi ^ 2 * (n : ℝ) ^ 2 * a n) B) :
    Real.pi ^ 2 * A ≤ B ∧
      (Real.pi ^ 2 * A = B ↔ ∀ n : ℤ, n ≠ 1 → n ≠ -1 → a n = 0) := by
  have hn (n : ℤ) : Real.pi ^ 2 * a n ≤ Real.pi ^ 2 * (n : ℝ) ^ 2 * a n := by
    by_cases h0 : n = 0
    · simp [h0, ha0]
    have h : 1 ≤ (n : ℝ) ^ 2 := by
      have hcases : n ≤ -1 ∨ 1 ≤ n := by omega
      rcases hcases with h | h
      · have h' : (n : ℝ) ≤ -1 := by exact_mod_cast h
        nlinarith
      · have h' : (1 : ℝ) ≤ n := by exact_mod_cast h
        nlinarith
    nlinarith [mul_nonneg (sq_nonneg Real.pi) (ha n),
      mul_nonneg (sq_nonneg Real.pi) (mul_nonneg (sub_nonneg.mpr h) (ha n))]
  have hsm := hs.mul_left (Real.pi ^ 2)
  refine ⟨hasSum_le hn hsm ht, ?_⟩
  constructor
  · intro he n hn1 hnm1
    have hd := ht.sub hsm
    have hd' : HasSum (fun n : ℤ =>
        Real.pi ^ 2 * (n : ℝ) ^ 2 * a n - Real.pi ^ 2 * a n) 0 := by
      simpa [← he] using hd
    have hall := (hasSum_zero_iff_of_nonneg (fun n => sub_nonneg.mpr (hn n))).mp hd'
    by_cases h0 : n = 0
    · simpa [h0] using ha0
    have h : 1 < (n : ℝ) ^ 2 := by
      have hcases : n ≤ -2 ∨ 2 ≤ n := by omega
      rcases hcases with h | h
      · have h' : (n : ℝ) ≤ -2 := by exact_mod_cast h
        nlinarith
      · have h' : (2 : ℝ) ≤ n := by exact_mod_cast h
        nlinarith
    have hpos : 0 < Real.pi ^ 2 * ((n : ℝ) ^ 2 - 1) :=
      mul_pos (sq_pos_of_pos Real.pi_pos) (sub_pos.mpr h)
    have he' := congrFun hall n
    have hz' : (Real.pi ^ 2 * ((n : ℝ) ^ 2 - 1)) * a n = 0 := by
      calc
        _ = Real.pi ^ 2 * (n : ℝ) ^ 2 * a n - Real.pi ^ 2 * a n := by ring
        _ = 0 := he'
    exact (mul_eq_zero.mp hz').resolve_left hpos.ne'
  · intro hall
    have he (n : ℤ) : Real.pi ^ 2 * a n = Real.pi ^ 2 * (n : ℝ) ^ 2 * a n := by
      by_cases hn1 : n = 1
      · simp [hn1]
      by_cases hnm1 : n = -1
      · simp [hnm1]
      simp [hall n hn1 hnm1]
    exact (hsm.congr_fun (fun n => (he n).symm)).unique ht

open AddCircle Complex intervalIntegral in
lemma fourierCoeffOn_of_ac {a b : ℝ} (hab : a < b) {f f' : ℝ → ℂ}
    {n : ℤ} (hn : n ≠ 0)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hff' : ∀ᵐ x ∂volume, x ∈ Icc a b → HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume a b) :
    fourierCoeffOn hab f n = 1 / (-2 * Real.pi * I * n) *
      (fourier (-n) (a : AddCircle (b - a)) * (f b - f a) - (b - a) * fourierCoeffOn hab f' n) := by
  rw [← ofReal_sub]
  have hT : Fact (0 < b - a) := ⟨by linarith⟩
  have hk := has_antideriv_at_fourier_neg hT hn
  have hl : LipschitzWith 1 (fun y : ℝ => ((b - a : ℝ) : ℂ) / (-2 * Real.pi * I * n) *
      fourier (-n) (y : AddCircle (b - a))) := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hk x).differentiableAt)
    intro x
    rw [(hk x).deriv]
    have hnorm : ‖fourier (-n) (x : AddCircle (b - a))‖ = 1 := by
      rw [fourier_apply]; exact Circle.norm_coe _
    exact_mod_cast hnorm.le
  simp_rw [fourierCoeffOn_eq_integral, smul_eq_mul, real_smul, ofReal_div, ofReal_one]
  conv => pattern (occs := 1 2 3) fourier _ _ * _ <;> (rw [mul_comm])
  have hki : IntervalIntegrable (fun x : ℝ => fourier (-n) (x : AddCircle (b - a))) volume a b :=
    ((map_continuous (fourier (-n))).comp (AddCircle.continuous_mk' _)).intervalIntegrable _ _
  rw [integral_mul_eq_boundary_sub hab.le hf hl.lipschitzOnWith.absolutelyContinuousOnInterval hf'
    hki hff' (Filter.Eventually.of_forall (fun x _ => hk x))]
  have : ∀ u v w : ℂ, u * ((b - a : ℝ) / v * w) = (b - a : ℝ) / v * (u * w) := by intros; ring
  conv in intervalIntegral _ _ _ _ => congr; ext; rw [this]
  rw [(by ring : ((b - a : ℝ) : ℂ) / (-2 * Real.pi * I * n) = ((b - a : ℝ) : ℂ) * (1 / (-2 * Real.pi * I * n)))]
  have s2 : (b : AddCircle (b - a)) = (a : AddCircle (b - a)) := by
    simpa using coe_add_period (b - a) a
  rw [s2, intervalIntegral.integral_const_mul, ← sub_mul, mul_sub, mul_sub]
  congr 1
  · conv_lhs => rw [mul_comm, mul_div, mul_one]
    rw [div_eq_iff (ofReal_ne_zero.mpr hT.out.ne')]
    ring
  · ring
open AddCircle Complex intervalIntegral in
/-- Period-two AC functions with zero mean satisfy the sharp spectral
estimate, with equality precisely when all frequencies except ±1 vanish. -/
lemma period_two_ac_spectral_gap {f g : ℝ → ℂ}
    (hf : AbsolutelyContinuousOnInterval f (-1) 1)
    (hfm : MemLp f 2 (volume.restrict (Ioc (-1 : ℝ) 1)))
    (hgm : MemLp g 2 (volume.restrict (Ioc (-1 : ℝ) 1)))
    (hd : ∀ᵐ x ∂volume, x ∈ Icc (-1 : ℝ) 1 → HasDerivAt f (g x) x)
    (hp : f 1 = f (-1)) (hm : (∫ x in (-1 : ℝ)..1, f x) = 0) :
    Real.pi ^ 2 * (∫ x in (-1 : ℝ)..1, ‖f x‖ ^ 2) ≤
      (∫ x in (-1 : ℝ)..1, ‖g x‖ ^ 2) ∧
    (Real.pi ^ 2 * (∫ x in (-1 : ℝ)..1, ‖f x‖ ^ 2) =
        (∫ x in (-1 : ℝ)..1, ‖g x‖ ^ 2) ↔
      ∀ n : ℤ, n ≠ 1 → n ≠ -1 → fourierCoeffOn (by norm_num : (-1 : ℝ) < 1) f n = 0) := by
  let hab : (-1 : ℝ) < 1 := by norm_num
  have hgi : IntervalIntegrable g volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact hgm.integrable (by norm_num)
  have hzero : fourierCoeffOn hab f 0 = 0 := by
    rw [fourierCoeffOn_eq_integral]
    simp [fourier_zero, hm]
  have hgzero : fourierCoeffOn hab g 0 = 0 := by
    rw [fourierCoeffOn_eq_integral]
    simp only [neg_zero, fourier_zero, one_smul]
    rw [integral_eq_sub_of_ac (by norm_num) hf hgi hd, hp, sub_self, smul_zero]
  have hcoeff (n : ℤ) : fourierCoeffOn hab g n =
      ((Real.pi : ℂ) * I * n) * fourierCoeffOn hab f n := by
    by_cases hn : n = 0
    · simp [hn, hgzero]
    have h := fourierCoeffOn_of_ac hab hn hf hd hgi
    rw [hp, sub_self, mul_zero] at h
    norm_num at h
    have hnon : (-2 * (Real.pi : ℂ) * I * n) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero) (by exact_mod_cast hn)
    have he := congrArg (fun z : ℂ => (-2 * (Real.pi : ℂ) * I * n) * z) h
    field_simp at he
    calc
      _ = -I * (I * fourierCoeffOn hab g n) := by simp [← mul_assoc]
      _ = -I * (-(Real.pi * n * fourierCoeffOn hab f n)) := by rw [← he]
      _ = _ := by ring
  have hnorm (n : ℤ) : ‖fourierCoeffOn hab g n‖ ^ 2 =
      Real.pi ^ 2 * (n : ℝ) ^ 2 * ‖fourierCoeffOn hab f n‖ ^ 2 := by
    rw [hcoeff]
    simp only [norm_mul, mul_pow, norm_I, mul_one, norm_real, Real.norm_eq_abs, sq_abs]
    norm_cast
    simp only [sq_abs]
  have hs := hasSum_sq_fourierCoeffOn hab hfm
  have ht := (hasSum_sq_fourierCoeffOn hab hgm).congr_fun (fun n => (hnorm n).symm)
  have hh := integer_spectral_gap (fun n => ‖fourierCoeffOn hab f n‖ ^ 2)
    _ _ (fun _ => sq_nonneg _) (by rw [hzero]; simp) hs ht
  norm_num [smul_eq_mul] at hh
  refine ⟨by nlinarith [hh.1], ?_⟩
  constructor
  · intro he n hn hnm
    have he' : Real.pi ^ 2 * ((1 / 2) * ∫ x in (-1 : ℝ)..1, ‖f x‖ ^ 2) =
        (1 / 2) * ∫ x in (-1 : ℝ)..1, ‖g x‖ ^ 2 := by linarith
    exact (hh.2.mp he') n hn hnm
  · intro h
    have hh' := hh.2.mpr h
    nlinarith
open AddCircle Complex intervalIntegral

/-- Reflection across zero, with a scalar on the negative half. -/
def reflection (s : ℂ) (f : ℝ → ℂ) : ℝ → ℂ :=
  (Iio (0 : ℝ)).piecewise (fun x => s * f (-x)) f

lemma reflection_memLp {f : ℝ → ℂ} (s : ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    MemLp (reflection s f) 2 (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  rw [← restrict_Ioo_eq_restrict_Ioc]
  have hm := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage (s := Ioo (0 : ℝ) 1) measurableSet_Ioo
  have hh : MemLp (fun x => f (-x)) 2 (volume.restrict (Ioo (-1 : ℝ) 0)) := by
    convert hf.comp_measurePreserving hm using 1 <;> simp [Function.comp_def]
  apply MemLp.piecewise measurableSet_Iio.nullMeasurableSet
  · rw [Measure.restrict_restrict measurableSet_Iio]
    have he : Iio (0 : ℝ) ∩ Ioo (-1 : ℝ) 1 = Ioo (-1 : ℝ) 0 := by
      ext x; simp only [mem_inter_iff, mem_Iio, mem_Ioo]
      constructor
      · rintro ⟨hx, h1, h2⟩; exact ⟨h1, hx⟩
      · rintro ⟨h1, h0⟩; exact ⟨h0, h1, lt_trans h0 zero_lt_one⟩
    rw [he]
    exact hh.const_mul s
  · rw [Measure.restrict_restrict measurableSet_Iio.compl]
    have he : (Iio (0 : ℝ))ᶜ ∩ Ioo (-1 : ℝ) 1 = Ico (0 : ℝ) 1 := by
      ext x; simp only [mem_inter_iff, mem_compl_iff, mem_Iio, not_lt, mem_Ioo, mem_Ico]
      constructor
      · rintro ⟨h0, h1, h2⟩; exact ⟨h0, h2⟩
      · rintro ⟨h0, h1⟩; exact ⟨h0, by linarith, h1⟩
    rw [he, ← restrict_Ioo_eq_restrict_Ico]
    exact hf

lemma integral_reflection {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) (G : ℝ → E)
    (hF : IntervalIntegrable F volume 0 1) (hG : IntervalIntegrable G volume 0 1) :
    (∫ x in (-1 : ℝ)..1, (Iio (0 : ℝ)).piecewise (fun x => F (-x)) G x) =
      (∫ x in (0 : ℝ)..1, F x) + ∫ x in (0 : ℝ)..1, G x := by
  let H := (Iio (0 : ℝ)).piecewise (fun x => F (-x)) G
  have hneg : IntervalIntegrable (fun x => F (-x)) volume (-1) 0 := by
    rw [IntervalIntegrable.iff_comp_neg]
    simpa using hF.symm
  have hleft : H =ᵐ[volume.restrict (Ioc (-1 : ℝ) 0)] (fun x => F (-x)) := by
    rw [← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simp [H, hx.2]
  have hright : EqOn H G (Icc (0 : ℝ) 1) := by
    intro x hx
    simp [H, Set.piecewise, not_lt.mpr hx.1]
  have hli : IntervalIntegrable H volume (-1) 0 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hneg ⊢
    exact hneg.congr hleft.symm
  have hri : IntervalIntegrable H volume 0 1 := by
    apply hG.congr
    intro x hx
    exact (hright (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using uIoc_subset_uIcc hx)).symm
  rw [← integral_add_adjacent_intervals hli hri]
  congr 1
  · rw [integral_congr_ae_restrict (by simpa only [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] using hleft)]
    simpa using integral_comp_neg (f := F) (a := (-1 : ℝ)) (b := 0)
  · exact integral_congr (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hright)

def reflectionKernel (n : ℤ) (x : ℝ) : ℂ := fourier (-n) (x : AddCircle (2 : ℝ))

lemma reflectionKernel_contDiff (n : ℤ) : ContDiff ℝ 1 (reflectionKernel n) := by
  unfold reflectionKernel
  simp only [fourier_coe_apply]
  exact Complex.contDiff_exp.comp
    ((contDiff_const.mul (Complex.ofRealCLM.contDiff : ContDiff ℝ 1 ((↑) : ℝ → ℂ))).div_const _)

lemma reflectionKernel_hasDerivAt (n : ℤ) (x : ℝ) :
    HasDerivAt (reflectionKernel n) (-((Real.pi : ℂ) * I * n) * reflectionKernel n x) x := by
  convert! hasDerivAt_fourier_neg 2 n x using 1 <;> norm_num [reflectionKernel] <;> ring

lemma reflectionKernel_endpoints (n : ℤ) : reflectionKernel n 1 = reflectionKernel n (-1) := by
  unfold reflectionKernel
  congr 1
  convert coe_add_period (2 : ℝ) (-1 : ℝ) using 1 <;> norm_num

lemma fourierCoeffOn_reflection {f : ℝ → ℂ} (s : ℂ)
    (hf : IntervalIntegrable f volume 0 1) (n : ℤ) :
    fourierCoeffOn (by norm_num : (-1 : ℝ) < 1) (reflection s f) n =
      (1 / 2 : ℂ) * ∫ x in (0 : ℝ)..1,
        (reflectionKernel n x + s * reflectionKernel n (-x)) * f x := by
  have hk := (reflectionKernel_contDiff n).continuous
  have hF : IntervalIntegrable (fun x => reflectionKernel n (-x) * (s * f x)) volume 0 1 :=
    (hf.const_mul s).continuousOn_mul (hk.comp continuous_neg).continuousOn
  have hG : IntervalIntegrable (fun x => reflectionKernel n x * f x) volume 0 1 :=
    hf.continuousOn_mul hk.continuousOn
  have he : (fun x => reflectionKernel n x * reflection s f x) =
      (Iio (0 : ℝ)).piecewise (fun x => reflectionKernel n (-(-x)) * (s * f (-x)))
        (fun x => reflectionKernel n x * f x) := by
    funext x
    by_cases hx : x < 0 <;> simp [reflection, hx]
  rw [fourierCoeffOn_eq_integral]
  simp only [fourier_coe_apply, smul_eq_mul, real_smul, ofReal_div, ofReal_one]
  norm_num only [show (1 - (-1) : ℝ) = 2 by norm_num, ofReal_ofNat]
  have hkval (x : ℝ) : cexp (2 * (Real.pi : ℂ) * I * (-n : ℤ) * x / 2) = reflectionKernel n x := by
    simp only [reflectionKernel, fourier_coe_apply, ofReal_ofNat]
  simp_rw [hkval]
  rw [he, integral_reflection _ _ hF hG, ← integral_add hF hG]
  congr 1
  apply integral_congr
  intro x _
  ring

lemma reflection_derivative_coeff {f g : ℝ → ℂ} (s : ℂ)
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hgi : IntervalIntegrable g volume 0 1)
    (hd : ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 → HasDerivAt f (g x) x)
    (hb0 : (1 - s) * f 0 = 0) (hb1 : (1 - s) * f 1 = 0) (n : ℤ) :
    fourierCoeffOn (by norm_num : (-1 : ℝ) < 1) (reflection (-s) g) n =
      ((Real.pi : ℂ) * I * n) *
        fourierCoeffOn (by norm_num : (-1 : ℝ) < 1) (reflection s f) n := by
  let ψ := fun x => reflectionKernel n x - s * reflectionKernel n (-x)
  let ψ' := fun x => -((Real.pi : ℂ) * I * n) *
    (reflectionKernel n x + s * reflectionKernel n (-x))
  have hψ : ContDiff ℝ 1 ψ := by
    dsimp [ψ]
    exact (reflectionKernel_contDiff n).sub
      (contDiff_const.mul ((reflectionKernel_contDiff n).comp contDiff_neg))
  have hψ' : Continuous ψ' := by
    dsimp [ψ']
    have hk := (reflectionKernel_contDiff n).continuous
    exact continuous_const.mul (hk.add (continuous_const.mul (hk.comp continuous_neg)))
  have hψd (x : ℝ) : HasDerivAt ψ (ψ' x) x := by
    have h := (reflectionKernel_hasDerivAt n x).sub
      (((reflectionKernel_hasDerivAt n (-x)).scomp x (hasDerivAt_neg x)).const_mul s)
    convert! h using 1 <;> norm_num [ψ, ψ', Function.comp_def, real_smul] <;> ring
  have he := integral_mul_eq_boundary_sub (by norm_num : (0 : ℝ) ≤ 1)
    hψ.contDiffOn.absolutelyContinuousOnInterval hf
    (hψ'.intervalIntegrable 0 1) hgi
    (Filter.Eventually.of_forall fun x _ => hψd x) hd
  have hboundary : ψ 1 * f 1 - ψ 0 * f 0 = 0 := by
    dsimp [ψ]
    rw [reflectionKernel_endpoints]
    have h0 : reflectionKernel n (-0) = reflectionKernel n 0 := by rw [neg_zero]
    rw [h0]
    calc
      _ = reflectionKernel n (-1) * ((1 - s) * f 1) -
        reflectionKernel n 0 * ((1 - s) * f 0) := by ring
      _ = 0 := by rw [hb0, hb1]; ring
  rw [hboundary, zero_sub] at he
  rw [fourierCoeffOn_reflection (-s) hgi,
    fourierCoeffOn_reflection s hf.continuousOn.intervalIntegrable]
  have hi : IntervalIntegrable (fun x => (reflectionKernel n x + s * reflectionKernel n (-x)) * f x)
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    exact ((reflectionKernel_contDiff n).continuous.continuousOn.add
      (continuousOn_const.mul ((reflectionKernel_contDiff n).continuous.comp continuous_neg).continuousOn)).mul hf.continuousOn
  have he' : (∫ x in (0 : ℝ)..1, (reflectionKernel n x + -s * reflectionKernel n (-x)) * g x) =
      ((Real.pi : ℂ) * I * n) * ∫ x in (0 : ℝ)..1,
        (reflectionKernel n x + s * reflectionKernel n (-x)) * f x := by
    calc
      _ = ∫ x in (0 : ℝ)..1, ψ x * g x := by congr 1; funext x; dsimp [ψ]; ring
      _ = -(∫ x in (0 : ℝ)..1, ψ' x * f x) := he
      _ = _ := by
        dsimp [ψ']
        simp_rw [mul_assoc]
        rw [intervalIntegral.integral_const_mul]
        ring
  rw [he']
  ring

lemma reflection_energy {f : ℝ → ℂ} (s : ℂ) (hs : ‖s‖ = 1)
    (hf : MemLp f 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    (∫ x in (-1 : ℝ)..1, ‖reflection s f x‖ ^ 2) =
      2 * ∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2 := by
  have hi : IntervalIntegrable (fun x => ‖f x‖ ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    change Integrable _ (volume.restrict (Ioc (0 : ℝ) 1))
    rw [← restrict_Ioo_eq_restrict_Ioc]
    exact hf.integrable_norm_pow (by decide)
  have he : (fun x => ‖reflection s f x‖ ^ 2) =
      (Iio (0 : ℝ)).piecewise (fun x => ‖f (-x)‖ ^ 2) (fun x => ‖f x‖ ^ 2) := by
    funext x
    by_cases hx : x < 0 <;> simp [reflection, hx, norm_mul, hs]
  rw [he, integral_reflection _ _ hi hi]
  ring

/-- Sharp energy comparison after reflection. Every datum here is an ordinary
AC function and its specified L² derivative on the original interval. -/
lemma reflection_spectral_gap {f g : ℝ → ℂ} (s : ℂ) (hs : ‖s‖ = 1)
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hfm : MemLp f 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hgm : MemLp g 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hd : ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 → HasDerivAt f (g x) x)
    (hb0 : (1 - s) * f 0 = 0) (hb1 : (1 - s) * f 1 = 0)
    (hm : (1 + s) * (∫ x in (0 : ℝ)..1, f x) = 0) :
    Real.pi ^ 2 * (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) ≤
      (∫ x in (0 : ℝ)..1, ‖g x‖ ^ 2) ∧
    (Real.pi ^ 2 * (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) =
        (∫ x in (0 : ℝ)..1, ‖g x‖ ^ 2) ↔
      ∀ n : ℤ, n ≠ 1 → n ≠ -1 →
        fourierCoeffOn (by norm_num : (-1 : ℝ) < 1) (reflection s f) n = 0) := by
  let hab : (-1 : ℝ) < 1 := by norm_num
  have hgi : IntervalIntegrable g volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    change Integrable g (volume.restrict (Ioc (0 : ℝ) 1))
    rw [← restrict_Ioo_eq_restrict_Ioc]
    exact hgm.integrable (by norm_num)
  have hzero : fourierCoeffOn hab (reflection s f) 0 = 0 := by
    rw [fourierCoeffOn_reflection s hf.continuousOn.intervalIntegrable]
    simp only [reflectionKernel, neg_zero, fourier_zero, mul_one, ← mul_add, one_mul]
    rw [intervalIntegral.integral_const_mul, hm, mul_zero]
  have hcoeff := reflection_derivative_coeff s hf hgi hd hb0 hb1
  have hnorm (n : ℤ) : ‖fourierCoeffOn hab (reflection (-s) g) n‖ ^ 2 =
      Real.pi ^ 2 * (n : ℝ) ^ 2 * ‖fourierCoeffOn hab (reflection s f) n‖ ^ 2 := by
    rw [hcoeff]
    simp only [norm_mul, mul_pow, norm_I, mul_one, norm_real, Real.norm_eq_abs, sq_abs]
    norm_cast
    simp only [sq_abs]
  have hsf := hasSum_sq_fourierCoeffOn hab (reflection_memLp s hfm)
  have hsg := hasSum_sq_fourierCoeffOn hab (reflection_memLp (-s) hgm)
  rw [reflection_energy s hs hfm] at hsf
  rw [reflection_energy (-s) (by simpa using hs) hgm] at hsg
  norm_num [smul_eq_mul] at hsf hsg
  have hh := integer_spectral_gap (fun n => ‖fourierCoeffOn hab (reflection s f) n‖ ^ 2)
    _ _ (fun _ => sq_nonneg _) (by rw [hzero]; simp) hsf
    (hsg.congr_fun (fun n => (hnorm n).symm))
  simpa only [sq_eq_zero_iff, norm_eq_zero, ← mul_assoc, one_div_mul_cancel (by norm_num : (2 : ℝ) ≠ 0), one_mul] using hh

lemma ac_energy_bound {𝕜 : Type} [RCLike 𝕜] {f g : ℝ → 𝕜}
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hfm : MemLp f 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hgm : MemLp g 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hd : ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 → HasDerivAt f (g x) x)
    (hbc : (∫ x in (0 : ℝ)..1, f x) = 0 ∨ f 0 = 0 ∧ f 1 = 0) :
    Real.pi ^ 2 * (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) ≤
      (∫ x in (0 : ℝ)..1, ‖g x‖ ^ 2) := by
  let L := RCLike.map 𝕜 ℂ
  let F := fun x => L (f x)
  let G := fun x => L (g x)
  have hFnorm (x : ℝ) : ‖F x‖ = ‖f x‖ := RCLike.norm_to_complex _
  have hGnorm (x : ℝ) : ‖G x‖ = ‖g x‖ := RCLike.norm_to_complex _
  have hFA : AbsolutelyContinuousOnInterval F 0 1 :=
    L.lipschitzWith.comp_absolutelyContinuousOnInterval hf
  have hFM : MemLp F 2 (volume.restrict (Ioo (0 : ℝ) 1)) := hfm.continuousLinearMap_comp L
  have hGM : MemLp G 2 (volume.restrict (Ioo (0 : ℝ) 1)) := hgm.continuousLinearMap_comp L
  have hD : ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 → HasDerivAt F (G x) x := by
    filter_upwards [hd] with x hx hxi
    exact L.hasFDerivAt.comp_hasDerivAt x (hx hxi)
  have hh : Real.pi ^ 2 * (∫ x in (0 : ℝ)..1, ‖F x‖ ^ 2) ≤
      (∫ x in (0 : ℝ)..1, ‖G x‖ ^ 2) := by
    rcases hbc with hm | ⟨h0, h1⟩
    · apply (reflection_spectral_gap 1 (by simp) hFA hFM hGM hD (by simp) (by simp) ?_).1
      have hi : IntervalIntegrable f volume 0 1 := hf.continuousOn.intervalIntegrable
      have hM : (∫ x in (0 : ℝ)..1, F x) = 0 := by
        rw [L.intervalIntegral_comp_comm hi, hm, map_zero]
      rw [hM, mul_zero]
    · apply (reflection_spectral_gap (-1) (by simp) hFA hFM hGM hD ?_ ?_ (by simp)).1
      · simp [F, h0]
      · simp [F, h1]
  simpa only [hFnorm, hGnorm] using hh

lemma representative_closed_ae_hasDerivAt {𝕜 : Type} [RCLike 𝕜] {u : H1 𝕜} {f : ℝ → 𝕜}
    (hf : ExpandedFA.Sobolev.OneDimensional.PrimitiveRepresentative u f) :
    ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 →
      HasDerivAt f (ExpandedFA.Sobolev.OneDimensional.lineFunction
        (ExpandedFA.Sobolev.OneDimensional.derivativeLp u) x) x := by
  have hd := (ae_restrict_iff' measurableSet_Ioo).mp (representative_ae_hasDerivAt hf)
  filter_upwards [hd, (Ioo_ae_eq_Icc : Ioo (0 : ℝ) 1 =ᵐ[volume] Icc (0 : ℝ) 1)] with x hx he hxi
  exact hx (he.mpr hxi)

theorem mean_bound : Specs.ExpandedFA.PartIV.IntervalL2Constants.MeanBound := by
  intro 𝕜 _ u f hf
  let g := ExpandedFA.Sobolev.OneDimensional.lineFunction
    (ExpandedFA.Sobolev.OneDimensional.derivativeLp u)
  have hfc : MemLp (fun x => f x - mean f) 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
    (representative_memLp hf).sub (memLp_const _)
  have hfac : AbsolutelyContinuousOnInterval (fun x => f x - mean f) 0 1 := by
    convert! (representative_absolutelyContinuous hf).sub
      ((LipschitzWith.const (mean f)).lipschitzOnWith.absolutelyContinuousOnInterval) using 1
  have hfd : ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 → HasDerivAt (fun x => f x - mean f) (g x) x := by
    filter_upwards [representative_closed_ae_hasDerivAt hf] with x hx hxi
    exact (hx hxi).sub_const _
  have hm : (∫ x in (0 : ℝ)..1, f x - mean f) = 0 := by
    rw [intervalIntegral.integral_sub (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using representative_continuous hf : ContinuousOn f (uIcc 0 1)).intervalIntegrable intervalIntegrable_const,
      intervalIntegral.integral_const]
    change mean f - (1 - 0 : ℝ) • mean f = 0
    simp
  have hh := ac_energy_bound hfac hfc
    (ExpandedFA.Sobolev.OneDimensional.lineFunction_memLp
      (ExpandedFA.Sobolev.OneDimensional.derivativeLp u)) hfd (Or.inl hm)
  rw [l2Norm_sq hfc, l2Norm_sq (ExpandedFA.Sobolev.OneDimensional.lineFunction_memLp
    (ExpandedFA.Sobolev.OneDimensional.derivativeLp u)), derivative_l2Norm] at hh
  have hπ := Real.pi_pos
  have hN := l2Norm_nonneg (fun x => f x - mean f)
  have hD := norm_nonneg (ExpandedFA.Sobolev.OneDimensional.derivativeLp u)
  apply (mul_le_mul_iff_right₀ hπ).mp
  rw [← mul_assoc, mul_inv_cancel₀ Real.pi_ne_zero, one_mul]
  nlinarith

theorem zero_bound : Specs.ExpandedFA.PartIV.IntervalL2Constants.ZeroBound := by
  intro 𝕜 _ u f hf hz
  have hend := (zero_trace_identification 𝕜 u f hf).mp hz
  have hh := ac_energy_bound (representative_absolutelyContinuous hf) (representative_memLp hf)
    (ExpandedFA.Sobolev.OneDimensional.lineFunction_memLp
      (ExpandedFA.Sobolev.OneDimensional.derivativeLp u))
    (representative_closed_ae_hasDerivAt hf) (Or.inr hend)
  rw [l2Norm_sq (representative_memLp hf),
    l2Norm_sq (ExpandedFA.Sobolev.OneDimensional.lineFunction_memLp
      (ExpandedFA.Sobolev.OneDimensional.derivativeLp u)), derivative_l2Norm] at hh
  apply (mul_le_mul_iff_right₀ Real.pi_pos).mp
  rw [← mul_assoc, mul_inv_cancel₀ Real.pi_ne_zero, one_mul]
  nlinarith [l2Norm_nonneg f, norm_nonneg (ExpandedFA.Sobolev.OneDimensional.derivativeLp u)]
lemma two_mode_representation {F : ℝ → ℂ}
    (hF : MemLp F 2 (volume.restrict (Ioc (-1 : ℝ) 1)))
    (hs : ∀ n : ℤ, n ≠ 1 → n ≠ -1 →
      fourierCoeffOn (by norm_num : (-1 : ℝ) < 1) F n = 0) :
    F =ᵐ[volume.restrict (Ioc (-1 : ℝ) 1)]
      (fun x => fourierCoeffOn (by norm_num : (-1 : ℝ) < 1) F 1 *
          fourier 1 (x : AddCircle (2 : ℝ)) +
        fourierCoeffOn (by norm_num : (-1 : ℝ) < 1) F (-1) *
          fourier (-1) (x : AddCircle (2 : ℝ))) := by
  letI : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩
  let V := AddCircle.liftIoc (2 : ℝ) (-1) F
  have hM : MemLp V 2 (volume : Measure (AddCircle (2 : ℝ))) := by
    have hF' : MemLp F 2 (volume.restrict (Ioc (-1 : ℝ) (-1 + 2))) := by norm_num; exact hF
    exact hF'.memLp_liftIoc
  let H := hM.haarAddCircle
  let v := H.toLp V
  have hc (n : ℤ) : fourierCoeff v n =
      fourierCoeffOn (by norm_num : (-1 : ℝ) < 1) F n := by
    rw [fourierCoeff_congr_ae H.coeFn_toLp]
    convert fourierCoeff_liftIoc_eq (T := (2 : ℝ)) (a := (-1 : ℝ)) F n using 1 <;> norm_num
  have he : v = fourierCoeff v 1 • fourierLp (T := (2 : ℝ)) 2 1 + fourierCoeff v (-1) • fourierLp (T := (2 : ℝ)) 2 (-1) := by
    have ht := (hasSum_ite_eq (1 : ℤ) (fourierCoeff v 1 • fourierLp (T := (2 : ℝ)) 2 1)).add
      (hasSum_ite_eq (-1 : ℤ) (fourierCoeff v (-1) • fourierLp (T := (2 : ℝ)) 2 (-1)))
    have ht' : HasSum (fun n : ℤ => fourierCoeff v n • fourierLp (T := (2 : ℝ)) 2 n)
        (fourierCoeff v 1 • fourierLp (T := (2 : ℝ)) 2 1 + fourierCoeff v (-1) • fourierLp (T := (2 : ℝ)) 2 (-1)) := by
      apply ht.congr_fun
      intro n
      by_cases h1 : n = 1
      · simp [h1]
      by_cases hm1 : n = -1
      · simp [hm1]
      simp [h1, hm1, hc, hs n h1 hm1]
    exact (hasSum_fourier_series_L2 v).unique ht'
  have hva : v =ᵐ[haarAddCircle] (fun x : AddCircle (2 : ℝ) =>
      fourierCoeff v 1 * fourier 1 x + fourierCoeff v (-1) * fourier (-1) x) := by
    nth_rw 1 [he]
    filter_upwards [Lp.coeFn_add (fourierCoeff v 1 • fourierLp (T := (2 : ℝ)) 2 1)
        (fourierCoeff v (-1) • fourierLp (T := (2 : ℝ)) 2 (-1)),
      Lp.coeFn_smul (fourierCoeff v 1) (fourierLp (T := (2 : ℝ)) 2 1),
      Lp.coeFn_smul (fourierCoeff v (-1)) (fourierLp (T := (2 : ℝ)) 2 (-1)),
      coeFn_fourierLp (T := (2 : ℝ)) 2 1, coeFn_fourierLp (T := (2 : ℝ)) 2 (-1)]
      with x ha hb hc' hd he'
    simp only [ha, Pi.add_apply, hb, hc', Pi.smul_apply, smul_eq_mul, hd, he']
  have hVa := H.coeFn_toLp.symm.trans hva
  have hVol : V =ᵐ[volume] (fun x : AddCircle (2 : ℝ) =>
      fourierCoeff v 1 * fourier 1 x + fourierCoeff v (-1) * fourier (-1) x) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    exact Measure.ae_smul_measure hVa _
  have hp := (AddCircle.measurePreserving_mk (2 : ℝ) (-1)).quasiMeasurePreserving.ae hVol
  have hp' : ∀ᵐ (x : ℝ) ∂volume.restrict (Ioc (-1 : ℝ) 1),
      V (x : AddCircle (2 : ℝ)) = fourierCoeff v 1 * fourier 1 (x : AddCircle (2 : ℝ)) +
        fourierCoeff v (-1) * fourier (-1) (x : AddCircle (2 : ℝ)) := by simpa only [show (-1 + 2 : ℝ) = 1 by norm_num] using hp
  filter_upwards [hp', ae_restrict_mem measurableSet_Ioc] with x hx hxi
  have heq : V (x : AddCircle (2 : ℝ)) = F x :=
    AddCircle.liftIoc_coe_apply (by constructor <;> linarith [hxi.1, hxi.2])
  rw [heq, hc, hc] at hx
  exact hx

lemma fourier_one_trig (x : ℝ) :
    fourier 1 (x : AddCircle (2 : ℝ)) =
      (Real.cos (Real.pi * x) : ℂ) + (Real.sin (Real.pi * x) : ℂ) * I := by
  rw [fourier_coe_apply]
  convert exp_ofReal_mul_I (Real.pi * x) using 1 <;> push_cast <;> ring

lemma fourier_neg_one_trig (x : ℝ) :
    fourier (-1) (x : AddCircle (2 : ℝ)) =
      (Real.cos (Real.pi * x) : ℂ) - (Real.sin (Real.pi * x) : ℂ) * I := by
  rw [fourier_neg, fourier_one_trig]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

lemma reflectionKernel_neg (n : ℤ) (x : ℝ) :
    reflectionKernel (-n) x = reflectionKernel n (-x) := by
  simp only [reflectionKernel, fourier_coe_apply, neg_neg, ofReal_neg, Int.cast_neg]
  congr 1
  ring

lemma reflection_trig_form {f : ℝ → ℂ} (s : ℂ)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hfm : MemLp f 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hs : ∀ n : ℤ, n ≠ 1 → n ≠ -1 →
      fourierCoeffOn (by norm_num : (-1 : ℝ) < 1) (reflection s f) n = 0) :
    ∃ a b : ℂ, EqOn f (fun x => a * (Real.cos (Real.pi * x) : ℂ) +
      b * (Real.sin (Real.pi * x) : ℂ)) (Icc 0 1) ∧ (s = 1 → b = 0) := by
  let p := fourierCoeffOn (by norm_num : (-1 : ℝ) < 1) (reflection s f) 1
  let q := fourierCoeffOn (by norm_num : (-1 : ℝ) < 1) (reflection s f) (-1)
  let E := fun (x : ℝ) => p * fourier 1 (x : AddCircle (2 : ℝ)) +
    q * fourier (-1) (x : AddCircle (2 : ℝ))
  have ha := two_mode_representation (reflection_memLp s hfm) hs
  have hpos : f =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] E := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    have hsub : Ioo (0 : ℝ) 1 ⊆ Ioc (-1 : ℝ) 1 := by intro x hx; constructor <;> linarith [hx.1, hx.2]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub ha,
      ae_restrict_mem measurableSet_Ioo] with x hx hxi
    rw [show reflection s f x = f x by simp [reflection, not_lt.mpr hxi.1.le]] at hx
    exact hx
  have hE : Continuous E := by
    exact (continuous_const.mul ((fourier 1).continuous.comp (AddCircle.continuous_mk' _))).add
      (continuous_const.mul ((fourier (-1)).continuous.comp (AddCircle.continuous_mk' _)))
  have he := Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (0 : ℝ) ≠ 1) hpos hf hE.continuousOn
  refine ⟨p + q, (p - q) * I, ?_, ?_⟩
  · intro x hx
    rw [he hx]
    change p * fourier 1 (x : AddCircle (2 : ℝ)) + q * fourier (-1) (x : AddCircle (2 : ℝ)) = _
    rw [fourier_one_trig, fourier_neg_one_trig]
    ring
  · intro hs1
    have hfi : IntervalIntegrable f volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hf
    have hpq : q = p := by
      dsimp [p, q]
      rw [hs1, fourierCoeffOn_reflection 1 hfi (-1), fourierCoeffOn_reflection 1 hfi 1]
      congr 1
      apply integral_congr
      intro x _
      change (reflectionKernel (-1) x + 1 * reflectionKernel (-1) (-x)) * f x =
        (reflectionKernel 1 x + 1 * reflectionKernel 1 (-x)) * f x
      rw [reflectionKernel_neg, reflectionKernel_neg]
      simp only [neg_neg, one_mul]
      ring
    rw [hpq, sub_self, zero_mul]

lemma complexified_equality_trig_form {𝕜 : Type} [RCLike 𝕜] {f g : ℝ → 𝕜} (s : ℂ)
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hfm : MemLp f 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hgm : MemLp g 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hd : ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 → HasDerivAt f (g x) x)
    (hbc : (s = 1 ∧ (∫ x in (0 : ℝ)..1, f x) = 0) ∨ (s = -1 ∧ f 0 = 0 ∧ f 1 = 0))
    (he : Real.pi ^ 2 * (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) =
      (∫ x in (0 : ℝ)..1, ‖g x‖ ^ 2)) :
    ∃ a b : ℂ, EqOn (fun x => RCLike.map 𝕜 ℂ (f x))
      (fun x => a * (Real.cos (Real.pi * x) : ℂ) + b * (Real.sin (Real.pi * x) : ℂ))
        (Icc 0 1) ∧ (s = 1 → b = 0) := by
  let L := RCLike.map 𝕜 ℂ
  let F := fun x => L (f x)
  let G := fun x => L (g x)
  have hFA : AbsolutelyContinuousOnInterval F 0 1 :=
    L.lipschitzWith.comp_absolutelyContinuousOnInterval hf
  have hFM := hfm.continuousLinearMap_comp L
  have hGM := hgm.continuousLinearMap_comp L
  have hD : ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 → HasDerivAt F (G x) x := by
    filter_upwards [hd] with x hx hxi
    exact L.hasFDerivAt.comp_hasDerivAt x (hx hxi)
  have hs : ‖s‖ = 1 := by rcases hbc with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
  have hb0 : (1 - s) * F 0 = 0 := by
    rcases hbc with ⟨rfl, _⟩ | ⟨rfl, h0, _⟩
    · simp
    · simp [F, h0]
  have hb1 : (1 - s) * F 1 = 0 := by
    rcases hbc with ⟨rfl, _⟩ | ⟨rfl, _, h1⟩
    · simp
    · simp [F, h1]
  have hm : (1 + s) * (∫ x in (0 : ℝ)..1, F x) = 0 := by
    rcases hbc with ⟨rfl, hm⟩ | ⟨rfl, _⟩
    · rw [L.intervalIntegral_comp_comm hf.continuousOn.intervalIntegrable, hm, map_zero, mul_zero]
    · simp
  have he' : Real.pi ^ 2 * (∫ x in (0 : ℝ)..1, ‖F x‖ ^ 2) =
      (∫ x in (0 : ℝ)..1, ‖G x‖ ^ 2) := by
    have hFnorm (x : ℝ) : ‖F x‖ = ‖f x‖ := RCLike.norm_to_complex _
    have hGnorm (x : ℝ) : ‖G x‖ = ‖g x‖ := RCLike.norm_to_complex _
    simpa only [hFnorm, hGnorm] using he
  have hh := (reflection_spectral_gap s hs hFA hFM hGM hD hb0 hb1 hm).2.mp he'
  exact reflection_trig_form s (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hFA.continuousOn) hFM hh

lemma complexification_injective (𝕜 : Type) [RCLike 𝕜] : Function.Injective (RCLike.map 𝕜 ℂ) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hh : ‖RCLike.map 𝕜 ℂ (a - b)‖ = ‖a - b‖ := RCLike.norm_to_complex _
  rw [← hh, map_sub, hab, sub_self, norm_zero]

lemma complexification_mul_real {𝕜 : Type} [RCLike 𝕜] (a : 𝕜) (r : ℝ) :
    RCLike.map 𝕜 ℂ (a * (r : 𝕜)) = RCLike.map 𝕜 ℂ a * (r : ℂ) := by
  simp only [RCLike.map_apply, RCLike.mul_re, RCLike.mul_im, RCLike.ofReal_re,
    RCLike.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, zero_add, RCLike.ofReal_mul]
  change (RCLike.re a : ℂ) * (r : ℂ) + (RCLike.im a : ℂ) * (r : ℂ) * I =
    ((RCLike.re a : ℂ) + (RCLike.im a : ℂ) * I) * (r : ℂ)
  ring

lemma l2_energy_equality {𝕜 : Type} [RCLike 𝕜] {f g : ℝ → 𝕜}
    (hf : MemLp f 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hg : MemLp g 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (he : l2Norm f = Real.pi⁻¹ * l2Norm g) :
    Real.pi ^ 2 * (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) =
      (∫ x in (0 : ℝ)..1, ‖g x‖ ^ 2) := by
  rw [l2Norm_sq hf, l2Norm_sq hg]
  have hh : Real.pi * l2Norm f = l2Norm g := by
    rw [he, ← mul_assoc, mul_inv_cancel₀ Real.pi_ne_zero, one_mul]
  calc
    Real.pi ^ 2 * l2Norm f ^ 2 = (Real.pi * l2Norm f) ^ 2 := by ring
    _ = l2Norm g ^ 2 := by rw [hh]

theorem mean_equality : Specs.ExpandedFA.PartIV.IntervalL2Constants.MeanEquality := by
  intro 𝕜 _ u f hf
  constructor
  · intro he
    let g := ExpandedFA.Sobolev.OneDimensional.lineFunction
      (ExpandedFA.Sobolev.OneDimensional.derivativeLp u)
    have hfc : MemLp (fun x => f x - mean f) 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
      (representative_memLp hf).sub (memLp_const _)
    have hfac : AbsolutelyContinuousOnInterval (fun x => f x - mean f) 0 1 := by
      convert! (representative_absolutelyContinuous hf).sub
        ((LipschitzWith.const (mean f)).lipschitzOnWith.absolutelyContinuousOnInterval) using 1
    have hfd : ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 → HasDerivAt (fun x => f x - mean f) (g x) x := by
      filter_upwards [representative_closed_ae_hasDerivAt hf] with x hx hxi
      exact (hx hxi).sub_const _
    have hm : (∫ x in (0 : ℝ)..1, f x - mean f) = 0 := by
      have hfi : IntervalIntegrable f volume 0 1 := by
        apply ContinuousOn.intervalIntegrable
        simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using representative_continuous hf
      rw [intervalIntegral.integral_sub hfi intervalIntegrable_const, intervalIntegral.integral_const]
      change mean f - (1 - 0 : ℝ) • mean f = 0
      simp
    have hgm := ExpandedFA.Sobolev.OneDimensional.lineFunction_memLp
      (ExpandedFA.Sobolev.OneDimensional.derivativeLp u)
    have he' : l2Norm (fun x => f x - mean f) = Real.pi⁻¹ * l2Norm g := by
      simpa only [g, derivative_l2Norm] using he
    obtain ⟨a, b, hform, hb⟩ := complexified_equality_trig_form 1 hfac hfc hgm hfd
      (Or.inl ⟨rfl, hm⟩) (l2_energy_equality hfc hgm he')
    have hb0 : b = 0 := hb rfl
    have ha : RCLike.map 𝕜 ℂ (f 0 - mean f) = a := by
      simpa using hform (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
    refine ⟨mean f, f 0 - mean f, ?_⟩
    intro x hx
    have hh : f x - mean f = (f 0 - mean f) * (Real.cos (Real.pi * x) : 𝕜) := by
      apply complexification_injective 𝕜
      rw [complexification_mul_real]
      simpa only [hb0, zero_mul, add_zero, ← ha] using hform hx
    calc
      f x = (f 0 - mean f) * (Real.cos (Real.pi * x) : 𝕜) + mean f := sub_eq_iff_eq_add.mp hh
      _ = mean f + (f 0 - mean f) * (Real.cos (Real.pi * x) : 𝕜) := add_comm _ _
  · exact cosine_optimizer_sufficient hf

theorem zero_equality : Specs.ExpandedFA.PartIV.IntervalL2Constants.ZeroEquality := by
  intro 𝕜 _ u f hf hz
  constructor
  · intro he
    have hend := (zero_trace_identification 𝕜 u f hf).mp hz
    have hgm := ExpandedFA.Sobolev.OneDimensional.lineFunction_memLp
      (ExpandedFA.Sobolev.OneDimensional.derivativeLp u)
    have he' : l2Norm f = Real.pi⁻¹ * l2Norm (ExpandedFA.Sobolev.OneDimensional.lineFunction
        (ExpandedFA.Sobolev.OneDimensional.derivativeLp u)) := by
      simpa only [derivative_l2Norm] using he
    obtain ⟨a, b, hform, _⟩ := complexified_equality_trig_form (-1)
      (representative_absolutelyContinuous hf) (representative_memLp hf) hgm
      (representative_closed_ae_hasDerivAt hf) (Or.inr ⟨rfl, hend⟩)
      (l2_energy_equality (representative_memLp hf) hgm he')
    have ha0 : a = 0 := by
      have hh := hform (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
      simpa [hend.1] using hh.symm
    have hb : RCLike.map 𝕜 ℂ (f (1 / 2)) = b := by
      have hh := hform (show (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
      dsimp only at hh
      rw [ha0, zero_mul, zero_add] at hh
      have hsine : (Real.sin (Real.pi * (1 / 2)) : ℂ) = 1 := by
        rw [show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.sin_pi_div_two]
        norm_num
      simpa only [hsine, mul_one] using hh
    refine ⟨f (1 / 2), ?_⟩
    intro x hx
    apply complexification_injective 𝕜
    rw [complexification_mul_real]
    simpa only [ha0, zero_mul, zero_add, ← hb] using hform hx
  · intro ho
    exact (sine_optimizer_sufficient hf ho).2
end ExpandedFA.PartIV.IntervalL2

/- Mathlib proof attribution
Adapted portion near line 529:
The Fourier-coefficient integration-by-parts argument, adapted to the local
absolute continuity and a.e. derivative formulation.

Upstream: Mathlib/Analysis/Fourier/AddCircle.lean (around line 558)
Revision: 56a005855ea17e0b0958f73ec801ae140b0a1679
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, David Loeffler

See THIRD_PARTY_NOTICES.md for source links and the Apache 2.0 license.
-/
