import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.MorreyEmbedding
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.SobolevSmoothingAndDensity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.C1DomainExtension
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Batteries.Tactic.OpenPrivate

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ExpandedFA.Sobolev.Morrey
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

open HalfSpace
open private firstJetCoordinate firstJetCoordinate_spec firstJetCoordinate_coordinate
  from MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.HalfSpaceExtension

/-- The nonzero degree-one multi-indices are precisely the d coordinate
derivatives, with no multiplicities. -/
def coordinateGradientEquiv (d : ℕ) : Fin d ≃ GradientIndex d where
  toFun j := ⟨coordinateIndex j, coordinateIndex_ne_zero j⟩
  invFun α := firstJetCoordinate α.val α.property
  left_inv j := firstJetCoordinate_coordinate j _
  right_inv α := Subtype.ext (firstJetCoordinate_spec α.val α.property).symm

theorem gradient_norm_sq (u : SpaceValue 𝕜 d Ω 1 p) (x : Domain d) :
    ‖gradient u x‖ ^ 2 = ∑ j : Fin d, ‖u.val (coordinateIndex j) x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact ((coordinateGradientEquiv d).sum_comp
    (fun α : GradientIndex d => ‖u.val α.val x‖ ^ 2)).symm

theorem gradient_memLp (u : SpaceValue 𝕜 d Ω 1 p) :
    MemLp (gradient u) p (volume.restrict (Ω : Set (Domain d))) :=
  memLp_piLp_iff.mpr (fun α => Lp.memLp (u.val α.val))

theorem gradientNorm_nonneg (u : SpaceValue 𝕜 d Ω 1 p) : 0 ≤ gradientNorm u :=
  ENNReal.toReal_nonneg

theorem gradient_pointwise_le (u : SpaceValue 𝕜 d Ω 1 p) (x : Domain d) :
    ‖gradient u x‖ ≤ ∑ α : GradientIndex d, ‖u.val α.val x‖ := by
  classical
  have heq : gradient u x = ∑ α : GradientIndex d,
      PiLp.single 2 α (u.val α.val x) := by
    ext α
    simp [gradient]
  rw [heq]
  exact (norm_sum_le _ _).trans_eq (by simp)

/-- The Euclidean gradient norm is controlled by the fixed Sobolev sum norm.
The deliberately harmless cardinal factor avoids changing the upstream norm. -/
theorem gradientNorm_le (u : SpaceValue 𝕜 d Ω 1 p) :
    gradientNorm u ≤ Fintype.card (GradientIndex d) * ‖u‖ := by
  classical
  let μ := volume.restrict (Ω : Set (Domain d))
  have hsum : (∑ α : GradientIndex d, eLpNorm (u.val α.val) p μ) ≠ ∞ :=
    ne_of_lt (ENNReal.sum_lt_top.mpr (fun α _ => Lp.memLp (u.val α.val)))
  have hbound : eLpNorm (gradient u) p μ ≤
      ∑ α : GradientIndex d, eLpNorm (u.val α.val) p μ := by
    calc
      eLpNorm (gradient u) p μ ≤
          eLpNorm (fun x => ∑ α : GradientIndex d, ‖u.val α.val x‖) p μ :=
        eLpNorm_mono (gradient_memLp u).aestronglyMeasurable (fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
          exact gradient_pointwise_le u x)
      _ ≤ ∑ α : GradientIndex d, eLpNorm (fun x => ‖u.val α.val x‖) p μ := by
        simpa only [Finset.sum_apply, Finset.sum_fn] using
          (eLpNorm_sum_le (f := fun α : GradientIndex d => fun x => ‖u.val α.val x‖)
            (s := Finset.univ) (p := p) (μ := μ) Fact.out)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro α _
        exact eLpNorm_norm _ (Lp.aestronglyMeasurable (u.val α.val))
  calc
    gradientNorm u ≤ (∑ α : GradientIndex d, eLpNorm (u.val α.val) p μ).toReal :=
      ENNReal.toReal_mono hsum hbound
    _ = ∑ α : GradientIndex d, ‖u.val α.val‖ := by
      rw [ENNReal.toReal_sum (fun α _ => (Lp.memLp (u.val α.val)).eLpNorm_ne_top)]
      rfl
    _ ≤ ∑ _ : GradientIndex d, ‖u‖ :=
      Finset.sum_le_sum (fun α _ => PiLp.norm_apply_le u.val α.val)
    _ = _ := by simp

def gradientLp (u : SpaceValue 𝕜 d Ω 1 p) :
    Lp (PiLp 2 (fun _ : GradientIndex d => 𝕜)) p
      (volume.restrict (Ω : Set (Domain d))) :=
  (gradient_memLp u).toLp (gradient u)

theorem gradientLp_coe (u : SpaceValue 𝕜 d Ω 1 p) :
    gradientLp u =ᵐ[volume.restrict (Ω : Set (Domain d))] gradient u :=
  MemLp.coeFn_toLp (gradient_memLp u)

theorem gradientLp_norm (u : SpaceValue 𝕜 d Ω 1 p) :
    ‖gradientLp u‖ = gradientNorm u :=
  Lp.norm_toLp _ _

theorem gradient_component_norm_le (u : SpaceValue 𝕜 d Ω 1 p) (α : GradientIndex d) :
    ‖u.val α.val‖ ≤ gradientNorm u := by
  rw [← gradientLp_norm]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [gradientLp_coe u] with x hx
  rw [hx]
  exact PiLp.norm_apply_le (gradient u x) α

def gradientLM : SpaceValue 𝕜 d Ω 1 p →ₗ[𝕜]
    Lp (PiLp 2 (fun _ : GradientIndex d => 𝕜)) p
      (volume.restrict (Ω : Set (Domain d))) where
  toFun := gradientLp
  map_add' u v := by
    apply Lp.ext
    have h := ae_all_iff.mpr (fun α : GradientIndex d => Lp.coeFn_add (u.val α.val) (v.val α.val))
    filter_upwards [gradientLp_coe (u + v), gradientLp_coe u, gradientLp_coe v,
      Lp.coeFn_add (gradientLp u) (gradientLp v), h] with x huv hu hv hadd hx
    rw [huv, hadd]
    change gradient (u + v) x = (gradientLp u : Domain d → _) x + (gradientLp v : Domain d → _) x
    rw [hu, hv]
    ext α
    exact hx α
  map_smul' c u := by
    apply Lp.ext
    have h := ae_all_iff.mpr (fun α : GradientIndex d => Lp.coeFn_smul c (u.val α.val))
    filter_upwards [gradientLp_coe (c • u), gradientLp_coe u,
      Lp.coeFn_smul c (gradientLp u), h] with x hcu hu hsmul hx
    change (gradientLp (c • u) : Domain d → _) x = (c • gradientLp u : Lp _ p _) x
    rw [hcu, hsmul]
    change gradient (c • u) x = c • (gradientLp u : Domain d → _) x
    rw [hu]
    ext α
    exact hx α

def gradientCLM : SpaceValue 𝕜 d Ω 1 p →L[𝕜]
    Lp (PiLp 2 (fun _ : GradientIndex d => 𝕜)) p
      (volume.restrict (Ω : Set (Domain d))) :=
  (gradientLM (𝕜 := 𝕜) (Ω := Ω) (p := p)).mkContinuous (Fintype.card (GradientIndex d)) (fun u => by
    simpa only [gradientLM, LinearMap.coe_mk, AddHom.coe_mk, gradientLp_norm]
      using gradientNorm_le u)

theorem gradientNorm_continuous :
    Continuous (gradientNorm : SpaceValue 𝕜 d Ω 1 p → ℝ) :=
  by
    have h := (gradientCLM (𝕜 := 𝕜) (Ω := Ω) (p := p)).continuous.norm
    simpa only [gradientCLM, LinearMap.mkContinuous_apply, gradientLM, LinearMap.coe_mk,
      AddHom.coe_mk, gradientLp_norm] using h

theorem representative_unique (u : SpaceValue 𝕜 d Ω 1 p) (f g : Domain d → 𝕜)
    (hf : Continuous f) (hg : Continuous g) (huf : Represents u f) (hug : Represents u g) :
    EqOn f g (closure (Ω : Set (Domain d))) := by
  have hfg : EqOn f g (Ω : Set (Domain d)) :=
    Measure.eqOn_open_of_ae_eq (huf.symm.trans hug) Ω.isOpen hf.continuousOn hg.continuousOn
  exact hfg.closure hf hg

theorem exponent_top (d : ℕ) : exponent d ∞ = 1 := by simp [exponent]

theorem exponent_pos (hdp : (d : ℝ≥0∞) < p) : 0 < exponent d p := by
  by_cases hp : p = ∞
  · subst p
    simp only [exponent_top, zero_lt_one]
  · have hp0 : 0 < p.toReal := ENNReal.toReal_pos
        (ne_of_gt ((show (0 : ℝ≥0∞) ≤ d from bot_le).trans_lt hdp)) hp
    have hdp' : (d : ℝ) < p.toReal := by
      have := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hdp
      simpa using this
    exact sub_pos.mpr ((div_lt_one hp0).mpr hdp')

theorem euclideanNorm_continuous : Continuous (@euclideanNorm d) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).norm

theorem euclideanNorm_le (x : Domain d) : euclideanNorm x ≤ (d : ℝ) * ‖x‖ := by
  classical
  have heq : WithLp.toLp 2 x = ∑ i : Fin d, PiLp.single 2 i (x i) := by
    ext i
    simp
  calc
    euclideanNorm x ≤ ∑ i : Fin d, ‖x i‖ := by
      unfold euclideanNorm
      rw [heq]
      exact (norm_sum_le _ _).trans_eq (by simp)
    _ ≤ ∑ _ : Fin d, ‖x‖ := Finset.sum_le_sum (fun i _ => norm_le_pi_norm x i)
    _ = _ := by simp

/-- A Euclidean Hölder bound on a subset gives uniform continuity in the
canonical product topology used by the accepted Sobolev interface. -/
theorem uniformContinuousOn_of_bound {s : Set (Domain d)} {f : Domain d → 𝕜}
    {K a : ℝ} (hK : 0 ≤ K) (ha : 0 < a)
    (h : ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ ≤ K * euclideanNorm (x - y) ^ a) :
    UniformContinuousOn f s := by
  let B : ℝ≥0 := ⟨K * (d : ℝ) ^ a, mul_nonneg hK (Real.rpow_nonneg (Nat.cast_nonneg _) _)⟩
  let r : ℝ≥0 := ⟨a, ha.le⟩
  have hh : HolderOnWith B r f s := by
    intro x hx y hy
    have hreal : dist (f x) (f y) ≤ B * dist x y ^ a := by
      rw [dist_eq_norm, dist_eq_norm]
      calc
        ‖f x - f y‖ ≤ K * euclideanNorm (x - y) ^ a := h x hx y hy
        _ ≤ K * ((d : ℝ) * ‖x - y‖) ^ a :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) (euclideanNorm_le _) ha.le) hK
        _ = _ := by rw [Real.mul_rpow (Nat.cast_nonneg _) (norm_nonneg _)]; exact (mul_assoc _ _ _).symm
    rw [edist_dist, edist_dist]
    change ENNReal.ofReal (dist (f x) (f y)) ≤
      (B : ℝ≥0∞) * ENNReal.ofReal (dist x y) ^ a
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_rpow_of_nonneg dist_nonneg ha.le,
      ← ENNReal.ofReal_mul B.coe_nonneg]
    exact ENNReal.ofReal_le_ofReal hreal
  exact hh.uniformContinuousOn ha

/-- Extend a bound from an a.e. set to every point, preserving its constant.
This is the representative-construction step shared by finite p and infinity. -/
theorem continuous_representative_of_ae_bound (u : SpaceValue 𝕜 d ⊤ 1 p)
    {K a : ℝ} (hK : 0 ≤ K) (ha : 0 < a) (s : Set (Domain d))
    (hs : ∀ᵐ x ∂volume, x ∈ s)
    (hbound : ∀ x ∈ s, ∀ y ∈ s,
      ‖u.val (zeroIndex d 1) x - u.val (zeroIndex d 1) y‖ ≤ K * euclideanNorm (x - y) ^ a) :
    ∃ f : Domain d → 𝕜, Continuous f ∧ Represents u f ∧
      ∀ x y, ‖f x - f y‖ ≤ K * euclideanNorm (x - y) ^ a := by
  have hdense : Dense s := Measure.dense_of_ae hs
  let g : s → 𝕜 := fun x => u.val (zeroIndex d 1) x
  have hg : UniformContinuous g :=
    uniformContinuousOn_iff_restrict.mp (uniformContinuousOn_of_bound hK ha hbound)
  let f := hdense.extend g
  have hf : Continuous f := (hdense.uniformContinuous_extend hg).continuous
  have heq : ∀ x ∈ s, f x = u.val (zeroIndex d 1) x :=
    fun x hx => hdense.extend_eq hg.continuous ⟨x, hx⟩
  refine ⟨f, hf, ?_, fun x y => ?_⟩
  · change u.val (zeroIndex d 1) =ᵐ[volume.restrict (Set.univ : Set (Domain d))] f
    rw [Measure.restrict_univ]
    exact hs.mono (fun x hx => (heq x hx).symm)
  · have hclosed : IsClosed {z : Domain d × Domain d |
        ‖f z.1 - f z.2‖ ≤ K * euclideanNorm (z.1 - z.2) ^ a} :=
      isClosed_le ((hf.comp continuous_fst).sub (hf.comp continuous_snd)).norm
        (continuous_const.mul ((euclideanNorm_continuous.comp
          (continuous_fst.sub continuous_snd)).rpow_const
            (fun z => Or.inr ha.le)))
    change (x, y) ∈ {z : Domain d × Domain d |
      ‖f z.1 - f z.2‖ ≤ K * euclideanNorm (z.1 - z.2) ^ a}
    apply closure_minimal (t := {z : Domain d × Domain d |
        ‖f z.1 - f z.2‖ ≤ K * euclideanNorm (z.1 - z.2) ^ a}) ?_ hclosed
      (by rw [(hdense.prod hdense).closure_eq]; trivial)
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    change ‖f x - f y‖ ≤ _
    rw [heq x hx, heq y hy]
    exact hbound x hx y hy

/-- The product norm on the source is dominated by the Euclidean norm. -/
theorem norm_le_euclideanNorm (x : Domain d) : ‖x‖ ≤ euclideanNorm x := by
  apply (pi_norm_le_iff_of_nonneg (show 0 ≤ euclideanNorm x from norm_nonneg _)).mpr
  intro i
  exact PiLp.norm_apply_le (WithLp.toLp 2 x) i

/-- A coordinate of the first classical jet is the ordinary directional derivative. -/
theorem classicalDerivative_coordinateIndex (i : Fin d) (f : Domain d → 𝕜) :
    Smoothing.classicalDerivative (coordinateIndex i) f =
      fun x => fderiv ℝ f x (coordinateVector i) := by
  simp only [Smoothing.classicalDerivative, coordinateIndex, natIndex_boundedIndex,
    Lines.multiIndexWord_single, List.reverse_singleton, partialFunction]

/-- Whole-space regularization commutes with every weak derivative at every
positive scale. There are no boundary support restrictions in this case. -/
theorem regularize_derivative_identity_whole (ρ : Domain d → ℝ)
    (hρ : SmoothApproximateIdentitiesSpec.IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    (u : SpaceValue 𝕜 d ⊤ 1 p) (α : DerivativeIndex d 1) (x : Domain d) :
    Smoothing.classicalDerivative α (Smoothing.regularize ρ ε (u.val (zeroIndex d 1))) x =
      Smoothing.regularize ρ ε (u.val α) x := by
  rw [Smoothing.regularize_eq_kernelTest ρ hρ hε,
    Smoothing.regularize_eq_kernelTest ρ hρ hε]
  exact Smoothing.interior_convolution_identity u α _ x (subset_univ _)

/-- Hölder's inequality bounds each mollified Lp function pointwise, for
finite and infinite p, using the conjugate-exponent norm of the actual kernel. -/
theorem regularize_norm_le_lp (ρ : Domain d → ℝ)
    (hρ : SmoothApproximateIdentitiesSpec.IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    (u : DomainLp 𝕜 Ω p) (x : Domain d) :
    ‖Smoothing.regularize ρ ε u x‖ ≤
      (eLpNorm (SmoothApproximateIdentitiesSpec.ScaledKernelValue ρ ε)
        p.conjExponent volume).toReal * ‖u‖ := by
  have hk := scaledKernel_properties ρ hρ ε hε
  have hkm : MemLp (SmoothApproximateIdentitiesSpec.ScaledKernelValue ρ ε)
      p.conjExponent volume := hk.1.continuous.memLp_of_hasCompactSupport hk.2.1
  have hbound := enorm_convolution_le (p := p.conjExponent) (q := p)
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] 𝕜 →L[ℝ] 𝕜)
    hk.1.continuous.aestronglyMeasurable (Smoothing.zeroExtend_memLp u).aestronglyMeasurable x
  have hbound' : ‖Smoothing.regularize ρ ε u x‖ₑ ≤
      eLpNorm (SmoothApproximateIdentitiesSpec.ScaledKernelValue ρ ε) p.conjExponent volume *
        ENNReal.ofReal ‖u‖ := by
    calc
      _ ≤ ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] 𝕜 →L[ℝ] 𝕜)‖ₑ *
          eLpNorm (SmoothApproximateIdentitiesSpec.ScaledKernelValue ρ ε) p.conjExponent volume *
            ENNReal.ofReal ‖u‖ := by
        simpa only [Smoothing.regularize, SmoothApproximateIdentitiesSpec.MollifyValue,
          Smoothing.zeroExtend_eLpNorm] using hbound
      _ ≤ 1 * eLpNorm (SmoothApproximateIdentitiesSpec.ScaledKernelValue ρ ε)
          p.conjExponent volume * ENNReal.ofReal ‖u‖ := by
        gcongr
        exact ContinuousLinearMap.opENorm_lsmul_le
      _ = _ := by rw [one_mul]
  have ht := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hkm.eLpNorm_ne_top ENNReal.ofReal_ne_top) hbound'
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _),
    enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm] using ht

/-- Mollification converges pointwise to each continuous representative. -/
theorem regularize_tendsto_of_rep (ρ : Domain d → ℝ)
    (hρ : SmoothApproximateIdentitiesSpec.IsMollifier ρ)
    (u : SpaceValue 𝕜 d ⊤ 1 p) (f : Domain d → 𝕜)
    (hf : Continuous f) (hrep : Represents u f) (x : Domain d) :
    Tendsto (fun ε => Smoothing.regularize ρ ε (u.val (zeroIndex d 1)) x)
      (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  have hae : Smoothing.zeroExtend (u.val (zeroIndex d 1)) =ᵐ[volume] f := by
    simpa only [Smoothing.zeroExtend, Opens.coe_top, Set.indicator_univ,
      Represents, Measure.restrict_univ] using hrep
  have heq (ε : ℝ) : Smoothing.regularize ρ ε (u.val (zeroIndex d 1)) =
      SmoothApproximateIdentitiesSpec.MollifyValue ρ ε f :=
    convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) EventuallyEq.rfl hae
  simpa only [heq] using
    (mollify_locallyUniform ρ hρ f hf {x} isCompact_singleton).tendsto_at (mem_singleton x)

/-- Dilation law for the kernel norm, expressed in real numbers and valid
also when the norm exponent is infinity. -/
theorem scaledKernel_lpNorm (ρ : Domain d → ℝ) (hρ : Continuous ρ)
    {ε : ℝ} (hε : 0 < ε) (q : ℝ≥0∞) :
    (eLpNorm (SmoothApproximateIdentitiesSpec.ScaledKernelValue ρ ε) q volume).toReal =
      ε ^ ((d : ℝ) / q.toReal - d) * (eLpNorm ρ q volume).toReal := by
  have hmap : Measure.map (fun x : Domain d => ε⁻¹ • x) volume =
      ENNReal.ofReal (ε ^ d) • volume := by
    rw [Measure.map_addHaar_smul volume (inv_ne_zero hε.ne')]
    simp only [Module.finrank_pi, Fintype.card_fin, inv_pow, inv_inv,
      abs_of_nonneg (pow_nonneg hε.le d)]
  have hcomp : (eLpNorm (fun x : Domain d => ρ (ε⁻¹ • x)) q volume).toReal =
      (ε ^ d) ^ (1 / q.toReal) * (eLpNorm ρ q volume).toReal := by
    change (eLpNorm (ρ ∘ (fun x : Domain d => ε⁻¹ • x)) q volume).toReal = _
    rw [← eLpNorm_map_measure hρ.aestronglyMeasurable (by fun_prop), hmap,
      eLpNorm_smul_measure_of_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hε d)))]
    simp only [one_div, ENNReal.toReal_inv, smul_eq_mul, ENNReal.toReal_mul,
      ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (pow_nonneg hε.le d)]
  change (eLpNorm ((ε ^ d)⁻¹ • (fun x : Domain d => ρ (ε⁻¹ • x))) q volume).toReal = _
  rw [eLpNorm_const_smul, ENNReal.toReal_mul, enorm_eq_nnnorm, ENNReal.coe_toReal,
    coe_nnnorm, Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg hε.le d)), hcomp]
  rw [← Real.rpow_natCast_mul hε.le, ← Real.rpow_natCast ε d, ← Real.rpow_neg hε.le]
  rw [← mul_assoc, ← Real.rpow_add hε]
  congr 2
  ring

/-- Conjugate exponents have the expected reciprocal sum, even at both endpoints. -/
theorem reciprocal_conjugate_sum (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    1 / p.toReal + 1 / p.conjExponent.toReal = 1 := by
  have h := congrArg ENNReal.toReal (ENNReal.HolderConjugate.inv_add_inv_eq_one p p.conjExponent)
  simpa only [ENNReal.toReal_add (ENNReal.inv_ne_top.mpr (ENNReal.HolderConjugate.ne_zero p p.conjExponent))
      (ENNReal.inv_ne_top.mpr (ENNReal.HolderConjugate.ne_zero p.conjExponent p)),
    ENNReal.toReal_inv, ENNReal.toReal_one, one_div] using h

/-- Bounds for coordinate derivatives control the full derivative in the
product norm. The dimension factor is sufficient for the Morrey constant. -/
theorem fderiv_norm_le_of_coordinates (f : Domain d → 𝕜) (x : Domain d)
    {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ i : Fin d, ‖fderiv ℝ f x (coordinateVector i)‖ ≤ M) :
    ‖fderiv ℝ f x‖ ≤ (d : ℝ) * M := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hM)
  intro v
  have hv : v = ∑ i : Fin d, v i • coordinateVector i := by
    ext j
    simp [coordinateVector, Pi.single_apply, mul_ite]
  calc
    ‖fderiv ℝ f x v‖ = ‖∑ i : Fin d, v i • fderiv ℝ f x (coordinateVector i)‖ := by
      conv_lhs => rw [hv, map_sum]
      simp only [map_smul]
    _ ≤ ∑ i : Fin d, ‖v i • fderiv ℝ f x (coordinateVector i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin d, ‖v‖ * M := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (norm_le_pi_norm v i) (h i) (norm_nonneg _) (norm_nonneg _)
    _ = (d : ℝ) * M * ‖v‖ := by simp; ring

/-- At each scale, global mollification is Lipschitz with its finite-p
scaling bound, using only the weak gradient of the original class. -/
theorem regularize_lipschitz_lp (ρ : Domain d → ℝ)
    (hρ : SmoothApproximateIdentitiesSpec.IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    (u : SpaceValue 𝕜 d ⊤ 1 p) (x y : Domain d) :
    ‖Smoothing.regularize ρ ε (u.val (zeroIndex d 1)) x -
      Smoothing.regularize ρ ε (u.val (zeroIndex d 1)) y‖ ≤
      ((d : ℝ) * (eLpNorm ρ p.conjExponent volume).toReal * gradientNorm u) *
        ε ^ (-(d : ℝ) / p.toReal) * euclideanNorm (x - y) := by
  let B := (eLpNorm (SmoothApproximateIdentitiesSpec.ScaledKernelValue ρ ε)
    p.conjExponent volume).toReal
  have hB : 0 ≤ B := ENNReal.toReal_nonneg
  have hD : ∀ z, ‖fderiv ℝ (Smoothing.regularize ρ ε (u.val (zeroIndex d 1))) z‖ ≤
      (d : ℝ) * (B * gradientNorm u) := by
    intro z
    apply fderiv_norm_le_of_coordinates _ z (mul_nonneg hB (gradientNorm_nonneg u))
    intro i
    rw [← congrFun (classicalDerivative_coordinateIndex i
      (Smoothing.regularize ρ ε (u.val (zeroIndex d 1)))) z,
      regularize_derivative_identity_whole ρ hρ hε]
    exact (regularize_norm_le_lp ρ hρ hε _ z).trans
      (mul_le_mul_of_nonneg_left
        (gradient_component_norm_le u ⟨coordinateIndex i, coordinateIndex_ne_zero i⟩) hB)
  have hf := Smoothing.regularize_contDiff ρ hρ hε (u.val (zeroIndex d 1))
  have hb := (convex_univ : Convex ℝ (Set.univ : Set (Domain d))).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hf.differentiable (by simp) z) (fun z _ => hD z)
    (Set.mem_univ y) (Set.mem_univ x)
  have he : (d : ℝ) / p.conjExponent.toReal - d = -(d : ℝ) / p.toReal := by
    have h := reciprocal_conjugate_sum p
    calc
      (d : ℝ) / p.conjExponent.toReal - d =
          d * (1 / p.conjExponent.toReal - 1) := by ring
      _ = d * (-(1 / p.toReal)) := by rw [show 1 / p.conjExponent.toReal - 1 = -(1 / p.toReal) by linarith]
      _ = _ := by ring
  have hB' : B = ε ^ (-(d : ℝ) / p.toReal) * (eLpNorm ρ p.conjExponent volume).toReal := by
    dsimp only [B]
    rw [scaledKernel_lpNorm ρ hρ.1.continuous hε, he]
  apply hb.trans
  calc
    (d : ℝ) * (B * gradientNorm u) * ‖x - y‖ ≤
        (d : ℝ) * (B * gradientNorm u) * euclideanNorm (x - y) :=
      mul_le_mul_of_nonneg_left (norm_le_euclideanNorm _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hB (gradientNorm_nonneg u)))
    _ = _ := by rw [hB']; ring

section MollifierIncrements
open ContinuousLinearMap Function SmoothApproximateIdentitiesSpec
local notation "L" => (lsmul ℝ ℝ : ℝ →L[ℝ] 𝕜 →L[ℝ] 𝕜)
local notation "M" => (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)

theorem convolution_commute_compact (φ ψ : (Fin d → ℝ) → ℝ)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (f : (Fin d → ℝ) → 𝕜) (hf : LocallyIntegrable f volume) (x : Fin d → ℝ) :
    convolution φ (convolution ψ f L volume) L volume x =
      convolution ψ (convolution φ f L volume) L volume x := by
  have hassoc (φ ψ : (Fin d → ℝ) → ℝ)
      (hφ : Continuous φ) (hφc : HasCompactSupport φ)
      (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
      convolution (convolution φ ψ M volume) f L volume x =
        convolution φ (convolution ψ f L volume) L volume x := by
    apply convolution_assoc M L L L (fun a b c => by simp [smul_smul, mul_comm])
      hφ.aestronglyMeasurable hψ.aestronglyMeasurable hf.aestronglyMeasurable
    · exact Eventually.of_forall (hφc.convolutionExists_left M hφ hψ.locallyIntegrable)
    · exact Eventually.of_forall
        (hψc.norm.convolutionExists_left (mul ℝ ℝ) hψ.norm (fun z => (hf z).norm))
    · exact hφc.norm.convolutionExists_left (mul ℝ ℝ) hφ.norm
        (hψc.norm.continuous_convolution_left (mul ℝ ℝ) hψ.norm (fun z => (hf z).norm)).locallyIntegrable x
  rw [← hassoc φ ψ hφ hφc hψ hψc, ← hassoc ψ φ hψ hψc hφ hφc]
  have hcomm : convolution φ ψ M volume = convolution ψ φ M volume :=
    convolution_symm M (by ext; simp [mul_comm])
  rw [hcomm]

theorem convolution_displacement_bound (φ : (Fin d → ℝ) → ℝ)
    {R A : ℝ} (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hφ : support φ ⊆ Metric.ball 0 R) (hφpos : ∀ x, 0 ≤ φ x)
    (hφmass : ∫ x, φ x = 1) (g : (Fin d → ℝ) → 𝕜)
    (hg : AEStronglyMeasurable g volume)
    (hLip : ∀ x y, ‖g x - g y‖ ≤ A * ‖x - y‖) (x : Fin d → ℝ) :
    ‖convolution φ g L volume x - g x‖ ≤ A * R := by
  rw [← dist_eq_norm]
  apply dist_convolution_le (mul_nonneg hA hR) hφ hφpos hφmass hg
  intro y hy
  simpa only [dist_eq_norm] using
    (hLip y x).trans (mul_le_mul_of_nonneg_left
      (show ‖y - x‖ ≤ R by simpa only [dist_eq_norm] using (Metric.mem_ball.mp hy).le) hA)

theorem scaledKernel_support_subset {d : ℕ} (ρ : Space d → ℝ)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (hρ : support ρ ⊆ Metric.ball 0 R) :
    support (ScaledKernelValue ρ ε) ⊆ Metric.ball 0 (ε * R) := by
  intro y hy
  have hy' : ε⁻¹ • y ∈ support ρ := (mul_ne_zero_iff.mp hy).2
  have hnorm : ‖y‖ < ε * R := by
    calc
      ‖y‖ = ‖ε • (ε⁻¹ • y)‖ := by rw [smul_inv_smul₀ (ne_of_gt hε)]
      _ = ε * ‖ε⁻¹ • y‖ := by rw [norm_smul, Real.norm_of_nonneg hε.le]
      _ < ε * R := mul_lt_mul_of_pos_left (by simpa using hρ hy') hε
  simpa only [mem_ball_zero_iff] using hnorm

theorem convolution_increment_bound (φ ψ : (Fin d → ℝ) → ℝ)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    {R S A B : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hφs : support φ ⊆ Metric.ball 0 R) (hψs : support ψ ⊆ Metric.ball 0 S)
    (hφpos : ∀ x, 0 ≤ φ x) (hψpos : ∀ x, 0 ≤ ψ x)
    (hφmass : ∫ x, φ x = 1) (hψmass : ∫ x, ψ x = 1)
    (f : (Fin d → ℝ) → 𝕜) (hf : LocallyIntegrable f volume)
    (hFA : ∀ x y, ‖convolution φ f L volume x - convolution φ f L volume y‖ ≤ A * ‖x - y‖)
    (hFB : ∀ x y, ‖convolution ψ f L volume x - convolution ψ f L volume y‖ ≤ B * ‖x - y‖)
    (x : Fin d → ℝ) :
    ‖convolution φ f L volume x - convolution ψ f L volume x‖ ≤ A * S + B * R := by
  let z := convolution ψ (convolution φ f L volume) L volume x
  have hz : z = convolution φ (convolution ψ f L volume) L volume x :=
    convolution_commute_compact ψ φ hψ hψc hφ hφc f hf x
  calc
    ‖convolution φ f L volume x - convolution ψ f L volume x‖ ≤
        ‖convolution φ f L volume x - z‖ + ‖z - convolution ψ f L volume x‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ A * S + B * R := by
      apply add_le_add
      · rw [norm_sub_rev]
        exact convolution_displacement_bound ψ hS hA hψs hψpos hψmass
          _ (hφc.continuous_convolution_left L hφ hf).aestronglyMeasurable hFA x
      · rw [hz]
        exact convolution_displacement_bound φ hR hB hφs hφpos hφmass
          _ (hψc.continuous_convolution_left L hψ hf).aestronglyMeasurable hFB x

theorem regularize_increment_bound (ρ : Domain d → ℝ)
    (hρ : SmoothApproximateIdentitiesSpec.IsMollifier ρ)
    {R ε δ : ℝ} (hR : 0 < R)
    (hρs : support ρ ⊆ Metric.ball 0 R) (hε : 0 < ε) (hδ : 0 < δ)
    (u : SpaceValue 𝕜 d ⊤ 1 p) (x : Domain d) :
    ‖Smoothing.regularize ρ ε (u.val (zeroIndex d 1)) x -
      Smoothing.regularize ρ δ (u.val (zeroIndex d 1)) x‖ ≤
      ((d : ℝ) * (eLpNorm ρ p.conjExponent volume).toReal) * ((d : ℝ) * R) *
        gradientNorm u * (ε ^ (-(d : ℝ) / p.toReal) * δ +
          δ ^ (-(d : ℝ) / p.toReal) * ε) := by
  let C : ℝ := (d : ℝ) * (eLpNorm ρ p.conjExponent volume).toReal
  let θ : ℝ := -(d : ℝ) / p.toReal
  let F (ε : ℝ) := Smoothing.regularize ρ ε (u.val (zeroIndex d 1))
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg
  have hA (t : ℝ) (ht : 0 < t) : 0 ≤ C * gradientNorm u * t ^ θ * d :=
    mul_nonneg (mul_nonneg (mul_nonneg hC (gradientNorm_nonneg u))
      (Real.rpow_nonneg ht.le _)) (Nat.cast_nonneg _)
  have hlip (t : ℝ) (ht : 0 < t) : ∀ x y,
      ‖F t x - F t y‖ ≤ (C * gradientNorm u * t ^ θ * d) * ‖x - y‖ := by
    intro y z
    calc
      ‖F t y - F t z‖ ≤ C * gradientNorm u * t ^ θ * euclideanNorm (y - z) :=
        regularize_lipschitz_lp ρ hρ ht u y z
      _ ≤ C * gradientNorm u * t ^ θ * ((d : ℝ) * ‖y - z‖) :=
        mul_le_mul_of_nonneg_left (euclideanNorm_le _)
          (mul_nonneg (mul_nonneg hC (gradientNorm_nonneg u)) (Real.rpow_nonneg ht.le _))
      _ = _ := by ring
  have hkε := scaledKernel_properties ρ hρ ε hε
  have hkδ := scaledKernel_properties ρ hρ δ hδ
  have hb := convolution_increment_bound
    (SmoothApproximateIdentitiesSpec.ScaledKernelValue ρ ε)
    (SmoothApproximateIdentitiesSpec.ScaledKernelValue ρ δ)
    hkε.1.continuous hkε.2.1 hkδ.1.continuous hkδ.2.1
    (mul_nonneg hε.le hR.le) (mul_nonneg hδ.le hR.le) (hA ε hε) (hA δ hδ)
    (scaledKernel_support_subset ρ hR hε hρs)
    (scaledKernel_support_subset ρ hR hδ hρs)
    hkε.2.2.1 hkδ.2.2.1 hkε.2.2.2 hkδ.2.2.2
    (Smoothing.zeroExtend (u.val (zeroIndex d 1)))
    (Smoothing.zeroExtend_locallyIntegrable _) (hlip ε hε) (hlip δ hδ) x
  change ‖F ε x - F δ x‖ ≤ _ at hb ⊢
  convert hb using 1
  dsimp only [C, θ]
  ring

lemma dyadic_scale_algebra {ε b : ℝ} (hε : 0 < ε) :
    ε ^ (-b) * (ε / 2) + (ε / 2) ^ (-b) * ε =
      ((1 / 2 : ℝ) + (2 : ℝ) ^ b) * ε ^ (1 - b) := by
  have hp : ε ^ (-b) * ε = ε ^ (1 - b) := by
    calc
      ε ^ (-b) * ε = ε ^ (-b) * ε ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = ε ^ ((-b) + 1) := (Real.rpow_add hε _ _).symm
      _ = ε ^ (1 - b) := by congr 1; ring
  rw [Real.div_rpow hε.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
  calc
    ε ^ (-b) * (ε / 2) + ε ^ (-b) * 2 ^ b * ε =
        (1 / 2 + 2 ^ b) * (ε ^ (-b) * ε) := by ring
    _ = _ := by rw [hp]

theorem regularize_dyadic_bound (ρ : Domain d → ℝ)
    (hρ : SmoothApproximateIdentitiesSpec.IsMollifier ρ)
    {R ε : ℝ} (hR : 0 < R)
    (hρs : support ρ ⊆ Metric.ball 0 R) (hε : 0 < ε)
    (u : SpaceValue 𝕜 d ⊤ 1 p) (x : Domain d) :
    ‖Smoothing.regularize ρ ε (u.val (zeroIndex d 1)) x -
      Smoothing.regularize ρ (ε / 2) (u.val (zeroIndex d 1)) x‖ ≤
      (((d : ℝ) * (eLpNorm ρ p.conjExponent volume).toReal) * ((d : ℝ) * R) *
        ((1 / 2 : ℝ) + (2 : ℝ) ^ ((d : ℝ) / p.toReal))) *
          gradientNorm u * ε ^ exponent d p := by
  have h := regularize_increment_bound ρ hρ hR hρs hε (half_pos hε) u x
  rw [show -(d : ℝ) / p.toReal = -((d : ℝ) / p.toReal) by ring,
    dyadic_scale_algebra hε] at h
  convert h using 1
  dsimp only [exponent]
  ring

end MollifierIncrements

section Dyadic

variable {E : Type*} [NormedAddCommGroup E]

lemma dyadic_error_bound (F : ℝ → E) (f : E) {t a B : ℝ}
    (ht : 0 < t) (ha : 0 < a)
    (hincr : ∀ s > 0, ‖F s - F (s / 2)‖ ≤ B * s ^ a)
    (hlim : Tendsto F (𝓝[>] 0) (𝓝 f)) :
    ‖F t - f‖ ≤ B / (1 - (1 / 2 : ℝ) ^ a) * t ^ a := by
  let s : ℕ → ℝ := fun n => t * (1 / 2 : ℝ) ^ n
  have hspos : ∀ n, 0 < s n := fun n => mul_pos ht (pow_pos (by norm_num) _)
  have hsstep : ∀ n, s (n + 1) = s n / 2 := by
    intro n
    simp only [s, pow_succ]
    ring
  have hgeom : ∀ n, dist (F (s n)) (F (s (n + 1))) ≤
      (B * t ^ a) * ((1 / 2 : ℝ) ^ a) ^ n := by
    intro n
    rw [hsstep, dist_eq_norm]
    convert hincr (s n) (hspos n) using 1
    dsimp only [s]
    rw [Real.mul_rpow ht.le (by positivity), ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), mul_comm (n : ℝ) a, Real.rpow_mul (by norm_num)]
    rw [Real.rpow_natCast]; ring
  have hr : (1 / 2 : ℝ) ^ a < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) ha
  have hs0 : Tendsto s atTop (𝓝 (0 : ℝ)) := by
    convert (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1))) using 1 <;> simp [s]
  have hs : Tendsto s atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hs0, Filter.Eventually.of_forall hspos⟩
  have hb := dist_le_of_le_geometric_of_tendsto₀ ((1 / 2 : ℝ) ^ a) (B * t ^ a)
    hr hgeom (hlim.comp hs)
  simpa [s, dist_eq_norm, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hb

lemma dyadic_pair_bound (Fx Fy : ℝ → E) (fx fy : E) {r a B K : ℝ}
    (hr : 0 < r) (ha : 0 < a)
    (hincrx : ∀ s > 0, ‖Fx s - Fx (s / 2)‖ ≤ B * s ^ a)
    (hincry : ∀ s > 0, ‖Fy s - Fy (s / 2)‖ ≤ B * s ^ a)
    (hlimx : Tendsto Fx (𝓝[>] 0) (𝓝 fx))
    (hlimy : Tendsto Fy (𝓝[>] 0) (𝓝 fy))
    (hcross : ‖Fx r - Fy r‖ ≤ K * r ^ a) :
    ‖fx - fy‖ ≤ (2 * B / (1 - (1 / 2 : ℝ) ^ a) + K) * r ^ a := by
  have hx := dyadic_error_bound Fx fx hr ha hincrx hlimx
  have hy := dyadic_error_bound Fy fy hr ha hincry hlimy
  have htriangle : ‖fx - fy‖ ≤ ‖Fx r - fx‖ + ‖Fx r - Fy r‖ + ‖Fy r - fy‖ := by
    calc
      ‖fx - fy‖ = ‖(fx - Fx r) + (Fx r - Fy r) + (Fy r - fy)‖ := by congr 1; abel
      _ ≤ ‖fx - Fx r‖ + ‖Fx r - Fy r‖ + ‖Fy r - fy‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = _ := by rw [norm_sub_rev fx]
  calc
    ‖fx - fy‖ ≤ _ := htriangle
    _ ≤ B / (1 - (1 / 2 : ℝ) ^ a) * r ^ a + K * r ^ a +
        B / (1 - (1 / 2 : ℝ) ^ a) * r ^ a := add_le_add (add_le_add hx hcross) hy
    _ = _ := by ring

lemma dyadic_holder_bound {X : Type*} (r : X → X → ℝ)
    (hr0 : ∀ x y, 0 ≤ r x y) (hrpos : ∀ x y, x ≠ y → 0 < r x y)
    (F : ℝ → X → E) (f : X → E) {a A B N : ℝ}
    (ha : 0 < a) (hA : 0 ≤ A) (hB : 0 ≤ B) (hN : 0 ≤ N)
    (hincr : ∀ t > 0, ∀ x, ‖F t x - F (t / 2) x‖ ≤ A * N * t ^ a)
    (hlip : ∀ t > 0, ∀ x y, ‖F t x - F t y‖ ≤ B * N * t ^ (a - 1) * r x y)
    (hlim : ∀ x, Tendsto (fun t => F t x) (𝓝[>] 0) (𝓝 (f x))) :
    ∀ x y, ‖f x - f y‖ ≤
      (2 * A / (1 - (1 / 2 : ℝ) ^ a) + B) * N * r x y ^ a := by
  intro x y
  have hq : 0 < 1 - (1 / 2 : ℝ) ^ a := sub_pos.mpr
    (Real.rpow_lt_one (by norm_num) (by norm_num) ha)
  by_cases hxy : x = y
  · subst y
    rw [sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg
      (add_nonneg (div_nonneg (mul_nonneg (by norm_num) hA) hq.le) hB) hN)
      (Real.rpow_nonneg (hr0 x x) a)
  · have hr := hrpos x y hxy
    have hp : (r x y) ^ (a - 1) * r x y = (r x y) ^ a := by
      calc
        (r x y) ^ (a - 1) * r x y = (r x y) ^ (a - 1) * (r x y) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = (r x y) ^ ((a - 1) + 1) := (Real.rpow_add hr _ _).symm
        _ = _ := by congr 1; ring
    have hcross : ‖F (r x y) x - F (r x y) y‖ ≤ (B * N) * r x y ^ a := by
      exact (hlip (r x y) hr x y).trans_eq (by rw [mul_assoc, hp])
    have hb := dyadic_pair_bound (fun t => F t x) (fun t => F t y) (f x) (f y) hr ha
      (fun t ht => hincr t ht x) (fun t ht => hincr t ht y) (hlim x) (hlim y) hcross
    convert hb using 1
    ring

end Dyadic

/-- The smooth finite-p Morrey estimate follows by summing dyadic changes in
regularization scale and comparing mollified values at the distance scale. -/
theorem smooth_estimate : Specs.ExpandedFA.Sobolev.MorreyEmbedding.SmoothEstimate := by
  intro 𝕜 _ d p _ _ hdp
  obtain ⟨ρ, hρ⟩ := Smoothing.exists_mollifier d
  obtain ⟨R, hR, hRs⟩ := hρ.2.1.isBounded.subset_ball_lt 0 (0 : Domain d)
  have hρs : Function.support ρ ⊆ Metric.ball 0 R := (subset_tsupport ρ).trans hRs
  let B : ℝ := (d : ℝ) * (eLpNorm ρ p.conjExponent volume).toReal
  let A : ℝ := B * ((d : ℝ) * R) * ((1 / 2 : ℝ) + (2 : ℝ) ^ ((d : ℝ) / p.toReal))
  have hB : 0 ≤ B := mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg
  have hA : 0 ≤ A := mul_nonneg
    (mul_nonneg hB (mul_nonneg (Nat.cast_nonneg _) hR.le))
    (add_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _))
  have ha : 0 < exponent d p := exponent_pos hdp
  have hq : 0 < 1 - (1 / 2 : ℝ) ^ exponent d p := sub_pos.mpr
    (Real.rpow_lt_one (by norm_num) (by norm_num) ha)
  refine ⟨2 * A / (1 - (1 / 2 : ℝ) ^ exponent d p) + B,
    add_nonneg (div_nonneg (mul_nonneg (by norm_num) hA) hq.le) hB, ?_⟩
  intro u f hf huf
  apply dyadic_holder_bound (fun x y : Domain d => euclideanNorm (x - y))
    (fun x y => norm_nonneg _) (fun x y hxy =>
      (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)).trans_le (norm_le_euclideanNorm (x - y)))
    (fun t => Smoothing.regularize ρ t (u.val (zeroIndex d 1))) f
    ha hA hB (gradientNorm_nonneg u)
  · intro t ht x
    exact regularize_dyadic_bound ρ hρ hR hρs ht u x
  · intro t ht x y
    have he : exponent d p - 1 = -(d : ℝ) / p.toReal := by dsimp [exponent]; ring
    simpa only [he] using regularize_lipschitz_lp ρ hρ ht u x y
  · intro x
    exact regularize_tendsto_of_rep ρ hρ u f hf.continuous huf x

/-- The local infinity derivative bound gives a common Lipschitz estimate on
any compact ball, eventually as the mollification scale tends to zero. -/
theorem regularize_eventually_lipschitz (ρ : Domain d → ℝ)
    (hρ : SmoothApproximateIdentitiesSpec.IsMollifier ρ)
    (u : SpaceValue 𝕜 d ⊤ 1 ∞) (R : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x ∈ Metric.closedBall (0 : Domain d) R,
      ∀ y ∈ Metric.closedBall (0 : Domain d) R,
      ‖Smoothing.regularize ρ ε (u.val (zeroIndex d 1)) x -
        Smoothing.regularize ρ ε (u.val (zeroIndex d 1)) y‖ ≤
          (d : ℝ) * gradientNorm u * euclideanNorm (x - y) := by
  have hb := Smoothing.uniform_derivative_bounds 𝕜 d ⊤ 1 ρ hρ u
    (Metric.closedBall 0 R) (isCompact_closedBall 0 R) (subset_univ _)
  filter_upwards [hb, self_mem_nhdsWithin] with ε hε he x hx y hy
  have hf := Smoothing.regularize_contDiff ρ hρ (Set.mem_Ioi.mp he) (u.val (zeroIndex d 1))
  have hder : ∀ z ∈ Metric.closedBall (0 : Domain d) R,
      ‖fderiv ℝ (Smoothing.regularize ρ ε (u.val (zeroIndex d 1))) z‖ ≤
        (d : ℝ) * gradientNorm u := by
    intro z hz
    apply fderiv_norm_le_of_coordinates _ z (gradientNorm_nonneg u)
    intro i
    have hcoord := hε (coordinateIndex i) z hz
    rw [classicalDerivative_coordinateIndex] at hcoord
    exact hcoord.trans (gradient_component_norm_le u ⟨coordinateIndex i, coordinateIndex_ne_zero i⟩)
  exact ((convex_closedBall (0 : Domain d) R).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hf.differentiable (by simp) z) hder hy hx).trans
      (mul_le_mul_of_nonneg_left (norm_le_euclideanNorm (x - y))
        (mul_nonneg (Nat.cast_nonneg _) (gradientNorm_nonneg u)))

/-- The infinity endpoint follows from local L¹ approximation and the
uniform derivative bounds. A separate subsequence on each ball suffices:
intersecting their conull convergence sets gives one global pairwise bound. -/
theorem infinity_whole_space :
    Specs.ExpandedFA.Sobolev.MorreyEmbedding.InfinityWholeSpace := by
  intro 𝕜 _ d
  refine ⟨d, Nat.cast_nonneg _, fun u => ?_⟩
  obtain ⟨ρ, hρ⟩ := Smoothing.exists_mollifier d
  let F : ℝ → Domain d → 𝕜 := fun ε => Smoothing.regularize ρ ε (u.val (zeroIndex d 1))
  have hlocal (n : ℕ) : ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝[>] (0 : ℝ)) ∧
      ∀ᵐ x ∂volume.restrict (Metric.closedBall (0 : Domain d) (n : ℝ)),
        Tendsto (fun k => F (ε k) x) atTop (𝓝 (u.val (zeroIndex d 1) x)) := by
    have hconv := Smoothing.regularize_local_finite_tendsto ρ hρ (u.val (zeroIndex d 1))
      (isCompact_closedBall (0 : Domain d) (n : ℝ)) (subset_univ _) 1 le_rfl ENNReal.one_ne_top
    exact (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hconv).exists_seq_tendsto_ae'
  choose ε hε hconv using hlocal
  let s : Set (Domain d) := {x | ∀ n : ℕ, x ∈ Metric.closedBall (0 : Domain d) (n : ℝ) →
    Tendsto (fun k => F (ε n k) x) atTop (𝓝 (u.val (zeroIndex d 1) x))}
  have hs : ∀ᵐ x ∂volume, x ∈ s :=
    ae_all_iff.mpr (fun n => (ae_restrict_iff' measurableSet_closedBall).mp (hconv n))
  obtain ⟨f, hf, huf, hbound⟩ := continuous_representative_of_ae_bound u
    (mul_nonneg (Nat.cast_nonneg d) (gradientNorm_nonneg u)) zero_lt_one s hs (fun x hx y hy => by
      obtain ⟨n, hn⟩ := exists_nat_ge (max ‖x‖ ‖y‖)
      have hxball : x ∈ Metric.closedBall (0 : Domain d) (n : ℝ) := by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact (le_max_left _ _).trans hn
      have hyball : y ∈ Metric.closedBall (0 : Domain d) (n : ℝ) := by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact (le_max_right _ _).trans hn
      have hb := (hε n).eventually (regularize_eventually_lipschitz ρ hρ u (n : ℝ))
      apply le_of_tendsto_of_tendsto ((hx n hxball).sub (hy n hyball)).norm tendsto_const_nhds
      filter_upwards [hb] with k hk
      simpa only [Real.rpow_one] using hk x hxball y hyball)
  exact ⟨f, hf, huf, by simpa only [Real.rpow_one] using hbound⟩

/-- The one-dimensional primitive and Hölder theorem already give the full
Morrey estimate on the line, with constant one. -/
theorem one_dimension : Specs.ExpandedFA.Sobolev.MorreyEmbedding.OneDimension := by
  intro 𝕜 _ p _ hp u
  let v : OneDimensional.W1p 𝕜 ⊤ p := u
  obtain ⟨f, hf, hrep, hAC, hFTC⟩ :=
    OneDimensional.representative_existence 𝕜 ⊤ ordConnected_univ p v
  have hf' : Continuous f := by simpa only [Opens.coe_top, closure_univ, continuousOn_univ] using hf
  have hfirst : OneDimensional.firstIndex ≠ zeroIndex 1 1 := by
    intro h
    have he := congrArg (fun α : DerivativeIndex 1 1 => α.val 0) h
    norm_num [OneDimensional.firstIndex, zeroIndex] at he
  have hgrad : ‖OneDimensional.derivativeLp v‖ ≤ gradientNorm u :=
    gradient_component_norm_le u ⟨OneDimensional.firstIndex, hfirst⟩
  refine ⟨fun x => f (x 0), hf'.comp (continuous_apply 0), hrep, fun x y => ?_⟩
  have hb := OneDimensional.holder_estimate 𝕜 ⊤ ordConnected_univ p hp v f
    ⟨hf, hrep, hAC, hFTC⟩ (x 0) (by simp) (y 0) (by simp)
  have hnorm : |x 0 - y 0| ≤ euclideanNorm (x - y) := by
    simpa only [euclideanNorm, Pi.sub_apply, Real.norm_eq_abs] using
      PiLp.norm_apply_le (WithLp.toLp 2 (x - y)) 0
  have ha : 0 < exponent 1 p := exponent_pos (by simpa using hp)
  change ‖f (x 0) - f (y 0)‖ ≤ _
  have hb' : ‖f (x 0) - f (y 0)‖ ≤ ‖OneDimensional.derivativeLp v‖ *
      |x 0 - y 0| ^ exponent 1 p := by
    simpa only [exponent, Nat.cast_one, OneDimensional.reciprocalExponent] using hb
  exact hb'.trans (mul_le_mul hgrad
    (Real.rpow_le_rpow (abs_nonneg _) hnorm ha.le)
    (Real.rpow_nonneg (abs_nonneg _) _) (gradientNorm_nonneg u))

theorem whole_space_assembly : Specs.ExpandedFA.Sobolev.MorreyEmbedding.WholeSpaceAssembly := by
  intro hfin hinf 𝕜 _ d p _ hdp
  by_cases hp : p = ∞
  · subst p
    obtain ⟨C, hC, h⟩ := hinf 𝕜 d
    refine ⟨C, hC, fun u => ?_⟩
    obtain ⟨f, hf, huf, hbound⟩ := h u
    exact ⟨f, hf, huf, by simpa only [exponent_top, Real.rpow_one] using hbound⟩
  · exact hfin 𝕜 d p hp hdp

theorem extension_consequence : Specs.ExpandedFA.Sobolev.MorreyEmbedding.ExtensionConsequence := by
  intro hwhole 𝕜 _ d Ω p _ hdp E hE
  obtain ⟨C, hC, hwhole⟩ := hwhole 𝕜 d p hdp
  let N : ℝ := Fintype.card (GradientIndex d)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  refine ⟨C * N * ‖E‖, mul_nonneg (mul_nonneg hC hN) (norm_nonneg E), fun u => ?_⟩
  obtain ⟨f, hf, huf, hbound⟩ := hwhole (E u)
  have huf' : (E u).val (zeroIndex d 1) =ᵐ[volume] f := by
    simpa only [Represents, Opens.coe_top, Measure.restrict_univ] using huf
  refine ⟨f, hf, (hE u).symm.trans (ae_restrict_of_ae huf'), fun x _ y _ => ?_⟩
  have hgrad : gradientNorm (E u) ≤ N * (‖E‖ * ‖u‖) :=
    (gradientNorm_le (E u)).trans (mul_le_mul_of_nonneg_left (E.le_opNorm u) hN)
  calc
    ‖f x - f y‖ ≤ C * gradientNorm (E u) * euclideanNorm (x - y) ^ exponent d p := hbound x y
    _ ≤ C * (N * (‖E‖ * ‖u‖)) * euclideanNorm (x - y) ^ exponent d p :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgrad hC)
        (Real.rpow_nonneg (norm_nonneg _) _)
    _ = _ := by ring

theorem c1_consequence : Specs.ExpandedFA.Sobolev.MorreyEmbedding.C1Consequence := by
  intro hext 𝕜 _ d Ω hΩ hcomp p _ hdp
  obtain ⟨T, E, hE, _⟩ := C1Extension.extension_exists 𝕜 d Ω hΩ hcomp
  exact hext 𝕜 d Ω p hdp (E p) (hE p)

theorem halfSpace_consequence : Specs.ExpandedFA.Sobolev.MorreyEmbedding.HalfSpaceConsequence := by
  intro hext 𝕜 _ d a ha c p _ hdp
  obtain ⟨i, A, b, _, _, h⟩ := HalfSpace.affineHalfSpace_extension d a ha c
  obtain ⟨E, _, hE, _⟩ := h 𝕜 p
  exact hext 𝕜 d (HalfSpace.affineHalfSpace a c) p hdp E hE

theorem zero_dimension : Specs.ExpandedFA.Sobolev.MorreyEmbedding.ZeroDimension := by
  intro 𝕜 _ p _ u
  refine ⟨fun _ => u.val (zeroIndex 0 1) 0, continuous_const, ?_, fun x y => ?_⟩
  · exact Eventually.of_forall (fun x => congrArg (u.val (zeroIndex 0 1)) (Subsingleton.elim x 0))
  · simp

/-- Finite-p density, convergence in measure, and extension from a conull set
turn the smooth inequality into a representative of each Sobolev class. -/
theorem finite_density_consequence :
    Specs.ExpandedFA.Sobolev.MorreyEmbedding.FiniteDensityConsequence := by
  intro hsmooth 𝕜 _ d p _ hp hdp
  obtain ⟨C, hC, hbound⟩ := hsmooth 𝕜 d p hp hdp
  refine ⟨C, hC, fun u => ?_⟩
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp
    (Smoothing.smooth_density 𝕜 d ⊤ 1 p hp u)
  change ∀ n, ∃ f : Domain d → 𝕜, ContDiffOn ℝ (⊤ : ℕ∞) f Set.univ ∧
    (v n).val (zeroIndex d 1) =ᵐ[volume.restrict (Set.univ : Set (Domain d))] f at hv
  choose f hf hrep using hv
  simp only [contDiffOn_univ] at hf
  have hproj : Continuous (fun w : SpaceValue 𝕜 d ⊤ 1 p => w.val (zeroIndex d 1)) :=
    (PiLp.proj (𝕜 := 𝕜) 1 (fun _ : DerivativeIndex d 1 => DomainLp 𝕜 ⊤ p)
      (zeroIndex d 1)).continuous.comp continuous_subtype_val
  have hmeasure := tendstoInMeasure_of_tendsto_Lp ((hproj.tendsto u).comp hlim)
  have hmeasure' : TendstoInMeasure volume f atTop (u.val (zeroIndex d 1)) := by
    simpa only [Measure.restrict_univ] using hmeasure.congr_left hrep
  obtain ⟨ns, hns, hae⟩ := hmeasure'.exists_seq_tendsto_ae
  have hgrad : Tendsto (fun n => gradientNorm (v (ns n))) atTop (𝓝 (gradientNorm u)) :=
    ((gradientNorm_continuous.tendsto u).comp hlim).comp hns.tendsto_atTop
  let s : Set (Domain d) := {x | Tendsto (fun n => f (ns n) x) atTop
    (𝓝 (u.val (zeroIndex d 1) x))}
  obtain ⟨g, hg, hug, hgbound⟩ := continuous_representative_of_ae_bound u
    (mul_nonneg hC (gradientNorm_nonneg u)) (exponent_pos hdp) s hae (fun x hx y hy => by
      apply le_of_tendsto_of_tendsto (hx.sub hy).norm
        ((tendsto_const_nhds.mul hgrad).mul_const (euclideanNorm (x - y) ^ exponent d p))
      exact Eventually.of_forall (fun n => hbound (v (ns n)) (f (ns n)) (hf (ns n)) (hrep (ns n)) x y))
  exact ⟨g, hg, hug, hgbound⟩

/-- Assemble the two analytic ingredients with the extension-domain reductions. -/
theorem embedding_assembly : Specs.ExpandedFA.Sobolev.MorreyEmbedding.EmbeddingAssembly := by
  intro hsmooth hinfty
  have hwhole := whole_space_assembly (finite_density_consequence hsmooth) hinfty
  have hext := extension_consequence hwhole
  exact ⟨hwhole, hext, c1_consequence hext, halfSpace_consequence hext⟩

/-- The proved infinity endpoint reduces assembly to the smooth estimate. -/
theorem embedding_of_smooth_estimate :
    Specs.ExpandedFA.Sobolev.MorreyEmbedding.EmbeddingOfSmoothEstimate := by
  intro hsmooth
  exact embedding_assembly hsmooth infinity_whole_space

/-- Every first-order Sobolev class in the finite Morrey range has the required
continuous representative and the gradient-only Euclidean Hölder estimate. -/
theorem finite_whole_space :
    Specs.ExpandedFA.Sobolev.MorreyEmbedding.FiniteWholeSpace :=
  finite_density_consequence smooth_estimate

/-- Whole-space Morrey embedding, including the Lipschitz endpoint p=∞. -/
theorem whole_space : Specs.ExpandedFA.Sobolev.MorreyEmbedding.WholeSpace :=
  whole_space_assembly finite_whole_space infinity_whole_space

/-- Morrey regularity on every domain with a bounded Sobolev extension. -/
theorem extension_domains : Specs.ExpandedFA.Sobolev.MorreyEmbedding.ExtensionDomains :=
  extension_consequence whole_space

/-- The compact-boundary C¹ domains of the manuscript satisfy Morrey's estimate. -/
theorem c1_domains : Specs.ExpandedFA.Sobolev.MorreyEmbedding.C1Domains :=
  c1_consequence extension_domains

/-- The full-norm estimate also holds on every affine half-space. -/
theorem half_spaces : Specs.ExpandedFA.Sobolev.MorreyEmbedding.HalfSpaces :=
  halfSpace_consequence extension_domains

/-- All first-order Morrey conclusions of the assigned source clause. -/
theorem embedding : Specs.ExpandedFA.Sobolev.MorreyEmbedding.Embedding :=
  ⟨whole_space, extension_domains, c1_domains, half_spaces⟩

end ExpandedFA.Sobolev.Morrey
