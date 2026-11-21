import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.SubcriticalWhole
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.WholeSpaceDensity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.SubcriticalSobolevEmbedding

import MathGenome.Internal.FourierSobolev.P102.U4.WholeSpaceDensity
noncomputable section
open MeasureTheory TopologicalSpace Filter
open scoped ENNReal NNReal Topology ContDiff
namespace P102.Sobolev
open P102.U4

/-- Bound the operator norm using the actual Euclidean coordinate basis. -/
private theorem norm_linear_le_coordinates {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (A : Space d →L[ℝ] 𝕜) : ‖A‖ ≤ ∑ i, ‖A (coordinateVector d i)‖ := by
  classical
  apply A.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro x
  have hx : ∑ i, x i • coordinateVector d i = x :=
    (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x
  calc
    ‖A x‖ = ‖∑ i, x i • A (coordinateVector d i)‖ := by
      conv_lhs => rw [← hx]
      simp only [map_sum, map_smul]
    _ ≤ ∑ i, ‖x i • A (coordinateVector d i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖x‖ * ‖A (coordinateVector d i)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le x i) (norm_nonneg _)
    _ = (∑ i, ‖A (coordinateVector d i)‖) * ‖x‖ := by rw [← Finset.mul_sum, mul_comm]

private theorem norm_linear_le_gradient {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (A : Space d →L[ℝ] 𝕜) :
    ‖A‖ ≤ d * ‖(WithLp.toLp 2 (fun i => A (coordinateVector d i)) :
      EuclideanSpace 𝕜 (Fin d))‖ := by
  classical
  apply (norm_linear_le_coordinates A).trans
  calc
    _ ≤ ∑ _i : Fin d, ‖(WithLp.toLp 2 (fun i => A (coordinateVector d i)) :
        EuclideanSpace 𝕜 (Fin d))‖ :=
      Finset.sum_le_sum fun i _ => PiLp.norm_apply_le _ i
    _ = _ := by simp

theorem weakGradient_memLp {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : U4.Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p) :
    MemLp (weakGradient u) p volume := by
  apply ExpandedFA.Sobolev.Subcritical.euclideanTuple_memLp
  intro i
  simpa using Lp.memLp (sobolevDerivative u (firstIndex i))

private theorem compact_smooth_bound {d : ℕ} {p : ℝ≥0} (hd : 2 ≤ d)
    (hp : 1 ≤ p) (hpd : p < d) {𝕜 : Type} [RCLike 𝕜]
    (f : Space d → 𝕜) (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    eLpNorm f (criticalExponent d p) volume ≤
      ((eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Space d)) p * d : ℝ≥0) : ℝ≥0∞) *
        eLpNorm (fun x => (WithLp.toLp 2 (fun i => fderiv ℝ f x (coordinateVector d i)) :
          EuclideanSpace 𝕜 (Fin d))) p volume := by
  let : InnerProductSpace ℝ 𝕜 := RCLike.toInnerProductSpaceReal
  have hdim : Module.finrank ℝ (Space d) = d := by simp [Space]
  have hexp : (criticalExponent d p : ℝ)⁻¹ =
      (p : ℝ)⁻¹ - (Module.finrank ℝ (Space d) : ℝ)⁻¹ := by
    rw [hdim]
    exact ExpandedFA.Sobolev.Subcritical.criticalExponent_inv hp hpd
  have h := eLpNorm_le_eLpNorm_fderiv_of_eq_inner volume hf hs hp
    (by rw [hdim]; omega) hexp
  have hg := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    (g := fun x => (WithLp.toLp 2 (fun i => fderiv ℝ f x (coordinateVector d i)) : EuclideanSpace 𝕜 (Fin d)))
    (c := (d : ℝ≥0)) (μ := volume)
    (hf.continuous_fderiv one_ne_zero).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x =>
      show ‖fderiv ℝ f x‖₊ ≤ (d : ℝ≥0) * ‖(WithLp.toLp 2 (fun i => fderiv ℝ f x (coordinateVector d i)) : EuclideanSpace 𝕜 (Fin d))‖₊ from
        by exact_mod_cast norm_linear_le_gradient (fderiv ℝ f x)) (p : ℝ≥0∞)
  exact h.trans (by simpa only [ENNReal.coe_mul, ENNReal.coe_natCast, ENNReal.smul_def, smul_eq_mul, mul_assoc]
    using mul_le_mul_right hg (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Space d)) p : ℝ≥0∞))

private theorem tuple_eLpNorm_le_sum {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} (hp : 1 ≤ p)
    (g : Fin d → X → 𝕜) (hg : ∀ i, MemLp (g i) p μ) :
    eLpNorm (fun x => (WithLp.toLp 2 (fun i => g i x) : EuclideanSpace 𝕜 (Fin d))) p μ ≤
      ∑ i, eLpNorm (g i) p μ := by
  classical
  simp_rw [ExpandedFA.Sobolev.Subcritical.euclideanTuple_eq_sum]
  calc
    _ ≤ ∑ i, eLpNorm (fun x => EuclideanSpace.single i (g i x)) p μ := by
      simpa only [Finset.sum_apply, Finset.sum_fn] using
        (eLpNorm_sum_le (f := fun i x => EuclideanSpace.single i (g i x))
          (s := Finset.univ) (μ := μ) hp)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact eLpNorm_congr_norm_ae
        ((ExpandedFA.Sobolev.Subcritical.euclideanSingle_continuous i).comp_aestronglyMeasurable
          (hg i).aestronglyMeasurable) (hg i).aestronglyMeasurable
        (Eventually.of_forall fun x => PiLp.norm_single 2 (fun _ : Fin d => 𝕜) i (g i x))

private theorem gradient_bound {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u v : U4.Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p) :
    eLpNorm (weakGradient v) p volume ≤ eLpNorm (weakGradient u) p volume +
      ∑ i : Fin d, ENNReal.ofReal ‖sobolevDerivative v (firstIndex i) -
        sobolevDerivative u (firstIndex i)‖ := by
  let g (i : Fin d) : Space d → 𝕜 :=
    (sobolevDerivative v (firstIndex i) - sobolevDerivative u (firstIndex i) :
      DomainLp 𝕜 (⊤ : Opens (Space d)) p)
  have hg (i : Fin d) : MemLp (g i) p volume := by
    simpa [g] using Lp.memLp (sobolevDerivative v (firstIndex i) - sobolevDerivative u (firstIndex i))
  have heq : weakGradient v - weakGradient u =ᵐ[volume]
      (fun x => (WithLp.toLp 2 (fun i => g i x) : EuclideanSpace 𝕜 (Fin d))) := by
    have h (i : Fin d) : g i =ᵐ[volume]
        (fun x => sobolevDerivative v (firstIndex i) x - sobolevDerivative u (firstIndex i) x) := by
      exact (Lp.coeFn_sub (sobolevDerivative v (firstIndex i))
        (sobolevDerivative u (firstIndex i))).filter_mono (by simp)
    filter_upwards [ae_all_iff.mpr h] with x hx
    ext i
    exact (hx i).symm
  calc
    _ = eLpNorm (weakGradient u + (weakGradient v - weakGradient u)) p volume := by congr 1; abel
    _ ≤ eLpNorm (weakGradient u) p volume + eLpNorm (weakGradient v - weakGradient u) p volume :=
      eLpNorm_add_le Fact.out
    _ ≤ eLpNorm (weakGradient u) p volume + ∑ i, eLpNorm (g i) p volume := by
      rw [eLpNorm_congr_ae heq]
      exact add_le_add_right (tuple_eLpNorm_le_sum Fact.out g hg) _
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simpa [g, ofReal_norm] using (Lp.enorm_def
        (sobolevDerivative v (firstIndex i) - sobolevDerivative u (firstIndex i))).symm

/-- The approximation interface identifies every coordinate with the
classical derivative; finite a.e. intersections identify the Euclidean tuple. -/
private theorem represented_gradient {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : Space d → 𝕜)
    (v : U4.Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p) (h : RepresentsSobolev f v) :
    weakGradient v =ᵐ[volume]
      (fun x => (WithLp.toLp 2 (fun i => fderiv ℝ f x (coordinateVector d i)) :
        EuclideanSpace 𝕜 (Fin d))) := by
  have hi (i : Fin d) : (sobolevDerivative v (firstIndex i) : Space d → 𝕜) =ᵐ[volume]
      (fun x => fderiv ℝ f x (coordinateVector d i)) := by
    simpa [firstIndex, multiPartial, partialWord] using h (firstIndex i)
  filter_upwards [ae_all_iff.mpr hi] with x hx
  ext i
  exact hx i

private theorem derivative_norm_tendsto {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {v : ℕ → U4.Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p}
    {u : U4.Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p}
    (hv : Tendsto v atTop (𝓝 u)) (α : SobolevIndex d 1) :
    Tendsto (fun n => ENNReal.ofReal ‖sobolevDerivative (v n) α - sobolevDerivative u α‖)
      atTop (𝓝 0) := by
  have hc : Continuous (fun w : U4.Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p =>
      sobolevDerivative w α) :=
    (PiLp.proj (𝕜 := 𝕜) 1 (fun _ : SobolevIndex d 1 =>
      DomainLp 𝕜 (⊤ : Opens (Space d)) p) α).continuous.comp continuous_subtype_val
  have ht := (((hc.tendsto u).comp hv).sub
    (tendsto_const_nhds (x := sobolevDerivative u α))).norm
  simpa using ENNReal.tendsto_ofReal ht

/-- Conditional draft of the whole-space Sobolev estimate. The six frozen
premises are retained in the contract's order; only density is needed by this
proof route. This is not the closed original target. -/
theorem subcriticalWhole_conditional
    (_cutoff : WholeSpaceDensityExpected.Cutoff)
    (density : WholeSpaceDensityExpected.Density)
    (_mollification : WholeSpaceDensityExpected.Mollification)
    (_mollifierExistence : WholeSpaceDensityExpected.MollifierExistence)
    (_smoothTests : WholeSpaceDensityExpected.SmoothTests)
    (_weakMollification : WholeSpaceDensityExpected.WeakMollification) :
    SubcriticalWholeExpected.Inequality := by
  intro d hd p hp hpd
  let C : ℝ≥0 := eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Space d)) p * d
  refine ⟨C, ?_⟩
  intro 𝕜 _ _ u
  obtain ⟨φ, v, hrep, hv, _⟩ := density 1 p ENNReal.coe_ne_top u
  have hzero (n : ℕ) : (sobolevUnderlying (v n) : Space d → 𝕜) =ᵐ[volume] φ n := by
    simpa [sobolevUnderlying, zeroSobolevIndex, multiPartial, partialWord] using
      hrep n (zeroSobolevIndex d 1)
  have herror : Tendsto (fun n => ∑ i : Fin d,
      ENNReal.ofReal ‖sobolevDerivative (v n) (firstIndex i) -
        sobolevDerivative u (firstIndex i)‖) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ => derivative_norm_tendsto hv (firstIndex i))
  have hgrad := weakGradient_memLp u
  have hbound (n : ℕ) : eLpNorm (φ n) (criticalExponent d p) volume ≤
      (C : ℝ≥0∞) * (eLpNorm (weakGradient u) p volume + ∑ i : Fin d,
        ENNReal.ofReal ‖sobolevDerivative (v n) (firstIndex i) -
          sobolevDerivative u (firstIndex i)‖) := by
    have h := compact_smooth_bound hd hp hpd (φ n)
      ((φ n).contDiff.of_le (by simp)) (φ n).hasCompactSupport
    rw [← eLpNorm_congr_ae (represented_gradient (φ n) (v n) (hrep n))] at h
    exact h.trans (mul_le_mul_right (gradient_bound u (v n)) (C : ℝ≥0∞))
  have ht : Tendsto (fun n => eLpNorm ((φ n : Space d → 𝕜) - (sobolevUnderlying u : Space d → 𝕜)) p volume)
      atTop (𝓝 0) := by
    have heq (n : ℕ) :
        eLpNorm ((φ n : Space d → 𝕜) - (sobolevUnderlying u : Space d → 𝕜)) p volume =
          ENNReal.ofReal ‖sobolevDerivative (v n) (zeroSobolevIndex d 1) -
            sobolevDerivative u (zeroSobolevIndex d 1)‖ := by
      have hs : ((φ n : Space d → 𝕜) - (sobolevUnderlying u : Space d → 𝕜)) =ᵐ[volume]
          (sobolevUnderlying (v n) - sobolevUnderlying u :
            DomainLp 𝕜 (⊤ : Opens (Space d)) p) := by
        have hlp := Lp.coeFn_sub (sobolevUnderlying (v n)) (sobolevUnderlying u)
        simp only [Opens.coe_top, Measure.restrict_univ] at hlp
        filter_upwards [hzero n, hlp] with x hx hx'
        exact (congrArg (fun z => z - sobolevUnderlying u x) hx).symm.trans hx'.symm
      rw [eLpNorm_congr_ae hs]
      simpa [sobolevUnderlying, ofReal_norm] using (Lp.enorm_def
        (sobolevDerivative (v n) (zeroSobolevIndex d 1) -
          sobolevDerivative u (zeroSobolevIndex d 1))).symm
    simp_rw [heq]
    exact derivative_norm_tendsto hv (zeroSobolevIndex d 1)
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm
    (show (p : ℝ≥0∞) ≠ 0 by exact_mod_cast (lt_of_lt_of_le zero_lt_one hp).ne') ht).exists_seq_tendsto_ae
  have hlimits : Tendsto (fun n => (C : ℝ≥0∞) *
      (eLpNorm (weakGradient u) p volume + ∑ i : Fin d,
        ENNReal.ofReal ‖sobolevDerivative (v n) (firstIndex i) -
          sobolevDerivative u (firstIndex i)‖)) atTop
      (𝓝 ((C : ℝ≥0∞) * eLpNorm (weakGradient u) p volume)) := by
    simpa using ENNReal.Tendsto.const_mul
      (a := (C : ℝ≥0∞)) (tendsto_const_nhds.add herror) (Or.inr ENNReal.coe_ne_top)
  have huLp : MemLp (sobolevUnderlying u) p volume := by
    simpa using Lp.memLp (sobolevUnderlying u)
  have hfinal : eLpNorm (sobolevUnderlying u) (criticalExponent d p) volume ≤
      (C : ℝ≥0∞) * eLpNorm (weakGradient u) p volume :=
    ExpandedFA.Sobolev.Subcritical.eLpNorm_le_of_ae_tendsto_bounds
      (fun n => (φ (ns n)).continuous.aestronglyMeasurable)
      huLp.aestronglyMeasurable hae (hlimits.comp hns.tendsto_atTop)
      (fun n => hbound (ns n))
  exact ⟨hgrad,
    hfinal.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hgrad.eLpNorm_lt_top), hfinal⟩

end P102.Sobolev

theorem _root_.«P102».«Sobolev».«subcriticalWhole» : _root_.«P102».«Sobolev».«SubcriticalWholeExpected».«Inequality» :=
  @_root_.«P102».«Sobolev».«subcriticalWhole_conditional» (@_root_.«P102».«U4».«wholeSpace_cutoff») (@_root_.«P102».«U4».«wholeSpace_density») (@_root_.«P102».«U4».«wholeSpace_mollification») (@_root_.«P102».«U4».«wholeSpace_mollifierExistence») (@_root_.«P102».«U4».«wholeSpace_smoothTests») (@_root_.«P102».«U4».«wholeSpace_weakMollification»)
