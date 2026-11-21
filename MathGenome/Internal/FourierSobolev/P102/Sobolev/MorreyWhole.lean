import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.MorreyWhole
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.WholeSpaceDensity
import MathGenome.Internal.FourierSobolev.P102.U4.SobolevSpace
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.MorreyEmbedding
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.HigherSobolevEmbeddings

import MathGenome.Internal.FourierSobolev.P102.U4.WholeSpaceDensity
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal Topology
namespace P102.Sobolev.MorreyWhole
open P102.U4

variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace Bridge

abbrev Domain (d : ℕ) := ExpandedFA.Distributions.Domain d
abbrev MGIndex (d : ℕ) := ExpandedFA.Sobolev.DerivativeIndex d 1
abbrev MGSpace (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :=
  Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.SpaceValue 𝕜 d ⊤ 1 p

abbrev toEuclidean (d : ℕ) : Domain d ≃L[ℝ] Space d :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm

lemma toEuclidean_measurePreserving : MeasurePreserving (toEuclidean d)
    (volume.restrict (⊤ : Opens (Domain d))) (volume.restrict (⊤ : Opens (Space d))) := by
  simp only [Opens.coe_top, Measure.restrict_univ]
  exact PiLp.volume_preserving_toLp (Fin d)

def transferLp (u : DomainLp 𝕜 (⊤ : Opens (Space d)) p) :
    ExpandedFA.Sobolev.DomainLp 𝕜 (⊤ : Opens (Domain d)) p :=
  Lp.compMeasurePreserving (toEuclidean d) toEuclidean_measurePreserving u

lemma transferLp_coe (u : DomainLp 𝕜 (⊤ : Opens (Space d)) p) :
    transferLp u =ᵐ[volume] fun x => u (toEuclidean d x) := by
  have h := Lp.coeFn_compMeasurePreserving u (toEuclidean_measurePreserving (d := d))
  simpa only [transferLp, Opens.coe_top, Measure.restrict_univ, Function.comp_def] using h

lemma transferLp_norm (u : DomainLp 𝕜 (⊤ : Opens (Space d)) p) :
    ‖transferLp u‖ = ‖u‖ := Lp.norm_compMeasurePreserving _ _

lemma representative_unique (u : Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p)
    {f g : Space d → 𝕜} (hf : Continuous f) (hg : Continuous g)
    (huf : Represents u f) (hug : Represents u g) : f = g := by
  exact Measure.eq_of_ae_eq (huf.symm.trans hug) hf hg

def liftTest (φ : ExpandedFA.Distributions.Tests 𝕜 (⊤ : Opens (Domain d))) :
    TestSpace 𝕜 (⊤ : Opens (Space d)) :=
  ⟨φ ∘ (toEuclidean d).symm,
    φ.contDiff.comp (toEuclidean d).symm.contDiff,
    φ.hasCompactSupport.comp_homeomorph (toEuclidean d).symm.toHomeomorph,
    subset_univ _⟩

lemma liftTest_partial (φ : ExpandedFA.Distributions.Tests 𝕜 (⊤ : Opens (Domain d)))
    (i : Fin d) (x : Domain d) :
    fderiv ℝ (liftTest φ) (toEuclidean d x) (coordinateVector d i) =
      fderiv ℝ φ x (ExpandedFA.Distributions.coordinateVector i) := by
  change fderiv ℝ (φ ∘ (toEuclidean d).symm) (toEuclidean d x) _ = _
  rw [fderiv_comp _ (φ.contDiff.differentiable (by simp) _)
    (toEuclidean d).symm.differentiableAt]
  simp only [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.fderiv]
  congr 1
  ext j
  simp [toEuclidean, coordinateVector, ExpandedFA.Distributions.coordinateVector,
    EuclideanSpace.basisFun_apply, Pi.single_apply]

lemma transfer_integral (u : DomainLp 𝕜 (⊤ : Opens (Space d)) p)
    (f : Domain d → 𝕜) :
    (∫ x, f x * transferLp u x) = ∫ z, f ((toEuclidean d).symm z) * u z := by
  calc
    (∫ x, f x * transferLp u x) = ∫ x, f x * u (toEuclidean d x) := by
      apply integral_congr_ae
      filter_upwards [transferLp_coe u] with x hx
      rw [hx]
    _ = _ := by
      have hm : MeasurePreserving (toEuclidean d) volume volume :=
        PiLp.volume_preserving_toLp (Fin d)
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using
        hm.integral_comp (toEuclidean d).toHomeomorph.measurableEmbedding
          (fun z => f ((toEuclidean d).symm z) * u z)

lemma transfer_coordinate_weak
    (u : Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p) (i : Fin d) :
    ExpandedFA.Sobolev.lpDistribution (transferLp (sobolevDerivative u (firstIndex i))) =
      -(ExpandedFA.Sobolev.lpDistribution (transferLp (sobolevUnderlying u))).comp
        (ExpandedFA.Distributions.testPartialCLM [i]) := by
  ext φ
  simp only [ExpandedFA.Sobolev.lpDistribution_apply, Opens.coe_top,
    Measure.restrict_univ, neg_apply, ContinuousLinearMap.comp_apply]
  rw [transfer_integral, transfer_integral]
  have h := (mem_sobolevSubmodule_iff (⊤ : Opens (Space d)) 1 p u.val).mp
    u.property (firstIndex i) (liftTest φ)
  rw [lpTestPairing_eq_integral, lpTestPairing_eq_integral] at h
  simp only [Opens.coe_top, Measure.restrict_univ, firstIndex,
    Multiset.card_singleton, pow_one, neg_one_mul] at h
  change (∫ z, sobolevDerivative u (firstIndex i) z * liftTest φ z) = _ at h
  calc
    _ = ∫ z, sobolevDerivative u (firstIndex i) z * liftTest φ z := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => mul_comm _ _
    _ = _ := h
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        have hp := liftTest_partial φ i ((toEuclidean d).symm z)
        have he : (testPartialWord (⊤ : Opens (Space d)) [i] (liftTest φ)) z =
            (ExpandedFA.Distributions.testPartialCLM [i] φ) ((toEuclidean d).symm z) := by
          simpa only [ContinuousLinearEquiv.apply_symm_apply,
            ExpandedFA.Distributions.testPartial_single_apply, testPartialWord_coe,
            partialWord] using hp
        simp only [Multiset.sort_singleton, he]
        exact mul_comm _ _

/-- Reindex a first-order jet without inserting or dropping derivative entries. -/
def sourceIndex (α : MGIndex d) : SobolevIndex d 1 :=
  if h : α = ExpandedFA.Sobolev.zeroIndex d 1 then zeroSobolevIndex d 1
  else firstIndex ((ExpandedFA.Sobolev.Morrey.coordinateGradientEquiv d).symm ⟨α, h⟩)

@[simp] lemma sourceIndex_zero :
    sourceIndex (ExpandedFA.Sobolev.zeroIndex d 1) = zeroSobolevIndex d 1 := by
  simp [sourceIndex]

@[simp] lemma sourceIndex_coordinate (i : Fin d) :
    sourceIndex (ExpandedFA.Sobolev.HalfSpace.coordinateIndex i) = firstIndex i := by
  simp only [sourceIndex, ExpandedFA.Sobolev.HalfSpace.coordinateIndex_ne_zero, ↓reduceDIte]
  congr 1
  exact (ExpandedFA.Sobolev.Morrey.coordinateGradientEquiv d).symm_apply_apply i

def transferSobolev (u : Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p) : MGSpace 𝕜 d p :=
  ⟨WithLp.toLp 1 (fun α => transferLp (sobolevDerivative u (sourceIndex α))), by
    apply ExpandedFA.Sobolev.HalfSpace.firstJet_mem_of_coordinateWeak
    intro i
    simpa only [ sourceIndex_zero, sourceIndex_coordinate,
      sobolev_derivative_zero] using transfer_coordinate_weak u i⟩

@[simp] lemma transferSobolev_zero (u : Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p) :
    (transferSobolev u).val (ExpandedFA.Sobolev.zeroIndex d 1) =
      transferLp (sobolevUnderlying u) := by
  simp [transferSobolev, sobolevUnderlying, sobolevDerivative]

@[simp] lemma transferSobolev_coordinate (u : Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p)
    (i : Fin d) :
    (transferSobolev u).val (ExpandedFA.Sobolev.HalfSpace.coordinateIndex i) =
      transferLp (sobolevDerivative u (firstIndex i)) := by
  simp [transferSobolev]

lemma gradient_memLp (u : Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p) :
    MemLp (gradient u) p volume := by
  apply memLp_piLp_iff.mpr
  intro i
  simpa only [Opens.coe_top, Measure.restrict_univ, gradient] using
    Lp.memLp (sobolevDerivative u (firstIndex i))

lemma transfer_gradientNorm (u : Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p) :
    ExpandedFA.Sobolev.Morrey.gradientNorm (transferSobolev u) = gradientNorm u := by
  have hm : MeasurePreserving (toEuclidean d) volume volume :=
    PiLp.volume_preserving_toLp (Fin d)
  have hv : AEStronglyMeasurable
      (ExpandedFA.Sobolev.Morrey.gradient (transferSobolev u)) volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      (ExpandedFA.Sobolev.Morrey.gradient_memLp (transferSobolev u)).aestronglyMeasurable
  have hg := (gradient_memLp u).aestronglyMeasurable
  have hn : ∀ᵐ x ∂volume,
      ‖ExpandedFA.Sobolev.Morrey.gradient (transferSobolev u) x‖ =
        ‖gradient u (toEuclidean d x)‖ := by
    have hc := ae_all_iff.mpr (fun i : Fin d =>
      transferLp_coe (sobolevDerivative u (firstIndex i)))
    filter_upwards [hc] with x hx
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [ExpandedFA.Sobolev.Morrey.gradient_norm_sq, PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro i _
    rw [transferSobolev_coordinate, hx i]
    rfl
  have he := eLpNorm_congr_norm_ae (p := p) hv
    (hg.comp_measurePreserving hm) hn
  have he' := eLpNorm_comp_measurePreserving (p := p) hg hm
  simp only [ExpandedFA.Sobolev.Morrey.gradientNorm, Opens.coe_top,
    Measure.restrict_univ, gradientNorm]
  rw [he]
  exact congrArg ENNReal.toReal he'

lemma transfer_represents (u : Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p)
    (f : Domain d → 𝕜) (hf : ExpandedFA.Sobolev.Morrey.Represents (transferSobolev u) f) :
    Represents u (f ∘ (toEuclidean d).symm) := by
  have hf' : transferLp (sobolevUnderlying u) =ᵐ[volume] f := by
    simpa only [ExpandedFA.Sobolev.Morrey.Represents, Opens.coe_top,
      Measure.restrict_univ, transferSobolev_zero] using hf
  have he := (transferLp_coe (sobolevUnderlying u)).symm.trans hf'
  have hp := (PiLp.volume_preserving_ofLp (Fin d)).quasiMeasurePreserving.ae_eq_comp he
  simpa only [Represents, Function.comp_def, toEuclidean,
    ContinuousLinearEquiv.symm_symm, PiLp.coe_continuousLinearEquiv,
    PiLp.coe_symm_continuousLinearEquiv, WithLp.toLp_ofLp] using hp

lemma euclidean_distance (x y : Space d) :
    ExpandedFA.Sobolev.Morrey.euclideanNorm
      ((toEuclidean d).symm x - (toEuclidean d).symm y) = ‖x - y‖ := by
  change ‖toEuclidean d ((toEuclidean d).symm x - (toEuclidean d).symm y)‖ = _
  rw [map_sub, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply]

lemma jet_norm_le (v : MGSpace 𝕜 d p) :
    ‖v‖ ≤ Fintype.card (MGIndex d) *
      (‖v.val (ExpandedFA.Sobolev.zeroIndex d 1)‖ +
        ExpandedFA.Sobolev.Morrey.gradientNorm v) := by
  classical
  rw [ExpandedFA.Sobolev.sobolev_norm_formula]
  calc
    _ ≤ ∑ _ : MGIndex d, (‖v.val (ExpandedFA.Sobolev.zeroIndex d 1)‖ +
        ExpandedFA.Sobolev.Morrey.gradientNorm v) := by
      apply Finset.sum_le_sum
      intro α _
      by_cases hα : α = ExpandedFA.Sobolev.zeroIndex d 1
      · subst α
        exact le_add_of_nonneg_right (ExpandedFA.Sobolev.Morrey.gradientNorm_nonneg v)
      · exact (ExpandedFA.Sobolev.Morrey.gradient_component_norm_le v ⟨α, hα⟩).trans
          (le_add_of_nonneg_left (norm_nonneg _))
    _ = _ := by simp [mul_add]

lemma continuous_rep_norm_le (u : Sobolev 𝕜 (⊤ : Opens (Space d)) 1 ⊤)
    {f : Space d → 𝕜} (hf : Continuous f) (huf : Represents u f) :
    ∀ x, ‖f x‖ ≤ ‖sobolevUnderlying u‖ := by
  have hu : MemLp (sobolevUnderlying u) ⊤ volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp (sobolevUnderlying u)
  have hb : ∀ᵐ x ∂volume, ‖f x‖ ≤ ‖sobolevUnderlying u‖ := by
    have h := ae_le_lpNorm_exponent_top hu
    have hn : lpNorm (sobolevUnderlying u) ⊤ volume = ‖sobolevUnderlying u‖ := by
      simp only [Lp.norm_def, ← toReal_eLpNorm, Opens.coe_top, Measure.restrict_univ]
    filter_upwards [h, huf] with x hx he
    simpa only [he, hn] using hx
  have hd := Measure.dense_of_ae hb
  have hc : IsClosed {x | ‖f x‖ ≤ ‖sobolevUnderlying u‖} :=
    isClosed_le hf.norm continuous_const
  have hall : {x | ‖f x‖ ≤ ‖sobolevUnderlying u‖} = univ :=
    hc.closure_eq.symm.trans hd.closure_eq
  intro x
  have hx : x ∈ {x | ‖f x‖ ≤ ‖sobolevUnderlying u‖} := by rw [hall]; trivial
  exact hx

end Bridge

/-- Conditional draft of the finite-exponent whole-space Morrey theorem.
All frozen premises are retained in their contract order. The analytic input
used here is the independent MathGenome theorem, transported through `Bridge`. -/
theorem finite_conditional
    (_cutoff : WholeSpaceDensityExpected.Cutoff)
    (_density : WholeSpaceDensityExpected.Density)
    (_mollification : WholeSpaceDensityExpected.Mollification)
    (_mollifierExistence : WholeSpaceDensityExpected.MollifierExistence)
    (_smoothTests : WholeSpaceDensityExpected.SmoothTests)
    (_weakMollification : WholeSpaceDensityExpected.WeakMollification) : Expected.Finite := by
  intro 𝕜 _ d _hd p _ hdp hp
  obtain ⟨B, hB, hMor⟩ := ExpandedFA.Sobolev.Morrey.finite_whole_space 𝕜 d p hp hdp
  obtain ⟨A, hA, hFull⟩ :=
    ExpandedFA.Sobolev.Higher.wholeSpace_full_morrey (𝕜 := 𝕜) hdp
  let N : ℝ := Fintype.card (Bridge.MGIndex d)
  let C : ℝ := max B (A * N)
  have hBC : B ≤ C := le_max_left _ _
  have hAC : A * N ≤ C := le_max_right _ _
  refine ⟨C, hB.trans hBC, fun u => ?_⟩
  obtain ⟨f, hf, huf, hb⟩ := hMor (Bridge.transferSobolev u)
  obtain ⟨g, hg, hug, hs, _⟩ := hFull (Bridge.transferSobolev u)
  have hfg : f = g := by
    apply Measure.eq_of_ae_eq (μ := (volume : Measure (Bridge.Domain d))) _ hf hg
    have he := huf.symm.trans hug
    simpa only [Opens.coe_top, Measure.restrict_univ] using he
  rw [← hfg] at hs
  let F : Space d → 𝕜 := f ∘ (Bridge.toEuclidean d).symm
  have hF : Continuous F := hf.comp (Bridge.toEuclidean d).symm.continuous
  have huF : Represents u F := Bridge.transfer_represents u f huf
  refine ⟨F, hF, huF, ?_, ?_, fun G hG huG =>
    Bridge.representative_unique u hG hF huG huF⟩
  · intro x y
    have h := hb ((Bridge.toEuclidean d).symm x) ((Bridge.toEuclidean d).symm y)
    rw [Bridge.transfer_gradientNorm, Bridge.euclidean_distance] at h
    change ‖F x - F y‖ ≤ B * gradientNorm u *
      ‖x - y‖ ^ (1 - (d : ℝ) / p.toReal) at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hBC ENNReal.toReal_nonneg)
      (Real.rpow_nonneg (norm_nonneg _) _))
  · intro x
    have hv := Bridge.jet_norm_le (Bridge.transferSobolev u)
    rw [Bridge.transferSobolev_zero, Bridge.transferLp_norm, Bridge.transfer_gradientNorm] at hv
    calc
      ‖F x‖ ≤ A * ‖Bridge.transferSobolev u‖ := hs _
      _ ≤ A * (N * (‖sobolevUnderlying u‖ + gradientNorm u)) :=
        mul_le_mul_of_nonneg_left hv hA
      _ = (A * N) * (‖sobolevUnderlying u‖ + gradientNorm u) := by ring
      _ ≤ C * (‖sobolevUnderlying u‖ + gradientNorm u) :=
        mul_le_mul_of_nonneg_right hAC (add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg)

/-- The infinity endpoint uses the library's separately proved Lipschitz
representative theorem, with no density assertion at infinity. -/
theorem infinity_conditional
    (_cutoff : WholeSpaceDensityExpected.Cutoff)
    (_density : WholeSpaceDensityExpected.Density)
    (_mollification : WholeSpaceDensityExpected.Mollification)
    (_mollifierExistence : WholeSpaceDensityExpected.MollifierExistence)
    (_smoothTests : WholeSpaceDensityExpected.SmoothTests)
    (_weakMollification : WholeSpaceDensityExpected.WeakMollification) : Expected.Infinity := by
  intro 𝕜 _ d _hd
  obtain ⟨C, hC, hMor⟩ := ExpandedFA.Sobolev.Morrey.infinity_whole_space 𝕜 d
  refine ⟨C, hC, fun u => ?_⟩
  obtain ⟨f, hf, huf, hb⟩ := hMor (Bridge.transferSobolev u)
  let F : Space d → 𝕜 := f ∘ (Bridge.toEuclidean d).symm
  have hF : Continuous F := hf.comp (Bridge.toEuclidean d).symm.continuous
  have huF : Represents u F := Bridge.transfer_represents u f huf
  refine ⟨F, hF, huF, ?_, Bridge.continuous_rep_norm_le u hF huF,
    fun G hG huG => Bridge.representative_unique u hG hF huG huF⟩
  intro x y
  have h := hb ((Bridge.toEuclidean d).symm x) ((Bridge.toEuclidean d).symm y)
  rw [Bridge.transfer_gradientNorm, Bridge.euclidean_distance] at h
  exact h

end P102.Sobolev.MorreyWhole

theorem _root_.«P102».«Sobolev».«MorreyWhole».«finite» : _root_.«P102».«Sobolev».«MorreyWhole».«Expected».«Finite» :=
  @_root_.«P102».«Sobolev».«MorreyWhole».«finite_conditional» (@_root_.«P102».«U4».«wholeSpace_cutoff») (@_root_.«P102».«U4».«wholeSpace_density») (@_root_.«P102».«U4».«wholeSpace_mollification») (@_root_.«P102».«U4».«wholeSpace_mollifierExistence») (@_root_.«P102».«U4».«wholeSpace_smoothTests») (@_root_.«P102».«U4».«wholeSpace_weakMollification»)
theorem _root_.«P102».«Sobolev».«MorreyWhole».«infinity» : _root_.«P102».«Sobolev».«MorreyWhole».«Expected».«Infinity» :=
  @_root_.«P102».«Sobolev».«MorreyWhole».«infinity_conditional» (@_root_.«P102».«U4».«wholeSpace_cutoff») (@_root_.«P102».«U4».«wholeSpace_density») (@_root_.«P102».«U4».«wholeSpace_mollification») (@_root_.«P102».«U4».«wholeSpace_mollifierExistence») (@_root_.«P102».«U4».«wholeSpace_smoothTests») (@_root_.«P102».«U4».«wholeSpace_weakMollification»)
