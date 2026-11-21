import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.SubcriticalEmbeddings
import MathGenome.Internal.FourierSobolev.P102.Sobolev.SubcriticalWhole
import MathGenome.Internal.FourierSobolev.P102.U4.ZeroExtension
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.FourierSobolev.P102.Sobolev.LipschitzExtension
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal NNReal
namespace P102.Sobolev
open P102.U4
open private tuple_eLpNorm_le_sum from MathGenome.Internal.FourierSobolev.P102.Sobolev.SubcriticalWhole

/-- The derivative representatives give an Lp Euclidean gradient on every open set. -/
theorem weakGradientOn_memLp {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : U4.Sobolev 𝕜 Ω 1 p) :
    MemLp (weakGradientOn u) p (volume.restrict (Ω : Set (Space d))) := by
  apply ExpandedFA.Sobolev.Subcritical.euclideanTuple_memLp
  intro i
  exact Lp.memLp (sobolevDerivative u (firstIndex i))

/-- A coarse dimension-dependent bound suffices to pass from the homogeneous
whole-space estimate to the shared full Sobolev norm. -/
theorem weakGradientOn_eLpNorm_le {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : U4.Sobolev 𝕜 Ω 1 p) :
    eLpNorm (weakGradientOn u) p (volume.restrict (Ω : Set (Space d))) ≤
      (d : ℝ≥0∞) * ENNReal.ofReal ‖u‖ := by
  classical
  apply (tuple_eLpNorm_le_sum Fact.out
    (fun i => (sobolevDerivative u (firstIndex i) : Space d → 𝕜))
    (fun i => Lp.memLp _)).trans
  calc
    _ = ∑ i : Fin d, ENNReal.ofReal ‖sobolevDerivative u (firstIndex i)‖ := by
      apply Finset.sum_congr rfl
      intro i _
      simpa [ofReal_norm] using (Lp.enorm_def (sobolevDerivative u (firstIndex i))).symm
    _ ≤ ∑ _i : Fin d, ENNReal.ofReal ‖u‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply ENNReal.ofReal_le_ofReal
      exact PiLp.norm_apply_le u.val (firstIndex i)
    _ = _ := by simp

/-- An Lq estimate for a continuous injective Lp-class map constructs the
actual continuous inclusion, without making any choice of pointwise values. -/
theorem lpInclusion_of_bound {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {V : Type} [SeminormedAddCommGroup V] [Module 𝕜 V]
    (U : V →L[𝕜] DomainLp 𝕜 Ω p) (hU : Function.Injective U)
    (C : ℝ≥0)
    (h : ∀ u, MemLp (U u) q (volume.restrict (Ω : Set (Space d))) ∧
      eLpNorm (U u) q (volume.restrict (Ω : Set (Space d))) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal ‖u‖) :
    ∃ I : V →L[𝕜] DomainLp 𝕜 Ω q,
      Function.Injective I ∧ ∀ u,
        (I u : Space d → 𝕜) =ᵐ[volume.restrict (Ω : Set (Space d))] U u := by
  let L : V →ₗ[𝕜] DomainLp 𝕜 Ω q :=
    { toFun := fun u => (h u).1.toLp (U u)
      map_add' := by
        intro u v
        apply Lp.ext
        grw [MemLp.coeFn_toLp, Lp.coeFn_add, MemLp.coeFn_toLp, MemLp.coeFn_toLp]
        simpa only [map_add] using Lp.coeFn_add (U u) (U v)
      map_smul' := by
        intro c u
        apply Lp.ext
        grw [MemLp.coeFn_toLp, Lp.coeFn_smul, MemLp.coeFn_toLp]
        simpa only [map_smul, RingHom.id_apply] using Lp.coeFn_smul c (U u) }
  have hb (u : V) : ‖L u‖ ≤ (C : ℝ) * ‖u‖ := by
    change ‖(h u).1.toLp (U u)‖ ≤ _
    rw [Lp.norm_toLp]
    have hh := ENNReal.toReal_mono (by finiteness) (h u).2
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal,
      ENNReal.toReal_ofReal (norm_nonneg u)] using hh
  let I := L.mkContinuous (C : ℝ) hb
  have hrep (u : V) : (I u : Space d → 𝕜) =ᵐ[
      volume.restrict (Ω : Set (Space d))] U u := (h u).1.coeFn_toLp
  refine ⟨I, ?_, hrep⟩
  intro u v huv
  apply hU
  apply Lp.ext
  exact (hrep u).symm.trans ((congrArg (fun w : DomainLp 𝕜 Ω q =>
    (w : Space d → 𝕜)) huv).eventuallyEq.trans (hrep v))

/-- Conditional whole-space clause. Both frozen extension premises are explicit,
in the required order, although neither is needed for this clause. -/
theorem subcritical_whole_conditional
    (_density : Extension.Expected.Density)
    (_extension : Extension.Expected.Extension) : SubcriticalEmbeddingsExpected.Whole := by
  refine ⟨subcriticalWhole, ?_⟩
  intro d hd p hp hpd
  let : Fact (1 ≤ (criticalExponent d p : ℝ≥0∞)) :=
    ⟨by exact_mod_cast one_le_criticalExponent hp hpd⟩
  intro 𝕜 _ _
  obtain ⟨C, hC⟩ := subcriticalWhole d hd p hp hpd
  unfold HasSobolevInclusion
  apply lpInclusion_of_bound (Ω := (⊤ : Opens (Space d)))
    (p := p) (q := criticalExponent d p)
    (sobolevUnderlyingCLM (𝕜 := 𝕜) (⊤ : Opens (Space d)) 1 p)
    (sobolevUnderlying_injective _ _ _) (C * d)
  intro u
  obtain ⟨_, hmem, hbound⟩ := hC 𝕜 u
  simp only [Opens.coe_top, Measure.restrict_univ]
  refine ⟨hmem, hbound.trans ?_⟩
  have hg := weakGradientOn_eLpNorm_le u
  simp only [Opens.coe_top, Measure.restrict_univ] at hg
  change eLpNorm (weakGradient u) p volume ≤
    (d : ℝ≥0∞) * ENNReal.ofReal ‖u‖ at hg
  simpa only [ENNReal.coe_mul, ENNReal.coe_natCast, mul_assoc] using
    mul_le_mul_right hg (C : ℝ≥0∞)

/-- Conditional full-norm estimate and class inclusion on bounded Lipschitz
open sets. The extension is used at its full frozen type. -/
theorem subcritical_lipschitz_conditional
    (_density : Extension.Expected.Density)
    (extension : Extension.Expected.Extension) : SubcriticalEmbeddingsExpected.Lipschitz := by
  intro m hd e Ω hΩ p hp hpd
  let : Fact (1 ≤ (criticalExponent (m + 1) p : ℝ≥0∞)) :=
    ⟨by exact_mod_cast one_le_criticalExponent hp hpd⟩
  obtain ⟨D, K, A, B, _, hE⟩ := extension m e Ω hΩ
  obtain ⟨C, hC⟩ := subcriticalWhole (m + 1) hd p hp hpd
  refine ⟨C * (m + 1) * A p, ?_⟩
  intro 𝕜 _ _
  obtain ⟨E, _, heq, _, hn, _⟩ := hE 𝕜 p
  have hbound (u : U4.Sobolev 𝕜 Ω 1 p) :
      MemLp (sobolevUnderlying u) (criticalExponent (m + 1) p)
        (volume.restrict (Ω : Set (Space (m + 1)))) ∧
      eLpNorm (sobolevUnderlying u) (criticalExponent (m + 1) p)
          (volume.restrict (Ω : Set (Space (m + 1)))) ≤
        ((C * (m + 1) * A p : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal ‖u‖ := by
    obtain ⟨_, hmem, hbound⟩ := hC 𝕜 (E u)
    refine ⟨(hmem.mono_measure Measure.restrict_le_self).ae_eq (heq u), ?_⟩
    have hg := weakGradientOn_eLpNorm_le (E u)
    simp only [Opens.coe_top, Measure.restrict_univ] at hg
    change eLpNorm (weakGradient (E u)) p volume ≤
      ((m + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ‖E u‖ at hg
    have hEu : ‖E u‖ ≤ (A p : ℝ) * ‖u‖ :=
      (E.le_opNorm u).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg u))
    calc
      _ = eLpNorm (sobolevUnderlying (E u)) (criticalExponent (m + 1) p)
          (volume.restrict (Ω : Set (Space (m + 1)))) :=
        (eLpNorm_congr_ae (heq u)).symm
      _ ≤ eLpNorm (sobolevUnderlying (E u)) (criticalExponent (m + 1) p) volume :=
        eLpNorm_mono_measure _ Measure.restrict_le_self
      _ ≤ (C : ℝ≥0∞) * eLpNorm (weakGradient (E u)) p volume := hbound
      _ ≤ (C : ℝ≥0∞) * ((m + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ‖E u‖ := by
        simpa only [mul_assoc] using
          mul_le_mul_right hg (C : ℝ≥0∞)
      _ ≤ (C : ℝ≥0∞) * ((m + 1 : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal ((A p : ℝ) * ‖u‖) :=
        mul_le_mul_right (ENNReal.ofReal_le_ofReal hEu) _
      _ = _ := by simp [ENNReal.ofReal_mul, mul_assoc]
  refine ⟨hbound, ?_⟩
  exact lpInclusion_of_bound (Ω := Ω) (p := p) (q := criticalExponent (m + 1) p)
    (sobolevUnderlyingCLM (𝕜 := 𝕜) Ω 1 p)
    (sobolevUnderlying_injective Ω 1 p) _ hbound

/-- The shared coordinatewise zero extension is also zero extension of the
Euclidean gradient tuple, as an almost-everywhere ambient function. -/
theorem weakGradient_zeroExtension_ae {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : SobolevZero 𝕜 Ω 1 p) :
    weakGradient (sobolevZeroExtensionLI Ω 1 p u) =ᵐ[volume]
      (Ω : Set (Space d)).indicator (weakGradientOn u.val) := by
  have hi (i : Fin d) := lpZeroExtension_ae Ω p (sobolevDerivative u.val (firstIndex i))
  filter_upwards [ae_all_iff.mpr hi] with x hx
  ext i
  by_cases hΩ : x ∈ Ω
  · simpa [weakGradient, weakGradientOn, sobolevZeroExtensionLI,
      sobolevTupleZeroExtensionLI, sobolevDerivative, hΩ] using hx i
  · simpa [weakGradient, weakGradientOn, sobolevZeroExtensionLI,
      sobolevTupleZeroExtensionLI, sobolevDerivative, hΩ] using hx i

/-- In particular zero extension preserves exactly the Lp gradient norm. -/
theorem weakGradient_zeroExtension_eLpNorm {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : SobolevZero 𝕜 Ω 1 p) :
    eLpNorm (weakGradient (sobolevZeroExtensionLI Ω 1 p u)) p volume =
      eLpNorm (weakGradientOn u.val) p (volume.restrict (Ω : Set (Space d))) := by
  rw [eLpNorm_congr_ae (weakGradient_zeroExtension_ae Ω p u),
    eLpNorm_indicator_eq_eLpNorm_restrict Ω.isOpen.measurableSet.nullMeasurableSet]

/-- Conditional zero-boundary clause. No regularity or boundedness is imposed
on Ω, and the constant is inherited from the whole-space estimate. -/
theorem subcritical_zero_conditional
    (_density : Extension.Expected.Density)
    (_extension : Extension.Expected.Extension) : SubcriticalEmbeddingsExpected.Zero := by
  intro d hd p hp hpd
  let : Fact (1 ≤ (criticalExponent d p : ℝ≥0∞)) :=
    ⟨by exact_mod_cast one_le_criticalExponent hp hpd⟩
  obtain ⟨C, hC⟩ := subcriticalWhole d hd p hp hpd
  refine ⟨C, ?_⟩
  intro Ω 𝕜 _ _
  have hbound (u : SobolevZero 𝕜 Ω 1 p) :
      MemLp (weakGradientOn u.val) p (volume.restrict (Ω : Set (Space d))) ∧
      MemLp (sobolevUnderlying u.val) (criticalExponent d p)
        (volume.restrict (Ω : Set (Space d))) ∧
      eLpNorm (sobolevUnderlying u.val) (criticalExponent d p)
          (volume.restrict (Ω : Set (Space d))) ≤
        (C : ℝ≥0∞) * eLpNorm (weakGradientOn u.val) p
          (volume.restrict (Ω : Set (Space d))) := by
    obtain ⟨_, hmem, hbound⟩ := hC 𝕜 (sobolevZeroExtensionLI Ω 1 p u)
    have hrep : (sobolevUnderlying (sobolevZeroExtensionLI Ω 1 p u) : Space d → 𝕜) =ᵐ[
        volume.restrict (Ω : Set (Space d))] sobolevUnderlying u.val := by
      have hz := (lpZeroExtension_ae Ω p (sobolevUnderlying u.val)).filter_mono
        (ae_mono (Measure.restrict_le_self (s := (Ω : Set (Space d)))))
      exact hz.trans (indicator_ae_eq_restrict Ω.isOpen.measurableSet.nullMeasurableSet)
    refine ⟨weakGradientOn_memLp u.val,
      (hmem.mono_measure Measure.restrict_le_self).ae_eq hrep, ?_⟩
    calc
      _ = eLpNorm (sobolevUnderlying (sobolevZeroExtensionLI Ω 1 p u))
          (criticalExponent d p) (volume.restrict (Ω : Set (Space d))) :=
        (eLpNorm_congr_ae hrep).symm
      _ ≤ eLpNorm (sobolevUnderlying (sobolevZeroExtensionLI Ω 1 p u))
          (criticalExponent d p) volume := eLpNorm_mono_measure _ Measure.restrict_le_self
      _ ≤ (C : ℝ≥0∞) * eLpNorm (weakGradient (sobolevZeroExtensionLI Ω 1 p u)) p volume :=
        hbound
      _ = _ := by rw [weakGradient_zeroExtension_eLpNorm]
  refine ⟨hbound, ?_⟩
  let U : SobolevZero 𝕜 Ω 1 p →L[𝕜] DomainLp 𝕜 Ω p :=
    (sobolevUnderlyingCLM (𝕜 := 𝕜) Ω 1 p).comp
      (sobolevZeroSubmodule 𝕜 Ω 1 p).subtypeL
  unfold HasZeroSobolevInclusion
  apply lpInclusion_of_bound (𝕜 := 𝕜) (V := SobolevZero 𝕜 Ω 1 p)
    (Ω := Ω) (p := p) (q := criticalExponent d p)
    U
    ((sobolevUnderlying_injective Ω 1 p).comp Subtype.val_injective) (C * d)
  intro u
  refine ⟨(hbound u).2.1, (hbound u).2.2.trans ?_⟩
  change (C : ℝ≥0∞) * eLpNorm (weakGradientOn u.val) p
    (volume.restrict (Ω : Set (Space d))) ≤
    ((C * d : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal ‖u.val‖
  calc
    _ ≤ (C : ℝ≥0∞) * ((d : ℝ≥0∞) * ENNReal.ofReal ‖u.val‖) :=
      mul_le_mul_right (weakGradientOn_eLpNorm_le u.val) (C : ℝ≥0∞)
    _ = _ := by simp only [ENNReal.coe_mul, ENNReal.coe_natCast, mul_assoc]

end P102.Sobolev

theorem _root_.«P102».«Sobolev».«subcritical_lipschitz» : _root_.«P102».«Sobolev».«SubcriticalEmbeddingsExpected».«Lipschitz» :=
  @_root_.«P102».«Sobolev».«subcritical_lipschitz_conditional» (@_root_.«P102».«Sobolev».«Extension».«lipschitz_ambient_density») (@_root_.«P102».«Sobolev».«Extension».«lipschitz_extension»)
theorem _root_.«P102».«Sobolev».«subcritical_whole» : _root_.«P102».«Sobolev».«SubcriticalEmbeddingsExpected».«Whole» :=
  @_root_.«P102».«Sobolev».«subcritical_whole_conditional» (@_root_.«P102».«Sobolev».«Extension».«lipschitz_ambient_density») (@_root_.«P102».«Sobolev».«Extension».«lipschitz_extension»)
theorem _root_.«P102».«Sobolev».«subcritical_zero» : _root_.«P102».«Sobolev».«SubcriticalEmbeddingsExpected».«Zero» :=
  @_root_.«P102».«Sobolev».«subcritical_zero_conditional» (@_root_.«P102».«Sobolev».«Extension».«lipschitz_ambient_density») (@_root_.«P102».«Sobolev».«Extension».«lipschitz_extension»)
