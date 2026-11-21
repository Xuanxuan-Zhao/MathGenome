import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.CriticalMorreyEmbeddings
import MathGenome.Internal.FourierSobolev.P102.Sobolev.MorreyWhole

import MathGenome.Internal.FourierSobolev.P102.Sobolev.LipschitzExtension
import MathGenome.Internal.FourierSobolev.P102.Sobolev.SubcriticalEmbeddings
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace P102.Sobolev.IntegerEmbeddings
open P102.U4

/-- Equality on the open set propagates to its closure. This argument also
covers an empty open set and does not require connectedness. -/
theorem representative_unique {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : Sobolev 𝕜 Ω 1 p)
    {f g : Space d → 𝕜} (hf : ContinuousOn f (closure (Ω : Set (Space d))))
    (hg : ContinuousOn g (closure (Ω : Set (Space d))))
    (huf : RepresentsOn u f) (hug : RepresentsOn u g) :
    EqOn f g (closure (Ω : Set (Space d))) := by
  have h := Measure.eqOn_open_of_ae_eq (huf.symm.trans hug) Ω.isOpen
    (hf.mono subset_closure) (hg.mono subset_closure)
  exact h.of_subset_closure hf hg subset_closure subset_rfl

lemma transfer_jet_norm_le {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p) :
    ‖MorreyWhole.Bridge.transferSobolev u‖ ≤
      Fintype.card (MorreyWhole.Bridge.MGIndex d) * ‖u‖ := by
  rw [ExpandedFA.Sobolev.sobolev_norm_formula]
  calc
    _ ≤ ∑ _ : MorreyWhole.Bridge.MGIndex d, ‖u‖ := by
      apply Finset.sum_le_sum
      intro α _
      change ‖MorreyWhole.Bridge.transferLp (sobolevDerivative u _)‖ ≤ ‖u‖
      rw [MorreyWhole.Bridge.transferLp_norm]
      exact PiLp.norm_apply_le u.val _
    _ = _ := by simp

lemma gradient_norm_le {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p) :
    MorreyWhole.gradientNorm u ≤
      (Fintype.card (ExpandedFA.Sobolev.Morrey.GradientIndex d) : ℝ) *
        Fintype.card (MorreyWhole.Bridge.MGIndex d) * ‖u‖ := by
  rw [← MorreyWhole.Bridge.transfer_gradientNorm]
  exact (ExpandedFA.Sobolev.Morrey.gradientNorm_le _).trans
    (by simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left
      (transfer_jet_norm_le u) (show (0 : ℝ) ≤ Fintype.card (ExpandedFA.Sobolev.Morrey.GradientIndex d) by positivity)))

/-- Rebuild the same weak derivative equations at another exponent. -/
def changeExponent {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (u : Sobolev 𝕜 Ω 1 p)
    (hm : ∀ α, MemLp (sobolevDerivative u α) r (volume.restrict (Ω : Set (Space d)))) :
    Sobolev 𝕜 Ω 1 r := by
  let v : SobolevTuple 𝕜 Ω 1 r := WithLp.toLp 1 fun α => (hm α).toLp (sobolevDerivative u α)
  have hv (α) : v α =ᵐ[volume.restrict (Ω : Set (Space d))] sobolevDerivative u α :=
    (hm α).coeFn_toLp
  refine ⟨v, (mem_sobolevSubmodule_iff Ω 1 r v).mpr ?_⟩
  intro α φ
  have hu := (mem_sobolevSubmodule_iff Ω 1 p u.val).mp u.property α φ
  simp only [lpTestPairing_eq_integral] at hu ⊢
  calc
    _ = ∫ x in Ω, sobolevDerivative u α x * φ x :=
      integral_congr_ae ((hv α).mul EventuallyEq.rfl)
    _ = _ := hu
    _ = _ := congrArg (fun z => (-1 : 𝕜) ^ α.val.card * z)
      (integral_congr_ae ((hv (zeroSobolevIndex d 1)).mul EventuallyEq.rfl)).symm

lemma changeExponent_coe {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (u : Sobolev 𝕜 Ω 1 p)
    (hm : ∀ α, MemLp (sobolevDerivative u α) r (volume.restrict (Ω : Set (Space d)))) (α) :
    sobolevDerivative (changeExponent u hm) α =ᵐ[volume.restrict (Ω : Set (Space d))]
      sobolevDerivative u α := (hm α).coeFn_toLp

lemma sobolev_eNorm {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : Sobolev 𝕜 Ω 1 p) :
    ENNReal.ofReal ‖u‖ = ∑ α, eLpNorm (sobolevDerivative u α) p
      (volume.restrict (Ω : Set (Space d))) := by
  rw [sobolev_norm, ENNReal.ofReal_sum_of_nonneg (fun α _ => norm_nonneg (sobolevDerivative u α))]
  simp only [ofReal_norm, Lp.enorm_def]

lemma changeExponent_eNorm_le {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)] (hrp : r ≤ p)
    (u : Sobolev 𝕜 Ω 1 p)
    (hm : ∀ α, MemLp (sobolevDerivative u α) r (volume.restrict (Ω : Set (Space d)))) :
    ENNReal.ofReal ‖changeExponent u hm‖ ≤ ENNReal.ofReal ‖u‖ *
      (volume.restrict (Ω : Set (Space d))) univ ^ (1/r.toReal - 1/p.toReal) := by
  rw [sobolev_eNorm, sobolev_eNorm, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro α _
  rw [eLpNorm_congr_ae (changeExponent_coe u hm α)]
  exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ hrp (Lp.aestronglyMeasurable _)

/-- A bound for the actual class constructs the continuous linear inclusion.
Injectivity uses the already proved injectivity of the zeroth Sobolev coordinate. -/
theorem inclusion_of_bound {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (C : ℝ≥0)
    (h : ∀ u : Sobolev 𝕜 Ω 1 p,
      MemLp (sobolevUnderlying u) q (volume.restrict (Ω : Set (Space d))) ∧
      eLpNorm (sobolevUnderlying u) q (volume.restrict (Ω : Set (Space d))) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal ‖u‖) : HasSobolevInclusion 𝕜 Ω p q := by
  let I : Sobolev 𝕜 Ω 1 p →ₗ[𝕜] DomainLp 𝕜 Ω q :=
    { toFun := fun u => (h u).1.toLp (sobolevUnderlying u)
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [(h (u+v)).1.coeFn_toLp, Lp.coeFn_add
          ((h u).1.toLp (sobolevUnderlying u)) ((h v).1.toLp (sobolevUnderlying v)),
          (h u).1.coeFn_toLp, (h v).1.coeFn_toLp,
          Lp.coeFn_add (sobolevUnderlying u) (sobolevUnderlying v)] with x hx hsum hu hv huv
        exact hx.trans (huv.trans (hsum.trans (congrArg₂ (· + ·) hu hv)).symm)
      map_smul' := by
        intro c u
        apply Lp.ext
        filter_upwards [(h (c • u)).1.coeFn_toLp,
          Lp.coeFn_smul c ((h u).1.toLp (sobolevUnderlying u)),
          (h u).1.coeFn_toLp, Lp.coeFn_smul c (sobolevUnderlying u)] with x hx hs hu hcu
        exact hx.trans (hcu.trans (hs.trans (congrArg (c • ·) hu)).symm) }
  have hI (u) : ‖I u‖ ≤ (C : ℝ) * ‖u‖ := by
    change ‖(h u).1.toLp (sobolevUnderlying u)‖ ≤ _
    rw [Lp.norm_toLp]
    have hb := ENNReal.toReal_mono (by finiteness) (h u).2
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal (norm_nonneg _)] using hb
  refine ⟨I.mkContinuous C hI, ?_, fun u => (h u).1.coeFn_toLp⟩
  intro u v huv
  apply sobolevUnderlying_injective Ω 1 p
  apply Lp.ext
  have he : (I u : Space d → 𝕜) =ᵐ[volume.restrict (Ω : Set (Space d))] I v :=
    Eventually.of_forall (fun x => congrFun
      (congrArg (fun f : DomainLp 𝕜 Ω q => (f : Space d → 𝕜)) huv) x)
  exact (h u).1.coeFn_toLp.symm.trans (he.trans (h v).1.coeFn_toLp)

/-- Domain Morrey estimate derived from a real whole-space representative and
the supplied extension, retaining all frozen premises in order. -/
theorem finite_conditional
    (_density : Extension.Expected.Density)
    (extension : Extension.Expected.Extension)
    (_subcriticalLipschitz : SubcriticalEmbeddingsExpected.Lipschitz)
    (_subcriticalWhole : SubcriticalEmbeddingsExpected.Whole)
    (_subcriticalZero : SubcriticalEmbeddingsExpected.Zero) : Expected.Finite := by
  intro m e Ω hΩ 𝕜 _ p _ hdp hp
  obtain ⟨D, K, C, B, hraw, hE⟩ := extension m e Ω hΩ
  obtain ⟨E, _, hres, _, _, _⟩ := hE 𝕜 p
  obtain ⟨A, hA, hMor⟩ := MorreyWhole.finite 𝕜 (m+1) (by omega) p hdp hp
  let N : ℝ := Fintype.card (ExpandedFA.Sobolev.Morrey.GradientIndex (m+1)) *
    Fintype.card (MorreyWhole.Bridge.MGIndex (m+1))
  have hN : 0 ≤ N := by dsimp [N]; positivity
  refine ⟨A * (1 + 2 * N) * ‖E‖, by positivity, fun u => ?_⟩
  obtain ⟨f, hf, huf, hholder, hsup, _⟩ := hMor (E u)
  have hrep : RepresentsOn u f := (hres u).symm.trans (ae_restrict_of_ae huf)
  have hgrad : MorreyWhole.gradientNorm (E u) ≤ N * (‖E‖ * ‖u‖) :=
    (gradient_norm_le (E u)).trans (mul_le_mul_of_nonneg_left (E.le_opNorm u) hN)
  have hbase : ‖sobolevUnderlying (E u)‖ ≤ ‖E‖ * ‖u‖ :=
    (PiLp.norm_apply_le (E u).val _).trans (E.le_opNorm u)
  refine ⟨f, hf.continuousOn, hrep, ?_, fun g hg hug =>
    representative_unique u hg hf.continuousOn hug hrep⟩
  refine ⟨A * (1 + N) * (‖E‖ * ‖u‖), A * N * (‖E‖ * ‖u‖),
    by positivity, by positivity, ?_, ?_, ?_⟩
  · dsimp [N]
    ring_nf
    exact le_rfl
  · intro x _
    calc
      ‖f x‖ ≤ A * (‖sobolevUnderlying (E u)‖ + MorreyWhole.gradientNorm (E u)) := hsup x
      _ ≤ A * (‖E‖ * ‖u‖ + N * (‖E‖ * ‖u‖)) := by gcongr
      _ = _ := by ring
  · intro x _ y _
    calc
      ‖f x - f y‖ ≤ A * MorreyWhole.gradientNorm (E u) *
          ‖x-y‖ ^ (1 - ((m+1 : ℕ) : ℝ) / p.toReal) := hholder x y
      _ ≤ A * (N * (‖E‖ * ‖u‖)) *
          ‖x-y‖ ^ (1 - ((m+1 : ℕ) : ℝ) / p.toReal) := by gcongr
      _ = _ := by ring

theorem infinity_conditional
    (_density : Extension.Expected.Density)
    (extension : Extension.Expected.Extension)
    (_subcriticalLipschitz : SubcriticalEmbeddingsExpected.Lipschitz)
    (_subcriticalWhole : SubcriticalEmbeddingsExpected.Whole)
    (_subcriticalZero : SubcriticalEmbeddingsExpected.Zero) : Expected.Infinity := by
  intro m e Ω hΩ 𝕜 _
  obtain ⟨D, K, C, B, hraw, hE⟩ := extension m e Ω hΩ
  obtain ⟨E, _, hres, _, _, _⟩ := hE 𝕜 ⊤
  obtain ⟨A, hA, hMor⟩ := MorreyWhole.infinity 𝕜 (m+1) (by omega)
  let N : ℝ := Fintype.card (ExpandedFA.Sobolev.Morrey.GradientIndex (m+1)) *
    Fintype.card (MorreyWhole.Bridge.MGIndex (m+1))
  have hN : 0 ≤ N := by dsimp [N]; positivity
  refine ⟨(1 + A * N) * ‖E‖, by positivity, fun u => ?_⟩
  obtain ⟨f, hf, huf, hlip, hsup, _⟩ := hMor (E u)
  have hrep : RepresentsOn u f := (hres u).symm.trans (ae_restrict_of_ae huf)
  have hgrad : MorreyWhole.gradientNorm (E u) ≤ N * (‖E‖ * ‖u‖) :=
    (gradient_norm_le (E u)).trans (mul_le_mul_of_nonneg_left (E.le_opNorm u) hN)
  refine ⟨f, hf.continuousOn, hrep, ?_, fun g hg hug =>
    representative_unique u hg hf.continuousOn hug hrep⟩
  refine ⟨‖E‖ * ‖u‖, A * N * (‖E‖ * ‖u‖), by positivity, by positivity, ?_, ?_, ?_⟩
  · ring_nf; exact le_rfl
  · intro x _
    exact (hsup x).trans ((PiLp.norm_apply_le (E u).val _).trans (E.le_opNorm u))
  · intro x _ y _
    simp only [Real.rpow_one]
    calc
      ‖f x - f y‖ ≤ A * MorreyWhole.gradientNorm (E u) * ‖x-y‖ := hlip x y
      _ ≤ A * (N * (‖E‖ * ‖u‖)) * ‖x-y‖ := by gcongr
      _ = _ := by ring

/-- Finite measure lowers both the source Sobolev exponent and the target
Lebesgue exponent. The subcritical input is applied to the rebuilt full jet. -/
theorem critical_conditional
    (_density : Extension.Expected.Density)
    (_extension : Extension.Expected.Extension)
    (subcriticalLipschitz : SubcriticalEmbeddingsExpected.Lipschitz)
    (_subcriticalWhole : SubcriticalEmbeddingsExpected.Whole)
    (_subcriticalZero : SubcriticalEmbeddingsExpected.Zero) : Expected.Critical := by
  intro m hd e Ω hΩ q hq
  have : Fact (1 ≤ ((m+1 : ℕ) : ℝ≥0∞)) := ⟨by exact_mod_cast (show 1 ≤ m+1 by omega)⟩
  have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq⟩
  have hbounded : Bornology.IsBounded (Ω : Set (Space (m+1))) := by
    have hb := e.lipschitzWith.isBounded_image hΩ.2.1
    have he : e '' (Extension.geometricOpen e Ω : Set (GraphPieces.Ambient m)) =
        (Ω : Set (Space (m+1))) := e.toEquiv.image_preimage _
    rwa [he] at hb
  let μ := volume.restrict (Ω : Set (Space (m+1)))
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hbounded.measure_lt_top.ne
  obtain ⟨r, hr, hrd, hqr⟩ :=
    ExpandedFA.Sobolev.Subcritical.choose_subcritical_exponent hd q hq
  have : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr⟩
  have hrD : (r : ℝ≥0∞) ≤ ((m+1 : ℕ) : ℝ≥0∞) := by exact_mod_cast hrd.le
  let s := criticalExponent (m+1) r
  have hqs : (q : ℝ≥0∞) ≤ (s : ℝ≥0∞) := by exact_mod_cast hqr
  let A : ℝ≥0∞ := μ univ ^ (1/(r : ℝ≥0∞).toReal - 1/((m+1 : ℕ) : ℝ≥0∞).toReal)
  let B : ℝ≥0∞ := μ univ ^ (1/(q : ℝ≥0∞).toReal - 1/(s : ℝ≥0∞).toReal)
  have hA : A ≠ ⊤ := by
    apply ENNReal.rpow_ne_top_of_nonneg _ (measure_ne_top μ univ)
    apply sub_nonneg.mpr
    simp only [ENNReal.coe_toReal, ENNReal.toReal_natCast]
    exact one_div_le_one_div_of_le (by exact_mod_cast (zero_lt_one.trans_le hr))
      (by exact_mod_cast hrd.le)
  have hB : B ≠ ⊤ := by
    apply ENNReal.rpow_ne_top_of_nonneg _ (measure_ne_top μ univ)
    apply sub_nonneg.mpr
    simp only [ENNReal.coe_toReal]
    exact one_div_le_one_div_of_le (by exact_mod_cast (zero_lt_one.trans_le hq))
      (by exact_mod_cast hqr)
  obtain ⟨C, hC⟩ := subcriticalLipschitz m hd e Ω hΩ r hr hrd
  let M : ℝ≥0 := C * A.toNNReal * B.toNNReal
  refine ⟨M, fun 𝕜 _ => ?_⟩
  have H (u : Sobolev 𝕜 Ω 1 (m+1 : ℕ)) :
      MemLp (sobolevUnderlying u) q μ ∧
      eLpNorm (sobolevUnderlying u) q μ ≤ (M : ℝ≥0∞) * ENNReal.ofReal ‖u‖ := by
    have hm (α) : MemLp (sobolevDerivative u α) r μ := (Lp.memLp _).mono_exponent hrD
    let v := changeExponent u hm
    have hv : (sobolevUnderlying v : Space (m+1) → 𝕜) =ᵐ[μ] sobolevUnderlying u :=
      changeExponent_coe u hm (zeroSobolevIndex (m+1) 1)
    obtain ⟨hmem, hb⟩ := (hC 𝕜).1 v
    have hvs : MemLp (sobolevUnderlying v) (s : ℝ≥0∞) μ := hmem
    refine ⟨(hvs.mono_exponent hqs).ae_eq hv, ?_⟩
    calc
      _ = eLpNorm (sobolevUnderlying v) q μ := eLpNorm_congr_ae hv.symm
      _ ≤ eLpNorm (sobolevUnderlying v) s μ * B :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ hqs hvs.aestronglyMeasurable
      _ ≤ ((C : ℝ≥0∞) * ENNReal.ofReal ‖v‖) * B := by gcongr
      _ ≤ ((C : ℝ≥0∞) * (ENNReal.ofReal ‖u‖ * A)) * B := by
        gcongr
        exact changeExponent_eNorm_le hrD u hm
      _ = _ := by
        simp only [M, ENNReal.coe_mul, ENNReal.coe_toNNReal hA,
          ENNReal.coe_toNNReal hB]
        ring
  exact ⟨H, inclusion_of_bound M H⟩

/-- A continuous representative satisfies its essential supremum bound at
all points. The full-support hypothesis is supplied by ordinary volume. -/
lemma continuous_bound_of_eLpNorm {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X]
    {μ : Measure X} [μ.IsOpenPosMeasure] {𝕜 : Type} [RCLike 𝕜]
    {f : X → 𝕜} (hf : Continuous f) {M : ℝ} (hM : 0 ≤ M)
    (hb : eLpNorm f ⊤ μ ≤ ENNReal.ofReal M) : ∀ x, ‖f x‖ ≤ M := by
  have ha : ∀ᵐ x ∂μ, ‖f x‖ ≤ M := by
    filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with x hx
    apply (ENNReal.ofReal_le_ofReal_iff hM).mp
    rw [ofReal_norm]
    exact hx.trans (by simpa only [eLpNorm_exponent_top hf.aestronglyMeasurable] using hb)
  have hd := Measure.dense_of_ae ha
  have hc : IsClosed {x | ‖f x‖ ≤ M} := isClosed_le hf.norm continuous_const
  have hall := closure_minimal (subset_rfl : {x | ‖f x‖ ≤ M} ⊆ {x | ‖f x‖ ≤ M}) hc
  rw [hd.closure_eq] at hall
  exact fun x => hall (mem_univ x)

/-- The whole-line primitive of the extension is AC on every finite interval;
restriction therefore retains AC on every closed component, with the uniform
Sobolev bound obtained from the whole-line W¹¹ endpoint. -/
theorem dimensionOne_conditional
    (_density : Extension.Expected.Density)
    (extension : Extension.Expected.Extension)
    (_subcriticalLipschitz : SubcriticalEmbeddingsExpected.Lipschitz)
    (_subcriticalWhole : SubcriticalEmbeddingsExpected.Whole)
    (_subcriticalZero : SubcriticalEmbeddingsExpected.Zero) : Expected.DimensionOne := by
  intro e Ω hΩ 𝕜 _
  obtain ⟨D, K, C, B, hraw, hE⟩ := extension 0 e Ω hΩ
  obtain ⟨E, _, hres, _, _, _⟩ := hE 𝕜 1
  obtain ⟨A, hA⟩ := ExpandedFA.Sobolev.Higher.oneDimension_whole_infinity (𝕜 := 𝕜)
  let N : ℝ := Fintype.card (MorreyWhole.Bridge.MGIndex 1)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  refine ⟨(A : ℝ) * N * ‖E‖, by positivity, fun u => ?_⟩
  let w := MorreyWhole.Bridge.transferSobolev (E u)
  obtain ⟨f, hf⟩ := ExpandedFA.Sobolev.OneDimensional.representative_existence
    𝕜 ⊤ ordConnected_univ 1 w
  have hfc : Continuous f := by
    simpa only [Opens.coe_top, closure_univ, continuousOn_univ] using hf.1
  let G : MorreyWhole.Bridge.Domain 1 → 𝕜 := fun x => f (x 0)
  have hG : Continuous G := hfc.comp (continuous_apply 0)
  have hwG : ExpandedFA.Sobolev.Morrey.Represents w G := hf.2.1
  let F : Space 1 → 𝕜 := G ∘ (MorreyWhole.Bridge.toEuclidean 1).symm
  have hF : Continuous F := hG.comp (MorreyWhole.Bridge.toEuclidean 1).symm.continuous
  have hEF : MorreyWhole.Represents (E u) F :=
    MorreyWhole.Bridge.transfer_represents (E u) G hwG
  have hrep : RepresentsOn u F := (hres u).symm.trans (ae_restrict_of_ae hEF)
  have hsupG : ∀ x, ‖G x‖ ≤ (A : ℝ) * ‖w‖ := by
    apply continuous_bound_of_eLpNorm (μ := volume) hG (by positivity)
    have he : (w.val (ExpandedFA.Sobolev.zeroIndex 1 1) : MorreyWhole.Bridge.Domain 1 → 𝕜)
        =ᵐ[volume] G := by
      simpa only [ExpandedFA.Sobolev.Morrey.Represents, Opens.coe_top,
        Measure.restrict_univ] using hwG
    rw [← eLpNorm_congr_ae he]
    simpa only [Opens.coe_top, Measure.restrict_univ, ENNReal.ofReal_mul (NNReal.coe_nonneg A),
      ENNReal.ofReal_coe_nnreal] using (hA w).2
  refine ⟨F, hF.continuousOn, hrep, ?_, ?_, fun g hg hug =>
    representative_unique u hg hF.continuousOn hug hrep⟩
  · intro x _
    calc
      ‖F x‖ ≤ (A : ℝ) * ‖w‖ := hsupG _
      _ ≤ (A : ℝ) * (N * (‖E‖ * ‖u‖)) := by
        apply mul_le_mul_of_nonneg_left _ A.coe_nonneg
        exact (transfer_jet_norm_le (E u)).trans
          (mul_le_mul_of_nonneg_left (E.le_opNorm u) hN)
      _ = _ := by ring
  · intro a b _ _
    have ha : a ∈ (⊤ : Opens ℝ) := mem_univ a
    have hb : b ∈ (⊤ : Opens ℝ) := mem_univ b
    convert hf.2.2.1 a ha b hb using 1
    funext t
    change f (((MorreyWhole.Bridge.toEuclidean 1).symm (ACL.line 0 0 t)) 0) = f t
    congr 1

end P102.Sobolev.IntegerEmbeddings

theorem _root_.«P102».«Sobolev».«IntegerEmbeddings».«critical» : _root_.«P102».«Sobolev».«IntegerEmbeddings».«Expected».«Critical» :=
  @_root_.«P102».«Sobolev».«IntegerEmbeddings».«critical_conditional» (@_root_.«P102».«Sobolev».«Extension».«lipschitz_ambient_density») (@_root_.«P102».«Sobolev».«Extension».«lipschitz_extension») (@_root_.«P102».«Sobolev».«subcritical_lipschitz») (@_root_.«P102».«Sobolev».«subcritical_whole») (@_root_.«P102».«Sobolev».«subcritical_zero»)
theorem _root_.«P102».«Sobolev».«IntegerEmbeddings».«dimensionOne» : _root_.«P102».«Sobolev».«IntegerEmbeddings».«Expected».«DimensionOne» :=
  @_root_.«P102».«Sobolev».«IntegerEmbeddings».«dimensionOne_conditional» (@_root_.«P102».«Sobolev».«Extension».«lipschitz_ambient_density») (@_root_.«P102».«Sobolev».«Extension».«lipschitz_extension») (@_root_.«P102».«Sobolev».«subcritical_lipschitz») (@_root_.«P102».«Sobolev».«subcritical_whole») (@_root_.«P102».«Sobolev».«subcritical_zero»)
theorem _root_.«P102».«Sobolev».«IntegerEmbeddings».«finite» : _root_.«P102».«Sobolev».«IntegerEmbeddings».«Expected».«Finite» :=
  @_root_.«P102».«Sobolev».«IntegerEmbeddings».«finite_conditional» (@_root_.«P102».«Sobolev».«Extension».«lipschitz_ambient_density») (@_root_.«P102».«Sobolev».«Extension».«lipschitz_extension») (@_root_.«P102».«Sobolev».«subcritical_lipschitz») (@_root_.«P102».«Sobolev».«subcritical_whole») (@_root_.«P102».«Sobolev».«subcritical_zero»)
theorem _root_.«P102».«Sobolev».«IntegerEmbeddings».«infinity» : _root_.«P102».«Sobolev».«IntegerEmbeddings».«Expected».«Infinity» :=
  @_root_.«P102».«Sobolev».«IntegerEmbeddings».«infinity_conditional» (@_root_.«P102».«Sobolev».«Extension».«lipschitz_ambient_density») (@_root_.«P102».«Sobolev».«Extension».«lipschitz_extension») (@_root_.«P102».«Sobolev».«subcritical_lipschitz») (@_root_.«P102».«Sobolev».«subcritical_whole») (@_root_.«P102».«Sobolev».«subcritical_zero»)
