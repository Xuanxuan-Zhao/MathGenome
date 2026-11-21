import MathGenome.Internal.LinearPDE.P201.Common.DifferenceQuotients
import MathGenome.Internal.LinearPDE.P201.Common.InteriorTesting
import MathGenome.Internal.FourierSobolev.P102.U4.MeyersSerrin
import MathGenome.Internal.FourierSobolev.P102.Sobolev.SupportedCompactness
import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.InteriorH2
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace MeasureTheory
open scoped NNReal ENNReal InnerProductSpace
namespace P201.InteriorH2
open P201Specs.InteriorH2

/-- The elementary absorption step used after the weak energy computation. -/
lemma quadratic_absorption {X Z K theta : ℝ} (_hX : 0 ≤ X) (hZ : 0 ≤ Z)
    (hK : 0 ≤ K) (htheta : 0 < theta)
    (h : theta * X ^ 2 ≤ K * X * Z + K * Z ^ 2) :
    X ≤ (1 + 2 * K / theta) * Z := by
  have hC : 0 ≤ 2 * K / theta := div_nonneg (by positivity) htheta.le
  by_cases hXZ : X ≤ Z
  · nlinarith [mul_nonneg hC hZ]
  · have hZX : Z < X := lt_of_not_ge hXZ
    have hXP : 0 < X := lt_of_le_of_lt hZ hZX
    have hsq : K * Z ^ 2 ≤ K * X * Z := by
      nlinarith [mul_le_mul_of_nonneg_left hZX.le (mul_nonneg hK hZ)]
    have hlin : theta * X ≤ 2 * K * Z := by
      apply (mul_le_mul_iff_left₀ hXP).mp
      nlinarith [h]
    have hdiv : X ≤ (2 * K / theta) * Z := by
      have hd : X ≤ 2 * K * Z / theta := (le_div_iff₀ htheta).mpr (by nlinarith [hlin])
      simpa only [div_mul_eq_mul_div] using hd
    nlinarith

/-- Difference product rule for the flux, with the coefficient translated in
its principal term. It uses no differentiability of either factor. -/
lemma flux_difference {n : ℕ} (A : Space n → Space n →L[ℝ] Space n)
    (q : Space n → Space n) (x a : Space n) (h : ℝ) :
    h⁻¹ • (A (x + a) (q (x + a)) - A x (q x)) =
      A (x + a) (h⁻¹ • (q (x + a) - q x)) +
        (h⁻¹ • (A (x + a) - A x)) (q x) := by
  simp only [map_smul, map_sub, smul_apply,
    sub_apply, smul_sub]
  abel

/-- Lipschitz coefficients have uniformly bounded coordinate differences;
no derivative of the coefficients is required. -/
lemma coefficient_difference_le {n : ℕ} {V : Domain n}
    {A : Space n → Space n →L[ℝ] Space n} {L : ℝ≥0}
    (hA : LipschitzOnWith L A (V : Set (Space n)))
    (j : Fin n) {x : Space n} {h : ℝ} (hh : h ≠ 0)
    (hx : x ∈ V) (hx' : x + h • coordinate n j ∈ V) :
    ‖h⁻¹ • (A (x + h • coordinate n j) - A x)‖ ≤ L := by
  have hb := hA.norm_sub_le hx' hx
  have hcoord : ‖coordinate n j‖ = 1 :=
    P102.U4.DifferenceQuotient.norm_coordinateVector j
  have hdist : ‖(x + h • coordinate n j) - x‖ = |h| := by
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hcoord, mul_one]
  rw [hdist] at hb
  rw [norm_smul, Real.norm_eq_abs, abs_inv]
  calc
    |h|⁻¹ * ‖A (x + h • coordinate n j) - A x‖ ≤ |h|⁻¹ * (L * |h|) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (abs_nonneg h))
    _ = L := by rw [mul_left_comm, inv_mul_cancel₀ (abs_ne_zero.mpr hh), mul_one]

/-- The converse produces actual L² classes, preserving the common constant.
The hypotheses contain quotient bounds only, not second weak derivatives. -/
theorem secondDerivatives_of_quotients {n : ℕ} {V U : Domain n}
    (hUV : RelativelyCompactIn U V) (v : H ℝ V 1) (B : ℝ≥0)
    (hb : GradientQuotientBound V U v B) :
    ∃ g : Fin n → Fin n → Lp ℝ U 2, ∀ j k,
      distributionDerivative {k} (regularDistribution U (hFirstDerivative v j)) =
        regularDistribution U (g j k) ∧ ‖g j k‖ ≤ B := by
  have h (j k : Fin n) :=
    P102.U4.DifferenceQuotient.HasBound.exists_local_derivative
      (by norm_num : (1 : ℝ≥0∞) < 2) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      (P102.U4.domainLp_locallyIntegrable V 2 (hFirstDerivative v j)) hUV (hb j k)
  choose g hg hD using h
  refine ⟨g, fun j k => ⟨hD j k, ?_⟩⟩
  have he := ENNReal.toReal_mono (by simp : (B : ℝ≥0∞) ≠ ∞) (hg j k)
  simpa only [Lp.norm_def, ENNReal.coe_toReal] using he

/-- A full H² class is built from its distributional derivative representatives. -/
theorem h2FromWeakDerivatives : P201Specs.InteriorH2.h2FromWeakDerivativesStatement := by
  intro n U u d g B hd hg huB hdB hgB
  have hα : ∀ α : MultiIndex n, α.card ≤ 2 →
      ∃ z : Lp ℝ U 2, distributionDerivative α (regularDistribution U u) =
        regularDistribution U z ∧ ‖z‖ ≤ B := by
    intro α hcard
    have hc : α.card = 0 ∨ α.card = 1 ∨ α.card = 2 := by omega
    rcases hc with hc | hc | hc
    · have hz : α = 0 := Multiset.card_eq_zero.mp hc
      subst α
      exact ⟨u, P102.U4.derivative_zero n ℝ U _, huB⟩
    · obtain ⟨j, rfl⟩ := Multiset.card_eq_one.mp hc
      exact ⟨d j, hd j, hdB j⟩
    · obtain ⟨j, k, rfl⟩ := Multiset.card_eq_two.mp hc
      refine ⟨g j k, ?_, hgB j k⟩
      have hsplit : ({j, k} : MultiIndex n) = {k} + {j} := by simp [add_comm]
      rw [hsplit]
      change P102.U4.distributionPartial ({k} + {j}) (regularDistribution U u) = _
      rw [P102.U4.derivative_add n ℝ U]
      change distributionDerivative {k}
        (distributionDerivative {j} (regularDistribution U u)) = _
      exact (congrArg (fun T : Distribution ℝ U => distributionDerivative {k} T) (hd j)).trans
        (hg j k)
  have hsob : P102.U4.HasSobolevDerivatives U 2 2 u := by
    intro α hcard
    obtain ⟨z, hz, _⟩ := hα α hcard
    exact ⟨z, hz⟩
  obtain ⟨v, hv⟩ := (Set.ext_iff.mp (P102.U4.sobolev_range U 2 2) u).mpr hsob
  let w : H ℝ U 2 := (hToW ℝ U 2).symm v
  have hw : hUnderlying U 2 w = u := by
    change P102.U4.sobolevUnderlying ((hToW ℝ U 2) w) = u
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact hv
  have hbound (α : P102.U4.SobolevIndex n 2) :
      ‖P102.U4.sobolevDerivative ((hToW ℝ U 2) w) α‖ ≤ B := by
    obtain ⟨z, hz, hzB⟩ := hα α.val α.property
    have heq : z = P102.U4.sobolevDerivative ((hToW ℝ U 2) w) α := by
      apply P102.U4.sobolev_derivative_unique U 2 2
      change distributionDerivative α.val (regularDistribution U (hUnderlying U 2 w)) = _
      rw [hw]
      exact hz
    rw [← heq]
    exact hzB
  refine ⟨w, hw, ?_⟩
  have hsq : ‖w‖ ^ 2 ≤
      (∑ α : P102.U4.SobolevIndex n 2,
        ‖P102.U4.sobolevDerivative ((hToW ℝ U 2) w) α‖) ^ 2 := by
    rw [fullHilbertNorm U 2 w]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun α _ => norm_nonneg _)
  have hnorm := (sq_le_sq₀ (norm_nonneg w)
    (Finset.sum_nonneg (fun α _ => norm_nonneg _))).mp hsq
  calc
    ‖w‖ ≤ ∑ α : P102.U4.SobolevIndex n 2,
        ‖P102.U4.sobolevDerivative ((hToW ℝ U 2) w) α‖ := hnorm
    _ ≤ ∑ _α : P102.U4.SobolevIndex n 2, B := Finset.sum_le_sum (fun α _ => hbound α)
    _ = _ := by simp

/-- Restriction of an L² class to an arbitrary smaller open set. -/
def restrictLp {n : ℕ} {V U : Domain n} (hUV : U ≤ V) (v : Lp ℝ V 2) : Lp ℝ U 2 :=
  ((Lp.memLp v).mono_measure (Measure.restrict_mono hUV le_rfl)).toLp v

lemma restrictLp_ae {n : ℕ} {V U : Domain n} (hUV : U ≤ V) (v : Lp ℝ V 2) :
    (restrictLp hUV v : Space n → ℝ) =ᵐ[domainMeasure U] v := MemLp.coeFn_toLp _

lemma restrictLp_norm_le {n : ℕ} {V U : Domain n} (hUV : U ≤ V) (v : Lp ℝ V 2) :
    ‖restrictLp hUV v‖ ≤ ‖v‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (restrictLp_ae hUV v)]
  exact ENNReal.toReal_mono (Lp.memLp v).eLpNorm_ne_top
    (eLpNorm_mono_measure _ (Measure.restrict_mono hUV le_rfl))

lemma regular_restrictLp {n : ℕ} {V U : Domain n} (hUV : U ≤ V) (v : Lp ℝ V 2) :
    regularDistribution U (restrictLp hUV v) = regularDistribution U v := by
  exact (P102.U4.regular_injectivity n ℝ U _ _
    (P102.U4.domainLp_locallyIntegrable U 2 _)
    ((P102.U4.domainLp_locallyIntegrable V 2 v).mono_set hUV)).mpr
      (restrictLp_ae hUV v)

/-- Uniform local bounds for gradient quotients give the full H² restriction
and a quantitative full-norm estimate. -/
theorem h2FromQuotients : P201Specs.InteriorH2.h2FromQuotientsStatement := by
  intro n V U hUV v B hb
  let hsub : U ≤ V := subset_closure.trans hUV.2
  let u := restrictLp hsub (hUnderlying V 1 v)
  let d : Fin n → Lp ℝ U 2 := fun j => restrictLp hsub (hFirstDerivative v j)
  obtain ⟨g, hg⟩ := secondDerivatives_of_quotients hUV v B hb
  have hd (j : Fin n) : distributionDerivative {j} (regularDistribution U u) =
      regularDistribution U (d j) := by
    dsimp only [u, d]
    rw [regular_restrictLp, regular_restrictLp]
    apply P102.U4.DifferenceQuotient.weak_derivative_restrict hsub
      (P102.U4.domainLp_locallyIntegrable V 2 _)
      (P102.U4.domainLp_locallyIntegrable V 2 _)
    exact hilbertDerivativeDistribution V 1 v ⟨{j}, by simp⟩
  have hdg (j k : Fin n) : distributionDerivative {k} (regularDistribution U (d j)) =
      regularDistribution U (g j k) := by
    dsimp only [d]
    rw [regular_restrictLp]
    exact (hg j k).1
  have hcoord (α : P102.U4.SobolevIndex n 1) :
      ‖P102.U4.sobolevDerivative ((hToW ℝ V 1) v) α‖ ≤ ‖v‖ := by
    change ‖v.val α‖ ≤ ‖v.val‖
    exact PiLp.norm_apply_le _ _
  have hu : ‖u‖ ≤ ‖v‖ := (restrictLp_norm_le hsub _).trans (hcoord _)
  have hdn (j : Fin n) : ‖d j‖ ≤ ‖v‖ :=
    (restrictLp_norm_le hsub _).trans (hcoord ⟨{j}, by simp⟩)
  obtain ⟨w, hw, hwn⟩ := h2FromWeakDerivatives U u d g (‖v‖ + B) hd hdg
    (by linarith [B.coe_nonneg]) (fun j => by linarith [hdn j, B.coe_nonneg])
    (fun j k => by linarith [(hg j k).2, norm_nonneg v])
  refine ⟨w, ?_, hwn⟩
  rw [hw]
  exact restrictLp_ae hsub _

/-- Local Lipschitz continuity and local ellipticity supply the finite data
needed on any relatively compact comparison set. -/
theorem localCoefficientBounds {n : ℕ} {Ω V : Domain n}
    (hV : RelativelyCompactIn V Ω) (A : Space n → Space n →L[ℝ] Space n)
    (hA : LocallyLipschitzOn (Ω : Set (Space n)) A)
    (hell : LocallyUniformlyElliptic Ω A) :
    ∃ (M L : ℝ≥0) (theta : ℝ), 0 < theta ∧ CoefficientBounds V A M L theta := by
  have hAK := hA.mono hV.2
  obtain ⟨L, hL⟩ := hAK.exists_lipschitzOnWith_of_compact hV.1
  obtain ⟨M, hM⟩ := hV.1.bddAbove_image hAK.continuousOn.norm
  obtain ⟨theta, ht, he⟩ := hell (closure (V : Set (Space n))) hV.1 hV.2
  refine ⟨⟨max M 0, le_max_right _ _⟩, L, theta, ht, ?_,
    hL.mono subset_closure, fun x hx => he x (subset_closure hx)⟩
  intro x hx
  exact (hM (mem_image_of_mem _ (subset_closure hx))).trans (le_max_left _ _)

/-- Assemble the quantitative H² conclusion from the uniform gradient quotient
estimate, with no additional regularity hypothesis. -/
theorem interiorH2Estimate_of_gradientEstimate
    (hEnergy : P201Specs.InteriorH2.gradientQuotientEstimateStatement) :
    P201Specs.InteriorH2.interiorH2EstimateStatement := by
  intro n hn Ω V U hUV hVΩ M L theta ht
  obtain ⟨C, hC⟩ := hEnergy hn Ω V U hUV hVΩ M L theta ht
  let N := Fintype.card (P102.U4.SobolevIndex n 2)
  have hN : 0 < (N : ℝ) := by
    have : Nonempty (P102.U4.SobolevIndex n 2) := ⟨P102.U4.zeroSobolevIndex n 2⟩
    exact_mod_cast Fintype.card_pos
  refine ⟨(N : ℝ) * (1 + C), mul_pos hN (by positivity), ?_⟩
  intro A hA v f heq
  obtain ⟨w, hw, hwn⟩ := h2FromQuotients V U hUV v
    (C * (‖v‖₊ + ‖f‖₊)) (hC A hA v f heq)
  refine ⟨w, hw, hwn.trans ?_⟩
  change (N : ℝ) * (‖v‖ + (C * (‖v‖₊ + ‖f‖₊) : ℝ≥0)) ≤ _
  simp only [NNReal.coe_mul, NNReal.coe_add, coe_nnnorm]
  rw [mul_assoc (N : ℝ)]
  apply mul_le_mul_of_nonneg_left _ hN.le
  nlinarith [norm_nonneg f]

/-- Assembly of local regularity from the quantitative theorem, including the
choice of local classes, finite coefficient bounds, and L² source restriction. -/
theorem interiorH2Regularity_of_estimate
    (hEstimate : P201Specs.InteriorH2.interiorH2EstimateStatement) :
    P201Specs.InteriorH2.interiorH2RegularityStatement := by
  intro n hn Ω A hA hell u f hu hf heq U hU
  obtain ⟨V, hV, hUV⟩ := P102.U4.DifferenceQuotient.exists_relativelyCompact_open hU.1 hU.2
  have hUV' : RelativelyCompactIn U V := ⟨hU.1, hUV⟩
  have hsub : U ≤ V := subset_closure.trans hUV
  obtain ⟨v, hv⟩ := hu V hV
  obtain ⟨M, L, theta, ht, hbound⟩ := localCoefficientBounds hV A hA hell
  obtain ⟨C, _, hC⟩ := hEstimate hn Ω V U hUV' hV M L theta ht
  let F : Lp ℝ V 2 := (hf V hV).toLp f
  have hF : (F : Space n → ℝ) =ᵐ[domainMeasure V] f := (hf V hV).coeFn_toLp
  have heqF : WeakEquation V A v F := by
    intro φ
    rw [heq V hV v hv φ]
    exact integral_congr_ae (hF.symm.mul Filter.EventuallyEq.rfl)
  obtain ⟨w, hw, _⟩ := hC A hbound v F heqF
  exact ⟨w, hw.trans (ae_restrict_of_ae_restrict_of_subset hsub hv)⟩


/-- A bounded continuous coefficient field sends an L² gradient to an L² flux.
This is a measurability and norm assertion, with no PDE regularity input. -/
lemma flux_memLp {n : ℕ} (V : Domain n)
    (A : Space n → Space n →L[ℝ] Space n) (g : MeasureTheory.Lp (Space n) 2 (domainMeasure V))
    (hA : ContinuousOn A V) {M : ℝ} (hM : ∀ x ∈ V, ‖A x‖ ≤ M) :
    MemLp (fun x => A x (g x)) 2 (domainMeasure V) := by
  apply (Lp.memLp g).of_le_mul
    ((isBoundedBilinearMap_apply (𝕜 := ℝ)).continuous.comp_aestronglyMeasurable₂
      (hA.aestronglyMeasurable V.isOpen.measurableSet) (Lp.memLp g).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem V.isOpen.measurableSet] with x hx
  exact (A x).le_opNorm (g x) |>.trans
    (mul_le_mul_of_nonneg_right (hM x hx) (norm_nonneg _))

/-- Smooth interior tests extend to the actual full-H¹ closure, for the L²
source and the original (possibly nonsymmetric) coefficients. -/
theorem weakEquation_energy {n : ℕ} (hn : 1 ≤ n) (V : Domain n)
    (A : Space n → Space n →L[ℝ] Space n) (v : H ℝ V 1) (f : Lp ℝ V 2)
    (hA : ContinuousOn A V) {M : ℝ} (hM : ∀ x ∈ V, ‖A x‖ ≤ M)
    (heq : WeakEquation V A v f) (w : H10 ℝ V) :
    (∫ x in V, inner ℝ (A x (hGradient v x)) (hGradient w.val x)) =
      ∫ x in V, f x * hZeroUnderlying V w x := by
  let hm := flux_memLp V A (hGradient v) hA hM
  let F : MeasureTheory.Lp (Space n) 2 (domainMeasure V) := hm.toLp _
  have hF : (F : Space n → Space n) =ᵐ[domainMeasure V]
      (fun x => A x (hGradient v x)) := hm.coeFn_toLp
  have htest (φ : Test ℝ V) (z : H10 ℝ V)
      (hz : hZeroUnderlying V z = P102.U4.testToDomainLp V 2 φ) :
      negativeDivergenceDistribution V F φ = pivot V f z := by
    rw [InteriorTesting.negativeDivergenceDistribution_pairing, pivotPairing, hz]
    change (∫ x in V, inner ℝ (F x) (gradient φ x)) = _
    calc
      _ = ∫ x in V, inner ℝ (A x (hGradient v x)) (gradient φ x) := by
        apply integral_congr_ae
        filter_upwards [hF] with x hx
        rw [hx]
      _ = ∫ x in V, f x * φ x := heq φ
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [P102.U4.testToDomainLp_ae V 2 φ] with x hx
        rw [hx]
  have he := InteriorTesting.energyTesting hn V F (pivot V f) htest w
  rw [pivotPairing] at he
  refine (integral_congr_ae ?_).trans he
  filter_upwards [hF] with x hx
  rw [hx]


/-- Essential compact support inside an arbitrary open set suffices for H¹₀
membership. The proof mollifies the zero extension with a fixed boundary buffer;
there is no boundary regularity or boundary value assumption. -/
theorem compactSupport_mem_hZero {n : ℕ} (V : Domain n) (v : H ℝ V 1)
    (hv : P102.U4.HasCompactSupportIn (hUnderlying V 1 v)) :
    v ∈ P201Specs.hZeroSubmodule ℝ V := by
  let u := hToW ℝ V 1 v
  obtain ⟨K, hKV, hK⟩ := hv
  obtain ⟨z, hz, _, _⟩ := P102.U4.zeroExtension_compact V 1 2 (by norm_num) u
    ⟨K, hKV, hK⟩
  have hzK : ∀ᵐ x ∂volume, x ∉ K → P102.U4.sobolevUnderlying z x = 0 := by
    rw [hz]
    have hK' := (ae_restrict_iff' V.isOpen.measurableSet).mp hK
    filter_upwards [P102.U4.lpZeroExtension_ae V 2 (P102.U4.sobolevUnderlying u), hK']
      with x hx hxK hxnot
    rw [hx]
    by_cases hxV : x ∈ V
    · rw [indicator_of_mem hxV]
      exact hxK hxV hxnot
    · exact indicator_of_notMem hxV _
  obtain ⟨δ, hδ, _, hbuffer⟩ := P102.U4.exists_supportRadius K hKV (by norm_num : (0 : ℝ) < 1)
  have huclosure : u ∈ (P102.U4.smoothSobolevSubmodule ℝ V 1 2).topologicalClosure := by
    change u ∈ closure (P102.U4.smoothSobolevSubmodule ℝ V 1 2 : Set _)
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨φ, z', hφ, herr, hs⟩ := P102.U4.exists_mollified_approximation
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) z K hzK hδ hε
    let φV : Test ℝ V := ⟨φ, φ.contDiff, φ.hasCompactSupport, hs.trans hbuffer⟩
    let w := P102.U4.sobolevRestrict V z'
    have hwφ : P102.U4.sobolevUnderlying w = P102.U4.testToDomainLp V 2 φV := by
      apply MeasureTheory.Lp.ext
      have hφ0 := hφ (P102.U4.zeroSobolevIndex n 1)
      simp only [P102.U4.zeroSobolevIndex, P102.U4.multiPartial,
        Multiset.sort_zero, P102.U4.partialWord] at hφ0
      exact ((P102.U4.domainLpRestrict_ae V (P102.U4.sobolevUnderlying z')).trans
        (ae_restrict_of_ae hφ0)).trans (P102.U4.testToDomainLp_ae V 2 φV).symm
    have hback : P102.U4.sobolevRestrict V z = u := by
      apply P102.U4.sobolevUnderlying_injective V 1 2
      change P102.U4.domainLpRestrict V (P102.U4.sobolevUnderlying z) = _
      rw [hz, P102.U4.domainLpRestrict_zeroExtension]
    refine ⟨w, ⟨φV, hwφ.symm⟩, ?_⟩
    rw [dist_comm, dist_eq_norm]
    calc
      ‖w - u‖ = ‖P102.U4.sobolevRestrict V (z' - z)‖ := by
        rw [← hback]
        exact congrArg norm ((P102.U4.sobolevRestrictCLM V).map_sub z' z).symm
      _ ≤ ‖z' - z‖ := P102.U4.sobolevRestrict_norm_le V _
      _ < ε := herr
  rw [hZeroClosureBridge ℝ V]
  exact huclosure

/-- Translation preserves local weak derivatives when the translated test
support stays inside the original open set. -/
lemma weakDerivative_translate {n : ℕ} (U V : Domain n) (a : Space n)
    (ha : (fun x => x + a) '' (U : Set (Space n)) ⊆ V)
    (u d : Space n → ℝ) (j : Fin n)
    (hu : LocallyIntegrableOn u V volume) (hd : LocallyIntegrableOn d V volume)
    (hu' : LocallyIntegrableOn (fun x => u (x + a)) U volume)
    (hd' : LocallyIntegrableOn (fun x => d (x + a)) U volume)
    (hweak : distributionDerivative {j} (regularDistribution V u) = regularDistribution V d) :
    distributionDerivative {j} (regularDistribution U (fun x => u (x + a))) =
      regularDistribution U (fun x => d (x + a)) := by
  apply (P102.U4.ACL.weak_iff_test_identity j hu' hd').mpr
  intro φ
  have hs : tsupport (fun x => φ (x - a)) ⊆ (V : Set (Space n)) := by
    intro x hx
    have hx' := tsupport_comp_subset_preimage (f := fun x => x - a) φ (by fun_prop) hx
    have hxU := φ.tsupport_subset hx'
    simpa only [sub_add_cancel] using ha (mem_image_of_mem _ hxU)
  let ψ : Test ℝ V := ⟨fun x => φ (x - a),
    φ.contDiff.comp (contDiff_id.sub contDiff_const),
    φ.hasCompactSupport.comp_homeomorph (Homeomorph.subRight a), hs⟩
  have hψj (x : Space n) : P102.U4.testPartialWord V [j] ψ x =
      P102.U4.testPartialWord U [j] φ (x - a) := by
    rw [P102.U4.testPartialWord_coe, P102.U4.testPartialWord_coe]
    change fderiv ℝ (fun y => φ (y - a)) x (coordinate n j) = _
    rw [fderiv_comp_sub]
    rfl
  have hleft : (∫ x, φ x * d (x + a)) = ∫ x, ψ x * d x := by
    simpa only [show ∀ x, ψ (x + a) = φ x from fun x => by
      change φ (x + a - a) = φ x; rw [add_sub_cancel_right]] using
      integral_add_right_eq_self (fun x => ψ x * d x) a
  rw [hleft, (P102.U4.ACL.weak_iff_test_identity j hu hd).mp hweak ψ]
  congr 1
  simpa only [hψj, add_sub_cancel_right] using
    (integral_add_right_eq_self (fun x => P102.U4.testPartialWord V [j] ψ x * u x) a).symm

/-- Translated L² representatives on an admissible smaller domain remain L². -/
lemma translated_memLp {n : ℕ} {U V : Domain n} (a : Space n)
    (ha : (fun x => x + a) '' (U : Set (Space n)) ⊆ V) (u : Lp ℝ V 2) :
    MemLp (fun x => u (x + a)) 2 (domainMeasure U) :=
  (DifferenceQuotients.translatedNorm_le (MeasureTheory.Lp.stronglyMeasurable u) a ha 2).trans_lt
    (Lp.memLp u)

/-- First-order reconstruction uses only the distributional identities. -/
theorem h1FromWeakDerivatives {n : ℕ} (U : Domain n) (u : Lp ℝ U 2)
    (d : Fin n → Lp ℝ U 2)
    (hd : ∀ j, distributionDerivative {j} (regularDistribution U u) =
      regularDistribution U (d j)) :
    ∃ v : H ℝ U 1, hUnderlying U 1 v = u ∧ ∀ j, hFirstDerivative v j = d j := by
  have hsob : P102.U4.HasSobolevDerivatives U 1 2 u := by
    intro α hα
    have hc : α.card = 0 ∨ α.card = 1 := by omega
    rcases hc with hc | hc
    · have hzero : α = 0 := Multiset.card_eq_zero.mp hc
      subst α
      exact ⟨u, P102.U4.derivative_zero n ℝ U _⟩
    · obtain ⟨j, rfl⟩ := Multiset.card_eq_one.mp hc
      exact ⟨d j, hd j⟩
  obtain ⟨w, hw⟩ := (Set.ext_iff.mp (P102.U4.sobolev_range U 1 2) u).mpr hsob
  let v := (hToW ℝ U 1).symm w
  have hv : hUnderlying U 1 v = u := by
    change P102.U4.sobolevUnderlying ((hToW ℝ U 1) v) = u
    simpa only [v, ContinuousLinearEquiv.apply_symm_apply] using hw
  refine ⟨v, hv, fun j => ?_⟩
  symm
  apply P102.U4.sobolev_derivative_unique U 1 2 ((hToW ℝ U 1) v) ⟨{j}, by simp⟩
  change distributionDerivative {j} (regularDistribution U (hUnderlying U 1 v)) = _
  rw [hv]
  exact hd j

/-- A translated H¹ class on an admissible smaller open set, with its actual
translated gradient coordinates. This holds for each fixed translation and
requires no second derivatives. -/
theorem h1Translate {n : ℕ} (U V : Domain n) (a : Space n)
    (ha : (fun x => x + a) '' (U : Set (Space n)) ⊆ V) (v : H ℝ V 1) :
    ∃ w : H ℝ U 1,
      (hUnderlying U 1 w : Space n → ℝ) =ᵐ[domainMeasure U]
        (fun x => hUnderlying V 1 v (x + a)) ∧
      ∀ j, (hFirstDerivative w j : Space n → ℝ) =ᵐ[domainMeasure U]
        (fun x => hFirstDerivative v j (x + a)) := by
  let hu := translated_memLp a ha (hUnderlying V 1 v)
  let hd (j : Fin n) := translated_memLp a ha (hFirstDerivative v j)
  let u : Lp ℝ U 2 := hu.toLp _
  let d : Fin n → Lp ℝ U 2 := fun j => (hd j).toLp _
  have huR : regularDistribution U u =
      regularDistribution U (fun x => hUnderlying V 1 v (x + a)) := by
    exact (P102.U4.regular_injectivity n ℝ U _ _ (P102.U4.domainLp_locallyIntegrable U 2 u)
      (locallyIntegrableOn_of_locallyIntegrable_restrict (hu.locallyIntegrable (by norm_num)))).mpr
      hu.coeFn_toLp
  have hdR (j : Fin n) : regularDistribution U (d j) =
      regularDistribution U (fun x => hFirstDerivative v j (x + a)) := by
    exact (P102.U4.regular_injectivity n ℝ U _ _ (P102.U4.domainLp_locallyIntegrable U 2 (d j))
      (locallyIntegrableOn_of_locallyIntegrable_restrict ((hd j).locallyIntegrable (by norm_num)))).mpr
      (hd j).coeFn_toLp
  obtain ⟨w, hw, hwd⟩ := h1FromWeakDerivatives U u d (fun j => by
    rw [huR, hdR]
    apply weakDerivative_translate U V a ha _ _ j
      (P102.U4.domainLp_locallyIntegrable V 2 _)
      (P102.U4.domainLp_locallyIntegrable V 2 _)
      (locallyIntegrableOn_of_locallyIntegrable_restrict (hu.locallyIntegrable (by norm_num)))
      (locallyIntegrableOn_of_locallyIntegrable_restrict ((hd j).locallyIntegrable (by norm_num)))
    exact hilbertDerivativeDistribution V 1 v ⟨{j}, by simp⟩)
  refine ⟨w, ?_, fun j => ?_⟩
  · rw [hw]; exact hu.coeFn_toLp
  · rw [hwd]; exact (hd j).coeFn_toLp

/-- Difference quotients of H¹ functions are H¹ on every admissible smaller
open set. Their weak derivatives commute with the quotient at each fixed step. -/
theorem h1Quotient {n : ℕ} (U V : Domain n) (hUV : U ≤ V)
    (k : Fin n) (h : ℝ)
    (ha : ∀ x ∈ U, x + h • coordinate n k ∈ V) (v : H ℝ V 1) :
    ∃ q : H ℝ U 1,
      (hUnderlying U 1 q : Space n → ℝ) =ᵐ[domainMeasure U]
        differenceQuotient (hUnderlying V 1 v) k h ∧
      ∀ j, (hFirstDerivative q j : Space n → ℝ) =ᵐ[domainMeasure U]
        differenceQuotient (hFirstDerivative v j) k h := by
  obtain ⟨va, hva, hvad⟩ := h1Translate U V (h • coordinate n k)
    (by rintro _ ⟨x, hx, rfl⟩; exact ha x hx) v
  obtain ⟨v0, hv0, hv0d⟩ := h1Translate U V 0
    (by
      rintro x ⟨y, hy, hxy⟩
      have he : y = x := (add_zero y).symm.trans hxy
      exact he ▸ hUV hy) v
  simp only [add_zero] at hv0 hv0d
  let q : H ℝ U 1 := h⁻¹ • (va - v0)
  have hq : hUnderlying U 1 q =
      h⁻¹ • (hUnderlying U 1 va - hUnderlying U 1 v0) := by
    exact (hUnderlying U 1).map_smul h⁻¹ (va - v0) |>.trans
      (congrArg (fun z => h⁻¹ • z) ((hUnderlying U 1).map_sub va v0))
  have hqd (j : Fin n) : hFirstDerivative q j =
      h⁻¹ • (hFirstDerivative va j - hFirstDerivative v0 j) := by
    change InteriorTesting.firstDerivativeMap U j (h⁻¹ • (va - v0)) = _
    rw [map_smul, map_sub]
    rfl
  refine ⟨q, ?_, fun j => ?_⟩
  · rw [hq]
    filter_upwards [MeasureTheory.Lp.coeFn_smul h⁻¹
      (hUnderlying U 1 va - hUnderlying U 1 v0),
      MeasureTheory.Lp.coeFn_sub (hUnderlying U 1 va) (hUnderlying U 1 v0), hva, hv0]
      with x hsm hsub hx hy
    simpa only [Pi.smul_apply, Pi.sub_apply, RingHom.id_apply, hsub, hx, hy,
      differenceQuotient, P201Specs.differenceQuotient, P102.U4.DifferenceQuotient.quotient]
      using hsm
  · rw [hqd]
    filter_upwards [MeasureTheory.Lp.coeFn_smul h⁻¹
      (hFirstDerivative va j - hFirstDerivative v0 j),
      MeasureTheory.Lp.coeFn_sub (hFirstDerivative va j) (hFirstDerivative v0 j), hvad j, hv0d j]
      with x hsm hsub hx hy
    simpa only [Pi.smul_apply, Pi.sub_apply, RingHom.id_apply, hsub, hx, hy,
      differenceQuotient, P201Specs.differenceQuotient, P102.U4.DifferenceQuotient.quotient]
      using hsm

/-- Smooth localization supplies an actual H¹₀ test and its weak product rule.
The input is only H¹; neither it nor its weak derivative is assumed smooth. -/
theorem h1TestProduct {n : ℕ} (V : Domain n) (φ : Test ℝ V) (v : H ℝ V 1) :
    ∃ w : H10 ℝ V,
      (hZeroUnderlying V w : Space n → ℝ) =ᵐ[domainMeasure V]
        (fun x => φ x * hUnderlying V 1 v x) ∧
      ∀ j, (hFirstDerivative w.val j : Space n → ℝ) =ᵐ[domainMeasure V]
        (fun x => φ x * hFirstDerivative v j x +
          fderiv ℝ φ x (coordinate n j) * hUnderlying V 1 v x) := by
  obtain ⟨z, hz, hc⟩ := P102.U4.exists_sobolev_testProduct φ ((hToW ℝ V 1) v)
  let w : H ℝ V 1 := (hToW ℝ V 1).symm z
  have hw : (hUnderlying V 1 w : Space n → ℝ) =ᵐ[domainMeasure V]
      (fun x => φ x * hUnderlying V 1 v x) := by
    change (P102.U4.sobolevUnderlying ((hToW ℝ V 1) w) : Space n → ℝ) =ᵐ[domainMeasure V] _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact hz
  have hwc : P102.U4.HasCompactSupportIn (hUnderlying V 1 w) := by
    change P102.U4.HasCompactSupportIn (P102.U4.sobolevUnderlying ((hToW ℝ V 1) w))
    simpa only [w, ContinuousLinearEquiv.apply_symm_apply] using hc
  refine ⟨⟨w, compactSupport_mem_hZero V w hwc⟩, hw, fun j => ?_⟩
  let φj := P102.U4.testPartialWord V [j] φ
  obtain ⟨b, hb, hbae⟩ := P102.U4.exists_regular_testProduct φ (hFirstDerivative v j)
  obtain ⟨c, hc, hcae⟩ := P102.U4.exists_regular_testProduct φj (hUnderlying V 1 v)
  obtain ⟨a, ha, haae⟩ := P102.U4.exists_regular_testProduct φ (hUnderlying V 1 v)
  have hwa : hUnderlying V 1 w = a := MeasureTheory.Lp.ext (hw.trans haae.symm)
  have hder : distributionDerivative {j} (regularDistribution V (hUnderlying V 1 w)) =
      regularDistribution V (b + c) := by
    change P102.U4.distributionPartial {j} (P102.U4.regularDistribution V
      (hUnderlying V 1 w)) = P102.U4.regularDistribution V (b + c)
    rw [hwa, ha]
    rw [P102.U4.distributionMultiplier_productRule]
    have hfirst := hilbertDerivativeDistribution V 1 v ⟨{j}, by simp⟩
    change P102.U4.distributionPartial {j} (P102.U4.regularDistribution V (hUnderlying V 1 v)) = _ at hfirst
    rw [hfirst, ← hb]
    have hcoeff : P102.U4.coefficientPartial j ⟨φ, φ.contDiff.contDiffOn⟩ =
        (⟨φj, φj.contDiff.contDiffOn⟩ : P102.U4.SmoothCoefficient ℝ V) := by
      apply Subtype.ext
      exact (P102.U4.testPartialWord_coe V [j] φ).symm
    rw [hcoeff, ← hc]
    ext ψ
    simp only [add_apply, P102.U4.regularLp_pairing V 2]
    rw [map_add, add_comm]
  have hwd : hFirstDerivative w j = b + c := by
    symm
    exact P102.U4.sobolev_derivative_unique V 1 2 ((hToW ℝ V 1) w) ⟨{j}, by simp⟩ (b + c) hder
  change (hFirstDerivative w j : Space n → ℝ) =ᵐ[domainMeasure V] _
  rw [hwd]
  filter_upwards [MeasureTheory.Lp.coeFn_add b c, hbae, hcae] with x hx hb' hc'
  rw [hx, Pi.add_apply, hb', hc']
  rw [show φj x = fderiv ℝ φ x (coordinate n j) from
    congrFun (P102.U4.testPartialWord_coe V [j] φ) x]

/-- Compactly supported H¹ classes extend by zero with every weak derivative,
and with exactly their full Hilbert norm. -/
theorem h1ZeroExtension {n : ℕ} (V : Domain n) (v : H ℝ V 1)
    (hv : P102.U4.HasCompactSupportIn (hUnderlying V 1 v)) :
    ∃ z : H ℝ (⊤ : Domain n) 1,
      hUnderlying ⊤ 1 z = P102.U4.lpZeroExtension V 2 (hUnderlying V 1 v) ∧
      (∀ j, hFirstDerivative z j = P102.U4.lpZeroExtension V 2 (hFirstDerivative v j)) ∧
      ‖z‖ = ‖v‖ := by
  obtain ⟨w, hw, hwd, _⟩ := P102.U4.zeroExtension_compact V 1 2
    (by norm_num) ((hToW ℝ V 1) v) hv
  let z : H ℝ (⊤ : Domain n) 1 := (hToW ℝ ⊤ 1).symm w
  have hzW : (hToW ℝ ⊤ 1) z = w := ContinuousLinearEquiv.apply_symm_apply _ _
  have hz : hUnderlying ⊤ 1 z = P102.U4.lpZeroExtension V 2 (hUnderlying V 1 v) := by
    change P102.U4.sobolevUnderlying ((hToW ℝ ⊤ 1) z) = _
    rw [hzW]
    exact hw
  have hzd (j : Fin n) : hFirstDerivative z j =
      P102.U4.lpZeroExtension V 2 (hFirstDerivative v j) := by
    change P102.U4.sobolevDerivative ((hToW ℝ ⊤ 1) z) ⟨{j}, by simp⟩ = _
    rw [hzW]
    exact hwd _
  refine ⟨z, hz, hzd, ?_⟩
  apply (sq_eq_sq₀ (norm_nonneg z) (norm_nonneg v)).mp
  rw [fullHilbertNorm ⊤ 1 z, fullHilbertNorm V 1 v, hzW]
  apply Finset.sum_congr rfl
  intro α _
  rw [hwd, P102.U4.lpZeroExtension_norm]

/-- One step radius works for both signs and every coordinate on a compact
subset. This is a geometric boundary buffer, independent of the solution. -/
lemma compact_step_buffer {n : ℕ} (V : Domain n) (K : Compacts (Space n))
    (hK : (K : Set (Space n)) ⊆ V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (j : Fin n) (h : ℝ), |h| < δ →
      ∀ x ∈ K, x + h • coordinate n j ∈ V := by
  obtain ⟨δ, hδ, hsub⟩ := K.isCompact.exists_cthickening_subset_open V.isOpen hK
  refine ⟨δ, hδ, fun j h hh x hx => ?_⟩
  apply hsub
  apply Metric.mem_cthickening_of_dist_le _ x δ _ hx
  simpa only [dist_eq_norm, add_sub_cancel_left, norm_smul,
    P102.U4.DifferenceQuotient.norm_coordinateVector, mul_one, Real.norm_eq_abs]
    using hh.le

/-- A compactly supported whole-space H¹ difference is an admissible H¹₀ test
when the support and its inverse translate lie inside the testing domain. -/
theorem h1CompactQuotient {n : ℕ} (V : Domain n) (z : H ℝ (⊤ : Domain n) 1)
    (K : Compacts (Space n)) (hKV : (K : Set (Space n)) ⊆ V)
    (hK : ∀ᵐ x ∂volume, x ∉ K → hUnderlying ⊤ 1 z x = 0)
    (k : Fin n) (h : ℝ)
    (ha : ∀ x ∈ K, x - h • coordinate n k ∈ V) :
    ∃ t : H10 ℝ V,
      (hZeroUnderlying V t : Space n → ℝ) =ᵐ[domainMeasure V]
        differenceQuotient (hUnderlying ⊤ 1 z) k h ∧
      ∀ j, (hFirstDerivative t.val j : Space n → ℝ) =ᵐ[domainMeasure V]
        differenceQuotient (hFirstDerivative z j) k h := by
  obtain ⟨q, hq, hqd⟩ := h1Quotient V ⊤ le_top k h (fun _ _ => mem_univ _) z
  let a := h • coordinate n k
  let K' : Compacts (Space n) :=
    ⟨(K : Set (Space n)) ∪ (fun x => x - a) '' (K : Set (Space n)),
      K.isCompact.union (K.isCompact.image (by fun_prop))⟩
  have hK'V : (K' : Set (Space n)) ⊆ V := by
    rintro x (hx | ⟨y, hy, rfl⟩)
    · exact hKV hx
    · exact ha y hy
  have hKtrans : ∀ᵐ x ∂volume, x + a ∉ K → hUnderlying ⊤ 1 z (x + a) = 0 :=
    (measurePreserving_add_right volume a).quasiMeasurePreserving.ae hK
  have hqc : P102.U4.HasCompactSupportIn (hUnderlying V 1 q) := by
    refine ⟨K', hK'V, ?_⟩
    filter_upwards [hq, ae_restrict_of_ae hK, ae_restrict_of_ae hKtrans]
      with x hx hxK hxtrans hxnot
    have hxK' : x ∉ K := fun hx => hxnot (Or.inl hx)
    have hxaK : x + a ∉ K := by
      intro hx
      apply hxnot
      exact Or.inr ⟨x + a, hx, add_sub_cancel_right x a⟩
    rw [hx]
    change h⁻¹ • (hUnderlying ⊤ 1 z (x + a) - hUnderlying ⊤ 1 z x) = 0
    rw [hxK hxK', hxtrans hxaK, sub_self, smul_zero]
  exact ⟨⟨q, compactSupport_mem_hZero V q hqc⟩, hq, hqd⟩

/-- Scalar coordinates of the genuine L² flux class. -/
def fluxCoordinate {n : ℕ} {V : Domain n}
    (F : MeasureTheory.Lp (Space n) 2 (domainMeasure V)) (j : Fin n) : Lp ℝ V 2 :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) j).compLp F

lemma fluxFunctional_eq_sum {n : ℕ} (V : Domain n)
    (F : MeasureTheory.Lp (Space n) 2 (domainMeasure V)) (w : H ℝ V 1) :
    InteriorTesting.fluxFunctional V F w =
      ∑ j : Fin n, ∫ x in V, fluxCoordinate F j x * hFirstDerivative w j x := by
  simp only [InteriorTesting.fluxFunctional, sum_apply, ContinuousLinearMap.comp_apply,
    InteriorTesting.firstDerivativeMap_apply, innerSL_apply_apply, L2.inner_def]
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [fluxCoordinate, RCLike.inner_apply, conj_trivial]
  exact mul_comm _ _

/-- The discrete energy identity is valid for compactly supported H¹ tests,
with no differentiability of the L² source. All flux and test coordinates are
actual L² classes, and support separation is explicit. -/
theorem discrete_energy_identity {n : ℕ} (hn : 1 ≤ n) (V : Domain n)
    (F : MeasureTheory.Lp (Space n) 2 (domainMeasure V)) (f : Lp ℝ V 2)
    (heq : ∀ φ : Test ℝ V,
      (∫ x in V, inner ℝ (F x) (gradient φ x)) = ∫ x in V, f x * φ x)
    (z : H ℝ (⊤ : Domain n) 1) (K : Compacts (Space n))
    (hKV : (K : Set (Space n)) ⊆ V)
    (hK : ∀ᵐ x ∂volume, x ∉ K → hUnderlying ⊤ 1 z x = 0)
    (k : Fin n) (h : ℝ) (hh : h ≠ 0)
    (ha : ∀ x ∈ K, x + h • coordinate n k ∈ V) :
    (∑ j : Fin n, ∫ x,
      differenceQuotient (P102.U4.lpZeroExtension V 2 (fluxCoordinate F j)) k h x *
        hFirstDerivative z j x) =
      -(∫ x in V, f x * differenceQuotient (hUnderlying ⊤ 1 z) k (-h) x) := by
  obtain ⟨t, ht, htd⟩ := h1CompactQuotient V z K hKV hK k (-h) (by
    intro x hx
    simpa only [neg_smul, sub_neg_eq_add] using ha x hx)
  have htest (φ : Test ℝ V) (w : H10 ℝ V)
      (hw : hZeroUnderlying V w = P102.U4.testToDomainLp V 2 φ) :
      negativeDivergenceDistribution V F φ = pivot V f w := by
    rw [InteriorTesting.negativeDivergenceDistribution_pairing, pivotPairing, hw]
    change (∫ x in V, inner ℝ (F x) (gradient φ x)) = _
    rw [heq φ]
    apply integral_congr_ae
    filter_upwards [P102.U4.testToDomainLp_ae V 2 φ] with x hx
    rw [hx]
  have henergy := InteriorTesting.energyTesting hn V F (pivot V f) htest t
  rw [pivotPairing] at henergy
  have hcoord (j : Fin n) :
      (∫ x, differenceQuotient (P102.U4.lpZeroExtension V 2 (fluxCoordinate F j)) k h x *
        hFirstDerivative z j x) =
      -(∫ x in V, fluxCoordinate F j x * hFirstDerivative t.val j x) := by
    have hF : MemLp (P102.U4.lpZeroExtension V 2 (fluxCoordinate F j) : Space n → ℝ)
        2 volume := by
      simpa only [Opens.coe_top, Measure.restrict_univ] using
        (MeasureTheory.Lp.memLp (P102.U4.lpZeroExtension V 2 (fluxCoordinate F j)))
    have hz : MemLp (hFirstDerivative z j : Space n → ℝ) 2 volume := by
      simpa only [domainMeasure, P201Specs.domainMeasure, Opens.coe_top, Measure.restrict_univ]
        using (MeasureTheory.Lp.memLp (hFirstDerivative z j))
    have hzT : MemLp (fun x => hFirstDerivative z j (x - h • coordinate n k)) 2 volume :=
      hz.comp_measurePreserving (measurePreserving_sub_right volume _)
    rw [discreteIntegrationByPartsWholeSpace hn _ _ k h hh
      (hF.integrable_mul hz) (hF.integrable_mul hzT)]
    rw [P102.U4.integral_lpZeroExtension_mul V 2]
    congr 1
    apply integral_congr_ae
    filter_upwards [htd j] with x hx
    rw [hx]
  simp_rw [hcoord]
  rw [Finset.sum_neg_distrib, ← fluxFunctional_eq_sum, InteriorTesting.fluxFunctional_integral,
    henergy]
  congr 1
  apply integral_congr_ae
  filter_upwards [ht] with x hx
  rw [hx]



lemma hGradient_ae {n : ℕ} {V : Domain n} (v : H ℝ V 1) :
    (hGradient v : Space n → Space n) =ᵐ[domainMeasure V]
      (fun x => WithLp.toLp 2 (fun j => hFirstDerivative v j x)) :=
  MemLp.coeFn_toLp _

lemma hGradient_norm_sq {n : ℕ} {V : Domain n} (v : H ℝ V 1) :
    ‖hGradient v‖ ^ 2 = ∑ j : Fin n, ‖hFirstDerivative v j‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  have hpoint : (fun x => inner ℝ (hGradient v x) (hGradient v x)) =ᵐ[domainMeasure V]
      (fun x => ∑ j : Fin n, hFirstDerivative v j x ^ 2) := by
    filter_upwards [hGradient_ae v] with x hx
    rw [hx, real_inner_self_eq_norm_sq, PiLp.norm_sq_eq_of_L2]
    simp only [Real.norm_eq_abs, sq_abs]
  rw [integral_congr_ae hpoint, integral_finsetSum _ (fun j _ => (Lp.memLp _).integrable_sq)]
  apply Finset.sum_congr rfl
  intro j _
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext x
  simp [pow_two]

lemma hGradient_norm_le {n : ℕ} {V : Domain n} (v : H ℝ V 1) :
    ‖hGradient v‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [hGradient_norm_sq, fullHilbertNorm V 1 v]
  apply Finset.sum_le_sum_of_injOn
    (fun j : Fin n => (⟨{j}, by simp⟩ : P102.U4.SobolevIndex n 1))
  · intro j hj k hk h
    have h' : ({j} : Multiset (Fin n)) = {k} := congrArg Subtype.val h
    simpa only [Multiset.singleton_inj] using h'
  · intro j hj
    change j ∈ (Finset.univ : Finset (P102.U4.SobolevIndex n 1))
    simp
  · intro j hj
    exact le_rfl
  · intro j hj _
    exact sq_nonneg _

lemma ae_eq_translate_local {n : ℕ} {E : Type*}
    {U V : Domain n} {f g : Space n → E}
    (hfg : f =ᵐ[domainMeasure V] g) (a : Space n)
    (ha : (fun x => x + a) '' (U : Set (Space n)) ⊆ V) :
    (fun x => f (x + a)) =ᵐ[domainMeasure U] (fun x => g (x + a)) := by
  exact ((measurePreserving_add_right volume a).restrict_image_emb
    (Homeomorph.addRight a).measurableEmbedding (U : Set (Space n))).quasiMeasurePreserving.ae
      (ae_restrict_of_ae_restrict_of_subset ha hfg)

lemma hGradient_quotient_ae {n : ℕ} (U V : Domain n) (hUV : U ≤ V)
    (v : H ℝ V 1) (k : Fin n) (h : ℝ)
    (ha : ∀ x ∈ U, x + h • coordinate n k ∈ V) :
    (fun x => h⁻¹ • (hGradient v (x + h • coordinate n k) - hGradient v x))
      =ᵐ[domainMeasure U]
    (fun x => WithLp.toLp 2 (fun j => differenceQuotient (hFirstDerivative v j) k h x)) := by
  have ht := ae_eq_translate_local (hGradient_ae v) (h • coordinate n k)
    (by rintro _ ⟨x, hx, rfl⟩; exact ha x hx)
  filter_upwards [ht, ae_restrict_of_ae_restrict_of_subset hUV (hGradient_ae v)]
    with x hx hy
  rw [hx, hy]
  apply PiLp.ext
  intro j
  rfl

/-- Assemble coordinate product formulas into the actual L² weak gradient. -/
lemma hGradient_product_ae {n : ℕ} (z : H ℝ (⊤ : Domain n) 1)
    (η q : Space n → ℝ) (d : Fin n → Space n → ℝ)
    (hzd : ∀ j, (hFirstDerivative z j : Space n → ℝ) =ᵐ[volume]
      (fun x => η x ^ 2 * d j x +
        2 * η x * fderiv ℝ η x (coordinate n j) * q x)) :
    (hGradient z : Space n → Space n) =ᵐ[volume]
      (fun x => η x ^ 2 • WithLp.toLp 2 (fun j => d j x) +
        (2 * η x * q x) • gradient η x) := by
  have hg := hGradient_ae z
  simp only [domainMeasure, P201Specs.domainMeasure, Opens.coe_top,
    Measure.restrict_univ] at hg
  filter_upwards [hg, ae_all_iff.mpr hzd] with x hx hxd
  rw [hx]
  apply PiLp.ext
  intro j
  change hFirstDerivative z j x = η x ^ 2 * d j x +
    (2 * η x * q x) * fderiv ℝ η x (coordinate n j)
  rw [hxd j]
  ring




theorem wholeSpace_quotient_bound {n : ℕ}
    (z : H ℝ (⊤ : Domain n) 1) (j : Fin n) (h : ℝ) (hh : h ≠ 0)
    (hdint : Integrable (hFirstDerivative z j : Space n → ℝ) volume) :
    MemLp (differenceQuotient (hUnderlying ⊤ 1 z) j h) 2 volume ∧
      eLpNorm (differenceQuotient (hUnderlying ⊤ 1 z) j h) 2 volume ≤
        eLpNorm (hFirstDerivative z j) 2 volume := by
  have hs : P201Specs.AdmissibleSegments (⊤ : Domain n) ⊤ j h := by
    intro x hx t ht
    trivial
  have hr := P102.U4.ACL.weak_to_representative j
    (P102.U4.domainLp_locallyIntegrable ⊤ 2 (hUnderlying ⊤ 1 z))
    (P102.U4.domainLp_locallyIntegrable ⊤ 2 (hFirstDerivative z j))
    (hilbertDerivativeDistribution ⊤ 1 z ⟨{j}, by simp⟩)
  have hid := DifferenceQuotients.segmentAverage_eq_quotient ⊤ ⊤ j
    (hUnderlying ⊤ 1 z) (hFirstDerivative z j) hh hs hr hdint
  obtain ⟨hmem, hbound⟩ := DifferenceQuotients.segmentAverage_bound ⊤ ⊤ j h hs
    (Lp.stronglyMeasurable (hFirstDerivative z j)) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (Lp.memLp (hFirstDerivative z j))
  simp only [domainMeasure, P201Specs.domainMeasure, Opens.coe_top,
    Measure.restrict_univ] at hid hmem hbound
  refine ⟨(memLp_congr_ae hid).mp hmem, ?_⟩
  rw [← eLpNorm_congr_ae hid]
  exact hbound

lemma lpZeroExtension_integrable {n : ℕ} (V : Domain n)
    [IsFiniteMeasure (domainMeasure V)] (u : Lp ℝ V 2) :
    Integrable (P102.U4.lpZeroExtension V 2 u : Space n → ℝ) volume := by
  have hu : Integrable (u : Space n → ℝ) (domainMeasure V) :=
    (Lp.memLp u).integrable (by norm_num)
  have hi : Integrable ((V : Set (Space n)).indicator u) volume :=
    (integrable_indicator_iff V.isOpen.measurableSet).mpr hu
  exact hi.congr (P102.U4.lpZeroExtension_ae V 2 u).symm

lemma wholeSpace_quotient_bound_toReal {n : ℕ}
    (z : H ℝ (⊤ : Domain n) 1) (j : Fin n) (h : ℝ) (hh : h ≠ 0)
    (hdint : Integrable (hFirstDerivative z j : Space n → ℝ) volume) :
    (eLpNorm (differenceQuotient (hUnderlying ⊤ 1 z) j h) 2 volume).toReal ≤
      ‖hFirstDerivative z j‖ := by
  have hdne : eLpNorm (hFirstDerivative z j) 2 volume ≠ ∞ := by
    simpa only [domainMeasure, P201Specs.domainMeasure, Opens.coe_top,
      Measure.restrict_univ] using (Lp.memLp (hFirstDerivative z j)).eLpNorm_ne_top
  have hb := ENNReal.toReal_mono hdne (wholeSpace_quotient_bound z j h hh hdint).2
  simpa only [Lp.norm_def, domainMeasure, P201Specs.domainMeasure, Opens.coe_top,
    Measure.restrict_univ] using hb

/-- The constant-one derivative bound applies directly to the actual compactly
supported extension; no derivative of any forcing is involved. -/
theorem h1ZeroExtension_quotient_bound {n : ℕ} (V : Domain n)
    [IsFiniteMeasure (domainMeasure V)] (v : H ℝ V 1)
    (hv : P102.U4.HasCompactSupportIn (hUnderlying V 1 v)) :
    ∃ z : H ℝ (⊤ : Domain n) 1,
      hUnderlying ⊤ 1 z = P102.U4.lpZeroExtension V 2 (hUnderlying V 1 v) ∧
      (∀ j, hFirstDerivative z j = P102.U4.lpZeroExtension V 2 (hFirstDerivative v j)) ∧
      ‖z‖ = ‖v‖ ∧
      ∀ (j : Fin n) (h : ℝ), h ≠ 0 →
        MemLp (differenceQuotient (hUnderlying ⊤ 1 z) j h) 2 volume ∧
          (eLpNorm (differenceQuotient (hUnderlying ⊤ 1 z) j h) 2 volume).toReal ≤
            ‖hFirstDerivative v j‖ := by
  obtain ⟨z, hz, hzd, hzn⟩ := h1ZeroExtension V v hv
  refine ⟨z, hz, hzd, hzn, ?_⟩
  intro j h hh
  have hdint : Integrable (hFirstDerivative z j : Space n → ℝ) volume := by
    rw [hzd j]
    exact lpZeroExtension_integrable V _
  refine ⟨(wholeSpace_quotient_bound z j h hh hdint).1, ?_⟩
  have hb := wholeSpace_quotient_bound_toReal z j h hh hdint
  simpa only [hzd j, P102.U4.lpZeroExtension_norm] using hb

/-- The right side of the discrete energy identity only needs the L² source,
paired with a difference quotient of the compact H¹ test. -/
theorem wholeSpace_source_pairing_bound {n : ℕ} (V : Domain n)
    (z : H ℝ (⊤ : Domain n) 1) (j : Fin n) (h : ℝ) (hh : h ≠ 0)
    (hdint : Integrable (hFirstDerivative z j : Space n → ℝ) volume)
    (f : Lp ℝ V 2) :
    |∫ x in V, f x * differenceQuotient (hUnderlying ⊤ 1 z) j h x| ≤
      ‖f‖ * ‖hFirstDerivative z j‖ := by
  obtain ⟨hq, hqb⟩ := wholeSpace_quotient_bound z j h hh hdint
  have hqV := hq.mono_measure (Measure.restrict_le_self (s := (V : Set (Space n))))
  have hb := P102.U4.DifferenceQuotient.integral_mul_bound (p := 2) (q := 2)
    (Lp.memLp f) hqV
  have hm : (eLpNorm (differenceQuotient (hUnderlying ⊤ 1 z) j h) 2
      (domainMeasure V)).toReal ≤
      (eLpNorm (differenceQuotient (hUnderlying ⊤ 1 z) j h) 2 volume).toReal :=
    ENNReal.toReal_mono hq.eLpNorm_ne_top
      (eLpNorm_mono_measure _ (Measure.restrict_le_self))
  have hbt := wholeSpace_quotient_bound_toReal z j h hh hdint
  have hb' : |∫ x in V, f x * differenceQuotient (hUnderlying ⊤ 1 z) j h x| ≤
      (eLpNorm (differenceQuotient (hUnderlying ⊤ 1 z) j h) 2
        (domainMeasure V)).toReal * ‖f‖ := by
    simpa only [Real.norm_eq_abs, Lp.norm_def] using hb
  exact hb'.trans ((mul_le_mul_of_nonneg_right (hm.trans hbt)
    (norm_nonneg f)).trans_eq (mul_comm _ _))




lemma cutoff_data {n : ℕ} {U V : Domain n} (hUV : RelativelyCompactIn U V) :
    ∃ (η : Test ℝ V) (W : Domain n),
      (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧ (∀ x ∈ U, η x = 1) ∧
      RelativelyCompactIn W V ∧ tsupport η ⊆ W := by
  obtain ⟨η, hη, O, hUO, _, hηO⟩ :=
    P102.U4.cutoff n V ⟨closure (U : Set (Space n)), hUV.1⟩ hUV.2
  obtain ⟨W, hWV, hKW⟩ := P102.U4.DifferenceQuotient.exists_relativelyCompact_open
    η.hasCompactSupport η.tsupport_subset
  exact ⟨η, W, hη, fun x hx => hηO x (hUO (subset_closure hx)), hWV, hKW⟩

def squareTest {n : ℕ} (W : Domain n) (η : Test ℝ W) : Test ℝ W :=
  ⟨fun x => η x * η x, η.contDiff.mul η.contDiff,
    η.hasCompactSupport.mul_right, (tsupport_mul_subset_left (f := (η : Space n → ℝ)) (g := (η : Space n → ℝ))).trans η.tsupport_subset⟩

lemma squareTest_fderiv {n : ℕ} (W : Domain n) (η : Test ℝ W)
    (j : Fin n) (x : Space n) :
    fderiv ℝ (squareTest W η) x (coordinate n j) =
      2 * η x * fderiv ℝ η x (coordinate n j) := by
  change fderiv ℝ ((η : Space n → ℝ) * (η : Space n → ℝ)) x (coordinate n j) = _
  rw [fderiv_mul (η.contDiff.differentiable (by simp) x)
    (η.contDiff.differentiable (by simp) x)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

lemma compact_segment_buffer {n : ℕ} (V : Domain n) (K : Compacts (Space n))
    (hK : (K : Set (Space n)) ⊆ V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (j : Fin n) (h : ℝ), |h| < δ →
      ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, x + (t * h) • coordinate n j ∈ V := by
  obtain ⟨δ, hδ, hb⟩ := compact_step_buffer V K hK
  refine ⟨δ, hδ, fun j h hh x hx t ht => hb j (t * h) ?_ x hx⟩
  rw [abs_mul, abs_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (abs_nonneg h) ht.2).trans_lt hh

lemma zeroExtension_eq_ae {n : ℕ} (W : Domain n) (u : Lp ℝ W 2)
    (f : Space n → ℝ) (hf : (u : Space n → ℝ) =ᵐ[domainMeasure W] f)
    (hzero : ∀ x, x ∉ W → f x = 0) :
    (P102.U4.lpZeroExtension W 2 u : Space n → ℝ) =ᵐ[volume] f := by
  have hf' := (ae_restrict_iff' W.isOpen.measurableSet).mp hf
  filter_upwards [P102.U4.lpZeroExtension_ae W 2 u, hf'] with x hx hx'
  rw [hx]
  by_cases hxW : x ∈ W
  · rw [indicator_of_mem hxW, hx' hxW]
  · rw [indicator_of_notMem hxW, hzero x hxW]

/-- Whole-space compact H¹ test corresponding exactly to η²D_hu. -/
theorem localizedQuotient {n : ℕ} (W V : Domain n) (hWV : W ≤ V)
    (η : Test ℝ W) (k : Fin n) (h : ℝ)
    (ha : ∀ x ∈ W, x + h • coordinate n k ∈ V) (v : H ℝ V 1) :
    ∃ z : H ℝ (⊤ : Domain n) 1,
      (hUnderlying ⊤ 1 z : Space n → ℝ) =ᵐ[volume]
        (fun x => η x ^ 2 * differenceQuotient (hUnderlying V 1 v) k h x) ∧
      (∀ j, (hFirstDerivative z j : Space n → ℝ) =ᵐ[volume]
        (fun x => η x ^ 2 * differenceQuotient (hFirstDerivative v j) k h x +
          2 * η x * fderiv ℝ η x (coordinate n j) *
            differenceQuotient (hUnderlying V 1 v) k h x)) ∧
      (∀ᵐ x ∂volume, x ∉ tsupport η → hUnderlying ⊤ 1 z x = 0) := by
  obtain ⟨q, hq, hqd⟩ := h1Quotient W V hWV k h ha v
  obtain ⟨w, hw, hwd⟩ := h1TestProduct W (squareTest W η) q
  have hwc : P102.U4.HasCompactSupportIn (hUnderlying W 1 w.val) := by
    refine ⟨⟨tsupport η, η.hasCompactSupport⟩, η.tsupport_subset, ?_⟩
    filter_upwards [hw] with x hx hxs
    change hUnderlying W 1 w.val x = _ at hx
    change hUnderlying W 1 w.val x = 0
    rw [hx]
    change η x * η x * hUnderlying W 1 q x = 0
    rw [image_eq_zero_of_notMem_tsupport hxs]
    simp
  obtain ⟨z, hz, hzd, _⟩ := h1ZeroExtension W w.val hwc
  have hz0 : (hUnderlying ⊤ 1 z : Space n → ℝ) =ᵐ[volume]
      (fun x => η x ^ 2 * differenceQuotient (hUnderlying V 1 v) k h x) := by
    rw [hz]
    apply zeroExtension_eq_ae W _ _
    · filter_upwards [hw, hq] with x hx hxq
      change hUnderlying W 1 w.val x = _ at hx
      change hUnderlying W 1 w.val x = _
      rw [hx]
      change η x * η x * hUnderlying W 1 q x = _
      rw [hxq, pow_two]
    · intro x hxW
      rw [η.zero_on_compl hxW]
      simp
  refine ⟨z, hz0, fun j => ?_, ?_⟩
  · rw [hzd j]
    apply zeroExtension_eq_ae W _ _
    · filter_upwards [hwd j, hqd j, hq] with x hx hxd hxq
      rw [hx]
      change η x * η x * hFirstDerivative q j x +
        fderiv ℝ (squareTest W η) x (coordinate n j) * hUnderlying W 1 q x = _
      rw [squareTest_fderiv, hxd, hxq, pow_two]
    · intro x hxW
      rw [η.zero_on_compl hxW]
      simp
  · filter_upwards [hz0] with x hx hxs
    rw [hx, image_eq_zero_of_notMem_tsupport hxs]
    simp


lemma test_derivative_bound {n : ℕ} (W : Domain n) (η : Test ℝ W) :
    ∃ G : ℝ≥0, ∀ x, ‖fderiv ℝ η x‖ ≤ G := by
  obtain ⟨G, hG⟩ := η.hasCompactSupport.fderiv ℝ |>.exists_bound_of_continuous
    (η.contDiff.continuous_fderiv (by simp))
  exact ⟨⟨max G 0, le_max_right _ _⟩, fun x => (hG x).trans (le_max_left _ _)⟩

/-- Geometry and constants are chosen before the coefficients and solution. -/
lemma cutoffGeometry {n : ℕ} {U V : Domain n} (hUV : RelativelyCompactIn U V) :
    ∃ (W : Domain n) (η : Test ℝ W) (δ : ℝ) (G : ℝ≥0),
      RelativelyCompactIn W V ∧ 0 < δ ∧
      (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧ (∀ x ∈ U, η x = 1) ∧
      (∀ x, ‖fderiv ℝ η x‖ ≤ G) ∧
      (∀ (j : Fin n) (h : ℝ), |h| < δ → P201Specs.AdmissibleSegments W V j h) := by
  obtain ⟨η, W, hη, hηU, hWV, hηW⟩ := cutoff_data hUV
  let ηW : Test ℝ W := ⟨η, η.contDiff, η.hasCompactSupport, hηW⟩
  obtain ⟨G, hG⟩ := test_derivative_bound W ηW
  obtain ⟨δ, hδ, hb⟩ := compact_segment_buffer V
    ⟨closure (W : Set (Space n)), hWV.1⟩ hWV.2
  exact ⟨W, ηW, δ, G, hWV, hδ, hη, hηU, hG,
    fun j h hh x hx t ht => hb j h hh x (subset_closure hx) t ht⟩



lemma energy_absorption_abstract {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (p b r e : E) {M L G Y F theta : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hG : 0 ≤ G) (hY : 0 ≤ Y) (hF : 0 ≤ F)
    (ht : 0 < theta)
    (hell : theta * ‖p‖ ^ 2 ≤ inner ℝ b p)
    (hb : ‖b‖ ≤ M * ‖p‖) (hr : ‖r‖ ≤ L * Y) (he : ‖e‖ ≤ 2 * G * Y)
    (heq : |inner ℝ (b + r) (p + e)| ≤ F * (‖p‖ + 2 * G * Y)) :
    ‖p‖ ≤ (1 + 2 * (1 + L + 2 * M * G + 2 * L * G + 2 * G) / theta) * (Y + F) := by
  let X := ‖p‖
  let K := 1 + L + 2 * M * G + 2 * L * G + 2 * G
  have hbe : |inner ℝ b e| ≤ 2 * M * G * X * Y := by
    calc
      _ ≤ ‖b‖ * ‖e‖ := abs_real_inner_le_norm _ _
      _ ≤ (M * X) * (2 * G * Y) := mul_le_mul hb he (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hrp : |inner ℝ r p| ≤ L * Y * X := by
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hr (norm_nonneg _))
  have hre : |inner ℝ r e| ≤ 2 * L * G * Y ^ 2 := by
    calc
      _ ≤ ‖r‖ * ‖e‖ := abs_real_inner_le_norm _ _
      _ ≤ (L * Y) * (2 * G * Y) := mul_le_mul hr he (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hid : inner ℝ (b + r) (p + e) =
      inner ℝ b p + inner ℝ b e + inner ℝ r p + inner ℝ r e := by
    rw [inner_add_left, inner_add_right, inner_add_right]
    ring
  have henergy : theta * X ^ 2 ≤
      F * (X + 2 * G * Y) + 2 * M * G * X * Y + L * Y * X + 2 * L * G * Y ^ 2 := by
    have heq' := (le_abs_self (inner ℝ (b + r) (p + e))).trans heq
    have hbe' := neg_abs_le (inner ℝ b e)
    have hrp' := neg_abs_le (inner ℝ r p)
    have hre' := neg_abs_le (inner ℝ r e)
    rw [hid] at heq'
    dsimp only [X]
    dsimp only [X] at hbe hrp
    linarith
  apply quadratic_absorption (norm_nonneg _) (add_nonneg hY hF) (by positivity) ht
  have hXY : X * Y ≤ X * (Y + F) := by
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hF) (norm_nonneg _)
  have hYY : Y ^ 2 ≤ (Y + F) ^ 2 := by nlinarith
  have hFX : F * X ≤ X * (Y + F) := by nlinarith [mul_nonneg hY (norm_nonneg p)]
  have hFY : F * Y ≤ (Y + F) ^ 2 := by nlinarith [sq_nonneg F, sq_nonneg Y, mul_nonneg hF hY]
  have h1 := mul_le_mul_of_nonneg_left hXY (show 0 ≤ 2 * M * G by positivity)
  have h2 := mul_le_mul_of_nonneg_left hXY hL
  have h3 := mul_le_mul_of_nonneg_left hYY (show 0 ≤ 2 * L * G by positivity)
  have h4 := mul_le_mul_of_nonneg_left hFY (show 0 ≤ 2 * G by positivity)
  have h5 : 0 ≤ X * (Y + F) := mul_nonneg (norm_nonneg _) (add_nonneg hY hF)
  have h6 : 0 ≤ (Y + F) ^ 2 := sq_nonneg _
  have h7 := mul_nonneg (show 0 ≤ 2 * L * G + 2 * G by positivity) h5
  have h8 := mul_nonneg (show 0 ≤ 1 + L + 2 * M * G by positivity) h6
  change theta * X ^ 2 ≤ _
  change theta * X ^ 2 ≤ (1 + L + 2 * M * G + 2 * L * G + 2 * G) * X * (Y + F) +
    (1 + L + 2 * M * G + 2 * L * G + 2 * G) * (Y + F) ^ 2
  nlinarith


section L2Estimates

variable {X E F : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma l2_coercivity (p b : MeasureTheory.Lp E 2 μ) {theta : ℝ}
    (h : ∀ᵐ x ∂μ, theta * ‖p x‖ ^ 2 ≤ inner ℝ (b x) (p x)) :
    theta * ‖p‖ ^ 2 ≤ inner ℝ b p := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def, ← integral_const_mul]
  apply integral_mono_ae ((L2.integrable_inner (𝕜 := ℝ) p p).const_mul theta)
    (L2.integrable_inner (𝕜 := ℝ) b p)
  filter_upwards [h] with x hx
  simpa only [real_inner_self_eq_norm_sq] using hx

lemma toLp_norm_le (g : MeasureTheory.Lp E 2 μ) {f : X → F}
    (hf : MemLp f 2 μ) {C : ℝ}
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ C * ‖g x‖) : ‖hf.toLp f‖ ≤ C * ‖g‖ := by
  apply MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hf.coeFn_toLp, h] with x hx hb
  rw [hx]
  exact hb

lemma matrixApply_memLp (g : MeasureTheory.Lp E 2 μ) (A : X → E →L[ℝ] F)
    (hA : AEStronglyMeasurable A μ) {M : ℝ}
    (hM : ∀ᵐ x ∂μ, ‖A x‖ ≤ M) : MemLp (fun x => A x (g x)) 2 μ := by
  apply (MeasureTheory.Lp.memLp g).of_le_mul
    ((isBoundedBilinearMap_apply (𝕜 := ℝ)).continuous.comp_aestronglyMeasurable₂
      hA (MeasureTheory.Lp.memLp g).aestronglyMeasurable)
  filter_upwards [hM] with x hx
  exact (A x).le_opNorm (g x) |>.trans
    (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

lemma matrixApply_norm_le (g : MeasureTheory.Lp E 2 μ) (A : X → E →L[ℝ] F)
    (hA : AEStronglyMeasurable A μ) {M : ℝ}
    (hM : ∀ᵐ x ∂μ, ‖A x‖ ≤ M) :
    ‖(matrixApply_memLp g A hA hM).toLp (fun x => A x (g x))‖ ≤ M * ‖g‖ := by
  apply toLp_norm_le
  filter_upwards [hM] with x hx
  exact (A x).le_opNorm (g x) |>.trans
    (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

lemma l2_inner_toLp {f g : X → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, inner ℝ (f x) (g x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]

end L2Estimates



lemma fluxCoordinate_zeroExtension_ae {n : ℕ} (V : Domain n)
    (F : MeasureTheory.Lp (Space n) 2 (domainMeasure V)) (j : Fin n) :
    (P102.U4.lpZeroExtension V 2 (fluxCoordinate F j) : Space n → ℝ) =ᵐ[volume]
      (fun x => ((V : Set (Space n)).indicator (F : Space n → Space n) x) j) := by
  have hFj : (fluxCoordinate F j : Space n → ℝ) =ᵐ[domainMeasure V]
      (fun x => F x j) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) j).coeFn_compLp F
  have hFj' := (ae_restrict_iff' V.isOpen.measurableSet).mp hFj
  filter_upwards [P102.U4.lpZeroExtension_ae V 2 (fluxCoordinate F j), hFj']
    with x hx hF
  rw [hx]
  by_cases hxV : x ∈ V
  · simp only [indicator_of_mem hxV]
    exact hF hxV
  · simp only [indicator_of_notMem hxV]
    rfl

/-- The scalar coordinate identity is exactly the Euclidean vector energy
identity for the zero-extended flux. -/
theorem discrete_energy_identity_vector {n : ℕ} (hn : 1 ≤ n) (V : Domain n)
    (F : MeasureTheory.Lp (Space n) 2 (domainMeasure V)) (f : Lp ℝ V 2)
    (heq : ∀ φ : Test ℝ V,
      (∫ x in V, inner ℝ (F x) (gradient φ x)) = ∫ x in V, f x * φ x)
    (z : H ℝ (⊤ : Domain n) 1) (K : Compacts (Space n))
    (hKV : (K : Set (Space n)) ⊆ V)
    (hK : ∀ᵐ x ∂volume, x ∉ K → hUnderlying ⊤ 1 z x = 0)
    (k : Fin n) (h : ℝ) (hh : h ≠ 0)
    (ha : ∀ x ∈ K, x + h • coordinate n k ∈ V) :
    (∫ x, inner ℝ
      (h⁻¹ • (((V : Set (Space n)).indicator (F : Space n → Space n))
          (x + h • coordinate n k) -
        ((V : Set (Space n)).indicator (F : Space n → Space n)) x))
      (hGradient z x)) =
      -(∫ x in V, f x * differenceQuotient (hUnderlying ⊤ 1 z) k (-h) x) := by
  let a := h • coordinate n k
  let E (j : Fin n) := P102.U4.lpZeroExtension V 2 (fluxCoordinate F j)
  have hE (j : Fin n) : MemLp (E j : Space n → ℝ) 2 volume := by
    simpa only [E, Opens.coe_top, Measure.restrict_univ] using (Lp.memLp (E j))
  have hq (j : Fin n) : MemLp (differenceQuotient (E j) k h) 2 volume := by
    have ht := (hE j).comp_measurePreserving (measurePreserving_add_right volume a)
    convert (ht.sub (hE j)).const_smul h⁻¹ using 1 <;> rfl
  have hd (j : Fin n) : MemLp (hFirstDerivative z j : Space n → ℝ) 2 volume := by
    simpa only [domainMeasure, P201Specs.domainMeasure, Opens.coe_top,
      Measure.restrict_univ] using (Lp.memLp (hFirstDerivative z j))
  have hi (j : Fin n) : Integrable
      (fun x => differenceQuotient (E j) k h x * hFirstDerivative z j x) volume :=
    (hq j).integrable_mul (hd j)
  have hcoord (j : Fin n) := fluxCoordinate_zeroExtension_ae V F j
  have hcoordT (j : Fin n) :=
    (measurePreserving_add_right volume a).quasiMeasurePreserving.ae (hcoord j)
  have hg : (hGradient z : Space n → Space n) =ᵐ[volume]
      (fun x => WithLp.toLp 2 (fun j => hFirstDerivative z j x)) := by
    have hg0 : (hGradient z : Space n → Space n) =ᵐ[domainMeasure (⊤ : Domain n)]
        (fun x => WithLp.toLp 2 (fun j => hFirstDerivative z j x)) := MemLp.coeFn_toLp _
    simpa only [domainMeasure, P201Specs.domainMeasure, Opens.coe_top,
      Measure.restrict_univ] using hg0
  have he : (fun x => inner ℝ
      (h⁻¹ • (((V : Set (Space n)).indicator (F : Space n → Space n)) (x + a) -
        ((V : Set (Space n)).indicator (F : Space n → Space n)) x))
      (hGradient z x)) =ᵐ[volume]
        (fun x => ∑ j : Fin n,
          differenceQuotient (E j) k h x * hFirstDerivative z j x) := by
    filter_upwards [hg, ae_all_iff.mpr hcoord, ae_all_iff.mpr hcoordT]
      with x hx hxF hxFT
    rw [hx]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_comm]
    congr 1
    change h⁻¹ * ((((V : Set (Space n)).indicator (F : Space n → Space n)) (x+a)) j -
        (((V : Set (Space n)).indicator (F : Space n → Space n)) x) j) =
      h⁻¹ * (E j (x+a) - E j x)
    rw [← hxF j, ← hxFT j]
  calc
    _ = ∫ x, ∑ j : Fin n,
        differenceQuotient (E j) k h x * hFirstDerivative z j x := integral_congr_ae he
    _ = ∑ j : Fin n, ∫ x,
        differenceQuotient (E j) k h x * hFirstDerivative z j x :=
      integral_finsetSum _ (fun j _ => hi j)
    _ = _ := discrete_energy_identity hn V F f heq z K hKV hK k h hh ha




/-- Pointwise weighted flux algebra. No regularity or nonzero-step hypothesis
is needed for this identity. -/
lemma weighted_flux_pairing {n : ℕ}
    (A A' : Space n →L[ℝ] Space n) (g g' ξ : Space n) (η q h : ℝ) :
    inner ℝ (h⁻¹ • (A' g' - A g))
        (η ^ 2 • (h⁻¹ • (g' - g)) + (2 * η * q) • ξ) =
      inner ℝ
        (A' (η • (h⁻¹ • (g' - g))) + η • ((h⁻¹ • (A' - A)) g))
        (η • (h⁻¹ • (g' - g)) + (2 * q) • ξ) := by
  have hf : h⁻¹ • (A' g' - A g) =
      A' (h⁻¹ • (g' - g)) + (h⁻¹ • (A' - A)) g := by
    simp only [map_smul, map_sub, smul_apply, sub_apply, smul_sub]
    abel
  rw [hf]
  simp only [map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, conj_trivial]
  ring

/-- The coordinate formula from localizedQuotient gives the vector product
formula globally, since every term is weighted by the compact cutoff. -/
lemma hGradient_localizedQuotient_ae {n : ℕ} (W V : Domain n) (hWV : W ≤ V)
    (η : Test ℝ W) (v : H ℝ V 1) (z : H ℝ (⊤ : Domain n) 1)
    (k : Fin n) (h : ℝ)
    (ha : ∀ x ∈ W, x + h • coordinate n k ∈ V)
    (hzd : ∀ j, (hFirstDerivative z j : Space n → ℝ) =ᵐ[volume]
      (fun x => η x ^ 2 * differenceQuotient (hFirstDerivative v j) k h x +
        2 * η x * fderiv ℝ η x (coordinate n j) *
          differenceQuotient (hUnderlying V 1 v) k h x)) :
    (hGradient z : Space n → Space n) =ᵐ[volume]
      (fun x => η x ^ 2 • (h⁻¹ • (hGradient v (x + h • coordinate n k) - hGradient v x)) +
        (2 * η x * differenceQuotient (hUnderlying V 1 v) k h x) • gradient η x) := by
  have hg := hGradient_product_ae z η
    (differenceQuotient (hUnderlying V 1 v) k h)
    (fun j => differenceQuotient (hFirstDerivative v j) k h) hzd
  have hq := (ae_restrict_iff' W.isOpen.measurableSet).mp
    (hGradient_quotient_ae W V hWV v k h ha)
  filter_upwards [hg, hq] with x hx hqx
  rw [hx]
  by_cases hxW : x ∈ W
  · rw [hqx hxW]
  · rw [η.zero_on_compl hxW]
    simp

/-- The zero-extended flux paired with the compact H¹ gradient is exactly the
weighted energy integral on W. This uses the original coefficient flux only on
V and admissibility of the translated points of W. -/
lemma weighted_flux_integral {n : ℕ} (W V : Domain n) (hWV : W ≤ V)
    (η : Test ℝ W) (A : Space n → Space n →L[ℝ] Space n)
    (g F : MeasureTheory.Lp (Space n) 2 (domainMeasure V))
    (hF : (F : Space n → Space n) =ᵐ[domainMeasure V] (fun x => A x (g x)))
    (z : H ℝ (⊤ : Domain n) 1) (q : Space n → ℝ) (k : Fin n) (h : ℝ)
    (ha : ∀ x ∈ W, x + h • coordinate n k ∈ V)
    (hgz : (hGradient z : Space n → Space n) =ᵐ[volume]
      (fun x => η x ^ 2 • (h⁻¹ • (g (x + h • coordinate n k) - g x)) +
        (2 * η x * q x) • gradient η x)) :
    (∫ x, inner ℝ
      (h⁻¹ • (((V : Set (Space n)).indicator (F : Space n → Space n))
          (x + h • coordinate n k) -
        ((V : Set (Space n)).indicator (F : Space n → Space n)) x)) (hGradient z x)) =
      ∫ x in W, inner ℝ
        (A (x + h • coordinate n k) (η x • (h⁻¹ • (g (x + h • coordinate n k) - g x))) +
          η x • ((h⁻¹ • (A (x + h • coordinate n k) - A x)) (g x)))
        (η x • (h⁻¹ • (g (x + h • coordinate n k) - g x)) +
          (2 * q x) • gradient η x) := by
  let a := h • coordinate n k
  have hI : ((V : Set (Space n)).indicator (F : Space n → Space n))
      =ᵐ[domainMeasure V] (fun x => A x (g x)) := by
    filter_upwards [hF, ae_restrict_mem V.isOpen.measurableSet] with x hx hxV
    rw [indicator_of_mem hxV]
    exact hx
  have hI0 := (ae_restrict_iff' W.isOpen.measurableSet).mp
    (ae_restrict_of_ae_restrict_of_subset hWV hI)
  have hIt := (ae_restrict_iff' W.isOpen.measurableSet).mp
    (ae_eq_translate_local hI a (by
      rintro _ ⟨x, hx, rfl⟩
      exact ha x hx))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · apply integral_congr_ae
    filter_upwards [hgz, hI0, hIt] with x hx h0 ht
    rw [hx]
    by_cases hxW : x ∈ W
    · rw [h0 hxW, ht hxW]
      exact weighted_flux_pairing (A x) (A (x+a)) (g x) (g (x+a))
        (gradient η x) (η x) (q x) h
    · rw [η.zero_on_compl hxW]
      simp
  · intro x hxW
    rw [η.zero_on_compl hxW]
    simp




lemma wholeSpace_integrable_of_zero_off {n : ℕ} (W : Domain n)
    [IsFiniteMeasure (domainMeasure W)] (g : Lp ℝ (⊤ : Domain n) 2)
    (hz : ∀ᵐ x ∂volume, x ∉ W → g x = 0) :
    Integrable (g : Space n → ℝ) volume := by
  have hgp : MemLp (g : Space n → ℝ) 2 volume := by
    simpa only [domainMeasure, P201Specs.domainMeasure, Opens.coe_top,
      Measure.restrict_univ] using Lp.memLp g
  have hi : Integrable (g : Space n → ℝ) (domainMeasure W) :=
    (hgp.mono_measure (Measure.restrict_le_self)).integrable (by norm_num)
  apply ((integrable_indicator_iff W.isOpen.measurableSet).mpr hi).congr
  filter_upwards [hz] with x hx
  by_cases hxW : x ∈ W
  · exact indicator_of_mem hxW _
  · rw [indicator_of_notMem hxW, hx hxW]

lemma fluxCoordinate_norm_le {n : ℕ} {W : Domain n}
    (r : MeasureTheory.Lp (Space n) 2 (domainMeasure W)) (j : Fin n) :
    ‖fluxCoordinate r j‖ ≤ ‖r‖ := by
  apply MeasureTheory.Lp.norm_le_norm_of_ae_le
  filter_upwards [(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) j).coeFn_compLp r]
    with x hx
  rw [show fluxCoordinate r j x = r x j from hx]
  exact PiLp.norm_apply_le _ _

/-- A localized coordinate derivative is bounded by the full vector L² norm.
Only the actual almost-everywhere product formula and compact localization enter. -/
lemma localized_derivative_norm_le {n : ℕ} (W : Domain n)
    (z : H ℝ (⊤ : Domain n) 1)
    (r : MeasureTheory.Lp (Space n) 2 (domainMeasure W)) (η : Space n → ℝ)
    (j : Fin n) (hη : ∀ x, |η x| ≤ 1)
    (hd : (hFirstDerivative z j : Space n → ℝ) =ᵐ[domainMeasure W]
      (fun x => η x * r x j))
    (hz : ∀ᵐ x ∂volume, x ∉ W → hFirstDerivative z j x = 0) :
    ‖hFirstDerivative z j‖ ≤ ‖r‖ := by
  have hd' := (ae_restrict_iff' W.isOpen.measurableSet).mp hd
  have hc : (fluxCoordinate r j : Space n → ℝ) =ᵐ[domainMeasure W]
      (fun x => r x j) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) j).coeFn_compLp r
  have hc' := (ae_restrict_iff' W.isOpen.measurableSet).mp hc
  have hraw : ∀ᵐ x ∂volume, ‖hFirstDerivative z j x‖ ≤
      ‖P102.U4.lpZeroExtension W 2 (fluxCoordinate r j) x‖ := by
    filter_upwards [hd', hz, hc', P102.U4.lpZeroExtension_ae W 2 (fluxCoordinate r j)]
      with x hdx hzx hcx hext
    rw [hext]
    by_cases hxW : x ∈ W
    · rw [indicator_of_mem hxW, hdx hxW, hcx hxW, norm_mul, Real.norm_eq_abs (η x)]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hη x) (norm_nonneg (r x j))
    · rw [indicator_of_notMem hxW, hzx hxW]
  calc
    _ ≤ ‖P102.U4.lpZeroExtension W 2 (fluxCoordinate r j)‖ := by
      apply MeasureTheory.Lp.norm_le_norm_of_ae_le
      simpa only [domainMeasure, P201Specs.domainMeasure, Opens.coe_top,
        Measure.restrict_univ] using hraw
    _ = ‖fluxCoordinate r j‖ := P102.U4.lpZeroExtension_norm W 2 _
    _ ≤ ‖r‖ := fluxCoordinate_norm_le r j

/-- The L² forcing is paired only with a quotient of the localized H¹ test. -/
lemma localized_source_bound {n : ℕ} (W V : Domain n)
    [IsFiniteMeasure (domainMeasure W)] (z : H ℝ (⊤ : Domain n) 1)
    (p e : MeasureTheory.Lp (Space n) 2 (domainMeasure W)) (η : Space n → ℝ)
    (hη : ∀ x, |η x| ≤ 1)
    (hg : (hGradient z : Space n → Space n) =ᵐ[domainMeasure W]
      (fun x => η x • (p + e) x))
    (k : Fin n) (h : ℝ) (hh : h ≠ 0)
    (hz : ∀ᵐ x ∂volume, x ∉ W → hFirstDerivative z k x = 0)
    (f : Lp ℝ V 2) :
    |∫ x in V, f x * differenceQuotient (hUnderlying ⊤ 1 z) k h x| ≤
      ‖f‖ * (‖p‖ + ‖e‖) := by
  have hg0 := hGradient_ae z
  simp only [domainMeasure, P201Specs.domainMeasure, Opens.coe_top,
    Measure.restrict_univ] at hg0
  have hd : (hFirstDerivative z k : Space n → ℝ) =ᵐ[domainMeasure W]
      (fun x => η x * (p + e) x k) := by
    filter_upwards [ae_restrict_of_ae hg0, hg] with x hx hy
    exact congrArg (fun ξ : Space n => ξ k) (hx.symm.trans hy)
  have hn := localized_derivative_norm_le W z (p + e) η k hη hd hz
  exact (wholeSpace_source_pairing_bound V z k h hh
    (wholeSpace_integrable_of_zero_off W (hFirstDerivative z k) hz) f).trans
    (mul_le_mul_of_nonneg_left (hn.trans (norm_add_le p e)) (norm_nonneg f))



section EnergyFields

variable {X E F : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma scalarMultiply_memLp (g : MeasureTheory.Lp E 2 μ) (a : X → ℝ)
    (ha : AEStronglyMeasurable a μ) {C : ℝ} (hC : ∀ᵐ x ∂μ, |a x| ≤ C) :
    MemLp (fun x => a x • g x) 2 μ := by
  apply (MeasureTheory.Lp.memLp g).of_le_mul
    (ha.smul (MeasureTheory.Lp.memLp g).aestronglyMeasurable)
  filter_upwards [hC] with x hx
  change ‖a x • g x‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

lemma scalarMultiply_norm_le (g : MeasureTheory.Lp E 2 μ) (a : X → ℝ)
    (ha : AEStronglyMeasurable a μ) {C : ℝ} (hC : ∀ᵐ x ∂μ, |a x| ≤ C) :
    ‖(scalarMultiply_memLp g a ha hC).toLp (fun x => a x • g x)‖ ≤ C * ‖g‖ := by
  apply toLp_norm_le
  filter_upwards [hC] with x hx
  change ‖a x • g x‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

lemma boundedVectorMultiply_memLp (g : MeasureTheory.Lp ℝ 2 μ) (a : X → E)
    (ha : AEStronglyMeasurable a μ) {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) :
    MemLp (fun x => g x • a x) 2 μ := by
  apply (MeasureTheory.Lp.memLp g).of_le_mul
    ((MeasureTheory.Lp.memLp g).aestronglyMeasurable.smul ha)
  filter_upwards [hC] with x hx
  change ‖g x • a x‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left hx (abs_nonneg _)).trans_eq (mul_comm _ _)

lemma boundedVectorMultiply_norm_le (g : MeasureTheory.Lp ℝ 2 μ) (a : X → E)
    (ha : AEStronglyMeasurable a μ) {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) :
    ‖(boundedVectorMultiply_memLp g a ha hC).toLp (fun x => g x • a x)‖ ≤ C * ‖g‖ := by
  apply toLp_norm_le
  filter_upwards [hC] with x hx
  change ‖g x • a x‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left hx (abs_nonneg _)).trans_eq (mul_comm _ _)


lemma construct_energy_fields {X E : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g dq : MeasureTheory.Lp E 2 μ) (q : MeasureTheory.Lp ℝ 2 μ)
    (a : X → ℝ) (geta : X → E) (B D : X → E →L[ℝ] E)
    (ha : AEStronglyMeasurable a μ) (hgeta : AEStronglyMeasurable geta μ)
    (hB : AEStronglyMeasurable B μ) (hD : AEStronglyMeasurable D μ)
    {M L G Y theta : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hG : 0 ≤ G)
    (ha1 : ∀ᵐ x ∂μ, |a x| ≤ 1) (hgetaG : ∀ᵐ x ∂μ, ‖geta x‖ ≤ G)
    (hBM : ∀ᵐ x ∂μ, ‖B x‖ ≤ M) (hDL : ∀ᵐ x ∂μ, ‖D x‖ ≤ L)
    (hell : ∀ᵐ x ∂μ, ∀ ξ : E, theta * ‖ξ‖ ^ 2 ≤ inner ℝ (B x ξ) ξ)
    (hgY : ‖g‖ ≤ Y) (hqY : ‖q‖ ≤ Y) :
    ∃ p b r e : MeasureTheory.Lp E 2 μ,
      ((p : X → E) =ᵐ[μ] fun x => a x • dq x) ∧
      ((b : X → E) =ᵐ[μ] fun x => B x (p x)) ∧
      ((r : X → E) =ᵐ[μ] fun x => a x • D x (g x)) ∧
      ((e : X → E) =ᵐ[μ] fun x => (2 * q x) • geta x) ∧
      theta * ‖p‖ ^ 2 ≤ inner ℝ b p ∧
      ‖b‖ ≤ M * ‖p‖ ∧ ‖r‖ ≤ L * Y ∧ ‖e‖ ≤ 2 * G * Y := by
  let hp := scalarMultiply_memLp dq a ha ha1
  let p : MeasureTheory.Lp E 2 μ := hp.toLp _
  let hb := matrixApply_memLp p B hB hBM
  let b : MeasureTheory.Lp E 2 μ := hb.toLp _
  let hr0 := matrixApply_memLp g D hD hDL
  let r0 : MeasureTheory.Lp E 2 μ := hr0.toLp _
  let hr := scalarMultiply_memLp r0 a ha ha1
  let r : MeasureTheory.Lp E 2 μ := hr.toLp _
  have h2geta : AEStronglyMeasurable (fun x => (2 : ℝ) • geta x) μ := hgeta.const_smul 2
  have h2getaG : ∀ᵐ x ∂μ, ‖(2 : ℝ) • geta x‖ ≤ 2 * G := by
    filter_upwards [hgetaG] with x hx
    simpa only [norm_smul, Real.norm_ofNat] using mul_le_mul_of_nonneg_left hx (by norm_num : (0 : ℝ) ≤ 2)
  let he := boundedVectorMultiply_memLp q (fun x => (2 : ℝ) • geta x) h2geta h2getaG
  let e : MeasureTheory.Lp E 2 μ := he.toLp _
  have hpa : (p : X → E) =ᵐ[μ] fun x => a x • dq x := hp.coeFn_toLp
  have hba : (b : X → E) =ᵐ[μ] fun x => B x (p x) := hb.coeFn_toLp
  have hra : (r : X → E) =ᵐ[μ] fun x => a x • D x (g x) := by
    filter_upwards [hr.coeFn_toLp, hr0.coeFn_toLp] with x hx hy
    rw [hx, hy]
  have hea : (e : X → E) =ᵐ[μ] fun x => (2 * q x) • geta x := by
    filter_upwards [he.coeFn_toLp] with x hx
    rw [hx, smul_smul, mul_comm]
  refine ⟨p, b, r, e, hpa, hba, hra, hea, ?_, ?_, ?_, ?_⟩
  · apply l2_coercivity
    filter_upwards [hba, hell] with x hx hxell
    rw [hx]
    exact hxell (p x)
  · exact matrixApply_norm_le p B hB hBM
  · calc
      ‖r‖ ≤ 1 * ‖r0‖ := scalarMultiply_norm_le r0 a ha ha1
      _ ≤ L * Y := by
        rw [one_mul]
        exact (matrixApply_norm_le g D hD hDL).trans
          (mul_le_mul_of_nonneg_left hgY hL)
  · calc
      ‖e‖ ≤ (2 * G) * ‖q‖ := boundedVectorMultiply_norm_le q _ h2geta h2getaG
      _ ≤ 2 * G * Y := mul_le_mul_of_nonneg_left hqY (by positivity)

end EnergyFields



lemma firstDerivative_norm_le {n : ℕ} (V : Domain n) (v : H ℝ V 1) (k : Fin n) :
    ‖hFirstDerivative v k‖ ≤ ‖v‖ := by
  change ‖v.val ⟨{k}, by simp⟩‖ ≤ ‖v.val‖
  exact PiLp.norm_apply_le _ _

lemma local_quotient_bound {n : ℕ} (hn : 1 ≤ n) (Ω V W : Domain n)
    (hWV : RelativelyCompactIn W V) (hVΩ : RelativelyCompactIn V Ω)
    (v : H ℝ V 1) (k : Fin n) (h : ℝ) (hh : h ≠ 0)
    (hs : P201Specs.AdmissibleSegments W V k h) :
    MemLp (differenceQuotient (hUnderlying V 1 v) k h) 2 (domainMeasure W) ∧
    eLpNorm (differenceQuotient (hUnderlying V 1 v) k h) 2 (domainMeasure W) ≤ ‖v‖₊ := by
  obtain ⟨hm, hb⟩ := differenceQuotientEstimate hn Ω V W k h 2 (by norm_num)
    hh hWV hVΩ hs ((hToW ℝ V 1) v)
  refine ⟨hm, hb.trans ?_⟩
  change eLpNorm (hFirstDerivative v k) 2 (domainMeasure V) ≤ _
  rw [← Lp.enorm_def, enorm_eq_nnnorm]
  exact_mod_cast firstDerivative_norm_le V v k

lemma gradient_test_bound {n : ℕ} (V : Domain n) (η : Test ℝ V) :
    ∃ G : ℝ≥0, ∀ x, ‖gradient η x‖ ≤ G := by
  have hc : Continuous (gradient η) := by
    change Continuous (fun x => WithLp.toLp 2 (fun j : Fin n =>
      fderiv ℝ η x (coordinate n j)))
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro j
    exact (η.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  have hs : Function.support (gradient η) ⊆ tsupport η := by
    intro x hx
    by_contra hn
    apply hx
    change WithLp.toLp 2 (fun j : Fin n => fderiv ℝ η x (coordinate n j)) = 0
    rw [fderiv_of_notMem_tsupport ℝ hn]
    rfl
  have hcompact : HasCompactSupport (gradient η) :=
    η.hasCompactSupport.of_isClosed_subset isClosed_closure
      (closure_minimal hs isClosed_closure)
  obtain ⟨G, hG⟩ := hcompact.exists_bound_of_continuous hc
  exact ⟨⟨max G 0, le_max_right _ _⟩, fun x => (hG x).trans (le_max_left _ _)⟩


lemma local_quotient_toLp_bound {n : ℕ} (hn : 1 ≤ n) (Ω V W : Domain n)
    (hWV : RelativelyCompactIn W V) (hVΩ : RelativelyCompactIn V Ω)
    (v : H ℝ V 1) (k : Fin n) (h : ℝ) (hh : h ≠ 0)
    (hs : P201Specs.AdmissibleSegments W V k h) :
    ∃ q : Lp ℝ W 2,
      (q : Space n → ℝ) =ᵐ[domainMeasure W]
        differenceQuotient (hUnderlying V 1 v) k h ∧ ‖q‖ ≤ ‖v‖ := by
  obtain ⟨hm, hb⟩ := local_quotient_bound hn Ω V W hWV hVΩ v k h hh hs
  refine ⟨hm.toLp _, hm.coeFn_toLp, ?_⟩
  rw [Lp.norm_toLp]
  exact_mod_cast ENNReal.toReal_mono ENNReal.coe_ne_top hb

lemma cutoff_error_class {n : ℕ} (W : Domain n) (η : Test ℝ W)
    (G : ℝ≥0) (hG : ∀ x, ‖gradient η x‖ ≤ G) (q : Lp ℝ W 2) :
    ∃ e : MeasureTheory.Lp (Space n) 2 (domainMeasure W),
      (e : Space n → Space n) =ᵐ[domainMeasure W]
        (fun x => (2 * q x) • gradient η x) ∧ ‖e‖ ≤ 2 * G * ‖q‖ := by
  have hc : Continuous (gradient η) := by
    change Continuous (fun x => WithLp.toLp 2 (fun j : Fin n =>
      fderiv ℝ η x (coordinate n j)))
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro j
    exact (η.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  have hmeas : AEStronglyMeasurable (fun x => (2 * q x) • gradient η x)
      (domainMeasure W) :=
    ((Lp.memLp q).aestronglyMeasurable.const_mul 2).smul hc.aestronglyMeasurable
  have hb : ∀ x, ‖(2 * q x) • gradient η x‖ ≤ (2 * G : ℝ) * ‖q x‖ := by
    intro x
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
    calc
      2 * |q x| * ‖gradient η x‖ ≤ 2 * |q x| * G :=
        mul_le_mul_of_nonneg_left (hG x) (by positivity)
      _ = (2 * G : ℝ) * ‖q x‖ := by rw [Real.norm_eq_abs]; ring
  have hm : MemLp (fun x => (2 * q x) • gradient η x) 2 (domainMeasure W) :=
    (Lp.memLp q).of_le_mul hmeas (Filter.Eventually.of_forall hb)
  refine ⟨hm.toLp _, hm.coeFn_toLp, ?_⟩
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hm.coeFn_toLp] with x hx
  rw [hx]
  exact hb x

lemma local_quotient_error_bound {n : ℕ} (hn : 1 ≤ n) (Ω V W : Domain n)
    (hWV : RelativelyCompactIn W V) (hVΩ : RelativelyCompactIn V Ω)
    (v : H ℝ V 1) (k : Fin n) (h : ℝ) (hh : h ≠ 0)
    (hs : P201Specs.AdmissibleSegments W V k h)
    (η : Test ℝ W) (G : ℝ≥0) (hG : ∀ x, ‖gradient η x‖ ≤ G) :
    ∃ e : MeasureTheory.Lp (Space n) 2 (domainMeasure W),
      (e : Space n → Space n) =ᵐ[domainMeasure W]
        (fun x => (2 * differenceQuotient (hUnderlying V 1 v) k h x) • gradient η x) ∧
      ‖e‖ ≤ 2 * G * ‖v‖ := by
  obtain ⟨q, hq, hqn⟩ := local_quotient_toLp_bound hn Ω V W hWV hVΩ v k h hh hs
  obtain ⟨e, he, hen⟩ := cutoff_error_class W η G hG q
  refine ⟨e, ?_, hen.trans (mul_le_mul_of_nonneg_left hqn (by positivity))⟩
  filter_upwards [he, hq] with x hx hxq
  rw [hx, hxq]



lemma translated_coefficient_data {n : ℕ} (W V : Domain n) (hWV : W ≤ V)
    (A : Space n → Space n →L[ℝ] Space n) (M L : ℝ≥0) (theta : ℝ)
    (hA : CoefficientBounds V A M L theta)
    (k : Fin n) (h : ℝ) (hh : h ≠ 0)
    (ha : ∀ x ∈ W, x + h • coordinate n k ∈ V) :
    AEStronglyMeasurable (fun x => A (x + h • coordinate n k)) (domainMeasure W) ∧
    AEStronglyMeasurable (fun x => h⁻¹ • (A (x + h • coordinate n k) - A x))
      (domainMeasure W) ∧
    (∀ᵐ x ∂domainMeasure W, ‖A (x + h • coordinate n k)‖ ≤ M) ∧
    (∀ᵐ x ∂domainMeasure W, ‖h⁻¹ • (A (x + h • coordinate n k) - A x)‖ ≤ L) ∧
    (∀ᵐ x ∂domainMeasure W, ∀ ξ : Space n,
      theta * ‖ξ‖ ^ 2 ≤ inner ℝ (A (x + h • coordinate n k) ξ) ξ) := by
  have hcA : ContinuousOn A (V : Set (Space n)) := hA.2.1.continuousOn
  have hcB : ContinuousOn (fun x => A (x + h • coordinate n k))
      (W : Set (Space n)) :=
    hcA.comp (continuous_id.add continuous_const).continuousOn ha
  have hcD : ContinuousOn (fun x => h⁻¹ • (A (x + h • coordinate n k) - A x))
      (W : Set (Space n)) :=
    (hcB.sub (hcA.mono hWV)).const_smul h⁻¹
  refine ⟨hcB.aestronglyMeasurable W.isOpen.measurableSet,
    hcD.aestronglyMeasurable W.isOpen.measurableSet, ?_, ?_, ?_⟩
  · filter_upwards [ae_restrict_mem W.isOpen.measurableSet] with x hx
    exact hA.1 _ (ha x hx)
  · filter_upwards [ae_restrict_mem W.isOpen.measurableSet] with x hx
    exact coefficient_difference_le hA.2.1 k hh (hWV hx) (ha x hx)
  · filter_upwards [ae_restrict_mem W.isOpen.measurableSet] with x hx
    exact hA.2.2 _ (ha x hx)



/-- The original weak equation produces the weighted discrete energy identity
for the actual compactly supported H¹ test η²D_hv. No derivative of f is used. -/
theorem localized_energy_identity {n : ℕ} (hn : 1 ≤ n)
    (W V : Domain n) (hWV : W ≤ V) (η : Test ℝ W)
    (A : Space n → Space n →L[ℝ] Space n) (v : H ℝ V 1) (f : Lp ℝ V 2)
    (hA : ContinuousOn A V) {M : ℝ} (hM : ∀ x ∈ V, ‖A x‖ ≤ M)
    (heq : WeakEquation V A v f)
    (z : H ℝ (⊤ : Domain n) 1) (k : Fin n) (h : ℝ) (hh : h ≠ 0)
    (ha : ∀ x ∈ W, x + h • coordinate n k ∈ V)
    (hzd : ∀ j, (hFirstDerivative z j : Space n → ℝ) =ᵐ[volume]
      (fun x => η x ^ 2 * differenceQuotient (hFirstDerivative v j) k h x +
        2 * η x * fderiv ℝ η x (coordinate n j) *
          differenceQuotient (hUnderlying V 1 v) k h x))
    (hK : ∀ᵐ x ∂volume, x ∉ tsupport η → hUnderlying ⊤ 1 z x = 0) :
    (∫ x in W, inner ℝ
      (A (x + h • coordinate n k)
          (η x • (h⁻¹ • (hGradient v (x + h • coordinate n k) - hGradient v x))) +
        η x • ((h⁻¹ • (A (x + h • coordinate n k) - A x)) (hGradient v x)))
      (η x • (h⁻¹ • (hGradient v (x + h • coordinate n k) - hGradient v x)) +
        (2 * differenceQuotient (hUnderlying V 1 v) k h x) • gradient η x)) =
      -(∫ x in V, f x * differenceQuotient (hUnderlying ⊤ 1 z) k (-h) x) := by
  let hm := flux_memLp V A (hGradient v) hA hM
  let F : MeasureTheory.Lp (Space n) 2 (domainMeasure V) := hm.toLp _
  have hF : (F : Space n → Space n) =ᵐ[domainMeasure V]
      (fun x => A x (hGradient v x)) := hm.coeFn_toLp
  have htest : ∀ φ : Test ℝ V,
      (∫ x in V, inner ℝ (F x) (gradient φ x)) = ∫ x in V, f x * φ x := by
    intro φ
    calc
      _ = ∫ x in V, inner ℝ (A x (hGradient v x)) (gradient φ x) := by
        apply integral_congr_ae
        filter_upwards [hF] with x hx
        rw [hx]
      _ = _ := heq φ
  have hgz := hGradient_localizedQuotient_ae W V hWV η v z k h ha hzd
  have hweighted := weighted_flux_integral W V hWV η A (hGradient v) F hF z
    (differenceQuotient (hUnderlying V 1 v) k h) k h ha hgz
  let K : Compacts (Space n) := ⟨tsupport η, η.hasCompactSupport⟩
  have hKV : (K : Set (Space n)) ⊆ V := η.tsupport_subset.trans hWV
  have hstep : ∀ x ∈ K, x + h • coordinate n k ∈ V :=
    fun x hx => ha x (η.tsupport_subset hx)
  exact hweighted.symm.trans
    (discrete_energy_identity_vector hn V F f htest z K hKV hK k h hh hstep)


lemma energy_fields_of_quotient {n : ℕ} (W V : Domain n) (hWV : W ≤ V)
    (A : Space n → Space n →L[ℝ] Space n) (M L : ℝ≥0) (theta : ℝ)
    (hA : CoefficientBounds V A M L theta)
    (v : H ℝ V 1) (k : Fin n) (h : ℝ) (hh : h ≠ 0)
    (ha : ∀ x ∈ W, x + h • coordinate n k ∈ V)
    (qH : H ℝ W 1)
    (hq : (hUnderlying W 1 qH : Space n → ℝ) =ᵐ[domainMeasure W]
      differenceQuotient (hUnderlying V 1 v) k h)
    (hqd : ∀ j, (hFirstDerivative qH j : Space n → ℝ) =ᵐ[domainMeasure W]
      differenceQuotient (hFirstDerivative v j) k h)
    (hqn : ‖hUnderlying W 1 qH‖ ≤ ‖v‖)
    (η : Test ℝ W) (hη : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (G : ℝ≥0) (hG : ∀ x, ‖gradient η x‖ ≤ G) :
    ∃ p b r e : MeasureTheory.Lp (Space n) 2 (domainMeasure W),
      ((p : Space n → Space n) =ᵐ[domainMeasure W] fun x =>
        η x • (h⁻¹ • (hGradient v (x + h • coordinate n k) - hGradient v x))) ∧
      ((b : Space n → Space n) =ᵐ[domainMeasure W] fun x =>
        A (x + h • coordinate n k) (p x)) ∧
      ((r : Space n → Space n) =ᵐ[domainMeasure W] fun x =>
        η x • (h⁻¹ • (A (x + h • coordinate n k) - A x)) (hGradient v x)) ∧
      ((e : Space n → Space n) =ᵐ[domainMeasure W] fun x =>
        (2 * differenceQuotient (hUnderlying V 1 v) k h x) • gradient η x) ∧
      theta * ‖p‖ ^ 2 ≤ inner ℝ b p ∧
      ‖b‖ ≤ M * ‖p‖ ∧ ‖r‖ ≤ L * ‖v‖ ∧ ‖e‖ ≤ 2 * G * ‖v‖ := by
  let hg := (MeasureTheory.Lp.memLp (hGradient v)).mono_measure
    (Measure.restrict_mono hWV le_rfl)
  let g : MeasureTheory.Lp (Space n) 2 (domainMeasure W) := hg.toLp _
  have hga : (g : Space n → Space n) =ᵐ[domainMeasure W] hGradient v := hg.coeFn_toLp
  have hgn : ‖g‖ ≤ ‖v‖ := by
    calc
      ‖g‖ = (eLpNorm (hGradient v) 2 (domainMeasure W)).toReal := Lp.norm_toLp _ _
      _ ≤ ‖hGradient v‖ := by
        rw [Lp.norm_def]
        exact ENNReal.toReal_mono (MeasureTheory.Lp.memLp (hGradient v)).eLpNorm_ne_top
          (eLpNorm_mono_measure _ (Measure.restrict_mono hWV le_rfl))
      _ ≤ ‖v‖ := hGradient_norm_le v
  have hηa : AEStronglyMeasurable η (domainMeasure W) := η.contDiff.continuous.aestronglyMeasurable
  have hη1 : ∀ᵐ x ∂domainMeasure W, |η x| ≤ 1 :=
    Filter.Eventually.of_forall fun x => by rw [abs_of_nonneg (hη x).1]; exact (hη x).2
  have hcgeta : Continuous (gradient η) := by
    change Continuous (fun x => WithLp.toLp 2 (fun j : Fin n => fderiv ℝ η x (coordinate n j)))
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro j
    exact (η.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨hB, hD, hBM, hDL, hell⟩ := translated_coefficient_data W V hWV A M L theta hA k h hh ha
  obtain ⟨p, b, r, e, hp, hb, hr, he, hel, hbn, hrn, hen⟩ :=
    construct_energy_fields g (hGradient qH) (hUnderlying W 1 qH)
      η (gradient η) (fun x => A (x + h • coordinate n k))
      (fun x => h⁻¹ • (A (x + h • coordinate n k) - A x)) hηa hcgeta.aestronglyMeasurable
      hB hD M.coe_nonneg L.coe_nonneg G.coe_nonneg hη1
      (Filter.Eventually.of_forall hG) hBM hDL hell hgn hqn
  have hdq : (hGradient qH : Space n → Space n) =ᵐ[domainMeasure W]
      fun x => h⁻¹ • (hGradient v (x + h • coordinate n k) - hGradient v x) := by
    have hto : (hGradient qH : Space n → Space n) =ᵐ[domainMeasure W]
        fun x => WithLp.toLp 2 (fun j => differenceQuotient (hFirstDerivative v j) k h x) := by
      filter_upwards [hGradient_ae qH, ae_all_iff.mpr hqd] with x hx hdx
      rw [hx]
      apply PiLp.ext
      intro j
      exact hdx j
    exact hto.trans (hGradient_quotient_ae W V hWV v k h ha).symm
  refine ⟨p, b, r, e, ?_, hb, ?_, ?_, hel, hbn, hrn, hen⟩
  · filter_upwards [hp, hdq] with x hx hy
    rw [hx, hy]
  · filter_upwards [hr, hga] with x hx hy
    rw [hx, hy]
  · filter_upwards [he, hq] with x hx hy
    rw [hx, hy]

lemma cutoffEnergyGeometry {n : ℕ} {U V : Domain n} (hUV : RelativelyCompactIn U V) :
    ∃ (W : Domain n) (η : Test ℝ W) (δ : ℝ) (G : ℝ≥0),
      RelativelyCompactIn W V ∧ 0 < δ ∧
      (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧ (∀ x ∈ U, η x = 1) ∧ U ≤ W ∧
      (∀ x, ‖gradient η x‖ ≤ G) ∧
      (∀ (j : Fin n) (h : ℝ), |h| < δ → P201Specs.AdmissibleSegments W V j h) := by
  obtain ⟨W, η, δ, _, hWV, hδ, hη, hηU, _, hb⟩ := cutoffGeometry hUV
  obtain ⟨G, hG⟩ := gradient_test_bound W η
  have hUW : U ≤ W := by
    intro x hx
    apply η.tsupport_subset
    apply subset_tsupport
    change η x ≠ 0
    rw [hηU x hx]
    exact one_ne_zero
  exact ⟨W, η, δ, G, hWV, hδ, hη, hηU, hUW, hG, hb⟩

lemma scalar_quotient_of_weighted_gradient {n : ℕ} {U W V : Domain n}
    (hUW : U ≤ W) (hWV : W ≤ V) (η : Test ℝ W)
    (hηU : ∀ x ∈ U, η x = 1) (v : H ℝ V 1) (k : Fin n) (h : ℝ)
    (ha : ∀ x ∈ W, x + h • coordinate n k ∈ V)
    (p : MeasureTheory.Lp (Space n) 2 (domainMeasure W))
    (hp : (p : Space n → Space n) =ᵐ[domainMeasure W]
      (fun x => η x • (h⁻¹ • (hGradient v (x + h • coordinate n k) - hGradient v x))))
    (j : Fin n) :
    MemLp (differenceQuotient (hFirstDerivative v j) k h) 2 (domainMeasure U) ∧
      eLpNorm (differenceQuotient (hFirstDerivative v j) k h) 2 (domainMeasure U) ≤ ‖p‖₊ := by
  have hg := hGradient_quotient_ae W V hWV v k h ha
  have hs : StronglyMeasurable (differenceQuotient (hFirstDerivative v j) k h) := by
    change StronglyMeasurable (fun x => h⁻¹ •
      (hFirstDerivative v j (x + h • coordinate n k) - hFirstDerivative v j x))
    exact (((Lp.stronglyMeasurable (hFirstDerivative v j)).comp_measurable
      (measurable_id.add_const (h • coordinate n k))).sub
      (Lp.stronglyMeasurable (hFirstDerivative v j))).const_smul h⁻¹
  have hb : ∀ᵐ x ∂domainMeasure U,
      ‖differenceQuotient (hFirstDerivative v j) k h x‖ ≤ ‖p x‖ := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hUW hp,
      ae_restrict_of_ae_restrict_of_subset hUW hg,
      ae_restrict_mem U.isOpen.measurableSet] with x hx hxg hxU
    rw [hηU x hxU, one_smul, hxg] at hx
    rw [hx]
    exact PiLp.norm_apply_le (WithLp.toLp 2 (fun i =>
      differenceQuotient (hFirstDerivative v i) k h x)) j
  have hbp : ∀ᵐ x ∂domainMeasure U,
      ‖differenceQuotient (hFirstDerivative v j) k h x‖ ≤ 1 * ‖p x‖ := by
    simpa only [one_mul] using hb
  refine ⟨((Lp.memLp p).mono_measure (Measure.restrict_mono hUW le_rfl)).of_le_mul
    hs.aestronglyMeasurable hbp, ?_⟩
  calc
    _ ≤ eLpNorm p 2 (domainMeasure U) := eLpNorm_mono_ae hs.aestronglyMeasurable hb
    _ ≤ eLpNorm p 2 (domainMeasure W) :=
      eLpNorm_mono_measure _ (Measure.restrict_mono hUW le_rfl)
    _ = ‖p‖₊ := by rw [← Lp.enorm_def, enorm_eq_nnnorm]




/-- The energy computation gives a bound uniform in the nonzero coordinate step.
The coefficient and cutoff constants are fixed before the solution and source. -/
theorem gradientQuotient_step_bound {n : ℕ} (hn : 1 ≤ n)
    (Ω V W : Domain n) (hWV : RelativelyCompactIn W V) (hVΩ : RelativelyCompactIn V Ω)
    (η : Test ℝ W) (hη : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (G M L : ℝ≥0) (theta : ℝ) (ht : 0 < theta)
    (hG : ∀ x, ‖gradient η x‖ ≤ G)
    (A : Space n → Space n →L[ℝ] Space n) (hA : CoefficientBounds V A M L theta)
    (v : H ℝ V 1) (f : Lp ℝ V 2) (heq : WeakEquation V A v f)
    (k : Fin n) (h : ℝ) (hh : h ≠ 0) (hs : P201Specs.AdmissibleSegments W V k h) :
    ∃ p : MeasureTheory.Lp (Space n) 2 (domainMeasure W),
      ((p : Space n → Space n) =ᵐ[domainMeasure W] fun x =>
        η x • (h⁻¹ • (hGradient v (x + h • coordinate n k) - hGradient v x))) ∧
      ‖p‖ ≤ (1 + 2 * (1 + L + 2 * M * G + 2 * L * G + 2 * G) / theta) *
        (‖v‖ + ‖f‖) := by
  have hsub : W ≤ V := subset_closure.trans hWV.2
  have ha : ∀ x ∈ W, x + h • coordinate n k ∈ V := by
    intro x hx
    have hx' := hs x hx 1 (by simp)
    rw [one_mul] at hx'
    exact hx'
  let : IsFiniteMeasure (domainMeasure W) :=
    isFiniteMeasure_restrict.mpr
      ((hWV.1.isBounded.subset subset_closure).measure_lt_top.ne)
  obtain ⟨qH, hq, hqd⟩ := h1Quotient W V hsub k h ha v
  obtain ⟨qL, hqL, hqLn⟩ := local_quotient_toLp_bound hn Ω V W hWV hVΩ v k h hh hs
  have hqn : ‖hUnderlying W 1 qH‖ ≤ ‖v‖ := by
    have hclass : hUnderlying W 1 qH = qL := Lp.ext (hq.trans hqL.symm)
    rw [hclass]
    exact hqLn
  obtain ⟨p, b, r, e, hp, hb, hr, he, hell, hbn, hrn, hen⟩ :=
    energy_fields_of_quotient W V hsub A M L theta hA v k h hh ha qH hq hqd hqn η hη G hG
  obtain ⟨z, _hz, hzd, hK⟩ := localizedQuotient W V hsub η k h ha v
  have hgz := hGradient_localizedQuotient_ae W V hsub η v z k h ha hzd
  have hη1 : ∀ x, |η x| ≤ 1 := by
    intro x
    rw [abs_of_nonneg (hη x).1]
    exact (hη x).2
  have hg : (hGradient z : Space n → Space n) =ᵐ[domainMeasure W]
      (fun x => η x • (p + e) x) := by
    filter_upwards [ae_restrict_of_ae hgz, hp, he, Lp.coeFn_add p e] with x hx hpx hex hpe
    rw [hx, hpe, Pi.add_apply, hpx, hex]
    simp only [smul_add, smul_smul, pow_two, mul_assoc, mul_left_comm, mul_comm]
  have hzoff : ∀ᵐ x ∂volume, x ∉ W → hFirstDerivative z k x = 0 := by
    filter_upwards [hzd k] with x hx hxW
    rw [hx, η.zero_on_compl hxW]
    simp
  have hsource := localized_source_bound W V z p e η hη1 hg k (-h)
    (neg_ne_zero.mpr hh) hzoff f
  have hsource' : |∫ x in V, f x * differenceQuotient (hUnderlying ⊤ 1 z) k (-h) x| ≤
      ‖f‖ * (‖p‖ + 2 * G * ‖v‖) :=
    hsource.trans (mul_le_mul_of_nonneg_left (show ‖p‖ + ‖e‖ ≤ ‖p‖ + 2 * G * ‖v‖ by linarith) (norm_nonneg f))
  have hidentity := localized_energy_identity hn W V hsub η A v f
    hA.2.1.continuousOn hA.1 heq z k h hh ha hzd hK
  have hinner : inner ℝ (b + r) (p + e) =
      -(∫ x in V, f x * differenceQuotient (hUnderlying ⊤ 1 z) k (-h) x) := by
    rw [L2.inner_def]
    refine (integral_congr_ae ?_).trans hidentity
    filter_upwards [Lp.coeFn_add b r, Lp.coeFn_add p e, hp, hb, hr, he]
      with x hbr hpe hpx hbx hrx hex
    rw [hbr, hpe, Pi.add_apply, Pi.add_apply, hbx, hrx, hpx, hex]
  have henergy : |inner ℝ (b + r) (p + e)| ≤ ‖f‖ * (‖p‖ + 2 * G * ‖v‖) := by
    rw [hinner, abs_neg]
    exact hsource'
  refine ⟨p, hp, ?_⟩
  exact energy_absorption_abstract p b r e M.coe_nonneg L.coe_nonneg G.coe_nonneg
    (norm_nonneg v) (norm_nonneg f) ht hell hbn hrn hen henergy


/-- Uniform weighted energy estimates at each small step give the common
coordinate-quotient bound on every relatively compact interior set. -/
theorem gradientQuotientEstimate_of_stepEstimate
    (hStep : ∀ {n : ℕ}, 1 ≤ n → ∀ (Ω V W : Domain n),
      RelativelyCompactIn W V → RelativelyCompactIn V Ω →
      ∀ η : Test ℝ W, (∀ x, 0 ≤ η x ∧ η x ≤ 1) →
      ∀ G : ℝ≥0, (∀ x, ‖gradient η x‖ ≤ G) →
      ∀ (M L : ℝ≥0) (theta : ℝ), 0 < theta →
      ∀ A : Space n → Space n →L[ℝ] Space n, CoefficientBounds V A M L theta →
      ∀ (v : H ℝ V 1) (f : Lp ℝ V 2), WeakEquation V A v f →
      ∀ (k : Fin n) (h : ℝ), h ≠ 0 → P201Specs.AdmissibleSegments W V k h →
      ∃ p : MeasureTheory.Lp (Space n) 2 (domainMeasure W),
        (p : Space n → Space n) =ᵐ[domainMeasure W]
          (fun x => η x • (h⁻¹ •
            (hGradient v (x + h • coordinate n k) - hGradient v x))) ∧
        ‖p‖ ≤ (1 + 2 * (1 + L + 2 * M * G + 2 * L * G + 2 * G) / theta) *
          (‖v‖ + ‖f‖)) :
    gradientQuotientEstimateStatement := by
  intro n hn Ω V U hUV hVΩ M L theta ht
  obtain ⟨W, η, δ, G, hWV, hδ, hη, hηU, hUW, hG, hs⟩ := cutoffEnergyGeometry hUV
  let C : ℝ≥0 := ⟨1 + 2 * (1 + L + 2 * M * G + 2 * L * G + 2 * G) / theta,
    by positivity⟩
  refine ⟨C, ?_⟩
  intro A hA v f heq j k
  refine ⟨δ, hδ, fun h hh hhδ => ?_⟩
  have hsegments := hs k h hhδ
  have ha : ∀ x ∈ W, x + h • coordinate n k ∈ V := by
    intro x hx
    have hxseg := hsegments x hx 1 (by simp)
    change x + (1 * h) • coordinate n k ∈ V at hxseg
    simpa only [one_mul] using hxseg
  have hWV' : W ≤ V := subset_closure.trans hWV.2
  obtain ⟨p, hp, hpn⟩ := hStep hn Ω V W hWV hVΩ η hη G hG M L theta ht
    A hA v f heq k h (abs_pos.mp hh) hsegments
  obtain ⟨hm, hb⟩ := scalar_quotient_of_weighted_gradient hUW hWV' η hηU v k h ha p hp j
  refine ⟨fun x hx => ha x (hUW hx), hm, hb.trans ?_⟩
  have hpnn : ‖p‖₊ ≤ C * (‖v‖₊ + ‖f‖₊) := by
    change ‖p‖ ≤ (C : ℝ) * ((‖v‖₊ + ‖f‖₊ : ℝ≥0) : ℝ)
    change ‖p‖ ≤ (1 + 2 * (1 + (L : ℝ) + 2 * M * G + 2 * L * G + 2 * G) / theta) *
      (‖v‖ + ‖f‖)
    exact hpn
  exact_mod_cast hpnn


/-- Uniform local control of every coordinate quotient of the weak gradient.
This is obtained from the weak equation with the compact H¹ difference test,
without differentiating the source or assuming any second derivative. -/
theorem gradientQuotientEstimate : P201Specs.InteriorH2.gradientQuotientEstimateStatement := by
  apply gradientQuotientEstimate_of_stepEstimate
  intro n hn Ω V W hWV hVΩ η hη G hG M L theta ht A hA v f heq k h hh hs
  exact gradientQuotient_step_bound hn Ω V W hWV hVΩ η hη G M L theta ht hG
    A hA v f heq k h hh hs

/-- The quantitative interior H² estimate for locally Lipschitz nonsymmetric
uniformly elliptic real coefficients and an L² right-hand side. -/
theorem interiorH2Estimate : P201Specs.InteriorH2.interiorH2EstimateStatement :=
  interiorH2Estimate_of_gradientEstimate gradientQuotientEstimate

/-- Every local H¹ weak solution with locally L² forcing has local H² regularity. -/
theorem interiorH2Regularity : P201Specs.InteriorH2.interiorH2RegularityStatement :=
  interiorH2Regularity_of_estimate interiorH2Estimate

end P201.InteriorH2
