import MathGenome.Internal.LinearPDE.P201.Common.SpatialInterfaces
import MathGenome.Internal.LinearPDE.P201Specs.Common.InteriorTesting
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Normed.Module.HahnBanach

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff InnerProductSpace
namespace P201.InteriorTesting

lemma gradient_const {n : ℕ} (c : ℝ) :
    gradient (fun _ : Space n => c) = 0 := by
  funext x
  apply PiLp.ext
  intro i
  simp

lemma laplacian_const {n : ℕ} (c : ℝ) (x : Space n) :
    laplacian (fun _ : Space n => c) x = 0 := by
  have hs (i : Fin n) :
      (i ::ₘ {i} : MultiIndex n).sort (· ≤ ·) = [i, i] := by
    rw [Multiset.sort_cons i {i} (· ≤ ·) (by simp), Multiset.sort_singleton]
  simp [laplacian, P201Specs.laplacian, P102.U4.multiPartial, hs,
    P102.U4.partialWord]

theorem constantTesting : P201Specs.InteriorTesting.ConstantTestingStatement := by
  intro n hn Ω c
  constructor
  · intro x hx
    exact laplacian_const c x
  · intro φ
    change weakNegativeDivergence Ω (gradient (fun _ : Space n => c)) φ = _
    rw [gradient_const]
    simp [weakNegativeDivergence, P201Specs.weakNegativeDivergence]

lemma flux_component_contDiff {n : ℕ} (Ω : Domain n)
    {F : Space n → Space n} (hF : ContDiffOn ℝ 1 F Ω) (i : Fin n) :
    ContDiffOn ℝ 1 (fun x => F x i) Ω :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).contDiff.comp_contDiffOn hF

lemma divergence_continuous {n : ℕ} (Ω : Domain n)
    {F : Space n → Space n} (hF : ContDiffOn ℝ 1 F Ω) :
    ContinuousOn (P201Specs.divergence F) Ω := by
  apply continuousOn_finsetSum
  intro i hi
  exact (((flux_component_contDiff Ω hF i).fderiv_of_isOpen Ω.isOpen
    (m := 0) (by simp)).clm_apply contDiffOn_const).continuousOn

lemma flux_testing_identity {n : ℕ} (Ω : Domain n)
    {F : Space n → Space n} (hF : ContDiffOn ℝ 1 F Ω) (φ : Test ℝ Ω) :
    P201Specs.weakNegativeDivergence Ω F φ =
      ∫ x in Ω, -P201Specs.divergence F x * φ x := by
  let ψ (i : Fin n) := P102.U4.testPartialWord Ω [i] φ
  have hψ (i : Fin n) (x : Space n) :
      ψ i x = fderiv ℝ φ x (coordinate n i) := by
    exact congrFun (P102.U4.testPartialWord_coe Ω [i] φ) x
  have hFi (i : Fin n) : LocallyIntegrableOn (fun x => F x i) Ω volume :=
    (flux_component_contDiff Ω hF i).continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  have hi (i : Fin n) : Integrable (fun x => F x i * ψ i x) volume := by
    have h := (ψ i).integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) (hFi i)
    simpa only [ContinuousLinearMap.mul_apply', mul_comm] using h
  have hdi (i : Fin n) : Integrable
      (fun x => φ x * fderiv ℝ (fun y => F y i) x (coordinate n i)) volume := by
    have hd : ContinuousOn (fun x => fderiv ℝ (fun y => F y i) x (coordinate n i)) Ω :=
      (((flux_component_contDiff Ω hF i).fderiv_of_isOpen Ω.isOpen
      (m := 0) (by simp)).clm_apply contDiffOn_const).continuousOn
    exact φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ)
      (hd.locallyIntegrableOn Ω.isOpen.measurableSet)
  have he (x : Space n) :
      inner ℝ (F x) (P201Specs.gradient φ x) = ∑ i, F x i * ψ i x := by
    simp [PiLp.inner_apply, P201Specs.gradient, hψ, RCLike.inner_apply, mul_comm]
  change (∫ x in Ω, inner ℝ (F x) (P201Specs.gradient φ x)) = _
  simp_rw [he]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    exact Finset.sum_eq_zero fun i _ => by rw [(ψ i).zero_on_compl hx]; simp)]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  rw [P102.U4.setIntegral_mul_test]
  simp only [P201Specs.divergence, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  rw [integral_finsetSum _ (fun i _ => (hdi i).neg.congr (by
    filter_upwards [] with x
    change -(φ x * _) = -(_ * φ x)
    rw [mul_comm]))]
  apply Finset.sum_congr rfl
  intro i hi'
  have hibp := P102.U4.integral_test_mul_partial Ω (flux_component_contDiff Ω hF i) i φ
  simp only [integral_neg]
  rw [show (∫ x, fderiv ℝ (fun y => F y i) x (coordinate n i) * φ x) =
      ∫ x, φ x * fderiv ℝ (fun y => F y i) x (coordinate n i) from by
      congr 1; funext x; ring]
  rw [hibp, neg_neg]
  congr 1
  funext x
  exact mul_comm _ _

lemma flux_testing_iff {n : ℕ} (Ω : Domain n)
    {F : Space n → Space n} {f : Space n → ℝ}
    (hF : ContDiffOn ℝ 1 F Ω) (hf : ContinuousOn f Ω) :
    (∀ x ∈ Ω, -P201Specs.divergence F x = f x) ↔
      ∀ φ : Test ℝ Ω, P201Specs.weakNegativeDivergence Ω F φ =
        ∫ x in Ω, f x * φ x := by
  have hd := (divergence_continuous Ω hF).neg
  constructor
  · intro h φ
    rw [flux_testing_identity Ω hF]
    exact setIntegral_congr_fun Ω.isOpen.measurableSet (fun x hx => by rw [h x hx])
  · intro h
    have he : P201Specs.regularDistribution Ω (fun x => -P201Specs.divergence F x) =
        P201Specs.regularDistribution Ω f := by
      ext φ
      change P102.U4.regularDistribution Ω (-P201Specs.divergence F) φ =
        P102.U4.regularDistribution Ω f φ
      exact (P102.U4.regular_pairing n ℝ Ω _
        (hd.locallyIntegrableOn Ω.isOpen.measurableSet) φ).trans
        ((flux_testing_identity Ω hF φ).symm.trans ((h φ).trans
          (P102.U4.regular_pairing n ℝ Ω _
            (hf.locallyIntegrableOn Ω.isOpen.measurableSet) φ).symm))
    have hae := (P102.U4.regular_injectivity n ℝ Ω _ _
      (hd.locallyIntegrableOn Ω.isOpen.measurableSet)
      (hf.locallyIntegrableOn Ω.isOpen.measurableSet)).mp he
    exact MeasureTheory.Measure.eqOn_open_of_ae_eq hae Ω.isOpen hd hf

lemma elliptic_flux_contDiff {n : ℕ} (Ω : Domain n)
    {A : Space n → Space n →L[ℝ] Space n} {u : Space n → ℝ}
    (hA : ContDiffOn ℝ 1 A Ω) (hu : ContDiffOn ℝ 2 u Ω) :
    ContDiffOn ℝ 1 (fun x => A x (P201Specs.gradient u x)) Ω := by
  apply hA.clm_apply
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.contDiff.comp_contDiffOn
  apply contDiffOn_pi.mpr
  intro i
  exact (hu.fderiv_of_isOpen Ω.isOpen (m := 1) (by norm_num)).clm_apply contDiffOn_const

theorem classicalTesting : P201Specs.InteriorTesting.ClassicalTestingStatement := by
  intro n hn Ω A u f hA hu hf
  exact flux_testing_iff Ω (elliptic_flux_contDiff Ω hA hu) hf

/-- The shared distributional divergence has exactly the manuscript's
integral pairing on L² fluxes, with its positive weak sign. -/
lemma negativeDivergenceDistribution_pairing {n : ℕ} (Ω : Domain n)
    (F : MeasureTheory.Lp (Space n) 2 (domainMeasure Ω)) (φ : Test ℝ Ω) :
    P201Specs.negativeDivergenceDistribution Ω F φ =
      P201Specs.weakNegativeDivergence Ω F φ := by
  let ψ (i : Fin n) := P102.U4.testPartialWord Ω [i] φ
  have hFi (i : Fin n) : LocallyIntegrableOn (fun x => F x i) Ω volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      (((Lp.memLp F).eval_piLp i).locallyIntegrable (by norm_num))
  have hi (i : Fin n) : IntegrableOn (fun x => F x i * ψ i x) Ω volume := by
    have h := (ψ i).integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) (hFi i)
    exact (h.congr (Eventually.of_forall fun x => mul_comm _ _)).integrableOn
  have he (x : Space n) : inner ℝ (F x) (P201Specs.gradient φ x) =
      ∑ i, F x i * ψ i x := by
    have hψ (i : Fin n) : ψ i x = fderiv ℝ φ x (coordinate n i) :=
      congrFun (P102.U4.testPartialWord_coe Ω [i] φ) x
    simp [PiLp.inner_apply, P201Specs.gradient, hψ, RCLike.inner_apply, mul_comm]
  change (-∑ i : Fin n, P102.U4.distributionPartial {i}
    (P102.U4.regularDistribution Ω (fun x => F x i))) φ = _
  simp only [neg_apply, sum_apply, P102.U4.distributionPartial,
    Multiset.card_singleton, pow_one, smul_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul, neg_one_mul, Finset.sum_neg_distrib, neg_neg,
    Multiset.sort_singleton]
  change (∑ i : Fin n, P102.U4.regularDistribution Ω (fun x => F x i) (ψ i)) =
    ∫ x in Ω, inner ℝ (F x) (P201Specs.gradient φ x)
  simp_rw [P102.U4.regular_pairing n ℝ Ω _ (hFi _), he]
  exact (integral_finsetSum _ (fun i _ => hi i)).symm

/-- The derivative coordinate is continuous for the full Hilbert norm. -/
def firstDerivativeMap {n : ℕ} (Ω : Domain n) (i : Fin n) :
    H ℝ Ω 1 →L[ℝ] Lp ℝ Ω 2 :=
  (PiLp.proj 2 _ (⟨{i}, by simp⟩ : P102.U4.SobolevIndex n 1)).comp
    (P201Specs.hilbertSubmodule ℝ Ω 1).subtypeL

lemma firstDerivativeMap_apply {n : ℕ} (Ω : Domain n) (i : Fin n) (v : H ℝ Ω 1) :
    firstDerivativeMap Ω i v = P201Specs.hFirstDerivative v i := rfl

/-- Pairing an L² flux with the weak gradient gives a continuous functional. -/
def fluxFunctional {n : ℕ} (Ω : Domain n)
    (F : MeasureTheory.Lp (Space n) 2 (domainMeasure Ω)) : H ℝ Ω 1 →L[ℝ] ℝ :=
  ∑ i : Fin n, (innerSL ℝ ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).compLp F)).comp
    (firstDerivativeMap Ω i)

lemma fluxFunctional_integral {n : ℕ} (Ω : Domain n)
    (F : MeasureTheory.Lp (Space n) 2 (domainMeasure Ω)) (v : H ℝ Ω 1) :
    fluxFunctional Ω F v = ∫ x in Ω, inner ℝ (F x) (P201Specs.hGradient v x) := by
  have hg : (P201Specs.hGradient v : Space n → Space n) =ᵐ[domainMeasure Ω]
      (fun x => WithLp.toLp 2 (fun i => P201Specs.hFirstDerivative v i x)) :=
    MemLp.coeFn_toLp _
  have hi (i : Fin n) : IntegrableOn
      (fun x => F x i * P201Specs.hFirstDerivative v i x) Ω volume :=
    ((Lp.memLp F).eval_piLp i).integrable_mul (Lp.memLp (P201Specs.hFirstDerivative v i))
  rw [show (∫ x in Ω, inner ℝ (F x) (P201Specs.hGradient v x)) =
      ∫ x in Ω, ∑ i, F x i * P201Specs.hFirstDerivative v i x from by
    apply integral_congr_ae
    filter_upwards [hg] with x hx
    rw [hx]
    simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp only [fluxFunctional, sum_apply, ContinuousLinearMap.comp_apply,
    firstDerivativeMap_apply, innerSL_apply_apply, L2.inner_def]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).coeFn_compLp F] with x hx
  simp [hx, RCLike.inner_apply, mul_comm]

lemma smooth_firstDerivative {n : ℕ} (Ω : Domain n) (v : H ℝ Ω 1)
    (φ : Test ℝ Ω) (hv : P201Specs.hUnderlying Ω 1 v = P102.U4.testToDomainLp Ω 2 φ)
    (i : Fin n) :
    P201Specs.hFirstDerivative v i =
      P102.U4.testToDomainLp Ω 2 (P102.U4.testPartialWord Ω [i] φ) := by
  symm
  apply P102.U4.sobolev_derivative_unique Ω 1 2 (P201Specs.hToW ℝ Ω 1 v)
    (⟨{i}, by simp⟩ : P102.U4.SobolevIndex n 1)
  change P102.U4.distributionPartial {i} (P102.U4.regularDistribution Ω
    (P201Specs.hUnderlying Ω 1 v)) = _
  rw [hv, P102.U4.regular_testToDomainLp, P102.U4.regular_testToDomainLp]
  rw [P102.U4.derivative_classicalCompatibility n ℝ Ω {i} φ
    (φ.contDiff.of_le (by simp)).contDiffOn]
  congr 1
  ext x
  simpa [P102.U4.multiPartial] using
    (congrFun (P102.U4.testPartialWord_coe Ω [i] φ) x).symm

lemma smooth_gradient_ae {n : ℕ} (Ω : Domain n) (v : H ℝ Ω 1)
    (φ : Test ℝ Ω) (hv : P201Specs.hUnderlying Ω 1 v = P102.U4.testToDomainLp Ω 2 φ) :
    (P201Specs.hGradient v : Space n → Space n) =ᵐ[domainMeasure Ω]
      P201Specs.gradient φ := by
  have hg : (P201Specs.hGradient v : Space n → Space n) =ᵐ[domainMeasure Ω]
      (fun x => WithLp.toLp 2 (fun i => P201Specs.hFirstDerivative v i x)) :=
    MemLp.coeFn_toLp _
  have hi (i : Fin n) : (P201Specs.hFirstDerivative v i : Space n → ℝ) =ᵐ[domainMeasure Ω]
      (fun x => fderiv ℝ φ x (coordinate n i)) := by
    rw [smooth_firstDerivative Ω v φ hv i]
    exact (P102.U4.testToDomainLp_ae Ω 2 _).trans (Eventually.of_forall
      (fun x => congrFun (P102.U4.testPartialWord_coe Ω [i] φ) x))
  filter_upwards [hg, (ae_all_iff.mpr hi)] with x hx hxi
  rw [hx]
  apply PiLp.ext
  intro i
  exact hxi i

/-- Every actual compact smooth test has an H¹₀ class; the distributional
hypothesis in the specification therefore tests every smooth test. -/
lemma exists_test_class {n : ℕ} (Ω : Domain n) (φ : Test ℝ Ω) :
    ∃ v : H10 ℝ Ω, P201Specs.hZeroUnderlying Ω v = P102.U4.testToDomainLp Ω 2 φ := by
  obtain ⟨u, hu⟩ := P102.U4.zeroExtension_smoothInclusion Ω 1 2 φ
  let v := (P201Specs.hToW ℝ Ω 1).symm u
  have hv : v ∈ (P102.U4.smoothSobolevSubmodule ℝ Ω 1 2).comap
      (P201Specs.hToW ℝ Ω 1).toLinearMap := by
    change ∃ ψ, P102.U4.testToDomainLp Ω 2 ψ =
      P102.U4.sobolevUnderlying (P201Specs.hToW ℝ Ω 1 v)
    exact ⟨φ, by simpa [v] using hu.symm⟩
  refine ⟨⟨v, Submodule.le_topologicalClosure _ hv⟩, ?_⟩
  change P201Specs.hUnderlying Ω 1 v = _
  change P102.U4.sobolevUnderlying (P201Specs.hToW ℝ Ω 1 v) = _
  simpa [v] using hu

theorem energyTesting : P201Specs.InteriorTesting.EnergyTestingStatement := by
  intro n hn Ω F f h v
  obtain ⟨g, hg, _⟩ := exists_extension_norm_eq (P201Specs.hZeroSubmodule ℝ Ω) f
  have hc : IsClosed {w : H ℝ Ω 1 | fluxFunctional Ω F w = g w} :=
    isClosed_eq (fluxFunctional Ω F).continuous g.continuous
  have hs : ((P102.U4.smoothSobolevSubmodule ℝ Ω 1 2).comap
      (P201Specs.hToW ℝ Ω 1).toLinearMap : Set (H ℝ Ω 1)) ⊆
      {w | fluxFunctional Ω F w = g w} := by
    intro w hw
    have hwmem := hw
    obtain ⟨φ, hφ⟩ := hw
    let z : H10 ℝ Ω := ⟨w, Submodule.le_topologicalClosure _ hwmem⟩
    have hz : P201Specs.hZeroUnderlying Ω z = P102.U4.testToDomainLp Ω 2 φ := hφ.symm
    change fluxFunctional Ω F w = g w
    rw [fluxFunctional_integral]
    have hae := smooth_gradient_ae Ω w φ hφ.symm
    have he : (∫ x in Ω, inner ℝ (F x) (P201Specs.hGradient w x)) =
        P201Specs.weakNegativeDivergence Ω F φ := by
      exact integral_congr_ae (hae.mono fun x hx => congrArg (fun a => inner ℝ (F x) a) hx)
    exact he.trans ((negativeDivergenceDistribution_pairing Ω F φ).symm.trans
      ((h φ z hz).trans (hg z).symm))
  have he := (closure_minimal hs hc) v.property
  rw [← fluxFunctional_integral]
  exact he.trans (hg v)

end P201.InteriorTesting
