import MathGenome.Internal.FourierSobolev.Specs.P102.U4.RegularDerivatives
import MathGenome.Internal.FourierSobolev.P102.U4.TestSpace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ContDiff Distributions
namespace P102.U4

abbrev regular : RegularDerivativesExpected.RegularType := @regularDistribution
abbrev derivative : RegularDerivativesExpected.DerivativeType := @distributionPartial

/-- Tests realize the ordinary coordinate word derivatives. -/
theorem testPartialWord_coe {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (l : List (Fin d)) (φ : TestSpace 𝕜 Ω) :
    ⇑(testPartialWord Ω l φ) = partialWord φ l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    ext x
    change TestFunction.lineDerivCLM 𝕜 (coordinateVector d i) (testPartialWord Ω l φ) x = _
    rw [TestFunction.lineDerivCLM_eq_fderivCLM,
      TestFunction.fderivCLM_apply_of_le _ (by simp)]
    rw [ih]
    rfl

/-- Composing coordinate words concatenates their lists. -/
theorem testPartialWord_append {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (l l' : List (Fin d)) (φ : TestSpace 𝕜 Ω) :
    testPartialWord Ω (l ++ l') φ = testPartialWord Ω l (testPartialWord Ω l' φ) := by
  induction l with
  | nil => rfl
  | cons i l ih => simpa only [List.cons_append, testPartialWord,
      ContinuousLinearMap.comp_apply] using congrArg (TestFunction.lineDerivCLM 𝕜
        (coordinateVector d i)) ih

/-- Smoothness of tests makes the coordinate word independent of its ordering. -/
theorem testPartialWord_perm {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    {l l' : List (Fin d)} (h : l.Perm l') (φ : TestSpace 𝕜 Ω) :
    testPartialWord Ω l φ = testPartialWord Ω l' φ := by
  ext x
  rw [testPartialWord_coe, testPartialWord_coe, partialWord_perm φ.contDiff h]

theorem regular_pairing : RegularDerivativesExpected.Pairing := by
  intro d 𝕜 _ Ω f hf φ
  rw [regularDistribution, TestFunction.integralAgainstBilinCLM_eq_integral hf]
  change (∫ x, φ x * f x) = _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (Ω : Set (Space d)))]
  · exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  · intro x hx
    simp only [φ.zero_on_compl hx, Pi.zero_apply, zero_mul]

theorem regular_supportBound : RegularDerivativesExpected.SupportBound := by
  intro d 𝕜 _ Ω f hf K hK φ
  have hfK := hf.integrableOn_compact_subset hK K.isCompact
  rw [regularDistribution, TestFunction.integralAgainstBilinCLM_eq_integral hf]
  change ‖∫ x, φ x * f x‖ ≤ _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (K : Set (Space d)))]
  · have hpoint : ∀ x ∈ K, ‖φ x‖ ≤ coordinateSupSeminorm 𝕜 K 0 φ := by
      intro x hx
      have h := (coordinateSeminormFormula d 𝕜 K 0 φ _ (apply_nonneg _ _)).mp
        le_rfl 0 le_rfl (fun j => Fin.elim0 j) x hx
      simpa [iteratedFDeriv_zero_apply] using h
    calc
      ‖∫ x in K, φ x * f x‖ ≤ ∫ x in K, coordinateSupSeminorm 𝕜 K 0 φ * ‖f x‖ :=
        norm_integral_le_of_norm_le (hfK.norm.const_mul _) <|
          (ae_restrict_mem K.isCompact.measurableSet).mono fun x hx => by
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right (hpoint x hx) (norm_nonneg _)
      _ = _ := integral_const_mul _ _
  · intro x hx
    simp only [φ.zero_on_compl hx, Pi.zero_apply, zero_mul]

theorem regular_injectivity : RegularDerivativesExpected.Injectivity := by
  intro d 𝕜 _ Ω f g hf hg
  constructor
  · intro h
    have hz := Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hf.sub hg) ?_
    · exact (ae_restrict_iff' Ω.isOpen.measurableSet).mpr <|
        hz.mono fun x hx hΩ => sub_eq_zero.mp (hx hΩ)
    · intro η hη hc hs
      let ηTest : TestSpace ℝ Ω := ⟨η, hη, hc, hs⟩
      let φ : TestSpace 𝕜 Ω :=
        TestFunction.postcompCLM (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) ηTest
      have he : (∫ x, φ x * f x) = ∫ x, φ x * g x := by
        have := congrArg (fun T : DistributionSpace 𝕜 Ω => T φ) h
        simpa only [regularDistribution, TestFunction.integralAgainstBilinCLM_eq_integral hf,
          TestFunction.integralAgainstBilinCLM_eq_integral hg, ContinuousLinearMap.mul_apply'] using this
      have hfi := φ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜) hf
      have hgi := φ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜) hg
      change (∫ x, η x • (f - g) x) = 0
      simp_rw [Pi.sub_apply, smul_sub, RCLike.real_smul_eq_coe_mul]
      rw [integral_sub]
      · exact sub_eq_zero.mpr he
      · exact hfi
      · exact hgi
  · intro h
    ext φ
    rw [regular_pairing d 𝕜 Ω f hf, regular_pairing d 𝕜 Ω g hg]
    exact integral_congr_ae (h.mul Filter.EventuallyEq.rfl)

theorem derivative_formula : RegularDerivativesExpected.DerivativeFormula := by
  intro d 𝕜 _ Ω α T φ
  refine ⟨testPartialWord Ω (α.sort (· ≤ ·)) φ, ?_, rfl⟩
  intro x
  exact congrFun (testPartialWord_coe Ω _ φ) x

theorem derivative_zero : RegularDerivativesExpected.DerivativeZero := by
  intro d 𝕜 _ Ω T
  ext φ
  simp [distributionPartial, testPartialWord]

theorem derivative_add : RegularDerivativesExpected.DerivativeAdd := by
  intro d 𝕜 _ Ω α β T
  have hp : ((α + β).sort (· ≤ ·)).Perm
      (β.sort (· ≤ ·) ++ α.sort (· ≤ ·)) :=
    Multiset.coe_eq_coe.mp (by simp only [← Multiset.coe_add, Multiset.sort_eq]; exact add_comm _ _)
  ext φ
  simp only [distributionPartial, smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, Multiset.card_add, pow_add]
  rw [testPartialWord_perm Ω hp, testPartialWord_append]
  ring

theorem derivative_coordinateCommutation : RegularDerivativesExpected.CoordinateCommutation := by
  intro d 𝕜 _ Ω i j T
  rw [← derivative_add d 𝕜 Ω, ← derivative_add d 𝕜 Ω, add_comm]

/-- A word of length k consumes exactly k of the available derivatives on Ω. -/
theorem partialWord_contDiffOn {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    {f : Space d → 𝕜} {N : ℕ} (hf : ContDiffOn ℝ (N : ℕ) f Ω)
    (l : List (Fin d)) (n : ℕ) (hn : n + l.length ≤ N) :
    ContDiffOn ℝ (n : ℕ) (partialWord f l) Ω := by
  induction l generalizing n with
  | nil => exact hf.of_le (by exact_mod_cast hn)
  | cons i l ih =>
    have h := ih (n + 1) (by simp only [List.length_cons] at hn; omega)
    exact (h.fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply contDiffOn_const

/-- Integration by parts only needs f to be C¹ on Ω. The library's support-local
hypotheses avoid imposing any differentiability on the ambient representative outside Ω. -/
theorem integral_test_mul_partial {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) {f : Space d → 𝕜} (hf : ContDiffOn ℝ 1 f Ω)
    (i : Fin d) (φ : TestSpace 𝕜 Ω) :
    (∫ x, φ x * fderiv ℝ f x (coordinateVector d i)) =
      -(∫ x, testPartialWord Ω [i] φ x * f x) := by
  have hfl : LocallyIntegrableOn f Ω volume :=
    hf.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  have hd : LocallyIntegrableOn (fun x => fderiv ℝ f x (coordinateVector d i)) Ω volume :=
    ((hf.fderiv_of_isOpen Ω.isOpen (m := 0) (by simp)).clm_apply
      contDiffOn_const).continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  have hcoe : ⇑(testPartialWord Ω [i] φ) =
      fun x => fderiv ℝ φ x (coordinateVector d i) := testPartialWord_coe Ω [i] φ
  rw [hcoe]
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (by
      have h := (testPartialWord Ω [i] φ).integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜) hfl
      change Integrable (fun x => testPartialWord Ω [i] φ x * f x) volume at h
      rwa [hcoe] at h)
    (φ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜) hd)
    (φ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜) hfl)
    (fun x _ => φ.contDiff.differentiable (by simp) x)
    (fun x hx => (hf.contDiffAt (Ω.isOpen.mem_nhds (φ.tsupport_subset hx))).differentiableAt
      (by simp))

/-- Repeated integration by parts, with precisely the finite regularity needed
for the specified word. Only the smooth test word is reordered. -/
theorem integral_test_mul_partialWord {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) {f : Space d → 𝕜} (l : List (Fin d))
    (hf : ContDiffOn ℝ (l.length : ℕ) f Ω) (φ : TestSpace 𝕜 Ω) :
    (∫ x, φ x * partialWord f l x) =
      (-1 : 𝕜) ^ l.length * ∫ x, testPartialWord Ω l φ x * f x := by
  induction l generalizing φ with
  | nil => simp [partialWord, testPartialWord]
  | cons i l ih =>
    have hg : ContDiffOn ℝ 1 (partialWord f l) Ω :=
      partialWord_contDiffOn Ω hf l 1 (by simp only [List.length_cons]; omega)
    have h1 := integral_test_mul_partial Ω hg i φ
    change (∫ x, φ x * partialWord f (i :: l) x) = _ at h1
    rw [h1, ih (hf.of_le (by simp))]
    have hw : testPartialWord Ω l (testPartialWord Ω [i] φ) =
        testPartialWord Ω (i :: l) φ := by
      rw [← testPartialWord_append]
      exact testPartialWord_perm Ω (by simpa only [List.singleton_append] using
        (List.perm_append_comm (l₁ := l) (l₂ := [i]))) φ
    rw [hw]
    simp only [List.length_cons, pow_succ]
    ring

theorem derivative_classicalCompatibility : RegularDerivativesExpected.ClassicalCompatibility := by
  intro d 𝕜 _ Ω α f hf
  have hfl : LocallyIntegrableOn f Ω volume :=
    hf.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  have hd : LocallyIntegrableOn (multiPartial f α) Ω volume :=
    (partialWord_contDiffOn Ω hf (α.sort (· ≤ ·)) 0 (by simp)).continuousOn.locallyIntegrableOn
      Ω.isOpen.measurableSet
  ext φ
  simp only [distributionPartial, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    regularDistribution, TestFunction.integralAgainstBilinCLM_eq_integral hfl,
    TestFunction.integralAgainstBilinCLM_eq_integral hd, ContinuousLinearMap.mul_apply']
  have hi := integral_test_mul_partialWord Ω (α.sort (· ≤ ·)) (by simpa using hf) φ
  simpa only [Multiset.length_sort, multiPartial] using hi.symm

end P102.U4
