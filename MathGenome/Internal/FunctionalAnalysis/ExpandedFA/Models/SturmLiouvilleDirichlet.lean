import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.SturmLiouvilleDirichlet
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.ClosedNonnegativeForms
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.OneDimensionalSobolev
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.RellichEmbeddings

set_option maxHeartbeats 1000000

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace
namespace ExpandedFA.Models.SturmLiouvilleDirichlet
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.OneDimensional
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open ExpandedFA.Unbounded

variable {𝕜 : Type} [RCLike 𝕜] {a b : ℝ}

theorem coefficientLp_coe (r : ℝ → ℝ) (hr : ContinuousOn r (Icc a b)) :
    coefficientLp (𝕜 := 𝕜) r hr =ᵐ[volume.restrict
      (spatialInterval a b : Set (Domain 1))] (fun z => (r (z 0) : 𝕜)) :=
  MemLp.coeFn_toLp _

theorem multiplier_coe (r : ℝ → ℝ) (hr : ContinuousOn r (Icc a b))
    (u : L2 𝕜 a b) :
    multiplier r hr u =ᵐ[volume.restrict (spatialInterval a b : Set (Domain 1))]
      (fun z => (r (z 0) : 𝕜) * u z) := by
  filter_upwards [(ContinuousLinearMap.mul 𝕜 𝕜).coeFn_holder (r := 2)
    (coefficientLp r hr) u, coefficientLp_coe (𝕜 := 𝕜) r hr] with z hz hcoeff
  exact hz.trans (by rw [hcoeff]; rfl)

theorem weighted_inner_integral (r : ℝ → ℝ) (hr : ContinuousOn r (Icc a b))
    (v u : L2 𝕜 a b) :
    inner 𝕜 v (multiplier r hr u) = ∫ z : Domain 1,
      (r (z 0) : 𝕜) * conj (v z) * u z
      ∂(volume.restrict (spatialInterval a b : Set (Domain 1))) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiplier_coe r hr u] with z hz
  rw [hz, RCLike.inner_apply]
  ring

theorem weighted_inner_integrable (r : ℝ → ℝ) (hr : ContinuousOn r (Icc a b))
    (v u : L2 𝕜 a b) :
    Integrable (fun z : Domain 1 => (r (z 0) : 𝕜) * conj (v z) * u z)
      (volume.restrict (spatialInterval a b : Set (Domain 1))) := by
  apply (L2.integrable_inner (𝕜 := 𝕜) v (multiplier r hr u)).congr
  filter_upwards [multiplier_coe r hr u] with z hz
  rw [hz, RCLike.inner_apply]
  ring

theorem form_integral : Spec.FormIntegral := by
  intro 𝕜 _ a b c v u
  rw [form, weighted_inner_integral, weighted_inner_integral, integral_add]
  · exact weighted_inner_integrable c.p c.p_C1.continuousOn _ _
  · exact weighted_inner_integrable c.q c.q_continuous _ _

/-- Multiplication by a real coefficient is symmetric, also over ℂ. -/
theorem multiplier_symmetric (r : ℝ → ℝ) (hr : ContinuousOn r (Icc a b))
    (v u : L2 𝕜 a b) :
    inner 𝕜 (multiplier r hr v) u = inner 𝕜 v (multiplier r hr u) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiplier_coe r hr v, multiplier_coe r hr u] with z hv hu
  rw [hv, hu]
  simp only [RCLike.inner_apply, map_mul, RCLike.conj_ofReal]
  ring

theorem form_hermitian : Spec.FormHermitian := by
  intro 𝕜 _ a b c v u
  simp only [form, map_add, inner_conj_symm]
  rw [multiplier_symmetric, multiplier_symmetric]

theorem form_add_left (c : Coefficients a b) (v w u : H1 𝕜 a b) :
    form c (v + w) u = form c v u + form c w u := by
  simp only [form]
  change inner 𝕜 (derivativeLp v + derivativeLp w) _ +
    inner 𝕜 (baseLp v + baseLp w) _ = _
  rw [inner_add_left, inner_add_left]
  abel

theorem form_smul_left (c : Coefficients a b) (t : 𝕜) (v u : H1 𝕜 a b) :
    form c (t • v) u = conj t * form c v u := by
  simp only [form]
  change inner 𝕜 (t • derivativeLp v) _ + inner 𝕜 (t • baseLp v) _ = _
  rw [inner_smul_left, inner_smul_left, mul_add]

theorem form_add_right (c : Coefficients a b) (v u w : H1 𝕜 a b) :
    form c v (u + w) = form c v u + form c v w := by
  simp only [form]
  change inner 𝕜 _ (multiplier _ _ (derivativeLp u + derivativeLp w)) +
    inner 𝕜 _ (multiplier _ _ (baseLp u + baseLp w)) = _
  rw [map_add, map_add, inner_add_right, inner_add_right]
  abel

theorem form_smul_right (c : Coefficients a b) (t : 𝕜) (v u : H1 𝕜 a b) :
    form c v (t • u) = t * form c v u := by
  simp only [form]
  change inner 𝕜 _ (multiplier _ _ (t • derivativeLp u)) +
    inner 𝕜 _ (multiplier _ _ (t • baseLp u)) = _
  rw [map_smul, map_smul, inner_smul_right, inner_smul_right, mul_add]

@[simp] theorem form_zero_right (c : Coefficients a b) (v : H1 𝕜 a b) :
    form c v 0 = 0 := by
  simpa using form_smul_right c 0 v (0 : H1 𝕜 a b)

@[simp] theorem form_zero_left (c : Coefficients a b) (u : H1 𝕜 a b) :
    form c 0 u = 0 := by
  simpa using form_smul_left c 0 (0 : H1 𝕜 a b) u

/-- The form is genuinely bounded for the upstream H¹ sum norm. -/
theorem form_bound (c : Coefficients a b) (v u : H1 𝕜 a b) :
    ‖form c v u‖ ≤
      (‖multiplier (𝕜 := 𝕜) c.p c.p_C1.continuousOn‖ +
        ‖multiplier (𝕜 := 𝕜) c.q c.q_continuous‖) * ‖v‖ * ‖u‖ := by
  have hv₀ : ‖baseLp v‖ ≤ ‖v‖ := PiLp.norm_apply_le v.val _
  have hv₁ : ‖derivativeLp v‖ ≤ ‖v‖ := PiLp.norm_apply_le v.val _
  have hu₀ : ‖baseLp u‖ ≤ ‖u‖ := PiLp.norm_apply_le u.val _
  have hu₁ : ‖derivativeLp u‖ ≤ ‖u‖ := PiLp.norm_apply_le u.val _
  have hmul (r : ℝ → ℝ) (hr : ContinuousOn r (Icc a b)) (x y : L2 𝕜 a b)
      (hx : ‖x‖ ≤ ‖v‖) (hy : ‖y‖ ≤ ‖u‖) :
      ‖inner 𝕜 x (multiplier r hr y)‖ ≤ ‖multiplier (𝕜 := 𝕜) r hr‖ * ‖v‖ * ‖u‖ := by
    calc
      ‖inner 𝕜 x (multiplier r hr y)‖ ≤ ‖x‖ * ‖multiplier r hr y‖ :=
        norm_inner_le_norm _ _
      _ ≤ ‖v‖ * (‖multiplier (𝕜 := 𝕜) r hr‖ * ‖u‖) :=
        mul_le_mul hx ((multiplier (𝕜 := 𝕜) r hr).le_opNorm y |>.trans
          (mul_le_mul_of_nonneg_left hy (norm_nonneg _))) (norm_nonneg _) (norm_nonneg _)
      _ = _ := by ring
  exact (norm_add_le _ _).trans ((add_le_add
    (hmul c.p c.p_C1.continuousOn _ _ hv₁ hu₁)
    (hmul c.q c.q_continuous _ _ hv₀ hu₀)).trans_eq (by ring))

/-- The real part of a weighted L² quadratic form is the expected integral. -/
theorem weighted_inner_re (r : ℝ → ℝ) (hr : ContinuousOn r (Icc a b))
    (u : L2 𝕜 a b) :
    RCLike.re (inner 𝕜 u (multiplier r hr u)) = ∫ z : Domain 1,
      r (z 0) * ‖u z‖ ^ 2
      ∂(volume.restrict (spatialInterval a b : Set (Domain 1))) := by
  rw [weighted_inner_integral, ← integral_re (weighted_inner_integrable r hr u u)]
  apply integral_congr_ae
  filter_upwards with z
  rw [mul_assoc, RCLike.conj_mul]
  simp

theorem weighted_square_integrable (r : ℝ → ℝ) (hr : ContinuousOn r (Icc a b))
    (u : L2 𝕜 a b) :
    Integrable (fun z : Domain 1 => r (z 0) * ‖u z‖ ^ 2)
      (volume.restrict (spatialInterval a b : Set (Domain 1))) := by
  convert (weighted_inner_integrable r hr u u).re using 1
  funext z
  rw [mul_assoc, RCLike.conj_mul]
  simp

theorem integral_norm_sq (u : L2 𝕜 a b) :
    (∫ z : Domain 1, ‖u z‖ ^ 2
      ∂(volume.restrict (spatialInterval a b : Set (Domain 1)))) = ‖u‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := 𝕜), L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := 𝕜) u u)]
  simp only [← norm_sq_eq_re_inner]

theorem weighted_inner_lower (r : ℝ → ℝ) (hr : ContinuousOn r (Icc a b))
    (k : ℝ) (hk : ∀ t ∈ Icc a b, k ≤ r t) (u : L2 𝕜 a b) :
    k * ‖u‖ ^ 2 ≤ RCLike.re (inner 𝕜 u (multiplier r hr u)) := by
  rw [weighted_inner_re, ← integral_norm_sq u, ← integral_const_mul]
  apply integral_mono_ae ((Lp.memLp u).norm.integrable_sq.const_mul k)
    (weighted_square_integrable r hr u)
  filter_upwards [ae_restrict_mem (spatialInterval a b).isOpen.measurableSet] with z hz
  exact mul_le_mul_of_nonneg_right (hk _ (Ioo_subset_Icc_self hz)) (sq_nonneg _)

theorem form_estimates : Spec.FormEstimates := by
  intro 𝕜 _ a b c
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image c.q_continuous.norm
  let Q := max 0 M
  refine ⟨‖multiplier (𝕜 := 𝕜) c.p c.p_C1.continuousOn‖ +
    ‖multiplier (𝕜 := 𝕜) c.q c.q_continuous‖, Q,
    add_nonneg (norm_nonneg _) (norm_nonneg _), le_max_left _ _, form_bound c, ?_⟩
  intro u
  have hq : ∀ t ∈ Icc a b, -Q ≤ c.q t := by
    intro t ht
    have he : |c.q t| ≤ M := by simpa using hM (mem_image_of_mem (fun t => ‖c.q t‖) ht)
    have hMQ : M ≤ Q := le_max_right _ _
    exact (neg_le_neg (he.trans hMQ)).trans (neg_abs_le _)
  have hp := weighted_inner_lower c.p c.p_C1.continuousOn c.p₀ c.p_lower (derivativeLp u)
  have hq' := weighted_inner_lower c.q c.q_continuous (-Q) hq (baseLp u)
  simp only [form, map_add]
  nlinarith

/-- Compact tests are elements of the actual H¹₀ closure. -/
def testH10 (φ : Tests 𝕜 (spatialInterval a b)) : H10 𝕜 a b :=
  ⟨testToSobolev 1 φ, (smoothSubmodule 𝕜 1 (spatialInterval a b) 1 2).le_topologicalClosure
    (by refine ⟨φ, ?_⟩; rw [testToSobolev_underlying]; exact testToDomainLp_coe φ)⟩

theorem h10_inner_separates (f : L2 𝕜 a b)
    (h : ∀ v : H10 𝕜 a b, inner 𝕜 (baseLp v.val) f = 0) : f = 0 := by
  apply Lp.ext
  have hz := (spatialInterval a b).isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (domainLp_locallyIntegrable f) (fun g hg hgc hgs => by
      let φ : Tests 𝕜 (spatialInterval a b) :=
        ⟨fun x => (g x : 𝕜), (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp hg,
          hgc.comp_left (by simp),
          (tsupport_comp_subset (g := fun r : ℝ => (r : 𝕜)) (by simp) g).trans hgs⟩
      have he := h (testH10 φ)
      change inner 𝕜 ((testToSobolev (p := 2) 1 φ).val (zeroIndex 1 1)) f = 0 at he
      rw [testToSobolev_underlying, L2.inner_def] at he
      calc
        (∫ x, g x • f x ∂(volume.restrict (spatialInterval a b : Set (Domain 1)))) =
            ∫ x, inner 𝕜 (testToDomainLp (p := 2) φ x) (f x)
              ∂(volume.restrict (spatialInterval a b : Set (Domain 1))) := by
          apply integral_congr_ae
          filter_upwards [testToDomainLp_coe (p := 2) φ] with x hx
          rw [hx, RCLike.inner_apply]
          simp only [RCLike.real_smul_eq_coe_mul]
          change (g x : 𝕜) * f x = f x * conj (g x : 𝕜)
          simp [mul_comm]
        _ = 0 := he)
  have hz' := (ae_restrict_iff' (spatialInterval a b).isOpen.measurableSet).mpr hz
  rw [Measure.restrict_restrict (spatialInterval a b).isOpen.measurableSet, inter_self] at hz'
  filter_upwards [hz', Lp.coeFn_zero 𝕜 2 _] with x hx hxzero
  exact hx.trans hxzero.symm

theorem dirichletFormDomain_dense :
    Dense (dirichletFormDomain 𝕜 a b : Set (L2 𝕜 a b)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  apply le_antisymm _ bot_le
  intro f hf
  exact h10_inner_separates f (fun v => hf _ ⟨v.val, v.property, rfl⟩)

/-- The weak form graph, before extracting its single-valued operator. -/
def formRelation (c : Coefficients a b) : Submodule 𝕜 (L2 𝕜 a b × L2 𝕜 a b) where
  carrier := {z | ∃ w : H10 𝕜 a b, baseLp w.val = z.1 ∧
    ∀ v : H10 𝕜 a b, form c v.val w.val = inner 𝕜 (baseLp v.val) z.2}
  zero_mem' := ⟨0, rfl, by intro v; simp⟩
  add_mem' := by
    rintro ⟨u, f⟩ ⟨w, g⟩ ⟨u', hu', hf⟩ ⟨w', hw', hg⟩
    refine ⟨u' + w', ?_, ?_⟩
    · change baseLp u'.val + baseLp w'.val = u + w
      rw [hu', hw']
    · intro v
      change form c v.val (u'.val + w'.val) = inner 𝕜 _ (f + g)
      rw [form_add_right, hf, hg, inner_add_right]
  smul_mem' := by
    rintro t ⟨u, f⟩ ⟨u', hu', hf⟩
    refine ⟨t • u', ?_, ?_⟩
    · change t • baseLp u'.val = t • u
      rw [hu']
    · intro v
      change form c v.val (t • u'.val) = inner 𝕜 _ (t • f)
      rw [form_smul_right, hf, inner_smul_right]

theorem formRelation_single_valued (c : Coefficients a b)
    (z : L2 𝕜 a b × L2 𝕜 a b) (hz : z ∈ formRelation c) (hzero : z.1 = 0) : z.2 = 0 := by
  obtain ⟨w, hw, hf⟩ := hz
  have hwzero : w.val = 0 := sobolev_underlying_injective 𝕜 1 (spatialInterval a b) 1 2
    (hw.trans hzero)
  apply h10_inner_separates z.2
  intro v
  rw [← hf v, hwzero, form_zero_right]

/-- The canonical Dirichlet form operator. Its H² domain identification is a
separate obligation; the construction itself uses the full weak form graph. -/
def dirichletOperator (c : Coefficients a b) : Operator 𝕜 (L2 𝕜 a b) (L2 𝕜 a b) :=
  (formRelation c).toLinearPMap

theorem dirichletOperator_graph (c : Coefficients a b) :
    (dirichletOperator (𝕜 := 𝕜) c).graph = formRelation c :=
  Submodule.toLinearPMap_graph_eq _ (formRelation_single_valued c)

theorem dirichletOperator_formRealization (c : Coefficients a b) :
    FormRealization c (dirichletOperator (𝕜 := 𝕜) c) := by
  intro u f
  rw [dirichletOperator_graph]
  rfl

theorem formRealization_unique (c : Coefficients a b)
    {A B : Operator 𝕜 (L2 𝕜 a b) (L2 𝕜 a b)}
    (hA : FormRealization c A) (hB : FormRealization c B) : A = B := by
  apply LinearPMap.eq_of_eq_graph
  ext ⟨u, f⟩
  exact (hA u f).trans (hB u f).symm

/-- Symmetry holds on the actual weak operator domain. -/
theorem dirichletOperator_formalAdjoint (c : Coefficients a b) :
    (dirichletOperator (𝕜 := 𝕜) c).IsFormalAdjoint (dirichletOperator c) := by
  intro u v
  obtain ⟨u', hu, hfu⟩ := (dirichletOperator_formRealization c _ _).mp
    ((dirichletOperator c).mem_graph u)
  obtain ⟨v', hv, hfv⟩ := (dirichletOperator_formRealization c _ _).mp
    ((dirichletOperator c).mem_graph v)
  rw [← hu, ← hv, ← inner_conj_symm, ← hfu v', form_hermitian 𝕜 a b c, hfv u']

/-- A lower bound for the operator, without assuming H² regularity. -/
theorem dirichletOperator_bounded_below (c : Coefficients a b) :
    ∃ γ : ℝ, ∀ u : (dirichletOperator (𝕜 := 𝕜) c).domain,
      γ * ‖(u : L2 𝕜 a b)‖ ^ 2 ≤
        RCLike.re (inner 𝕜 (u : L2 𝕜 a b) (dirichletOperator c u)) := by
  obtain ⟨C, Q, _, _, _, hcoerc⟩ := form_estimates 𝕜 a b c
  refine ⟨-Q, fun u => ?_⟩
  obtain ⟨w, hw, hf⟩ := (dirichletOperator_formRealization c _ _).mp
    ((dirichletOperator c).mem_graph u)
  rw [← hw, ← hf w]
  have he := hcoerc w.val
  have hp := mul_nonneg c.p₀_pos.le (sq_nonneg ‖derivativeLp w.val‖)
  nlinarith

/-- Complex conjugation of tests; this is real-smooth for either scalar field. -/
def conjugateTest (φ : Tests 𝕜 (spatialInterval a b)) : Tests 𝕜 (spatialInterval a b) :=
  ⟨fun x => conj (φ x), (RCLike.conjCLE : 𝕜 ≃L[ℝ] 𝕜).contDiff.comp φ.contDiff,
    φ.hasCompactSupport.comp_left (by simp),
    (tsupport_comp_subset (g := conj) (by simp) φ).trans φ.tsupport_subset⟩

@[simp] theorem conjugateTest_apply (φ : Tests 𝕜 (spatialInterval a b)) (z : Domain 1) :
    conjugateTest φ z = conj (φ z) := rfl

theorem testPartial_conjugate (φ : Tests 𝕜 (spatialInterval a b)) (z : Domain 1) :
    testPartialCLM [0] (conjugateTest φ) z = conj (testPartialCLM [0] φ z) := by
  rw [testPartial_single_apply, testPartial_single_apply]
  have hf : DifferentiableAt ℝ φ z := φ.contDiff.differentiable (by simp) z
  change fderiv ℝ ((RCLike.conjCLE : 𝕜 ≃L[ℝ] 𝕜).toContinuousLinearMap ∘ φ) z
    (coordinateVector 0) = _
  rw [((RCLike.conjCLE : 𝕜 ≃L[ℝ] 𝕜).toContinuousLinearMap.hasFDerivAt.comp z
    hf.hasFDerivAt).fderiv]
  rfl

theorem testH10_base (φ : Tests 𝕜 (spatialInterval a b)) :
    baseLp (testH10 φ).val = testToDomainLp (p := 2) φ :=
  testToSobolev_underlying 1 φ

theorem testH10_derivative (φ : Tests 𝕜 (spatialInterval a b)) :
    derivativeLp (testH10 φ).val = testToDomainLp (p := 2) (testPartialCLM [0] φ) := by
  change testToDomainLp (p := 2)
    (testPartialCLM (multiIndexWord (natIndex firstIndex)).reverse φ) = _
  rw [multiIndexWord_firstIndex, List.reverse_singleton]

/-- The weak form operator already acts as the literal differential expression;
this statement does not replace the remaining H² domain theorem. -/
theorem dirichletOperator_differentialAction (c : Coefficients a b) :
    DifferentialAction c (dirichletOperator (𝕜 := 𝕜) c) := by
  intro u
  obtain ⟨w, hw, hf⟩ := (dirichletOperator_formRealization c _ _).mp
    ((dirichletOperator c).mem_graph u)
  refine ⟨w.val, hw, ?_⟩
  ext φ
  let v := testH10 (conjugateTest φ)
  have hb : baseLp v.val =ᵐ[volume.restrict (spatialInterval a b : Set (Domain 1))]
      (fun z => conj (φ z)) := by
    rw [show baseLp v.val = testToDomainLp (p := 2) (conjugateTest φ) from
      testH10_base _]
    exact testToDomainLp_coe _
  have hd : derivativeLp v.val =ᵐ[volume.restrict (spatialInterval a b : Set (Domain 1))]
      (fun z => conj (testPartialCLM [0] φ z)) := by
    rw [show derivativeLp v.val = testToDomainLp (p := 2)
      (testPartialCLM [0] (conjugateTest φ)) from testH10_derivative _]
    filter_upwards [testToDomainLp_coe (p := 2) (testPartialCLM [0] (conjugateTest φ))]
      with z hz
    exact hz.trans (testPartial_conjugate φ z)
  have hbase (g : L2 𝕜 a b) : inner 𝕜 (baseLp v.val) g = lpDistribution g φ := by
    rw [L2.inner_def, lpDistribution_apply]
    apply integral_congr_ae
    filter_upwards [hb] with z hz
    simp only [RCLike.inner_apply, hz, starRingEnd_self_apply]
    ring
  have hderiv (g : L2 𝕜 a b) : inner 𝕜 (derivativeLp v.val) g =
      lpDistribution g (testPartialCLM [0] φ) := by
    rw [L2.inner_def, lpDistribution_apply]
    apply integral_congr_ae
    filter_upwards [hd] with z hz
    simp only [RCLike.inner_apply, hz, starRingEnd_self_apply]
    ring
  have he := hf v
  rw [form, hbase, hbase, hderiv] at he
  change lpDistribution (dirichletOperator c u) φ =
    lpDistribution (multiplier c.p c.p_C1.continuousOn (derivativeLp w.val))
      (testPartialCLM [0] φ) +
    lpDistribution (multiplier c.q c.q_continuous (baseLp w.val)) φ
  exact he.symm

/-- The first regularity step: the flux pu′ belongs to the actual H¹ graph,
with weak derivative qu−Lu. No H² hypothesis is used. -/
theorem dirichletOperator_flux_regularity (c : Coefficients a b)
    (u : (dirichletOperator (𝕜 := 𝕜) c).domain) :
    ∃ (w : H1 𝕜 a b) (flux : H1 𝕜 a b),
      baseLp w = (u : L2 𝕜 a b) ∧
      baseLp flux = multiplier c.p c.p_C1.continuousOn (derivativeLp w) ∧
      derivativeLp flux = multiplier c.q c.q_continuous (baseLp w) - dirichletOperator c u := by
  obtain ⟨w, hw, ha⟩ := dirichletOperator_differentialAction c u
  let P := multiplier c.p c.p_C1.continuousOn (derivativeLp w)
  let G := multiplier c.q c.q_continuous (baseLp w) - dirichletOperator c u
  have hG : lpDistribution G = -(lpDistribution P).comp (testPartialCLM [0]) := by
    change lpDistributionLM (_ - _) = _
    rw [map_sub]
    change lpDistribution (multiplier c.q c.q_continuous (baseLp w)) -
      lpDistribution (dirichletOperator c u) = _
    rw [ha]
    abel
  exact ⟨w, ofWeakDerivative P G hG, hw,
    ofWeakDerivative_base P G hG, ofWeakDerivative_derivative P G hG⟩

/-- A compact resolvent at one point is compact at every resolvent point.
The factorization keeps the source convention (ζI−A)⁻¹. -/
theorem resolvent_compact_of_compact_at {H : Type*} [NormedAddCommGroup H]
    [NormedSpace 𝕜 H] (A : Operator 𝕜 H H) {z w : 𝕜}
    (R : ResolventInverse A z) (hR : IsCompactOperator R.inverse)
    (S : ResolventInverse A w) : IsCompactOperator S.inverse := by
  have he : S.inverse = R.inverse.comp
      (ContinuousLinearMap.id 𝕜 H + (z - w) • S.inverse) := by
    ext y
    have harg : z • S.inverse y - A ⟨S.inverse y, S.mem_domain y⟩ =
        y + (z - w) • S.inverse y := by
      calc
        z • S.inverse y - A ⟨S.inverse y, S.mem_domain y⟩ =
          (w • S.inverse y - A ⟨S.inverse y, S.mem_domain y⟩) +
            (z - w) • S.inverse y := by rw [sub_smul]; abel
        _ = _ := by rw [S.right_inverse]
    have hy := R.left_inverse ⟨S.inverse y, S.mem_domain y⟩
    rw [harg] at hy
    exact hy.symm
  rw [he]
  exact hR.comp_clm _

theorem weak_realization : Spec.WeakRealization := by
  intro 𝕜 _ a b c
  refine ⟨dirichletOperator c, dirichletOperator_formRealization c, ?_⟩
  intro A hA
  exact formRealization_unique c hA (dirichletOperator_formRealization c)

theorem weak_properties : Spec.WeakProperties := by
  intro 𝕜 _ a b c A hA
  have he : A = dirichletOperator c :=
    formRealization_unique c hA (dirichletOperator_formRealization c)
  subst A
  exact ⟨dirichletOperator_differentialAction c, dirichletOperator_formalAdjoint c,
    dirichletOperator_bounded_below c⟩

theorem flux_regularity : Spec.FluxRegularity := by
  intro 𝕜 _ a b c A hA
  have he : A = dirichletOperator c :=
    formRealization_unique c hA (dirichletOperator_formRealization c)
  subst A
  exact dirichletOperator_flux_regularity c


instance h1_completeSpace : CompleteSpace (H1 𝕜 a b) :=
  (Smoothing.derivativeGraph_isClosed (𝕜 := 𝕜) (Ω := spatialInterval a b)
    (p := 2) (m := 1)).isComplete.completeSpace_coe

instance h10_completeSpace : CompleteSpace (H10 𝕜 a b) :=
  (smoothSubmodule 𝕜 1 (spatialInterval a b) 1 2).isClosed_topologicalClosure.isComplete.completeSpace_coe

def baseCLM (𝕜 : Type) [RCLike 𝕜] (a b : ℝ) : H1 𝕜 a b →L[𝕜] L2 𝕜 a b :=
  (baseLM 𝕜 a b).mkContinuous 1 (fun u => by
    change ‖u.val (zeroIndex 1 1)‖ ≤ 1 * ‖u.val‖
    rw [one_mul]
    exact PiLp.norm_apply_le u.val (zeroIndex 1 1))

def h10BaseCLM (𝕜 : Type) [RCLike 𝕜] (a b : ℝ) : H10 𝕜 a b →L[𝕜] L2 𝕜 a b :=
  (baseCLM 𝕜 a b).comp (H10 𝕜 a b).subtypeL

@[simp] theorem h10BaseCLM_apply (u : H10 𝕜 a b) :
    h10BaseCLM 𝕜 a b u = baseLp u.val := rfl

theorem h10BaseCLM_injective : Function.Injective (h10BaseCLM 𝕜 a b) := by
  intro u v h
  apply Subtype.ext
  exact sobolev_underlying_injective 𝕜 1 (spatialInterval a b) 1 2 h

theorem spatialInterval_bounded (a b : ℝ) :
    Bornology.IsBounded (spatialInterval a b : Set (Domain 1)) := by
  have hc : IsCompact (linePoint '' Icc a b) :=
    isCompact_Icc.image (continuous_pi (fun _ => continuous_id))
  apply hc.isBounded.subset
  intro z hz
  refine ⟨z 0, Ioo_subset_Icc_self hz, ?_⟩
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  simp [linePoint, hi]

theorem h10BaseCLM_compact : IsCompactOperator (h10BaseCLM 𝕜 a b) := by
  obtain ⟨J, hJ, hcompact⟩ := Rellich.zero_same_exponent
    (𝕜 := 𝕜) (p := 2) (spatialInterval_bounded a b) (by norm_num)
  have hJ' : J = h10BaseCLM 𝕜 a b := by
    apply ContinuousLinearMap.ext
    intro u
    exact Lp.ext (hJ u)
  rw [hJ'] at hcompact
  apply (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image _).mpr
  exact ⟨Metric.ball 0 1, Metric.ball_mem_nhds 0 (by norm_num),
    hcompact (Metric.ball 0 1) Metric.isBounded_ball⟩


def formShift (c : Coefficients a b) : ℝ :=
  Classical.choose (Classical.choose_spec (form_estimates 𝕜 a b c)) + 1

theorem formShift_pos (c : Coefficients a b) : 0 < formShift (𝕜 := 𝕜) c := by
  unfold formShift
  exact add_pos_of_nonneg_of_pos
    (Classical.choose_spec (Classical.choose_spec (form_estimates 𝕜 a b c))).2.1 zero_lt_one

theorem formShift_coercive (c : Coefficients a b) (u : H1 𝕜 a b) :
    c.p₀ * ‖derivativeLp u‖ ^ 2 + ‖baseLp u‖ ^ 2 ≤
      RCLike.re (form c u u) + formShift (𝕜 := 𝕜) c * ‖baseLp u‖ ^ 2 :=
  (Classical.choose_spec (Classical.choose_spec (form_estimates 𝕜 a b c))).2.2.2 u

theorem h1_norm_eq (u : H1 𝕜 a b) : ‖u‖ = ‖baseLp u‖ + ‖derivativeLp u‖ := by
  rw [sobolev_norm_formula]
  have hi : (Finset.univ : Finset (DerivativeIndex 1 1)) = {zeroIndex 1 1, firstIndex} := by
    ext α
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact derivativeIndex_one_cases α
  have hne : zeroIndex 1 1 ≠ firstIndex := by
    intro he
    have h := congrArg (fun α : DerivativeIndex 1 1 => (α.val 0).val) he
    norm_num [zeroIndex, firstIndex] at h
  change (∑ α : DerivativeIndex 1 1, ‖u.val α‖) = _
  rw [hi, Finset.sum_pair hne]

/-- H10 with the equivalent coercive form inner product. -/
def DirichletEnergy (𝕜 : Type) [RCLike 𝕜] {a b : ℝ} (c : Coefficients a b) : Type := H10 𝕜 a b
namespace DirichletEnergy
variable (c : Coefficients a b)
instance : AddCommGroup (DirichletEnergy 𝕜 c) := inferInstanceAs (AddCommGroup (H10 𝕜 a b))
instance : Module 𝕜 (DirichletEnergy 𝕜 c) := inferInstanceAs (Module 𝕜 (H10 𝕜 a b))
def toH10 (u : DirichletEnergy 𝕜 c) : H10 𝕜 a b := u

@[instance_reducible] def energyCore : InnerProductSpace.Core 𝕜 (DirichletEnergy 𝕜 c) where
  inner v u := form c (toH10 c v).val (toH10 c u).val +
    (formShift (𝕜 := 𝕜) c : 𝕜) * inner 𝕜 (baseLp (toH10 c v).val) (baseLp (toH10 c u).val)
  conj_inner_symm v u := by
    simp only [map_add, map_mul, RCLike.conj_ofReal, inner_conj_symm, form_hermitian 𝕜 a b c]
  re_inner_nonneg u := by
    simp only [map_add, RCLike.re_ofReal_mul, ← norm_sq_eq_re_inner]
    exact (add_nonneg (mul_nonneg c.p₀_pos.le (sq_nonneg _)) (sq_nonneg _)).trans
      (formShift_coercive c _)
  add_left v w u := by
    change form c ((toH10 c v).val + (toH10 c w).val) _ +
      _ * inner 𝕜 (baseLp (toH10 c v).val + baseLp (toH10 c w).val) _ = _
    rw [form_add_left, inner_add_left, mul_add]
    ring
  smul_left v u t := by
    change form c (t • (toH10 c v).val) _ +
      _ * inner 𝕜 (t • baseLp (toH10 c v).val) _ = _
    rw [form_smul_left, inner_smul_left]
    ring
  definite u hu := by
    have he := congrArg RCLike.re hu
    simp only [map_add, RCLike.re_ofReal_mul, ← norm_sq_eq_re_inner, map_zero] at he
    have hc := formShift_coercive c (toH10 c u).val
    have hp := mul_nonneg c.p₀_pos.le (sq_nonneg ‖derivativeLp (toH10 c u).val‖)
    have hb : baseLp (toH10 c u).val = 0 := by
      have hn : ‖baseLp (toH10 c u).val‖ = 0 := by nlinarith [sq_nonneg ‖baseLp (toH10 c u).val‖]
      exact norm_eq_zero.mp hn
    apply Subtype.ext
    exact sobolev_underlying_injective 𝕜 1 (spatialInterval a b) 1 2 hb

instance : NormedAddCommGroup (DirichletEnergy 𝕜 c) :=
  letI : InnerProductSpace.Core 𝕜 (DirichletEnergy 𝕜 c) := energyCore c
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := 𝕜)
instance : InnerProductSpace 𝕜 (DirichletEnergy 𝕜 c) :=
  InnerProductSpace.ofCore { energyCore c with }

theorem norm_sq (u : DirichletEnergy 𝕜 c) :
    ‖u‖ ^ 2 = RCLike.re (form c (toH10 c u).val (toH10 c u).val) +
      formShift (𝕜 := 𝕜) c * ‖baseLp (toH10 c u).val‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := 𝕜)]
  change RCLike.re (form c (toH10 c u).val (toH10 c u).val +
    (formShift (𝕜 := 𝕜) c : 𝕜) * inner 𝕜 (baseLp (toH10 c u).val) (baseLp (toH10 c u).val)) = _
  rw [map_add, RCLike.re_ofReal_mul, ← norm_sq_eq_re_inner]

theorem base_bound (u : DirichletEnergy 𝕜 c) : ‖baseLp (toH10 c u).val‖ ≤ ‖u‖ := by
  have he := formShift_coercive c (toH10 c u).val
  rw [← norm_sq c u] at he
  have hp := mul_nonneg c.p₀_pos.le (sq_nonneg ‖derivativeLp (toH10 c u).val‖)
  nlinarith [norm_nonneg u, norm_nonneg (baseLp (toH10 c u).val)]

theorem derivative_bound (u : DirichletEnergy 𝕜 c) :
    ‖derivativeLp (toH10 c u).val‖ ≤ (1 / Real.sqrt c.p₀) * ‖u‖ := by
  have he := formShift_coercive c (toH10 c u).val
  rw [← norm_sq c u] at he
  have hs := Real.sqrt_pos.mpr c.p₀_pos
  have hsq := Real.sq_sqrt c.p₀_pos.le
  rw [one_div_mul_eq_div]
  apply (le_div_iff₀ hs).mpr
  nlinarith [sq_nonneg ‖baseLp (toH10 c u).val‖, norm_nonneg u, norm_nonneg (derivativeLp (toH10 c u).val)]

theorem toH10_bound (u : DirichletEnergy 𝕜 c) :
    ‖toH10 c u‖ ≤ (1 + 1 / Real.sqrt c.p₀) * ‖u‖ := by
  change ‖(toH10 c u).val‖ ≤ _
  rw [h1_norm_eq]
  have hb := base_bound c u
  have hd := derivative_bound c u
  nlinarith

theorem fromH10_bound (u : H10 𝕜 a b) :
    ‖(show DirichletEnergy 𝕜 c from u)‖ ≤
      (‖multiplier (𝕜 := 𝕜) c.p c.p_C1.continuousOn‖ +
        ‖multiplier (𝕜 := 𝕜) c.q c.q_continuous‖ + formShift (𝕜 := 𝕜) c + 1) * ‖u‖ := by
  let C := ‖multiplier (𝕜 := 𝕜) c.p c.p_C1.continuousOn‖ +
    ‖multiplier (𝕜 := 𝕜) c.q c.q_continuous‖
  have hC : 0 ≤ C := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hσ := (formShift_pos (𝕜 := 𝕜) c).le
  have hb : ‖baseLp u.val‖ ≤ ‖u‖ := by
    change ‖u.val.val (zeroIndex 1 1)‖ ≤ ‖u.val.val‖
    exact PiLp.norm_apply_le u.val.val _
  have hb2 : ‖baseLp u.val‖ ^ 2 ≤ ‖u‖ ^ 2 := by nlinarith [norm_nonneg (baseLp u.val), norm_nonneg u]
  have hr := (RCLike.re_le_norm (form c u.val u.val)).trans (form_bound c u.val u.val)
  have he : ‖(show DirichletEnergy 𝕜 c from u)‖ ^ 2 ≤
      (C + formShift (𝕜 := 𝕜) c) * ‖u‖ ^ 2 := by
    rw [norm_sq]
    change RCLike.re (form c u.val u.val) + formShift (𝕜 := 𝕜) c * ‖baseLp u.val‖ ^ 2 ≤ _
    have h := mul_le_mul_of_nonneg_left hb2 hσ
    change RCLike.re (form c u.val u.val) ≤ C * ‖u‖ * ‖u‖ at hr
    nlinarith
  have hK : C + formShift (𝕜 := 𝕜) c ≤ (C + formShift (𝕜 := 𝕜) c + 1) ^ 2 := by
    nlinarith [sq_nonneg (C + formShift (𝕜 := 𝕜) c)]
  have he' := he.trans (mul_le_mul_of_nonneg_right hK (sq_nonneg ‖u‖))
  have hk : 0 ≤ (C + formShift (𝕜 := 𝕜) c + 1) * ‖u‖ :=
    mul_nonneg (by linarith) (norm_nonneg _)
  change ‖(show DirichletEnergy 𝕜 c from u)‖ ≤ (C + formShift (𝕜 := 𝕜) c + 1) * ‖u‖
  nlinarith [norm_nonneg (show DirichletEnergy 𝕜 c from u)]

def toH10CLM : DirichletEnergy 𝕜 c →L[𝕜] H10 𝕜 a b :=
  LinearMap.mkContinuous
    { toFun := toH10 c
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } _ (toH10_bound c)

def fromH10CLM : H10 𝕜 a b →L[𝕜] DirichletEnergy 𝕜 c :=
  LinearMap.mkContinuous
    { toFun := fun u => u
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } _ (fromH10_bound c)

instance : CompleteSpace (DirichletEnergy 𝕜 c) := by
  let e : H10 𝕜 a b ≃ᵤ DirichletEnergy 𝕜 c :=
    { toEquiv :=
        { toFun := fromH10CLM c
          invFun := toH10CLM c
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      uniformContinuous_toFun := (fromH10CLM c).uniformContinuous
      uniformContinuous_invFun := (toH10CLM c).uniformContinuous }
  exact e.completeSpace_iff.mp h10_completeSpace

/-- Bounded inclusion from the coercive form Hilbert space. -/
def inclusion : DirichletEnergy 𝕜 c →L[𝕜] L2 𝕜 a b :=
  LinearMap.mkContinuous
    { toFun := fun u => baseLp (toH10 c u).val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun u => by
      change ‖baseLp (toH10 c u).val‖ ≤ 1 * ‖u‖
      simpa only [one_mul] using base_bound c u)

theorem inner_def (v u : DirichletEnergy 𝕜 c) :
    inner 𝕜 v u = form c (toH10 c v).val (toH10 c u).val +
      (formShift (𝕜 := 𝕜) c : 𝕜) *
        inner 𝕜 (baseLp (toH10 c v).val) (baseLp (toH10 c u).val) := rfl

theorem shifted_solution (f : L2 𝕜 a b) :
    ∀ v : H10 𝕜 a b,
      form c v.val (toH10 c ((inclusion c).adjoint f)).val +
        (formShift (𝕜 := 𝕜) c : 𝕜) *
          inner 𝕜 (baseLp v.val) (baseLp (toH10 c ((inclusion c).adjoint f)).val) =
        inner 𝕜 (baseLp v.val) f := by
  intro v
  have he := (inclusion c).adjoint_inner_right (show DirichletEnergy 𝕜 c from v) f
  rw [inner_def] at he
  exact he

end DirichletEnergy

section RealShift
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
theorem dense_of_real_shift_surjective (A : Operator 𝕜 H H) (γ σ : ℝ)
    (hpos : 0 < γ + σ)
    (hlower : ∀ u : A.domain, γ * ‖(u : H)‖ ^ 2 ≤
      RCLike.re (inner 𝕜 (u : H) (A u)))
    (hsurj : ∀ f : H, ∃ u : A.domain, A u + (σ : 𝕜) • (u : H) = f) :
    Dense (A.domain : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  apply le_antisymm _ bot_le
  intro f hf
  obtain ⟨u, hu⟩ := hsurj f
  have ho : inner 𝕜 (u : H) f = 0 := hf u u.property
  rw [← hu, inner_add_right, inner_smul_right] at ho
  have hr := congrArg RCLike.re ho
  rw [map_add, map_zero, RCLike.re_ofReal_mul, ← norm_sq_eq_re_inner] at hr
  have hp := hlower u
  have hsq : (γ + σ) * ‖(u : H)‖ ^ 2 ≤ 0 := by nlinarith
  have hsquare : ‖(u : H)‖ ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right hsq hpos
  have hn : ‖(u : H)‖ = 0 := by nlinarith [norm_nonneg (u : H)]
  have hz : u = 0 := Subtype.ext (norm_eq_zero.mp hn)
  have hfzero : f = 0 := by simpa [hz] using hu.symm
  exact hfzero

theorem selfAdjoint_of_real_shift_surjective (A : Operator 𝕜 H H) (σ : ℝ)
    (hd : Dense (A.domain : Set H))
    (hs : A.IsFormalAdjoint A)
    (hsurj : ∀ f : H, ∃ u : A.domain, A u + (σ : 𝕜) • (u : H) = f) :
    A = HilbertAdjointSpec.adjointValue A := by
  have hle : A ≤ A.adjoint := LinearPMap.IsFormalAdjoint.le_adjoint hd hs
  apply le_antisymm hle
  apply LinearPMap.le_of_le_graph
  intro p hp
  obtain ⟨y, hy, hyp⟩ := A.adjoint.mem_graph_iff.mp hp
  obtain ⟨u, hu⟩ := hsurj (A.adjoint y + (σ : 𝕜) • (y : H))
  have heq : (y : H) = (u : H) := by
    apply ext_inner_left 𝕜
    intro f
    obtain ⟨v, hv⟩ := hsurj f
    rw [← hv, inner_add_left, inner_smul_left, inner_add_left, inner_smul_left]
    rw [(LinearPMap.adjoint_isFormalAdjoint hd).symm v y, hs v u]
    simp only [RCLike.conj_ofReal]
    rw [← inner_smul_right, ← inner_smul_right, ← inner_add_right, ← inner_add_right, ← hu]
  have hvalue : A.adjoint y = A u := by
    apply add_right_cancel (b := (σ : 𝕜) • (y : H))
    rw [← hu, heq]
  exact A.mem_graph_iff.mpr ⟨u, heq.symm.trans hy, hvalue.symm.trans hyp⟩

omit [CompleteSpace H] in
theorem real_shift_injective (A : Operator 𝕜 H H) (γ σ : ℝ)
    (hpos : 0 < γ + σ)
    (hlower : ∀ u : A.domain, γ * ‖(u : H)‖ ^ 2 ≤
      RCLike.re (inner 𝕜 (u : H) (A u))) :
    Function.Injective (fun u : A.domain => A u + (σ : 𝕜) • (u : H)) := by
  suffices hz : ∀ u : A.domain, A u + (σ : 𝕜) • (u : H) = 0 → u = 0 by
    intro u v huv
    have he : A (u - v) + (σ : 𝕜) • ((u - v : A.domain) : H) = 0 := by
      rw [A.map_sub]
      change A u - A v + (σ : 𝕜) • ((u : H) - (v : H)) = 0
      rw [smul_sub]
      calc
        _ = (A u + (σ : 𝕜) • (u : H)) - (A v + (σ : 𝕜) • (v : H)) := by abel
        _ = 0 := sub_eq_zero.mpr huv
    exact sub_eq_zero.mp (hz (u - v) he)
  intro u hu
  have hr := congrArg (fun f : H => RCLike.re (inner 𝕜 (u : H) f)) hu
  simp only [inner_add_right, inner_smul_right, map_add, RCLike.re_ofReal_mul,
    ← norm_sq_eq_re_inner, inner_zero_right, map_zero] at hr
  have hp := hlower u
  have hsq : (γ + σ) * ‖(u : H)‖ ^ 2 ≤ 0 := by nlinarith
  have hsquare : ‖(u : H)‖ ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right hsq hpos
  have hn : ‖(u : H)‖ = 0 := by nlinarith [norm_nonneg (u : H)]
  exact Subtype.ext (norm_eq_zero.mp hn)

def resolventInverseOfRealShift (A : Operator 𝕜 H H) (γ σ : ℝ)
    (hpos : 0 < γ + σ)
    (hlower : ∀ u : A.domain, γ * ‖(u : H)‖ ^ 2 ≤
      RCLike.re (inner 𝕜 (u : H) (A u)))
    (T : H →L[𝕜] H) (hmem : ∀ f, T f ∈ A.domain)
    (hsolve : ∀ f, A ⟨T f, hmem f⟩ + (σ : 𝕜) • T f = f) :
    ResolventInverse A (-(σ : 𝕜)) where
  inverse := -T
  mem_domain := fun f => A.domain.neg_mem (hmem f)
  right_inverse f := by
    change -(σ : 𝕜) • (-T f) - A ⟨-T f, _⟩ = f
    have he : (⟨-T f, A.domain.neg_mem (hmem f)⟩ : A.domain) = -⟨T f, hmem f⟩ := rfl
    rw [he, A.map_neg, neg_smul, smul_neg, neg_neg, sub_neg_eq_add, add_comm]
    exact hsolve f
  left_inverse u := by
    change -T (-(σ : 𝕜) • (u : H) - A u) = (u : H)
    rw [neg_smul, sub_eq_add_neg, ← neg_add, map_neg, neg_neg]
    have he := real_shift_injective A γ σ hpos hlower
      (hsolve ((σ : 𝕜) • (u : H) + A u) |>.trans (add_comm _ _))
    exact congrArg Subtype.val he


end RealShift

/-- The inverse of the positively shifted operator, obtained by Riesz in the
complete form Hilbert space. -/
def shiftedSolution (c : Coefficients a b) : L2 𝕜 a b →L[𝕜] L2 𝕜 a b :=
  (DirichletEnergy.inclusion c).comp (DirichletEnergy.inclusion c).adjoint

theorem shiftedSolution_graph (c : Coefficients a b) (f : L2 𝕜 a b) :
    (shiftedSolution c f, f - (formShift (𝕜 := 𝕜) c : 𝕜) • shiftedSolution c f) ∈
      (dirichletOperator c).graph := by
  apply (dirichletOperator_formRealization c _ _).mpr
  let w := DirichletEnergy.toH10 c ((DirichletEnergy.inclusion c).adjoint f)
  refine ⟨w, rfl, fun v => ?_⟩
  rw [inner_sub_right, inner_smul_right]
  exact eq_sub_iff_add_eq.mpr (DirichletEnergy.shifted_solution c f v)

theorem shiftedSolution_mem (c : Coefficients a b) (f : L2 𝕜 a b) :
    shiftedSolution c f ∈ (dirichletOperator c).domain := by
  rw [LinearPMap.mem_domain_iff]
  exact ⟨_, shiftedSolution_graph c f⟩

theorem shiftedSolution_solve (c : Coefficients a b) (f : L2 𝕜 a b) :
    dirichletOperator c ⟨shiftedSolution c f, shiftedSolution_mem c f⟩ +
      (formShift (𝕜 := 𝕜) c : 𝕜) • shiftedSolution c f = f := by
  obtain ⟨u, hu, hAu⟩ := (dirichletOperator c).mem_graph_iff.mp (shiftedSolution_graph c f)
  have he : u = ⟨shiftedSolution c f, shiftedSolution_mem c f⟩ := Subtype.ext hu
  rw [he] at hAu
  rw [hAu, sub_add_cancel]

theorem shiftedSolution_compact (c : Coefficients a b) : IsCompactOperator (shiftedSolution (𝕜 := 𝕜) c) := by
  have he : shiftedSolution (𝕜 := 𝕜) c = (h10BaseCLM 𝕜 a b).comp
      ((DirichletEnergy.toH10CLM c).comp (DirichletEnergy.inclusion c).adjoint) := by
    ext f
    rfl
  rw [he]
  exact h10BaseCLM_compact.comp_clm _

theorem dirichletOperator_shift_lower (c : Coefficients a b) :
    ∀ u : (dirichletOperator (𝕜 := 𝕜) c).domain,
      (1 - formShift (𝕜 := 𝕜) c) * ‖(u : L2 𝕜 a b)‖ ^ 2 ≤
        RCLike.re (inner 𝕜 (u : L2 𝕜 a b) (dirichletOperator c u)) := by
  intro u
  obtain ⟨w, hw, hf⟩ := (dirichletOperator_formRealization c _ _).mp
    ((dirichletOperator c).mem_graph u)
  rw [← hw, ← hf w]
  have he := formShift_coercive c w.val
  have hp := mul_nonneg c.p₀_pos.le (sq_nonneg ‖derivativeLp w.val‖)
  nlinarith

theorem dirichletOperator_dense (c : Coefficients a b) :
    Dense ((dirichletOperator (𝕜 := 𝕜) c).domain : Set (L2 𝕜 a b)) := by
  apply dense_of_real_shift_surjective (𝕜 := 𝕜) (H := L2 𝕜 a b) (dirichletOperator (𝕜 := 𝕜) c)
    (1 - formShift (𝕜 := 𝕜) c) (formShift (𝕜 := 𝕜) c) (by ring_nf; norm_num)
    (dirichletOperator_shift_lower (𝕜 := 𝕜) c)
  intro f
  exact ⟨⟨shiftedSolution c f, shiftedSolution_mem c f⟩, shiftedSolution_solve c f⟩

theorem dirichletOperator_selfAdjoint (c : Coefficients a b) :
    dirichletOperator (𝕜 := 𝕜) c = HilbertAdjointSpec.adjointValue (dirichletOperator c) := by
  apply selfAdjoint_of_real_shift_surjective (𝕜 := 𝕜) (H := L2 𝕜 a b) (dirichletOperator (𝕜 := 𝕜) c) (formShift (𝕜 := 𝕜) c)
    (dirichletOperator_dense (𝕜 := 𝕜) c) (dirichletOperator_formalAdjoint (𝕜 := 𝕜) c)
  intro f
  exact ⟨⟨shiftedSolution c f, shiftedSolution_mem c f⟩, shiftedSolution_solve c f⟩

def dirichletResolvent (c : Coefficients a b) :
    ResolventInverse (dirichletOperator (𝕜 := 𝕜) c) (-(formShift (𝕜 := 𝕜) c : 𝕜)) :=
  resolventInverseOfRealShift (𝕜 := 𝕜) (H := L2 𝕜 a b) (dirichletOperator (𝕜 := 𝕜) c)
    (1 - formShift (𝕜 := 𝕜) c) (formShift (𝕜 := 𝕜) c) (by ring_nf; norm_num)
    (dirichletOperator_shift_lower (𝕜 := 𝕜) c) (shiftedSolution c) (shiftedSolution_mem c) (shiftedSolution_solve c)

theorem dirichletOperator_compactResolvent (c : Coefficients a b) :
    HasCompactResolvent (dirichletOperator (𝕜 := 𝕜) c) := by
  have hR : IsCompactOperator (dirichletResolvent (𝕜 := 𝕜) c).inverse := by
    change IsCompactOperator (-shiftedSolution (𝕜 := 𝕜) c)
    exact (shiftedSolution_compact (𝕜 := 𝕜) c).neg
  exact ⟨⟨_, ⟨dirichletResolvent c⟩⟩, fun ζ R =>
    resolvent_compact_of_compact_at (𝕜 := 𝕜) (H := L2 𝕜 a b)
      (dirichletOperator (𝕜 := 𝕜) c) (dirichletResolvent (𝕜 := 𝕜) c) hR R⟩




theorem h1_weak_derivative (u : H1 𝕜 a b) :
    lpDistribution (derivativeLp u) = -(lpDistribution (baseLp u)).comp (testPartialCLM [0]) := by
  have h := u.property firstIndex
  change lpDistribution (derivativeLp u) = distributionDerivative 𝕜 1 (spatialInterval a b)
    (multiIndexWord (natIndex firstIndex)) (lpDistribution (baseLp u)) at h
  simpa only [multiIndexWord_firstIndex, distributionDerivative_cons, distributionDerivative_nil] using h

theorem h2_of_derivative_h1 (u v : H1 𝕜 a b) (hv : baseLp v = derivativeLp u) :
    ∃ w : H2 𝕜 a b, w.val (zeroIndex 1 2) = baseLp u := by
  apply (sobolev_membership 𝕜 1 (spatialInterval a b) 2 2 (baseLp u)).mpr
  intro α hα
  have hb : α 0 ≤ 2 := by simpa using hα
  have hconst : α = fun _ => α 0 := by funext i; exact congrArg α (Subsingleton.elim i 0)
  rw [hconst]
  interval_cases h : α 0
  · exact ⟨baseLp u, (derivative_zero _).symm⟩
  · refine ⟨derivativeLp u, ?_⟩
    change lpDistribution _ = distributionDerivative 𝕜 1 (spatialInterval a b)
      (multiIndexWord (fun _ => 1)) (lpDistribution _)
    have hw : multiIndexWord (fun _ : Fin 1 => 1) = [0] := by
      simp [multiIndexWord, List.ofFn_succ]
    rw [hw, distributionDerivative_cons, distributionDerivative_nil]
    exact h1_weak_derivative u
  · refine ⟨derivativeLp v, ?_⟩
    change lpDistribution _ = distributionDerivative 𝕜 1 (spatialInterval a b)
      (multiIndexWord (fun _ => 2)) (lpDistribution _)
    have hw : multiIndexWord (fun _ : Fin 1 => 2) = [0,0] := by
      simp [multiIndexWord, List.ofFn_succ]
    rw [hw, distributionDerivative_cons, distributionDerivative_cons, distributionDerivative_nil,
      ← h1_weak_derivative u, ← hv]
    exact h1_weak_derivative v



theorem h2_has_h1_derivative (w : H2 𝕜 a b) :
    ∃ u v : H1 𝕜 a b, baseLp u = w.val (zeroIndex 1 2) ∧ baseLp v = derivativeLp u := by
  let α₁ : DerivativeIndex 1 2 := boundedIndex (fun _ => 1) (by simp)
  let α₂ : DerivativeIndex 1 2 := boundedIndex (fun _ => 2) (by simp)
  let f := w.val (zeroIndex 1 2)
  let g := w.val α₁
  let h := w.val α₂
  have hg : lpDistribution g = -(lpDistribution f).comp (testPartialCLM [0]) := by
    have he := w.property α₁
    change lpDistribution g = distributionDerivative 𝕜 1 (spatialInterval a b)
      (multiIndexWord (fun _ => 1)) (lpDistribution f) at he
    simpa [multiIndexWord, List.ofFn_succ, distributionDerivative_cons,
      distributionDerivative_nil] using he
  have hh : lpDistribution h = -(lpDistribution g).comp (testPartialCLM [0]) := by
    have he := w.property α₂
    change lpDistribution h = distributionDerivative 𝕜 1 (spatialInterval a b)
      (multiIndexWord (fun _ => 2)) (lpDistribution f) at he
    simpa [multiIndexWord, List.ofFn_succ, distributionDerivative_cons,
      distributionDerivative_nil, hg] using he
  refine ⟨ofWeakDerivative f g hg, ofWeakDerivative g h hh, ?_, ?_⟩
  · exact ofWeakDerivative_base _ _ _
  · rw [ofWeakDerivative_base, ofWeakDerivative_derivative]



theorem integral_eq_sub_of_ac_interval {f g : ℝ → 𝕜}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : IntervalIntegrable g volume a b)
    (hd : ∀ᵐ x ∂volume, x ∈ uIcc a b → HasDerivAt f (g x) x) :
    (∫ t in a..b, g t) = f b - f a := by
  let G := (uIcc a b).indicator g
  have hG : Integrable G volume := by
    exact (integrable_indicator_iff measurableSet_uIcc).mpr
      ((intervalIntegrable_iff' (f := g)).mp hg)
  have hdG : ∀ᵐ x ∂volume, x ∈ uIcc a b → HasDerivAt f (G x) x := by
    filter_upwards [hd] with x hx hxi
    simpa only [G, indicator_of_mem hxi] using hx hxi
  have he := integral_eq_sub_of_absolutelyContinuous_of_ae_hasDerivAt hf hG.locallyIntegrable hdG
  rw [← he]
  apply intervalIntegral.integral_congr
  intro x hx
  exact (indicator_of_mem hx g).symm

/-- AC and an actual L² density imply the original distributional derivative. -/
theorem weakDerivative_of_ac (hab : a < b) (v g : L2 𝕜 a b) {f : ℝ → 𝕜}
    (hv : Represents v f) (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt f (lineFunction g t) t) :
    lpDistribution g = -(lpDistribution v).comp (testPartialCLM [0]) := by
  ext φ
  have hmp : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) ℝ).symm
      (volume.restrict (Ioo a b))
      (volume.restrict (spatialInterval a b : Set (Domain 1))) :=
    linePoint_measurePreserving (interval a b)
  let ψ : ℝ → 𝕜 := fun t => φ (linePoint t)
  have hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ := φ.contDiff.comp (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.contDiff
  have hψa : ψ a = 0 := by
    apply image_eq_zero_of_notMem_tsupport (f := φ)
    intro ht
    exact (lt_irrefl a) (φ.tsupport_subset ht).1
  have hψb : ψ b = 0 := by
    apply image_eq_zero_of_notMem_tsupport (f := φ)
    intro ht
    exact (lt_irrefl b) (φ.tsupport_subset ht).2
  let : IsFiniteMeasure (volume.restrict (Ioo a b)) := inferInstance
  have hg : IntervalIntegrable (lineFunction g) volume a b := by
    apply intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le |>.mpr
    exact (lineFunction_memLp g).integrable (by norm_num)
  have hleft : IntervalIntegrable (fun t => ψ t * lineFunction g t) volume a b :=
    (hg.continuousOn_mul hψ.continuous.continuousOn)
  have hright : IntervalIntegrable (fun t => deriv ψ t * f t) volume a b :=
    ((hψ.continuous_deriv (by simp)).continuousOn.mul hf.continuousOn).intervalIntegrable
  have hq : AbsolutelyContinuousOnInterval (fun t => ψ t * f t) a b := by
    convert! ((hψ.of_le (by simp) : ContDiff ℝ 1 ψ).contDiffOn.absolutelyContinuousOnInterval).smul hf using 1
  have hd' : ∀ᵐ t ∂volume, t ∈ uIcc a b →
      HasDerivAt (fun t => ψ t * f t)
        (deriv ψ t * f t + ψ t * lineFunction g t) t := by
    have he : ∀ᵐ t ∂volume.restrict (Icc a b), HasDerivAt f (lineFunction g t) t := by
      rwa [← Measure.restrict_congr_set (Ioo_ae_eq_Icc : Ioo a b =ᵐ[volume] Icc a b)]
    rw [uIcc_of_le hab.le]
    apply (ae_restrict_iff' measurableSet_Icc).mp
    filter_upwards [he] with t ht
    exact (hψ.differentiable (by simp) t).hasDerivAt.mul ht
  have he := integral_eq_sub_of_ac_interval hq (hright.add hleft) hd'
  rw [intervalIntegral.integral_add hright hleft, hψa, hψb, zero_mul, zero_mul,
    sub_self] at he
  have hi : (∫ t in a..b, ψ t * lineFunction g t) =
      -(∫ t in a..b, deriv ψ t * f t) := eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using he)
  simp only [neg_apply, ContinuousLinearMap.comp_apply, lpDistribution_apply]
  have hgint : (∫ z : Domain 1, φ z * g z ∂volume.restrict (spatialInterval a b : Set (Domain 1))) =
      ∫ t in a..b, ψ t * lineFunction g t := by
    rw [← hmp.integral_comp' (fun z => φ z * g z)]
    rw [intervalIntegral.integral_of_le hab.le, setIntegral_congr_set Ioo_ae_eq_Ioc]
    rfl
  have hvint : (∫ z : Domain 1, testPartialCLM [0] φ z * v z
      ∂volume.restrict (spatialInterval a b : Set (Domain 1))) =
      ∫ t in a..b, deriv ψ t * f t := by
    calc
      _ = ∫ z : Domain 1, testPartialCLM [0] φ z * f (z 0)
          ∂volume.restrict (spatialInterval a b : Set (Domain 1)) := by
        apply integral_congr_ae
        filter_upwards [hv] with z hz
        rw [hz]
      _ = _ := by
        rw [← hmp.integral_comp'
          (fun z => testPartialCLM [0] φ z * f (z 0))]
        rw [intervalIntegral.integral_of_le hab.le, setIntegral_congr_set Ioo_ae_eq_Ioc]
        congr 1
        funext t
        rw [test_line_deriv]
        rfl
  rw [hgint, hvint]
  exact hi

/-- C¹ multiplication preserves the actual distributional H¹ graph. -/
theorem h1_multiplier_from_ac (hab : a < b) (r s : ℝ → ℝ)
    (hr : ContDiffOn ℝ 1 r (Icc a b)) (hs : ContinuousOn s (Icc a b))
    (hrs : ∀ t ∈ Ioo a b, HasDerivAt r (s t) t)
    (u : H1 𝕜 a b) (f : ℝ → 𝕜) (huf : Represents (baseLp u) f)
    (hfac : AbsolutelyContinuousOnInterval f a b)
    (hfd : ∀ᵐ t ∂volume.restrict (Ioo a b),
      HasDerivAt f (lineFunction (derivativeLp u) t) t) :
    ∃ v : H1 𝕜 a b,
      baseLp v = multiplier r hr.continuousOn (baseLp u) ∧
      derivativeLp v = multiplier s hs (baseLp u) +
        multiplier r hr.continuousOn (derivativeLp u) := by
  let V := multiplier r hr.continuousOn (baseLp u)
  let G := multiplier s hs (baseLp u) + multiplier r hr.continuousOn (derivativeLp u)
  have hV : Represents V (fun t => (r t : 𝕜) * f t) := by
    filter_upwards [multiplier_coe r hr.continuousOn (baseLp u), huf] with z hz hzf
    exact hz.trans (by rw [hzf])
  have hRac : AbsolutelyContinuousOnInterval (fun t => (r t : 𝕜)) a b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le hab.le]
    exact (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp_contDiffOn hr
  have hVac : AbsolutelyContinuousOnInterval (fun t => (r t : 𝕜) * f t) a b := by
    convert! hRac.smul hfac using 1
  have hG : ∀ᵐ t ∂volume.restrict (Ioo a b), lineFunction G t =
      (s t : 𝕜) * f t + (r t : 𝕜) * lineFunction (derivativeLp u) t := by
    have hGD : ∀ᵐ z ∂volume.restrict (spatialInterval a b : Set (Domain 1)),
        G z = (s (z 0) : 𝕜) * f (z 0) + (r (z 0) : 𝕜) * derivativeLp u z := by
      filter_upwards [Lp.coeFn_add (multiplier s hs (baseLp u))
        (multiplier r hr.continuousOn (derivativeLp u)),
        multiplier_coe s hs (baseLp u), multiplier_coe r hr.continuousOn (derivativeLp u),
        huf] with z hz hs' hr' hzf
      rw [show G z = _ from hz, Pi.add_apply, hs', hr', hzf]
    exact (linePoint_measurePreserving (interval a b)).quasiMeasurePreserving.ae hGD
  have hVd : ∀ᵐ t ∂volume.restrict (Ioo a b),
      HasDerivAt (fun t => (r t : 𝕜) * f t) (lineFunction G t) t := by
    filter_upwards [hfd, hG, ae_restrict_mem measurableSet_Ioo] with t ht hgt hti
    rw [hgt]
    have hrt : HasDerivAt (fun t => (r t : 𝕜)) (s t : 𝕜) t := by
      exact (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).hasFDerivAt.comp_hasDerivAt t (hrs t hti)
    exact hrt.mul ht
  have hweak := weakDerivative_of_ac hab V G hV hVac hVd
  exact ⟨ofWeakDerivative V G hweak, ofWeakDerivative_base _ _ _,
    ofWeakDerivative_derivative _ _ _⟩




theorem Coefficients.p_ne_zero (c : Coefficients a b) (x : ℝ) (hx : x ∈ Icc a b) :
    c.p x ≠ 0 := ne_of_gt (c.p₀_pos.trans_le (c.p_lower x hx))

theorem Coefficients.p_inv_C1 (c : Coefficients a b) :
    ContDiffOn ℝ 1 (fun x => (c.p x)⁻¹) (Icc a b) :=
  c.p_C1.inv c.p_ne_zero

theorem multiplier_p_inv_cancel (c : Coefficients a b) (v : L2 𝕜 a b) :
    multiplier (fun x => (c.p x)⁻¹) c.p_inv_C1.continuousOn
      (multiplier c.p c.p_C1.continuousOn v) = v := by
  apply Lp.ext
  filter_upwards [multiplier_coe (𝕜 := 𝕜) (fun x => (c.p x)⁻¹)
      c.p_inv_C1.continuousOn (multiplier c.p c.p_C1.continuousOn v),
    multiplier_coe (𝕜 := 𝕜) c.p c.p_C1.continuousOn v,
    ae_restrict_mem (spatialInterval a b).isOpen.measurableSet] with z hinv hp hz
  rw [hinv, hp]
  have hpcast : (c.p (z 0) : 𝕜) ≠ 0 := by
    exact_mod_cast c.p_ne_zero (z 0) (Ioo_subset_Icc_self hz)
  rw [RCLike.ofReal_inv, inv_mul_cancel_left₀ hpcast]

theorem multiplier_p_cancel_inv (c : Coefficients a b) (v : L2 𝕜 a b) :
    multiplier c.p c.p_C1.continuousOn
      (multiplier (fun x => (c.p x)⁻¹) c.p_inv_C1.continuousOn v) = v := by
  apply Lp.ext
  filter_upwards [multiplier_coe (𝕜 := 𝕜) c.p c.p_C1.continuousOn
      (multiplier (fun x => (c.p x)⁻¹) c.p_inv_C1.continuousOn v),
    multiplier_coe (𝕜 := 𝕜) (fun x => (c.p x)⁻¹) c.p_inv_C1.continuousOn v,
    ae_restrict_mem (spatialInterval a b).isOpen.measurableSet] with z hp hinv hz
  rw [hp, hinv]
  have hpcast : (c.p (z 0) : 𝕜) ≠ 0 := by
    exact_mod_cast c.p_ne_zero (z 0) (Ioo_subset_Icc_self hz)
  rw [RCLike.ofReal_inv, mul_inv_cancel_left₀ hpcast]



theorem testH10_inner_base (φ : Tests 𝕜 (spatialInterval a b)) (g : L2 𝕜 a b) :
    inner 𝕜 (baseLp (testH10 φ).val) g = lpDistribution g (conjugateTest φ) := by
  rw [testH10_base, L2.inner_def, lpDistribution_apply]
  apply integral_congr_ae
  filter_upwards [testToDomainLp_coe (p := 2) φ] with z hz
  simp only [RCLike.inner_apply, hz, conjugateTest_apply]
  ring

theorem testH10_inner_derivative (φ : Tests 𝕜 (spatialInterval a b)) (g : L2 𝕜 a b) :
    inner 𝕜 (derivativeLp (testH10 φ).val) g =
      lpDistribution g (testPartialCLM [0] (conjugateTest φ)) := by
  rw [testH10_derivative, L2.inner_def, lpDistribution_apply]
  apply integral_congr_ae
  filter_upwards [testToDomainLp_coe (p := 2) (testPartialCLM [0] φ)] with z hz
  rw [hz, testPartial_conjugate, RCLike.inner_apply]
  ring

theorem testH10_integration_by_parts (φ : Tests 𝕜 (spatialInterval a b))
    (flux : H1 𝕜 a b) :
    inner 𝕜 (derivativeLp (testH10 φ).val) (baseLp flux) =
      -inner 𝕜 (baseLp (testH10 φ).val) (derivativeLp flux) := by
  have he := flux.property firstIndex
  change lpDistribution (derivativeLp flux) =
    distributionDerivative 𝕜 1 (spatialInterval a b)
      (multiIndexWord (natIndex firstIndex)) (lpDistribution (baseLp flux)) at he
  rw [multiIndexWord_firstIndex, distributionDerivative_cons, distributionDerivative_nil] at he
  have ht := congrArg (fun T : ScalarDistribution 𝕜 (spatialInterval a b) =>
    T (conjugateTest φ)) he
  simp only [neg_apply, ContinuousLinearMap.comp_apply] at ht
  rw [testH10_inner_base, testH10_inner_derivative]
  simpa only [neg_neg] using (congrArg Neg.neg ht).symm

theorem h10_integration_by_parts (v : H10 𝕜 a b) (flux : H1 𝕜 a b) :
    inner 𝕜 (derivativeLp v.val) (baseLp flux) =
      -inner 𝕜 (baseLp v.val) (derivativeLp flux) := by
  let S : Set (H1 𝕜 a b) := {w | inner 𝕜 (derivativeLp w) (baseLp flux) =
      -inner 𝕜 (baseLp w) (derivativeLp flux)}
  have hc : IsClosed S := by
    apply isClosed_eq
    · exact ((PiLp.continuous_apply 1 _ firstIndex).comp continuous_subtype_val).inner continuous_const
    · exact (((PiLp.continuous_apply 1 _ (zeroIndex 1 1)).comp continuous_subtype_val).inner continuous_const).neg
  have hs : (smoothSubmodule 𝕜 1 (spatialInterval a b) 1 2 : Set (H1 𝕜 a b)) ⊆ S := by
    rintro w ⟨φ, hφ⟩
    have he : w = (testH10 φ).val := by
      apply sobolev_underlying_injective 𝕜 1 (spatialInterval a b) 1 2
      apply Lp.ext
      exact hφ.trans (testToDomainLp_coe (p := 2) φ).symm
    rw [he]
    exact testH10_integration_by_parts φ flux
  exact closure_minimal hs hc v.property

theorem flux_form_identity (c : Coefficients a b) (w : H1 𝕜 a b)
    (flux : H1 𝕜 a b)
    (hflux : baseLp flux = multiplier c.p c.p_C1.continuousOn (derivativeLp w))
    (v : H10 𝕜 a b) :
    form c v.val w = inner 𝕜 (baseLp v.val)
      (multiplier c.q c.q_continuous (baseLp w) - derivativeLp flux) := by
  rw [form, ← hflux, h10_integration_by_parts, inner_sub_right]
  abel

theorem dirichletOperator_graph_of_flux (c : Coefficients a b) (w : H10 𝕜 a b)
    (flux : H1 𝕜 a b)
    (hflux : baseLp flux = multiplier c.p c.p_C1.continuousOn (derivativeLp w.val)) :
    (baseLp w.val, multiplier c.q c.q_continuous (baseLp w.val) - derivativeLp flux) ∈
      (dirichletOperator c).graph := by
  apply (dirichletOperator_formRealization c _ _).mpr
  exact ⟨w, rfl, fun v => flux_form_identity c w.val flux hflux v⟩



/-- Exact regularity from the two C¹ multipliers; no strong-domain input. -/
theorem dirichletOperator_domain_eq_of_multiplier
    (hm : ∀ (r : ℝ → ℝ) (hr : ContDiffOn ℝ 1 r (Icc a b)) (u : H1 𝕜 a b),
      ∃ v : H1 𝕜 a b, baseLp v = multiplier r hr.continuousOn (baseLp u))
    (c : Coefficients a b) (u : L2 𝕜 a b) :
    u ∈ (dirichletOperator c).domain ↔ StrongDomain u := by
  constructor
  · intro hu
    obtain ⟨w, flux, hw, hflux, _⟩ := dirichletOperator_flux_regularity c ⟨u, hu⟩
    obtain ⟨v, hv⟩ := hm (fun x => (c.p x)⁻¹) c.p_inv_C1 flux
    have hv' : baseLp v = derivativeLp w := by
      rw [hv, hflux, multiplier_p_inv_cancel]
    obtain ⟨w₂, hw₂⟩ := h2_of_derivative_h1 w v hv'
    refine ⟨⟨w₂, hw₂.trans hw⟩, ?_⟩
    obtain ⟨w₀, hw₀, _⟩ := (dirichletOperator_formRealization c _ _).mp
      ((dirichletOperator c).mem_graph ⟨u, hu⟩)
    exact ⟨w₀.val, w₀.property, hw₀⟩
  · rintro ⟨⟨w₂, hw₂⟩, w, hw₀, hwu⟩
    let w₀ : H10 𝕜 a b := ⟨w, hw₀⟩
    obtain ⟨w₁, v, hw₁, hv⟩ := h2_has_h1_derivative w₂
    have he : w₁ = w := sobolev_underlying_injective 𝕜 1 (spatialInterval a b) 1 2
      (hw₁.trans (hw₂.trans hwu.symm))
    subst w₁
    obtain ⟨flux, hflux⟩ := hm c.p c.p_C1 v
    have hf : baseLp flux = multiplier c.p c.p_C1.continuousOn (derivativeLp w₀.val) := by
      rw [hflux, hv]
    apply LinearPMap.mem_domain_of_mem_graph (y :=
      multiplier c.q c.q_continuous (baseLp w₀.val) - derivativeLp flux)
    rw [← hwu]
    exact dirichletOperator_graph_of_flux c w₀ flux hf




theorem h1_canonical_representative (u : H1 𝕜 a b) :
    ∃ f : ℝ → 𝕜, Represents (baseLp u) f ∧
      AbsolutelyContinuousOnInterval f a b ∧
      ∀ᵐ t ∂volume.restrict (Ioo a b),
        HasDerivAt f (lineFunction (derivativeLp u) t) t := by
  have hl : LocallyIntegrable (fun t => extendedLineFunction (baseLp u) t -
      canonicalPrimitive (derivativeLp u) t) volume :=
    (extendedLineFunction_locallyIntegrable (baseLp u)).sub
      (canonicalPrimitive_continuous (derivativeLp u)).locallyIntegrable
  obtain ⟨c, hc⟩ := ae_eq_const_of_integral_deriv_eq_zero isOpen_Ioo
    (convex_Ioo a b).ordConnected hl
    (fun ψ hψ hcψ hsψ => weakPrimitive_real_test_identity u ψ hψ hcψ hsψ)
  refine ⟨fun t => canonicalPrimitive (derivativeLp u) t + c, ?_, ?_, ?_⟩
  · exact (primitiveRepresentative_of_ae_eq_const (convex_Ioo a b).ordConnected u c hc).2.1
  · exact (canonicalPrimitive_absolutelyContinuous (derivativeLp u) a b).add
      ((LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval)
  · filter_upwards [canonicalPrimitive_ae_hasDerivAt (derivativeLp u)] with t ht
    exact ht.add_const c



theorem h1_multiplier (hab : a < b) (r : ℝ → ℝ)
    (hr : ContDiffOn ℝ 1 r (Icc a b)) (u : H1 𝕜 a b) :
    ∃ v : H1 𝕜 a b, baseLp v = multiplier r hr.continuousOn (baseLp u) := by
  let s := derivWithin r (Icc a b)
  have hs : ContinuousOn s (Icc a b) :=
    hr.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by norm_num)
  have hrs : ∀ t ∈ Ioo a b, HasDerivAt r (s t) t := by
    intro t ht
    exact ((hr.differentiableOn (by norm_num) t (Ioo_subset_Icc_self ht)).hasDerivWithinAt).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  obtain ⟨f, huf, hfac, hfd⟩ := h1_canonical_representative u
  obtain ⟨v, hv, _⟩ := h1_multiplier_from_ac hab r s hr hs hrs u f huf hfac hfd
  exact ⟨v, hv⟩

theorem dirichletOperator_domain_eq (c : Coefficients a b) (u : L2 𝕜 a b) :
    u ∈ (dirichletOperator c).domain ↔ StrongDomain u :=
  dirichletOperator_domain_eq_of_multiplier (h1_multiplier c.interval_nonempty) c u


/-- The full Dirichlet realization, with exact Sobolev domain, over both scalar fields. -/
theorem realization : Spec.Realization := by
  intro 𝕜 _ a b c
  refine ⟨dirichletOperator c, ?_, ?_⟩
  · exact ⟨dirichletOperator_formRealization c,
      dirichletOperator_domain_eq c,
      dirichletOperator_differentialAction c,
      dirichletOperator_dense (𝕜 := 𝕜) c,
      dirichletOperator_selfAdjoint (𝕜 := 𝕜) c,
      dirichletOperator_bounded_below c,
      dirichletOperator_compactResolvent (𝕜 := 𝕜) c⟩
  · intro A hA
    exact formRealization_unique c hA.1 (dirichletOperator_formRealization c)

end ExpandedFA.Models.SturmLiouvilleDirichlet
