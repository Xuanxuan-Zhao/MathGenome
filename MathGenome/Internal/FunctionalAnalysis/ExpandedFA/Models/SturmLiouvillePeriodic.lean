import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.SturmLiouvillePeriodic
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Models.SturmLiouvilleDirichlet
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.SobolevTraceAndKernel

set_option maxHeartbeats 1000000
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace
namespace ExpandedFA.Models.SturmLiouvillePeriodic
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.OneDimensional
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces ExpandedFA.Unbounded
open SturmLiouvilleDirichlet
variable {𝕜 : Type} [RCLike 𝕜] {a b : ℝ}

/-- The closed kernel of the difference of the two bounded endpoint traces. -/
def periodicSpace (𝕜 : Type) [RCLike 𝕜] {a b : ℝ} (hab : a < b) :
    Submodule 𝕜 (H1 𝕜 a b) :=
  (((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin 2 => 𝕜) 0 - ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin 2 => 𝕜) 1) :
    (Fin 2 → 𝕜) →L[𝕜] 𝕜).comp
    (Trace.intervalTrace (𝕜 := 𝕜) (p := 2) hab)).ker

theorem mem_periodicSpace (hab : a < b) (w : H1 𝕜 a b) :
    w ∈ periodicSpace 𝕜 hab ↔
      Trace.intervalTrace hab w 0 = Trace.intervalTrace hab w 1 := by
  simp [periodicSpace, sub_eq_zero]

theorem periodicH1_iff (hab : a < b) (w : H1 𝕜 a b) :
    PeriodicH1 w ↔ w ∈ periodicSpace 𝕜 hab := by
  rw [mem_periodicSpace]
  constructor
  · rintro ⟨f, ⟨hfc, hfr⟩, hf⟩
    rw [Trace.intervalTrace_of_continuous hab w f hfc hfr 0,
      Trace.intervalTrace_of_continuous hab w f hfc hfr 1]
    simpa [Trace.endpoint] using hf
  · intro hw
    let f := Trace.intervalRepresentative w
    have hf := Trace.intervalRepresentative_spec w
    refine ⟨f, ⟨?_, hf.2.1⟩, ?_⟩
    · have hc := hf.1
      change ContinuousOn f (closure (Ioo a b)) at hc
      rwa [closure_Ioo hab.ne] at hc
    · simpa [Trace.intervalTrace, Trace.endpointValuesLM, Trace.endpointValues,
        Trace.endpoint, f] using hw

theorem h10_mem_periodicSpace (hab : a < b) (w : H10 𝕜 a b) :
    w.val ∈ periodicSpace 𝕜 hab := by
  rw [mem_periodicSpace]
  rw [Trace.intervalTrace_zero_of_zeroSpace hab (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    w.val w.property]
  rfl

instance periodic_completeSpace (hab : a < b) : CompleteSpace (periodicSpace 𝕜 hab) := by
  unfold periodicSpace
  exact (ContinuousLinearMap.isClosed_ker _).isComplete.completeSpace_coe

def periodicBaseCLM (hab : a < b) : periodicSpace 𝕜 hab →L[𝕜] L2 𝕜 a b :=
  (baseCLM 𝕜 a b).comp (periodicSpace 𝕜 hab).subtypeL

theorem periodic_inner_separates (hab : a < b) (f : L2 𝕜 a b)
    (h : ∀ v : periodicSpace 𝕜 hab, inner 𝕜 (baseLp v.val) f = 0) : f = 0 := by
  apply h10_inner_separates f
  intro v
  exact h ⟨v.val, h10_mem_periodicSpace hab v⟩

/-- The maximal weak graph on the periodic H¹ space. -/
def periodicRelation (c : Coefficients a b) : Submodule 𝕜 (L2 𝕜 a b × L2 𝕜 a b) where
  carrier := {z | ∃ w : periodicSpace 𝕜 c.interval_nonempty, baseLp w.val = z.1 ∧
    ∀ v : periodicSpace 𝕜 c.interval_nonempty,
      form c v.val w.val = inner 𝕜 (baseLp v.val) z.2}
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

theorem periodicRelation_single_valued (c : Coefficients a b)
    (z : L2 𝕜 a b × L2 𝕜 a b) (hz : z ∈ periodicRelation c) (hzero : z.1 = 0) :
    z.2 = 0 := by
  obtain ⟨w, hw, hf⟩ := hz
  have hwzero : w.val = 0 := sobolev_underlying_injective 𝕜 1 (spatialInterval a b) 1 2
    (hw.trans hzero)
  apply periodic_inner_separates c.interval_nonempty z.2
  intro v
  rw [← hf v, hwzero, form_zero_right]

def periodicOperator (c : Coefficients a b) : Operator 𝕜 (L2 𝕜 a b) (L2 𝕜 a b) :=
  (periodicRelation c).toLinearPMap

theorem periodicOperator_graph (c : Coefficients a b) :
    (periodicOperator (𝕜 := 𝕜) c).graph = periodicRelation c :=
  Submodule.toLinearPMap_graph_eq _ (periodicRelation_single_valued c)

theorem periodicOperator_weak_graph (c : Coefficients a b) (u f : L2 𝕜 a b) :
    (u, f) ∈ (periodicOperator c).graph ↔
      ∃ w : periodicSpace 𝕜 c.interval_nonempty, baseLp w.val = u ∧
        ∀ v : periodicSpace 𝕜 c.interval_nonempty,
          form c v.val w.val = inner 𝕜 (baseLp v.val) f := by
  rw [periodicOperator_graph]; rfl

theorem periodicOperator_formRealization (c : Coefficients a b) :
    FormRealization c (periodicOperator (𝕜 := 𝕜) c) := by
  intro u f
  rw [periodicOperator_weak_graph]
  constructor
  · rintro ⟨w, hw, hf⟩
    refine ⟨w.val, hw, (periodicH1_iff c.interval_nonempty _).mpr w.property, ?_⟩
    intro v hv
    exact hf ⟨v, (periodicH1_iff c.interval_nonempty _).mp hv⟩
  · rintro ⟨w, hw, hp, hf⟩
    exact ⟨⟨w, (periodicH1_iff c.interval_nonempty _).mp hp⟩, hw,
      fun v => hf v.val ((periodicH1_iff c.interval_nonempty _).mpr v.property)⟩

theorem formRealization_unique (c : Coefficients a b)
    {A B : Operator 𝕜 (L2 𝕜 a b) (L2 𝕜 a b)}
    (hA : FormRealization c A) (hB : FormRealization c B) : A = B := by
  apply LinearPMap.eq_of_eq_graph
  ext ⟨u, f⟩
  exact (hA u f).trans (hB u f).symm

theorem weak_realization : Spec.WeakRealization := by
  intro 𝕜 _ a b c
  exact ⟨periodicOperator c, periodicOperator_formRealization c,
    fun A hA => formRealization_unique c hA (periodicOperator_formRealization c)⟩

theorem periodicOperator_formalAdjoint (c : Coefficients a b) :
    (periodicOperator (𝕜 := 𝕜) c).IsFormalAdjoint (periodicOperator c) := by
  intro u v
  obtain ⟨u', hu, hfu⟩ := (periodicOperator_weak_graph c _ _).mp
    ((periodicOperator c).mem_graph u)
  obtain ⟨v', hv, hfv⟩ := (periodicOperator_weak_graph c _ _).mp
    ((periodicOperator c).mem_graph v)
  rw [← hu, ← hv, ← inner_conj_symm, ← hfu v', form_hermitian 𝕜 a b c, hfv u']

theorem periodicOperator_shift_lower (c : Coefficients a b) :
    ∀ u : (periodicOperator (𝕜 := 𝕜) c).domain,
      (1 - formShift (𝕜 := 𝕜) c) * ‖(u : L2 𝕜 a b)‖ ^ 2 ≤
        RCLike.re (inner 𝕜 (u : L2 𝕜 a b) (periodicOperator c u)) := by
  intro u
  obtain ⟨w, hw, hf⟩ := (periodicOperator_weak_graph c _ _).mp
    ((periodicOperator c).mem_graph u)
  rw [← hw, ← hf w]
  have he := formShift_coercive c w.val
  have hp := mul_nonneg c.p₀_pos.le (sq_nonneg ‖derivativeLp w.val‖)
  nlinarith

/-- Testing the maximal graph with compact tests gives its distributional action. -/
theorem periodicOperator_differentialAction (c : Coefficients a b) :
    DifferentialAction c (periodicOperator (𝕜 := 𝕜) c) := by
  intro u
  obtain ⟨w, hw, hf⟩ := (periodicOperator_weak_graph c _ _).mp
    ((periodicOperator c).mem_graph u)
  refine ⟨w.val, hw, ?_⟩
  ext φ
  let v := testH10 (conjugateTest φ)
  have hb : baseLp v.val =ᵐ[volume.restrict (spatialInterval a b : Set (Domain 1))]
      (fun z => conj (φ z)) := by
    rw [show baseLp v.val = testToDomainLp (p := 2) (conjugateTest φ) from testH10_base _]
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
  have he := hf ⟨v.val, h10_mem_periodicSpace c.interval_nonempty v⟩
  rw [form, hbase, hbase, hderiv] at he
  change lpDistribution (periodicOperator c u) φ = _
  exact he.symm

theorem periodicOperator_flux_regularity (c : Coefficients a b)
    (u : (periodicOperator (𝕜 := 𝕜) c).domain) :
    ∃ w flux : H1 𝕜 a b, baseLp w = (u : L2 𝕜 a b) ∧ PeriodicH1 w ∧
      baseLp flux = multiplier c.p c.p_C1.continuousOn (derivativeLp w) ∧
      derivativeLp flux = multiplier c.q c.q_continuous (baseLp w) - periodicOperator c u := by
  obtain ⟨w, hw, ha⟩ := periodicOperator_differentialAction c u
  obtain ⟨w₀, hw₀, hper, _⟩ := (periodicOperator_formRealization c _ _).mp
    ((periodicOperator c).mem_graph u)
  have heq : w = w₀ := sobolev_underlying_injective 𝕜 1 (spatialInterval a b) 1 2
    (hw.trans hw₀.symm)
  let P := multiplier c.p c.p_C1.continuousOn (derivativeLp w)
  let G := multiplier c.q c.q_continuous (baseLp w) - periodicOperator c u
  have hG : lpDistribution G = -(lpDistribution P).comp (testPartialCLM [0]) := by
    change lpDistributionLM (_ - _) = _
    rw [map_sub]
    change lpDistribution (multiplier c.q c.q_continuous (baseLp w)) -
      lpDistribution (periodicOperator c u) = _
    rw [ha]
    abel
  exact ⟨w, ofWeakDerivative P G hG, hw, heq ▸ hper,
    ofWeakDerivative_base P G hG, ofWeakDerivative_derivative P G hG⟩

theorem flux_regularity : Spec.FluxRegularity := by
  intro 𝕜 _ a b c A hA
  have heq := formRealization_unique c hA (periodicOperator_formRealization c)
  subst A
  exact periodicOperator_flux_regularity c

/-- Periodic H¹ with the equivalent coercive form inner product. -/
def PeriodicEnergy (𝕜 : Type) [RCLike 𝕜] {a b : ℝ} (c : Coefficients a b) : Type := periodicSpace 𝕜 c.interval_nonempty
namespace PeriodicEnergy
variable (c : Coefficients a b)
instance : AddCommGroup (PeriodicEnergy 𝕜 c) := inferInstanceAs (AddCommGroup (periodicSpace 𝕜 c.interval_nonempty))
instance : Module 𝕜 (PeriodicEnergy 𝕜 c) := inferInstanceAs (Module 𝕜 (periodicSpace 𝕜 c.interval_nonempty))
def toPeriodic (u : PeriodicEnergy 𝕜 c) : periodicSpace 𝕜 c.interval_nonempty := u

@[instance_reducible] def energyCore : InnerProductSpace.Core 𝕜 (PeriodicEnergy 𝕜 c) where
  inner v u := form c (toPeriodic c v).val (toPeriodic c u).val +
    (formShift (𝕜 := 𝕜) c : 𝕜) * inner 𝕜 (baseLp (toPeriodic c v).val) (baseLp (toPeriodic c u).val)
  conj_inner_symm v u := by
    simp only [map_add, map_mul, RCLike.conj_ofReal, inner_conj_symm, form_hermitian 𝕜 a b c]
  re_inner_nonneg u := by
    simp only [map_add, RCLike.re_ofReal_mul, ← norm_sq_eq_re_inner]
    exact (add_nonneg (mul_nonneg c.p₀_pos.le (sq_nonneg _)) (sq_nonneg _)).trans
      (formShift_coercive c _)
  add_left v w u := by
    change form c ((toPeriodic c v).val + (toPeriodic c w).val) _ +
      _ * inner 𝕜 (baseLp (toPeriodic c v).val + baseLp (toPeriodic c w).val) _ = _
    rw [form_add_left, inner_add_left, mul_add]
    ring
  smul_left v u t := by
    change form c (t • (toPeriodic c v).val) _ +
      _ * inner 𝕜 (t • baseLp (toPeriodic c v).val) _ = _
    rw [form_smul_left, inner_smul_left]
    ring
  definite u hu := by
    have he := congrArg RCLike.re hu
    simp only [map_add, RCLike.re_ofReal_mul, ← norm_sq_eq_re_inner, map_zero] at he
    have hc := formShift_coercive c (toPeriodic c u).val
    have hp := mul_nonneg c.p₀_pos.le (sq_nonneg ‖derivativeLp (toPeriodic c u).val‖)
    have hb : baseLp (toPeriodic c u).val = 0 := by
      have hn : ‖baseLp (toPeriodic c u).val‖ = 0 := by nlinarith [sq_nonneg ‖baseLp (toPeriodic c u).val‖]
      exact norm_eq_zero.mp hn
    apply Subtype.ext
    exact sobolev_underlying_injective 𝕜 1 (spatialInterval a b) 1 2 hb

instance : NormedAddCommGroup (PeriodicEnergy 𝕜 c) :=
  letI : InnerProductSpace.Core 𝕜 (PeriodicEnergy 𝕜 c) := energyCore c
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := 𝕜)
instance : InnerProductSpace 𝕜 (PeriodicEnergy 𝕜 c) :=
  InnerProductSpace.ofCore { energyCore c with }

theorem norm_sq (u : PeriodicEnergy 𝕜 c) :
    ‖u‖ ^ 2 = RCLike.re (form c (toPeriodic c u).val (toPeriodic c u).val) +
      formShift (𝕜 := 𝕜) c * ‖baseLp (toPeriodic c u).val‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := 𝕜)]
  change RCLike.re (form c (toPeriodic c u).val (toPeriodic c u).val +
    (formShift (𝕜 := 𝕜) c : 𝕜) * inner 𝕜 (baseLp (toPeriodic c u).val) (baseLp (toPeriodic c u).val)) = _
  rw [map_add, RCLike.re_ofReal_mul, ← norm_sq_eq_re_inner]

theorem base_bound (u : PeriodicEnergy 𝕜 c) : ‖baseLp (toPeriodic c u).val‖ ≤ ‖u‖ := by
  have he := formShift_coercive c (toPeriodic c u).val
  rw [← norm_sq c u] at he
  have hp := mul_nonneg c.p₀_pos.le (sq_nonneg ‖derivativeLp (toPeriodic c u).val‖)
  nlinarith [norm_nonneg u, norm_nonneg (baseLp (toPeriodic c u).val)]

theorem derivative_bound (u : PeriodicEnergy 𝕜 c) :
    ‖derivativeLp (toPeriodic c u).val‖ ≤ (1 / Real.sqrt c.p₀) * ‖u‖ := by
  have he := formShift_coercive c (toPeriodic c u).val
  rw [← norm_sq c u] at he
  have hs := Real.sqrt_pos.mpr c.p₀_pos
  have hsq := Real.sq_sqrt c.p₀_pos.le
  rw [one_div_mul_eq_div]
  apply (le_div_iff₀ hs).mpr
  nlinarith [sq_nonneg ‖baseLp (toPeriodic c u).val‖, norm_nonneg u, norm_nonneg (derivativeLp (toPeriodic c u).val)]

theorem toPeriodic_bound (u : PeriodicEnergy 𝕜 c) :
    ‖toPeriodic c u‖ ≤ (1 + 1 / Real.sqrt c.p₀) * ‖u‖ := by
  change ‖(toPeriodic c u).val‖ ≤ _
  rw [h1_norm_eq]
  have hb := base_bound c u
  have hd := derivative_bound c u
  nlinarith

theorem fromPeriodic_bound (u : periodicSpace 𝕜 c.interval_nonempty) :
    ‖(show PeriodicEnergy 𝕜 c from u)‖ ≤
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
  have he : ‖(show PeriodicEnergy 𝕜 c from u)‖ ^ 2 ≤
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
  change ‖(show PeriodicEnergy 𝕜 c from u)‖ ≤ (C + formShift (𝕜 := 𝕜) c + 1) * ‖u‖
  nlinarith [norm_nonneg (show PeriodicEnergy 𝕜 c from u)]

def toPeriodicCLM : PeriodicEnergy 𝕜 c →L[𝕜] periodicSpace 𝕜 c.interval_nonempty :=
  LinearMap.mkContinuous
    { toFun := toPeriodic c
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } _ (toPeriodic_bound c)

def fromPeriodicCLM : periodicSpace 𝕜 c.interval_nonempty →L[𝕜] PeriodicEnergy 𝕜 c :=
  LinearMap.mkContinuous
    { toFun := fun u => u
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } _ (fromPeriodic_bound c)

instance : CompleteSpace (PeriodicEnergy 𝕜 c) := by
  let e : periodicSpace 𝕜 c.interval_nonempty ≃ᵤ PeriodicEnergy 𝕜 c :=
    { toEquiv :=
        { toFun := fromPeriodicCLM c
          invFun := toPeriodicCLM c
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      uniformContinuous_toFun := (fromPeriodicCLM c).uniformContinuous
      uniformContinuous_invFun := (toPeriodicCLM c).uniformContinuous }
  exact e.completeSpace_iff.mp (periodic_completeSpace c.interval_nonempty)

/-- Bounded inclusion from the coercive form Hilbert space. -/
def inclusion : PeriodicEnergy 𝕜 c →L[𝕜] L2 𝕜 a b :=
  LinearMap.mkContinuous
    { toFun := fun u => baseLp (toPeriodic c u).val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun u => by
      change ‖baseLp (toPeriodic c u).val‖ ≤ 1 * ‖u‖
      simpa only [one_mul] using base_bound c u)

theorem inner_def (v u : PeriodicEnergy 𝕜 c) :
    inner 𝕜 v u = form c (toPeriodic c v).val (toPeriodic c u).val +
      (formShift (𝕜 := 𝕜) c : 𝕜) *
        inner 𝕜 (baseLp (toPeriodic c v).val) (baseLp (toPeriodic c u).val) := rfl

theorem shifted_solution (f : L2 𝕜 a b) :
    ∀ v : periodicSpace 𝕜 c.interval_nonempty,
      form c v.val (toPeriodic c ((inclusion c).adjoint f)).val +
        (formShift (𝕜 := 𝕜) c : 𝕜) *
          inner 𝕜 (baseLp v.val) (baseLp (toPeriodic c ((inclusion c).adjoint f)).val) =
        inner 𝕜 (baseLp v.val) f := by
  intro v
  have he := (inclusion c).adjoint_inner_right (show PeriodicEnergy 𝕜 c from v) f
  rw [inner_def] at he
  exact he

end PeriodicEnergy


/-- Compactness of the full H¹ inclusion on the interval. -/
theorem h1BaseCLM_compact (hab : a < b) : IsCompactOperator (baseCLM 𝕜 a b) := by
  obtain ⟨J, hJ, hcompact⟩ := Rellich.same_exponent 𝕜 1 (spatialInterval a b)
    (Trace.interval_isC1 hab) (spatialInterval_bounded a b) 2 (by norm_num)
  have he : J = baseCLM 𝕜 a b := by
    apply ContinuousLinearMap.ext
    intro u
    exact Lp.ext (hJ u)
  rw [he] at hcompact
  apply (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image _).mpr
  exact ⟨Metric.ball 0 1, Metric.ball_mem_nhds 0 (by norm_num),
    hcompact (Metric.ball 0 1) Metric.isBounded_ball⟩

theorem periodicBaseCLM_compact (hab : a < b) :
    IsCompactOperator (periodicBaseCLM (𝕜 := 𝕜) hab) :=
  (h1BaseCLM_compact hab).comp_clm _

def periodicShiftedSolution (c : Coefficients a b) : L2 𝕜 a b →L[𝕜] L2 𝕜 a b :=
  (PeriodicEnergy.inclusion c).comp (PeriodicEnergy.inclusion c).adjoint

theorem periodicShiftedSolution_graph (c : Coefficients a b) (f : L2 𝕜 a b) :
    (periodicShiftedSolution c f,
      f - (formShift (𝕜 := 𝕜) c : 𝕜) • periodicShiftedSolution c f) ∈
      (periodicOperator c).graph := by
  apply (periodicOperator_weak_graph c _ _).mpr
  let w := PeriodicEnergy.toPeriodic c ((PeriodicEnergy.inclusion c).adjoint f)
  refine ⟨w, rfl, fun v => ?_⟩
  rw [inner_sub_right, inner_smul_right]
  exact eq_sub_iff_add_eq.mpr (PeriodicEnergy.shifted_solution c f v)

theorem periodicShiftedSolution_mem (c : Coefficients a b) (f : L2 𝕜 a b) :
    periodicShiftedSolution c f ∈ (periodicOperator c).domain := by
  rw [LinearPMap.mem_domain_iff]
  exact ⟨_, periodicShiftedSolution_graph c f⟩

theorem periodicShiftedSolution_solve (c : Coefficients a b) (f : L2 𝕜 a b) :
    periodicOperator c ⟨periodicShiftedSolution c f, periodicShiftedSolution_mem c f⟩ +
      (formShift (𝕜 := 𝕜) c : 𝕜) • periodicShiftedSolution c f = f := by
  obtain ⟨u, hu, hAu⟩ := (periodicOperator c).mem_graph_iff.mp (periodicShiftedSolution_graph c f)
  have he : u = ⟨periodicShiftedSolution c f, periodicShiftedSolution_mem c f⟩ := Subtype.ext hu
  rw [he] at hAu
  rw [hAu, sub_add_cancel]

theorem periodicShiftedSolution_compact (c : Coefficients a b) :
    IsCompactOperator (periodicShiftedSolution (𝕜 := 𝕜) c) := by
  have he : periodicShiftedSolution (𝕜 := 𝕜) c = (periodicBaseCLM c.interval_nonempty).comp
      ((PeriodicEnergy.toPeriodicCLM c).comp (PeriodicEnergy.inclusion c).adjoint) := by
    ext f; rfl
  rw [he]
  exact (periodicBaseCLM_compact c.interval_nonempty).comp_clm _

theorem periodicOperator_dense (c : Coefficients a b) :
    Dense ((periodicOperator (𝕜 := 𝕜) c).domain : Set (L2 𝕜 a b)) := by
  apply dense_of_real_shift_surjective (𝕜 := 𝕜) (H := L2 𝕜 a b) (periodicOperator c)
    (1 - formShift (𝕜 := 𝕜) c) (formShift (𝕜 := 𝕜) c) (by ring_nf; norm_num)
    (periodicOperator_shift_lower c)
  intro f
  exact ⟨⟨periodicShiftedSolution c f, periodicShiftedSolution_mem c f⟩,
    periodicShiftedSolution_solve c f⟩

theorem periodicOperator_selfAdjoint (c : Coefficients a b) :
    periodicOperator (𝕜 := 𝕜) c = HilbertAdjointSpec.adjointValue (periodicOperator c) := by
  apply selfAdjoint_of_real_shift_surjective (𝕜 := 𝕜) (H := L2 𝕜 a b) (periodicOperator c)
    (formShift (𝕜 := 𝕜) c) (periodicOperator_dense c) (periodicOperator_formalAdjoint c)
  intro f
  exact ⟨⟨periodicShiftedSolution c f, periodicShiftedSolution_mem c f⟩,
    periodicShiftedSolution_solve c f⟩

def periodicResolvent (c : Coefficients a b) :
    ResolventInverse (periodicOperator (𝕜 := 𝕜) c) (-(formShift (𝕜 := 𝕜) c : 𝕜)) :=
  resolventInverseOfRealShift (𝕜 := 𝕜) (H := L2 𝕜 a b) (periodicOperator c)
    (1 - formShift (𝕜 := 𝕜) c) (formShift (𝕜 := 𝕜) c) (by ring_nf; norm_num)
    (periodicOperator_shift_lower c) (periodicShiftedSolution c)
    (periodicShiftedSolution_mem c) (periodicShiftedSolution_solve c)

theorem periodicOperator_compactResolvent (c : Coefficients a b) :
    HasCompactResolvent (periodicOperator (𝕜 := 𝕜) c) := by
  have hR : IsCompactOperator (periodicResolvent (𝕜 := 𝕜) c).inverse := by
    change IsCompactOperator (-periodicShiftedSolution (𝕜 := 𝕜) c)
    exact (periodicShiftedSolution_compact c).neg
  exact ⟨⟨_, ⟨periodicResolvent c⟩⟩, fun ζ R =>
    resolvent_compact_of_compact_at (𝕜 := 𝕜) (H := L2 𝕜 a b)
      (periodicOperator (𝕜 := 𝕜) c) (periodicResolvent (𝕜 := 𝕜) c) hR R⟩

/-- Constants belong to L² on this bounded interval. -/
instance spatialInterval_finiteMeasure :
    IsFiniteMeasure (volume.restrict (spatialInterval a b : Set (Domain 1))) := by
  constructor
  simpa using (spatialInterval_bounded a b).measure_lt_top (μ := volume)

def oneLp : L2 𝕜 a b := (memLp_const (p := 2) (μ := volume.restrict
  (spatialInterval a b : Set (Domain 1))) (1 : 𝕜)).toLp (fun _ => 1)

theorem oneLp_coe : (oneLp : L2 𝕜 a b) =ᵐ[volume.restrict
    (spatialInterval a b : Set (Domain 1))] (fun _ => 1) := MemLp.coeFn_toLp _

theorem oneLp_weakDerivative (hab : a < b) :
    lpDistribution (0 : L2 𝕜 a b) = -(lpDistribution (oneLp : L2 𝕜 a b)).comp
      (testPartialCLM [0]) := by
  apply weakDerivative_of_ac hab oneLp 0 (f := fun _ => 1) oneLp_coe
    (LipschitzWith.const (1 : 𝕜)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hz := (linePoint_measurePreserving (interval a b)).quasiMeasurePreserving.ae
    (Lp.coeFn_zero 𝕜 2 (volume.restrict (spatialInterval a b : Set (Domain 1))))
  filter_upwards [hz] with t ht
  change (0 : L2 𝕜 a b) (linePoint t) = 0 at ht
  change HasDerivAt (fun _ : ℝ => (1 : 𝕜)) ((0 : L2 𝕜 a b) (linePoint t)) t
  rw [ht]
  exact hasDerivAt_const t 1

def oneH1 (hab : a < b) : H1 𝕜 a b := ofWeakDerivative oneLp 0 (oneLp_weakDerivative hab)

@[simp] theorem oneH1_base (hab : a < b) : baseLp (oneH1 (𝕜 := 𝕜) hab) = oneLp :=
  ofWeakDerivative_base _ _ _
@[simp] theorem oneH1_derivative (hab : a < b) :
    derivativeLp (oneH1 (𝕜 := 𝕜) hab) = 0 := ofWeakDerivative_derivative _ _ _

theorem oneH1_trace (hab : a < b) (i : Fin 2) :
    Trace.intervalTrace hab (oneH1 (𝕜 := 𝕜) hab) i = 1 := by
  exact Trace.intervalTrace_of_continuous hab _ (fun _ => 1) continuousOn_const
    (by
      change Represents (oneLp : L2 𝕜 a b) (fun _ => 1)
      exact oneLp_coe) i

theorem oneH1_periodic (hab : a < b) : oneH1 (𝕜 := 𝕜) hab ∈ periodicSpace 𝕜 hab := by
  rw [mem_periodicSpace, oneH1_trace, oneH1_trace]

/-- The constant test pairs with the actual scalar integral of an L² class. -/
theorem inner_oneLp (hab : a < b) (g : L2 𝕜 a b) :
    inner 𝕜 (oneLp : L2 𝕜 a b) g = ∫ t in a..b, lineFunction g t := by
  rw [L2.inner_def]
  calc
    _ = ∫ z : Domain 1, g z ∂volume.restrict (spatialInterval a b : Set (Domain 1)) := by
      apply integral_congr_ae
      filter_upwards [oneLp_coe (𝕜 := 𝕜) (a := a) (b := b)] with z hz
      simp [RCLike.inner_apply, hz]
    _ = ∫ t : ℝ, lineFunction g t ∂volume.restrict (Ioo a b) := by
      have hmp : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) ℝ).symm
          (volume.restrict (Ioo a b))
          (volume.restrict (spatialInterval a b : Set (Domain 1))) :=
        linePoint_measurePreserving (interval a b)
      exact (hmp.integral_comp' g).symm
    _ = _ := by
      rw [intervalIntegral.integral_of_le hab.le, setIntegral_congr_set Ioo_ae_eq_Ioc]

/-- Fundamental theorem for the endpoint traces of the flux. -/
theorem inner_one_derivative (hab : a < b) (w : H1 𝕜 a b) :
    inner 𝕜 (oneLp : L2 𝕜 a b) (derivativeLp w) =
      Trace.intervalTrace hab w 1 - Trace.intervalTrace hab w 0 := by
  rw [inner_oneLp hab]
  have hf := Trace.intervalRepresentative_spec w
  have hcl : closure (Ioo a b) = Icc a b := closure_Ioo hab.ne
  have he := (hf.2.2.2 b (by change b ∈ closure (Ioo a b); rw [hcl]; exact ⟨hab.le, le_rfl⟩)
    a (by change a ∈ closure (Ioo a b); rw [hcl]; exact ⟨le_rfl, hab.le⟩)).2
  rw [Trace.intervalTrace_apply hab w _ hf 1, Trace.intervalTrace_apply hab w _ hf 0]
  simpa [Trace.endpoint] using he.symm

/-- Removing the common endpoint value leaves an element of the closure-defined H¹₀. -/
theorem periodic_sub_constant_mem_h10 (hab : a < b) (v : periodicSpace 𝕜 hab) :
    v.val - Trace.intervalTrace hab v.val 0 • oneH1 hab ∈ H10 𝕜 a b := by
  let w := v.val - Trace.intervalTrace hab v.val 0 • oneH1 hab
  have hw : Trace.intervalTrace hab w = 0 := by
    ext i
    simp only [w, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      oneH1_trace, mul_one, Pi.zero_apply]
    have hv := (mem_periodicSpace hab v.val).mp v.property
    fin_cases i
    · exact sub_self _
    · exact sub_eq_zero.mpr hv.symm
  obtain ⟨f, hf⟩ := representative_existence 𝕜 (interval a b) ordConnected_Ioo 2 w
  apply Trace.interval_zeroSpace_of_endpoints (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hab w f hf
  · have he := Trace.intervalTrace_apply hab w f hf 0
    simpa [Trace.endpoint, hw] using he.symm
  · have he := Trace.intervalTrace_apply hab w f hf 1
    simpa [Trace.endpoint, hw] using he.symm

/-- Integration by parts on the periodic space, proved from H¹₀ and the constant test. -/
theorem periodic_integration_by_parts (hab : a < b)
    (v : periodicSpace 𝕜 hab) (flux : H1 𝕜 a b)
    (hflux : flux ∈ periodicSpace 𝕜 hab) :
    inner 𝕜 (derivativeLp v.val) (baseLp flux) =
      -inner 𝕜 (baseLp v.val) (derivativeLp flux) := by
  have hm : inner 𝕜 (oneLp : L2 𝕜 a b) (derivativeLp flux) = 0 := by
    rw [inner_one_derivative hab, (mem_periodicSpace hab flux).mp hflux, sub_self]
  have he := h10_integration_by_parts
    ⟨_, periodic_sub_constant_mem_h10 hab v⟩ flux
  change inner 𝕜 (derivativeLp v.val -
      Trace.intervalTrace hab v.val 0 • derivativeLp (oneH1 (𝕜 := 𝕜) hab)) (baseLp flux) =
    -inner 𝕜 (baseLp v.val -
      Trace.intervalTrace hab v.val 0 • baseLp (oneH1 (𝕜 := 𝕜) hab)) (derivativeLp flux) at he
  simpa only [oneH1_derivative, oneH1_base, smul_zero, sub_zero, inner_sub_left,
    inner_smul_left, hm, mul_zero, sub_zero] using he


/-- Endpoint traces commute with multiplication by a C¹ coefficient. -/
theorem multiplier_trace (hab : a < b) (r : ℝ → ℝ)
    (hr : ContDiffOn ℝ 1 r (Icc a b)) (v w : H1 𝕜 a b)
    (hw : baseLp w = multiplier r hr.continuousOn (baseLp v)) (i : Fin 2) :
    Trace.intervalTrace hab w i =
      (r (Trace.endpoint a b i) : 𝕜) * Trace.intervalTrace hab v i := by
  let f := Trace.intervalRepresentative v
  have hf := Trace.intervalRepresentative_spec v
  have hfc : ContinuousOn f (Icc a b) := by
    have he := hf.1
    change ContinuousOn f (closure (Ioo a b)) at he
    rwa [closure_Ioo hab.ne] at he
  have hwf : Represents (baseLp w) (fun t => (r t : 𝕜) * f t) := by
    rw [hw]
    filter_upwards [multiplier_coe r hr.continuousOn (baseLp v), hf.2.1] with z hz hzf
    rw [hz, hzf]
  rw [Trace.intervalTrace_of_continuous hab w (fun t => (r t : 𝕜) * f t)
    (((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).continuous.comp_continuousOn hr.continuousOn).mul hfc)
      hwf i, Trace.intervalTrace_apply hab v f hf i]

/-- The literal endpoint/H² domain equals the periodic H¹ flux domain.
This is a regularity conclusion, using p⁻¹, rather than an input assumption. -/
theorem strongDomain_iff_flux (c : Coefficients a b) (u : L2 𝕜 a b) :
    StrongDomain c u ↔
      ∃ w flux : H1 𝕜 a b, baseLp w = u ∧ w ∈ periodicSpace 𝕜 c.interval_nonempty ∧
        baseLp flux = multiplier c.p c.p_C1.continuousOn (derivativeLp w) ∧
          flux ∈ periodicSpace 𝕜 c.interval_nonempty := by
  let hab := c.interval_nonempty
  constructor
  · rintro ⟨_, w, d, hw, hd, f, g, hf, hg, hfper, hgper⟩
    obtain ⟨flux, hflux⟩ := h1_multiplier hab c.p c.p_C1 d
    refine ⟨w, flux, hw, (periodicH1_iff hab w).mp ⟨f, hf, hfper⟩,
      hflux.trans (congrArg (multiplier c.p c.p_C1.continuousOn) hd), ?_⟩
    rw [mem_periodicSpace, multiplier_trace hab c.p c.p_C1 d flux hflux 0,
      multiplier_trace hab c.p c.p_C1 d flux hflux 1,
      Trace.intervalTrace_of_continuous hab d g hg.1 hg.2 0,
      Trace.intervalTrace_of_continuous hab d g hg.1 hg.2 1]
    simpa [Trace.endpoint] using hgper
  · rintro ⟨w, flux, hw, hwper, hflux, hfper⟩
    obtain ⟨d, hd⟩ := h1_multiplier hab (fun x => (c.p x)⁻¹) c.p_inv_C1 flux
    have hd' : baseLp d = derivativeLp w := by
      rw [hd, hflux, multiplier_p_inv_cancel]
    obtain ⟨w₂, hw₂⟩ := h2_of_derivative_h1 w d hd'
    let f := Trace.intervalRepresentative w
    let g := Trace.intervalRepresentative d
    have hf := Trace.intervalRepresentative_spec w
    have hg := Trace.intervalRepresentative_spec d
    have hfC : EndpointRepresentative w f := by
      refine ⟨?_, hf.2.1⟩
      have he := hf.1
      change ContinuousOn f (closure (Ioo a b)) at he
      rwa [closure_Ioo hab.ne] at he
    have hgC : EndpointRepresentative d g := by
      refine ⟨?_, hg.2.1⟩
      have he := hg.1
      change ContinuousOn g (closure (Ioo a b)) at he
      rwa [closure_Ioo hab.ne] at he
    refine ⟨⟨w₂, hw₂.trans hw⟩, w, d, hw, hd', f, g, hfC, hgC, ?_, ?_⟩
    · have he := (mem_periodicSpace hab w).mp hwper
      rw [Trace.intervalTrace_apply hab w f hf 0, Trace.intervalTrace_apply hab w f hf 1] at he
      simpa [Trace.endpoint] using he
    · have hbase : baseLp flux = multiplier c.p c.p_C1.continuousOn (baseLp d) := by
        rw [hd', hflux]
      have he := (mem_periodicSpace hab flux).mp hfper
      rw [multiplier_trace hab c.p c.p_C1 d flux hbase 0,
        multiplier_trace hab c.p c.p_C1 d flux hbase 1,
        Trace.intervalTrace_apply hab d g hg 0, Trace.intervalTrace_apply hab d g hg 1] at he
      simpa [Trace.endpoint] using he

/-- The constant periodic test forces equality of the two flux traces. -/
theorem periodicOperator_flux_periodic (c : Coefficients a b)
    (u : (periodicOperator (𝕜 := 𝕜) c).domain) (w flux : H1 𝕜 a b)
    (hw : baseLp w = (u : L2 𝕜 a b))
    (hd : derivativeLp flux = multiplier c.q c.q_continuous (baseLp w) - periodicOperator c u) :
    flux ∈ periodicSpace 𝕜 c.interval_nonempty := by
  obtain ⟨w₀, hw₀, hf⟩ := (periodicOperator_weak_graph c _ _).mp
    ((periodicOperator c).mem_graph u)
  have heq : w = w₀.val := sobolev_underlying_injective 𝕜 1 (spatialInterval a b) 1 2
    (hw.trans hw₀.symm)
  have he := hf ⟨oneH1 c.interval_nonempty, oneH1_periodic c.interval_nonempty⟩
  change form c (oneH1 c.interval_nonempty) w₀.val =
    inner 𝕜 (baseLp (oneH1 c.interval_nonempty)) (periodicOperator c u) at he
  rw [form, oneH1_derivative, oneH1_base, inner_zero_left, zero_add, ← heq] at he
  have hz : inner 𝕜 (oneLp : L2 𝕜 a b) (derivativeLp flux) = 0 := by
    rw [hd, inner_sub_right, he, sub_self]
  rw [inner_one_derivative c.interval_nonempty] at hz
  exact (mem_periodicSpace c.interval_nonempty flux).mpr (sub_eq_zero.mp hz).symm

theorem periodicOperator_graph_of_flux (c : Coefficients a b)
    (w flux : H1 𝕜 a b) (hw : w ∈ periodicSpace 𝕜 c.interval_nonempty)
    (hflux : baseLp flux = multiplier c.p c.p_C1.continuousOn (derivativeLp w))
    (hfper : flux ∈ periodicSpace 𝕜 c.interval_nonempty) :
    (baseLp w, multiplier c.q c.q_continuous (baseLp w) - derivativeLp flux) ∈
      (periodicOperator c).graph := by
  apply (periodicOperator_weak_graph c _ _).mpr
  refine ⟨⟨w, hw⟩, rfl, fun v => ?_⟩
  rw [form, ← hflux, periodic_integration_by_parts c.interval_nonempty v flux hfper,
    inner_sub_right]
  abel

/-- The maximal form domain has exactly the source's H² and weighted endpoint conditions. -/
theorem periodicOperator_domain_eq (c : Coefficients a b) (u : L2 𝕜 a b) :
    u ∈ (periodicOperator c).domain ↔ StrongDomain c u := by
  rw [strongDomain_iff_flux]
  constructor
  · intro hu
    obtain ⟨w, flux, hw, hp, hflux, hd⟩ := periodicOperator_flux_regularity c ⟨u, hu⟩
    exact ⟨w, flux, hw, (periodicH1_iff c.interval_nonempty _).mp hp, hflux,
      periodicOperator_flux_periodic c ⟨u, hu⟩ w flux hw hd⟩
  · rintro ⟨w, flux, hw, hp, hflux, hfper⟩
    apply LinearPMap.mem_domain_of_mem_graph (y :=
      multiplier c.q c.q_continuous (baseLp w) - derivativeLp flux)
    rw [← hw]
    exact periodicOperator_graph_of_flux c w flux hp hflux hfper

/-- Complete periodic realization, with maximal form graph and literal operator domain. -/
theorem realization : Spec.Realization := by
  intro 𝕜 _ a b c
  refine ⟨periodicOperator c, ?_, ?_⟩
  · exact ⟨periodicOperator_formRealization c, periodicOperator_domain_eq c,
      periodicOperator_differentialAction c, periodicOperator_dense c,
      periodicOperator_selfAdjoint c, ⟨1 - formShift (𝕜 := 𝕜) c,
        periodicOperator_shift_lower c⟩, periodicOperator_compactResolvent c⟩
  · intro A hA
    exact formRealization_unique c hA.1 (periodicOperator_formRealization c)

end ExpandedFA.Models.SturmLiouvillePeriodic
