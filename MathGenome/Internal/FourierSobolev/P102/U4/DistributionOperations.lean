import MathGenome.Internal.FourierSobolev.Specs.P102.U4.DistributionOperations
import MathGenome.Internal.FourierSobolev.P102.U4.RegularDerivatives

noncomputable section
open Set TopologicalSpace Filter
open scoped ContDiff Distributions Topology
namespace P102.U4

abbrev multiplyTest : OperationsExpected.ProductType := @coefficientTestProduct

@[simp] theorem coefficientTestProduct_apply {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (a : SmoothCoefficient 𝕜 Ω) (φ : TestSpace 𝕜 Ω) (x : Space d) :
    coefficientTestProduct a φ x = a.val x * φ x := rfl

/-- A cutoff makes the coefficient globally smooth without changing multiplication
on the specified compact support. No growth hypothesis on the coefficient is used. -/
private theorem local_coefficient {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (a : SmoothCoefficient 𝕜 Ω)
    (K : Compacts (Space d)) (hK : (K : Set (Space d)) ⊆ Ω) :
    ∃ b : Space d → 𝕜, ContDiff ℝ (⊤ : ℕ∞) b ∧ EqOn b a.val K := by
  obtain ⟨χ, _, U, hKU, _, hχ⟩ := cutoff d Ω K hK
  let χk : TestSpace 𝕜 Ω := TestFunction.postcompCLM
    (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) χ
  refine ⟨coefficientTestProduct a χk, (coefficientTestProduct a χk).contDiff, ?_⟩
  intro x hx
  change a.val x * (χ x : 𝕜) = a.val x
  rw [hχ x (hKU hx)]
  simp

/-- Multiplication on tests as a continuous scalar-linear map. -/
def testMultiplier {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    (a : SmoothCoefficient 𝕜 Ω) : TestSpace 𝕜 Ω →L[𝕜] TestSpace 𝕜 Ω :=
  TestFunction.mkCLM 𝕜 (coefficientTestProduct a)
    (by intro φ ψ; ext x; simp [mul_add])
    (by intro c φ; ext x; simp [mul_left_comm])
    (by
      intro K hK
      obtain ⟨b, hb, hba⟩ := local_coefficient a K hK
      let B : FixedSupport d 𝕜 K →L[𝕜] FixedSupport d 𝕜 K :=
        ContDiffMapSupportedIn.bilinLeftCLM (ContinuousLinearMap.mul 𝕜 𝕜) hb
      apply ((stageInclusion 𝕜 hK).comp B).continuous.congr
      intro φ
      ext x
      change φ x * b x = a.val x * φ x
      by_cases hx : x ∈ K
      · rw [hba hx, mul_comm]
      · simp [φ.zero_on_compl hx])

@[simp] theorem testMultiplier_apply {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (a : SmoothCoefficient 𝕜 Ω) (φ : TestSpace 𝕜 Ω) (x : Space d) :
    testMultiplier a φ x = a.val x * φ x := rfl

theorem testProductContinuity : OperationsExpected.TestProductContinuity := by
  intro d 𝕜 _ Ω a
  exact (testMultiplier a).continuous

theorem multiplierConstruction : OperationsExpected.MultiplierConstruction := by
  intro d 𝕜 _ Ω
  exact ⟨testMultiplier, fun _ _ _ => rfl⟩

/-- The actual distribution multiplier; the topology on this CLM is the strong one. -/
def distributionMultiplier {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    (a : SmoothCoefficient 𝕜 Ω) : DistributionSpace 𝕜 Ω →L[𝕜] DistributionSpace 𝕜 Ω :=
  ContinuousLinearMap.precomp 𝕜 (testMultiplier a)

@[simp] theorem distributionMultiplier_apply {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (a : SmoothCoefficient 𝕜 Ω) (T : DistributionSpace 𝕜 Ω)
    (φ : TestSpace 𝕜 Ω) : distributionMultiplier a T φ = T (coefficientTestProduct a φ) := rfl

/-- Restriction as a strongly continuous scalar-linear map. -/
def distributionRestriction {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {V Ω : Opens (Space d)}
    (h : V ≤ Ω) : DistributionSpace 𝕜 Ω →L[𝕜] DistributionSpace 𝕜 V :=
  ContinuousLinearMap.precomp 𝕜 (zeroExtension 𝕜 h)

theorem transposeContinuity : OperationsExpected.TransposeContinuity := by
  intro d 𝕜 _ V Ω A
  constructor
  · let : TopologicalSpace (DistributionSpace 𝕜 Ω) := distributionWeakTopology 𝕜 Ω
    let : TopologicalSpace (DistributionSpace 𝕜 V) := distributionWeakTopology 𝕜 V
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro φ
    exact (continuous_apply (A φ)).comp continuous_induced_dom
  · exact (ContinuousLinearMap.precomp 𝕜 A).continuous

theorem weakConvergence : OperationsExpected.WeakConvergence := by
  intro d 𝕜 _ Ω ι p u T
  rw [distributionWeakTopology, nhds_induced, tendsto_comap_iff]
  exact tendsto_pi_nhds

theorem strongConvergence : OperationsExpected.StrongConvergence := by
  intro d 𝕜 _ Ω ι p u T
  exact UniformConvergenceCLM.tendsto_iff_tendstoUniformlyOn
    (σ := RingHom.id 𝕜) (F := 𝕜)
    {B : Set (TestSpace 𝕜 Ω) | Bornology.IsVonNBounded 𝕜 B}

theorem restrictionTransitive : OperationsExpected.RestrictionTransitive := by
  intro d 𝕜 _ W V Ω hWV hVΩ T
  ext φ
  apply congrArg T
  ext x
  simp [zeroExtension, TestFunction.monoCLM_apply, hWV, hVΩ,
    hWV.trans hVΩ]

/-- The ordinary product rule on tests, including their zero extensions. -/
theorem testMultiplier_derivative {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (M : TestMultiplierFamily 𝕜 Ω) (hM : HasMultiplierGraph M)
    (a : SmoothCoefficient 𝕜 Ω) (φ : TestSpace 𝕜 Ω) (i : Fin d) :
    testPartialWord Ω [i] (M a φ) =
      M (coefficientPartial i a) φ + M a (testPartialWord Ω [i] φ) := by
  ext x
  by_cases hx : x ∈ Ω
  · have hcoe : ⇑(M a φ) = fun y => a.val y * φ y := funext (hM a φ)
    rw [testPartialWord_coe, hcoe]
    change fderiv ℝ (fun y => a.val y * φ y) x (coordinateVector d i) = _
    rw [fderiv_fun_mul
      ((a.property.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp))
      (φ.contDiff.differentiable (by simp) x)]
    change _ = M (coefficientPartial i a) φ x + M a (testPartialWord Ω [i] φ) x
    rw [hM, hM, testPartialWord_coe]
    simp only [add_apply, smul_apply, smul_eq_mul]
    change a.val x * fderiv ℝ φ x (coordinateVector d i) +
      φ x * fderiv ℝ a.val x (coordinateVector d i) = _
    simp only [coefficientPartial, partialWord]
    ring
  · rw [(testPartialWord Ω [i] (M a φ)).zero_on_compl hx,
      (M (coefficientPartial i a) φ + M a (testPartialWord Ω [i] φ)).zero_on_compl hx]

/-- Evaluation of a first distribution derivative with its bilinear sign. -/
theorem distributionPartial_singleton_apply {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (T : DistributionSpace 𝕜 Ω) (i : Fin d) (φ : TestSpace 𝕜 Ω) :
    distributionPartial {i} T φ = -T (testPartialWord Ω [i] φ) := by
  simp [distributionPartial]

theorem multiplierProductRule : OperationsExpected.ProductRule := by
  intro d 𝕜 _ Ω M hM a T i
  ext φ
  simp only [distributionPartial_singleton_apply, transposeMultiplier,
    add_apply, ContinuousLinearMap.comp_apply]
  have h := congrArg T (testMultiplier_derivative M hM a φ i)
  rw [map_add] at h
  linear_combination h

/-- Linearity in the distribution argument is inherited from transposition. -/
theorem distributionPartial_add {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (α : MultiIndex d) (T S : DistributionSpace 𝕜 Ω) :
    distributionPartial α (T + S) = distributionPartial α T + distributionPartial α S := by
  ext φ
  simp [distributionPartial]

theorem multiplierIteratedProductRule : OperationsExpected.IteratedProductRule := by
  intro d 𝕜 _ Ω M hM l
  induction l with
  | nil =>
    intro a T
    exact derivative_zero d 𝕜 Ω _
  | cons i l ih =>
    intro a T
    have hmultiset : ((i :: l : List (Fin d)) : Multiset (Fin d)) =
        (l : Multiset (Fin d)) + {i} := by
      change i ::ₘ (l : Multiset (Fin d)) = _
      rw [add_comm, Multiset.singleton_add]
    rw [hmultiset, derivative_add d 𝕜 Ω,
      multiplierProductRule d 𝕜 Ω M hM a T i, distributionPartial_add, ih, ih]
    rfl

/-- Product rule for the constructed, canonical distribution multiplier. -/
theorem distributionMultiplier_productRule {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (a : SmoothCoefficient 𝕜 Ω) (T : DistributionSpace 𝕜 Ω)
    (i : Fin d) : distributionPartial {i} (distributionMultiplier a T) =
      distributionMultiplier (coefficientPartial i a) T +
      distributionMultiplier a (distributionPartial {i} T) :=
  multiplierProductRule d 𝕜 Ω testMultiplier (fun _ _ _ => rfl) a T i

/-- Every multi-index specializes the iterated rule; the expansion retains all
multiplicities by successively splitting each coordinate derivative. -/
theorem distributionMultiplier_iteratedProductRule {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (a : SmoothCoefficient 𝕜 Ω) (T : DistributionSpace 𝕜 Ω)
    (α : MultiIndex d) : distributionPartial α (distributionMultiplier a T) =
      leibnizExpansion testMultiplier (α.sort (· ≤ ·)) a T := by
  have h := multiplierIteratedProductRule d 𝕜 Ω testMultiplier (fun _ _ _ => rfl)
    (α.sort (· ≤ ·)) a T
  simpa only [Multiset.sort_eq, transposeMultiplier, distributionMultiplier,
    ContinuousLinearMap.precomp_apply] using h

/-- The whole multiplier result, with the family constructed rather than assumed. -/
theorem multiplicationOperations : OperationsExpected.MultiplicationOperations := by
  intro d 𝕜 _ Ω
  refine ⟨testMultiplier, (fun _ _ _ => rfl), ?_, ?_, ?_⟩
  · intro a
    exact transposeContinuity d 𝕜 Ω Ω (testMultiplier a)
  · exact multiplierProductRule d 𝕜 Ω testMultiplier (fun _ _ _ => rfl)
  · exact multiplierIteratedProductRule d 𝕜 Ω testMultiplier (fun _ _ _ => rfl)

theorem restrictionOperations : OperationsExpected.RestrictionOperations := by
  intro d 𝕜 _ V Ω h
  exact ⟨(zeroExtension 𝕜 h).continuous,
    (fun φ => (zeroExtensionProperties d 𝕜 V Ω h φ).1),
    transposeContinuity d 𝕜 V Ω (zeroExtension 𝕜 h)⟩

end P102.U4
