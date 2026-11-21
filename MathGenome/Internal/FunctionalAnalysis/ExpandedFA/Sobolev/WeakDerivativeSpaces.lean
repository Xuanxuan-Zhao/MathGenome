import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.DistributionCalculus
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.BochnerLpCompleteness
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! Integer-order Sobolev spaces, with the paper's sum norm. The canonical
finite derivative graph retains exactly one copy of each multi-index. Its
order-zero projection is injective, so this is a space of Lp a.e. classes,
not a space of functions with an extra choice of weak derivatives. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal Distributions

namespace ExpandedFA.Sobolev
open ExpandedFA.Distributions

abbrev SobolevSpace : Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.SpaceType := Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.SpaceValue

def sobolevNorm : Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.NormType := Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.NormValue

def sobolevHilbertNorm : Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.HilbertNormType := Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.HilbertNormValue

def SobolevZero : Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.ZeroSpaceType := Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.ZeroSpaceValue

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A scalar test distribution determines its Lp a.e. class, over either scalar
field. Real-valued tests suffice by the fundamental lemma of distributions. -/
theorem lpDistribution_injective :
    Function.Injective (lpDistribution (𝕜 := 𝕜) (Ω := Ω) (p := p)) := by
  intro u v huv
  apply Lp.ext
  have hloc : LocallyIntegrableOn (fun x => u x - v x) Ω
      (volume.restrict (Ω : Set (Domain d))) :=
    (domainLp_locallyIntegrable u).sub (domainLp_locallyIntegrable v)
  have hz := Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    (fun g hg hgc hgs => by
      let φ : Tests 𝕜 Ω :=
        ⟨fun x => (g x : 𝕜), ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp hg),
          hgc.comp_left (by simp), (tsupport_comp_subset (g := fun r : ℝ => (r : 𝕜)) (by simp) g).trans hgs⟩
      have heq := congrArg (fun T : ScalarDistribution 𝕜 Ω => T φ) huv
      simp only [lpDistribution_apply] at heq
      have hu : Integrable (fun x => φ x * u x) (volume.restrict (Ω : Set (Domain d))) :=
        φ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜) (domainLp_locallyIntegrable u)
      have hv : Integrable (fun x => φ x * v x) (volume.restrict (Ω : Set (Domain d))) :=
        φ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜) (domainLp_locallyIntegrable v)
      simp only [RCLike.real_smul_eq_coe_mul]
      change (∫ x, φ x * (u x - v x) ∂(volume.restrict (Ω : Set (Domain d)))) = 0
      simp_rw [mul_sub]
      rw [integral_sub hu hv, heq, sub_self])
  have hz' := (ae_restrict_iff' Ω.isOpen.measurableSet).mpr hz
  rw [Measure.restrict_restrict Ω.isOpen.measurableSet, inter_self] at hz'
  filter_upwards [hz'] with x hx
  exact sub_eq_zero.mp hx

/-- Each coordinate bound needed to convert an ordinary multi-index. -/
def boundedIndex {m : ℕ} (α : Fin d → ℕ) (hα : (∑ i, α i) ≤ m) :
    DerivativeIndex d m :=
  ⟨fun i => ⟨α i, Nat.lt_succ_of_le ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hα)⟩,
    hα⟩

@[simp] theorem natIndex_boundedIndex {m : ℕ} (α : Fin d → ℕ)
    (hα : (∑ i, α i) ≤ m) : natIndex (boundedIndex α hα) = α := rfl

@[simp] theorem boundedIndex_natIndex {m : ℕ} (α : DerivativeIndex d m) :
    boundedIndex (natIndex α) α.property = α := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  rfl

@[simp] theorem derivative_zero (u : ScalarDistribution 𝕜 Ω) :
    Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue 𝕜 d Ω (fun _ => 0) u = u := by
  change distributionDerivative 𝕜 d Ω (multiIndexWord (fun _ => 0)) u = u
  have hw : multiIndexWord (fun _ : Fin d => 0) = [] := by
    apply List.length_eq_zero_iff.mp
    simp
  rw [hw, distributionDerivative_nil]

theorem sobolev_underlying_injective : Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.UnderlyingInjective := by
  intro 𝕜 _ d Ω m p _ u v huv
  apply Subtype.ext
  apply PiLp.ext
  intro α
  apply lpDistribution_injective
  have hu := u.property α
  have hv := v.property α
  exact hu.trans ((congrArg (Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue 𝕜 d Ω (natIndex α))
    (congrArg lpDistribution huv)).trans hv.symm)

theorem sobolev_membership : Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.Membership := by
  intro 𝕜 _ d Ω m p _ u
  constructor
  · rintro ⟨v, rfl⟩ α hα
    exact ⟨v.val (boundedIndex α hα), v.property (boundedIndex α hα)⟩
  · intro h
    choose g hg using h
    let v : DerivativeTuple 𝕜 Ω m p :=
      WithLp.toLp 1 (fun α => g (natIndex α) α.property)
    have hzero : v (zeroIndex d m) = u := by
      apply lpDistribution_injective
      exact (hg _ (zeroIndex d m).property).trans (derivative_zero _)
    refine ⟨⟨v, ?_⟩, hzero⟩
    intro α
    change lpDistribution (v α) = Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue 𝕜 d Ω (natIndex α)
      (lpDistribution (v (zeroIndex d m)))
    rw [hzero]
    exact hg _ α.property

theorem sobolev_norm_formula : Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.NormFormula := by
  intro 𝕜 _ d Ω m p _ u
  exact PiLp.norm_eq_of_L1 u.val

set_option maxHeartbeats 800000 in
theorem sobolev_hilbert_norm_equivalent : Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.HilbertNormEquivalent := by
  intro 𝕜 _ d Ω m u
  let v : PiLp 2 (fun _ : DerivativeIndex d m => DomainLp 𝕜 Ω 2) :=
    WithLp.toLp 2 (fun α => u.val α)
  have hv : ‖v‖ = Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.HilbertNormValue 𝕜 d Ω m u := PiLp.norm_eq_of_L2 v
  rw [← hv, sobolev_norm_formula]
  change ‖v‖ ≤ ∑ α, ‖v α‖ ∧ (∑ α, ‖v α‖) ≤ _ * ‖v‖
  constructor
  · have heq : v = ∑ α, PiLp.single (β := fun _ : DerivativeIndex d m => DomainLp 𝕜 Ω 2) 2 α (v α) := by
      ext α
      simp
    calc
      ‖v‖ = ‖∑ α, PiLp.single (β := fun _ : DerivativeIndex d m => DomainLp 𝕜 Ω 2) 2 α (v α)‖ := congrArg norm heq
      _ ≤ ∑ α, ‖PiLp.single (β := fun _ : DerivativeIndex d m => DomainLp 𝕜 Ω 2) 2 α (v α)‖ := norm_sum_le _ _
      _ = ∑ α, ‖v α‖ := by simp
  · calc
      (∑ α, ‖v α‖) ≤ ∑ _ : DerivativeIndex d m, ‖v‖ :=
        Finset.sum_le_sum (fun α _ => PiLp.norm_apply_le v α)
      _ = _ := by simp

theorem sobolev_zero_closure : Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.ZeroClosure := by
  intro 𝕜 _ d Ω m p _ hp
  rfl

/-- Compactly supported smooth functions have finite p-norm for every p. -/
def testToDomainLp (φ : Tests 𝕜 Ω) : DomainLp 𝕜 Ω p :=
  (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).toLp φ

@[simp] theorem testToDomainLp_coe (φ : Tests 𝕜 Ω) :
    testToDomainLp (p := p) φ =ᵐ[volume.restrict (Ω : Set (Domain d))] φ :=
  MemLp.coeFn_toLp _

/-- Full-volume regular distribution for a test function. -/
def testDistribution (φ : Tests 𝕜 Ω) : ScalarDistribution 𝕜 Ω :=
  regularDistribution volume φ

@[simp] theorem testDistribution_apply (φ ψ : Tests 𝕜 Ω) :
    testDistribution φ ψ = ∫ x, φ x * ψ x :=
  regularDistribution_apply volume φ (φ.continuous.locallyIntegrable.locallyIntegrableOn _) ψ

@[simp] theorem lpDistribution_testToDomainLp (φ : Tests 𝕜 Ω) :
    lpDistribution (testToDomainLp (p := p) φ) = testDistribution φ := by
  ext ψ
  rw [lpDistribution_apply, testDistribution_apply]
  calc
    (∫ x in (Ω : Set (Domain d)), ψ x * testToDomainLp (p := p) φ x) =
        ∫ x in (Ω : Set (Domain d)), φ x * ψ x := by
      apply integral_congr_ae
      filter_upwards [testToDomainLp_coe (p := p) φ] with x hx
      rw [hx, mul_comm]
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by simp [φ.zero_on_compl hx])

/-- Integration by parts is applied to Haar volume on the whole space; the
compact supports remove boundary terms on arbitrary open Ω. -/
theorem testDistribution_partial (i : Fin d) (φ : Tests 𝕜 Ω) :
    testDistribution (testPartialCLM [i] φ) =
      -(testDistribution φ).comp (testPartialCLM [i]) := by
  ext ψ
  simp only [testDistribution_apply, neg_apply, ContinuousLinearMap.comp_apply]
  have h₁ : Integrable (fun x => fderiv ℝ ψ x (coordinateVector i) * φ x) := by
    have h : Integrable (fun x => testPartialCLM [i] ψ x * φ x)
        (volume : Measure (Domain d)) :=
      (testPartialCLM [i] ψ).integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜)
        (φ.continuous.locallyIntegrable.locallyIntegrableOn _)
    simpa only [testPartial_single_apply] using h
  have h₂ : Integrable (fun x => ψ x * fderiv ℝ φ x (coordinateVector i)) := by
    have h : Integrable (fun x => ψ x * testPartialCLM [i] φ x)
        (volume : Measure (Domain d)) :=
      ψ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜)
        ((testPartialCLM [i] φ).continuous.locallyIntegrable.locallyIntegrableOn _)
    simpa only [testPartial_single_apply] using h
  have h₃ : Integrable (fun x => ψ x * φ x) :=
    ψ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜)
      (φ.continuous.locallyIntegrable.locallyIntegrableOn _)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h₁ h₂ h₃
    (fun x _ => ψ.contDiff.differentiable (by simp) x)
    (fun x _ => φ.contDiff.differentiable (by simp) x)
  simpa only [testPartial_single_apply, mul_comm] using h

/-- Composition follows concatenation of coordinate words. -/
theorem testPartial_append (w z : List (Fin d)) (φ : Tests 𝕜 Ω) :
    testPartialCLM (w ++ z) φ = testPartialCLM w (testPartialCLM z φ) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change TestFunction.lineDerivCLM 𝕜 (coordinateVector i)
      (testPartialCLM (w ++ z) φ) = _
    rw [ih]
    rfl

/-- Repeated integration by parts identifies each weak derivative. Reversing
the coordinate word avoids needing any separate mixed-partial commutation
lemma: the result is identified with the specified distribution derivative. -/
theorem testDistribution_derivative (w : List (Fin d)) (φ : Tests 𝕜 Ω) :
    distributionDerivative 𝕜 d Ω w (testDistribution φ) =
      testDistribution (testPartialCLM w.reverse φ) := by
  induction w generalizing φ with
  | nil => exact distributionDerivative_nil _
  | cons i w ih =>
    rw [distributionDerivative_cons, ← testDistribution_partial, ih,
      List.reverse_cons, testPartial_append]

/-- The natural compactly supported smooth inclusion, into the same derivative
space used for all p and m, including the infinity endpoint. -/
def testToSobolev (m : ℕ) (φ : Tests 𝕜 Ω) : SobolevSpace 𝕜 d Ω m p :=
  ⟨WithLp.toLp 1 (fun α => testToDomainLp (p := p)
      (testPartialCLM (multiIndexWord (natIndex α)).reverse φ)), by
    intro α
    change lpDistribution (testToDomainLp (p := p)
        (testPartialCLM (multiIndexWord (natIndex α)).reverse φ)) =
      Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue 𝕜 d Ω
        (natIndex α) (lpDistribution (testToDomainLp (p := p)
          (testPartialCLM (multiIndexWord (natIndex (zeroIndex d m))).reverse φ)))
    have hz : multiIndexWord (natIndex (zeroIndex d m)) = [] := by
      apply List.length_eq_zero_iff.mp
      simp [natIndex, zeroIndex]
    simp only [hz, List.reverse_nil, testPartialCLM, ContinuousLinearMap.id_apply,
      lpDistribution_testToDomainLp]
    exact (testDistribution_derivative _ φ).symm⟩

@[simp] theorem testToSobolev_underlying (m : ℕ) (φ : Tests 𝕜 Ω) :
    (testToSobolev (p := p) m φ).val (zeroIndex d m) = testToDomainLp (p := p) φ := by
  have hz : multiIndexWord (natIndex (zeroIndex d m)) = [] := by
    apply List.length_eq_zero_iff.mp
    simp [natIndex, zeroIndex]
  change testToDomainLp (p := p) (testPartialCLM _ φ) = _
  rw [hz]
  rfl

theorem sobolev_smooth_inclusion :
    Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.SmoothInclusion := by
  intro 𝕜 _ d Ω m p _ φ
  refine ⟨testToSobolev m φ, ?_⟩
  rw [testToSobolev_underlying]
  exact testToDomainLp_coe φ

/-- The underlying scalar Lp class. -/
abbrev underlyingLp {m : ℕ} (u : SobolevSpace 𝕜 d Ω m p) : DomainLp 𝕜 Ω p :=
  u.val (zeroIndex d m)

/-- The unique Lp representative class of the indicated distribution derivative. -/
abbrev weakDerivative {m : ℕ} (u : SobolevSpace 𝕜 d Ω m p)
    (α : DerivativeIndex d m) : DomainLp 𝕜 Ω p := u.val α

/-- Compatibility with the accepted scalar-linear distribution calculus. -/
theorem weakDerivative_distribution {m : ℕ} (u : SobolevSpace 𝕜 d Ω m p)
    (α : DerivativeIndex d m) :
    lpDistribution (weakDerivative u α) = distributionMultiIndexDerivative 𝕜 d Ω
      (natIndex α) (lpDistribution (underlyingLp u)) := u.property α

end ExpandedFA.Sobolev
