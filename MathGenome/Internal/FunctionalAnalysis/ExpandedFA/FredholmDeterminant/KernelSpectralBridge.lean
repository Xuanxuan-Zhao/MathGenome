import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.KernelSpectralBridge
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.IntegralOperators.ContinuousKernelCompactness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.L2Kernel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.CompactNonzeroSpectrum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! The natural quotient map J need not be injective. We construct A by a
Bochner integral in C(Q), identify both canonical products, and transfer
resolvents explicitly. On each nonzero full generalized eigenspace, J and A
are injective in opposite directions. Compactness of AJ makes one space
finite dimensional, hence both are finite dimensional with equal dimensions.
-/
noncomputable section
open MeasureTheory
universe u v w
namespace ExpandedFA.FredholmDeterminant.KernelSpectralBridge

section Representation
variable {Q : Type u} [MetricSpace Q] [CompactSpace Q]
  [MeasurableSpace Q] [BorelSpace Q] (μ : Measure Q) [IsFiniteMeasure μ]
  (k : C(Q × Q, ℂ))

abbrev sectionMap := ExpandedFA.PartV.ContinuousKernel.Spec.kernelSection k

omit [MeasurableSpace Q] [BorelSpace Q] in
lemma section_bound (y : Q) : ‖sectionMap k y‖ ≤ ‖k‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg k)).mpr
  intro x
  exact k.norm_coe_le_norm (x,y)

lemma image_integrable (f : Lp ℂ 2 μ) :
    Integrable (fun y => f y • sectionMap k y) μ := by
  apply ((Lp.memLp f).integrable (by norm_num)).smul_bdd ‖k‖
    (sectionMap k).continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall (section_bound k)

def image (f : Lp ℂ 2 μ) : C(Q, ℂ) := ∫ y, f y • sectionMap k y ∂μ

lemma image_apply (f : Lp ℂ 2 μ) (x : Q) :
    image μ k f x = ∫ y, k (x,y) * f y ∂μ := by
  rw [image, ContinuousMap.integral_apply (image_integrable μ k f)]
  simp [sectionMap, ExpandedFA.PartV.ContinuousKernel.Spec.kernelSection, mul_comm]

lemma image_bound (f : Lp ℂ 2 μ) :
    ‖image μ k f‖ ≤ (‖ContinuousMap.toLp (E := ℂ) 2 μ ℂ‖ * ‖k‖) * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  rw [image_apply]
  let s : C(Q, ℂ) := k.curry x
  have hs : ‖s‖ ≤ ‖k‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg k)).mpr
    intro y
    exact k.norm_coe_le_norm (x,y)
  have he : ‖(s.memLp (p := 2) μ ℂ).toLp s‖ ≤
      ‖ContinuousMap.toLp (E := ℂ) 2 μ ℂ‖ * ‖k‖ := by
    have ht : (s.memLp (p := 2) μ ℂ).toLp s = ContinuousMap.toLp 2 μ ℂ s := by
      apply Lp.ext
      exact (MemLp.coeFn_toLp _).trans (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ s).symm
    rw [ht]
    exact ((ContinuousMap.toLp 2 μ ℂ).le_opNorm s).trans
      (mul_le_mul_of_nonneg_left hs (norm_nonneg _))
  change ‖∫ y, s y * f y ∂μ‖ ≤ _
  rw [← ExpandedFA.FunctionSpaces.lp_pairing_on_representatives μ 2 2
    s f (s.memLp (p := 2) μ ℂ) (Lp.memLp f)]
  rw [Lp.toLp_coeFn]
  have h := ExpandedFA.FunctionSpaces.lp_pairing_apply_bound μ 2 2
    ((Lp.memLp f).toLp f) ((s.memLp (p := 2) μ ℂ).toLp s)
  rw [Lp.toLp_coeFn] at h
  exact h.trans (by
    calc
      ‖f‖ * ‖(s.memLp (p := 2) μ ℂ).toLp s‖ ≤
          ‖f‖ * (‖ContinuousMap.toLp (E := ℂ) 2 μ ℂ‖ * ‖k‖) :=
        mul_le_mul_of_nonneg_left he (norm_nonneg f)
      _ = _ := mul_comm _ _)

def imageLinear : Lp ℂ 2 μ →ₗ[ℂ] C(Q, ℂ) where
  toFun := image μ k
  map_add' f g := by
    change (∫ y, (f+g) y • sectionMap k y ∂μ) = _
    rw [show (∫ y, (f+g) y • sectionMap k y ∂μ) =
      ∫ y, (f y • sectionMap k y + g y • sectionMap k y) ∂μ by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add f g] with y hy
        rw [hy]
        exact add_smul _ _ _]
    exact integral_add (image_integrable μ k f) (image_integrable μ k g)
  map_smul' c f := by
    change (∫ y, (c • f) y • sectionMap k y ∂μ) = c • image μ k f
    rw [show (∫ y, (c • f) y • sectionMap k y ∂μ) =
      ∫ y, c • (f y • sectionMap k y) ∂μ by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c f] with y hy
        rw [hy]
        exact mul_smul _ _ _]
    exact integral_smul c _

def constructedMap : Lp ℂ 2 μ →L[ℂ] C(Q, ℂ) :=
  (imageLinear μ k).mkContinuous _ (image_bound μ k)

lemma kernelMap_apply (f : Lp ℂ 2 μ) (x : Q) :
    Spec.kernelMap μ k f x = ∫ y, k (x,y) * f y ∂μ := by
  have hex : ∃ A : Lp ℂ 2 μ →L[ℂ] C(Q, ℂ),
      ∀ (f : Lp ℂ 2 μ) (x : Q), A f x = ∫ y, k (x,y) * f y ∂μ :=
    ⟨constructedMap μ k, image_apply μ k⟩
  exact Classical.epsilon_spec hex f x

lemma factor_continuous :
    (Spec.kernelMap μ k).comp (Spec.inclusion μ) = Spec.continuousOperator μ k := by
  ext f x
  rw [ContinuousLinearMap.comp_apply, kernelMap_apply,
    ExpandedFA.PartV.ContinuousKernel.Spec.KernelOperatorValue_apply]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ f] with y hy
  rw [hy]

lemma factor_hilbert :
    (Spec.inclusion μ).comp (Spec.kernelMap μ k) = Spec.hilbertOperator μ k := by
  ext1 f
  apply Lp.ext
  have hker : Spec.kernelClass μ k = (k.memLp (p := 2) (μ.prod μ) ℂ).toLp k := by
    apply Lp.ext
    exact (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ.prod μ) k).trans (MemLp.coeFn_toLp _).symm
  have h := ExpandedFA.PartV.L2Kernel.kernel_representative_formula μ μ k f
    (k.memLp (p := 2) (μ.prod μ) ℂ) (Lp.memLp f)
  rw [Lp.toLp_coeFn] at h
  change (ContinuousMap.toLp 2 μ ℂ (Spec.kernelMap μ k f) : Q → ℂ) =ᵐ[μ] _
  refine (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (Spec.kernelMap μ k f)).trans ?_
  rw [Spec.hilbertOperator, hker]
  have hp : (Spec.kernelMap μ k f : Q → ℂ) =ᵐ[μ] (fun x => ∫ y, k (x,y) * f y ∂μ) :=
    Filter.Eventually.of_forall (kernelMap_apply μ k f)
  exact hp.trans h.symm
end Representation

theorem representation : Spec.Representation.{u} := by
  intro Q _ _ _ _ μ _ k
  exact ⟨kernelMap_apply μ k, factor_continuous μ k, factor_hilbert μ k⟩

section Algebra
variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma mem_generalizedSpace (T : E →L[ℂ] E) (z : ℂ) (x : E) :
    x ∈ Spec.generalizedSpace T z ↔
      ∃ n : ℕ, ((z • (LinearMap.id : E →ₗ[ℂ] E) - T.toLinearMap) ^ n) x = 0 := by
  exact Submodule.mem_iSup_of_directed
    (fun n : ℕ => LinearMap.ker ((z • (LinearMap.id : E →ₗ[ℂ] E) - T.toLinearMap) ^ n))
    (z • LinearMap.id - T.toLinearMap).iterateKer.monotone.directed_le


lemma intertwine_power (A : F →L[ℂ] E) (J : E →L[ℂ] F) (z : ℂ) (n : ℕ) (x : E) :
    ((z • (LinearMap.id : F →ₗ[ℂ] F) - (J.comp A).toLinearMap) ^ n) (J x) =
      J (((z • (LinearMap.id : E →ₗ[ℂ] E) - (A.comp J).toLinearMap) ^ n) x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
    simpa only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, map_sub, map_smul] using
      ih (z • x - A (J x))

lemma maps_generalizedSpace (A : F →L[ℂ] E) (J : E →L[ℂ] F) (z : ℂ)
    {x : E} (hx : x ∈ Spec.generalizedSpace (A.comp J) z) :
    J x ∈ Spec.generalizedSpace (J.comp A) z := by
  obtain ⟨n, hn⟩ := (mem_generalizedSpace _ _ _).mp hx
  exact (mem_generalizedSpace _ _ _).mpr ⟨n, by rw [intertwine_power, hn, map_zero]⟩

/-- The restriction of J to the generalized space. -/
def generalizedMap (A : F →L[ℂ] E) (J : E →L[ℂ] F) (z : ℂ) :
    Spec.generalizedSpace (A.comp J) z →ₗ[ℂ] Spec.generalizedSpace (J.comp A) z :=
  J.toLinearMap.restrict (fun _ hx => maps_generalizedSpace A J z hx)

lemma generalizedMap_injective (A : F →L[ℂ] E) (J : E →L[ℂ] F)
    (z : ℂ) (hz : z ≠ 0) : Function.Injective (generalizedMap A J z) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro x hx
  have hJ : J (x : E) = 0 := congrArg Subtype.val hx
  have hpow (n : ℕ) :
      ((z • (LinearMap.id : E →ₗ[ℂ] E) - (A.comp J).toLinearMap) ^ n) (x : E) = z ^ n • (x : E) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      simp [hJ, pow_succ, smul_smul, mul_comm]
  obtain ⟨n, hn⟩ := (mem_generalizedSpace _ _ _).mp x.property
  rw [hpow] at hn
  have hx0 : (x : E) = 0 := (smul_eq_zero.mp hn).resolve_left (pow_ne_zero n hz)
  exact Subtype.ext hx0

lemma compact_generalizedSpace_finite (T : E →L[ℂ] E) (hT : IsCompactOperator T)
    (z : ℂ) (hz : z ≠ 0) : FiniteDimensional ℂ (Spec.generalizedSpace T z) := by
  obtain ⟨p, hp, hfin, hstable, _⟩ := ExpandedFA.Fredholm.compact_generalized_eigenspace_stabilizes
    T ((ExpandedFA.Compactness.compact_iff_isCompactOperator _).mpr hT) z hz
  have heq : Spec.generalizedSpace T z =
      LinearMap.ker ((z • (LinearMap.id : E →ₗ[ℂ] E) - T.toLinearMap) ^ p) := by
    apply le_antisymm
    · apply iSup_le
      intro n
      by_cases hn : n ≤ p
      · exact (z • (LinearMap.id : E →ₗ[ℂ] E) - T.toLinearMap).iterateKer.monotone hn
      · exact le_of_eq (hstable n (le_of_not_ge hn))
    · exact le_iSup (fun n : ℕ => LinearMap.ker ((z • (LinearMap.id : E →ₗ[ℂ] E) - T.toLinearMap) ^ n)) p
  rw [heq]
  exact hfin

/-- Algebraic multiplicity comparison uses injections in both directions;
neither map is required to be globally injective. Only AJ needs compactness. -/
lemma generalized_equivalence (A : F →L[ℂ] E) (J : E →L[ℂ] F)
    (hT : IsCompactOperator (A.comp J)) (z : ℂ) (hz : z ≠ 0) :
    FiniteDimensional ℂ (Spec.generalizedSpace (A.comp J) z) ∧
    FiniteDimensional ℂ (Spec.generalizedSpace (J.comp A) z) ∧
    (∃ e : Spec.generalizedSpace (A.comp J) z ≃ₗ[ℂ]
        Spec.generalizedSpace (J.comp A) z,
      ∀ x, (e x : F) = J (x : E)) ∧
    Module.finrank ℂ (Spec.generalizedSpace (A.comp J) z) =
      Module.finrank ℂ (Spec.generalizedSpace (J.comp A) z) := by
  haveI := compact_generalizedSpace_finite (A.comp J) hT z hz
  haveI := FiniteDimensional.of_injective (generalizedMap J A z)
    (generalizedMap_injective J A z hz)
  have heq := le_antisymm
    (LinearMap.finrank_le_finrank_of_injective (generalizedMap_injective A J z hz))
    (LinearMap.finrank_le_finrank_of_injective (generalizedMap_injective J A z hz))
  refine ⟨inferInstance, inferInstance, ?_, heq⟩
  exact ⟨(generalizedMap A J z).linearEquivOfInjective
    (generalizedMap_injective A J z hz) heq, fun _ => rfl⟩

/-- The explicit resolvent transfer, valid for any pair of bounded maps. -/
lemma transfer_inverse (A : F →L[ℂ] E) (J : E →L[ℂ] F) (z : ℂ) (hz : z ≠ 0)
    (S : E →L[ℂ] E)
    (hl : ∀ x, S (z • x - A (J x)) = x)
    (hr : ∀ x, z • S x - A (J (S x)) = x) :
    ∃ R : F →L[ℂ] F,
      (∀ y, R (z • y - J (A y)) = y) ∧
      (∀ y, z • R y - J (A (R y)) = y) := by
  let R : F →L[ℂ] F := z⁻¹ • (ContinuousLinearMap.id ℂ F + J.comp (S.comp A))
  refine ⟨R, ?_, ?_⟩
  · intro y
    change z⁻¹ • ((z • y - J (A y)) + J (S (A (z • y - J (A y))))) = y
    rw [map_sub, map_smul, hl (A y)]
    simp [sub_add_cancel, inv_smul_smul₀ hz]
  · intro y
    change z • (z⁻¹ • (y + J (S (A y)))) -
      J (A (z⁻¹ • (y + J (S (A y))))) = y
    simp only [smul_inv_smul₀ hz, map_smul, map_add]
    have h := congrArg J (hr (A y))
    simp only [map_sub, map_smul] at h
    have hh : z⁻¹ • (J (A y) + J (A (J (S (A y))))) = J (S (A y)) := by
      rw [← sub_eq_iff_eq_add.mp h, inv_smul_smul₀ hz]
    rw [hh]
    abel

lemma spectrum_comp_iff (A : F →L[ℂ] E) (J : E →L[ℂ] F)
    (z : ℂ) (hz : z ≠ 0) :
    z ∈ spectrum ℂ (A.comp J) ↔ z ∈ spectrum ℂ (J.comp A) := by
  change (z ∈ Specs.ExpandedFA.BanachAlgebra.Conventions.AlgebraSpectrumValue ℂ (E →L[ℂ] E) (A.comp J) ↔
    z ∈ Specs.ExpandedFA.BanachAlgebra.Conventions.AlgebraSpectrumValue ℂ (F →L[ℂ] F) (J.comp A))
  rw [ExpandedFA.BanachAlgebra.operator_spectrum_iff_no_bounded_inverse,
    ExpandedFA.BanachAlgebra.operator_spectrum_iff_no_bounded_inverse]
  constructor
  · intro h ⟨S, hl, hr⟩
    exact h (transfer_inverse J A z hz S hl hr)
  · intro h ⟨S, hl, hr⟩
    exact h (transfer_inverse A J z hz S hl hr)
end Algebra

theorem spectral_comparison : Spec.SpectralComparison.{u} := by
  intro Q _ _ _ _ μ _ k z hz
  have hcompact : IsCompactOperator ((Spec.kernelMap μ k).comp (Spec.inclusion μ)) := by
    rw [factor_continuous]
    exact ExpandedFA.PartV.ContinuousKernel.kernelOperator_isCompact μ k
  have h := generalized_equivalence (Spec.kernelMap μ k) (Spec.inclusion μ) hcompact z hz
  have hs := spectrum_comp_iff (Spec.kernelMap μ k) (Spec.inclusion μ) z hz
  rw [factor_continuous, factor_hilbert] at hs h
  exact ⟨hs, h⟩

end ExpandedFA.FredholmDeterminant.KernelSpectralBridge
