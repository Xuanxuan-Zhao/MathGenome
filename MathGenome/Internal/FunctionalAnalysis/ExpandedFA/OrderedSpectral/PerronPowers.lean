import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.OrderedSpectral.PerronPowers
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.OrderedSpectral.PerronEigenstructure

/-! Norm convergence of Perron powers on an arbitrary nonempty compact Hausdorff
space. The explicit eigenprojection splits off a compact remainder whose
spectral radius is below one. The Markov conclusion uses the same norm limit
to identify every invariant normalized functional and its Radon measure. -/

noncomputable section
namespace ExpandedFA.OrderedSpectral.PerronPowers
open PerronEigenstructure PerronEigenstructure.Spec Spec
open Filter MeasureTheory
open scoped Topology
universe u
variable {Q : Type u} [TopologicalSpace Q] [CompactSpace Q]

lemma eigenprojection_apply (u : C(Q, ℂ)) (φ : C(Q, ℂ) →L[ℂ] ℂ) (f : C(Q, ℂ)) :
    eigenprojection u φ f = (φ f / φ u) • u := by
  simp [eigenprojection, smul_smul, div_eq_mul_inv]

lemma eigenprojection_apply_point (u : C(Q, ℂ)) (φ : C(Q, ℂ) →L[ℂ] ℂ)
    (f : C(Q, ℂ)) (q : Q) : eigenprojection u φ f q = u q * φ f / φ u := by
  rw [eigenprojection_apply]
  simp [div_eq_mul_inv, mul_comm, mul_assoc]

lemma eigenprojection_idempotent (u : C(Q, ℂ)) (φ : C(Q, ℂ) →L[ℂ] ℂ)
    (hφu : φ u ≠ 0) : eigenprojection u φ * eigenprojection u φ = eigenprojection u φ := by
  ext f q
  simp [eigenprojection_apply, hφu, div_eq_mul_inv]

lemma eigenprojection_compact (u : C(Q, ℂ)) (φ : C(Q, ℂ) →L[ℂ] ℂ) :
    IsCompactOperator (eigenprojection u φ) := by
  exact (isCompactOperator_of_locallyCompactSpace_dom φ).clm_comp
    ((ContinuousLinearMap.id ℂ ℂ).smulRight ((φ u)⁻¹ • u))

/-- A strict spectral-radius bound gives decay in the Banach algebra norm. -/
lemma powers_tendsto_zero_of_radius_lt_one
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (hA : Specs.ExpandedFA.BanachAlgebra.Conventions.IsUnitalBanachAlgebraValue A)
    (a : A)
    (ha : Specs.ExpandedFA.BanachAlgebra.Conventions.AlgebraSpectralRadiusValue ℂ A a < 1) :
    Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0) := by
  let r := Specs.ExpandedFA.BanachAlgebra.Conventions.AlgebraSpectralRadiusValue ℂ A a
  have hr0 : 0 ≤ r := (BanachAlgebra.algebraSpectralRadius_maximum A hA a).2.2.1
  obtain ⟨c, hrc, hc⟩ := exists_between ha
  have hc0 : 0 ≤ c := hr0.trans hrc.le
  have hroot := BanachAlgebra.algebraSpectralRadius_root_limit A hA a
  have hb : ∀ᶠ n : ℕ in atTop, ‖a ^ (n + 1)‖ ≤ c ^ (n + 1) := by
    filter_upwards [hroot.eventually (gt_mem_nhds hrc)] with n hn
    have hp := pow_le_pow_left₀ (Real.rpow_nonneg (norm_nonneg _) _) hn.le (n + 1)
    simpa only [one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) (Nat.succ_ne_zero n)] using hp
  have hz : Tendsto (fun n : ℕ => a ^ (n + 1)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' hb
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc).comp (tendsto_add_atTop_nat 1)
  exact (tendsto_add_atTop_iff_nat 1).mp hz

/-- Algebraic separation of the fixed line from the decaying remainder. -/
lemma powers_eq_projection_add {A : Type*} [Ring A] {T P : A}
    (hP : P * P = P) (hTP : T * P = P) (hPT : P * T = P) :
    ∀ n : ℕ, T ^ (n + 1) = P + (T - P) ^ (n + 1) := by
  intro n
  have hz : (T - P) * P = 0 := by rw [sub_mul, hTP, hP, sub_self]
  have hpow : ∀ n : ℕ, P * T ^ n = P := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← mul_assoc, ih, hPT]
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      T ^ (n + 1 + 1) = T * T ^ (n + 1) := pow_succ' _ _
      _ = P + (T - P) * T ^ (n + 1) := by rw [sub_mul, hpow]; abel
      _ = P + (T - P) * (P + (T - P) ^ (n + 1)) := by rw [ih]
      _ = P + (T - P) ^ (n + 1 + 1) := by
        rw [mul_add, hz, zero_add]
        exact congrArg (P + ·) (pow_succ' (T - P) (n + 1)).symm

/-- The compact remainder has no spectral value of modulus at least one. -/
theorem normalized_powers_tendsto [Nonempty Q]
    (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ)) (hcompact : IsCompactOperator K)
    (hreal : PreservesReal K) (hstrong : StronglyPositive K)
    {r : ℝ} (hr : 0 < r) {u : C(Q, ℂ)} (hu : StrictlyPositive u)
    (hKu : K u = (r : ℂ) • u) (φ : C(Q, ℂ) →L[ℂ] ℂ)
    (hφ : ∀ f, φ (K f) = (r : ℂ) * φ f) (hφu : φ u ≠ 0) :
    Tendsto (fun n : ℕ => ((r : ℂ)⁻¹ ^ n) • K ^ n) atTop
      (𝓝 (eigenprojection u φ)) := by
  let T : C(Q, ℂ) →L[ℂ] C(Q, ℂ) := (r : ℂ)⁻¹ • K
  let P := eigenprojection u φ
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hTu : T u = u := by
    change (r : ℂ)⁻¹ • K u = u
    rw [hKu, smul_smul, inv_mul_cancel₀ hrC, one_smul]
  have hφT (f : C(Q, ℂ)) : φ (T f) = φ f := by simp [T, hφ, hrC]
  have hφP (f : C(Q, ℂ)) : φ (P f) = φ f := by
    simp [P, eigenprojection_apply, hφu]
  have hP : P * P = P := eigenprojection_idempotent u φ hφu
  have hTP : T * P = P := by
    ext f q
    simp only [mul_apply_eq_comp, P, eigenprojection_apply, map_smul, hTu]
  have hPT : P * T = P := by
    ext f q
    simp only [mul_apply_eq_comp, P, eigenprojection_apply, hφT]
  let R := T - P
  have hRcompact : IsCompactOperator R :=
    (hcompact.smul (r : ℂ)⁻¹).sub (eigenprojection_compact u φ)
  have hRφ (f : C(Q, ℂ)) : φ (R f) = 0 := by
    simp only [R, sub_apply, map_sub, hφT, hφP, sub_self]
  have hspectrum : ∀ ζ ∈ spectrum ℂ R, ‖ζ‖ < 1 := by
    intro ζ hζ
    by_cases hζ0 : ζ = 0
    · simp [hζ0]
    have hc : Compactness.IsCompactLinearMap R.toLinearMap :=
      (Compactness.compact_iff_isCompactOperator R.toLinearMap).mpr hRcompact
    obtain ⟨z, hz, hRz⟩ :=
      (Fredholm.compact_nonzero_spectrum_iff_eigenvalue R hc ζ hζ0).mp hζ
    have hφz : φ z = 0 := by
      have he := congrArg φ hRz
      rw [hRφ, map_smul, smul_eq_mul] at he
      exact (mul_eq_zero.mp he.symm).resolve_left hζ0
    have hPz : P z = 0 := by simp [P, eigenprojection_apply, hφz]
    have hTz : T z = ζ • z := by
      simpa only [R, sub_apply, hPz, sub_zero] using hRz
    have hKz : K z = ((r : ℂ) * ζ) • z := by
      have he := congrArg (fun f : C(Q, ℂ) => (r : ℂ) • f) hTz
      simpa only [T, smul_apply, smul_smul, mul_inv_cancel₀ hrC,
        one_smul] using he
    by_contra hn
    have hnorm : r ≤ ‖(r : ℂ) * ζ‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      nlinarith [le_of_not_gt hn]
    obtain ⟨_, a, ha⟩ := peripheral_eigenvector K hreal hstrong hr hu hKu hz hKz hnorm
    have ha0 : a = 0 := by
      have he := congrArg φ ha
      rw [hφz, map_smul, smul_eq_mul] at he
      exact (mul_eq_zero.mp he.symm).resolve_right hφu
    exact hz (by simp [ha, ha0])
  have hA : Specs.ExpandedFA.BanachAlgebra.Conventions.IsUnitalBanachAlgebraValue
      (C(Q, ℂ) →L[ℂ] C(Q, ℂ)) := ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨⟨ζ, hζ, he⟩, _⟩ := BanachAlgebra.algebraSpectralRadius_maximum _ hA R
  have hdecay := powers_tendsto_zero_of_radius_lt_one hA R (he ▸ hspectrum ζ hζ)
  have ht : Tendsto (fun n : ℕ => T ^ (n + 1)) atTop (𝓝 P) := by
    have hlim := (tendsto_const_nhds (x := P) (f := atTop)).add (hdecay.comp (tendsto_add_atTop_nat 1))
    simpa only [Function.comp_def, add_zero, R, ← powers_eq_projection_add hP hTP hPT] using hlim
  have ht' := (tendsto_add_atTop_iff_nat 1).mp ht
  change Tendsto (fun n : ℕ => T ^ n) atTop (𝓝 P) at ht'
  convert ht' using 1
  funext n
  change ((r : ℂ)⁻¹ ^ n) • K ^ n = T ^ n
  induction n with
  | zero => simp
  | succ n ih =>
    ext f q
    simp only [pow_succ', mul_apply_eq_comp, T, smul_apply, ← ih, map_smul,
      smul_smul, mul_comm]

/-- The complete conclusion, retaining the upstream eigenstructure witnesses. -/
theorem powers : Spec.PowersTheorem.{u} := by
  intro Q _ _ _ _ _ _ K hcompact hreal hstrong
  obtain ⟨hr, u, φ, μ, hu, hKu, hsimple, hμ, him, hpos, hother⟩ :=
    PerronEigenstructure.eigenstructure Q K hcompact hreal hstrong
  have hφu : φ u ≠ 0 := by
    intro hz
    have := congrArg Complex.re hz
    simp only [Complex.zero_re] at this
    linarith
  exact ⟨hr, u, φ, μ, hu, hKu, hsimple, hμ, him, hpos, hother,
    normalized_powers_tendsto K hcompact hreal hstrong hr hu hKu φ hμ.2.2.2 hφu,
    eigenprojection_apply_point u φ⟩

section Measures
variable [MeasurableSpace Q] [BorelSpace Q]

/-- Integration as a bounded complex-linear functional in the supremum norm. -/
def integralFunctional (ν : Measure Q) [IsFiniteMeasure ν] : C(Q, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ q, f q ∂ν
      map_add' := fun f g => integral_add
        ((BoundedContinuousFunction.mkOfCompact f).integrable ν)
        ((BoundedContinuousFunction.mkOfCompact g).integrable ν)
      map_smul' := fun c f => integral_smul c f }
    (ν.real Set.univ) (fun f =>
      (BoundedContinuousFunction.mkOfCompact f).norm_integral_le_mul_norm ν)

@[simp] lemma integralFunctional_apply (ν : Measure Q) [IsFiniteMeasure ν]
    (f : C(Q, ℂ)) : integralFunctional ν f = ∫ q, f q ∂ν := rfl

lemma eigenmeasure_one {K : C(Q, ℂ) →L[ℂ] C(Q, ℂ)} {r : ℝ}
    {φ : C(Q, ℂ) →L[ℂ] ℂ} {μ : Measure Q} (hμ : Eigenmeasure K r φ μ) :
    φ 1 = 1 := by
  have : IsProbabilityMeasure μ := ⟨hμ.2.1⟩
  simpa using (hμ.2.2.1 1).2

/-- Any normalized invariant functional is determined by the norm limit. -/
lemma invariant_functional_unique
    (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ)) (φ ψ : C(Q, ℂ) →L[ℂ] ℂ)
    (hlim : Tendsto (fun n : ℕ => K ^ n) atTop (𝓝 (φ.smulRight 1)))
    (hψ : ∀ f, ψ (K f) = ψ f) (hψ1 : ψ 1 = 1) : ψ = φ := by
  apply ContinuousLinearMap.ext
  intro f
  have hiter : ∀ n : ℕ, ψ ((K ^ n) f) = ψ f := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simpa only [pow_succ', mul_apply_eq_comp, hψ] using ih
  have htest := (ψ.continuous.tendsto ((φ.smulRight 1) f)).comp
    (((ContinuousLinearMap.apply ℂ (C(Q, ℂ)) f).continuous.tendsto (φ.smulRight 1)).comp hlim)
  change Tendsto (fun n : ℕ => ψ ((K ^ n) f)) atTop
    (𝓝 (ψ ((φ.smulRight 1) f))) at htest
  have he : ψ f = ψ ((φ.smulRight 1) f) :=
    tendsto_nhds_unique (by simpa only [hiter] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => ψ f) atTop (𝓝 (ψ f)))) htest
  simpa only [ContinuousLinearMap.smulRight_apply, map_smul, hψ1,
    smul_eq_mul, mul_one] using he

/-- The Markov normalization and uniqueness of the representing probability. -/
theorem markov : Spec.MarkovTheorem.{u} := by
  intro Q _ _ _ _ _ _ K hcompact hreal hstrong hK1
  obtain ⟨hr, u, φ, μ, hu, hKu, hsimple, hμ, him, hpos, hother⟩ :=
    PerronEigenstructure.eigenstructure Q K hcompact hreal hstrong
  have hφ1 : φ 1 = 1 := eigenmeasure_one hμ
  have hr1 : radius K = 1 := by
    have he := hμ.2.2.2 1
    rw [hK1, hφ1, mul_one] at he
    simpa using (congrArg Complex.re he).symm
  have hone : StrictlyPositive (1 : C(Q, ℂ)) := by intro q; simp
  have hKone : K 1 = (radius K : ℂ) • (1 : C(Q, ℂ)) := by simp [hK1, hr1]
  have hsimple1 : AlgebraicallySimple K (radius K) (1 : C(Q, ℂ)) :=
    algebraicallySimple_of_eigenfunctional K hreal hstrong hr hone hKone φ
      hμ.2.2.2 (by rw [hφ1]; exact one_ne_zero)
  have hlimit := normalized_powers_tendsto K hcompact hreal hstrong hr hone hKone
    φ hμ.2.2.2 (by rw [hφ1]; exact one_ne_zero)
  have hp : eigenprojection (1 : C(Q, ℂ)) φ = φ.smulRight 1 := by
    simp [eigenprojection, hφ1]
  have hlimit' : Tendsto (fun n : ℕ => K ^ n) atTop (𝓝 (φ.smulRight 1)) := by
    simpa only [hr1, Complex.ofReal_one, inv_one, one_pow, one_smul, hp] using hlimit
  have hμinv : InvariantProbability K μ := by
    refine ⟨hμ.1, hμ.2.1, ?_⟩
    intro f
    rw [← (hμ.2.2.1 (K f)).2, ← (hμ.2.2.1 f).2, hμ.2.2.2, hr1]
    simp
  refine ⟨hr1, φ, μ, hone, hKone, hsimple1, hμ, hφ1, hμinv, ?_, hlimit'⟩
  intro ν hν
  have : IsProbabilityMeasure ν := ⟨hν.2.1⟩
  have hψ : integralFunctional ν = φ := invariant_functional_unique K φ
    (integralFunctional ν) hlimit' hν.2.2 (by simp)
  have heq (f : C(Q, ℂ)) : (∫ q, f q ∂ν) = ∫ q, f q ∂μ := by
    calc
      (∫ q, f q ∂ν) = integralFunctional ν f := rfl
      _ = φ f := congrArg (fun ψ : C(Q, ℂ) →L[ℂ] ℂ => ψ f) hψ
      _ = ∫ q, f q ∂μ := (hμ.2.2.1 f).2
  have : ν.Regular :=
    FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular ν |>.mp hν.1
  have : μ.Regular :=
    FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular μ |>.mp hμ.1
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let g : C(Q, ℂ) := ⟨fun q => (f q : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have he := heq g
  simp only [g, ContinuousMap.coe_mk, integral_complex_ofReal] at he
  exact Complex.ofReal_injective he

end Measures
end ExpandedFA.OrderedSpectral.PerronPowers

namespace ExpandedFA.OrderedSpectral.PerronPowers.Real
open MeasureTheory Filter
open scoped Topology
universe u
variable {Q : Type u} [TopologicalSpace Q] [CompactSpace Q]

@[simp] lemma realCoord_apply (f : C(Q, ℂ)) (q : Q) : realCoord f q = (f q).re := rfl
@[simp] lemma imagCoord_apply (f : C(Q, ℂ)) (q : Q) : imagCoord f q = (f q).im := rfl
@[simp] lemma complexEmbed_apply (f : C(Q, ℝ)) (q : Q) : complexEmbed f q = (f q : ℂ) := rfl
@[simp] lemma realCoord_embed (f : C(Q, ℝ)) : realCoord (complexEmbed f) = f := by ext q; simp
@[simp] lemma imagCoord_embed (f : C(Q, ℝ)) : imagCoord (complexEmbed f) = 0 := by ext q; simp
@[simp] lemma complexEmbed_one : complexEmbed (1 : C(Q, ℝ)) = 1 := by ext q; simp
@[simp] lemma realCoord_one : realCoord (1 : C(Q, ℂ)) = 1 := by ext q; simp
lemma complexEmbed_injective : Function.Injective (complexEmbed (Q := Q)) := by
  intro f g h
  simpa using congrArg realCoord h

lemma norm_complexEmbed (f : C(Q, ℝ)) : ‖complexEmbed f‖ = ‖f‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro q
    simpa using f.norm_coe_le_norm q
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro q
    simpa using (complexEmbed f).norm_coe_le_norm q

lemma norm_realCoord_le (f : C(Q, ℂ)) : ‖realCoord f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro q
  exact (Complex.abs_re_le_norm (f q)).trans (f.norm_coe_le_norm q)

lemma norm_imagCoord_le (f : C(Q, ℂ)) : ‖imagCoord f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro q
  exact (Complex.abs_im_le_norm (f q)).trans (f.norm_coe_le_norm q)

@[simp] lemma complexify_apply (K : C(Q, ℝ) →L[ℝ] C(Q, ℝ)) (f : C(Q, ℂ)) (q : Q) :
    complexify K f q = (K (realCoord f) q : ℂ) + Complex.I * (K (imagCoord f) q : ℂ) := rfl

@[simp] lemma complexify_embed (K : C(Q, ℝ) →L[ℝ] C(Q, ℝ)) (f : C(Q, ℝ)) :
    complexify K (complexEmbed f) = complexEmbed (K f) := by
  ext q
  simp

lemma complexify_compact (K : C(Q, ℝ) →L[ℝ] C(Q, ℝ)) (hK : IsCompactOperator K) :
    IsCompactOperator (complexify K) := by
  exact ((hK.comp_clm realCoord).clm_comp complexEmbed).add
    (((hK.comp_clm imagCoord).clm_comp complexEmbed).smul Complex.I)

lemma complexify_preservesReal (K : C(Q, ℝ) →L[ℝ] C(Q, ℝ)) :
    PerronEigenstructure.Spec.PreservesReal (complexify K) := by
  intro f hf
  have him : imagCoord f = 0 := by ext q; exact hf q
  intro q
  simp [him]

lemma complexify_stronglyPositive (K : C(Q, ℝ) →L[ℝ] C(Q, ℝ))
    (hK : StronglyPositive K) : PerronEigenstructure.Spec.StronglyPositive (complexify K) := by
  intro f hf hf0
  have him : imagCoord f = 0 := by ext q; exact (hf q).1
  have hre0 : realCoord f ≠ 0 := by
    intro h
    apply hf0
    ext q
    apply Complex.ext
    · exact congrArg (fun g : C(Q, ℝ) => g q) h
    · exact (hf q).1
  intro q
  simpa [him] using hK (realCoord f) (fun p => (hf p).2) hre0 q

/-- Restriction of an operator to real inputs followed by its real coordinate.
This is continuous for operator norms, even for operators not preserving reals. -/
def restrictOperator (T : C(Q, ℂ) →L[ℂ] C(Q, ℂ)) : C(Q, ℝ) →L[ℝ] C(Q, ℝ) :=
  realCoord.comp ((T.restrictScalars ℝ).comp complexEmbed)

/-- Restriction is contractive for the supremum operator norms. -/
lemma norm_restrictOperator_le (T : C(Q, ℂ) →L[ℂ] C(Q, ℂ)) :
    ‖restrictOperator T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  change ‖realCoord (T (complexEmbed f))‖ ≤ ‖T‖ * ‖f‖
  exact (norm_realCoord_le _).trans (by simpa only [norm_complexEmbed] using T.le_opNorm (complexEmbed f))

/-- The concrete complexification has equivalent operator norm. In particular
it neither loses real vectors nor changes norm convergence of its powers. -/
lemma norm_complexify_bounds (K : C(Q, ℝ) →L[ℝ] C(Q, ℝ)) :
    ‖K‖ ≤ ‖complexify K‖ ∧ ‖complexify K‖ ≤ 2 * ‖K‖ := by
  constructor
  · have he : restrictOperator (complexify K) = K := by
      ext f q; simp [restrictOperator]
    simpa only [he] using norm_restrictOperator_le (complexify K)
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro f
    calc
      ‖complexify K f‖ ≤ ‖complexEmbed (K (realCoord f))‖ +
          ‖Complex.I • complexEmbed (K (imagCoord f))‖ := norm_add_le _ _
      _ = ‖K (realCoord f)‖ + ‖K (imagCoord f)‖ := by
        rw [norm_smul, Complex.norm_I, one_mul, norm_complexEmbed, norm_complexEmbed]
      _ ≤ ‖K‖ * ‖realCoord f‖ + ‖K‖ * ‖imagCoord f‖ :=
        add_le_add (K.le_opNorm _) (K.le_opNorm _)
      _ ≤ ‖K‖ * ‖f‖ + ‖K‖ * ‖f‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (norm_realCoord_le f) (norm_nonneg K))
          (mul_le_mul_of_nonneg_left (norm_imagCoord_le f) (norm_nonneg K))
      _ = (2 * ‖K‖) * ‖f‖ := by ring

lemma continuous_restrictOperator : Continuous (restrictOperator (Q := Q)) := by
  unfold restrictOperator
  exact ((ContinuousLinearMap.compL ℝ (C(Q, ℝ)) (C(Q, ℂ)) (C(Q, ℝ)) realCoord).continuous).comp
    (((ContinuousLinearMap.compL ℝ (C(Q, ℝ)) (C(Q, ℂ)) (C(Q, ℂ))).flip complexEmbed).continuous.comp
      (ContinuousLinearMap.restrictScalarsL ℂ (C(Q, ℂ)) (C(Q, ℂ)) ℝ ℝ).continuous)

@[simp] lemma complexify_pow_embed (K : C(Q, ℝ) →L[ℝ] C(Q, ℝ)) (n : ℕ) (f : C(Q, ℝ)) :
    (complexify K ^ n) (complexEmbed f) = complexEmbed ((K ^ n) f) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ', mul_apply_eq_comp, ih, complexify_embed]

lemma restrict_normalized_pow (K : C(Q, ℝ) →L[ℝ] C(Q, ℝ)) (r : ℝ) (n : ℕ) :
    restrictOperator (((r : ℂ)⁻¹ ^ n) • complexify K ^ n) = (r⁻¹ ^ n) • K ^ n := by
  apply ContinuousLinearMap.ext
  intro f
  change realCoord ((((r : ℂ)⁻¹ ^ n) • complexify K ^ n) (complexEmbed f)) = _
  rw [smul_apply, complexify_pow_embed]
  ext q
  simp [← Complex.ofReal_inv, ← Complex.ofReal_pow]

lemma restrict_projection (u : C(Q, ℂ)) (φ : C(Q, ℂ) →L[ℂ] ℂ)
    (hu : PerronEigenstructure.Spec.RealValued u) (hφu : (φ u).im = 0) :
    restrictOperator (Spec.eigenprojection u φ) =
      eigenprojection (realCoord u) (Complex.reCLM.comp ((φ.restrictScalars ℝ).comp complexEmbed)) := by
  have heu : complexEmbed (realCoord u) = u := by
    ext q; exact Complex.ext (by simp) (by simp [hu q])
  have heφ : φ u = ((φ u).re : ℂ) := by
    apply Complex.ext <;> simp [hφu]
  ext f q
  change ((Spec.eigenprojection u φ (complexEmbed f)) q).re =
    (φ (complexEmbed f)).re * ((φ (complexEmbed (realCoord u))).re⁻¹ * (u q).re)
  rw [heu, PerronPowers.eigenprojection_apply]
  simp only [ContinuousMap.smul_apply, smul_eq_mul, div_eq_mul_inv]
  rw [heφ]
  simp [Complex.mul_re, hu q, mul_assoc]

lemma embed_realCoord (f : C(Q, ℂ)) (hf : PerronEigenstructure.Spec.RealValued f) :
    complexEmbed (realCoord f) = f := by
  ext q; exact Complex.ext (by simp) (by simp [hf q])

lemma complexEmbed_real_smul (c : ℝ) (f : C(Q, ℝ)) :
    complexEmbed (c • f) = (c : ℂ) • complexEmbed f := by
  ext q; simp

lemma defect_pow_embed (K : C(Q, ℝ) →L[ℝ] C(Q, ℝ)) (r : ℝ) (n : ℕ) (f : C(Q, ℝ)) :
    (((r : ℂ) • LinearMap.id - (complexify K).toLinearMap : C(Q, ℂ) →ₗ[ℂ] C(Q, ℂ)) ^ n) (complexEmbed f) =
    complexEmbed (((r • LinearMap.id - K.toLinearMap : C(Q, ℝ) →ₗ[ℝ] C(Q, ℝ)) ^ n) f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', Module.End.mul_apply, ih, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, ContinuousLinearMap.coe_coe,
      complexify_embed, map_sub, complexEmbed_real_smul]

lemma algebraicallySimple_restrict (K : C(Q, ℝ) →L[ℝ] C(Q, ℝ)) (r : ℝ)
    (u : C(Q, ℂ)) (hu : PerronEigenstructure.Spec.RealValued u)
    (hs : PerronEigenstructure.Spec.AlgebraicallySimple (complexify K) r u) :
    AlgebraicallySimple K r (realCoord u) := by
  intro n hn
  ext f
  constructor
  · intro hf
    have hc : complexEmbed f ∈ LinearMap.ker
        (((r : ℂ) • LinearMap.id - (complexify K).toLinearMap) ^ n) := by
      rw [LinearMap.mem_ker, defect_pow_embed, (LinearMap.mem_ker.mp hf), map_zero]
    rw [hs n hn] at hc
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hc
    apply Submodule.mem_span_singleton.mpr
    refine ⟨a.re, ?_⟩
    ext q
    have he := congrArg (fun g : C(Q, ℂ) => (g q).re) ha
    simpa [Complex.mul_re, hu q] using he
  · intro hf
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hf
    have hc : complexEmbed (a • realCoord u) ∈ Submodule.span ℂ {u} := by
      rw [complexEmbed_real_smul, embed_realCoord u hu]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
    rw [← hs n hn, LinearMap.mem_ker, defect_pow_embed] at hc
    apply LinearMap.mem_ker.mpr
    apply complexEmbed_injective
    simpa using hc

/-- The real dual functional obtained from the actual complex eigenmeasure. -/
def restrictFunctional (φ : C(Q, ℂ) →L[ℂ] ℂ) : C(Q, ℝ) →L[ℝ] ℝ :=
  Complex.reCLM.comp ((φ.restrictScalars ℝ).comp complexEmbed)

@[simp] lemma restrictFunctional_apply (φ : C(Q, ℂ) →L[ℂ] ℂ) (f : C(Q, ℝ)) :
    restrictFunctional φ f = (φ (complexEmbed f)).re := rfl

lemma eigenpair_restrict (K : C(Q, ℝ) →L[ℝ] C(Q, ℝ)) (r : ℝ)
    (u : C(Q, ℂ)) (hKu : complexify K u = (r : ℂ) • u) :
    K (realCoord u) = r • realCoord u := by
  ext q
  have he := congrArg (fun g : C(Q, ℂ) => (g q).re) hKu
  simpa [Complex.mul_re] using he

variable [MeasurableSpace Q] [BorelSpace Q]

lemma eigenmeasure_restrict (K : C(Q, ℝ) →L[ℝ] C(Q, ℝ)) (r : ℝ)
    (φ : C(Q, ℂ) →L[ℂ] ℂ) (μ : Measure Q)
    (hμ : PerronEigenstructure.Spec.Eigenmeasure (complexify K) r φ μ) :
    Eigenmeasure K r (restrictFunctional φ) μ := by
  have : IsProbabilityMeasure μ := ⟨hμ.2.1⟩
  refine ⟨hμ.1, hμ.2.1, ?_, ?_⟩
  · intro f
    refine ⟨(BoundedContinuousFunction.mkOfCompact f).integrable μ, ?_⟩
    have he := congrArg Complex.re (hμ.2.2.1 (complexEmbed f)).2
    simpa only [restrictFunctional_apply, complexEmbed_apply, integral_complex_ofReal, Complex.ofReal_re] using he
  · intro f
    have he := congrArg Complex.re (hμ.2.2.2 (complexEmbed f))
    simpa [Complex.mul_re] using he

/-- The real operator-norm convergence, with real eigenfunction and real dual. -/
theorem powers : PowersTheorem.{u} := by
  intro Q _ _ _ _ _ _ K hcompact hstrong
  obtain ⟨hr, u, φ, μ, hu, hKu, hsimple, hμ, him, hpos, hother, hlim, _⟩ :=
    PerronPowers.powers Q (complexify K) (complexify_compact K hcompact)
      (complexify_preservesReal K) (complexify_stronglyPositive K hstrong)
  have hureal : PerronEigenstructure.Spec.RealValued u := fun q => (hu q).1
  have hψu : restrictFunctional φ (realCoord u) = (φ u).re := by
    rw [restrictFunctional_apply, embed_realCoord u hureal]
  refine ⟨hr, realCoord u, restrictFunctional φ, μ, (fun q => (hu q).2),
    eigenpair_restrict K _ u hKu, algebraicallySimple_restrict K _ u hureal hsimple,
    eigenmeasure_restrict K _ φ μ hμ, hψu ▸ hpos, hother, ?_, ?_⟩
  · have ht := continuous_restrictOperator.tendsto (Spec.eigenprojection u φ) |>.comp hlim
    change Tendsto (fun n : ℕ => restrictOperator
      (((PerronEigenstructure.Spec.radius (complexify K) : ℂ)⁻¹ ^ n) • complexify K ^ n))
      atTop (𝓝 (restrictOperator (Spec.eigenprojection u φ))) at ht
    simp_rw [restrict_normalized_pow] at ht
    rw [restrict_projection u φ hureal him] at ht
    exact ht
  · intro f q
    simp [eigenprojection, div_eq_mul_inv]
    ring

/-- Invariance for real tests gives invariance for all complex tests by the two
coordinates. Finiteness follows from probability; no measure countability is used. -/
lemma invariantProbability_complexify (K : C(Q, ℝ) →L[ℝ] C(Q, ℝ))
    (ν : Measure Q) (hν : InvariantProbability K ν) :
    Spec.InvariantProbability (complexify K) ν := by
  have : IsProbabilityMeasure ν := ⟨hν.2.1⟩
  refine ⟨hν.1, hν.2.1, ?_⟩
  intro f
  have hif : Integrable (fun q => f q) ν := (BoundedContinuousFunction.mkOfCompact f).integrable ν
  have hiK : Integrable (fun q => complexify K f q) ν :=
    (BoundedContinuousFunction.mkOfCompact (complexify K f)).integrable ν
  apply Complex.ext
  · have heK := integral_re hiK
    have hef := integral_re hif
    simp only [RCLike.re_eq_complex_re] at heK hef
    rw [← heK, ← hef]
    simpa [Complex.mul_re] using hν.2.2 (realCoord f)
  · have heK := integral_im hiK
    have hef := integral_im hif
    simp only [RCLike.im_eq_complex_im] at heK hef
    rw [← heK, ← hef]
    simpa [Complex.mul_im] using hν.2.2 (imagCoord f)

lemma restrict_constantProjection (φ : C(Q, ℂ) →L[ℂ] ℂ) :
    restrictOperator (φ.smulRight (1 : C(Q, ℂ))) = (restrictFunctional φ).smulRight 1 := by
  ext f q
  simp [restrictOperator, restrictFunctional]

/-- The real Markov case, with uniqueness among all invariant Radon probabilities. -/
theorem markov : MarkovTheorem.{u} := by
  intro Q _ _ _ _ _ _ K hcompact hstrong hK1
  have hK1c : complexify K 1 = 1 := by
    rw [← complexEmbed_one, complexify_embed, hK1]
  obtain ⟨hr, φ, μ, hone, hKe, hsimple, hμ, hφ1, hμinv, huniq, hlim⟩ :=
    PerronPowers.markov Q (complexify K) (complexify_compact K hcompact)
      (complexify_preservesReal K) (complexify_stronglyPositive K hstrong) hK1c
  have hμr := eigenmeasure_restrict K _ φ μ hμ
  have hsimpleR := algebraicallySimple_restrict K _ 1 (fun q => by simp) hsimple
  have hφ1r : restrictFunctional φ 1 = 1 := by
    simp [hφ1]
  have hμinvR : InvariantProbability K μ := by
    refine ⟨hμr.1, hμr.2.1, ?_⟩
    intro f
    rw [← (hμr.2.2.1 (K f)).2, ← (hμr.2.2.1 f).2, hμr.2.2.2, hr, one_mul]
  refine ⟨hr, restrictFunctional φ, μ, (fun q => by simp), ?_, ?_, hμr, hφ1r,
    hμinvR, ?_, ?_⟩
  · simpa only [realCoord_one, radius] using eigenpair_restrict K _ 1 hKe
  · simpa only [realCoord_one, radius] using hsimpleR
  · intro ν hν
    exact huniq ν (invariantProbability_complexify K ν hν)
  · have ht := continuous_restrictOperator.tendsto (φ.smulRight 1) |>.comp hlim
    have hpow (n : ℕ) : restrictOperator (complexify K ^ n) = K ^ n := by
      simpa using restrict_normalized_pow K 1 n
    change Tendsto (fun n : ℕ => restrictOperator (complexify K ^ n))
      atTop (𝓝 (restrictOperator (φ.smulRight 1))) at ht
    simpa only [hpow, restrict_constantProjection] using ht

end ExpandedFA.OrderedSpectral.PerronPowers.Real
