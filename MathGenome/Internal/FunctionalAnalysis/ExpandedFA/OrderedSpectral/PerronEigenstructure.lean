import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.OrderedSpectral.PerronEigenstructure
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.SpectralRadius
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.CompactNonzeroSpectrum
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.SpecificLimits.Normed
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarRieszMarkov

/-! Strong order positivity on complex C(Q).
The eigenfunction comes from the compact spectrum and modulus comparison.
Bounded Cesàro evaluations in the weak dual supply the positive eigenmeasure. -/
namespace ExpandedFA.OrderedSpectral.PerronEigenstructure

open Spec MeasureTheory
open scoped ZeroAtInfty
universe u
variable {Q : Type u} [TopologicalSpace Q]

/-- The real part, still regarded as a complex-valued continuous function. -/
def realPart (f : C(Q, ℂ)) : C(Q, ℂ) :=
  ⟨fun q => ((f q).re : ℂ), Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp f.continuous)⟩

def imagPart (f : C(Q, ℂ)) : C(Q, ℂ) :=
  ⟨fun q => ((f q).im : ℂ), Complex.continuous_ofReal.comp
    (Complex.continuous_im.comp f.continuous)⟩

@[simp] lemma realPart_apply (f : C(Q, ℂ)) (q : Q) :
    realPart f q = ((f q).re : ℂ) := rfl

@[simp] lemma imagPart_apply (f : C(Q, ℂ)) (q : Q) :
    imagPart f q = ((f q).im : ℂ) := rfl

lemma realPart_add_I_smul_imagPart (f : C(Q, ℂ)) :
    realPart f + Complex.I • imagPart f = f := by
  ext q
  simpa [mul_comm] using Complex.re_add_im (f q)

variable [CompactSpace Q]

lemma map_realPart (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ)) (hK : PreservesReal K)
    (f : C(Q, ℂ)) : K (realPart f) = realPart (K f) := by
  have h₁ := hK (realPart f) (by intro q; simp)
  have h₂ := hK (imagPart f) (by intro q; simp)
  have he := congrArg K (realPart_add_I_smul_imagPart f)
  rw [map_add, map_smul] at he
  ext q
  apply Complex.ext
  · have heq := congrArg (fun g : C(Q, ℂ) => (g q).re) he
    simpa [Complex.mul_re, h₂ q] using heq
  · simp [h₁ q]

lemma stronglyPositive_nonnegative (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ))
    (hK : StronglyPositive K) {f : C(Q, ℂ)} (hf : Nonnegative f) :
    Nonnegative (K f) := by
  by_cases h : f = 0
  · subst f
    simp [Nonnegative]
  · intro q
    exact ⟨(hK f hf h q).1, (hK f hf h q).2.le⟩

/-- A nonnegative test whose image vanishes at even one point must be zero. -/
lemma eq_zero_of_image_re_nonpos (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ))
    (hK : StronglyPositive K) {f : C(Q, ℂ)} (hf : Nonnegative f)
    (q : Q) (hq : (K f q).re ≤ 0) : f = 0 := by
  by_contra h
  exact (hK f hf h q).2.not_ge hq

lemma strictlyPositive_ne_zero [Nonempty Q] {u : C(Q, ℂ)}
    (hu : StrictlyPositive u) : u ≠ 0 := by
  intro h
  obtain ⟨q⟩ := ‹Nonempty Q›
  have := (hu q).2
  simpa [h] using this

/-- A positive function on compact Q is bounded away from zero. -/
lemma strictlyPositive_uniform_lower_bound [Nonempty Q] {u : C(Q, ℂ)}
    (hu : StrictlyPositive u) : ∃ c : ℝ, 0 < c ∧ ∀ q, c ≤ (u q).re := by
  obtain ⟨q, _, hq⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
    (Complex.continuous_re.comp u.continuous).continuousOn
  exact ⟨(u q).re, (hu q).2, fun p => hq (Set.mem_univ p)⟩

/-- The complex scalar that rotates a nonzero number onto the positive axis. -/
lemma exists_norming_phase (z : ℂ) (hz : z ≠ 0) :
    ∃ α : ℂ, ‖α‖ = 1 ∧ α * z = (‖z‖ : ℂ) := by
  refine ⟨(‖z‖ : ℂ) / z, ?_, div_mul_cancel₀ _ hz⟩
  simp [norm_ne_zero_iff.mpr hz]

/-- A positive eigenfunction is an order unit. Strong positivity then forces
any eigenvector of at least its modulus to lie on its complex eigenline.
This also proves that its eigenvalue is the only peripheral eigenvalue. -/
theorem peripheral_eigenvector [Nonempty Q]
    (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ)) (hreal : PreservesReal K)
    (hstrong : StronglyPositive K) {r : ℝ} (hr : 0 < r)
    {u : C(Q, ℂ)} (hu : StrictlyPositive u) (hKu : K u = (r : ℂ) • u)
    {ζ : ℂ} {z : C(Q, ℂ)} (hz : z ≠ 0) (hKz : K z = ζ • z)
    (hζ : r ≤ ‖ζ‖) : ζ = (r : ℂ) ∧ ∃ a : ℂ, z = a • u := by
  classical
  have hc : Continuous (fun q => ‖z q‖ / (u q).re) :=
    z.continuous.norm.div (Complex.continuous_re.comp u.continuous)
      (fun q => (hu q).2.ne')
  obtain ⟨q, _, hq⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hc.continuousOn
  let M : ℝ := ‖z q‖ / (u q).re
  have hbound (p : Q) : ‖z p‖ ≤ M * (u p).re :=
    (div_le_iff₀ (hu p).2).mp (hq (Set.mem_univ p))
  have hMq : ‖z q‖ = M * (u q).re := by
    dsimp [M]
    exact (div_mul_cancel₀ _ (hu q).2.ne').symm
  have hM : 0 < M := by
    obtain ⟨p, hp⟩ : ∃ p, z p ≠ 0 := by
      by_contra h
      apply hz
      ext p
      exact not_ne_iff.mp (not_exists.mp h p)
    have := hbound p
    have := norm_pos_iff.mpr hp
    nlinarith [(hu p).2]
  have hnormq : 0 < ‖z q‖ := by rw [hMq]; exact mul_pos hM (hu q).2
  have hw : K z q ≠ 0 := by
    have : 0 < ‖K z q‖ := by
      rw [hKz]
      change 0 < ‖ζ * z q‖
      rw [norm_mul]
      exact mul_pos (hr.trans_le hζ) hnormq
    exact norm_pos_iff.mp this
  obtain ⟨α, hα, hphase⟩ := exists_norming_phase (K z q) hw
  let f : C(Q, ℂ) := (M : ℂ) • u - realPart (α • z)
  have hf : Nonnegative f := by
    intro p
    constructor
    · simp [f, Complex.mul_im, (hu p).1]
    · have hre := Complex.re_le_norm (α * z p)
      have hn : ‖α * z p‖ = ‖z p‖ := by rw [norm_mul, hα, one_mul]
      rw [hn] at hre
      have hb := hbound p
      simpa [f, Complex.mul_re] using sub_nonneg.mpr (hre.trans hb)
  have hKf : (K f q).re ≤ 0 := by
    have he : K f = (M : ℂ) • ((r : ℂ) • u) - realPart (α • K z) := by
      change K ((M : ℂ) • u - realPart (α • z)) = _
      rw [map_sub, K.map_smul, hKu, map_realPart K hreal, K.map_smul]
    have hn : ‖K z q‖ = ‖ζ‖ * ‖z q‖ := by
      rw [hKz]
      exact norm_mul ζ (z q)
    have hphase' : (α * K z q).re = ‖K z q‖ := by
      simpa using congrArg Complex.re hphase
    rw [he]
    change (M : ℂ).re * ((r : ℂ) * u q).re -
      (M : ℂ).im * ((r : ℂ) * u q).im - (α * K z q).re ≤ 0
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.mul_re, hphase', hn, hMq]
    nlinarith [mul_pos hM (hu q).2]
  have hf0 : f = 0 := eq_zero_of_image_re_nonpos K hstrong hf q hKf
  have heq : α • z = (M : ℂ) • u := by
    ext p
    have hp : (M : ℂ) * u p = ((α * z p).re : ℂ) := by
      have ht := congrArg (fun g : C(Q, ℂ) => g p) hf0
      exact sub_eq_zero.mp ht
    have hre : (α * z p).re = M * (u p).re := by
      have := congrArg Complex.re hp
      simpa [Complex.mul_re] using this.symm
    have hn : ‖α * z p‖ ≤ M * (u p).re := by
      rw [norm_mul, hα, one_mul]
      exact hbound p
    have him : (α * z p).im = 0 := by
      apply Complex.abs_re_eq_norm.mp
      rw [hre, abs_of_nonneg (mul_nonneg hM.le (hu p).2.le)]
      exact le_antisymm (by rw [← hre]; exact Complex.re_le_norm _) hn
    apply Complex.ext
    · simpa only [ContinuousMap.smul_apply, smul_eq_mul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hre
    · simp [him, Complex.mul_im, (hu p).1]
  have hα0 : α ≠ 0 := by intro h; simpa [h] using hα
  have hzline : z = (α⁻¹ * (M : ℂ)) • u := by
    have ht := congrArg (fun g : C(Q, ℂ) => α⁻¹ • g) heq
    simpa only [smul_smul, inv_mul_cancel₀ hα0, one_smul] using ht
  have hzeq : ζ • z = (r : ℂ) • z := by
    calc
      ζ • z = K z := hKz.symm
      _ = (r : ℂ) • z := by
        rw [hzline, K.map_smul, hKu]
        simp only [smul_smul, mul_comm]
  exact ⟨(smul_left_injective ℂ hz) hzeq, ⟨_, hzline⟩⟩



/-- A dual eigenfunctional nonzero on an eigenline rules out every Jordan
chain. The induction works on the actual infinite-dimensional space. -/
lemma power_kernel_eq_eigenline {E : Type*} [AddCommGroup E] [Module ℂ E]
    (A : E →ₗ[ℂ] E) (u : E) (φ : E →ₗ[ℂ] ℂ)
    (hker : LinearMap.ker A = Submodule.span ℂ {u})
    (hφA : ∀ x, φ (A x) = 0) (hφu : φ u ≠ 0) :
    ∀ n : ℕ, 0 < n → LinearMap.ker (A ^ n) = Submodule.span ℂ {u} := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ n ih =>
    intro _
    by_cases hn : n = 0
    · subst n
      simpa using hker
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    ext x
    constructor
    · intro hx
      have hAx : A x ∈ LinearMap.ker (A ^ n) := by
        change (A ^ n) (A x) = 0
        simpa only [LinearMap.mem_ker, pow_succ, Module.End.mul_apply] using hx
      rw [ih hnpos] at hAx
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hAx
      have ha0 : a = 0 := by
        have ht := congrArg φ ha
        rw [map_smul, hφA, smul_eq_mul] at ht
        exact (mul_eq_zero.mp ht).resolve_right hφu
      have hxker : x ∈ LinearMap.ker A := by
        change A x = 0
        simpa [ha0] using ha.symm
      rwa [hker] at hxker
    · intro hx
      rw [← hker] at hx
      have ht := A.iterateKer.monotone (show 1 ≤ n + 1 by omega)
      exact ht (by simpa using hx)

/-- Geometric simplicity, for a prescribed strictly positive eigenpair. -/
theorem eigenline [Nonempty Q]
    (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ)) (hreal : PreservesReal K)
    (hstrong : StronglyPositive K) {r : ℝ} (hr : 0 < r)
    {u : C(Q, ℂ)} (hu : StrictlyPositive u) (hKu : K u = (r : ℂ) • u) :
    LinearMap.ker ((r : ℂ) • LinearMap.id - K.toLinearMap) =
      Submodule.span ℂ {u} := by
  ext z
  constructor
  · intro hz
    by_cases hz0 : z = 0
    · simp [hz0]
    · have he : K z = (r : ℂ) • z := by
        exact (sub_eq_zero.mp hz).symm
      obtain ⟨_, a, ha⟩ := peripheral_eigenvector K hreal hstrong hr hu hKu hz0 he
        (by simp [Complex.norm_real, abs_of_pos hr])
      exact Submodule.mem_span_singleton.mpr ⟨a, ha.symm⟩
  · intro hz
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    change (r : ℂ) • (a • u) - K (a • u) = 0
    rw [K.map_smul, hKu, smul_smul, smul_smul, mul_comm, sub_self]

/-- Full algebraic simplicity from a positive eigenpair and a dual
functional whose value there is nonzero. Existence is not assumed implicitly. -/
theorem algebraicallySimple_of_eigenfunctional [Nonempty Q]
    (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ)) (hreal : PreservesReal K)
    (hstrong : StronglyPositive K) {r : ℝ} (hr : 0 < r)
    {u : C(Q, ℂ)} (hu : StrictlyPositive u) (hKu : K u = (r : ℂ) • u)
    (φ : C(Q, ℂ) →L[ℂ] ℂ) (hφ : ∀ f, φ (K f) = (r : ℂ) * φ f)
    (hφu : φ u ≠ 0) : AlgebraicallySimple K r u := by
  apply power_kernel_eq_eigenline _ u φ.toLinearMap
    (eigenline K hreal hstrong hr hu hKu) _ hφu
  intro f
  change φ ((r : ℂ) • f - K f) = 0
  rw [map_sub, φ.map_smul, hφ, smul_eq_mul, sub_self]

/-- The strict comparison includes zero eigenvalues and requires no
integral-kernel or selfadjointness assumption. -/
theorem other_eigenvalue_norm_lt [Nonempty Q]
    (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ)) (hreal : PreservesReal K)
    (hstrong : StronglyPositive K) {r : ℝ} (hr : 0 < r)
    {u : C(Q, ℂ)} (hu : StrictlyPositive u) (hKu : K u = (r : ℂ) • u)
    {ζ : ℂ} {z : C(Q, ℂ)} (hz : z ≠ 0) (hKz : K z = ζ • z)
    (hζ : ζ ≠ (r : ℂ)) : ‖ζ‖ < r := by
  by_contra h
  exact hζ (peripheral_eigenvector K hreal hstrong hr hu hKu hz hKz
    (le_of_not_gt h)).1



/-- Assemble the comparison and Jordan-chain conclusions from their witnesses. -/
theorem conclusion_of_eigenpair_eigenmeasure : Spec.AssemblyFromWitnesses.{u} := by
  intro Q _ _ _ _ _ _ K hreal hstrong hr u φ μ hu hKu hμ hφim hφpos
  have hφu : φ u ≠ 0 := by
    intro h
    have ht := congrArg Complex.re h
    simpa [ht] using hφpos
  exact ⟨hr, u, φ, μ, hu, hKu,
    algebraicallySimple_of_eigenfunctional K hreal hstrong hr hu hKu φ hμ.2.2.2 hφu,
    hμ, hφim, hφpos, fun _ _ hz hKz hζ =>
      other_eigenvalue_norm_lt K hreal hstrong hr hu hKu hz hKz hζ⟩


/-- Modulus as a nonnegative complex-valued continuous function. -/
noncomputable def modulus (f : C(Q, ℂ)) : C(Q, ℂ) :=
  ⟨fun q => (‖f q‖ : ℂ), Complex.continuous_ofReal.comp f.continuous.norm⟩

@[simp] lemma modulus_apply (f : C(Q, ℂ)) (q : Q) :
    modulus f q = (‖f q‖ : ℂ) := rfl

lemma modulus_nonnegative (f : C(Q, ℂ)) : Nonnegative (modulus f) := by
  intro q
  exact ⟨Complex.ofReal_im _, norm_nonneg _⟩

lemma norm_eq_re_of_nonnegative {f : C(Q, ℂ)} (hf : Nonnegative f) (q : Q) :
    ‖f q‖ = (f q).re := by
  rw [← Complex.re_add_im (f q), (hf q).1]
  simp [abs_of_nonneg (hf q).2]

lemma norm_mono_nonnegative {f g : C(Q, ℂ)} (hf : Nonnegative f)
    (hg : Nonnegative g) (h : ∀ q, (f q).re ≤ (g q).re) : ‖f‖ ≤ ‖g‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro q
  rw [norm_eq_re_of_nonnegative hf q]
  exact (h q).trans ((norm_eq_re_of_nonnegative hg q).symm.le.trans
    (g.norm_coe_le_norm q))

lemma map_re_mono (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ))
    (hstrong : StronglyPositive K) {f g : C(Q, ℂ)}
    (hf : RealValued f) (hg : RealValued g) (h : ∀ q, (f q).re ≤ (g q).re) :
    ∀ q, (K f q).re ≤ (K g q).re := by
  have hp : Nonnegative (g - f) := by
    intro q
    exact ⟨by simp [hf q, hg q], sub_nonneg.mpr (h q)⟩
  have ht := stronglyPositive_nonnegative K hstrong hp
  intro q
  simpa only [map_sub, ContinuousMap.sub_apply, Complex.sub_re, sub_nonneg] using
    (ht q).2

/-- Phase rotation proves domination of the complex modulus by K|f|. -/
lemma modulus_image_le (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ))
    (hreal : PreservesReal K) (hstrong : StronglyPositive K)
    (f : C(Q, ℂ)) (q : Q) : ‖K f q‖ ≤ (K (modulus f) q).re := by
  by_cases h0 : K f q = 0
  · simpa [h0] using (stronglyPositive_nonnegative K hstrong (modulus_nonnegative f) q).2
  obtain ⟨α, hα, he⟩ := exists_norming_phase (K f q) h0
  have hle : ∀ p, (realPart (α • f) p).re ≤ (modulus f p).re := by
    intro p
    change (α * f p).re ≤ ‖f p‖
    calc
      _ ≤ ‖α * f p‖ := Complex.re_le_norm _
      _ = ‖f p‖ := by rw [norm_mul, hα, one_mul]
  have hm := map_re_mono K hstrong
    (show RealValued (realPart (α • f)) by intro p; simp)
    (show RealValued (modulus f) by intro p; simp) hle q
  rw [map_realPart K hreal, K.map_smul] at hm
  have he' := congrArg Complex.re he
  exact he'.symm.trans_le hm

/-- A pointwise subeigenvector forces a lower bound on the spectral radius. -/
lemma le_radius_of_subeigenvector [Nonempty Q]
    (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ)) (hstrong : StronglyPositive K)
    {v : C(Q, ℂ)} (hv : Nonnegative v) (hv0 : v ≠ 0)
    {a : ℝ} (ha : 0 ≤ a) (hle : ∀ q, a * (v q).re ≤ (K v q).re) :
    a ≤ radius K := by
  have hpos (n : ℕ) : Nonnegative ((K ^ n) v) := by
    induction n with
    | zero => simpa using hv
    | succ n ih =>
      simpa only [pow_succ', ContinuousLinearMap.mul_apply] using
        stronglyPositive_nonnegative K hstrong ih
  have hiter (n : ℕ) : ∀ q, a ^ n * (v q).re ≤ ((K ^ n) v q).re := by
    induction n with
    | zero => intro q; simp
    | succ n ih =>
      have hm := map_re_mono K hstrong
        (show RealValued (((a ^ n : ℝ) : ℂ) • v) by intro q; simp only [ContinuousMap.smul_apply, smul_eq_mul, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, (hv q).1, mul_zero, zero_mul, add_zero])
        (fun q => (hpos n q).1) (by intro q; simpa only [ContinuousMap.smul_apply, smul_eq_mul, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using ih q)
      intro q
      have ht := hm q
      rw [K.map_smul] at ht
      simp only [ContinuousMap.smul_apply, smul_eq_mul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at ht
      have := mul_le_mul_of_nonneg_left (hle q) (pow_nonneg ha n)
      simpa only [pow_succ', ContinuousLinearMap.mul_apply, mul_assoc, mul_left_comm] using this.trans ht
  have hbound (n : ℕ) : a ^ n ≤ ‖K ^ n‖ := by
    have hsn : Nonnegative (((a ^ n : ℝ) : ℂ) • v) := by
      intro q
      exact ⟨by simp only [ContinuousMap.smul_apply, smul_eq_mul, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, (hv q).1, mul_zero, zero_mul, add_zero],
        by simpa only [ContinuousMap.smul_apply, smul_eq_mul, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
          mul_nonneg (pow_nonneg ha n) (hv q).2⟩
    have hn := norm_mono_nonnegative hsn (hpos n) (by intro q; simpa only [ContinuousMap.smul_apply, smul_eq_mul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hiter n q)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg ha n)] at hn
    exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hv0)).mp
      (hn.trans ((K ^ n).le_opNorm v))
  have hA : Specs.ExpandedFA.BanachAlgebra.Conventions.IsUnitalBanachAlgebraValue
      (C(Q, ℂ) →L[ℂ] C(Q, ℂ)) := ⟨inferInstance, inferInstance, inferInstance⟩
  apply ge_of_tendsto (BanachAlgebra.algebraSpectralRadius_root_limit _ hA K)
  apply Filter.Eventually.of_forall
  intro n
  rw [one_div]
  apply (Real.le_rpow_inv_iff_of_pos ha (norm_nonneg _) (by positivity)).mpr
  simpa only [Real.rpow_natCast] using hbound (n + 1)

lemma radius_pos [Nonempty Q] (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ))
    (hstrong : StronglyPositive K) : 0 < radius K := by
  have h1 : Nonnegative (1 : C(Q, ℂ)) := by intro q; simp
  have hK1 := hstrong 1 h1 one_ne_zero
  obtain ⟨c, hc, hbound⟩ := strictlyPositive_uniform_lower_bound hK1
  exact hc.trans_le (le_radius_of_subeigenvector K hstrong h1 one_ne_zero hc.le
    (by simpa using hbound))


lemma modulus_ne_zero {f : C(Q, ℂ)} (hf : f ≠ 0) : modulus f ≠ 0 := by
  intro h
  apply hf
  ext q
  have ht := congrArg (fun g : C(Q, ℂ) => (g q).re) h
  simpa using ht

/-- The modulus of a peripheral eigenvector is an eigenfunction. If its
nonnegative defect were nonzero, strong positivity would increase the radius. -/
lemma modulus_eigenfunction [Nonempty Q]
    (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ)) (hreal : PreservesReal K)
    (hstrong : StronglyPositive K) {ζ : ℂ} {z : C(Q, ℂ)}
    (hz : z ≠ 0) (hKz : K z = ζ • z) (hζ : ‖ζ‖ = radius K) :
    StrictlyPositive (modulus z) ∧ K (modulus z) = (radius K : ℂ) • modulus z := by
  let y := modulus z
  let r := radius K
  have hr : 0 < r := radius_pos K hstrong
  have hy : Nonnegative y := modulus_nonnegative z
  have hy0 : y ≠ 0 := modulus_ne_zero hz
  have hv : StrictlyPositive (K y) := hstrong y hy hy0
  let h := K y - (r : ℂ) • y
  have hh : Nonnegative h := by
    intro q
    constructor
    · change (K y q).im - ((r : ℂ) * y q).im = 0
      simp [Complex.mul_im, (hv q).1, (hy q).1]
    · have ht := modulus_image_le K hreal hstrong z q
      rw [hKz] at ht
      change ‖ζ * z q‖ ≤ (K y q).re at ht
      rw [norm_mul, hζ] at ht
      change 0 ≤ (K y q).re - ((r : ℂ) * y q).re
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, y, modulus_apply, Complex.ofReal_re, sub_nonneg] using ht
  have hh0 : h = 0 := by
    by_contra hh0
    obtain ⟨δ, hδ, hδbound⟩ := strictlyPositive_uniform_lower_bound (hstrong h hh hh0)
    have hv0 : K y ≠ 0 := strictlyPositive_ne_zero hv
    have hn : 0 < ‖K y‖ := norm_pos_iff.mpr hv0
    have he : K (K y) = (r : ℂ) • K y + K h := by
      dsimp [h]
      rw [map_sub, K.map_smul_of_tower]
      abel
    have hsub : ∀ q, (r + δ / ‖K y‖) * (K y q).re ≤ (K (K y) q).re := by
      intro q
      have hb : (K y q).re ≤ ‖K y‖ :=
        (Complex.re_le_norm _).trans ((K y).norm_coe_le_norm q)
      have ht := mul_le_mul_of_nonneg_left hb (div_nonneg hδ.le hn.le)
      rw [div_mul_cancel₀ _ hn.ne'] at ht
      rw [he]
      change (r + δ / ‖K y‖) * (K y q).re ≤
        ((r : ℂ) * K y q).re + (K h q).re
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero]
      nlinarith [hδbound q]
    have ht := le_radius_of_subeigenvector K hstrong
      (fun q => ⟨(hv q).1, (hv q).2.le⟩) hv0
      (show 0 ≤ r + δ / ‖K y‖ by positivity) hsub
    have hd : 0 < δ / ‖K y‖ := div_pos hδ hn
    change r + δ / ‖K y‖ ≤ r at ht
    linarith
  have heig : K y = (r : ℂ) • y := sub_eq_zero.mp hh0
  refine ⟨?_, heig⟩
  intro q
  refine ⟨(hy q).1, ?_⟩
  have ht := (hv q).2
  rw [heig] at ht
  change 0 < ((r : ℂ) * y q).re at ht
  have ht' : 0 < r * (y q).re := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero] using ht
  exact (mul_pos_iff_of_pos_left hr).mp ht'


/-- Existence at the actual spectral radius under the source hypotheses. -/
theorem positive_eigenfunction [Nonempty Q]
    (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ)) (hcompact : IsCompactOperator K)
    (hreal : PreservesReal K) (hstrong : StronglyPositive K) :
    0 < radius K ∧ ∃ u : C(Q, ℂ), StrictlyPositive u ∧
      K u = (radius K : ℂ) • u := by
  have hr := radius_pos K hstrong
  have hA : Specs.ExpandedFA.BanachAlgebra.Conventions.IsUnitalBanachAlgebraValue
      (C(Q, ℂ) →L[ℂ] C(Q, ℂ)) := ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨⟨ζ, hζ, hnorm⟩, _⟩ := BanachAlgebra.algebraSpectralRadius_maximum _ hA K
  have hζ0 : ζ ≠ 0 := by
    intro h
    have ht : ‖ζ‖ = radius K := hnorm
    rw [h, norm_zero] at ht
    linarith
  have hc : Compactness.IsCompactLinearMap K.toLinearMap :=
    (Compactness.compact_iff_isCompactOperator K.toLinearMap).mpr hcompact
  obtain ⟨z, hz, hKz⟩ :=
    (Fredholm.compact_nonzero_spectrum_iff_eigenvalue K hc ζ hζ0).mp hζ
  exact ⟨hr, modulus z, modulus_eigenfunction K hreal hstrong hz hKz hnorm⟩


/-- A fixed strictly positive order unit bounds every power in the original
supremum norm. This estimate does not use metrizability of Q. -/
lemma powers_bounded_of_positive_fixed [Nonempty Q]
    (T : C(Q, ℂ) →L[ℂ] C(Q, ℂ)) (hreal : PreservesReal T)
    (hstrong : StronglyPositive T) {u : C(Q, ℂ)}
    (hu : StrictlyPositive u) (hTu : T u = u) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖T ^ n‖ ≤ C := by
  obtain ⟨c, hc, hcu⟩ := strictlyPositive_uniform_lower_bound hu
  refine ⟨‖u‖ / c, div_pos (norm_pos_iff.mpr (strictlyPositive_ne_zero hu)) hc, ?_⟩
  intro n
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  have hb : ∀ n : ℕ, ∀ q, ‖(T ^ n) f q‖ ≤ (‖f‖ / c) * (u q).re := by
    intro n
    induction n with
    | zero =>
      intro q
      have ht := mul_le_mul_of_nonneg_left (hcu q) (div_nonneg (norm_nonneg f) hc.le)
      rw [div_mul_cancel₀ _ hc.ne'] at ht
      exact (f.norm_coe_le_norm q).trans (by simpa using ht)
    | succ n ih =>
      have hm := map_re_mono T hstrong
        (show RealValued (modulus ((T ^ n) f)) by intro q; simp)
        (show RealValued (((‖f‖ / c : ℝ) : ℂ) • u) by
          intro q
          simp only [ContinuousMap.smul_apply, smul_eq_mul, Complex.mul_im,
            Complex.ofReal_im, Complex.ofReal_re, (hu q).1, mul_zero, zero_mul, add_zero])
        (by intro q; simpa only [modulus_apply, ContinuousMap.smul_apply,
          smul_eq_mul, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
          zero_mul, sub_zero] using ih q)
      intro q
      have ht := hm q
      rw [T.map_smul, hTu] at ht
      have ht' := (modulus_image_le T hreal hstrong ((T ^ n) f) q).trans ht
      simpa only [pow_succ', ContinuousLinearMap.mul_apply,
        ContinuousMap.smul_apply, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero] using ht'
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro q
  have ht := mul_le_mul_of_nonneg_left
    ((Complex.re_le_norm (u q)).trans (u.norm_coe_le_norm q))
    (div_nonneg (norm_nonneg f) hc.le)
  calc
    ‖(T ^ n) f q‖ ≤ (‖f‖ / c) * (u q).re := hb n q
    _ ≤ (‖f‖ / c) * ‖u‖ := ht
    _ = (‖u‖ / c) * ‖f‖ := by ring

/-- Positive powers stay in the real cone. -/
lemma powers_nonnegative (T : C(Q, ℂ) →L[ℂ] C(Q, ℂ))
    (hstrong : StronglyPositive T) {f : C(Q, ℂ)} (hf : Nonnegative f) (n : ℕ) :
    Nonnegative ((T ^ n) f) := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    simpa only [pow_succ', ContinuousLinearMap.mul_apply] using
      stronglyPositive_nonnegative T hstrong ih

noncomputable def cesaroEvaluation (T : C(Q, ℂ) →L[ℂ] C(Q, ℂ)) (q : Q)
    (n : ℕ) : C(Q, ℂ) →L[ℂ] ℂ :=
  ((n + 1 : ℂ)⁻¹) • ∑ j ∈ Finset.range (n + 1),
    (ContinuousMap.evalCLM (R := ℂ) q).comp (T ^ j)

lemma cesaroEvaluation_apply (T : C(Q, ℂ) →L[ℂ] C(Q, ℂ)) (q : Q)
    (n : ℕ) (f : C(Q, ℂ)) :
    cesaroEvaluation T q n f = ((n + 1 : ℂ)⁻¹) *
      ∑ j ∈ Finset.range (n + 1), (T ^ j) f q := by
  simp [cesaroEvaluation, ContinuousLinearMap.sum_apply]

lemma cesaroEvaluation_fixed (T : C(Q, ℂ) →L[ℂ] C(Q, ℂ))
    {u : C(Q, ℂ)} (hTu : T u = u) (q : Q) (n : ℕ) :
    cesaroEvaluation T q n u = u q := by
  have hp (j : ℕ) : (T ^ j) u = u := by
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ', ContinuousLinearMap.mul_apply, ih, hTu]
  rw [cesaroEvaluation_apply]
  simp only [hp, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [Nat.cast_add, Nat.cast_one, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast
    (Nat.succ_ne_zero n)), one_mul]

lemma cesaroEvaluation_nonnegative (T : C(Q, ℂ) →L[ℂ] C(Q, ℂ))
    (hstrong : StronglyPositive T) {f : C(Q, ℂ)} (hf : Nonnegative f)
    (q : Q) (n : ℕ) :
    (cesaroEvaluation T q n f).im = 0 ∧ 0 ≤ (cesaroEvaluation T q n f).re := by
  have hp (j : ℕ) := powers_nonnegative T hstrong hf j q
  have him : (∑ j ∈ Finset.range (n + 1), (T ^ j) f q).im = 0 := by
    simp only [map_sum, Complex.imCLM_apply, Complex.im_sum]
    exact Finset.sum_eq_zero fun j _ => (hp j).1
  have hre : 0 ≤ (∑ j ∈ Finset.range (n + 1), (T ^ j) f q).re := by
    rw [Complex.re_sum]
    exact Finset.sum_nonneg fun j _ => (hp j).2
  rw [cesaroEvaluation_apply]
  have hn : 0 < (n + 1 : ℝ) := by positivity
  have hcast : (n + 1 : ℂ) = ((n + 1 : ℝ) : ℂ) := by simp
  rw [hcast, ← Complex.ofReal_inv]
  constructor
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, him,
      mul_zero, zero_mul, add_zero]
  · simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using mul_nonneg (inv_nonneg.mpr hn.le) hre

lemma cesaroEvaluation_norm_le (T : C(Q, ℂ) →L[ℂ] C(Q, ℂ))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ j : ℕ, ‖T ^ j‖ ≤ C) (q : Q) (n : ℕ) :
    ‖cesaroEvaluation T q n‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  have hnorm : ‖(n + 1 : ℂ)‖ = (n + 1 : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n + 1)
  rw [cesaroEvaluation_apply, norm_mul, norm_inv, hnorm]
  have hsum : ‖∑ j ∈ Finset.range (n + 1), (T ^ j) f q‖ ≤ (n + 1 : ℝ) * (C * ‖f‖) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (n + 1), ‖(T ^ j) f q‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range (n + 1), C * ‖f‖ :=
        Finset.sum_le_sum fun j _ => ((T ^ j) f).norm_coe_le_norm q |>.trans
          (((T ^ j).le_opNorm f).trans (mul_le_mul_of_nonneg_right (hb j) (norm_nonneg f)))
      _ = _ := by simp
  have ht := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (show 0 ≤ (n + 1 : ℝ) by positivity))
  simpa only [← mul_assoc, inv_mul_cancel₀ (show (n + 1 : ℝ) ≠ 0 by positivity), one_mul] using ht


lemma cesaroEvaluation_difference (T : C(Q, ℂ) →L[ℂ] C(Q, ℂ))
    (q : Q) (n : ℕ) (f : C(Q, ℂ)) :
    cesaroEvaluation T q n (T f) - cesaroEvaluation T q n f =
      ((n + 1 : ℂ)⁻¹) * ((T ^ (n + 1)) f q - f q) := by
  have htele (m : ℕ) :
      (∑ j ∈ Finset.range m, ((T ^ j) (T f) q - (T ^ j) f q)) =
        (T ^ m) f q - f q := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      rw [pow_succ, ContinuousLinearMap.mul_apply]
      ring
  rw [cesaroEvaluation_apply, cesaroEvaluation_apply, ← mul_sub,
    ← Finset.sum_sub_distrib, htele]

lemma cesaroEvaluation_asymptotic (T : C(Q, ℂ) →L[ℂ] C(Q, ℂ))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ j : ℕ, ‖T ^ j‖ ≤ C)
    (q : Q) (f : C(Q, ℂ)) :
    Filter.Tendsto (fun n : ℕ => cesaroEvaluation T q n (T f) -
      cesaroEvaluation T q n f) Filter.atTop (nhds 0) := by
  have hnorm : ∀ n : ℕ, ‖(n + 1 : ℂ)‖ = (n + 1 : ℝ) := by
    intro n
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n + 1)
  have ht : Filter.Tendsto (fun n : ℕ => (n + 1 : ℝ)⁻¹ * ((C + 1) * ‖f‖))
      Filter.atTop (nhds 0) := by
    simpa only [one_div, zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const ((C + 1) * ‖f‖)
  apply squeeze_zero_norm _ ht
  intro n
  rw [cesaroEvaluation_difference, norm_mul, norm_inv, hnorm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    ‖(T ^ (n + 1)) f q - f q‖ ≤ ‖(T ^ (n + 1)) f q‖ + ‖f q‖ := norm_sub_le _ _
    _ ≤ C * ‖f‖ + ‖f‖ := add_le_add
      (((T ^ (n + 1)) f).norm_coe_le_norm q |>.trans
        (((T ^ (n + 1)).le_opNorm f).trans
          (mul_le_mul_of_nonneg_right (hb (n + 1)) (norm_nonneg f))))
      (f.norm_coe_le_norm q)
    _ = (C + 1) * ‖f‖ := by ring

/-- Banach--Alaoglu applied to bounded Cesàro evaluations gives a positive
invariant functional nonzero on the fixed order unit. No sequential compactness
of the weak dual, and no countability hypothesis on Q, is used. -/
theorem positive_invariant_functional [Nonempty Q]
    (T : C(Q, ℂ) →L[ℂ] C(Q, ℂ)) (hreal : PreservesReal T)
    (hstrong : StronglyPositive T) {u : C(Q, ℂ)}
    (hu : StrictlyPositive u) (hTu : T u = u) :
    ∃ φ : C(Q, ℂ) →L[ℂ] ℂ,
      (∀ f, Nonnegative f → (φ f).im = 0 ∧ 0 ≤ (φ f).re) ∧
      (∀ f, φ (T f) = φ f) ∧ (φ u).im = 0 ∧ 0 < (φ u).re := by
  obtain ⟨C, hC, hb⟩ := powers_bounded_of_positive_fixed T hreal hstrong hu hTu
  let q : Q := Classical.choice ‹Nonempty Q›
  let ψ : ℕ → WeakDual ℂ C(Q, ℂ) :=
    fun n => StrongDual.toWeakDual (cesaroEvaluation T q n)
  have hc := WeakDual.isCompact_closedBall (0 : C(Q, ℂ) →L[ℂ] ℂ) C
  obtain ⟨φ, _, hφ⟩ := hc.exists_mapClusterPt (u := ψ) (f := Filter.atTop)
    (Filter.tendsto_principal.mpr (Filter.Eventually.of_forall (fun n => by
      change dist (cesaroEvaluation T q n) 0 ≤ C
      simpa only [dist_zero_right] using cesaroEvaluation_norm_le T hC.le hb q n)))
  have hcl : ClusterPt φ (Filter.map ψ Filter.atTop) := hφ
  haveI : Filter.NeBot (nhds φ ⊓ Filter.map ψ Filter.atTop) := hcl
  have hval (f : C(Q, ℂ)) :
      Filter.Tendsto (fun θ : WeakDual ℂ C(Q, ℂ) => θ f)
        (nhds φ ⊓ Filter.map ψ Filter.atTop) (nhds (φ f)) :=
    (WeakDual.eval_continuous f).continuousAt.tendsto.mono_left inf_le_left
  refine ⟨WeakDual.toStrongDual φ, ?_, ?_, ?_, ?_⟩
  · intro f hf
    have hclosed : IsClosed {θ : WeakDual ℂ C(Q, ℂ) |
        (θ f).im = 0 ∧ 0 ≤ (θ f).re} :=
      (isClosed_eq (Complex.continuous_im.comp (WeakDual.eval_continuous f)) continuous_const).inter
        (isClosed_le continuous_const (Complex.continuous_re.comp (WeakDual.eval_continuous f)))
    exact hclosed.mem_of_mapClusterPt hφ (Filter.Eventually.of_forall
      (fun n => cesaroEvaluation_nonnegative T hstrong hf q n))
  · intro f
    have hg := cesaroEvaluation_asymptotic T hC.le hb q f
    have hg' : Filter.Tendsto (fun θ : WeakDual ℂ C(Q, ℂ) => θ (T f) - θ f)
        (Filter.map ψ Filter.atTop) (nhds 0) := Filter.tendsto_map'_iff.mpr hg
    exact sub_eq_zero.mp (tendsto_nhds_unique ((hval (T f)).sub (hval f))
      (hg'.mono_left inf_le_right))
  · have hconst : Filter.Tendsto (fun θ : WeakDual ℂ C(Q, ℂ) => θ u)
        (Filter.map ψ Filter.atTop) (nhds (u q)) := by
      apply Filter.tendsto_map'_iff.mpr
      simpa only [Function.comp_def, ψ, StrongDual.toWeakDual_apply,
        cesaroEvaluation_fixed T hTu] using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => u q) Filter.atTop (nhds (u q)))
    have he := tendsto_nhds_unique (hval u) (hconst.mono_left inf_le_right)
    exact he ▸ (hu q).1
  · have heq : φ u = u q := by
      have hclosed : IsClosed {θ : WeakDual ℂ C(Q, ℂ) | θ u = u q} :=
        isClosed_eq (WeakDual.eval_continuous u) continuous_const
      exact hclosed.mem_of_mapClusterPt hφ
        (Filter.Eventually.of_forall (fun n => cesaroEvaluation_fixed T hTu q n))
    exact heq ▸ (hu q).2


/-- Rescale a positive eigenpair to a fixed order unit, and recover the
original (scalar-linear) transpose eigen-equation. -/
lemma positive_eigenfunctional [Nonempty Q]
    (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ)) (hreal : PreservesReal K)
    (hstrong : StronglyPositive K) {r : ℝ} (hr : 0 < r)
    {u : C(Q, ℂ)} (hu : StrictlyPositive u) (hKu : K u = (r : ℂ) • u) :
    ∃ φ : C(Q, ℂ) →L[ℂ] ℂ,
      (∀ f, Nonnegative f → (φ f).im = 0 ∧ 0 ≤ (φ f).re) ∧
      (∀ f, φ (K f) = (r : ℂ) * φ f) ∧ (φ u).im = 0 ∧ 0 < (φ u).re := by
  let T : C(Q, ℂ) →L[ℂ] C(Q, ℂ) := ((r⁻¹ : ℝ) : ℂ) • K
  have hTr : PreservesReal T := by
    intro f hf q
    change (((r⁻¹ : ℝ) : ℂ) * K f q).im = 0
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hreal f hf q,
      mul_zero, zero_mul, add_zero]
  have hTs : StronglyPositive T := by
    intro f hf hf0 q
    obtain ⟨him, hre⟩ := hstrong f hf hf0 q
    constructor
    · change (((r⁻¹ : ℝ) : ℂ) * K f q).im = 0
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, him,
        mul_zero, zero_mul, add_zero]
    · change 0 < (((r⁻¹ : ℝ) : ℂ) * K f q).re
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero] using mul_pos (inv_pos.mpr hr) hre
  have hTu : T u = u := by
    change ((r⁻¹ : ℝ) : ℂ) • K u = u
    rw [hKu, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hr.ne', Complex.ofReal_one,
      one_smul]
  obtain ⟨φ, hφpos, hφT, hφim, hφu⟩ := positive_invariant_functional T hTr hTs hu hTu
  refine ⟨φ, hφpos, ?_, hφim, hφu⟩
  intro f
  have hKf : K f = (r : ℂ) • T f := by
    change K f = (r : ℂ) • (((r⁻¹ : ℝ) : ℂ) • K f)
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne', Complex.ofReal_one, one_smul]
  rw [hKf, φ.map_smul, hφT, smul_eq_mul]

lemma positive_functional_one_pos [Nonempty Q]
    (φ : C(Q, ℂ) →L[ℂ] ℂ)
    (hφ : ∀ f, Nonnegative f → (φ f).im = 0 ∧ 0 ≤ (φ f).re)
    {u : C(Q, ℂ)} (hu : StrictlyPositive u) (hφu : 0 < (φ u).re) :
    0 < (φ 1).re := by
  have hf : Nonnegative ((‖u‖ : ℂ) • (1 : C(Q, ℂ)) - u) := by
    intro q
    constructor
    · simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
        smul_eq_mul, mul_one, Complex.sub_im, Complex.ofReal_im, (hu q).1, sub_self]
    · change 0 ≤ ((‖u‖ : ℂ) * 1).re - (u q).re
      simpa only [mul_one, Complex.ofReal_re, sub_nonneg] using
        (Complex.re_le_norm (u q)).trans (u.norm_coe_le_norm q)
  have ht := (hφ _ hf).2
  rw [map_sub, φ.map_smul] at ht
  change 0 ≤ ((‖u‖ : ℂ) * φ 1).re - (φ u).re at ht
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at ht
  by_contra h
  have hn := mul_nonpos_of_nonneg_of_nonpos (norm_nonneg u) (le_of_not_gt h)
  linarith

/-- Normalize before invoking Riesz--Markov, so the representing positive
Radon measure has mass one without any measure-scaling convention. -/
theorem eigenmeasure_of_positive_eigenpair [T2Space Q] [Nonempty Q]
    [MeasurableSpace Q] [BorelSpace Q]
    (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ)) (hreal : PreservesReal K)
    (hstrong : StronglyPositive K) {r : ℝ} (hr : 0 < r)
    {u : C(Q, ℂ)} (hu : StrictlyPositive u) (hKu : K u = (r : ℂ) • u) :
    ∃ (φ : C(Q, ℂ) →L[ℂ] ℂ) (μ : MeasureTheory.Measure Q),
      Eigenmeasure K r φ μ ∧ (φ u).im = 0 ∧ 0 < (φ u).re := by
  obtain ⟨ψ, hψpos, hψeig, hψim, hψu⟩ :=
    positive_eigenfunctional K hreal hstrong hr hu hKu
  let d : ℝ := (ψ 1).re
  have hd : 0 < d := positive_functional_one_pos ψ hψpos hu hψu
  have hψ1im : (ψ 1).im = 0 := (hψpos 1 (by intro q; simp)).1
  have hψ1 : ψ 1 = (d : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using hψ1im
  let φ : C(Q, ℂ) →L[ℂ] ℂ := ((d⁻¹ : ℝ) : ℂ) • ψ
  have hφ1 : φ 1 = 1 := by
    change ((d⁻¹ : ℝ) : ℂ) * ψ 1 = 1
    rw [hψ1, ← Complex.ofReal_mul, inv_mul_cancel₀ hd.ne', Complex.ofReal_one]
  have hφpos : ∀ f, Nonnegative f → (φ f).im = 0 ∧ 0 ≤ (φ f).re := by
    intro f hf
    obtain ⟨him, hre⟩ := hψpos f hf
    change ((((d⁻¹ : ℝ) : ℂ) * ψ f).im = 0 ∧
      0 ≤ (((d⁻¹ : ℝ) : ℂ) * ψ f).re)
    constructor
    · simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, him,
        zero_mul, mul_zero, add_zero]
    · simpa only [Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, zero_mul,
        sub_zero] using mul_nonneg (inv_nonneg.mpr hd.le) hre
  have hφeig : ∀ f, φ (K f) = (r : ℂ) * φ f := by
    intro f
    change ((d⁻¹ : ℝ) : ℂ) * ψ (K f) = (r : ℂ) * (((d⁻¹ : ℝ) : ℂ) * ψ f)
    rw [hψeig]
    ring
  obtain ⟨e, he, hes⟩ := FunctionSpaces.ScalarRieszMarkov.compact_identification Q ℂ
  let L : C₀(Q, ℂ) →L[ℂ] ℂ :=
    φ.comp e.symm.toLinearIsometry.toContinuousLinearMap
  have hL : ∀ f : C₀(Q, ℂ), (∀ q, (f q).im = 0 ∧ 0 ≤ (f q).re) →
      (L f).im = 0 ∧ 0 ≤ (L f).re := by
    intro f hf
    change (φ (e.symm f)).im = 0 ∧ 0 ≤ (φ (e.symm f)).re
    apply hφpos (e.symm f)
    intro q
    simpa only [hes] using hf q
  obtain ⟨μ, hμ, hfinite, hrep, _⟩ :=
    FunctionSpaces.ScalarRieszMarkov.complex_positive_representation Q L hL
  haveI : MeasureTheory.IsFiniteMeasure μ := ⟨hfinite⟩
  have hrep' (f : C(Q, ℂ)) : MeasureTheory.Integrable f μ ∧ φ f = ∫ q, f q ∂μ := by
    have ht := hrep (e f)
    have hfun : (fun q => e f q) = (fun q => f q) := funext (he f)
    have hLf : L (e f) = φ f := by
      change φ (e.symm (e f)) = φ f
      rw [e.symm_apply_apply]
    rw [hLf] at ht
    simpa only [hfun] using ht
  have hmass : μ Set.univ = 1 := by
    have ht := (hrep' 1).2
    rw [hφ1] at ht
    have ht' : (μ.real Set.univ : ℂ) = 1 := by
      simpa only [ContinuousMap.one_apply, MeasureTheory.integral_const,
        Complex.real_smul, mul_one] using ht.symm
    have hrealmass : μ.real Set.univ = 1 := by
      simpa only [Complex.ofReal_re, Complex.one_re] using congrArg Complex.re ht'
    calc
      μ Set.univ = ENNReal.ofReal (μ.real Set.univ) := (ENNReal.ofReal_toReal hfinite.ne).symm
      _ = 1 := by rw [hrealmass]; exact ENNReal.ofReal_one
  refine ⟨φ, μ, ⟨hμ, hmass, hrep', hφeig⟩, ?_, ?_⟩
  · change (((d⁻¹ : ℝ) : ℂ) * ψ u).im = 0
    simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, hψim,
      zero_mul, mul_zero, add_zero]
  · change 0 < (((d⁻¹ : ℝ) : ℂ) * ψ u).re
    simpa only [Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, zero_mul,
      sub_zero] using mul_pos (inv_pos.mpr hd) hψu

/-- Strong order positivity on complex C(Q): the full assigned eigenstructure. -/
theorem eigenstructure : Spec.EigenstructureTheorem.{u} := by
  intro Q _ _ _ _ _ _ K hcompact hreal hstrong
  obtain ⟨hr, u, hu, hKu⟩ := positive_eigenfunction K hcompact hreal hstrong
  obtain ⟨φ, μ, hμ, hφim, hφpos⟩ :=
    eigenmeasure_of_positive_eigenpair K hreal hstrong hr hu hKu
  exact conclusion_of_eigenpair_eigenmeasure Q K hreal hstrong hr u φ μ hu hKu hμ hφim hφpos


end ExpandedFA.OrderedSpectral.PerronEigenstructure
