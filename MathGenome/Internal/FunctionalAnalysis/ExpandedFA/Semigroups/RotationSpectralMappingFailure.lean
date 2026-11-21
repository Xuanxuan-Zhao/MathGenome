import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.RotationSpectralMappingFailure
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.SpectralInclusion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.TorusFourierBasis
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.Spectrum

noncomputable section
open MeasureTheory Filter
open scoped Real ENNReal Topology NNReal

namespace ExpandedFA.Semigroups.RotationSpectralMappingFailure
open RotationSpectralMappingFailureSpec

lemma rotation_apply_ae (t : ℝ) (f : H) :
    (rotation t f : AngularCircle → ℂ) =ᵐ[AddCircle.haarAddCircle]
      fun θ => f ((t : AngularCircle) + θ) :=
  Lp.coeFn_compMeasurePreserving f _

lemma rotation_zero : rotation 0 = ContinuousLinearMap.id ℂ H := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [rotation_apply_ae 0 f] with θ hθ
  simpa using hθ

lemma rotation_add (t s : ℝ) : rotation (t + s) = (rotation t).comp (rotation s) := by
  apply ContinuousLinearMap.ext
  intro f
  change Lp.compMeasurePreserving (fun θ : AngularCircle => ((t + s : ℝ) : AngularCircle) + θ) _ f =
    Lp.compMeasurePreserving (fun θ : AngularCircle => (t : AngularCircle) + θ) _
      (Lp.compMeasurePreserving (fun θ : AngularCircle => (s : AngularCircle) + θ) _ f)
  rw [← Lp.compMeasurePreserving_comp_apply]
  congr 2
  funext θ
  simp [add_assoc, add_left_comm]

lemma rotation_continuous (f : H) : Continuous (fun t : ℝ => rotation t f) := by
  let g (t : ℝ) : C(AngularCircle, AngularCircle) :=
    ⟨fun θ => (t : AngularCircle) + θ, by fun_prop⟩
  have hg : Continuous g := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : ℝ × AngularCircle => (p.1 : AngularCircle) + p.2)
    fun_prop
  exact continuous_const.compMeasurePreservingLp hg
    (fun t => measurePreserving_add_left AddCircle.haarAddCircle (t : AngularCircle)) (by simp)

def rotationSemigroup : C0Semigroup ℂ H where
  operators t := rotation t
  at_zero := rotation_zero
  add_time t s := by simpa only [NNReal.coe_add] using rotation_add t s
  strong_zero f := by
    have h := (rotation_continuous f).comp (NNReal.continuous_coe.comp continuous_real_toNNReal)
    simpa [Function.comp_def, rotation_zero] using
      (h.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))

theorem rotation_model : RotationModel := ⟨rotationSemigroup, fun _ => rfl⟩

lemma rotation_period : rotation (2 * π) = ContinuousLinearMap.id ℂ H := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [rotation_apply_ae (2 * π) f] with θ hθ
  simpa only [AddCircle.coe_period, zero_add, ContinuousLinearMap.id_apply] using hθ

lemma rotation_norm (t : ℝ) (f : H) : ‖rotation t f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving _ _

def rotationEquiv (t : ℝ) : H ≃ₗᵢ[ℂ] H where
  toLinearEquiv :=
    { (rotation t).toLinearMap with
      invFun := rotation (-t)
      left_inv := fun f => by
        have h := congrArg (fun U : H →L[ℂ] H => U f) (rotation_add (-t) t)
        simpa [rotation_zero] using h.symm
      right_inv := fun f => by
        have h := congrArg (fun U : H →L[ℂ] H => U f) (rotation_add t (-t))
        simpa [rotation_zero] using h.symm }
  norm_map' := rotation_norm t

lemma rotation_spectrum_subset (t : ℝ) :
    _root_.spectrum ℂ (rotation t) ⊆ unitCircle := by
  have hu := (Unitary.linearIsometryEquiv.symm (rotationEquiv t)).property
  exact fun z hz => spectrum.norm_eq_one_of_unitary hu hz

lemma rotation_mode (t : ℝ) (n : ℤ) :
    rotation t (fourierLp (T := 2 * π) 2 n) =
      Complex.exp (Complex.I * n * t) • fourierLp (T := 2 * π) 2 n := by
  apply Lp.ext
  filter_upwards [rotation_apply_ae t (fourierLp (T := 2 * π) 2 n),
    (measurePreserving_add_left AddCircle.haarAddCircle (t : AngularCircle)).quasiMeasurePreserving.ae
      (coeFn_fourierLp (T := 2 * π) 2 n),
    Lp.coeFn_smul (Complex.exp (Complex.I * n * t)) (fourierLp (T := 2 * π) 2 n),
    coeFn_fourierLp (T := 2 * π) 2 n] with θ hθ hshift hsmul hmode
  rw [hθ, hshift, hsmul, Pi.smul_apply, hmode, smul_eq_mul]
  rw [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]
  rw [← fourier_apply, ExpandedFA.Fourier.TorusFourierBasis.modes.1]
  rfl

lemma mode_ne_zero (n : ℤ) : (fourierLp (T := 2 * π) 2 n : H) ≠ 0 :=
  (orthonormal_fourier (T := 2 * π)).ne_zero n

local instance : Nontrivial H := ⟨⟨fourierLp (T := 2 * π) 2 0, 0, mode_ne_zero 0⟩⟩

lemma mode_mem_time_spectrum (t : ℝ) (n : ℤ) :
    Complex.exp (Complex.I * n * t) ∈ _root_.spectrum ℂ (rotation t) := by
  apply spectrum.mem_iff.mpr
  rintro ⟨u, hu⟩
  let e : H := fourierLp (T := 2 * π) 2 n
  have he : (u : H →L[ℂ] H) e = 0 := by
    rw [hu]
    change Complex.exp (Complex.I * n * t) • e - rotation t e = 0
    rw [rotation_mode, sub_self]
  exact mode_ne_zero n ((ContinuousLinearEquiv.ofUnit u).injective (he.trans (map_zero _).symm))

lemma mode_generator_limit (T : C0Semigroup ℂ H)
    (hT : ∀ t, T.operators t = rotation t) (n : ℤ) :
    C0SemigroupSpec.hasGeneratorLimitValue T (fourierLp (T := 2 * π) 2 n)
      ((Complex.I * n) • fourierLp (T := 2 * π) 2 n) := by
  let e : H := fourierLp (T := 2 * π) 2 n
  have hd : HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * n * t) • e)
      ((Complex.I * n) • e) 0 := by
    simpa only [ExpandedFA.Fourier.TorusFourierBasis.modes.1, Complex.ofReal_zero,
      mul_zero, Complex.exp_zero, mul_one] using
      (ExpandedFA.Fourier.TorusFourierBasis.mode_derivatives.1 n 0).smul_const e
  have hl := hd.tendsto_slope_zero_right
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp only [C0SemigroupSpec.differenceQuotientValue, smul_apply,
    sub_apply, ContinuousLinearMap.id_apply, hT,
    Real.toNNReal_of_nonneg (le_of_lt hh), rotation_mode, zero_add, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, one_smul, RCLike.real_smul_eq_coe_smul (K := ℂ),
    map_inv₀]
  rfl

lemma mode_mem_generator_spectrum (T : C0Semigroup ℂ H)
    (hT : ∀ t, T.operators t = rotation t) (n : ℤ) :
    Complex.I * n ∈ C0SemigroupSpec.spectrumValue (C0SemigroupSpec.generatorValue T) := by
  let e : H := fourierLp (T := 2 * π) 2 n
  have hl := mode_generator_limit T hT n
  let x : (C0SemigroupSpec.generatorValue T).domain := ⟨e, _, hl⟩
  have hx : C0SemigroupSpec.generatorValue T x = (Complex.I * n) • e :=
    tendsto_nhds_unique (generator_has_limit T x) hl
  rintro ⟨R⟩
  have h := R.left_inverse x
  rw [hx, sub_self, map_zero] at h
  exact mode_ne_zero n h.symm

/-- Periodicity and the general spectral inclusion exclude every nonintegral
imaginary frequency; the Fourier-mode derivatives supply all integral ones. -/
theorem generator_spectrum : GeneratorSpectrum := by
  intro T hT
  apply Set.Subset.antisymm
  · intro z hz
    let τ : ℝ≥0 := ⟨2 * π, by positivity⟩
    have hτ : 0 < τ := by change (0 : ℝ) < 2 * π; positivity
    have hm := SpectralInclusion.spectral_inclusion T τ hτ ⟨z, hz, rfl⟩
    have hs : _root_.spectrum ℂ (ContinuousLinearMap.id ℂ H) = {1} := by
      change _root_.spectrum ℂ (1 : H →L[ℂ] H) = {1}
      simpa only [map_one] using (_root_.spectrum.scalar_eq (A := H →L[ℂ] H) (1 : ℂ))
    have he : Complex.exp ((2 * π : ℝ) • z) = 1 := by
      have hm' := hm.1
      rw [hT] at hm'
      change Complex.exp ((2 * π : ℝ) • z) ∈ _root_.spectrum ℂ (rotation (2 * π)) at hm'
      rw [rotation_period, hs] at hm'
      exact hm'
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp he
    refine ⟨n, ?_⟩
    have hp : ((2 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (by positivity : 0 < 2 * π))
    apply mul_left_cancel₀ hp
    change ((2 * π : ℝ) : ℂ) * (Complex.I * n) = ((2 * π : ℝ) : ℂ) * z
    change ((2 * π : ℝ) : ℂ) * z = _ at hn
    rw [hn]
    push_cast
    ring
  · rintro z ⟨n, rfl⟩
    exact mode_mem_generator_spectrum T hT n

lemma exponentialImage_eq_range (t : ℝ) :
    exponentialImage t = Set.range (fun n : ℤ => Complex.exp (Complex.I * n * t)) := by
  ext z
  simp only [exponentialImage, imaginaryIntegers, Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
    refine ⟨n, ?_⟩
    congr 1
    change Complex.I * n * t = (t : ℂ) * (Complex.I * n)
    ring
  · rintro ⟨n, rfl⟩
    refine ⟨Complex.I * n, ⟨n, rfl⟩, ?_⟩
    congr 1
    change (t : ℂ) * (Complex.I * n) = Complex.I * n * t
    ring

lemma exponentialImage_subset (t : ℝ) : exponentialImage t ⊆ unitCircle := by
  rw [exponentialImage_eq_range]
  rintro z ⟨n, rfl⟩
  change ‖Complex.exp (Complex.I * n * t)‖ = 1
  simp [Complex.norm_exp]

lemma exponentialImage_closure (t : ℝ) (ht : Irrational (t / (2 * π))) :
    closure (exponentialImage t) = unitCircle := by
  let f (n : ℤ) : Circle := AddCircle.homeomorphCircle' (n • (t : AngularCircle))
  have hd : DenseRange f :=
    AddCircle.homeomorphCircle'.surjective.denseRange.comp
      (AddCircle.denseRange_zsmul_coe_iff.mpr ht) AddCircle.homeomorphCircle'.continuous
  have hf (n : ℤ) : (f n : ℂ) = Complex.exp (Complex.I * n * t) := by
    change (AddCircle.homeomorphCircle' (n • (t : AngularCircle)) : ℂ) = _
    rw [← AddCircle.coe_zsmul, AddCircle.homeomorphCircle'_apply_mk, Circle.coe_exp]
    congr 1
    push_cast
    ring
  apply Set.Subset.antisymm
  · exact closure_minimal (exponentialImage_subset t) (isClosed_eq continuous_norm continuous_const)
  · intro z hz
    let w : Circle := ⟨z, by simpa [unitCircle, Submonoid.unitSphere] using hz⟩
    have hw : w ∈ closure (Set.range f) := hd w
    have hc := mem_closure_image
      ((continuous_subtype_val : Continuous (Subtype.val : Circle → ℂ)).continuousAt (x := w)) hw
    apply closure_mono (s := (Subtype.val : Circle → ℂ) '' Set.range f) (t := exponentialImage t) ?_ hc
    rintro _ ⟨v, ⟨n, rfl⟩, rfl⟩
    rw [exponentialImage_eq_range]
    exact ⟨n, (hf n).symm⟩

/-- The translations are unitary, and their Fourier eigenvalues are dense
in the circle at every irrational rotation time. -/
theorem time_spectrum : TimeSpectrum := by
  intro t ht
  apply Set.Subset.antisymm (rotation_spectrum_subset t)
  rw [← exponentialImage_closure t ht]
  apply closure_minimal
  · rw [exponentialImage_eq_range]
    rintro z ⟨n, rfl⟩
    exact mode_mem_time_spectrum t n
  · exact _root_.spectrum.isClosed (rotation t)

lemma neg_one_not_mem_exponentialImage (t : ℝ) (ht : Irrational (t / (2 * π))) :
    (-1 : ℂ) ∉ exponentialImage t := by
  rw [exponentialImage_eq_range]
  rintro ⟨n, hn⟩
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    norm_num at hn
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  have he : Circle.exp ((n : ℝ) * t) = Circle.exp π := by
    apply Subtype.ext
    change Complex.exp (((n : ℝ) * t : ℝ) * Complex.I) = Complex.exp (π * Complex.I)
    rw [Complex.exp_pi_mul_I]
    convert hn using 1
    congr 1
    push_cast
    ring
  obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp he
  apply ht.ne_rational (2 * k + 1) (2 * n)
  push_cast
  apply (div_eq_div_iff (by positivity : (2 : ℝ) * π ≠ 0)
    (mul_ne_zero (by norm_num) hnr)).mpr
  nlinarith [hk]

theorem exponential_image : ExponentialImage := by
  intro t ht
  refine ⟨?_, exponentialImage_closure t ht, exponentialImage_subset t, ?_⟩
  · rw [exponentialImage_eq_range]
    exact Set.countable_range _
  · intro h
    apply neg_one_not_mem_exponentialImage t ht
    exact h (by simp [unitCircle])

theorem counterexample : Counterexample := by
  refine ⟨rotationSemigroup, (fun _ => rfl), generator_spectrum rotationSemigroup (fun _ => rfl), ?_⟩
  intro t ht
  dsimp only
  rw [generator_spectrum rotationSemigroup (fun _ => rfl)]
  change (exponentialImage t).Countable ∧ closure (exponentialImage t) = unitCircle ∧
    _root_.spectrum ℂ (rotation t) = unitCircle ∧
    exponentialImage t ⊂ _root_.spectrum ℂ (rotation t) \ {0}
  obtain ⟨hc, hd, hs⟩ := exponential_image t ht
  refine ⟨hc, hd, time_spectrum t ht, ?_⟩
  rw [time_spectrum t ht]
  have hzero : unitCircle \ {(0 : ℂ)} = unitCircle := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_singleton_iff, and_iff_left_iff_imp]
    intro hz hz0
    subst z
    norm_num [unitCircle] at hz
  rw [hzero]
  exact hs

end ExpandedFA.Semigroups.RotationSpectralMappingFailure
