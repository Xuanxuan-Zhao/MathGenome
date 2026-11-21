import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.TranslationFourierModel
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

set_option maxHeartbeats 800000

noncomputable section
open MeasureTheory Filter Topology
open scoped SchwartzMap FourierTransform ENNReal
namespace ExpandedFA.Models.FullTranslationModel
universe u
variable {M : Type u} [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]

@[simp] theorem translation_zero (f : L2 M) : translate (M := M) 0 f = f := by
  change Lp.compMeasurePreserving (fun s : ℝ => s + 0) _ f = f
  simp only [add_zero]
  change Lp.compMeasurePreserving id _ f = f
  exact Lp.compMeasurePreserving_id_apply f

theorem translation_add (t s : ℝ) (f : L2 M) :
    translate (M := M) (t + s) f = translate (M := M) t (translate (M := M) s f) := by
  change Lp.compMeasurePreserving _ _ f =
    Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f)
  simpa only [Function.comp_def, add_assoc, add_comm, add_left_comm] using
    (Lp.compMeasurePreserving_comp_apply f (measurePreserving_add_right volume s)
      (measurePreserving_add_right volume t))

def translationUnitary (t : ℝ) : L2 M ≃ₗᵢ[ℂ] L2 M where
  toFun := translate (M := M) t
  invFun := translate (M := M) (-t)
  map_add' := (translate (M := M) t).map_add
  map_smul' := (translate (M := M) t).map_smul
  norm_map' := (translate (M := M) t).norm_map
  left_inv f := by rw [← translation_add]; simp
  right_inv f := by rw [← translation_add]; simp

theorem continuous_translation (f : L2 M) : Continuous (fun t => translate (M := M) t f) := by
  let g : ℝ → C(ℝ, ℝ) := fun t => ⟨fun s => s + t, continuous_id.add continuous_const⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g
    (continuous_snd.add continuous_fst)
  exact continuous_const.compMeasurePreservingLp hg
    (fun t => measurePreserving_add_right volume t) (by norm_num)

def translationGroup : Semigroups.Stone.UnitaryGroup (L2 M) where
  operators := translationUnitary
  at_zero := translation_zero
  add_time := translation_add
  continuous_orbit := continuous_translation

theorem translation_representative (t : ℝ) (f : L2 M) :
    (translate (M := M) t f : ℝ → M) =ᵐ[volume] fun s => f (s + t) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume t)

end ExpandedFA.Models.FullTranslationModel

namespace ExpandedFA.Models.TranslationFourierModel
open FullTranslationModel
universe u

theorem translation_group : Spec.TranslationGroupExpected.{u} := by
  intro M _ _ _
  exact ⟨translationGroup, fun _ _ => rfl⟩

end ExpandedFA.Models.TranslationFourierModel

namespace ExpandedFA.Models.TranslationFourierModel
open FullTranslationModel
universe u
variable {M : Type u} [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]

def realDilation (a : ℝ) (ha : a ≠ 0) : ℝ ≃L[ℝ] ℝ where
  toLinearEquiv := LinearEquiv.smulOfNeZero ℝ ℝ a ha
  continuous_toFun := continuous_const.smul continuous_id
  continuous_invFun := continuous_const.smul continuous_id

/-- Dilation on the Schwartz core, with the square-root Jacobian. -/
def schwartzDilation (a : ℝ) (ha : 0 < a) : 𝓢(ℝ, M) ≃ₗ[ℂ] 𝓢(ℝ, M) where
  toFun φ := (Real.sqrt a : ℂ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (realDilation a ha.ne') φ
  invFun φ := ((Real.sqrt a : ℂ)⁻¹) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (realDilation a ha.ne').symm φ
  map_add' φ ψ := by simp only [map_add, smul_add]
  map_smul' c φ := by
    simp only [map_smul]
    exact smul_comm _ _ _
  left_inv φ := by
    ext x
    change (Real.sqrt a : ℂ)⁻¹ • ((Real.sqrt a : ℂ) •
      φ ((realDilation a ha.ne') ((realDilation a ha.ne').symm x))) = φ x
    rw [ContinuousLinearEquiv.apply_symm_apply, inv_smul_smul₀]
    exact_mod_cast Real.sqrt_ne_zero'.mpr ha
  right_inv φ := by
    ext x
    change (Real.sqrt a : ℂ) • ((Real.sqrt a : ℂ)⁻¹ •
      φ ((realDilation a ha.ne').symm ((realDilation a ha.ne') x))) = φ x
    rw [ContinuousLinearEquiv.symm_apply_apply, smul_inv_smul₀]
    exact_mod_cast Real.sqrt_ne_zero'.mpr ha

@[simp] theorem schwartzDilation_apply (a : ℝ) (ha : 0 < a) (φ : 𝓢(ℝ, M)) (x : ℝ) :
    schwartzDilation a ha φ x = (Real.sqrt a : ℂ) • φ (a * x) := rfl

theorem schwartzDilation_norm (a : ℝ) (ha : 0 < a) (φ : 𝓢(ℝ, M)) :
    ‖(schwartzDilation a ha φ).toLp 2‖ = ‖φ.toLp 2‖ := by
  rw [SchwartzMap.norm_toLp' (by norm_num) (by norm_num),
    SchwartzMap.norm_toLp' (by norm_num) (by norm_num)]
  congr 1
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, schwartzDilation_apply, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt ha.le]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun x => ‖φ x‖ ^ 2) a, smul_eq_mul,
    abs_of_pos (inv_pos.mpr ha), ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]

/-- The angular transform on the dense vector-valued Schwartz core. -/
def angularSchwartz : 𝓢(ℝ, M) ≃ₗ[ℂ] 𝓢(ℝ, M) :=
  (FourierTransform.fourierEquiv ℂ 𝓢(ℝ, M)).trans
    (schwartzDilation (2 * Real.pi)⁻¹ (inv_pos.mpr (by positivity)))

theorem angularSchwartz_norm (φ : 𝓢(ℝ, M)) :
    ‖(angularSchwartz φ).toLp 2‖ = ‖φ.toLp 2‖ := by
  exact (schwartzDilation_norm (2 * Real.pi)⁻¹
    (inv_pos.mpr (by positivity)) (𝓕 φ)).trans (SchwartzMap.norm_fourier_toL2_eq φ)

/-- Surjective isometric extension; vector Schwartz density needs no separability of M. -/
def angularFourier : L2 M ≃ₗᵢ[ℂ] L2 M :=
  (angularSchwartz (M := M)).extendOfIsometry
    (SchwartzMap.toLpCLM ℂ (E := ℝ) M 2 volume)
    (SchwartzMap.toLpCLM ℂ (E := ℝ) M 2 volume)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top)
    (by intro φ; exact angularSchwartz_norm φ)

@[simp] theorem angularFourier_schwartz (φ : 𝓢(ℝ, M)) :
    angularFourier (φ.toLp 2) = (angularSchwartz φ).toLp 2 := by
  exact LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ φ

end ExpandedFA.Models.TranslationFourierModel

namespace ExpandedFA.Models.TranslationFourierModel
open FullTranslationModel
universe u
variable {M : Type u} [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]

/-- The angular integral used to compute the transform on its Schwartz core. -/
def angularIntegral (M : Type u) [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    [CompleteSpace M] (f : ℝ → M) (r : ℝ) : M :=
  (Real.sqrt (2 * Real.pi))⁻¹ •
    ∫ s : ℝ, Complex.exp (-Complex.I * (s : ℂ) * (r : ℂ)) • f s

theorem angularSchwartz_integral (φ : 𝓢(ℝ, M)) (r : ℝ) :
    angularSchwartz φ r = angularIntegral M φ r := by
  change (Real.sqrt ((2 * Real.pi)⁻¹) : ℂ) •
    (𝓕 φ) ((2 * Real.pi)⁻¹ * r) = _
  simp only [Real.sqrt_inv, angularIntegral,
    RCLike.real_smul_eq_coe_smul (K := ℂ), Complex.ofReal_inv]
  congr 1
  · norm_cast
  · rw [SchwartzMap.fourier_coe, Real.fourier_eq']
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun s => by
      simp only [RCLike.inner_apply, conj_trivial]
      push_cast
      have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      field_simp

theorem angularFourier_integral : AngularFourierAgreement (angularFourier (M := M)) := by
  intro φ
  rw [angularFourier_schwartz]
  exact (SchwartzMap.coeFn_toLp _ 2).trans
    (Filter.Eventually.of_forall (angularSchwartz_integral φ))

/-- The angular change-of-variables identity, with the positive translation phase. -/
theorem angular_integral_translation (f : ℝ → M) (t r : ℝ) :
    angularIntegral M (fun s => f (s + t)) r =
      Complex.exp (Complex.I * (t : ℂ) * (r : ℂ)) • angularIntegral M f r := by
  unfold angularIntegral
  rw [smul_comm (Complex.exp _) ((Real.sqrt (2 * Real.pi))⁻¹)]
  congr 1
  rw [← integral_smul]
  calc
    (∫ s : ℝ, Complex.exp (-Complex.I * (s : ℂ) * (r : ℂ)) • f (s + t)) =
        ∫ s : ℝ, Complex.exp (-Complex.I * ((s - t : ℝ) : ℂ) * (r : ℂ)) • f s := by
          simpa only [add_sub_cancel_right] using
            (integral_add_right_eq_self
              (fun s : ℝ => Complex.exp (-Complex.I * ((s - t : ℝ) : ℂ) * (r : ℂ)) • f s) t)
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun s => by
        dsimp only
        rw [smul_smul, ← Complex.exp_add]
        congr 2
        push_cast
        ring

end ExpandedFA.Models.TranslationFourierModel

namespace ExpandedFA.Models.TranslationFourierModel
open FullTranslationModel
universe u
variable {M : Type u} [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]

def phase (t r : ℝ) : ℂ := Complex.exp (Complex.I * (t : ℂ) * (r : ℂ))

@[simp] theorem phase_norm (t r : ℝ) : ‖phase t r‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem phase_continuous (t : ℝ) : Continuous (phase t) := by
  unfold phase
  fun_prop

theorem modulationMemLp (t : ℝ) (f : L2 M) : MemLp (fun r => phase t r • f r) 2 :=
  (Lp.memLp f).of_le
    ((phase_continuous t).aestronglyMeasurable.smul (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun r => by simp [norm_smul])

def modulation (t : ℝ) (f : L2 M) : L2 M :=
  (modulationMemLp t f).toLp _

theorem modulation_representative (t : ℝ) (f : L2 M) :
    (modulation t f : ℝ → M) =ᵐ[volume] fun r => phase t r • f r :=
  (modulationMemLp t f).coeFn_toLp

def modulationLinear (t : ℝ) : L2 M →ₗ[ℂ] L2 M where
  toFun := modulation t
  map_add' f g := by
    apply Lp.ext
    filter_upwards [modulation_representative t (f + g),
      Lp.coeFn_add f g, Lp.coeFn_add (modulation t f) (modulation t g),
      modulation_representative t f, modulation_representative t g] with r h₁ h₂ h₃ h₄ h₅
    simp only [h₁, h₂, h₃, Pi.add_apply, h₄, h₅, smul_add]
  map_smul' c f := by
    change modulation t (c • f) = c • modulation t f
    apply Lp.ext
    filter_upwards [modulation_representative t (c • f), Lp.coeFn_smul c f,
      Lp.coeFn_smul c (modulation t f), modulation_representative t f] with r h₁ h₂ h₃ h₄
    simp only [h₁, h₂, h₃, Pi.smul_apply, h₄]
    exact smul_comm _ _ _

theorem modulation_norm (t : ℝ) (f : L2 M) : ‖modulation t f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [modulation_representative t f] with r hr
  simp [hr, norm_smul]

def modulationIsometry (t : ℝ) : L2 M →ₗᵢ[ℂ] L2 M where
  toLinearMap := modulationLinear t
  norm_map' := modulation_norm t

end ExpandedFA.Models.TranslationFourierModel

namespace ExpandedFA.Models.TranslationFourierModel
open FullTranslationModel
universe u
variable {M : Type u} [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]

theorem translation_schwartz (t : ℝ) (φ : 𝓢(ℝ, M)) :
    translate (M := M) t (φ.toLp 2) = (φ.compSubConstCLM ℂ (-t)).toLp 2 := by
  apply Lp.ext
  filter_upwards [FullTranslationModel.translation_representative t (φ.toLp 2),
    (measurePreserving_add_right volume t).quasiMeasurePreserving.ae (φ.coeFn_toLp 2 volume),
    (φ.compSubConstCLM ℂ (-t)).coeFn_toLp 2] with r h₁ h₂ h₃
  simp only [h₁, h₂, h₃, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]

theorem angularFourier_translation_core (t : ℝ) (φ : 𝓢(ℝ, M)) :
    angularFourier (translate (M := M) t (φ.toLp 2)) = modulation t (angularFourier (φ.toLp 2)) := by
  rw [translation_schwartz, angularFourier_schwartz]
  apply Lp.ext
  filter_upwards [(φ.compSubConstCLM ℂ (-t) |> angularSchwartz).coeFn_toLp 2,
    modulation_representative t (angularFourier (φ.toLp 2)),
    angularFourier_integral φ] with r h₁ h₂ h₃
  rw [h₁, h₂, h₃, angularSchwartz_integral]
  have hs : (φ.compSubConstCLM ℂ (-t) : ℝ → M) = fun s => φ (s + t) := by
    ext s
    simp only [SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]
  rw [hs]
  exact angular_integral_translation (φ : ℝ → M) t r

theorem angularFourier_translation (t : ℝ) (f : L2 M) :
    angularFourier (translate (M := M) t f) = modulation t (angularFourier f) := by
  have heq := (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := M)
    (p := 2) ENNReal.ofNat_ne_top).equalizer
    ((angularFourier (M := M)).continuous.comp (translate (M := M) t).continuous)
    ((modulationIsometry (M := M) t).continuous.comp (angularFourier (M := M)).continuous)
    (funext (angularFourier_translation_core t))
  exact congrFun heq f

/-- Existence with the exact angular normalization on every Schwartz input. -/
theorem angular_fourier : Spec.AngularFourierExpected.{u} := by
  intro M _ _ _
  exact ⟨angularFourier, angularFourier_integral⟩

/-- Transport of translations by the constructed Fourier unitary. -/
def coordinateGroup : Semigroups.Stone.UnitaryGroup (L2 M) where
  operators t := ((angularFourier (M := M)).symm.trans (translationUnitary t)).trans
    angularFourier
  at_zero f := by
    change angularFourier (translate 0 (angularFourier.symm f)) = f
    rw [translation_zero, LinearIsometryEquiv.apply_symm_apply]
  add_time t s f := by
    change angularFourier (translate (t + s) (angularFourier.symm f)) =
      angularFourier (translate t (angularFourier.symm
        (angularFourier (translate s (angularFourier.symm f)))))
    rw [LinearIsometryEquiv.symm_apply_apply, translation_add]
  continuous_orbit f :=
    angularFourier.continuous.comp (continuous_translation (angularFourier.symm f))

theorem coordinateGroup_formula : IsCoordinateGroup (coordinateGroup (M := M)) := by
  intro t f
  change (angularFourier (translate t (angularFourier.symm f)) : ℝ → M) =ᵐ[volume] _
  rw [angularFourier_translation, LinearIsometryEquiv.apply_symm_apply]
  exact modulation_representative t f

theorem translation_conjugacy : Spec.TranslationConjugacyExpected.{u} := by
  intro M _ _ _
  refine ⟨translationGroup, coordinateGroup, angularFourier, (fun _ _ => rfl),
    coordinateGroup_formula, angularFourier_integral, ?_⟩
  intro t f
  change angularFourier (translate t f) =
    angularFourier (translate t (angularFourier.symm (angularFourier f)))
  rw [LinearIsometryEquiv.symm_apply_apply]

end ExpandedFA.Models.TranslationFourierModel

namespace ExpandedFA.Models.FullTranslationModel
universe u
variable {M : Type u} [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]

/-- The coordinate graph includes precisely the full weighted L² domain. -/
theorem coordinate_domain (f : L2 M) :
    (∃ g : L2 M, CoordinateGraph f g) ↔
      MemLp (fun r : ℝ => (r : ℂ) • f r) 2 volume := by
  constructor
  · rintro ⟨g, hg⟩
    exact (memLp_congr_ae hg).mp (Lp.memLp g)
  · intro hf
    exact ⟨hf.toLp _, hf.coeFn_toLp⟩

theorem coordinateGraph_unique {f g h : L2 M}
    (hg : CoordinateGraph f g) (hh : CoordinateGraph f h) : g = h :=
  Lp.ext (hg.trans hh.symm)

end ExpandedFA.Models.FullTranslationModel
