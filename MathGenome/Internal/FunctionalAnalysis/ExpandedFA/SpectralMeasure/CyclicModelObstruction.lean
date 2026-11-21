import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.CyclicModelObstruction
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.ArbitraryCyclicSum
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.NormalPVM
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

noncomputable section
open Function MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace ExpandedFA.SpectralMeasure.ArbitraryCyclicSum

private abbrev H := lp (fun _ : ℝ => ℂ) 2

private def entry (i : ℝ) : ℂ := (Real.arctan i : ℝ)

private lemma entry_injective : Function.Injective entry := by
  intro i j hij
  exact Real.arctan_injective (Complex.ofReal_injective hij)

private def diagonal : H →L[ℂ] H :=
  lp.mapCLM 2 (fun i => entry i • (1 : ℂ →L[ℂ] ℂ))
    (by positivity : 0 ≤ Real.pi / 2) (by
      intro i
      rw [norm_smul, norm_one, mul_one]
      simp only [entry, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan i).le,
        (Real.arctan_lt_pi_div_two i).le⟩)

private lemma diagonal_apply (x : H) (i : ℝ) :
    diagonal x i = entry i • x i := rfl

private lemma diagonal_selfAdjoint : IsSelfAdjoint diagonal := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change ⟪diagonal x, y⟫_ℂ = ⟪x, diagonal y⟫_ℂ
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr 1
  funext i
  simp only [diagonal_apply, inner_smul_left, inner_smul_right]
  simp [entry]

private def coordinate (i : ℝ) : H := lp.single 2 i 1

private lemma coordinate_ne_zero (i : ℝ) : coordinate i ≠ 0 := by
  intro h
  have hi := congrArg (fun x : H => x i) h
  simp [coordinate] at hi

private lemma diagonal_eigenvector (i : ℝ) :
    diagonal (coordinate i) = entry i • coordinate i := by
  apply lp.ext
  funext j
  change diagonal (coordinate i) j = entry i • coordinate i j
  rw [diagonal_apply]
  by_cases hij : j = i
  · rw [hij]
  · rw [show coordinate i j = 0 from lp.single_apply_ne 2 i 1 hij]
    rw [smul_zero, smul_zero]

private lemma mem_spectrum_of_eigenvector {K : Type*} [NormedAddCommGroup K]
    [NormedSpace ℂ K] {N : K →L[ℂ] K} {z : ℂ} {v : K} (hv : v ≠ 0)
    (hNv : N v = z • v) : z ∈ spectrum ℂ N := by
  apply spectrum.mem_iff.mpr
  rintro ⟨u, hu⟩
  apply hv
  apply (ContinuousLinearEquiv.ofUnit u).injective
  change (u : K →L[ℂ] K) v = (u : K →L[ℂ] K) 0
  rw [hu, map_zero]
  change z • v - N v = 0
  rw [hNv, sub_self]

private def spectralPoint (i : ℝ) : spectrum ℂ diagonal :=
  ⟨entry i, mem_spectrum_of_eigenvector (coordinate_ne_zero i) (diagonal_eigenvector i)⟩

private lemma spectralPoint_injective : Function.Injective spectralPoint := by
  intro i j hij
  apply entry_injective
  exact congrArg Subtype.val hij

private lemma singleton_projection_ne_zero {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] {N : K →L[ℂ] K}
    (E : ProjectionValuedMeasure (spectrum ℂ N) K) (hE : NormalPVM.Spec.Resolves N E)
    (z : spectrum ℂ N) {v : K} (hv : v ≠ 0) (hNv : N v = (z : ℂ) • v) :
    E {z} ≠ 0 := by
  let f : C(spectrum ℂ N, ℂ) := (ContinuousMap.id ℂ).restrict (spectrum ℂ N) -
    algebraMap ℂ C(spectrum ℂ N, ℂ) (z : ℂ)
  have hf : ∀ w, f w = (w : ℂ) - (z : ℂ) := by
    intro w
    rfl
  have hi : E.spectralIntegral f v = 0 := by
    change NormalPVM.continuousIntegral E f v = 0
    rw [show f = _ from rfl, map_sub, NormalPVM.continuousIntegral_coordinate E hE,
      AlgHomClass.commutes]
    change N v - (z : ℂ) • v = 0
    rw [hNv, sub_self]
  have hnorm := E.spectralIntegral_norm_sq_integral f (NormalPVM.continuous_bounded f) v
  rw [hi, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hnorm
  have hc : Continuous fun w => ‖f w‖ ^ 2 := f.continuous.norm.pow 2
  have hae := (integral_eq_zero_iff_of_nonneg (fun w => sq_nonneg ‖f w‖)
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp hnorm.symm
  have hae' : ∀ᵐ w ∂E.diagonalMeasure v, w = z := by
    filter_upwards [hae] with w hw
    apply Subtype.ext
    exact sub_eq_zero.mp (by simpa [hf w] using hw)
  have hz : E.diagonalMeasure v {z}ᶜ = 0 := by
    have heq : {z}ᶜ = {w | ¬ w = z} := by ext w; simp
    rw [heq]
    exact ae_iff.mp hae'
  intro hzero
  have hzero' : E.diagonalMeasure v {z} = 0 := by
    rw [E.diagonalMeasure_apply v {z} (MeasurableSet.singleton _), hzero]
    simp
  have huniv : E.diagonalMeasure v univ = 0 := by
    rw [← union_compl_self {z}, measure_union (disjoint_compl_right) (MeasurableSet.singleton _).compl,
      hz, hzero', add_zero]
  rw [E.diagonalMeasure_univ] at huniv
  exact (ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr hv)))) huniv

private lemma not_sigmaFinite_of_positive_disjoint {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : ℝ → Set Ω) (hm : ∀ i, MeasurableSet (A i))
    (hd : Pairwise (Disjoint on A)) (hp : ∀ i, 0 < μ (A i)) : ¬ SigmaFinite μ := by
  intro h
  let : SigmaFinite μ := h
  have hc := Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ) hm hd
  have hu : { i : ℝ | 0 < μ (A i) } = univ := eq_univ_of_forall hp
  rw [hu] at hc
  exact not_countable (countable_univ_iff.mp hc)

private lemma no_finite_control (E : ProjectionValuedMeasure (spectrum ℂ diagonal) H)
    (hE : NormalPVM.Spec.Resolves diagonal E) :
    ¬ ∃ μ : Measure (spectrum ℂ diagonal), IsFiniteMeasure μ ∧
      ∀ B, MeasurableSet B → (E B = 0 ↔ μ B = 0) := by
  rintro ⟨μ, hfinite, hcontrol⟩
  let : IsFiniteMeasure μ := hfinite
  apply not_sigmaFinite_of_positive_disjoint μ (fun i => {spectralPoint i})
    (fun _ => MeasurableSet.singleton _)
  · intro i j hij
    simpa only [Function.onFun, disjoint_singleton] using spectralPoint_injective.ne hij
  · intro i
    exact pos_iff_ne_zero.mpr fun h =>
      singleton_projection_ne_zero E hE (spectralPoint i)
        (coordinate_ne_zero i) (diagonal_eigenvector i)
        ((hcontrol _ (MeasurableSet.singleton _)).mpr h)
  · infer_instance

private lemma no_sigmaFinite_model {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (g : Ω → ℂ) (hg : Measurable g)
    (M : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] H)
    (hM : ∀ f, M f =ᵐ[μ] fun x => g x * f x)
    (hU : ∀ f, U (M f) = diagonal (U f)) : ¬ SigmaFinite μ := by
  let A (i : ℝ) := g ⁻¹' {entry i}
  have hm (i : ℝ) : MeasurableSet (A i) := hg (MeasurableSet.singleton _)
  have hd : Pairwise (Disjoint on A) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    change g x = entry i at hx
    change g x = entry j at hy
    exact hij (entry_injective (hx.symm.trans hy))
  apply not_sigmaFinite_of_positive_disjoint μ A hm hd
  intro i
  let f := U.symm (coordinate i)
  have hf : f ≠ 0 := by
    intro he
    have := congrArg U he
    exact coordinate_ne_zero i (by simpa [f] using this)
  have hMf : M f = entry i • f := by
    apply U.injective
    rw [hU, map_smul]
    simpa [f] using diagonal_eigenvector i
  have hae := hM f
  rw [hMf] at hae
  have hmul : ∀ᵐ x ∂μ, entry i * f x = g x * f x := by
    filter_upwards [hae, Lp.coeFn_smul (entry i) f] with x hx hx'
    exact hx'.symm.trans hx
  apply pos_iff_ne_zero.mpr
  intro hA
  apply hf
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have hnot : ∀ᵐ x ∂μ, x ∉ A i := by
    rw [ae_iff]
    convert hA using 2
    ext x
    exact not_not
  filter_upwards [hmul, hnot] with x hx hn
  change ¬ g x = entry i at hn
  exact (mul_eq_zero.mp (by rw [sub_mul, hx, sub_self] :
    (entry i - g x) * f x = 0)).resolve_left (sub_ne_zero.mpr (Ne.symm hn))

/-- Distinct eigenvalues on a nonseparable Hilbert space force both
obstructions in the cyclic multiplication theorem. -/
theorem cyclic_model_obstruction : Spec.CyclicModelObstruction.{u} := by
  have hN := diagonal_selfAdjoint.isStarNormal
  refine ⟨diagonal, hN, multiplication_model _ diagonal hN, ?_, no_finite_control⟩
  intro Ω _ μ g hg M U hM hU
  exact no_sigmaFinite_model μ g hg M U hM hU

end ExpandedFA.SpectralMeasure.ArbitraryCyclicSum
