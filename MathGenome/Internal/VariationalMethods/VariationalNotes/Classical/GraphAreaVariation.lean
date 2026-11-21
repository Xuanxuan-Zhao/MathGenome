import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.GraphAreaVariation
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.Spaces
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic

noncomputable section
open MeasureTheory TopologicalSpace Set
open scoped InnerProductSpace
set_option maxHeartbeats 400000
namespace VariationalNotes.Classical.GraphArea
open VariationalNotes.Sobolev

variable {d : ℕ}

lemma density_pos (z : Gradient 1 d) : 0 < density z := by
  exact Real.sqrt_pos.2 (by positivity)

lemma norm_le_density (z : Gradient 1 d) : ‖z‖ ≤ density z := by
  apply (Real.le_sqrt (norm_nonneg _) (by positivity)).2
  linarith

lemma density_le (z : Gradient 1 d) : density z ≤ 1 + ‖z‖ := by
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · nlinarith [norm_nonneg z]

lemma continuous_density : Continuous (density (d := d)) := by
  exact Real.continuous_sqrt.comp (continuous_const.add (continuous_norm.pow 2))

lemma continuous_densityVariation : Continuous (fun zw : Gradient 1 d × Gradient 1 d =>
    densityVariation zw.1 zw.2) := by
  exact (continuous_fst.inner continuous_snd).div
    (continuous_density.comp continuous_fst) (fun z => ne_of_gt (density_pos z.1))

lemma densityVariation_bound (z w : Gradient 1 d) : |densityVariation z w| ≤ ‖w‖ := by
  rw [densityVariation, abs_div, abs_of_pos (density_pos z)]
  apply (div_le_iff₀ (density_pos z)).2
  exact (abs_real_inner_le_norm z w).trans (by
    nlinarith [norm_le_density z, norm_nonneg w])

lemma density_hasDerivAt (z w : Gradient 1 d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => density (z + s • w))
      (densityVariation (z + t • w) w) t := by
  have h : HasDerivAt (fun s : ℝ => z + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add z
  have hh := (h.norm_sq.const_add 1).sqrt (by positivity)
  convert hh using 1 <;> simp only [density, densityVariation, Sobolev.frobenius]; ring

lemma gradient_integrable (Ω : Opens (Domain d)) (u : W11 Ω) :
    Integrable (gradient Ω 1 one u : Domain d → Gradient 1 d) (domainMeasure Ω) := by
  apply memLp_one_iff_integrable.mp
  simpa [one, Exponent.ennreal] using Lp.memLp (gradient Ω 1 one u)

lemma area_integrable (Ω : Opens (Domain d))
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (u : W11 Ω) :
    Integrable (fun x => density (gradient Ω 1 one u x)) (domainMeasure Ω) := by
  let : IsFiniteMeasure (domainMeasure Ω) := isFiniteMeasure_restrict.mpr hΩ.measure_lt_top.ne
  apply ((integrable_const (1 : ℝ)).add (gradient_integrable Ω u).norm).mono'
    (continuous_density.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _))
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (density_pos _)]
    exact density_le _

/-- Differentiate on fixed measurable representatives; the dominating function
is the L1 norm of the direction's gradient. -/
lemma variation_formula (Ω : Opens (Domain d))
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) (u v : W11 Ω) :
    Integrable (fun x => densityVariation (gradient Ω 1 one u x)
      (gradient Ω 1 one v x)) (domainMeasure Ω) ∧
    HasDerivAt (fun t : ℝ => area Ω (u + t • v)) (firstVariation Ω u v) 0 := by
  let U := gradient Ω 1 one u
  let V := gradient Ω 1 one v
  have hU := Lp.aestronglyMeasurable U
  have hV := Lp.aestronglyMeasurable V
  have hm (t : ℝ) : AEStronglyMeasurable
      (fun x => density (U x + t • V x)) (domainMeasure Ω) :=
    continuous_density.comp_aestronglyMeasurable (hU.add (hV.const_smul t))
  have hm' : AEStronglyMeasurable
      (fun x => densityVariation (U x + (0 : ℝ) • V x) (V x)) (domainMeasure Ω) := by
    simpa using continuous_densityVariation.comp_aestronglyMeasurable (hU.prodMk hV)
  have hi : Integrable (fun x => density (U x + (0 : ℝ) • V x)) (domainMeasure Ω) := by
    simpa [U] using area_integrable Ω hΩ u
  have H := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := domainMeasure Ω) (s := Set.univ) (x₀ := (0 : ℝ))
    (F := fun t x => density (U x + t • V x))
    (F' := fun t x => densityVariation (U x + t • V x) (V x))
    (bound := fun x => ‖V x‖)
    (Filter.univ_mem) (Filter.Eventually.of_forall hm) hi hm'
    (Filter.Eventually.of_forall fun x t _ => by
      simpa only [Real.norm_eq_abs] using densityVariation_bound (U x + t • V x) (V x))
    (gradient_integrable Ω v).norm
    (Filter.Eventually.of_forall fun x t _ => density_hasDerivAt (U x) (V x) t)
  have heq : (fun t : ℝ => area Ω (u + t • v)) =
      (fun t : ℝ => ∫ x, density (U x + t • V x) ∂domainMeasure Ω) := by
    funext t
    unfold area
    apply integral_congr_ae
    simp only [map_add, map_smul]
    filter_upwards [Lp.coeFn_add U (t • V), Lp.coeFn_smul t V] with x hx hy
    rw [hx, Pi.add_apply, hy, Pi.smul_apply]
  refine ⟨by simpa [U, V] using H.1, ?_⟩
  rw [heq]
  simpa [firstVariation, U, V] using H.2

theorem area_finite : Expected.AreaFinite := by
  intro d Ω hΩ u
  exact area_integrable Ω hΩ u

theorem first_variation : Expected.VariationFormula := by
  intro d Ω hΩ u v
  exact variation_formula Ω hΩ u v

/-- Identifying a smooth test by its value class also identifies all its
weak derivatives with its classical coordinate derivatives. -/
lemma representsTest_gradient (Ω : Opens (Domain d))
    (φ : P102.U4.TestSpace ℝ Ω) (v : W11 Ω) (hv : RepresentsTest Ω φ v) :
    (gradient Ω 1 one v : Domain d → Gradient 1 d) =ᵐ[domainMeasure Ω] testGradient Ω φ := by
  have hc : vectorTestCoordinate Ω (scalarTest Ω φ) 0 = φ := by
    ext x
    simp [vectorTestCoordinate, scalarTest, Function.comp_apply]
  have heq (j : Fin d) : coordinateLp Ω one (0,j) (gradient Ω 1 one v) =
      P102.U4.testToDomainLp Ω one.ennreal (P102.U4.testPartialWord Ω [j] φ) := by
    apply P102.U4.regularLp_injective Ω one.ennreal
    change P102.U4.regularDistribution Ω (coordinateLp Ω one (0,j) (gradient Ω 1 one v)) =
      P102.U4.regularDistribution Ω (P102.U4.testToDomainLp Ω one.ennreal
        (P102.U4.testPartialWord Ω [j] φ))
    rw [← Sobolev.distribution_derivative Ω one v 0 j]
    rw [show value Ω 1 one v = testToValueLp Ω 1 one (scalarTest Ω φ) from hv,
      coordinate_testToValueLp, hc]
    rw [P102.U4.regular_testToDomainLp, P102.U4.regular_testToDomainLp]
    rw [P102.U4.derivative_classicalCompatibility d ℝ Ω {j} φ
      (φ.contDiff.of_le (by simp)).contDiffOn]
    congr 1
    simpa [P102.U4.multiPartial] using (P102.U4.testPartialWord_coe Ω [j] φ).symm
  have ha (j : Fin d) : (fun x => gradient Ω 1 one v x (0,j)) =ᵐ[domainMeasure Ω]
      fun x => P102.U4.partialWord (φ : Domain d → ℝ) [j] x := by
    have h := (coordinateLp_ae Ω one (0,j) (gradient Ω 1 one v)).symm
    rw [heq] at h
    exact h.trans ((P102.U4.testToDomainLp_ae Ω one.ennreal
      (P102.U4.testPartialWord Ω [j] φ)).trans
        (Filter.Eventually.of_forall fun x => congrFun (P102.U4.testPartialWord_coe Ω [j] φ) x))
  filter_upwards [Filter.eventually_all.mpr ha] with x hx
  apply PiLp.ext
  rintro ⟨i,j⟩
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact hx j

theorem smooth_tests : Expected.SmoothTests := by
  intro d Ω hΩ u φ
  obtain ⟨v, hv⟩ := Sobolev.smooth_vector_inclusion Ω one (scalarTest Ω φ)
  have hg := representsTest_gradient Ω φ v hv
  have hi := (variation_formula Ω hΩ u v).1.congr (by
    filter_upwards [hg] with x hx
    rw [hx])
  have heq : firstVariation Ω u v = scalarVariation Ω u φ := by
    apply integral_congr_ae
    filter_upwards [hg] with x hx
    rw [hx]
  exact ⟨v, hv, hg, hi, heq ▸ (variation_formula Ω hΩ u v).2⟩

theorem stationarity : Expected.Stationarity := by
  intro d Ω hΩ u hmin φ
  obtain ⟨v, hv, _, _, hd⟩ := smooth_tests Ω hΩ u φ
  exact (hmin φ v hv).hasDerivAt_eq_zero hd

end VariationalNotes.Classical.GraphArea
