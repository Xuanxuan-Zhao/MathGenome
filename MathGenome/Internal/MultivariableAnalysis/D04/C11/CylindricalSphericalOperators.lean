import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C11.CylindricalSphericalOperators
import MathGenome.Internal.MultivariableAnalysis.D04.C11.OrthogonalCoordinateOperators
import MathGenome.Internal.MultivariableAnalysis.D04.C07.CoordinateCharts
import Mathlib.Tactic.FieldSimp

noncomputable section
open Set Function Filter Topology
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace D04.Curvilinear
open D04 D04.CoordinateCharts
open Specs.D04.C07.CoordinateCharts.Model
open Specs.D04.C11.OrthogonalCoordinateOperators.Model

lemma cylindrical_smooth : ContDiff ℝ ∞ cylindrical := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i <;> dsimp [cylindrical] <;> fun_prop

lemma spherical_smooth : ContDiff ℝ ∞ spherical := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i <;> dsimp [spherical] <;> fun_prop

lemma column_matrix {φ : E 3 → E 3} {M : Matrix (Fin 3) (Fin 3) ℝ}
    {u : E 3} (h : HasFDerivAt φ (matrixCLM M) u) (i j : Fin 3) :
    coordinateColumn φ u i j = M j i := by
  change (fderiv ℝ φ u (standardBasis 3 i)) j = _
  rw [h.fderiv]
  simp [matrixCLM, Matrix.toLpLin_apply, dotProduct, standardBasis,
    Specs.D04.C01.EuclideanInterfaces.Model.standardBasis,
    EuclideanSpace.basisFun_apply]

lemma cylindrical_column (u : E 3) (i j : Fin 3) :
    coordinateColumn cylindrical u i j = cylindricalMatrix u j i :=
  column_matrix (cylindrical_hasFDerivAt u) i j

lemma spherical_column (u : E 3) (i j : Fin 3) :
    coordinateColumn spherical u i j = sphericalMatrix u j i :=
  column_matrix (spherical_hasFDerivAt u) i j

lemma cylindrical_factors : Specs.D04.C11.CylindricalSphericalOperators.cylindrical_factorsType := by
  intro u hr
  funext i
  have hc := Real.sin_sq_add_cos_sq (u 1)
  have hn := norm_nonneg (coordinateColumn cylindrical u i)
  have hs := EuclideanSpace.real_norm_sq_eq (coordinateColumn cylindrical u i)
  simp only [Fin.sum_univ_three, cylindrical_column] at hs
  change ‖coordinateColumn cylindrical u i‖ = _
  fin_cases i <;>
    simp [cylindricalMatrix, Matrix.of_apply] at hs ⊢
  · rcases hs with hs | hs <;> nlinarith [norm_nonneg (coordinateColumn cylindrical u 0)]
  · have hh : ‖coordinateColumn cylindrical u 1‖ ^ 2 = (u 0)^2 := by
      linear_combination hs + (u 0)^2 * hc
    nlinarith [norm_nonneg (coordinateColumn cylindrical u 1)]
  · rcases hs with hs | hs <;> nlinarith [norm_nonneg (coordinateColumn cylindrical u 2)]

lemma spherical_factors : Specs.D04.C11.CylindricalSphericalOperators.spherical_factorsType := by
  intro u hr ht hpi
  have hsin := Real.sin_pos_of_pos_of_lt_pi ht hpi
  have hc := Real.sin_sq_add_cos_sq (u 1)
  have hp := Real.sin_sq_add_cos_sq (u 2)
  funext i
  have hn := norm_nonneg (coordinateColumn spherical u i)
  have hs := EuclideanSpace.real_norm_sq_eq (coordinateColumn spherical u i)
  simp only [Fin.sum_univ_three, spherical_column] at hs
  change ‖coordinateColumn spherical u i‖ = _
  fin_cases i <;>
    simp [sphericalMatrix, Matrix.of_apply] at hs ⊢
  · have hh : ‖coordinateColumn spherical u 0‖ ^ 2 = 1 := by
      linear_combination hs + (Real.sin (u 1))^2 * hp + hc
    nlinarith [norm_nonneg (coordinateColumn spherical u 0)]
  · have hh : ‖coordinateColumn spherical u 1‖ ^ 2 = (u 0)^2 := by
      linear_combination hs + (u 0)^2 * (Real.cos (u 1))^2 * hp + (u 0)^2 * hc
    nlinarith [norm_nonneg (coordinateColumn spherical u 1)]
  · have hh : ‖coordinateColumn spherical u 2‖ ^ 2 = (u 0 * Real.sin (u 1))^2 := by
      linear_combination hs + (u 0)^2 * (Real.sin (u 1))^2 * hp
    nlinarith [mul_pos hr hsin, norm_nonneg (coordinateColumn spherical u 2)]

/-- Upgrade a known C¹ coordinate branch to the C² chart required by the
operator theorem, then restrict it to any open parameter subdomain. -/
lemma orthogonalChart_of_positive {φ : E 3 → E 3} {W U : Set (E 3)}
    {J : E 3 → ℝ} (hc : PositiveChart φ W J) (hs : ContDiff ℝ 2 φ)
    (hU : IsOpen U) (hUW : U ⊆ W)
    (ho : ∀ u ∈ U, Pairwise (fun i j =>
      inner ℝ (coordinateColumn φ u i) (coordinateColumn φ u j) = 0))
    (hn : ∀ u ∈ U, ∀ i, 0 < scaleFactor φ u i) :
    OrthogonalChart U (φ '' U) φ := by
  obtain ⟨hJ, e, heW, _, heφ, _, _⟩ := hc
  have heU : U ⊆ e.source := by simpa only [heW] using hUW
  have hV : IsOpen (φ '' U) := by
    rw [← heφ]
    exact e.isOpen_image_of_subset_source hU heU
  have hInv : MapsTo e.symm (φ '' U) U := by
    rintro y ⟨x, hx, rfl⟩
    have hh := e.left_inv (heU hx)
    rw [heφ] at hh
    rwa [hh]
  have hLeft : LeftInvOn e.symm φ U := by
    intro x hx
    simpa only [heφ] using e.left_inv (heU hx)
  have hRight : RightInvOn e.symm φ (φ '' U) := by
    rintro y ⟨x, hx, rfl⟩
    rw [hLeft hx]
  have hi : ContDiffOn ℝ 2 e.symm (φ '' U) := by
    intro y hy
    have hyt : y ∈ e.target := by
      obtain ⟨x, hx, rfl⟩ := hy
      rw [← heφ]
      exact e.map_source (heU hx)
    have hx := hInv hy
    let A : E 3 ≃L[ℝ] E 3 :=
      ((fderiv ℝ φ (e.symm y)).toLinearMap.equivOfDetNeZero
        (by change (fderiv ℝ φ (e.symm y)).det ≠ 0
            rw [(hJ _ (hUW hx)).1]; exact (hJ _ (hUW hx)).2.ne')).toContinuousLinearEquiv
    have hA : A.toContinuousLinearMap = fderiv ℝ φ (e.symm y) := rfl
    apply (e.contDiffAt_symm hyt (f₀' := A) ?_ ?_).contDiffWithinAt
    · rw [heφ, hA]
      exact (hs.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    · rw [heφ]
      exact hs.contDiffAt
  refine ⟨hU, hV, mapsTo_image _ _,
    (crOn_iff_contDiffOn 2 U φ hU).mpr hs.contDiffOn,
    ⟨e.symm, hInv, hLeft, hRight, (crOn_iff_contDiffOn 2 _ _ hV).mpr hi⟩,
    ?_, ho, ?_⟩
  · intro u hu
    have hdet : Matrix.det (jacobian φ u) = (fderiv ℝ φ u).det := by
      change Matrix.det (LinearMap.toMatrix (standardBasis 3) (standardBasis 3)
        (fderiv ℝ φ u).toLinearMap) = _
      exact LinearMap.det_toMatrix _ _
    change 0 < Matrix.det (jacobian φ u)
    rw [hdet, (hJ u (hUW hu)).1]
    exact (hJ u (hUW hu)).2
  · intro u hu i
    exact norm_pos_iff.mp (hn u hu i)

lemma cylindrical_orthogonal (u : E 3) :
    Pairwise (fun i j => inner ℝ (coordinateColumn cylindrical u i)
      (coordinateColumn cylindrical u j) = 0) := by
  intro i j hij
  simp only [PiLp.inner_apply, Fin.sum_univ_three, cylindrical_column, RCLike.inner_apply,
    conj_trivial]
  fin_cases i <;> fin_cases j <;> simp_all [cylindricalMatrix, Matrix.of_apply] <;> ring

lemma spherical_orthogonal (u : E 3) :
    Pairwise (fun i j => inner ℝ (coordinateColumn spherical u i)
      (coordinateColumn spherical u j) = 0) := by
  intro i j hij
  simp only [PiLp.inner_apply, Fin.sum_univ_three, spherical_column, RCLike.inner_apply,
    conj_trivial]
  fin_cases i <;> fin_cases j <;> simp_all [sphericalMatrix, Matrix.of_apply]
  all_goals first
    | solve | ring
    | linear_combination u 0 * Real.sin (u 1) * Real.cos (u 1) * Real.sin_sq_add_cos_sq (u 2)

lemma cylindrical_orthogonalChart (α : ℝ) (U : Set (E 3))
    (hU : IsOpen U) (hUW : U ⊆ cylindricalDomain α) :
    OrthogonalChart U (cylindrical '' U) cylindrical := by
  apply orthogonalChart_of_positive (cylindrical_chart α)
    (cylindrical_smooth.of_le (by simp)) hU hUW
  · exact fun u _ => cylindrical_orthogonal u
  · intro u hu i
    rw [cylindrical_factors u (hUW hu).1]
    fin_cases i <;> simp_all
    exact (hUW hu).1

lemma spherical_orthogonalChart (α : ℝ) (U : Set (E 3))
    (hU : IsOpen U) (hUW : U ⊆ sphericalDomain α) :
    OrthogonalChart U (spherical '' U) spherical := by
  apply orthogonalChart_of_positive (spherical_chart α)
    (spherical_smooth.of_le (by simp)) hU hUW
  · exact fun u _ => spherical_orthogonal u
  · intro u hu i
    have hp := hUW hu
    have ht := Real.sin_pos_of_pos_of_lt_pi hp.2.1 hp.2.2.1
    rw [spherical_factors u hp.1 hp.2.1 hp.2.2.1]
    fin_cases i <;> simp_all [mul_pos hp.1 ht]
    exact hp.1

/-- A factor constant on a coordinate line can be pulled outside that partial
without any extra regularity requirement on the other factor. -/
lemma partial_mul_lineConstant (a g : E 3 → ℝ) (u : E 3) (i : Fin 3)
    (ha : ∀ t : ℝ, a (u + t • standardBasis 3 i) = a u) :
    scalarPartialDerivative (fun v => a v * g v) u i =
      a u * scalarPartialDerivative g u i := by
  change deriv (fun t : ℝ => a (u + t • standardBasis 3 i) *
    g (u + t • standardBasis 3 i)) 0 = _
  simp_rw [ha]
  exact deriv_const_mul_field _

lemma line_coordinate (u : E 3) (i j : Fin 3) (h : j ≠ i) (t : ℝ) :
    (u + t • standardBasis 3 i) j = u j := by
  simp [D04.standardBasis_apply, h, Ne.symm h]


lemma cylindrical_volume (u : E 3) (hr : 0 < u 0) :
    volumeFactor cylindrical u = u 0 := by
  simp [volumeFactor, cylindrical_factors u hr, Fin.prod_univ_three]

lemma spherical_volume (u : E 3) (hr : 0 < u 0) (ht : 0 < u 1) (hp : u 1 < Real.pi) :
    volumeFactor spherical u = (u 0)^2 * Real.sin (u 1) := by
  simp [volumeFactor, spherical_factors u hr ht hp, Fin.prod_univ_three]
  ring

/-- Equality of coefficient functions on the open domain suffices inside a partial. -/
lemma partial_weight_congr (U : Set (E 3)) (hU : IsOpen U) {u : E 3} (hu : u ∈ U)
    (a b g : E 3 → ℝ) (i : Fin 3) (he : EqOn a b U) :
    scalarPartialDerivative (fun v => a v * g v) u i =
      scalarPartialDerivative (fun v => b v * g v) u i := by
  apply scalarPartialDerivative_congr U _ _ hU _ u hu i
  intro v hv
  change a v * g v = b v * g v
  rw [he hv]

/-- The metric-factor sum, simplified on a regular cylindrical branch. -/
lemma cylindrical_divergence_sum (α : ℝ) (U : Set (E 3)) (hU : IsOpen U)
    (hUW : U ⊆ cylindricalDomain α) (G : Fin 3 → E 3 → ℝ) (u : E 3) (hu : u ∈ U) :
    (volumeFactor cylindrical u)⁻¹ * (∑ i : Fin 3,
      scalarPartialDerivative (fun v => volumeFactor cylindrical v / (scaleFactor cylindrical v i) * G i v) u i) =
      (u 0)⁻¹ * scalarPartialDerivative (fun v => v 0 * G 0 v) u 0 +
      (u 0)⁻¹ * scalarPartialDerivative (fun v => G 1 v) u 1 +
      1 * scalarPartialDerivative (fun v => G 2 v) u 2 := by
  have hr := (hUW hu).1
  have h0 : scalarPartialDerivative
      (fun v => volumeFactor cylindrical v / (scaleFactor cylindrical v 0) * G 0 v) u 0 =
      scalarPartialDerivative (fun v => (v 0) * G 0 v) u 0 := by
    apply partial_weight_congr U hU hu
    intro v hv
    have hp := hUW hv
    simp [cylindrical_volume v hp.1, cylindrical_factors v hp.1, hp.1.ne', pow_two] <;>
      field_simp [hp.1.ne'] <;> ring
  have h1 : scalarPartialDerivative
      (fun v => volumeFactor cylindrical v / (scaleFactor cylindrical v 1) * G 1 v) u 1 =
      scalarPartialDerivative (fun v => (1) * G 1 v) u 1 := by
    apply partial_weight_congr U hU hu
    intro v hv
    have hp := hUW hv
    simp [cylindrical_volume v hp.1, cylindrical_factors v hp.1, hp.1.ne', pow_two] <;>
      field_simp [hp.1.ne'] <;> ring
  have h2 : scalarPartialDerivative
      (fun v => volumeFactor cylindrical v / (scaleFactor cylindrical v 2) * G 2 v) u 2 =
      scalarPartialDerivative (fun v => (v 0) * G 2 v) u 2 := by
    apply partial_weight_congr U hU hu
    intro v hv
    have hp := hUW hv
    simp [cylindrical_volume v hp.1, cylindrical_factors v hp.1, hp.1.ne', pow_two] <;>
      field_simp [hp.1.ne'] <;> ring
  rw [Fin.sum_univ_three, h0, h1, h2]
  simp only [one_mul]
  rw [partial_mul_lineConstant (fun v => v 0) (G 2) u 2
    (fun t => line_coordinate u 2 0 (by decide) t)]
  rw [cylindrical_volume u hr]
  field_simp [hr.ne'] <;> ring

theorem cylindrical_divergence : Specs.D04.C11.CylindricalSphericalOperators.cylindrical_divergenceType := by
  intro α U hU hUW F hf u hu
  apply (Orthogonal.orthogonal_divergence U (cylindrical '' U) cylindrical
    (cylindrical_orthogonalChart α U hU hUW) _ hf u hu).trans
  simpa only [one_mul, D04.scalarPartialDerivative,
    Specs.D04.C02.DerivativeBridge.scalarPartialDerivativeValue] using cylindrical_divergence_sum α U hU hUW
    ((fun i v => physicalComponent cylindrical F v i)) u hu

/-- The metric-factor sum, simplified on a regular cylindrical branch. -/
lemma cylindrical_laplacian_sum (α : ℝ) (U : Set (E 3)) (hU : IsOpen U)
    (hUW : U ⊆ cylindricalDomain α) (G : Fin 3 → E 3 → ℝ) (u : E 3) (hu : u ∈ U) :
    (volumeFactor cylindrical u)⁻¹ * (∑ i : Fin 3,
      scalarPartialDerivative (fun v => volumeFactor cylindrical v / (scaleFactor cylindrical v i)^2 * G i v) u i) =
      (u 0)⁻¹ * scalarPartialDerivative (fun v => v 0 * G 0 v) u 0 +
      ((u 0)^2)⁻¹ * scalarPartialDerivative (fun v => G 1 v) u 1 +
      1 * scalarPartialDerivative (fun v => G 2 v) u 2 := by
  have hr := (hUW hu).1
  have h0 : scalarPartialDerivative
      (fun v => volumeFactor cylindrical v / ((scaleFactor cylindrical v 0)^2) * G 0 v) u 0 =
      scalarPartialDerivative (fun v => (v 0) * G 0 v) u 0 := by
    apply partial_weight_congr U hU hu
    intro v hv
    have hp := hUW hv
    simp [cylindrical_volume v hp.1, cylindrical_factors v hp.1, hp.1.ne', pow_two] <;>
      field_simp [hp.1.ne'] <;> ring
  have h1 : scalarPartialDerivative
      (fun v => volumeFactor cylindrical v / ((scaleFactor cylindrical v 1)^2) * G 1 v) u 1 =
      scalarPartialDerivative (fun v => ((v 0)⁻¹) * G 1 v) u 1 := by
    apply partial_weight_congr U hU hu
    intro v hv
    have hp := hUW hv
    simp [cylindrical_volume v hp.1, cylindrical_factors v hp.1, hp.1.ne', pow_two] <;>
      field_simp [hp.1.ne'] <;> ring
  have h2 : scalarPartialDerivative
      (fun v => volumeFactor cylindrical v / ((scaleFactor cylindrical v 2)^2) * G 2 v) u 2 =
      scalarPartialDerivative (fun v => (v 0) * G 2 v) u 2 := by
    apply partial_weight_congr U hU hu
    intro v hv
    have hp := hUW hv
    simp [cylindrical_volume v hp.1, cylindrical_factors v hp.1, hp.1.ne', pow_two] <;>
      field_simp [hp.1.ne'] <;> ring
  rw [Fin.sum_univ_three, h0, h1, h2]
  rw [partial_mul_lineConstant (fun v => v 0) (G 2) u 2
    (fun t => line_coordinate u 2 0 (by decide) t)]
  rw [partial_mul_lineConstant (fun v => (v 0)⁻¹) (G 1) u 1
    (fun t => congrArg Inv.inv (line_coordinate u 1 0 (by decide) t))]
  rw [cylindrical_volume u hr]
  field_simp [hr.ne'] <;> ring

theorem cylindrical_laplacian : Specs.D04.C11.CylindricalSphericalOperators.cylindrical_laplacianType := by
  intro α U hU hUW f hf u hu
  apply (Orthogonal.orthogonal_laplacian U (cylindrical '' U) cylindrical
    (cylindrical_orthogonalChart α U hU hUW) _ hf u hu).trans
  simpa only [one_mul, D04.scalarPartialDerivative,
    Specs.D04.C02.DerivativeBridge.scalarPartialDerivativeValue] using cylindrical_laplacian_sum α U hU hUW
    ((fun i v => scalarPartialDerivative (f ∘ cylindrical) v i)) u hu

/-- The metric-factor sum, simplified on a regular spherical branch. -/
lemma spherical_divergence_sum (α : ℝ) (U : Set (E 3)) (hU : IsOpen U)
    (hUW : U ⊆ sphericalDomain α) (G : Fin 3 → E 3 → ℝ) (u : E 3) (hu : u ∈ U) :
    (volumeFactor spherical u)⁻¹ * (∑ i : Fin 3,
      scalarPartialDerivative (fun v => volumeFactor spherical v / (scaleFactor spherical v i) * G i v) u i) =
      ((u 0)^2)⁻¹ * scalarPartialDerivative (fun v => (v 0)^2 * G 0 v) u 0 +
      (u 0 * Real.sin (u 1))⁻¹ * scalarPartialDerivative (fun v => Real.sin (v 1) * G 1 v) u 1 +
      (u 0 * Real.sin (u 1))⁻¹ * scalarPartialDerivative (fun v => G 2 v) u 2 := by
  have hr := (hUW hu).1
  have ht := Real.sin_pos_of_pos_of_lt_pi (hUW hu).2.1 (hUW hu).2.2.1
  have h0 : scalarPartialDerivative
      (fun v => volumeFactor spherical v / (scaleFactor spherical v 0) * G 0 v) u 0 =
      scalarPartialDerivative (fun v => ((v 0)^2 * Real.sin (v 1)) * G 0 v) u 0 := by
    apply partial_weight_congr U hU hu
    intro v hv
    have hp := hUW hv
    have hs := Real.sin_pos_of_pos_of_lt_pi hp.2.1 hp.2.2.1
    simp [spherical_volume v hp.1 hp.2.1 hp.2.2.1,
      spherical_factors v hp.1 hp.2.1 hp.2.2.1, hp.1.ne', hs.ne', pow_two] <;>
      field_simp [hp.1.ne'] <;> ring
  have h1 : scalarPartialDerivative
      (fun v => volumeFactor spherical v / (scaleFactor spherical v 1) * G 1 v) u 1 =
      scalarPartialDerivative (fun v => (v 0 * Real.sin (v 1)) * G 1 v) u 1 := by
    apply partial_weight_congr U hU hu
    intro v hv
    have hp := hUW hv
    have hs := Real.sin_pos_of_pos_of_lt_pi hp.2.1 hp.2.2.1
    simp [spherical_volume v hp.1 hp.2.1 hp.2.2.1,
      spherical_factors v hp.1 hp.2.1 hp.2.2.1, hp.1.ne', hs.ne', pow_two] <;>
      field_simp [hp.1.ne'] <;> ring
  have h2 : scalarPartialDerivative
      (fun v => volumeFactor spherical v / (scaleFactor spherical v 2) * G 2 v) u 2 =
      scalarPartialDerivative (fun v => (v 0) * G 2 v) u 2 := by
    apply partial_weight_congr U hU hu
    intro v hv
    have hp := hUW hv
    have hs := Real.sin_pos_of_pos_of_lt_pi hp.2.1 hp.2.2.1
    simp [spherical_volume v hp.1 hp.2.1 hp.2.2.1,
      spherical_factors v hp.1 hp.2.1 hp.2.2.1, hp.1.ne', hs.ne', pow_two] <;>
      field_simp [hp.1.ne'] <;> ring
  rw [Fin.sum_univ_three, h0, h1, h2]
  have hh0 : (fun v : E 3 => (v 0)^2 * Real.sin (v 1) * G 0 v) =
      (fun v => Real.sin (v 1) * ((v 0)^2 * G 0 v)) := by funext v; ring
  rw [hh0, partial_mul_lineConstant (fun v => Real.sin (v 1))
    (fun v => (v 0)^2 * G 0 v) u 0
    (fun t => congrArg Real.sin (line_coordinate u 0 1 (by decide) t))]
  have hh1 : (fun v : E 3 => v 0 * Real.sin (v 1) * G 1 v) =
      (fun v => v 0 * (Real.sin (v 1) * G 1 v)) := by funext v; ring
  rw [hh1, partial_mul_lineConstant (fun v => v 0)
    (fun v => Real.sin (v 1) * G 1 v) u 1
    (fun t => line_coordinate u 1 0 (by decide) t)]
  rw [partial_mul_lineConstant (fun v => v 0) (G 2) u 2
    (fun t => line_coordinate u 2 0 (by decide) t)]
  rw [spherical_volume u hr (hUW hu).2.1 (hUW hu).2.2.1]
  field_simp [hr.ne', ht.ne'] <;> ring

theorem spherical_divergence : Specs.D04.C11.CylindricalSphericalOperators.spherical_divergenceType := by
  intro α U hU hUW F hf u hu
  apply (Orthogonal.orthogonal_divergence U (spherical '' U) spherical
    (spherical_orthogonalChart α U hU hUW) _ hf u hu).trans
  simpa only [one_mul, D04.scalarPartialDerivative,
    Specs.D04.C02.DerivativeBridge.scalarPartialDerivativeValue] using spherical_divergence_sum α U hU hUW
    ((fun i v => physicalComponent spherical F v i)) u hu

/-- The metric-factor sum, simplified on a regular spherical branch. -/
lemma spherical_laplacian_sum (α : ℝ) (U : Set (E 3)) (hU : IsOpen U)
    (hUW : U ⊆ sphericalDomain α) (G : Fin 3 → E 3 → ℝ) (u : E 3) (hu : u ∈ U) :
    (volumeFactor spherical u)⁻¹ * (∑ i : Fin 3,
      scalarPartialDerivative (fun v => volumeFactor spherical v / (scaleFactor spherical v i)^2 * G i v) u i) =
      ((u 0)^2)⁻¹ * scalarPartialDerivative (fun v => (v 0)^2 * G 0 v) u 0 +
      ((u 0)^2 * Real.sin (u 1))⁻¹ * scalarPartialDerivative (fun v => Real.sin (v 1) * G 1 v) u 1 +
      ((u 0)^2 * (Real.sin (u 1))^2)⁻¹ * scalarPartialDerivative (fun v => G 2 v) u 2 := by
  have hr := (hUW hu).1
  have ht := Real.sin_pos_of_pos_of_lt_pi (hUW hu).2.1 (hUW hu).2.2.1
  have h0 : scalarPartialDerivative
      (fun v => volumeFactor spherical v / ((scaleFactor spherical v 0)^2) * G 0 v) u 0 =
      scalarPartialDerivative (fun v => ((v 0)^2 * Real.sin (v 1)) * G 0 v) u 0 := by
    apply partial_weight_congr U hU hu
    intro v hv
    have hp := hUW hv
    have hs := Real.sin_pos_of_pos_of_lt_pi hp.2.1 hp.2.2.1
    simp [spherical_volume v hp.1 hp.2.1 hp.2.2.1,
      spherical_factors v hp.1 hp.2.1 hp.2.2.1, hp.1.ne', hs.ne', pow_two] <;>
      field_simp [hp.1.ne'] <;> ring
  have h1 : scalarPartialDerivative
      (fun v => volumeFactor spherical v / ((scaleFactor spherical v 1)^2) * G 1 v) u 1 =
      scalarPartialDerivative (fun v => (Real.sin (v 1)) * G 1 v) u 1 := by
    apply partial_weight_congr U hU hu
    intro v hv
    have hp := hUW hv
    have hs := Real.sin_pos_of_pos_of_lt_pi hp.2.1 hp.2.2.1
    simp [spherical_volume v hp.1 hp.2.1 hp.2.2.1,
      spherical_factors v hp.1 hp.2.1 hp.2.2.1, hp.1.ne', hs.ne', pow_two] <;>
      field_simp [hp.1.ne'] <;> ring
  have h2 : scalarPartialDerivative
      (fun v => volumeFactor spherical v / ((scaleFactor spherical v 2)^2) * G 2 v) u 2 =
      scalarPartialDerivative (fun v => ((Real.sin (v 1))⁻¹) * G 2 v) u 2 := by
    apply partial_weight_congr U hU hu
    intro v hv
    have hp := hUW hv
    have hs := Real.sin_pos_of_pos_of_lt_pi hp.2.1 hp.2.2.1
    simp [spherical_volume v hp.1 hp.2.1 hp.2.2.1,
      spherical_factors v hp.1 hp.2.1 hp.2.2.1, hp.1.ne', hs.ne', pow_two] <;>
      field_simp [hp.1.ne'] <;> ring
  rw [Fin.sum_univ_three, h0, h1, h2]
  have hh0 : (fun v : E 3 => (v 0)^2 * Real.sin (v 1) * G 0 v) =
      (fun v => Real.sin (v 1) * ((v 0)^2 * G 0 v)) := by funext v; ring
  rw [hh0, partial_mul_lineConstant (fun v => Real.sin (v 1))
    (fun v => (v 0)^2 * G 0 v) u 0
    (fun t => congrArg Real.sin (line_coordinate u 0 1 (by decide) t))]
  simp only [one_mul]
  rw [partial_mul_lineConstant (fun v => (Real.sin (v 1))⁻¹) (G 2) u 2
    (fun t => congrArg (fun x : ℝ => (Real.sin x)⁻¹)
      (line_coordinate u 2 1 (by decide) t))]
  rw [spherical_volume u hr (hUW hu).2.1 (hUW hu).2.2.1]
  field_simp [hr.ne', ht.ne'] <;> ring

theorem spherical_laplacian : Specs.D04.C11.CylindricalSphericalOperators.spherical_laplacianType := by
  intro α U hU hUW f hf u hu
  apply (Orthogonal.orthogonal_laplacian U (spherical '' U) spherical
    (spherical_orthogonalChart α U hU hUW) _ hf u hu).trans
  simpa only [one_mul, D04.scalarPartialDerivative,
    Specs.D04.C02.DerivativeBridge.scalarPartialDerivativeValue] using spherical_laplacian_sum α U hU hUW
    ((fun i v => scalarPartialDerivative (f ∘ spherical) v i)) u hu

end D04.Curvilinear
