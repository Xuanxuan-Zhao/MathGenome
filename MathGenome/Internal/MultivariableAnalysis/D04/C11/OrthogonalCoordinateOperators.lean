import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C11.OrthogonalCoordinateOperators
import MathGenome.Internal.MultivariableAnalysis.D04.C11.EuclideanVectorOperators
import MathGenome.Internal.MultivariableAnalysis.D04.C13.OrientedEuclideanDictionary
import MathGenome.Internal.MultivariableAnalysis.D04.C13.DifferentialIdentities
import Mathlib.Tactic.FieldSimp

/-! Orthogonal-coordinate operators, paper d04:11:orthogonal.
The metric and positive orientation identify the pulled-back work and flux
coefficients. Naturality at C²/C¹ regularity gives curl and divergence;
the scalar chain rule gives gradient, and divergence of gradient gives Laplacian.
All auxiliary coordinate fields are derived from the canonical upstream forms. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace D04.Orthogonal
open D04 D04.Dictionary
open Specs.D04.C11.OrthogonalCoordinateOperators.Model

/-- The coordinate factors are strictly positive on the regular domain. -/
theorem scaleFactor_pos {U V : Set (E 3)} {φ : E 3 → E 3}
    (h : OrthogonalChart U V φ) {u : E 3} (hu : u ∈ U) (i : Fin 3) :
    0 < scaleFactor φ u i := norm_pos_iff.mpr (h.nonzero u hu i)

theorem volumeFactor_pos {U V : Set (E 3)} {φ : E 3 → E 3}
    (h : OrthogonalChart U V φ) {u : E 3} (hu : u ∈ U) :
    0 < volumeFactor φ u := Finset.prod_pos fun i _ => scaleFactor_pos h hu i

/-- Recover each derivative column from its length and unit vector. -/
theorem column_eq_scale_smul {U V : Set (E 3)} {φ : E 3 → E 3}
    (h : OrthogonalChart U V φ) {u : E 3} (hu : u ∈ U) (i : Fin 3) :
    coordinateColumn φ u i = scaleFactor φ u i • unitVector φ u i := by
  simp [unitVector, smul_smul, ne_of_gt (scaleFactor_pos h hu i)]

theorem unitVector_orthonormal {U V : Set (E 3)} {φ : E 3 → E 3}
    (h : OrthogonalChart U V φ) {u : E 3} (hu : u ∈ U) :
    Orthonormal ℝ (unitVector φ u) := by
  rw [orthonormal_iff_ite]
  intro i j
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl, real_inner_self_eq_norm_sq]
    have hn : ‖unitVector φ u i‖ = 1 := by
      simp only [unitVector, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_nonneg (le_of_lt (scaleFactor_pos h hu i))]
      exact inv_mul_cancel₀ (ne_of_gt (scaleFactor_pos h hu i))
    rw [hn, one_pow]
  · simp [unitVector, real_inner_smul_left, real_inner_smul_right,
      h.orthogonal u hu hij, hij]

/-- The normalized derivative columns form a complete orthonormal basis. -/
def frameBasis {U V : Set (E 3)} {φ : E 3 → E 3}
    (h : OrthogonalChart U V φ) {u : E 3} (hu : u ∈ U) :
    OrthonormalBasis (Fin 3) ℝ (E 3) :=
  OrthonormalBasis.mk (unitVector_orthonormal h hu)
    ((unitVector_orthonormal h hu).linearIndependent.span_eq_top_of_card_eq_finrank'
      (by simp [Specs.D04.C01.EuclideanInterfaces.Model.E])).ge

@[simp] theorem frameBasis_apply {U V : Set (E 3)} {φ : E 3 → E 3}
    (h : OrthogonalChart U V φ) {u : E 3} (hu : u ∈ U) (i : Fin 3) :
    frameBasis h hu i = unitVector φ u i := by
  simp [frameBasis]

theorem frame_expansion {U V : Set (E 3)} {φ : E 3 → E 3}
    (h : OrthogonalChart U V φ) {u : E 3} (hu : u ∈ U) (v : E 3) :
    ∑ i : Fin 3, inner ℝ v (unitVector φ u i) • unitVector φ u i = v := by
  simpa only [frameBasis_apply, real_inner_comm] using (frameBasis h hu).sum_repr' v


private theorem partial_eq_total (U : Set (E 3)) (f : E 3 → ℝ) (u : E 3)
    (hf : TotalDifferentiableAt U f u) (i : Fin 3) :
    scalarPartialDerivative f u i = totalDerivative f u (standardBasis 3 i) := by
  obtain ⟨A, hA⟩ := hf
  rw [scalarPartialDerivative_eq U f u A hA, totalDerivative_eq U f A u hA]

/-- Chain rule in physical components. -/
theorem partial_composition {U V : Set (E 3)} {φ : E 3 → E 3}
    (h : OrthogonalChart U V φ) (f : E 3 → ℝ) (hf : CrOn 1 V f)
    {u : E 3} (hu : u ∈ U) (i : Fin 3) :
    scalarPartialDerivative (f ∘ φ) u i =
      scaleFactor φ u i * inner ℝ (scalarGradient f (φ u)) (unitVector φ u i) := by
  have hdφ := h.regularity.1 u hu
  have hdf := hf.1 (φ u) (h.maps_to hu)
  rw [partial_eq_total U _ u (totalDifferentiableAt_comp U V φ f u hdφ hdf) i,
    totalDerivative_comp U V φ f u hdφ hdf]
  change totalDerivative f (φ u) (coordinateColumn φ u i) = _
  rw [scalarGradient_represents, column_eq_scale_smul h hu i, real_inner_smul_right]

theorem orthogonal_gradient (U V : Set (E 3)) (φ : E 3 → E 3)
    (h : OrthogonalChart U V φ) (f : E 3 → ℝ) (hf : CrOn 1 V f)
    (u : E 3) (hu : u ∈ U) :
    scalarGradient f (φ u) = ∑ i : Fin 3,
      (scalarPartialDerivative (f ∘ φ) u i / scaleFactor φ u i) • unitVector φ u i := by
  calc
    scalarGradient f (φ u) =
        ∑ i : Fin 3, inner ℝ (scalarGradient f (φ u)) (unitVector φ u i) •
          unitVector φ u i := (frame_expansion h hu _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [partial_composition h f hf hu i]
      congr 1
      field_simp [ne_of_gt (scaleFactor_pos h hu i)]

/-- The volume of the derivative columns is its signed Jacobian. -/
theorem columns_volume (φ : E 3 → E 3) (u : E 3) :
    omega 3 (coordinateColumn φ u) = Matrix.det (jacobian φ u) := by
  change Matrix.det (fun i j => coordinateColumn φ u j i) = _
  congr 1
  ext i j
  exact (matrixOfLinearMap_apply (totalDerivative φ u).toLinearMap i j).symm

/-- Positive orientation makes the unit frame have volume one. -/
theorem frame_volume {U V : Set (E 3)} {φ : E 3 → E 3}
    (h : OrthogonalChart U V φ) {u : E 3} (hu : u ∈ U) :
    omega 3 (unitVector φ u) = 1 := by
  have hd : omega 3 (unitVector φ u) = 1 ∨ omega 3 (unitVector φ u) = -1 := by
    have hh := (EuclideanSpace.basisFun (Fin 3) ℝ).det_to_matrix_orthonormalBasis_real
      (frameBasis h hu)
    change omega 3 (fun i => frameBasis h hu i) = 1 ∨
      omega 3 (fun i => frameBasis h hu i) = -1 at hh
    simpa only [frameBasis_apply] using hh
  have he : Matrix.det (jacobian φ u) =
      volumeFactor φ u * omega 3 (unitVector φ u) := by
    have hc : coordinateColumn φ u = fun i => scaleFactor φ u i • unitVector φ u i :=
      funext (column_eq_scale_smul h hu)
    rw [← columns_volume, hc]
    exact (omega 3).toMultilinearMap.map_smul_univ _ _
  rcases hd with hd | hd
  · exact hd
  · have hp : 0 < Matrix.det (jacobian φ u) := h.positive u hu
    have hJ := volumeFactor_pos h hu
    rw [hd] at he
    nlinarith

theorem jacobian_eq_volumeFactor {U V : Set (E 3)} {φ : E 3 → E 3}
    (h : OrthogonalChart U V φ) {u : E 3} (hu : u ∈ U) :
    Matrix.det (jacobian φ u) = volumeFactor φ u := by
  have hc : coordinateColumn φ u = fun i => scaleFactor φ u i • unitVector φ u i :=
    funext (column_eq_scale_smul h hu)
  rw [← columns_volume, hc]
  rw [(omega 3).map_smul_univ, frame_volume h hu]
  exact mul_one _


/-- Coordinates of the pulled-back work form. These are hᵢFᵢ on U. -/
def workCoordinates (φ F : E 3 → E 3) (u : E 3) : E 3 :=
  WithLp.toLp 2 (fun i => coefficient (standardBasis 3) (pullback φ (alpha F) u)
    (Set.powersetCard.ofSingleton i))

/-- Coordinates of the pulled-back flux form, with the middle sign included. -/
def fluxCoordinates (φ F : E 3 → E 3) (u : E 3) : E 3 :=
  WithLp.toLp 2 (fun i => (-1 : ℝ)^i.val *
    coefficient (standardBasis 3) (pullback φ (beta F) u) (missingIndexEquiv 2 i))

private theorem covector_ext_coeff {k : ℕ} {A B : Covector (E 3) k}
    (he : ∀ I, coefficient (standardBasis 3) A I = coefficient (standardBasis 3) B I) :
    A = B := by
  apply (covectorBasis (standardBasis 3) k).repr.injective
  ext I
  simpa only [← coefficient_eq_repr] using he I

theorem pullback_alpha_coordinates (φ F : E 3 → E 3) (u : E 3) :
    pullback φ (alpha F) u = alpha (workCoordinates φ F) u := by
  apply covector_ext_coeff
  intro I
  obtain ⟨i, rfl⟩ := (Set.powersetCard.ofSingleton (α := Fin 3)).surjective I
  rw [alpha_coefficient_singleton]
  rfl

theorem pullback_beta_coordinates (φ F : E 3 → E 3) (u : E 3) :
    pullback φ (beta F) u = beta (fluxCoordinates φ F) u := by
  rw [← fluxForm_three (fluxCoordinates φ F)]
  apply covector_ext_coeff
  intro I
  obtain ⟨i, rfl⟩ := (missingIndexEquiv 2).surjective I
  rw [fluxForm_coefficient]
  change _ = (-1 : ℝ)^i.val * ((-1 : ℝ)^i.val * _)
  rw [← mul_assoc, ← mul_pow]
  simp

private theorem chart_C1 {U V : Set (E 3)} {φ : E 3 → E 3}
    (h : OrthogonalChart U V φ) : CrOn 1 U φ :=
  (crOn_iff_contDiffOn 1 U φ h.open_source).mpr
    (((crOn_iff_contDiffOn 2 U φ h.open_source).mp h.regularity).of_le (by norm_num))

theorem workCoordinates_C1 {U V : Set (E 3)} {φ : E 3 → E 3}
    (h : OrthogonalChart U V φ) (F : E 3 → E 3) (hF : CrOn 1 V F) :
    CrOn 1 U (workCoordinates φ F) := by
  have hp := pullback_C1 U V φ (alpha F) h.open_source h.maps_to h.regularity
    (alpha_isCr 1 V F h.open_target hF)
  apply (crOn_iff_contDiffOn 1 U _ h.open_source).mpr
  apply (contDiffOn_piLp 2).mpr
  intro i
  exact (crOn_iff_contDiffOn 1 U _ h.open_source).mp (hp.2 (Set.powersetCard.ofSingleton i))

theorem fluxCoordinates_C1 {U V : Set (E 3)} {φ : E 3 → E 3}
    (h : OrthogonalChart U V φ) (F : E 3 → E 3) (hF : CrOn 1 V F) :
    CrOn 1 U (fluxCoordinates φ F) := by
  have hp := pullback_C1 U V φ (beta F) h.open_source h.maps_to h.regularity
    (beta_isCr 1 V F h.open_target hF)
  apply (crOn_iff_contDiffOn 1 U _ h.open_source).mpr
  apply (contDiffOn_piLp 2).mpr
  intro i
  exact contDiffOn_const.mul
    ((crOn_iff_contDiffOn 1 U _ h.open_source).mp (hp.2 (missingIndexEquiv 2 i)))

theorem workCoordinates_physical {U V : Set (E 3)} {φ : E 3 → E 3}
    (h : OrthogonalChart U V φ) (F : E 3 → E 3) {u : E 3} (hu : u ∈ U) (i : Fin 3) :
    workCoordinates φ F u i = scaleFactor φ u i * physicalComponent φ F u i := by
  change inner ℝ (F (φ u))
    (totalDerivative φ u (standardBasis 3 (indexTuple (Set.powersetCard.ofSingleton i) 0))) = _
  rw [indexTuple_singleton]
  change inner ℝ (F (φ u)) (coordinateColumn φ u i) = _
  rw [column_eq_scale_smul h hu i, real_inner_smul_right]
  rfl

/-- In the positive orthonormal frame, flux has the physical component as coefficient. -/
theorem beta_frame {U V : Set (E 3)} {φ : E 3 → E 3}
    (h : OrthogonalChart U V φ) {u : E 3} (hu : u ∈ U) (v : E 3)
    (i j l : Fin 3) (hc : CyclicTriple i j l) :
    beta (fun _ => v) u ![unitVector φ u j, unitVector φ u l] =
      inner ℝ v (unitVector φ u i) := by
  let b := frameBasis h hu
  have hb (a : Fin 3) : unitVector φ u a = b a := (frameBasis_apply h hu a).symm
  have ho : omega 3 = b.toBasis.det := by
    have ht : omega 3 b.toBasis = 1 := by
      change omega 3 (fun a => frameBasis h hu a) = 1
      simp only [frameBasis_apply, frame_volume h hu]
    rw [(omega 3).eq_smul_basis_det b.toBasis, ht, one_smul]
  rw [beta_volume, ho]
  simp only [hb, Module.Basis.det_apply, Matrix.det_fin_three, Module.Basis.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, OrthonormalBasis.repr_self, PiLp.single_apply]
  rcases hc with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  all_goals simp [OrthonormalBasis.repr_apply_apply, real_inner_comm]


/-- The product of the other two lengths is J/hᵢ. -/
theorem volumeFactor_div_cyclic {U V : Set (E 3)} {φ : E 3 → E 3}
    (h : OrthogonalChart U V φ) {u : E 3} (hu : u ∈ U)
    (i j l : Fin 3) (hc : CyclicTriple i j l) :
    volumeFactor φ u / scaleFactor φ u i = scaleFactor φ u j * scaleFactor φ u l := by
  have hn (a : Fin 3) := ne_of_gt (scaleFactor_pos h hu a)
  rw [volumeFactor, Fin.prod_univ_three]
  rcases hc with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  all_goals field_simp [hn 0, hn 1, hn 2] <;> ring

/-- Flux on a pair of coordinate columns in positive cyclic order. -/
theorem beta_columns {U V : Set (E 3)} {φ : E 3 → E 3}
    (h : OrthogonalChart U V φ) (F : E 3 → E 3) {u : E 3} (hu : u ∈ U)
    (i j l : Fin 3) (hc : CyclicTriple i j l) :
    beta F (φ u) ![coordinateColumn φ u j, coordinateColumn φ u l] =
      scaleFactor φ u j * scaleFactor φ u l * physicalComponent φ F u i := by
  have he : ![coordinateColumn φ u j, coordinateColumn φ u l] =
      fun a : Fin 2 => ![scaleFactor φ u j, scaleFactor φ u l] a •
        ![unitVector φ u j, unitVector φ u l] a := by
    funext a
    fin_cases a <;> exact column_eq_scale_smul h hu _
  rw [he, (beta F (φ u)).map_smul_univ]
  change (scaleFactor φ u j * (scaleFactor φ u l * 1)) *
    beta (fun _ => F (φ u)) u ![unitVector φ u j, unitVector φ u l] = _
  rw [beta_frame h hu (F (φ u)) i j l hc, mul_one]
  rfl

private theorem alternating_swap_two (A : Covector (E 3) 2) (v w : E 3) :
    -A ![v,w] = A ![w,v] := by
  have hs := A.map_swap ![v,w] (i := 0) (j := 1) (by decide)
  have ht : ![v,w] ∘ Equiv.swap 0 1 = ![w,v] := by
    funext a
    fin_cases a <;> simp
  rw [ht] at hs
  exact hs.symm

/-- The signed coefficient convention equals cyclic evaluation. -/
theorem fluxCoordinates_cyclic (φ F : E 3 → E 3) (u : E 3)
    (i j l : Fin 3) (hc : CyclicTriple i j l) :
    fluxCoordinates φ F u i =
      beta F (φ u) ![coordinateColumn φ u j, coordinateColumn φ u l] := by
  change (-1 : ℝ)^i.val * (pullback φ (beta F) u)
    (fun a => standardBasis 3 (indexTuple (missingIndexEquiv 2 i) a)) = _
  simp_rw [indexTuple_missing]
  rw [pullback_apply]
  rcases hc with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · change 1 * beta F (φ u) ![coordinateColumn φ u 1, coordinateColumn φ u 2] = _
    exact one_mul _
  · have ht : (fun a : Fin 2 => totalDerivative φ u (standardBasis 3
        ((1 : Fin 3).succAbove a))) = ![coordinateColumn φ u 0, coordinateColumn φ u 2] := by
      funext a
      fin_cases a <;> rfl
    rw [ht]
    change (-1 : ℝ)^(1 : ℕ) * _ = _
    rw [pow_one, neg_one_mul, alternating_swap_two]
  · have ht : (fun a : Fin 2 => totalDerivative φ u (standardBasis 3
        ((2 : Fin 3).succAbove a))) = ![coordinateColumn φ u 0, coordinateColumn φ u 1] := by
      funext a
      fin_cases a <;> rfl
    rw [ht]
    change (-1 : ℝ)^(2 : ℕ) * _ = _
    norm_num

theorem fluxCoordinates_physical {U V : Set (E 3)} {φ : E 3 → E 3}
    (h : OrthogonalChart U V φ) (F : E 3 → E 3) {u : E 3} (hu : u ∈ U) (i : Fin 3) :
    fluxCoordinates φ F u i = volumeFactor φ u / scaleFactor φ u i *
      physicalComponent φ F u i := by
  have hh (i j l : Fin 3) (hc : CyclicTriple i j l) :
      fluxCoordinates φ F u i = volumeFactor φ u / scaleFactor φ u i *
        physicalComponent φ F u i := by
    rw [fluxCoordinates_cyclic φ F u i j l hc, beta_columns h F hu i j l hc,
      volumeFactor_div_cyclic h hu i j l hc]
  fin_cases i
  · exact hh 0 1 2 (Or.inl ⟨rfl,rfl,rfl⟩)
  · exact hh 1 2 0 (Or.inr (Or.inl ⟨rfl,rfl,rfl⟩))
  · exact hh 2 0 1 (Or.inr (Or.inr ⟨rfl,rfl,rfl⟩))


/-- Naturality applied to the flux form gives the transformed divergence. -/
theorem divergence_fluxCoordinates {U V : Set (E 3)} {φ : E 3 → E 3}
    (h : OrthogonalChart U V φ) (F : E 3 → E 3) (hF : CrOn 1 V F)
    {u : E 3} (hu : u ∈ U) :
    divergence (fluxCoordinates φ F) u = divergence F (φ u) * volumeFactor φ u := by
  have hn : exteriorDerivative (beta (fluxCoordinates φ F)) u =
      pullback φ (exteriorDerivative (beta F)) u :=
    (exteriorDerivative_congr U (pullback φ (beta F)) (beta (fluxCoordinates φ F))
      h.open_source (fun v _ => pullback_beta_coordinates φ F v) u hu).symm.trans
      (exteriorDerivative_pullback U V φ (beta F) h.open_source h.maps_to h.regularity
        (beta_isCr 1 V F h.open_target hF) u hu)
  rw [exterior_beta_divergence U _ h.open_source (fluxCoordinates_C1 h F hF) u hu] at hn
  have hv := congrArg (fun A : Covector (E 3) 3 => A (standardBasis 3)) hn
  change divergence (fluxCoordinates φ F) u * omega 3 (standardBasis 3) =
    exteriorDerivative (beta F) (φ u) (coordinateColumn φ u) at hv
  rw [exterior_beta_divergence V F h.open_target hF (φ u) (h.maps_to hu)] at hv
  have hone : omega 3 (standardBasis 3) = 1 := (standardBasis 3).det_self
  rw [hone, mul_one, smul_apply, smul_eq_mul, columns_volume,
    jacobian_eq_volumeFactor h hu] at hv
  exact hv

theorem orthogonal_divergence (U V : Set (E 3)) (φ : E 3 → E 3)
    (h : OrthogonalChart U V φ) (F : E 3 → E 3) (hF : CrOn 1 V F)
    (u : E 3) (hu : u ∈ U) :
    divergence F (φ u) = (volumeFactor φ u)⁻¹ * ∑ i : Fin 3,
      scalarPartialDerivative (fun v => volumeFactor φ v / scaleFactor φ v i *
        physicalComponent φ F v i) u i := by
  have hd := divergence_fluxCoordinates h F hF hu
  rw [divergence_coordinates U _ u h.open_source (fluxCoordinates_C1 h F hF) hu] at hd
  have he : (∑ i : Fin 3, scalarPartialDerivative (fun v => fluxCoordinates φ F v i) u i) =
      ∑ i : Fin 3, scalarPartialDerivative (fun v => volumeFactor φ v / scaleFactor φ v i *
        physicalComponent φ F v i) u i := by
    apply Finset.sum_congr rfl
    intro i _
    exact scalarPartialDerivative_congr U _ _ h.open_source
      (fun v hv => fluxCoordinates_physical h F hv i) u hu i
  rw [he] at hd
  rw [hd]
  field_simp [ne_of_gt (volumeFactor_pos h hu)]

/-- Naturality on the work form, evaluated on each coordinate pair. -/
theorem curl_workCoordinates {U V : Set (E 3)} {φ : E 3 → E 3}
    (h : OrthogonalChart U V φ) (F : E 3 → E 3) (hF : CrOn 1 V F)
    {u : E 3} (hu : u ∈ U) (j l : Fin 3) :
    scalarPartialDerivative (fun v => workCoordinates φ F v l) u j -
        scalarPartialDerivative (fun v => workCoordinates φ F v j) u l =
      beta (curl F) (φ u) ![coordinateColumn φ u j, coordinateColumn φ u l] := by
  have hn : exteriorDerivative (alpha (workCoordinates φ F)) u =
      pullback φ (exteriorDerivative (alpha F)) u :=
    (exteriorDerivative_congr U (pullback φ (alpha F)) (alpha (workCoordinates φ F))
      h.open_source (fun v _ => pullback_alpha_coordinates φ F v) u hu).symm.trans
      (exteriorDerivative_pullback U V φ (alpha F) h.open_source h.maps_to h.regularity
        (alpha_isCr 1 V F h.open_target hF) u hu)
  have hv := congrArg (fun A : Covector (E 3) 2 =>
    A ![standardBasis 3 j, standardBasis 3 l]) hn
  rw [exterior_alpha_basis] at hv
  rw [pullback_apply] at hv
  have ht : (fun a : Fin 2 => totalDerivative φ u (![standardBasis 3 j, standardBasis 3 l] a)) =
      ![coordinateColumn φ u j, coordinateColumn φ u l] := by
    funext a
    fin_cases a <;> rfl
  rw [ht] at hv
  rw [exterior_alpha_curl V F h.open_target hF (φ u) (h.maps_to hu)] at hv
  exact hv

theorem orthogonal_curl (U V : Set (E 3)) (φ : E 3 → E 3)
    (h : OrthogonalChart U V φ) (F : E 3 → E 3) (hF : CrOn 1 V F)
    (u : E 3) (hu : u ∈ U) (i j l : Fin 3) (hc : CyclicTriple i j l) :
    inner ℝ (curl F (φ u)) (unitVector φ u i) =
      (scalarPartialDerivative (fun v => scaleFactor φ v l * physicalComponent φ F v l) u j -
        scalarPartialDerivative (fun v => scaleFactor φ v j * physicalComponent φ F v j) u l) /
          (scaleFactor φ u j * scaleFactor φ u l) := by
  have hd := curl_workCoordinates h F hF hu j l
  rw [beta_columns h (curl F) hu i j l hc] at hd
  have he (a b : Fin 3) : scalarPartialDerivative (fun v => workCoordinates φ F v a) u b =
      scalarPartialDerivative (fun v => scaleFactor φ v a * physicalComponent φ F v a) u b :=
    scalarPartialDerivative_congr U _ _ h.open_source
      (fun v hv => workCoordinates_physical h F hv a) u hu b
  rw [he l j, he j l] at hd
  rw [hd]
  change _ = (scaleFactor φ u j * scaleFactor φ u l *
    inner ℝ (curl F (φ u)) (unitVector φ u i)) / _
  field_simp [ne_of_gt (scaleFactor_pos h hu j), ne_of_gt (scaleFactor_pos h hu l)]


/-- Apply transformed divergence to the gradient and use its physical components. -/
theorem orthogonal_laplacian (U V : Set (E 3)) (φ : E 3 → E 3)
    (h : OrthogonalChart U V φ) (f : E 3 → ℝ) (hf : CrOn 2 V f)
    (u : E 3) (hu : u ∈ U) :
    laplacian f (φ u) = (volumeFactor φ u)⁻¹ * ∑ i : Fin 3,
      scalarPartialDerivative (fun v => volumeFactor φ v / (scaleFactor φ v i)^2 *
        scalarPartialDerivative (f ∘ φ) v i) u i := by
  have hf1 : CrOn 1 V f := (crOn_iff_contDiffOn 1 V f h.open_target).mpr
    (((crOn_iff_contDiffOn 2 V f h.open_target).mp hf).of_le (by norm_num))
  rw [laplacian_eq_divergence_gradient,
    orthogonal_divergence U V φ h (scalarGradient f) (gradient_crOn V f h.open_target hf) u hu]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply scalarPartialDerivative_congr U _ _ h.open_source _ u hu i
  intro v hv
  change volumeFactor φ v / scaleFactor φ v i *
    inner ℝ (scalarGradient f (φ v)) (unitVector φ v i) =
      volumeFactor φ v / (scaleFactor φ v i)^2 * scalarPartialDerivative (f ∘ φ) v i
  rw [partial_composition h f hf1 hv i]
  field_simp [ne_of_gt (scaleFactor_pos h hv i)]

end D04.Orthogonal
