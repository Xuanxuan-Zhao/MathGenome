import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.CoordinateCharts
import MathGenome.Internal.MultivariableAnalysis.D04.C07.RegionSubstitution
import MathGenome.Internal.MultivariableAnalysis.D04.C04.InverseFunction
import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeBridge
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

noncomputable section
open Set Function Filter Topology
open scoped ContDiff
namespace D04.CoordinateCharts
open Specs.D04.C07.CoordinateCharts.Model

/-- The two Cartesian components recover the positive radius. -/
lemma circle_squares (r t : ℝ) :
    (r * Real.cos t)^2 + (r * Real.sin t)^2 = r^2 := by
  calc
    _ = r^2 * ((Real.cos t)^2 + (Real.sin t)^2) := by ring
    _ = r^2 := by rw [Real.cos_sq_add_sin_sq]; ring

/-- An open angular interval of length 2π has no repeated sine/cosine pair. -/
lemma angle_unique {α t u : ℝ} (ht : t ∈ Ioo α (α + 2 * Real.pi))
    (hu : u ∈ Ioo α (α + 2 * Real.pi))
    (hc : Real.cos t = Real.cos u) (hs : Real.sin t = Real.sin u) : t = u := by
  have hcos : Real.cos (t - u) = 1 := by
    rw [Real.cos_sub, hc, hs]
    nlinarith [Real.sin_sq_add_cos_sq u]
  have hz : t - u = 0 :=
    (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [ht.1, hu.2])
      (by linarith [ht.2, hu.1])).mp hcos
  linarith

lemma radial_angle_unique {α r s t u : ℝ} (hr : 0 < r) (hs : 0 < s)
    (ht : t ∈ Ioo α (α + 2 * Real.pi))
    (hu : u ∈ Ioo α (α + 2 * Real.pi))
    (hc : r * Real.cos t = s * Real.cos u)
    (hh : r * Real.sin t = s * Real.sin u) : r = s ∧ t = u := by
  have hsq : r^2 = s^2 := by rw [← circle_squares r t, hc, hh, circle_squares]
  have hrs : r = s := by nlinarith
  subst s
  exact ⟨rfl, angle_unique ht hu ((mul_left_cancel₀ hr.ne') hc)
    ((mul_left_cancel₀ hr.ne') hh)⟩

lemma polar_injOn (α : ℝ) : InjOn polar (polarDomain α) := by
  intro p hp q hq heq
  have h0 := congrArg (fun x : E 2 => x 0) heq
  have h1 := congrArg (fun x : E 2 => x 1) heq
  obtain ⟨hr, ht⟩ := radial_angle_unique hp.1 hq.1 hp.2 hq.2 h0 h1
  ext i
  fin_cases i <;> assumption

lemma cylindrical_injOn (α : ℝ) : InjOn cylindrical (cylindricalDomain α) := by
  intro p hp q hq heq
  have h0 := congrArg (fun x : E 3 => x 0) heq
  have h1 := congrArg (fun x : E 3 => x 1) heq
  have h2 := congrArg (fun x : E 3 => x 2) heq
  obtain ⟨hr, ht⟩ := radial_angle_unique hp.1 hq.1 hp.2 hq.2 h0 h1
  ext i
  fin_cases i <;> assumption

lemma spherical_radius_sq (p : E 3) :
    (spherical p 0)^2 + (spherical p 1)^2 + (spherical p 2)^2 = (p 0)^2 := by
  change (p 0 * Real.sin (p 1) * Real.cos (p 2))^2 +
    (p 0 * Real.sin (p 1) * Real.sin (p 2))^2 + (p 0 * Real.cos (p 1))^2 = _
  rw [circle_squares]
  nlinarith [circle_squares (p 0) (p 1)]

lemma spherical_injOn (α : ℝ) : InjOn spherical (sphericalDomain α) := by
  intro p hp q hq heq
  have h0 := congrArg (fun x : E 3 => x 0) heq
  have h1 := congrArg (fun x : E 3 => x 1) heq
  have h2 := congrArg (fun x : E 3 => x 2) heq
  have hsq : (p 0)^2 = (q 0)^2 := by
    rw [← spherical_radius_sq p, heq, spherical_radius_sq]
  have hr : p 0 = q 0 := by nlinarith [hp.1, hq.1]
  have hc : Real.cos (p 1) = Real.cos (q 1) := by
    change p 0 * Real.cos (p 1) = q 0 * Real.cos (q 1) at h2
    rw [← hr] at h2
    exact mul_left_cancel₀ hp.1.ne' h2
  have hφ : p 1 = q 1 := Real.injOn_cos ⟨hp.2.1.le, hp.2.2.1.le⟩
    ⟨hq.2.1.le, hq.2.2.1.le⟩ hc
  have hsp : 0 < p 0 * Real.sin (p 1) :=
    mul_pos hp.1 (Real.sin_pos_of_pos_of_lt_pi hp.2.1 hp.2.2.1)
  have hsq' : 0 < q 0 * Real.sin (q 1) :=
    mul_pos hq.1 (Real.sin_pos_of_pos_of_lt_pi hq.2.1 hq.2.2.1)
  obtain ⟨_, hθ⟩ := radial_angle_unique hsp hsq' hp.2.2.2 hq.2.2.2 h0 h1
  ext i
  fin_cases i <;> assumption

lemma polar_contDiff : ContDiff ℝ 1 polar := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i <;> dsimp [polar] <;> fun_prop

lemma cylindrical_contDiff : ContDiff ℝ 1 cylindrical := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i <;> dsimp [cylindrical] <;> fun_prop

lemma spherical_contDiff : ContDiff ℝ 1 spherical := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i <;> dsimp [spherical] <;> fun_prop

lemma polarDomain_isOpen (α : ℝ) : IsOpen (polarDomain α) := by
  have hc (i : Fin 2) : Continuous (fun p : E 2 => p i) := by fun_prop
  exact (isOpen_lt continuous_const (hc 0)).inter
    ((isOpen_lt continuous_const (hc 1)).inter (isOpen_lt (hc 1) continuous_const))

lemma cylindricalDomain_isOpen (α : ℝ) : IsOpen (cylindricalDomain α) := by
  have hc (i : Fin 3) : Continuous (fun p : E 3 => p i) := by fun_prop
  exact (isOpen_lt continuous_const (hc 0)).inter
    ((isOpen_lt continuous_const (hc 1)).inter (isOpen_lt (hc 1) continuous_const))

lemma sphericalDomain_isOpen (α : ℝ) : IsOpen (sphericalDomain α) := by
  have hc (i : Fin 3) : Continuous (fun p : E 3 => p i) := by fun_prop
  exact (isOpen_lt continuous_const (hc 0)).inter
    ((isOpen_lt continuous_const (hc 1)).inter
      ((isOpen_lt (hc 1) continuous_const).inter
        ((isOpen_lt continuous_const (hc 2)).inter (isOpen_lt (hc 2) continuous_const))))

/-- A matrix interpreted in the shared Euclidean coordinate bases. -/
def matrixCLM {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : E n →L[ℝ] E n :=
  M.toEuclideanLin.toContinuousLinearMap

def polarMatrix (p : E 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos (p 1), -p 0 * Real.sin (p 1);
     Real.sin (p 1), p 0 * Real.cos (p 1)]

def cylindricalMatrix (p : E 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos (p 1), -p 0 * Real.sin (p 1), 0;
     Real.sin (p 1), p 0 * Real.cos (p 1), 0;
     0, 0, 1]

def sphericalMatrix (p : E 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.sin (p 1) * Real.cos (p 2), p 0 * Real.cos (p 1) * Real.cos (p 2),
       -p 0 * Real.sin (p 1) * Real.sin (p 2);
     Real.sin (p 1) * Real.sin (p 2), p 0 * Real.cos (p 1) * Real.sin (p 2),
       p 0 * Real.sin (p 1) * Real.cos (p 2);
     Real.cos (p 1), -p 0 * Real.sin (p 1), 0]

lemma polar_hasFDerivAt (p : E 2) : HasFDerivAt polar (matrixCLM (polarMatrix p)) p := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_piLp 2]
  have h0 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 0
  have h1 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 1
  intro i
  fin_cases i
  · convert! (h0.mul h1.cos).hasFDerivWithinAt using 1
    ext v
    simp [matrixCLM, polarMatrix, Matrix.toLpLin_apply, dotProduct,
      Fin.sum_univ_two, ContinuousLinearMap.comp_apply, PiLp.proj_apply]
    ring
  · convert! (h0.mul h1.sin).hasFDerivWithinAt using 1
    ext v
    simp [matrixCLM, polarMatrix, Matrix.toLpLin_apply, dotProduct,
      Fin.sum_univ_two, ContinuousLinearMap.comp_apply, PiLp.proj_apply]
    ring

lemma cylindrical_hasFDerivAt (p : E 3) :
    HasFDerivAt cylindrical (matrixCLM (cylindricalMatrix p)) p := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_piLp 2]
  have h0 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 0
  have h1 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 1
  have h2 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 2
  intro i
  fin_cases i
  · convert! (h0.mul h1.cos).hasFDerivWithinAt using 1
    ext v
    simp [matrixCLM, cylindricalMatrix, Matrix.toLpLin_apply, dotProduct,
      Fin.sum_univ_succ, ContinuousLinearMap.comp_apply, PiLp.proj_apply]
    ring
  · convert! (h0.mul h1.sin).hasFDerivWithinAt using 1
    ext v
    simp [matrixCLM, cylindricalMatrix, Matrix.toLpLin_apply, dotProduct,
      Fin.sum_univ_succ, ContinuousLinearMap.comp_apply, PiLp.proj_apply]
    ring
  · convert! h2.hasFDerivWithinAt using 1
    ext v
    simp [matrixCLM, cylindricalMatrix, Matrix.toLpLin_apply, dotProduct,
      Fin.sum_univ_succ, ContinuousLinearMap.comp_apply, PiLp.proj_apply]

lemma spherical_hasFDerivAt (p : E 3) :
    HasFDerivAt spherical (matrixCLM (sphericalMatrix p)) p := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_piLp 2]
  have h0 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 0
  have h1 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 1
  have h2 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p 2
  intro i
  fin_cases i
  · convert! ((h0.mul h1.sin).mul h2.cos).hasFDerivWithinAt using 1
    ext v
    simp [matrixCLM, sphericalMatrix, Matrix.toLpLin_apply, dotProduct,
      Fin.sum_univ_succ, ContinuousLinearMap.comp_apply, PiLp.proj_apply]
    ring
  · convert! ((h0.mul h1.sin).mul h2.sin).hasFDerivWithinAt using 1
    ext v
    simp [matrixCLM, sphericalMatrix, Matrix.toLpLin_apply, dotProduct,
      Fin.sum_univ_succ, ContinuousLinearMap.comp_apply, PiLp.proj_apply]
    ring
  · convert! (h0.mul h1.cos).hasFDerivWithinAt using 1
    ext v
    simp [matrixCLM, sphericalMatrix, Matrix.toLpLin_apply, dotProduct,
      Fin.sum_univ_succ, ContinuousLinearMap.comp_apply, PiLp.proj_apply]
    ring

lemma polar_det (p : E 2) : (fderiv ℝ polar p).det = p 0 := by
  rw [(polar_hasFDerivAt p).fderiv]
  change (polarMatrix p).toEuclideanLin.det = _
  rw [LinearMap.det_toLpLin]
  simp only [polarMatrix, Matrix.det_fin_two_of]
  calc
    _ = p 0 * ((Real.cos (p 1))^2 + (Real.sin (p 1))^2) := by ring
    _ = p 0 := by rw [Real.cos_sq_add_sin_sq]; ring

lemma cylindrical_det (p : E 3) : (fderiv ℝ cylindrical p).det = p 0 := by
  rw [(cylindrical_hasFDerivAt p).fderiv]
  change (cylindricalMatrix p).toEuclideanLin.det = _
  rw [LinearMap.det_toLpLin]
  calc
    _ = p 0 * ((Real.cos (p 1))^2 + (Real.sin (p 1))^2) := by
      rw [Matrix.det_fin_three]
      simp only [cylindricalMatrix, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      ring
    _ = p 0 := by rw [Real.cos_sq_add_sin_sq]; ring

lemma spherical_det (p : E 3) :
    (fderiv ℝ spherical p).det = (p 0)^2 * Real.sin (p 1) := by
  rw [(spherical_hasFDerivAt p).fderiv]
  change (sphericalMatrix p).toEuclideanLin.det = _
  rw [LinearMap.det_toLpLin]
  calc
    _ = (p 0)^2 * Real.sin (p 1) *
        ((Real.sin (p 1))^2 + (Real.cos (p 1))^2) *
        ((Real.sin (p 2))^2 + (Real.cos (p 2))^2) := by
      rw [Matrix.det_fin_three]
      simp only [sphericalMatrix, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      ring
    _ = (p 0)^2 * Real.sin (p 1) := by rw [Real.sin_sq_add_cos_sq, Real.sin_sq_add_cos_sq]; ring

/-- A nonsingular C¹ map is open on any open subset of its regular domain.
This is the local inverse theorem applied at each preimage point. -/
lemma open_image_of_nonsingular {n : ℕ} (f : E n → E n) (U : Set (E n))
    (hf : ContDiff ℝ 1 f) (hdet : ∀ x ∈ U, (fderiv ℝ f x).det ≠ 0)
    (W : Set (E n)) (hW : IsOpen W) (hWU : W ⊆ U) : IsOpen (f '' W) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x, hx, rfl⟩
  let A : E n ≃L[ℝ] E n :=
    ((fderiv ℝ f x).toLinearMap.equivOfDetNeZero (hdet x (hWU hx))).toContinuousLinearEquiv
  have hA : A.toContinuousLinearMap = fderiv ℝ f x := rfl
  have hd : HasFDerivAt f A.toContinuousLinearMap x := by
    rw [hA]
    exact (hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  let e := hf.contDiffAt.toOpenPartialHomeomorph f hd (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hxe : x ∈ e.source := hf.contDiffAt.mem_toOpenPartialHomeomorph_source hd _
  have ho := e.isOpen_image_of_subset_source (e.open_source.inter hW) inter_subset_left
  have hy : f x ∈ e '' (e.source ∩ W) := ⟨x, ⟨hxe, hx⟩, rfl⟩
  exact mem_of_superset (ho.mem_nhds hy) (image_mono inter_subset_right)

/-- Injectivity makes the local C¹ inverses agree, giving one inverse on
the full open image. No formula involving a globally defined angle is used. -/
lemma positiveChart_of_nonsingular {n : ℕ} (f : E n → E n) (U : Set (E n))
    (J : E n → ℝ) (hf : ContDiff ℝ 1 f) (hU : IsOpen U) (hinj : InjOn f U)
    (hJ : ∀ p ∈ U, (fderiv ℝ f p).det = J p ∧ 0 < J p) : PositiveChart f U J := by
  classical
  have hdet (x : E n) (hx : x ∈ U) : (fderiv ℝ f x).det ≠ 0 := by
    rw [(hJ x hx).1]
    exact (hJ x hx).2.ne'
  let p := hinj.toPartialEquiv f U
  have ho : IsOpenMap (p.source.domRestrict p) := by
    intro s hs
    change IsOpen ((fun x : U => f x) '' s)
    rw [show (fun x : U => f x) '' s = f '' (Subtype.val '' s) by rw [image_image]; rfl]
    apply open_image_of_nonsingular f U hf hdet _ (hU.isOpenMap_subtype_val s hs)
    rintro x ⟨z, _, rfl⟩
    exact z.property
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict p hf.continuous.continuousOn ho hU
  have he : (e : E n → E n) = f := rfl
  refine ⟨hJ, e, rfl, rfl, he, hf.contDiffOn, ?_⟩
  intro y hy
  have hx : e.symm y ∈ U := e.map_target hy
  let A : E n ≃L[ℝ] E n :=
    ((fderiv ℝ f (e.symm y)).toLinearMap.equivOfDetNeZero (hdet _ hx)).toContinuousLinearEquiv
  have hA : A.toContinuousLinearMap = fderiv ℝ f (e.symm y) := rfl
  apply (e.contDiffAt_symm hy (f₀' := A) ?_ hf.contDiffAt).contDiffWithinAt
  change HasFDerivAt f A.toContinuousLinearMap (e.symm y)
  rw [hA]
  exact (hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt

/-- The ordinary Riemann theorem specializes with the positive signed
Jacobian, and retains integrability in both directions for bounded data. -/
lemma coordinateSubstitution_of_positiveChart {n : ℕ} (f : E n → E n)
    (U : Set (E n)) (J : E n → ℝ) (hc : PositiveChart f U J) :
    CoordinateSubstitution f U J := by
  obtain ⟨hJ, e, hsource, _, heq, he, hei⟩ := hc
  subst U
  subst f
  intro K hK hcompact hKU
  have habs (x : K) : |(fderiv ℝ e x).det| = J x := by
    rw [(hJ x (hKU (subset_closure x.property))).1]
    exact abs_of_pos (hJ x (hKU (subset_closure x.property))).2
  have himage := RegionSubstitution.jordan_image e he hei K hK hcompact hKU
  refine ⟨himage.1, himage.2, ?_, ?_⟩
  · intro h hb
    have hs := RegionSubstitution.region_substitution e he hei K hK hcompact hKU h hb
    simpa only [habs] using hs
  · have hv := RegionSubstitution.volume_substitution e he hei K hK hcompact hKU
    simpa only [habs] using hv

theorem polar_chart : Specs.D04.C07.CoordinateCharts.polar_chartType := by
  intro α
  apply positiveChart_of_nonsingular polar (polarDomain α) (fun p => p 0)
    polar_contDiff (polarDomain_isOpen α) (polar_injOn α)
  intro p hp
  exact ⟨polar_det p, hp.1⟩

theorem cylindrical_chart : Specs.D04.C07.CoordinateCharts.cylindrical_chartType := by
  intro α
  apply positiveChart_of_nonsingular cylindrical (cylindricalDomain α) (fun p => p 0)
    cylindrical_contDiff (cylindricalDomain_isOpen α) (cylindrical_injOn α)
  intro p hp
  exact ⟨cylindrical_det p, hp.1⟩

theorem spherical_chart : Specs.D04.C07.CoordinateCharts.spherical_chartType := by
  intro α
  apply positiveChart_of_nonsingular spherical (sphericalDomain α)
    (fun p => (p 0)^2 * Real.sin (p 1))
    spherical_contDiff (sphericalDomain_isOpen α) (spherical_injOn α)
  intro p hp
  exact ⟨spherical_det p, mul_pos (sq_pos_of_pos hp.1)
    (Real.sin_pos_of_pos_of_lt_pi hp.2.1 hp.2.2.1)⟩

theorem polar_substitution : Specs.D04.C07.CoordinateCharts.polar_substitutionType :=
  fun α => coordinateSubstitution_of_positiveChart _ _ _ (polar_chart α)

theorem cylindrical_substitution : Specs.D04.C07.CoordinateCharts.cylindrical_substitutionType :=
  fun α => coordinateSubstitution_of_positiveChart _ _ _ (cylindrical_chart α)

theorem spherical_substitution : Specs.D04.C07.CoordinateCharts.spherical_substitutionType :=
  fun α => coordinateSubstitution_of_positiveChart _ _ _ (spherical_chart α)

end D04.CoordinateCharts
