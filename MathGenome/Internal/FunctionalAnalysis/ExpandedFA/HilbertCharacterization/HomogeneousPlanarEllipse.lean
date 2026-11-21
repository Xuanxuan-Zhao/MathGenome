import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.HilbertCharacterization.HomogeneousPlanarEllipse
import Mathlib.Analysis.Convex.Gauge
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open Set MeasureTheory
namespace ExpandedFA.HilbertCharacterization
namespace HomogeneousPlanarEllipse

/-- The oriented area pairing in auxiliary coordinates; the body is not assumed Euclidean. -/
def area (x y : Plane) : ℝ := x 0 * y 1 - x 1 * y 0

lemma area_smul_left (a : ℝ) (x y : Plane) : area (a • x) y = a * area x y := by
  simp [area, mul_sub]; ring

lemma area_smul_right (a : ℝ) (x y : Plane) : area x (a • y) = a * area x y := by
  simp [area]; ring

lemma continuous_area_right (x : Plane) : Continuous (area x) := by
  unfold area
  fun_prop

/-- A coordinate polynomial for the area-square moment. -/
def momentForm (D : Set Plane) : QuadraticForm ℝ Plane :=
  (∫ y in D, (y 1) ^ 2) • QuadraticMap.linMulLin (LinearMap.proj 0) (LinearMap.proj 0) -
  (2 * ∫ y in D, y 0 * y 1) • QuadraticMap.linMulLin (LinearMap.proj 0) (LinearMap.proj 1) +
  (∫ y in D, (y 0) ^ 2) • QuadraticMap.linMulLin (LinearMap.proj 1) (LinearMap.proj 1)

lemma momentForm_eq_integral {D : Set Plane} (hD : IsCompact D) (x : Plane) :
    momentForm D x = ∫ y in D, area x y ^ 2 := by
  have hi0 : IntegrableOn (fun y : Plane => (y 0) ^ 2) D :=
    (by fun_prop : Continuous (fun y : Plane => (y 0) ^ 2)).continuousOn.integrableOn_compact hD
  have hi1 : IntegrableOn (fun y : Plane => (y 1) ^ 2) D :=
    (by fun_prop : Continuous (fun y : Plane => (y 1) ^ 2)).continuousOn.integrableOn_compact hD
  have hi01 : IntegrableOn (fun y : Plane => y 0 * y 1) D :=
    (by fun_prop : Continuous (fun y : Plane => y 0 * y 1)).continuousOn.integrableOn_compact hD
  have hexp : (fun y => area x y ^ 2) =
      (fun y : Plane => (x 0)^2 * (y 1)^2 - (2*x 0*x 1) * (y 0*y 1) +
        (x 1)^2 * (y 0)^2) := by
    funext y
    simp only [area]
    ring
  rw [hexp]
  have hadd := integral_add ((hi1.const_mul ((x 0)^2)).sub (hi01.const_mul (2*x 0*x 1))) (hi0.const_mul ((x 1)^2))
  have hsub := integral_sub (hi1.const_mul ((x 0)^2)) (hi01.const_mul (2*x 0*x 1))
  simp only [Pi.sub_apply] at hadd
  rw [hadd, hsub]
  simp [momentForm, integral_const_mul, QuadraticMap.linMulLin_apply]
  ring

/-- Symmetry and convexity put the center in the interior; this is not an extra hypothesis. -/
lemma zero_mem_interior {D : Set Plane} (hc : Convex ℝ D) (hs : OriginSymmetric D)
    (hne : (interior D).Nonempty) : (0 : Plane) ∈ interior D := by
  obtain ⟨z, hz⟩ := hne
  have hn : -z ∈ interior D := by
    have hsub : Neg.neg ⁻¹' interior D ⊆ D := by
      intro y hy
      simpa using hs (-y) (interior_subset hy)
    exact (interior_maximal hsub (isOpen_interior.preimage continuous_neg))
      (by simpa using hz)
  have hm := hc.interior hz hn (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  simpa using hm

lemma area_map (A : Plane ≃ₗ[ℝ] Plane) (x y : Plane) :
    area (A x) (A y) = LinearMap.det A.toLinearMap * area x y := by
  have h := (Pi.basisFun ℝ (Fin 2)).det_comp A.toLinearMap ![x, y]
  rw [Pi.basisFun_det_apply, Pi.basisFun_det_apply] at h
  simpa [Matrix.det_fin_two, area, Function.comp_def] using h

/-- The area moment is strictly positive in every nonzero direction. -/
lemma momentForm_posDef {D : Set Plane} (hD : IsCompact D)
    (h0 : (0 : Plane) ∈ interior D) : (momentForm D).PosDef := by
  intro x hx
  let L : Plane →ₗ[ℝ] ℝ := (x 0) • LinearMap.proj 1 - (x 1) • LinearMap.proj 0
  have hL (y : Plane) : L y = area x y := by simp [L, area]
  have hne : (Function.support (fun y => area x y ^ 2) ∩ interior D).Nonempty := by
    by_contra h
    have hsub : interior D ⊆ (LinearMap.ker L : Set Plane) := by
      intro y hy
      change L y = 0
      rw [hL]
      by_contra hy0
      exact h ⟨y, (pow_ne_zero 2 hy0), hy⟩
    have htop : LinearMap.ker L = ⊤ :=
      (LinearMap.ker L).eq_top_of_nonempty_interior' ⟨0, interior_mono hsub (by simpa only [interior_interior] using h0)⟩
    have hz (y : Plane) : area x y = 0 := by
      rw [← hL]
      exact (show y ∈ LinearMap.ker L by rw [htop]; trivial)
    have hx0 := hz ![0, 1]
    have hx1 := hz ![1, 0]
    simp [area] at hx0 hx1
    exact hx (by ext i; fin_cases i <;> simp_all)
  rw [momentForm_eq_integral hD]
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall (fun y => sq_nonneg (area x y)))
    (((continuous_area_right x).pow 2).continuousOn.integrableOn_compact hD)).2
  have hopen : IsOpen (Function.support (fun y => area x y ^ 2) ∩ interior D) :=
    ((continuous_area_right x).pow 2).isOpen_support.inter isOpen_interior
  exact (hopen.measure_pos volume hne).trans_le
    (measure_mono (inter_subset_inter_right _ interior_subset))

lemma preimage_eq_of_image_eq {D : Set Plane} (A : Plane ≃ₗ[ℝ] Plane)
    (hA : A '' D = D) : A ⁻¹' D = D := by
  ext x
  change A x ∈ D ↔ x ∈ D
  constructor
  · intro hx
    rw [← hA] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    rwa [← A.injective hxy]
  · intro hx
    rw [← hA]
    exact mem_image_of_mem A hx

/-- Every automorphism preserves area, because the body has finite positive area. -/
lemma abs_det_eq_one {D : Set Plane} (hD : IsCompact D)
    (h0 : (0 : Plane) ∈ interior D) (A : Plane ≃ₗ[ℝ] Plane) (hA : A '' D = D) :
    |LinearMap.det A.toLinearMap| = 1 := by
  have hvpos : 0 < volume D :=
    volume.measure_pos_of_mem_nhds (mem_interior_iff_mem_nhds.mp h0)
  have hm := Real.map_linearMap_volume_pi_eq_smul_volume_pi A.isUnit_det'.ne_zero
  have heq := congrArg (fun μ : Measure Plane => μ D) hm
  change (Measure.map A volume) D = (ENNReal.ofReal |(LinearMap.det A.toLinearMap)⁻¹| • volume) D at heq
  have hmeas : Measurable (A : Plane → Plane) := A.toContinuousLinearEquiv.continuous.measurable
  rw [Measure.map_apply hmeas hD.measurableSet,
    preimage_eq_of_image_eq A hA, Measure.smul_apply, smul_eq_mul] at heq
  have hc : ENNReal.ofReal |(LinearMap.det A.toLinearMap)⁻¹| = 1 := by
    apply (ENNReal.mul_eq_left hvpos.ne' hD.measure_ne_top).mp
    simpa [mul_comm, abs_inv] using heq.symm
  have hr := congrArg ENNReal.toReal hc
  rw [ENNReal.toReal_ofReal (abs_nonneg ((LinearMap.det A.toLinearMap)⁻¹)), ENNReal.toReal_one] at hr
  rw [abs_inv] at hr
  exact inv_eq_one.mp hr

/-- Lebesgue measure, including its restriction to the body, is preserved by its automorphisms. -/
lemma map_restrict_volume {D : Set Plane} (hD : IsCompact D)
    (h0 : (0 : Plane) ∈ interior D) (A : Plane ≃ₗ[ℝ] Plane) (hA : A '' D = D) :
    Measure.map A (volume.restrict D) = volume.restrict D := by
  have hm := Real.map_linearMap_volume_pi_eq_smul_volume_pi A.isUnit_det'.ne_zero
  have hm' : Measure.map A volume = volume := by
    simpa [abs_inv, abs_det_eq_one hD h0 A hA] using hm
  have hr := congrArg (fun μ : Measure Plane => μ.restrict D) hm'
  have hmeas : Measurable (A : Plane → Plane) := A.toContinuousLinearEquiv.continuous.measurable
  rw [Measure.restrict_map hmeas hD.measurableSet,
    preimage_eq_of_image_eq A hA] at hr
  exact hr

/-- The positive quadratic form furnished by the body is invariant under its linear automorphisms. -/
lemma momentForm_invariant {D : Set Plane} (hD : IsCompact D)
    (h0 : (0 : Plane) ∈ interior D) (A : Plane ≃ₗ[ℝ] Plane) (hA : A '' D = D) (x : Plane) :
    momentForm D (A x) = momentForm D x := by
  rw [momentForm_eq_integral hD, momentForm_eq_integral hD]
  let e : Plane ≃ᵐ Plane := A.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hi := integral_map_equiv (μ := volume.restrict D) e (fun y => area (A x) y ^ 2)
  change (∫ y, area (A x) y ^ 2 ∂Measure.map A (volume.restrict D)) =
    ∫ y in D, area (A x) (A y) ^ 2 at hi
  rw [map_restrict_volume hD h0 A hA] at hi
  rw [hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  change area (A x) (A y) ^ 2 = area x y ^ 2
  rw [area_map, mul_pow]
  have hdet : LinearMap.det A.toLinearMap ^ 2 = 1 := by
    have hh := abs_det_eq_one hD h0 A hA
    nlinarith [sq_abs (LinearMap.det A.toLinearMap)]
  rw [hdet, one_mul]

/-- Each nonzero vector has a positive radial rescaling on the boundary. -/
lemma normalize_mem_frontier {D : Set Plane} (hD : IsCompact D) (hc : Convex ℝ D)
    (h0 : (0 : Plane) ∈ interior D) {x : Plane} (hx : x ≠ 0) :
    (gauge D x)⁻¹ • x ∈ frontier D := by
  have hn := mem_interior_iff_mem_nhds.mp h0
  have ht : 0 < gauge D x :=
    (gauge_pos (absorbent_nhds_zero hn) (hD.isVonNBounded ℝ)).2 hx
  apply (gauge_eq_one_iff_mem_frontier hc hn).mp
  rw [gauge_smul_of_nonneg (inv_nonneg.mpr ht.le), smul_eq_mul, inv_mul_cancel₀ ht.ne']

/-- Boundary transitivity of a symmetric planar convex body forces it to be an ellipse. -/
theorem homogeneous_planar_ellipse (D : Set Plane) (hD : IsCompact D) (hc : Convex ℝ D)
    (hs : OriginSymmetric D) (hne : (interior D).Nonempty) (htrans : BoundaryTransitive D) :
    IsEllipse D := by
  have h0 := zero_mem_interior hc hs hne
  have hn := mem_interior_iff_mem_nhds.mp h0
  have hpos := momentForm_posDef hD h0
  let u : Plane := ![1, 0]
  have hu : u ≠ 0 := by
    intro h
    have := congrFun h 0
    norm_num [u] at this
  let p : Plane := (gauge D u)⁻¹ • u
  have hp : p ∈ frontier D := normalize_mem_frontier hD hc h0 hu
  have hgu : 0 < gauge D u :=
    (gauge_pos (absorbent_nhds_zero hn) (hD.isVonNBounded ℝ)).2 hu
  have hpne : p ≠ 0 := smul_ne_zero (inv_ne_zero hgu.ne') hu
  have hcp : 0 < momentForm D p := hpos p hpne
  have hconst (y : Plane) (hy : y ∈ frontier D) : momentForm D y = momentForm D p := by
    obtain ⟨A, hA, hAy⟩ := htrans p hp y hy
    rw [← hAy]
    exact momentForm_invariant hD h0 A hA p
  refine ⟨momentForm D, hpos, momentForm D p, hcp, ?_⟩
  ext x
  change x ∈ D ↔ momentForm D x ≤ momentForm D p
  by_cases hx : x = 0
  · subst x
    exact iff_of_true (interior_subset h0) (by simpa using hcp.le)
  have ht : 0 < gauge D x :=
    (gauge_pos (absorbent_nhds_zero hn) (hD.isVonNBounded ℝ)).2 hx
  have hq : momentForm D x = (gauge D x) ^ 2 * momentForm D p := by
    calc
      momentForm D x = momentForm D ((gauge D x) • ((gauge D x)⁻¹ • x)) := by
        rw [smul_inv_smul₀ ht.ne']
      _ = (gauge D x) ^ 2 * momentForm D p := by
        rw [QuadraticMap.map_smul, hconst _ (normalize_mem_frontier hD hc h0 hx)]
        simp [pow_two]
  have hmem : x ∈ D ↔ gauge D x ≤ 1 := by
    simpa only [hD.isClosed.closure_eq] using (gauge_le_one_iff_mem_closure hc hn (x := x)).symm
  rw [hmem, hq]
  have hcancel : (gauge D x) ^ 2 * momentForm D p ≤ momentForm D p ↔ (gauge D x) ^ 2 ≤ 1 := by
    simpa using (mul_le_mul_iff_left₀ hcp :
      (gauge D x)^2 * momentForm D p ≤ 1 * momentForm D p ↔ (gauge D x)^2 ≤ 1)
  rw [hcancel]
  constructor <;> intro h <;> nlinarith

end HomogeneousPlanarEllipse
end ExpandedFA.HilbertCharacterization
