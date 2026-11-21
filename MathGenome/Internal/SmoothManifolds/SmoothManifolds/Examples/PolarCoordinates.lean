import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Examples.SpheresAndTori
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Examples.PolarCoordinates
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

namespace SmoothManifolds.PolarCoordinates
open PolarData Set Filter
open scoped Topology ContDiff

lemma analytic_polar : ContDiff ℝ ω polar := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [polar] <;> fun_prop

theorem smooth : Specs.SmoothManifolds.Examples.PolarCoordinates.smoothType :=
  analytic_polar.of_le (by simp)

noncomputable def polarDerivative (x : Euclidean 2) : Euclidean 2 →L[ℝ] Euclidean 2 :=
  (Matrix.toLin' !![-(2*Real.pi)*x 1*Real.sin (2*Real.pi*x 0), Real.cos (2*Real.pi*x 0);
    (2*Real.pi)*x 1*Real.cos (2*Real.pi*x 0), Real.sin (2*Real.pi*x 0)]).toContinuousLinearMap

lemma hasFDerivAt_polar (x : Euclidean 2) : HasFDerivAt polar (polarDerivative x) x := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 0 x
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 1 x
  have hc := ((h0.const_mul (2*Real.pi)).cos)
  have hs := ((h0.const_mul (2*Real.pi)).sin)
  rw [hasFDerivAt_pi']
  intro i
  fin_cases i
  · convert h1.mul hc using 1 <;>
      (ext v; simp [polar, polarDerivative, Matrix.toLin'_apply,
        dotProduct, Fin.sum_univ_two] <;> ring)
  · convert h1.mul hs using 1 <;>
      (ext v; simp [polar, polarDerivative, Matrix.toLin'_apply,
        dotProduct, Fin.sum_univ_two] <;> ring)

lemma det_polarDerivative (x : Euclidean 2) : (polarDerivative x).det = -2*Real.pi*x 1 := by
  simp only [polarDerivative, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin',
    Matrix.det_fin_two_of]
  calc
    _ = (-2*Real.pi*x 1) * (Real.cos (2*Real.pi*x 0)^2 + Real.sin (2*Real.pi*x 0)^2) := by ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq, mul_one]

theorem jacobian : Specs.SmoothManifolds.Examples.PolarCoordinates.jacobianType := by
  intro x
  rw [(hasFDerivAt_polar x).fderiv, det_polarDerivative]

noncomputable def derivativeEquiv (x : Euclidean 2) (hx : 0 < x 1) :
    Euclidean 2 ≃L[ℝ] Euclidean 2 :=
  (LinearMap.equivOfIsUnitDet (f := (polarDerivative x).toLinearMap)
    (by change IsUnit ((polarDerivative x).det)
        rw [det_polarDerivative]
        exact isUnit_iff_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hx.ne'))).toContinuousLinearEquiv

lemma derivativeEquiv_coe (x : Euclidean 2) (hx : 0 < x 1) :
    (derivativeEquiv x hx : Euclidean 2 →L[ℝ] Euclidean 2) = polarDerivative x := by
  ext v i
  simp [derivativeEquiv]

lemma hasFDerivAt_polar_equiv (x : Euclidean 2) (hx : 0 < x 1) :
    HasFDerivAt polar (derivativeEquiv x hx : Euclidean 2 →L[ℝ] Euclidean 2) x := by
  rw [derivativeEquiv_coe]
  exact hasFDerivAt_polar x

lemma inverse_smooth (e : OpenPartialHomeomorph (Euclidean 2) (Euclidean 2))
    (he : ∀ y, e y = polar y) (hr : ∀ y ∈ e.source, 0 < y 1) :
    ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target := by
  have heq : (e : Euclidean 2 → Euclidean 2) = polar := funext he
  intro y hy
  apply ContDiffAt.contDiffWithinAt
  apply e.contDiffAt_symm hy (f₀' := derivativeEquiv (e.symm y) (hr _ (e.map_target hy)))
  · rw [heq]
    exact hasFDerivAt_polar_equiv _ _
  · rw [heq]
    exact smooth.contDiffAt

theorem localInverse : Specs.SmoothManifolds.Examples.PolarCoordinates.localInverseType := by
  intro x hx
  let e := analytic_polar.contDiffAt.toOpenPartialHomeomorph polar (hasFDerivAt_polar_equiv x hx) (by simp)
  let U : Set (Euclidean 2) := {y | 0 < y 1}
  have hU : IsOpen U := isOpen_lt continuous_const (continuous_apply 1)
  let d := e.restr U
  have hd : ∀ y, d y = polar y := fun _ => rfl
  have hpos : ∀ y ∈ d.source, 0 < y 1 := by
    intro y hy
    have : y ∈ U := interior_subset hy.2
    exact this
  refine ⟨d, ?_, hd, hpos, inverse_smooth d hd hpos⟩
  change x ∈ e.source ∩ interior U
  rw [hU.interior_eq]
  exact ⟨analytic_polar.contDiffAt.mem_toOpenPartialHomeomorph_source _ _, hx⟩

lemma anglePoint_fiber (s t : ℝ) :
    SphereTorusData.anglePoint s = SphereTorusData.anglePoint t ↔
      ∃ k : ℤ, s = t + k := by
  have he : SphereTorusData.anglePoint s = SphereTorusData.anglePoint t ↔
      SphereTorusData.quotientProjection 1 (fun _ => s) =
        SphereTorusData.quotientProjection 1 (fun _ => t) := by
    rw [← (SphereTorus.periodicAngleHomeomorph 1).injective.eq_iff]
    rw [SphereTorus.periodicAngleHomeomorph_apply, SphereTorus.periodicAngleHomeomorph_apply]
    constructor
    · intro h; funext j; exact h
    · intro h; exact congrFun h 0
  rw [he, SphereTorus.quotientProjection_fiber]
  constructor
  · rintro ⟨z, hz⟩; exact ⟨z 0, hz 0⟩
  · rintro ⟨k, hk⟩; exact ⟨fun _ => k, fun _ => hk⟩

lemma polar_squareSum (x : Euclidean 2) :
    SphereTorusData.squareSum (polar x) = (x 1)^2 := by
  simp only [SphereTorusData.squareSum, Fin.sum_univ_two, polar,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  calc
    _ = (x 1)^2 * (Real.cos (2*Real.pi*x 0)^2 + Real.sin (2*Real.pi*x 0)^2) := by ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq, mul_one]

theorem fibers : Specs.SmoothManifolds.Examples.PolarCoordinates.fibersType := by
  intro x y hx hy
  constructor
  · intro h
    have hr : x 1 = y 1 := by
      have := congrArg SphereTorusData.squareSum h
      rw [polar_squareSum, polar_squareSum] at this
      nlinarith
    refine ⟨hr, (anglePoint_fiber _ _).mp ?_⟩
    apply Subtype.ext
    funext i
    have hi := congrFun h i
    fin_cases i <;> simp [polar, SphereTorusData.anglePoint, hr, hy.ne'] at hi ⊢ <;>
      exact hi
  · rintro ⟨hr, hk⟩
    have ha := congrArg Subtype.val ((anglePoint_fiber _ _).mpr hk)
    funext i
    have hi := congrFun ha i
    fin_cases i <;> simpa [polar, SphereTorusData.anglePoint, hr] using congrArg (fun z : ℝ => y 1 * z) hi

theorem injective : Specs.SmoothManifolds.Examples.PolarCoordinates.injectiveType := by
  intro a b hab x hx y hy he
  obtain ⟨hr, k, hk⟩ := (fibers x y hx.2.2 hy.2.2).mp he
  have hlt : |(k : ℝ)| < 1 := abs_lt.mpr ⟨by linarith [hx.1, hx.2.1, hy.1, hy.2.1],
    by linarith [hx.1, hx.2.1, hy.1, hy.2.1]⟩
  have hk0 : k = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hlt)
  funext i
  fin_cases i
  · simpa [hk0] using hk
  · exact hr

lemma isOpen_image_polar {U : Set (Euclidean 2)} (hU : IsOpen U)
    (hpos : ∀ x ∈ U, 0 < x 1) : IsOpen (polar '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨e, hxe, he, _, _⟩ := localInverse x (hpos x hx)
  have heq : (e : Euclidean 2 → Euclidean 2) = polar := funext he
  have hm : e '' U ∈ Filter.map e (𝓝 x) := Filter.image_mem_map (hU.mem_nhds hx)
  rw [e.map_nhds_eq hxe, heq] at hm
  exact hm

lemma isOpen_sector (a δ r₀ r₁ : ℝ) : IsOpen (sector a δ r₀ r₁) := by
  exact (isOpen_lt (((continuous_apply 0).sub continuous_const).abs) continuous_const).inter
    ((isOpen_lt continuous_const (continuous_apply 1)).inter
      (isOpen_lt (continuous_apply 1) continuous_const))

lemma injOn_sector {a δ r₀ r₁ : ℝ} (hδ : δ < 1/4) (hr₀ : 0 < r₀) :
    InjOn polar (sector a δ r₀ r₁) := by
  apply (injective (a-δ) (a+δ) (by linarith)).mono
  intro x hx
  have ha := abs_lt.mp hx.1
  exact ⟨by linarith, by linarith, lt_trans hr₀ hx.2.1⟩

noncomputable def sectorParametrization (a δ r₀ r₁ : ℝ)
    (hδ : δ < 1/4) (hr₀ : 0 < r₀) :
    OpenPartialHomeomorph (Euclidean 2) (Euclidean 2) :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict
    ((injOn_sector hδ hr₀).toPartialEquiv polar (sector a δ r₀ r₁))
    smooth.continuous.continuousOn
    (by
      change IsOpenMap ((sector a δ r₀ r₁).domRestrict polar)
      intro U hU
      change IsOpen ((fun x : sector a δ r₀ r₁ => polar x.val) '' U)
      rw [← image_image]
      exact isOpen_image_polar ((isOpen_sector a δ r₀ r₁).isOpenMap_subtype_val U hU)
        (by rintro x ⟨z, _, rfl⟩; exact lt_trans hr₀ z.property.2.1))
    (isOpen_sector a δ r₀ r₁)

theorem sectors : Specs.SmoothManifolds.Examples.PolarCoordinates.sectorType := by
  intro a δ r₀ r₁ _ hδ hr₀ _
  let e := sectorParametrization a δ r₀ r₁ hδ hr₀
  have he : ∀ x, e x = polar x := fun _ => rfl
  refine ⟨e, rfl, rfl, he, inverse_smooth e he ?_⟩
  intro x hx
  exact lt_trans hr₀ hx.2.1

noncomputable def reflectionLinear : Euclidean 2 →L[ℝ] Euclidean 2 :=
  (Matrix.toLin' !![-1, 0; 0, 1]).toContinuousLinearMap

lemma reflectionLinear_apply (x : Euclidean 2) : reflectionLinear x = reflect x := by
  ext i
  fin_cases i <;> simp [reflectionLinear, reflect, Matrix.toLin'_apply,
    dotProduct, Fin.sum_univ_two]

lemma hasFDerivAt_reflect (x : Euclidean 2) : HasFDerivAt reflect reflectionLinear x := by
  convert reflectionLinear.hasFDerivAt using 1
  exact (funext reflectionLinear_apply).symm

lemma det_reflectionLinear : reflectionLinear.det = -1 := by
  simp [reflectionLinear, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin',
    Matrix.det_fin_two_of]

theorem reflection : Specs.SmoothManifolds.Examples.PolarCoordinates.reflectionType := by
  constructor
  · intro x
    rw [(hasFDerivAt_reflect x).fderiv, det_reflectionLinear]
  · intro s r
    have h : 2*Real.pi*(1/2-s) = Real.pi - 2*Real.pi*s := by ring
    ext i
    fin_cases i
    · change -(r * Real.cos (2*Real.pi*s)) = r * Real.cos (2*Real.pi*(1/2-s))
      rw [h, Real.cos_pi_sub, mul_neg]
    · change r * Real.sin (2*Real.pi*s) = r * Real.sin (2*Real.pi*(1/2-s))
      rw [h, Real.sin_pi_sub]

noncomputable def radialShift (σ : ℝ) (x : Euclidean 2) : Euclidean 2 :=
  ![x 0, 1/8 + σ*x 1]

noncomputable def radialLinear (σ : ℝ) : Euclidean 2 →L[ℝ] Euclidean 2 :=
  (Matrix.toLin' !![1, 0; 0, σ]).toContinuousLinearMap

lemma analytic_radialShift (σ : ℝ) : ContDiff ℝ ω (radialShift σ) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [radialShift] <;> fun_prop

lemma hasFDerivAt_radialShift (σ : ℝ) (x : Euclidean 2) :
    HasFDerivAt (radialShift σ) (radialLinear σ) x := by
  rw [hasFDerivAt_pi']
  intro i
  fin_cases i
  · convert (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 0 x) using 1 <;>
      (ext v; simp [radialShift, radialLinear, Matrix.toLin'_apply,
        dotProduct, Fin.sum_univ_two])
  · convert (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 1 x).const_mul σ |>.const_add (1/8) using 1 <;>
      (ext v; simp [radialShift, radialLinear, Matrix.toLin'_apply,
        dotProduct, Fin.sum_univ_two])

lemma det_radialLinear (σ : ℝ) : (radialLinear σ).det = σ := by
  simp [radialLinear, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin',
    Matrix.det_fin_two_of]

lemma det_comp (A B : Euclidean 2 →L[ℝ] Euclidean 2) :
    (A.comp B).det = A.det * B.det := LinearMap.det_comp A.toLinearMap B.toLinearMap

lemma smooth_positiveCollar : ContDiff ℝ (⊤ : ℕ∞) positiveCollar := by
  have he : positiveCollar = polar ∘ radialShift 1 := by
    funext x; simp [positiveCollar, radialShift, Function.comp_def]
  rw [he]
  exact smooth.comp ((analytic_radialShift 1).of_le (by simp))

lemma smooth_negativeCollar : ContDiff ℝ (⊤ : ℕ∞) negativeCollar := by
  have he : negativeCollar = reflectionLinear ∘ polar ∘ radialShift (-1) := by
    funext x; simp [negativeCollar, radialShift, Function.comp_def, reflectionLinear_apply, sub_eq_add_neg]
  rw [he]
  exact reflectionLinear.contDiff.comp (smooth.comp ((analytic_radialShift (-1)).of_le (by simp)))

lemma positiveCollar_jacobian (x : Euclidean 2) :
    (fderiv ℝ positiveCollar x).det = -2*Real.pi*(1/8+x 1) := by
  have hd := (hasFDerivAt_polar (radialShift 1 x)).comp x (hasFDerivAt_radialShift 1 x)
  have he : positiveCollar = polar ∘ radialShift 1 := by
    funext x; simp [positiveCollar, radialShift, Function.comp_def]
  rw [he, hd.fderiv, det_comp, det_polarDerivative, det_radialLinear]
  simp [radialShift]

lemma negativeCollar_jacobian (x : Euclidean 2) :
    (fderiv ℝ negativeCollar x).det = -2*Real.pi*(1/8-x 1) := by
  have hd := (hasFDerivAt_reflect (polar (radialShift (-1) x))).comp x
    ((hasFDerivAt_polar (radialShift (-1) x)).comp x (hasFDerivAt_radialShift (-1) x))
  have he : negativeCollar = reflect ∘ (polar ∘ radialShift (-1)) := by
    funext x; simp [negativeCollar, radialShift, Function.comp_def, sub_eq_add_neg]
  rw [he, hd.fderiv, det_comp, det_comp, det_reflectionLinear, det_polarDerivative, det_radialLinear]
  simp [radialShift, sub_eq_add_neg]

theorem collars : Specs.SmoothManifolds.Examples.PolarCoordinates.collarType := by
  refine ⟨smooth_positiveCollar, smooth_negativeCollar, positiveCollar_jacobian,
    negativeCollar_jacobian, ?_, ?_⟩
  · intro x hx
    rw [positiveCollar_jacobian]
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) Real.pi_pos) hx
  · intro x hx
    rw [negativeCollar_jacobian]
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) Real.pi_pos) hx

/-- The same period-one circle used in the torus angle convention. -/
lemma polar_eq_smul_anglePoint (s r : ℝ) :
    PolarData.polar ![s,r] = r • (SphereTorusData.anglePoint s).val := by
  ext i
  fin_cases i <;> simp [PolarData.polar, SphereTorusData.anglePoint]

lemma polar_periodic (s r : ℝ) : PolarData.polar ![s+1,r] = PolarData.polar ![s,r] := by
  rw [polar_eq_smul_anglePoint, polar_eq_smul_anglePoint]
  rw [(anglePoint_fiber (s+1) s).mpr ⟨1, by norm_num⟩]

@[simp] lemma sectorParametrization_source (a δ r₀ r₁ : ℝ)
    (hδ : δ < 1/4) (hr₀ : 0 < r₀) :
    (sectorParametrization a δ r₀ r₁ hδ hr₀).source = PolarData.sector a δ r₀ r₁ := rfl

@[simp] lemma sectorParametrization_target (a δ r₀ r₁ : ℝ)
    (hδ : δ < 1/4) (hr₀ : 0 < r₀) :
    (sectorParametrization a δ r₀ r₁ hδ hr₀).target =
      PolarData.polar '' PolarData.sector a δ r₀ r₁ := rfl

@[simp] lemma sectorParametrization_apply (a δ r₀ r₁ : ℝ)
    (hδ : δ < 1/4) (hr₀ : 0 < r₀) (x : Euclidean 2) :
    sectorParametrization a δ r₀ r₁ hδ hr₀ x = PolarData.polar x := rfl

lemma sectorParametrization_symm_smooth (a δ r₀ r₁ : ℝ)
    (hδ : δ < 1/4) (hr₀ : 0 < r₀) :
    ContDiffOn ℝ (⊤ : ℕ∞) (sectorParametrization a δ r₀ r₁ hδ hr₀).symm
      (PolarData.polar '' PolarData.sector a δ r₀ r₁) :=
  inverse_smooth _ (fun _ => rfl) (fun _ hx => lt_trans hr₀ hx.2.1)

/- Transparent public aliases of the canonical independent data. -/
noncomputable abbrev polar := PolarData.polar
abbrev reflect := PolarData.reflect
abbrev sector := PolarData.sector
noncomputable abbrev positiveCollar := PolarData.positiveCollar
noncomputable abbrev negativeCollar := PolarData.negativeCollar

end SmoothManifolds.PolarCoordinates
