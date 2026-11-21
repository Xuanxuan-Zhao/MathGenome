import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.HardyAveragingC1
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.HardyAveragingContinuous
import Mathlib.MeasureTheory.Integral.Prod
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.HardyAveragingRealBridge

set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Set
open scoped unitInterval Topology
namespace ExpandedFA.PartV.HardyAveragingC1
open Spec


@[simp] lemma primitive_zero (v : CSpace) : primitive v 0 = 0 := by
  simp [primitive, position, ContinuousLinearMap.mul_apply']

theorem primitive_formula : Spec.PrimitiveFormula := by
  intro v x
  change (x : ℂ) * HardyAveragingContinuous.hardy v x = _
  by_cases hx : (x : ℝ) = 0
  · simp [hx]
  · rw [HardyAveragingContinuous.hardy_apply_pos v x (lt_of_le_of_ne x.property.1 (Ne.symm hx))]
    have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx
    rw [← mul_assoc, mul_inv_cancel₀ hxc, one_mul]

lemma mem_c1_iff (f v : CSpace) : (f, v) ∈ c1Subspace ↔
    ∀ x : I, f x = f 0 + primitive v x := by
  change (graphMap (f, v) = 0) ↔ _
  constructor
  · intro h x
    have hx := congrArg (fun g : CSpace => g x) h
    change f x - f 0 - primitive v x = 0 at hx
    linear_combination hx
  · intro h
    ext x
    change f x - f 0 - primitive v x = 0
    rw [h x]; ring

lemma primitive_hasDerivWithinAt (v : CSpace) (x : I) :
    HasDerivWithinAt (HardyAveragingContinuous.Spec.extension (primitive v)) (v x)
      (Icc (0 : ℝ) 1) (x : ℝ) := by
  have hd := intervalIntegral.integral_hasDerivAt_right
    ((HardyAveragingContinuous.Spec.extension v).continuous.intervalIntegrable 0 (x : ℝ))
    (HardyAveragingContinuous.Spec.extension v).continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    (HardyAveragingContinuous.Spec.extension v).continuous.continuousAt
  rw [HardyAveragingContinuous.extension_apply] at hd
  apply hd.hasDerivWithinAt.congr
  · intro t ht
    exact (HardyAveragingContinuous.extension_apply (primitive v) ⟨t, ht⟩).trans (primitive_formula v ⟨t, ht⟩)
  · exact (HardyAveragingContinuous.extension_apply (primitive v) x).trans (primitive_formula v x)

theorem c1_characterization : Spec.C1Characterization := by
  intro f v
  rw [mem_c1_iff]
  constructor
  · intro h x
    have hd := (primitive_hasDerivWithinAt v x).const_add (f 0)
    apply hd.congr
    · intro t ht
      rw [HardyAveragingContinuous.extension_apply f ⟨t, ht⟩, HardyAveragingContinuous.extension_apply (primitive v) ⟨t, ht⟩]
      exact h ⟨t, ht⟩
    · rw [HardyAveragingContinuous.extension_apply f x, HardyAveragingContinuous.extension_apply (primitive v) x]
      exact h x
  · intro hd x
    rw [primitive_formula]
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le x.property.1
      (HardyAveragingContinuous.Spec.extension f).continuous.continuousOn
      (fun t ht => by
        have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le.trans x.property.2⟩
        have hdt := hd ⟨t, htI⟩
        rw [← HardyAveragingContinuous.extension_apply v ⟨t, htI⟩] at hdt
        exact hdt.hasDerivAt (Icc_mem_nhds ht.1 (ht.2.trans_le x.property.2)))
      ((HardyAveragingContinuous.Spec.extension v).continuous.intervalIntegrable 0 (x : ℝ))
    rw [HardyAveragingContinuous.extension_apply f x] at hi
    have h0 : HardyAveragingContinuous.Spec.extension f 0 = f 0 :=
      HardyAveragingContinuous.extension_apply f (0 : I)
    rw [h0] at hi
    rw [hi]; ring

instance : CompleteSpace Space := (graphMap.isClosed_ker).completeSpace_coe

theorem c1_complete : Spec.C1Complete := by unfold Spec.C1Complete; infer_instance

/-- The inverse map reconstructs a function from its value at zero and its
continuous derivative, with both components in the standard C¹ norm. -/
def fromCoordinates : (ℂ × CSpace) →L[ℂ] Space :=
  ((constant.comp (ContinuousLinearMap.fst ℂ ℂ CSpace) +
    primitive.comp (ContinuousLinearMap.snd ℂ ℂ CSpace)).prod
    (ContinuousLinearMap.snd ℂ ℂ CSpace)).codRestrict c1Subspace (by
      intro p
      apply (mem_c1_iff _ _).mpr
      intro x
      change p.1 + primitive p.2 x = p.1 + primitive p.2 0 + primitive p.2 x
      rw [primitive_zero, add_zero])

@[simp] lemma coordinates_fromCoordinates (p : ℂ × CSpace) :
    coordinates (fromCoordinates p) = p := by
  apply Prod.ext
  · change p.1 + primitive p.2 0 = p.1
    rw [primitive_zero, add_zero]
  · rfl

@[simp] lemma fromCoordinates_coordinates (f : Space) :
    fromCoordinates (coordinates f) = f := by
  apply Subtype.ext
  apply Prod.ext
  · ext x
    change f.val.1 0 + primitive f.val.2 x = f.val.1 x
    exact ((mem_c1_iff _ _).mp f.property x).symm
  · rfl

def coordinateEquiv : Space ≃L[ℂ] (ℂ × CSpace) :=
  { coordinates with
    invFun := fromCoordinates
    left_inv := fromCoordinates_coordinates
    right_inv := coordinates_fromCoordinates
    continuous_invFun := fromCoordinates.continuous }

theorem coordinate_isomorphism : Spec.CoordinateIsomorphism := ⟨coordinateEquiv, rfl⟩

lemma primitive_apply (v : CSpace) (x : I) : primitive v x =
    (x : ℂ) * HardyAveragingContinuous.hardy v x := rfl

/-- Fubini gives Q P = P R. All integrands are continuous on the compact
square, so the identity also includes x=0. -/
lemma hardy_primitive (v : CSpace) :
    HardyAveragingContinuous.hardy (primitive v) = primitive (weightedOperator v) := by
  ext x
  have hs := integral_integral_swap_of_hasCompactSupport
    (f := fun r s : I => (r : ℂ) * v (s * (r * x)))
    (by fun_prop) (HasCompactSupport.of_compactSpace _)
    (μ := volume) (ν := volume)
  calc
    _ = ∫ r : I, ((r * x : I) : ℂ) *
        ∫ s : I, v (s * (r * x)) := by
      rw [HardyAveragingContinuous.hardy_apply]
      apply integral_congr_ae
      filter_upwards [] with r
      rw [primitive_apply, HardyAveragingContinuous.hardy_apply]
    _ = (x : ℂ) * ∫ r : I, ∫ s : I, (r : ℂ) * v (s * (r * x)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with r
      rw [integral_const_mul]
      simp only [Set.Icc.coe_mul, Complex.ofReal_mul]
      ring
    _ = (x : ℂ) * ∫ s : I, ∫ r : I, (r : ℂ) * v (s * (r * x)) := by rw [hs]
    _ = primitive (weightedOperator v) x := by
      rw [primitive_apply, HardyAveragingContinuous.hardy_apply]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with s
      change _ = (∫ r : I, weightedDilation v r) (s * x)
      rw [ContinuousMap.integral_apply
        ((weightedDilation v).continuous.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))]
      apply integral_congr_ae
      filter_upwards [] with r
      change (r : ℂ) * v (s * (r * x)) = (r : ℂ) * v (r * (s * x))
      rw [mul_left_comm s r x]

/-- Q on C¹, constructed by the proved coordinate isomorphism. -/
def hardy : Space →L[ℂ] Space :=
  fromCoordinates.comp (blockOperator.comp coordinates)

@[simp] lemma hardy_coordinates (f : Space) :
    coordinates (hardy f) = blockOperator (coordinates f) :=
  coordinates_fromCoordinates _

theorem coordinate_formula : Spec.CoordinateFormula hardy := hardy_coordinates

/-- This bridge verifies that the coordinate construction is the source's
actual Hardy averaging operator on functions. -/
theorem hardy_value (f : Space) :
    value (hardy f) = HardyAveragingContinuous.Spec.operatorValue (value f) := by
  have hf : value f = constant (value f 0) + primitive (derivative f) := by
    ext x
    exact (mem_c1_iff _ _).mp f.property x
  change constant (value f 0) + primitive (weightedOperator (derivative f)) = _
  calc
    _ = HardyAveragingContinuous.hardy
        (constant (value f 0) + primitive (derivative f)) := by
      rw [map_add, hardy_primitive]
      congr 1
      exact (HardyAveragingContinuous.hardy_const _).symm
    _ = _ := congrArg HardyAveragingContinuous.hardy hf.symm

/-- The square-root substitution is a homeomorphism of the entire closed interval. -/
def rootMap : C(I, I) :=
  ⟨fun y => ⟨Real.sqrt y, Real.sqrt_nonneg _, Real.sqrt_le_one.mpr y.property.2⟩,
    by fun_prop⟩

def squareMap : C(I, I) := ⟨fun x => x * x, by fun_prop⟩

@[simp] lemma square_root (y : I) : squareMap (rootMap y) = y := by
  apply Subtype.ext
  exact Real.mul_self_sqrt y.property.1

@[simp] lemma root_square (x : I) : rootMap (squareMap x) = x := by
  apply Subtype.ext
  exact Real.sqrt_mul_self x.property.1

def squareSubstitution : CSpace ≃L[ℂ] CSpace :=
  { ContinuousMap.compCLM ℂ ℂ rootMap with
    invFun := ContinuousMap.compCLM ℂ ℂ squareMap
    left_inv := by intro v; ext x; change v (rootMap (squareMap x)) = v x; rw [root_square]
    right_inv := by intro v; ext x; change v (squareMap (rootMap x)) = v x; rw [square_root]
    continuous_invFun := (ContinuousMap.compCLM ℂ ℂ squareMap).continuous }

lemma weighted_apply (v : CSpace) (x : I) :
    weightedOperator v x = ∫ r : I, (r : ℂ) * v (r * x) := by
  change (∫ r : I, weightedDilation v r) x = _
  exact ContinuousMap.integral_apply
    ((weightedDilation v).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) x

lemma weighted_apply_interval (v : CSpace) (x : I) :
    weightedOperator v x = ∫ r in (0 : ℝ)..1,
      (r : ℂ) * HardyAveragingContinuous.Spec.extension v (r * (x : ℝ)) := by
  rw [weighted_apply]
  have heq : (fun r : I => (r : ℂ) * v (r * x)) =
      (fun r : I => (r : ℂ) * HardyAveragingContinuous.Spec.extension v
        ((r : ℝ) * (x : ℝ))) := by
    funext r
    exact congrArg (fun z : ℂ => (r : ℂ) * z) (HardyAveragingContinuous.extension_apply v (r * x)).symm
  rw [heq]
  rw [integral_subtype measurableSet_Icc
    (fun r : ℝ => (r : ℂ) * HardyAveragingContinuous.Spec.extension v (r * (x : ℝ)))]
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]

lemma squared_hardy (v : CSpace) (x : I) :
    HardyAveragingContinuous.hardy (squareSubstitution v) (x * x) =
      2 * weightedOperator v x := by
  rw [HardyAveragingContinuous.hardy_apply_interval, weighted_apply_interval]
  have hsub := intervalIntegral.integral_deriv_smul_comp
    (a := (0 : ℝ)) (b := 1) (f := fun r : ℝ => r * r) (f' := fun r => 2 * r)
    (g := fun s => HardyAveragingContinuous.Spec.extension (squareSubstitution v)
      (s * ((x * x : I) : ℝ)))
    (by intro r hr; convert! (hasDerivAt_pow 2 r) using 1 <;> simp [pow_two])
    (by fun_prop) (by fun_prop)
  simp only [zero_mul, mul_one, Function.comp_apply] at hsub
  rw [← hsub, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le zero_le_one] at hr
  let ri : I := ⟨r, hr⟩
  have hp : r * r * ((x * x : I) : ℝ) =
      (((ri * x) * (ri * x) : I) : ℝ) := by change r * r * ((x : ℝ) * x) = (r * (x : ℝ)) * (r * x); ring
  dsimp only
  rw [hp, HardyAveragingContinuous.extension_apply]
  change (2 * r) • v (rootMap (squareMap (ri * x))) = _
  rw [root_square]
  have he : HardyAveragingContinuous.Spec.extension v (r * (x : ℝ)) = v (ri * x) :=
    HardyAveragingContinuous.extension_apply v (ri * x)
  rw [he]
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

lemma substitution_intertwines (v : CSpace) :
    squareSubstitution (weightedOperator v) =
      (1 / 2 : ℂ) • HardyAveragingContinuous.hardy (squareSubstitution v) := by
  ext y
  have h := squared_hardy v (rootMap y)
  have hy : rootMap y * rootMap y = y := square_root y
  rw [hy] at h
  change weightedOperator v (rootMap y) = (1 / 2 : ℂ) * _
  rw [h]
  ring

theorem square_substitution : Spec.SquareSubstitution :=
  ⟨squareSubstitution, by intros; rfl, by intros; rfl, substitution_intertwines⟩

lemma conjugate_weighted : squareSubstitution.conjContinuousAlgEquiv weightedOperator =
    (1 / 2 : ℂ) • HardyAveragingContinuous.hardy := by
  apply ContinuousLinearMap.ext
  intro v
  change squareSubstitution (weightedOperator (squareSubstitution.symm v)) = _
  rw [substitution_intertwines, squareSubstitution.apply_symm_apply]
  rfl

lemma scaled_spectrum_mem (z : ℂ) :
    z ∈ spectrum ℂ weightedOperator ↔
      ‖2 * z - (1 / 2 : ℂ)‖ ≤ (1 / 2 : ℝ) := by
  have hs := AlgEquiv.spectrum_eq squareSubstitution.conjContinuousAlgEquiv weightedOperator
  rw [conjugate_weighted] at hs
  rw [← hs]
  have h := spectrum.smul_mem_smul_iff
    (r := Units.mk0 (1 / 2 : ℂ) (by norm_num))
    (s := 2 * z) (a := HardyAveragingContinuous.hardy)
  have hz : (Units.mk0 (1 / 2 : ℂ) (by norm_num)) • (2 * z) = z := by
    change (1 / 2 : ℂ) * (2 * z) = z
    ring
  rw [hz] at h
  change z ∈ spectrum ℂ ((1 / 2 : ℂ) • HardyAveragingContinuous.hardy) ↔ _
  change (z ∈ spectrum ℂ ((1 / 2 : ℂ) • HardyAveragingContinuous.hardy) ↔
    2 * z ∈ spectrum ℂ HardyAveragingContinuous.hardy) at h
  rw [h]
  change 2 * z ∈ spectrum ℂ HardyAveragingContinuous.Spec.operatorValue ↔ _
  rw [HardyAveragingContinuous.spectrum_disk]
  rfl

lemma small_disk_scale_le (z : ℂ) :
    ‖2 * z - (1 / 2 : ℂ)‖ ≤ (1 / 2 : ℝ) ↔
      ‖z - (1 / 4 : ℂ)‖ ≤ (1 / 4 : ℝ) := by
  have he : 2 * z - (1 / 2 : ℂ) = 2 * (z - (1 / 4 : ℂ)) := by ring
  rw [he, norm_mul]
  norm_num
  constructor <;> intro h <;> linarith

lemma small_disk_scale_lt (z : ℂ) :
    ‖2 * z - (1 / 2 : ℂ)‖ < (1 / 2 : ℝ) ↔
      ‖z - (1 / 4 : ℂ)‖ < (1 / 4 : ℝ) := by
  have he : 2 * z - (1 / 2 : ℂ) = 2 * (z - (1 / 4 : ℂ)) := by ring
  rw [he, norm_mul]
  norm_num
  constructor <;> intro h <;> linarith

lemma weighted_spectrum_mem (z : ℂ) :
    z ∈ spectrum ℂ weightedOperator ↔
      ‖z - (1 / 4 : ℂ)‖ ≤ (1 / 4 : ℝ) :=
  (scaled_spectrum_mem z).trans (small_disk_scale_le z)

lemma block_spectrum_mem (z : ℂ) :
    z ∈ spectrum ℂ blockOperator ↔ z = 1 ∨ z ∈ spectrum ℂ weightedOperator := by
  have he : algebraMap ℂ ((ℂ × CSpace) →L[ℂ] (ℂ × CSpace)) z - blockOperator =
      ((z - 1) • ContinuousLinearMap.id ℂ ℂ).prodMap
        (algebraMap ℂ (CSpace →L[ℂ] CSpace) z - weightedOperator) := by
    apply ContinuousLinearMap.ext
    intro p
    apply Prod.ext
    · change z * p.1 - p.1 = (z - 1) * p.1
      ring
    · rfl
  rw [spectrum.mem_iff, he, ContinuousLinearMap.isUnit_iff_bijective]
  change (¬ Function.Bijective (Prod.map (fun c : ℂ => (z - 1) * c)
      (algebraMap ℂ (CSpace →L[ℂ] CSpace) z - weightedOperator))) ↔ _
  rw [Prod.map_bijective]
  have hscalar : Function.Bijective (fun c : ℂ => (z - 1) * c) ↔ z ≠ 1 := by
    constructor
    · intro h hz
      subst z
      have h01 := h.injective (a₁ := 0) (a₂ := 1) (by simp)
      exact zero_ne_one h01
    · intro hz
      exact ⟨fun _ _ h => mul_left_cancel₀ (sub_ne_zero.mpr hz) h,
        fun y => ⟨(z - 1)⁻¹ * y, by dsimp only; rw [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hz), one_mul]⟩⟩
  rw [hscalar, spectrum.mem_iff, ContinuousLinearMap.isUnit_iff_bijective]
  tauto

lemma conjugate_hardy : (ContinuousLinearEquiv.conjContinuousAlgEquiv (𝕜 := ℂ) (G := Space) (H := ℂ × CSpace) coordinateEquiv) hardy = blockOperator := by
  apply ContinuousLinearMap.ext
  intro p
  change coordinates (hardy (fromCoordinates p)) = blockOperator p
  rw [hardy_coordinates, coordinates_fromCoordinates]

theorem spectrum_disk : Spec.SpectrumDisk hardy := by
  have hs := AlgEquiv.spectrum_eq (ContinuousLinearEquiv.conjContinuousAlgEquiv (𝕜 := ℂ) (G := Space) (H := ℂ × CSpace) coordinateEquiv) hardy
  rw [conjugate_hardy] at hs
  change spectrum ℂ hardy = _
  rw [← hs]
  ext z
  exact (block_spectrum_mem z).trans (or_congr Iff.rfl (weighted_spectrum_mem z))

lemma weighted_eigen_iff (z : ℂ) :
    (∃ v : CSpace, v ≠ 0 ∧ weightedOperator v = z • v) ↔
    (∃ w : CSpace, w ≠ 0 ∧ HardyAveragingContinuous.hardy w = (2 * z) • w) := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    refine ⟨squareSubstitution v, ?_, ?_⟩
    · simpa using hv0
    · calc
        _ = (2 : ℂ) • ((1 / 2 : ℂ) •
            HardyAveragingContinuous.hardy (squareSubstitution v)) := by
          simp [smul_smul]
        _ = (2 : ℂ) • squareSubstitution (weightedOperator v) := by
          rw [substitution_intertwines]
        _ = _ := by rw [hv, map_smul, smul_smul]
  · rintro ⟨w, hw0, hw⟩
    refine ⟨squareSubstitution.symm w, ?_, ?_⟩
    · simpa using hw0
    · apply squareSubstitution.injective
      rw [substitution_intertwines, map_smul, squareSubstitution.apply_symm_apply, hw, smul_smul]
      congr 1
      ring

lemma weighted_eigenvalues (z : ℂ) :
    (∃ v : CSpace, v ≠ 0 ∧ weightedOperator v = z • v) ↔
      z = 1 / 2 ∨ ‖z - (1 / 4 : ℂ)‖ < (1 / 4 : ℝ) := by
  rw [weighted_eigen_iff]
  have h := Set.ext_iff.mp HardyAveragingContinuous.eigenvalue_disk (2 * z)
  change (∃ w : CSpace, w ≠ 0 ∧ HardyAveragingContinuous.hardy w = (2 * z) • w) ↔
    ‖2 * z - (1 / 2 : ℂ)‖ < (1 / 2 : ℝ) ∨ 2 * z = 1 at h
  rw [h, small_disk_scale_lt]
  have he : 2 * z = 1 ↔ z = 1 / 2 := by
    constructor
    · intro h
      linear_combination (1 / 2 : ℂ) * h
    · rintro rfl
      norm_num
  rw [he, or_comm]

lemma block_eigenvalues (z : ℂ) :
    (∃ p : ℂ × CSpace, p ≠ 0 ∧ blockOperator p = z • p) ↔
      z = 1 ∨ ∃ v : CSpace, v ≠ 0 ∧ weightedOperator v = z • v := by
  constructor
  · rintro ⟨p, hp0, hp⟩
    have hv : weightedOperator p.2 = z • p.2 := congrArg Prod.snd hp
    by_cases hp2 : p.2 = 0
    · left
      have hp1 : p.1 ≠ 0 := by
        intro hz
        exact hp0 (Prod.ext hz hp2)
      have hc : p.1 = z * p.1 := congrArg Prod.fst hp
      apply (mul_right_cancel₀ hp1)
      simpa using hc.symm
    · exact Or.inr ⟨p.2, hp2, hv⟩
  · rintro (rfl | ⟨v, hv0, hv⟩)
    · refine ⟨(1, 0), ?_, ?_⟩
      · intro h; exact one_ne_zero (congrArg Prod.fst h)
      · simp [blockOperator]
    · refine ⟨(0, v), ?_, ?_⟩
      · intro h; exact hv0 (congrArg Prod.snd h)
      · apply Prod.ext
        · simp [blockOperator]
        · exact hv

lemma hardy_eigen_iff (z : ℂ) :
    (∃ f : Space, f ≠ 0 ∧ hardy f = z • f) ↔
      ∃ p : ℂ × CSpace, p ≠ 0 ∧ blockOperator p = z • p := by
  constructor
  · rintro ⟨f, hf0, hf⟩
    refine ⟨coordinates f, ?_, ?_⟩
    · intro hz
      apply hf0
      have h := congrArg fromCoordinates hz
      simpa only [fromCoordinates_coordinates, map_zero] using h
    · rw [← hardy_coordinates, hf, map_smul]
  · rintro ⟨p, hp0, hp⟩
    refine ⟨fromCoordinates p, ?_, ?_⟩
    · intro hz
      apply hp0
      have h := congrArg coordinates hz
      simpa only [coordinates_fromCoordinates, map_zero] using h
    · apply coordinateEquiv.injective
      change coordinates (hardy (fromCoordinates p)) = coordinates (z • fromCoordinates p)
      rw [hardy_coordinates, map_smul, coordinates_fromCoordinates, hp]

theorem eigenvalue_disk : Spec.EigenvalueDisk hardy := by
  ext z
  change (∃ f : Space, f ≠ 0 ∧ hardy f = z • f) ↔ _
  rw [hardy_eigen_iff, block_eigenvalues, weighted_eigenvalues]
  rfl

theorem noncompact : Spec.Noncompact hardy := by
  intro hc
  have hR : IsCompactOperator weightedOperator := by
    have h := (hc.comp_clm (fromCoordinates.comp (ContinuousLinearMap.inr ℂ ℂ CSpace))).clm_comp
      ((ContinuousLinearMap.snd ℂ ℂ CSpace).comp coordinates)
    convert h using 1
    funext v
    change weightedOperator v = (coordinates (hardy (fromCoordinates (0, v)))).2
    rw [hardy_coordinates, coordinates_fromCoordinates]
    rfl
  have hhalf : IsCompactOperator ((1 / 2 : ℂ) • HardyAveragingContinuous.hardy) := by
    have h := (hR.comp_clm squareSubstitution.symm.toContinuousLinearMap).clm_comp
      squareSubstitution.toContinuousLinearMap
    convert h using 1
    funext v
    change ((1 / 2 : ℂ) • HardyAveragingContinuous.hardy v) =
      squareSubstitution (weightedOperator (squareSubstitution.symm v))
    rw [substitution_intertwines, squareSubstitution.apply_symm_apply]
  apply HardyAveragingContinuous.noncompact
  have h := hhalf.smul (2 : ℂ)
  convert h using 1
  funext v
  change HardyAveragingContinuous.hardy v =
    (2 : ℂ) • ((1 / 2 : ℂ) • HardyAveragingContinuous.hardy v)
  simp [smul_smul]

theorem norm_formula : Spec.NormFormula := by
  intro f
  rfl

/-- Derivative uniqueness on the nondegenerate closed interval identifies
this graph realization with functions, rather than functions with extra data. -/
theorem function_faithfulness : Spec.FunctionFaithfulness := by
  intro f g h
  apply Subtype.ext
  apply Prod.ext h
  ext x
  have hf := c1_characterization (value f) (derivative f) |>.mp f.property
  have hg := c1_characterization (value g) (derivative g) |>.mp g.property
  rw [h] at hf
  have hu := uniqueDiffOn_Icc zero_lt_one (x : ℝ) x.property
  exact ((hf x).derivWithin hu).symm.trans ((hg x).derivWithin hu)

theorem real_spectrum_section : Spec.RealSpectrumSection hardy := by
  intro t
  change (t : ℂ) ∈ spectrum ℂ hardy ↔ _
  rw [spectrum_disk]
  change ((t : ℂ) = 1 ∨ ‖(t : ℂ) - (1 / 4 : ℂ)‖ ≤ (1 / 4 : ℝ)) ↔ _
  have hr : (t : ℂ) = 1 ↔ t = 1 := by exact_mod_cast Iff.rfl
  have hn : ‖(t : ℂ) - (1 / 4 : ℂ)‖ = |t - (1 / 4 : ℝ)| := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_ofNat (n := 4), ← Complex.ofReal_div,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hr, hn, abs_le]
  unfold Icc
  simp only [mem_ofPred_eq]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨by linarith, by linarith⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨by linarith, by linarith⟩

theorem hardy_theorem : Spec.HardyTheorem := by
  refine ⟨hardy, hardy_value, coordinate_formula, spectrum_disk,
    eigenvalue_disk, noncompact, real_spectrum_section, ?_⟩
  intro U hU
  apply ContinuousLinearMap.ext
  intro f
  apply function_faithfulness
  exact (hU f).trans (hardy_value f).symm

/-- A bounded real-linear scalar map acts on both entries of the FTC graph. -/
def scalarMap (L : ℂ →L[ℝ] ℂ) : Space →L[ℝ] Space :=
  (((ContinuousLinearMap.compLeftContinuous ℝ I L).prodMap (ContinuousLinearMap.compLeftContinuous ℝ I L)).comp
    (c1Subspace.subtypeL.restrictScalars ℝ)).codRestrict
    (c1Subspace.restrictScalars ℝ) (by
      intro f
      apply (c1_characterization _ _).mpr
      intro x
      exact L.hasFDerivAt.comp_hasDerivWithinAt (x : ℝ)
        ((c1_characterization _ _).mp f.property x))

@[simp] lemma scalarMap_value (L : ℂ →L[ℝ] ℂ) (f : Space) (x : I) :
    value (scalarMap L f) x = L (value f x) := rfl

@[simp] lemma scalarMap_derivative (L : ℂ →L[ℝ] ℂ) (f : Space) (x : I) :
    derivative (scalarMap L f) x = L (derivative f x) := rfl

/-- The canonical inclusion of the real FTC graph. -/
def realInclusion : RealSpace →ₗᵢ[ℝ] Space where
  toFun f := f.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

/-- Real and imaginary projections retain the derivative as well as the function. -/
def realPart : Space →L[ℝ] RealSpace :=
  (scalarMap (Complex.ofRealCLM.comp Complex.reCLM)).codRestrict realSubspace (by
    intro f x
    constructor <;> simp [scalarMap_value, scalarMap_derivative])

def imagPart : Space →L[ℝ] RealSpace :=
  (scalarMap (Complex.ofRealCLM.comp Complex.imCLM)).codRestrict realSubspace (by
    intro f x
    constructor <;> simp [scalarMap_value, scalarMap_derivative])

@[simp] lemma realPart_value (f : Space) (x : I) :
    value (realPart f).val x = ((value f x).re : ℂ) := rfl
@[simp] lemma realPart_derivative (f : Space) (x : I) :
    derivative (realPart f).val x = ((derivative f x).re : ℂ) := rfl
@[simp] lemma imagPart_value (f : Space) (x : I) :
    value (imagPart f).val x = ((value f x).im : ℂ) := rfl
@[simp] lemma imagPart_derivative (f : Space) (x : I) :
    derivative (imagPart f).val x = ((derivative f x).im : ℂ) := rfl

lemma real_ext {f g : RealSpace} (h : realValue f = realValue g) : f = g := by
  apply Subtype.ext
  apply function_faithfulness
  ext x
  apply Complex.ext
  · exact congrArg (fun v : RealCSpace => v x) h
  · exact (f.property x).1.trans (g.property x).1.symm

lemma realSubspace_closed : IsClosed (realSubspace : Set Space) := by
  change IsClosed {f : Space | ∀ x : I,
    (value f x).im = 0 ∧ (derivative f x).im = 0}
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro x
  apply IsClosed.inter
  · exact isClosed_eq (by unfold value; fun_prop) continuous_const
  · exact isClosed_eq (by unfold derivative; fun_prop) continuous_const

instance : CompleteSpace RealSpace := realSubspace_closed.completeSpace_coe

lemma value_realInclusion (F : RealSpace) :
    value (realInclusion F) = HardyAveragingContinuous.realInclusion (realValue F) := by
  ext x
  apply Complex.ext
  · rfl
  · exact (F.property x).1

lemma derivative_realInclusion (F : RealSpace) :
    derivative (realInclusion F) =
      HardyAveragingContinuous.realInclusion (realDerivative F) := by
  ext x
  apply Complex.ext
  · rfl
  · exact (F.property x).2

theorem real_c1_model : Spec.RealC1Model := by
  refine ⟨?_, ?_, fun _ _ h => real_ext h, inferInstance⟩
  · intro f v
    constructor
    · intro h
      let fc := HardyAveragingContinuous.realInclusion f
      let vc := HardyAveragingContinuous.realInclusion v
      have hm : (fc, vc) ∈ c1Subspace := by
        apply (c1_characterization _ _).mpr
        intro x
        exact Complex.ofRealCLM.hasFDerivAt.comp_hasDerivWithinAt (x : ℝ) (h x)
      refine ⟨⟨⟨(fc, vc), hm⟩, ?_⟩, ?_, ?_⟩
      · intro x
        constructor <;> exact Complex.ofReal_im _
      · ext x; rfl
      · ext x; rfl
    · rintro ⟨F, rfl, rfl⟩ x
      have hd := (c1_characterization _ _).mp F.val.property x
      exact Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt (x : ℝ) hd
  · intro F
    change ‖F.val‖ = _
    rw [norm_formula]
    change max ‖value (realInclusion F)‖ ‖derivative (realInclusion F)‖ = _
    rw [value_realInclusion F, derivative_realInclusion F,
      HardyAveragingContinuous.realInclusion.norm_map,
      HardyAveragingContinuous.realInclusion.norm_map]

def realForm : HardyAveragingRealBridge.RealForm RealSpace Space where
  inclusion := realInclusion
  re := realPart
  im := imagPart
  re_inclusion F := by
    apply real_ext
    ext x
    rfl
  im_inclusion F := by
    apply real_ext
    ext x
    exact (F.property x).1
  re_I_inclusion F := by
    apply real_ext
    ext x
    change (Complex.I * value F.val x).re = 0
    simp [Complex.mul_re, (F.property x).1]
  im_I_inclusion F := by
    apply real_ext
    ext x
    change (Complex.I * value F.val x).im = (value F.val x).re
    simp [Complex.mul_im]
  reconstruct f := by
    apply function_faithfulness
    ext x
    change value f x = ((value f x).re : ℂ) + Complex.I * ((value f x).im : ℂ)
    simpa only [mul_comm Complex.I] using (Complex.re_add_im (value f x)).symm

/-- Restriction of complex averaging to the real FTC graph. -/
def realHardy : RealSpace →L[ℝ] RealSpace :=
  realPart.comp ((hardy.restrictScalars ℝ).comp realInclusion.toContinuousLinearMap)

lemma realHardy_value (F : RealSpace) :
    realValue (realHardy F) = HardyAveragingContinuous.realHardy (realValue F) := by
  ext x
  change (value (hardy (realInclusion F)) x).re = _
  rw [hardy_value, value_realInclusion]
  change (HardyAveragingContinuous.hardy
    (HardyAveragingContinuous.realInclusion (realValue F)) x).re = _
  rw [HardyAveragingContinuous.realHardy_intertwines]
  rfl

lemma realHardy_intertwines (F : RealSpace) :
    hardy (realInclusion F) = realInclusion (realHardy F) := by
  apply function_faithfulness
  rw [hardy_value, value_realInclusion, value_realInclusion, realHardy_value]
  exact HardyAveragingContinuous.realHardy_intertwines _

lemma realHardy_formula : Spec.RealOperatorFormula realHardy := by
  constructor
  · intro f
    rw [realHardy_value]
    exact HardyAveragingContinuous.realHardy_formula.1 _
  · intro f x hx
    rw [realHardy_value]
    exact HardyAveragingContinuous.realHardy_formula.2 _ _ hx

lemma realHardy_spectrum :
    spectrum ℝ realHardy = {t : ℝ | t = 1 ∨ t ∈ Icc (0 : ℝ) (1 / 2)} := by
  rw [HardyAveragingRealBridge.spectrum_transport realForm realHardy hardy
    realHardy_intertwines]
  ext t
  exact real_spectrum_section t

lemma real_eigenvalue_iff (t : ℝ) :
    ((t : ℂ) = 1 ∨ (t : ℂ) = 1 / 2 ∨
      ‖(t : ℂ) - (1 / 4 : ℂ)‖ < (1 / 4 : ℝ)) ↔
      t = 1 ∨ t ∈ Ioc (0 : ℝ) (1 / 2) := by
  have h1 : (t : ℂ) = 1 ↔ t = 1 := by exact_mod_cast Iff.rfl
  have h2 : (t : ℂ) = 1 / 2 ↔ t = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      Complex.ofReal_inj]
  have hn : ‖(t : ℂ) - (1 / 4 : ℂ)‖ = |t - 1 / 4| := by
    rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [h1, h2, hn, abs_lt]
  constructor
  · rintro (h | h | ⟨h₀, h₁⟩)
    · exact Or.inl h
    · right; subst t; norm_num
    · right; constructor <;> linarith
  · rintro (h | ⟨h₀, h₁⟩)
    · exact Or.inl h
    · by_cases ht : t = 1 / 2
      · exact Or.inr (Or.inl ht)
      · right; right; constructor <;> have := lt_of_le_of_ne h₁ ht <;> linarith

lemma realHardy_eigenvalues :
    {t : ℝ | ∃ f : RealSpace, f ≠ 0 ∧ realHardy f = t • f} =
      {t : ℝ | t = 1 ∨ t ∈ Ioc (0 : ℝ) (1 / 2)} := by
  ext t
  change (∃ f : RealSpace, f ≠ 0 ∧ realHardy f = t • f) ↔ _
  rw [HardyAveragingRealBridge.eigenvalue_transport realForm realHardy hardy
    realHardy_intertwines t]
  exact (Set.ext_iff.mp eigenvalue_disk (t : ℂ)).trans (real_eigenvalue_iff t)

lemma hardy_injective : Function.Injective hardy := by
  intro f g h
  apply function_faithfulness
  apply HardyAveragingContinuous.no_zero_eigenvalue
  rw [← hardy_value, ← hardy_value, h]

lemma realHardy_injective : Function.Injective realHardy := by
  intro f g h
  apply realInclusion.injective
  apply hardy_injective
  rw [realHardy_intertwines, realHardy_intertwines, h]

lemma realHardy_noncompact : ¬ IsCompactOperator realHardy := by
  intro hc
  exact noncompact ((HardyAveragingRealBridge.compact_transport realForm realHardy hardy
    realHardy_intertwines).mp hc)

lemma real_formula_value {U : RealSpace →L[ℝ] RealSpace}
    (hU : Spec.RealOperatorFormula U) (f : RealSpace) :
    realValue (U f) = HardyAveragingContinuous.realHardy (realValue f) := by
  ext x
  by_cases hx : (x : ℝ) = 0
  · have hx0 : x = 0 := Subtype.ext hx
    subst x
    rw [hU.1, HardyAveragingContinuous.realHardy_formula.1]
  · have hp : 0 < (x : ℝ) := lt_of_le_of_ne x.property.1 (Ne.symm hx)
    rw [hU.2 f x hp, HardyAveragingContinuous.realHardy_formula.2 _ x hp]

theorem real_hardy_theorem : Spec.RealHardyTheorem := by
  refine ⟨realHardy, realHardy_formula, realHardy_spectrum, realHardy_eigenvalues,
    realHardy_injective, realHardy_noncompact, ?_⟩
  intro U hU
  apply ContinuousLinearMap.ext
  intro f
  apply real_ext
  exact (real_formula_value hU f).trans (realHardy_value f).symm

end ExpandedFA.PartV.HardyAveragingC1


