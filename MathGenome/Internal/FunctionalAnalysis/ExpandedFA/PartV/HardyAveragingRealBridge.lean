import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.HardyAveragingRealBridge
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic.Ring

/-! Transport through a concrete real form. The decomposition identifies the
operators and their inverses; no particular complexification norm is used. -/

namespace ExpandedFA.PartV.HardyAveragingRealBridge

universe u v

section Transport

variable {XR : Type u} {XC : Type v}
  [NormedAddCommGroup XR] [NormedSpace ℝ XR]
  [NormedAddCommGroup XC] [NormedSpace ℂ XC]
  (F : RealForm XR XC) (A : XR →L[ℝ] XR) (B : XC →L[ℂ] XC)
  (h : ∀ x, B (F.inclusion x) = F.inclusion (A x))

include F h

theorem map_decomposition (z : XC) :
    B z = F.inclusion (A (F.re z)) + Complex.I • F.inclusion (A (F.im z)) := by
  conv_lhs => rw [F.reconstruct z]
  simp only [map_add, map_smul, h]

theorem re_map (z : XC) : F.re (B z) = A (F.re z) := by
  rw [map_decomposition F A B h]
  simp only [map_add, F.re_inclusion, F.re_I_inclusion, add_zero]

theorem im_map (z : XC) : F.im (B z) = A (F.im z) := by
  rw [map_decomposition F A B h]
  simp only [map_add, F.im_inclusion, F.im_I_inclusion, zero_add]

theorem shift_intertwines (t : ℝ) (x : XR) :
    (B - (t : ℂ) • 1) (F.inclusion x) = F.inclusion ((A - t • 1) x) := by
  change B (F.inclusion x) - (t : ℂ) • F.inclusion x =
    F.inclusion (A x - t • x)
  rw [h, map_sub, map_smul, Complex.coe_smul]

/-- Bijectivity is preserved, including for the zero space. -/
theorem bijective_iff : Function.Bijective A ↔ Function.Bijective B := by
  constructor
  · rintro ⟨hinj, hsurj⟩
    constructor
    · intro z w heq
      have hr : F.re z = F.re w := hinj (by
        simpa only [re_map F A B h] using congrArg F.re heq)
      have hi : F.im z = F.im w := hinj (by
        simpa only [im_map F A B h] using congrArg F.im heq)
      rw [F.reconstruct z, F.reconstruct w, hr, hi]
    · intro z
      obtain ⟨x, hx⟩ := hsurj (F.re z)
      obtain ⟨y, hy⟩ := hsurj (F.im z)
      refine ⟨F.inclusion x + Complex.I • F.inclusion y, ?_⟩
      rw [map_add, map_smul, h, h, hx, hy, ← F.reconstruct z]
  · rintro ⟨hinj, hsurj⟩
    constructor
    · intro x y heq
      apply F.inclusion.injective
      apply hinj
      rw [h, h, heq]
    · intro x
      obtain ⟨z, hz⟩ := hsurj (F.inclusion x)
      refine ⟨F.re z, ?_⟩
      rw [← re_map F A B h, hz, F.re_inclusion]

omit F h in
/-- Inverse laws imply bijectivity without any completeness argument. -/
theorem TwoSidedInverse.bijective {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {T S : X →L[𝕜] X} (hS : TwoSidedInverse T S) : Function.Bijective T :=
  ⟨fun x y hxy => by rw [← hS.1 x, ← hS.1 y, hxy], fun y => ⟨S y, hS.2 y⟩⟩

/-- A real bounded inverse gives a complex bounded inverse with the componentwise formula. -/
theorem extend_inverse_of_intertwines [CompleteSpace XC]
    (S : XR →L[ℝ] XR) (hS : TwoSidedInverse A S) :
    ∃ C : XC →L[ℂ] XC, TwoSidedInverse B C ∧
      ∀ z, C z = F.inclusion (S (F.re z)) + Complex.I • F.inclusion (S (F.im z)) := by
  have hbij := (bijective_iff F A B h).mp hS.bijective
  let E := ContinuousLinearEquiv.ofBijective B
    (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
  refine ⟨E.symm.toContinuousLinearMap, ⟨?_, ?_⟩, ?_⟩
  · exact E.symm_apply_apply
  · exact E.apply_symm_apply
  · intro z
    apply hbij.1
    change B (E.symm z) = _
    rw [show B (E.symm z) = z from E.apply_symm_apply z,
      map_add, map_smul, h, h, hS.2, hS.2, ← F.reconstruct z]

/-- Restriction of a complex inverse is a real inverse on the actual real form. -/
theorem restrict_inverse_of_intertwines
    (C : XC →L[ℂ] XC) (hC : TwoSidedInverse B C) :
    ∃ S : XR →L[ℝ] XR, TwoSidedInverse A S ∧
      (∀ x, F.inclusion (S x) = C (F.inclusion x)) ∧
      (∀ x, S x = F.re (C (F.inclusion x))) := by
  let S := F.re.comp ((C.restrictScalars ℝ).comp F.inclusion.toContinuousLinearMap)
  have hS : TwoSidedInverse A S := by
    constructor
    · intro x
      change F.re (C (F.inclusion (A x))) = x
      rw [← h, hC.1, F.re_inclusion]
    · intro x
      change A (F.re (C (F.inclusion x))) = x
      rw [← re_map F A B h, hC.2, F.re_inclusion]
  refine ⟨S, hS, ?_, fun _ => rfl⟩
  intro x
  apply hC.bijective.1
  rw [h, hS.2, hC.2]

/-- Compactness is independent of the scalar field in this concrete decomposition. -/
theorem compact_iff_of_intertwines : IsCompactOperator A ↔ IsCompactOperator B := by
  constructor
  · intro hA
    have hr := ((hA.comp_clm F.re).clm_comp F.inclusion.toContinuousLinearMap)
    have hi := ((hA.comp_clm F.im).clm_comp F.inclusion.toContinuousLinearMap).smul Complex.I
    have heq : (fun z => F.inclusion (A (F.re z)) +
        Complex.I • F.inclusion (A (F.im z))) = B := by
      funext z
      exact (map_decomposition F A B h z).symm
    have ht : IsCompactOperator (fun z => F.inclusion (A (F.re z)) +
        Complex.I • F.inclusion (A (F.im z))) := hr.add hi
    rwa [heq] at ht
  · intro hB
    have ht := (hB.comp_clm F.inclusion.toContinuousLinearMap).clm_comp F.re
    have heq : (F.re ∘ B ∘ F.inclusion.toContinuousLinearMap) = A := by
      funext x
      simp only [Function.comp_def, LinearIsometry.coe_toContinuousLinearMap, h,
        F.re_inclusion]
    rwa [heq] at ht

/-- The norm estimates use only the isometric inclusion and bounded coordinates. -/
theorem norm_bounds_of_intertwines :
    ‖A‖ ≤ ‖B‖ ∧ ‖B‖ ≤ (‖F.re‖ + ‖F.im‖) * ‖A‖ := by
  constructor
  · apply A.opNorm_le_bound (norm_nonneg B)
    intro x
    calc
      ‖A x‖ = ‖B (F.inclusion x)‖ := by rw [h, F.inclusion.norm_map]
      _ ≤ ‖B‖ * ‖F.inclusion x‖ := B.le_opNorm _
      _ = ‖B‖ * ‖x‖ := by rw [F.inclusion.norm_map]
  · apply B.opNorm_le_bound (mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
      (norm_nonneg _))
    intro z
    calc
      ‖B z‖ ≤ ‖A (F.re z)‖ + ‖A (F.im z)‖ := by
        rw [map_decomposition F A B h]
        simpa only [F.inclusion.norm_map, norm_smul, Complex.norm_I, one_mul] using
          norm_add_le (F.inclusion (A (F.re z))) (Complex.I • F.inclusion (A (F.im z)))
      _ ≤ ‖A‖ * ‖F.re z‖ + ‖A‖ * ‖F.im z‖ :=
        add_le_add (A.le_opNorm _) (A.le_opNorm _)
      _ ≤ ‖A‖ * (‖F.re‖ * ‖z‖) + ‖A‖ * (‖F.im‖ * ‖z‖) :=
        add_le_add (mul_le_mul_of_nonneg_left (F.re.le_opNorm z) (norm_nonneg A))
          (mul_le_mul_of_nonneg_left (F.im.le_opNorm z) (norm_nonneg A))
      _ = ((‖F.re‖ + ‖F.im‖) * ‖A‖) * ‖z‖ := by ring

end Transport

/-- The inverse on the complex space acts on the two real coordinates. -/
theorem extend_inverse : Spec.ExtendInverse.{u, v} := by
  intro XR XC _ _ _ _ _ _ F TR TC h t SR hSR
  exact extend_inverse_of_intertwines F (TR - t • 1) (TC - (t : ℂ) • 1)
    (shift_intertwines F TR TC h t) SR hSR

/-- The complex inverse preserves the real form, and its restriction is the real inverse. -/
theorem restrict_inverse : Spec.RestrictInverse.{u, v} := by
  intro XR XC _ _ _ _ _ _ F TR TC h t SC hSC
  exact restrict_inverse_of_intertwines F (TR - t • 1) (TC - (t : ℂ) • 1)
    (shift_intertwines F TR TC h t) SC hSC

/-- Bounded two-sided inverses exist over the two fields at exactly the same real parameters. -/
theorem inverse_equivalence : Spec.InverseEquivalence.{u, v} := by
  intro XR XC _ _ _ _ _ _ F TR TC h t
  constructor
  · rintro ⟨SR, hSR⟩
    obtain ⟨SC, hSC, _⟩ := extend_inverse F TR TC h t SR hSR
    exact ⟨SC, hSC⟩
  · rintro ⟨SC, hSC⟩
    obtain ⟨SR, hSR, _⟩ := restrict_inverse F TR TC h t SC hSC
    exact ⟨SR, hSR⟩

/-- This is the intrinsic real spectrum of the original real operator. -/
theorem spectrum_transport : Spec.SpectrumTransport.{u, v} := by
  intro XR XC _ _ _ _ _ _ F TR TC h
  ext t
  have hu : IsUnit (TR - t • 1) ↔ IsUnit (TC - (t : ℂ) • 1) :=
    ContinuousLinearMap.isUnit_iff_bijective.trans
      ((bijective_iff F (TR - t • 1) (TC - (t : ℂ) • 1)
        (shift_intertwines F TR TC h t)).trans
          ContinuousLinearMap.isUnit_iff_bijective.symm)
  change (¬ IsUnit (algebraMap ℝ (XR →L[ℝ] XR) t - TR)) ↔
    (¬ IsUnit (algebraMap ℂ (XC →L[ℂ] XC) (t : ℂ) - TC))
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    show t • (1 : XR →L[ℝ] XR) - TR = -(TR - t • 1) from (neg_sub _ _).symm,
    show (t : ℂ) • (1 : XC →L[ℂ] XC) - TC = -(TC - (t : ℂ) • 1) from (neg_sub _ _).symm]
  simpa only [IsUnit.neg_iff] using not_congr hu

/-- Nonzero eigenvectors are transported using the inclusion or a nonzero real coordinate. -/
theorem eigenvalue_transport : Spec.EigenvalueTransport.{u, v} := by
  intro XR XC _ _ _ _ _ _ F TR TC h t
  constructor
  · rintro ⟨x, hx, heig⟩
    refine ⟨F.inclusion x, ?_, ?_⟩
    · intro hj
      apply hx
      apply F.inclusion.injective
      simpa only [map_zero] using hj
    · rw [h, heig, map_smul, Complex.coe_smul]
  · rintro ⟨z, hz, heig⟩
    have hr : TR (F.re z) = t • F.re z := by
      rw [← re_map F TR TC h, heig, Complex.coe_smul, map_smul]
    have hi : TR (F.im z) = t • F.im z := by
      rw [← im_map F TR TC h, heig, Complex.coe_smul, map_smul]
    by_cases hr0 : F.re z = 0
    · refine ⟨F.im z, ?_, hi⟩
      intro hi0
      apply hz
      rw [F.reconstruct z, hr0, hi0, map_zero, smul_zero, add_zero]
    · exact ⟨F.re z, hr0, hr⟩

/-- Compactness of the actual operators is equivalent over their original fields. -/
theorem compact_transport : Spec.CompactTransport.{u, v} := by
  intro XR XC _ _ _ _ _ _ F TR TC h
  exact compact_iff_of_intertwines F TR TC h

/-- General real forms give these bounds; equality of operator norms is not assumed. -/
theorem norm_bounds : Spec.NormBounds.{u, v} := by
  intro XR XC _ _ _ _ _ _ F TR TC h
  exact norm_bounds_of_intertwines F TR TC h

end ExpandedFA.PartV.HardyAveragingRealBridge
