import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.OdeIntegral
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.VolterraResolvent
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The ODE clause of `fa2:p5:volterra-regularity` (paper.tex:21956–21960).
Continuous Bochner primitives give the endpoint within derivatives. Conversely
FTC on each subinterval integrates the prescribed derivative. For existence we
apply the accepted full-interval Volterra theorem to k(t,s)=A(s) and to the
datum ξ + ∫ B. All function spaces, operators and integrals are the accepted
native ones. In particular no smallness or positive interval length is needed.
-/
noncomputable section
open Set MeasureTheory
namespace ExpandedFA.PartV
open OdeIntegralSpec

section
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
local instance odeIntegralRealNormedSpace : NormedSpace ℝ E :=
  NormedSpace.restrictScalars ℝ 𝕜 E
variable {a b : ℝ} (hab : a ≤ b)

theorem continuous_ode_extend (u : C(VolterraInterval a b, E)) :
    Continuous (extendCurve hab u) :=
  u.continuous.comp continuous_projIcc

@[simp] theorem ode_extend_at (u : C(VolterraInterval a b, E))
    (t : VolterraInterval a b) : extendCurve hab u (t : ℝ) = u t := by
  simp [extendCurve, projIcc_of_mem hab t.property]

variable [CompleteSpace E]

theorem continuous_ode_primitive (f : C(VolterraInterval a b, E)) :
    Continuous (fun t : ℝ => ∫ s in a..t, extendCurve hab f s) :=
  (intervalIntegral.differentiable_integral_of_continuous
    (continuous_ode_extend hab f)).continuous

theorem ode_primitive_derivative (f : C(VolterraInterval a b, E)) (t : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ s in a..t, extendCurve hab f s) (extendCurve hab f t) t :=
  intervalIntegral.integral_hasDerivAt_right
    ((continuous_ode_extend hab f).intervalIntegrable _ _)
    (continuous_ode_extend hab f).aestronglyMeasurable.stronglyMeasurableAtFilter
    (continuous_ode_extend hab f).continuousAt

theorem ode_integral_to_classical
    (A : C(VolterraInterval a b, E →L[𝕜] E)) (B : C(VolterraInterval a b, E))
    (ξ : E) (u : C(VolterraInterval a b, E))
    (hu : IsIntegralSolution hab A B ξ u) : IsClassicalSolution hab A B ξ u := by
  have hd (t : VolterraInterval a b) :
      HasDerivWithinAt (extendCurve hab u) (A t (u t) + B t) (Icc a b) (t : ℝ) := by
    have hp := ((ode_primitive_derivative hab (rhs A B u) (t : ℝ)).const_add ξ).hasDerivWithinAt (s := Icc a b)
    have hp' : HasDerivWithinAt
        (fun r => ξ + ∫ s in a..r, extendCurve hab (rhs A B u) s)
        (A t (u t) + B t) (Icc a b) (t : ℝ) := by
      simpa only [ode_extend_at, rhs, ContinuousMap.coe_mk] using hp
    apply hp'.congr
    · intro r hr
      simpa only [ode_extend_at hab u ⟨r, hr⟩] using hu ⟨r, hr⟩
    · simpa only [ode_extend_at] using hu t
  refine ⟨⟨rhs A B u, hd⟩, ?_, hd⟩
  simpa using hu ⟨a, le_rfl, hab⟩

theorem ode_classical_to_integral
    (A : C(VolterraInterval a b, E →L[𝕜] E)) (B : C(VolterraInterval a b, E))
    (ξ : E) (u : C(VolterraInterval a b, E))
    (hu : IsClassicalSolution hab A B ξ u) : IsIntegralSolution hab A B ξ u := by
  intro t
  have hsub : Icc a (t : ℝ) ⊆ Icc a b :=
    fun _ hr => ⟨hr.1, hr.2.trans t.property.2⟩
  have hd : ∀ r ∈ Ioo a (t : ℝ),
      HasDerivAt (extendCurve hab u) (extendCurve hab (rhs A B u) r) r := by
    intro r hr
    have hrI : r ∈ Icc a b := hsub ⟨hr.1.le, hr.2.le⟩
    have h := (hu.2.2 ⟨r, hrI⟩).hasDerivAt
      (Icc_mem_nhds hr.1 (hr.2.trans_le t.property.2))
    have he := ode_extend_at hab (rhs A B u) ⟨r, hrI⟩
    change extendCurve hab (rhs A B u) r = A ⟨r, hrI⟩ (u ⟨r, hrI⟩) + B ⟨r, hrI⟩ at he
    rw [he]
    exact h
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.property.1
    ((continuous_ode_extend hab u).continuousOn) hd
    ((continuous_ode_extend hab (rhs A B u)).intervalIntegrable a (t : ℝ))
  rw [ode_extend_at, ode_extend_at hab u ⟨a, le_rfl, hab⟩, hu.2.1] at hi
  rw [hi]
  abel

/-- The kernel of the ODE has no dependence on its first variable. -/
def odeKernel (A : C(VolterraInterval a b, E →L[𝕜] E)) :
    C(volterraTriangle a b, E →L[𝕜] E) :=
  A.comp ⟨fun p => ⟨p.val.2, p.property.1, p.property.2.1.trans p.property.2.2⟩,
    (continuous_snd.comp continuous_subtype_val).subtype_mk _⟩

/-- The inhomogeneous term after integrating b. -/
def odeDatum (B : C(VolterraInterval a b, E)) (ξ : E) : C(VolterraInterval a b, E) :=
  ⟨fun t => ξ + ∫ s in a..(t : ℝ), extendCurve hab B s,
    continuous_const.add ((continuous_ode_primitive hab B).comp continuous_subtype_val)⟩

theorem ode_volterra_formula (A : C(VolterraInterval a b, E →L[𝕜] E))
    (u : C(VolterraInterval a b, E)) (t : VolterraInterval a b) :
    VolterraOperatorSpec.OperatorValue 𝕜 E a b hab (odeKernel A) u t =
      ∫ s in a..(t : ℝ), A (projIcc a b hab s) (u (projIcc a b hab s)) := by
  rw [(volterra_operator_properties 𝕜 E a b hab (odeKernel A)).1]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le t.property.1] at hs
  rw [volterraIntegrand_eq hab (odeKernel A) u t s hs]
  simp only [odeKernel, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [projIcc_of_mem hab ⟨hs.1, hs.2.trans t.property.2⟩]

/-- Exact bridge to the accepted second-kind equation; neither integrand nor
scalar linearity has been replaced by a formal ODE certificate. -/
theorem ode_integral_iff_volterra (A : C(VolterraInterval a b, E →L[𝕜] E))
    (B : C(VolterraInterval a b, E)) (ξ : E) (u : C(VolterraInterval a b, E)) :
    IsIntegralSolution hab A B ξ u ↔
      u - VolterraOperatorSpec.OperatorValue 𝕜 E a b hab (odeKernel A) u =
        odeDatum (𝕜 := 𝕜) hab B ξ := by
  have hi (t : VolterraInterval a b) :
      (∫ s in a..(t : ℝ), extendCurve hab (rhs A B u) s) =
      VolterraOperatorSpec.OperatorValue 𝕜 E a b hab (odeKernel A) u t +
        ∫ s in a..(t : ℝ), extendCurve hab B s := by
    rw [ode_volterra_formula]
    change (∫ s in a..(t : ℝ),
      (A (projIcc a b hab s) (u (projIcc a b hab s)) + extendCurve hab B s)) = _
    apply intervalIntegral.integral_add
    · exact (((A.continuous.comp continuous_projIcc).clm_apply
        (continuous_ode_extend hab u))).intervalIntegrable _ _
    · exact (continuous_ode_extend hab B).intervalIntegrable _ _
  constructor
  · intro hu
    ext t
    have h := hu t
    rw [hi t] at h
    change u t - _ = ξ + _
    rw [h]
    abel
  · intro hu t
    have h := congrArg (fun v : C(VolterraInterval a b, E) => v t) hu
    change u t - _ = ξ + _ at h
    rw [hi t]
    calc
      u t = _ := sub_eq_iff_eq_add.mp h
      _ = _ := by abel

end

theorem ode_differential_equivalence : OdeIntegralSpec.DifferentialEquivalence := by
  intro 𝕜 E _ _ _ _ a b hab A B ξ u
  exact ⟨ode_integral_to_classical hab A B ξ u, ode_classical_to_integral hab A B ξ u⟩

theorem ode_unique_solvability : OdeIntegralSpec.UniqueSolvability := by
  intro 𝕜 E _ _ _ _ a b hab A B ξ
  obtain ⟨u, hu, huniq, _⟩ := volterra_solvability_and_iteration
    𝕜 E a b hab (odeKernel A) 1 (odeDatum (𝕜 := 𝕜) hab B ξ)
  simp only [one_smul] at hu huniq
  have hui := (ode_integral_iff_volterra hab A B ξ u).mpr hu
  refine ⟨u, hui, ode_integral_to_classical hab A B ξ u hui, ?_, ?_⟩
  · intro v hv
    exact huniq v ((ode_integral_iff_volterra hab A B ξ v).mp hv)
  · intro v hv
    exact huniq v ((ode_integral_iff_volterra hab A B ξ v).mp
      (ode_classical_to_integral hab A B ξ v hv))

theorem ode_singleton_characterization : OdeIntegralSpec.SingletonCharacterization := by
  intro 𝕜 E _ _ _ _ a A B ξ u
  have hi : IsIntegralSolution (le_refl a) A B ξ u ↔ u ⟨a, le_rfl, le_rfl⟩ = ξ := by
    constructor
    · intro hu
      simpa using hu ⟨a, le_rfl, le_rfl⟩
    · intro hu t
      have ht : t = ⟨a, le_rfl, le_rfl⟩ := Subtype.ext (le_antisymm t.property.2 t.property.1)
      subst t
      simpa using hu
  exact ⟨hi, (ode_differential_equivalence 𝕜 E a a (le_refl a) A B ξ u).symm.trans hi⟩

end ExpandedFA.PartV
