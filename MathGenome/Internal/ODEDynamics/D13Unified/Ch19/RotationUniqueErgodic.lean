import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.RotationUniqueErgodic
import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.CircleLift
import MathGenome.Internal.ODEDynamics.D13Unified.Ch19.MeasureDefinitions
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! An invariant probability for an irrational rotation is invariant under a
dense cyclic subgroup. Testing against all bounded continuous real functions
extends that invariance to every translation; uniqueness of Haar measure then
identifies it with the normalized Lebesgue measure. -/
namespace D13Unified.Ch19.RotationUniqueErgodic

noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open D13Unified.Ch15

abbrev Circle := Specs.D13Unified.Ch15.CircleLift.Circle
abbrev rotation : ℝ → Circle → Circle :=
  Specs.D13Unified.Ch19.RotationUniqueErgodic.rotation
abbrev lebesgueProbability : Measure Circle :=
  Specs.D13Unified.Ch19.RotationUniqueErgodic.lebesgueProbability

theorem rotation_quotient (α x : ℝ) :
    rotation α (CircleLift.quotientMap x) = CircleLift.quotientMap (x + α) := by
  exact (AddCircle.coe_add (1 : ℝ) x α).symm

theorem lebesgueProbability_eq_map (t : ℝ) :
    lebesgueProbability =
      Measure.map CircleLift.quotientMap (volume.restrict (Ioc t (t + 1))) := by
  exact (AddCircle.measurePreserving_mk 1 t).map_eq.symm

theorem lebesgueProbability_isProbability : IsProbabilityMeasure lebesgueProbability := by
  constructor
  change (volume : Measure (AddCircle (1 : ℝ))) univ = 1
  simp

theorem integral_lebesgueProbability (f : Circle → ℝ) :
    (∫ x, f x ∂lebesgueProbability) =
      ∫ t in (0 : ℝ)..1, f (CircleLift.quotientMap t) := by
  change (∫ x : AddCircle (1 : ℝ), f x) = ∫ t in (0 : ℝ)..1, f (t : AddCircle (1 : ℝ))
  simpa using (AddCircle.intervalIntegral_preimage 1 0 f).symm

theorem rotation_preserves_lebesgueProbability (α : ℝ) :
    MeasureDefinitions.PreservesMeasure (rotation α) lebesgueProbability := by
  exact measurePreserving_add_right volume (CircleLift.quotientMap α)

/-- The translations preserving a given measure form an additive subgroup. -/
def translationSubgroup (η : Measure Circle) : AddSubgroup Circle where
  carrier := {a | MeasurePreserving (a + ·) η η}
  zero_mem' := by
    change MeasurePreserving (fun x : Circle => 0 + x) η η
    have hid : (fun x : Circle => 0 + x) = id := funext zero_add
    rw [hid]
    exact MeasurePreserving.id η
  add_mem' := by
    intro a b ha hb
    change MeasurePreserving (a + ·) η η at ha
    change MeasurePreserving (b + ·) η η at hb
    change MeasurePreserving (a + b + ·) η η
    simpa only [Function.comp_def, add_assoc] using ha.comp hb
  neg_mem' := by
    intro a ha
    simpa using MeasurePreserving.symm (MeasurableEquiv.addLeft a) ha

/-- Density upgrades invariance under a single translation to invariance under
all translations. Equality of integrals is established for every bounded
continuous function, then the finite Borel measure extensionality theorem is used. -/
theorem translation_invariant_of_dense_multiples (η : Measure Circle) [IsFiniteMeasure η]
    (a : Circle) (ha : MeasurePreserving (a + ·) η η)
    (hd : DenseRange (fun n : ℤ => n • a)) : IsAddLeftInvariant η := by
  have hz (n : ℤ) : MeasurePreserving (n • a + ·) η η :=
    (translationSubgroup η).zsmul_mem ha n
  have hi (f : BoundedContinuousFunction Circle ℝ) (b : Circle) :
      (∫ x, f (b + x) ∂η) = ∫ x, f x ∂η := by
    have hc : Continuous (fun b : Circle => ∫ x, f (b + x) ∂η) := by
      apply continuous_of_dominated (bound := fun _ => ‖f‖)
      · intro b
        exact (f.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable
      · intro b
        exact ae_of_all η (fun x => f.norm_coe_le_norm (b + x))
      · exact integrable_const _
      · exact ae_of_all η (fun x => f.continuous.comp (continuous_id.add continuous_const))
    have heq := Continuous.ext_on hd hc continuous_const (by
      rintro _ ⟨n, rfl⟩
      exact (hz n).integral_comp (MeasurableEquiv.addLeft (n • a)).measurableEmbedding f)
    exact congrFun heq b
  constructor
  intro b
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  exact ((MeasurableEquiv.addLeft b).measurableEmbedding.integral_map f).trans (hi f b)

theorem invariant_probability_unique (α : ℝ) (hα : Irrational α)
    (η : Measure Circle) (hη : IsProbabilityMeasure η)
    (hrot : MeasureDefinitions.PreservesMeasure (rotation α) η) :
    η = lebesgueProbability := by
  have := hη
  have : IsProbabilityMeasure (volume : Measure Circle) := lebesgueProbability_isProbability
  have hd : DenseRange (fun n : ℤ => n • CircleLift.quotientMap α) := by
    apply AddCircle.denseRange_zsmul_coe_iff.mpr
    simpa using hα
  have ha : MeasurePreserving (CircleLift.quotientMap α + ·) η η := by
    change MeasurePreserving (fun x => x + CircleLift.quotientMap α) η η at hrot
    simpa only [add_comm] using hrot
  have := translation_invariant_of_dense_multiples η _ ha hd
  change η = (volume : Measure Circle)
  have heq := isAddInvariant_eq_smul_of_compactSpace η (volume : Measure Circle)
  have hmass := congrArg (fun μ : Measure Circle => μ univ) heq
  simp only [measure_univ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
    mul_one, ENNReal.one_eq_coe] at hmass
  have hscalar : (1 : NNReal) = η.addHaarScalarFactor volume :=
    hmass
  rw [heq, ← hscalar, one_smul]

end
end D13Unified.Ch19.RotationUniqueErgodic
