import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.InvariantHahnBanach
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.BanachCircleIntegration
import Mathlib.MeasureTheory.Group.Integral

/-! Banach integration on the unit circle. We apply invariant Hahn–Banach
with the supremum norm as dominating sublinear function. Preservation of
the constant one and contractivity then give positivity. -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ExpandedFA.P1
namespace BanachCircle

/-- Circle translation as a real linear operator. -/
def translateLinear (a : UnitAddCircle) : Module.End ℝ BoundedCircleFunction where
  toFun := circleTranslate a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma translateLinear_add (a b : UnitAddCircle) :
    translateLinear (a + b) = translateLinear a * translateLinear b := by
  ext f x
  change f ((a + b) + x) = f (b + (a + x))
  rw [add_left_comm b a x, add_assoc]

/-- The semigroup of all translations. -/
def translations : Subsemigroup (Module.End ℝ BoundedCircleFunction) where
  carrier := Set.range translateLinear
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, translateLinear_add a b⟩

lemma translations_commute :
    ∀ A ∈ translations, ∀ B ∈ translations, Commute A B := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  show translateLinear a * translateLinear b = translateLinear b * translateLinear a
  rw [← translateLinear_add, ← translateLinear_add, add_comm a b]

lemma translate_norm_le (a : UnitAddCircle) (f : BoundedCircleFunction) :
    ‖circleTranslate a f‖ ≤ ‖f‖ :=
  lp.norm_le_of_forall_le (norm_nonneg _) fun x =>
    lp.norm_apply_le_norm ENNReal.top_ne_zero f (a + x)

/-- The subspace of bounded Lebesgue measurable functions. -/
def measurableFunctions : Submodule ℝ BoundedCircleFunction where
  carrier := {f | AEStronglyMeasurable (fun x => f x) volume}
  zero_mem' := aestronglyMeasurable_zero
  add_mem' hf hg := hf.add hg
  smul_mem' c _f hf := hf.const_smul c

lemma integrable (f : measurableFunctions) : Integrable (fun x => (f : BoundedCircleFunction) x) :=
  Integrable.of_bound f.property ‖(f : BoundedCircleFunction)‖
    (Filter.Eventually.of_forall (lp.norm_apply_le_norm ENNReal.top_ne_zero _))

/-- The ordinary Lebesgue integral on its bounded measurable subspace. -/
def integralFunctional : measurableFunctions →ₗ[ℝ] ℝ where
  toFun f := ∫ x : UnitAddCircle, (f : BoundedCircleFunction) x
  map_add' f g := integral_add (integrable f) (integrable g)
  map_smul' c f := integral_smul c (fun x => (f : BoundedCircleFunction) x)

lemma measurable_invariant : ∀ A ∈ translations,
    ∀ f ∈ measurableFunctions, A f ∈ measurableFunctions := by
  rintro _ ⟨a, rfl⟩ f hf
  exact hf.comp_measurePreserving (measurePreserving_add_left volume a)

lemma integral_norm_le (f : measurableFunctions) :
    ‖integralFunctional f‖ ≤ ‖(f : BoundedCircleFunction)‖ := by
  change ‖∫ x : UnitAddCircle, (f : BoundedCircleFunction) x‖ ≤ ‖(f : BoundedCircleFunction)‖
  have h := norm_integral_le_of_norm_le_const
    (μ := (volume : Measure UnitAddCircle))
    (Filter.Eventually.of_forall (lp.norm_apply_le_norm ENNReal.top_ne_zero
      (f : BoundedCircleFunction)))
  simpa [Measure.real, UnitAddCircle.measure_univ] using h

lemma integral_invariant :
    ∀ (A : Module.End ℝ BoundedCircleFunction) (hA : A ∈ translations)
      (f : measurableFunctions),
    integralFunctional ⟨A f, measurable_invariant A hA f f.property⟩ =
      integralFunctional f := by
  rintro _ ⟨a, rfl⟩ f
  exact integral_add_left_eq_self (fun x => (f : BoundedCircleFunction) x) a

lemma norm_sublinear : IsSublinear (fun f : BoundedCircleFunction => ‖f‖) := by
  refine ⟨norm_add_le, ?_⟩
  intro t ht f
  change ‖t • f‖ = t * ‖f‖
  rw [norm_smul, Real.norm_of_nonneg ht]

/-- An invariant algebraic extension dominated by the supremum norm. -/
lemma exists_extension :
    ∃ F : BoundedCircleFunction →ₗ[ℝ] ℝ,
      (∀ f : measurableFunctions, F (f : BoundedCircleFunction) = integralFunctional f) ∧
      (∀ f, F f ≤ ‖f‖) ∧
      (∀ a f, F (circleTranslate a f) = F f) := by
  obtain ⟨F, hext, hbound, hinv⟩ := invariant_hahn_banach
    (fun f : BoundedCircleFunction => ‖f‖) norm_sublinear
    translations translations_commute
    (by rintro _ ⟨a, rfl⟩ f; exact translate_norm_le a f)
    measurableFunctions measurable_invariant integralFunctional
    (fun f => (le_abs_self _).trans (integral_norm_le f)) integral_invariant
  exact ⟨F, hext, hbound, fun a f => hinv (translateLinear a) ⟨a, rfl⟩ f⟩

lemma one_measurable : (1 : BoundedCircleFunction) ∈ measurableFunctions := by
  exact aestronglyMeasurable_const

lemma integral_one : integralFunctional ⟨1, one_measurable⟩ = 1 := by
  change (∫ _ : UnitAddCircle, (1 : ℝ)) = 1
  simp [integral_const, Measure.real]

end BanachCircle

/-- The Lebesgue integral on bounded Lebesgue measurable circle functions has a
positive, translation-invariant, norm-one extension to all bounded functions. -/
theorem banach_circle_integration :
    Specs.ExpandedFA.P1.BanachCircleIntegration.banachCircleIntegrationType := by
  obtain ⟨F, hext, hbound, hinv⟩ := BanachCircle.exists_extension
  have hnorm (f : BoundedCircleFunction) : ‖F f‖ ≤ 1 * ‖f‖ := by
    rw [one_mul, Real.norm_eq_abs, abs_le]
    constructor
    · have h := hbound (-f)
      rw [map_neg, norm_neg] at h
      linarith
    · exact hbound f
  let I : BoundedCircleFunction →L[ℝ] ℝ := F.mkContinuous 1 hnorm
  have hone : F (1 : BoundedCircleFunction) = 1 := by
    exact (hext ⟨1, BanachCircle.one_measurable⟩).trans BanachCircle.integral_one
  refine ⟨I, ?_, ?_, hinv, ?_⟩
  · intro f hf
    have hg : ‖‖f‖ • (1 : BoundedCircleFunction) - f‖ ≤ ‖f‖ := by
      apply lp.norm_le_of_forall_le (norm_nonneg _)
      intro x
      change ‖‖f‖ * (1 : ℝ) - f x‖ ≤ ‖f‖
      rw [mul_one, Real.norm_eq_abs, abs_le]
      have hx := lp.norm_apply_le_norm ENNReal.top_ne_zero f x
      have hx' : f x ≤ ‖f‖ := (le_abs_self _).trans hx
      constructor <;> linarith [hf x, norm_nonneg f]
    have h := (hbound (‖f‖ • (1 : BoundedCircleFunction) - f)).trans hg
    rw [map_sub, map_smul, hone, smul_eq_mul, mul_one] at h
    change 0 ≤ F f
    linarith
  · apply le_antisymm
    · exact I.opNorm_le_bound (by norm_num) hnorm
    · have h := I.le_opNorm (1 : BoundedCircleFunction)
      change ‖F (1 : BoundedCircleFunction)‖ ≤ ‖I‖ * ‖(1 : BoundedCircleFunction)‖ at h
      simpa [hone] using h
  · intro f hf
    exact hext ⟨f, hf.aemeasurable.aestronglyMeasurable⟩

end ExpandedFA.P1
