import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.RiemannLebesgueBridge
import MathGenome.Internal.RealAnalysis.D11.Ch23.CompactDiniRiemannElementary
import MathGenome.Internal.RealAnalysis.D11.Ch23.UnitImpliesFiniteUnique
import MathGenome.Internal.RealAnalysis.D11.Ch16.ProperIntegralEquality
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! The Riemann Daniell measure on a closed interval is the usual Borel
Lebesgue restriction. The comparison of ordinary completions is made only
after equality of the original Borel measures has been proved. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace D11.Ch23.RiemannLebesgueBridge
open Model

/-- The positive levels of all continuous functions generate the relative
Borel structure. The coordinate function proves the nontrivial inclusion. -/
theorem generated_eq_borel : _root_.Specs.D11.Ch23.RiemannLebesgueBridge.generated_eq_borel := by
  intro a b
  let V := Specs.continuousFunctions (Icc a b)
  have hV := (continuousFunctions_stone (Icc a b)).1
  have hle : Specs.positiveLevelMeasurableSpace V ≤
      (inferInstance : MeasurableSpace (Icc a b)) := by
    apply (le_iff_all_measurable V hV _).mpr
    intro f hf
    exact (show Continuous f from hf).measurable
  have hcoord : @Measurable (Icc a b) ℝ (Specs.positiveLevelMeasurableSpace V)
      (borel ℝ) Subtype.val :=
    measurable_of_mem V hV Subtype.val continuous_subtype_val
  have hge : (inferInstance : MeasurableSpace (Icc a b)) ≤
      Specs.positiveLevelMeasurableSpace V := hcoord.comap_le
  exact (le_antisymm hle hge).trans BorelSpace.measurable_eq

lemma generated_eq_native (a b : ℝ) :
    Specs.positiveLevelMeasurableSpace (Specs.continuousFunctions (Icc a b)) =
      (inferInstance : MeasurableSpace (Icc a b)) :=
  (generated_eq_borel a b).trans BorelSpace.measurable_eq.symm

/-- Ordinary completion trims back to the original measure. -/
lemma completion_trim {X : Type*} [MeasurableSpace X] (μ : Measure X) :
    (_root_.Specs.D11.Ch02.Completion.completedMeasure_value μ).trim (show (inferInstance : MeasurableSpace X) ≤
      _root_.Specs.D11.Ch02.Completion.completedSpace_value μ from
      le_eventuallyMeasurableSpace) = μ := by
  ext A hA
  rw [trim_measurableSet_eq _ hA]
  rfl

/-- The classical proper equality, transferred from the ordinary completion
back to Borel measure for an actually Borel integrand. -/
lemma riemann_eq_borel_integral {a b : ℝ} (hab : a ≤ b)
    (f : Specs.continuousFunctions (Icc a b)) :
    Specs.riemannFunctional hab f =
      ∫ x in Icc a b, Set.IccExtend hab f.val x := by
  let F := Set.IccExtend hab f.val
  have hF : Continuous F := f.property.comp continuous_projIcc
  have hm : StronglyMeasurable ((Icc a b).indicator F) :=
    hF.stronglyMeasurable.indicator measurableSet_Icc
  have htrim := integral_trim
    (μ := _root_.Specs.D11.Ch02.Completion.completedMeasure_value (volume : Measure ℝ))
    (show (inferInstance : MeasurableSpace ℝ) ≤
      _root_.Specs.D11.Ch02.Completion.completedSpace_value (volume : Measure ℝ) from
      le_eventuallyMeasurableSpace) hm
  rw [completion_trim] at htrim
  have he := D11.Ch16.ProperIntegralEquality.real_integral_eq F
    (Specs.interval_continuous_integrable hab f)
  change Specs.riemannFunctional hab f = _ at he
  rw [htrim] at he
  exact he.trans (integral_indicator measurableSet_Icc)

/-- The subtype restriction has its usual finite mass, including mass zero
on a singleton interval. -/
lemma intervalLebesgue_mass (a b : ℝ) :
    intervalLebesgue a b univ = ENNReal.ofReal (b - a) := by
  rw [intervalLebesgue, comap_subtype_coe_apply measurableSet_Icc]
  simp only [image_univ, Subtype.range_coe_subtype, setOf_mem_eq, Real.volume_Icc]

/-- Lebesgue integration of every continuous interval function equals its
actual Darboux value. -/
theorem lebesgue_represents : _root_.Specs.D11.Ch23.RiemannLebesgueBridge.lebesgue_represents := by
  intro a b hab
  refine ⟨⟨by rw [intervalLebesgue_mass]; exact ENNReal.ofReal_lt_top⟩, ?_⟩
  intro f
  let F := Set.IccExtend hab f.val
  have hF : Continuous F := f.property.comp continuous_projIcc
  have hres : (fun x : Icc a b => F x.val) = f.val := by
    funext x
    exact Set.IccExtend_of_mem hab f.val x.property
  have hi := (integrableOn_iff_comap_subtypeVal measurableSet_Icc).mp
    (hF.continuousOn.integrableOn_Icc : IntegrableOn F (Icc a b) volume)
  have he := integral_subtype_comap (μ := (volume : Measure ℝ)) (s := Icc a b) measurableSet_Icc F
  rw [hres] at he
  refine ⟨?_, he.trans (riemann_eq_borel_integral hab f).symm⟩
  change Integrable f.val ((volume : Measure ℝ).comap Subtype.val)
  simpa only [Function.comp_def, hres] using hi

/-- Transfer the unit uniqueness theorem across the established equality
of measurable structures. No regularity premise is required. -/
theorem representing_measure_eq :
    _root_.Specs.D11.Ch23.RiemannLebesgueBridge.representing_measure_eq := by
  intro a b hab μ hμ
  let V := Specs.continuousFunctions (Icc a b)
  obtain ⟨hV, hStone, hunit⟩ := continuousFunctions_stone (Icc a b)
  have huniq := UnitImpliesFiniteUnique.full_uniqueness_of_univ V hV hStone
    (Specs.riemannFunctional hab) (riemann_elementary hab)
    (UnitImpliesFiniteUnique.unit_univ_mem V hunit)
  rw [generated_eq_native a b] at huniq
  have heq := huniq μ (intervalLebesgue a b) hμ (lebesgue_represents hab).2
  exact ⟨heq.symm ▸ (lebesgue_represents hab).1, heq⟩

/-- Daniell–Stone supplies a measure; the independent classical integral
comparison identifies it with Lebesgue measure. -/
theorem daniell_riemann_lebesgue :
    _root_.Specs.D11.Ch23.RiemannLebesgueBridge.daniell_riemann_lebesgue := by
  intro a b hab
  let V := Specs.continuousFunctions (Icc a b)
  obtain ⟨hV, hStone, hunit⟩ := continuousFunctions_stone (Icc a b)
  have hex := UnitImpliesFiniteUnique.unit_implies_finite_unique V hV hStone
    (Specs.riemannFunctional hab) (riemann_elementary hab) hunit
  rw [generated_eq_native a b] at hex
  obtain ⟨μ, hμ, hfinite, _, _, huniq⟩ := hex
  have hr : RepresentsRiemann hab μ := fun f => (hμ f).2
  exact ⟨μ, hr, hfinite, (representing_measure_eq hab μ hr).2, huniq⟩

/-- Ordinary completion is a construction on the original Borel measure;
its entire measurable space and values coincide after the identification. -/
theorem completions_agree :
    _root_.Specs.D11.Ch23.RiemannLebesgueBridge.completions_agree := by
  intro a b hab μ hμ
  obtain ⟨_, rfl⟩ := representing_measure_eq hab μ hμ
  exact ⟨rfl, fun _ => rfl⟩

theorem completed_nonnegative_integrals :
    _root_.Specs.D11.Ch23.RiemannLebesgueBridge.completed_nonnegative_integrals := by
  intro a b hab μ hμ
  obtain ⟨_, rfl⟩ := representing_measure_eq hab μ hμ
  exact fun _ => rfl

theorem completed_scalar_integrals :
    _root_.Specs.D11.Ch23.RiemannLebesgueBridge.completed_scalar_integrals := by
  intro a b hab μ hμ
  obtain ⟨_, rfl⟩ := representing_measure_eq hab μ hμ
  intro E _ _ f
  exact ⟨Iff.rfl, fun _ => rfl⟩

end D11.Ch23.RiemannLebesgueBridge
