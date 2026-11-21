import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.ModulusCounterexample
import MathGenome.Internal.RealAnalysis.D11.Ch03.Vitali
import MathGenome.Internal.RealAnalysis.D11.Ch04.MeasurableMapTests
import MathGenome.Internal.RealAnalysis.D11.Ch05.SimpleIntegral

open Set MeasureTheory
open scoped ENNReal NNReal
noncomputable section

namespace D11.Ch04.ModulusCounterexample

open D11.Ch03
open Specs.D11.Ch04.ModulusCounterexample

lemma closedUnitInterval_measurable :
    MeasurableSet[Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value 1] closedUnitInterval := by
  exact LebesgueMeasures.borel_le_lebesgue 1 _
    (LebesgueMeasures.endpointBox_borel 1 (fun _ => 0) (fun _ => 1)
      (fun _ => true) (fun _ => true))

/-- The chosen interval really has exactly the real coordinates in [0,1]. -/
lemma coordinate_bijective : Function.Bijective
    (fun x : Interval => (⟨x.val 0, x.property 0⟩ : Icc (0 : ℝ) 1)) := by
  constructor
  · intro x y h
    apply Subtype.ext
    exact Vitali.ext_one (congrArg Subtype.val h)
  · intro t
    exact ⟨⟨Vitali.point t.val, fun _ => t.property⟩, Subtype.ext rfl⟩

lemma intervalMeasure_univ : intervalMeasure univ = 1 := by
  let : MeasurableSpace (Point 1) := Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value 1
  have he : MeasurableEmbedding (Subtype.val : Interval → Point 1) :=
    MeasurableEmbedding.subtype_coe closedUnitInterval_measurable
  have hc := @Measure.comap_apply Interval (Point 1) univ intervalSpace
    (Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value 1)
    Subtype.val he.injective (fun _ hs => he.measurableSet_image.mpr hs)
    (Specs.D11.Ch03.LebesgueMeasures.lebesgue_value 1) MeasurableSet.univ
  change (Measure.comap Subtype.val
    (Specs.D11.Ch03.LebesgueMeasures.lebesgue_value 1)) univ = 1
  calc
    _ = _ := hc
    _ = 1 := by
      have himage : (Subtype.val : Interval → Point 1) '' univ = closedUnitInterval :=
        Subtype.coe_image_univ _
      have hmass : Specs.D11.Ch03.LebesgueMeasures.lebesgue_value 1
          closedUnitInterval = 1 := by
        simpa [closedUnitInterval, closedBox, endpointBox, boxContent] using
          LebesgueMeasures.lebesgue_box 1 (fun _ => 0) (fun _ => 1)
            (fun _ => true) (fun _ => true)
      exact (congrArg (fun s : Set (Point 1) =>
        Specs.D11.Ch03.LebesgueMeasures.lebesgue_value 1 s) himage).trans hmass

lemma abs_signFunction (V : Set ℝ) (x : Interval) : |signFunction V x| = 1 := by
  classical
  by_cases hx : x.val 0 ∈ V <;> norm_num [signFunction, hx]

lemma positive_set (V : Set ℝ) :
    {x : Interval | 0 < signFunction V x} = {x | x.val 0 ∈ V} := by
  classical
  ext x
  by_cases hx : x.val 0 ∈ V <;> simp [signFunction, hx]

lemma simple_modulus_integral :
    D11.Ch05.SimpleIntegral.simpleIntegral intervalMeasure modulusSimple = 1 := by
  change ((SimpleFunc.const Interval (1 : ℝ≥0)).map
    (fun a : ℝ≥0 => (a : ℝ≥0∞))).lintegral intervalMeasure = 1
  rw [SimpleFunc.map_const, SimpleFunc.const_lintegral, intervalMeasure_univ]
  norm_num

/-- Trace measurability would make the original real set measurable in
canonical one-space, since it is contained in the interval. -/
lemma not_measurable_signFunction (V : Set ℝ) (hV : V ⊆ Icc 0 1)
    (hVm : ¬ MeasurableSet[Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value 1]
      (Vitali.inOneSpace V)) :
    ¬ @Measurable Interval ℝ intervalSpace (borel ℝ) (signFunction V) := by
  intro hf
  have hlevel : MeasurableSet {x : Interval | x.val 0 ∈ V} := by
    rw [← positive_set V]
    exact (MeasurableMapTests.real_upper_strict intervalSpace (signFunction V)).mp hf 0
  let : MeasurableSpace (Point 1) := Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value 1
  have he : MeasurableEmbedding (Subtype.val : Interval → Point 1) :=
    MeasurableEmbedding.subtype_coe closedUnitInterval_measurable
  have himage : (Subtype.val : Interval → Point 1) '' {x | x.val 0 ∈ V} =
      Vitali.inOneSpace V := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hp
      have hpI : p ∈ closedUnitInterval := by
        intro j
        have hj : j = 0 := Subsingleton.elim _ _
        simpa [hj] using hV hp
      exact ⟨⟨p, hpI⟩, hp, rfl⟩
  exact hVm (himage ▸ he.measurableSet_image.mpr hlevel)

theorem measurable_modulus_insufficient :
    Specs.D11.Ch04.ModulusCounterexample.measurable_modulus_insufficient := by
  intro V hV hVm
  refine ⟨abs_signFunction V, ?_, ?_, simple_modulus_integral, ?_,
    positive_set V, not_measurable_signFunction V hV hVm⟩
  · have h : (fun x : Interval => |signFunction V x|) = fun _ => (1 : ℝ) :=
      funext (abs_signFunction V)
    rw [h]
    exact measurable_const
  · intro x
    simpa [modulusSimple] using (abs_signFunction V x).symm
  · change D11.Ch05.SimpleIntegral.simpleIntegral intervalMeasure modulusSimple < ∞
    rw [simple_modulus_integral]
    exact ENNReal.one_lt_top

/-- Choice supplies a genuine instance of the example's nonmeasurable set. -/
theorem counterexample_exists : Specs.D11.Ch04.ModulusCounterexample.counterexample_exists := by
  obtain ⟨V, hV⟩ := Vitali.selector_exists
  have hVm := Vitali.selector_nonmeasurable V hV
  exact ⟨V, hV.1, hVm, measurable_modulus_insufficient V hV.1 hVm⟩

end D11.Ch04.ModulusCounterexample
