import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.MeasurableMapTests
import MathGenome.Internal.RealAnalysis.D11.Ch01.SetSystems
import MathGenome.Internal.RealAnalysis.D11.Ch03.BorelGenerators

/-! Measurable maps and generator tests (paper.tex:1174–1203).
All scalar measurability is Borel measurability, not a.e. measurability.
The rational EReal tests use order density between arbitrary extended values,
so no finite-valued hypothesis is imposed. -/

open Set MeasurableSpace
open scoped MeasureTheory
universe u v
namespace D11.Ch04.MeasurableMapTests

abbrev measurableMap {X : Type u} {Y : Type v}
    (m : MeasurableSpace X) (n : MeasurableSpace Y) (f : X → Y) : Prop :=
  @Measurable X Y m n f

abbrev realMeasurable {X : Type u} (m : MeasurableSpace X) (f : X → ℝ) : Prop :=
  @Measurable X ℝ m (borel ℝ) f

abbrev complexMeasurable {X : Type u} (m : MeasurableSpace X) (f : X → ℂ) : Prop :=
  @Measurable X ℂ m (borel ℂ) f

abbrev extendedRealMeasurable {X : Type u} (m : MeasurableSpace X) (f : X → EReal) : Prop :=
  @Measurable X EReal m (borel EReal) f

abbrev traceMeasurableMap {X : Type u} {Y : Type v}
    (m : MeasurableSpace X) (n : MeasurableSpace Y) (E : Set X) (f : E → Y) : Prop :=
  @Measurable E Y (m.comap Subtype.val) n f

theorem map_iff : Specs.D11.Ch04.MeasurableMapTests.map_iff := by
  intro X Y m n f
  rfl

theorem trace_iff : Specs.D11.Ch04.MeasurableMapTests.trace_iff := by
  intro X Y m n E hE f
  constructor
  · intro hf B hB
    exact (D11.Ch01.SetSystems.trace_measurable_iff m hE (f ⁻¹' B)).mp (hf hB)
  · intro hf B hB
    exact (D11.Ch01.SetSystems.trace_measurable_iff m hE (f ⁻¹' B)).mpr (hf B hB)

theorem generator_test : Specs.D11.Ch04.MeasurableMapTests.generator_test := by
  intro X Y m n C f hn
  subst n
  constructor
  · intro hf B hB
    exact hf (measurableSet_generateFrom hB)
  · intro hf
    exact @measurable_generateFrom X Y m C f hf

theorem real_lower_strict : Specs.D11.Ch04.MeasurableMapTests.real_lower_strict := by
  intro X m f
  let : MeasurableSpace X := m
  exact ⟨fun hf _ => hf measurableSet_Iio, fun hf => measurable_of_Iio hf⟩

theorem real_lower_closed : Specs.D11.Ch04.MeasurableMapTests.real_lower_closed := by
  intro X m f
  let : MeasurableSpace X := m
  exact ⟨fun hf _ => hf measurableSet_Iic, fun hf => measurable_of_Iic hf⟩

theorem real_upper_strict : Specs.D11.Ch04.MeasurableMapTests.real_upper_strict := by
  intro X m f
  let : MeasurableSpace X := m
  exact ⟨fun hf _ => hf measurableSet_Ioi, fun hf => measurable_of_Ioi hf⟩

theorem real_upper_closed : Specs.D11.Ch04.MeasurableMapTests.real_upper_closed := by
  intro X m f
  let : MeasurableSpace X := m
  exact ⟨fun hf _ => hf measurableSet_Ici, fun hf => measurable_of_Ici hf⟩

theorem ereal_lower_strict : Specs.D11.Ch04.MeasurableMapTests.ereal_lower_strict := by
  intro X m f
  let : MeasurableSpace X := m
  exact ⟨fun hf _ => hf measurableSet_Iio, fun hf => measurable_of_Iio hf⟩

theorem ereal_lower_closed : Specs.D11.Ch04.MeasurableMapTests.ereal_lower_closed := by
  intro X m f
  let : MeasurableSpace X := m
  exact ⟨fun hf _ => hf measurableSet_Iic, fun hf => measurable_of_Iic hf⟩

theorem ereal_upper_strict : Specs.D11.Ch04.MeasurableMapTests.ereal_upper_strict := by
  intro X m f
  let : MeasurableSpace X := m
  exact ⟨fun hf _ => hf measurableSet_Ioi, fun hf => measurable_of_Ioi hf⟩

theorem ereal_upper_closed : Specs.D11.Ch04.MeasurableMapTests.ereal_upper_closed := by
  intro X m f
  let : MeasurableSpace X := m
  exact ⟨fun hf _ => hf measurableSet_Ici, fun hf => measurable_of_Ici hf⟩

theorem real_lower_strict_rat : Specs.D11.Ch04.MeasurableMapTests.real_lower_strict_rat := by
  intro X m f
  let : MeasurableSpace X := m
  constructor
  · intro hf q
    exact hf measurableSet_Iio
  · intro hf
    rw [Real.borel_eq_generateFrom_Iio_rat]
    apply measurable_generateFrom
    intro B hB
    simp only [mem_iUnion, mem_singleton_iff] at hB
    obtain ⟨q, rfl⟩ := hB
    exact hf q

theorem real_lower_closed_rat : Specs.D11.Ch04.MeasurableMapTests.real_lower_closed_rat := by
  intro X m f
  let : MeasurableSpace X := m
  constructor
  · intro hf q
    exact hf measurableSet_Iic
  · intro hf
    rw [Real.borel_eq_generateFrom_Iic_rat]
    apply measurable_generateFrom
    intro B hB
    simp only [mem_iUnion, mem_singleton_iff] at hB
    obtain ⟨q, rfl⟩ := hB
    exact hf q

theorem real_upper_strict_rat : Specs.D11.Ch04.MeasurableMapTests.real_upper_strict_rat := by
  intro X m f
  let : MeasurableSpace X := m
  constructor
  · intro hf q
    exact hf measurableSet_Ioi
  · intro hf
    rw [Real.borel_eq_generateFrom_Ioi_rat]
    apply measurable_generateFrom
    intro B hB
    simp only [mem_iUnion, mem_singleton_iff] at hB
    obtain ⟨q, rfl⟩ := hB
    exact hf q

theorem real_upper_closed_rat : Specs.D11.Ch04.MeasurableMapTests.real_upper_closed_rat := by
  intro X m f
  let : MeasurableSpace X := m
  constructor
  · intro hf q
    exact hf measurableSet_Ici
  · intro hf
    rw [Real.borel_eq_generateFrom_Ici_rat]
    apply measurable_generateFrom
    intro B hB
    simp only [mem_iUnion, mem_singleton_iff] at hB
    obtain ⟨q, rfl⟩ := hB
    exact hf q

/-- Rational levels recover even the infinite-threshold lower rays. -/
theorem ereal_lower_strict_rat : Specs.D11.Ch04.MeasurableMapTests.ereal_lower_strict_rat := by
  intro X m f
  let : MeasurableSpace X := m
  constructor
  · intro hf q
    exact hf measurableSet_Iio
  · intro hf
    apply (ereal_lower_strict m f).mpr
    intro a
    have heq : {x | f x < a} =
        ⋃ (q : ℚ) (_ : ((q : ℝ) : EReal) < a), {x | f x < ((q : ℝ) : EReal)} := by
      ext x
      simp only [mem_ofPred_eq, mem_iUnion]
      constructor
      · intro hx
        obtain ⟨q, hxq, hqa⟩ := EReal.exists_rat_btwn_of_lt hx
        exact ⟨q, hqa, hxq⟩
      · rintro ⟨q, hqa, hxq⟩
        exact hxq.trans hqa
    rw [heq]
    exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ => hf q

/-- Rational levels recover even the infinite-threshold upper rays. -/
theorem ereal_upper_strict_rat : Specs.D11.Ch04.MeasurableMapTests.ereal_upper_strict_rat := by
  intro X m f
  let : MeasurableSpace X := m
  constructor
  · intro hf q
    exact hf measurableSet_Ioi
  · intro hf
    apply (ereal_upper_strict m f).mpr
    intro a
    have heq : {x | f x > a} =
        ⋃ (q : ℚ) (_ : a < ((q : ℝ) : EReal)), {x | f x > ((q : ℝ) : EReal)} := by
      ext x
      simp only [mem_ofPred_eq, mem_iUnion]
      constructor
      · intro hx
        obtain ⟨q, haq, hqx⟩ := EReal.exists_rat_btwn_of_lt hx
        exact ⟨q, haq, hqx⟩
      · rintro ⟨q, haq, hqx⟩
        exact haq.trans hqx
    rw [heq]
    exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ => hf q

theorem ereal_lower_closed_rat : Specs.D11.Ch04.MeasurableMapTests.ereal_lower_closed_rat := by
  intro X m f
  let : MeasurableSpace X := m
  constructor
  · intro hf q
    exact hf measurableSet_Iic
  · intro hf
    apply (ereal_upper_strict_rat m f).mpr
    intro q
    simpa only [Set.compl_ofPred, not_le] using (hf q).compl

theorem ereal_upper_closed_rat : Specs.D11.Ch04.MeasurableMapTests.ereal_upper_closed_rat := by
  intro X m f
  let : MeasurableSpace X := m
  constructor
  · intro hf q
    exact hf measurableSet_Ici
  · intro hf
    apply (ereal_lower_strict_rat m f).mpr
    intro q
    simpa only [Set.compl_ofPred, not_le] using (hf q).compl

end D11.Ch04.MeasurableMapTests
