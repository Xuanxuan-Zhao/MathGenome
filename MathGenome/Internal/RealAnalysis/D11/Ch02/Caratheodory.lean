import MathGenome.Internal.RealAnalysis.D11.Ch02.OuterCover
import MathGenome.Internal.RealAnalysis.D11.Ch01.MeasureDefinitions
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch02.Caratheodory

/-!
# Carathéodory's splitting test and complete measure

The native predicate tests every subset of the underlying type. Its native
measurable space provides exactly the sigma-algebra in the source. The native
`toMeasure` construction restricts the given outer measure to that space;
`measure_apply` records the exact agreement on its measurable sets.

The finite-test reduction uses the order on `[0,∞]`: a test set of infinite
outer measure imposes no reverse inequality. Null subsets pass the full test
by monotonicity. These facts prove completeness without sigma-finiteness.
-/

open Set MeasureTheory
open scoped ENNReal

universe u

namespace D11.Ch02.Caratheodory

/-- The splitting predicate, with tests over all subsets. -/
abbrev isMeasurable {α : Type u} (m : OuterMeasure α) (A : Set α) : Prop :=
  m.IsCaratheodory A

/-- The sigma-algebra of precisely the sets passing the splitting test. -/
abbrev measurableSpace {α : Type u} (m : OuterMeasure α) : MeasurableSpace α :=
  m.caratheodory

/-- Restriction of the outer measure to its Carathéodory sigma-algebra. -/
noncomputable def measure {α : Type u} (m : OuterMeasure α) :
    @Measure α (measurableSpace m) :=
  @OuterMeasure.toMeasure α (measurableSpace m) m le_rfl

theorem splitting_iff {α : Type u} (m : OuterMeasure α) (A : Set α) :
    isMeasurable m A ↔ ∀ E : Set α, m E = m (E ∩ A) + m (E \ A) :=
  Iff.rfl

/-- Subadditivity always supplies the forward splitting inequality. -/
theorem splitting_le {α : Type u} (m : OuterMeasure α) (A E : Set α) :
    m E ≤ m (E ∩ A) + m (E \ A) :=
  measure_le_inter_add_sdiff m E A

theorem isMeasurable_iff_le {α : Type u} (m : OuterMeasure α) (A : Set α) :
    isMeasurable m A ↔ ∀ E : Set α, m (E ∩ A) + m (E \ A) ≤ m E :=
  m.isCaratheodory_iff_le'

/-- Only finite-outer-measure tests are needed for the reverse inequality. -/
theorem isMeasurable_iff_finite {α : Type u} (m : OuterMeasure α) (A : Set α) :
    isMeasurable m A ↔
      ∀ E : Set α, m E < ∞ → m (E ∩ A) + m (E \ A) ≤ m E := by
  rw [isMeasurable_iff_le]
  constructor
  · intro h E _
    exact h E
  · intro h E
    by_cases hE : m E = ∞
    · rw [hE]
      exact le_top
    · exact h E (lt_top_iff_ne_top.mpr hE)

theorem measurableSet_iff {α : Type u} (m : OuterMeasure α) (A : Set α) :
    MeasurableSet[measurableSpace m] A ↔ isMeasurable m A :=
  Iff.rfl

/-- Explicit algebra and countable-union closure of the splitting sets. -/
theorem sigmaAlgebra {α : Type u} (m : OuterMeasure α) :
    IsSetAlgebra {A : Set α | isMeasurable m A} ∧
      ∀ E : ℕ → Set α, (∀ n, isMeasurable m (E n)) →
        isMeasurable m (⋃ n, E n) := by
  apply (D11.Ch01.SetSystems.sigmaAlgebra_iff _).mp
  exact ⟨measurableSpace m, fun A => measurableSet_iff m A⟩

/-- Agreement is asserted on the source domain, not on arbitrary subsets. -/
theorem measure_apply {α : Type u} (m : OuterMeasure α) (A : Set α)
    (hA : isMeasurable m A) : measure m A = m A :=
  @toMeasure_apply α (measurableSpace m) m le_rfl A hA

theorem countable_additivity {α : Type u} (m : OuterMeasure α) (E : ℕ → Set α)
    (hE : ∀ n, isMeasurable m (E n))
    (hd : Pairwise fun i j => Disjoint (E i) (E j)) :
    m (⋃ n, E n) = ∑' n, m (E n) :=
  m.iUnion_eq_of_caratheodory hE hd

/-- Every subset of an outer-null set is splitting-measurable and outer-null. -/
theorem null_subset {α : Type u} (m : OuterMeasure α) (N Z : Set α)
    (hN : m N = 0) (hZN : Z ⊆ N) : isMeasurable m Z ∧ m Z = 0 := by
  have hZ : m Z = 0 := measure_mono_null hZN hN
  exact ⟨m.isCaratheodory_of_measure_eq_zero hZ, hZ⟩

/-- Native completeness, available to later library applications. -/
instance measure_isComplete {α : Type u} (m : OuterMeasure α) :
    @Measure.IsComplete α (measurableSpace m) (measure m) := by
  constructor
  intro Z hZ
  apply m.isCaratheodory_of_measure_eq_zero
  exact le_antisymm ((@le_toMeasure_apply α (measurableSpace m) m le_rfl Z).trans_eq hZ)
    bot_le

/-- Completeness with the previously fixed source definition of negligible sets. -/
theorem complete {α : Type u} (m : OuterMeasure α) :
    @D11.Ch01.MeasureDefinitions.isComplete α (measurableSpace m) (measure m) :=
  (@D11.Ch01.MeasureDefinitions.complete_iff α (measurableSpace m) (measure m)).mpr
    (measure_isComplete m)

end D11.Ch02.Caratheodory
