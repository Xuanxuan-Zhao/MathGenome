import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.GeneratedRingAlgebra
import MathGenome.Internal.RealAnalysis.D11.Ch23.SigmaRingInterfaces
import MathGenome.Internal.RealAnalysis.D11.Ch23.VectorLatticeStone
import MathGenome.Internal.RealAnalysis.D11.Ch01.SetSystems
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! The two generated domains in paper.tex:6203--6211.
All sets are subsets of the original arbitrary type. No measure, unit function,
nonemptiness, or Stone condition is used in this generation argument. -/

open Set MeasurableSpace
open scoped MeasureTheory
universe u

namespace D11.Ch23

/-- Strictly positive superlevel sets of the original lattice functions. -/
abbrev positiveLevelFamily {X : Type u} (V : Submodule ℝ (X → ℝ)) : Set (Set X) :=
  Specs.positiveLevelFamily V

/-- R_V, a sigma-ring without any whole-space requirement. -/
def positiveLevelSigmaRing {X : Type u} (V : Submodule ℝ (X → ℝ)) : SigmaRing X :=
  generatedSigmaRing (positiveLevelFamily V)

/-- A_V, a sigma-algebra on the whole original domain. -/
@[instance_reducible]
def positiveLevelMeasurableSpace {X : Type u} (V : Submodule ℝ (X → ℝ)) :
    MeasurableSpace X :=
  generateFrom (positiveLevelFamily V)

theorem positiveLevel_mem_sigmaRing {X : Type u} (V : Submodule ℝ (X → ℝ))
    (f : X → ℝ) (hf : f ∈ V) (b : ℝ) (hb : 0 < b) :
    {x | b < f x} ∈ positiveLevelSigmaRing V :=
  subset_generatedSigmaRing _ ⟨f, hf, b, hb, rfl⟩

theorem positiveLevelSigmaRing_le {X : Type u} (V : Submodule ℝ (X → ℝ))
    (R : SigmaRing X) (h : positiveLevelFamily V ⊆ (R : Set (Set X))) :
    (positiveLevelSigmaRing V : Set (Set X)) ⊆ (R : Set (Set X)) :=
  generatedSigmaRing_le _ R h

theorem positiveLevelSigmaRing_eq_iInter {X : Type u} (V : Submodule ℝ (X → ℝ)) :
    (positiveLevelSigmaRing V : Set (Set X)) =
      ⋂ (R : SigmaRing X) (_ : positiveLevelFamily V ⊆ (R : Set (Set X))),
        (R : Set (Set X)) :=
  generatedSigmaRing_eq_iInter _

theorem positiveLevel_measurableSet {X : Type u} (V : Submodule ℝ (X → ℝ))
    (f : X → ℝ) (hf : f ∈ V) (b : ℝ) (hb : 0 < b) :
    MeasurableSet[positiveLevelMeasurableSpace V] {x | b < f x} :=
  measurableSet_generateFrom ⟨f, hf, b, hb, rfl⟩

theorem positiveLevelMeasurableSpace_le_iff {X : Type u} (V : Submodule ℝ (X → ℝ))
    (m : MeasurableSpace X) :
    positiveLevelMeasurableSpace V ≤ m ↔
      positiveLevelFamily V ⊆ {A | MeasurableSet[m] A} :=
  generateFrom_le_iff m

theorem positiveLevelMeasurableSpace_eq_sInf {X : Type u}
    (V : Submodule ℝ (X → ℝ)) :
    positiveLevelMeasurableSpace V =
      sInf {m : MeasurableSpace X | positiveLevelFamily V ⊆ {A | MeasurableSet[m] A}} :=
  D11.Ch01.SetSystems.generated_eq_sInf _

theorem sigmaRing_sets_measurable {X : Type u} (V : Submodule ℝ (X → ℝ))
    (A : Set X) (hA : A ∈ positiveLevelSigmaRing V) :
    MeasurableSet[positiveLevelMeasurableSpace V] A := by
  let : MeasurableSpace X := positiveLevelMeasurableSpace V
  let R : SigmaRing X :=
    { sets := {B | MeasurableSet[positiveLevelMeasurableSpace V] B}
      empty_mem := by
        change MeasurableSet[positiveLevelMeasurableSpace V] ∅
        exact MeasurableSet.empty
      diff_mem := by
        intro B C hB hC
        change MeasurableSet[positiveLevelMeasurableSpace V] B at hB
        change MeasurableSet[positiveLevelMeasurableSpace V] C at hC
        change MeasurableSet[positiveLevelMeasurableSpace V] (B \ C)
        exact hB.diff hC
      iUnion_mem := by
        intro B hB
        change ∀ n, MeasurableSet[positiveLevelMeasurableSpace V] (B n) at hB
        change MeasurableSet[positiveLevelMeasurableSpace V] (⋃ n, B n)
        exact MeasurableSet.iUnion hB }
  exact positiveLevelSigmaRing_le V R (fun _ hB => measurableSet_generateFrom hB) hA

theorem generateFrom_sigmaRing {X : Type u} (V : Submodule ℝ (X → ℝ)) :
    generateFrom (positiveLevelSigmaRing V : Set (Set X)) =
      positiveLevelMeasurableSpace V := by
  apply le_antisymm
  · exact generateFrom_le fun A hA => sigmaRing_sets_measurable V A hA
  · exact generateFrom_mono (subset_generatedSigmaRing _)

/-- Positive superlevels determine measurability of the positive part, including
the zero level. Rational levels keep the union countable. -/
private theorem measurable_positivePart_of_levels {X : Type u} [MeasurableSpace X]
    (f : X → ℝ) (h : ∀ b : ℝ, 0 < b → MeasurableSet {x | b < f x}) :
    Measurable (fun x => max (f x) 0) := by
  apply measurable_of_Ioi
  intro a
  by_cases ha : a < 0
  · have heq : (fun x => max (f x) 0) ⁻¹' Ioi a = univ := by
      ext x
      simp only [mem_preimage, mem_Ioi, mem_univ, iff_true]
      exact ha.trans_le (le_max_right _ _)
    rw [heq]
    exact MeasurableSet.univ
  · have ha0 : 0 ≤ a := le_of_not_gt ha
    have heq : (fun x => max (f x) 0) ⁻¹' Ioi a =
        ⋃ (q : ℚ) (_ : a < (q : ℝ)), {x | (q : ℝ) < f x} := by
      ext x
      simp only [mem_preimage, mem_Ioi, mem_iUnion, mem_ofPred_eq]
      constructor
      · intro hx
        have hax : a < f x := by
          rcases lt_max_iff.mp hx with hx | hx
          · exact hx
          · exact (not_lt_of_ge ha0 hx).elim
        obtain ⟨q, haq, hqx⟩ := exists_rat_btwn hax
        exact ⟨q, haq, hqx⟩
      · rintro ⟨q, haq, hqx⟩
        exact (haq.trans hqx).trans_le (le_max_left _ _)
    rw [heq]
    exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun haq =>
      h q (lt_of_le_of_lt ha0 haq)

theorem measurable_of_mem {X : Type u} (V : Submodule ℝ (X → ℝ))
    (_hV : IsVectorLattice V) (f : X → ℝ) (hf : f ∈ V) :
    @Measurable X ℝ (positiveLevelMeasurableSpace V) (borel ℝ) f := by
  let : MeasurableSpace X := positiveLevelMeasurableSpace V
  have hp := measurable_positivePart_of_levels f (positiveLevel_measurableSet V f hf)
  have hn := measurable_positivePart_of_levels (-f)
    (positiveLevel_measurableSet V (-f) (V.neg_mem hf))
  have heq : (fun x => max (f x) 0 - max (-f x) 0) = f := by
    funext x
    rcases le_total 0 (f x) with hx | hx
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), sub_zero]
    · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
      simp
  have hs : Measurable (fun x => max (f x) 0 - max (-f x) 0) := hp.sub hn
  rw [heq] at hs
  exact hs

theorem le_iff_all_measurable {X : Type u} (V : Submodule ℝ (X → ℝ))
    (hV : IsVectorLattice V) (m : MeasurableSpace X) :
    positiveLevelMeasurableSpace V ≤ m ↔
      ∀ f ∈ V, @Measurable X ℝ m (borel ℝ) f := by
  constructor
  · intro h f hf
    exact (measurable_of_mem V hV f hf).mono h le_rfl
  · intro h
    apply generateFrom_le
    rintro A ⟨f, hf, b, _hb, rfl⟩
    exact h f hf measurableSet_Ioi

theorem sigmaRing_need_not_contain_univ :
    (Set.univ : Set Unit) ∉ positiveLevelSigmaRing (⊥ : Submodule ℝ (Unit → ℝ)) ∧
    MeasurableSet[positiveLevelMeasurableSpace (⊥ : Submodule ℝ (Unit → ℝ))]
      (Set.univ : Set Unit) := by
  let R : SigmaRing Unit :=
    { sets := {∅}
      empty_mem := rfl
      diff_mem := by
        intro A B hA hB
        simp only [mem_singleton_iff] at hA hB ⊢
        simp [hA]
      iUnion_mem := by
        intro A hA
        simp only [mem_singleton_iff] at hA ⊢
        simp [hA] }
  have h : positiveLevelFamily (⊥ : Submodule ℝ (Unit → ℝ)) ⊆ (R : Set (Set Unit)) := by
    rintro A ⟨f, hf, b, hb, rfl⟩
    have hf0 := (Submodule.mem_bot ℝ).mp hf
    change {x | b < f x} = ∅
    simp [hf0, not_lt_of_ge hb.le]
  refine ⟨?_, MeasurableSet.univ⟩
  intro hu
  have hzero := positiveLevelSigmaRing_le _ R h hu
  change (Set.univ : Set Unit) = ∅ at hzero
  exact Set.nonempty_iff_ne_empty.mp Set.univ_nonempty hzero

end D11.Ch23
