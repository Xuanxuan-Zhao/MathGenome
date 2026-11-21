import MathGenome.Internal.RealAnalysis.D11.Ch18.CompactCutoff
import MathGenome.Internal.RealAnalysis.D11.Ch02.Caratheodory
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.PositiveContentOuterMeasure

/-!
# The open content and its outer measure

We identify the source's supremum with the open masses of the native Riesz
measure. One inequality is the Riesz compact-support estimate. For the other,
compact inner approximation and a cutoff equal to one on each compact set
suffice. Outer regularity then identifies the specified infimum on all subsets,
so its outer-measure axioms and Borel Carathéodory measurability follow.
No countability or global boundedness hypothesis is used.
-/

open Set MeasureTheory
open scoped ENNReal

namespace D11.Ch19.PositiveContentOuterMeasure
universe u

noncomputable abbrev openContent :
    Specs.D11.Ch19.PositiveContentOuterMeasure.openContent_type.{u} :=
  @Specs.D11.Ch19.PositiveContentOuterMeasure.openContent_value.{u}
noncomputable abbrev outerCost :
    Specs.D11.Ch19.PositiveContentOuterMeasure.outerCost_type.{u} :=
  @Specs.D11.Ch19.PositiveContentOuterMeasure.outerCost_value.{u}
noncomputable abbrev positiveFunctional :
    Specs.D11.Ch19.PositiveContentOuterMeasure.positiveFunctional_type.{u} :=
  @Specs.D11.Ch19.PositiveContentOuterMeasure.positiveFunctional_value.{u}
noncomputable abbrev borelMeasure :
    Specs.D11.Ch19.PositiveContentOuterMeasure.borelMeasure_type.{u} :=
  @Specs.D11.Ch19.PositiveContentOuterMeasure.borelMeasure_value.{u}
noncomputable abbrev outerMeasure :
    Specs.D11.Ch19.PositiveContentOuterMeasure.outerMeasure_type.{u} :=
  @Specs.D11.Ch19.PositiveContentOuterMeasure.outerMeasure_value.{u}
noncomputable abbrev caratheodoryMeasure :
    Specs.D11.Ch19.PositiveContentOuterMeasure.caratheodoryMeasure_type.{u} :=
  @Specs.D11.Ch19.PositiveContentOuterMeasure.caratheodoryMeasure_value.{u}

variable {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
variable (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ)
variable (hI : ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ I f)

/-- The paper's compact-support supremum gives exactly the mass of every open. -/
theorem openContent_eq (U : Set X) (hU : IsOpen U) :
    openContent I U = borelMeasure I hI U := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  change openContent I U = RealRMK.rieszMeasure (positiveFunctional I hI) U
  apply le_antisymm
  · refine iSup_le fun f => iSup_le fun hf => iSup_le fun hs => ?_
    exact RealRMK.le_rieszMeasure_tsupport_subset (positiveFunctional I hI) hf hs
  · rw [hU.measure_eq_iSup_isCompact]
    refine iSup_le fun K => iSup_le fun hKU => iSup_le fun hK => ?_
    obtain ⟨f, hf, hfK, _, hfs⟩ := D11.Ch18.compact_cutoff X K U hK hU hKU
    exact (RealRMK.rieszMeasure_le_of_eq_one (positiveFunctional I hI)
      (fun x => (hf x).1) hK hfK).trans
        (le_iSup_of_le f (le_iSup_of_le hf (le_iSup_of_le hfs le_rfl)))

/-- Identification on all sets, including non-Borel sets. -/
theorem outerMeasure_formula (A : Set X) :
    outerMeasure I hI A = outerCost I A := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  change RealRMK.rieszMeasure (positiveFunctional I hI) A = outerCost I A
  rw [A.measure_eq_iInf_isOpen]
  congr 1
  funext U
  congr 1
  funext hAU
  congr 1
  funext hU
  exact (openContent_eq I hI U hU).symm

/-- The outer measure restricts to the prescribed content on opens. -/
theorem outerMeasure_open (U : Set X) (hU : IsOpen U) :
    outerMeasure I hI U = openContent I U :=
  (openContent_eq I hI U hU).symm

theorem empty_values :
    openContent I ∅ = 0 ∧ outerCost I ∅ = 0 ∧ outerMeasure I hI ∅ = 0 := by
  have hm : outerMeasure I hI ∅ = 0 := measure_empty
  exact ⟨(outerMeasure_open I hI ∅ isOpen_empty).symm.trans hm,
    (outerMeasure_formula I hI ∅).symm.trans hm, hm⟩

include hI in
/-- Thus the literal open-cover infimum satisfies all outer-measure axioms. -/
theorem outerCost_axioms :
    outerCost I ∅ = 0 ∧ Monotone (outerCost I) ∧
      ∀ A : ℕ → Set X, outerCost I (⋃ n, A n) ≤ ∑' n, outerCost I (A n) := by
  have heq : outerCost I = fun A => outerMeasure I hI A :=
    funext fun A => (outerMeasure_formula I hI A).symm
  rw [heq]
  exact ⟨measure_empty, (fun _ _ h => (outerMeasure I hI).mono h),
    fun A => measure_iUnion_le A⟩

theorem borel_caratheodory : borel X ≤ (outerMeasure I hI).caratheodory :=
  @le_toOuterMeasure_caratheodory X (borel X) (borelMeasure I hI)

/-- The Borel measure is the Borel restriction of the specified outer cost. -/
theorem borel_restriction (A : Set X) (_hA : MeasurableSet[borel X] A) :
    borelMeasure I hI A = outerCost I A := outerMeasure_formula I hI A

/-- Retain the full restriction, without confusing it with the Borel domain. -/
theorem caratheodory_restriction (A : Set X)
    (hA : (outerMeasure I hI).IsCaratheodory A) :
    caratheodoryMeasure I hI A = outerCost I A :=
  (D11.Ch02.Caratheodory.measure_apply (outerMeasure I hI) A hA).trans
    (outerMeasure_formula I hI A)

theorem caratheodory_complete :
    @Measure.IsComplete X (outerMeasure I hI).caratheodory
      (caratheodoryMeasure I hI) :=
  D11.Ch02.Caratheodory.measure_isComplete (outerMeasure I hI)

/-- Exactly the Radon regularity convention of Chapter 18. -/
theorem radon :
    (∀ K : Set X, IsCompact K → borelMeasure I hI K < ∞) ∧
    (∀ A : Set X, MeasurableSet[borel X] A →
      borelMeasure I hI A =
        ⨅ (U : Set X) (_ : A ⊆ U) (_ : IsOpen U), borelMeasure I hI U) ∧
    (∀ U : Set X, IsOpen U → borelMeasure I hI U =
      ⨆ (K : Set X) (_ : K ⊆ U) (_ : IsCompact K), borelMeasure I hI K) := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  change (∀ K : Set X, IsCompact K → RealRMK.rieszMeasure (positiveFunctional I hI) K < ∞) ∧
    (∀ A : Set X, MeasurableSet A →
      RealRMK.rieszMeasure (positiveFunctional I hI) A =
        ⨅ (U : Set X) (_ : A ⊆ U) (_ : IsOpen U),
          RealRMK.rieszMeasure (positiveFunctional I hI) U) ∧
    (∀ U : Set X, IsOpen U → RealRMK.rieszMeasure (positiveFunctional I hI) U =
      ⨆ (K : Set X) (_ : K ⊆ U) (_ : IsCompact K),
        RealRMK.rieszMeasure (positiveFunctional I hI) K)
  exact ⟨fun K hK => hK.measure_lt_top, fun A _ => A.measure_eq_iInf_isOpen _,
    fun U hU => hU.measure_eq_iSup_isCompact _⟩

end D11.Ch19.PositiveContentOuterMeasure
