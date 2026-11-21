import MathGenome.Internal.RealAnalysis.D11.Ch18.BorelBaire
import MathGenome.Internal.RealAnalysis.D11.Ch18.CompactCutoff
import MathGenome.Internal.RealAnalysis.D11.Ch18.CountablePrecompactBase
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.BaireBorelSecondCountable

/-!
# Baire equals Borel on second-countable LCH spaces

Each open set has a compact cover. Cutoffs equal to one on those compacts
give a countable positivity cover with support inside the open set.
Do this for each member of a countable base to obtain one countable family
working for every open set. Its positivity sets are Baire measurable by the
exact Cc-generated definition, so every open set is Baire measurable.
The compact G_delta conclusion is exported from the accepted topology stage.
-/

open Set TopologicalSpace
open scoped MeasureTheory

universe u

namespace D11.Ch18

/-- An open set is covered by the positivity sets of a sequence of cutoffs
whose entire closed supports lie in that open set. -/
theorem openCutoffCover (X : Type u) [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    (U : Set X) (hU : IsOpen U) :
    ∃ f : ℕ → D11.Ch19.Cc X ℝ,
      (∀ n, (∀ x, 0 ≤ f n x ∧ f n x ≤ 1) ∧
        closure {x | f n x ≠ 0} ⊆ U) ∧
      U = ⋃ n, {x | 0 < f n x} := by
  obtain ⟨K, hK, hcover⟩ := openCompactCover X U hU
  choose f hf using fun n => compact_cutoff X (K n) U (hK n).1 hU (hK n).2
  refine ⟨f, fun n => ⟨(hf n).1, (hf n).2.2.2⟩, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover ▸ hx)
    exact mem_iUnion.mpr ⟨n, by change 0 < f n x; rw [(hf n).2.1 x hn]; exact zero_lt_one⟩
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact (hf n).2.2.2 (subset_closure (ne_of_gt hn))

/-- A countable family of real Cc cutoffs whose positivity sets generate
every open set. The union includes only cutoffs with support inside U. -/
theorem countableCutoffGenerators :
    Specs.D11.Ch18.BaireBorelSecondCountable.CountableCutoffGenerators.{u} := by
  classical
  intro X _ _ _ _
  obtain ⟨B, hBcount, hBbasis, hB⟩ := countablePrecompactBase X
  have : Countable B := hBcount.to_subtype
  choose f hf using fun V : B => openCutoffCover X V.val (hB V.val V.property).1
  let F : Set (D11.Ch19.Cc X ℝ) := ⋃ V : B, range (f V)
  refine ⟨F, countable_iUnion (fun V => countable_range (f V)), ?_, ?_⟩
  · intro g hg
    obtain ⟨V, n, rfl⟩ := mem_iUnion.mp hg
    exact (hf V).1 n |>.1
  · intro U hU
    ext x
    constructor
    · intro hx
      obtain ⟨V, hVB, hxV, hVU⟩ := hBbasis.exists_subset_of_mem_open hx hU
      let v : B := ⟨V, hVB⟩
      have hxv : x ∈ (v : Set X) := hxV
      rw [(hf v).2] at hxv
      obtain ⟨n, hn⟩ := mem_iUnion.mp hxv
      refine mem_iUnion.mpr ⟨f v n, mem_iUnion.mpr ⟨?_, mem_iUnion.mpr ⟨?_, hn⟩⟩⟩
      · exact mem_iUnion.mpr ⟨v, mem_range_self n⟩
      · exact ((hf v).1 n).2.trans hVU
    · intro hx
      obtain ⟨g, hx⟩ := mem_iUnion.mp hx
      obtain ⟨_, hx⟩ := mem_iUnion.mp hx
      obtain ⟨hgU, hxg⟩ := mem_iUnion.mp hx
      exact hgU (subset_closure (ne_of_gt hxg))

/-- Every open set is measurable for the exact Cc-generated Baire structure. -/
theorem open_baire_measurable (X : Type u) [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    (U : Set X) (hU : IsOpen U) : MeasurableSet[baireSpace X] U := by
  obtain ⟨F, hF, _, hcover⟩ := countableCutoffGenerators X
  have : Countable F := hF.to_subtype
  rw [hcover U hU, biUnion_eq_iUnion]
  apply MeasurableSet.iUnion
  intro f
  apply MeasurableSet.iUnion
  intro _
  exact (cc_baire_measurable X f.val)
    (show MeasurableSet[borel ℝ] (Ioi 0) from
      MeasurableSpace.measurableSet_generateFrom
        (show IsOpen (Ioi (0 : ℝ)) from isOpen_Ioi))

/-- The exact Baire and Borel sigma-algebras coincide under second countability. -/
theorem baire_eq_borel_secondCountable :
    Specs.D11.Ch18.BaireBorelSecondCountable.BaireEqBorel.{u} := by
  intro X _ _ _ _
  change baireSpace X = borelSpace X
  apply le_antisymm (baireSpace_le_borelSpace X)
  rw [borelSpace_eq_generateFrom]
  exact MeasurableSpace.generateFrom_le fun U hU => open_baire_measurable X U hU

/-- Every compact subset is an ambient countable intersection of open sets,
including the empty compact set and the empty ambient space. -/
theorem compact_gdelta_secondCountable :
    Specs.D11.Ch18.BaireBorelSecondCountable.CompactGDelta.{u} :=
  compactOpenIntersection

end D11.Ch18
