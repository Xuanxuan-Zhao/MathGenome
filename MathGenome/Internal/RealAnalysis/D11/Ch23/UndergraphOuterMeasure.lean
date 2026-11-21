import MathGenome.Internal.RealAnalysis.D11.Ch23.UndergraphContent
import MathGenome.Internal.RealAnalysis.D11.Ch02.Caratheodory
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.UndergraphOuterMeasure
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent

/-! The paper's covering construction on X × ℝ. The semiring extension
API used here has no whole-space membership or countable-cover assumption.
Stone truncation is unnecessary for this step: lattice closure and the
elementary integral properties already suffice. -/
noncomputable section
universe u
open Set MeasureTheory Function
open scoped ENNReal BigOperators
namespace D11.Ch23

abbrev undergraphCoverCost {X : Type u} (V : Submodule ℝ (X → ℝ))
    (L : V →ₗ[ℝ] ℝ) := Specs.UndergraphCoverCost V L
abbrev undergraphOuterMeasure {X : Type u} (V : Submodule ℝ (X → ℝ))
    (L : V →ₗ[ℝ] ℝ) := Specs.UndergraphOuterMeasure V L
abbrev undergraphMeasurableSpace {X : Type u} (V : Submodule ℝ (X → ℝ)) :=
  Specs.UndergraphMeasurableSpace V
abbrev undergraphMeasure {X : Type u} (V : Submodule ℝ (X → ℝ))
    (L : V →ₗ[ℝ] ℝ) := Specs.UndergraphMeasure V L

theorem undergraph_outerMeasure_formula : Specs.UndergraphOuterMeasureFormula := by
  intro X V L A
  unfold Specs.UndergraphOuterMeasure inducedOuterMeasure
  rw [OuterMeasure.ofFunction_eq_iInf_mem _ _ (P := fun s => s ∈ undergraphFamily V)
    (fun s hs => extend_eq_top _ hs)]
  unfold Specs.UndergraphCoverCost
  apply iInf_congr
  intro a
  apply iInf_congr
  intro ha
  apply iInf_congr
  intro _
  congr 1
  funext n
  exact extend_eq _ (ha n)

theorem undergraph_coverCost_axioms : Specs.UndergraphCoverCostAxioms := by
  intro X V L
  have he : Specs.UndergraphCoverCost V L = fun A => undergraphOuterMeasure V L A :=
    (funext (undergraph_outerMeasure_formula V L)).symm
  rw [he]
  exact ⟨measure_empty, fun _ _ h => measure_mono h, fun a => measure_iUnion_le a⟩

theorem undergraph_no_cover : Specs.UndergraphNoCover := by
  intro X V L A h
  rw [undergraph_outerMeasure_formula]
  apply iInf_eq_top.mpr
  intro a
  apply iInf_eq_top.mpr
  intro ha
  apply iInf_eq_top.mpr
  intro hA
  exact False.elim (h a ha hA)

/-- Bundle exactly the finite additivity already established upstream. -/
def undergraphAddContent {X : Type u} (V : Submodule ℝ (X → ℝ))
    (hV : Specs.IsVectorLattice V) (L : V →ₗ[ℝ] ℝ)
    (hL : Specs.IsElementaryIntegral V L) : AddContent ℝ≥0∞ (undergraphFamily V) where
  toFun := undergraphContent V L
  empty' := undergraph_content_empty V L
  sUnion' I hI hd hu := by
    have he : (⋃ s : I, (s : Set (X × ℝ))) = ⋃₀ (↑I : Set (Set (X × ℝ))) := by
      ext p
      simp
    have h := undergraph_content_finite_additive V hV L hL
      (⋃₀ (↑I : Set (Set (X × ℝ)))) (fun s : I => (s : Set (X × ℝ))) hu
      (fun s => hI s.property)
      (fun s t hst => hd s.property t.property (fun h => hst (Subtype.ext h))) he
    simpa only [Finset.sum_coe_sort] using h

theorem undergraphAddContent_sigmaSubadditive {X : Type u}
    (V : Submodule ℝ (X → ℝ)) (hV : Specs.IsVectorLattice V)
    (L : V →ₗ[ℝ] ℝ) (hL : Specs.IsElementaryIntegral V L) :
    (undergraphAddContent V hV L hL).IsSigmaSubadditive := by
  intro a ha hu
  exact undergraph_content_cover V hV L hL (⋃ n, a n) a hu ha subset_rfl

theorem undergraph_caratheodory : Specs.UndergraphCaratheodory := by
  intro X V hV L hL s hs
  exact AddContent.isCaratheodory_inducedOuterMeasure_of_mem
    (undergraph_isSetSemiring V hV) (undergraphAddContent V hV L hL) hs

theorem undergraph_outerMeasure_exact : Specs.UndergraphOuterMeasureExact := by
  intro X V hV L hL s hs
  exact AddContent.inducedOuterMeasure_eq
    (undergraph_isSetSemiring V hV) (undergraphAddContent V hV L hL)
    (undergraphAddContent_sigmaSubadditive V hV L hL) hs

theorem undergraph_generated_le : Specs.UndergraphGeneratedLe := by
  intro X V hV L hL
  apply MeasurableSpace.generateFrom_le
  intro s hs
  exact undergraph_caratheodory V hV L hL s hs

theorem undergraph_measure_apply : Specs.UndergraphMeasureApply := by
  classical
  intro X V hV L hL A hA
  unfold Specs.UndergraphMeasure
  rw [dif_pos (undergraph_generated_le V hV L hL)]
  exact @toMeasure_apply _ (Specs.UndergraphMeasurableSpace V) _ _ A hA

theorem undergraph_measure_exact : Specs.UndergraphMeasureExact := by
  intro X V hV L hL s hs
  exact (undergraph_measure_apply V hV L hL s
    (MeasurableSpace.measurableSet_generateFrom hs)).trans
    (undergraph_outerMeasure_exact V hV L hL s hs)

end D11.Ch23
