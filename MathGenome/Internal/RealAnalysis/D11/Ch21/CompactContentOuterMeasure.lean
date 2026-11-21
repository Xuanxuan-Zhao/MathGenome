import MathGenome.Internal.RealAnalysis.D11.Ch21.CompactContentCluster
import MathGenome.Internal.RealAnalysis.D11.Ch02.Caratheodory
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.CompactContentOuterMeasure

/-!
# The outer measure of a finite compact content

The generic `Content` construction takes the supremum over compact subsets
of an open set and the infimum over open supersets of an arbitrary set.
We check both formulas, the unrestricted outer-measure axioms, the full
Carathéodory splitting test for Borel sets, and invariance under images of
left translations. The measure has exactly the Borel measurable space.

The final bridge applies to every real-valued content satisfying the preceding
construction's laws. No sigma-compactness, second countability, metrizability
or sigma-finiteness is used. Regularity and nonzero mass are the next goal.
-/

noncomputable section
namespace D11.Ch21.CompactContentOuterMeasure

open Set TopologicalSpace MeasureTheory
open scoped ENNReal
universe u

/-- A real-valued finite nonnegative compact content as a native content. -/
def realContent : Specs.D11.Ch21.CompactContentOuterMeasure.realContent_type.{u} := Specs.D11.Ch21.CompactContentOuterMeasure.realContent_value

theorem realContent_apply : Specs.D11.Ch21.CompactContentOuterMeasure.realContent_apply.{u} := by
  intro G _ h hn hm hs ha K
  exact ENNReal.coe_nnreal_eq ⟨h K, hn K⟩

/-- The source's supremum over all compact subsets of an open set. -/
def openCost : Specs.D11.Ch21.CompactContentOuterMeasure.openCost_type.{u} := Specs.D11.Ch21.CompactContentOuterMeasure.openCost_value

/-- The source's infimum over all open supersets, allowing infinite cost. -/
def outerCost : Specs.D11.Ch21.CompactContentOuterMeasure.outerCost_type.{u} := Specs.D11.Ch21.CompactContentOuterMeasure.outerCost_value

/-- Bundling the open approximation construction as an outer measure. -/
def outerMeasure : Specs.D11.Ch21.CompactContentOuterMeasure.outerMeasure_type.{u} := fun c => c.outerMeasure

theorem outerMeasure_apply : Specs.D11.Ch21.CompactContentOuterMeasure.outerMeasure_apply.{u} := by
  intro G _ _ c A
  exact c.outerMeasure_eq_iInf A

theorem outerCost_axioms : Specs.D11.Ch21.CompactContentOuterMeasure.outerCost_axioms.{u} := by
  intro G _ _ c
  have h (A : Set G) : Specs.D11.Ch21.CompactContentOuterMeasure.outerCost_value c A = c.outerMeasure A :=
    (outerMeasure_apply c A).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [h]
    exact measure_empty
  · intro A B hAB
    rw [h, h]
    exact measure_mono hAB
  · intro A
    simp_rw [h]
    exact measure_iUnion_le A

theorem outerMeasure_open : Specs.D11.Ch21.CompactContentOuterMeasure.outerMeasure_open.{u} := by
  intro G _ _ c U
  exact c.outerMeasure_opens U

theorem borel_le_caratheodory : Specs.D11.Ch21.CompactContentOuterMeasure.borel_le_caratheodory.{u} := by
  intro G _ _ c
  letI : MeasurableSpace G := borel G
  letI : BorelSpace G := ⟨rfl⟩
  exact c.borel_le_caratheodory

theorem borel_splitting : Specs.D11.Ch21.CompactContentOuterMeasure.borel_splitting.{u} := by
  intro G _ _ c B hB A
  exact borel_le_caratheodory c B hB A

/-- Restrict to the Borel sigma-algebra, not the larger complete
Carathéodory sigma-algebra. -/
def borelMeasure : Specs.D11.Ch21.CompactContentOuterMeasure.borelMeasure_type.{u} := Specs.D11.Ch21.CompactContentOuterMeasure.borelMeasure_value

theorem borelMeasure_apply : Specs.D11.Ch21.CompactContentOuterMeasure.borelMeasure_apply.{u} := by
  intro G _ _ c B hB
  letI : MeasurableSpace G := borel G
  letI : BorelSpace G := ⟨rfl⟩
  exact c.measure_apply hB

theorem openCost_left_image : Specs.D11.Ch21.CompactContentOuterMeasure.openCost_left_image.{u} := by
  intro G _ _ _ c hc a U
  let V : Opens G :=
    ⟨(fun x => a * x) '' U, (Homeomorph.mulLeft a).isOpenMap _ U.isOpen⟩
  have hpre : Opens.comap (Homeomorph.mulLeft a) V = U := by
    apply SetLike.coe_injective
    exact (Homeomorph.mulLeft a).preimage_image (U : Set G)
  have h := c.is_mul_left_invariant_innerContent (fun a {K} => hc a K) a V
  rw [hpre] at h
  exact h.symm

theorem outerMeasure_left_image : Specs.D11.Ch21.CompactContentOuterMeasure.outerMeasure_left_image.{u} := by
  intro G _ _ _ _ c hc a A
  have h := c.is_mul_left_invariant_outerMeasure (fun a {K} => hc a K) a
    ((fun x => a * x) '' A)
  have hset : (fun x => a * x) ⁻¹' ((fun x => a * x) '' A) = A :=
    (Homeomorph.mulLeft a).preimage_image A
  rw [hset] at h
  exact h.symm

/-- The original content, with the original `K₀`; this makes no new choice. -/
def sourceContent : Specs.D11.Ch21.CompactContentOuterMeasure.sourceContent_type.{u} := Specs.D11.Ch21.CompactContentOuterMeasure.sourceContent_value

theorem sourceContent_laws : Specs.D11.Ch21.CompactContentOuterMeasure.sourceContent_laws.{u} := by
  intro G _ _ _ K₀ h hh
  have hval (K : Compacts G) : Specs.D11.Ch21.CompactContentOuterMeasure.sourceContent_value K₀ h hh K = ENNReal.ofReal (h K) :=
    realContent_apply h _ _ _ _ K
  refine ⟨hval, ?_⟩
  intro a K
  simp only [hval, hh.2.2.2.1 a K]

theorem source_formulas : Specs.D11.Ch21.CompactContentOuterMeasure.source_formulas.{u} := by
  intro G _ _ _ _ K₀ h hh
  have hopen (U : Opens G) : Specs.D11.Ch21.CompactContentOuterMeasure.openCost_value (Specs.D11.Ch21.CompactContentOuterMeasure.sourceContent_value K₀ h hh) U =
      ⨆ (K : Compacts G) (_ : (K : Set G) ⊆ U), ENNReal.ofReal (h K) := by
    unfold Specs.D11.Ch21.CompactContentOuterMeasure.openCost_value
    simp_rw [(sourceContent_laws K₀ h hh).1]
  refine ⟨hopen, ?_⟩
  intro A
  rw [outerMeasure_apply]
  unfold Specs.D11.Ch21.CompactContentOuterMeasure.outerCost_value
  simp_rw [hopen]
  rfl

end D11.Ch21.CompactContentOuterMeasure
