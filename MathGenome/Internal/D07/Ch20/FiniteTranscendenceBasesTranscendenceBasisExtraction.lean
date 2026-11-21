import MathGenome.Internal.Specs.D07.Ch20.FiniteTranscendenceBasesTranscendenceBasisExtraction
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

/-!
The field-generating tuple spans the algebraic-independence matroid. Choose a
basis in its range and select one original index for each basis element.
Algebraicity follows from maximality. Finite field generation passes to the
larger base field, and an algebraic finitely generated field extension is finite.
-/

universe u v

namespace D07.Ch20.FiniteTranscendenceBasesTranscendenceBasisExtraction

open Specs.D07.Ch20.FiniteTranscendenceBasesTranscendenceBasisExtraction

/-- The extraction keeps the specified generating tuple, and proves finite degree,
not merely algebraicity over the selected independent elements. -/
theorem transcendence_basis_extraction : TranscendenceBasisExtraction.{u, v} := by
  classical
  intro K L _ _ _ m b hgen
  have hfield : Algebra.IsAlgebraic (IntermediateField.adjoin K (Set.range b)) L := by
    rw [hgen]
    infer_instance
  let : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range b)) L :=
    IntermediateField.isAlgebraic_adjoin_iff_top.mp hfield
  obtain ⟨t, ht, hbase⟩ := exists_isTranscendenceBasis_subset (R := K) (Set.range b)
  have htfin : t.Finite := (Set.finite_range b).subset ht
  let : Fintype t := htfin.fintype
  have hpre : ∀ x : t, ∃ i : Fin m, b i = (x : L) := fun x => ht x.property
  choose f hf using hpre
  have hf_inj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact (hf x).symm.trans ((congrArg b h).trans (hf y))
  let e : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  let j : Fin (Fintype.card t) ↪ Fin m := ⟨f ∘ e, hf_inj.comp e.injective⟩
  have hj : (fun i => b (j i)) = (fun i => ((e i : t) : L)) := by
    funext i
    exact hf (e i)
  have hbasis : IsTranscendenceBasis K (fun i => b (j i)) := by
    rw [hj]
    exact hbase.comp_equiv e
  let A := IntermediateField.adjoin K (Set.range fun i => b (j i))
  let : Algebra.IsAlgebraic A L := hbasis.isAlgebraic_field
  have hfg : (⊤ : IntermediateField K L).FG := by
    refine ⟨Finset.univ.image b, ?_⟩
    simpa using hgen
  let : Algebra.EssFiniteType K L := IntermediateField.fg_top_iff.mp hfg
  let : Algebra.EssFiniteType A L := Algebra.EssFiniteType.of_comp K A L
  exact ⟨Fintype.card t, j, hbasis, inferInstance,
    Algebra.finite_of_essFiniteType_of_isAlgebraic⟩

end D07.Ch20.FiniteTranscendenceBasesTranscendenceBasisExtraction
