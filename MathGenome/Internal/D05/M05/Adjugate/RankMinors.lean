import MathGenome.Internal.Specs.D05.M05.Adjugate.RankMinors
import MathGenome.Internal.D05.M04.RankBridge
import MathGenome.Internal.D05.M02.BasisExtension
import MathGenome.Internal.D05.M05.DetRowRules
import MathGenome.Internal.D05.M05.DetInvertible

/-! The rank–minor lemma (paper.tex:839–846). Finite basis extraction selects
columns and then rows. All arguments include empty matrices and rank zero. -/

namespace D05.M05.Adjugate.RankMinors

open Submodule Set

/-- A finite indexed family contains an independent spanning subfamily, indexed
by its span dimension. Selection is of positions, so repeated values cause no
identification of occurrences. This uses the upstream finite extraction proof. -/
theorem exists_independent_spanning_subfamily
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (v : Fin n → V) :
    ∃ e : Fin (Module.finrank K (span K (range v))) ↪ Fin n,
      LinearIndependent K (v ∘ e) ∧
      span K (range (v ∘ e)) = span K (range v) := by
  classical
  obtain ⟨s, _, hs, hspan⟩ :=
    D05.M02.BasisExtension.extend_by_finite_indices v ∅ Finset.univ
      (linearIndepOn_empty K v)
  simp only [empty_union, Finset.coe_univ, image_univ] at hs hspan
  have hrange : range (fun j : s => v j) = v '' (s : Set (Fin n)) := by
    ext x
    simp
  have hsp : span K (range (fun j : s => v j)) = span K (range v) := by
    rw [hrange]
    exact le_antisymm (span_mono (image_subset_range _ _)) (span_le.mpr hspan)
  have hcard : Fintype.card s = Module.finrank K (span K (range v)) := by
    have hc := (linearIndependent_iff_card_eq_finrank_span
      (R := K) (b := fun j : s => v j)).mp hs
    change Fintype.card s = Module.finrank K
      (span K (range (fun j : s => v j))) at hc
    rwa [hsp] at hc
  let e : Fin (Module.finrank K (span K (range v))) ≃ s :=
    (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨⟨fun i => (e i).val, Subtype.val_injective.comp e.injective⟩,
    hs.comp e e.injective, ?_⟩
  have he : range (fun i => v (e i)) = range (fun j : s => v j) :=
    e.surjective.range_comp (fun j : s => v j)
  simpa only [Function.comp_def, Function.Embedding.coeFn_mk, he] using hsp

theorem minor_size_le_rank :
    Specs.D05.M05.Adjugate.RankMinors.minor_size_le_rank := by
  intro K _ m n k A rows cols hdet
  rw [DetDefinition.matrix_det_bridge] at hdet
  have hfull := Matrix.rank_of_det_ne_zero hdet
  have hle := Matrix.rank_submatrix_le A rows cols
  simpa only [hfull, Fintype.card_fin] using hle

theorem exists_rank_minor :
    Specs.D05.M05.Adjugate.RankMinors.exists_rank_minor := by
  intro K _ m n A
  classical
  have hsel := exists_independent_spanning_subfamily (K := K) A.col
  rw [← D05.M04.RankBridge.rank_eq_column_rank A] at hsel
  obtain ⟨cols, _, hcols⟩ := hsel
  let C : Matrix (Fin m) (Fin A.rank) K := A.submatrix id cols
  have hC : C.rank = A.rank := by
    rw [D05.M04.RankBridge.rank_eq_column_rank]
    change Module.finrank K (span K (range (A.col ∘ cols))) = A.rank
    rw [hcols, ← D05.M04.RankBridge.rank_eq_column_rank A]
  have hrowdim : Module.finrank K (span K (range C.row)) = A.rank :=
    (Matrix.rank_eq_finrank_span_row C).symm.trans hC
  have hrows := exists_independent_spanning_subfamily (K := K) C.row
  rw [hrowdim] at hrows
  obtain ⟨rows, hrows, _⟩ := hrows
  refine ⟨rows, cols, ?_⟩
  have hB : LinearIndependent K (A.submatrix rows cols).row := hrows
  have hu := Matrix.linearIndependent_row_iff_isUnit.mp hB
  rw [DetDefinition.matrix_det_bridge]
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)

theorem rank_isGreatest_minor_sizes :
    Specs.D05.M05.Adjugate.RankMinors.rank_isGreatest_minor_sizes := by
  intro K _ m n A
  refine ⟨exists_rank_minor A, ?_⟩
  rintro k ⟨rows, cols, hdet⟩
  exact minor_size_le_rank A rows cols hdet

theorem larger_minors_vanish :
    Specs.D05.M05.Adjugate.RankMinors.larger_minors_vanish := by
  intro K _ m n k A hk rows cols
  by_contra hdet
  exact (Nat.not_le_of_lt hk) (minor_size_le_rank A rows cols hdet)

theorem empty_minor : Specs.D05.M05.Adjugate.RankMinors.empty_minor := by
  intro R _ m n A
  exact DetDefinition.empty_determinant _

end D05.M05.Adjugate.RankMinors
