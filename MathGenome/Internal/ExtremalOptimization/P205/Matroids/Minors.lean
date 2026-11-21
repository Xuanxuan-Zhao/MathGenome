import MathGenome.Internal.ExtremalOptimization.P205.Matroids.Models
import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.Minors

/-! Restriction and contraction for finite canonical matroids (paper.tex, Lemma 9.7). -/
namespace P205.Matroids
open Set
open scoped Matroid
universe u

theorem restriction_ground : Specs.P205.Matroids.RestrictionGround := by
  intro α M _ U _
  exact Matroid.restrict_ground_eq

theorem restriction_finite : Specs.P205.Matroids.RestrictionFinite := by
  intro α M _ U hU
  exact Matroid.restrict_finite (M.ground_finite.subset hU)

theorem restriction_indep : Specs.P205.Matroids.RestrictionIndep := by
  intro α M _ U _ I
  exact Matroid.restrict_indep_iff

theorem restriction_rank : Specs.P205.Matroids.RestrictionRank := by
  intro α M _ U _ S hS
  exact congrArg ENat.toNat (M.restrict_eRk_eq hS)

theorem contraction_ground : Specs.P205.Matroids.ContractionGround := by
  intro α M _ C _
  exact M.contract_ground C

theorem contraction_finite : Specs.P205.Matroids.ContractionFinite := by
  intro α M _ C _
  infer_instance

theorem contraction_indep : Specs.P205.Matroids.ContractionIndep := by
  intro α M _ C _ I hI J hJ
  have hd : Disjoint C J := disjoint_left.mpr (fun e heC heJ => (hJ heJ).2 heC)
  simpa only [union_comm] using hI.contract_indep_iff_of_disjoint hd

/-- Extend a basis of `C` to a basis of `S ∪ C`. Its elements outside `C`
form a basis after contraction. The finite cardinality difference gives the
rank formula even when the contracted set is dependent. -/
theorem contraction_rank : Specs.P205.Matroids.ContractionRank := by
  intro α M _ C hC S hS
  obtain ⟨I, hI⟩ := M.exists_isBasis C hC
  obtain ⟨B, hB, hBC⟩ := hI.exists_isBasis_inter_eq_of_superset
    (subset_union_right : C ⊆ S ∪ C) (union_subset (hS.trans sdiff_subset) hC)
  have hIB : I ⊆ B := by
    rw [← hBC]
    exact inter_subset_left
  have hInd : M.Indep (B \ C ∪ I) :=
    hB.indep.subset (union_subset sdiff_subset hIB)
  have hBasis := hB.contract_isBasis hI hInd
  have hSC : (S ∪ C) \ C = S := by
    ext e
    constructor
    · rintro ⟨heS | heC, hnC⟩
      · exact heS
      · exact False.elim (hnC heC)
    · intro heS
      exact ⟨Or.inl heS, (hS heS).2⟩
  rw [hSC] at hBasis
  rw [← (basis_rank (M ／ C) (B \ C) S hS).mp hBasis |>.2.2,
    ← (basis_rank M B (S ∪ C) (union_subset (hS.trans sdiff_subset) hC)).mp hB |>.2.2,
    ← (basis_rank M I C hC).mp hI |>.2.2]
  rw [ncard_sdiff'' (hB.indep.finite.subset inter_subset_left), hBC]

end P205.Matroids
