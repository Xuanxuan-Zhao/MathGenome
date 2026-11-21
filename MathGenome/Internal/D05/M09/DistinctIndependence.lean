import MathGenome.Internal.Specs.D05.M09.DistinctIndependence
import MathGenome.Internal.D05.M02.Independence
import MathGenome.Internal.D05.M09.Eigenspace

/-! Independence and the dimension bound of K05.09.distinct_independence. -/

namespace D05.M09.DistinctIndependence

theorem eigenspaces_independent :
    Specs.D05.M09.DistinctIndependence.eigenspaces_independent := by
  intro K V I _ _ _ T μ hμ
  exact T.eigenspaces_iSupIndep.comp hμ

theorem zero_sum_components :
    Specs.D05.M09.DistinctIndependence.zero_sum_components := by
  intro K V I _ _ _ T μ hμ s v hv hsum
  apply (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp
    (eigenspaces_independent T μ hμ) s v _ hsum
  intro i hi
  exact (D05.M09.Eigenspace.mem_eigenspace_iff T (μ i) (v i)).mpr (hv i hi)

theorem unique_components :
    Specs.D05.M09.DistinctIndependence.unique_components := by
  intro K V I _ _ _ T μ hμ
  exact (iSupIndep_iff_finsetSum_eq_imp_eq _).mp (eigenspaces_independent T μ hμ)

theorem eigenvectors_independent :
    Specs.D05.M09.DistinctIndependence.eigenvectors_independent := by
  intro K V I _ _ _ T μ hμ v hv
  exact T.eigenvectors_linearIndependent' μ hμ v hv

theorem eigenvalue_family_card_le :
    Specs.D05.M09.DistinctIndependence.eigenvalue_family_card_le := by
  intro K V I _ _ _ _ _ T μ hμ h
  choose v hv using fun i => (h i).exists_hasEigenvector
  exact (eigenvectors_independent T μ hμ v hv).fintype_card_le_finrank

theorem eigenvalues_finite_and_card_le :
    Specs.D05.M09.DistinctIndependence.eigenvalues_finite_and_card_le := by
  intro K V _ _ _ _ T
  classical
  let S : Set K := {μ : K | T.HasEigenvalue μ}
  choose v hv using fun μ : S => μ.property.exists_hasEigenvector
  have hind : LinearIndependent K v :=
    eigenvectors_independent T (fun μ : S => (μ : K)) Subtype.val_injective v hv
  letI : Finite S := hind.finite
  letI : Fintype S := Fintype.ofFinite S
  refine ⟨Set.toFinite S, ?_⟩
  change S.ncard ≤ Module.finrank K V
  simpa only [Set.ncard_eq_toFinset_card', Set.toFinset_card] using
    hind.fintype_card_le_finrank

end D05.M09.DistinctIndependence
