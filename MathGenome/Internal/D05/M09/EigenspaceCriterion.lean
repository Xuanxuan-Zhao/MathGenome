import MathGenome.Internal.Specs.D05.M09.EigenspaceCriterion
import MathGenome.Internal.D05.M09.Diagonalizable
import MathGenome.Internal.D05.M09.DistinctIndependence
import MathGenome.Internal.D05.M06.SumDimension
import MathGenome.Internal.D05.M02.SubspaceDimension

/-! K05.09.eigenspace_criterion: dimension of the direct eigenspace sum and
its equivalence with existence of an eigenbasis over the original field. -/

namespace D05.M09.EigenspaceCriterion

open scoped BigOperators

/-- Independence makes the canonical addition map injective. Its range is
exactly the eigenspace sum, so finite direct-sum dimension applies to it. -/
theorem eigenspace_sum_dimension :
    Specs.D05.M09.EigenspaceCriterion.eigenspace_sum_dimension := by
  intro K V _ _ _ _ T
  classical
  let : Fintype T.Eigenvalues :=
    (D05.M09.DistinctIndependence.eigenvalues_finite_and_card_le T).1.fintype
  let U : T.Eigenvalues → Submodule K V := fun μ => T.eigenspace (μ : K)
  have hind : iSupIndep U :=
    D05.M09.DistinctIndependence.eigenspaces_independent T
      (fun μ : T.Eigenvalues => (μ : K)) Subtype.val_injective
  have hinj : Function.Injective (DirectSum.coeLinearMap U) :=
    hind.dfinsupp_lsum_injective
  calc
    Module.finrank K (⨆ μ, U μ : Submodule K V) =
        Module.finrank K (LinearMap.range (DirectSum.coeLinearMap U)) := by
          rw [DirectSum.range_coeLinearMap]
    _ = Module.finrank K (DirectSum T.Eigenvalues (fun μ => U μ)) :=
      LinearMap.finrank_range_of_inj hinj
    _ = ∑ μ : T.Eigenvalues, Module.finrank K (U μ) :=
      D05.M06.SumDimension.external_dimension
    _ = ∑ᶠ μ : T.Eigenvalues, Module.finrank K (T.eigenspace (μ : K)) :=
      (finsum_eq_sum_of_fintype _).symm

/-- In one direction every eigenbasis vector belongs to the eigenspace sum.
In the other, concatenate bases of the independent eigenspaces and reindex
that finite basis by `Fin n`, as required by the upstream definition. -/
theorem diagonalizable_iff_eigenspaces_span :
    Specs.D05.M09.EigenspaceCriterion.diagonalizable_iff_eigenspaces_span := by
  intro K V _ _ _ _ T
  classical
  let : Fintype T.Eigenvalues :=
    (D05.M09.DistinctIndependence.eigenvalues_finite_and_card_le T).1.fintype
  let U : T.Eigenvalues → Submodule K V := fun μ => T.eigenspace (μ : K)
  constructor
  · rintro ⟨n, b, μ, hb⟩
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    have hv : T.HasEigenvector (μ i) (b i) :=
      Module.End.hasEigenvector_iff.mpr
        ⟨Module.End.mem_eigenspace_iff.mpr (hb i), b.ne_zero i⟩
    let a : T.Eigenvalues := ⟨μ i, Module.End.hasEigenvalue_of_hasEigenvector hv⟩
    exact (le_iSup U a) hv.1
  · intro hspan
    have hind : iSupIndep U :=
      D05.M09.DistinctIndependence.eigenspaces_independent T
        (fun μ : T.Eigenvalues => (μ : K)) Subtype.val_injective
    have hint : DirectSum.IsInternal U :=
      DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hspan
    let b := hint.collectedBasis (fun μ => Module.finBasis K (U μ))
    let e := Fintype.equivFin (Σ μ : T.Eigenvalues, Fin (Module.finrank K (U μ)))
    refine ⟨_, b.reindex e, (fun i => ((e.symm i).1 : K)), ?_⟩
    intro i
    apply Module.End.mem_eigenspace_iff.mp
    rw [Module.Basis.reindex_apply]
    exact hint.collectedBasis_mem _ (e.symm i)

/-- Equality of dimensions forces the eigenspace sum to be the whole space;
conversely an eigenbasis makes that sum the whole space. -/
theorem dimension_criterion :
    Specs.D05.M09.EigenspaceCriterion.dimension_criterion := by
  intro K V _ _ _ _ T
  rw [diagonalizable_iff_eigenspaces_span T, ← eigenspace_sum_dimension T]
  exact ((D05.M02.SubspaceDimension.subspace_dimension
    (⨆ μ : T.Eigenvalues, T.eigenspace (μ : K)) (Module.finrank K V) rfl).2.2.2).symm

end D05.M09.EigenspaceCriterion
