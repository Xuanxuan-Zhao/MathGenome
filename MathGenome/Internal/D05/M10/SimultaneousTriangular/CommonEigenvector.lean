import MathGenome.Internal.Specs.D05.M10.SimultaneousTriangular.CommonEigenvector
import MathGenome.Internal.D05.M10.Triangularization
import MathGenome.Internal.D05.M09.CommutantInvariance
import MathGenome.Internal.D05.M08.RestrictionMinpoly

/-! Successively choose a nonzero eigenspace. Commutation preserves it, and
minimal-polynomial divisibility preserves splitting. Induction on a finite
set of indices then produces the common vector, including for the empty set. -/
noncomputable section
namespace D05.M10.SimultaneousTriangular.CommonEigenvector

open Specs.D05.M06.Invariant (invariant_value)

theorem restriction_splits :
    Specs.D05.M10.SimultaneousTriangular.CommonEigenvector.restriction_splits := by
  intro K V _ _ _ _ U T hU hs
  exact hs.of_dvd (D05.M08.Minpoly.ne_zero T)
    (D05.M08.RestrictionMinpoly.restriction_minpoly_dvd U T hU)

theorem eigenspace_step :
    Specs.D05.M10.SimultaneousTriangular.CommonEigenvector.eigenspace_step := by
  intro K V ι _ _ _ _ _ T hc hs i
  have hdeg : (minpoly K (T i)).degree ≠ 0 :=
    Polynomial.degree_ne_of_natDegree_ne (Nat.ne_of_gt
      (D05.M08.Minpoly.positive_degree (T i) (Module.finrank_pos (R := K))))
  obtain ⟨μ, hμ⟩ := (hs i).exists_eval_eq_zero hdeg
  have hE0 : (T i).eigenspace μ ≠ ⊥ := by
    rw [D05.M09.Eigenspace.eigenspace_eq_kernel]
    exact (D05.M08.EigenRoots.kernel_iff_minpoly_root (T i) μ).mpr hμ
  have hE (j : ι) : invariant_value K V ((T i).eigenspace μ) (T j) := by
    apply D05.M09.CommutantInvariance.eigenspace_invariant (T j) (T i)
    by_cases hji : j = i
    · subst j; rfl
    · exact hc hji
  exact ⟨μ, hE, hE0, fun j k hjk => LinearMap.restrict_commute (hc hjk) _ _,
    fun j => restriction_splits _ (T j) (hE j) (hs j)⟩

/-- Induction is generalized over the ambient space: after the first choice,
apply it to the whole commuting family restricted to the chosen eigenspace. -/
private theorem common_on_finset {K ι : Type*} [Field K] (s : Finset ι) :
    ∀ {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      [Nontrivial V] (T : ι → Module.End K V),
      (Pairwise fun i j => Commute (T i) (T j)) →
      (∀ i, (minpoly K (T i)).Splits) →
      ∃ v : V, v ≠ 0 ∧ ∀ i ∈ s, ∃ μ : K, T i v = μ • v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro V _ _ _ _ T hc hs
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact ⟨v, hv, by simp⟩
  | @insert a s ha ih =>
    intro V _ _ _ _ T hc hs
    obtain ⟨μ, hE, hE0, hcE, hsE⟩ := eigenspace_step T hc hs a
    let E := (T a).eigenspace μ
    haveI : Nontrivial E := (Submodule.nontrivial_iff_ne_bot (p := E)).mpr hE0
    obtain ⟨v, hv0, hv⟩ := ih (fun i => (T i).restrict (hE i)) hcE hsE
    refine ⟨(v : V), ?_, ?_⟩
    · intro hz
      exact hv0 (Subtype.ext hz)
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ⟨μ, Module.End.mem_eigenspace_iff.mp v.property⟩
      · obtain ⟨ν, hν⟩ := hv i hi
        exact ⟨ν, congrArg Subtype.val hν⟩

theorem common_eigenvector_of_splits :
    Specs.D05.M10.SimultaneousTriangular.CommonEigenvector.common_eigenvector_of_splits := by
  intro K V ι _ _ _ _ _ _ T hc hs
  classical
  letI := Fintype.ofFinite ι
  obtain ⟨v, hv0, hv⟩ := common_on_finset (K := K) Finset.univ T hc hs
  choose μ hμ using fun i => hv i (Finset.mem_univ i)
  exact ⟨v, μ, hv0, hμ⟩

theorem common_eigenvector :
    Specs.D05.M10.SimultaneousTriangular.CommonEigenvector.common_eigenvector := by
  intro K V ι _ _ _ _ _ _ T hc ht
  apply common_eigenvector_of_splits T hc
  intro i
  exact (D05.M10.Triangularization.triangularization (T i)).2.mp (ht i)

theorem common_eigenvector_in_subspace :
    Specs.D05.M10.SimultaneousTriangular.CommonEigenvector.common_eigenvector_in_subspace := by
  intro K V ι _ _ _ _ _ T hc ht U hU0 hU
  haveI : Nontrivial U := (Submodule.nontrivial_iff_ne_bot (p := U)).mpr hU0
  have hs (i : ι) : (minpoly K ((T i).restrict (hU i))).Splits :=
    restriction_splits U (T i) (hU i)
      ((D05.M10.Triangularization.triangularization (T i)).2.mp (ht i))
  obtain ⟨v, μ, hv0, hv⟩ := common_eigenvector_of_splits
    (fun i => (T i).restrict (hU i))
    (fun i j hij => LinearMap.restrict_commute (hc hij) _ _) hs
  exact ⟨(v : V), μ, v.property, fun hz => hv0 (Subtype.ext hz),
    fun i => congrArg Subtype.val (hv i)⟩

end D05.M10.SimultaneousTriangular.CommonEigenvector
