import MathGenome.Internal.Specs.D05.M09.DistinctRoots
import MathGenome.Internal.D05.M08.EigenRoots
import MathGenome.Internal.D05.M09.DistinctIndependence
import MathGenome.Internal.D05.M09.Diagonalizable
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! K05.09.distinct_roots: simple spectrum suffices, but is not necessary. -/

noncomputable section

namespace D05.M09.DistinctRoots

theorem eigenbasis_of_distinct_roots :
    Specs.D05.M09.DistinctRoots.eigenbasis_of_distinct_roots := by
  intro K V _ _ _ _ T μ hμ hroot
  classical
  have heigen : ∀ i, T.HasEigenvalue (μ i) := by
    intro i
    rw [Module.End.hasEigenvalue_iff, Eigenspace.eigenspace_eq_kernel]
    exact (D05.M08.EigenRoots.kernel_iff_charpoly_root T (μ i)).mpr (hroot i)
  choose v hv using fun i => (heigen i).exists_hasEigenvector
  have hind : LinearIndependent K v :=
    DistinctIndependence.eigenvectors_independent T μ hμ v hv
  let b := basisOfLinearIndependentOfCardEqFinrank' v hind (Fintype.card_fin _)
  refine ⟨b, ?_⟩
  intro i
  simpa only [b, coe_basisOfLinearIndependentOfCardEqFinrank'] using hv i

theorem distinct_roots_diagonalizable :
    Specs.D05.M09.DistinctRoots.distinct_roots_diagonalizable := by
  intro K V _ _ _ _ T h
  obtain ⟨μ, hμ, hroot⟩ := h
  obtain ⟨b, hb⟩ := eigenbasis_of_distinct_roots T μ hμ hroot
  exact ⟨Module.finrank K V, b, μ,
    (Diagonalizable.eigenbasis_iff_hasEigenvector b T μ).mpr hb⟩

theorem identity_diagonalizable :
    Specs.D05.M09.DistinctRoots.identity_diagonalizable := by
  intro K V _ _ _ _
  exact ⟨Module.finrank K V, Module.finBasis K V, (fun _ => 1), by simp⟩

theorem identity_counterexample :
    Specs.D05.M09.DistinctRoots.identity_counterexample := by
  intro K V _ _ _ _ hdim
  have hchar : Specs.D05.M08.Charpoly.charpoly_value (LinearMap.id : Module.End K V) =
      (Polynomial.X - Polynomial.C (1 : K)) ^ Module.finrank K V := by
    simpa only [Specs.D05.M08.Charpoly.charpoly_value, Polynomial.C_1,
      Module.End.one_eq_id] using
      (LinearMap.charpoly_one (R := K) (M := V))
  refine ⟨identity_diagonalizable, hchar, ?_, ?_⟩
  · rw [hchar]
    exact pow_dvd_pow _ hdim
  · rintro ⟨μ, hμ, hroot⟩
    have hone : ∀ i, μ i = 1 := by
      intro i
      have hi := hroot i
      rw [hchar] at hi
      simpa only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, pow_eq_zero_iff (by omega : Module.finrank K V ≠ 0),
        sub_eq_zero] using hi
    have h01 : (⟨0, by omega⟩ : Fin (Module.finrank K V)) = ⟨1, by omega⟩ :=
      hμ ((hone _).trans (hone _).symm)
    have hbad : (0 : ℕ) = 1 := congrArg Fin.val h01
    exact Nat.zero_ne_one hbad

end D05.M09.DistinctRoots
