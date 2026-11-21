import MathGenome.Internal.Specs.D05.M14.SingularValues
import MathGenome.Internal.D05.M14.PositiveSpectrum
import MathGenome.Internal.D05.M13.AdjointKernel
import MathGenome.Internal.D05.M08.Charpoly

noncomputable section

namespace D05.M14.SingularValues

open Module

/-- The finite source definition, with zeros retained. -/
def fullList : Specs.D05.M14.SingularValues.fullList_type :=
  Specs.D05.M14.SingularValues.fullList_value

/-- The source's positive-only list. -/
def positiveList : Specs.D05.M14.SingularValues.positiveList_type :=
  Specs.D05.M14.SingularValues.positiveList_value

theorem gram_positive : Specs.D05.M14.SingularValues.gram_positive := by
  intro F V W _ _ _ _ _ _ _ T
  exact D05.M14.PositiveSpectrum.adjoint_comp_positive T

theorem full_length : Specs.D05.M14.SingularValues.full_length := by
  intro F V W _ _ _ _ _ _ _ T
  exact List.length_ofFn

theorem library_prefix : Specs.D05.M14.SingularValues.library_prefix := by
  intro F V W _ _ _ _ _ _ _ T
  unfold D05.singularValues
  congr 1
  funext i
  exact (T.singularValues_fin rfl i).symm

theorem full_get : Specs.D05.M14.SingularValues.full_get := by
  intro F V W _ _ _ _ _ _ _ T i hi
  simp only [library_prefix T, List.getElem_ofFn]

theorem nonnegative : Specs.D05.M14.SingularValues.nonnegative := by
  intro F V W _ _ _ _ _ _ _ T
  rw [library_prefix]
  exact List.forall_mem_ofFn_iff.mpr fun i => T.singularValues_nonneg i

theorem nonincreasing : Specs.D05.M14.SingularValues.nonincreasing := by
  intro F V W _ _ _ _ _ _ _ T
  rw [library_prefix, List.pairwise_ofFn]
  intro i j hij
  exact T.singularValues_antitone (Nat.le_of_lt hij)

theorem squared_eigenvalues : Specs.D05.M14.SingularValues.squared_eigenvalues := by
  intro F V W _ _ _ _ _ _ _ T
  rw [library_prefix, List.map_ofFn]
  congr 1
  funext i
  exact T.sq_singularValues_fin rfl i

theorem charpoly_roots : Specs.D05.M14.SingularValues.charpoly_roots := by
  intro F V W _ _ _ _ _ _ _ T
  rw [T.isSymmetric_adjoint_comp_self.roots_charpoly_eq_eigenvalues rfl]
  have h := congrArg (fun l : List ℝ => ((l.map fun x : ℝ => (x : F)) : Multiset F))
    (squared_eigenvalues T)
  simpa [List.map_map, List.map_ofFn, Function.comp_def, Fin.univ_val_map] using h.symm

theorem charpoly_characterization :
    Specs.D05.M14.SingularValues.charpoly_characterization := by
  intro F V W _ _ _ _ _ _ _ T
  rw [T.isSymmetric_adjoint_comp_self.sort_roots_charpoly_eq_eigenvalues rfl]
  simp only [D05.singularValues, List.map_ofFn]
  rfl

/-- An arbitrary orthonormal eigenbasis gives the same characteristic roots,
with one occurrence for each basis index. No ordering or distinctness is assumed. -/
theorem eigenbasis_multiplicities :
    Specs.D05.M14.SingularValues.eigenbasis_multiplicities := by
  intro F V W _ _ _ _ _ _ _ T n b a ha
  classical
  let G := (LinearMap.adjoint T).comp T
  have hm : G.toMatrix b.toBasis b.toBasis = Matrix.diagonal (fun i => (a i : F)) := by
    ext i j
    by_cases hij : i = j <;>
      simp [LinearMap.toMatrix_apply, G, ha, hij, RCLike.real_smul_eq_coe_mul]
  have hb : G.charpoly.roots = (List.ofFn fun i => (a i : F) : Multiset F) := by
    rw [← LinearMap.charpoly_toMatrix G b.toBasis, hm, Matrix.charpoly_diagonal,
      Polynomial.roots_prod _ _ (by simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])]
    simp
  apply Multiset.map_injective (RCLike.ofReal_injective (K := F))
  have he := hb.symm.trans (charpoly_roots T)
  simpa [Multiset.map_coe, List.map_ofFn, List.map_map, Function.comp_def] using he

theorem eigenbasis_sqrt_multiplicities :
    Specs.D05.M14.SingularValues.eigenbasis_sqrt_multiplicities := by
  intro F V W _ _ _ _ _ _ _ T n b a ha
  have h := congrArg (Multiset.map Real.sqrt) (eigenbasis_multiplicities T b a ha)
  have hs : ((D05.singularValues T).map (fun s => s ^ 2)).map Real.sqrt =
      D05.singularValues T := by
    simp only [List.map_map]
    trans (D05.singularValues T).map id
    · exact List.map_congr_left fun x hx => Real.sqrt_sq (nonnegative T x hx)
    · simp
  simpa only [Multiset.map_coe, hs] using h

theorem kernel_gram : Specs.D05.M14.SingularValues.kernel_gram := by
  intro F V W _ _ _ _ _ _ _ T
  exact D05.M13.AdjointKernel.ker_adjoint_comp_self T

theorem positive_length : Specs.D05.M14.SingularValues.positive_length := by
  intro F V W _ _ _ _ _ _ _ T
  exact List.length_ofFn

theorem positive_library_prefix :
    Specs.D05.M14.SingularValues.positive_library_prefix := by
  intro F V W _ _ _ _ _ _ _ T
  rfl

theorem positive_entries : Specs.D05.M14.SingularValues.positive_entries := by
  intro F V W _ _ _ _ _ _ _ T
  unfold D05.positiveSingularValues
  exact List.forall_mem_ofFn_iff.mpr fun i =>
    T.singularValues_pos_iff_lt_finrank_range.mpr i.isLt

theorem positive_iff : Specs.D05.M14.SingularValues.positive_iff := by
  intro F V W _ _ _ _ _ _ _ T i
  exact T.singularValues_pos_iff_lt_finrank_range

theorem zero_iff : Specs.D05.M14.SingularValues.zero_iff := by
  intro F V W _ _ _ _ _ _ _ T i
  exact T.singularValues_eq_zero_iff_le_finrank_range

theorem full_decomposition : Specs.D05.M14.SingularValues.full_decomposition := by
  intro F V W _ _ _ _ _ _ _ T
  apply List.ext_getElem
  · simp only [full_length T, List.length_append, positive_length T, List.length_replicate]
    exact T.finrank_range_add_finrank_ker.symm
  · intro i hi hj
    rw [full_get]
    by_cases hir : i < finrank F (LinearMap.range T)
    · rw [List.getElem_append_left (by simpa [positive_length T] using hir)]
      simp [D05.positiveSingularValues]
    · rw [List.getElem_append_right (by simpa [positive_length T] using Nat.le_of_not_lt hir)]
      simp only [List.getElem_replicate]
      exact (zero_iff T i).mpr (Nat.le_of_not_lt hir)

theorem positive_filter : Specs.D05.M14.SingularValues.positive_filter := by
  intro F V W _ _ _ _ _ _ _ T
  rw [full_decomposition, List.filter_append]
  have h : (D05.positiveSingularValues T).filter (fun s => decide (0 < s)) =
      D05.positiveSingularValues T := by
    apply List.filter_eq_self.mpr
    intro x hx
    simpa using positive_entries T x hx
  simp [h]

theorem positive_nonincreasing : Specs.D05.M14.SingularValues.positive_nonincreasing := by
  intro F V W _ _ _ _ _ _ _ T
  rw [D05.positiveSingularValues, List.pairwise_ofFn]
  intro i j hij
  exact T.singularValues_antitone (Nat.le_of_lt hij)

theorem zero_multiplicity : Specs.D05.M14.SingularValues.zero_multiplicity := by
  intro F V W _ _ _ _ _ _ _ T
  classical
  have hz : (0 : ℝ) ∉ D05.positiveSingularValues T := by
    intro h
    exact lt_irrefl 0 (positive_entries T 0 h)
  rw [full_decomposition, List.count_append, List.count_eq_zero.mpr hz]
  simp

theorem zero_eigenvalue_multiplicity :
    Specs.D05.M14.SingularValues.zero_eigenvalue_multiplicity := by
  intro F V W _ _ _ _ _ _ _ T
  classical
  rw [T.isSymmetric_adjoint_comp_self.roots_charpoly_eq_eigenvalues rfl,
    Multiset.count_map]
  have h := T.isSymmetric_adjoint_comp_self.card_filter_eigenvalues_eq rfl (0 : F)
  rw [Module.End.eigenspace_zero, kernel_gram] at h
  simpa [← Finset.filter_val, eq_comm] using h

theorem rank_nullity : Specs.D05.M14.SingularValues.rank_nullity := by
  intro F V W _ _ _ _ _ _ _ T
  rw [positive_length, ← T.finrank_range_add_finrank_ker, Nat.add_sub_cancel]

theorem rank_bound : Specs.D05.M14.SingularValues.rank_bound := by
  intro F V W _ _ _ _ _ _ _ T
  rw [positive_length]
  exact le_min T.finrank_range_le (Submodule.finrank_le _)

theorem empty_domain : Specs.D05.M14.SingularValues.empty_domain := by
  intro F V W _ _ _ _ _ _ _ T hn
  have h : D05.singularValues T = [] := List.eq_nil_of_length_eq_zero ((full_length T).trans hn)
  refine ⟨h, ?_⟩
  rw [← positive_filter, h]
  rfl

theorem zero_map : Specs.D05.M14.SingularValues.zero_map := by
  intro F V W _ _ _ _ _ _ _
  constructor
  · rw [library_prefix]
    simp
  · simp [D05.positiveSingularValues]

end D05.M14.SingularValues
