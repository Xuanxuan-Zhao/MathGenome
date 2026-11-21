import MathGenome.Internal.Specs.D05.M14.SvdPseudoinverse
import MathGenome.Internal.D05.M13.Adjoint
import MathGenome.Internal.D05.M14.Pseudoinverse
import MathGenome.Internal.D05.M14.Svd

noncomputable section

namespace D05.M14.SvdPseudoinverse

open scoped BigOperators

universe u v w
variable {F : Type u} {V : Type v} {W : Type w} [RCLike F]
  [NormedAddCommGroup V] [NormedAddCommGroup W]
  [InnerProductSpace F V] [InnerProductSpace F W]
  [FiniteDimensional F V] [FiniteDimensional F W]

omit [FiniteDimensional F V] in
/-- Fourier expansion with the vanishing tail removed, including the empty block. -/
private theorem positive_block_expansion {n r : ℕ}
    (b : OrthonormalBasis (Fin n) F V) (hr : r ≤ n) (v : V)
    (hz : ∀ j : Fin n, r ≤ j.val → inner F (b j) v = 0) :
    v = ∑ i : Fin r, inner F (b (Fin.castLE hr i)) v • b (Fin.castLE hr i) := by
  classical
  nth_rw 1 [← b.sum_repr' v]
  symm
  apply Finset.sum_of_injOn (fun i => Fin.castLE hr i)
  · intro i hi j hj hij
    exact Fin.ext (congrArg (fun x : Fin n => x.val) hij)
  · intro i hi
    simp
  · intro j hj hnot
    have hjr : r ≤ j.val := by
      by_contra hn
      exact hnot ⟨⟨j.val, Nat.lt_of_not_ge hn⟩, Finset.mem_univ _, rfl⟩
    rw [hz j hjr, zero_smul]
  · intro i hi
    rfl

theorem adjoint_formula : Specs.D05.M14.SvdPseudoinverse.adjoint_formula := by
  intro F V W _ _ _ _ _ _ _ T d w
  classical
  rw [positive_block_expansion d.domainBasis T.finrank_range_le (LinearMap.adjoint T w)
    (by intro j hj; rw [LinearMap.adjoint_inner_right, d.zero_action j hj, inner_zero_left])]
  apply Finset.sum_congr rfl
  intro i hi
  rw [LinearMap.adjoint_inner_right, d.positive_action, inner_smul_left,
    RCLike.conj_ofReal]
  rfl

/-- Adjoint action on each vector of the positive codomain block. -/
theorem adjoint_positive_action (T : V →ₗ[F] W)
    (d : D05.SingularValueDecomposition T)
    (i : Fin (Module.finrank F (LinearMap.range T))) :
    LinearMap.adjoint T (d.codomainBasis (Fin.castLE (Submodule.finrank_le _) i)) =
      (T.singularValues i : F) • d.domainBasis (Fin.castLE T.finrank_range_le i) := by
  classical
  rw [adjoint_formula T d]
  simp [D05.firstInner, orthonormal_iff_ite.mp d.codomainBasis.orthonormal]

/-- Every positive left singular vector lies in the image of T. -/
theorem codomain_mem_range (T : V →ₗ[F] W)
    (d : D05.SingularValueDecomposition T)
    (i : Fin (Module.finrank F (LinearMap.range T))) :
    d.codomainBasis (Fin.castLE (Submodule.finrank_le _) i) ∈ T.range := by
  have hs : (T.singularValues i : F) ≠ 0 := by
    exact_mod_cast (ne_of_gt ((Svd.diagonal_signs T).2.1 i))
  refine ⟨(T.singularValues i : F)⁻¹ •
    d.domainBasis (Fin.castLE T.finrank_range_le i), ?_⟩
  rw [map_smul, d.positive_action, smul_smul, inv_mul_cancel₀ hs, one_smul]

theorem pseudoinverse_formula : Specs.D05.M14.SvdPseudoinverse.pseudoinverse_formula := by
  intro F V W _ _ _ _ _ _ _ T d w
  classical
  have hz : ∀ j : Fin (Module.finrank F V),
      Module.finrank F T.range ≤ j.val →
      inner F (d.domainBasis j) (D05.pseudoinverse T w) = 0 := by
    intro j hj
    exact T.ker.inner_right_of_mem_orthogonal (d.zero_action j hj)
      (Pseudoinverse.mem_kernel_orthogonal T w)
  rw [positive_block_expansion d.domainBasis T.finrank_range_le
    (D05.pseudoinverse T w) hz]
  apply Finset.sum_congr rfl
  intro i hi
  have hs : (T.singularValues i : F) ≠ 0 := by
    exact_mod_cast (ne_of_gt ((Svd.diagonal_signs T).2.1 i))
  have hproj := ((D05.M12.Projection.component_characterization T.range w _).mp rfl).2
  have hinner := T.range.inner_right_of_mem_orthogonal (codomain_mem_range T d i) hproj
  rw [inner_sub_right, sub_eq_zero] at hinner
  have h := LinearMap.adjoint_inner_left T (D05.pseudoinverse T w)
    (d.codomainBasis (Fin.castLE (Submodule.finrank_le _) i))
  rw [adjoint_positive_action T d, inner_smul_left, RCLike.conj_ofReal,
    Pseudoinverse.map_pseudoinverse T w, ← hinner] at h
  congr 1
  change inner F _ _ = (T.singularValues i : F)⁻¹ * inner F _ _
  rw [← h, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]

end D05.M14.SvdPseudoinverse
