import MathGenome.Internal.Specs.D05.M13.SimultaneousSpectral.JointProjections
import MathGenome.Internal.D05.M13.SimultaneousSpectral
import MathGenome.Internal.D05.M13.AlgebraicProjections
import MathGenome.Internal.D05.M12.Projection

noncomputable section
namespace D05.M13.SimultaneousSpectral.JointProjections
open scoped BigOperators
open Module.End

theorem basis_grouping : Specs.D05.M13.SimultaneousSpectral.JointProjections.basis_grouping := by
  intro F V ι κ _ _ _ _ T b μ hb χ
  classical
  have hcoord (i : ι) (v : V) (k : κ) :
      b.repr (T i v) k = μ i k * b.repr v k := by
    have hmap : (b.coord k).comp (T i) = (μ i k) • b.coord k := by
      apply b.ext
      intro l
      by_cases h : l = k
      · subst l
        simp [hb, Module.Basis.coord_apply]
      · simp [hb, Module.Basis.coord_apply, Ne.symm h]
    exact congrArg (fun f : V →ₗ[F] F => f v) hmap
  apply le_antisymm
  · intro v hv
    apply b.mem_span_image.mpr
    intro k hk
    have hk0 : b.repr v k ≠ 0 := Finsupp.mem_support_iff.mp hk
    funext i
    have hi := congrArg (fun w => b.repr w k)
      (mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hv i))
    rw [hcoord] at hi
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hi
    exact mul_right_cancel₀ hk0 hi
  · apply Submodule.span_le.mpr
    rintro v ⟨k, hk, rfl⟩
    apply (Submodule.mem_iInf _).mpr
    intro i
    exact mem_eigenspace_iff.mpr ((hb i k).trans (by rw [congrFun hk i]))

section InnerProduct
variable {F V ι : Type*} [RCLike F] [NormedAddCommGroup V]
  [InnerProductSpace F V] [FiniteDimensional F V]

/-- Orthogonality is intrinsic and needs no chosen eigenbasis. -/
theorem joint_orthogonal (T : ι → Module.End F V)
    (hn : ∀ i, D05.normalOperator (T i)) {χ ψ : ι → F} (hne : χ ≠ ψ) :
    D05.jointEigenspace T χ ≤ (D05.jointEigenspace T ψ).orthogonal := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  exact le_trans (iInf_le _ i)
    ((D05.M13.NormalBasic.eigenspaces_orthogonal (T i) (hn i) _ _ hi).trans
      (Submodule.orthogonal_le (iInf_le _ i)))

omit [FiniteDimensional F V] in
/-- A polynomial list acts diagonally on any joint eigenspace, independently
of its ordering. This is used before asserting that the product is a projection. -/
theorem polynomial_list_action (T : ι → Module.End F V)
    (L : List (ι × Polynomial F)) (ψ : ι → F) (v : V)
    (hv : v ∈ D05.jointEigenspace T ψ) :
    (L.map (fun z => Polynomial.aeval (T z.1) z.2)).prod v =
      (L.map (fun z => z.2.eval (ψ z.1))).prod • v := by
  induction L with
  | nil => simp
  | cons z L ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [ih, map_smul,
      Module.End.aeval_apply_of_mem_apply_eq_smul
        (mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hv z.1)), smul_smul]
    congr 1
    exact mul_comm _ _

/-- Lagrange interpolation evaluated at any eigenvalue, expressed without
requiring the caller to choose that eigenvalue's enumeration index. -/
theorem interpolation_eval {r : ℕ} (a : Fin r → F) (ha : Function.Injective a)
    (j : Fin r) (ν : F) (hν : ∃ k, a k = ν) :
    (Specs.D05.M08.Interpolation.lagrangePolynomial_value F r a j).eval ν =
      if a j = ν then 1 else 0 := by
  obtain ⟨k, rfl⟩ := hν
  rw [D05.M08.Interpolation.basis_evaluation F r a ha j k]
  simp only [ha.eq_iff]

/-- All orthogonal projections onto the intrinsic joint spaces can be
assembled from any common orthonormal eigenbasis of a normal family. -/
theorem resolution_of_common_basis (T : ι → Module.End F V)
    (hn : ∀ i, D05.normalOperator (T i))
    (b : Module.Basis (Fin (Module.finrank F V)) F V)
    (_hb : D05.orthonormalFamily (F := F) b)
    (μ : ι → Fin (Module.finrank F V) → F)
    (hμ : ∀ i k, T i (b k) = μ i k • b k) :
    D05.JointProjectionResolution T := by
  classical
  let eigfn (k : Fin (Module.finrank F V)) : ι → F := fun i => μ i k
  let s : Finset (ι → F) := Finset.univ.image eigfn
  have hbk (k) : b k ∈ D05.jointEigenspace T (eigfn k) :=
    (Submodule.mem_iInf _).mpr fun i => mem_eigenspace_iff.mpr (hμ i k)
  have hs (χ) : χ ∈ s ↔ D05.jointEigenspace T χ ≠ ⊥ := by
    constructor
    · intro hx
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
      exact (Submodule.ne_bot_iff _).mpr ⟨b k, hbk k, b.ne_zero k⟩
    · intro hx
      by_contra hh
      have he : {k | eigfn k = χ} = (∅ : Set (Fin (Module.finrank F V))) := by
        ext k
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hk
        exact hh (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩)
      apply hx
      rw [basis_grouping T b μ hμ χ]
      change Submodule.span F (b '' {k | eigfn k = χ}) = ⊥
      rw [he, Set.image_empty, Submodule.span_empty]
  have ho (χ ψ : ι → F) (hne : χ ≠ ψ) := joint_orthogonal T hn hne
  have hspan : (⨆ χ : {χ // χ ∈ s}, D05.jointEigenspace T χ.val) = ⊤ := by
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact Submodule.mem_iSup_of_mem
      (⟨eigfn k, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩ : {χ // χ ∈ s})
      (hbk k)
  have hort : OrthogonalFamily F
      (fun χ : {χ // χ ∈ s} => D05.jointEigenspace T χ.val)
      (fun χ => (D05.jointEigenspace T χ.val).subtypeₗᵢ) := by
    apply OrthogonalFamily.of_pairwise
    intro χ ψ hne
    exact ho χ.val ψ.val (fun h => hne (Subtype.ext h))
  have hinter : DirectSum.IsInternal
      (fun χ : {χ // χ ∈ s} => D05.jointEigenspace T χ.val) := by
    apply hort.isInternal_iff.mpr
    rw [hspan, Submodule.top_orthogonal_eq_bot]
  -- Enumerate each member's distinct full spectrum, using the finite
  -- dimensional eigenvalue theorem, not a presumed spectral certificate.
  let r (i : ι) := Fintype.card (T i).Eigenvalues
  let a (i : ι) (k : Fin (r i)) : F :=
    ((Fintype.equivFin (T i).Eigenvalues).symm k).val
  have ha (i) : Function.Injective (a i) :=
    Subtype.val_injective.comp (Fintype.equivFin (T i).Eigenvalues).symm.injective
  have hfull (i ν) : (T i).HasEigenvalue ν ↔ ∃ k, a i k = ν := by
    constructor
    · intro hν
      exact ⟨Fintype.equivFin (T i).Eigenvalues ⟨ν, hν⟩,
        congrArg (fun e : (T i).Eigenvalues => e.val)
          ((Fintype.equivFin (T i).Eigenvalues).symm_apply_apply ⟨ν, hν⟩)⟩
    · rintro ⟨k, rfl⟩
      exact ((Fintype.equivFin (T i).Eigenvalues).symm k).property
  have hev (χ) (hχ : χ ∈ s) (i) : (T i).HasEigenvalue (χ i) := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp ((hs χ).mp hχ)
    exact hasEigenvalue_of_hasEigenvector
      ⟨(Submodule.mem_iInf _).mp hv i, hv0⟩
  have hproducts (χ) (hχ : χ ∈ s) :
      ∃ L : List (ι × Polynomial F),
        (∀ z ∈ L, ∃ (r : ℕ) (a : Fin r → F) (j : Fin r),
          Function.Injective a ∧
          (∀ ν, (T z.1).HasEigenvalue ν ↔ ∃ k, a k = ν) ∧
          a j = χ z.1 ∧
          z.2 = Specs.D05.M08.Interpolation.lagrangePolynomial_value F r a j) ∧
        (∀ ψ ∈ s, ψ ≠ χ → ∃ z ∈ L, χ z.1 ≠ ψ z.1) ∧
        (L.map (fun z => Polynomial.aeval (T z.1) z.2)).prod =
          D05.orthogonalProjection (D05.jointEigenspace T χ) := by
    let J := {ψ : ι → F // ψ ∈ s.erase χ}
    have hdiff (ψ : J) : ∃ i, χ i ≠ ψ.val i := by
      apply Function.ne_iff.mp
      exact Ne.symm (Finset.mem_erase.mp ψ.property).1
    choose sep hsep using hdiff
    let idx (i : ι) : Fin (r i) :=
      Classical.choose ((hfull i (χ i)).mp (hev χ hχ i))
    have hidx (i) : a i (idx i) = χ i :=
      Classical.choose_spec ((hfull i (χ i)).mp (hev χ hχ i))
    let q (i : ι) :=
      Specs.D05.M08.Interpolation.lagrangePolynomial_value F (r i) (a i) (idx i)
    let factor (ψ : J) : ι × Polynomial F := (sep ψ, q (sep ψ))
    let L := (s.erase χ).attach.toList.map factor
    have hL : ∀ z ∈ L, ∃ (r : ℕ) (a : Fin r → F) (j : Fin r),
        Function.Injective a ∧
        (∀ ν, (T z.1).HasEigenvalue ν ↔ ∃ k, a k = ν) ∧
        a j = χ z.1 ∧
        z.2 = Specs.D05.M08.Interpolation.lagrangePolynomial_value F r a j := by
      intro z hz
      obtain ⟨ψ, _, rfl⟩ := List.mem_map.mp hz
      exact ⟨r (sep ψ), a (sep ψ), idx (sep ψ), ha _, hfull _, hidx _, rfl⟩
    have hseparate : ∀ ψ ∈ s, ψ ≠ χ → ∃ z ∈ L, χ z.1 ≠ ψ z.1 := by
      intro ψ hψ hne
      let j : J := ⟨ψ, Finset.mem_erase.mpr ⟨hne, hψ⟩⟩
      exact ⟨factor j, List.mem_map.mpr ⟨j, Finset.mem_toList.mpr (Finset.mem_attach _ j), rfl⟩, hsep j⟩
    have heval (ψ) (hψ : ψ ∈ s) (z) (hz : z ∈ L) :
        z.2.eval (ψ z.1) = if χ z.1 = ψ z.1 then 1 else 0 := by
      obtain ⟨r', a', j, haj, hfullj, hj, hp⟩ := hL z hz
      rw [hp, interpolation_eval a' haj j _ ((hfullj _).mp (hev ψ hψ z.1)), hj]
    refine ⟨L, hL, hseparate, ?_⟩
    apply b.ext
    intro k
    have hk : eigfn k ∈ s := Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
    rw [polynomial_list_action T L (eigfn k) (b k) (hbk k)]
    by_cases heq : eigfn k = χ
    · have hscalar : (L.map (fun z => z.2.eval (eigfn k z.1))).prod = 1 := by
        apply List.prod_eq_one
        intro c hc
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hc
        rw [heval _ hk z hz, heq, ite_eq_left rfl]
      rw [hscalar, one_smul]
      exact (D05.M12.Projection.fixes_subspace _ _ (heq ▸ hbk k)).symm
    · have hscalar : (L.map (fun z => z.2.eval (eigfn k z.1))).prod = 0 := by
        apply List.prod_eq_zero_iff.mpr
        obtain ⟨z, hz, hne⟩ := hseparate _ hk heq
        exact List.mem_map.mpr ⟨z, hz, by rw [heval _ hk z hz, ite_eq_right hne]⟩
      rw [hscalar, zero_smul]
      apply Eq.symm
      apply LinearMap.mem_ker.mp
      rw [D05.M12.Projection.kernel_eq]
      exact ho _ _ heq (hbk k)
  refine ⟨s, hs, (fun χ _ ψ _ hne => ho χ ψ hne), hinter, hproducts, ?_⟩
  intro χ hχ
  obtain ⟨L, hL, hsep, hprod⟩ := hproducts χ hχ
  rw [← hprod]
  apply Subalgebra.list_prod_mem
  intro A hA
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hA
  exact (Algebra.adjoin_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self z.1)))
    (Polynomial.aeval_mem_adjoin_singleton F (p := z.2) (T z.1))

end InnerProduct

theorem real_joint_projections :
    Specs.D05.M13.SimultaneousSpectral.JointProjections.real_joint_projections := by
  intro V ι _ _ _ T hT hC
  obtain ⟨b, hb, μ, hμ⟩ :=
    D05.M13.SimultaneousSpectral.real_common_orthonormal_eigenbasis T hT hC
  exact resolution_of_common_basis T
    (fun i => D05.M13.Normal.selfAdjoint_normal (T i) (hT i)) b hb μ hμ

theorem complex_joint_projections :
    Specs.D05.M13.SimultaneousSpectral.JointProjections.complex_joint_projections := by
  intro V ι _ _ _ T hT hC
  obtain ⟨b, hb, μ, hμ⟩ :=
    D05.M13.SimultaneousSpectral.complex_common_orthonormal_eigenbasis T hT hC
  exact resolution_of_common_basis T hT b hb μ hμ

theorem empty_family :
    Specs.D05.M13.SimultaneousSpectral.JointProjections.empty_family := by
  intro F V ι _ _ _ _ _ _ T
  have htop (χ : ι → F) : D05.jointEigenspace T χ = ⊤ := by
    simp [D05.jointEigenspace]
  refine ⟨?_, fun χ => ⟨htop χ, ?_⟩⟩
  · refine ⟨fun _ => 0, ?_, ?_⟩
    · change D05.jointEigenspace T (fun _ => 0) ≠ ⊥
      rw [htop]
      exact top_ne_bot
    · intro ψ _
      exact Subsingleton.elim _ _
  · ext v
    exact D05.M12.Projection.fixes_subspace _ v (by rw [htop]; trivial)

theorem zero_space :
    Specs.D05.M13.SimultaneousSpectral.JointProjections.zero_space := by
  intro F V ι _ _ _ _ T
  ext χ
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
  exact Subsingleton.elim _ _


end D05.M13.SimultaneousSpectral.JointProjections
