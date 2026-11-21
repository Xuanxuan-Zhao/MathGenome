import MathGenome.Internal.Specs.D05.M13.SimultaneousSpectral.JointAlgebra
import MathGenome.Internal.D05.M13.SimultaneousSpectral.JointProjections

/-! Generated algebras of commuting real self-adjoint or complex normal families.
All algebra arguments below use the intrinsic orthogonal resolution already proved
upstream; neither the family nor the space is assumed nonempty. -/
noncomputable section
local instance {α : Sort*} : DecidableEq α := Classical.typeDecidableEq α
open scoped BigOperators
namespace D05.M13.SimultaneousSpectral.JointAlgebra

section Resolution
variable {F V ι : Type*} [RCLike F] [NormedAddCommGroup V]
  [InnerProductSpace F V] [FiniteDimensional F V]
  (T : ι → Module.End F V) (s : Finset (ι → F))
  (ho : ∀ χ ∈ s, ∀ ψ ∈ s, χ ≠ ψ →
    D05.jointEigenspace T χ ≤ (D05.jointEigenspace T ψ).orthogonal)
  (hi : DirectSum.IsInternal (fun χ : {χ // χ ∈ s} => D05.jointEigenspace T χ.val))

/- Equality can be checked on the joint spaces, since they span V. -/
include hi in
theorem ext_on_joint (A B : Module.End F V)
    (h : ∀ χ : {χ // χ ∈ s}, ∀ v ∈ D05.jointEigenspace T χ.val, A v = B v) :
    A = B := by
  apply LinearMap.eqLocus_eq_top.mp
  apply top_unique
  rw [← hi.submodule_iSup_eq_top]
  exact iSup_le fun χ v hv => h χ v hv

/- The actual orthogonal projection acts by the Kronecker delta on joint spaces. -/
include ho in
theorem projection_action (χ ψ : {χ // χ ∈ s}) (v : V)
    (hv : v ∈ D05.jointEigenspace T ψ.val) :
    D05.orthogonalProjection (D05.jointEigenspace T χ.val) v =
      if χ = ψ then v else 0 := by
  classical
  by_cases h : χ = ψ
  · subst ψ
    rw [ite_eq_left rfl]
    exact D05.M12.Projection.fixes_subspace _ v hv
  · rw [ite_eq_right h]
    apply LinearMap.mem_ker.mp
    rw [D05.M12.Projection.kernel_eq]
    exact ho ψ.val ψ.property χ.val χ.property
      (fun he => h (Subtype.ext he.symm)) hv

/- Finite projection combinations have precisely their stated scalars. -/
include ho in
theorem sum_action (c : {χ // χ ∈ s} → F) (ψ : {χ // χ ∈ s}) (v : V)
    (hv : v ∈ D05.jointEigenspace T ψ.val) :
    D05.jointProjectionSum T s c v = c ψ • v := by
  classical
  simp [D05.jointProjectionSum, LinearMap.sum_apply, projection_action T s ho _ ψ v hv]

/- Each polynomial in the family is scalar on every joint space. The induction
uses only algebraic operations, so it applies to infinitely indexed families. -/
theorem scalar_action_of_mem (A : Module.End F V)
    (hA : A ∈ Algebra.adjoin F (Set.range T)) :
    ∃ c : {χ // χ ∈ s} → F,
      ∀ χ v, v ∈ D05.jointEigenspace T χ.val → A v = c χ • v := by
  classical
  induction hA using Algebra.adjoin_induction with
  | mem A hA =>
      obtain ⟨i, rfl⟩ := hA
      exact ⟨fun χ => χ.val i, fun χ v hv =>
        Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hv i)⟩
  | algebraMap r =>
      refine ⟨fun _ => r, ?_⟩
      intro χ v hv
      simp [Algebra.algebraMap_eq_smul_one]
  | add A B hA hB ihA ihB =>
      obtain ⟨a, ha⟩ := ihA
      obtain ⟨b, hb⟩ := ihB
      refine ⟨fun χ => a χ + b χ, ?_⟩
      intro χ v hv
      simp only [LinearMap.add_apply, ha χ v hv, hb χ v hv, add_smul]
  | mul A B hA hB ihA ihB =>
      obtain ⟨a, ha⟩ := ihA
      obtain ⟨b, hb⟩ := ihB
      refine ⟨fun χ => b χ * a χ, ?_⟩
      intro χ v hv
      simp only [Module.End.mul_apply, hb χ v hv, map_smul, ha χ v hv, smul_smul]

/- Orthogonal projections are self-adjoint, using the upstream inner identity. -/
theorem projection_adjoint (U : Submodule F V) :
    LinearMap.adjoint (D05.orthogonalProjection U) = D05.orthogonalProjection U := by
  apply Eq.symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  exact (D05.M12.Projection.self_adjoint_identity U y x).symm

/- Adjoints conjugate coefficients, including complex coefficients. -/
theorem sum_adjoint (c : {χ // χ ∈ s} → F) :
    LinearMap.adjoint (D05.jointProjectionSum T s c) =
      D05.jointProjectionSum T s (fun χ => star (c χ)) := by
  unfold D05.jointProjectionSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [map_smulₛₗ, projection_adjoint]
  rfl

/- The algebra equality follows from scalar action and membership of all Pχ. -/
include ho hi in
theorem mem_iff_projection_sum
    (hm : ∀ χ ∈ s, D05.orthogonalProjection (D05.jointEigenspace T χ) ∈
      Algebra.adjoin F (Set.range T)) (A : Module.End F V) :
    A ∈ Algebra.adjoin F (Set.range T) ↔ ∃ c, A = D05.jointProjectionSum T s c := by
  constructor
  · intro hA
    obtain ⟨c, hc⟩ := scalar_action_of_mem T s A hA
    refine ⟨c, ext_on_joint T s hi A _ ?_⟩
    intro χ v hv
    rw [hc χ v hv, sum_action T s ho c χ v hv]
  · rintro ⟨c, rfl⟩
    apply Subalgebra.sum_mem
    intro χ hχ
    exact Subalgebra.smul_mem _ (hm χ.val χ.property) (c χ)

/- Distinct real labels give Lagrange polynomials for the same projections. -/
include ho hi in
theorem generator_interpolation (t : {χ // χ ∈ s} → ℝ) (ht : Function.Injective t)
    (j : {χ // χ ∈ s}) :
    Polynomial.aeval (D05.jointProjectionSum T s (fun χ => (t χ : F)))
      (Lagrange.basis Finset.univ (fun χ => (t χ : F)) j) =
        D05.orthogonalProjection (D05.jointEigenspace T j.val) := by
  classical
  have htF : Function.Injective (fun χ => (t χ : F)) := RCLike.ofReal_injective.comp ht
  apply ext_on_joint T s hi
  intro ψ v hv
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul (sum_action T s ho _ ψ v hv)]
  rw [projection_action T s ho j ψ v hv]
  by_cases hj : j = ψ
  · subst ψ
    rw [Lagrange.eval_basis_self htF.injOn (Finset.mem_univ j), ite_eq_left rfl, one_smul]
  · rw [Lagrange.eval_basis_of_ne (v := fun χ => (t χ : F)) hj (Finset.mem_univ ψ), ite_eq_right hj, zero_smul]

/- Assemble the full algebra and generator conclusion from a joint resolution. -/
include ho hi in
theorem algebra_on_of_resolution
    (hm : ∀ χ ∈ s, D05.orthogonalProjection (D05.jointEigenspace T χ) ∈
      Algebra.adjoin F (Set.range T)) : D05.JointAlgebraOn T s := by
  classical
  have hmem := mem_iff_projection_sum T s ho hi hm
  refine ⟨hmem, sum_adjoint T s, ?_, ?_⟩
  · intro A hA
    obtain ⟨c, rfl⟩ := (hmem A).mp hA
    rw [sum_adjoint]
    exact (hmem _).mpr ⟨_, rfl⟩
  · intro t ht
    dsimp only
    let D := D05.jointProjectionSum T s (fun χ => (t χ : F))
    have hD : D ∈ Algebra.adjoin F (Set.range T) := (hmem D).mpr ⟨_, rfl⟩
    have hP (j : {χ // χ ∈ s}) :
        D05.orthogonalProjection (D05.jointEigenspace T j.val) ∈ Algebra.adjoin F {D} := by
      rw [← generator_interpolation T s ho hi t ht j]
      exact Polynomial.aeval_mem_adjoin_singleton F D
    refine ⟨?_, le_antisymm ?_ ?_, generator_interpolation T s ho hi t ht⟩
    · change D = LinearMap.adjoint D
      rw [sum_adjoint]
      simp only [RCLike.star_def, RCLike.conj_ofReal]
      rfl
    · exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hD)
    · intro A hA
      obtain ⟨c, rfl⟩ := (hmem A).mp hA
      apply Subalgebra.sum_mem
      intro χ hχ
      exact Subalgebra.smul_mem _ (hP χ) (c χ)

end Resolution

/- No decomposition is assumed by the final family theorems: the upstream
joint-projection theorem constructs it from exactly their operator hypotheses. -/
theorem algebra_of_resolution {F V ι : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : ι → Module.End F V)
    (hr : D05.JointProjectionResolution T) : D05.JointAlgebraConclusion T := by
  obtain ⟨s, hs, ho, hi, hp, hm⟩ := hr
  exact ⟨s, hs, ho, hi, algebra_on_of_resolution T s ho hi hm⟩

theorem real_joint_algebra :
    Specs.D05.M13.SimultaneousSpectral.JointAlgebra.real_joint_algebra := by
  intro V ι _ _ _ T hT hC
  exact algebra_of_resolution T (JointProjections.real_joint_projections T hT hC)

theorem complex_joint_algebra :
    Specs.D05.M13.SimultaneousSpectral.JointAlgebra.complex_joint_algebra := by
  intro V ι _ _ _ T hT hC
  exact algebra_of_resolution T (JointProjections.complex_joint_projections T hT hC)

/- Finiteness of the intrinsic spectrum supplies distinct real labels, even
for the empty joint list. Thus the universal label statement gives existence. -/
theorem exists_selfAdjoint_generator {F V ι : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V] [FiniteDimensional F V]
    (T : ι → Module.End F V) (h : D05.JointAlgebraConclusion T) :
    ∃ D : Module.End F V, D05.selfAdjoint D ∧
      Algebra.adjoin F {D} = Algebra.adjoin F (Set.range T) := by
  classical
  obtain ⟨s, hs, ho, hi, ha⟩ := h
  let t : {χ // χ ∈ s} → ℝ := fun χ => (Fintype.equivFin {χ // χ ∈ s} χ).val
  have ht : Function.Injective t := by
    intro χ ψ he
    apply (Fintype.equivFin {χ // χ ∈ s}).injective
    apply Fin.ext
    dsimp only [t] at he
    exact_mod_cast he
  obtain ⟨hself, hgen, hproj⟩ := ha.2.2.2 t ht
  exact ⟨_, hself, hgen⟩

theorem real_single_generator :
    Specs.D05.M13.SimultaneousSpectral.JointAlgebra.real_single_generator := by
  intro V ι _ _ _ T hT hC
  exact exists_selfAdjoint_generator T (real_joint_algebra T hT hC)

theorem complex_single_generator :
    Specs.D05.M13.SimultaneousSpectral.JointAlgebra.complex_single_generator := by
  intro V ι _ _ _ T hT hC
  exact exists_selfAdjoint_generator T (complex_joint_algebra T hT hC)

/- Empty generation is the scalar algebra; adjoining zero leaves it unchanged. -/
theorem empty_family_algebra :
    Specs.D05.M13.SimultaneousSpectral.JointAlgebra.empty_family_algebra := by
  intro F V ι _ _ _ _ _ T
  have he : Set.range T = ∅ := by
    simp only [Set.range_eq_empty]
  have hz : Algebra.adjoin F {(0 : Module.End F V)} = ⊥ := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      intro A hA
      rcases Set.mem_singleton_iff.mp hA with rfl
      exact zero_mem _
    · exact bot_le
  refine ⟨?_, ?_, ?_⟩
  · intro A
    rw [he, Algebra.adjoin_empty, Algebra.mem_bot]
    change (∃ c, algebraMap F (Module.End F V) c = A) ↔ ∃ c, A = c • 1
    simp only [Algebra.algebraMap_eq_smul_one]
    exact exists_congr fun c => eq_comm
  · change (0 : Module.End F V) = LinearMap.adjoint 0
    simp
  · rw [hz, he, Algebra.adjoin_empty]

/- All maps and all sums on the zero space are the unique zero map. -/
theorem zero_space_algebra :
    Specs.D05.M13.SimultaneousSpectral.JointAlgebra.zero_space_algebra := by
  intro F V ι _ _ _ _ _ T
  classical
  have ho : ∀ χ ∈ (∅ : Finset (ι → F)), ∀ ψ ∈ (∅ : Finset (ι → F)), χ ≠ ψ →
      D05.jointEigenspace T χ ≤ (D05.jointEigenspace T ψ).orthogonal := by simp
  have hi : DirectSum.IsInternal
      (fun χ : {χ // χ ∈ (∅ : Finset (ι → F))} => D05.jointEigenspace T χ.val) := by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · exact iSupIndep_subsingleton _
    · exact Subsingleton.elim _ _
  have hm : ∀ χ ∈ (∅ : Finset (ι → F)),
      D05.orthogonalProjection (D05.jointEigenspace T χ) ∈
        Algebra.adjoin F (Set.range T) := by simp
  refine ⟨fun χ => Subsingleton.elim _ _, algebra_on_of_resolution T ∅ ho hi hm, ?_, ?_, ?_⟩
  · intro A
    have hA : A = 0 := Subsingleton.elim _ _
    simp [hA]
  · exact Subsingleton.elim _ _
  · exact Subsingleton.elim _ _

end D05.M13.SimultaneousSpectral.JointAlgebra
