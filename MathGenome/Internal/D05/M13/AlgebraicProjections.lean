import MathGenome.Internal.Specs.D05.M13.AlgebraicProjections
import MathGenome.Internal.D05.M09.Diagonalizable
import MathGenome.Internal.D05.M08.Interpolation
import MathGenome.Internal.D05.M08.Evaluation
import MathGenome.Internal.D05.M06.Projection
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-! K05.13.algebraic_projections: Lagrange polynomials give algebraic
component projections over any field, including the empty spectrum. -/
noncomputable section
namespace D05.M13.AlgebraicProjections
open scoped BigOperators

abbrev projection : Specs.D05.M13.AlgebraicProjections.projection_type :=
  Specs.D05.M13.AlgebraicProjections.projection_value

theorem denominators_nonzero : Specs.D05.M13.AlgebraicProjections.denominators_nonzero := by
  intro K _ r a ha i j hij
  exact D05.M08.Interpolation.denominators_nonzero K r a ha i j hij

theorem action_on_eigenspace : Specs.D05.M13.AlgebraicProjections.action_on_eigenspace := by
  intro K V _ _ _ T r a ha i j v hv
  change Polynomial.aeval T _ v = _
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul (Module.End.mem_eigenspace_iff.mp hv),
    D05.M08.Interpolation.basis_evaluation K r a ha i j]
  split_ifs <;> simp

section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {T : Module.End K V} {r : ℕ} {a : Fin r → K}

/-- Equality of linear maps follows from their values on the listed eigenspaces.
The required spanning is derived from diagonalizability and the full spectrum. -/
theorem ext_on_eigenspaces
    (hT : Specs.D05.M09.Diagonalizable.diagonalizable_value K V T)
    (hfull : ∀ μ, T.HasEigenvalue μ ↔ ∃ i, a i = μ)
    {S R : Module.End K V}
    (h : ∀ j v, v ∈ T.eigenspace (a j) → S v = R v) : S = R := by
  obtain ⟨n, b, μ, hb⟩ := hT
  apply b.ext
  intro k
  have hev : T.HasEigenvalue (μ k) :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr (hb k), b.ne_zero k⟩
  obtain ⟨j, hj⟩ := (hfull (μ k)).mp hev
  exact h j (b k) (Module.End.mem_eigenspace_iff.mpr (hj ▸ hb k))

end

theorem eigenspaces_span : Specs.D05.M13.AlgebraicProjections.eigenspaces_span := by
  intro K V _ _ _ _ T r a hT hfull
  obtain ⟨n, b, μ, hb⟩ := hT
  apply top_unique
  rw [← b.span_eq]
  apply Submodule.span_le.mpr
  rintro x ⟨k, rfl⟩
  have hev : T.HasEigenvalue (μ k) :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr (hb k), b.ne_zero k⟩
  obtain ⟨j, hj⟩ := (hfull (μ k)).mp hev
  exact Submodule.mem_iSup_of_mem j (Module.End.mem_eigenspace_iff.mpr (hj ▸ hb k))

theorem sum_projections : Specs.D05.M13.AlgebraicProjections.sum_projections := by
  intro K V _ _ _ _ T r a ha hT hfull
  apply ext_on_eigenspaces hT hfull
  intro j v hv
  simp only [LinearMap.sum_apply, action_on_eigenspace T a ha _ j v hv]
  simp

theorem idempotent_projections : Specs.D05.M13.AlgebraicProjections.idempotent_projections := by
  intro K V _ _ _ _ T r a ha hT hfull i
  apply ext_on_eigenspaces hT hfull
  intro j v hv
  simp only [pow_two, Module.End.mul_apply, action_on_eigenspace T a ha _ j v hv]
  by_cases hij : i = j
  · subst j
    simpa using action_on_eigenspace T a ha i i v hv
  · simp [hij]

theorem distinct_projections_mul : Specs.D05.M13.AlgebraicProjections.distinct_projections_mul := by
  intro K V _ _ _ _ T r a ha hT hfull i j hij
  apply ext_on_eigenspaces hT hfull
  intro k v hv
  simp only [Module.End.mul_apply, action_on_eigenspace T a ha j k v hv]
  by_cases hjk : j = k
  · subst k
    simp [action_on_eigenspace T a ha i j v hv, hij]
  · simp [hjk]

theorem range_projection : Specs.D05.M13.AlgebraicProjections.range_projection := by
  intro K V _ _ _ _ T r a ha hT hfull i
  have heq : T * projection K V T r a i = a i • projection K V T r a i := by
    apply ext_on_eigenspaces hT hfull
    intro j v hv
    simp only [Module.End.mul_apply, LinearMap.smul_apply,
      action_on_eigenspace T a ha i j v hv]
    by_cases hij : i = j
    · subst j
      simpa using Module.End.mem_eigenspace_iff.mp hv
    · simp [hij]
  apply le_antisymm
  · rintro v ⟨x, rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    exact congrArg (fun f : Module.End K V => f x) heq
  · intro v hv
    exact ⟨v, by simpa using action_on_eigenspace T a ha i i v hv⟩

theorem kernel_projection : Specs.D05.M13.AlgebraicProjections.kernel_projection := by
  intro K V _ _ _ _ T r a ha hT hfull i
  apply le_antisymm
  · intro v hv
    have hv0 : projection K V T r a i v = 0 := hv
    have hsum : v = ∑ j, projection K V T r a j v := by
      simpa only [LinearMap.sum_apply, LinearMap.id_apply] using
        (congrArg (fun f : Module.End K V => f v) (sum_projections T a ha hT hfull)).symm
    rw [hsum]
    apply Submodule.sum_mem
    intro j _
    by_cases hji : j = i
    · subst j
      rw [hv0]
      exact Submodule.zero_mem _
    · apply Submodule.mem_iSup_of_mem j
      apply Submodule.mem_iSup_of_mem hji
      rw [← range_projection T a ha hT hfull j]
      exact LinearMap.mem_range_self _ v
  · apply iSup_le
    intro j
    apply iSup_le
    intro hji v hv
    change projection K V T r a i v = 0
    simpa [Ne.symm hji] using action_on_eigenspace T a ha i j v hv

theorem projection_apply_sum : Specs.D05.M13.AlgebraicProjections.projection_apply_sum := by
  intro K V _ _ _ _ T r a ha hT hfull i u w hu hw
  exact D05.M06.Projection.projection_apply_sum _ _ _
    (idempotent_projections T a ha hT hfull i)
    (range_projection T a ha hT hfull i)
    (kernel_projection T a ha hT hfull i) u w hu hw

theorem zero_space : Specs.D05.M13.AlgebraicProjections.zero_space := by
  intro K V _ _ _ _ T a
  refine ⟨fun μ => D05.M09.Eigenspace.no_eigenvalues_on_zero_space T μ, ?_, ?_⟩
  · exact Finset.sum_empty
  · ext v
    exact Subsingleton.elim _ _

theorem empty_spectrum_iff : Specs.D05.M13.AlgebraicProjections.empty_spectrum_iff := by
  intro K V _ _ _ _ T r a hT hfull
  constructor
  · intro hr
    subst r
    have hs := eigenspaces_span T a hT hfull
    have hbot : (⊥ : Submodule K V) = ⊤ := by simpa using hs
    have hz : ∀ x : V, x = 0 := fun x => by
      have hx : x ∈ (⊥ : Submodule K V) := hbot.symm ▸ Submodule.mem_top
      exact hx
    exact ⟨fun x y => (hz x).trans (hz y).symm⟩
  · intro hzero
    haveI := hzero
    by_contra hr
    have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    let i : Fin r := ⟨0, hrpos⟩
    have hev := (hfull (a i)).mpr ⟨i, rfl⟩
    exact D05.M09.Eigenspace.no_eigenvalues_on_zero_space T (a i) hev

end D05.M13.AlgebraicProjections
