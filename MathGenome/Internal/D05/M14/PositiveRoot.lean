import MathGenome.Internal.Specs.D05.M14.PositiveRoot
import MathGenome.Internal.D05.M14.PositiveRoot.Uniqueness
import MathGenome.Internal.D05.M13.FunctionalCalculus

/-! The positive square root is constructed on an orthonormal eigenbasis with
nonnegative diagonal sqrt λ. Its square is checked on that basis. The upstream
restriction argument proves uniqueness and the formula on entire eigenspaces;
comparison on a spectral basis identifies the construction with the finite
spectral functional calculus. No eigenvalue is divided by. -/

noncomputable section

namespace D05.M14.PositiveRoot

open Module.End
open scoped ComplexOrder

theorem exists_positive_root : Specs.D05.M14.PositiveRoot.exists_positive_root := by
  intro F V _ _ _ _ T hT
  classical
  have hp := (D05.M14.Positive.positiveSemidefinite_iff_mathlib T).mp hT
  let hs := hp.isSymmetric
  let b := hs.eigenvectorBasis rfl
  let a := fun i => Real.sqrt (hs.eigenvalues rfl i)
  let S := b.toBasis.constr F (fun i => (a i : F) • b i)
  have hS : ∀ i, S (b i) = (a i : F) • b i := by
    intro i
    exact b.toBasis.constr_basis F _ i
  refine ⟨S, ?_, ?_⟩
  · apply (D05.M14.Positive.positiveSemidefinite_iff_mathlib S).mpr
    apply (LinearMap.posSemidef_toMatrix_iff b).mp
    have hm : S.toMatrix b.toBasis b.toBasis = Matrix.diagonal (fun i => (a i : F)) := by
      ext i j
      by_cases hij : i = j <;>
        simp [LinearMap.toMatrix_apply, hS, hij, RCLike.real_smul_eq_coe_mul]
    rw [hm, Matrix.posSemidef_diagonal_iff]
    intro i
    exact RCLike.ofReal_nonneg.mpr (Real.sqrt_nonneg _)
  · apply b.toBasis.ext
    intro i
    change S (S (b i)) = T (b i)
    rw [hS, map_smul, hS, smul_smul, hs.apply_eigenvectorBasis rfl,
      ← RCLike.ofReal_mul, Real.mul_self_sqrt (hp.nonneg_eigenvalues rfl i)]

theorem existsUnique_positive_root :
    Specs.D05.M14.PositiveRoot.existsUnique_positive_root := by
  intro F V _ _ _ _ T hT
  obtain ⟨S, hS, hsq⟩ := exists_positive_root T hT
  refine ⟨S, ⟨hS, hsq⟩, ?_⟩
  intro R hR
  exact Uniqueness.positive_roots_unique T R S hT hR.1 hS hR.2 hsq

theorem root_on_eigenspace : Specs.D05.M14.PositiveRoot.root_on_eigenspace :=
  Uniqueness.root_on_scalar_eigenspace

theorem root_on_real_eigenspace : Specs.D05.M14.PositiveRoot.root_on_real_eigenspace :=
  Uniqueness.root_on_eigenspace

theorem root_eq_functional_calculus :
    Specs.D05.M14.PositiveRoot.root_eq_functional_calculus := by
  intro F V _ _ _ _ T S hT hS hsq r a ha hfull
  have hp := (D05.M14.Positive.positiveSemidefinite_iff_mathlib T).mp hT
  let b := hp.isSymmetric.eigenvectorBasis rfl
  apply b.toBasis.ext
  intro i
  have hev := hp.isSymmetric.hasEigenvalue_eigenvalues rfl i
  obtain ⟨j, hj⟩ := (hfull _).mp hev
  have hi : b i ∈ T.eigenspace (a j) := by
    rw [hj]
    exact (hp.isSymmetric.hasEigenvector_eigenvectorBasis rfl i).1
  exact (root_on_eigenspace T S hT hS hsq (a j) (b i) hi).trans
    (D05.M13.FunctionalCalculus.action_on_eigenspace T a ha
      (fun μ => (Real.sqrt (RCLike.re μ.val) : F)) j (b i) hi).symm

theorem functional_calculus_is_positive_root :
    Specs.D05.M14.PositiveRoot.functional_calculus_is_positive_root := by
  intro F V _ _ _ _ T hT r a ha hfull
  obtain ⟨S, hS, hsq⟩ := exists_positive_root T hT
  have he := root_eq_functional_calculus T S hT hS hsq a ha hfull
  exact he ▸ ⟨hS, hsq⟩

end D05.M14.PositiveRoot
