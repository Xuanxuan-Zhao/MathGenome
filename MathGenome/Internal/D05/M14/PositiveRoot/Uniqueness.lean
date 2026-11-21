import MathGenome.Internal.Specs.D05.M14.PositiveRoot.Uniqueness
import MathGenome.Internal.D05.M14.PositiveSpectrum
import MathGenome.Internal.D05.M09.CommutantInvariance

/-! A positive square root is scalar on each eigenspace of its square.
We apply the spectral theorem to the positive restriction. Its eigenvalues ν
satisfy ν ≥ 0 and ν² = a, hence ν = sqrt a, also when a = 0. Equality on the
spectral basis of T then proves uniqueness, without defining a preferred root. -/

noncomputable section

namespace D05.M14.PositiveRoot.Uniqueness

open Module.End

variable {F V : Type*} [RCLike F] [NormedAddCommGroup V]
  [InnerProductSpace F V] [FiniteDimensional F V]

theorem root_commutes : Specs.D05.M14.PositiveRoot.Uniqueness.root_commutes := by
  intro F V _ _ _ _ T R hsq
  rw [← hsq, pow_two, mul_assoc]

theorem root_preserves_eigenspace :
    Specs.D05.M14.PositiveRoot.Uniqueness.root_preserves_eigenspace := by
  intro F V _ _ _ _ T R hsq μ x hx
  exact D05.M09.CommutantInvariance.eigenspace_invariant R T
    (root_commutes T R hsq) μ x hx

omit [FiniteDimensional F V] in
/-- Restricting positivity to an invariant subspace preserves both symmetry and
nonnegativity of the quadratic form. -/
theorem positive_restriction (R : V →ₗ[F] V) (hR : R.IsPositive)
    (P : Submodule F V) (hinv : ∀ x ∈ P, R x ∈ P) :
    (R.restrict hinv).IsPositive :=
  ⟨hR.isSymmetric.restrict_invariant hinv, fun x => hR.2 x⟩

theorem root_on_eigenspace :
    Specs.D05.M14.PositiveRoot.Uniqueness.root_on_eigenspace := by
  intro F V _ _ _ _ T R _hT hR hsq a x hx
  classical
  let P := T.eigenspace (a : F)
  have hinv : ∀ y ∈ P, R y ∈ P := root_preserves_eigenspace T R hsq (a : F)
  let A := R.restrict hinv
  have hA : A.IsPositive := positive_restriction R
    ((D05.M14.Positive.positiveSemidefinite_iff_mathlib R).mp hR) P hinv
  let b := hA.isSymmetric.eigenvectorBasis rfl
  have he : ∀ i, A (b i) = (Real.sqrt a : F) • b i := by
    intro i
    let ν := hA.isSymmetric.eigenvalues rfl i
    have hν : 0 ≤ ν := hA.nonneg_eigenvalues rfl i
    have hdiag : R (b i : V) = (ν : F) • (b i : V) :=
      congrArg Subtype.val (hA.isSymmetric.apply_eigenvectorBasis rfl i)
    have hn : (b i : V) ≠ 0 := by
      intro hz
      exact (b.toBasis.ne_zero i) (Subtype.ext hz)
    have hsqv : R (R (b i : V)) = (a : F) • (b i : V) := by
      calc
        _ = T (b i : V) := congrArg (fun f : V →ₗ[F] V => f (b i : V)) hsq
        _ = _ := mem_eigenspace_iff.mp (b i).property
    rw [hdiag, map_smul, hdiag, smul_smul] at hsqv
    have hs : (ν : F) * (ν : F) = (a : F) := smul_left_injective F hn hsqv
    have hsreal : ν * ν = a := by
      apply RCLike.ofReal_injective (K := F)
      simpa only [RCLike.ofReal_mul] using hs
    have hroot : ν = Real.sqrt a := by
      rw [← hsreal, Real.sqrt_mul_self hν]
    simpa only [← hroot] using hA.isSymmetric.apply_eigenvectorBasis rfl i
  have hscalar : A = (Real.sqrt a : F) • (LinearMap.id : P →ₗ[F] P) := by
    apply b.toBasis.ext
    intro i
    exact he i
  exact congrArg Subtype.val (LinearMap.congr_fun hscalar (⟨x, hx⟩ : P))

theorem root_on_scalar_eigenspace :
    Specs.D05.M14.PositiveRoot.Uniqueness.root_on_scalar_eigenspace := by
  intro F V _ _ _ _ T R hT hR hsq μ x hx
  by_cases hn : x = 0
  · simp [hn]
  · have hμ : HasEigenvalue T μ := hasEigenvalue_of_hasEigenvector ⟨hx, hn⟩
    have hre := D05.M14.PositiveSpectrum.eigenvalues_real T hT.1 μ hμ
    apply root_on_eigenspace T R hT hR hsq (RCLike.re μ) x
    rwa [hre]

theorem restricted_eigenvalues :
    Specs.D05.M14.PositiveRoot.Uniqueness.restricted_eigenvalues := by
  intro F V _ _ _ _ T R hT hR hsq a hinv μ hμ
  obtain ⟨x, hx, hn⟩ := hμ.exists_hasEigenvector
  have he : R (x : V) = μ • (x : V) :=
    congrArg Subtype.val (mem_eigenspace_iff.mp hx)
  have hs := root_on_eigenspace T R hT hR hsq a (x : V) x.property
  have hn' : (x : V) ≠ 0 := fun h => hn (Subtype.ext h)
  exact smul_left_injective F hn' (he.symm.trans hs)

theorem root_vanishes_on_kernel :
    Specs.D05.M14.PositiveRoot.Uniqueness.root_vanishes_on_kernel := by
  intro F V _ _ _ _ T R hT hR hsq x hx
  have he : x ∈ T.eigenspace ((0 : ℝ) : F) := by
    apply mem_eigenspace_iff.mpr
    simpa using hx
  simpa using root_on_eigenspace T R hT hR hsq 0 x he

theorem positive_roots_unique :
    Specs.D05.M14.PositiveRoot.Uniqueness.positive_roots_unique := by
  intro F V _ _ _ _ T R S hT hR hS hRsq hSsq
  have hs := (D05.M14.Positive.positiveSemidefinite_iff_mathlib T).mp hT
  let b := hs.isSymmetric.eigenvectorBasis rfl
  apply b.toBasis.ext
  intro i
  have hi : b i ∈ T.eigenspace (hs.isSymmetric.eigenvalues rfl i : F) :=
    (hs.isSymmetric.hasEigenvector_eigenvectorBasis rfl i).1
  exact (root_on_eigenspace T R hT hR hRsq _ (b i) hi).trans
    (root_on_eigenspace T S hT hS hSsq _ (b i) hi).symm

end D05.M14.PositiveRoot.Uniqueness
