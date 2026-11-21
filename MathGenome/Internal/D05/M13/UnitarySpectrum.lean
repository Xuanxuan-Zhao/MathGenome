import MathGenome.Internal.Specs.D05.M13.UnitarySpectrum
import MathGenome.Internal.D05.M13.ComplexSpectral
import MathGenome.Internal.D05.M13.Unitary
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

noncomputable section

namespace D05.M13.UnitarySpectrum

open Module.End

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

/-- The adjoint acts on a normal eigenvector by the conjugate eigenvalue. -/
theorem adjoint_eigenvector (T : Module.End ℂ V) (hT : D05.normalOperator T)
    {μ : ℂ} {v : V} (hv : T v = μ • v) :
    LinearMap.adjoint T v = starRingEnd ℂ μ • v :=
  (D05.M13.NormalBasic.eigenvector_equation_iff T hT μ v).mp hv

theorem selfAdjoint_iff_real_eigenvalues :
    Specs.D05.M13.UnitarySpectrum.selfAdjoint_iff_real_eigenvalues := by
  intro V _ _ _ T hT
  constructor
  · intro hs μ hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have he := adjoint_eigenvector T hT hv.apply_eq_smul
    rw [← hs, hv.apply_eq_smul] at he
    have hc : μ = starRingEnd ℂ μ := smul_left_injective ℂ hv.2 he
    have hi := congrArg Complex.im hc
    change μ.im = -μ.im at hi
    linarith
  · intro hr
    obtain ⟨b, μ, hb⟩ := D05.M13.ComplexSpectral.exists_orthonormalBasis T hT
    apply b.toBasis.ext
    intro i
    change T (b i) = LinearMap.adjoint T (b i)
    have hμ : T.HasEigenvalue (μ i) :=
      hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.mpr (hb i), b.toBasis.ne_zero i⟩
    have hc : starRingEnd ℂ (μ i) = μ i := by
      apply Complex.ext <;> simp [hr (μ i) hμ]
    rw [hb, adjoint_eigenvector T hT (hb i), hc]

theorem unitary_iff_norm_eigenvalues :
    Specs.D05.M13.UnitarySpectrum.unitary_iff_norm_eigenvalues := by
  intro V _ _ _ T hT
  constructor
  · intro hu μ hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have hn := D05.M13.Unitary.isometry_norm T hu.1 v
    rw [hv.apply_eq_smul, norm_smul] at hn
    exact mul_right_cancel₀ (norm_ne_zero_iff.mpr hv.2) (by simpa using hn)
  · intro hn
    obtain ⟨b, μ, hb⟩ := D05.M13.ComplexSpectral.exists_orthonormalBasis T hT
    have hid : (LinearMap.adjoint T).comp T = LinearMap.id := by
      apply b.toBasis.ext
      intro i
      change LinearMap.adjoint T (T (b i)) = b i
      have hμ : T.HasEigenvalue (μ i) :=
        hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.mpr (hb i), b.toBasis.ne_zero i⟩
      simp only [hb, map_smul, adjoint_eigenvector T hT (hb i), smul_smul]
      have hc : μ i * starRingEnd ℂ (μ i) = 1 := by
        rw [Complex.mul_conj', hn (μ i) hμ]
        norm_num
      rw [hc, one_smul]
    exact (D05.M13.Unitary.endomorphism_isometry_iff_unitary T).mp
      ((D05.M13.Unitary.isometry_iff_adjoint_comp T).mpr hid)

theorem jordan_counterexample :
    Specs.D05.M13.UnitarySpectrum.jordan_counterexample := by
  let A : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 0, 1]
  let J : Module.End ℂ (EuclideanSpace ℂ (Fin 2)) := Matrix.toEuclideanLin A
  let e₀ : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![1, 0]
  let e₁ : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![0, 1]
  have hJ₀ (v : EuclideanSpace ℂ (Fin 2)) : J v 0 = v 0 + v 1 := by
    simp [J, A, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_two]
  have hJ₁ (v : EuclideanSpace ℂ (Fin 2)) : J v 1 = v 1 := by
    simp [J, A, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_two]
  have he₀ : J e₀ = e₀ := by
    ext i
    fin_cases i <;> simp [hJ₀, hJ₁, e₀]
  have he₁ : J e₁ = WithLp.toLp 2 ![1, 1] := by
    ext i
    fin_cases i <;> simp [hJ₀, hJ₁, e₁]
  have hspectrum (μ : ℂ) : J.HasEigenvalue μ ↔ μ = 1 := by
    constructor
    · intro hμ
      obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
      by_contra hn
      have h₀ := congrArg (fun w : EuclideanSpace ℂ (Fin 2) => w 0) hv.apply_eq_smul
      have h₁ := congrArg (fun w : EuclideanSpace ℂ (Fin 2) => w 1) hv.apply_eq_smul
      have hz₁ : v 1 = 0 := by
        apply (mul_eq_zero.mp (show (μ - 1) * v 1 = 0 by
          have hh : v 1 = μ * v 1 := by simpa [hJ₁] using h₁
          rw [sub_mul, one_mul, sub_eq_zero]
          exact hh.symm)).resolve_left (sub_ne_zero.mpr hn)
      have hz₀ : v 0 = 0 := by
        apply (mul_eq_zero.mp (show (μ - 1) * v 0 = 0 by
          have hh : v 0 = μ * v 0 := by simpa [hJ₀, hz₁] using h₀
          rw [sub_mul, one_mul, sub_eq_zero]
          exact hh.symm)).resolve_left (sub_ne_zero.mpr hn)
      apply hv.2
      ext i
      fin_cases i <;> simp [hz₀, hz₁]
    · rintro rfl
      apply hasEigenvalue_of_hasEigenvector (x := e₀)
      refine ⟨mem_eigenspace_iff.mpr ?_, ?_⟩
      · simpa using he₀
      · intro h
        have := congrArg (fun w : EuclideanSpace ℂ (Fin 2) => w 0) h
        norm_num [e₀] at this
  refine ⟨hspectrum, ?_, ?_, ?_, ?_, ?_⟩
  · intro μ hμ
    rw [(hspectrum μ).mp hμ]
    simp
  · intro h
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
    norm_num [A, Matrix.transpose_apply] at this
  · intro h
    change J = LinearMap.adjoint J at h
    have he := congrArg (fun L : Module.End ℂ (EuclideanSpace ℂ (Fin 2)) => L e₀ 1) h
    change J e₀ 1 = (Matrix.toEuclideanLin A).adjoint e₀ 1 at he
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint] at he
    norm_num [hJ₁, A, e₀, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Matrix.conjTranspose_apply] at he
  · intro hu
    have h := hu.1 e₁ e₀
    change inner ℂ (J e₀) (J e₁) = inner ℂ e₀ e₁ at h
    rw [he₀, he₁] at h
    norm_num [e₀, e₁, PiLp.inner_apply, Fin.sum_univ_two] at h
  · norm_num [A, PiLp.inner_apply, Fin.sum_univ_two]

end D05.M13.UnitarySpectrum
