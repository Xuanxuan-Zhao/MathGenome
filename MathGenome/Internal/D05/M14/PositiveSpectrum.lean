import MathGenome.Internal.Specs.D05.M14.PositiveSpectrum
import MathGenome.Internal.D05.M14.Positive
import MathGenome.Internal.D05.M13.AdjointLaws

noncomputable section

namespace D05.M14.PositiveSpectrum

open Module.End

variable {F V : Type*} [RCLike F] [NormedAddCommGroup V]
  [InnerProductSpace F V] [FiniteDimensional F V]

/-- The spectral quadratic expansion, with finite support and real weights. -/
theorem quadratic_expansion (T : V →ₗ[F] V) (hs : T.IsSymmetric) (v : V) :
    RCLike.re (D05.firstInner (F := F) (T v) v) =
      ∑ i, hs.eigenvalues rfl i * ‖(hs.eigenvectorBasis rfl).repr v i‖ ^ 2 := by
  let b := hs.eigenvectorBasis rfl
  have he : ∀ i, b.repr (T v) i = (hs.eigenvalues rfl i : F) * b.repr v i :=
    hs.eigenvectorBasis_apply_self_apply rfl v
  change RCLike.re (inner F v (T v)) = _
  rw [← b.repr.inner_map_map, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, he, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change RCLike.re (((hs.eigenvalues rfl i : F) * b.repr v i) *
    starRingEnd F (b.repr v i)) = _
  rw [mul_assoc, RCLike.mul_conj, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul,
    RCLike.ofReal_re]

theorem eigenvalues_real : Specs.D05.M14.PositiveSpectrum.eigenvalues_real := by
  intro F V _ _ _ _ T hT μ hμ
  have hs := (D05.M13.SelfAdjoint.selfAdjoint_iff_isSymmetric T).mp hT
  exact RCLike.conj_eq_iff_re.mp (hs.conj_eigenvalue_eq_self hμ)

theorem semidefinite_iff_eigenvalues :
    Specs.D05.M14.PositiveSpectrum.semidefinite_iff_eigenvalues := by
  intro F V _ _ _ _ T hT
  have hs := (D05.M13.SelfAdjoint.selfAdjoint_iff_isSymmetric T).mp hT
  constructor
  · intro hp μ hμ
    have hμ' : HasEigenvalue T (RCLike.re μ : F) := by
      rwa [eigenvalues_real T hT μ hμ]
    exact eigenvalue_nonneg_of_nonneg hμ' hp.2
  · intro h
    refine ⟨hT, fun v => ?_⟩
    rw [quadratic_expansion T hs v]
    apply Finset.sum_nonneg
    intro i _
    have hi := h _ (hs.hasEigenvalue_eigenvalues rfl i)
    simp only [RCLike.ofReal_re] at hi
    exact mul_nonneg hi (sq_nonneg _)

theorem definite_iff_eigenvalues :
    Specs.D05.M14.PositiveSpectrum.definite_iff_eigenvalues := by
  intro F V _ _ _ _ T hT
  have hs := (D05.M13.SelfAdjoint.selfAdjoint_iff_isSymmetric T).mp hT
  constructor
  · intro hp μ hμ
    have hμ' : HasEigenvalue T (RCLike.re μ : F) := by
      rwa [eigenvalues_real T hT μ hμ]
    exact eigenvalue_pos_of_pos hμ' hp.2
  · intro h
    refine ⟨hT, fun v hv => ?_⟩
    rw [quadratic_expansion T hs v]
    have hi : ∀ i, 0 < hs.eigenvalues rfl i := by
      intro i
      simpa using h _ (hs.hasEigenvalue_eigenvalues rfl i)
    have hn : ∃ i, (hs.eigenvectorBasis rfl).repr v i ≠ 0 := by
      by_contra! hz
      apply hv
      rw [← (hs.eigenvectorBasis rfl).sum_repr v]
      simp [hz]
    obtain ⟨i, hi'⟩ := hn
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hi j).le (sq_nonneg _))
      ⟨i, Finset.mem_univ _, mul_pos (hi i) (sq_pos_of_pos (norm_pos_iff.mpr hi'))⟩

theorem adjoint_comp_positive : Specs.D05.M14.PositiveSpectrum.adjoint_comp_positive := by
  intro F V W _ _ _ _ _ _ _ R
  exact (D05.M14.Positive.positiveSemidefinite_iff_mathlib _).mpr
    (LinearMap.isPositive_adjoint_comp_self R)

theorem adjoint_comp_quadratic : Specs.D05.M14.PositiveSpectrum.adjoint_comp_quadratic := by
  intro F V W _ _ _ _ _ _ _ R v
  change inner F v (LinearMap.adjoint R (R v)) = _
  rw [LinearMap.adjoint_inner_right]
  simpa only [RCLike.ofReal_pow] using inner_self_eq_norm_sq_to_K (𝕜 := F) (R v)

/-- Real diagonal maps are self-adjoint in an orthonormal basis. -/
theorem selfAdjoint_of_real_diagonal {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι F V) (R : V →ₗ[F] V) (a : ι → ℝ)
    (ha : ∀ i, R (b i) = (a i : F) • b i) : D05.selfAdjoint R := by
  classical
  have hm : R.toMatrix b.toBasis b.toBasis = Matrix.diagonal (fun i => (a i : F)) := by
    ext i j
    by_cases hij : i = j <;>
      simp [LinearMap.toMatrix_apply, ha, hij, RCLike.real_smul_eq_coe_mul]
  apply (D05.M13.SelfAdjoint.selfAdjoint_iff_isSymmetric R).mpr
  apply (LinearMap.isHermitian_toMatrix_iff b).mp
  rw [hm]
  apply Matrix.isHermitian_diagonal_of_self_adjoint
  ext i
  simp

theorem semidefinite_iff_factorization :
    Specs.D05.M14.PositiveSpectrum.semidefinite_iff_factorization := by
  intro F V _ _ _ _ T
  constructor
  · intro hp
    classical
    have hm := (D05.M14.Positive.positiveSemidefinite_iff_mathlib T).mp hp
    let hs := hm.isSymmetric
    let b := hs.eigenvectorBasis rfl
    let a := fun i => Real.sqrt (hs.eigenvalues rfl i)
    let R := b.toBasis.constr F (fun i => (a i : F) • b i)
    have hR : ∀ i, R (b i) = (a i : F) • b i := by
      intro i
      exact b.toBasis.constr_basis F _ i
    have hsa := selfAdjoint_of_real_diagonal b R a hR
    refine ⟨R, ?_⟩
    rw [← hsa]
    apply b.toBasis.ext
    intro i
    change T (b i) = R (R (b i))
    rw [hs.apply_eigenvectorBasis rfl, hR, map_smul, hR, smul_smul,
      ← RCLike.ofReal_mul, Real.mul_self_sqrt (hm.nonneg_eigenvalues rfl i)]
  · rintro ⟨R, rfl⟩
    exact adjoint_comp_positive R

theorem definite_iff_invertible : Specs.D05.M14.PositiveSpectrum.definite_iff_invertible := by
  intro F V _ _ _ _ T hp
  constructor
  · intro hd
    rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra hn
    have h := hd.2 v hn
    simp [hv, D05.firstInner] at h
  · intro hu
    apply (definite_iff_eigenvalues T hp.1).mpr
    intro μ hμ
    have hn := (semidefinite_iff_eigenvalues T hp.1).mp hp μ hμ
    apply lt_of_le_of_ne hn
    intro hz
    have hm : μ = 0 := by
      rw [← eigenvalues_real T hp.1 μ hμ, ← hz]
      simp
    obtain ⟨v, hv, hvn⟩ := hμ.exists_hasEigenvector
    have hzv : T v = 0 := by
      simpa [hm] using mem_eigenspace_iff.mp hv
    exact hvn ((LinearMap.ker_eq_bot'.mp
      ((LinearMap.isUnit_iff_ker_eq_bot T).mp hu)) v hzv)

end D05.M14.PositiveSpectrum
