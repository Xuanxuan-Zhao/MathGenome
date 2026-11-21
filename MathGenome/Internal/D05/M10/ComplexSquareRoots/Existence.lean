import MathGenome.Internal.Specs.D05.M10.ComplexSquareRoots.Existence
import MathGenome.Internal.D05.M10.ComplexSquareRoots
import MathGenome.Internal.D05.M10.GeneralizedDecomposition
import MathGenome.Internal.D05.Foundations.ComplexRoots
import MathGenome.Internal.D05.Foundations.Fta
import Mathlib.Algebra.Module.Submodule.EqLocus

noncomputable section
namespace D05.M10.ComplexSquareRoots.Existence

/-- Scalar rescaling of the upstream finite nilpotent polynomial construction. -/
theorem scalar_add_nilpotent_square_root {V : Type*} [AddCommGroup V] [Module ℂ V]
    (Q : Module.End ℂ V) (hQ : IsNilpotent Q) (μ : ℂ) (hμ : μ ≠ 0) :
    ∃ R : Module.End ℂ V, R ^ 2 = μ • 1 + Q := by
  obtain ⟨r, hr, hQr⟩ := (D05.M10.Nilpotent.nilpotent_iff_positive_power Q).mp hQ
  have hscaled : (μ⁻¹ • Q) ^ r = 0 := by rw [smul_pow, hQr, smul_zero]
  obtain ⟨q, _, hq⟩ := D05.M10.ComplexSquareRoots.exists_polynomial_square_root
    ℂ V (μ⁻¹ • Q) r (by omega) hscaled
  obtain ⟨c, hc⟩ := D05.Foundations.ComplexRoots.complexRoot μ 2 (by decide)
  refine ⟨c • Polynomial.aeval (μ⁻¹ • Q) q, ?_⟩
  rw [smul_pow, hc, hq, smul_add, smul_smul, mul_inv_cancel₀ hμ, one_smul]

/-- Transport component roots through the canonical internal-sum isomorphism. -/
theorem square_root_of_internal {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [DecidableEq ι] (U : ι → Submodule K V)
    (hU : DirectSum.IsInternal U) (T : Module.End K V)
    (A : ∀ i, Module.End K (U i))
    (hA : ∀ i (x : U i), (((A i) ^ 2) x : V) = T x) :
    ∃ R : Module.End K V, R ^ 2 = T := by
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap U) hU
  let B := DirectSum.lmap A
  let R : Module.End K V := e.toLinearMap ∘ₗ B ∘ₗ e.symm.toLinearMap
  have hR (i : ι) (x : U i) : R (x : V) = (A i x : V) := by
    have hx : e (DirectSum.lof K ι (fun i => U i) i x) = (x : V) := by
      exact DirectSum.coeLinearMap_lof U i x
    rw [← hx]
    simp only [R, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, B, DirectSum.lmap_lof]
    exact DirectSum.coeLinearMap_lof U i (A i x)
  refine ⟨R, ?_⟩
  apply LinearMap.eqLocus_eq_top.mp
  apply top_unique
  rw [← hU.submodule_iSup_eq_top]
  apply iSup_le
  intro i x hx
  let u : U i := ⟨x, hx⟩
  change R (R (u : V)) = T u
  rw [hR, hR]
  exact hA i u

theorem exists_square_root : Specs.D05.M10.ComplexSquareRoots.Existence.exists_square_root := by
  intro V _ _ _ T hT
  classical
  let U := fun μ : spectrum ℂ T => T.genEigenspace μ.val (Module.finrank ℂ V)
  have hU : DirectSum.IsInternal U :=
    D05.M10.GeneralizedDecomposition.decomposition T (D05.Foundations.Fta.splits _)
  have hroots (μ : spectrum ℂ T) :
      ∃ R : Module.End ℂ (U μ), ∀ x : U μ, ((R ^ 2) x : V) = T x := by
    have hμ : μ.val ≠ 0 := by
      intro hz
      exact spectrum.zero_notMem ℂ hT (hz ▸ μ.property)
    obtain ⟨hTμ, hQ, hdecomp, r, hr, hQr⟩ :=
      D05.M10.GeneralizedDecomposition.summand_structure T μ
    obtain ⟨R, hR⟩ := scalar_add_nilpotent_square_root
      ((T - μ.val • 1).restrict hQ) ⟨r, hQr⟩ μ.val hμ
    refine ⟨R, ?_⟩
    intro x
    have heq : R ^ 2 = T.restrict hTμ := by
      rw [hdecomp]
      exact hR
    exact congrArg Subtype.val (LinearMap.congr_fun heq x)
  choose A hA using hroots
  exact square_root_of_internal U hU T A hA

theorem identity_roots : Specs.D05.M10.ComplexSquareRoots.Existence.identity_roots := by
  intro V _ _ _
  refine ⟨by simp, by simp, ?_⟩
  intro h
  have hc : (1 : ℂ) = -1 := (algebraMap ℂ (Module.End ℂ V)).injective (by simpa using h)
  norm_num at hc

theorem zero_space : Specs.D05.M10.ComplexSquareRoots.Existence.zero_space := by
  intro V _ _ _ T
  exact Subsingleton.elim _ _

/-- Commutation with its square forces a putative root of this Jordan block
into the upper triangular form with equal diagonal entries. -/
theorem jordan_no_root : Specs.D05.M10.ComplexSquareRoots.Existence.jordan_no_root := by
  rintro ⟨R, hR⟩
  have hcomm : R * !![0, 1; 0, 0] = !![0, 1; 0, 0] * R := by
    rw [← hR]
    simp only [pow_two, mul_assoc]
  have h21 : R 1 0 = 0 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hcomm
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h.symm
  have hdiag : R 0 0 = R 1 1 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hcomm
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have hsquare : (R 0 0) ^ 2 = 0 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hR
    simpa [pow_two, Matrix.mul_apply, Fin.sum_univ_two, h21] using h
  have ha : R 0 0 = 0 := sq_eq_zero_iff.mp hsquare
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hR
  simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, ← hdiag, ha] at h

theorem singular_operator_no_root :
    Specs.D05.M10.ComplexSquareRoots.Existence.singular_operator_no_root := by
  let J : Module.End ℂ (Fin 2 → ℂ) := Matrix.toLin' !![0, 1; 0, 0]
  change ¬ IsUnit J ∧ ¬ ∃ R : Module.End ℂ (Fin 2 → ℂ), R ^ 2 = J
  have hn : ¬ ∃ R : Module.End ℂ (Fin 2 → ℂ), R ^ 2 = J := by
    rintro ⟨R, hR⟩
    apply jordan_no_root
    refine ⟨LinearMap.toMatrixAlgEquiv' R, ?_⟩
    rw [← map_pow, hR]
    exact LinearMap.toMatrix'_toLin' _
  refine ⟨?_, hn⟩
  intro hJ
  exact hn (exists_square_root (Fin 2 → ℂ) J hJ)

end D05.M10.ComplexSquareRoots.Existence
