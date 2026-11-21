import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.HenselFactorStep
import Mathlib.RingTheory.Henselian

universe u
namespace P103.Ch07.HenselFactorStep
open Polynomial

/-- Unit resultant gives bijectivity of the bounded correction map.
The adjugate identities apply even when either degree is zero. -/
theorem sylvesterMap_bijective {R : Type u} [CommRing R] (g h : R[X])
    (hu : IsUnit (Polynomial.resultant g h)) :
    Function.Bijective (sylvesterMap g h le_rfl le_rfl) := by
  obtain ⟨u, hu⟩ := hu
  let T := sylvesterMap g h le_rfl le_rfl
  let S := adjSylvester (m := g.natDegree) (n := h.natDegree) g h
  have hST (x) : S (T x) = Polynomial.resultant g h • x := by
    exact DFunLike.congr_fun (adjSylvester_comp_sylvesterMap g h le_rfl le_rfl) x
  have hTS (x) : T (S x) = Polynomial.resultant g h • x := by
    exact DFunLike.congr_fun (sylvesterMap_comp_adjSylvester g h le_rfl le_rfl) x
  let inv := fun x => (↑(u⁻¹) : R) • S x
  have hl : Function.LeftInverse inv T := by
    intro x
    change (↑(u⁻¹) : R) • S (T x) = x
    rw [hST, ← hu, smul_smul]
    simp
  have hr : Function.RightInverse inv T := by
    intro x
    change T ((↑(u⁻¹) : R) • S x) = x
    rw [map_smul, hTS, ← hu, smul_smul]
    simp
  exact ⟨hl.injective, hr.surjective⟩

/-- Coprimality of monic polynomials lifts across an ideal in the Jacobson radical. -/
theorem coprime_of_coprime_reduction {R : Type u} [CommRing R] (I : Ideal R)
    (hI : I ≤ Ideal.jacobson ⊥) (g h : R[X]) (hg : g.Monic) (hh : h.Monic)
    (hcop : IsCoprime (g.map (Ideal.Quotient.mk I)) (h.map (Ideal.Quotient.mk I))) :
    IsCoprime g h := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨0, 0, Subsingleton.elim _ _⟩
  have hItop : I ≠ ⊤ := by
    intro he
    have hj : Ideal.jacobson (⊥ : Ideal R) = ⊤ := top_le_iff.mp (he ▸ hI)
    have hb : (⊥ : Ideal R) = ⊤ := Ideal.jacobson_eq_top_iff.mp hj
    exact bot_ne_top hb
  letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  letI : IsLocalHom (Ideal.Quotient.mk I) := isLocalHom_of_le_jacobson_bot I hI
  apply (isUnit_resultant_iff_isCoprime hg).mp
  apply isUnit_of_map_unit (Ideal.Quotient.mk I)
  have hu := (isUnit_resultant_iff_isCoprime (hg.map (Ideal.Quotient.mk I))).mpr hcop
  rwa [hg.natDegree_map, hh.natDegree_map, resultant_map_map] at hu

/-- Bounded coefficient vectors expand in the monomial basis, so every output
coefficient is a finite linear combination of input coefficients. -/
theorem bounded_linearMap_preserves_coefficients :
    P103.Specs.Ch07.HenselFactorStep.bounded_linearMap_preserves_coefficientsType.{u} := by
  intro R _ J d T p hp k
  rw [← (degreeLT.basis R d).sum_repr p, map_sum, finsetSum_coeff]
  apply J.sum_mem
  intro i _
  simp only [map_smul, coeff_smul, smul_eq_mul, degreeLT.basis_repr]
  exact J.mul_mem_right _ (hp i)

/-- One Newton correction cancels the linear error; the remaining error is quadratic. -/
theorem factor_step : P103.Specs.Ch07.HenselFactorStep.factor_stepType.{u} := by
  intro R _ I hI n f g h hf hg hh hdeg hcop herr
  rcases subsingleton_or_nontrivial R with hR | hR
  · refine ⟨g, h, hg, hh, rfl, rfl, ?_, ?_, ?_⟩
    · intro k
      simp only [sub_self, coeff_zero]
      exact (I ^ (n + 1)).zero_mem
    · intro k
      simp only [sub_self, coeff_zero]
      exact (I ^ (n + 1)).zero_mem
    · intro k
      rw [Subsingleton.elim ((f - g * h).coeff k) 0]
      exact (I ^ (n + 2)).zero_mem
  have hgh : (g * h).Monic := hg.mul hh
  have hdeg' : f.degree = (g * h).degree := by
    rw [degree_eq_natDegree hf.ne_zero, degree_eq_natDegree hgh.ne_zero,
      hg.natDegree_mul hh, hdeg]
  have hE : f - g * h ∈ degreeLT R (g.natDegree + h.natDegree) := by
    rw [mem_degreeLT, ← hdeg, ← degree_eq_natDegree hf.ne_zero]
    exact degree_sub_lt_left hdeg' hf.ne_zero (hf.trans hgh.symm)
  let E : degreeLT R (g.natDegree + h.natDegree) := ⟨f - g * h, hE⟩
  have hc : IsCoprime g h := coprime_of_coprime_reduction I hI g h hg hh hcop
  let e := LinearEquiv.ofBijective (sylvesterMap g h le_rfl le_rfl)
    (sylvesterMap_bijective g h ((isUnit_resultant_iff_isCoprime hg).mpr hc))
  let ab := e.symm E
  let a : R[X] := ab.1.val
  let b : R[X] := ab.2.val
  have hcorr : g * b + h * a = f - g * h := by
    exact congrArg Subtype.val (e.apply_symm_apply E)
  let A : degreeLT R (g.natDegree + h.natDegree) →ₗ[R] R[X] :=
    (degreeLT R g.natDegree).subtype.comp
      ((LinearMap.fst R _ _).comp e.symm.toLinearMap)
  let B : degreeLT R (g.natDegree + h.natDegree) →ₗ[R] R[X] :=
    (degreeLT R h.natDegree).subtype.comp
      ((LinearMap.snd R _ _).comp e.symm.toLinearMap)
  have ha : ∀ k, a.coeff k ∈ I ^ (n + 1) :=
    bounded_linearMap_preserves_coefficients (I ^ (n + 1)) _ A E herr
  have hb : ∀ k, b.coeff k ∈ I ^ (n + 1) :=
    bounded_linearMap_preserves_coefficients (I ^ (n + 1)) _ B E herr
  have had : a.degree < g.degree := by
    rw [degree_eq_natDegree hg.ne_zero]
    exact mem_degreeLT.mp ab.1.property
  have hbd : b.degree < h.degree := by
    rw [degree_eq_natDegree hh.ne_zero]
    exact mem_degreeLT.mp ab.2.property
  refine ⟨g + a, h + b, hg.add_of_left had, hh.add_of_left hbd,
    natDegree_add_eq_left_of_degree_lt had, natDegree_add_eq_left_of_degree_lt hbd,
    ?_, ?_, ?_⟩
  · simpa only [add_sub_cancel_left] using ha
  · simpa only [add_sub_cancel_left] using hb
  · have heq : f - (g + a) * (h + b) = -(a * b) := by
      linear_combination -hcorr
    intro k
    rw [heq, coeff_neg]
    apply (I ^ (n + 2)).neg_mem
    apply Ideal.pow_le_pow_right (I := I) (show n + 2 ≤ (n + 1) + (n + 1) by omega)
    rw [pow_add, coeff_mul]
    apply (I ^ (n + 1) * I ^ (n + 1)).sum_mem
    intro ij _
    exact Ideal.mul_mem_mul (ha ij.1) (hb ij.2)

end P103.Ch07.HenselFactorStep
