import MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Symmetric.Grading
import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Symmetric.Polynomial

namespace Alg01SymmetricWitt.Symmetric.Polynomial

open Module
open Alg01SymmetricWitt.Symmetric.Algebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {r : ℕ}

/-- The symmetric algebra of a module with basis `b` is the polynomial algebra on that basis. -/
noncomputable abbrev equivMvPolynomial (b : Basis (Fin r) R M) :
    SymmetricAlgebra R M ≃ₐ[R] MvPolynomial (Fin r) R :=
  SymmetricAlgebra.equivMvPolynomial b

@[simp] theorem equivMvPolynomial_ι (b : Basis (Fin r) R M) (i : Fin r) :
    equivMvPolynomial b (SymmetricAlgebra.ι R M (b i)) = MvPolynomial.X i :=
  SymmetricAlgebra.equivMvPolynomial_ι_apply b i

@[simp] theorem equivMvPolynomial_symm_X (b : Basis (Fin r) R M) (i : Fin r) :
    (equivMvPolynomial b).symm (MvPolynomial.X i) = SymmetricAlgebra.ι R M (b i) :=
  SymmetricAlgebra.equivMvPolynomial_symm_X b i

private theorem image_ι_isHomogeneous (b : Basis (Fin r) R M) (x : M) :
    (equivMvPolynomial b (SymmetricAlgebra.ι R M x)).IsHomogeneous 1 := by
  change SymmetricAlgebra.lift (b.constr R MvPolynomial.X) (SymmetricAlgebra.ι R M x) ∈
    MvPolynomial.homogeneousSubmodule (Fin r) R 1
  rw [SymmetricAlgebra.lift_ι_apply, MvPolynomial.homogeneousSubmodule_one_eq_span_X,
    ← Basis.constr_range b R]
  exact LinearMap.mem_range_self _ x

private theorem image_degree_mem (b : Basis (Fin r) R M) (n : ℕ)
    {x : SymmetricAlgebra R M} (hx : x ∈ degree R M n) :
    equivMvPolynomial b x ∈ MvPolynomial.homogeneousSubmodule (Fin r) R n := by
  obtain ⟨t, rfl⟩ := hx
  let p := MvPolynomial.homogeneousSubmodule (Fin r) R n
  change equivMvPolynomial b (degreeMap R M n t) ∈ p
  induction t using PiTensorProduct.induction_on with
  | smul_tprod a t =>
    rw [map_smul, map_smul, Grading.degreeMap_tprod, map_prod]
    apply p.smul_mem
    change (∏ i, equivMvPolynomial b (SymmetricAlgebra.ι R M (t i))).IsHomogeneous n
    simpa using MvPolynomial.IsHomogeneous.prod Finset.univ
      (fun i => equivMvPolynomial b (SymmetricAlgebra.ι R M (t i)))
      (fun _ => 1) (fun i _ => image_ι_isHomogeneous b (t i))
  | add t u ht hu =>
    rw [map_add, map_add]
    exact p.add_mem ht hu

private theorem symm_image_degree_mem (b : Basis (Fin r) R M) (n : ℕ)
    {p : MvPolynomial (Fin r) R} (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin r) R n) :
    (equivMvPolynomial b).symm p ∈ degree R M n := by
  change p.IsHomogeneous n at hp
  rw [p.as_sum, map_sum]
  refine (degree R M n).sum_mem fun d hd => ?_
  have hdegree := hp.degree_eq_sum_deg_support hd
  rw [MvPolynomial.monomial_eq, map_mul, Finsupp.prod, map_prod]
  rw [show MvPolynomial.C (p.coeff d) = algebraMap R _ (p.coeff d) from rfl,
    AlgEquiv.commutes, ← Algebra.smul_def]
  refine (degree R M n).smul_mem _ ?_
  rw [hdegree]
  simpa only [map_pow, equivMvPolynomial_symm_X, smul_eq_mul, mul_one] using
    SetLike.prod_pow_mem_graded (degree R M) (fun _ : Fin r => (1 : ℕ))
      (fun i => SymmetricAlgebra.ι R M (b i)) (F := d.support) d
      (fun i _ => Grading.degreeOneEquiv_coe R M (b i) ▸ (Grading.degreeOneEquiv R M (b i)).property)

/-- The algebra equivalence carries each symmetric degree onto the polynomial degree. -/
theorem map_degree (b : Basis (Fin r) R M) (n : ℕ) :
    (degree R M n).map (equivMvPolynomial b).toLinearMap =
      MvPolynomial.homogeneousSubmodule (Fin r) R n := by
  ext p
  change (∃ x ∈ degree R M n, equivMvPolynomial b x = p) ↔ _
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact image_degree_mem b n hx
  · intro hp
    exact ⟨(equivMvPolynomial b).symm p, symm_image_degree_mem b n hp,
      (equivMvPolynomial b).apply_symm_apply p⟩

/-- The restriction of the algebra equivalence to degree `n`. -/
noncomputable def degreeEquiv (b : Basis (Fin r) R M) (n : ℕ) :
    degree R M n ≃ₗ[R] MvPolynomial.homogeneousSubmodule (Fin r) R n :=
  (equivMvPolynomial b).toLinearEquiv.ofSubmodules _ _ (map_degree b n)

@[simp] theorem degreeEquiv_apply (b : Basis (Fin r) R M) (n : ℕ) (x : degree R M n) :
    (degreeEquiv b n x : MvPolynomial (Fin r) R) = equivMvPolynomial b x :=
  rfl

@[simp] theorem degreeEquiv_symm_apply (b : Basis (Fin r) R M) (n : ℕ)
    (p : MvPolynomial.homogeneousSubmodule (Fin r) R n) :
    ((degreeEquiv b n).symm p : SymmetricAlgebra R M) = (equivMvPolynomial b).symm p :=
  rfl

end Alg01SymmetricWitt.Symmetric.Polynomial
