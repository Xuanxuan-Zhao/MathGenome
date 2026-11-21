import MathGenome.Internal.Specs.D05.M15.SymmetricBasis
import MathGenome.Internal.D05.M15.Symmetric
import MathGenome.Internal.D05.Foundations.FormalPolynomials
import MathGenome.Internal.D05.Foundations.StarsBars

noncomputable section
namespace D05.M15.SymmetricBasis
open Specs.D05.M15.Symmetric
open D05.Foundations

abbrev powerInclusion := @Specs.D05.M15.SymmetricBasis.powerInclusion
abbrev polynomialEquiv := @Specs.D05.M15.SymmetricBasis.polynomialEquiv

theorem inclusion_elementary : Specs.D05.M15.SymmetricBasis.inclusion_elementary := by
  intro K V _ _ _ p x
  exact D05.M15.Symmetric.homogeneousMap_tprod p x

theorem inclusion_injective : Specs.D05.M15.SymmetricBasis.inclusion_injective := by
  intro K V _ _ _ p
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.ker_liftQ_eq_bot
  exact (D05.M15.Symmetric.homogeneous_kernel p).le

theorem polynomial_generators : Specs.D05.M15.SymmetricBasis.polynomial_generators := by
  intro K V _ _ _ n b i
  exact ⟨_root_.SymmetricAlgebra.equivMvPolynomial_ι_apply b i,
    _root_.SymmetricAlgebra.equivMvPolynomial_symm_X b i⟩

theorem polynomial_monomials : Specs.D05.M15.SymmetricBasis.polynomial_monomials := by
  intro K V _ _ _ n b a
  simp only [map_prod, map_pow, (polynomial_generators b _).1]
  rw [MvPolynomial.monic_monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
  rfl

section Degree
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {n : ℕ} (b : Module.Basis (Fin n) K V)

/-- The degree-p tensor map followed by the polynomial coordinate isomorphism. -/
def tensorPolynomialMap (p : ℕ) : TensorPower K p V →ₗ[K] MvPolynomial (Fin n) K :=
  (polynomialEquiv b).toLinearMap.comp (homogeneousMap K V p)

@[simp] theorem tensorPolynomialMap_tprod (p : ℕ) (x : Fin p → V) :
    tensorPolynomialMap b p (PiTensorProduct.tprod K x) =
      ∏ i, polynomialEquiv b (_root_.SymmetricAlgebra.ι K V (x i)) := by
  change polynomialEquiv b (homogeneousMap K V p (PiTensorProduct.tprod K x)) = _
  rw [D05.M15.Symmetric.homogeneousMap_tprod, map_prod]

/-- Multiplication of homogeneous tensor images concatenates their tensors. -/
theorem polynomialRange_mul (p q : ℕ) :
    LinearMap.range (tensorPolynomialMap b p) *
      LinearMap.range (tensorPolynomialMap b q) ≤
      LinearMap.range (tensorPolynomialMap b (p+q)) := by
  apply Submodule.mul_le.mpr
  rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩
  refine ⟨(TensorPower.mulEquiv (R := K) (M := V)) (x ⊗ₜ[K] y), ?_⟩
  change polynomialEquiv b (_root_.SymmetricAlgebra.algHom K V
    (TensorPower.toTensorAlgebra _)) = _
  rw [← TensorPower.gMul_def, TensorPower.toTensorAlgebra_gMul, map_mul, map_mul]
  rfl

theorem generator_polynomial_homogeneous (v : V) :
    (polynomialEquiv b (_root_.SymmetricAlgebra.ι K V v)).IsHomogeneous 1 := by
  let f := (polynomialEquiv b).toLinearMap.comp (_root_.SymmetricAlgebra.ι K V)
  have hf : f = b.constr K (MvPolynomial.X : Fin n → MvPolynomial (Fin n) K) := by
    apply b.ext
    intro i
    exact (polynomial_generators b i).1.trans (b.constr_basis K _ i).symm
  have hr : LinearMap.range f = MvPolynomial.homogeneousSubmodule (Fin n) K 1 := by
    rw [hf, b.constr_range, MvPolynomial.homogeneousSubmodule_one_eq_span_X]
  change f v ∈ MvPolynomial.homogeneousSubmodule (Fin n) K 1
  rw [← hr]
  exact ⟨v,rfl⟩

/-- The full range computation; the reverse inclusion uses products of the
linear coordinate variables and requires no averaging. -/
theorem polynomialRange_eq (p : ℕ) :
    LinearMap.range (tensorPolynomialMap b p) =
      MvPolynomial.homogeneousSubmodule (Fin n) K p := by
  apply le_antisymm
  · rintro _ ⟨t,rfl⟩
    induction t using PiTensorProduct.induction_on with
    | smul_tprod c x =>
      rw [map_smul, tensorPolynomialMap_tprod]
      apply Submodule.smul_mem
      simpa using MvPolynomial.IsHomogeneous.prod Finset.univ
        (fun i => polynomialEquiv b (_root_.SymmetricAlgebra.ι K V (x i)))
        (fun _ => 1) (fun i _ => generator_polynomial_homogeneous b (x i))
    | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  · have h1 : MvPolynomial.homogeneousSubmodule (Fin n) K 1 ≤
        LinearMap.range (tensorPolynomialMap b 1) := by
      rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X]
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      refine ⟨PiTensorProduct.tprod K (fun _ : Fin 1 => b i), ?_⟩
      simp [tensorPolynomialMap_tprod, (polynomial_generators b i).1]
    rw [← MvPolynomial.homogeneousSubmodule_one_pow]
    induction p with
    | zero =>
      apply Submodule.one_le.mpr
      refine ⟨PiTensorProduct.tprod K (fun i : Fin 0 => Fin.elim0 i), ?_⟩
      simp
    | succ p ih =>
      rw [pow_succ]
      exact (mul_le_mul' ih h1).trans (polynomialRange_mul b p 1)

/-- The quotient polynomial map has exactly the required homogeneous range. -/
theorem quotientPolynomialRange_eq (p : ℕ) :
    LinearMap.range ((polynomialEquiv b).toLinearMap.comp
      (powerInclusion (K := K) (V := V) p)) =
      MvPolynomial.homogeneousSubmodule (Fin n) K p := by
  rw [LinearMap.range_comp]
  change Submodule.map (polynomialEquiv b).toLinearMap
    (LinearMap.range ((adjacentRelations K V p).liftQ (homogeneousMap K V p) _)) = _
  erw [Submodule.range_liftQ]
  rw [← LinearMap.range_comp]
  exact polynomialRange_eq b p

/-- Explicit restriction of the algebra isomorphism to the degreewise quotient. -/
def powerPolynomialEquiv (p : ℕ) :
    symmetricPower K V p ≃ₗ[K] MvPolynomial.homogeneousSubmodule (Fin n) K p :=
  (LinearEquiv.ofInjective
    ((polynomialEquiv b).toLinearMap.comp (powerInclusion (K := K) (V := V) p))
    ((polynomialEquiv b).injective.comp (inclusion_injective p))).trans
    (LinearEquiv.ofEq _ _ (quotientPolynomialRange_eq b p))

@[simp] theorem powerPolynomialEquiv_apply (p : ℕ) (q : symmetricPower K V p) :
    (powerPolynomialEquiv b p q : MvPolynomial (Fin n) K) =
      polynomialEquiv b (powerInclusion (K := K) (V := V) p q) := rfl

end Degree

theorem graded_equiv : Specs.D05.M15.SymmetricBasis.graded_equiv := by
  intro K V _ _ _ n b p
  exact ⟨powerPolynomialEquiv b p, powerPolynomialEquiv_apply b p⟩

/-- The exponent reindexing uses actual nonnegative tuples of the stated total. -/
def degreeTuplesEquiv (n p : ℕ) :
    {d : Fin n →₀ ℕ // d.degree = p} ≃ NonnegativeTuples n p where
  toFun d := ⟨exponentEquiv n d.val, by
    change ∑ i, d.val i = p
    rw [← Finsupp.degree_eq_sum]
    exact d.property⟩
  invFun a := ⟨(exponentEquiv n).symm a.val, by
    rw [Finsupp.degree_eq_sum]
    change ∑ i, a.val i = p
    exact a.property⟩
  left_inv d := Subtype.ext ((exponentEquiv n).symm_apply_apply d.val)
  right_inv a := Subtype.ext ((exponentEquiv n).apply_symm_apply a.val)

/-- Coefficient-array monomials give a basis of each homogeneous submodule. -/
def polynomialDegreeBasis (K : Type*) [Field K] (n p : ℕ) :
    Module.Basis (NonnegativeTuples n p) K
      (MvPolynomial.homogeneousSubmodule (Fin n) K p) :=
  ((MvPolynomial.basisRestrictSupport K {d : Fin n →₀ ℕ | d.degree = p}).map
    (LinearEquiv.ofEq _ _ (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported
      (Fin n) K p).symm)).reindex (degreeTuplesEquiv n p)

@[simp] theorem polynomialDegreeBasis_apply (K : Type*) [Field K] (n p : ℕ)
    (a : NonnegativeTuples n p) :
    (polynomialDegreeBasis K n p a : MvPolynomial (Fin n) K) =
      MvPolynomial.monomial ((exponentEquiv n).symm a.val) 1 := by
  classical
  rw [polynomialDegreeBasis, Module.Basis.reindex_apply, Module.Basis.map_apply]
  erw [LinearEquiv.coe_ofEq_apply]
  change (((MvPolynomial.basisRestrictSupport K {d : Fin n →₀ ℕ | d.degree = p})
    ((degreeTuplesEquiv n p).symm a)) : MvPolynomial (Fin n) K) = _
  change AddMonoidAlgebra.ofCoeff
    (↑((Finsupp.supportedEquivFinsupp (M := K) (R := K)
      {d : Fin n →₀ ℕ | d.degree = p}).symm
      (Finsupp.single ((degreeTuplesEquiv n p).symm a) 1)) : (Fin n →₀ ℕ) →₀ K) = _
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

/-- A concrete basis of the original quotient, transported through the graded
isomorphism rather than defined on an unrelated polynomial model. -/
def monomialBasis {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (p : ℕ) :
    Module.Basis (NonnegativeTuples n p) K (symmetricPower K V p) :=
  (polynomialDegreeBasis K n p).map (powerPolynomialEquiv b p).symm

@[simp] theorem monomialBasis_inclusion {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] {n : ℕ} (b : Module.Basis (Fin n) K V)
    (p : ℕ) (a : NonnegativeTuples n p) :
    powerInclusion (K := K) (V := V) p (monomialBasis b p a) =
      ∏ i, (_root_.SymmetricAlgebra.ι K V (b i)) ^ a.val i := by
  apply (polynomialEquiv b).injective
  rw [polynomial_monomials]
  rw [← powerPolynomialEquiv_apply]
  change ((powerPolynomialEquiv b p)
    ((powerPolynomialEquiv b p).symm (polynomialDegreeBasis K n p a)) :
      MvPolynomial (Fin n) K) = _
  rw [LinearEquiv.apply_symm_apply, polynomialDegreeBasis_apply]

theorem monomial_basis : Specs.D05.M15.SymmetricBasis.monomial_basis := by
  intro K V _ _ _ n b p
  exact ⟨monomialBasis b p, monomialBasis_inclusion b p⟩

theorem dimension : Specs.D05.M15.SymmetricBasis.dimension := by
  intro K V _ _ _ n b p hn
  rw [Module.finrank_eq_nat_card_basis (monomialBasis b p)]
  exact D05.Foundations.StarsBars.stars_bars n p hn

theorem zero_space_degree_zero : Specs.D05.M15.SymmetricBasis.zero_space_degree_zero := by
  intro K V _ _ _ b
  constructor
  · rw [Module.finrank_eq_nat_card_basis (monomialBasis b 0)]
    exact D05.Foundations.StarsBars.zero_variables_zero
  · refine ⟨elementary K V 0 (fun i => Fin.elim0 i), ?_⟩
    simpa using (inclusion_elementary (K := K) (V := V) 0 (fun i => Fin.elim0 i))

theorem zero_space_positive : Specs.D05.M15.SymmetricBasis.zero_space_positive := by
  intro K V _ _ _ b p hp
  have : IsEmpty (NonnegativeTuples 0 p) := ⟨fun a => by
    have h := a.property
    change (∑ i : Fin 0, a.val i) = p at h
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at h
    omega⟩
  exact (monomialBasis b p).repr.symm.surjective.subsingleton

end D05.M15.SymmetricBasis
