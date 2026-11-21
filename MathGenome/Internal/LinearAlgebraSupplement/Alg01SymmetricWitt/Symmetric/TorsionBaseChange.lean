import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Symmetric.TorsionBaseChange
import MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Symmetric.BaseChangeDegree
import MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Symmetric.Polynomial
import MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Symmetric.TorsionPresentation
import Mathlib.RingTheory.TensorProduct.Maps

namespace Alg01SymmetricWitt.Symmetric.TorsionBaseChange

open scoped _root_.Polynomial TensorProduct
open Module
open Alg01SymmetricWitt.Symmetric.Algebra (degree)
open Alg01SymmetricWitt.Symmetric.BaseChangeAlgebra
  (comparison comparison_toAlgHom comparison_tmul_ι)
open Alg01SymmetricWitt.Symmetric.BaseChangeDegree
  (baseChangedDegree comparison_mem_degree comparison_symm_mem_degree)
open Specs.Alg01SymmetricWitt.Symmetric.TorsionBaseChange
  (ResidueField ExtendedModule ExtendedAlgebra residuePolynomialDegree)
open Specs.Alg01SymmetricWitt.Symmetric.TorsionPresentation
  (PolynomialQuotient quotientMap quotientDegree)

theorem integralPresentation :
    Specs.Alg01SymmetricWitt.Symmetric.TorsionBaseChange.integralPresentation :=
  ⟨TorsionPresentation.presentation, TorsionPresentation.quotientGrading,
    TorsionPresentation.degreeZero, TorsionPresentation.degreePositive⟩

private noncomputable def tensorMultiplication : ExtendedModule ≃ₐ[ResidueField] ResidueField := by
  letI : TensorProduct.CompatibleSMul ℤ ResidueField ResidueField ResidueField :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective
      (M := ResidueField) (N := ResidueField) ZMod.intCast_surjective
  exact Algebra.TensorProduct.lmulEquiv ℤ ResidueField

/-- The rank-one basis of the extended cyclic module, with basis vector `1 ⊗ 1`. -/
noncomputable def extendedBasis : Basis (Fin 1) ResidueField ExtendedModule :=
  (Basis.singleton (Fin 1) ResidueField).map tensorMultiplication.toLinearEquiv.symm

@[simp] theorem extendedBasis_zero : extendedBasis 0 = 1 ⊗ₜ[ℤ] (1 : ZMod 2) := by
  rw [extendedBasis, Basis.map_apply, Basis.singleton_apply]
  apply tensorMultiplication.injective
  change tensorMultiplication (tensorMultiplication.symm 1) = _
  rw [AlgEquiv.apply_symm_apply]
  change (1 : ResidueField) = 1 * 1
  exact (one_mul 1).symm

private theorem oneVariable_map_degree (n : ℕ) :
    (MvPolynomial.homogeneousSubmodule (Fin 1) ResidueField n).map
        (MvPolynomial.uniqueAlgEquiv ResidueField (Fin 1)).toLinearMap =
      residuePolynomialDegree n := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    change q.IsHomogeneous n at hq
    refine ⟨q.coeff (Finsupp.single default n), ?_⟩
    apply Polynomial.ext
    intro m
    change (Polynomial.monomial n _).coeff m =
      (MvPolynomial.uniqueAlgEquiv ResidueField (Fin 1) q).coeff m
    rw [Polynomial.coeff_monomial, MvPolynomial.coeff_uniqueAlgEquiv]
    by_cases h : n = m
    · subst m
      simp
    · rw [ite_eq_right h, hq.coeff_eq_zero]
      simpa only [Finsupp.degree_single] using Ne.symm h
  · rintro ⟨a, rfl⟩
    refine ⟨MvPolynomial.monomial (Finsupp.single default n) a,
      MvPolynomial.isHomogeneous_monomial a (Finsupp.degree_single _ _), ?_⟩
    simp only [AlgEquiv.toLinearMap_apply, MvPolynomial.uniqueAlgEquiv_monomial,
      Finsupp.single_eq_same]

private theorem comparison_map_degree (n : ℕ) :
    (baseChangedDegree ℤ ResidueField (ZMod 2) n).map
      (comparison ℤ ResidueField (ZMod 2)).toLinearMap =
    degree ResidueField ExtendedModule n := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact comparison_mem_degree _ _ _ hx
  · intro hz
    let e := comparison ℤ ResidueField (ZMod 2)
    exact ⟨e.symm z, comparison_symm_mem_degree _ _ _ hz, e.apply_symm_apply z⟩

/-- The graded polynomial identification after extension of scalars to the residue field. -/
noncomputable def polynomialEquiv : ExtendedAlgebra ≃ₐ[ResidueField] ResidueField[X] :=
  (comparison ℤ ResidueField (ZMod 2)).trans
    ((Polynomial.equivMvPolynomial extendedBasis).trans
      (MvPolynomial.uniqueAlgEquiv ResidueField (Fin 1)))

@[simp] theorem polynomialEquiv_generator :
    polynomialEquiv (1 ⊗ₜ[ℤ] SymmetricAlgebra.ι ℤ (ZMod 2) 1) = Polynomial.X := by
  rw [polynomialEquiv, AlgEquiv.trans_apply, comparison_tmul_ι, one_smul,
    AlgEquiv.trans_apply, ← extendedBasis_zero, Polynomial.equivMvPolynomial_ι]
  exact MvPolynomial.eval₂_X _ _ _

theorem polynomialEquiv_map_degree (n : ℕ) :
    (baseChangedDegree ℤ ResidueField (ZMod 2) n).map polynomialEquiv.toLinearMap =
      residuePolynomialDegree n := by
  unfold polynomialEquiv
  rw [AlgEquiv.trans_toLinearMap, Submodule.map_comp, comparison_map_degree,
    AlgEquiv.trans_toLinearMap, Submodule.map_comp, Polynomial.map_degree,
    oneVariable_map_degree]

private noncomputable def extendPresentation :
    ExtendedAlgebra ≃ₐ[ResidueField] (ResidueField ⊗[ℤ] PolynomialQuotient) :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : ResidueField ≃ₐ[ResidueField] ResidueField)
    TorsionPresentation.presentationEquiv

/-- The polynomial equivalence for the actual scalar extension of the integral quotient. -/
noncomputable def quotientPolynomialEquiv :
    (ResidueField ⊗[ℤ] PolynomialQuotient) ≃ₐ[ResidueField] ResidueField[X] :=
  extendPresentation.symm.trans polynomialEquiv

private theorem quotientPolynomialEquiv_extend (x : ExtendedAlgebra) :
    quotientPolynomialEquiv (extendPresentation x) = polynomialEquiv x :=
  congrArg polynomialEquiv (extendPresentation.symm_apply_apply x)

private theorem quotientPolynomialEquiv_generator :
    quotientPolynomialEquiv (1 ⊗ₜ[ℤ] quotientMap Polynomial.X) = Polynomial.X := by
  rw [← TorsionPresentation.presentationEquiv_generator]
  exact (quotientPolynomialEquiv_extend
    (1 ⊗ₜ[ℤ] SymmetricAlgebra.ι ℤ (ZMod 2) 1)).trans polynomialEquiv_generator

private theorem quotientPolynomialEquiv_reduce (p : ℤ[X]) :
    quotientPolynomialEquiv (1 ⊗ₜ[ℤ] quotientMap p) = p.map (Int.castRingHom ResidueField) := by
  let f : ℤ[X] →ₐ[ℤ] ResidueField[X] :=
    (quotientPolynomialEquiv.toAlgHom.restrictScalars ℤ).comp
      (Algebra.TensorProduct.includeRight.comp quotientMap)
  let g : ℤ[X] →ₐ[ℤ] ResidueField[X] :=
    Polynomial.mapAlgHom (Algebra.ofId ℤ ResidueField)
  have h : f = g := Polynomial.algHom_ext (by simpa [f, g] using quotientPolynomialEquiv_generator)
  exact DFunLike.congr_fun h p

private theorem extendPresentation_map_degree (n : ℕ) :
    (baseChangedDegree ℤ ResidueField (ZMod 2) n).map extendPresentation.toLinearMap =
      (quotientDegree n).baseChange ResidueField := by
  change ((degree ℤ (ZMod 2) n).baseChange ResidueField).map extendPresentation.toLinearMap = _
  rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.baseChange_eq_span]
  congr 1
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨TorsionPresentation.presentationEquiv x, ?_, rfl⟩
    rw [← TorsionPresentation.presentationEquiv_map_degree]
    exact ⟨x, hx, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [← TorsionPresentation.presentationEquiv_map_degree] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩

theorem quotientScalarExtension :
    Specs.Alg01SymmetricWitt.Symmetric.TorsionBaseChange.quotientScalarExtension polynomialEquiv := by
  refine ⟨TorsionPresentation.presentationEquiv, quotientPolynomialEquiv,
    TorsionPresentation.presentationEquiv_generator, TorsionPresentation.presentationEquiv_map_degree,
    fun s x => quotientPolynomialEquiv_extend (s ⊗ₜ[ℤ] x), ?_, ?_⟩
  · intro s p
    rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul, quotientPolynomialEquiv_reduce]
  · intro n
    have h : quotientPolynomialEquiv.toLinearMap.comp extendPresentation.toLinearMap =
        polynomialEquiv.toLinearMap := LinearMap.ext quotientPolynomialEquiv_extend
    rw [← extendPresentation_map_degree, ← Submodule.map_comp, h, polynomialEquiv_map_degree]

theorem scalarExtension : Specs.Alg01SymmetricWitt.Symmetric.TorsionBaseChange.scalarExtension :=
  ⟨extendedBasis, polynomialEquiv, extendedBasis_zero, polynomialEquiv_generator,
    rfl, polynomialEquiv_map_degree, quotientScalarExtension⟩

theorem nonflatness : Specs.Alg01SymmetricWitt.Symmetric.TorsionBaseChange.nonflatness := by
  let mulTwo : ℤ →ₗ[ℤ] ℤ := (2 : ℤ) • LinearMap.id
  change Function.Injective mulTwo ∧ mulTwo.baseChange ResidueField = 0 ∧
    (1 ⊗ₜ[ℤ] (1 : ℤ) : ResidueField ⊗[ℤ] ℤ) ≠ 0 ∧ ¬ Module.Flat ℤ ResidueField
  have hInjective : Function.Injective mulTwo := by
    intro a b h
    change (2 : ℤ) * a = 2 * b at h
    exact mul_left_cancel₀ (by decide) h
  have hZero : mulTwo.baseChange ResidueField = 0 := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s a
    rw [LinearMap.baseChange_tmul, LinearMap.zero_apply]
    change s ⊗ₜ[ℤ] ((2 : ℤ) • a) = 0
    rw [← TensorProduct.smul_tmul, zsmul_eq_mul,
      show ((2 : ℤ) : ResidueField) = 0 by decide, zero_mul, TensorProduct.zero_tmul]
  have hNonzero : (1 ⊗ₜ[ℤ] (1 : ℤ) : ResidueField ⊗[ℤ] ℤ) ≠ 0 := by
    intro h
    have hh := congrArg (TensorProduct.AlgebraTensorModule.rid ℤ ResidueField ResidueField) h
    simp at hh
  refine ⟨hInjective, hZero, hNonzero, ?_⟩
  intro hFlat
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := ResidueField) mulTwo hInjective
  apply hNonzero
  apply h
  change mulTwo.baseChange ResidueField _ = mulTwo.baseChange ResidueField 0
  rw [hZero]
  rfl

end Alg01SymmetricWitt.Symmetric.TorsionBaseChange
