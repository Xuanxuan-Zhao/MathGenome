import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.SymmetricPowerTrace
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.RingTheory.PowerSeries.WellKnown

open Module
open scoped BigOperators Polynomial TensorProduct

namespace RepTheorySurvey.Invariants

variable {k W ι : Type*} [Field k] [AddCommGroup W] [Module k W]

@[simp]
theorem symmetricAlgebraMap_ι (f : W →ₗ[k] W) (w : W) :
    symmetricAlgebraMap f (SymmetricAlgebra.ι k W w) = SymmetricAlgebra.ι k W (f w) := by
  simp [symmetricAlgebraMap]

@[simp]
theorem symmetricDegreeMap_one (d : ℕ) :
    symmetricDegreeMap (k := k) (W := W) d 1 = 1 := by
  have h : symmetricAlgebraMap (1 : Module.End k W) = AlgHom.id k _ := by
    apply SymmetricAlgebra.algHom_ext
    ext w
    simp
  apply LinearMap.ext
  intro x
  exact Subtype.ext (DFunLike.congr_fun h x.val)

theorem symmetricDegreeMap_mul (d : ℕ) (f g : Module.End k W) :
    symmetricDegreeMap d (f * g) = symmetricDegreeMap d f * symmetricDegreeMap d g := by
  have h : symmetricAlgebraMap (f * g) = (symmetricAlgebraMap f).comp (symmetricAlgebraMap g) := by
    apply SymmetricAlgebra.algHom_ext
    ext w
    simp
  apply LinearMap.ext
  intro x
  exact Subtype.ext (DFunLike.congr_fun h x.val)

/-- The symmetric-algebra coordinates identify each degree with homogeneous polynomials. -/
theorem map_symmetricDegree (b : Basis ι k W) (d : ℕ) :
    Submodule.map (SymmetricAlgebra.equivMvPolynomial b).toLinearEquiv.toLinearMap
      (symmetricDegree k W d) = MvPolynomial.homogeneousSubmodule ι k d := by
  change Submodule.map (SymmetricAlgebra.equivMvPolynomial b).toAlgHom.toLinearMap
    ((LinearMap.range (SymmetricAlgebra.ι k W)) ^ d) = _
  rw [Submodule.map_pow, ← MvPolynomial.homogeneousSubmodule_one_pow]
  congr 1
  rw [← LinearMap.range_comp, ← Submodule.map_top, ← b.span_eq, Submodule.map_span,
    ← Set.range_comp]
  simp [MvPolynomial.homogeneousSubmodule_one_eq_span_X, Function.comp_def]

private noncomputable def degreeCoordinates (b : Basis ι k W) (d : ℕ) :
    symmetricDegree k W d ≃ₗ[k] MvPolynomial.homogeneousSubmodule ι k d :=
  (SymmetricAlgebra.equivMvPolynomial b).toLinearEquiv.ofSubmodules _ _ (map_symmetricDegree b d)

private theorem homogeneousSubmodule_eq_restrictSupport (d : ℕ) :
    MvPolynomial.homogeneousSubmodule ι k d =
      MvPolynomial.restrictSupport k {a : ι →₀ ℕ | a.degree = d} :=
  MvPolynomial.homogeneousSubmodule_eq_finsupp_supported ι k d

private noncomputable def monomialBasis (b : Basis ι k W) (d : ℕ) :
    Basis {a : ι →₀ ℕ // a.degree = d} k (symmetricDegree k W d) :=
  (MvPolynomial.basisRestrictSupport k {a : ι →₀ ℕ | a.degree = d}).map
    ((LinearEquiv.ofEq (MvPolynomial.restrictSupport k {a : ι →₀ ℕ | a.degree = d}) _
      (homogeneousSubmodule_eq_restrictSupport (ι := ι) (k := k) d).symm).trans
      (degreeCoordinates b d).symm)

private theorem mem_monomialIndices [Fintype ι] [DecidableEq ι] (d : ℕ) (a : ι →₀ ℕ) :
    a ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) d ↔ a.degree = d := by
  simp [Finsupp.degree_eq_sum]

@[instance_reducible] private noncomputable def monomialFintype [Fintype ι] (d : ℕ) :
    Fintype {a : ι →₀ ℕ // a.degree = d} := by
  classical
  exact Fintype.ofFinset (Finset.finsuppAntidiag Finset.univ d) (mem_monomialIndices d)

instance symmetricDegree_finite [Module.Finite k W] (d : ℕ) :
    Module.Finite k (symmetricDegree k W d) := by
  let := monomialFintype (ι := Fin (finrank k W)) d
  exact Module.Finite.of_basis (monomialBasis (finBasis k W) d)

private theorem denominator_eq_det [Fintype ι] [DecidableEq ι]
    (b : Basis ι k W) (f : W →ₗ[k] W) :
    symmetricTraceDenominator f =
      Matrix.det (1 - (PowerSeries.X : PowerSeries k) •
        (LinearMap.toMatrix b b f).map PowerSeries.C) := by
  let c := Algebra.TensorProduct.basis (PowerSeries k) b
  unfold symmetricTraceDenominator
  refine (LinearMap.det_toMatrix c _).symm.trans (congrArg Matrix.det ?_)
  apply Matrix.ext
  intro i j
  change LinearMap.toMatrix c c (1 - (PowerSeries.X : PowerSeries k) • f.baseChange _) i j = _
  rw [LinearMap.toMatrix_apply]
  simp [c, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.toMatrix_apply,
    Matrix.one_apply, Finsupp.single_apply, eq_comm]

@[simp]
theorem constantCoeff_symmetricTraceDenominator [Module.Finite k W] (f : W →ₗ[k] W) :
    PowerSeries.constantCoeff (symmetricTraceDenominator f) = 1 := by
  rw [denominator_eq_det (finBasis k W), RingHom.map_det]
  have h : (1 - (PowerSeries.X : PowerSeries k) •
      (LinearMap.toMatrix (finBasis k W) (finBasis k W) f).map PowerSeries.C).map
        PowerSeries.constantCoeff = 1 := by
    ext i j
    simp [Matrix.one_apply]
  exact (congrArg Matrix.det h).trans Matrix.det_one

private theorem monomialBasis_repr (b : Basis ι k W) (d : ℕ)
    (x : symmetricDegree k W d) (a : {a : ι →₀ ℕ // a.degree = d}) :
    (monomialBasis b d).repr x a =
      (SymmetricAlgebra.equivMvPolynomial b x.val).coeff a.val := by
  rfl

private theorem monomialBasis_polynomial (b : Basis ι k W) (d : ℕ)
    (a : {a : ι →₀ ℕ // a.degree = d}) :
    SymmetricAlgebra.equivMvPolynomial b (monomialBasis b d a).val =
      MvPolynomial.monomial a.val 1 := by
  classical
  rw [monomialBasis, Basis.map_apply]
  simp only [LinearEquiv.trans_apply, degreeCoordinates, LinearEquiv.ofSubmodules_symm_apply]
  let q := (MvPolynomial.basisRestrictSupport k {a : ι →₀ ℕ | a.degree = d}) a
  change (SymmetricAlgebra.equivMvPolynomial b)
    ((SymmetricAlgebra.equivMvPolynomial b).symm (q.val)) = _
  rw [AlgEquiv.apply_symm_apply]
  unfold q
  rw [← Basis.repr_symm_single_one]
  apply MvPolynomial.ext
  intro m
  change ((Finsupp.supportedEquivFinsupp (R := k) {a : ι →₀ ℕ | a.degree = d}).symm
    (Finsupp.single a 1)).val m = _
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

private theorem polynomial_generator [Fintype ι] (b : Basis ι k W) (w : W) :
    SymmetricAlgebra.equivMvPolynomial b (SymmetricAlgebra.ι k W w) =
      ∑ i, b.repr w i • MvPolynomial.X i := by
  calc
    _ = SymmetricAlgebra.equivMvPolynomial b
        (SymmetricAlgebra.ι k W (∑ i, b.repr w i • b i)) :=
      congrArg (fun z => SymmetricAlgebra.equivMvPolynomial b (SymmetricAlgebra.ι k W z))
        (b.sum_repr w).symm
    _ = _ := by
      simp only [map_sum, map_smul, SymmetricAlgebra.equivMvPolynomial_ι_apply]

private theorem polynomial_action (b : Basis ι k W) (f : W →ₗ[k] W) (p : MvPolynomial ι k) :
    SymmetricAlgebra.equivMvPolynomial b (symmetricAlgebraMap f
      ((SymmetricAlgebra.equivMvPolynomial b).symm p)) =
      MvPolynomial.aeval (fun i => SymmetricAlgebra.equivMvPolynomial b
        (SymmetricAlgebra.ι k W (f (b i)))) p := by
  let e := SymmetricAlgebra.equivMvPolynomial b
  have h : e.toAlgHom.comp ((symmetricAlgebraMap f).comp e.symm.toAlgHom) =
      MvPolynomial.aeval (fun i => e (SymmetricAlgebra.ι k W (f (b i)))) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [e]
  exact DFunLike.congr_fun h p

private theorem polynomial_action_monomial (b : Basis ι k W) (f : W →ₗ[k] W)
    (d : ℕ) (a : {a : ι →₀ ℕ // a.degree = d}) :
    SymmetricAlgebra.equivMvPolynomial b (symmetricDegreeMap d f (monomialBasis b d a)).val =
      ∏ i ∈ a.val.support,
        (SymmetricAlgebra.equivMvPolynomial b (SymmetricAlgebra.ι k W (f (b i)))) ^ a.val i := by
  change SymmetricAlgebra.equivMvPolynomial b (symmetricAlgebraMap f (monomialBasis b d a).val) = _
  rw [← (SymmetricAlgebra.equivMvPolynomial b).symm_apply_apply (monomialBasis b d a).val,
    polynomial_action, monomialBasis_polynomial, ← MvPolynomial.prod_X_pow_eq_monomial]
  simp only [map_prod, map_pow, MvPolynomial.aeval_X]

section ScalarExtension

variable {K : Type*} [Field K] [Algebra k K]

open Algebra.TensorProduct

private theorem polynomial_generator_baseChange [Fintype ι] (b : Basis ι k W)
    (f : W →ₗ[k] W) (i : ι) :
    MvPolynomial.map (algebraMap k K)
      (SymmetricAlgebra.equivMvPolynomial b (SymmetricAlgebra.ι k W (f (b i)))) =
    SymmetricAlgebra.equivMvPolynomial (basis K b)
      (SymmetricAlgebra.ι K (K ⊗[k] W) (f.baseChange K (basis K b i))) := by
  simp only [polynomial_generator, basis_apply, LinearMap.baseChange_tmul, basis_repr_tmul,
    one_smul, Finsupp.mapRange_apply, map_sum, MvPolynomial.smul_eq_C_mul, map_mul,
    MvPolynomial.map_C, MvPolynomial.map_X]

private theorem trace_symmetricDegreeMap_baseChange [Module.Finite k W]
    (f : W →ₗ[k] W) (d : ℕ) :
    LinearMap.trace K _ (symmetricDegreeMap d (f.baseChange K)) =
      algebraMap k K (LinearMap.trace k _ (symmetricDegreeMap d f)) := by
  classical
  let b := finBasis k W
  let := monomialFintype (ι := Fin (finrank k W)) d
  -- The coefficients of substituted monomials give the diagonal entries in both fields.
  rw [LinearMap.trace_eq_matrix_trace K (monomialBasis (basis K b) d),
    LinearMap.trace_eq_matrix_trace k (monomialBasis b d)]
  simp only [Matrix.trace, Matrix.diag_apply, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [LinearMap.toMatrix_apply, monomialBasis_repr, polynomial_action_monomial]
  rw [← MvPolynomial.coeff_map]
  simp only [map_prod, map_pow, polynomial_generator_baseChange]

private theorem map_symmetricTraceDenominator [Module.Finite k W] (f : W →ₗ[k] W) :
    PowerSeries.map (algebraMap k K) (symmetricTraceDenominator f) =
      symmetricTraceDenominator (f.baseChange K) := by
  classical
  let b := finBasis k W
  rw [denominator_eq_det b, denominator_eq_det (basis K b), RingHom.map_det,
    LinearMap.toMatrix_baseChange]
  congr 1
  ext i j
  simp [Matrix.one_apply, apply_ite, smul_eq_mul, PowerSeries.map_X, PowerSeries.map_C]

private theorem map_symmetricTraceDenominator_inv [Module.Finite k W] (f : W →ₗ[k] W) :
    PowerSeries.map (algebraMap k K) (symmetricTraceDenominator f)⁻¹ =
      (symmetricTraceDenominator (f.baseChange K))⁻¹ := by
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by simp)).2
  rw [← map_symmetricTraceDenominator (K := K) f, ← map_mul,
    PowerSeries.inv_mul_cancel _ (by simp), map_one]

end ScalarExtension

private theorem trace_symmetricDegreeMap_of_eigenbasis [Fintype ι] [DecidableEq ι]
    (b : Basis ι k W) (f : W →ₗ[k] W) (eigenvalue : ι → k)
    (h : ∀ i, f (b i) = eigenvalue i • b i) (d : ℕ) :
    LinearMap.trace k _ (symmetricDegreeMap d f) =
      ∑ a ∈ Finset.finsuppAntidiag Finset.univ d, ∏ i, eigenvalue i ^ a i := by
  let := monomialFintype (ι := ι) d
  rw [LinearMap.trace_eq_matrix_trace k (monomialBasis b d)]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, monomialBasis_repr,
    polynomial_action_monomial, h, map_smul, SymmetricAlgebra.equivMvPolynomial_ι_apply,
    MvPolynomial.smul_eq_C_mul, mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod,
    MvPolynomial.prod_X_pow_eq_monomial, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial,
    ite_true, mul_one]
  have hprod (a : ι →₀ ℕ) : ∏ i ∈ a.support, eigenvalue i ^ a i = ∏ i, eigenvalue i ^ a i := by
    apply Finset.prod_subset (Finset.subset_univ _)
    intro i _ hi
    rw [Finsupp.notMem_support_iff.mp hi, pow_zero]
  simp only [hprod]
  exact (Finset.sum_subtype (Finset.finsuppAntidiag (Finset.univ : Finset ι) d)
    (mem_monomialIndices d) (fun a => ∏ i, eigenvalue i ^ a i)).symm

private theorem denominator_of_eigenbasis [Fintype ι] [DecidableEq ι]
    (b : Basis ι k W) (f : W →ₗ[k] W) (eigenvalue : ι → k) (h : ∀ i, f (b i) = eigenvalue i • b i) :
    symmetricTraceDenominator f = ∏ i, (1 - PowerSeries.C (eigenvalue i) * PowerSeries.X) := by
  rw [denominator_eq_det b]
  have hmat : LinearMap.toMatrix b b f = Matrix.diagonal eigenvalue := by
    ext i j
    simp only [LinearMap.toMatrix_apply, h, map_smul, Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_apply, Matrix.diagonal_apply, smul_eq_mul]
    split_ifs with hij hji hji <;> simp_all [eq_comm]
  rw [hmat]
  have hdiag : (1 - (PowerSeries.X : PowerSeries k) • (Matrix.diagonal eigenvalue).map PowerSeries.C) =
      Matrix.diagonal (fun i => 1 - PowerSeries.C (eigenvalue i) * PowerSeries.X) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [mul_comm]
    · simp [hij]
  rw [hdiag, Matrix.det_diagonal]

private theorem trace_identity_of_eigenbasis [Fintype ι] [DecidableEq ι]
    (b : Basis ι k W) [Module.Finite k W] (f : W →ₗ[k] W) (eigenvalue : ι → k)
    (h : ∀ i, f (b i) = eigenvalue i • b i) :
    PowerSeries.mk (fun d => LinearMap.trace k _ (symmetricDegreeMap d f)) =
      (symmetricTraceDenominator f)⁻¹ := by
  let geom (a : k) : PowerSeries k := PowerSeries.rescale a (PowerSeries.mk 1)
  have hgeom (a : k) : geom a * (1 - PowerSeries.C a * PowerSeries.X) = 1 := by
    simpa only [geom, map_mul, map_sub, map_one, PowerSeries.rescale_X] using
      congrArg (PowerSeries.rescale a) (PowerSeries.mk_one_mul_one_sub_eq_one k)
  have hcoeff (a : k) (d : ℕ) : PowerSeries.coeff d (geom a) = a ^ d := by
    simp [geom, PowerSeries.coeff_rescale]
  have hseries : PowerSeries.mk (fun d => LinearMap.trace k _ (symmetricDegreeMap d f)) =
      ∏ i, geom (eigenvalue i) := by
    apply PowerSeries.ext
    intro d
    rw [PowerSeries.coeff_mk, trace_symmetricDegreeMap_of_eigenbasis b f eigenvalue h,
      PowerSeries.coeff_prod]
    simp only [hcoeff]
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by simp)).2
  rw [hseries, denominator_of_eigenbasis b f eigenvalue h, ← Finset.prod_mul_distrib]
  simp [hgeom]

private theorem exists_eigenbasis_of_pow_eq_one [CharZero k] [IsAlgClosed k] [Module.Finite k W]
    (f : Module.End k W) {m : ℕ} (hm : 0 < m) (hf : f ^ m = 1) :
    ∃ (n : ℕ) (b : Basis (Fin n) k W) (eigenvalue : Fin n → k), ∀ i, f (b i) = eigenvalue i • b i := by
  classical
  let p : k[X] := Polynomial.X ^ m - Polynomial.C 1
  have hp : Polynomial.aeval f p = 0 := by simp [p, hf]
  have hsep : (minpoly k f).Separable :=
    (Polynomial.separable_X_pow_sub_C (1 : k) (Nat.cast_ne_zero.mpr hm.ne') one_ne_zero).of_dvd
      (minpoly.dvd k f hp)
  have hs := Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree (minpoly.aeval k f)
  let s : Set W := {w | ∃ a : k, w ∈ f.eigenspace a}
  have hspan : ⊤ ≤ Submodule.span k s := by
    rw [← hs.iSup_eigenspace_eq_top]
    exact iSup_le fun a w hw => Submodule.subset_span ⟨a, hw⟩
  let b := Basis.ofSpan hspan
  let := FiniteDimensional.fintypeBasisIndex b
  let c := b.reindex (Fintype.equivFin _)
  have hvec (i : Fin _) : ∃ a : k, f (c i) = a • c i := by
    have hi : c i ∈ Set.range b := by
      change b.reindex (Fintype.equivFin _) i ∈ Set.range b
      rw [Basis.reindex_apply]
      exact Set.mem_range_self _
    obtain ⟨a, ha⟩ := Basis.ofSpan_subset hspan hi
    exact ⟨a, Module.End.mem_eigenspace_iff.mp ha⟩
  exact ⟨_, c, fun i => (hvec i).choose, fun i => (hvec i).choose_spec⟩

/-- The generating series of the traces on the symmetric powers of a finite-order automorphism. -/
theorem symmetricPowerTrace [CharZero k] [Module.Finite k W]
    (g : W ≃ₗ[k] W) (hg : IsOfFinOrder g) :
    PowerSeries.mk (fun d => LinearMap.trace k (symmetricDegree k W d)
      (symmetricDegreeMap d g.toLinearMap)) = (symmetricTraceDenominator g.toLinearMap)⁻¹ := by
  let K := AlgebraicClosure k
  let f : Module.End k W := g.toLinearMap
  let fK := f.baseChange K
  obtain ⟨m, hm, hgm⟩ := hg.exists_pow_eq_one
  have hf : f ^ m = 1 := by
    let h := LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := k) (M := W)
    exact (map_pow h g m).symm.trans ((congrArg h hgm).trans (map_one h))
  have hfK : fK ^ m = 1 := by
    rw [← LinearMap.baseChange_pow, hf, LinearMap.baseChange_one]
  obtain ⟨_, b, eigenvalue, hb⟩ := exists_eigenbasis_of_pow_eq_one fK hm hfK
  have hK := trace_identity_of_eigenbasis b fK eigenvalue hb
  apply PowerSeries.map_injective (algebraMap k K) (algebraMap k K).injective
  change PowerSeries.map (algebraMap k K) (PowerSeries.mk (fun d =>
    LinearMap.trace k _ (symmetricDegreeMap d f))) =
      PowerSeries.map (algebraMap k K) (symmetricTraceDenominator f)⁻¹
  rw [map_symmetricTraceDenominator_inv, ← hK]
  apply PowerSeries.ext
  intro d
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
    trace_symmetricDegreeMap_baseChange]

end RepTheorySurvey.Invariants
