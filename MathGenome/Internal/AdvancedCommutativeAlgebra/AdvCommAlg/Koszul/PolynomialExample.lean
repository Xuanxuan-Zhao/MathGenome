import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.PolynomialExample
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.RegularSequence.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.Resolution
import Mathlib.LinearAlgebra.TensorProduct.Basis

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
namespace AdvCommAlg.Koszul.PolynomialExample

variable {A : Type u} [CommRing A] {r : ℕ}

@[simp] theorem mem_variableList_take (j : ℕ) (p : PolynomialRing A r) :
    p ∈ (variableList A r).take j ↔ ∃ i : Fin r, i.val < j ∧ MvPolynomial.X i = p := by
  simp only [variableList, List.mem_take_iff_getElem, List.length_ofFn, lt_min_iff]
  constructor
  · rintro ⟨i, hi, hp⟩
    refine ⟨⟨i, ?_⟩, hi.1, ?_⟩
    · simpa using hi.2
    · simpa using hp
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.val, ⟨hi, by simp⟩, by simp⟩

/-- Evaluate a prefix at zero while retaining precisely the remaining variables. -/
def prefixEvaluation (j : ℕ) : PolynomialRing A r →ₐ[A]
    MvPolynomial {i : Fin r // j ≤ i.val} A :=
  MvPolynomial.aeval fun i => if h : j ≤ i.val then MvPolynomial.X ⟨i, h⟩ else 0

@[simp] theorem prefixEvaluation_C (j : ℕ) (a : A) :
    prefixEvaluation j (MvPolynomial.C a : PolynomialRing A r) = MvPolynomial.C a := by
  simp [prefixEvaluation]

@[simp] theorem prefixEvaluation_X (j : ℕ) (i : Fin r) :
    prefixEvaluation (A := A) j (MvPolynomial.X i) =
      if h : j ≤ i.val then MvPolynomial.X ⟨i, h⟩ else 0 := by
  simp [prefixEvaluation]

/-- All prefix variables vanish under the evaluation map. -/
theorem prefixIdeal_le_ker (j : ℕ) :
    prefixIdeal A r j ≤ RingHom.ker (prefixEvaluation (A := A) j).toRingHom := by
  apply Ideal.span_le.mpr
  intro p hp
  obtain ⟨i, hi, rfl⟩ := (mem_variableList_take j p).mp hp
  simp [RingHom.mem_ker, prefixEvaluation_X, Nat.not_le.mpr hi]

/-- The quotient map, retaining the original coefficient algebra. -/
def prefixQuotientMap (j : ℕ) : (PolynomialRing A r ⧸ prefixIdeal A r j) →ₐ[A]
    MvPolynomial {i : Fin r // j ≤ i.val} A :=
  Ideal.Quotient.liftₐ _ (prefixEvaluation j) (prefixIdeal_le_ker j)

def prefixQuotientInverse (j : ℕ) : MvPolynomial {i : Fin r // j ≤ i.val} A →ₐ[A]
    (PolynomialRing A r ⧸ prefixIdeal A r j) :=
  MvPolynomial.aeval fun i => Ideal.Quotient.mk _ (MvPolynomial.X i.val)

/-- The successive quotients, also valid over the zero coefficient ring. -/
def prefixQuotientEquiv (j : ℕ) : (PolynomialRing A r ⧸ prefixIdeal A r j) ≃ₐ[A]
    MvPolynomial {i : Fin r // j ≤ i.val} A :=
  AlgEquiv.ofAlgHom (prefixQuotientMap j) (prefixQuotientInverse j)
    (by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, prefixQuotientInverse, MvPolynomial.aeval_X]
      change prefixEvaluation (A := A) j (MvPolynomial.X i.val) = MvPolynomial.X i
      simp [i.property])
    (by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro i
      change prefixQuotientInverse j (prefixEvaluation j (MvPolynomial.X i)) =
        Ideal.Quotient.mk _ (MvPolynomial.X i)
      by_cases hi : j ≤ i.val
      · simp [prefixQuotientInverse, hi]
      · rw [prefixEvaluation_X, dite_eq_right hi, map_zero]
        symm
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        exact Ideal.subset_span ((mem_variableList_take j _).mpr ⟨i, Nat.lt_of_not_ge hi, rfl⟩))

@[simp] theorem prefixQuotientEquiv_mk (j : ℕ) (p : PolynomialRing A r) :
    prefixQuotientEquiv j (Ideal.Quotient.mk (prefixIdeal A r j) p) =
      prefixEvaluation j p := rfl

/-- The next variable remains a nonzerodivisor in the prefix quotient. -/
theorem variable_regular_mod_prefix (i : Fin r) :
    IsSMulRegular (PolynomialRing A r ⧸ prefixIdeal A r i.val) (MvPolynomial.X (R := A) i) := by
  intro a b hab
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  apply (prefixQuotientEquiv i.val).injective
  change prefixEvaluation i.val a = prefixEvaluation i.val b
  apply (MvPolynomial.isRegular_X (n := (⟨i, le_rfl⟩ : {k : Fin r // i.val ≤ k.val}))).left
  have h := congrArg (prefixQuotientEquiv i.val) hab
  change prefixQuotientEquiv i.val (Ideal.Quotient.mk _ (MvPolynomial.X i * a)) =
    prefixQuotientEquiv i.val (Ideal.Quotient.mk _ (MvPolynomial.X i * b)) at h
  simpa using h

theorem variableList_weaklyRegular (A : Type u) [CommRing A] (r : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular (PolynomialRing A r) (variableList A r) := by
  constructor
  intro j hj
  have hjr : j < r := by simpa using hj
  let e := Submodule.quotEquivOfEq
    (Ideal.ofList ((variableList A r).take j) • (⊤ : Submodule (PolynomialRing A r) _))
    (prefixIdeal A r j)
    (by simp [prefixIdeal])
  apply (e.isSMulRegular_congr _).mpr
  simpa [variableList] using variable_regular_mod_prefix (A := A) (⟨j, hjr⟩ : Fin r)

theorem variableList_regular : Specs.AdvCommAlg.Koszul.PolynomialExample.variableListRegular.{u} := by
  intro A _ _ r
  refine ⟨variableList_weaklyRegular A r, ?_⟩
  rw [Ideal.smul_eq_mul, Ideal.mul_top]
  intro h
  have htop : prefixIdeal A r r = ⊤ := by
    unfold prefixIdeal
    rw [List.take_of_length_le (by simp)]
    exact h.symm
  have hn : Nontrivial (PolynomialRing A r ⧸ prefixIdeal A r r) :=
    (prefixQuotientEquiv (A := A) (r := r) r).toEquiv.nontrivial
  exact (Ideal.Quotient.nontrivial_iff.mp hn) htop

theorem successive_quotients : Specs.AdvCommAlg.Koszul.PolynomialExample.successiveQuotients.{u} := by
  intro A _ _ r j _
  exact ⟨prefixQuotientEquiv j⟩

/-- All variables are in the augmentation ideal. -/
theorem variable_mem_listIdeal (i : Fin r) :
    MvPolynomial.X (R := A) i ∈ listIdeal (variableList A r) := by
  apply Ideal.subset_span
  simp [variableList]

/-- Evaluate the full quotient at zero. -/
def quotientCoefficientsMap : (PolynomialRing A r ⧸ listIdeal (variableList A r)) →ₐ[A] A :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (fun _ : Fin r => (0 : A))) (by
    change listIdeal (variableList A r) ≤ RingHom.ker _
    apply Ideal.span_le.mpr
    intro p hp
    obtain ⟨i, rfl⟩ : ∃ i : Fin r, MvPolynomial.X i = p := by
      simpa [variableList] using hp
    simp [RingHom.mem_ker])

/-- The full polynomial quotient is the original coefficient algebra. -/
def quotientCoefficientsEquiv : (PolynomialRing A r ⧸ listIdeal (variableList A r)) ≃ₐ[A] A :=
  AlgEquiv.ofAlgHom quotientCoefficientsMap (Algebra.ofId A _)
    (by ext)
    (by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro i
      change (Algebra.ofId A (PolynomialRing A r ⧸ listIdeal (variableList A r))) (MvPolynomial.aeval (fun _ : Fin r => (0 : A))
        (MvPolynomial.X i)) = Ideal.Quotient.mk _ (MvPolynomial.X i)
      rw [MvPolynomial.aeval_X, map_zero]
      symm
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (variable_mem_listIdeal i))

@[simp] theorem quotientCoefficientsEquiv_mk (p : PolynomialRing A r) :
    quotientCoefficientsEquiv (Ideal.Quotient.mk _ p) =
      MvPolynomial.eval (fun _ => 0) p := by
  change MvPolynomial.aeval (fun _ => (0 : A)) p = _
  rfl

section Coefficients
variable (A : Type u) [CommRing A] (r : ℕ)
local instance : Algebra (PolynomialRing A r) A := evaluationAlgebra A r

/-- The quotient identification respects the evaluation action of R. -/
def quotientCoefficientsLinearEquiv :
    (PolynomialRing A r ⧸ listIdeal (variableList A r)) ≃ₗ[PolynomialRing A r] A :=
  { (quotientCoefficientsEquiv (A := A) (r := r)).toAddEquiv with
    map_smul' := by
      intro p z
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
      change quotientCoefficientsEquiv (Ideal.Quotient.mk _ (p * z)) =
        MvPolynomial.eval (fun _ => 0) p * quotientCoefficientsEquiv (Ideal.Quotient.mk _ z)
      simp }

def polynomialAugmentation : listComplex (variableList A r) ⟶
    (ChainComplex.single₀ (ModuleCat (PolynomialRing A r))).obj (ModuleCat.of _ A) :=
  augmentation (variableList A r) ≫ (ChainComplex.single₀ _).map
    (quotientCoefficientsLinearEquiv A r).toModuleIso.hom

/-- The finite free resolution is augmented by ordinary evaluation at zero. -/
theorem resolves_coefficients : Specs.AdvCommAlg.Koszul.PolynomialExample.resolvesCoefficients.{u} := by
  intro A _ _ r
  refine ⟨polynomialAugmentation A r, ?_, ?_, listComplex_finiteFree _, ?_⟩
  · intro z
    change quotientCoefficientsEquiv (Ideal.Quotient.mk _
      (exteriorPower.zeroEquiv (PolynomialRing A r) _ z)) = _
    exact quotientCoefficientsEquiv_mk _
  · have := augmentation_quasiIso (variableList A r) (variableList_regular A r)
    unfold polynomialAugmentation
    infer_instance
  · intro q hq
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (listComplex_vanish _ q (by simpa using hq))

/-- The polynomial linear form evaluates to zero on every input. -/
theorem listForm_eval_zero (a : Fin (variableList A r).length → PolynomialRing A r) :
    MvPolynomial.eval (fun _ => (0 : A)) (listForm (variableList A r) a) = 0 := by
  classical
  rw [listForm, Module.Basis.constr_apply_fintype]
  simp [variableList, smul_eq_mul]

/-- Each summand of the deletion differential contains a variable coefficient. -/
theorem differential_tmul_zero (n : ℕ)
    (a : ⋀[PolynomialRing A r]^(n+1) (Fin (variableList A r).length → PolynomialRing A r))
    (m : A) : differential (listForm (variableList A r)) n a ⊗ₜ[PolynomialRing A r] m = 0 := by
  let R := PolynomialRing A r
  let E := Fin (variableList A r).length → R
  let t : (⋀[R]^(n+1) E) →ₗ[R] ((⋀[R]^n E) ⊗[R] A) :=
    ((TensorProduct.mk R _ A).flip m).comp (differential (listForm (variableList A r)) n)
  have ht : t = 0 := by
    apply exteriorPower.linearMap_ext (R := R) (M := E) (n := n+1) (N := ((⋀[R]^n E) ⊗[R] A)) (f := t)
    apply AlternatingMap.ext
    intro e
    have hd : differential (listForm (variableList A r)) n (exteriorPower.ιMulti R (n+1) e) =
        ∑ i : Fin (n+1), (-1 : R)^i.val •
          (listForm (variableList A r) (e i) • exteriorPower.ιMulti R n (e ∘ i.succAbove)) := by
      apply Subtype.ext
      simpa only [differential_coe, exteriorPower.ιMulti_apply_coe, Submodule.coe_sum,
        SetLike.val_smul] using contraction_formula (listForm (variableList A r)) n e
    change differential (listForm (variableList A r)) n
      (exteriorPower.ιMulti R (n+1) e) ⊗ₜ[R] m = 0
    rw [hd, TensorProduct.sum_tmul]
    apply Finset.sum_eq_zero
    intro i hi
    rw [← smul_assoc, TensorProduct.smul_tmul]
    change _ ⊗ₜ[R] (MvPolynomial.eval (fun _ => (0 : A))
      ((-1 : R)^i.val * listForm (variableList A r) (e i)) * m) = 0
    rw [map_mul, listForm_eval_zero]
    simp
  exact LinearMap.congr_fun ht a

theorem coefficient_differential_zero (n : ℕ) :
    coefficientDifferential A (variableList A r) n = 0 := by
  apply TensorProduct.ext'
  intro a m
  exact differential_tmul_zero A r n a m

/-- With zero incoming and outgoing differentials, homology is the term itself. -/
def coefficientHomologyTermEquiv (q : ℕ) :
    homology A (variableList A r) q ≃ₗ[PolynomialRing A r]
      (coefficientComplex A (variableList A r)).X q := by
  have hd (i j : ℕ) : (coefficientComplex A (variableList A r)).d i j = 0 := by
    by_cases h : j + 1 = i
    · subst i
      simp only [coefficientComplex, ChainComplex.of_d, coefficient_differential_zero,
        ModuleCat.ofHom_zero]
    · exact HomologicalComplex.shape _ i j h
  let S := (coefficientComplex A (variableList A r)).sc q
  exact (ShortComplex.LeftHomologyData.ofZeros S (hd _ _) (hd _ _)).homologyIso.toLinearEquiv

/-- Restrict the coefficient-term identification along A → R. -/
def coefficientHomologyTermEquivA (q : ℕ) :
    letI : Module A (homology A (variableList A r) q) := Module.compHom _ (MvPolynomial.C : A →+* PolynomialRing A r)
    letI : Module A ((coefficientComplex A (variableList A r)).X q) :=
      Module.compHom _ (MvPolynomial.C : A →+* PolynomialRing A r)
    homology A (variableList A r) q ≃ₗ[A]
      (coefficientComplex A (variableList A r)).X q := by
  letI : Module A (homology A (variableList A r) q) := Module.compHom _ (MvPolynomial.C : A →+* PolynomialRing A r)
  letI : Module A ((coefficientComplex A (variableList A r)).X q) :=
    Module.compHom _ (MvPolynomial.C : A →+* PolynomialRing A r)
  exact { (coefficientHomologyTermEquiv A r q).toAddEquiv with
    map_smul' := fun a z => (coefficientHomologyTermEquiv A r q).map_smul (MvPolynomial.C a) z }

/-- A linear equivalence restricted along a specified scalar map, with an
already specified compatible action on its target. -/
def restrictLinearEquiv {S T M N : Type*} [Semiring S] [Semiring T]
    [AddCommMonoid M] [AddCommMonoid N] [Module T M] [Module T N] [Module S N]
    (f : S →+* T) (h : ∀ (s : S) (n : N), f s • n = s • n) (e : M ≃ₗ[T] N) :
    letI : Module S M := Module.compHom M f
    M ≃ₗ[S] N :=
  letI : Module S M := Module.compHom M f
  { e.toAddEquiv with
    map_smul' := fun s m => (e.map_smul (f s) m).trans (h s (e m)) }

/-- Base change of the standard wedge basis, in explicit coordinates. -/
def coefficientTermCoordinates (q : ℕ) :
    letI : Module A ((coefficientComplex A (variableList A r)).X q) :=
      Module.compHom _ (MvPolynomial.C : A →+* PolynomialRing A r)
    (coefficientComplex A (variableList A r)).X q ≃ₗ[A]
      (Set.powersetCard (Fin (variableList A r).length) q →₀ A) := by
  classical
  exact restrictLinearEquiv (MvPolynomial.C : A →+* PolynomialRing A r)
    (fun a z => by
      ext i
      change MvPolynomial.eval (fun _ => (0 : A)) (MvPolynomial.C a) * _ = a * _
      simp)
    (TensorProduct.equivFinsuppOfBasisLeft (N := A) (listBasis (variableList A r) q))

/-- The coefficient homology is the exterior power over A in every degree. -/
theorem coefficient_homology : Specs.AdvCommAlg.Koszul.PolynomialExample.coefficientHomology.{u} := by
  intro A _ _ r q
  let := evaluationAlgebra A r
  let : Module A (homology A (variableList A r) q) := Module.compHom _ (MvPolynomial.C : A →+* PolynomialRing A r)
  let : Module A ((coefficientComplex A (variableList A r)).X q) :=
    Module.compHom _ (MvPolynomial.C : A →+* PolynomialRing A r)
  have e := (coefficientHomologyTermEquivA A r q).trans
    ((coefficientTermCoordinates A r q).trans
      ((Pi.basisFun A (Fin (variableList A r).length)).exteriorPower q).repr.symm)
  have e' : (⋀[A]^q (Fin (variableList A r).length → A)) ≃ₗ[A]
      (⋀[A]^q (Fin r → A)) := by
    rw [variableList_length]
  exact ⟨e.trans e'⟩

end Coefficients

end AdvCommAlg.Koszul.PolynomialExample
