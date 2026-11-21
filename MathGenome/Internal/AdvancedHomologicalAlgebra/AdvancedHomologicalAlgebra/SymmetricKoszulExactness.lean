import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.SymmetricKoszulExactness
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.Resolution
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.Functoriality
import Mathlib.Data.List.NodupEquivFin
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.ExteriorAlgebra.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Basis

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v
namespace AdvancedHomologicalAlgebra.SymmetricKoszul
attribute [local instance] Classical.propDecidable

variable {R : Type u} [CommRing R] {I : Type v}

@[simp] theorem killVariables_X (s : Set I) (i : I) :
    killVariables (R := R) s (MvPolynomial.X i) =
      if h : i ∈ s then 0 else MvPolynomial.X ⟨i, h⟩ := by
  classical
  simp [killVariables]

theorem variableIdeal_le_ker (s : Set I) :
    variableIdeal (R := R) s ≤ RingHom.ker (killVariables s).toRingHom := by
  apply Ideal.span_le.mpr
  rintro p ⟨i, hi, rfl⟩
  simp [RingHom.mem_ker, hi]

def quotientMap (s : Set I) : (MvPolynomial I R ⧸ variableIdeal s) →ₐ[R]
    MvPolynomial {i : I // i ∉ s} R :=
  Ideal.Quotient.liftₐ _ (killVariables s) (variableIdeal_le_ker s)

def quotientInverse (s : Set I) : MvPolynomial {i : I // i ∉ s} R →ₐ[R]
    (MvPolynomial I R ⧸ variableIdeal s) :=
  MvPolynomial.aeval fun i => Ideal.Quotient.mk _ (MvPolynomial.X i.val)

/-- Killing any set of variables leaves the polynomial ring on its complement. -/
def remainingVariablesEquiv (s : Set I) :
    (MvPolynomial I R ⧸ variableIdeal s) ≃ₐ[R]
      MvPolynomial {i : I // i ∉ s} R := by
  classical
  refine AlgEquiv.ofAlgHom (quotientMap s) (quotientInverse s) ?_ ?_
  · apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, quotientInverse, MvPolynomial.aeval_X]
    change killVariables (R := R) s (MvPolynomial.X i.val) = MvPolynomial.X i
    simp [i.property]
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    change quotientInverse s (killVariables s (MvPolynomial.X i)) =
      Ideal.Quotient.mk _ (MvPolynomial.X i)
    by_cases hi : i ∈ s
    · rw [killVariables_X, dite_eq_left hi, map_zero]
      symm
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, hi, rfl⟩)
    · simp [hi, quotientInverse]

@[simp] theorem remainingVariablesEquiv_mk (s : Set I) (p : MvPolynomial I R) :
    remainingVariablesEquiv s (Ideal.Quotient.mk _ p) = killVariables s p := rfl

theorem quotient_identification :
    Specs.AdvancedHomologicalAlgebra.SymmetricKoszul.QuotientIdentification.{u,v} := by
  intro R _ I s
  exact ⟨remainingVariablesEquiv s, remainingVariablesEquiv_mk s⟩

/-- This uses regularity of a polynomial variable, not a domain assumption. -/
theorem variable_regular_mod_others (s : Set I) (i : I) (hi : i ∉ s) :
    IsSMulRegular (MvPolynomial I R ⧸ variableIdeal s) (MvPolynomial.X (R := R) i) := by
  classical
  intro a b hab
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  apply (remainingVariablesEquiv s).injective
  change killVariables s a = killVariables s b
  apply (MvPolynomial.isRegular_X (R := R) (n := (⟨i, hi⟩ : {j : I // j ∉ s}))).left
  have h := congrArg (remainingVariablesEquiv s) hab
  change remainingVariablesEquiv s (Ideal.Quotient.mk _ (MvPolynomial.X i * a)) =
    remainingVariablesEquiv s (Ideal.Quotient.mk _ (MvPolynomial.X i * b)) at h
  simpa [hi] using h

theorem variable_regularity :
    Specs.AdvancedHomologicalAlgebra.SymmetricKoszul.VariableRegularity.{u,v} := by
  intro R _ I s i hi
  exact variable_regular_mod_others s i hi

theorem listIdeal_variableList (l : List I) :
    AdvCommAlg.Koszul.listIdeal (variableList (R := R) l) = variableIdeal {i | i ∈ l} := by
  unfold AdvCommAlg.Koszul.listIdeal variableIdeal
  congr 1
  ext p
  simp [variableList, Set.mem_image]

/-- Every finite list of distinct variables is weakly regular in the whole ring. -/
theorem finite_variables_weaklyRegular (l : List I) (hl : l.Nodup) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial I R) (variableList (R := R) l) := by
  constructor
  intro j hj
  have hjl : j < l.length := by simpa [variableList] using hj
  have hid : l[j] ∉ l.take j := by
    intro h
    obtain ⟨k, hk, hkj⟩ := List.mem_take_iff_getElem.mp h
    have : k = j := hl.getElem_inj.mp hkj
    omega
  have heq :
      Ideal.ofList ((variableList (R := R) l).take j) •
        (⊤ : Submodule (MvPolynomial I R) (MvPolynomial I R)) =
      variableIdeal (R := R) {i | i ∈ l.take j} := by
    simp only [Ideal.smul_eq_mul, Ideal.mul_top]
    rw [show (variableList (R := R) l).take j = variableList (l.take j) by
      simp [variableList]]
    exact listIdeal_variableList (l.take j)
  let e := Submodule.quotEquivOfEq _ _ heq
  apply (e.isSMulRegular_congr _).mpr
  simpa [variableList] using variable_regular_mod_others (R := R) {i | i ∈ l.take j} l[j] hid

theorem finite_weak_regularity :
    Specs.AdvancedHomologicalAlgebra.SymmetricKoszul.FiniteWeakRegularity.{u,v} := by
  intro R _ I l hl
  exact finite_variables_weaklyRegular l hl

theorem finite_exactness :
    Specs.AdvancedHomologicalAlgebra.SymmetricKoszul.FiniteExactness.{u,v} := by
  intro R _ I l hl n hn
  exact AdvCommAlg.Koszul.listComplex_exactAt _ (finite_variables_weaklyRegular l hl) n hn

theorem finite_deletion_formula :
    Specs.AdvancedHomologicalAlgebra.SymmetricKoszul.FiniteDeletionFormula.{u,v} := by
  intro R _ I l n x
  exact AdvCommAlg.Koszul.differential_ιMulti _ n x

theorem finite_augmented_exactness :
    Specs.AdvancedHomologicalAlgebra.SymmetricKoszul.FiniteAugmentedExactness.{u,v} := by
  intro R _ I l
  constructor
  · have h := (AdvCommAlg.Koszul.augmentation_exact (variableList (R := R) l)).moduleCat_range_eq_ker
    change LinearMap.range (AdvCommAlg.Koszul.differential
        (AdvCommAlg.Koszul.listForm (variableList l)) 0) =
      LinearMap.ker ((AdvCommAlg.Koszul.listIdeal (variableList l)).mkQ.comp
        (exteriorPower.zeroEquiv (MvPolynomial I R) _).toLinearMap) at h
    rw [h]
    ext z
    simp only [LinearMap.mem_ker, finiteAugmentation, LinearMap.comp_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, listIdeal_variableList]
  · exact (Submodule.mkQ_surjective _).comp (exteriorPower.zeroEquiv (MvPolynomial I R) _).surjective

theorem finite_zero_homology :
    Specs.AdvancedHomologicalAlgebra.SymmetricKoszul.FiniteZeroHomology.{u,v} := by
  intro R _ I l
  have heq : AdvCommAlg.Koszul.listSubmodule (MvPolynomial I R) (variableList l) =
      variableIdeal (R := R) {i | i ∈ l} := by
    simp only [AdvCommAlg.Koszul.listSubmodule, Ideal.smul_eq_mul, Ideal.mul_top]
    exact listIdeal_variableList l
  exact ⟨(AdvCommAlg.Koszul.homologyZeroEquiv (MvPolynomial I R) (variableList l)).trans
    (Submodule.quotEquivOfEq _ _ heq)⟩

/-- The augmentation quotient for all variables, without a finiteness assumption. -/
def allVariablesEquiv :
    (MvPolynomial I R ⧸ variableIdeal (Set.univ : Set I)) ≃ₐ[R] R := by
  let f : (MvPolynomial I R ⧸ variableIdeal (Set.univ : Set I)) →ₐ[R] R :=
    Ideal.Quotient.liftₐ _ (MvPolynomial.aeval fun _ : I => (0 : R)) (by
      change variableIdeal (R := R) (Set.univ : Set I) ≤ RingHom.ker _
      apply Ideal.span_le.mpr
      rintro p ⟨i, hi, rfl⟩
      simp [RingHom.mem_ker])
  refine AlgEquiv.ofAlgHom f (Algebra.ofId R _) ?_ ?_
  · ext
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    change (Algebra.ofId R (MvPolynomial I R ⧸ variableIdeal (Set.univ : Set I)))
      (MvPolynomial.aeval (fun _ : I => (0 : R))
      (MvPolynomial.X i)) = Ideal.Quotient.mk _ (MvPolynomial.X i)
    rw [MvPolynomial.aeval_X, map_zero]
    symm
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, Set.mem_univ i, rfl⟩)

theorem all_variables_quotient :
    Specs.AdvancedHomologicalAlgebra.SymmetricKoszul.AllVariablesQuotient.{u,v} := by
  intro R _ I
  refine ⟨allVariablesEquiv, ?_⟩
  intro p
  change MvPolynomial.eval₂ (RingHom.id R) (fun _ : I => (0 : R)) p = _
  simp

section FiniteSupport
variable {A : Type*} [CommRing A]

/-- Extend a finitely supported vector on a finite subset by zero. -/
def finiteInclusion (s : Finset I) : (s →₀ A) →ₗ[A] (I →₀ A) :=
  Finsupp.lmapDomain A A (Subtype.val : s → I)

@[simp] theorem finiteInclusion_single (s : Finset I) (i : s) (a : A) :
    finiteInclusion s (Finsupp.single i a) = Finsupp.single i.val a := by
  simp [finiteInclusion]

/-- Reading the selected coordinates retracts extension by zero. -/
theorem finiteInclusion_retraction (s : Finset I) :
    (Finsupp.lsubtypeDomain (R := A) (s : Set I)).comp (finiteInclusion s) =
      LinearMap.id := by
  apply Finsupp.lhom_ext'
  intro i
  apply LinearMap.ext
  intro a
  apply Finsupp.ext
  intro j
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.id_apply,
    finiteInclusion_single]
  change (Finsupp.single i.val a) j.val = (Finsupp.single i a) j
  simp only [Finsupp.single_apply]
  congr 1
  exact propext Subtype.ext_iff.symm

theorem finiteExteriorInclusion_injective (s : Finset I) (n : ℕ) :
    Function.Injective (exteriorPower.map n (finiteInclusion (A := A) s)) :=
  exteriorPower.map_injective (Finsupp.lsubtypeDomain (s : Set I))
    (finiteInclusion_retraction s)

/-- Enlarging a finite subset enlarges its exterior-chain range. -/
theorem finiteExteriorRange_mono {s t : Finset I} (h : s ⊆ t) (n : ℕ) :
    LinearMap.range (exteriorPower.map n (finiteInclusion (A := A) s)) ≤
      LinearMap.range (exteriorPower.map n (finiteInclusion (A := A) t)) := by
  let j : s → t := fun i => ⟨i.val, h i.property⟩
  have hc : (finiteInclusion (A := A) t).comp (Finsupp.lmapDomain A A j) =
      finiteInclusion s := by
    unfold finiteInclusion
    rw [← Finsupp.lmapDomain_comp]
    rfl
  rw [← hc, exteriorPower.map_comp]
  exact LinearMap.range_comp_le_range _ _

/-- Every exterior chain involves only a finite subset of the free generators. -/
theorem exterior_finite_support (n : ℕ) (z : ⋀[A]^n (I →₀ A)) :
    ∃ (s : Finset I) (w : ⋀[A]^n (s →₀ A)),
      exteriorPower.map n (finiteInclusion s) w = z := by
  classical
  let U : Finset I → Submodule A (⋀[A]^n (I →₀ A)) :=
    fun s => LinearMap.range (exteriorPower.map n (finiteInclusion s))
  have hdir : Directed (· ≤ ·) U := fun s t =>
    ⟨s ∪ t, finiteExteriorRange_mono Finset.subset_union_left n,
      finiteExteriorRange_mono Finset.subset_union_right n⟩
  have htop : iSup U = ⊤ := by
    apply top_unique
    rw [← exteriorPower.ιMulti_span_of_span A n (I →₀ A)
      (Finsupp.basisSingleOne.span_eq)]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    choose j hj using fun k => hv (Set.mem_range_self k)
    let s : Finset I := Finset.univ.image j
    let w : Fin n → (s →₀ A) := fun k =>
      Finsupp.single ⟨j k, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩ 1
    apply (le_iSup U s)
    refine ⟨exteriorPower.ιMulti A n w, ?_⟩
    rw [exteriorPower.map_apply_ιMulti]
    congr 1
    funext k
    exact (finiteInclusion_single s _ 1).trans (hj k)
  have hz : z ∈ iSup U := by rw [htop]; trivial
  obtain ⟨s, w, hw⟩ := (Submodule.mem_iSup_of_directed U hdir).mp hz
  exact ⟨s, w, hw⟩
end FiniteSupport

/-- Enumerate a finite subset in the order of its duplicate-free list. -/
def finiteEnumeration (s : Finset I) :
    Fin (variableList (R := R) s.toList).length ≃ s :=
  ((finCongr (by simp [variableList])).trans
    (s.nodup_toList.getEquiv s.toList)).trans
      (Equiv.subtypeEquivRight (fun i => Finset.mem_toList))

/-- The standard finite coordinates and the direct sum on that finite subset. -/
def finiteCoordinates (s : Finset I) :
    (Fin (variableList (R := R) s.toList).length → MvPolynomial I R) ≃ₗ[MvPolynomial I R]
      (s →₀ MvPolynomial I R) :=
  (Pi.basisFun (MvPolynomial I R) _).equiv Finsupp.basisSingleOne (finiteEnumeration s)

@[simp] theorem polynomialForm_single (i : I) (p : MvPolynomial I R) :
    polynomialForm (Finsupp.single i p) = p * MvPolynomial.X i := by
  simp [polynomialForm]

/-- Compatibility of the finite list form with inclusion into all variables. -/
theorem finiteCoordinates_form (s : Finset I) :
    (polynomialForm (R := R)).comp
      ((finiteInclusion s).comp (finiteCoordinates s).toLinearMap) =
        AdvCommAlg.Koszul.listForm (variableList s.toList) := by
  apply (Pi.basisFun (MvPolynomial I R) _).ext
  intro j
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, finiteCoordinates,
    Module.Basis.equiv_apply, Finsupp.coe_basisSingleOne, finiteInclusion_single,
    polynomialForm_single, one_mul, AdvCommAlg.Koszul.listForm_basis]
  simp [finiteEnumeration, variableList, List.get_eq_getElem]

/-- Finite acyclicity expressed as cycle lifting for the actual differential. -/
theorem finite_cycle_lift (l : List I) (hl : l.Nodup) (n : ℕ)
    (z : ⋀[MvPolynomial I R]^(n+1)
      (Fin (variableList (R := R) l).length → MvPolynomial I R))
    (hz : AdvCommAlg.Koszul.differential (AdvCommAlg.Koszul.listForm (variableList l)) n z = 0) :
    ∃ y, AdvCommAlg.Koszul.differential (AdvCommAlg.Koszul.listForm (variableList l)) (n+1) y = z := by
  have h := finite_exactness R I l hl (n+1) (Nat.zero_lt_succ n)
  have h' := (HomologicalComplex.exactAt_iff' (K :=
    AdvCommAlg.Koszul.listComplex (variableList (R := R) l))
    (j := n+1) (i := n+2) (k := n) (by simp) (by simp)).mp h
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff] at h'
  simp only [AdvCommAlg.Koszul.listComplex, AdvCommAlg.Koszul.complex,
    HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', ChainComplex.of_d] at h'
  rw [show n + 2 = (n+1)+1 by omega, ChainComplex.of_d] at h'
  exact h' z hz

/-- Every positive-degree cycle in the arbitrary-rank coordinate complex is a boundary. -/
theorem polynomial_cycle_lift (n : ℕ)
    (z : ⋀[MvPolynomial I R]^(n+1) (I →₀ MvPolynomial I R))
    (hz : AdvCommAlg.Koszul.differential polynomialForm n z = 0) :
    ∃ y, AdvCommAlg.Koszul.differential polynomialForm (n+1) y = z := by
  obtain ⟨s, w, rfl⟩ := exterior_finite_support (n+1) z
  let e := finiteCoordinates (R := R) s
  obtain ⟨v, rfl⟩ := exteriorPower.map_surjective (n := n+1) e.surjective w
  let φ := (finiteInclusion s).comp e.toLinearMap
  have hn (k : ℕ) := AdvCommAlg.Koszul.differential_naturality
    (AdvCommAlg.Koszul.listForm (variableList (R := R) s.toList)) polynomialForm φ
    (finiteCoordinates_form s) k
  have hinj : Function.Injective (exteriorPower.map n φ) := by
    rw [exteriorPower.map_comp]
    exact (finiteExteriorInclusion_injective s n).comp
      (exteriorPower.map_injective e.symm.toLinearMap (by ext; simp))
  have hv : AdvCommAlg.Koszul.differential
      (AdvCommAlg.Koszul.listForm (variableList (R := R) s.toList)) n v = 0 := by
    apply hinj
    rw [map_zero, ← LinearMap.comp_apply, ← hn n]
    simpa [φ, exteriorPower.map_comp] using hz
  obtain ⟨y, hy⟩ := finite_cycle_lift s.toList s.nodup_toList n v hv
  refine ⟨exteriorPower.map (n+2) φ y, ?_⟩
  rw [← LinearMap.comp_apply, hn (n+1), LinearMap.comp_apply, hy]
  simp [φ, exteriorPower.map_comp]

/-- The image of the universal form is precisely the ideal of all variables. -/
theorem polynomialForm_range :
    LinearMap.range (polynomialForm (R := R) (I := I)) =
      variableIdeal (Set.univ : Set I) := by
  rw [polynomialForm, Finsupp.range_linearCombination, variableIdeal, Set.image_univ]

@[simp] theorem polynomialAugmentation_apply
    (z : ⋀[MvPolynomial I R]^0 (I →₀ MvPolynomial I R)) :
    polynomialAugmentation z = MvPolynomial.constantCoeff
      (exteriorPower.zeroEquiv (MvPolynomial I R) _ z) := by
  simp [polynomialAugmentation]

theorem polynomial_augmented_lift
    (z : ⋀[MvPolynomial I R]^0 (I →₀ MvPolynomial I R))
    (hz : polynomialAugmentation z = 0) :
    ∃ y, AdvCommAlg.Koszul.differential polynomialForm 0 y = z := by
  let p := exteriorPower.zeroEquiv (MvPolynomial I R) _ z
  have hp : MvPolynomial.constantCoeff p = 0 := by simpa [p] using hz
  obtain ⟨e, he⟩ := all_variables_quotient R I
  have hmem : p ∈ variableIdeal (Set.univ : Set I) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply e.injective
    rw [he, map_zero, hp]
  rw [← polynomialForm_range] at hmem
  obtain ⟨v, hv⟩ := hmem
  refine ⟨(exteriorPower.oneEquiv (MvPolynomial I R) _).symm v, ?_⟩
  apply (exteriorPower.zeroEquiv (MvPolynomial I R) _).injective
  rw [AdvCommAlg.Koszul.differential_one, LinearEquiv.apply_symm_apply, hv]

theorem polynomial_augmentation_differential
    (z : ⋀[MvPolynomial I R]^1 (I →₀ MvPolynomial I R)) :
    polynomialAugmentation (AdvCommAlg.Koszul.differential polynomialForm 0 z) = 0 := by
  rw [polynomialAugmentation_apply, AdvCommAlg.Koszul.differential_one]
  have hm : polynomialForm (exteriorPower.oneEquiv (MvPolynomial I R) _ z) ∈
      variableIdeal (Set.univ : Set I) := by
    rw [← polynomialForm_range]
    exact LinearMap.mem_range_self _ _
  obtain ⟨e, he⟩ := all_variables_quotient R I
  rw [← he, Ideal.Quotient.eq_zero_iff_mem.mpr hm, map_zero]

theorem polynomial_augmentation_surjective :
    Function.Surjective (polynomialAugmentation (R := R) (I := I)) := by
  intro r
  refine ⟨(exteriorPower.zeroEquiv (MvPolynomial I R) _).symm (MvPolynomial.C r), ?_⟩
  simp

/-- The finite-subset union proves the augmented coordinate complex exact in arbitrary rank. -/
theorem arbitrary_rank_exactness :
    Specs.AdvancedHomologicalAlgebra.SymmetricKoszul.ArbitraryRankExactness.{u,v} := by
  intro R _ I
  exact ⟨polynomial_cycle_lift, polynomial_augmented_lift,
    polynomial_augmentation_differential, polynomial_augmentation_surjective⟩

section ExteriorBaseChange
variable {K : Type*} [CommRing K] {N : Type*} [AddCommGroup N] [Module K N]
  {J : Type*} [LinearOrder J] (b : Module.Basis J K N)
  (S : Type*) [CommRing S] [Algebra K S]
open scoped TensorProduct

/-- Degree-by-degree exterior base change for a free module of arbitrary rank. -/
def exteriorBaseChange (n : ℕ) :
    (S ⊗[K] (⋀[K]^n N)) ≃ₗ[S] (⋀[S]^n (S ⊗[K] N)) :=
  ((b.exteriorPower n).baseChange S).equiv ((b.baseChange S).exteriorPower n) (Equiv.refl _)

theorem exteriorAlgebra_baseChange_word (n : ℕ) (x : Fin n → N) :
    ExteriorAlgebra.baseChangeEquiv K N S (1 ⊗ₜ[K] ExteriorAlgebra.ιMulti K n x) =
      ExteriorAlgebra.ιMulti S n (fun i => 1 ⊗ₜ[K] x i) := by
  induction n with
  | zero => simp [ExteriorAlgebra.ιMulti_zero_apply, Algebra.TensorProduct.one_def]
  | succ n ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
      show (1 : S) ⊗ₜ[K] (ExteriorAlgebra.ι K (x 0) *
        ExteriorAlgebra.ιMulti K n (Matrix.vecTail x)) =
        (1 ⊗ₜ[K] ExteriorAlgebra.ι K (x 0)) *
          (1 ⊗ₜ[K] ExteriorAlgebra.ιMulti K n (Matrix.vecTail x)) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul],
      map_mul, ExteriorAlgebra.baseChangeEquiv_apply, ih]
    rfl

/-- The basis equivalence agrees with the canonical exterior-algebra map. -/
theorem exteriorBaseChange_subtype (n : ℕ) :
    (⋀[S]^n (S ⊗[K] N)).subtype.comp (exteriorBaseChange b S n).toLinearMap =
      (ExteriorAlgebra.baseChangeEquiv K N S).toLinearMap.comp
        ((⋀[K]^n N).subtype.baseChange S) := by
  apply ((b.exteriorPower n).baseChange S).ext
  intro s
  simp only [LinearMap.comp_apply, exteriorBaseChange, LinearEquiv.coe_coe,
    Module.Basis.equiv_apply, Equiv.refl_apply]
  simp only [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul,
    Submodule.subtype_apply, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family, exteriorPower.ιMulti_apply_coe]
  change _ = ExteriorAlgebra.baseChangeEquiv K N S
    (1 ⊗ₜ[K] ExteriorAlgebra.ιMulti K n _)
  rw [exteriorAlgebra_baseChange_word]
  simp [Function.comp_def]

/-- Canonical formula on pure tensors of arbitrary wedges, not only basis wedges. -/
theorem exteriorBaseChange_tmul (n : ℕ) (p : S) (x : Fin n → N) :
    exteriorBaseChange b S n (p ⊗ₜ[K] exteriorPower.ιMulti K n x) =
      p • exteriorPower.ιMulti S n (fun i => 1 ⊗ₜ[K] x i) := by
  apply Subtype.ext
  have h := LinearMap.congr_fun (exteriorBaseChange_subtype b S n)
    (p ⊗ₜ[K] exteriorPower.ιMulti K n x)
  change (exteriorBaseChange b S n (p ⊗ₜ[K] exteriorPower.ιMulti K n x) :
    ExteriorAlgebra S (S ⊗[K] N)) = ExteriorAlgebra.baseChangeEquiv K N S
      (p ⊗ₜ[K] ExteriorAlgebra.ιMulti K n x) at h
  rw [h, show p ⊗ₜ[K] ExteriorAlgebra.ιMulti K n x =
    p • ((1 : S) ⊗ₜ[K] ExteriorAlgebra.ιMulti K n x) by
      simp [TensorProduct.smul_tmul'], map_smul, exteriorAlgebra_baseChange_word]
  rfl
end ExteriorBaseChange

/-- Naturality with independently sized module universes. -/
theorem differential_map {A : Type*} [CommRing A]
    {E : Type*} [AddCommGroup E] [Module A E]
    {F : Type*} [AddCommGroup F] [Module A F]
    (a : E →ₗ[A] A) (b : F →ₗ[A] A) (φ : E →ₗ[A] F) (h : b.comp φ = a) (n : ℕ) :
    (AdvCommAlg.Koszul.differential b n).comp (exteriorPower.map (n+1) φ) =
      (exteriorPower.map n φ).comp (AdvCommAlg.Koszul.differential a n) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro x
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, AdvCommAlg.Koszul.differential_ιMulti, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← LinearMap.congr_fun h (x i)]
  rfl

section GeneralCoordinateExactness
variable {A : Type*} [CommRing A] (f : I → A)

private def subsetEnumeration (s : Finset I) : Fin (s.toList.map f).length ≃ s :=
  ((finCongr (by simp)).trans (s.nodup_toList.getEquiv s.toList)).trans
    (Equiv.subtypeEquivRight (fun i => Finset.mem_toList))

private def subsetCoordinates (s : Finset I) :
    (Fin (s.toList.map f).length → A) ≃ₗ[A] (s →₀ A) :=
  (Pi.basisFun A _).equiv Finsupp.basisSingleOne (subsetEnumeration f s)

private theorem subsetCoordinates_form (s : Finset I) :
    (Finsupp.linearCombination A f).comp
      ((finiteInclusion s).comp (subsetCoordinates f s).toLinearMap) =
        AdvCommAlg.Koszul.listForm (s.toList.map f) := by
  apply (Pi.basisFun A _).ext
  intro j
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, subsetCoordinates,
    Module.Basis.equiv_apply, Finsupp.coe_basisSingleOne, finiteInclusion_single,
    Finsupp.linearCombination_single, smul_eq_mul, one_mul, AdvCommAlg.Koszul.listForm_basis]
  simp [subsetEnumeration, List.get_eq_getElem]

/-- Arbitrary-rank acyclicity from acyclicity on each finite set of generators. -/
theorem coordinate_cycle_lift
    (hf : ∀ (s : Finset I), RingTheory.Sequence.IsWeaklyRegular A (s.toList.map f))
    (n : ℕ) (z : ⋀[A]^(n+1) (I →₀ A))
    (hz : AdvCommAlg.Koszul.differential (Finsupp.linearCombination A f) n z = 0) :
    ∃ y, AdvCommAlg.Koszul.differential (Finsupp.linearCombination A f) (n+1) y = z := by
  obtain ⟨s, w, rfl⟩ := exterior_finite_support (n+1) z
  let e := subsetCoordinates f s
  obtain ⟨v, rfl⟩ := exteriorPower.map_surjective (n := n+1) e.surjective w
  let φ := (finiteInclusion s).comp e.toLinearMap
  have hn (k : ℕ) := differential_map
    (AdvCommAlg.Koszul.listForm (s.toList.map f)) (Finsupp.linearCombination A f) φ
    (subsetCoordinates_form f s) k
  have hinj : Function.Injective (exteriorPower.map n φ) := by
    rw [exteriorPower.map_comp]
    exact (finiteExteriorInclusion_injective s n).comp
      (exteriorPower.map_injective e.symm.toLinearMap (by ext; simp))
  have hv : AdvCommAlg.Koszul.differential (AdvCommAlg.Koszul.listForm (s.toList.map f)) n v = 0 := by
    apply hinj
    rw [map_zero, ← LinearMap.comp_apply, ← hn n]
    simpa [φ, exteriorPower.map_comp] using hz
  have h := AdvCommAlg.Koszul.listComplex_exactAt (s.toList.map f) (hf s)
    (n+1) (Nat.zero_lt_succ n)
  have h' := (HomologicalComplex.exactAt_iff' (K :=
    AdvCommAlg.Koszul.listComplex (s.toList.map f))
    (j := n+1) (i := n+2) (k := n) (by simp) (by simp)).mp h
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff] at h'
  simp only [AdvCommAlg.Koszul.listComplex, AdvCommAlg.Koszul.complex,
    HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', ChainComplex.of_d] at h'
  rw [show n + 2 = (n+1)+1 by omega, ChainComplex.of_d] at h'
  obtain ⟨y, hy⟩ := h' v hv
  change AdvCommAlg.Koszul.differential (AdvCommAlg.Koszul.listForm (s.toList.map f)) (n+1) y = v at hy
  refine ⟨exteriorPower.map (n+2) φ y, ?_⟩
  rw [← LinearMap.comp_apply, hn (n+1), LinearMap.comp_apply, hy]
  simp [φ, exteriorPower.map_comp]
end GeneralCoordinateExactness

/-- Positive acyclicity for a free module, from regularity on finite basis subsets. -/
theorem basis_cycle_lift {A : Type*} [CommRing A] {E : Type*}
    [AddCommGroup E] [Module A E] (c : Module.Basis I A E) (a : E →ₗ[A] A)
    (ha : ∀ s : Finset I, RingTheory.Sequence.IsWeaklyRegular A
      (s.toList.map (fun i => a (c i)))) (n : ℕ) (z : ⋀[A]^(n+1) E)
    (hz : AdvCommAlg.Koszul.differential a n z = 0) :
    ∃ y, AdvCommAlg.Koszul.differential a (n+1) y = z := by
  let f : I → A := fun i => a (c i)
  have hc : (Finsupp.linearCombination A f).comp c.repr.toLinearMap = a := by
    apply c.ext
    intro i
    simp [f]
  have hn (k : ℕ) := differential_map a (Finsupp.linearCombination A f)
    c.repr.toLinearMap hc k
  have hz' : AdvCommAlg.Koszul.differential (Finsupp.linearCombination A f) n
      (exteriorPower.map (n+1) c.repr.toLinearMap z) = 0 := by
    rw [← LinearMap.comp_apply, hn n, LinearMap.comp_apply, hz, map_zero]
  obtain ⟨v, hv⟩ := coordinate_cycle_lift f ha n _ hz'
  obtain ⟨y, rfl⟩ := exteriorPower.map_surjective (n := n+2) c.repr.surjective v
  refine ⟨y, ?_⟩
  apply exteriorPower.map_injective (f := c.repr.toLinearMap) c.repr.symm.toLinearMap
    (by ext; simp) (n := n+1)
  rw [← LinearMap.comp_apply, ← hn (n+1)]
  exact hv

section SymmetricDifferential
variable {M : Type*} [AddCommGroup M] [Module R M] [LinearOrder I]
  (b : Module.Basis I R M)
open scoped TensorProduct

/-- Extend the symmetric generator map by scalars to the coefficient ring. -/
def symmetricForm :
    (SymmetricAlgebra R M ⊗[R] M) →ₗ[SymmetricAlgebra R M] SymmetricAlgebra R M :=
  (SymmetricAlgebra.ι R M).liftBaseChange (SymmetricAlgebra R M)

/-- The canonical Koszul differential on the original tensor terms. -/
def symmetricDifferential (n : ℕ) :
    Term R M (n+1) →ₗ[SymmetricAlgebra R M] Term R M n :=
  (exteriorBaseChange b (SymmetricAlgebra R M) n).symm.toLinearMap.comp
    ((AdvCommAlg.Koszul.differential symmetricForm n).comp
      (exteriorBaseChange b (SymmetricAlgebra R M) (n+1)).toLinearMap)

/-- The original signed-deletion formula, including arbitrary module inputs. -/
theorem symmetricDifferential_formula (n : ℕ) (p : SymmetricAlgebra R M) (x : Fin (n+1) → M) :
    symmetricDifferential b n (p ⊗ₜ[R] exteriorPower.ιMulti R (n+1) x) =
      ∑ i : Fin (n+1), (-1 : R)^i.val •
        ((p * SymmetricAlgebra.ι R M (x i)) ⊗ₜ[R]
          exteriorPower.ιMulti R n (x ∘ i.succAbove)) := by
  apply (exteriorBaseChange b (SymmetricAlgebra R M) n).injective
  simp only [symmetricDifferential, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, exteriorBaseChange_tmul, map_smul,
    AdvCommAlg.Koszul.differential_ιMulti, symmetricForm, LinearMap.liftBaseChange_tmul,
    one_smul, map_sum]
  simp only [TensorProduct.smul_tmul', exteriorBaseChange_tmul]
  simp only [Finset.smul_sum, smul_smul, Algebra.smul_def, map_pow, map_neg, map_one]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ring

theorem symmetricDifferential_square (n : ℕ) :
    (symmetricDifferential b n).comp (symmetricDifferential b (n+1)) = 0 := by
  apply LinearMap.ext
  intro z
  apply (exteriorBaseChange b (SymmetricAlgebra R M) n).injective
  simp only [LinearMap.comp_apply, symmetricDifferential, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, LinearMap.zero_apply, map_zero]
  exact LinearMap.congr_fun (AdvCommAlg.Koszul.differential_comp symmetricForm n) _

/-- A finite list of symmetric generators is weakly regular over the original ring. -/
theorem symmetric_generators_weaklyRegular (l : List I) (hl : l.Nodup) :
    RingTheory.Sequence.IsWeaklyRegular (SymmetricAlgebra R M)
      (l.map (fun i => SymmetricAlgebra.ι R M (b i))) := by
  let e := SymmetricAlgebra.equivMvPolynomial b
  have h : List.Forall₂ (fun (r : SymmetricAlgebra R M) (s : MvPolynomial I R) =>
      ∀ x, e (r • x) = s • e x)
      (l.map (fun i => SymmetricAlgebra.ι R M (b i))) (variableList (R := R) l) := by
    rw [variableList, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.Forall₂.imp (fun i j hij => by subst j; intro x; simp [e])
      (List.forall₂_same.mpr (fun _ _ => rfl))
  exact (AddEquiv.isWeaklyRegular_congr (e := e.toRingEquiv.toAddEquiv) h).mpr
    (finite_variables_weaklyRegular l hl)
/-- Positive-degree exactness on the tensor terms in the source. -/
theorem symmetric_cycle_lift (n : ℕ) (z : Term R M (n+1))
    (hz : symmetricDifferential b n z = 0) :
    ∃ y, symmetricDifferential b (n+1) y = z := by
  let S := SymmetricAlgebra R M
  let e (k : ℕ) := exteriorBaseChange b S k
  have hz' : AdvCommAlg.Koszul.differential symmetricForm n (e (n+1) z) = 0 := by
    have h := congrArg (e n) hz
    simpa [symmetricDifferential, e, S] using h
  have hr (s : Finset I) : RingTheory.Sequence.IsWeaklyRegular S
      (s.toList.map (fun i => symmetricForm ((b.baseChange S) i))) := by
    simpa [symmetricForm] using symmetric_generators_weaklyRegular b s.toList s.nodup_toList
  obtain ⟨v, hv⟩ := basis_cycle_lift (b.baseChange S) symmetricForm hr n _ hz'
  refine ⟨(e (n+2)).symm v, ?_⟩
  change (e n.succ).symm
    (AdvCommAlg.Koszul.differential symmetricForm (n+1) ((e (n+2)) ((e (n+2)).symm v))) = z
  rw [LinearEquiv.apply_symm_apply, hv, LinearEquiv.symm_apply_apply]

theorem symmetric_zero_comparison (z : Term R M 0) :
    exteriorPower.zeroEquiv (SymmetricAlgebra R M) _
      (exteriorBaseChange b (SymmetricAlgebra R M) 0 z) = zeroTermEquiv R M z := by
  induction z using TensorProduct.inductionOn with
  | tmul p w =>
    obtain ⟨r, rfl⟩ := (exteriorPower.zeroEquiv R M).symm.surjective w
    simp [exteriorPower.zeroEquiv_symm_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      exteriorBaseChange_tmul, zeroTermEquiv, Algebra.smul_def, mul_comm]
  | add z w hz hw => simpa only [map_add, hz, hw]

theorem symmetric_eval_coordinates (p : SymmetricAlgebra R M) :
    SymmetricAlgebra.lift (0 : M →ₗ[R] R) p =
      MvPolynomial.constantCoeff (SymmetricAlgebra.equivMvPolynomial b p) := by
  have h : SymmetricAlgebra.lift (0 : M →ₗ[R] R) =
      (MvPolynomial.aeval (fun _ : I => (0 : R))).comp
        (SymmetricAlgebra.equivMvPolynomial b).toAlgHom := by
    apply SymmetricAlgebra.algHom_ext
    apply b.ext
    intro i
    simp
  rw [h]
  simp

theorem symmetricForm_range : LinearMap.range (symmetricForm (R := R) (M := M)) =
    Ideal.span (Set.range (fun i => SymmetricAlgebra.ι R M (b i))) := by
  rw [LinearMap.range_eq_map, ← (b.baseChange (SymmetricAlgebra R M)).span_eq,
    Submodule.map_span, ← Set.range_comp]
  congr 1
  ext p
  simp [symmetricForm]

include b in
theorem symmetric_eval_mem_range (p : SymmetricAlgebra R M)
    (hp : SymmetricAlgebra.lift (0 : M →ₗ[R] R) p = 0) :
    p ∈ LinearMap.range (symmetricForm (R := R) (M := M)) := by
  let e := SymmetricAlgebra.equivMvPolynomial b
  have hm : e p ∈ variableIdeal (Set.univ : Set I) := by
    obtain ⟨q, hq⟩ := all_variables_quotient R I
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply q.injective
    rw [hq, map_zero, ← symmetric_eval_coordinates b, hp]
  have he : Ideal.map e.toRingHom
      (Ideal.span (Set.range (fun i => SymmetricAlgebra.ι R M (b i)))) =
        variableIdeal (Set.univ : Set I) := by
    rw [Ideal.map_span, ← Set.range_comp, variableIdeal, Set.image_univ]
    congr 1
    ext p
    simp [e]
  rw [← he] at hm
  obtain ⟨q, hq, hpq⟩ := (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp hm
  have hqp : q = p := e.injective hpq
  rw [symmetricForm_range b, ← hqp]
  exact hq

set_option maxRecDepth 2048 in
theorem symmetric_augmented_lift (z : Term R M 0) (hz : augmentation R M z = 0) :
    ∃ y, symmetricDifferential b 0 y = z := by
  obtain ⟨v, hv⟩ := symmetric_eval_mem_range b (zeroTermEquiv R M z) hz
  let S := SymmetricAlgebra R M
  let e (k : ℕ) := exteriorBaseChange b S k
  refine ⟨(e 1).symm ((exteriorPower.oneEquiv S _).symm v), ?_⟩
  apply (zeroTermEquiv R M).injective
  rw [← symmetric_zero_comparison b]
  simpa only [symmetricDifferential, e, S, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, AdvCommAlg.Koszul.differential_one] using hv

theorem symmetric_augmentation_differential (z : Term R M 1) :
    augmentation R M (symmetricDifferential b 0 z) = 0 := by
  have hkill (v : SymmetricAlgebra R M ⊗[R] M) :
      SymmetricAlgebra.lift (0 : M →ₗ[R] R) (symmetricForm v) = 0 := by
    induction v using TensorProduct.inductionOn with
    | tmul p x => simp [symmetricForm]
    | add v w hv hw => simp only [map_add, hv, hw, add_zero]
  unfold augmentation
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearEquiv.coe_coe]
  rw [← symmetric_zero_comparison b]
  simp only [symmetricDifferential, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, AdvCommAlg.Koszul.differential_one]
  exact hkill _

theorem symmetric_augmentation_surjective : Function.Surjective (augmentation R M) := by
  intro r
  refine ⟨(zeroTermEquiv R M).symm (algebraMap R (SymmetricAlgebra R M) r), ?_⟩
  simp [augmentation]

def symmetricZeroHomologyEquiv :
    (Term R M 0 ⧸ LinearMap.range ((symmetricDifferential b 0).restrictScalars R)) ≃ₗ[R] R := by
  have h : LinearMap.range ((symmetricDifferential b 0).restrictScalars R) =
      LinearMap.ker (augmentation R M) := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact symmetric_augmentation_differential b y
    · intro hz
      exact symmetric_augmented_lift b z hz
  exact (Submodule.quotEquivOfEq _ _ h).trans
    ((augmentation R M).quotKerEquivOfSurjective symmetric_augmentation_surjective)

end SymmetricDifferential

/-- All augmented exactness conclusions on the original terms, before grading by total weight. -/
theorem unweighted_exactness :
    Specs.AdvancedHomologicalAlgebra.SymmetricKoszul.UnweightedExactness.{u,v} := by
  intro R _ M _ _ I b
  classical
  letI : LinearOrder I := linearOrderOfSTO WellOrderingRel
  exact ⟨symmetricDifferential b, symmetricDifferential_formula b, symmetricDifferential_square b,
    symmetric_augmentation_differential b, symmetric_augmentation_surjective,
    symmetric_cycle_lift b, symmetric_augmented_lift b, ⟨symmetricZeroHomologyEquiv b⟩⟩

section TotalWeight
variable {M : Type*} [AddCommGroup M] [Module R M] (b : Module.Basis I R M)
open scoped TensorProduct

def polynomialWeightProjection (a n : ℕ) :
    SymmetricAlgebra R M →ₗ[R] SymmetricAlgebra R M := by
  classical
  exact b.symmetricAlgebra.constr R fun m =>
    if n + m.degree = a then b.symmetricAlgebra m else 0

def weightProjection (a n : ℕ) : Term R M n →ₗ[R] Term R M n :=
  TensorProduct.map (polynomialWeightProjection b a n) LinearMap.id

@[simp] theorem weightProjection_tmul (a n : ℕ) (m : I →₀ ℕ) (w : ⋀[R]^n M) :
    weightProjection b a n (b.symmetricAlgebra m ⊗ₜ[R] w) =
      if n + m.degree = a then b.symmetricAlgebra m ⊗ₜ[R] w else 0 := by
  classical
  simp only [weightProjection, TensorProduct.map_tmul, polynomialWeightProjection,
    Module.Basis.constr_basis, LinearMap.id_apply]
  split <;> simp_all

theorem weightProjection_eq_self (a n : ℕ) (z : Term R M n)
    (hz : z ∈ weightSpace b a n) : weightProjection b a n z = z := by
  classical
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨m, w, hmw, rfl⟩ := hz
      simp [hmw]
  | zero => simp
  | add x y hx hy hpx hpy => simp [hpx, hpy]
  | smul r x hx hpx => simp [hpx]

theorem weightProjection_eq_zero (a c n : ℕ) (hca : c ≠ a) (z : Term R M n)
    (hz : z ∈ weightSpace b c n) : weightProjection b a n z = 0 := by
  classical
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨m, w, hmw, rfl⟩ := hz
      simp [hmw, hca]
  | zero => simp
  | add x y hx hy hpx hpy => simp [hpx, hpy]
  | smul r x hx hpx => simp [hpx]

theorem weightProjection_mem (a n : ℕ) (z : Term R M n) :
    weightProjection b a n z ∈ weightSpace b a n := by
  classical
  induction z using TensorProduct.inductionOn with
  | tmul p w =>
      rw [← b.symmetricAlgebra.linearCombination_repr p, Finsupp.linearCombination_apply]
      simp only [Finsupp.sum, TensorProduct.sum_tmul, TensorProduct.smul_tmul, map_sum]
      apply Submodule.sum_mem
      intro m hm
      rw [weightProjection_tmul]
      split
      · exact Submodule.subset_span ⟨m, (b.symmetricAlgebra.repr p) m • w, by assumption, rfl⟩
      · exact Submodule.zero_mem _
  | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy

/-- The projection keeps a homogeneous chain of the chosen weight and kills other weights. -/
theorem weightProjection_of_mem (a c n : ℕ) (z : Term R M n)
    (hz : z ∈ weightSpace b c n) :
    weightProjection b a n z = if c = a then z else 0 := by
  classical
  by_cases hca : c = a
  · subst c
    simp [weightProjection_eq_self b a n z hz]
  · simp [hca, weightProjection_eq_zero b a c n hca z hz]

/-- Linear maps on a tensor term are determined by monomials tensored with arbitrary wedges. -/
theorem term_linearMap_ext {n : ℕ} {Q : Type*} [AddCommGroup Q] [Module R Q]
    {f g : Term R M n →ₗ[R] Q}
    (h : ∀ (m : I →₀ ℕ) (w : ⋀[R]^n M),
      f (b.symmetricAlgebra m ⊗ₜ[R] w) = g (b.symmetricAlgebra m ⊗ₜ[R] w)) : f = g := by
  apply TensorProduct.ext
  apply b.symmetricAlgebra.ext
  intro m
  apply LinearMap.ext
  intro w
  exact h m w

/-- Projecting a map which preserves weight commutes with projection to a fixed weight. -/
theorem weightProjection_commutes_of_preserves {n : ℕ}
    (d : Term R M (n+1) →ₗ[R] Term R M n)
    (hd : ∀ (a : ℕ) (z : Term R M (n+1)), z ∈ weightSpace b a (n+1) →
      d z ∈ weightSpace b a n) (a : ℕ) :
    d.comp (weightProjection b a (n+1)) = (weightProjection b a n).comp d := by
  classical
  apply term_linearMap_ext b
  intro m w
  have hz : b.symmetricAlgebra m ⊗ₜ[R] w ∈ weightSpace b ((n+1)+m.degree) (n+1) :=
    Submodule.subset_span ⟨m, w, rfl, rfl⟩
  simp only [LinearMap.comp_apply, weightProjection_of_mem b _ _ _ _ hz,
    weightProjection_of_mem b _ _ _ _ (hd _ _ hz)]
  split_ifs <;> simp

end TotalWeight

section WeightExactness
variable {M : Type*} [AddCommGroup M] [Module R M] [LinearOrder I]
  (b : Module.Basis I R M)
open scoped TensorProduct

lemma symm_basis_monomial (m : I →₀ ℕ) :
    SymmetricAlgebra.equivMvPolynomial b (b.symmetricAlgebra m) = MvPolynomial.monomial m 1 := by
  simp only [Module.Basis.symmetricAlgebra, Module.Basis.map_apply,
    LinearEquiv.coe_coe, AlgEquiv.toLinearEquiv_apply, AlgEquiv.apply_symm_apply]
  rfl

lemma symm_basis_mul_ι (m : I →₀ ℕ) (i : I) :
    b.symmetricAlgebra m * SymmetricAlgebra.ι R M (b i) =
      b.symmetricAlgebra (m + Finsupp.single i 1) := by
  apply (SymmetricAlgebra.equivMvPolynomial b).injective
  simp [symm_basis_monomial, MvPolynomial.X, MvPolynomial.monomial_mul_monomial]

lemma differential_weight_basis (a n : ℕ) (m : I →₀ ℕ) (hm : n+1+m.degree=a)
    (s : Set.powersetCard I (n+1)) :
    symmetricDifferential b n (b.symmetricAlgebra m ⊗ₜ[R] b.exteriorPower (n+1) s) ∈
      weightSpace b a n := by
  classical
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, symmetricDifferential_formula]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨m + Finsupp.single ((Set.powersetCard.ofFinEmbEquiv.symm s) i) 1,
    exteriorPower.ιMulti R n ((b ∘ Set.powersetCard.ofFinEmbEquiv.symm s) ∘ i.succAbove), ?_, ?_⟩
  · simp only [map_add, Finsupp.degree_single]
    omega
  · simp only [Function.comp_apply]
    rw [symm_basis_mul_ι]

lemma differential_weight_monomial (a n : ℕ) (m : I →₀ ℕ) (hm : n+1+m.degree=a)
    (w : ⋀[R]^(n+1) M) :
    symmetricDifferential b n (b.symmetricAlgebra m ⊗ₜ[R] w) ∈ weightSpace b a n := by
  have hw : w ∈ Submodule.span R (Set.range (b.exteriorPower (n+1))) := by
    rw [(b.exteriorPower (n+1)).span_eq]
    exact Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    exact differential_weight_basis b a n m hm s
  | zero => simp
  | add x y _ _ hx hy => simpa only [TensorProduct.tmul_add, map_add] using
      (weightSpace b a n).add_mem hx hy
  | smul r x _ hx => simpa only [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', LinearMap.map_smul_of_tower] using
      (weightSpace b a n).smul_mem r hx

lemma symmetricDifferential_weight (a n : ℕ) (z : Term R M (n+1))
    (hz : z ∈ weightSpace b a (n+1)) :
    symmetricDifferential b n z ∈ weightSpace b a n := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, w, hm, rfl⟩ := hx
    exact differential_weight_monomial b a n m hm w
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using (weightSpace b a n).add_mem hx hy
  | smul r x _ hx => simpa only [LinearMap.map_smul_of_tower] using (weightSpace b a n).smul_mem r hx

lemma augmentation_basis_tmul (m : I →₀ ℕ) (w : ⋀[R]^0 M) :
    augmentation R M (b.symmetricAlgebra m ⊗ₜ[R] w) =
      (if m = 0 then 1 else 0) * exteriorPower.zeroEquiv R M w := by
  classical
  obtain ⟨r, rfl⟩ := (exteriorPower.zeroEquiv R M).symm.surjective w
  simp [augmentation, zeroTermEquiv, exteriorPower.zeroEquiv_symm_apply,
    TensorProduct.tmul_smul, TensorProduct.smul_tmul', symmetric_eval_coordinates b,
    symm_basis_monomial, MvPolynomial.constantCoeff_monomial, mul_comm]

lemma augmentation_positive_weight (a : ℕ) (z : Term R M 0) (ha : 0 < a)
    (hz : z ∈ weightSpace b a 0) : augmentation R M z = 0 := by
  classical
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, w, hm, rfl⟩ := hx
    have hm0 : m ≠ 0 := by intro h; simp [h] at hm; omega
    simp [augmentation_basis_tmul, hm0]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy, add_zero]
  | smul r x _ hx => simp only [map_smul, hx, smul_zero]

lemma augmentation_weight_zero_surjective (r : R) :
    ∃ z ∈ weightSpace b 0 0, augmentation R M z = r := by
  classical
  refine ⟨b.symmetricAlgebra 0 ⊗ₜ[R] (exteriorPower.zeroEquiv R M).symm r, ?_, ?_⟩
  · apply Submodule.subset_span
    exact ⟨0, _, by simp, rfl⟩
  · simp [augmentation_basis_tmul]

/-- The canonical boundary commutes with projection onto any total weight. -/
theorem symmetricDifferential_weightProjection (a n : ℕ) (z : Term R M (n+1)) :
    symmetricDifferential b n (weightProjection b a (n+1) z) =
      weightProjection b a n (symmetricDifferential b n z) := by
  exact LinearMap.congr_fun (weightProjection_commutes_of_preserves b
    ((symmetricDifferential b n).restrictScalars R)
    (fun a z hz => symmetricDifferential_weight b a n z hz) a) z

/-- A cycle of a given weight has a primitive of the same weight. -/
theorem symmetric_weight_cycle_lift (a n : ℕ) (z : Term R M (n+1))
    (hzw : z ∈ weightSpace b a (n+1)) (hz : symmetricDifferential b n z = 0) :
    ∃ y ∈ weightSpace b a (n+2), symmetricDifferential b (n+1) y = z := by
  obtain ⟨y, hy⟩ := symmetric_cycle_lift b n z hz
  refine ⟨weightProjection b a (n+2) y, weightProjection_mem b a (n+2) y, ?_⟩
  rw [symmetricDifferential_weightProjection, hy, weightProjection_eq_self b a (n+1) z hzw]

/-- The augmented degree-zero kernel is exact in each total weight. -/
theorem symmetric_weight_augmented_lift (a : ℕ) (z : Term R M 0)
    (hzw : z ∈ weightSpace b a 0) (hz : augmentation R M z = 0) :
    ∃ y ∈ weightSpace b a 1, symmetricDifferential b 0 y = z := by
  obtain ⟨y, hy⟩ := symmetric_augmented_lift b z hz
  refine ⟨weightProjection b a 1 y, weightProjection_mem b a 1 y, ?_⟩
  rw [symmetricDifferential_weightProjection, hy, weightProjection_eq_self b a 0 z hzw]

end WeightExactness

/-- The augmented symmetric Koszul complex is exact, including every total weight,
over any commutative ring and for a free module of unrestricted rank. -/
theorem full_exactness :
    Specs.AdvancedHomologicalAlgebra.SymmetricKoszul.FullExactness.{u,v} := by
  intro R _ M _ _ I b
  classical
  letI : LinearOrder I := linearOrderOfSTO WellOrderingRel
  exact ⟨symmetricDifferential b, symmetricDifferential_formula b, symmetricDifferential_square b,
    symmetric_augmentation_differential b, symmetric_augmentation_surjective,
    symmetric_cycle_lift b, symmetric_augmented_lift b, ⟨symmetricZeroHomologyEquiv b⟩,
    symmetricDifferential_weight b, symmetric_weight_cycle_lift b,
    symmetric_weight_augmented_lift b, augmentation_weight_zero_surjective b,
    augmentation_positive_weight b⟩

end AdvancedHomologicalAlgebra.SymmetricKoszul
