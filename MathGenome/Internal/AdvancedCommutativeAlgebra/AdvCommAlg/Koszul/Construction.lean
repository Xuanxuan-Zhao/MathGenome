import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.Construction
import Mathlib.Tactic.Abel

open scoped TensorProduct
open CategoryTheory
noncomputable section
universe u v
namespace AdvCommAlg.Koszul
variable {R : Type u} [CommRing R]
variable {E : Type v} [AddCommGroup E] [Module R E]

/-- The full graded product rule, with no condition on the second factor. -/
theorem contraction_leibniz (f : E →ₗ[R] R) (p : ℕ) (a b : ExteriorAlgebra R E)
    (ha : a ∈ ⋀[R]^p E) :
    contraction f (a * b) = contraction f a * b + (-1 : R)^p • (a * contraction f b) := by
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r => simp [← Algebra.smul_def]
  | add x y n hx hy ihx ihy =>
    simp only [add_mul, map_add, ihx, ihy, smul_add]
    abel
  | mem_mul m hm n x hx ih =>
    obtain ⟨e, rfl⟩ := hm
    rw [mul_assoc, contraction_generator_mul, ih, contraction_generator_mul]
    simp only [sub_eq_add_neg, add_mul, mul_add, neg_mul, mul_neg,
      smul_mul_assoc, mul_smul_comm, pow_succ, neg_smul, mul_one, mul_assoc]
    abel

/-- The signed deletion formula, with position i starting at zero. -/
theorem contraction_formula (f : E →ₗ[R] R) (n : ℕ) (e : Fin (n+1) → E) :
    contraction f (ExteriorAlgebra.ιMulti R (n+1) e) =
      ∑ i : Fin (n+1), (-1 : R)^i.val •
        (f (e i) • ExteriorAlgebra.ιMulti R n (e ∘ i.succAbove)) := by
  induction n with
  | zero => simp [Algebra.algebraMap_eq_smul_one]
  | succ n ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, contraction_generator_mul, ih]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero,
      Function.comp_def, Matrix.vecTail]
    rw [sub_eq_add_neg]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    simp only [Function.comp_def, Fin.succ_succAbove_zero,
      Fin.succ_succAbove_succ, Matrix.vecTail, Fin.val_succ, pow_succ,
      mul_neg_one, neg_smul, mul_smul_comm]

@[simp] theorem listForm_basis (x : List R) (i : Fin x.length) :
    listForm x (Pi.basisFun R (Fin x.length) i) = x.get i :=
  Module.Basis.constr_basis _ _ _ _

/-- The basis vectors are precisely the increasing exterior products. -/
theorem listBasis_apply (x : List R) (q : ℕ) (s : Set.powersetCard (Fin x.length) q) :
    listBasis x q s = exteriorPower.ιMulti_family R q (Pi.basisFun R (Fin x.length)) s :=
  exteriorPower.basis_apply _ _ _ _

theorem listBasis_card (x : List R) (q : ℕ) :
    Nat.card (Set.powersetCard (Fin x.length) q) = x.length.choose q := by
  rw [Set.powersetCard.card, Nat.card_fin]

/-- The complex is zero above the number of generators, including over the zero ring. -/
theorem listComplex_vanish (x : List R) (q : ℕ) (hq : x.length < q) :
    Subsingleton ((listComplex x).X q) := by
  apply exteriorPower.subsingleton_of_span_eq_top_of_card_lt
    (Pi.basisFun R (Fin x.length)) (Module.Basis.span_eq _) q
  simpa using hq

variable (M : Type v) [AddCommGroup M] [Module R M]

theorem coefficientComplex_vanish (x : List R) (q : ℕ) (hq : x.length < q) :
    Subsingleton ((coefficientComplex M x).X q) := by
  have : Subsingleton (⋀[R]^q (Fin x.length → R)) := listComplex_vanish x q hq
  change Subsingleton ((⋀[R]^q (Fin x.length → R)) ⊗[R] M)
  infer_instance

/-- All differentials of the empty-list complex vanish. -/
theorem empty_differential (n : ℕ) : coefficientDifferential M ([] : List R) n = 0 := by
  have : Subsingleton ((⋀[R]^(n+1) (Fin ([] : List R).length → R)) ⊗[R] M) :=
    coefficientComplex_vanish M [] (n+1) (by simp)
  exact Subsingleton.elim _ _

/-- The empty list has M in degree zero, zero positive terms, and zero differentials. -/
theorem emptyComplex_description :
    Nonempty ((coefficientComplex M ([] : List R)).X 0 ≃ₗ[R] M) ∧
      (∀ q : ℕ, 0 < q → Subsingleton ((coefficientComplex M ([] : List R)).X q)) ∧
      (∀ n : ℕ, coefficientDifferential M ([] : List R) n = 0) := by
  exact ⟨⟨coefficientZeroEquiv M []⟩,
    fun q hq => coefficientComplex_vanish M [] q (by simpa using hq), empty_differential M⟩

/-- In degree one contraction is the given linear form. -/
theorem differential_one (f : E →ₗ[R] R) (a : ⋀[R]^1 E) :
    exteriorPower.zeroEquiv R E (differential f 0 a) =
      f (exteriorPower.oneEquiv R E a) := by
  have h : (exteriorPower.zeroEquiv R E).toLinearMap.comp (differential f 0) =
      f.comp (exteriorPower.oneEquiv R E).toLinearMap := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro e
    have he : differential f 0 (exteriorPower.ιMulti R 1 e) =
        f (e 0) • exteriorPower.ιMulti R 0 (fun i => Fin.elim0 i) := by
      apply Subtype.ext
      simp [ExteriorAlgebra.ιMulti_succ_apply, Algebra.algebraMap_eq_smul_one]
    simp [he]
  exact LinearMap.congr_fun h a

@[simp] theorem coefficientZeroEquiv_tmul (x : List R)
    (a : ⋀[R]^0 (Fin x.length → R)) (m : M) :
    coefficientZeroEquiv M x (a ⊗ₜ[R] m) =
      exteriorPower.zeroEquiv R (Fin x.length → R) a • m := by
  rfl

@[simp] theorem degreeZeroBoundary_tmul (x : List R)
    (a : ⋀[R]^1 (Fin x.length → R)) (m : M) :
    coefficientZeroEquiv M x (coefficientDifferential M x 0 (a ⊗ₜ[R] m)) =
      listForm x (exteriorPower.oneEquiv R (Fin x.length → R) a) • m := by
  simp [coefficientDifferential, differential_one]

theorem listForm_mem (x : List R) (a : Fin x.length → R) : listForm x a ∈ listIdeal x := by
  classical
  rw [listForm, Module.Basis.constr_apply_fintype]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  exact Ideal.subset_span (List.get_mem _ _)

/-- The degree-zero boundaries, identified inside M, are precisely (x)M. -/
theorem degreeZeroBoundary_range (x : List R) :
    LinearMap.range ((coefficientZeroEquiv M x).toLinearMap.comp
      (coefficientDifferential M x 0)) = listSubmodule M x := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul a m =>
      change coefficientZeroEquiv M x (coefficientDifferential M x 0 (a ⊗ₜ[R] m)) ∈ _
      rw [degreeZeroBoundary_tmul]
      exact Submodule.smul_mem_smul (listForm_mem x _) (Submodule.mem_top : m ∈ ⊤)
    | add z w hz hw => simpa using Submodule.add_mem _ hz hw
  · apply Submodule.smul_le.mpr
    intro r hr m hm
    change r ∈ Submodule.span R {r | r ∈ x} at hr
    induction hr using Submodule.span_induction with
    | mem r hr =>
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hr
      refine ⟨exteriorPower.ιMulti R 1
        (fun _ => Pi.basisFun R (Fin x.length) i) ⊗ₜ[R] m, ?_⟩
      change coefficientZeroEquiv M x (coefficientDifferential M x 0
        (exteriorPower.ιMulti R 1 (fun _ => Pi.basisFun R (Fin x.length) i) ⊗ₜ[R] m)) = _
      rw [degreeZeroBoundary_tmul, exteriorPower.oneEquiv_ιMulti, listForm_basis, hi]
    | zero => simp
    | add r s hr hs ihr ihs => simpa [add_smul] using Submodule.add_mem _ ihr ihs
    | smul c r hr ihr => simpa [smul_eq_mul, mul_smul] using Submodule.smul_mem _ c ihr

-- Fix the additive-group instance before elaborating the quotient of a tensor term.
local instance coefficientTermQuotient (x : List R) (n : ℕ) :
    HasQuotient ((⋀[R]^n (Fin x.length → R)) ⊗[R] M)
      (Submodule R ((⋀[R]^n (Fin x.length → R)) ⊗[R] M)) :=
  @Submodule.hasQuotient R ((⋀[R]^n (Fin x.length → R)) ⊗[R] M) _ _ _

/-- The homology in degree zero of a nonnegative module complex is a cokernel. -/
def zeroHomologyCokernelEquiv (x : List R) :
    homology M x 0 ≃ₗ[R]
      (((⋀[R]^0 (Fin x.length → R)) ⊗[R] M) ⧸ LinearMap.range (coefficientDifferential M x 0)) := by
  let S := (coefficientComplex M x).sc 0
  have hg : S.g = 0 := by
    change (coefficientComplex M x).d 0 ((ComplexShape.down ℕ).next 0) = 0
    apply HomologicalComplex.shape
    intro h
    have : (ComplexShape.down ℕ).next 0 + 1 = 0 := h
    omega
  have hp : (ComplexShape.down ℕ).prev 0 = 1 :=
    ComplexShape.prev_eq' _ rfl
  let L := ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork S hg
    (ModuleCat.cokernelCocone S.f) (ModuleCat.cokernelIsColimit S.f)
  have hL : L.H = ModuleCat.of R
      (((⋀[R]^0 (Fin x.length → R)) ⊗[R] M) ⧸ LinearMap.range (coefficientDifferential M x 0)) := by
    dsimp [L, S, HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
      HomologicalComplex.shortComplexFunctor']
    rw [hp]
    rfl
  exact (L.homologyIso ≪≫ eqToIso hL).toLinearEquiv

/-- H₀(x;M) is the quotient M/(x)M. -/
def homologyZeroEquiv (x : List R) : homology M x 0 ≃ₗ[R] M ⧸ listSubmodule M x :=
  (zeroHomologyCokernelEquiv M x).trans
    (Submodule.Quotient.equiv _ _ (coefficientZeroEquiv M x) (by
      rw [← LinearMap.range_comp]
      exact degreeZeroBoundary_range M x))

/-- The deletion sum is an alternating multilinear map to the intended exterior power. -/
theorem contraction_descends (f : E →ₗ[R] R) (n : ℕ) :
    ∃ F : E [⋀^Fin (n+1)]→ₗ[R] (⋀[R]^n E), ∀ e,
      F e = ∑ i : Fin (n+1), (-1 : R)^i.val •
        (f (e i) • exteriorPower.ιMulti R n (e ∘ i.succAbove)) := by
  refine ⟨(differential f n).compAlternatingMap (exteriorPower.ιMulti R (n+1)), ?_⟩
  intro e
  apply Subtype.ext
  simpa only [LinearMap.compAlternatingMap_apply, differential_coe,
    exteriorPower.ιMulti_apply_coe, Submodule.coe_sum, SetLike.val_smul] using
      contraction_formula f n e

theorem differential_squared : Specs.AdvCommAlg.Koszul.differentialSquared.{u,v} := by
  intro R _ E _ _ f n
  exact differential_comp f n

theorem homology_zero : Specs.AdvCommAlg.Koszul.homologyZero.{u,v} := by
  intro R _ M _ _ x
  exact ⟨homologyZeroEquiv M x⟩

/-- Exported definitions all reduce to the single canonical interface in the Specs. -/
def koszulContraction := @contraction.{u,v}
def koszulDifferential := @differential.{u,v}
def koszulComplex := @complex.{u,v}
def koszulListForm := @listForm.{u}
def koszulListComplex := @listComplex.{u}
def koszulCoefficientComplex := @coefficientComplex.{u,v}
def koszulHomology := @homology.{u,v}
def koszulListBasis := @listBasis.{u}

end AdvCommAlg.Koszul
