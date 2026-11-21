import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.Functoriality
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.BaseChange
import Mathlib.LinearAlgebra.ExteriorAlgebra.BaseChange
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.RingTheory.GradedAlgebra.TensorProduct
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.LinearAlgebra.TensorProduct.Basis

open CategoryTheory
open scoped TensorProduct
noncomputable section
universe u v
namespace AdvCommAlg.Koszul
variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
variable {E : Type v} [AddCommGroup E] [Module R E]

@[simp] theorem scalarExtensionForm_tmul (a : E →ₗ[R] R) (s : S) (e : E) :
    scalarExtensionForm S a (s ⊗ₜ[R] e) = s * algebraMap R S (a e) := by
  simp [scalarExtensionForm, Algebra.smul_def, mul_comm]

/-- The algebra comparison restricted along the inclusion of the original algebra. -/
def exteriorScalarMap : ExteriorAlgebra R E →ₐ[R] ExteriorAlgebra S (S ⊗[R] E) :=
  (ExteriorAlgebra.baseChangeEquiv R E S).toAlgHom.restrictScalars R |>.comp
    Algebra.TensorProduct.includeRight

@[simp] theorem exteriorScalarMap_generator (e : E) :
    exteriorScalarMap S (ExteriorAlgebra.ι R e) =
      ExteriorAlgebra.ι S ((1 : S) ⊗ₜ[R] e) :=
  ExteriorAlgebra.baseChangeEquiv_apply R E S 1 e

lemma exteriorScalarMap_mem (n : ℕ) (x : ExteriorAlgebra R E) (hx : x ∈ ⋀[R]^n E) :
    exteriorScalarMap S x ∈ ⋀[S]^n (S ⊗[R] E) := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R S]
    exact Submodule.algebraMap_mem _
  | add x y n hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | mem_mul x hx n y hy ih =>
    obtain ⟨e, rfl⟩ := hx
    rw [map_mul, exteriorScalarMap_generator]
    change _ ∈ (ExteriorAlgebra.ι S).range ^ (n+1)
    rw [pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) ih

lemma exteriorBaseChange_tmul (s : S) (x : ExteriorAlgebra R E) :
    ExteriorAlgebra.baseChangeEquiv R E S (s ⊗ₜ[R] x) = s • exteriorScalarMap S x := by
  change ExteriorAlgebra.baseChangeEquiv R E S (s ⊗ₜ[R] x) =
    s • ExteriorAlgebra.baseChangeEquiv R E S ((1 : S) ⊗ₜ[R] x)
  rw [← map_smul]
  congr 1
  simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

lemma exteriorBaseChange_symm_generator (x : S ⊗[R] E) :
    (ExteriorAlgebra.baseChangeEquiv R E S).symm (ExteriorAlgebra.ι S x) =
      (ExteriorAlgebra.ι R).baseChange S x := by
  induction x using TensorProduct.inductionOn with
  | tmul s e => exact ExteriorAlgebra.baseChangeEquiv_symm_apply R E S s e
  | add x y hx hy => simp only [map_add, hx, hy]

lemma exteriorBaseChange_symm_mem (n : ℕ) (x : ExteriorAlgebra S (S ⊗[R] E))
    (hx : x ∈ ⋀[S]^n (S ⊗[R] E)) :
    (ExteriorAlgebra.baseChangeEquiv R E S).symm x ∈ (⋀[R]^n E).baseChange S := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap s =>
    simpa only [AlgEquiv.commutes] using
      (SetLike.algebraMap_mem_graded (fun n => (⋀[R]^n E).baseChange S) s)
  | add x y n hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | mem_mul x hx n y hy ih =>
    obtain ⟨e, rfl⟩ := hx
    rw [map_mul, exteriorBaseChange_symm_generator]
    have he : (ExteriorAlgebra.ι R).baseChange S e ∈ (⋀[R]^1 E).baseChange S := by
      induction e using TensorProduct.inductionOn with
      | tmul s e =>
        exact Submodule.tmul_mem_baseChange_of_mem s (by
          simpa only [ExteriorAlgebra.exteriorPower, pow_one] using
            LinearMap.mem_range_self (ExteriorAlgebra.ι R) e)
      | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
    simpa only [Nat.add_comm 1 n] using SetLike.mul_mem_graded (A := fun n => (⋀[R]^n E).baseChange S) he ih

/-- Exterior powers commute with arbitrary scalar extension. The injectivity
uses the direct-sum grading, not flatness of S. -/
def exteriorPowerScalarEquiv (n : ℕ) :
    S ⊗[R] (⋀[R]^n E) ≃ₗ[S] (⋀[S]^n (S ⊗[R] E)) := by
  let f := (ExteriorAlgebra.baseChangeEquiv R E S).toLinearMap.comp
    ((⋀[R]^n E).subtype.baseChange S)
  have hf : ∀ x, f x ∈ ⋀[S]^n (S ⊗[R] E) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s x =>
      change ExteriorAlgebra.baseChangeEquiv R E S (s ⊗ₜ[R] (x : ExteriorAlgebra R E)) ∈ _
      rw [exteriorBaseChange_tmul]
      exact Submodule.smul_mem _ s (exteriorScalarMap_mem (R := R) (E := E) S n x x.property)
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  let g := f.codRestrict _ hf
  apply LinearEquiv.ofBijective g
  constructor
  · intro x y h
    apply DirectSum.toBaseChange_injective (fun n => ⋀[R]^n E) n
    apply Subtype.ext
    apply (ExteriorAlgebra.baseChangeEquiv R E S).injective
    exact congrArg Subtype.val h
  · intro y
    obtain ⟨x, hx⟩ := Submodule.toBaseChange_surjective' S (⋀[R]^n E)
      (exteriorBaseChange_symm_mem S n y y.property)
    refine ⟨x, Subtype.ext ?_⟩
    change ExteriorAlgebra.baseChangeEquiv R E S
      (((⋀[R]^n E).subtype.baseChange S) x) = y
    change ((⋀[R]^n E).subtype.baseChange S) x = _ at hx
    rw [hx]
    exact (ExteriorAlgebra.baseChangeEquiv R E S).apply_symm_apply y

@[simp] theorem exteriorPowerScalarEquiv_coe (n : ℕ) (x : S ⊗[R] (⋀[R]^n E)) :
    (exteriorPowerScalarEquiv S n x : ExteriorAlgebra S (S ⊗[R] E)) =
      ExteriorAlgebra.baseChangeEquiv R E S (((⋀[R]^n E).subtype.baseChange S) x) := rfl

lemma exteriorScalarMap_ιMulti (n : ℕ) (e : Fin n → E) :
    exteriorScalarMap S (ExteriorAlgebra.ιMulti R n e) =
      ExteriorAlgebra.ιMulti S n (fun i => (1 : S) ⊗ₜ[R] e i) := by
  induction n with
  | zero => simp only [ExteriorAlgebra.ιMulti_zero_apply, map_one]
  | succ n ih =>
    simp only [ExteriorAlgebra.ιMulti_succ_apply, map_mul, exteriorScalarMap_generator, ih]
    rfl

@[simp] theorem exteriorPowerScalarEquiv_ιMulti (n : ℕ) (s : S) (e : Fin n → E) :
    exteriorPowerScalarEquiv S n (s ⊗ₜ[R] exteriorPower.ιMulti R n e) =
      s • exteriorPower.ιMulti S n (fun j => (1 : S) ⊗ₜ[R] e j) := by
  apply Subtype.ext
  rw [exteriorPowerScalarEquiv_coe]
  change ExteriorAlgebra.baseChangeEquiv R E S (s ⊗ₜ[R] ExteriorAlgebra.ιMulti R n e) = _
  rw [exteriorBaseChange_tmul, exteriorScalarMap_ιMulti]
  rfl

/-- Compatibility with contraction follows from the full signed deletion formula. -/
theorem scalarExtension_differential (a : E →ₗ[R] R) (n : ℕ) :
    (differential (scalarExtensionForm S a) n).comp
        (exteriorPowerScalarEquiv S (n+1)).toLinearMap =
      (exteriorPowerScalarEquiv S n).toLinearMap.comp ((differential a n).baseChange S) := by
  apply LinearMap.restrictScalars_injective R
  apply TensorProduct.ext
  apply LinearMap.ext
  intro s
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro e
  change differential (scalarExtensionForm S a) n
      (exteriorPowerScalarEquiv S (n+1) (s ⊗ₜ[R] exteriorPower.ιMulti R (n+1) e)) =
    exteriorPowerScalarEquiv S n (s ⊗ₜ[R] differential a n (exteriorPower.ιMulti R (n+1) e))
  simp only [exteriorPowerScalarEquiv_ιMulti, map_smul, differential_ιMulti,
    TensorProduct.tmul_sum, TensorProduct.tmul_smul, map_sum,
    scalarExtensionForm_tmul, one_mul]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change _ = (exteriorPowerScalarEquiv S n).toLinearMap _
  rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower]
  change _ = (-1 : R)^i.val • (a (e i) •
    exteriorPowerScalarEquiv S n (s ⊗ₜ[R] exteriorPower.ιMulti R n (e ∘ i.succAbove)))
  rw [exteriorPowerScalarEquiv_ιMulti]
  rw [← algebraMap_smul S ((-1 : R)^i.val), ← algebraMap_smul S (a (e i))]
  simp only [map_pow, map_neg, map_one, smul_smul]
  congr 1
  simp only [mul_comm, mul_left_comm]

section Complexes
variable {E : Type v} [AddCommGroup E] [Module R E]

/-- The canonical chain isomorphism, without any flatness assumption. -/
def scalarComparisonIso (a : E →ₗ[R] R) :
    scalarExtensionComplex S a ≅ complex (scalarExtensionForm S a) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (exteriorPowerScalarEquiv S n).toModuleIso) (fun i j hij => by
      have h : j + 1 = i := hij
      subst i
      simp only [scalarExtensionComplex, Functor.mapHomologicalComplex_obj_d,
        complex, ChainComplex.of_d]
      apply ModuleCat.hom_ext
      exact scalarExtension_differential S a j)

theorem scalarComparison_iso : Specs.AdvCommAlg.Koszul.scalarComparison.{u,v} := by
  intro R _ S _ _ E _ _ a
  exact ⟨scalarComparisonIso S a, fun n s e => exteriorPowerScalarEquiv_ιMulti S n s e⟩

theorem scalarComparison_naturality :
    Specs.AdvCommAlg.Koszul.scalarComparisonNaturality.{u,v} := by
  intro R _ S _ _ E F _ _ _ _ a b φ f g i j _hf hf hg hi hj
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  let : Module R ((complex (scalarExtensionForm S b)).X n) :=
    Module.compHom _ (algebraMap R S)
  let : IsScalarTower R S ((complex (scalarExtensionForm S b)).X n) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  change ((j.hom.f n).hom.comp ((f.f n).hom.baseChange S) :
    S ⊗[R] (⋀[R]^n E) →ₗ[S] (⋀[S]^n (S ⊗[R] F))) =
    (g.f n).hom.comp (i.hom.f n).hom
  apply LinearMap.restrictScalars_injective R
  apply TensorProduct.ext
  apply LinearMap.ext
  intro s
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro e
  change (j.hom.f n).hom ((f.f n).hom.baseChange S
      (s ⊗ₜ[R] exteriorPower.ιMulti R n e)) =
    (g.f n).hom ((i.hom.f n).hom (s ⊗ₜ[R] exteriorPower.ιMulti R n e))
  erw [hf n, LinearMap.baseChange_tmul, exteriorPower.map_apply_ιMulti, hj, hi,
    map_smul, hg n, exteriorPower.map_apply_ιMulti]
  simp only [Function.comp_def, LinearMap.baseChange_tmul]
  rfl

end Complexes
/-- Standard scalar extension of the finite free module of positions. -/
def listScalarCoordinates (x : List R) :
    (S ⊗[R] (Fin x.length → R)) ≃ₗ[S] (Fin (x.map (algebraMap R S)).length → S) :=
  ((Pi.basisFun R (Fin x.length)).baseChange S).equiv
    (Pi.basisFun S (Fin (x.map (algebraMap R S)).length)) (finCongr (by simp))

lemma listScalarCoordinates_form (x : List R) :
    (listForm (x.map (algebraMap R S))).comp (listScalarCoordinates S x).toLinearMap =
      scalarExtensionForm S (listForm x) := by
  apply ((Pi.basisFun R (Fin x.length)).baseChange S).ext
  intro i
  change listForm _ (((Pi.basisFun R (Fin x.length)).baseChange S).equiv
    (Pi.basisFun S _) (finCongr (by simp))
    (((Pi.basisFun R (Fin x.length)).baseChange S) i)) = _
  rw [Module.Basis.equiv_apply, listForm_basis, Module.Basis.baseChange_apply,
    scalarExtensionForm_tmul, one_mul]
  simp
  simpa only [Pi.basisFun_apply, List.get_eq_getElem] using
    congrArg (algebraMap R S) (listForm_basis x i).symm

/-- Base change in the canonical finite-list coordinates. -/
def listScalarComparisonIso (x : List R) :
    scalarExtensionComplex S (listForm x) ≅ listComplex (x.map (algebraMap R S)) :=
  scalarComparisonIso S (listForm x) ≪≫
    complexIso (scalarExtensionForm S (listForm x)) (listForm (x.map (algebraMap R S)))
      (listScalarCoordinates S x) (listScalarCoordinates_form S x)

def listScalarTermEquiv (x : List R) (n : ℕ) :
    S ⊗[R] (⋀[R]^n (Fin x.length → R)) ≃ₗ[S]
      (⋀[S]^n (Fin (x.map (algebraMap R S)).length → S)) :=
  (HomologicalComplex.Hom.isoApp (listScalarComparisonIso S x) n).toLinearEquiv

lemma listScalarTermEquiv_differential (x : List R) (n : ℕ)
    (z : S ⊗[R] (⋀[R]^(n+1) (Fin x.length → R))) :
    differential (listForm (x.map (algebraMap R S))) n (listScalarTermEquiv S x (n+1) z) =
      listScalarTermEquiv S x n ((differential (listForm x) n).baseChange S z) := by
  have h := (listScalarComparisonIso S x).hom.comm (n+1) n
  have h' := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp h) z
  simp only [scalarExtensionComplex, Functor.mapHomologicalComplex_obj_d] at h'
  simp only [complex, listComplex, ChainComplex.of_d] at h'
  exact h'

variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Distribution of scalar extension over tensor products, followed by the
Koszul degreewise comparison. -/
def coefficientScalarTermEquiv (x : List R) (n : ℕ) :
    S ⊗[R] ((⋀[R]^n (Fin x.length → R)) ⊗[R] M) ≃ₗ[S]
      ((⋀[S]^n (Fin (x.map (algebraMap R S)).length → S)) ⊗[S] (S ⊗[R] M)) :=
  (TensorProduct.AlgebraTensorModule.distribBaseChange R S _ M).trans
    (TensorProduct.congr (listScalarTermEquiv S x n) (LinearEquiv.refl S _))

@[simp] theorem coefficientScalarTermEquiv_tmul (x : List R) (n : ℕ)
    (s : S) (a : ⋀[R]^n (Fin x.length → R)) (m : M) :
    coefficientScalarTermEquiv S M x n (s ⊗ₜ[R] (a ⊗ₜ[R] m)) =
      listScalarTermEquiv S x n (s ⊗ₜ[R] a) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m) := rfl

lemma coefficientScalarTermEquiv_differential (x : List R) (n : ℕ) :
    (coefficientDifferential (S ⊗[R] M) (x.map (algebraMap R S)) n).comp
        (coefficientScalarTermEquiv S M x (n+1)).toLinearMap =
      (coefficientScalarTermEquiv S M x n).toLinearMap.comp
        ((coefficientDifferential M x n).baseChange S) := by
  apply LinearMap.restrictScalars_injective R
  apply TensorProduct.ext
  apply LinearMap.ext
  intro s
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro m
  change coefficientDifferential (S ⊗[R] M) (x.map (algebraMap R S)) n
      (coefficientScalarTermEquiv S M x (n+1) (s ⊗ₜ[R] (a ⊗ₜ[R] m))) =
    coefficientScalarTermEquiv S M x n (s ⊗ₜ[R] coefficientDifferential M x n (a ⊗ₜ[R] m))
  simp only [coefficientScalarTermEquiv_tmul, coefficientDifferential, TensorProduct.map_tmul,
    LinearMap.id_apply, listScalarTermEquiv_differential, LinearMap.baseChange_tmul]

/-- The comparison for coefficient complexes also needs no flatness. -/
def coefficientScalarComparisonIso (x : List R) :
    ((scalarExtension R S).mapHomologicalComplex _).obj (coefficientComplex M x) ≅
      coefficientComplex (S ⊗[R] M) (x.map (algebraMap R S)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (coefficientScalarTermEquiv S M x n).toModuleIso) (fun i j hij => by
      have h : j+1 = i := hij
      subst i
      simp only [Functor.mapHomologicalComplex_obj_d, coefficientComplex, ChainComplex.of_d]
      apply ModuleCat.hom_ext
      exact coefficientScalarTermEquiv_differential S M x j)

/-- Flatness is used only here, to preserve kernels and cokernels. -/
instance scalarExtension_preservesHomology [Module.Flat R S] :
    (scalarExtension R S : ModuleCat.{max u v} R ⥤ _).PreservesHomology := by
  apply ((Functor.exact_tfae (scalarExtension R S)).out 2 3).mp
  intro C hC
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hC ⊢
  exact Module.Flat.lTensor_exact S hC

/-- Flat scalar extension of homology, composed with the coefficient chain comparison. -/
def flatHomologyScalarEquiv [Module.Flat R S] (x : List R) (q : ℕ) :
    (S ⊗[R] homology M x q) ≃ₗ[S]
      homology (S ⊗[R] M) (x.map (algebraMap R S)) q :=
  (((coefficientComplex M x).sc q).mapHomologyIso (scalarExtension R S)).symm.toLinearEquiv |>.trans
    ((HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.down ℕ) q).mapIso
      (coefficientScalarComparisonIso S M x)).toLinearEquiv

theorem flatHomology_comparison : Specs.AdvCommAlg.Koszul.flatHomologyComparison.{u,v} := by
  intro R _ S _ _ _ M _ _ x q
  exact ⟨flatHomologyScalarEquiv S M x q⟩

/-- The coefficient chain comparison is natural in all coefficient maps. -/
def coefficientScalarNaturalIso (x : List R) :
    (coefficientFunctor.{u,v} x ⋙ (scalarExtension R S).mapHomologicalComplex _) ≅
      (scalarExtension R S ⋙ coefficientFunctor (x.map (algebraMap R S))) :=
  NatIso.ofComponents (fun M => coefficientScalarComparisonIso S M x) (fun {M N} f => by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    change ((coefficientScalarTermEquiv S N x n).toLinearMap.comp
        ((TensorProduct.map (LinearMap.id : (⋀[R]^n (Fin x.length → R)) →ₗ[R] _) f.hom).baseChange S)) =
      (TensorProduct.map LinearMap.id (f.hom.baseChange S)).comp
        (coefficientScalarTermEquiv S M x n).toLinearMap
    apply LinearMap.restrictScalars_injective R
    apply TensorProduct.ext
    apply LinearMap.ext
    intro s
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro m
    change coefficientScalarTermEquiv S N x n (s ⊗ₜ[R] (a ⊗ₜ[R] f.hom m)) =
      TensorProduct.map LinearMap.id (f.hom.baseChange S)
        (coefficientScalarTermEquiv S M x n (s ⊗ₜ[R] (a ⊗ₜ[R] m)))
    simp only [coefficientScalarTermEquiv_tmul, TensorProduct.map_tmul,
      LinearMap.id_apply, LinearMap.baseChange_tmul])

theorem coefficientScalar_comparison :
    Specs.AdvCommAlg.Koszul.coefficientScalarComparison.{u,v} := by
  intro R _ S _ _ x
  exact ⟨coefficientScalarNaturalIso S x⟩

/-- Exact scalar extension commutes naturally with homology of arbitrary chain complexes. -/
def scalarHomologyNaturalIso [Module.Flat R S] (q : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{max u v} R) (ComplexShape.down ℕ) q ⋙
      scalarExtension R S) ≅
    ((scalarExtension R S).mapHomologicalComplex _ ⋙
      HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.down ℕ) q) :=
  NatIso.ofComponents (fun C => ((C.sc q).mapHomologyIso (scalarExtension R S)).symm)
    (fun f => ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor _ _ q).map f) (scalarExtension R S))

/-- The homology equivalence is natural in M, not only an objectwise isomorphism. -/
def flatHomologyScalarNaturalIso [Module.Flat R S] (x : List R) (q : ℕ) :
    (coefficientHomologyFunctor.{u,v} x q ⋙ scalarExtension R S) ≅
      (scalarExtension R S ⋙ coefficientHomologyFunctor (x.map (algebraMap R S)) q) :=
  Functor.isoWhiskerLeft (coefficientFunctor x) (scalarHomologyNaturalIso S q) ≪≫
    Functor.isoWhiskerRight (coefficientScalarNaturalIso S x)
      (HomologicalComplex.homologyFunctor _ _ q)

theorem flatHomology_naturalComparison :
    Specs.AdvCommAlg.Koszul.flatHomologyNaturalComparison.{u,v} := by
  intro R _ S _ _ _ x q
  exact ⟨flatHomologyScalarNaturalIso S x q⟩

end AdvCommAlg.Koszul
