import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! Canonical objects for RK-03 (paper.tex, definition 5.3).
All rings are commutative, including the zero ring. No freeness assumption
is imposed on the module used to define contraction. -/
open scoped TensorProduct
noncomputable section
universe u v
namespace AdvCommAlg.Koszul
variable {R : Type u} [CommRing R]
variable {E : Type v} [AddCommGroup E] [Module R E]

/-- Contraction on the exterior algebra; the zero quadratic form imposes
exactly the alternating relations, also in characteristic two. -/
def contraction (f : E →ₗ[R] R) : ExteriorAlgebra R E →ₗ[R] ExteriorAlgebra R E :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R E)) f

@[simp] theorem contraction_scalar (f : E →ₗ[R] R) (a : R) :
    contraction f (algebraMap R (ExteriorAlgebra R E) a) = 0 :=
  CliffordAlgebra.contractLeft_algebraMap _ _ _

@[simp] theorem contraction_one (f : E →ₗ[R] R) : contraction f 1 = 0 :=
  CliffordAlgebra.contractLeft_one _ _

@[simp] theorem contraction_generator (f : E →ₗ[R] R) (e : E) :
    contraction f (ExteriorAlgebra.ι R e) = algebraMap R _ (f e) :=
  CliffordAlgebra.contractLeft_ι _ _ _

theorem contraction_generator_mul (f : E →ₗ[R] R) (e : E) (a : ExteriorAlgebra R E) :
    contraction f (ExteriorAlgebra.ι R e * a) =
      f e • a - ExteriorAlgebra.ι R e * contraction f a :=
  CliffordAlgebra.contractLeft_ι_mul _ _ _

theorem contraction_square (f : E →ₗ[R] R) (a : ExteriorAlgebra R E) :
    contraction f (contraction f a) = 0 :=
  CliffordAlgebra.contractLeft_contractLeft _ _

/-- The contraction of a pure (n+1)-wedge lies in exterior degree n. -/
theorem contraction_word_mem (f : E →ₗ[R] R) (n : ℕ) (e : Fin (n+1) → E) :
    contraction f (ExteriorAlgebra.ιMulti R (n+1) e) ∈ ⋀[R]^n E := by
  induction n with
  | zero =>
    simp only [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply,
      mul_one, contraction_generator]
    exact Submodule.algebraMap_mem _
  | succ n ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, contraction_generator_mul]
    apply Submodule.sub_mem
    · exact Submodule.smul_mem _ _ (ExteriorAlgebra.ιMulti_range R _ (Set.mem_range_self _))
    · change _ ∈ (ExteriorAlgebra.ι R).range ^ (n+1)
      rw [pow_succ']
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) (ih (Matrix.vecTail e))

/-- Contraction lowers degree on arbitrary exterior powers. -/
theorem contraction_mem (f : E →ₗ[R] R) (n : ℕ) (a : ExteriorAlgebra R E)
    (ha : a ∈ ⋀[R]^(n+1) E) : contraction f a ∈ ⋀[R]^n E := by
  rw [← exteriorPower.ιMulti_span_fixedDegree] at ha
  induction ha using Submodule.span_induction with
  | mem a ha => obtain ⟨e, rfl⟩ := ha; exact contraction_word_mem f n e
  | zero => simp
  | add a b ha hb iha ihb => simpa using Submodule.add_mem _ iha ihb
  | smul r a ha ih => simpa using Submodule.smul_mem _ r ih

/-- The degree-restricted Koszul differential. -/
def differential (f : E →ₗ[R] R) (n : ℕ) : (⋀[R]^(n+1) E) →ₗ[R] (⋀[R]^n E) :=
  ((contraction f).comp (⋀[R]^(n+1) E).subtype).codRestrict _
    (fun a => contraction_mem f n a a.property)

@[simp] theorem differential_coe (f : E →ₗ[R] R) (n : ℕ) (a : ⋀[R]^(n+1) E) :
    (differential f n a : ExteriorAlgebra R E) = contraction f a := rfl

/-- Square-zero needed to construct the chain-complex object. -/
theorem differential_comp (f : E →ₗ[R] R) (n : ℕ) :
    (differential f n).comp (differential f (n+1)) = 0 := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  exact contraction_square f a

open CategoryTheory
/-- The nonnegative chain complex for an arbitrary linear form. -/
def complex (f : E →ₗ[R] R) : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (⋀[R]^n E))
    (fun n => ModuleCat.ofHom (differential f n))
    (fun n => ModuleCat.hom_ext (differential_comp f n))

/-- The linear form whose standard-basis values are the entries of a finite list. -/
def listForm (x : List R) : (Fin x.length → R) →ₗ[R] R :=
  (Pi.basisFun R (Fin x.length)).constr R (fun i => x.get i)

/-- The increasing-wedge basis, indexed by q-element subsets of the positions. -/
def listBasis (x : List R) (q : ℕ) :
    Module.Basis (Set.powersetCard (Fin x.length) q) R (⋀[R]^q (Fin x.length → R)) :=
  (Pi.basisFun R (Fin x.length)).exteriorPower q

/-- Koszul complex of an ordered finite list. -/
def listComplex (x : List R) : ChainComplex (ModuleCat R) ℕ := complex (listForm x)

variable (M : Type v) [AddCommGroup M] [Module R M]
/-- The differential of K(x) tensor M is d tensor id, without a flatness hypothesis. -/
def coefficientDifferential (x : List R) (n : ℕ) :
    ((⋀[R]^(n+1) (Fin x.length → R)) ⊗[R] M) →ₗ[R]
      ((⋀[R]^n (Fin x.length → R)) ⊗[R] M) :=
  TensorProduct.map (differential (listForm x) n) LinearMap.id

theorem coefficientDifferential_comp (x : List R) (n : ℕ) :
    (coefficientDifferential M x n).comp (coefficientDifferential M x (n+1)) = 0 := by
  rw [coefficientDifferential, coefficientDifferential, ← TensorProduct.map_comp,
    differential_comp, TensorProduct.map_zero_left]

/-- The coefficient complex K(x;M). -/
def coefficientComplex (x : List R) : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R ((⋀[R]^n (Fin x.length → R)) ⊗[R] M))
    (fun n => ModuleCat.ofHom (coefficientDifferential M x n))
    (fun n => ModuleCat.hom_ext (coefficientDifferential_comp M x n))

/-- Degree zero of K(x;M) is canonically M. -/
def coefficientZeroEquiv (x : List R) : (coefficientComplex M x).X 0 ≃ₗ[R] M :=
  (TensorProduct.congr (exteriorPower.zeroEquiv R (Fin x.length → R))
    (LinearEquiv.refl R M)).trans (TensorProduct.lid R M)

/-- Koszul homology uses the homology of the actual coefficient complex. -/
def homology (x : List R) (n : ℕ) : ModuleCat R := (coefficientComplex M x).homology n

/-- The ideal generated by the entries of x. -/
def listIdeal (x : List R) : Ideal R := Ideal.span {r | r ∈ x}

/-- The submodule (x)M in the source's degree-zero formula. -/
def listSubmodule (x : List R) : Submodule R M := listIdeal x • (⊤ : Submodule R M)

end AdvCommAlg.Koszul


/-! Independent expected types and values. These import no implementation. -/
namespace Specs.AdvCommAlg.Koszul
open _root_.AdvCommAlg.Koszul

def contractionType := ∀ {R : Type u} [CommRing R] {E : Type v}
  [AddCommGroup E] [Module R E],
  (E →ₗ[R] R) → (ExteriorAlgebra R E →ₗ[R] ExteriorAlgebra R E)
def contractionValue : contractionType.{u,v} := @contraction

def differentialType := ∀ {R : Type u} [CommRing R] {E : Type v}
  [AddCommGroup E] [Module R E],
  (E →ₗ[R] R) → ∀ n : ℕ, (⋀[R]^(n+1) E) →ₗ[R] (⋀[R]^n E)
def differentialValue : differentialType.{u,v} := @differential

def complexType := ∀ {R : Type u} [CommRing R] {E : Type v}
  [AddCommGroup E] [Module R E],
  (E →ₗ[R] R) → ChainComplex (ModuleCat.{max u v} R) ℕ
def complexValue : complexType.{u,v} := @complex

def listFormType := ∀ {R : Type u} [CommRing R] (x : List R),
  (Fin x.length → R) →ₗ[R] R
def listFormValue : listFormType.{u} := @listForm

def listComplexType := ∀ {R : Type u} [CommRing R],
  List R → ChainComplex (ModuleCat.{u} R) ℕ
def listComplexValue : listComplexType.{u} := @listComplex

def coefficientComplexType := ∀ {R : Type u} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M],
  List R → ChainComplex (ModuleCat.{max u v} R) ℕ
def coefficientComplexValue : coefficientComplexType.{u,v} := @coefficientComplex

def homologyType := ∀ {R : Type u} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M], List R → ℕ → ModuleCat.{max u v} R
def homologyValue : homologyType.{u,v} := @homology

def listBasisType := ∀ {R : Type u} [CommRing R] (x : List R) (q : ℕ),
  Module.Basis (Set.powersetCard (Fin x.length) q) R (⋀[R]^q (Fin x.length → R))
def listBasisValue : listBasisType.{u} := @listBasis

def contractionFormula : Prop := ∀ {R : Type u} [CommRing R] {E : Type v}
  [AddCommGroup E] [Module R E] (f : E →ₗ[R] R) (n : ℕ) (e : Fin (n+1) → E),
  contraction f (ExteriorAlgebra.ιMulti R (n+1) e) =
    ∑ i : Fin (n+1), (-1 : R)^i.val •
      (f (e i) • ExteriorAlgebra.ιMulti R n (e ∘ i.succAbove))

def contractionLeibniz : Prop := ∀ {R : Type u} [CommRing R] {E : Type v}
  [AddCommGroup E] [Module R E] (f : E →ₗ[R] R) (p : ℕ) (a b : ExteriorAlgebra R E),
  a ∈ ⋀[R]^p E →
    contraction f (a * b) = contraction f a * b + (-1 : R)^p • (a * contraction f b)

def contractionDescends : Prop := ∀ {R : Type u} [CommRing R] {E : Type v}
  [AddCommGroup E] [Module R E] (f : E →ₗ[R] R) (n : ℕ),
  ∃ F : E [⋀^Fin (n+1)]→ₗ[R] (⋀[R]^n E), ∀ e,
    F e = ∑ i : Fin (n+1), (-1 : R)^i.val •
      (f (e i) • exteriorPower.ιMulti R n (e ∘ i.succAbove))

def differentialSquared : Prop := ∀ {R : Type u} [CommRing R] {E : Type v}
  [AddCommGroup E] [Module R E] (f : E →ₗ[R] R) (n : ℕ),
  (differential f n).comp (differential f (n+1)) = 0

def listFormBasis : Prop := ∀ {R : Type u} [CommRing R] (x : List R) (i : Fin x.length),
  listForm x (Pi.basisFun R (Fin x.length) i) = x.get i

def listBasisApply : Prop := ∀ {R : Type u} [CommRing R] (x : List R) (q : ℕ)
  (s : Set.powersetCard (Fin x.length) q),
  listBasis x q s = exteriorPower.ιMulti_family R q (Pi.basisFun R (Fin x.length)) s

def listBasisCard : Prop := ∀ {R : Type u} [CommRing R] (x : List R) (q : ℕ),
  Nat.card (Set.powersetCard (Fin x.length) q) = x.length.choose q

def listComplexVanish : Prop := ∀ {R : Type u} [CommRing R] (x : List R) (q : ℕ),
  x.length < q → Subsingleton ((listComplex x).X q)

def emptyComplexDescription : Prop := ∀ {R : Type u} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M],
  Nonempty ((coefficientComplex M ([] : List R)).X 0 ≃ₗ[R] M) ∧
    (∀ q : ℕ, 0 < q → Subsingleton ((coefficientComplex M ([] : List R)).X q)) ∧
    (∀ n : ℕ, coefficientDifferential M ([] : List R) n = 0)

def homologyZero : Prop := ∀ {R : Type u} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M] (x : List R),
  Nonempty (homology M x 0 ≃ₗ[R] M ⧸ listSubmodule M x)

end Specs.AdvCommAlg.Koszul
