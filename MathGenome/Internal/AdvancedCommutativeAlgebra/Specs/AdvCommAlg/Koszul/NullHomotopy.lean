import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.Construction
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.Linear
import Mathlib.LinearAlgebra.BilinearMap

/-! The coefficient cochain convention is δ(f) = f ∘ d (RK-10).
No nontriviality, flatness, or finiteness assumption is made on coefficients. -/
open CategoryTheory
open scoped TensorProduct
noncomputable section
universe u v
namespace AdvCommAlg.Koszul
variable {R : Type u} [CommRing R]
variable {E : Type v} [AddCommGroup E] [Module R E]

/-- Left wedge by a vector, restricted to a homogeneous exterior power. -/
def leftWedge (e : E) (n : ℕ) : (⋀[R]^n E) →ₗ[R] (⋀[R]^(n+1) E) :=
  ((LinearMap.mulLeft R (ExteriorAlgebra.ι R e)).comp (⋀[R]^n E).subtype).codRestrict _
    (fun a => by
      change ExteriorAlgebra.ι R e * (a : ExteriorAlgebra R E) ∈
        (ExteriorAlgebra.ι R).range ^ (n+1)
      rw [pow_succ']
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) a.property)

variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Left wedge on the first tensor factor of the canonical coefficient complex. -/
def coefficientWedge (x : List R) (e : Fin x.length → R) (n : ℕ) :
    ((⋀[R]^n (Fin x.length → R)) ⊗[R] M) →ₗ[R]
      ((⋀[R]^(n+1) (Fin x.length → R)) ⊗[R] M) :=
  TensorProduct.map (leftWedge e n) LinearMap.id

/-- Differential on Hom_R(K(x), M), with the source's unsigned precomposition convention. -/
def cochainDifferential (x : List R) (n : ℕ) :
    ((⋀[R]^n (Fin x.length → R)) →ₗ[R] M) →ₗ[R]
      ((⋀[R]^(n+1) (Fin x.length → R)) →ₗ[R] M) :=
  LinearMap.lcomp R M (differential (listForm x) n)

theorem cochainDifferential_comp (x : List R) (n : ℕ) :
    (cochainDifferential M x (n+1)).comp (cochainDifferential M x n) = 0 := by
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro a
  change f (differential (listForm x) n (differential (listForm x) (n+1) a)) = 0
  have h := LinearMap.congr_fun (differential_comp (listForm x) n) a
  change differential (listForm x) n (differential (listForm x) (n+1) a) = 0 at h
  rw [h, map_zero]

/-- The actual coefficient Koszul cochain complex. -/
def cochainComplex (x : List R) : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R ((⋀[R]^n (Fin x.length → R)) →ₗ[R] M))
    (fun n => ModuleCat.ofHom (cochainDifferential M x n))
    (fun n => ModuleCat.hom_ext (cochainDifferential_comp M x n))

/-- Coefficient Koszul cohomology is homology of the Hom cochain complex. -/
def cohomology (x : List R) (q : ℕ) : ModuleCat R := (cochainComplex M x).homology q

/-- The cochain homotopy is precomposition with left wedge. -/
def cochainWedge (x : List R) (e : Fin x.length → R) (n : ℕ) :
    ((⋀[R]^(n+1) (Fin x.length → R)) →ₗ[R] M) →ₗ[R]
      ((⋀[R]^n (Fin x.length → R)) →ₗ[R] M) :=
  LinearMap.lcomp R M (leftWedge e n)
end AdvCommAlg.Koszul

namespace Specs.AdvCommAlg.Koszul
open _root_.AdvCommAlg.Koszul

def leftWedgeType := ∀ {R : Type u} [CommRing R] {E : Type v}
  [AddCommGroup E] [Module R E], E → ∀ n : ℕ, (⋀[R]^n E) →ₗ[R] (⋀[R]^(n+1) E)
def leftWedgeValue : leftWedgeType.{u,v} := @leftWedge

def coefficientWedgeType := ∀ {R : Type u} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M] (x : List R),
  (Fin x.length → R) → ∀ n : ℕ,
  ((⋀[R]^n (Fin x.length → R)) ⊗[R] M) →ₗ[R]
      ((⋀[R]^(n+1) (Fin x.length → R)) ⊗[R] M)
def coefficientWedgeValue : coefficientWedgeType.{u,v} := @coefficientWedge

def cochainComplexType := ∀ {R : Type u} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M],
  List R → CochainComplex (ModuleCat.{max u v} R) ℕ
def cochainComplexValue : cochainComplexType.{u,v} := @cochainComplex

def cohomologyType := ∀ {R : Type u} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M], List R → ℕ → ModuleCat.{max u v} R
def cohomologyValue : cohomologyType.{u,v} := @cohomology

/-- Coefficients b represent the vector Σ bᵢeᵢ in the standard coordinate module. -/
def listFormSum : Prop := ∀ {R : Type u} [CommRing R] (x : List R)
  (b : Fin x.length → R), listForm x b = ∑ i, b i * x.get i

def idealPreimage : Prop := ∀ {R : Type u} [CommRing R] (x : List R) (a : R),
  a ∈ listIdeal x → ∃ e : Fin x.length → R, listForm x e = a

/-- These are dh+hd=a id, with the missing term zero in degree zero. -/
def coefficientWedgeIdentities : Prop := ∀ {R : Type u} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M] (x : List R) (e : Fin x.length → R),
  (coefficientDifferential M x 0).comp (coefficientWedge M x e 0) =
      listForm x e • LinearMap.id ∧
  ∀ n : ℕ,
    (coefficientDifferential M x (n+1)).comp (coefficientWedge M x e (n+1)) +
      (coefficientWedge M x e n).comp (coefficientDifferential M x n) =
        listForm x e • LinearMap.id

/-- For a displayed linear combination, the homotopy components really are
left wedge by the displayed sum of standard basis vectors, tensor id_M. -/
def explicitNullHomotopy : Prop := ∀ {R : Type u} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M] (x : List R)
  (b : Fin x.length → R) (a : R), (∑ i, b i * x.get i) = a →
  ∃ H : Homotopy (a • 𝟙 (coefficientComplex M x)) 0,
    ∀ n : ℕ, H.hom n (n+1) = ModuleCat.ofHom
      (coefficientWedge M x (∑ i, b i • Pi.basisFun R (Fin x.length) i) n)

def coefficientNullHomotopy : Prop := ∀ {R : Type u} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M] (x : List R) (a : R),
  a ∈ listIdeal x → Nonempty (Homotopy (a • 𝟙 (coefficientComplex M x)) 0)

def cochainWedgeIdentities : Prop := ∀ {R : Type u} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M] (x : List R) (e : Fin x.length → R),
  (cochainWedge M x e 0).comp (cochainDifferential M x 0) =
      listForm x e • LinearMap.id ∧
  ∀ n : ℕ,
    (cochainWedge M x e (n+1)).comp (cochainDifferential M x (n+1)) +
      (cochainDifferential M x n).comp (cochainWedge M x e n) =
        listForm x e • LinearMap.id

def cochainNullHomotopy : Prop := ∀ {R : Type u} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M] (x : List R) (a : R),
  a ∈ listIdeal x → Nonempty (Homotopy (a • 𝟙 (cochainComplex M x)) 0)

def annihilatesHomology : Prop := ∀ {R : Type u} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M] (x : List R) (a : R),
  a ∈ listIdeal x → ∀ q : ℕ, ∀ z : homology M x q, a • z = 0

def annihilatesCohomology : Prop := ∀ {R : Type u} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M] (x : List R) (a : R),
  a ∈ listIdeal x → ∀ q : ℕ, ∀ z : cohomology M x q, a • z = 0

def unitIdealContractible : Prop := ∀ {R : Type u} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M] (x : List R),
  listIdeal x = ⊤ → Nonempty (Homotopy (𝟙 (coefficientComplex M x)) 0)
end Specs.AdvCommAlg.Koszul
