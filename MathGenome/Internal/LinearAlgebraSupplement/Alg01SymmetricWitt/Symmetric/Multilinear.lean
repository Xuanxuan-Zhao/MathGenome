import MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Symmetric.Grading
import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Symmetric.Multilinear

namespace Alg01SymmetricWitt.Symmetric.Multilinear

open Alg01SymmetricWitt.Symmetric.Algebra
open Alg01SymmetricWitt.Symmetric.Grading
open Specs.Alg01SymmetricWitt.Symmetric.Multilinear (SymmetricMultilinearMap)

section Universal

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {n : ℕ}

/-- Permuting the inputs leaves the pure product unchanged in the homogeneous component. -/
theorem pureProduct_perm (x : Fin n → M) (σ : Equiv.Perm (Fin n)) :
    pureProduct R M n (x ∘ σ) = pureProduct R M n x := by
  apply Subtype.ext
  rw [pureProductCoe, pureProductCoe]
  exact Equiv.prod_comp σ (fun i => SymmetricAlgebra.ι R M (x i))

/-- Restriction of a linear map on the symmetric degree to pure products. -/
def restrict (g : degree R M n →ₗ[R] N) : SymmetricMultilinearMap R M N n :=
  ⟨g.compMultilinearMap (pureProduct R M n), fun x σ => congrArg g (pureProduct_perm x σ)⟩

private theorem relations_le_ker_lift (f : SymmetricMultilinearMap R M N n) :
    adjacentRelations R M n ≤ LinearMap.ker (PiTensorProduct.lift f.val) := by
  rw [adjacent_eq_permutation]
  apply Submodule.span_le.mpr
  rintro _ ⟨x, σ, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, PiTensorProduct.lift.tprod,
    PiTensorProduct.lift.tprod, f.property x σ, sub_self]

/-- Extend a symmetric multilinear map by lifting through the tensor degree quotient. -/
noncomputable def extend (f : SymmetricMultilinearMap R M N n) : degree R M n →ₗ[R] N :=
  ((adjacentRelations R M n).liftQ (PiTensorProduct.lift f.val) (relations_le_ker_lift f)).comp
    (degreeQuotientEquiv R M n).symm.toLinearMap

@[simp] theorem extend_pureProduct (f : SymmetricMultilinearMap R M N n) (x : Fin n → M) :
    extend f (pureProduct R M n x) = f.val x := by
  have h := (degreeQuotientEquiv R M n).symm_apply_eq.mpr
    (degreeQuotientEquiv_tprod R M n x).symm
  change (adjacentRelations R M n).liftQ (PiTensorProduct.lift f.val) (relations_le_ker_lift f)
    ((degreeQuotientEquiv R M n).symm (pureProduct R M n x)) = f.val x
  rw [h]
  exact PiTensorProduct.lift.tprod x

/-- Linear maps on a symmetric degree are determined by their values on pure products. -/
theorem hom_ext {g h : degree R M n →ₗ[R] N}
    (hh : ∀ x, g (pureProduct R M n x) = h (pureProduct R M n x)) : g = h := by
  have he : g.comp (degreeQuotientMap R M n) = h.comp (degreeQuotientMap R M n) :=
    PiTensorProduct.ext (MultilinearMap.ext hh)
  exact LinearMap.ext fun y => by
    obtain ⟨t, rfl⟩ := (degreeMap R M n).surjective_rangeRestrict y
    exact LinearMap.congr_fun he t

/-- The universal bijection for the degree submodule of the symmetric algebra. -/
noncomputable def equiv (R M N : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (n : ℕ) :
    (degree R M n →ₗ[R] N) ≃ SymmetricMultilinearMap R M N n where
  toFun := restrict
  invFun := extend
  left_inv g := hom_ext fun x => extend_pureProduct (restrict g) x
  right_inv f := Subtype.ext (MultilinearMap.ext fun x => extend_pureProduct f x)

theorem universal : Specs.Alg01SymmetricWitt.Symmetric.Multilinear.universal := by
  intro R M N _ _ _ _ _ n
  exact ⟨equiv R M N n, fun _ => rfl, extend_pureProduct⟩

end Universal

section LowDegrees

variable (R M N : Type*) [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

private def symmetricEquivOfSubsingleton (n : ℕ) [Subsingleton (Fin n)] :
    SymmetricMultilinearMap R M N n ≃ MultilinearMap R (fun _ : Fin n => M) N where
  toFun := Subtype.val
  invFun f := ⟨f, fun x σ =>
    congrArg f (funext fun i => congrArg x (Subsingleton.elim (σ i) i))⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

/-- An empty symmetric multilinear map is determined by its value on the empty tuple. -/
def degreeZeroEquiv : SymmetricMultilinearMap R M N 0 ≃ N where
  toFun f := f.val (fun i => Fin.elim0 i)
  invFun y := ⟨MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 => M) y, fun _ _ => rfl⟩
  left_inv f := Subtype.ext (MultilinearMap.ext fun x =>
    congrArg f.val (Subsingleton.elim _ x))
  right_inv _ := rfl

theorem degreeZero : Specs.Alg01SymmetricWitt.Symmetric.Multilinear.degreeZero := by
  intro R M N _ _ _ _ _
  let x : Fin 0 → M := fun i => Fin.elim0 i
  refine ⟨degreeZeroEquiv R M N, pureProduct R M 0 x, ?_, fun _ => rfl, ?_⟩
  · rw [pureProductCoe, Fin.prod_univ_zero]
  · intro g f hf
    change f.val x = _
    rw [hf]
    rfl

/-- Evaluation on the one-entry tuple identifies symmetric multilinear maps with linear maps. -/
def degreeOneEquiv : SymmetricMultilinearMap R M N 1 ≃ (M →ₗ[R] N) :=
  (symmetricEquivOfSubsingleton R M N 1).trans (MultilinearMap.ofSubsingleton R M N (0 : Fin 1)).symm

theorem degreeOne : Specs.Alg01SymmetricWitt.Symmetric.Multilinear.degreeOne := by
  intro R M N _ _ _ _ _
  refine ⟨degreeOneEquiv R M N, Grading.degreeOneEquiv R M, Grading.degreeOneEquiv_coe R M,
    fun _ _ => rfl, ?_⟩
  intro g f hf
  apply LinearMap.ext
  intro x
  change f.val (fun _ => x) = g (Grading.degreeOneEquiv R M x)
  rw [hf, LinearMap.compMultilinearMap_apply]
  have hp : pureProduct R M 1 (fun _ => x) = Grading.degreeOneEquiv R M x := by
    apply Subtype.ext
    rw [pureProductCoe, Fin.prod_univ_one, Grading.degreeOneEquiv_coe]
  exact congrArg g hp

end LowDegrees

section Naturality

variable {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M']

/-- Apply a linear map to every factor of a symmetric product in a fixed degree. -/
noncomputable def mapDegree (n : ℕ) (h : M →ₗ[R] M') : degree R M n →ₗ[R] degree R M' n :=
  extend ⟨(pureProduct R M' n).compLinearMap (fun _ => h),
    fun x σ => pureProduct_perm (fun i => h (x i)) σ⟩

@[simp] theorem mapDegree_pureProduct (n : ℕ) (h : M →ₗ[R] M') (x : Fin n → M) :
    mapDegree n h (pureProduct R M n x) = pureProduct R M' n (fun i => h (x i)) :=
  extend_pureProduct _ x

/-- The map on symmetric degrees is induced by the map on tensor powers. -/
theorem mapDegree_comp_quotient (n : ℕ) (h : M →ₗ[R] M') :
    (mapDegree n h).comp (degreeQuotientMap R M n) =
      (degreeQuotientMap R M' n).comp (PiTensorProduct.map (fun _ : Fin n => h)) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change mapDegree n h (pureProduct R M n x) =
    degreeQuotientMap R M' n (PiTensorProduct.map (fun _ : Fin n => h) (PiTensorProduct.tprod R x))
  rw [mapDegree_pureProduct, PiTensorProduct.map_tprod]
  rfl

theorem inducedDegreeMap : Specs.Alg01SymmetricWitt.Symmetric.Multilinear.inducedDegreeMap := by
  intro R M M' _ _ _ _ _ n h
  refine ⟨mapDegree n h, ⟨mapDegree_pureProduct n h, mapDegree_comp_quotient n h⟩, ?_⟩
  intro F hF
  exact hom_ext fun x => (hF.1 x).trans (mapDegree_pureProduct n h x).symm

theorem naturalityTarget : Specs.Alg01SymmetricWitt.Symmetric.Multilinear.naturalityTarget := by
  intro R M N N' _ _ _ _ _ _ _ n h g
  exact MultilinearMap.ext fun _ => rfl

theorem naturalitySource : Specs.Alg01SymmetricWitt.Symmetric.Multilinear.naturalitySource := by
  intro R M M' N _ _ _ _ _ _ _ n h F hF g
  apply MultilinearMap.ext
  exact fun x => congrArg g (hF x)

end Naturality

end Alg01SymmetricWitt.Symmetric.Multilinear
