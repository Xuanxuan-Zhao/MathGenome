import MathGenome.Internal.Specs.D05.M15.ExteriorDirectSum
import MathGenome.Internal.D05.M15.ExteriorDirectSum.GradedProduct
import MathGenome.Internal.D05.M15.TensorDirectSum
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
import Batteries.Tactic.OpenPrivate

/-!
The whole-algebra equivalence is Mathlib's universal-property construction,
with its maps checked against the paper's formulas. For each total degree,
`bigrading` distributes the two exterior decompositions over the tensor product.
Inserting the degree pairs has an explicit restriction retraction, so is injective.
Its image is exactly the span used in the prerequisite's total grading. Restricting
the algebra equivalence then yields the fixed-degree equivalence and its formula.
-/

noncomputable section
namespace D05.M15.ExteriorDirectSum

open scoped TensorProduct DirectSum
open Specs.D05.M15.ExteriorDirectSum

open private homogeneousPart_eq_map from MathGenome.Internal.D05.M15.ExteriorDirectSum.GradedProduct

universe u v w

theorem algebra_equivalence : Specs.D05.M15.ExteriorDirectSum.algebra_equivalence := by
  intro K V W _ _ _ _ _
  refine ⟨_root_.ExteriorAlgebra.prodEquivTensor K V W, ?_, ?_, ?_⟩
  · intro v w
    exact _root_.ExteriorAlgebra.prodEquivTensorForward_ι_apply K V W (v, w)
  · exact _root_.ExteriorAlgebra.prodEquivTensor_symm_tmul K V W
  · intro n x
    change (_root_.ExteriorAlgebra.prodEquivTensor K V W) x ∈
      GradedProduct.homogeneousPart K V W n ↔ _
    rw [homogeneousPart_eq_map]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have : y = x := (_root_.ExteriorAlgebra.prodEquivTensor K V W).injective hxy
      simpa [this] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩

section Degree

variable (K : Type u) (V : Type v) (W : Type w)
  [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Distribute over both exterior gradings, retaining the ordered pair of degrees. -/
def bigrading : GradedProduct.gradedTensor K V W ≃ₗ[K]
    ⨁ ij : ℕ × ℕ, DegreePiece K V W ij :=
  (GradedTensorProduct.auxEquiv K (fun p : ℕ => ⋀[K]^p V) (fun q : ℕ => ⋀[K]^q W)) ≪≫ₗ
    TensorProduct.directSum K K (fun p : ℕ => ⋀[K]^p V) (fun q : ℕ => ⋀[K]^q W)

@[simp] theorem bigrading_tmul (p q : ℕ) (a : ⋀[K]^p V) (b : ⋀[K]^q W) :
    bigrading K V W (GradedTensorProduct.tmul K a.val b.val) =
      DirectSum.lof K (ℕ × ℕ) (DegreePiece K V W) (p, q) (a ⊗ₜ[K] b) := by
  simp only [bigrading, LinearEquiv.trans_apply, GradedTensorProduct.auxEquiv_tmul,
    DirectSum.decompose_coe]
  exact TensorProduct.directSum_lof_tmul_lof K K
    (M₁ := fun p : ℕ => ⋀[K]^p V) (M₂ := fun q : ℕ => ⋀[K]^q W) p a q b

/-- Insert only the summands of the specified total degree. -/
def degreeInclusion (n : ℕ) :
    (⨁ ij : DegreePairs n, DegreePiece K V W ij.val) →ₗ[K]
      ⨁ ij : ℕ × ℕ, DegreePiece K V W ij :=
  DirectSum.toModule K _ _ (fun ij => DirectSum.lof K _ (DegreePiece K V W) ij.val)

theorem degreeInclusion_injective (n : ℕ) :
    Function.Injective (degreeInclusion K V W n) := by
  let r := DFinsupp.subtypeDomainLinearMap K (DegreePiece K V W)
    (fun ij : ℕ × ℕ => ij.1 + ij.2 = n)
  have h : r.comp (degreeInclusion K V W n) = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro ij
    apply LinearMap.ext
    intro x
    apply DirectSum.ext
    intro ij'
    change (r (degreeInclusion K V W n (DirectSum.lof K _ _ ij x))) ij' = _
    rw [degreeInclusion, DirectSum.toModule_lof]
    change (DirectSum.lof K (ℕ × ℕ) (DegreePiece K V W) ij.val x) ij'.val =
      (DirectSum.lof K (DegreePairs n) (fun ij => DegreePiece K V W ij.val) ij x) ij' 
    by_cases heq : ij = ij'
    · subst ij'
      simp
    · have hv : ij.val ≠ ij'.val := fun h => heq (Subtype.ext h)
      simp [DirectSum.lof_eq_of, DirectSum.of_apply, heq, hv]
  intro x y hxy
  exact (LinearMap.congr_fun h x).symm.trans
    ((congrArg r hxy).trans (LinearMap.congr_fun h y))

/-- Sum the homogeneous tensor inclusions in total degree `n`. -/
def degreeTensorMap (n : ℕ) :
    (⨁ ij : DegreePairs n, DegreePiece K V W ij.val) →ₗ[K]
      GradedProduct.gradedTensor K V W :=
  (bigrading K V W).symm.toLinearMap.comp (degreeInclusion K V W n)

@[simp] theorem degreeTensorMap_lof_tmul (n : ℕ) (ij : DegreePairs n)
    (a : ⋀[K]^ij.val.1 V) (b : ⋀[K]^ij.val.2 W) :
    degreeTensorMap K V W n (DirectSum.lof K _ _ ij (a ⊗ₜ[K] b)) =
      GradedTensorProduct.tmul K a.val b.val := by
  apply (bigrading K V W).injective
  simp only [degreeTensorMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, degreeInclusion, DirectSum.toModule_lof,
    bigrading_tmul]

theorem degreeTensorMap_injective (n : ℕ) :
    Function.Injective (degreeTensorMap K V W n) :=
  (bigrading K V W).symm.injective.comp (degreeInclusion_injective K V W n)

theorem degreeTensorMap_range (n : ℕ) :
    LinearMap.range (degreeTensorMap K V W n) = GradedProduct.homogeneousPart K V W n := by
  apply le_antisymm
  · rintro x ⟨z, rfl⟩
    induction z using DirectSum.induction_on with
    | zero => simp
    | add z z' hz hz' =>
      simpa only [map_add] using (GradedProduct.homogeneousPart K V W n).add_mem hz hz'
    | of ij z =>
      induction z using TensorProduct.inductionOn with
      | add z z' hz hz' =>
        simpa only [map_add] using (GradedProduct.homogeneousPart K V W n).add_mem hz hz'
      | tmul a b =>
        rw [← DirectSum.lof_eq_of K, degreeTensorMap_lof_tmul]
        exact Submodule.subset_span ⟨ij.val.1, ij.val.2, ij.property, a, b, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨p, q, hpq, a, b, rfl⟩
    refine ⟨DirectSum.lof K (DegreePairs n) (fun ij => DegreePiece K V W ij.val)
      ⟨(p, q), hpq⟩ (a ⊗ₜ[K] b), ?_⟩
    exact degreeTensorMap_lof_tmul K V W n ⟨(p, q), hpq⟩ a b

/-- The fixed-total-degree sum is equivalent to its natural image. -/
def degreeTensorEquiv (n : ℕ) :
    (⨁ ij : DegreePairs n, DegreePiece K V W ij.val) ≃ₗ[K]
      GradedProduct.homogeneousPart K V W n :=
  LinearEquiv.ofInjective (degreeTensorMap K V W n) (degreeTensorMap_injective K V W n) ≪≫ₗ
    LinearEquiv.ofEq _ _ (degreeTensorMap_range K V W n)

@[simp] theorem degreeTensorEquiv_coe (n : ℕ)
    (z : ⨁ ij : DegreePairs n, DegreePiece K V W ij.val) :
    (degreeTensorEquiv K V W n z : GradedProduct.gradedTensor K V W) =
      degreeTensorMap K V W n z := rfl

/-- Restrict the algebra equivalence and identify the total-degree tensor span. -/
def degreeEquiv (n : ℕ) : (⋀[K]^n (V × W)) ≃ₗ[K]
    ⨁ ij : DegreePairs n, DegreePiece K V W ij.val :=
  (_root_.ExteriorAlgebra.prodEquivTensor K V W).toLinearEquiv.ofSubmodules
    (⋀[K]^n (V × W)) (GradedProduct.homogeneousPart K V W n)
    (homogeneousPart_eq_map n).symm ≪≫ₗ (degreeTensorEquiv K V W n).symm

end Degree

theorem degree_decomposition : Specs.D05.M15.ExteriorDirectSum.degree_decomposition := by
  intro K V W _ _ _ _ _ n
  refine ⟨degreeEquiv K V W n, ?_⟩
  intro ij a b
  change (_root_.ExteriorAlgebra.prodEquivTensor K V W).symm
    (degreeTensorEquiv K V W n (DirectSum.lof K (DegreePairs n)
      (fun ij => DegreePiece K V W ij.val) ij (a ⊗ₜ[K] b))) = _
  rw [degreeTensorEquiv_coe, degreeTensorMap_lof_tmul,
    _root_.ExteriorAlgebra.prodEquivTensor_symm_tmul]
end D05.M15.ExteriorDirectSum
