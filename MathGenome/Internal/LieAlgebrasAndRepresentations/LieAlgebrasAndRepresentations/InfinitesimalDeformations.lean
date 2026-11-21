import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.InfinitesimalDeformations
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.AbelianExtensions
import Mathlib.RingTheory.AdjoinRoot

open scoped TensorProduct
noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace LieAlgebrasAndRepresentations.InfinitesimalDeformations
open LieModule.Cohomology
open LieAlgebrasAndRepresentations.AbelianExtensions

section Quotient
open Polynomial
variable (k : Type u) [CommRing k]

private def quotientToDualNumber :
    AdjoinRoot ((X : k[X]) ^ 2) →ₐ[k] DualNumber k :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId k (DualNumber k)) DualNumber.eps (by simp)

private def dualNumberToQuotient :
    DualNumber k →ₐ[k] AdjoinRoot ((X : k[X]) ^ 2) :=
  DualNumber.lift ⟨(Algebra.ofId k _, AdjoinRoot.root ((X : k[X]) ^ 2)), by
    rw [← pow_two]
    simp only [AdjoinRoot.root, ← map_pow]
    exact AdjoinRoot.mk_eq_zero.mpr dvd_rfl, fun _ => Commute.all _ _⟩

@[simp] private theorem quotientToDualNumber_root :
    quotientToDualNumber k (AdjoinRoot.root ((X : k[X]) ^ 2)) = DualNumber.eps := by
  simp [quotientToDualNumber]

@[simp] private theorem dualNumberToQuotient_eps :
    dualNumberToQuotient k DualNumber.eps = AdjoinRoot.root ((X : k[X]) ^ 2) := by
  simp [dualNumberToQuotient]

/-- The polynomial quotient from the source, with the class of the variable
identified with the infinitesimal in the dual-number model. -/
def quotientDualNumberEquiv : AdjoinRoot ((X : k[X]) ^ 2) ≃ₐ[k] DualNumber k :=
  AlgEquiv.ofAlgHom (quotientToDualNumber k) (dualNumberToQuotient k)
    (DualNumber.algHom_ext (by simp)) (AdjoinRoot.algHom_ext (by simp))

@[simp] theorem quotientDualNumberEquiv_root :
    quotientDualNumberEquiv k (AdjoinRoot.root ((X : k[X]) ^ 2)) = DualNumber.eps :=
  quotientToDualNumber_root k

end Quotient

variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]

private def dualPair : DualNumber k ≃ₗ[k] (k × k) where
  toFun r := (r.fst,r.snd)
  invFun p := ⟨p.1,p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def tensorCoordinates : (g ⊗[k] DualNumber k) ≃ₗ[k] (g × g) :=
  (TensorProduct.congr (LinearEquiv.refl k g) dualPair).trans
    ((TensorProduct.prodRight k k g k k).trans
      ((TensorProduct.rid k g).prodCongr (TensorProduct.rid k g)))

open Polynomial in
/-- Coordinates on the scalar extension by the polynomial quotient. -/
def quotientTensorCoordinates :
    (g ⊗[k] AdjoinRoot ((X : k[X]) ^ 2)) ≃ₗ[k] (g × g) :=
  (TensorProduct.congr (LinearEquiv.refl k g)
    (quotientDualNumberEquiv k).toLinearEquiv).trans tensorCoordinates

@[simp] theorem tensorCoordinates_tmul (x : g) (r : DualNumber k) :
    tensorCoordinates (x ⊗ₜ[k] r) = (r.fst • x, r.snd • x) := by
  simp [tensorCoordinates, dualPair]

theorem tensorCoordinates_scalar (r : DualNumber k) (z : g ⊗[k] DualNumber k) :
    tensorCoordinates (tensorScalar k g r z) = dualSMul k g r (tensorCoordinates z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x s => simp [tensorScalar, dualSMul, add_smul, mul_smul]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    simp [dualSMul, smul_add]
    abel

open Polynomial in
@[simp] theorem quotientTensorCoordinates_tmul (x : g) (r : AdjoinRoot ((X : k[X]) ^ 2)) :
    quotientTensorCoordinates (x ⊗ₜ[k] r) =
      ((quotientDualNumberEquiv k r).fst • x, (quotientDualNumberEquiv k r).snd • x) := by
  simp [quotientTensorCoordinates]

open Polynomial in
/-- Multiply the right tensor factor by a scalar in the polynomial quotient. -/
def quotientTensorScalar (r : AdjoinRoot ((X : k[X]) ^ 2)) :
    (g ⊗[k] AdjoinRoot ((X : k[X]) ^ 2)) →ₗ[k] (g ⊗[k] AdjoinRoot ((X : k[X]) ^ 2)) :=
  TensorProduct.map LinearMap.id (LinearMap.mulLeft k r)

open Polynomial in
/-- Transport the quotient scalar action to the two coordinates. -/
theorem quotientTensorCoordinates_scalar (r : AdjoinRoot ((X : k[X]) ^ 2))
    (z : g ⊗[k] AdjoinRoot ((X : k[X]) ^ 2)) :
    quotientTensorCoordinates (quotientTensorScalar r z) =
      dualSMul k g (quotientDualNumberEquiv k r) (quotientTensorCoordinates z) := by
  let e := TensorProduct.congr (LinearEquiv.refl k g) (quotientDualNumberEquiv k).toLinearEquiv
  have h : e.toLinearMap.comp (quotientTensorScalar (g := g) r) =
      (tensorScalar k g (quotientDualNumberEquiv k r)).comp e.toLinearMap := by
    apply TensorProduct.ext'
    intro x s
    simp [e, quotientTensorScalar, tensorScalar]
  change tensorCoordinates (e (quotientTensorScalar r z)) =
    dualSMul k g (quotientDualNumberEquiv k r) (tensorCoordinates (e z))
  rw [show e (quotientTensorScalar r z) =
      tensorScalar k g (quotientDualNumberEquiv k r) (e z) from LinearMap.congr_fun h z]
  exact tensorCoordinates_scalar _ _

theorem tensorModel_spec :
    Specs.LieAlgebrasAndRepresentations.InfinitesimalDeformations.tensorModelStatement k g :=
  ⟨tensorCoordinates, tensorCoordinates_tmul, tensorCoordinates_scalar⟩

theorem jacobi_spec :
    Specs.LieAlgebrasAndRepresentations.InfinitesimalDeformations.jacobiStatement k g :=
  twisted_jacobi_iff

theorem linearJacobi_spec :
    Specs.LieAlgebrasAndRepresentations.InfinitesimalDeformations.linearJacobiStatement k g := by
  intro c x y z
  simp only [d₂₃_apply]
  rw [← twoCochain_skew c x z, ← lie_skew x z, map_neg]
  simp only [neg_lie, LinearMap.neg_apply]
  rw [← lie_skew z (c x y), ← lie_skew x (c y z), ← lie_skew y (c x z)]
  abel

def bracketMap (c : twoCochain k g g) : (g × g) →ₗ[k] (g × g) →ₗ[k] (g × g) where
  toFun p :=
    { toFun := bracketFormula c p
      map_add' q r := by
        apply Prod.ext <;> simp [bracketFormula, twistedBracket, lie_add, add_lie,
          map_add] <;> abel
      map_smul' r q := by
        apply Prod.ext <;> simp [bracketFormula, twistedBracket, lie_smul, smul_lie,
          map_smul, smul_add, smul_sub] }
  map_add' p q := by
    apply LinearMap.ext
    intro r
    apply Prod.ext <;> simp [bracketFormula, twistedBracket, lie_add, add_lie,
      map_add] <;> abel
  map_smul' r p := by
    apply LinearMap.ext
    intro q
    apply Prod.ext <;> simp [bracketFormula, twistedBracket, lie_smul, smul_lie,
      map_smul, smul_add, smul_sub]

@[simp] theorem bracketMap_apply (c : twoCochain k g g) (p q : g × g) :
    bracketMap c p q = bracketFormula c p q := rfl

def model (c : twoCocycle k g g) : Deformation k g where
  bracket := bracketMap c.1
  alternating p := by simp [bracketFormula, twistedBracket]
  scalar_left r p q := by
    apply Prod.ext
    · simp [bracketFormula, twistedBracket, dualSMul]
    · simp [bracketFormula, twistedBracket, dualSMul, lie_add, lie_smul,
        smul_lie, smul_sub, smul_add]
      rw [← lie_skew p.1 q.1]
      simp only [smul_neg]
      abel
  scalar_right r p q := by
    apply Prod.ext <;> simp [bracketFormula, twistedBracket, dualSMul, lie_add,
      lie_smul, smul_lie, smul_sub, smul_add] <;> abel
  reduction _ _ := rfl
  jacobi := (twisted_jacobi_iff c.1).mpr c.2

theorem models_spec :
    Specs.LieAlgebrasAndRepresentations.InfinitesimalDeformations.modelsStatement k g := by
  intro c
  exact ⟨model c, fun _ _ => rfl⟩

/-- Recover the actual ε coefficient on constant vectors. -/
def coefficient (B : Deformation k g) : twoCochain k g g :=
  ⟨(B.bracket.compl₁₂ (LinearMap.inl k g g) (LinearMap.inl k g g)).compr₂
      (LinearMap.snd k g g), by
    intro x
    change (B.bracket (x,0) (x,0)).2 = 0
    rw [B.alternating]
    rfl⟩

@[simp] theorem coefficient_apply (B : Deformation k g) (x y : g) :
    coefficient B x y = (B.bracket (x,0) (y,0)).2 := rfl

private theorem epsilon_left (B : Deformation k g) (x : g) (q : g × g) :
    B.bracket (0,x) q = (0,⁅x,q.1⁆) := by
  have h := B.scalar_left (DualNumber.eps : DualNumber k) (x,0) q
  simpa [dualSMul, B.reduction] using h

private theorem epsilon_right (B : Deformation k g) (p : g × g) (y : g) :
    B.bracket p (0,y) = (0,⁅p.1,y⁆) := by
  have h := B.scalar_right (DualNumber.eps : DualNumber k) p (y,0)
  simpa [dualSMul, B.reduction] using h

theorem bracket_normal_form (B : Deformation k g) (p q : g × g) :
    B.bracket p q = bracketFormula (coefficient B) p q := by
  have hp : p = (p.1,0) + (0,p.2) := by ext <;> simp
  have hq : q = (q.1,0) + (0,q.2) := by ext <;> simp
  conv_lhs => rw [hp, hq]
  simp only [map_add, LinearMap.add_apply, epsilon_left, epsilon_right]
  apply Prod.ext
  · simp [bracketFormula, twistedBracket, B.reduction]
  · simp only [Prod.snd_add, bracketFormula, twistedBracket, coefficient_apply]
    rw [← lie_skew q.1 p.2]
    simp only [zero_lie, add_zero]
    abel

def cocycle (B : Deformation k g) : twoCocycle k g g :=
  ⟨coefficient B, (twisted_jacobi_iff (coefficient B)).mp (by
    intro p q r
    simpa only [bracket_normal_form, bracketFormula] using B.jacobi p q r)⟩

theorem coefficient_unique (B : Deformation k g) (c : twoCochain k g g)
    (hc : ∀ p q, B.bracket p q = bracketFormula c p q) : coefficient B = c := by
  apply Subtype.ext
  ext x y
  have h := congrArg Prod.snd (hc (x,0) (y,0))
  simpa [bracketFormula, twistedBracket] using h

theorem normalForm_spec :
    Specs.LieAlgebrasAndRepresentations.InfinitesimalDeformations.normalFormStatement k g := by
  intro B
  refine ⟨cocycle B, bracket_normal_form B, ?_⟩
  intro c hc
  apply Subtype.ext
  exact (coefficient_unique B c.1 hc).symm

def shearEquiv (a : g →ₗ[k] g) : (g × g) ≃ₗ[k] (g × g) where
  toFun := shear a
  invFun := shear (-a)
  left_inv p := by ext <;> simp [shear]
  right_inv p := by ext <;> simp [shear]
  map_add' p q := by ext <;> simp [shear, map_add] <;> abel
  map_smul' r p := by ext <;> simp [shear, smul_add]

def shearChange (a : g →ₗ[k] g) : CoordinateChange k g where
  equiv := shearEquiv a
  scalar r p := by
    change shear a (dualSMul k g r p) = dualSMul k g r (shear a p)
    ext <;> simp [shear, dualSMul, smul_add] <;> abel
  reduction _ := rfl

def coordinateCoefficient (T : CoordinateChange k g) : g →ₗ[k] g :=
  (LinearMap.snd k g g).comp (T.equiv.toLinearMap.comp (LinearMap.inl k g g))

private theorem coordinate_epsilon (T : CoordinateChange k g) (x : g) :
    T.equiv (0,x) = (0,x) := by
  have h := T.scalar (DualNumber.eps : DualNumber k) (x,0)
  simpa [dualSMul, T.reduction] using h

theorem coordinate_normal_form (T : CoordinateChange k g) (p : g × g) :
    T.equiv p = shear (coordinateCoefficient T) p := by
  have hp : p = (p.1,0) + (0,p.2) := by ext <;> simp
  conv_lhs => rw [hp, map_add, coordinate_epsilon]
  apply Prod.ext
  · simp [shear, T.reduction]
  · simp [shear, coordinateCoefficient, add_comm]

theorem coordinates_spec :
    Specs.LieAlgebrasAndRepresentations.InfinitesimalDeformations.coordinatesStatement k g := by
  constructor
  · intro T
    refine ⟨coordinateCoefficient T, coordinate_normal_form T, ?_⟩
    intro a ha
    apply LinearMap.ext
    intro x
    have h := congrArg Prod.snd (ha (x,0))
    simpa [shear, coordinateCoefficient] using h.symm
  · intro a
    exact ⟨shearChange a, fun _ => rfl⟩

theorem pullback_spec :
    Specs.LieAlgebrasAndRepresentations.InfinitesimalDeformations.pullbackStatement k g :=
  LieAlgebrasAndRepresentations.AbelianExtensions.shear

/-- Extracting the coefficient of a displayed model recovers that coefficient. -/
theorem cocycle_model (c : twoCocycle k g g) : cocycle (model c) = c := by
  apply Subtype.ext
  exact coefficient_unique (model c) c.1 (fun _ _ => rfl)

def deformationClass (B : Deformation k g) : LowH2 (k := k) (g := g) (M := g) :=
  lowClass (cocycle B)

theorem deformationClass_surjective :
    Function.Surjective (deformationClass (k := k) (g := g)) := by
  intro q
  obtain ⟨c, rfl⟩ := (lowBoundaries (k := k) (g := g) (M := g)).mkQ_surjective q
  refine ⟨model c, ?_⟩
  simp [deformationClass, cocycle_model, lowClass]

/-- The full coordinate equivalence relation is exactly a CE coboundary. -/
theorem equivalent_iff (B D : Deformation k g) :
    Equivalent B D ↔ ∃ a : g →ₗ[k] g, cocycle D = cocycle B + coboundaryToCocycles a := by
  constructor
  · rintro ⟨T, hT⟩
    let a := coordinateCoefficient T
    refine ⟨a, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    ext x y
    have h := hT (x,0) (y,0)
    simp only [coordinate_normal_form, bracket_normal_form] at h
    have hs := congrArg Prod.snd h
    simp only [bracketFormula, twistedBracket, shear, lie_zero, sub_zero,
      zero_add] at hs
    change coefficient D x y + a ⁅x,y⁆ =
      ⁅x,a y⁆ - ⁅y,a x⁆ + coefficient B x y at hs
    change coefficient D x y = coefficient B x y +
      (⁅x,a y⁆ - ⁅y,a x⁆ - a ⁅x,y⁆)
    calc
      _ = (⁅x,a y⁆ - ⁅y,a x⁆ + coefficient B x y) - a ⁅x,y⁆ :=
        eq_sub_of_add_eq hs
      _ = _ := by abel
  · rintro ⟨a, ha⟩
    refine ⟨shearChange a, ?_⟩
    intro p q
    change shear a (D.bracket p q) =
      B.bracket (shear a p) (shear a q)
    rw [bracket_normal_form, bracket_normal_form]
    have hc : coefficient D = coefficient B + d₁₂ k g g a :=
      congrArg Subtype.val ha
    rw [hc]
    exact pullback_spec _ _ _ _

theorem deformationClass_eq_iff (B D : Deformation k g) :
    deformationClass B = deformationClass D ↔ Equivalent B D := by
  rw [equivalent_iff]
  change lowClass (cocycle B) = lowClass (cocycle D) ↔ _
  rw [eq_comm, lowClass_eq_iff]

open AdvancedHomologicalAlgebra.CE in
theorem classification_spec :
    Specs.LieAlgebrasAndRepresentations.InfinitesimalDeformations.classificationStatement k g := by
  intro δ hs hδ
  obtain ⟨e,j,hj,he⟩ := ceComparison_spec δ hs hδ
  refine ⟨fun B => e (deformationClass B),
    e.surjective.comp deformationClass_surjective, ?_, ?_⟩
  · intro B D
    rw [e.injective.eq_iff, deformationClass_eq_iff]
  · intro B c hc
    have hb : cocycle B = c := Subtype.ext (coefficient_unique B c.1 hc)
    refine ⟨j c, hj c, ?_⟩
    change e (lowClass (cocycle B)) = _
    rw [hb, he]

end LieAlgebrasAndRepresentations.InfinitesimalDeformations
