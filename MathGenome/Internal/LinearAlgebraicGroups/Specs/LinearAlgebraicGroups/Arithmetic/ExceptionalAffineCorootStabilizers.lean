import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.GroupTheory.SemidirectProduct

noncomputable section

open scoped TensorProduct Matrix
open LieAlgebrasAndRepresentations
open LinearAlgebraicGroups.Specs.AbsoluteDynkinTypes (CartanRoots PreservesCartan)

namespace LinearAlgebraicGroups.Specs.ExceptionalAffineCorootStabilizers

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
variable (Q : RootDatum ι X Y)

/-- The covariant Weyl action on the cocharacter lattice. -/
def cocharacterAction : Q.weylGroup →* (Y ≃ₗ[ℤ] Y) where
  toFun w := w.val.coweightEquiv.symm
  map_one' := by
    change (RootPairing.Equiv.coweightEquiv (1 : RootPairing.Aut Q)).symm = 1
    exact congrArg LinearEquiv.symm (MulOpposite.op_injective ((RootPairing.Equiv.coweightHom Q).map_one))
  map_mul' v w := by
    change (RootPairing.Equiv.coweightEquiv (v.val * w.val)).symm =
      v.val.coweightEquiv.symm * w.val.coweightEquiv.symm
    exact congrArg LinearEquiv.symm
      (MulOpposite.op_injective ((RootPairing.Equiv.coweightHom Q).map_mul v.val w.val))

/-- The affine Weyl group with its integral translation lattice. -/
def translationAction : Q.weylGroup →* MulAut (Multiplicative Y) where
  toFun w := AddEquiv.toMultiplicative (cocharacterAction Q w).toAddEquiv
  map_one' := by ext; simp [map_one]
  map_mul' v w := by ext; simp [map_mul]

abbrev AffineWeylGroup := Multiplicative Y ⋊[translationAction Q] Q.weylGroup

abbrev Space (Y : Type*) [AddCommGroup Y] := ℝ ⊗[ℤ] Y

/-- The natural map of the translation lattice into its real scalar extension. -/
def latticeMap : Y →ₗ[ℤ] Space Y :=
  TensorProduct.mk ℤ ℝ Y 1

def realAction (w : Q.weylGroup) : Space Y ≃ₗ[ℝ] Space Y :=
  LinearEquiv.baseChange ℤ ℝ Y Y (cocharacterAction Q w)

instance affineAction : MulAction (AffineWeylGroup Q) (Space Y) where
  smul g x := latticeMap g.left.toAdd + realAction Q g.right x
  one_smul x := by
    change latticeMap (0 : Y) + realAction Q 1 x = x
    rw [map_zero, zero_add]
    change ((cocharacterAction Q 1).toLinearMap.baseChange ℝ) x = x
    rw [map_one]
    exact congrArg (fun f : Module.End ℝ (Space Y) => f x) (LinearMap.baseChange_one ℤ Y (A := ℝ))
  mul_smul v w x := by
    change latticeMap (v.left.toAdd + cocharacterAction Q v.right w.left.toAdd) +
      realAction Q (v.right * w.right) x =
      latticeMap v.left.toAdd + realAction Q v.right
        (latticeMap w.left.toAdd + realAction Q w.right x)
    rw [map_add, map_add, ← add_assoc]
    congr 1
    change ((cocharacterAction Q (v.right * w.right)).toLinearMap.baseChange ℝ) x =
      ((cocharacterAction Q v.right).toLinearMap.baseChange ℝ)
        (((cocharacterAction Q w.right).toLinearMap.baseChange ℝ) x)
    rw [map_mul]
    exact congrArg (fun f : Module.End ℝ (Space Y) => f x)
      (LinearMap.baseChange_mul (A := ℝ) (cocharacterAction Q v.right).toLinearMap
        (cocharacterAction Q w.right).toLinearMap)

/-- The real extension of evaluation by the root character. -/
def rootValue (i : ι) : Space Y →ₗ[ℝ] ℝ :=
  RootData.extendFunctional ℝ (Q.root' i)

def wallReflection (i : ι) (k : ℤ) : AffineWeylGroup Q :=
  ⟨Multiplicative.ofAdd (k • Q.coroot i), RootPairing.weylGroup.ofIdx Q i⟩

def wallGenerators (x : Space Y) : Set (AffineWeylGroup Q) :=
  {g | ∃ (i : ι) (k : ℤ), rootValue Q i x = (k : ℝ) ∧ g = wallReflection Q i k}

def congruenceGenerators (d : ℕ) (y : Y) : Set Q.weylGroup :=
  {w | ∃ i, (d : ℤ) ∣ Q.toLinearMap (Q.root i) y ∧
    w = RootPairing.weylGroup.ofIdx Q i}

/-- Highest-root coordinates and exclusion of the nonzero alcove vertices
from the simple-coroot lattice. -/
def HighestRootAndVertices {n : ℕ} (m : Fin n → ℤ) : Prop :=
  (∀ i, 0 < m i) ∧
  CartanRoots (CartanMatrix.E n) (CartanMatrix.E n *ᵥ m, m) ∧
  (∀ p, CartanRoots (CartanMatrix.E n) p → ∀ i, p.2 i ≤ m i) ∧
  ∀ (i : Fin n) (a : Fin n → ℤ),
    ¬ ∀ j, (m i : ℝ) * (∑ k, (a k : ℝ) * (CartanMatrix.E n k j : ℝ)) =
      (Pi.single i 1 : Fin n → ℝ) j

def WallReflectionFormula.{u,v,w} : Prop :=
  ∀ {ι : Type u} {X : Type v} {Y : Type w} [AddCommGroup X] [AddCommGroup Y]
    (Q : RootDatum ι X Y) (i : ι) (k : ℤ) (x : Space Y),
    wallReflection Q i k • x =
      x - (rootValue Q i x - (k : ℝ)) • latticeMap (Q.coroot i)

def PointStabilizers.{u,v,w} : Prop :=
  ∀ {ι : Type u} {X : Type v} {Y : Type w}
    [Finite ι] [AddCommGroup X] [AddCommGroup Y]
    [Module.Free ℤ X] [Module.Free ℤ Y] [Module.Finite ℤ X] [Module.Finite ℤ Y]
    (Q : RootDatum ι X Y) [Q.IsReduced] [Q.flip.IsReduced] (B : Q.Base),
    Submodule.span ℤ (Set.range Q.coroot) = ⊤ →
    ∀ {n : ℕ}, (n = 6 ∨ n = 7 ∨ n = 8) →
      ∀ e : B.support ≃ Fin n,
        PreservesCartan (RootData.integralCartan Q B) (CartanMatrix.E n) e →
        ∀ m : Fin n → ℤ, HighestRootAndVertices m →
          ∀ x : Space Y, MulAction.stabilizer (AffineWeylGroup Q) x =
            Subgroup.closure (wallGenerators Q x)

def CongruenceStabilizers.{u,v,w} : Prop :=
  ∀ {ι : Type u} {X : Type v} {Y : Type w}
    [Finite ι] [AddCommGroup X] [AddCommGroup Y]
    [Module.Free ℤ X] [Module.Free ℤ Y] [Module.Finite ℤ X] [Module.Finite ℤ Y]
    (Q : RootDatum ι X Y) [Q.IsReduced] [Q.flip.IsReduced] (B : Q.Base),
    Submodule.span ℤ (Set.range Q.coroot) = ⊤ →
    ∀ {n : ℕ}, (n = 6 ∨ n = 7 ∨ n = 8) →
      ∀ e : B.support ≃ Fin n,
        PreservesCartan (RootData.integralCartan Q B) (CartanMatrix.E n) e →
        ∀ m : Fin n → ℤ, HighestRootAndVertices m →
          ∀ (d : ℕ), 0 < d → ∀ (y : Y) (w : Q.weylGroup),
            (∃ a : Y, cocharacterAction Q w y - y = (d : ℤ) • a) ↔
              w ∈ Subgroup.closure (congruenceGenerators Q d y)

/-- The projection of the affine point stabilizer at a divided lattice point. -/
def CongruenceProjection.{u,v,w} : Prop :=
  ∀ {ι : Type u} {X : Type v} {Y : Type w}
    [Finite ι] [AddCommGroup X] [AddCommGroup Y]
    [Module.Free ℤ X] [Module.Free ℤ Y] [Module.Finite ℤ X] [Module.Finite ℤ Y]
    (Q : RootDatum ι X Y) [Q.IsReduced] [Q.flip.IsReduced] (B : Q.Base),
    Submodule.span ℤ (Set.range Q.coroot) = ⊤ →
    ∀ {n : ℕ}, (n = 6 ∨ n = 7 ∨ n = 8) →
      ∀ e : B.support ≃ Fin n,
        PreservesCartan (RootData.integralCartan Q B) (CartanMatrix.E n) e →
        ∀ m : Fin n → ℤ, HighestRootAndVertices m →
          ∀ (d : ℕ), 0 < d → ∀ y : Y,
            (MulAction.stabilizer (AffineWeylGroup Q) ((d : ℝ)⁻¹ • latticeMap y)).map
              SemidirectProduct.rightHom = Subgroup.closure (congruenceGenerators Q d y)

/-- The translation in any stabilizing lift is determined by the linear part. -/
def StabilizerTranslation.{u,v,w} : Prop :=
  ∀ {ι : Type u} {X : Type v} {Y : Type w} [AddCommGroup X] [AddCommGroup Y]
    (Q : RootDatum ι X Y) (x : Space Y) (g : AffineWeylGroup Q),
    g ∈ MulAction.stabilizer (AffineWeylGroup Q) x →
      latticeMap g.left.toAdd = x - realAction Q g.right x

end LinearAlgebraicGroups.Specs.ExceptionalAffineCorootStabilizers
