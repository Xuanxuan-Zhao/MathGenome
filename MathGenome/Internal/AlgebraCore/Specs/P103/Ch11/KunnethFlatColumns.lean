import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.UniversalCoefficientsHomology

/-!
The flat-column calculation in paper.tex 3080–3088. The tensor and quotient
homology are the shared noncommutative models. No condition is imposed on the
terms, boundaries or homology of the left-module complex.
-/
namespace P103.Specs.Ch11.KunnethFlatColumns
open CategoryTheory
open scoped DirectSum
open P103.BalancedTensor
open P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch11.TorBalance
open P103.Specs.Ch11.UniversalCoefficientsHomology
open P103.Specs.Ch02.FlatnessTests
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
variable {R : Type u} [Ring R]

/-- The evident cycle in the ordinary tensor column. -/
def columnCycle (U : ModuleCat.{v} Rᵐᵒᵖ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (q : ℕ) (a : U) (x : cycles D q) :
    cycles (leftOrdinaryTensorComplex U D) q :=
  ⟨tmul R a x.val, by
    change tmul R a ((D.d q ((ComplexShape.down ℕ).next q)).hom x.val) = 0
    rw [show (D.d q ((ComplexShape.down ℕ).next q)).hom x.val = 0 from x.property]
    simp [tmul]⟩

/-- The representative formula fixes the isomorphism uniquely. -/
def ColumnFormula (U : ModuleCat.{v} Rᵐᵒᵖ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (q : ℕ)
    (e : Tensor R U (Homology D q) ≃ₗ[ℤ]
      Homology (leftOrdinaryTensorComplex U D) q) : Prop :=
  ∀ (a : U) (x : cycles D q),
    e (tmul R a (homologyClass D q x)) =
      homologyClass _ q (columnCycle U D q a x)

def column_isomorphismType : Prop :=
  ∀ (R : Type u) [Ring R] (U : ModuleCat.{v} Rᵐᵒᵖ),
    RightFlat.{u,v,w} R U → ∀ (D : ChainComplex (ModuleCat.{w} R) ℕ) (q : ℕ),
    ∃ e : Tensor R U (Homology D q) ≃ₗ[ℤ]
      Homology (leftOrdinaryTensorComplex U D) q, ColumnFormula U D q e

/-- Simultaneous naturality, for any isomorphisms with the stated formula. -/
def column_naturalType : Prop :=
  ∀ (R : Type u) [Ring R] (U U' : ModuleCat.{v} Rᵐᵒᵖ)
    (D D' : ChainComplex (ModuleCat.{w} R) ℕ) (f : U ⟶ U') (g : D ⟶ D') (q : ℕ)
    (e : Tensor R U (Homology D q) ≃ₗ[ℤ] Homology (leftOrdinaryTensorComplex U D) q)
    (e' : Tensor R U' (Homology D' q) ≃ₗ[ℤ] Homology (leftOrdinaryTensorComplex U' D') q),
    ColumnFormula U D q e → ColumnFormula U' D' q e' →
    (homologyMap (leftTensorMap f.hom g) q).comp e.toLinearMap =
      e'.toLinearMap.comp (tensorMap f.hom (homologyMap g q))

/-- Multiplication of a column differential by its Koszul sign preserves
both the kernel and the image, over integer modules of arbitrary size. -/
def sign_submodulesType : Prop :=
  ∀ (A B : ModuleCat.{v} ℤ) (d : A →ₗ[ℤ] B) (p : ℕ),
    LinearMap.ker ((p : ℤ).negOnePow • d) = LinearMap.ker d ∧
    LinearMap.range ((p : ℤ).negOnePow • d) = LinearMap.range d

/-- The finite nonnegative diagonal; at n = 0 it has its single (0,0) term. -/
abbrev Diagonal (n : ℕ) := {i : ℕ × ℕ // i.1 + i.2 = n}

abbrev DiagonalTensor (X : ℕ → ModuleCat.{v} Rᵐᵒᵖ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (n : ℕ) :=
  ⨁ i : Diagonal n, Tensor R (X i.val.1) (Homology D i.val.2)

/-- Any degreewise linear family map is a chain map between the actual
zero-differential complexes. -/
def familyMap {X X' : ℕ → ModuleCat.{v} Rᵐᵒᵖ} (f : ∀ p, X p ⟶ X' p) :
    zeroDifferentialComplex X ⟶ zeroDifferentialComplex X' where
  f := f
  comm' _ _ _ := by simp

/-- The diagonal map induced in the two variables. -/
def diagonalMap {X X' : ℕ → ModuleCat.{v} Rᵐᵒᵖ}
    {D D' : ChainComplex (ModuleCat.{w} R) ℕ}
    (f : ∀ p, X p ⟶ X' p) (g : D ⟶ D') (n : ℕ) :
    DiagonalTensor X D n →ₗ[ℤ] DiagonalTensor X' D' n :=
  DirectSum.toModule ℤ _ _ (fun i =>
    (DirectSum.lof ℤ _ _ i).comp (tensorMap (f i.val.1).hom (homologyMap g i.val.2)))

/-- The image of each pure tensor class is the class of its actual total
inclusion. Existence of the cycle is included, not assumed. -/
def DiagonalFormula (X : ℕ → ModuleCat.{v} Rᵐᵒᵖ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (n : ℕ)
    (e : DiagonalTensor X D n ≃ₗ[ℤ]
      Homology (ordinaryTotal (zeroDifferentialComplex X) D) n) : Prop :=
  ∀ (p q : ℕ) (h : p + q = n) (a : X p) (x : cycles D q),
    ∃ z : cycles (ordinaryTotal (zeroDifferentialComplex X) D) n,
      z.val = ordinaryInclusion (zeroDifferentialComplex X) D p q n h (tmul R a x.val) ∧
      e (DirectSum.lof ℤ _ _ ⟨(p,q),h⟩ (tmul R a (homologyClass D q x))) =
        homologyClass _ n z

def diagonal_isomorphismType : Prop :=
  ∀ (R : Type u) [Ring R] (X : ℕ → ModuleCat.{v} Rᵐᵒᵖ),
    (∀ p, RightFlat.{u,v,w} R (X p)) →
    ∀ (D : ChainComplex (ModuleCat.{w} R) ℕ) (n : ℕ),
    ∃ e : DiagonalTensor X D n ≃ₗ[ℤ]
      Homology (ordinaryTotal (zeroDifferentialComplex X) D) n, DiagonalFormula X D n e

def diagonal_naturalType : Prop :=
  ∀ (R : Type u) [Ring R] (X X' : ℕ → ModuleCat.{v} Rᵐᵒᵖ)
    (D D' : ChainComplex (ModuleCat.{w} R) ℕ) (f : ∀ p, X p ⟶ X' p) (g : D ⟶ D') (n : ℕ)
    (e : DiagonalTensor X D n ≃ₗ[ℤ]
      Homology (ordinaryTotal (zeroDifferentialComplex X) D) n)
    (e' : DiagonalTensor X' D' n ≃ₗ[ℤ]
      Homology (ordinaryTotal (zeroDifferentialComplex X') D') n),
    DiagonalFormula X D n e → DiagonalFormula X' D' n e' →
    ∀ t : DiagonalTensor X D n,
      homologyMap (R := ℤ) (ordinaryTotalMap (familyMap f) g) n (e t) =
        e' (diagonalMap f g n t)

end
end P103.Specs.Ch11.KunnethFlatColumns
