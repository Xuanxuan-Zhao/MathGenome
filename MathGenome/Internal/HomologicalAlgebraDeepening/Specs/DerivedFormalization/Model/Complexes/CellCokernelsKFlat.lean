import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Complexes.CellFactorization
import MathGenome.AlgebraCore.Topics.P103.Ch11

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v

namespace DerivedFormalization.Specs.ComplexCellCokernelsKFlat

open Model.Complexes ComplexCellFactorization

/-- Negating the degree converts cochain grading to chain grading. -/
def downToUp : (ComplexShape.down ℤ).Embedding (ComplexShape.up ℤ) :=
  ComplexShape.Embedding.mk' _ _ Neg.neg (by intro i j h; omega)
    (by intro i j; change j + 1 = i ↔ -i + 1 = -j; omega)

/-- Negating the degree converts chain grading to cochain grading. -/
def upToDown : (ComplexShape.up ℤ).Embedding (ComplexShape.down ℤ) :=
  ComplexShape.Embedding.mk' _ _ Neg.neg (by intro i j h; omega)
    (by intro i j; change i + 1 = j ↔ -j + 1 = -i; omega)

instance : downToUp.IsRelIff where
  rel' i j h := by
    change -i + 1 = -j at h
    change j + 1 = i
    omega

instance : upToDown.IsRelIff where
  rel' i j h := by
    change -j + 1 = -i at h
    change i + 1 = j
    omega

abbrev RightCochains (A : Type u) [Ring A] := CochainComplex (ModuleCat.{v} Aᵐᵒᵖ) ℤ
abbrev TensorCochains := CochainComplex (ModuleCat.{u} ℤ) ℤ

-- The two universes are independent in the function domain.
set_option linter.checkUnivs false in
def tensorTotalType :=
  ∀ (A : Type u) [Ring A], RightCochains.{u,v} A → Cochains A → TensorCochains.{max u v}

/-- The direct-sum balanced total uses the chain construction with all indices negated. -/
noncomputable def tensorTotalValue : tensorTotalType.{u,v} :=
  fun _ _ E P ↦ (P103.Specs.Ch11.TorBalance.tensorTotal
    (E.restriction downToUp) (P.restriction downToUp)).restriction upToDown

/-- The inclusion of a homogeneous balanced tensor into the direct-sum total. -/
noncomputable def tensorInclusionValue (A : Type u) [Ring A]
    (E : RightCochains.{u,v} A) (P : Cochains A) (p q k : ℤ) (h : p + q = k)
    (x : E.X p) (y : P.X q) : (tensorTotalValue A E P).X k :=
  P103.Specs.Ch11.TorBalance.tensorInclusion (E.restriction downToUp)
    (P.restriction downToUp) (-p) (-q) (-k) (by omega)
    (P103.BalancedTensor.tmul A
      ((E.restrictionXIso downToUp (Int.neg_neg p)).inv.hom x)
      ((P.restrictionXIso downToUp (Int.neg_neg q)).inv.hom y))

def tensorTotalDifferentialType : Prop :=
  ∀ (A : Type u) [Ring A] (E : RightCochains.{u,v} A) (P : Cochains A)
    (p q k : ℤ) (h : p + q = k) (x : E.X p) (y : P.X q),
    ((tensorTotalValue A E P).d k (k + 1)).hom (tensorInclusionValue A E P p q k h x y) =
      tensorInclusionValue A E P (p + 1) q (k + 1) (by omega) ((E.d p (p + 1)).hom x) y +
      p.negOnePow •
        tensorInclusionValue A E P p (q + 1) (k + 1) (by omega) x ((P.d q (q + 1)).hom y)

def isKFlatType := ∀ (A : Type u) [Ring A], Cochains A → Prop

/-- The tests use every acyclic right module complex over the same ring. -/
def isKFlatValue : isKFlatType.{u} :=
  fun A _ P ↦ ∀ (E : RightCochains.{u,v} A), E.Acyclic → (tensorTotalValue A E P).Acyclic

def iCellCokernelKFlatType : Prop :=
  ∀ (A : Type u) [Ring A] {X Y : Cochains A} (f : X ⟶ Y),
    iCellValue A f → isKFlatValue.{u,v} A (cokernel f)

def retractKFlatType : Prop :=
  ∀ (A : Type u) [Ring A] {P Q : Cochains A}, Retract P Q →
    isKFlatValue.{u,v} A Q → isKFlatValue.{u,v} A P

end DerivedFormalization.Specs.ComplexCellCokernelsKFlat
