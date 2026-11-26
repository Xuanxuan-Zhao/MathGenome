import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace LinearAlgebraicGroups.Specs.InnerProductFactors

open AutomorphismSequence
open RelativeFormComparison (fieldTest transportedAut)
open QuasiSplitInnerForms (AreInnerForms)
open GeometricRadicals (IsReductive IsSplitReductive)

variable {F : Type u} [Field F]

/-- The selected comparison over the separable closure has inner displacement. -/
def IsInnerComparison {Q H : AffineAlgebraicGroup F}
    (i : relativePoints Q.val (fieldTest F (SeparableClosure F)) ≅
      relativePoints H.val (fieldTest F (SeparableClosure F))) : Prop :=
  ∃ (V : AdjointQuotient Q) (inn : groupSections V.quotient.val ⟶ automorphisms Q.val),
    (∀ (U : SchemeOver F) (g : U ⟶ Q.val.X),
      inn.app (op U) ⟨g ≫ V.projection.hom.hom⟩ = innerAut g) ∧
    (∀ U, Function.Injective (inn.app U)) ∧
    ∀ σ, transportedAut F (SeparableClosure F) i σ ∈
      (inn.app (op (fieldTest F (SeparableClosure F)))).hom.range

/-- Scalar-extended product comparisons commute with the two projections. -/
def IsProductComparison {Q Q₁ Q₂ H H₁ H₂ : AffineAlgebraicGroup F}
    (b : Q.val ≅ prod Q₁.val Q₂.val) (e : H.val ≅ prod H₁.val H₂.val)
    (i : relativePoints Q.val (fieldTest F (SeparableClosure F)) ≅
      relativePoints H.val (fieldTest F (SeparableClosure F)))
    (i₁ : relativePoints Q₁.val (fieldTest F (SeparableClosure F)) ≅
      relativePoints H₁.val (fieldTest F (SeparableClosure F)))
    (i₂ : relativePoints Q₂.val (fieldTest F (SeparableClosure F)) ≅
      relativePoints H₂.val (fieldTest F (SeparableClosure F))) : Prop :=
  let Y := yonedaGrp ⋙ (Functor.whiskeringLeft _ _ _).obj
    (Over.forget (fieldTest F (SeparableClosure F))).op
  (Y.map (b.hom ≫ prod.fst)) ≫ i₁.hom = i.hom ≫ Y.map (e.hom ≫ prod.fst) ∧
  (Y.map (b.hom ≫ prod.snd)) ≫ i₂.hom = i.hom ≫ Y.map (e.hom ≫ prod.snd)

/-- Inner descent of a split product preserves its ordered factors. -/
def Statement : Prop :=
  ∀ {F : Type u} [Field F] (Q₁ Q₂ Q H : AffineAlgebraicGroup F),
    IsSplitReductive Q₁ → IsSplitReductive Q₂ → IsReductive H →
    ∀ b : Q.val ≅ prod Q₁.val Q₂.val,
    AreInnerForms (S := SeparableClosure F) Q H →
    ∃ (H₁ H₂ : AffineAlgebraicGroup F) (e : H.val ≅ prod H₁.val H₂.val),
      IsReductive H₁ ∧ IsReductive H₂ ∧
      ∃ (i : relativePoints Q.val (fieldTest F (SeparableClosure F)) ≅
          relativePoints H.val (fieldTest F (SeparableClosure F)))
        (i₁ : relativePoints Q₁.val (fieldTest F (SeparableClosure F)) ≅
          relativePoints H₁.val (fieldTest F (SeparableClosure F)))
        (i₂ : relativePoints Q₂.val (fieldTest F (SeparableClosure F)) ≅
          relativePoints H₂.val (fieldTest F (SeparableClosure F))),
        IsInnerComparison i ∧ IsInnerComparison i₁ ∧ IsInnerComparison i₂ ∧
        IsProductComparison b e i i₁ i₂

end LinearAlgebraicGroups.Specs.InnerProductFactors
