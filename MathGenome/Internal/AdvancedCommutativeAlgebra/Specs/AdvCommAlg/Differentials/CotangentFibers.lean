import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.BaseChange
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Localization
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! KD-24, paper.tex:458–470. The condition q.LiesOver p says exactly that
p is the inverse image of q. In particular p can always be taken to be
q.comap (algebraMap A B). No finiteness hypotheses are imposed. -/
namespace Specs.AdvCommAlg.Differentials.CotangentFibers

open TensorProduct
universe u v
noncomputable section
attribute [local instance] Localization.AtPrime.algebraOfLiesOver
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The point of the fibre induced by the maps κ(p) → κ(q) and B → κ(q).
The residue-field action is the one induced by the local ring map A_p → B_q. -/
def fiberPointType :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) (q : Ideal B) [p.IsPrime] [q.IsPrime] [q.LiesOver p],
    (p.ResidueField ⊗[A] B) →ₐ[p.ResidueField] q.ResidueField

def fiberPointValue : fiberPointType.{u,v} :=
  fun A B _ _ _ p q _ _ _ =>
    (AlgHom.liftEquiv A p.ResidueField B q.ResidueField)
      (IsScalarTower.toAlgHom A B q.ResidueField)

/-- Values on all pure tensors specify the induced point, including both
structural maps and its compatibility with A. -/
def fiberPointFormula : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) (q : Ideal B) [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    (a : p.ResidueField) (b : B),
    fiberPointValue A B p q (a ⊗ₜ[A] b) = a • algebraMap B q.ResidueField b

/-- The two cotangent comparisons and the map from the localized cotangent
space to the fibre cotangent space. The last equality is the commuting triangle
on every element; all three maps are specified on extended differential
generators. Thus the local replacement uses Ω[B_q/A_p], with the original
residue-field actions, rather than changing the base to κ(p) on the left. -/
def cotangentComparison : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) (q : Ideal B) [p.IsPrime] [q.IsPrime] [q.LiesOver p],
    letI : Algebra (p.ResidueField ⊗[A] B) q.ResidueField :=
      (fiberPointValue A B p q).toRingHom.toAlgebra
    ∃ (e : q.ResidueField ⊗[B] KaehlerDifferential A B ≃ₗ[q.ResidueField]
          q.ResidueField ⊗[p.ResidueField ⊗[A] B]
            KaehlerDifferential p.ResidueField (p.ResidueField ⊗[A] B))
      (l : q.ResidueField ⊗[B] KaehlerDifferential A B ≃ₗ[q.ResidueField]
          q.ResidueField ⊗[Localization.AtPrime q]
            KaehlerDifferential (Localization.AtPrime p) (Localization.AtPrime q))
      (f : q.ResidueField ⊗[Localization.AtPrime q]
            KaehlerDifferential (Localization.AtPrime p) (Localization.AtPrime q)
          ≃ₗ[q.ResidueField] q.ResidueField ⊗[p.ResidueField ⊗[A] B]
            KaehlerDifferential p.ResidueField (p.ResidueField ⊗[A] B)),
      (∀ (k : q.ResidueField) (b : B),
        e (k ⊗ₜ[B] KaehlerDifferential.D A B b) =
          k ⊗ₜ KaehlerDifferential.D p.ResidueField (p.ResidueField ⊗[A] B)
            (1 ⊗ₜ[A] b)) ∧
      (∀ (k : q.ResidueField) (b : B),
        l (k ⊗ₜ[B] KaehlerDifferential.D A B b) =
          k ⊗ₜ KaehlerDifferential.D (Localization.AtPrime p) (Localization.AtPrime q)
            (algebraMap B (Localization.AtPrime q) b)) ∧
      (∀ (k : q.ResidueField) (b : B),
        f (k ⊗ₜ KaehlerDifferential.D (Localization.AtPrime p) (Localization.AtPrime q)
            (algebraMap B (Localization.AtPrime q) b)) =
          k ⊗ₜ KaehlerDifferential.D p.ResidueField (p.ResidueField ⊗[A] B)
            (1 ⊗ₜ[A] b)) ∧
      ∀ x, f (l x) = e x

end
end Specs.AdvCommAlg.Differentials.CotangentFibers
