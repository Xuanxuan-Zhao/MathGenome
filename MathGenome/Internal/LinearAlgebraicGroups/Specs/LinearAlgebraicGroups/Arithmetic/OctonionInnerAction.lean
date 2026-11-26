import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Composition.OctonionAutomorphisms
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.RelativeFormComparison

open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs

open _root_.LinearAlgebraicGroups.Composition (Zorn)
open Composition.Specification (normBaseChange)
open Composition.OctonionAutomorphismSpecification (AutomorphismGroup)
open Descent (SemilinearAction)
open AutomorphismSequence (innerAut relativePoints)
open RelativeFormComparison (fieldMap fieldTest transportedAut)

/-- The uniquely lifted inner displacement acts on the split octonions by
applying the field automorphism to coefficients and then the lifted point. -/
def OctonionInnerAction : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    (A₀ : AutomorphismGroup k (Zorn k)) (H : AffineGroupScheme k)
    (i : relativePoints A₀.group (fieldTest k K) ≅ relativePoints H.val (fieldTest k K))
    (c : Gal(K/k) → (fieldTest k K ⟶ A₀.group.X)),
    (∀ σ, innerAut (c σ) = transportedAut k K i σ ∧
      ∀ g, innerAut g = transportedAut k K i σ → g = c σ) →
    c 1 = 1 ∧
    (∀ σ τ, c (σ * τ) = c σ * (fieldMap k K σ ≫ c τ)) ∧
    ∃ ρ : SemilinearAction k K (K ⊗[k] Zorn k),
      (∀ σ x, ρ.act σ x =
        (A₀.subgroupPoints (CommAlgCat.of k K) (c σ)).val.val
          ((SemilinearAction.scalarExtension (K := K) (Zorn k)).act σ x)) ∧
      (∀ σ, ρ.act σ 1 = 1) ∧
      (∀ σ x y, ρ.act σ (x * y) = ρ.act σ x * ρ.act σ y) ∧
      (∀ σ x, normBaseChange K (Composition.ZornSpecification.norm k) (ρ.act σ x) =
        σ (normBaseChange K (Composition.ZornSpecification.norm k) x))

end LinearAlgebraicGroups.Specs
