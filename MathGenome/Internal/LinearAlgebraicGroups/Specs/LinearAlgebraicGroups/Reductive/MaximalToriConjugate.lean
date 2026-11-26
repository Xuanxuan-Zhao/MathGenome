import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.Stabilizers

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonoidalCategory

universe u

namespace LinearAlgebraicGroups.Specs.MaximalToriConjugate

open GeometricBorelConjugacy (IsBorel ConjugatesSubgroups subgroupOfSubgroup)
open GeometricRadicals (IsMaximalTorus)
open SchemeDerivedGroup (IsSubgroupOf)

/-- Maximal tori are conjugate as closed subgroup schemes over an algebraically closed field. -/
def ToriConjugate : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    ∀ T₁ T₂ : ClosedSubgroup G.val, IsMaximalTorus T₁ → IsMaximalTorus T₂ →
      ∃ g : 𝟙_ (SchemeOver k) ⟶ G.val.X, ConjugatesSubgroups g T₁ T₂

/-- A single rational point conjugates both the Borel and the torus of a Borel pair. -/
def BorelPairsConjugate : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    ∀ (B₁ B₂ : ClosedSubgroup G.val), IsBorel B₁ → IsBorel B₂ →
    ∀ (T₁ : ClosedSubgroup B₁.group) (T₂ : ClosedSubgroup B₂.group),
      IsMaximalTorus T₁ → IsMaximalTorus T₂ →
      ∃ g : 𝟙_ (SchemeOver k) ⟶ G.val.X,
        ConjugatesSubgroups g B₁ B₂ ∧
        ConjugatesSubgroups g (subgroupOfSubgroup B₁ T₁) (subgroupOfSubgroup B₂ T₂)

/-- A torus in a Borel is maximal there exactly when it is maximal in the ambient group. -/
def BorelMaximalTorusIff : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    ∀ (B : ClosedSubgroup G.val), IsBorel B → ∀ T : ClosedSubgroup B.group,
      IsMaximalTorus T ↔ IsMaximalTorus (subgroupOfSubgroup B T)

/-- The rational points of the scheme normalizer of a maximal torus act transitively
on the Borels containing that torus. -/
def NormalizerTransitiveOnBorels : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    ∀ (T : ClosedSubgroup G.val), IsMaximalTorus T →
    ∀ B₁ B₂ : ClosedSubgroup G.val, IsBorel B₁ → IsBorel B₂ →
      IsSubgroupOf T B₁ → IsSubgroupOf T B₂ →
      ∃ g : 𝟙_ (SchemeOver k) ⟶ G.val.X,
        Normalizes T.inclusion g ∧ ConjugatesSubgroups g B₁ B₂

end LinearAlgebraicGroups.Specs.MaximalToriConjugate
