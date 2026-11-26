import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.TorsorObstruction
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.SmoothTorsors
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.Lang

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.ExactLifting

open Fppf TorsorObstruction SmoothTorsors
open LinearAlgebraicGroups.Descent LinearAlgebraicGroups.Descent.NonabelianCohomology

noncomputable section

variable {k S : Type u} [Field k] [Field S] [Algebra k S]

/-- The class of a cocycle in the continuous Galois cohomology of a group scheme. -/
abbrev galoisClass [IsSepClosure k S] {G : GroupScheme k} (a : GaloisCocycle (S := S) G) :
    groupH1 k G.X S :=
  @classOf (S ≃ₐ[k] S) (NonabelianCohomology.Points k S G.X) _
    (krullTopology k S) _ ⊥ (pointAction k S G.X) a

/-- Postcomposition on cocycles with a morphism of coefficient group schemes. -/
def mapCocycle {H G : GroupScheme k} (i : H ⟶ G) (a : GaloisCocycle (S := S) H) :
    GaloisCocycle (S := S) G := by
  letI : TopologicalSpace (NonabelianCohomology.Points k S H.X) := ⊥
  letI : TopologicalSpace (NonabelianCohomology.Points k S G.X) := ⊥
  letI : DiscreteTopology (NonabelianCohomology.Points k S H.X) := ⟨rfl⟩
  letI : TopologicalSpace (S ≃ₐ[k] S) := krullTopology k S
  let f : NonabelianCohomology.Points k S H.X → NonabelianCohomology.Points k S G.X :=
    fun z ↦ z ≫ i.hom.hom
  refine ⟨fun σ ↦ f (a σ), (continuous_of_discreteTopology : Continuous f).comp a.property.1, ?_⟩
  intro σ τ
  change a (σ * τ) ≫ i.hom.hom =
    (a σ ≫ i.hom.hom) * pointAction k S G.X σ (a τ ≫ i.hom.hom)
  rw [a.property.2 σ τ, MonObj.mul_comp]
  congr 1

/-- Pointed exactness, the fibre-torsor interpretation of the boundary, and
the rational orbit criterion for a smooth homogeneous quotient. -/
def GaloisExactness : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (G : AffineAlgebraicGroup k) (H : ClosedSubgroup G.val),
    Smooth G.val.X.hom → Smooth H.group.X.hom →
    ∃ (δ : RationalPoints H → groupH1 k H.group.X S)
      (e : groupH1 k H.group.X S → groupH1 k G.val.X S)
      (c : H1fppf k H.group ≃ groupH1 k H.group.X S),
      (∀ a, e (galoisClass a) = galoisClass (mapCocycle H.inclusion a)) ∧
      (∀ x, ∃ t, IsFibreClass H x t ∧ δ x = c t) ∧
      (∀ (P : FppfTorsor (fieldBase k) H.group)
        (p : P.val.Section (fieldExtensionTest k S)) (a : GaloisCocycle (S := S) H.group),
        IsCocycleOf P p a → c (Quotient.mk _ P) = galoisClass a) ∧
      δ (projectSection H 1) = groupBasepoint k H.group.X S ∧
      e (groupBasepoint k H.group.X S) = groupBasepoint k G.val.X S ∧
      Set.range (fun g : fieldBase k ⟶ G.val.X ↦ projectSection H g) =
        {x | δ x = groupBasepoint k H.group.X S} ∧
      Set.range δ = {a | e a = groupBasepoint k G.val.X S} ∧
      (∀ x y, δ x = δ y ↔ ∃ g : fieldBase k ⟶ G.val.X, actOnSection H g x = y) ∧
      ∀ x : RationalPoints H, Nonempty (FibreSection H x (fieldExtensionTest k S)) ∧
        ∀ p : FibreSection H x (fieldExtensionTest k S),
          ∃ a : GaloisCocycle (S := S) H.group, δ x = galoisClass a ∧
            ∀ σ, let g : NonabelianCohomology.Points k S G.val.X := p.val.down
              a σ ≫ H.inclusion.hom.hom = g⁻¹ * pointAction k S G.val.X σ g

/-- Every rational quotient point lifts over a finite field for a connected
smooth subgroup. -/
def FiniteFieldLifting : Prop :=
  ∀ {k : Type u} [Field k] [Fintype k]
    (G : AffineAlgebraicGroup k) (H : ClosedSubgroup G.val),
    Smooth G.val.X.hom → Smooth H.group.X.hom → ConnectedSpace H.group.X.left →
    Function.Surjective (fun g : fieldBase k ⟶ G.val.X ↦ projectSection H g)

/-- Restriction of global units along a map of test schemes. -/
abbrev restrictUnit {T U : SchemeOver k} (f : U ⟶ T) :
    (testFunctions T)ˣ →* (testFunctions U)ˣ :=
  Units.map ((algΓ (CommRingCat.of k)).map f).unop.hom.toMonoidHom

/-- The quotient of the multiplicative group by the smooth, disconnected
subgroup of square roots of unity is represented by the squaring map. Over a
finite field of odd order every nonsquare gives a rational point without a lift. -/
def NonsquareCounterexample : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k], Odd (Fintype.card k) →
    ∃ (G : AffineAlgebraicGroup k) (H : ClosedSubgroup G.val)
      (coord : ∀ T : SchemeOver k, (T ⟶ G.val.X) ≃* (testFunctions T)ˣ)
      (ground : testFunctions (fieldBase k) ≃ₐ[k] k)
      (q : G.val.X ⟶ G.val.X)
      (e : rightQuotientSheaf H ≅ schemeFppfSheaf G.val.X),
      Smooth G.val.X.hom ∧ Smooth H.group.X.hom ∧ ¬ ConnectedSpace H.group.X.left ∧
      (∀ {U T : SchemeOver k} (f : U ⟶ T) (g : T ⟶ G.val.X),
        coord U (f ≫ g) = restrictUnit f (coord T g)) ∧
      (∀ (T : SchemeOver k) (g : T ⟶ G.val.X),
        (∃ h : T ⟶ H.group.X, h ≫ H.inclusion.hom.hom = g) ↔ (coord T g) ^ 2 = 1) ∧
      (∀ (T : SchemeOver k) (g : T ⟶ G.val.X), coord T (g ≫ q) = (coord T g) ^ 2) ∧
      (∀ (T : SchemeOver k) (g : T ⟶ G.val.X),
        e.hom.hom.app (op T) (projectSection H g) = ULift.up (g ≫ q)) ∧
      (∃ a : kˣ, ¬IsSquare (a : k)) ∧
      ∀ (a : kˣ), ¬IsSquare (a : k) →
        ∃ x : RationalPoints H,
          Units.map ground.toMonoidHom
            (coord (fieldBase k) (e.hom.hom.app _ x).down) = a ∧
          ∀ g : fieldBase k ⟶ G.val.X, projectSection H g ≠ x

end

end LinearAlgebraicGroups.Specs.ExactLifting
