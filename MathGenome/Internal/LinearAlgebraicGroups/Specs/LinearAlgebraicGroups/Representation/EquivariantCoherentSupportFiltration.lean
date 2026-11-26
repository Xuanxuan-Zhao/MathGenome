import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.EquivariantCoherentClosedImage

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

universe u

namespace LinearAlgebraicGroups.Specs.EquivariantCoherentSupportFiltration

open EquivariantAffineModules EquivariantCoherentClosedImage

variable {k : Type u} [Field k] {T : GroupScheme k} {X Z : SchemeOver k}
  {a : ModObj T.X X} {b : ModObj T.X Z} {i : Z ⟶ X}

/-- A descending finite filtration, using the kernels of the adjunction units.
Each short exact sequence identifies the corresponding quotient with the closed
direct image of the actual inverse image of the term of the filtration. -/
def HasSupportFiltration (D : ClosedImageData i a b) (F : EquivariantCoherent a) : Prop :=
  ∃ (n : ℕ) (term : ℕ → EquivariantCoherent a),
    term 0 = F ∧ IsZero (term n).sheaf ∧
    (∀ m < n, ∃ (f : (term (m + 1)).sheaf ⟶ (term m).sheaf),
      let unit := (Scheme.Modules.pullbackPushforwardAdjunction i.left).unit.app (term m).sheaf
      ∃ w : f ≫ unit = 0,
        EquivariantHom (F := term (m + 1)) (H := term m) f ∧
        EquivariantHom (F := term m) (H := D.push (D.pull (term m))) unit ∧
        (ShortComplex.mk f unit w).ShortExact) ∧
    classOf F ∈ LinearMap.range D.pushClasses

/-- Closed-support dévissage for an invariant closed subscheme with its given
scheme structure and the actual inverse image to its open complement. -/
def SupportFiltration : Prop :=
  ∀ {k : Type u} [Field k] {T : GroupScheme k} {X Z Y : SchemeOver k}
    (a : ModObj T.X X) (b : ModObj T.X Z) (c : ModObj T.X Y)
    (i : Z ⟶ X) (j : Y ⟶ X),
    IsSplitTorus T →
    LocallyOfFiniteType X.hom → IsSeparated X.hom → CompactSpace X.left →
    (∀ x : X.left, ∃ U : X.left.Opens,
      x ∈ U ∧ IsAffineOpen U ∧ a.smul.left ⁻¹ᵁ U = (snd T.X X).left ⁻¹ᵁ U) →
    IsClosedImmersion i.left → IsOpenImmersion j.left →
    IsEquivariantMap a b i → IsEquivariantMap a c j →
    Set.range j.left = (Set.range i.left)ᶜ →
    ∃ D : ClosedImageData i a b,
      (∀ F, IsEquivariantPullback i F (D.pull F) (Iso.refl _)) ∧
      (∀ H, IsEquivariantPushforward i H (D.push H) (Iso.refl _)) ∧
      (∀ H, D.pushClasses (classOf H) = classOf (D.push H)) ∧
      ∀ F : EquivariantCoherent a, IsZero (Pull j F.sheaf) → HasSupportFiltration D F

end LinearAlgebraicGroups.Specs.EquivariantCoherentSupportFiltration
