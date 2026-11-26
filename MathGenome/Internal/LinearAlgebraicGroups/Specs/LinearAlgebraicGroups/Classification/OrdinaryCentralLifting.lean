import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.RankTwoLifting

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.OrdinaryCentralLifting

open AbstractPairing (Root)
open CellHomomorphism (pullbackCharacters)
open CharacterDescent (Character)
open CharacterPairing (pairing)
open Pinning (AttachedDatum PinnedGroup)
open RankTwoLifting (HasCentralTorusKernel MatchesPinning MatchesRootGroups)
open RootGroups (AdditiveLine)

/-- An ordinary lattice isogeny of based data lifts over the ground field.
The character homomorphism is contravariant and its dual carries every
coroot to its counterpart, as expressed by the two perfect pairings.
The lift is an isomorphism on each root group and is a group isomorphism
when the character homomorphism is surjective. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} (P Q : PinnedGroup A)
    (D : AttachedDatum P.pair) (E : AttachedDatum Q.pair),
    letI := D.comm
    letI := E.comm
    ∀ (d : Root P.pair.T ≃ Root Q.pair.T)
      (h : Character Q.pair.T.group →* Character P.pair.T.group),
      Function.Injective h →
      Finite (Character P.pair.T.group ⧸ h.range) →
      (∀ α, h (d α).val = α.val) →
      (∀ α (χ : Character Q.pair.T.group),
        pairing P.pair.T.group (h χ) (Additive.toMul (D.datum.rootDatum.coroot α)) =
          pairing Q.pair.T.group χ (Additive.toMul (E.datum.rootDatum.coroot (d α)))) →
      (∀ α, α ∈ D.base.support ↔ d α ∈ E.base.support) →
      ∃ (τ : P.pair.T.group ⟶ Q.pair.T.group) (f : P.pair.G.val ⟶ Q.pair.G.val),
        pullbackCharacters τ = h ∧
        MatchesPinning d τ f ∧
        IsFinite f.hom.hom.left ∧ Flat f.hom.hom.left ∧ Surjective f.hom.hom.left ∧
        HasCentralTorusKernel τ f ∧
        (Function.Surjective h → IsIso f) ∧
        MatchesRootGroups d f

end LinearAlgebraicGroups.Specs.OrdinaryCentralLifting
