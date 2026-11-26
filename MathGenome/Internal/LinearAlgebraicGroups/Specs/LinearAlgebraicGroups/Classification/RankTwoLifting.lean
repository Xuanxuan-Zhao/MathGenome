import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.CellHomomorphism
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.Pinning

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.RankTwoLifting

open AbstractPairing (Root)
open BorelsAndChambers (subgroupRoots)
open CellHomomorphism (pullbackCharacters)
open CharacterDescent (Character)
open CharacterPairing (pairing)
open Pinning (AttachedDatum PinnedGroup SimpleRoot)
open RootGroups (AdditiveLine)

variable {k : Type u} [Field k] {A : AdditiveLine k}

/-- Compatibility of the prescribed torus map with the based roots and coroots. -/
structure Compatible (P Q : PinnedGroup A) (D : AttachedDatum P.pair)
    (E : AttachedDatum Q.pair) (d : Root P.pair.T ≃ Root Q.pair.T)
    (τ : P.pair.T.group ⟶ Q.pair.T.group) : Prop where
  injective : Function.Injective (pullbackCharacters τ)
  finiteIndex : Finite (Character P.pair.T.group ⧸ (pullbackCharacters τ).range)
  root : ∀ α, τ ≫ (d α).val = α.val
  coroot : letI := D.comm; letI := E.comm; ∀ α, Additive.toMul (D.datum.rootDatum.coroot α) ≫ τ =
    Additive.toMul (E.datum.rootDatum.coroot (d α))
  simple : letI := D.comm; letI := E.comm; ∀ α, α ∈ D.base.support ↔ d α ∈ E.base.support

/-- The lift realizes the specified torus morphism and sends each pinned
simple root parametrization to the corresponding pinned parametrization. -/
def MatchesPinning {P Q : PinnedGroup A} (d : Root P.pair.T ≃ Root Q.pair.T)
    (τ : P.pair.T.group ⟶ Q.pair.T.group) (f : P.pair.G.val ⟶ Q.pair.G.val) : Prop :=
  P.pair.T.inclusion ≫ f = τ ≫ Q.pair.T.inclusion ∧
    ∀ (α : SimpleRoot P.pair) (β : SimpleRoot Q.pair), d α.val = β.val →
      ((P.pin α).val.hom ≫ (P.roots α.val).val.inclusion) ≫ f =
        (Q.pin β).val.hom ≫ (Q.roots β.val).val.inclusion

/-- The finite, possibly nonsmooth, kernel of the torus map is the full
scheme kernel of the lift, and centralizes the source group. -/
def HasCentralTorusKernel {P Q : PinnedGroup A}
    (τ : P.pair.T.group ⟶ Q.pair.T.group) (f : P.pair.G.val ⟶ Q.pair.G.val) : Prop :=
  ∃ N : ClosedSubgroup P.pair.T.group,
    IsFinite N.group.X.hom ∧ IsSchemeKernel τ N ∧
    ∃ hi : IsClosedImmersion (N.inclusion ≫ P.pair.T.inclusion).hom.hom.left,
      let NG : ClosedSubgroup P.pair.G.val := ⟨N.group, N.inclusion ≫ P.pair.T.inclusion, hi⟩
      IsSchemeKernel f NG ∧ Centralizes (𝟙 P.pair.G.val) NG.inclusion.hom.hom

/-- The lift restricts to an isomorphism on each pair of corresponding root
subgroups, with its given ambient inclusions. -/
def MatchesRootGroups {P Q : PinnedGroup A} (d : Root P.pair.T ≃ Root Q.pair.T)
    (f : P.pair.G.val ⟶ Q.pair.G.val) : Prop :=
  ∀ α, ∃ e : (P.roots α).val.group ≅ (Q.roots (d α)).val.group,
    (P.roots α).val.inclusion ≫ f = e.hom ≫ (Q.roots (d α)).val.inclusion

/-- Ordinary central lifting for split pinned groups of semisimple rank at
most two over an arbitrary field. The bases present the positive systems of
the specified Borels, and the character lattice includes all central directions. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} (P Q : PinnedGroup A)
    (D : AttachedDatum P.pair) (E : AttachedDatum Q.pair),
    letI := D.comm
    letI := E.comm
    (∀ α, D.base.IsPos α ↔ α ∈ subgroupRoots P.pair.T P.pair.B) →
    (∀ β, E.base.IsPos β ↔ β ∈ subgroupRoots Q.pair.T Q.pair.B) →
    D.base.support.card ≤ 2 →
    ∀ (d : Root P.pair.T ≃ Root Q.pair.T) (τ : P.pair.T.group ⟶ Q.pair.T.group),
      Compatible P Q D E d τ →
      ∃ f : P.pair.G.val ⟶ Q.pair.G.val,
        MatchesPinning d τ f ∧
        IsFinite f.hom.hom.left ∧ Flat f.hom.hom.left ∧ Surjective f.hom.hom.left ∧
        HasCentralTorusKernel τ f ∧
        (Function.Surjective (pullbackCharacters τ) → IsIso f)

/-- The character-lattice formulation. The equality of coroots under the
dual map is expressed by pairing with every target character. -/
def CharacterStatement : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} (P Q : PinnedGroup A)
    (D : AttachedDatum P.pair) (E : AttachedDatum Q.pair),
    letI := D.comm
    letI := E.comm
    D.base.support.card ≤ 2 →
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

end LinearAlgebraicGroups.Specs.RankTwoLifting
