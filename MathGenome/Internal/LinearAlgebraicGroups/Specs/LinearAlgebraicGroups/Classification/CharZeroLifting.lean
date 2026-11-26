import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.SchemeImageQuotient
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.Pinning

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.CharZeroLifting

open AbstractPairing (Root)
open CharacterDescent (Character Cocharacter)
open CharacterPairing (pairing)
open Pinning (AttachedDatum PinnedGroup IsSimple SimpleRoot SplitBorelPair)
open RootGroups (AdditiveLine)

variable {k : Type u} [Field k]

/-- The coroot of the actual attached datum, viewed as a map of group schemes. -/
def attachedCoroot {P : SplitBorelPair k} (D : AttachedDatum P) (α : Root P.T) :
    Cocharacter P.T.group :=
  letI := D.comm
  Additive.toMul (D.datum.rootDatum.coroot α)

/-- An ordinary based isogeny of attached root data, with pullback on the
full character lattice. The pairing equation specifies the transpose on coroots. -/
structure LatticeMap {P Q : SplitBorelPair k} (D : AttachedDatum P) (E : AttachedDatum Q) where
  characters : Character Q.T.group →* Character P.T.group
  injective : Function.Injective characters
  finiteIndex : Finite (Character P.T.group ⧸ characters.range)
  roots : Root P.T ≃ Root Q.T
  simple_iff : ∀ α, IsSimple Q (roots α) ↔ IsSimple P α
  root_eq : ∀ α, characters (roots α).val = α.val
  coroot_eq : ∀ α (χ : Character Q.T.group),
    pairing P.T.group (characters χ) (attachedCoroot D α) =
      pairing Q.T.group χ (attachedCoroot E (roots α))

/-- The chosen map carries simple roots to simple roots. -/
def LatticeMap.simpleRoot {P Q : SplitBorelPair k} {D : AttachedDatum P}
    {E : AttachedDatum Q} (h : LatticeMap D E) (α : SimpleRoot P) : SimpleRoot Q :=
  ⟨h.roots α.val, (h.simple_iff α.val).mpr α.property⟩

/-- Centrality is imposed on the scheme kernel, including its families over
arbitrary base schemes. -/
def IsCentralIsogeny {G H : GroupScheme k} (f : G ⟶ H) : Prop :=
  Surjective f.hom.hom.left ∧
    ∃ N : ClosedSubgroup G, IsSchemeKernel f N ∧ IsFinite N.group.X.hom ∧
      Centralizes (𝟙 G) N.inclusion.hom.hom

/-- The conclusion for a given pair of groups and a given lattice map. -/
def Lifts {A : AdditiveLine k} (P Q : PinnedGroup A)
    (D : AttachedDatum P.pair) (E : AttachedDatum Q.pair) (h : LatticeMap D E) : Prop :=
    ∃ (f : P.pair.G.val ⟶ Q.pair.G.val) (t : P.pair.T.group ⟶ Q.pair.T.group)
      (b : P.pair.B.group ⟶ Q.pair.B.group),
      IsCentralIsogeny f ∧ Surjective t.hom.hom.left ∧ Surjective b.hom.hom.left ∧
      P.pair.T.inclusion ≫ f = t ≫ Q.pair.T.inclusion ∧
      P.pair.B.inclusion ≫ f = b ≫ Q.pair.B.inclusion ∧
      (∀ χ : Character Q.pair.T.group, t ≫ χ = h.characters χ) ∧
      (∀ α : SimpleRoot P.pair,
        (P.pin α).val.hom ≫ (P.roots α.val).val.inclusion ≫ f =
          (Q.pin (h.simpleRoot α)).val.hom ≫ (Q.roots (h.roots α.val)).val.inclusion) ∧
      (Function.Bijective h.characters → IsIso f)

/-- In characteristic zero an ordinary based lattice map lifts to a
pin-compatible central isogeny, which is invertible for a lattice isomorphism. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {A : AdditiveLine k} (P Q : PinnedGroup A)
    (D : AttachedDatum P.pair) (E : AttachedDatum Q.pair) (h : LatticeMap D E),
    Lifts P Q D E h

end LinearAlgebraicGroups.Specs.CharZeroLifting
