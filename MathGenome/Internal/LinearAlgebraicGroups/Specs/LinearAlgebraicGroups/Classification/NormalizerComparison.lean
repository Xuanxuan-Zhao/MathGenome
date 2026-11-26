import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.RankTwoLifting
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.SimpleRoots
import Mathlib.GroupTheory.OrderOfElement

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.NormalizerComparison

open AbstractPairing (Root)
open Pinning (AttachedDatum PinnedGroup SimpleRoot)
open RankTwoLifting (Compatible)
open RootGroups (AdditiveLine CorootReflection)

/-- The simple reflections present the actual Weyl group. The diagonal
relations are squares and the other exponents are orders in that group. -/
def WeylPresentation : Prop :=
  ∀ {I X Y : Type u} [AddCommGroup X] [AddCommGroup Y] [Finite I]
    [Module.Free ℤ X] [Module.Finite ℤ X] (D : RootDatum I X Y) [D.IsReduced]
    (b : D.Base) {H : Type u} [Group H] (g : b.support → H),
    let s := fun i : b.support => RootPairing.weylGroup.ofIdx D i.val
    (∀ i j, (g i * g j) ^ (orderOf (s i * s j)) = 1) →
    ∃! f : D.weylGroup →* H, ∀ i, f (s i) = g i

variable {k : Type u} [Field k] {A : AdditiveLine k}

/-- The lift of a simple reflection given by the pinned positive coordinate
and its linked opposite coordinate, with the attached coroot. -/
structure SimpleRepresentative (P : PinnedGroup A) (D : AttachedDatum P.pair)
    (i : SimpleRoot P.pair) where
  opposite : Root P.pair.T
  opposite_eq : opposite.val = i.val.val⁻¹
  negative : Pinning.RootCoordinate A P.pair.T (P.roots opposite).val opposite.val
  reflection : CorootReflection P.pair.T i.val.val
    ((P.pin i).val.hom ≫ (P.roots i.val).val.inclusion)
    (negative.val.hom ≫ (P.roots opposite).val.inclusion)
  coroot_eq : letI := D.comm
    reflection.coroot = Additive.toMul (D.datum.rootDatum.coroot i.val)

/-- The comparison of normalizers over the ground field. The specified torus
map is realized on the whole torus and the pinned representatives match over
the ground field. The normalizers represent the normalizing functors on all
test schemes. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} (P Q : PinnedGroup A)
    (D : AttachedDatum P.pair) (E : AttachedDatum Q.pair)
    (d : Root P.pair.T ≃ Root Q.pair.T) (τ : P.pair.T.group ⟶ Q.pair.T.group),
    Compatible P Q D E d τ →
    ∃ (N : ClosedSubgroup P.pair.G.val) (M : ClosedSubgroup Q.pair.G.val)
      (j : P.pair.T.group ⟶ N.group) (l : Q.pair.T.group ⟶ M.group)
      (f : N.group ⟶ M.group),
      RepresentsSubgroup N (fun _ g => Normalizes P.pair.T.inclusion g) ∧
      RepresentsSubgroup M (fun _ g => Normalizes Q.pair.T.inclusion g) ∧
      j ≫ N.inclusion = P.pair.T.inclusion ∧ l ≫ M.inclusion = Q.pair.T.inclusion ∧
      j ≫ f = τ ≫ l ∧
      ∃ (n : ∀ i : SimpleRoot P.pair, SimpleRepresentative P D i)
        (m : ∀ i : SimpleRoot Q.pair, SimpleRepresentative Q E i),
        ∀ (i : SimpleRoot P.pair) (h : SimpleRoot Q.pair), d i.val = h.val →
          ∃ x : 𝟙_ (SchemeOver k) ⟶ N.group.X,
            x ≫ N.inclusion.hom.hom = (n i).reflection.representative ∧
            x ≫ f.hom.hom ≫ M.inclusion.hom.hom = (m h).reflection.representative

end LinearAlgebraicGroups.Specs.NormalizerComparison
