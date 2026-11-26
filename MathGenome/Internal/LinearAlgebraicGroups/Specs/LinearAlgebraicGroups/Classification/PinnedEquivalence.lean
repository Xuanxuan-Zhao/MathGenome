import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.Pinning
import Mathlib.CategoryTheory.Equivalence

open CategoryTheory
universe u

namespace LinearAlgebraicGroups.Specs.PinnedEquivalence

open Pinning (AttachedDatum BasedRootDatum BasedIso PinnedGroup SplitBorelPair transportCharacter)
open CharacterDescent (Character Cocharacter)
open GeometricRadicals (IsSplitReductive)
open RootGroups (AdditiveLine)

/-- A finite reduced integral root datum with both full lattices and no chosen base. -/
structure ReducedRootDatum where
  I : Type u
  X : Type u
  Y : Type u
  [addX : AddCommGroup X]
  [addY : AddCommGroup Y]
  finiteRoots : Finite I
  freeX : Module.Free ℤ X
  freeY : Module.Free ℤ Y
  finiteX : Module.Finite ℤ X
  finiteY : Module.Finite ℤ Y
  datum : RootDatum I X Y
  reduced : datum.IsReduced

attribute [instance] ReducedRootDatum.addX ReducedRootDatum.addY

/-- Forget only the base. -/
def forgetBase (D : BasedRootDatum.{u}) : ReducedRootDatum.{u} where
  I := D.I
  X := D.X
  Y := D.Y
  addX := D.addX
  addY := D.addY
  finiteRoots := D.finiteRoots
  freeX := D.freeX
  freeY := D.freeY
  finiteX := D.finiteX
  finiteY := D.finiteY
  datum := D.datum
  reduced := D.reduced

/-- Pinned equivalence, with the indicated maps on the actual lattices. -/
def PinnedClassification : Prop :=
  ∀ {k : Type u} [Field k] (A : AdditiveLine k),
    ∃ (D : ∀ P : PinnedGroup A, AttachedDatum P.pair)
      (F : PinnedGroup A ⥤ BasedRootDatum.{u}),
      ∃ hObj : ∀ P, F.obj P = (D P).toBased,
        (∀ (P Q : PinnedGroup A) (f : P ⟶ Q),
          let e : BasedIso (D P).toBased (D Q).toBased :=
            (hObj P) ▸ (hObj Q) ▸ F.map f
          (∀ χ : Character P.pair.T.group, e.val.weightEquiv (Additive.ofMul χ) =
            Additive.ofMul (transportCharacter f.torus χ)) ∧
          (∀ c : Cocharacter Q.pair.T.group, e.val.coweightEquiv (Additive.ofMul c) =
            Additive.ofMul (c ≫ f.torus.inv))) ∧
        F.IsEquivalence ∧
        (∀ (P Q : PinnedGroup A) (e : F.obj P ⟶ F.obj Q),
          ∃! f : P ⟶ Q, F.map f = e)

/-- The datum of any split Borel pair classifies the underlying split group
up to ground-field isomorphism. All split groups and all reduced data occur. -/
def UnpinnedClassification : Prop :=
  ∀ (k : Type u) [Field k],
    (∀ (G : AffineAlgebraicGroup k), IsSplitReductive G →
      ∃ P : SplitBorelPair k, P.G = G) ∧
    (∀ (P Q : SplitBorelPair k) (D : AttachedDatum P) (E : AttachedDatum Q),
      Nonempty (P.G.val ≅ Q.G.val) ↔ Nonempty (D.toBased.datum.Equiv E.toBased.datum)) ∧
    ∀ D : ReducedRootDatum.{u},
      ∃ (P : SplitBorelPair k) (E : AttachedDatum P),
        Nonempty (D.datum.Equiv E.toBased.datum)

def Statement : Prop := PinnedClassification.{u} ∧ UnpinnedClassification.{u}

end LinearAlgebraicGroups.Specs.PinnedEquivalence
