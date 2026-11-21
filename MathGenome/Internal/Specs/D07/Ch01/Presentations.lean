import MathGenome.Internal.Specs.D07.Ch01.FreeGroupUniversalProperty
import MathGenome.Internal.Specs.D07.Ch01.GroupNormalQuotient
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
Independent specification of `K07.01.presentations`, paper.tex:399–409.

The free group is the same signed-word quotient as in the upstream specification.
`Subgroup.normalClosure` is identified with the intersection in the source by
`NormalClosureEqIntersection`. The presentation is its normal quotient, and the
generator map is the free generator followed by the quotient projection.
Relator evaluation is `FreeGroup.lift f`, whose signed-word evaluation formula
is part of the upstream free-group specification. Both the factorization and
generator-value versions of unique induction are stated below.

No finiteness, decidable equality, nonemptiness, or nontriviality is required.
The generator type and target group may belong to different universes.
-/

namespace Specs.D07.Ch01.Presentations

universe u v

def PresentationType := (S : Type u) → Set (FreeGroup S) → Type u

abbrev presentationValue (S : Type u) (R : Set (FreeGroup S)) : Type u :=
  FreeGroup S ⧸ Subgroup.normalClosure R

def ProjectionType :=
  (S : Type u) → (R : Set (FreeGroup S)) → FreeGroup S →* presentationValue S R

def projectionValue (S : Type u) (R : Set (FreeGroup S)) :
    FreeGroup S →* presentationValue S R :=
  QuotientGroup.mk' (Subgroup.normalClosure R)

def GeneratorType :=
  (S : Type u) → (R : Set (FreeGroup S)) → S → presentationValue S R

def generatorValue (S : Type u) (R : Set (FreeGroup S)) (s : S) :
    presentationValue S R :=
  projectionValue S R (FreeGroup.of s)

def NormalClosureEqIntersection : Prop :=
  ∀ (S : Type u) (R : Set (FreeGroup S)),
    Subgroup.normalClosure R =
      ⨅ (N : Subgroup (FreeGroup S)) (_ : N.Normal) (_ : R ⊆ N), N

def NormalClosureNormal : Prop :=
  ∀ (S : Type u) (R : Set (FreeGroup S)), (Subgroup.normalClosure R).Normal

def RelatorsSubsetNormalClosure : Prop :=
  ∀ (S : Type u) (R : Set (FreeGroup S)), R ⊆ Subgroup.normalClosure R

def ProjectionSurjective : Prop :=
  ∀ (S : Type u) (R : Set (FreeGroup S)), Function.Surjective (projectionValue S R)

def ProjectionKernel : Prop :=
  ∀ (S : Type u) (R : Set (FreeGroup S)),
    (projectionValue S R).ker = Subgroup.normalClosure R

def RelatorsVanish : Prop :=
  ∀ (S : Type u) (R : Set (FreeGroup S)) (r : FreeGroup S),
    r ∈ R → projectionValue S R r = 1

/-- The induced homomorphism factors the unique evaluation on the free group. -/
def DescendsUniqueIff : Prop :=
  ∀ (S : Type u) (R : Set (FreeGroup S)) (H : Type v) [Group H] (f : S → H),
    (∃! φ : presentationValue S R →* H,
      φ.comp (projectionValue S R) = FreeGroup.lift f) ↔
      ∀ r ∈ R, FreeGroup.lift f r = 1

/-- Existence alone is equivalent to all the defining relations holding. -/
def InducedHomExistsIff : Prop :=
  ∀ (S : Type u) (R : Set (FreeGroup S)) (H : Type v) [Group H] (f : S → H),
    (∃ φ : presentationValue S R →* H,
      ∀ s : S, φ (generatorValue S R s) = f s) ↔
      ∀ r ∈ R, FreeGroup.lift f r = 1

/-- Every map on generators satisfying the relators extends uniquely. -/
def InducedHomUniqueIff : Prop :=
  ∀ (S : Type u) (R : Set (FreeGroup S)) (H : Type v) [Group H] (f : S → H),
    (∃! φ : presentationValue S R →* H,
      ∀ s : S, φ (generatorValue S R s) = f s) ↔
      ∀ r ∈ R, FreeGroup.lift f r = 1

end Specs.D07.Ch01.Presentations
