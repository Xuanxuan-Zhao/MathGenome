import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.SuperLie
import Mathlib.Algebra.Algebra.Bilinear

namespace LieNotes.SuperRestricted.Supercommutator

variable {k A : Type*} [Field k] [NonUnitalRing A] [Module k A]

/-- Multiplication respects the given parity grading. -/
def MulGraded (G : Grading k A) : Prop :=
  ∀ ⦃i j : ZMod 2⦄ ⦃x y : A⦄, x ∈ G.piece i → y ∈ G.piece j →
    x * y ∈ G.piece (i + j)

end LieNotes.SuperRestricted.Supercommutator

namespace Specs.LieNotes.SuperRestricted.Supercommutator

open _root_.LieNotes.SuperRestricted
open _root_.LieNotes.SuperRestricted.Supercommutator
open scoped BigOperators

universe u v

set_option linter.checkUnivs false

variable {k : Type u} {A : Type v} [Field k] [NonUnitalRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A]

/-- Take the (i)-component in the internal direct sum and include it in the algebra. -/
noncomputable def projection (G : Grading k A) (i : ZMod 2) : A →ₗ[k] A :=
  (G.piece i).subtype ∘ₗ
    DirectSum.component k (ZMod 2) (fun j => G.piece j) i ∘ₗ
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap G.piece) G.isInternal).symm.toLinearMap

def bracketType :=
  ∀ {k : Type u} {A : Type v} [Field k] [NonUnitalRing A] [Module k A]
    [SMulCommClass k A A] [IsScalarTower k A A],
    Grading k A → (A →ₗ[k] A →ₗ[k] A)

/-- Sum the signed commutators of all pairs of homogeneous components. -/
noncomputable def bracketValue (G : Grading k A) : A →ₗ[k] A →ₗ[k] A :=
  ∑ i : ZMod 2, ∑ j : ZMod 2,
    let product := ((LinearMap.mul k A).comp (projection G i)).compl₂ (projection G j)
    let reverse := ((LinearMap.mul k A).flip.comp (projection G i)).compl₂ (projection G j)
    product - paritySign k i j • reverse

def bracketOfMemType : Prop :=
  ∀ {k : Type u} {A : Type v} [Field k] [NonUnitalRing A] [Module k A]
    [SMulCommClass k A A] [IsScalarTower k A A] (G : Grading k A),
    ∀ ⦃i j : ZMod 2⦄ ⦃x y : A⦄, x ∈ G.piece i → y ∈ G.piece j →
      bracketValue G x y = x * y - paritySign k i j • (y * x)

def bracketOddSelfType : Prop :=
  ∀ {k : Type u} {A : Type v} [Field k] [NonUnitalRing A] [Module k A]
    [SMulCommClass k A A] [IsScalarTower k A A] (G : Grading k A),
    ∀ ⦃x : A⦄, x ∈ G.piece 1 → bracketValue G x x = (2 : k) • (x * x)

def oddTripleType : Prop :=
  ∀ {k : Type u} {A : Type v} [Field k] [NonUnitalRing A] [Module k A]
    [SMulCommClass k A A] [IsScalarTower k A A] (G : Grading k A),
    MulGraded G → OddTripleIdentity G (bracketValue G)

def existsLieSuperalgebraType : Prop :=
  ∀ {k : Type u} {A : Type v} [Field k] [NonUnitalRing A] [Module k A]
    [SMulCommClass k A A] [IsScalarTower k A A] [NeZero (2 : k)] (G : Grading k A),
    MulGraded G → ∃ L : LieSuperalgebra k A, L.grading = G ∧ L.bracket = bracketValue G

end Specs.LieNotes.SuperRestricted.Supercommutator
