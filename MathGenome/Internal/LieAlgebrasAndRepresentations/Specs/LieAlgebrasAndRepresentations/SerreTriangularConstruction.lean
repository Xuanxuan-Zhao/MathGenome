import Mathlib.Algebra.Lie.SerreConstruction
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CartanMatrix
import Mathlib.Basic.Complex.Basic

/-!
LA-F02, converse construction, source notes/005 lines 2560–2646.
The assertion for triples in an existing semisimple algebra is allocated to
LA-F02-Relations. Here all quotients are actual Lie-ideal quotients.

Rows of A index coroots. Mathlib writes its last two relations as
(ad e_i)^(-a_ij).toNat [e_i,e_j], including redundant zero relations for i=j.
For off-diagonal a_ij ≤ 0 this is exactly (ad e_i)^(1-a_ij) e_j.
No faithfulness of any quotient generator is built into these definitions.
-/
noncomputable section

namespace LieAlgebrasAndRepresentations.Serre
universe u
variable {ι : Type u} [DecidableEq ι]

abbrev Free (ι : Type u) := FreeLieAlgebra ℂ (CartanMatrix.Generators ι)
abbrev Algebra (A : Matrix ι ι ℤ) := Matrix.ToLieAlgebra ℂ A

def projection (A : Matrix ι ι ℤ) : Free ι →ₗ⁅ℂ⁆ Algebra A :=
  { (CartanMatrix.Relations.toIdeal ℂ A).toSubmodule.mkQ with
    map_lie' := by intros; rfl }

def e (A : Matrix ι ι ℤ) (i : ι) : Algebra A :=
  projection A (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E i))
def f (A : Matrix ι ι ℤ) (i : ι) : Algebra A :=
  projection A (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F i))
def h (A : Matrix ι ι ℤ) (i : ι) : Algebra A :=
  projection A (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i))

/-- n repetitions of left bracketing by x, including n=0. -/
def iterBracket {L : Type*} [LieRing L] (x : L) : ℕ → L → L
  | 0, y => y
  | n+1, y => ⁅x, iterBracket x n y⁆

/-- The displayed relations (6.1), with their original exponent. -/
def RelationsHold {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (A : Matrix ι ι ℤ) (E F H : ι → L) : Prop :=
  (∀ i j, ⁅H i, H j⁆ = 0) ∧
  (∀ i j, ⁅H i, E j⁆ = A i j • E j) ∧
  (∀ i j, ⁅H i, F j⁆ = -(A i j • F j)) ∧
  (∀ i j, ⁅E i, F j⁆ = if i = j then H i else 0) ∧
  (∀ i j, i ≠ j → iterBracket (E i) (1 - A i j).toNat (E j) = 0) ∧
  (∀ i j, i ≠ j → iterBracket (F i) (1 - A i j).toNat (F j) = 0)

/-- Free Lie algebra on only the positive (or only the negative) symbols. -/
abbrev SideFree (ι : Type u) := FreeLieAlgebra ℂ ι

def sideRelation (A : Matrix ι ι ℤ) (i j : ι) : SideFree ι :=
  iterBracket (FreeLieAlgebra.of ℂ i) (-A i j).toNat
    ⁅FreeLieAlgebra.of ℂ i, FreeLieAlgebra.of ℂ j⁆

/-- Only the one-sided Serre relations, with no Cartan or mixed relations. -/
def sideIdeal (A : Matrix ι ι ℤ) : LieIdeal ℂ (SideFree ι) :=
  LieSubmodule.lieSpan ℂ _ {x | ∃ i j, x = sideRelation A i j}

abbrev Side (A : Matrix ι ι ℤ) := SideFree ι ⧸ sideIdeal A

def sideGenerator (A : Matrix ι ι ℤ) (i : ι) : Side A :=
  LieSubmodule.Quotient.mk (FreeLieAlgebra.of ℂ i)

def positiveLift (A : Matrix ι ι ℤ) : SideFree ι →ₗ⁅ℂ⁆ Algebra A :=
  FreeLieAlgebra.lift ℂ (e A)
def negativeLift (A : Matrix ι ι ℤ) : SideFree ι →ₗ⁅ℂ⁆ Algebra A :=
  FreeLieAlgebra.lift ℂ (f A)

def positive (A : Matrix ι ι ℤ) : LieSubalgebra ℂ (Algebra A) :=
  LieSubalgebra.lieSpan ℂ _ (Set.range (e A))
def negative (A : Matrix ι ι ℤ) : LieSubalgebra ℂ (Algebra A) :=
  LieSubalgebra.lieSpan ℂ _ (Set.range (f A))
def cartan (A : Matrix ι ι ℤ) : Submodule ℂ (Algebra A) :=
  Submodule.span ℂ (Set.range (h A))

/-- The actual addition map of the three specified subspaces. -/
def triangularSum (A : Matrix ι ι ℤ) :
    negative A × (cartan A × positive A) →ₗ[ℂ] Algebra A :=
  (negative A).toSubmodule.subtype.coprod
    ((cartan A).subtype.coprod (positive A).toSubmodule.subtype)

/-- Algebraic Cartan conditions sufficient for the triangular construction;
finite-type root matrices satisfy these, but no such conditions are assumed
when defining the quotient itself. -/
def CartanConditions (A : Matrix ι ι ℤ) : Prop :=
  (∀ i, A i i = 2) ∧ (∀ i j, i ≠ j → A i j ≤ 0) ∧
  (∀ i j, A i j = 0 ↔ A j i = 0)

/-- Full vector-space decomposition, the specified Cartan basis, exact
one-sided presentations, and survival of every generator. Kernel equalities
identify Side A with the corresponding actual subalgebras, by the first
isomorphism theorem. In particular they exclude additional one-sided relations. -/
def Triangular (A : Matrix ι ι ℤ) : Prop :=
  Function.Bijective (triangularSum A) ∧
  (∃ b : Module.Basis ι ℂ (cartan A), ∀ i, (b i : Algebra A) = h A i) ∧
  ((negativeLift A).ker = sideIdeal A ∧ (negativeLift A).range = negative A) ∧
  ((positiveLift A).ker = sideIdeal A ∧ (positiveLift A).range = positive A) ∧
  (∀ i, e A i ≠ 0 ∧ f A i ≠ 0 ∧ h A i ≠ 0)

end LieAlgebrasAndRepresentations.Serre

namespace Specs.LieAlgebrasAndRepresentations.SerreTriangularConstruction
open _root_.LieAlgebrasAndRepresentations
open _root_.LieAlgebrasAndRepresentations.Serre
universe u v w

def algebraExpectedType := ∀ {ι : Type v} [DecidableEq ι], Matrix ι ι ℤ → Type v
def algebraExpectedValue : algebraExpectedType.{v} := fun A => Matrix.ToLieAlgebra ℂ A

def projectionExpectedType := ∀ {ι : Type v} [DecidableEq ι] (A : Matrix ι ι ℤ),
  Free ι →ₗ⁅ℂ⁆ Algebra A
def projectionExpectedValue : projectionExpectedType.{v} := @projection

def generatorsExpectedType := ∀ {ι : Type v} [DecidableEq ι] (A : Matrix ι ι ℤ),
  (ι → Algebra A) × (ι → Algebra A) × (ι → Algebra A)
def generatorsExpectedValue : generatorsExpectedType.{v} := fun A => (e A, f A, h A)

def relationsExpected : Prop := ∀ {ι : Type v} [DecidableEq ι] (A : Matrix ι ι ℤ),
  (∀ i j, i ≠ j → A i j ≤ 0) → RelationsHold A (e A) (f A) (h A)

/-- Universality of the displayed presentation, not merely its relations. -/
def presentationExpected : Prop :=
  ∀ {ι : Type v} [DecidableEq ι] (A : Matrix ι ι ℤ),
  (∀ i j, i ≠ j → A i j ≤ 0) →
  ∀ (L : Type w) [LieRing L] [LieAlgebra ℂ L] (E F H : ι → L),
  RelationsHold A E F H →
    ∃! φ : Algebra A →ₗ⁅ℂ⁆ L,
      (∀ i, φ (e A i) = E i) ∧ (∀ i, φ (f A i) = F i) ∧ (∀ i, φ (h A i) = H i)

def cartanConditionsExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ {ι : Type v} [DecidableEq ι] (R : Set E), IsRootSystem R →
  ∀ z, RootRegular R z → ∀ b : Module.Basis ι ℝ E, IsSimpleBasis R z b →
  ∀ A : Matrix ι ι ℤ, (∀ i j, (A i j : ℝ) = cartanMatrix b i j) → CartanConditions A

/-- The theorem applies to every original finite reduced root system and its
simple basis. The integer matrix is compared entrywise with the accepted
Euclidean Cartan interface, so no classification or stronger matrix assumption
is hidden here. Empty index types and the zero Euclidean space are allowed. -/
def triangularExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E],
  ∀ {ι : Type v} [Fintype ι] [DecidableEq ι] (R : Set E), IsRootSystem R →
  ∀ z, RootRegular R z → ∀ b : Module.Basis ι ℝ E, IsSimpleBasis R z b →
  ∀ A : Matrix ι ι ℤ, (∀ i j, (A i j : ℝ) = cartanMatrix b i j) → Triangular A

/-- The one-sided relations vanish in the full quotient, and the canonical
free maps have precisely the intended generated subalgebras as their ranges.
The reverse kernel inclusions are part of triangularExpected, not assumed here. -/
def oneSidedExpected : Prop := ∀ {ι : Type v} [DecidableEq ι] (A : Matrix ι ι ℤ),
  sideIdeal A ≤ (positiveLift A).ker ∧ sideIdeal A ≤ (negativeLift A).ker ∧
  (positiveLift A).range = positive A ∧ (negativeLift A).range = negative A

def sideSurvivalExpected : Prop := ∀ {ι : Type v} [DecidableEq ι]
  (A : Matrix ι ι ℤ) (i : ι), sideGenerator A i ≠ 0

/-- Boundary case independently of root-system witnesses. -/
def emptyExpected : Prop := ∀ {ι : Type v} [DecidableEq ι] [IsEmpty ι]
  (A : Matrix ι ι ℤ), Subsingleton (Algebra A)

end Specs.LieAlgebrasAndRepresentations.SerreTriangularConstruction
