import Mathlib.Algebra.Ring.Subring.Basic
import MathGenome.Internal.Specs.D07.Ch23.CentralizersFiniteDivisionCoordinates

/-!
Independent specifications for K07.23.centralizers, paper.tex:7355–7385.
`Subfield D` means an inverse-closed unital subring of a division ring;
it does not require commutativity. The center and element centralizer use
Mathlib's canonical subrings, with carrier bridges fixing the order of
multiplication in the source. The field structure retains the inherited
ring operations. Finiteness always means finiteness of the underlying set.

The finite left-coordinate and central-dimension statements are reused
verbatim from the independent prerequisite specification. In particular
no commutativity of a division subring, nor Wedderburn's theorem, is assumed.
-/

universe u v

namespace Specs.D07.Ch23.Centralizers

def CenterCarrier : Prop :=
  ∀ (D : Type u) [DivisionRing D],
    (Subring.center D : Set D) = {a | ∀ x : D, a * x = x * a}

def CentralizerCarrier : Prop :=
  ∀ (D : Type u) [DivisionRing D] (x : D),
    (Subring.centralizer ({x} : Set D) : Set D) = {a | a * x = x * a}

/-- Inversion preserves the commuting identity, including the totalized zero case. -/
def CommutingInverse : Prop :=
  ∀ (D : Type u) [DivisionRing D] (a x : D),
    a * x = x * a → a⁻¹ * x = x * a⁻¹

/-- The center, with precisely its original carrier and inherited operations,
is a division subring. -/
def CenterDivisionSubring : Prop :=
  ∀ (D : Type u) [DivisionRing D],
    ∃ Z : Subfield D, Z.toSubring = Subring.center D

/-- The element centralizer is a division subring, without finiteness assumptions. -/
def CentralizerDivisionSubring : Prop :=
  ∀ (D : Type u) [DivisionRing D] (x : D),
    ∃ C : Subfield D, C.toSubring = Subring.centralizer ({x} : Set D)

def CenterCommutative : Prop :=
  ∀ (D : Type u) [DivisionRing D] (a b : Subring.center D), a * b = b * a

/-- Existence of a field structure with the actual inherited ring structure. -/
def CenterField : Prop :=
  ∀ (D : Type u) [DivisionRing D],
    ∃ f : Field (Subring.center D), f.toRing = (Subring.center D).toRing

/-- For every unital subring of a finite division ring, ambient inverses lie in it. -/
def FiniteSubringInverseClosed : Prop :=
  ∀ (D : Type u) [DivisionRing D] [Finite D] (S : Subring D)
    (a : D), a ∈ S → a⁻¹ ∈ S

def FiniteSubringDivisionSubring : Prop :=
  ∀ (D : Type u) [DivisionRing D] [Finite D] (S : Subring D),
    ∃ E : Subfield D, E.toSubring = S

/-- A finite ambient division ring gives a division ring structure on each
unital subring, keeping its inherited ring operations. -/
def FiniteSubringDivisionRing : Prop :=
  ∀ (D : Type u) [DivisionRing D] [Finite D] (S : Subring D),
    ∃ d : DivisionRing S, d.toRing = S.toRing

/-- Finite basis, unique left coordinates, positive rank, and |D| = |E|^r. -/
def LeftBasisAndCounting : Prop :=
  CentralizersFiniteDivisionCoordinates.LeftBasisAndCounting.{u}

/-- For any specified finite central field F contained in E: counts, positive
dimensions, n = d*r, divisibility, and strict inequality for a proper E. -/
def CentralDimensions : Prop :=
  CentralizersFiniteDivisionCoordinates.CentralDimensions.{u, v}

end Specs.D07.Ch23.Centralizers
