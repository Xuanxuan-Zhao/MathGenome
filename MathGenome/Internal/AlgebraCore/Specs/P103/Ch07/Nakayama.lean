import MathGenome.Internal.AlgebraCore.Specs.P103.Ch03.Nakayama
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Finiteness.Nakayama

/-!
Independent statements for paper.tex, lines 1172–1178 (Theorem 7.1), with
its determinant-trick consequence used at lines 1198–1202.
The global conventions (line 47) make the scalar ring commutative and unital;
the zero ring is allowed. Local rings have a proper unique maximal ideal,
so the local-ring assertions exclude the zero ring by their conclusions,
not by an added ambient hypothesis.

We reuse `radical R = Ring.jacobson R` from the Chapter 3 Specs. The first
statement identifies it with the intersection of proper maximal ideals.
`I • ⊤` denotes IM and `Module.Finite R M` denotes finite generation.
`Subsingleton M` means M is the zero module. All generator families are
arbitrarily indexed, including the empty family. No Noetherian assumption
is made, including in the determinant-trick statement.
-/

universe u v w

namespace P103.Specs.Ch07.Nakayama

open P103.Specs.Ch03.JacobsonRadical (radical)

def maximal_intersectionType : Prop :=
  ∀ (R : Type u) [CommRing R],
    radical R = sInf {m : Ideal R | m.IsMaximal}

def one_sub_isUnitType : Prop :=
  ∀ (R : Type u) [CommRing R] (a : R), a ∈ radical R → IsUnit (1 - a)

/-- Every choice of maximal ideal in a local ring is the proper ideal of nonunits. -/
def local_nonunitsType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] (m : Ideal R), m.IsMaximal →
    m ≠ ⊤ ∧ (m : Set R) = nonunits R ∧
      (∀ J : Ideal R, J ≠ ⊤ → J ≤ m) ∧
      (∀ J : Ideal R, J.IsMaximal → J = m)

def local_iff_unique_maximalType : Prop :=
  ∀ (R : Type u) [CommRing R],
    IsLocalRing R ↔ ∃! m : Ideal R, m.IsMaximal

def local_iff_nonunits_idealType : Prop :=
  ∀ (R : Type u) [CommRing R],
    IsLocalRing R ↔ ∃ m : Ideal R, m ≠ ⊤ ∧ (m : Set R) = nonunits R

/-- The converse also identifies the given ideal and contains every proper ideal. -/
def nonunits_ideal_uniqueType : Prop :=
  ∀ (R : Type u) [CommRing R] (m : Ideal R),
    m ≠ ⊤ → (m : Set R) = nonunits R →
    IsLocalRing R ∧ m.IsMaximal ∧
      (∀ J : Ideal R, J ≠ ⊤ → J ≤ m) ∧
      (∀ J : Ideal R, J.IsMaximal → J = m)

def sup_iffType : Prop :=
  ∀ (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R), I ≤ radical R →
    ∀ N : Submodule R M, N ⊔ I • (⊤ : Submodule R M) = ⊤ ↔ N = ⊤

def eq_zeroType : Prop :=
  ∀ (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R), I ≤ radical R →
    I • (⊤ : Submodule R M) = ⊤ → Subsingleton M

def generators_liftType : Prop :=
  ∀ (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R), I ≤ radical R →
    ∀ (ι : Type w) (g : ι → M ⧸ (I • (⊤ : Submodule R M))) (x : ι → M),
      (∀ i, (I • (⊤ : Submodule R M)).mkQ (x i) = g i) →
      Submodule.span R (Set.range g) = ⊤ → Submodule.span R (Set.range x) = ⊤

/-- The scalar annihilator conclusion before imposing any Jacobson condition. -/
def determinant_trickType : Prop :=
  ∀ (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R),
    I • (⊤ : Submodule R M) = ⊤ → ∃ a ∈ I, ∀ m : M, (1 - a) • m = 0

end P103.Specs.Ch07.Nakayama
