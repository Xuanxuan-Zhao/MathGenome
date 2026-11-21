import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.CompletedQuotients
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Jacobson.Radical

/-! The flatness, maximal fibers, and locality assertions of Theorem 7.5,
paper.tex:1229–1242. All completions are the shared inverse limits. The
canonical scalar structure is used throughout. No nonzero-ring, proper-ideal,
or Jacobson hypothesis is imposed on the general assertions. Local rings have
a proper maximal ideal, as in the source conventions at paper.tex:47.

`Module.Flat` is preservation of injections by tensor product over the
commutative ring. `Module.FaithfullyFlat` includes flatness and nonvanishing
at every maximal fiber; its tensor faithfulness and exactness characterizations
are in Mathlib.RingTheory.Flat.FaithfullyFlat.Basic.
-/
universe u

namespace P103.Specs.Ch07.CompletedFlatnessLocality
open P103.Adic P103.Specs.Ch07.CompletedQuotients

def flatType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R),
    Module.Flat R (Completion I R)

def extendedIdeal_le_jacobsonType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R),
    extendedIdeal I ≤ Ring.jacobson (Completion I R)

/-- The representative formula identifies the isomorphism as the inverse of
the map on quotients induced by the canonical map R → R-hat. -/
def maximal_fiberType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (I m : Ideal R),
    m.IsMaximal → I ≤ m →
    ∃ e : (Completion I R ⧸ m.map (algebraMap R (Completion I R))) ≃+* (R ⧸ m),
      ∀ r : R, e (Ideal.Quotient.mk _ (algebraMap R (Completion I R) r)) =
        Ideal.Quotient.mk m r

def maximal_fiber_zeroType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (I m : Ideal R),
    m.IsMaximal → ¬ I ≤ m →
    Subsingleton (Completion I R ⧸ m.map (algebraMap R (Completion I R)))

def faithfullyFlat_iffType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R),
    Module.FaithfullyFlat R (Completion I R) ↔ I ≤ Ring.jacobson R

/-- Any chosen maximal ideal of the local base may be used as the ideal of
completion. The extended ideal is the unique proper maximal ideal. -/
def localType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (m : Ideal R), m.IsMaximal →
    IsLocalRing (Completion m R) ∧ (extendedIdeal m).IsMaximal ∧
      ∀ n : Ideal (Completion m R), n.IsMaximal → n = extendedIdeal m

/-- The induced map on residue fields, with its canonical formula. -/
def residueFieldType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (m : Ideal R), m.IsMaximal →
    ∃ e : (R ⧸ m) ≃+* (Completion m R ⧸ extendedIdeal m),
      ∀ r : R, e (Ideal.Quotient.mk m r) =
        Ideal.Quotient.mk _ (algebraMap R (Completion m R) r)

/-- At the zero ideal the canonical map itself is a ring isomorphism. -/
def zeroIdealType : Prop :=
  ∀ (R : Type u) [CommRing R],
    ∃ e : R ≃+* Completion (⊥ : Ideal R) R,
      ∀ r : R, e r = algebraMap R (Completion (⊥ : Ideal R) R) r

def topIdealType : Prop :=
  ∀ (R : Type u) [CommRing R], Subsingleton (Completion (⊤ : Ideal R) R)

end P103.Specs.Ch07.CompletedFlatnessLocality
