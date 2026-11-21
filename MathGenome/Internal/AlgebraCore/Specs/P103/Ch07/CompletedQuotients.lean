import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.CompletionInterface
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.ReesGradedConstruction
import Mathlib.RingTheory.Noetherian.Basic

/-! The quotient, graded-ring and completeness assertions of Theorem 7.5.
The completion and associated graded rings are the shared canonical objects.
No quotient comparison or completeness certificate is an assumption. -/
universe u
namespace P103.Specs.Ch07.CompletedQuotients
open P103.Adic P103.Rees

/-- The extension of I to its completed ring. -/
noncomputable abbrev extendedIdeal {R : Type u} [CommRing R] (I : Ideal R) :
    Ideal (Completion I R) := I.map (algebraMap R (Completion I R))

def projection_kernelType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (n : ℕ),
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom = extendedIdeal I ^ n

/-- The isomorphisms are induced by evaluation and commute with every reduction.
Including n=0 is harmless: both zeroth quotients are zero rings. -/
def quotient_comparisonType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R),
    ∃ e : ∀ n : ℕ, (Completion I R ⧸ extendedIdeal I ^ n) ≃+* (R ⧸ I ^ n),
      (∀ n x, e n (Ideal.Quotient.mk _ x) = AdicCompletion.evalₐ I n x) ∧
      (∀ {m n : ℕ} (h : m ≤ n) x,
        Ideal.Quotient.factorPow I h (e n x) =
          e m (Ideal.Quotient.factorPow (extendedIdeal I) h x))

/-- A ring isomorphism preserving all internal homogeneous pieces. Its formula
on classes fixes the canonical identification on successive quotients. -/
def graded_comparisonType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R),
    ∃ e : AssociatedRing (extendedIdeal I) ≃+* AssociatedRing I,
      (∀ n, (ringPiece (extendedIdeal I) n).map e.toAddMonoidHom = ringPiece I n) ∧
      (∀ n (a : (I ^ n : Ideal R)) (b : (extendedIdeal I ^ n : Ideal (Completion I R))),
        b.val = algebraMap R (Completion I R) a.val →
          e (ringClass (extendedIdeal I) n b) = ringClass I n a)

/-- Separatedness and the canonical isomorphism to the limit of J-power
quotients. The limit uses the same shared completion construction, over R-hat. -/
def complete_separatedType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R),
    (⨅ n : ℕ, extendedIdeal I ^ n) = ⊥ ∧
      ∃ e : Completion I R ≃+* Completion (extendedIdeal I) (Completion I R),
        ∀ x, e x = algebraMap (Completion I R)
          (Completion (extendedIdeal I) (Completion I R)) x

end P103.Specs.Ch07.CompletedQuotients
