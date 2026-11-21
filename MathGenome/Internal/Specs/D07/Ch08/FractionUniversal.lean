import MathGenome.Internal.Specs.D07.Ch08.FractionField

/-!
Independent statements for K07.08.fraction_universal, paper.tex:1481–1515.
The concrete field of fractions is the quotient `FractionRing R` used by
the preceding construction. All maps are unital. General ring targets may
be zero rings. The statement about two models uses precisely embeddings
and fraction representations, without assuming an isomorphism or universal
property of either model.
-/

universe u v w

namespace Specs.D07.Ch08.FractionUniversal

def FieldExtensionUnique : Prop :=
  ∀ (R : Type u) (K : Type v) [CommRing R] [IsDomain R] [Field K]
    (f : R →+* K), Function.Injective f →
    ∃! g : FractionRing R →+* K, g.comp (algebraMap R (FractionRing R)) = f

def FieldExtensionInjective : Prop :=
  ∀ (R : Type u) (K : Type v) [CommRing R] [IsDomain R] [Field K]
    (f : R →+* K), Function.Injective f →
    ∀ g : FractionRing R →+* K,
      g.comp (algebraMap R (FractionRing R)) = f → Function.Injective g

def FieldFractionFormula : Prop :=
  ∀ (R : Type u) (K : Type v) [CommRing R] [IsDomain R] [Field K]
    (f : R →+* K), Function.Injective f →
    ∀ (g : FractionRing R →+* K),
      g.comp (algebraMap R (FractionRing R)) = f →
      ∀ a b : R, b ≠ 0 →
        g (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b) =
          f a / f b

def ModelsUniqueIso : Prop :=
  ∀ (R : Type u) (K : Type v) (L : Type w)
    [CommRing R] [IsDomain R] [Field K] [Field L]
    (i : R →+* K) (j : R →+* L),
    Function.Injective i → Function.Injective j →
    (∀ x : K, ∃ a b : R, b ≠ 0 ∧ x = i a / i b) →
    (∀ x : L, ∃ a b : R, b ≠ 0 ∧ x = j a / j b) →
    ∃! e : K ≃+* L, ∀ a : R, e (i a) = j a

def RingExtensionCriterion : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [IsDomain R] [CommRing S]
    (f : R →+* S),
    (∃ g : FractionRing R →+* S,
      g.comp (algebraMap R (FractionRing R)) = f) ↔
    ∀ b : R, b ≠ 0 → IsUnit (f b)

def RingExtensionUnique : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [IsDomain R] [CommRing S]
    (f : R →+* S) (g h : FractionRing R →+* S),
    g.comp (algebraMap R (FractionRing R)) = f →
    h.comp (algebraMap R (FractionRing R)) = f → g = h

/-- `s` is any unit representing the image of a nonzero denominator.
This expresses the inverse formula even when `S` has no global inverse operation. -/
def RingFractionFormula : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [IsDomain R] [CommRing S]
    (f : R →+* S) (g : FractionRing R →+* S),
    g.comp (algebraMap R (FractionRing R)) = f →
    ∀ (a b : R), b ≠ 0 → ∀ s : Sˣ, (s : S) = f b →
      g (algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b) =
        f a * (↑(s⁻¹) : S)

end Specs.D07.Ch08.FractionUniversal
