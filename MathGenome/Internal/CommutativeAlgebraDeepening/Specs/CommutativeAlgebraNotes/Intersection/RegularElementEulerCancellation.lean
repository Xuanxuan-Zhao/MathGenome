import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

noncomputable section

open P103.Specs.Ch10.Comparison (LeftResolution)
open CommutativeAlgebraNotes.Intersection.IsolatedTorSupport.Specs (Tor)
open CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler.Specs
  (cutoffEuler intersectionEuler)

open scoped TensorProduct nonZeroDivisors

namespace CommutativeAlgebraNotes.Intersection.RegularElementEulerCancellation.Specs

universe u v w

abbrev QuotientRing {S : Type u} [CommRing S] (h : S) :=
  S ⧸ Ideal.span ({h} : Set S)

abbrev restrict {S : Type u} [CommRing S] (h : S) (M : ModuleCat.{v} (QuotientRing h)) :
    ModuleCat.{v} S :=
  (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span ({h} : Set S)))).obj M

/-- A free resolution by finitely generated modules, supported in degrees at most `d`. -/
def IsBoundedFiniteFree {R : Type u} [CommRing R] {M : ModuleCat.{v} R}
    (P : LeftResolution R M) (d : ℕ) : Prop :=
  P.IsFree ∧ (∀ i, Module.Finite R (P.complex.X i)) ∧
    (∀ i : ℕ, d < i → Subsingleton (P.complex.X i))

def torFiniteLength : Prop :=
  ∀ {S : Type u} [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    (h : S) (M : ModuleCat.{v} (QuotientRing h)) (N : ModuleCat.{w} (QuotientRing h))
    [Module.Finite (QuotientRing h) M] [Module.Finite (QuotientRing h) N],
    IsFiniteLength (QuotientRing h) (M ⊗[QuotientRing h] N) →
    ∀ i, IsFiniteLength S (Tor (restrict h M) (restrict h N) i)

def torVanishesAbove : Prop :=
  ∀ {S : Type u} [CommRing S] (h : S)
    (M : ModuleCat.{v} (QuotientRing h)) (N : ModuleCat.{w} (QuotientRing h))
    (Q : LeftResolution S (restrict h N)) (q : ℕ),
    IsBoundedFiniteFree Q q →
    ∀ i : ℕ, q < i → Subsingleton (Tor (restrict h M) (restrict h N) i)

def cutoffEulerZero : Prop :=
  ∀ {S : Type u} [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    (h : S), h ∈ IsLocalRing.maximalIdeal S → h ∈ S⁰ →
    ∀ (M : ModuleCat.{v} (QuotientRing h)) (N : ModuleCat.{w} (QuotientRing h))
    [Module.Finite (QuotientRing h) M] [Module.Finite (QuotientRing h) N],
    IsFiniteLength (QuotientRing h) (M ⊗[QuotientRing h] N) →
    ∀ (P : LeftResolution (QuotientRing h) M) (Q : LeftResolution S (restrict h N))
      (p q : ℕ), IsBoundedFiniteFree P p → IsBoundedFiniteFree Q q →
    ∀ d : ℕ, (∀ i : ℕ, d < i → Subsingleton (Tor (restrict h M) (restrict h N) i)) →
      cutoffEuler (restrict h M) (restrict h N) d = 0

def intersectionEulerZero : Prop :=
  ∀ {S : Type u} [CommRing S] [IsRegularLocalRing S]
    (h : S), h ∈ IsLocalRing.maximalIdeal S → h ∈ S⁰ →
    ∀ (M : ModuleCat.{v} (QuotientRing h)) (N : ModuleCat.{w} (QuotientRing h))
    [Module.Finite (QuotientRing h) M] [Module.Finite (QuotientRing h) N],
    IsFiniteLength (QuotientRing h) (M ⊗[QuotientRing h] N) →
    ∀ (P : LeftResolution (QuotientRing h) M) (Q : LeftResolution S (restrict h N))
      (p q : ℕ), IsBoundedFiniteFree P p → IsBoundedFiniteFree Q q →
      intersectionEuler (restrict h M) (restrict h N) = 0

end CommutativeAlgebraNotes.Intersection.RegularElementEulerCancellation.Specs
