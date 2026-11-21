import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.CompletionInterface
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! Independent statements for the factor form of paper.tex, Theorem 7.8.
`IsAdicComplete I R` includes both completeness and separatedness.
No nontriviality assumption is made. -/
universe u
namespace P103.Specs.Ch07.HenselFactors
open Polynomial

/-- The ordered coefficient correction map, with strict degree bounds. -/
def correction_isomorphismType : Prop :=
  ∀ (R : Type u) [CommRing R] (g h : R[X]),
    g.Monic → h.Monic → IsCoprime g h →
    ∃ e : (degreeLT R g.natDegree × degreeLT R h.natDegree) ≃ₗ[R]
        degreeLT R (g.natDegree + h.natDegree),
      ∀ a b, (e (a, b)).val = a.val * h + b.val * g

/-- The full factor-lifting conclusion, including ordered uniqueness and degrees. -/
def factor_liftingType : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Ideal R) [IsAdicComplete I R]
      (f : R[X]) (g₀ h₀ : (R ⧸ I)[X]),
    f.Monic → g₀.Monic → h₀.Monic → IsCoprime g₀ h₀ →
    f.map (Ideal.Quotient.mk I) = g₀ * h₀ →
    ∃! p : R[X] × R[X],
      p.1.Monic ∧ p.2.Monic ∧ f = p.1 * p.2 ∧
      p.1.map (Ideal.Quotient.mk I) = g₀ ∧
      p.2.map (Ideal.Quotient.mk I) = h₀ ∧
      p.1.natDegree = g₀.natDegree ∧ p.2.natDegree = h₀.natDegree


def sylvesterMap_bijectiveType : Prop :=
  ∀ {R : Type u} [CommRing R] (g h : R[X])
    (hu : IsUnit (Polynomial.resultant g h)),
    Function.Bijective (sylvesterMap g h le_rfl le_rfl)


def coprime_of_coprime_reductionType : Prop :=
  ∀ {R : Type u} [CommRing R] (I : Ideal R)
    (hI : I ≤ Ideal.jacobson ⊥) (g h : R[X]) (hg : g.Monic) (hh : h.Monic)
    (hcop : IsCoprime (g.map (Ideal.Quotient.mk I)) (h.map (Ideal.Quotient.mk I))),
    IsCoprime g h


def factors_uniqueType : Prop :=
  ∀ {R : Type u} [CommRing R] (I : Ideal R)
    (hI : I ≤ Ideal.jacobson ⊥) (g h g' h' : R[X])
    (hg : g.Monic) (_hh : h.Monic) (hg' : g'.Monic) (hh' : h'.Monic)
    (hcop : IsCoprime (g.map (Ideal.Quotient.mk I)) (h.map (Ideal.Quotient.mk I)))
    (hprod : g * h = g' * h')
    (_hgr : g.map (Ideal.Quotient.mk I) = g'.map (Ideal.Quotient.mk I))
    (hhr : h.map (Ideal.Quotient.mk I) = h'.map (Ideal.Quotient.mk I))
    (hd : g.natDegree = g'.natDegree),
    g = g' ∧ h = h'


def monic_liftType : Prop :=
  ∀ {R : Type u} [CommRing R] (I : Ideal R)
    (g₀ : (R ⧸ I)[X]) (hg₀ : g₀.Monic),
    ∃ g : R[X], g.map (Ideal.Quotient.mk I) = g₀ ∧
      g.natDegree = g₀.natDegree ∧ g.Monic


def initial_liftsType : Prop :=
  ∀ {R : Type u} [CommRing R] (I : Ideal R)
    (f : R[X]) (g₀ h₀ : (R ⧸ I)[X])
    (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hf : f.map (Ideal.Quotient.mk I) = g₀ * h₀),
    ∃ g h : R[X], g.Monic ∧ h.Monic ∧
      g.map (Ideal.Quotient.mk I) = g₀ ∧ h.map (Ideal.Quotient.mk I) = h₀ ∧
      g.natDegree = g₀.natDegree ∧ h.natDegree = h₀.natDegree ∧
      ∀ k, (f - g * h).coeff k ∈ I


def degree_sumType : Prop :=
  ∀ {R : Type u} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (f : R[X]) (g₀ h₀ : (R ⧸ I)[X])
    (hf : f.Monic) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hred : f.map (Ideal.Quotient.mk I) = g₀ * h₀),
    f.natDegree = g₀.natDegree + h₀.natDegree

end P103.Specs.Ch07.HenselFactors
