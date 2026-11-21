import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Noetherian.Defs

/-!
Independent statements for paper.tex, Lemma SN-05 (lines 4163–4173).
The Noetherian hypothesis is the chapter convention at line 4039.
`L ≠ ⊥` says that the submodule is nonzero, and `L.FG` means finite
generation over `A`. Stability is stated as multiplication in the fraction
field. `IsIntegral` itself means the existence of a monic polynomial equation;
the second statement makes that witness explicit for downstream use.
-/

namespace Specs.AdvCommAlg.Normality

def FractionalDeterminantTest : Prop :=
  ∀ (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Submodule A K), L ≠ ⊥ → L.FG →
    ∀ u : K, (∀ v ∈ L, u * v ∈ L) → IsIntegral A u

def FractionalDeterminantTestMonic : Prop :=
  ∀ (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Submodule A K), L ≠ ⊥ → L.FG →
    ∀ u : K, (∀ v ∈ L, u * v ∈ L) →
      ∃ p : Polynomial A, p.Monic ∧ p.eval₂ (algebraMap A K) u = 0

end Specs.AdvCommAlg.Normality
