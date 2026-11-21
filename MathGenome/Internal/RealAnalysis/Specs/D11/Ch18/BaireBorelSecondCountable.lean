import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.BorelBaire
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.CountablePrecompactBase

/-!
Independent statements for paper.tex:5354, `d11:18:baire-borel-second-countable`.
The Baire structure is exactly the Cc-real-generated structure fixed upstream.
All statements allow empty spaces and empty compact sets.
-/

open Set

universe u

namespace Specs.D11.Ch18.BaireBorelSecondCountable

/-- A single countable family of compact-support cutoffs generates all open sets
by countable unions of positivity sets. Support includes its closure. -/
def CountableCutoffGenerators : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X],
    ∃ F : Set (CompactlySupportedContinuousMap X ℝ), F.Countable ∧
      (∀ f ∈ F, ∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      ∀ U : Set X, IsOpen U →
        U = ⋃ f ∈ F, ⋃ (_ : closure {x | f x ≠ 0} ⊆ U), {x | 0 < f x}

/-- Equality for the precise Baire and Borel sigma-algebras in the source. -/
def BaireEqBorel : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X],
    Specs.D11.Ch18.BorelBaire.baireSpaceValue X =
      Specs.D11.Ch18.BorelBaire.borelSpaceValue X

/-- The full other conclusion of the source theorem, in ambient X. -/
def CompactGDelta : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    (K : Set X), IsCompact K →
    ∃ U : ℕ → Set X, (∀ n, IsOpen (U n)) ∧ K = ⋂ n, U n

end Specs.D11.Ch18.BaireBorelSecondCountable
