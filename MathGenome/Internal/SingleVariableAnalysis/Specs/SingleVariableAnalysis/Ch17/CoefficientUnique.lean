import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.AsymptoticScale

/-!
Independent specification of K03.17.coefficient_unique, paper.tex:4321–4334.
A fixed nontrivial approach, eventual nonvanishing, and adjacent little-o
comparisons are exactly the upstream scale hypotheses. Finite expansions
include indices 0 through m. All-orders uniqueness concerns coefficients of
the same function; no uniqueness assertion about functions is made.
The normed-field formulation includes the canonical real and complex scalars.
-/

namespace Specs.SingleVariableAnalysis.Ch17.CoefficientUnique

open Filter
open AsymptoticScale
universe u v

def expansionThroughCoefficientsUnique : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K]
    (l : Filter X) (φ : ℕ → X → K) (a b : ℕ → K) (f : X → K) (m : ℕ),
    isScalarAsymptoticScaleValue l φ →
    hasScalarExpansionThroughValue l φ a f m →
    hasScalarExpansionThroughValue l φ b f m →
    ∀ j, j ≤ m → a j = b j

def asymptoticExpansionCoefficientsUnique : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K]
    (l : Filter X) (φ : ℕ → X → K) (a b : ℕ → K) (f : X → K),
    isScalarAsymptoticScaleValue l φ →
    hasScalarAsymptoticExpansionValue l φ a f →
    hasScalarAsymptoticExpansionValue l φ b f → a = b

end Specs.SingleVariableAnalysis.Ch17.CoefficientUnique
