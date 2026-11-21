import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.QuadraticContinuedFractions

/-! The pure-period criterion of paper.tex, Theorem nt:E08
(lines 2458–2460 and 2529–2537), for the canonical zero-based digits. -/
namespace P203Specs

/-- A quadratic irrational has a period starting at its first digit exactly
when its value exceeds one and its intrinsic conjugate belongs to (-1,0). -/
def PurePeriodicityCriterion : Prop :=
  ∀ x : ℝ, QuadraticIrrational x →
    (PurelyPeriodicCF x ↔ ReducedQuadratic x)

end P203Specs
