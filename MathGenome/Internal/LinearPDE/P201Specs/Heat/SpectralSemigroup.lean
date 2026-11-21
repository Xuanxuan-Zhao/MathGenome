import MathGenome.Internal.LinearPDE.P201Specs.Heat.FormOperator
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.SelfAdjointSmoothing

/-! Heat evolution for the canonical form operator, on arbitrary real Hilbert
spaces. Time includes zero; only smoothing requires positive time. The spectral
exponential is identified through the isometric Hilbert complexification, as in
the manuscript. No compactness or separability is assumed. -/
noncomputable section
open scoped InnerProductSpace NNReal
universe u v
namespace P201.Heat.SpectralSemigroupExpected
open ExpandedFA.Semigroups ExpandedFA.Unbounded
open SelfAdjointSmoothing

variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The complexification of S is the actual spectral exponential of the
complexified canonical operator. `ComplexHeatRepresentation` asserts that a
PVM and its bounded realization represent the lifted operator by the coordinate
function, and represent U(t), with full domain, by z ↦ exp(-t*z).
The isometric inclusion intertwines this exponential with S on the real space.
Thus this is an identification with the spectral exponential, not merely a
choice of notation for an arbitrary semigroup. -/
def SpectralExponential (d : CoerciveForm V H) (S : C0Semigroup ℝ H) : Prop :=
  ∃ U : C0Semigroup ℂ (Complexification H),
    Spec.ComplexHeatRepresentation (Complexification.lift d.operator) U ∧
    ∀ (t : ℝ≥0) (x : H),
      Complexification.inclusion (S.operators t x) =
        U.operators t (Complexification.inclusion x)

/-- All conclusions concern the same S and the exact canonical partial
operator B. The shared power is recursively the partial product B ∘ B^m,
so the graph assertion includes every intermediate domain condition. -/
def HeatSemigroup (d : CoerciveForm V H) (S : C0Semigroup ℝ H) : Prop :=
  SpectralExponential d S ∧
  (∀ x : H, Continuous (fun t : ℝ≥0 => S.operators t x)) ∧
  (∀ t : ℝ≥0, IsSelfAdjoint (S.operators t) ∧ ‖S.operators t‖ ≤ 1) ∧
  C0SemigroupSpec.generatorValue S = -d.operator ∧
  (C0SemigroupSpec.generatorValue S).domain = d.operator.domain ∧
  (∀ (t : ℝ≥0), 0 < t → ∀ (m : ℕ), 1 ≤ m →
    (∀ x : H, S.operators t x ∈ (OperatorDomainsSpec.powerValue d.operator m).domain) ∧
    ∃ A : H →L[ℝ] H,
      (∀ x : H, (S.operators t x, A x) ∈
        (OperatorDomainsSpec.powerValue d.operator m).graph) ∧
      ‖A‖ ≤ ((m : ℝ) / (Real.exp 1 * (t : ℝ))) ^ m) ∧
  (∀ U : C0Semigroup ℝ H, C0SemigroupSpec.generatorValue U = -d.operator →
    ∀ t : ℝ≥0, U.operators t = S.operators t)

/-- The real heat semigroup and sharp power smoothing for every bounded
symmetric coercive form on a dense continuous Hilbert injection. -/
def SemigroupTheorem : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (d : CoerciveForm V H), ∃ S : C0Semigroup ℝ H, HeatSemigroup d S

end P201.Heat.SpectralSemigroupExpected
