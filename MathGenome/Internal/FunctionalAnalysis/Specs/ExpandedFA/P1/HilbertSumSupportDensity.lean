import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02HilbertSum

/-! Independent statements for the support and density clauses of
Proposition `fa2:p1:c02:hilbert-sum-complete` (paper.tex 497–513, support and density clauses).

These clauses hold for normed additive groups, and hence for every family of
real or complex Hilbert spaces. The index type is arbitrary, including empty
and uncountable types; completeness of the summands is unnecessary here.
All objects are the canonical ones fixed by the upstream direct-sum interface.
-/

open scoped ENNReal Classical

universe u v

namespace ExpandedFA.P1.HilbertSumSupportDensity.Spec

open ExpandedFA.P1.C02HilbertSum.Spec

/-- Every direct-sum vector has at most countably many nonzero coordinates. -/
def countable_support_type : Prop :=
  ∀ {I : Type u} {H : I → Type v} [∀ i, NormedAddCommGroup (H i)],
  ∀ x : Space H, Set.Countable {i | x i ≠ 0}

/-- The truncation net is indexed by all finite subsets ordered by inclusion. -/
def tendsto_truncate_type : Prop :=
  ∀ {I : Type u} {H : I → Type v} [∀ i, NormedAddCommGroup (H i)],
  ∀ x : Space H,
    Filter.Tendsto (fun A : Finset I => truncate H A (fun i => x i))
      Filter.atTop (nhds x)

/-- Every positive tolerance is achieved by a finite coordinate truncation. -/
def exists_finite_truncation_type : Prop :=
  ∀ {I : Type u} {H : I → Type v} [∀ i, NormedAddCommGroup (H i)],
  ∀ (x : Space H) (ε : ℝ), 0 < ε →
    ∃ A : Finset I, ‖x - truncate H A (fun i => x i)‖ < ε

/-- Finite-support vectors are dense in the norm topology of the direct sum. -/
def dense_finiteSupport_type : Prop :=
  ∀ {I : Type u} (H : I → Type v) [∀ i, NormedAddCommGroup (H i)],
    Dense (finiteSupport H)

end ExpandedFA.P1.HilbertSumSupportDensity.Spec
