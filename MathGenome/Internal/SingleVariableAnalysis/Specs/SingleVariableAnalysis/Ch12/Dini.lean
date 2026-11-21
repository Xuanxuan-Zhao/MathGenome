import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Uniform

/-!
Independent specification of K03.12.dini (paper.tex:1228–1237).

`K` is the compact domain itself. For a compact subset of a metric space,
use its subtype with the induced topology. `IsCompact univ` says exactly
that the domain is compact, including when it is empty. The statement is
valid for arbitrary topological domains, hence in particular all the
metric domains of the manuscript.

Monotonicity concerns the natural-number index at each fixed point;
there is no order or monotonicity assumption on the spatial domain.
Pointwise and uniform convergence use the previously fixed epsilon
predicates. As upstream, index `n` denotes manuscript term `n + 1`.
Continuity of the limiting real-valued function is an explicit hypothesis.
-/

namespace Specs.SingleVariableAnalysis.Ch12.Dini

universe u

def diniMonotone : Prop :=
  ∀ {K : Type u} [TopologicalSpace K],
    IsCompact (Set.univ : Set K) →
    ∀ (F : ℕ → K → ℝ) (f : K → ℝ),
      (∀ n, Continuous (F n)) → Continuous f →
      (∀ x, Monotone (fun n => F n x)) →
      Pointwise.realPointwiseConvergesValue F f →
      Uniform.realUniformConvergesValue F f

def diniAntitone : Prop :=
  ∀ {K : Type u} [TopologicalSpace K],
    IsCompact (Set.univ : Set K) →
    ∀ (F : ℕ → K → ℝ) (f : K → ℝ),
      (∀ n, Continuous (F n)) → Continuous f →
      (∀ x, Antitone (fun n => F n x)) →
      Pointwise.realPointwiseConvergesValue F f →
      Uniform.realUniformConvergesValue F f

/-- The two alternative directions in the source theorem. -/
def dini : Prop :=
  ∀ {K : Type u} [TopologicalSpace K],
    IsCompact (Set.univ : Set K) →
    ∀ (F : ℕ → K → ℝ) (f : K → ℝ),
      (∀ n, Continuous (F n)) → Continuous f →
      ((∀ x, Monotone (fun n => F n x)) ∨
        (∀ x, Antitone (fun n => F n x))) →
      Pointwise.realPointwiseConvergesValue F f →
      Uniform.realUniformConvergesValue F f

end Specs.SingleVariableAnalysis.Ch12.Dini
