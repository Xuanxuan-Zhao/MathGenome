import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Flows.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Flows.CirculationDecomposition

/-! W47: exact decomposition of signed feasible flows, preserving original arcs.
The two path endpoints are explicit. Integer coefficients are actual integers,
with casts only at the comparison with the given real loads and value. -/
universe u v
namespace FiniteCombinatorics.Graph.Flows.PathCycleSpec
open FiniteCombinatorics.Directed
variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

noncomputable def pathContribution {R : Type*} [Zero R] {G : Digraph V A}
    {s t : V} (w : R) (p : Directed.Spec.path G s t) (a : A) : R := by
  classical
  exact if a ∈ Directed.Spec.arcs p.val then w else 0

/-- All weights are strictly positive; lists provide finite indexed families. -/
def Decomposes {R : Type*} [AddCommMonoid R] [LT R] {G : Digraph V A}
    {s t : V} (f : A → R) (r : R)
    (ps : List (R × Directed.Spec.path G s t))
    (cs : List (R × Directed.Spec.cycle G)) : Prop :=
  (∀ p ∈ ps, 0 < p.1) ∧ (∀ c ∈ cs, 0 < c.1) ∧
  (ps.map Prod.fst).sum = r ∧
  ∀ a, f a = (ps.map fun p => pathContribution p.1 p.2 a).sum +
    (cs.map fun c => CirculationSpec.contribution c.1 c.2 a).sum

def IntegralDecomposes {G : Digraph V A} {s t : V} (f : A → ℝ) (r : ℝ)
    (ps : List (ℤ × Directed.Spec.path G s t))
    (cs : List (ℤ × Directed.Spec.cycle G)) : Prop :=
  (∀ p ∈ ps, 0 < p.1) ∧ (∀ c ∈ cs, 0 < c.1) ∧
  (((ps.map Prod.fst).sum : ℤ) : ℝ) = r ∧
  ∀ a, f a = (((ps.map fun p => pathContribution p.1 p.2 a).sum +
    (cs.map fun c => CirculationSpec.contribution c.1 c.2 a).sum : ℤ) : ℝ)

def real_decomposition : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ), Spec.feasible N f →
    (0 < Spec.value N f → ∃ ps cs,
      Decomposes (s := N.source) (t := N.sink) (G := N.graph) f (Spec.value N f) ps cs) ∧
    (Spec.value N f = 0 → ∃ cs, CirculationSpec.Decomposes (G := N.graph) f cs) ∧
    (Spec.value N f < 0 → ∃ ps cs,
      Decomposes (s := N.sink) (t := N.source) (G := N.graph) f (-Spec.value N f) ps cs)

def integer_decomposition : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ), Spec.feasible N f →
    (∀ a, ∃ z : ℤ, (z : ℝ) = f a) →
    (0 < Spec.value N f → ∃ ps cs,
      IntegralDecomposes (s := N.source) (t := N.sink) (G := N.graph)
        f (Spec.value N f) ps cs) ∧
    (Spec.value N f = 0 → ∃ cs : List (ℤ × Directed.Spec.cycle N.graph),
      (∀ c ∈ cs, 0 < c.1) ∧ ∀ a,
        f a = ((cs.map fun c => CirculationSpec.contribution c.1 c.2 a).sum : ℤ)) ∧
    (Spec.value N f < 0 → ∃ ps cs,
      IntegralDecomposes (s := N.sink) (t := N.source) (G := N.graph)
        f (-Spec.value N f) ps cs)
end FiniteCombinatorics.Graph.Flows.PathCycleSpec
