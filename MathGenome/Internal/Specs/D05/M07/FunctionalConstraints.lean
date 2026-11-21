import MathGenome.Internal.Specs.D05.M07.Dual
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Module.Submodule.Ker

/-!
Independent specifications for K05.07.functional_constraints
(paper.tex:1109–1117).

The finite list is indexed by `Fin r`, so repeated occurrences are permitted.
The ambient space is arbitrary. All duals are algebraic, over the same field,
and no dimension, continuity, or conjugation assumptions enter the statements.
The intersection is a submodule of V, while the span is a submodule of its dual.
-/

namespace Specs.D05.M07.FunctionalConstraints

/-- A homogeneous constraint is redundant exactly when its functional lies in
the span of the given rows. This includes the empty list. -/
def mem_span_iff_iInf_ker_le : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (r : ℕ) (f : Fin r → Module.Dual K V) (g : Module.Dual K V),
    g ∈ Submodule.span K (Set.range f) ↔
      (⨅ i, LinearMap.ker (f i)) ≤ LinearMap.ker g

/-- The same statement with simultaneous vanishing written pointwise. -/
def mem_span_iff_vanishes : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (r : ℕ) (f : Fin r → Module.Dual K V) (g : Module.Dual K V),
    g ∈ Submodule.span K (Set.range f) ↔
      ∀ v : V, (∀ i, f i v = 0) → g v = 0

/-- Vanishing on the common kernel yields exactly the finite coefficient
formula from the source, with one coefficient for each row occurrence. -/
def exists_coefficients_iff_vanishes : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (r : ℕ) (f : Fin r → Module.Dual K V) (g : Module.Dual K V),
    (∃ a : Fin r → K, ∀ v : V, g v = ∑ i, a i * f i v) ↔
      ∀ v : V, (∀ i, f i v = 0) → g v = 0

/-- With no given rows the span is zero, the intersection is all of V,
and each of the two conditions says that g is the zero functional. -/
def empty_constraints : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : Fin 0 → Module.Dual K V) (g : Module.Dual K V),
    Submodule.span K (Set.range f) = ⊥ ∧
      (⨅ i, LinearMap.ker (f i)) = ⊤ ∧
      (g ∈ Submodule.span K (Set.range f) ↔ g = 0) ∧
      ((⨅ i, LinearMap.ker (f i)) ≤ LinearMap.ker g ↔ g = 0)

end Specs.D05.M07.FunctionalConstraints
