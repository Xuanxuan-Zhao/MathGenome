import Mathlib.Topology.UnitInterval

/-!
Independent specification of paper.tex, `d10:18:peano` (Corollary 18.5).
The interval is the actual closed real interval with its subspace topology.
The finite cube has the finite product of those subspace topologies; the
square is also stated in the usual pair representation. These are existence
statements, with no prescribed construction of the curve.
-/

open Set

namespace Specs.D10Topology.Ch18.Peano

def peano_cube : Prop :=
  ∀ (m : ℕ), 1 ≤ m →
    ∃ f : Icc (0 : ℝ) 1 → (Fin m → Icc (0 : ℝ) 1),
      Continuous f ∧ Function.Surjective f

def peano_square : Prop :=
  ∃ f : Icc (0 : ℝ) 1 → (Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1),
    Continuous f ∧ Function.Surjective f

end Specs.D10Topology.Ch18.Peano
