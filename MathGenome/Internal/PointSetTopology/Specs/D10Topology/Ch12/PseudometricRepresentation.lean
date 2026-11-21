import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.PseudometricFamilies

/-! The arbitrary-uniformity part of paper.tex,
`d10:12:pseudometric-representation` (lines 1653–1664).
Distances are finite real numbers. Uniform continuity and continuity below use
the original uniformity and its induced product topology: the new pseudometric
is never installed as an instance on X. No countability, separation or
nonemptiness hypothesis is imposed. -/

open Set Filter
open scoped Uniformity
universe u

namespace Specs.D10Topology.Ch12.PseudometricRepresentation

/-- A bounded pseudometric subordinate to any specified original entourage.
Every positive distance test is an original entourage, and the fixed radius
1/4 test refines the specified entourage. -/
def entourage_pseudometric : Prop :=
  ∀ {X : Type u} [UniformSpace X] (U : Set (X × X)), U ∈ 𝓤 X →
    ∃ p : PseudoMetricSpace X,
      (∀ x y, @dist X p.toDist x y ≤ 1) ∧
      UniformContinuous (fun q : X × X => @dist X p.toDist q.1 q.2) ∧
      Continuous (fun q : X × X => @dist X p.toDist q.1 q.2) ∧
      (∀ ε : ℝ, 0 < ε → {q | @dist X p.toDist q.1 q.2 < ε} ∈ 𝓤 X) ∧
      {q | @dist X p.toDist q.1 q.2 < (1 / 4 : ℝ)} ⊆ U

/-- One pseudometric for each original entourage gives exactly the original
uniform structure, using the previously specified finite-intersection family
construction. The indexed refinement clause also makes the witness usable
without choosing a finite intersection. -/
def pseudometric_representation : Prop :=
  ∀ {X : Type u} [uX : UniformSpace X],
    ∃ p : {U : Set (X × X) // U ∈ 𝓤 X} → PseudoMetricSpace X,
      (∀ U,
        (∀ x y, @dist X (p U).toDist x y ≤ 1) ∧
        UniformContinuous (fun q : X × X => @dist X (p U).toDist q.1 q.2) ∧
        Continuous (fun q : X × X => @dist X (p U).toDist q.1 q.2) ∧
        (∀ ε : ℝ, 0 < ε → {q | @dist X (p U).toDist q.1 q.2 < ε} ∈ 𝓤 X) ∧
        {q | @dist X (p U).toDist q.1 q.2 < (1 / 4 : ℝ)} ⊆ U.val) ∧
      PseudometricFamilies.familyUniformity p = uX

/-- The empty space is represented by its zero pseudometric, with the same
degenerate uniformity. This is also a specialization of the general result. -/
def empty_pseudometric_representation : Prop :=
  ∀ {X : Type u} [IsEmpty X] [uX : UniformSpace X],
    (PseudometricFamilies.zeroPseudometric X).toUniformSpace = uX ∧
    UniformContinuous (fun _q : X × X => (0 : ℝ)) ∧
    Continuous (fun _q : X × X => (0 : ℝ))

end Specs.D10Topology.Ch12.PseudometricRepresentation
