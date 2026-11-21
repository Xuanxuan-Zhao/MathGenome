import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.Meromorphic
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch10.TriplesCrossRatio

/-!
Independent statements for the entire-plane assertion of paper.tex:4320–4339,
D12.23.06. The plane-to-sphere holomorphy predicate admits the constant infinity
map. The scalar meromorphic predicate retains the source convention excluding
that map. The omitted values are fixed sphere points, with all infinity cases
included in the canonical cross-ratio normalization.
-/

noncomputable section

namespace Specs.D12Complex.Ch23.MeromorphicLittlePicard
open _root_.D12Complex _root_.D12Complex.Mobius

/-- One fixed normalized Möbius map makes the sphere map an entire scalar
function omitting zero and one. The equality records the actual sphere values. -/
def normalized_entire_type : Prop :=
  ∀ (F : ℂ → RiemannSphere) (p q r : RiemannSphere),
    PlaneSphereHolomorphicOn Set.univ F → p ≠ q → p ≠ r → q ≠ r →
    (∀ z : ℂ, F z ≠ p) → (∀ z : ℂ, F z ≠ q) → (∀ z : ℂ, F z ≠ r) →
    let G : ℂ → RiemannSphere := fun z => crossRatio (F z) p q r
    HolomorphicOn Set.univ (scalarFinitePart G) ∧
      (∀ z : ℂ, G z = sphereFinite (scalarFinitePart G z)) ∧
      (∀ z : ℂ, scalarFinitePart G z ≠ 0) ∧
      (∀ z : ℂ, scalarFinitePart G z ≠ 1)

/-- Meromorphic maps from the whole plane omitting three distinct sphere
values are constant; the constant is allowed to be infinity. -/
def sphere_little_picard_type : Prop :=
  ∀ (F : ℂ → RiemannSphere) (p q r : RiemannSphere),
    PlaneSphereHolomorphicOn Set.univ F → p ≠ q → p ≠ r → q ≠ r →
    (∀ z : ℂ, F z ≠ p) → (∀ z : ℂ, F z ≠ q) → (∀ z : ℂ, F z ≠ r) →
    ∃ c : RiemannSphere, ∀ z : ℂ, F z = c

/-- With the scalar meromorphic convention the resulting constant is finite. -/
def scalar_little_picard_type : Prop :=
  ∀ (F : ℂ → RiemannSphere) (p q r : RiemannSphere),
    ScalarMeromorphicOn Set.univ F → p ≠ q → p ≠ r → q ≠ r →
    (∀ z : ℂ, F z ≠ p) → (∀ z : ℂ, F z ≠ q) → (∀ z : ℂ, F z ≠ r) →
    ∃ c : ℂ, ∀ z : ℂ, F z = sphereFinite c

end Specs.D12Complex.Ch23.MeromorphicLittlePicard
