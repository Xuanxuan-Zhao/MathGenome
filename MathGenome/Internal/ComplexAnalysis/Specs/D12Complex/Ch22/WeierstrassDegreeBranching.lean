import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.TorusSurface
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.HalfPeriodValues
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.MapsMultiplicity
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-! Degree and branching of the actual Weierstrass map (paper.tex:3941–3962).
The order is tested in every quotient disk coordinate, using the finite target
coordinate at finite values and the reciprocal coordinate at infinity. The
finitely supported fibre divisors express degree including ramified fibres. -/
noncomputable section
open Set
open scoped Classical

namespace Specs.D12Complex.Ch22.WeierstrassDegreeBranching
open _root_.D12Complex _root_.D12Complex.TorusSurface
open WeierstrassSeries (weierstrassP)
open HalfPeriodValues (halfPeriod branchValue)

/-- The genuine sphere values, disregarding scalar fillers at poles. -/
def planeMap (ω₁ ω₂ z : ℂ) : RiemannSphere :=
  if z ∈ lattice ω₁ ω₂ then sphereInfty else sphereFinite (weierstrassP ω₁ ω₂ z)

/-- The four specified classes. -/
def ramificationClasses (ω₁ ω₂ : ℂ) : Set (Torus ω₁ ω₂) :=
  {0} ∪ range (fun i => projection ω₁ ω₂ (halfPeriod ω₁ ω₂ i))

/-- The asserted multiplicities are verified by coordinate orders below. -/
def multiplicity (ω₁ ω₂ : ℂ) (q : Torus ω₁ ω₂) : ℕ :=
  if q ∈ ramificationClasses ω₁ ω₂ then 2 else 1

/-- Full conclusion, with no holomorphy or degree certificates in the hypotheses. -/
def degree_branching_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
  ∃ (d : ℝ) (S : Surfaces.RiemannSurface (Torus ω₁ ω₂))
    (F : Torus ω₁ ω₂ → RiemannSphere),
    Separation ω₁ ω₂ d ∧ S.atlas = quotientAtlas ω₁ ω₂ d ∧
    F ∘ projection ω₁ ω₂ = planeMap ω₁ ω₂ ∧
    Surfaces.SphereValuedHolomorphic S F ∧
    (∀ q, F q = sphereInfty ↔ q = 0) ∧
    (∀ i, F (projection ω₁ ω₂ (halfPeriod ω₁ ω₂ i)) =
      sphereFinite (branchValue ω₁ ω₂ i)) ∧
    (∀ e ∈ S.atlas, ∀ q ∈ e.val.source,
      (F q ≠ sphereInfty →
        analyticOrderAt (fun z => finiteCoordinate (F (e.val.symm z)) -
          finiteCoordinate (F q)) (e.val q) = (multiplicity ω₁ ω₂ q : ℕ∞)) ∧
      (F q = sphereInfty →
        analyticOrderAt (fun z => infinityCoordinate (F (e.val.symm z)))
          (e.val q) = (2 : ℕ∞))) ∧
    (∀ b : RiemannSphere, ∃ D : Torus ω₁ ω₂ →₀ ℕ,
      (∀ q, D q ≠ 0 ↔ F q = b) ∧
      (∀ q, F q = b → D q = multiplicity ω₁ ω₂ q) ∧
      D.sum (fun _ n => n) = 2) ∧
    ({q | 1 < multiplicity ω₁ ω₂ q} = ramificationClasses ω₁ ω₂) ∧
    (F '' {q | 1 < multiplicity ω₁ ω₂ q} =
      {sphereInfty} ∪ range (fun i => sphereFinite (branchValue ω₁ ω₂ i)))

end Specs.D12Complex.Ch22.WeierstrassDegreeBranching
