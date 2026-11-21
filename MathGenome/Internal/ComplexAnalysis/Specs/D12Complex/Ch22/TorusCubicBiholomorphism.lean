import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.TorusCubicLocalMap
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.WeierstrassDegreeBranching

/-! The complete lattice-associated cubic identification, paper.tex:3941–4013.
All spaces, functions, coordinate charts and topologies are the shared literal
objects. The inverse in the final coordinate formula is the global inverse of
the displayed homeomorphism, rather than a separately assumed inverse branch.
The target surface retains the finite/infinity atlas constructed on the cubic.
No converse uniformization or choice of a different abstract cubic is made. -/
noncomputable section
open Set

namespace Specs.D12Complex.Ch22.TorusCubicBiholomorphism
open _root_.D12Complex _root_.D12Complex.TorusSurface
open _root_.D12Complex.CubicFiniteCharts _root_.D12Complex.CubicInfinityChart
open _root_.D12Complex.TorusCubicLocalMap _root_.D12Complex.Surfaces
open _root_.D12Complex.ProjectivePlaneTopology (HomogeneousVector)
open WeierstrassSeries (weierstrassP)
open WeierstrassEquations (g₂ g₃)

/-- The three actual partial derivatives of the homogeneous cubic cannot all
vanish on its nonzero homogeneous representatives. Coordinate order is Z,X,Y. -/
def nonsingular_type : Prop := ∀ ω₁ ω₂ : ℂ,
  ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → ∀ v : HomogeneousVector,
    homogeneousEquation (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) v.val = 0 →
      v.val 2 ^ 2 + 2 * g₂ ω₁ ω₂ * v.val 1 * v.val 0 +
        3 * g₃ ω₁ ω₂ * v.val 0 ^ 2 ≠ 0 ∨
      -12 * v.val 1 ^ 2 + g₂ ω₁ ω₂ * v.val 0 ^ 2 ≠ 0 ∨
      2 * v.val 2 * v.val 0 ≠ 0

/-- Finite fibres consist precisely of a class and its negative, including
coincident classes at the nonzero half-periods. No scalar filler at a pole is used. -/
def fibre_separation_type : Prop := ∀ ω₁ ω₂ : ℂ,
  ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → ∀ z w : ℂ,
    z ∉ lattice ω₁ ω₂ → w ∉ lattice ω₁ ω₂ →
      (weierstrassP ω₁ ω₂ z = weierstrassP ω₁ ω₂ w ↔
        projection ω₁ ω₂ w = projection ω₁ ω₂ z ∨
        projection ω₁ ω₂ w = -projection ω₁ ω₂ z)

/-- The odd derivative distinguishes the two finite classes. At a half-period
its zero forces the two classes to coincide. -/
def derivative_separation_type : Prop := ∀ ω₁ ω₂ : ℂ,
  ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    (∀ z w : ℂ, z ∉ lattice ω₁ ω₂ → w ∉ lattice ω₁ ω₂ →
      (weierstrassP ω₁ ω₂ z = weierstrassP ω₁ ω₂ w ∧
        deriv (weierstrassP ω₁ ω₂) z = deriv (weierstrassP ω₁ ω₂) w ↔
          projection ω₁ ω₂ w = projection ω₁ ω₂ z)) ∧
    (∀ z : ℂ, z ∉ lattice ω₁ ω₂ →
      (deriv (weierstrassP ω₁ ω₂) z = 0 ↔
        projection ω₁ ω₂ z = -projection ω₁ ω₂ z))

/-- The pole case is separate from finite scalar evaluations. -/
def pole_fibre_type : Prop := ∀ ω₁ ω₂ : ℂ,
  ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → ∀ t : Torus ω₁ ω₂,
    phi ω₁ ω₂ t = O ↔ t = 0

/-- Every affine cubic point is attained with exactly its specified ordinate,
and every point of the literal projective cubic is attained, including O. -/
def surjectivity_type : Prop := ∀ ω₁ ω₂ : ℂ,
  ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    (∀ x y : ℂ, y ^ 2 = q (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) x →
      ∃ z : ℂ, z ∉ lattice ω₁ ω₂ ∧ weierstrassP ω₁ ω₂ z = x ∧
        deriv (weierstrassP ω₁ ω₂) z = y) ∧
    ∀ p : Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂),
      ∃ t : Torus ω₁ ω₂, phi ω₁ ω₂ t = p.val

/-- The full upstream degree-two, order and branch-value conclusion is retained. -/
def degree_branching_type : Prop :=
  WeierstrassDegreeBranching.degree_branching_type

/-- The genuine analytic extension in both infinity coordinates and its
nonzero derivative are retained, including the specified remainder orders. -/
def infinity_bridge_type : Prop := TorusCubicLocalMap.infinity_bridge_type

/-- A global biholomorphism expressed in actual quotient-disk and cubic
coordinates. In every neighborhood both coordinate maps are holomorphic and
mutually inverse, and the inverse is literally that of the global homeomorphism.
The surface witnesses retain the natural atlases; compactness and connectedness
of the literal cubic are conclusions, never hypotheses. -/
def biholomorphism_type : Prop := ∀ ω₁ ω₂ : ℂ,
  ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∃ (d : ℝ) (S : RiemannSurface (Torus ω₁ ω₂))
      (T : RiemannSurface (Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂)))
      (h : Torus ω₁ ω₂ ≃ₜ Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂)),
      Separation ω₁ ω₂ d ∧ S.atlas = quotientAtlas ω₁ ω₂ d ∧
      CompactSpace (Torus ω₁ ω₂) ∧ CompactSpace (Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂)) ∧
      (∀ e ∈ T.atlas, IsCubicChart (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) e.val) ∧
      (∀ t, (h t).val = phi ω₁ ω₂ t) ∧
      HolomorphicMap S T h ∧ HolomorphicMap T S h.symm ∧
      ∀ t, ∃ d' : ℝ, Separation ω₁ ω₂ d' ∧
        ∃ s ∈ quotientAtlas ω₁ ω₂ d', t ∈ s.val.source ∧
          ∃ e : OpenPartialHomeomorph (Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂)) ℂ,
            IsCubicChart (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) e ∧
            ∃ U V : Set ℂ, s.val t ∈ U ∧ U ⊆ s.val.target ∧ V ⊆ e.target ∧
              MapsTo (h ∘ s.val.symm) U e.source ∧
              BiholomorphicPair U V (e ∘ h ∘ s.val.symm)
                (s.val ∘ h.symm ∘ e.symm)

end Specs.D12Complex.Ch22.TorusCubicBiholomorphism
