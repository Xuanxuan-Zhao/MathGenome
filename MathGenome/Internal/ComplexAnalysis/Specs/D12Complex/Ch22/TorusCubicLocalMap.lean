import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.TorusSurface
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.CubicInfinityChart
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.WeierstrassPeriods

/-! The local analytic part of paper.tex:3948–3954,3996–4005.
The cubic has its literal projective subspace topology. No connectedness,
global bijectivity, or inverse to the whole map is presupposed here. -/
noncomputable section
open Set Filter
open scoped Topology

namespace D12Complex.TorusCubicLocalMap
open TorusSurface CubicFiniteCharts CubicInfinityChart
open Specs.D12Complex.Ch22.WeierstrassSeries (weierstrassP)

/-- The plane formula, with the entire lattice mapped to [0:0:1]. -/
def planeMap (ω₁ ω₂ z : ℂ) : ProjectivePlaneTopology.ComplexProjectivePlane := by
  classical
  exact if z ∈ lattice ω₁ ω₂ then O else
    affinePoint (weierstrassP ω₁ ω₂ z) (deriv (weierstrassP ω₁ ω₂) z)

/-- A representative-based definition; independence is a theorem below. -/
def phi (ω₁ ω₂ : ℂ) (t : Torus ω₁ ω₂) :
    ProjectivePlaneTopology.ComplexProjectivePlane :=
  planeMap ω₁ ω₂ (Quotient.out t)

/-- The actual finite and infinity coordinates constructed upstream. -/
def IsCubicChart (G H : ℂ) (e : OpenPartialHomeomorph (Cubic G H) ℂ) : Prop :=
  IsInfinityChart G H e ∨ ∃ axis, IsFiniteChart G H axis e

/-- A plane-coordinate local inverse, including its open source and target,
the actual image in the cubic chart, and holomorphy of both inverse maps. -/
def PlaneLocalInverseAt {G H : ℂ} (F : ℂ → Cubic G H) (a : ℂ) : Prop :=
  ∃ e : OpenPartialHomeomorph (Cubic G H) ℂ, IsCubicChart G H e ∧
    ∃ (U V : Set ℂ) (h : ℂ → ℂ), a ∈ U ∧ MapsTo F U e.source ∧
      BiholomorphicPair U V (e ∘ F) h

/-- Local biholomorphy in genuine torus and cubic coordinates. The source
coordinate is a small-disk quotient chart; U can be a smaller open neighborhood.
The displayed pair is the coordinate expression of F and its holomorphic inverse.
Thus this also asserts local holomorphy, with no derivative continuity assumption. -/
def QuotientLocalInverseAt {ω₁ ω₂ G H : ℂ}
    (F : Torus ω₁ ω₂ → Cubic G H) (t : Torus ω₁ ω₂) : Prop :=
  ∃ d : ℝ, Separation ω₁ ω₂ d ∧
    ∃ s ∈ quotientAtlas ω₁ ω₂ d, t ∈ s.val.source ∧
      ∃ e : OpenPartialHomeomorph (Cubic G H) ℂ, IsCubicChart G H e ∧
        ∃ (U V : Set ℂ) (h : ℂ → ℂ), s.val t ∈ U ∧ U ⊆ s.val.target ∧
          MapsTo (F ∘ s.val.symm) U e.source ∧
          BiholomorphicPair U V (e ∘ F ∘ s.val.symm) h

end D12Complex.TorusCubicLocalMap

namespace Specs.D12Complex.Ch22.TorusCubicLocalMap
open _root_.D12Complex _root_.D12Complex.TorusCubicLocalMap
open _root_.D12Complex.TorusSurface _root_.D12Complex.CubicFiniteCharts
open _root_.D12Complex.CubicInfinityChart
open WeierstrassSeries (weierstrassP)
open WeierstrassEquations (g₂ g₃)

def planeMap_type := ℂ → ℂ → ℂ → _root_.D12Complex.ProjectivePlaneTopology.ComplexProjectivePlane
def planeMap_value : planeMap_type := by
  classical
  exact fun ω₁ ω₂ z => if z ∈ lattice ω₁ ω₂ then O else
    affinePoint (weierstrassP ω₁ ω₂ z) (deriv (weierstrassP ω₁ ω₂) z)
def phi_type := (ω₁ ω₂ : ℂ) → Torus ω₁ ω₂ →
  _root_.D12Complex.ProjectivePlaneTopology.ComplexProjectivePlane
def phi_value : phi_type := fun ω₁ ω₂ t => planeMap ω₁ ω₂ (Quotient.out t)

def periodic_type : Prop := ∀ ω₁ ω₂ : ℂ,
  ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → Periodic ω₁ ω₂ (planeMap ω₁ ω₂)

def projection_formula_type : Prop := ∀ ω₁ ω₂ : ℂ,
  ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → ∀ z : ℂ,
    phi ω₁ ω₂ (projection ω₁ ω₂ z) = planeMap ω₁ ω₂ z

def formulas_type : Prop := ∀ ω₁ ω₂ : ℂ,
  ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    (∀ z ∉ lattice ω₁ ω₂, phi ω₁ ω₂ (projection ω₁ ω₂ z) =
      affinePoint (weierstrassP ω₁ ω₂ z) (deriv (weierstrassP ω₁ ω₂) z)) ∧
    phi ω₁ ω₂ 0 = O ∧
    ∀ t, OnCubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) (phi ω₁ ω₂ t)

/-- The unique map into the actual cubic, rather than just its ambient space. -/
def construction_type : Prop := ∀ ω₁ ω₂ : ℂ,
  ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∃! F : Torus ω₁ ω₂ → Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂),
      ∀ t, (F t).val = phi ω₁ ω₂ t

/-- The analytic extension in both ambient infinity coordinates, including
the quantitative orders and the nonzero coordinate derivative. -/
def infinity_bridge_type : Prop := ∀ ω₁ ω₂ : ℂ,
  ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ F : Torus ω₁ ω₂ → Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂),
      (∀ t, (F t).val = phi ω₁ ω₂ t) →
      ∃ u v : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ AnalyticAt ℂ v 0 ∧
        u 0 = 0 ∧ v 0 = 0 ∧ HasDerivAt u (-1 / 2) 0 ∧
        (∀ᶠ z in 𝓝[≠] (0 : ℂ),
          u z = weierstrassP ω₁ ω₂ z / deriv (weierstrassP ω₁ ω₂) z ∧
          v z = 1 / deriv (weierstrassP ω₁ ω₂) z) ∧
        Asymptotics.IsBigO (𝓝 (0 : ℂ)) (fun z => u z + z / 2) (fun z => z ^ 5) ∧
        Asymptotics.IsBigO (𝓝 (0 : ℂ)) (fun z => v z + z ^ 3 / 2) (fun z => z ^ 7) ∧
        (∀ᶠ z in 𝓝 (0 : ℂ),
          (F (projection ω₁ ω₂ z)).val = infinityPoint (u z) (v z))

/-- At a finite point use x exactly when wp' is nonzero, and y otherwise. -/
def finite_local_type : Prop := ∀ ω₁ ω₂ : ℂ,
  ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ F : Torus ω₁ ω₂ → Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂),
      (∀ t, (F t).val = phi ω₁ ω₂ t) → ∀ a ∉ lattice ω₁ ω₂,
      ∃ e : OpenPartialHomeomorph (Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂)) ℂ,
        IsFiniteChart (g₂ ω₁ ω₂) (g₃ ω₁ ω₂)
          (if deriv (weierstrassP ω₁ ω₂) a = 0 then false else true) e ∧
        ∃ (U V : Set ℂ) (h : ℂ → ℂ), a ∈ U ∧
          MapsTo (F ∘ projection ω₁ ω₂) U e.source ∧
          BiholomorphicPair U V (e ∘ F ∘ projection ω₁ ω₂) h

/-- Holomorphic local inverses at every torus point, including the pole class.
There is no assumption of global injectivity, surjectivity, or connectedness of E. -/
def locally_biholomorphic_type : Prop := ∀ ω₁ ω₂ : ℂ,
  ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
    ∀ F : Torus ω₁ ω₂ → Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂),
      (∀ t, (F t).val = phi ω₁ ω₂ t) →
      Continuous F ∧ ∀ t, QuotientLocalInverseAt F t

end Specs.D12Complex.Ch22.TorusCubicLocalMap
