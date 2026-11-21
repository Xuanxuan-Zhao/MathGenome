import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.LatticeGeometry
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.Surfaces
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Meromorphic.Basic

noncomputable section
open Set

namespace D12Complex.TorusSurface

abbrev lattice := Specs.D12Complex.Ch22.LatticeGeometry.lattice

/-- The literal additive quotient, with Mathlib's quotient topology and group law. -/
abbrev Torus (ω₁ ω₂ : ℂ) := ℂ ⧸ (lattice ω₁ ω₂).toAddSubgroup

def projection (ω₁ ω₂ : ℂ) : ℂ →+ Torus ω₁ ω₂ :=
  QuotientAddGroup.mk' (lattice ω₁ ω₂).toAddSubgroup

/-- Periodicity for all lattice translations, including at designated pole values. -/
def Periodic {A : Type*} (ω₁ ω₂ : ℂ) (f : ℂ → A) : Prop :=
  ∀ z l, l ∈ lattice ω₁ ω₂ → f (z + l) = f z

/-- A quantitative lower bound for every nonzero lattice modulus. -/
def Separation (ω₁ ω₂ : ℂ) (d : ℝ) : Prop :=
  0 < d ∧ ∀ l ∈ lattice ω₁ ω₂, l ≠ 0 → d ≤ ‖l‖

/-- Every chart in this family is an inverse to the quotient map on a small disk.
The overlap is allowed to be disconnected. -/
def quotientAtlas (ω₁ ω₂ : ℂ) (d : ℝ) : Set (Surfaces.ComplexChart (Torus ω₁ ω₂)) :=
  {e | ∃ a : ℂ, ∃ r : ℝ, 0 < r ∧ r < d / 3 ∧
    e.val.target = Metric.ball a r ∧
    EqOn e.val.symm (projection ω₁ ω₂) (Metric.ball a r)}

end D12Complex.TorusSurface

namespace Specs.D12Complex.Ch22.TorusSurface
open _root_.D12Complex _root_.D12Complex.TorusSurface

-- Canonical definition contracts.
def Torus_type := ℂ → ℂ → Type
def Torus_value : Torus_type := fun ω₁ ω₂ => ℂ ⧸ (lattice ω₁ ω₂).toAddSubgroup

def projection_type := (ω₁ ω₂ : ℂ) → ℂ →+ Torus ω₁ ω₂
def projection_value : projection_type := fun ω₁ ω₂ =>
  QuotientAddGroup.mk' (lattice ω₁ ω₂).toAddSubgroup

universe u
def Periodic_type := {A : Type u} → ℂ → ℂ → (ℂ → A) → Prop
def Periodic_value : Periodic_type := fun ω₁ ω₂ f =>
  ∀ z l, l ∈ lattice ω₁ ω₂ → f (z + l) = f z

def Separation_type := ℂ → ℂ → ℝ → Prop
def Separation_value : Separation_type := fun ω₁ ω₂ d =>
  0 < d ∧ ∀ l ∈ lattice ω₁ ω₂, l ≠ 0 → d ≤ ‖l‖

def quotientAtlas_type := (ω₁ ω₂ : ℂ) → ℝ → Set (Surfaces.ComplexChart (Torus ω₁ ω₂))
def quotientAtlas_value : quotientAtlas_type := fun ω₁ ω₂ d =>
  {e | ∃ a : ℂ, ∃ r : ℝ, 0 < r ∧ r < d / 3 ∧
    e.val.target = Metric.ball a r ∧
    EqOn e.val.symm (projection ω₁ ω₂) (Metric.ball a r)}

def quotient_topology_type : Prop := ∀ ω₁ ω₂ : ℂ,
  IsOpenQuotientMap (projection ω₁ ω₂) ∧ IsTopologicalAddGroup (Torus ω₁ ω₂)

def metric_type : Prop := ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
  ∃ m : MetricSpace (Torus ω₁ ω₂),
    m.toPseudoMetricSpace = (inferInstance : PseudoMetricSpace (Torus ω₁ ω₂))

def distance_minimum_type : Prop := ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
  ∀ z w : ℂ, ∃ l ∈ lattice ω₁ ω₂,
    dist (projection ω₁ ω₂ z) (projection ω₁ ω₂ w) = ‖z - w - l‖ ∧
    ∀ k ∈ lattice ω₁ ω₂, ‖z - w - l‖ ≤ ‖z - w - k‖

def topology_type : Prop := ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
  ConnectedSpace (Torus ω₁ ω₂) ∧ T2Space (Torus ω₁ ω₂) ∧
    SecondCountableTopology (Torus ω₁ ω₂) ∧ CompactSpace (Torus ω₁ ω₂)

def disk_charts_type : Prop := ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
  ∀ d : ℝ, Separation ω₁ ω₂ d → ∀ a : ℂ, ∀ r : ℝ, 0 < r → r < d / 3 →
  ∃ e ∈ quotientAtlas ω₁ ω₂ d,
    e.val.target = Metric.ball a r ∧
    e.val.source = projection ω₁ ω₂ '' Metric.ball a r ∧
    EqOn e.val.symm (projection ω₁ ω₂) (Metric.ball a r) ∧
    ∀ z ∈ Metric.ball a r, e.val (projection ω₁ ω₂ z) = z

def translations_type : Prop := ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
  ∀ d : ℝ, ∀ e ∈ quotientAtlas ω₁ ω₂ d, ∀ f ∈ quotientAtlas ω₁ ω₂ d,
  ∀ C : Set ℂ, C ⊆ (e.val.symm.trans f.val).source → IsPreconnected C →
  ∃ l ∈ lattice ω₁ ω₂,
    EqOn (e.val.symm.trans f.val) (fun z => z + l) C

def surface_type : Prop := ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
  ∀ d : ℝ, Separation ω₁ ω₂ d →
  ∃ S : Surfaces.RiemannSurface (Torus ω₁ ω₂),
    S.atlas = quotientAtlas ω₁ ω₂ d

/-- The minimum is attained, and no additional separation hypothesis is assumed. -/
def compact_surface_type : Prop := ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
  ∃ d : ℝ, Separation ω₁ ω₂ d ∧
    (∃ l ∈ lattice ω₁ ω₂, l ≠ 0 ∧ ‖l‖ = d) ∧
    ∃ S : Surfaces.RiemannSurface (Torus ω₁ ω₂),
      S.atlas = quotientAtlas ω₁ ω₂ d ∧ CompactSpace (Torus ω₁ ω₂)

/-- In the constructed quotient coordinate, the projection is the identity
biholomorphism between the two disk coordinates. -/
def locally_biholomorphic_type : Prop := ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
  ∀ d : ℝ, Separation ω₁ ω₂ d → ∀ a : ℂ, ∀ r : ℝ, 0 < r → r < d / 3 →
  ∃ e ∈ quotientAtlas ω₁ ω₂ d,
    e.val.target = Metric.ball a r ∧
    e.val.source = projection ω₁ ω₂ '' Metric.ball a r ∧
    BiholomorphicPair (Metric.ball a r) (Metric.ball a r)
      (e.val ∘ projection ω₁ ω₂) id

/-- Descent is asserted for arbitrary values as well as for scalar functions.
The chart identity explicitly identifies the descended function with the original
one. Thus it also handles sphere pole values without choosing a new function. -/
def descent_type : Prop := ∀ ω₁ ω₂ : ℂ, ∀ (A : Type) (f : ℂ → A), Periodic ω₁ ω₂ f →
  ∃! F : Torus ω₁ ω₂ → A, F ∘ projection ω₁ ω₂ = f

def holomorphic_descent_type : Prop := ∀ ω₁ ω₂ : ℂ, ∀ (f : ℂ → ℂ),
  Periodic ω₁ ω₂ f → HolomorphicOn univ f →
  ∃ F : Torus ω₁ ω₂ → ℂ, F ∘ projection ω₁ ω₂ = f ∧
    ∀ d : ℝ, ∀ e ∈ quotientAtlas ω₁ ω₂ d, HolomorphicOn e.val.target (F ∘ e.val.symm)

def meromorphic_descent_type : Prop := ∀ ω₁ ω₂ : ℂ, ∀ (f : ℂ → ℂ),
  Periodic ω₁ ω₂ f → (∀ z, MeromorphicAt f z) →
  ∃ F : Torus ω₁ ω₂ → ℂ, F ∘ projection ω₁ ω₂ = f ∧
    ∀ d : ℝ, ∀ e ∈ quotientAtlas ω₁ ω₂ d,
      ∀ z ∈ e.val.target, MeromorphicAt (F ∘ e.val.symm) z

end Specs.D12Complex.Ch22.TorusSurface
