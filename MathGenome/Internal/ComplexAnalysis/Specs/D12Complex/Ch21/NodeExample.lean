import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.Surfaces
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! The affine node in its inherited product/subspace topology, paper.tex:3762–3767.
The local models are graphs over actual open disks; the final obstruction excludes
all topological complex charts, hence any Riemann surface atlas at the node. -/
noncomputable section
open Set Metric
open scoped Topology

namespace Specs.D12Complex.Ch21.NodeExample.Model

def nodeSet : Set (ℂ × ℂ) := {p | p.2 ^ 2 = p.1 ^ 2 * (p.1 + 1)}
abbrev Node := {p : ℂ × ℂ // p ∈ nodeSet}

def origin : Node := ⟨(0, 0), by simp [nodeSet]⟩

def patch (r : ℝ) : Set Node := {p | p.val.1 ∈ ball 0 r}

def branch (s : ℂ → ℂ) (ε : ℂ) (z : ℂ) : ℂ × ℂ := (z, ε * (z * s z))

def graph (r : ℝ) (s : ℂ → ℂ) (ε : ℂ) : Set (ℂ × ℂ) :=
  {p | p.1 ∈ ball 0 r ∧ p.2 = ε * (p.1 * s p.1)}

end Specs.D12Complex.Ch21.NodeExample.Model

namespace Specs.D12Complex.Ch21.NodeExample
open _root_.D12Complex _root_.D12Complex.Surfaces Model

def nodeSet_type := Set (ℂ × ℂ)
def nodeSet_value : nodeSet_type := {p | p.2 ^ 2 = p.1 ^ 2 * (p.1 + 1)}
def Node_type := Type
def Node_value : Node_type := {p : ℂ × ℂ // p ∈ nodeSet}
def origin_type := Node
def origin_value : origin_type := ⟨(0, 0), by change (0 : ℂ)^2 = 0^2 * (0+1); simp⟩
def patch_type := ℝ → Set Node
def patch_value : patch_type := fun r => {p | p.val.1 ∈ ball 0 r}
def branch_type := (ℂ → ℂ) → ℂ → ℂ → ℂ × ℂ
def branch_value : branch_type := fun s ε z => (z, ε * (z * s z))
def graph_type := ℝ → (ℂ → ℂ) → ℂ → Set (ℂ × ℂ)
def graph_value : graph_type := fun r s ε =>
  {p | p.1 ∈ ball 0 r ∧ p.2 = ε * (p.1 * s p.1)}

def exists_local_branches_type : Prop :=
  ∃ (r : ℝ) (s : ℂ → ℂ), 0 < r ∧ r < 1 ∧
    HolomorphicOn (ball 0 r) s ∧ s 0 = 1 ∧
    (∀ z ∈ ball 0 r, (s z)^2 = 1 + z ∧ s z ≠ 0) ∧
    HolomorphicOn (ball 0 r) (fun z => z * s z) ∧
    HolomorphicOn (ball 0 r) (fun z => -(z * s z)) ∧
    (∀ x ∈ ball 0 r, ∀ y : ℂ,
      (x, y) ∈ nodeSet ↔ y = x * s x ∨ y = -(x * s x)) ∧
    (∀ x ∈ ball 0 r, x * s x = -(x * s x) ↔ x = 0)

/-- Each separated branch has a regular holomorphic parameter, inverse the first
coordinate, and is homeomorphic to the disk in the inherited affine topology. -/
def branch_parameter_type : Prop :=
  ∀ (r : ℝ) (s : ℂ → ℂ), HolomorphicOn (ball 0 r) s → ∀ ε : ℂ,
    (∃ e : (ball (0 : ℂ) r) ≃ₜ graph r s ε,
      ∀ z, (e z).val = branch s ε z) ∧
    (∀ z ∈ ball 0 r, DifferentiableAt ℂ (branch s ε) z) ∧
    (∀ z : ℂ, deriv (fun t => (branch s ε t).1) z = 1)

def puncture_disconnected_type : Prop :=
  ∃ r : ℝ, 0 < r ∧ IsOpen (patch r) ∧ origin ∈ patch r ∧
    ∀ U : Set Node, IsOpen U → origin ∈ U → U ⊆ patch r →
      ¬ IsPreconnected (U \ {origin})

def punctured_disk_connected_type : Prop :=
  ∀ (c : ℂ) (r : ℝ), 0 < r → IsConnected (ball c r \ {c})

def no_chart_at_origin_type : Prop :=
  ∀ e : OpenPartialHomeomorph Node ℂ, origin ∉ e.source

def not_riemann_surface_type : Prop := ¬ Nonempty (RiemannSurface Node)

end Specs.D12Complex.Ch21.NodeExample
