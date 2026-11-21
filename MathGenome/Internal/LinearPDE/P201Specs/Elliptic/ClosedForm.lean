import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.ClosedNonnegativeForms
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! Shared associated operator, with the manuscript's linear-first convention.
No symmetry, sign, continuity or closedness is required to define this operator.
Only the closed-form theorem below imposes Hermitian symmetry and nonnegativity.
The separate library EnergySpace carries the energy norm, not the ambient norm.
-/
noncomputable section
open scoped ComplexConjugate InnerProductSpace
universe u v
namespace P201.Elliptic

variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The manuscript's inner product, linear in its first argument. -/
def paperInner (x y : H) : 𝕜 := inner 𝕜 y x

/-- A densely defined sesquilinear form, linear in the unknown (first slot)
and conjugate-linear in the test (second slot). No ambient bound is imposed. -/
structure DenseForm (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] where
  domain : Submodule 𝕜 H
  dense : Dense (domain : Set H)
  form : domain →ₗ[𝕜] domain →ₗ⋆[𝕜] 𝕜

namespace DenseForm
variable (a : DenseForm 𝕜 H)

/-- The full representation relation, for arbitrary sesquilinear forms. -/
def graph : Submodule 𝕜 (H × H) where
  carrier := {p | ∃ hu : p.1 ∈ a.domain,
    ∀ v : a.domain, a.form ⟨p.1, hu⟩ v = paperInner (𝕜 := 𝕜) p.2 (v : H)}
  zero_mem' := ⟨a.domain.zero_mem, by
    intro v
    change a.form 0 v = inner 𝕜 (v : H) 0
    simp⟩
  add_mem' := by
    rintro ⟨x, f⟩ ⟨y, g⟩ ⟨hx, hfx⟩ ⟨hy, hgy⟩
    refine ⟨a.domain.add_mem hx hy, fun v => ?_⟩
    change a.form (⟨x, hx⟩ + ⟨y, hy⟩) v = inner 𝕜 (v : H) (f + g)
    simpa only [map_add, LinearMap.add_apply, inner_add_right, paperInner] using congrArg₂ (· + ·) (hfx v) (hgy v)
  smul_mem' := by
    rintro c ⟨x, f⟩ ⟨hx, hfx⟩
    refine ⟨a.domain.smul_mem c hx, fun v => ?_⟩
    change a.form (c • ⟨x, hx⟩) v = inner 𝕜 (v : H) (c • f)
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, inner_smul_right]
    exact congrArg (c * ·) (hfx v)

/-- One canonical partial operator, also used for nonsymmetric forms.
Density will prove that extracting this partial map preserves the entire graph. -/
def associatedOperator : ExpandedFA.Unbounded.Operator 𝕜 H H := a.graph.toLinearPMap

def IsHermitian : Prop := ∀ x y, conj (a.form x y) = a.form y x

def IsNonnegative : Prop := ∀ x, 0 ≤ RCLike.re (a.form x x)

/-- The actual slot reversal into the pinned library's test-first convention. -/
def toNonnegative (hs : a.IsHermitian) (hn : a.IsNonnegative) :
    ExpandedFA.Unbounded.ClosedNonnegativeForms.NonnegativeForm 𝕜 H where
  domain := a.domain
  dense := a.dense
  form := a.form.flip
  hermitian := hs
  nonneg := hn

end DenseForm

namespace ClosedFormExpected

/-- The inner product bridge includes the scalar law in the linear slot. -/
def Conventions : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (a : DenseForm 𝕜 H) (hs : a.IsHermitian) (hn : a.IsNonnegative),
    (∀ x y : a.domain, (a.toNonnegative hs hn).form y x = a.form x y) ∧
    (∀ x : a.domain, (RCLike.re (a.form x x) : 𝕜) = a.form x x) ∧
    (∀ f w : H, inner 𝕜 w f = paperInner (𝕜 := 𝕜) f w) ∧
    (∀ (c : 𝕜) (f w : H), paperInner (𝕜 := 𝕜) (c • f) w = c * paperInner (𝕜 := 𝕜) f w) ∧
    (∀ (c : 𝕜) (f w : H), paperInner (𝕜 := 𝕜) f (c • w) = conj c * paperInner (𝕜 := 𝕜) f w)

/-- Exact graph, domain, action and uniqueness for the general canonical operator. -/
def CanonicalOperator : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (a : DenseForm 𝕜 H),
    (∀ u f : H, (u, f) ∈ a.associatedOperator.graph ↔
      ∃ hu : u ∈ a.domain, ∀ w : a.domain,
        a.form ⟨u, hu⟩ w = paperInner (𝕜 := 𝕜) f (w : H)) ∧
    (∀ u : H, u ∈ a.associatedOperator.domain ↔
      ∃ hu : u ∈ a.domain, ∃ f : H, ∀ w : a.domain,
        a.form ⟨u, hu⟩ w = paperInner (𝕜 := 𝕜) f (w : H)) ∧
    (∀ (u : a.domain) (f g : H),
      (∀ w : a.domain, a.form u w = paperInner (𝕜 := 𝕜) f (w : H)) →
      (∀ w : a.domain, a.form u w = paperInner (𝕜 := 𝕜) g (w : H)) → f = g) ∧
    (∀ u : a.associatedOperator.domain,
      ∃ hu : (u : H) ∈ a.domain, ∀ w : a.domain,
        a.form ⟨(u : H), hu⟩ w = paperInner (𝕜 := 𝕜) (a.associatedOperator u) (w : H))

/-- Completeness and compactness use precisely the prescribed energy norm.
The graph equivalence specifies both directions of the shifted inverse identity. -/
def ClosedForm : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (a : DenseForm 𝕜 H) (hs : a.IsHermitian) (hn : a.IsNonnegative),
    let q := a.toNonnegative hs hn
    q.IsClosed →
    (∀ x : q.EnergySpace,
      ‖x‖ ^ 2 = RCLike.re (a.form (q.toDomain x) (q.toDomain x)) +
        ‖(q.toDomain x : H)‖ ^ 2) ∧
    Dense (a.associatedOperator.domain : Set H) ∧
    a.associatedOperator = a.associatedOperator.adjoint ∧
    (∀ x : a.associatedOperator.domain,
      0 ≤ RCLike.re (paperInner (𝕜 := 𝕜) (a.associatedOperator x) (x : H))) ∧
    ∃ S : H →L[𝕜] q.EnergySpace,
      (∀ f : H, ‖S f‖ ≤ ‖f‖) ∧
      (∀ (f : H) (u : a.domain),
        (∀ w : a.domain, a.form u w + paperInner (𝕜 := 𝕜) (u : H) (w : H) =
          paperInner (𝕜 := 𝕜) f (w : H)) ↔ u = q.toDomain (S f)) ∧
      (∀ u f : H, (u, f - u) ∈ a.associatedOperator.graph ↔ q.inclusion (S f) = u) ∧
      (IsCompactOperator q.inclusion → IsCompactOperator (q.inclusion.comp S))

end ClosedFormExpected
end P201.Elliptic
