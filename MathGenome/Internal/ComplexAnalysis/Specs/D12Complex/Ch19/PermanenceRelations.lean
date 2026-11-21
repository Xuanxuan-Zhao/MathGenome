import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch19.GermsContinuation
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! Permanence, paper.tex:3192–3208. Representatives are arbitrary total
functions with the specified neighborhood germs. `jetGraph` includes the base
coordinate and every derivative from order zero through r. A single function H
on an open subset of this finite dimensional space expresses single-valued
holomorphic dependence on the base and jets. Admissibility asks exactly that
these local graphs belong to its domain at every parameter; openness then gives
the needed neighborhoods. No existence of the input continuations is asserted.
-/
open Filter
open scoped Topology
noncomputable section
namespace D12Complex.RelationData

def jetGraph {m : ℕ} (r : ℕ) (f : Fin m → ℂ → ℂ) (z : ℂ) :
    ℂ × (Fin m × Fin (r + 1) → ℂ) :=
  (z, fun p => iteratedDeriv p.2.val (f p.1) z)

def RepresentsTuple {m : ℕ} (a : ℂ) (φ : Fin m → HolomorphicGerm a)
    (f : Fin m → ℂ → ℂ) : Prop :=
  ∀ i, (φ i).val = (f i : Germ (𝓝 a) ℂ)

def GraphsIn {m : ℕ} (r : ℕ) (γ : unitInterval → ℂ)
    (Φ : Fin m → GermFamily γ) (D : Set (ℂ × (Fin m × Fin (r + 1) → ℂ))) : Prop :=
  ∀ t, ∃ (U : Set ℂ) (f : Fin m → ℂ → ℂ), γ t ∈ U ∧
    (∀ i, HolomorphicOn U (f i)) ∧ RepresentsTuple (γ t) (fun i => Φ i t) f ∧
    jetGraph r f (γ t) ∈ D
end D12Complex.RelationData

namespace Specs.D12Complex.Ch19.PermanenceRelations
open _root_.D12Complex _root_.D12Complex.RelationData

def jetGraph_type := ∀ {m : ℕ} (r : ℕ), (Fin m → ℂ → ℂ) → ℂ →
  ℂ × (Fin m × Fin (r + 1) → ℂ)
def jetGraph_value : jetGraph_type := @jetGraph

def RepresentsTuple_type := ∀ {m : ℕ} (a : ℂ), (Fin m → HolomorphicGerm a) →
  (Fin m → ℂ → ℂ) → Prop
def RepresentsTuple_value : RepresentsTuple_type := @RepresentsTuple

def GraphsIn_type := ∀ {m : ℕ} (r : ℕ) (γ : unitInterval → ℂ),
  (Fin m → GermFamily γ) → Set (ℂ × (Fin m × Fin (r + 1) → ℂ)) → Prop
def GraphsIn_value : GraphsIn_type := @GraphsIn

/-- Equality of representatives preserves all finite jets and substitutions,
including their full neighborhood germs, with no domain restriction omitted. -/
def expression_representative_independence_type : Prop :=
  ∀ (m r : ℕ) (a : ℂ) (f g : Fin m → ℂ → ℂ)
    (H : (ℂ × (Fin m × Fin (r + 1) → ℂ)) → ℂ),
    (∀ i, f i =ᶠ[𝓝 a] g i) →
    (fun z => H (jetGraph r f z)) =ᶠ[𝓝 a] (fun z => H (jetGraph r g z)) ∧
      jetGraph r f a = jetGraph r g a

def derivative_continuation_type : Prop :=
  ∀ (k : ℕ) (Ω : Set ℂ) (γ : unitInterval → ℂ)
    (φ : HolomorphicGerm (γ 0)) (Φ : GermFamily γ),
    IsContinuation Ω γ φ Φ → ∃ Ψ : GermFamily γ,
      IsContinuation Ω γ (Ψ 0) Ψ ∧ ∀ t (f : ℂ → ℂ),
        (Φ t).val = (f : Germ (𝓝 (γ t)) ℂ) →
        (Ψ t).val = (iteratedDeriv k f : Germ (𝓝 (γ t)) ℂ)

def sum_continuation_type : Prop :=
  ∀ (Ω : Set ℂ) (γ : unitInterval → ℂ)
    (φ ψ : HolomorphicGerm (γ 0)) (Φ Ψ : GermFamily γ),
    IsContinuation Ω γ φ Φ → IsContinuation Ω γ ψ Ψ →
    ∃ Θ : GermFamily γ, IsContinuation Ω γ (Θ 0) Θ ∧
      ∀ t (f g : ℂ → ℂ), (Φ t).val = (f : Germ (𝓝 (γ t)) ℂ) →
        (Ψ t).val = (g : Germ (𝓝 (γ t)) ℂ) →
        (Θ t).val = ((fun z => f z + g z) : Germ (𝓝 (γ t)) ℂ)

def product_continuation_type : Prop :=
  ∀ (Ω : Set ℂ) (γ : unitInterval → ℂ)
    (φ ψ : HolomorphicGerm (γ 0)) (Φ Ψ : GermFamily γ),
    IsContinuation Ω γ φ Φ → IsContinuation Ω γ ψ Ψ →
    ∃ Θ : GermFamily γ, IsContinuation Ω γ (Θ 0) Θ ∧
      ∀ t (f g : ℂ → ℂ), (Φ t).val = (f : Germ (𝓝 (γ t)) ℂ) →
        (Ψ t).val = (g : Germ (𝓝 (γ t)) ℂ) →
        (Θ t).val = ((fun z => f z * g z) : Germ (𝓝 (γ t)) ℂ)

/-- The denominator must stay nonzero along the path on which the quotient
is continued. This applies as well to any restricted/reparametrized subpath. -/
def quotient_continuation_type : Prop :=
  ∀ (Ω : Set ℂ) (γ : unitInterval → ℂ)
    (φ ψ : HolomorphicGerm (γ 0)) (Φ Ψ : GermFamily γ),
    IsContinuation Ω γ φ Φ → IsContinuation Ω γ ψ Ψ →
    (∀ t, (Ψ t).value ≠ 0) →
    ∃ Θ : GermFamily γ, IsContinuation Ω γ (Θ 0) Θ ∧
      ∀ t (f g : ℂ → ℂ), (Φ t).val = (f : Germ (𝓝 (γ t)) ℂ) →
        (Ψ t).val = (g : Germ (𝓝 (γ t)) ℂ) →
        (Θ t).val = ((fun z => f z / g z) : Germ (𝓝 (γ t)) ℂ)

/-- Every admissible holomorphic expression in the finite jets continues. -/
def expression_continuation_type : Prop :=
  ∀ (m r : ℕ) (Ω : Set ℂ) (γ : unitInterval → ℂ)
    (φ : Fin m → HolomorphicGerm (γ 0)) (Φ : Fin m → GermFamily γ),
    IsDomain Ω → Continuous γ → (∀ t, γ t ∈ Ω) →
    (∀ i, IsContinuation Ω γ (φ i) (Φ i)) →
    ∀ (D : Set (ℂ × (Fin m × Fin (r + 1) → ℂ)))
      (H : (ℂ × (Fin m × Fin (r + 1) → ℂ)) → ℂ),
    IsOpen D → DifferentiableOn ℂ H D → GraphsIn r γ Φ D →
    ∃ Ψ : GermFamily γ, IsContinuation Ω γ (Ψ 0) Ψ ∧
      ∀ t (f : Fin m → ℂ → ℂ), RepresentsTuple (γ t) (fun i => Φ i t) f →
        (Ψ t).val = ((fun z => H (jetGraph r f z)) : Germ (𝓝 (γ t)) ℂ)

/-- An initial zero germ remains a zero germ at every time and for every
choice of representatives. Includes m = 0 and r = 0. -/
def identity_permanence_type : Prop :=
  ∀ (m r : ℕ) (Ω : Set ℂ) (γ : unitInterval → ℂ)
    (φ : Fin m → HolomorphicGerm (γ 0)) (Φ : Fin m → GermFamily γ),
    IsDomain Ω → Continuous γ → (∀ t, γ t ∈ Ω) →
    (∀ i, IsContinuation Ω γ (φ i) (Φ i)) →
    ∀ (D : Set (ℂ × (Fin m × Fin (r + 1) → ℂ)))
      (H : (ℂ × (Fin m × Fin (r + 1) → ℂ)) → ℂ),
    IsOpen D → DifferentiableOn ℂ H D → GraphsIn r γ Φ D →
    ∀ (f₀ : Fin m → ℂ → ℂ), RepresentsTuple (γ 0) φ f₀ →
    (fun z => H (jetGraph r f₀ z)) =ᶠ[𝓝 (γ 0)] (fun _ => 0) →
    ∀ t (f : Fin m → ℂ → ℂ), RepresentsTuple (γ t) (fun i => Φ i t) f →
    (fun z => H (jetGraph r f z)) =ᶠ[𝓝 (γ t)] (fun _ => 0)
end Specs.D12Complex.Ch19.PermanenceRelations
