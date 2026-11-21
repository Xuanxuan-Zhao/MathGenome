import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch19.GermTopology
import Mathlib.Topology.Connected.LocallyConnected

/-! Independent interface for paper.tex:3165–3190 (d12:19-02).
There are `n+1` segments, so even a constant path has a nonempty chain.
The time coordinates are strictly increasing. Compatibility is equality on
the actual connected component of the intersection containing the joint.
All functions and germs are the upstream canonical objects. -/

open Set
open scoped Topology
noncomputable section

namespace D12Complex.FiniteContinuationChains

/-- A finite chain with prescribed endpoint germs. -/
structure Chain (Ω : Set ℂ) (γ : unitInterval → ℂ)
    (φ : HolomorphicGerm (γ 0)) (ψ : HolomorphicGerm (γ 1)) where
  n : ℕ
  time : Fin (n + 2) → unitInterval
  strict : StrictMono time
  time_zero : time 0 = 0
  time_last : time (Fin.last (n + 1)) = 1
  element : Fin (n + 1) → FunctionElement
  domain_subset : ∀ i, (element i).domain ⊆ Ω
  contains : ∀ i t, t ∈ Icc (time i.castSucc) (time i.succ) →
    γ t ∈ (element i).domain
  compatible : ∀ i : Fin n,
    EqOn (element i.castSucc).toFun (element i.succ).toFun
      (connectedComponentIn ((element i.castSucc).domain ∩ (element i.succ).domain)
        (γ (time i.succ.castSucc)))
  initial_mem : γ 0 ∈ (element 0).domain
  terminal_mem : γ 1 ∈ (element (Fin.last n)).domain
  initial_germ : φ = (element 0).germAt (γ 0) initial_mem
  terminal_germ : ψ = (element (Fin.last n)).germAt (γ 1) terminal_mem

end D12Complex.FiniteContinuationChains

namespace Specs.D12Complex.Ch19.FiniteContinuationChains
open _root_.D12Complex _root_.D12Complex.FiniteContinuationChains

def Chain_type := (Ω : Set ℂ) → (γ : unitInterval → ℂ) →
  HolomorphicGerm (γ 0) → HolomorphicGerm (γ 1) → Type
def Chain_value : Chain_type := Chain

/-- Extract the finite chain while retaining the specified terminal germ. -/
def continuation_to_chain_type : Prop :=
  ∀ (Ω : Set ℂ) (γ : unitInterval → ℂ) (φ : HolomorphicGerm (γ 0))
    (ψ : HolomorphicGerm (γ 1)) (Φ : GermFamily γ),
    IsContinuation Ω γ φ Φ → Φ 1 = ψ → Nonempty (Chain Ω γ φ ψ)

/-- Reconstruction also specifies the representative on every closed piece. -/
def chain_reconstruction_type : Prop :=
  ∀ (Ω : Set ℂ) (γ : unitInterval → ℂ) (φ : HolomorphicGerm (γ 0))
    (ψ : HolomorphicGerm (γ 1)), IsDomain Ω → Continuous γ →
    ∀ c : Chain Ω γ φ ψ, ∃ Φ : GermFamily γ,
      IsContinuation Ω γ φ Φ ∧ Φ 1 = ψ ∧
        ∀ i, RepresentsOn γ Φ (c.element i).domain (c.element i).toFun
          (Icc (c.time i.castSucc) (c.time i.succ))

def continuation_iff_chain_type : Prop :=
  ∀ (Ω : Set ℂ) (γ : unitInterval → ℂ) (φ : HolomorphicGerm (γ 0))
    (ψ : HolomorphicGerm (γ 1)), IsDomain Ω → Continuous γ →
    ((∃ Φ : GermFamily γ, IsContinuation Ω γ φ Φ ∧ Φ 1 = ψ) ↔
      Nonempty (Chain Ω γ φ ψ))

/-- The second equivalence in the source, in the canonical germ topology. -/
def chain_iff_continuous_lift_type : Prop :=
  ∀ (Ω : Set ℂ) (γ : unitInterval → ℂ) (hγ : ∀ t, γ t ∈ Ω)
    (φ : HolomorphicGerm (γ 0)) (ψ : HolomorphicGerm (γ 1)),
    IsDomain Ω → Continuous γ →
    (Nonempty (Chain Ω γ φ ψ) ↔
      ∃ Φ : GermFamily γ, Φ 0 = φ ∧ Φ 1 = ψ ∧
        Continuous (GermTopology.lift γ hγ Φ))

end Specs.D12Complex.Ch19.FiniteContinuationChains
