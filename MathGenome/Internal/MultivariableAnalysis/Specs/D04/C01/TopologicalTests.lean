import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.EuclideanInterfaces

/-! Independent statements of the basic topological tests
(`chapters/01.tex`, `d04:01:closure-tests`). All sets and points are in
the shared Euclidean space, including dimension zero. The two sequence
criteria do not require the limiting point to belong to the set. -/

open Set Filter Topology
namespace Specs.D04.C01.TopologicalTests
open Specs.D04.C01.EuclideanInterfaces.Model

def open_sUnionType : Prop :=
  ∀ {n : ℕ} (S : Set (Set (E n))),
    (∀ U ∈ S, Open U) → Open (⋃₀ S)

def open_sInterType : Prop :=
  ∀ {n : ℕ} (S : Set (Set (E n))),
    S.Finite → (∀ U ∈ S, Open U) → Open (⋂₀ S)

def closed_iff_seq_limitsType : Prop :=
  ∀ {n : ℕ} (F : Set (E n)), Closed F ↔
    ∀ (s : ℕ → E n) (a : E n),
      (∀ k, s k ∈ F) → Tendsto s atTop (𝓝 a) → a ∈ F

def mem_closure_iff_sequenceType : Prop :=
  ∀ {n : ℕ} (A : Set (E n)) (a : E n),
    a ∈ Closure A ↔
      ∃ s : ℕ → E n, (∀ k, s k ∈ A) ∧ Tendsto s atTop (𝓝 a)

def accumulationPoint_iff_sequenceType : Prop :=
  ∀ {n : ℕ} (A : Set (E n)) (a : E n),
    AccumulationPoint A a ↔
      ∃ s : ℕ → E n, (∀ k, s k ∈ A \ {a}) ∧ Tendsto s atTop (𝓝 a)

def closed_closureType : Prop :=
  ∀ {n : ℕ} (A : Set (E n)), Closed (Closure A)

def open_interiorType : Prop :=
  ∀ {n : ℕ} (A : Set (E n)), Open (Interior A)

def boundary_eq_closure_inter_complType : Prop :=
  ∀ {n : ℕ} (A : Set (E n)),
    Boundary A = Closure A ∩ Closure Aᶜ

def closed_boundaryType : Prop :=
  ∀ {n : ℕ} (A : Set (E n)), Closed (Boundary A)

end Specs.D04.C01.TopologicalTests
