import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.RsSums
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.ContinuousOn

/-! K03.15.rs_mesh_bridge, paper.tex:3774–3794.
An unrestricted mesh limit quantifies over every partition and all closed-cell
 tags. The theorem compares the value itself, hence also existence of values.
The endpoints may coincide. No continuity of the bounded integrand is imposed.
-/
namespace Specs.SingleVariableAnalysis.Ch15.RsMeshBridge
open _root_.SingleVariableAnalysis.Riemann
universe u

abbrev meshLimitType := {E : Type u} → [NormedAddCommGroup E] → [Module ℝ E] →
  ℝ → ℝ → (ℝ → E) → (ℝ → ℝ) → E → Prop

def meshLimitValue : meshLimitType := fun a b f α I =>
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ P : PartitionData a b,
      Specs.SingleVariableAnalysis.Ch08.Partitions.meshValue P < δ →
      ∀ t : Specs.SingleVariableAnalysis.Ch08.Partitions.taggingValue P,
        ‖Specs.SingleVariableAnalysis.Ch15.RsSums.sumValue P t f α - I‖ < ε

def realBridge : Prop := ∀ (a b : ℝ), a ≤ b → ∀ (f α : ℝ → ℝ),
  Specs.SingleVariableAnalysis.Ch15.RsSums.boundedOnValue a b f →
  ContinuousOn α (Set.Icc a b) → MonotoneOn α (Set.Icc a b) →
  ∀ I : ℝ, Specs.SingleVariableAnalysis.Ch15.RsSums.integralValue a b f α I ↔
    meshLimitValue a b f α I

def complexBridge : Prop := ∀ (a b : ℝ), a ≤ b → ∀ (f : ℝ → ℂ) (α : ℝ → ℝ),
  Specs.SingleVariableAnalysis.Ch15.RsSums.boundedOnValue a b f →
  ContinuousOn α (Set.Icc a b) → MonotoneOn α (Set.Icc a b) →
  ∀ I : ℂ, Specs.SingleVariableAnalysis.Ch15.RsSums.integralValue a b f α I ↔
    meshLimitValue a b f α I

def realExistence : Prop := ∀ (a b : ℝ), a ≤ b → ∀ (f α : ℝ → ℝ),
  Specs.SingleVariableAnalysis.Ch15.RsSums.boundedOnValue a b f →
  ContinuousOn α (Set.Icc a b) → MonotoneOn α (Set.Icc a b) →
  ((∃ I : ℝ, Specs.SingleVariableAnalysis.Ch15.RsSums.integralValue a b f α I) ↔
    ∃ I : ℝ, meshLimitValue a b f α I)

def complexExistence : Prop := ∀ (a b : ℝ), a ≤ b → ∀ (f : ℝ → ℂ) (α : ℝ → ℝ),
  Specs.SingleVariableAnalysis.Ch15.RsSums.boundedOnValue a b f →
  ContinuousOn α (Set.Icc a b) → MonotoneOn α (Set.Icc a b) →
  ((∃ I : ℂ, Specs.SingleVariableAnalysis.Ch15.RsSums.integralValue a b f α I) ↔
    ∃ I : ℂ, meshLimitValue a b f α I)

/-- Componentwise interpretation uses the same unrestricted partitions and tags. -/
def complexComponents : Prop := ∀ (a b : ℝ) (f : ℝ → ℂ) (α : ℝ → ℝ) (I : ℂ),
  meshLimitValue a b f α I ↔
    meshLimitValue a b (fun x => (f x).re) α I.re ∧
    meshLimitValue a b (fun x => (f x).im) α I.im

def degenerate : Prop := ∀ {E : Type u} [NormedAddCommGroup E] [Module ℝ E]
  (a : ℝ) (f : ℝ → E) (α : ℝ → ℝ) (I : E),
  meshLimitValue a a f α I ↔ I = 0

def constantIntegrator : Prop := ∀ {E : Type u} [NormedAddCommGroup E] [Module ℝ E]
  (a b : ℝ) (f : ℝ → E) (c : ℝ), meshLimitValue a b f (fun _ => c) 0

def constantIntegrand : Prop := ∀ {E : Type u} [NormedAddCommGroup E] [Module ℝ E]
  (a b : ℝ) (c : E) (α : ℝ → ℝ),
  meshLimitValue a b (fun _ => c) α ((α b - α a) • c)
end Specs.SingleVariableAnalysis.Ch15.RsMeshBridge
