import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral

/-! The step approximation used in K03.19.riemann_lebesgue
(paper.tex:4750–4754). The integral is the proper Darboux integral of the
upstream interface. A step function is specified by its constants on the
open cells of a finite strict partition and its separately assigned node
values. The node values are universally quantified after the partition
and constants have been chosen. No uniform approximation or regulatedness
hypothesis is imposed. Singleton intervals are included. -/
namespace Specs.SingleVariableAnalysis.Ch19.StepL1Approximation
open _root_.SingleVariableAnalysis.Riemann
open Specs.SingleVariableAnalysis.Ch08

def realStepL1Approximation : Prop :=
  ∀ (f : ℝ → ℝ) {a b : ℝ} (_hf : Integral.realIntegrableValue f a b)
    (ε : ℝ), 0 < ε →
    ∃ (P : PartitionData a b) (c : Fin P.n → ℝ),
      ∀ v : Fin (P.n + 1) → ℝ, ∃ s : ℝ → ℝ,
        (∀ (i : Fin P.n) (x : ℝ),
          x ∈ Set.Ioo (P.point i.castSucc) (P.point i.succ) → s x = c i) ∧
        (∀ j : Fin (P.n + 1), s (P.point j) = v j) ∧
        Integral.realIntegrableValue s a b ∧
        ∃ he : Integral.realIntegrableValue (fun x => ‖f x - s x‖) a b,
          Integral.realIntegralValue (fun x => ‖f x - s x‖) he < ε

def complexStepL1Approximation : Prop :=
  ∀ (f : ℝ → ℂ) {a b : ℝ} (_hf : Integral.complexIntegrableValue f a b)
    (ε : ℝ), 0 < ε →
    ∃ (P : PartitionData a b) (c : Fin P.n → ℂ),
      ∀ v : Fin (P.n + 1) → ℂ, ∃ s : ℝ → ℂ,
        (∀ (i : Fin P.n) (x : ℝ),
          x ∈ Set.Ioo (P.point i.castSucc) (P.point i.succ) → s x = c i) ∧
        (∀ j : Fin (P.n + 1), s (P.point j) = v j) ∧
        Integral.complexIntegrableValue s a b ∧
        ∃ he : Integral.realIntegrableValue (fun x => ‖f x - s x‖) a b,
          Integral.realIntegralValue (fun x => ‖f x - s x‖) he < ε

end Specs.SingleVariableAnalysis.Ch19.StepL1Approximation
