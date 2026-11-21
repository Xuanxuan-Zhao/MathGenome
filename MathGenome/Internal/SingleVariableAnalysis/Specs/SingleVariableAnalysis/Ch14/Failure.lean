import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.UniformImproper
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.ExpConstruction
import Mathlib.Topology.Order.Basic

/-! K03.14.failure, paper.tex:3535–3551. The exponential is the shared
factorial-series construction. Proper and improper integrals are the existing
Darboux integrals and their cofinal limits, not total measure integrals. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch14.Failure
open Set
open scoped Topology
open Ch08.Integral Ch10.OneEndpoint Ch14.UniformImproper

abbrev integrandType := ℝ → ℝ → ℝ
def integrandValue : integrandType := fun x t =>
  t * Ch07.ExpConstruction.realSeriesExpValue (-t * x)
abbrev limitType := ℝ → ℝ
def limitValue : limitType := fun t => if t = 0 then 0 else 1

def jointContinuity : Prop := ∀ X T : ℝ, 0 ≤ X → 0 ≤ T →
  ContinuousOn (fun p : ℝ × ℝ => integrandValue p.1 p.2) (Icc 0 X ×ˢ Icc 0 T)

def finiteFormula : Prop := ∀ R t : ℝ, 0 ≤ R → 0 ≤ t →
  ∃ h : realIntegrableValue (fun x => integrandValue x t) 0 R,
    realIntegralValue _ h = 1 - Ch07.ExpConstruction.realSeriesExpValue (-t * R)

def zeroValues : Prop := (∀ x : ℝ, integrandValue x 0 = 0) ∧
  (∀ R : ℝ, ∀ h : realIntegrableValue (fun x => integrandValue x 0) 0 R,
    realIntegralValue _ h = 0) ∧ limitValue 0 = 0 ∧
  ∀ t : ℝ, 0 < t → limitValue t = 1

def truncationContinuity : Prop := ∀ R : ℝ, 0 ≤ R →
  ContinuousOn (fun t => 1 - Ch07.ExpConstruction.realSeriesExpValue (-t * R)) (Ici 0)

def improperFormula : Prop := ∀ t : ℝ, 0 ≤ t →
  rightHasIntegralValue .real (fun x => integrandValue x t) 0 ⊤ (limitValue t)

def discontinuity : Prop := ¬ ContinuousWithinAt limitValue (Ici 0) 0

def tailFormula : Prop := ∀ R t : ℝ, 0 ≤ R → 0 < t →
  ∀ h : realIntegrableValue (fun x => integrandValue x t) 0 R,
    limitValue t - realIntegralValue _ h = Ch07.ExpConstruction.realSeriesExpValue (-t * R)

/-- The tail is itself a convergent improper Darboux integral. -/
def tailHasIntegral : Prop := ∀ R t : ℝ, 0 ≤ R → 0 < t →
  rightHasIntegralValue .real (fun x => integrandValue x t) R ⊤
    (Ch07.ExpConstruction.realSeriesExpValue (-t * R))

def tailSupremum : Prop := ∀ R δ : ℝ, 0 < R → 0 < δ →
  IsLUB ((fun t => Ch07.ExpConstruction.realSeriesExpValue (-t * R)) '' Ioc 0 δ) 1 ∧
  sSup ((fun t => Ch07.ExpConstruction.realSeriesExpValue (-t * R)) '' Ioc 0 δ) = 1

/-- Failure for both the closed parameter neighborhood and its positive part;
no possible alternative uniform limit is allowed. -/
def nonuniform : Prop := ∀ δ : ℝ, 0 < δ →
  ¬ rightUniformConvergesValue .real {t : ℝ // t ∈ Icc 0 δ}
      (fun x t => integrandValue x t.val) 0 ⊤ ∧
  ¬ rightUniformConvergesValue .real {t : ℝ // t ∈ Ioc 0 δ}
      (fun x t => integrandValue x t.val) 0 ⊤

end Specs.SingleVariableAnalysis.Ch14.Failure
