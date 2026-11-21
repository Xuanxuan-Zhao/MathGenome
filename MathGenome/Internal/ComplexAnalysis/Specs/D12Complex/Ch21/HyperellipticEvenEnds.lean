import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.Surfaces
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Analytic.Order

/-! Independent interface for the two even-degree ends, paper.tex:3737–3741.
The affine set carries only its inherited subtype topology. Every embedding,
chart, inverse law, and compatibility proof below is output data. -/
noncomputable section
open Set

namespace D12Complex.HyperellipticEvenEnds

abbrev Affine (P : Polynomial ℂ) := {q : ℂ × ℂ // q.2 ^ 2 = P.eval q.1}

def parameterDomain (r : ℝ) : Set ℂ := {t | t ≠ 0 ∧ ‖t‖ < r}

/-- The finite coordinate charts with which an infinity parameter must agree. -/
def CoordinateChart (P : Polynomial ℂ) (e : Surfaces.ComplexChart (Affine P)) : Prop :=
  (EqOn e.val (fun x => x.val.1) e.val.source ∨
    EqOn e.val (fun x => x.val.2) e.val.source) ∧
  HolomorphicOn e.val.target (fun t => (e.val.symm t).val.1) ∧
  HolomorphicOn e.val.target (fun t => (e.val.symm t).val.2)

/-- An actual punctured embedding and its inverse complex chart. -/
structure Sheet (P : Polynomial ℂ) (g : ℕ) (r : ℝ) (h : ℂ → ℂ) where
  parameter : parameterDomain r → Affine P
  parameter_z : ∀ t, (parameter t).val.1 = (t.val)⁻¹
  parameter_w : ∀ t, (parameter t).val.2 = h t / t.val ^ (g + 1)
  openEmbedding : Topology.IsOpenEmbedding parameter
  chart : Surfaces.ComplexChart (Affine P)
  chart_source : chart.val.source = range parameter
  chart_target : chart.val.target = parameterDomain r
  chart_apply : ∀ x ∈ chart.val.source, chart.val x = x.val.1⁻¹
  chart_inverse : ∀ t (ht : t ∈ parameterDomain r),
    chart.val.symm t = parameter ⟨t, ht⟩
  left_inverse : ∀ x ∈ chart.val.source, chart.val.symm (chart.val x) = x
  right_inverse : ∀ t ∈ parameterDomain r, chart.val (chart.val.symm t) = t
  inverse_z_holomorphic : HolomorphicOn chart.val.target (fun t => (chart.val.symm t).val.1)
  inverse_w_holomorphic : HolomorphicOn chart.val.target (fun t => (chart.val.symm t).val.2)
  compatible : ∀ e : Surfaces.ComplexChart (Affine P), CoordinateChart P e →
    Surfaces.CompatibleCharts chart e
  inverse_base_parameter : ∀ t ∈ parameterDomain r, ((chart.val.symm t).val.1)⁻¹ = t

/-- The full even-end conclusion, without presupposing an affine surface or completion. -/
structure EvenEnds (P : Polynomial ℂ) (g : ℕ) where
  radius : ℝ
  radius_pos : 0 < radius
  root : ℂ → ℂ
  root_holomorphic : HolomorphicOn (Metric.ball 0 radius) root
  root_nonzero : ∀ t ∈ Metric.ball 0 radius, root t ≠ 0
  root_square : ∀ t ∈ Metric.ball 0 radius, root t ^ 2 = P.reverse.eval t
  root_zero_square : root 0 ^ 2 = P.leadingCoeff
  leadingCoeff_nonzero : P.leadingCoeff ≠ 0
  reverse_extension : ∀ t : ℂ, t ≠ 0 →
    P.reverse.eval t = t ^ (2 * g + 2) * P.eval t⁻¹
  plus : Sheet P g radius root
  minus : Sheet P g radius (fun t => -root t)
  disjoint : Disjoint (range plus.parameter) (range minus.parameter)
  exterior : range plus.parameter ∪ range minus.parameter =
    {x : Affine P | x.val.1 ≠ 0 ∧ ‖x.val.1⁻¹‖ < radius}
  /-- The reciprocal base coordinate extends as the literal identity on each added disk. -/
  inverse_base_holomorphic : HolomorphicOn (Metric.ball 0 radius) (fun t : ℂ => t)
  inverse_base_order : analyticOrderAt (fun t : ℂ => t) 0 = 1

end D12Complex.HyperellipticEvenEnds

namespace Specs.D12Complex.Ch21.HyperellipticEvenEnds
open _root_.D12Complex.HyperellipticEvenEnds

def even_ends_type : Prop :=
  ∀ (P : Polynomial ℂ) (g : ℕ), Squarefree P → P.natDegree = 2 * g + 2 →
    Nonempty (EvenEnds P g)

end Specs.D12Complex.Ch21.HyperellipticEvenEnds
