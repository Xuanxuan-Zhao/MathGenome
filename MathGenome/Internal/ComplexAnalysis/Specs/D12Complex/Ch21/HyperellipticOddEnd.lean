import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.Surfaces
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Analytic.Order

/-! Independent specification of the odd infinity parameter in paper.tex:3741–3755.
The affine curve carries the topology induced from the literal zero set in ℂ².
No surface, embedding, covering or compatibility is an input certificate. -/

noncomputable section
open Set

namespace D12Complex.HyperellipticOddEnd

abbrev AffineCurve (P : Polynomial ℂ) := {q : ℂ × ℂ // q.2 ^ 2 = P.eval q.1}

def puncturedDisk (r : ℝ) : Set ℂ := {t | t ≠ 0 ∧ ‖t‖ < r}

def exterior (P : Polynomial ℂ) (r : ℝ) : Set (AffineCurve P) :=
  {q | q.val.1 ≠ 0 ∧ ‖q.val.1⁻¹‖ < r ^ 2}

/-- Exactly the ordinary z/w coordinate charts whose inverse coordinates are
holomorphic. All regularity is on the actual chart target. -/
def GoodCoordinateChart {P : Polynomial ℂ} (e : Surfaces.ComplexChart (AffineCurve P)) : Prop :=
  ((∀ q ∈ e.val.source, e.val q = q.val.1) ∨
   (∀ q ∈ e.val.source, e.val q = q.val.2)) ∧
  HolomorphicOn e.val.target (fun s => (e.val.symm s).val.1) ∧
  HolomorphicOn e.val.target (fun s => (e.val.symm s).val.2)

/-- The complete local end construction. Its certificates are conclusions of
`exists_odd_end`, with no completion or affine surface structure assumed. -/
structure Data (P : Polynomial ℂ) (g : ℕ) where
  R : ℝ
  r : ℝ
  R_pos : 0 < R
  r_pos : 0 < r
  radius_le : r ^ 2 ≤ R
  h : ℂ → ℂ
  h_holomorphic : HolomorphicOn (Metric.ball 0 R) h
  h_nonzero : ∀ s ∈ Metric.ball 0 R, h s ≠ 0
  h_square : ∀ s ∈ Metric.ball 0 R, h s ^ 2 = P.reverse.eval s
  h_zero_square : h 0 ^ 2 = P.leadingCoeff
  leadingCoeff_ne_zero : P.leadingCoeff ≠ 0
  square_maps : ∀ t : ℂ, t ∈ Metric.ball 0 r → t ^ 2 ∈ Metric.ball 0 R
  u_holomorphic : HolomorphicOn (Metric.ball 0 r) (fun t => h (t ^ 2))
  u_even : ∀ t : ℂ, h ((-t) ^ 2) = h (t ^ 2)
  u_nonzero : ∀ t ∈ Metric.ball 0 r, h (t ^ 2) ≠ 0
  u_square : ∀ t ∈ Metric.ball 0 r, h (t ^ 2) ^ 2 = P.reverse.eval (t ^ 2)
  u_substitution : ∀ t ∈ puncturedDisk r,
    h (t ^ 2) ^ 2 = t ^ (4 * g + 2) * P.eval ((t⁻¹) ^ 2)
  exterior_w_nonzero : ∀ q ∈ exterior P r, q.val.2 ≠ 0
  chart : Surfaces.ComplexChart (AffineCurve P)
  chart_source : chart.val.source = exterior P r
  chart_target : chart.val.target = puncturedDisk r
  chart_apply : ∀ q ∈ exterior P r,
    chart.val q = h (q.val.1⁻¹) * q.val.1 ^ g / q.val.2
  chart_symm_z : ∀ t ∈ puncturedDisk r,
    (chart.val.symm t).val.1 = (t⁻¹) ^ 2
  chart_symm_w : ∀ t ∈ puncturedDisk r,
    (chart.val.symm t).val.2 = (t⁻¹) ^ (2 * g + 1) * h (t ^ 2)
  inverse_coordinates_holomorphic :
    HolomorphicOn (puncturedDisk r) (fun t => (chart.val.symm t).val.1) ∧
    HolomorphicOn (puncturedDisk r) (fun t => (chart.val.symm t).val.2)
  compatible : ∀ e : Surfaces.ComplexChart (AffineCurve P),
    GoodCoordinateChart e → Surfaces.CompatibleCharts chart e
  theta : puncturedDisk r → AffineCurve P
  theta_eq : ∀ t, theta t = chart.val.symm t
  theta_openEmbedding : Topology.IsOpenEmbedding theta
  theta_range : Set.range theta = exterior P r
  exterior_connected : IsConnected (exterior P r)
  inverse_base : ∀ t ∈ puncturedDisk r, ((chart.val.symm t).val.1)⁻¹ = t ^ 2
  base_analytic : AnalyticAt ℂ (fun t : ℂ => t ^ 2) 0
  base_order : analyticOrderAt (fun t : ℂ => t ^ 2) 0 = 2

end D12Complex.HyperellipticOddEnd

namespace Specs.D12Complex.Ch21.HyperellipticOddEnd
open _root_.D12Complex.HyperellipticOddEnd

def exists_odd_end_type : Prop :=
  ∀ (P : Polynomial ℂ) (g : ℕ), Squarefree P → P.natDegree = 2 * g + 1 →
    Nonempty (Data P g)

end Specs.D12Complex.Ch21.HyperellipticOddEnd
