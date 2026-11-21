import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Iterations.ResidualCertificate
import Mathlib.Tactic.Linarith

/-! Residual certificates on an invariant metric contraction domain.
These proofs use the triangle inequality and contraction at `x` and `p` only. -/
namespace NumAnalysis206.Iterations

universe u

theorem distance_le_residual {X : Type u} [MetricSpace X] (D : Set X) (T : X → X)
    (q : ℝ) (_hq0 : 0 ≤ q) (hq1 : q < 1) (_hinv : Set.MapsTo T D D)
    (hcontract : ∀ a ∈ D, ∀ b ∈ D, dist (T a) (T b) ≤ q * dist a b)
    (p : X) (hp : p ∈ D) (hfixed : T p = p) (x : X) (hx : x ∈ D) :
    dist x p ≤ dist x (T x) / (1 - q) := by
  have hstep : dist x p ≤ dist x (T x) + q * dist x p := by
    calc
      dist x p ≤ dist x (T x) + dist (T x) p := dist_triangle _ _ _
      _ ≤ dist x (T x) + q * dist x p := by
        exact add_le_add le_rfl (by simpa only [hfixed] using hcontract x hx p hp)
  apply (le_div_iff₀ (sub_pos.mpr hq1)).2
  nlinarith

theorem distance_le_residual_upper_bound {X : Type u} [MetricSpace X] (D : Set X) (T : X → X)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hinv : Set.MapsTo T D D)
    (hcontract : ∀ a ∈ D, ∀ b ∈ D, dist (T a) (T b) ≤ q * dist a b)
    (p : X) (hp : p ∈ D) (hfixed : T p = p) (x : X) (hx : x ∈ D)
    (R : ℝ) (hR : dist x (T x) ≤ R) :
    dist x p ≤ R / (1 - q) := by
  exact (distance_le_residual D T q hq0 hq1 hinv hcontract p hp hfixed x hx).trans
    (div_le_div_of_nonneg_right hR (sub_nonneg.mpr hq1.le))

theorem residual_stopping {X : Type u} [MetricSpace X] (D : Set X) (T : X → X)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hinv : Set.MapsTo T D D)
    (hcontract : ∀ a ∈ D, ∀ b ∈ D, dist (T a) (T b) ≤ q * dist a b)
    (p : X) (hp : p ∈ D) (hfixed : T p = p) (x : X) (hx : x ∈ D)
    (ε R : ℝ) (_hε : 0 < ε) (hR : dist x (T x) ≤ R)
    (hstop : R ≤ (1 - q) * ε) :
    dist x p ≤ ε := by
  have hbound := distance_le_residual_upper_bound D T q hq0 hq1 hinv hcontract
    p hp hfixed x hx R hR
  exact hbound.trans ((div_le_iff₀ (sub_pos.mpr hq1)).2 (by nlinarith))

theorem approximate_residual_le {X : Type u} [MetricSpace X] (T : X → X) (x y : X)
    (δ : ℝ) (herror : dist y (T x) ≤ δ) :
    dist x (T x) ≤ dist x y + δ := by
  exact (dist_triangle x y (T x)).trans (add_le_add le_rfl herror)

theorem distance_le_approximate_residual_upper_bound {X : Type u} [MetricSpace X] (D : Set X) (T : X → X)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hinv : Set.MapsTo T D D)
    (hcontract : ∀ a ∈ D, ∀ b ∈ D, dist (T a) (T b) ≤ q * dist a b)
    (p : X) (hp : p ∈ D) (hfixed : T p = p) (x : X) (hx : x ∈ D)
    (y : X) (δ R : ℝ) (herror : dist y (T x) ≤ δ) (hR : dist x y ≤ R) :
    dist x p ≤ (R + δ) / (1 - q) := by
  apply distance_le_residual_upper_bound D T q hq0 hq1 hinv hcontract p hp hfixed x hx
  exact (approximate_residual_le T x y δ herror).trans (add_le_add hR le_rfl)

theorem approximate_residual_stopping {X : Type u} [MetricSpace X] (D : Set X) (T : X → X)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hinv : Set.MapsTo T D D)
    (hcontract : ∀ a ∈ D, ∀ b ∈ D, dist (T a) (T b) ≤ q * dist a b)
    (p : X) (hp : p ∈ D) (hfixed : T p = p) (x : X) (hx : x ∈ D)
    (y : X) (δ ε R : ℝ) (hε : 0 < ε)
    (herror : dist y (T x) ≤ δ) (hR : dist x y ≤ R)
    (hstop : R + δ ≤ (1 - q) * ε) :
    dist x p ≤ ε := by
  apply residual_stopping D T q hq0 hq1 hinv hcontract p hp hfixed x hx ε (R + δ) hε
  · exact (approximate_residual_le T x y δ herror).trans (add_le_add hR le_rfl)
  · exact hstop

end NumAnalysis206.Iterations
