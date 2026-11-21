import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeInterfaces
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! The closed ball is the metric closed ball, including radius zero. Neighborhoods
may depend on the sequence index. No common open neighborhood is assumed. -/
noncomputable section
open Set Filter Topology
namespace Specs.D04.C08.UniformC1Limit
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model

/-- Full uniform limit statement with the total, operator-valued derivative. -/
def uniform_c1_limitType : Prop :=
  ∀ {m k : ℕ} (p : E m) (r : ℝ) (hr : 0 ≤ r)
    (f : ℕ → E m → E k) (G : E m → E m →L[ℝ] E k),
    (∀ j, ∃ U : Set (E m), IsOpen U ∧ Metric.closedBall p r ⊆ U ∧ CrOn 1 U (f j)) →
    (∃ a : E k, Tendsto (fun j => f j p) atTop (𝓝 a)) →
    TendstoUniformlyOn (fun j => totalDerivative (f j)) G atTop (Metric.closedBall p r) →
    ∃ F : E m → E k,
      TendstoUniformlyOn f F atTop (Metric.closedBall p r) ∧
      ContinuousOn G (Metric.closedBall p r) ∧
      CrOn 1 (interior (Metric.closedBall p r)) F ∧
      (∀ x ∈ interior (Metric.closedBall p r),
        HasTotalDerivative (interior (Metric.closedBall p r)) F (G x) x ∧
        totalDerivative F x = G x)

/-- The suprema are finite because the individual derivatives are continuous on
this compact ball; the ball is nonempty even when r = 0. -/
def uniform_c1_cauchy_estimateType : Prop :=
  ∀ {m k : ℕ} (p : E m) (r : ℝ) (hr : 0 ≤ r) (f : ℕ → E m → E k),
    (∀ j, ∃ U : Set (E m), IsOpen U ∧ Metric.closedBall p r ⊆ U ∧ CrOn 1 U (f j)) →
    ∀ j l : ℕ,
      sSup ((fun x => ‖f j x - f l x‖) '' Metric.closedBall p r) ≤
        ‖f j p - f l p‖ + r *
          sSup ((fun x => ‖totalDerivative (f j) x - totalDerivative (f l) x‖) ''
            Metric.closedBall p r)

/-- At zero radius uniform convergence is precisely convergence at the base point;
in positive dimension there is no interior assertion. -/
def uniform_c1_zero_radiusType : Prop :=
  ∀ {m k : ℕ} (p : E m) (f : ℕ → E m → E k) (F : E m → E k),
    (TendstoUniformlyOn f F atTop (Metric.closedBall p 0) ↔
      Tendsto (fun j => f j p) atTop (𝓝 (F p))) ∧
    (0 < m → interior (Metric.closedBall p 0) = ∅)

/-- In dimension zero the ball is the whole singleton and is open, every map is
C¹, and every operator out of the parameter space is zero. -/
def uniform_c1_zero_dimensionType : Prop :=
  ∀ {k : ℕ} (p : E 0) (r : ℝ) (hr : 0 ≤ r) (F : E 0 → E k)
    (G : E 0 → E 0 →L[ℝ] E k),
    interior (Metric.closedBall p r) = univ ∧
    CrOn 1 (interior (Metric.closedBall p r)) F ∧
    ∀ x, totalDerivative F x = 0 ∧ G x = 0

end Specs.D04.C08.UniformC1Limit
