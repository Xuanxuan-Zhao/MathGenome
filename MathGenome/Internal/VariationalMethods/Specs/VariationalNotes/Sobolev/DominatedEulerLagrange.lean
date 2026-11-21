import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.Spaces
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.CaratheodoryIntegrands
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Distribution.Distribution

noncomputable section
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal InnerProductSpace Topology

namespace VariationalNotes.Sobolev.EulerLagrange

/-- The classical Jacobian of a smooth vector test, with target index first. -/
def testGradient {d m : ℕ} {Ω : Opens (Domain d)} (φ : VectorTest Ω m)
    (x : Domain d) : Gradient m d :=
  WithLp.toLp 2 (fun ij =>
    ((TestFunction.lineDerivCLM ℝ (P102.U4.coordinateVector d ij.2) φ :
      VectorTest Ω m) x) ij.1)

/-- The derivative in the state and matrix variables, using the source pairings. -/
def fiberDerivative {d m : ℕ} (a : Vector m) (b : Gradient m d) :
    (Vector m × Gradient m d) →L[ℝ] ℝ :=
  (innerSL ℝ a).comp (ContinuousLinearMap.fst ℝ _ _) +
    (innerSL ℝ b).comp (ContinuousLinearMap.snd ℝ _ _)

/-- Continuous first derivatives outside a single common exceptional set. -/
def HasContinuousFiberDerivative {d m : ℕ} (Ω : Opens (Domain d))
    (F : Domain d → Vector m → Gradient m d → ℝ)
    (Fs : Domain d → Vector m → Gradient m d → Vector m)
    (FZ : Domain d → Vector m → Gradient m d → Gradient m d) : Prop :=
  ∀ᵐ x ∂domainMeasure Ω,
    (∀ y : Vector m × Gradient m d,
      HasFDerivAt (fun y => F x y.1 y.2)
        (fiberDerivative (Fs x y.1 y.2) (FZ x y.1 y.2)) y) ∧
    Continuous (fun y : Vector m × Gradient m d => Fs x y.1 y.2) ∧
    Continuous (fun y : Vector m × Gradient m d => FZ x y.1 y.2)

/-- The directional derivative along the actual smooth variation. -/
def variationDensity {d m : ℕ} {Ω : Opens (Domain d)}
    (Fs : Domain d → Vector m → Gradient m d → Vector m)
    (FZ : Domain d → Vector m → Gradient m d → Gradient m d)
    (u : Domain d → Vector m) (U : Domain d → Gradient m d)
    (φ : VectorTest Ω m) (t : ℝ) (x : Domain d) : ℝ :=
  ⟪Fs x (u x + t • φ x) (U x + t • testGradient φ x), φ x⟫_ℝ +
    frobenius (FZ x (u x + t • φ x) (U x + t • testGradient φ x)) (testGradient φ x)

/-- Energy on the line through a Sobolev representative. Since `φ` is smooth,
its classical Jacobian is also its weak Jacobian. All energies use the canonical
signed extended integral and are invariant under changes of representative. -/
def lineEnergy {d m : ℕ} {Ω : Opens (Domain d)}
    (F : Domain d → Vector m → Gradient m d → ℝ)
    (u : Domain d → Vector m) (U : Domain d → Gradient m d)
    (φ : VectorTest Ω m) (t : ℝ) : EReal :=
  energyOnFields Ω F (fun x => u x + t • φ x)
    (fun x => U x + t • testGradient φ x)

/-- The weak Euler--Lagrange pairing on arbitrary coefficient fields. -/
def weakDensity {d m : ℕ} {Ω : Opens (Domain d)}
    (A : Domain d → Vector m) (B : Domain d → Gradient m d)
    (φ : VectorTest Ω m) (x : Domain d) : ℝ :=
  ⟪A x, φ x⟫_ℝ + frobenius (B x) (testGradient φ x)

/-- The distributional divergence of one row, with the usual minus sign on tests. -/
def rowDivergence {d m : ℕ} (Ω : Opens (Domain d))
    (B : Domain d → Gradient m d) (i : Fin m) : Distribution Ω ℝ ⊤ :=
  ∑ j : Fin d, Distribution.lineDerivCLM (P102.U4.coordinateVector d j)
    (Distribution.ofFun Ω (fun x => B x (i,j)) volume ⊤)

namespace Expected

/-- No integrability of individual flux components is imposed in this theorem. -/
def FieldStationarity : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent)
    (u : W1p Ω m p)
    (F : Domain d → Vector m → Gradient m d → ℝ)
    (Fs : Domain d → Vector m → Gradient m d → Vector m)
    (FZ : Domain d → Vector m → Gradient m d → Gradient m d),
    CaratheodorySpecs.Caratheodory (domainMeasure Ω) (fun x (y : Vector m × Gradient m d) => F x y.1 y.2) →
    HasContinuousFiberDerivative Ω F Fs FZ →
    (∃ r : ℝ, energy Ω m p F u = r) →
    (∀ φ : VectorTest Ω m,
      IsLocalMin (lineEnergy F (value Ω m p u) (gradient Ω m p u) φ) 0) →
    (∀ φ : VectorTest Ω m, ∃ (ε : ℝ) (b : Domain d → ℝ),
      0 < ε ∧ Integrable b (domainMeasure Ω) ∧
      ∀ᵐ x ∂domainMeasure Ω, ∀ t : ℝ, |t| < ε →
        |variationDensity Fs FZ (value Ω m p u) (gradient Ω m p u) φ t x| ≤ b x) →
    ∀ φ : VectorTest Ω m,
      Integrable (weakDensity
        (fun x => Fs x (value Ω m p u x) (gradient Ω m p u x))
        (fun x => FZ x (value Ω m p u x) (gradient Ω m p u x)) φ) (domainMeasure Ω) ∧
      (∫ x, weakDensity
        (fun x => Fs x (value Ω m p u x) (gradient Ω m p u x))
        (fun x => FZ x (value Ω m p u x) (gradient Ω m p u x)) φ x ∂domainMeasure Ω) = 0

/-- No integrability of individual flux components is imposed in this theorem. -/
def DominatedStationarity : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent)
    (u : W1p Ω m p)
    (F : Domain d → Vector m → Gradient m d → ℝ)
    (Fs : Domain d → Vector m → Gradient m d → Vector m)
    (FZ : Domain d → Vector m → Gradient m d → Gradient m d),
    CaratheodorySpecs.Caratheodory (domainMeasure Ω) (fun x (y : Vector m × Gradient m d) => F x y.1 y.2) →
    HasContinuousFiberDerivative Ω F Fs FZ →
    (∃ r : ℝ, energy Ω m p F u = r) →
    (∀ (φ : VectorTest Ω m) (w : W1p Ω m p),
      value Ω m p w = testToValueLp Ω m p φ →
      IsLocalMin (fun t : ℝ => energy Ω m p F (u + t • w)) 0) →
    (∀ φ : VectorTest Ω m, ∃ (ε : ℝ) (b : Domain d → ℝ),
      0 < ε ∧ Integrable b (domainMeasure Ω) ∧
      ∀ᵐ x ∂domainMeasure Ω, ∀ t : ℝ, |t| < ε →
        |variationDensity Fs FZ (value Ω m p u) (gradient Ω m p u) φ t x| ≤ b x) →
    ∀ φ : VectorTest Ω m,
      Integrable (weakDensity
        (fun x => Fs x (value Ω m p u x) (gradient Ω m p u x))
        (fun x => FZ x (value Ω m p u x) (gradient Ω m p u x)) φ) (domainMeasure Ω) ∧
      (∫ x, weakDensity
        (fun x => Fs x (value Ω m p u x) (gradient Ω m p u x))
        (fun x => FZ x (value Ω m p u x) (gradient Ω m p u x)) φ x ∂domainMeasure Ω) = 0

/-- The weak identity is precisely the row-wise distributional equation when
its coefficients are locally integrable. -/
def DistributionalEquation : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d))
    (A : Domain d → Vector m) (B : Domain d → Gradient m d),
    (∀ i, LocallyIntegrableOn (fun x => A x i) Ω volume) →
    (∀ i j, LocallyIntegrableOn (fun x => B x (i,j)) Ω volume) →
    ((∀ φ : VectorTest Ω m, (∫ x, weakDensity A B φ x ∂domainMeasure Ω) = 0) ↔
      ∀ i : Fin m, Distribution.ofFun Ω (fun x => A x i) volume ⊤ - rowDivergence Ω B i = 0)

/-- A continuous representative of the distributional divergence agrees
pointwise with the continuous state derivative. -/
def PointwiseEquation : Prop :=
  ∀ {d m : ℕ} (Ω : Opens (Domain d))
    (A : Domain d → Vector m) (B : Domain d → Gradient m d)
    (q : Domain d → Vector m),
    ContinuousOn A Ω → ContinuousOn q Ω →
    (∀ i : Fin m, Distribution.ofFun Ω (fun x => A x i) volume ⊤ - rowDivergence Ω B i = 0) →
    (∀ i : Fin m, rowDivergence Ω B i = Distribution.ofFun Ω (fun x => q x i) volume ⊤) →
    ∀ x ∈ Ω, A x = q x

end Expected
end VariationalNotes.Sobolev.EulerLagrange
