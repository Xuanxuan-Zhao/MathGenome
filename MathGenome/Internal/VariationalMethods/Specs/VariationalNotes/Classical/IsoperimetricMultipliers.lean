import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.FirstVariation

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff

namespace VariationalNotes.Classical.IsoperimetricMultipliers

/-- The first variation on the actual endpoint-zero C¹ space. -/
def firstVariation {I : Interval} {m : ℕ} (L : Lagrangian m) (u η : C1Curve I m) : ℝ :=
  ∫ t in I.a..I.b, variationDensity (momentumField L u) (stateGradientField L u)
    (stateField I m η) (velocityField I m η) t

def constraintDerivative {I : Interval} {m k : ℕ} (Ls : Fin k → Lagrangian m)
    (u : C1Curve I m) (η : endpointZero I m) : Fin k → ℝ :=
  fun i => firstVariation (Ls i) u η

/-- All competitors have the same endpoints and all their graphs are admissible.
The neighborhood is in the C¹ norm, exactly as in the source. -/
def constrainedLocalMinimum {I : Interval} {m k : ℕ} (L : Lagrangian m)
    (Ls : Fin k → Lagrangian m) (u : C1Curve I m) : Prop :=
  graphAdmissible L u ∧ (∀ i, graphAdmissible (Ls i) u) ∧
    ∃ ε > 0, ∀ v : C1Curve I m,
      v - u ∈ endpointZero I m → graphAdmissible L v →
      (∀ i, graphAdmissible (Ls i) v) →
      (∀ i, action (Ls i) v = action (Ls i) u) →
      ‖v - u‖ < ε → action L u ≤ action L v

def augmented {m k : ℕ} (L : Lagrangian m) (Ls : Fin k → Lagrangian m)
    (lam0 : ℝ) (lam : Fin k → ℝ) : Lagrangian m where
  domain := L.domain ∩ ⋂ i, (Ls i).domain
  isOpen_domain := L.isOpen_domain.inter (isOpen_iInter_of_finite fun i => (Ls i).isOpen_domain)
  value := fun x => lam0 * L.value x + ∑ i, lam i * (Ls i).value x

def stationary {I : Interval} {m k : ℕ} (L : Lagrangian m)
    (Ls : Fin k → Lagrangian m) (u : C1Curve I m) (lam0 : ℝ) (lam : Fin k → ℝ) : Prop :=
  ∀ η : endpointZero I m,
    lam0 * firstVariation L u η + ∑ i, lam i * constraintDerivative Ls u η i = 0

/-- This uses the momentum and state gradient of the augmented integrand itself. -/
def augmentedEulerLagrange {I : Interval} {m k : ℕ} (L : Lagrangian m)
    (Ls : Fin k → Lagrangian m) (u : C1Curve I m) (lam0 : ℝ) (lam : Fin k → ℝ) : Prop :=
  let A := augmented L Ls lam0 lam
  WeakDerivativeInterval m I.a I.b (momentumField A u) (stateGradientField A u) ∧
    ContDiffOn ℝ 1 (momentumField A u) (Ioo I.a I.b) ∧
    ∀ t ∈ Ioo I.a I.b, HasDerivAt (momentumField A u) (stateGradientField A u t) t

namespace Specs

def IsoperimetricMultipliersType : Prop :=
  ∀ (I : Interval) (m k : ℕ) (L : Lagrangian m) (Ls : Fin k → Lagrangian m)
    (u : C1Curve I m), regularNearGraph L u 1 →
    (∀ i, regularNearGraph (Ls i) u 1) → constrainedLocalMinimum L Ls u →
    (∃ (lam0 : ℝ) (lam : Fin k → ℝ), 0 ≤ lam0 ∧ (lam0 ≠ 0 ∨ lam ≠ 0) ∧
      stationary L Ls u lam0 lam ∧ augmentedEulerLagrange L Ls u lam0 lam) ∧
    (Function.Surjective (constraintDerivative Ls u) →
      ∃! lam : Fin k → ℝ, stationary L Ls u 1 lam ∧ augmentedEulerLagrange L Ls u 1 lam) ∧
    (¬ Function.Surjective (constraintDerivative Ls u) →
      ∃ lam : Fin k → ℝ, lam ≠ 0 ∧ stationary L Ls u 0 lam ∧
        augmentedEulerLagrange L Ls u 0 lam)

/-- With no constraints the coefficient of J is one and the constraint vector
is the unique empty vector. -/
def EmptyConstraintsType : Prop :=
  ∀ (I : Interval) (m : ℕ) (L : Lagrangian m) (u : C1Curve I m),
    regularNearGraph L u 1 →
    constrainedLocalMinimum L (fun i : Fin 0 => Fin.elim0 i) u →
    stationary L (fun i : Fin 0 => Fin.elim0 i) u 1 0 ∧
    augmentedEulerLagrange L (fun i : Fin 0 => Fin.elim0 i) u 1 0

end Specs
end VariationalNotes.Classical.IsoperimetricMultipliers
