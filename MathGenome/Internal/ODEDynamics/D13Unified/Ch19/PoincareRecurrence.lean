import MathGenome.Internal.ODEDynamics.D13Unified.Ch19.MeasureDefinitions
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.PoincareRecurrence
import Mathlib.Dynamics.Ergodic.Conservative

/-! Poincare recurrence on an arbitrary finite measure space. -/

namespace D13Unified.Ch19.PoincareRecurrence

universe u
open Set Filter MeasureTheory
open D13Unified.Ch19.MeasureDefinitions

/-- `paper.tex`, Theorem `d13:19:poincare-recurrence`, including finite measures
of arbitrary total mass and infinitely many return times greater than zero. -/
theorem poincare_recurrence :
    ∀ {X : Type u} [MeasurableSpace X] (T : X → X) (μ : Measure X)
      [IsFiniteMeasure μ],
      PreservesMeasure T μ →
      ∀ E : Set X, MeasurableSet E →
        ∀ᵐ x ∂μ, x ∈ E → Set.Infinite {n : ℕ | 1 ≤ n ∧ T^[n] x ∈ E} := by
  intro X _ T μ _ hT E hE
  -- The canonical preservation predicate is native measure preservation.
  -- Finiteness supplies conservativity, without an inverse or normalization.
  have hconservative : Conservative T μ :=
    (hT : MeasurePreserving T μ μ).conservative
  filter_upwards [hconservative.ae_mem_imp_frequently_image_mem hE.nullMeasurableSet]
    with x hx
  intro hxE
  -- Excluding time zero preserves frequent recurrence, hence infinitude.
  apply Nat.frequently_atTop_iff_infinite.mp
  exact ((hx hxE).and_eventually (eventually_ge_atTop 1)).mono
    (fun _ hn => ⟨hn.2, hn.1⟩)

end D13Unified.Ch19.PoincareRecurrence
