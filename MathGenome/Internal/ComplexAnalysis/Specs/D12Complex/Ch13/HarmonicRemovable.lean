import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.HarmonicFoundation

/-! Bounded harmonic punctures and the failure without boundedness,
paper.tex:2597–2603. Harmonicity uses the canonical C² Laplacian predicate.
Uniqueness is on the disk, since representatives are total functions. -/
noncomputable section
open Set Metric
namespace Specs.D12Complex.Ch13.HarmonicRemovable
open _root_.D12Complex

def bounded_harmonic_removable_type : Prop :=
  ∀ (a : ℂ) (R : ℝ) (u : ℂ → ℝ), 0 < R →
    HarmonicOn (ball a R \ {a}) u →
    (∃ M : ℝ, ∀ z ∈ ball a R \ {a}, |u z| ≤ M) →
    ∃ v : ℂ → ℝ, HarmonicOn (ball a R) v ∧
      EqOn v u (ball a R \ {a}) ∧
      ∀ v' : ℂ → ℝ, HarmonicOn (ball a R) v' →
        EqOn v' u (ball a R \ {a}) → EqOn v' v (ball a R)

def locally_bounded_harmonic_removable_type : Prop :=
  ∀ (a : ℂ) (R : ℝ) (u : ℂ → ℝ), 0 < R →
    HarmonicOn (ball a R \ {a}) u →
    (∃ r : ℝ, 0 < r ∧ r ≤ R ∧
      ∃ M : ℝ, ∀ z ∈ ball a r \ {a}, |u z| ≤ M) →
    ∃ v : ℂ → ℝ, HarmonicOn (ball a R) v ∧
      EqOn v u (ball a R \ {a}) ∧
      ∀ v' : ℂ → ℝ, HarmonicOn (ball a R) v' →
        EqOn v' u (ball a R \ {a}) → EqOn v' v (ball a R)

def log_norm_harmonic_type : Prop :=
  ∀ (a : ℂ) (R : ℝ), 0 < R →
    HarmonicOn (ball a R \ {a}) (fun z => Real.log ‖z - a‖)

def log_norm_no_continuous_extension_type : Prop :=
  ∀ (a : ℂ) (R : ℝ), 0 < R →
    ¬ ∃ v : ℂ → ℝ, ContinuousAt v a ∧
      EqOn v (fun z => Real.log ‖z - a‖) (ball a R \ {a})

def log_norm_no_harmonic_extension_type : Prop :=
  ∀ (a : ℂ) (R : ℝ), 0 < R →
    ¬ ∃ v : ℂ → ℝ, HarmonicOn (ball a R) v ∧
      EqOn v (fun z => Real.log ‖z - a‖) (ball a R \ {a})

end Specs.D12Complex.Ch13.HarmonicRemovable
