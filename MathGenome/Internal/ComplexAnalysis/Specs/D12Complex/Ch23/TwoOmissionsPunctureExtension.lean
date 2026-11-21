import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.Singularities

/-!
The puncture-extension step in the proof of Great Picard,
paper.tex:4284–4308. Only weak holomorphy on the whole punctured disk is
assumed. The total representative's value at the puncture is unrestricted.
The pole alternative uses the canonical finite, strictly positive exact order.
-/
namespace Specs.D12Complex.Ch23.TwoOmissionsPunctureExtension
open _root_.D12Complex

/-- The normalized two-omissions assertion, retaining both possible extensions. -/
def zero_one_puncture_extension_type : Prop :=
  ∀ (a : ℂ) (R : ℝ) (f : ℂ → ℂ), 0 < R →
    HolomorphicOn (puncturedDisk a R) f →
    (∀ z ∈ puncturedDisk a R, f z ≠ 0) →
    (∀ z ∈ puncturedDisk a R, f z ≠ 1) →
    RemovableSingularityAt f a ∨ PoleAt f a

/-- Arbitrary distinct omitted finite values, with the original function in the conclusion. -/
def two_omissions_puncture_extension_type : Prop :=
  ∀ (a : ℂ) (R : ℝ) (f : ℂ → ℂ) (u v : ℂ), 0 < R →
    HolomorphicOn (puncturedDisk a R) f → u ≠ v →
    (∀ z ∈ puncturedDisk a R, f z ≠ u) →
    (∀ z ∈ puncturedDisk a R, f z ≠ v) →
    RemovableSingularityAt f a ∨ PoleAt f a

/-- In particular, such a puncture cannot be essential. -/
def not_essential_of_two_omissions_type : Prop :=
  ∀ (a : ℂ) (R : ℝ) (f : ℂ → ℂ) (u v : ℂ), 0 < R →
    HolomorphicOn (puncturedDisk a R) f → u ≠ v →
    (∀ z ∈ puncturedDisk a R, f z ≠ u) →
    (∀ z ∈ puncturedDisk a R, f z ≠ v) →
    ¬ EssentialSingularityAt f a

end Specs.D12Complex.Ch23.TwoOmissionsPunctureExtension
