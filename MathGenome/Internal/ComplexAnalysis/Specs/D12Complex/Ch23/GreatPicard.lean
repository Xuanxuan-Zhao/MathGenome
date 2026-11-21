import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch23.TwoOmissionsPunctureExtension

/-!
Great Picard, paper.tex:4279–4318 (d12:23-05).
The exceptional set uses a single existentially quantified radius for each
value. Its subsingleton conclusion therefore holds across all neighborhoods,
not just separately on each fixed punctured disk. Infinitude means infinitely
many distinct points, rather than an assertion about multiplicities.
-/

namespace Specs.D12Complex.Ch23.GreatPicard

open _root_.D12Complex

def finitePreimageValues_type := (ℂ → ℂ) → ℂ → ℝ → Set ℂ

def finitePreimageValues_value : finitePreimageValues_type :=
  fun f a R => {v | ∃ r : ℝ, 0 < r ∧ r < R ∧
    ({z : ℂ | z ∈ puncturedDisk a r ∧ f z = v} : Set ℂ).Finite}

/-- Both finite-preimage values become omitted on one common smaller disk. -/
def two_finite_preimages_omitted_type : Prop :=
  ∀ (a : ℂ) (R : ℝ) (f : ℂ → ℂ) (u v : ℂ),
    u ∈ finitePreimageValues_value f a R → v ∈ finitePreimageValues_value f a R →
    ∃ r : ℝ, 0 < r ∧ r < R ∧
      (∀ z ∈ puncturedDisk a r, f z ≠ u) ∧
      (∀ z ∈ puncturedDisk a r, f z ≠ v)

/-- There is at most one finite-preimage value, globally across neighborhoods. -/
def exceptional_values_subsingleton_type : Prop :=
  ∀ (a : ℂ) (R : ℝ) (f : ℂ → ℂ), 0 < R →
    HolomorphicOn (puncturedDisk a R) f → EssentialSingularityAt f a →
    (finitePreimageValues_value f a R).Subsingleton

/-- Every value outside the exceptional set has infinitely many preimages in
every punctured neighborhood, including radii larger than the original disk. -/
def infinite_preimages_type : Prop :=
  ∀ (a : ℂ) (R : ℝ) (f : ℂ → ℂ), 0 < R →
    ∀ v : ℂ, v ∉ finitePreimageValues_value f a R →
    ∀ r : ℝ, 0 < r →
      ({z : ℂ | z ∈ puncturedDisk a r ∧ f z = v} : Set ℂ).Infinite

/-- One exceptional value can be chosen independently of the neighborhood. -/
def exists_global_exception_type : Prop :=
  ∀ (a : ℂ) (R : ℝ) (f : ℂ → ℂ), 0 < R →
    HolomorphicOn (puncturedDisk a R) f → EssentialSingularityAt f a →
    ∃ e : ℂ, ∀ v : ℂ, v ≠ e → ∀ r : ℝ, 0 < r →
      ({z : ℂ | z ∈ puncturedDisk a r ∧ f z = v} : Set ℂ).Infinite

end Specs.D12Complex.Ch23.GreatPicard
