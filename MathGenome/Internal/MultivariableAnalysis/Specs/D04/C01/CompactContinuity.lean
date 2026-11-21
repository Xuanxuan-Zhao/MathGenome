import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.EuclideanInterfaces

/-! Independent statements for `chapters/01.tex`, `d04:01:compact-continuity`.
The domain is the actual subtype K, so its image is `Set.range f`.
The first three conclusions allow empty K and dimensions zero.
For the scalar conclusion, E 1 has the single real coordinate indexed by 0;
the extremal points are elements of K itself. -/

namespace Specs.D04.C01.CompactContinuity
open Specs.D04.C01.EuclideanInterfaces.Model

def compact_imageType : Prop :=
  ∀ {n m : ℕ} (K : Set (E n)) (f : K → E m),
    Compact K → RelativeContinuous K f → Compact (Set.range f)

def bounded_of_compactType : Prop :=
  ∀ {n m : ℕ} (K : Set (E n)) (f : K → E m),
    Compact K → RelativeContinuous K f → ∃ B : ℝ, ∀ x : K, ‖f x‖ ≤ B

def uniformContinuous_of_compactType : Prop :=
  ∀ {n m : ℕ} (K : Set (E n)) (f : K → E m),
    Compact K → RelativeContinuous K f → RelativeUniformContinuous K f

def exists_min_max_of_compactType : Prop :=
  ∀ {n : ℕ} (K : Set (E n)) (f : K → E 1),
    Compact K → RelativeContinuous K f → K.Nonempty →
      ∃ x_min x_max : K, ∀ x : K,
        f x_min 0 ≤ f x 0 ∧ f x 0 ≤ f x_max 0

end Specs.D04.C01.CompactContinuity
