import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Independent finite closed-interval differentiability contract.
The functions in a jet are only constrained on the closed interval.
A natural-number index is used; entries above `r` carry no conditions. -/
namespace NumAnalysis206.Approximation.IntervalCalculusSpec
open Set

/-- Continuous derivative data, with derivatives taken within the interval. -/
def jetValue (a b : ℝ) (r : ℕ) (f : ℝ → ℝ) (D : ℕ → ℝ → ℝ) : Prop :=
  EqOn (D 0) f (Icc a b) ∧
  (∀ j, j ≤ r → ContinuousOn (D j) (Icc a b)) ∧
  (∀ j, j < r → ∀ t ∈ Icc a b,
    HasDerivWithinAt (D j) (D (j + 1) t) (Icc a b) t)

def jetType := ℝ → ℝ → ℕ → (ℝ → ℝ) → (ℕ → ℝ → ℝ) → Prop

/-- `C^r[a,b]`, with no condition on the function outside `[a,b]`. -/
def smoothValue (a b : ℝ) (r : ℕ) (f : ℝ → ℝ) : Prop :=
  ∃ D, jetValue a b r f D

def smoothType := ℝ → ℝ → ℕ → (ℝ → ℝ) → Prop

def jet_eq_iterated_type : Prop :=
  ∀ {a b : ℝ} {r : ℕ} {f : ℝ → ℝ} {D : ℕ → ℝ → ℝ},
    a < b → jetValue a b r f D → ∀ j, j ≤ r →
      EqOn (D j) (iteratedDerivWithin j f (Icc a b)) (Icc a b)

def jet_to_contDiff_type : Prop :=
  ∀ {a b : ℝ} {r : ℕ} {f : ℝ → ℝ} {D : ℕ → ℝ → ℝ},
    a ≤ b → jetValue a b r f D → ContDiffOn ℝ r f (Icc a b)

def jet_of_contDiff_type : Prop :=
  ∀ {a b : ℝ} {r : ℕ} {f : ℝ → ℝ}, a < b →
    ContDiffOn ℝ r f (Icc a b) →
      jetValue a b r f (fun j => iteratedDerivWithin j f (Icc a b))

def smooth_iff_contDiff_type : Prop :=
  ∀ {a b : ℝ} {r : ℕ} {f : ℝ → ℝ}, a ≤ b →
    (smoothValue a b r f ↔ ContDiffOn ℝ r f (Icc a b))

def jet_restrict_type : Prop :=
  ∀ {a b c d : ℝ} {r : ℕ} {f : ℝ → ℝ} {D : ℕ → ℝ → ℝ},
    a ≤ c → d ≤ b → jetValue a b r f D → jetValue c d r f D

def smooth_restrict_type : Prop :=
  ∀ {a b c d : ℝ} {r : ℕ} {f : ℝ → ℝ},
    a ≤ c → d ≤ b → smoothValue a b r f → smoothValue c d r f

def jet_congr_type : Prop :=
  ∀ {a b : ℝ} {r : ℕ} {f g : ℝ → ℝ} {D : ℕ → ℝ → ℝ},
    EqOn f g (Icc a b) → (jetValue a b r f D ↔ jetValue a b r g D)

def smooth_congr_type : Prop :=
  ∀ {a b : ℝ} {r : ℕ} {f g : ℝ → ℝ},
    EqOn f g (Icc a b) → (smoothValue a b r f ↔ smoothValue a b r g)

def jet_unique_type : Prop :=
  ∀ {a b : ℝ} {r : ℕ} {f g : ℝ → ℝ} {D E : ℕ → ℝ → ℝ},
    a < b → EqOn f g (Icc a b) → jetValue a b r f D → jetValue a b r g E →
      ∀ j, j ≤ r → EqOn (D j) (E j) (Icc a b)

def iterated_congr_type : Prop :=
  ∀ {a b : ℝ} {f g : ℝ → ℝ}, EqOn f g (Icc a b) → ∀ j,
    EqOn (iteratedDerivWithin j f (Icc a b))
      (iteratedDerivWithin j g (Icc a b)) (Icc a b)

def jet_singleton_type : Prop :=
  ∀ {a : ℝ} {r : ℕ} {f : ℝ → ℝ} {D : ℕ → ℝ → ℝ},
    jetValue a a r f D ↔ D 0 a = f a

def smooth_singleton_type : Prop :=
  ∀ (a : ℝ) (r : ℕ) (f : ℝ → ℝ), smoothValue a a r f

def smooth_zero_type : Prop :=
  ∀ (a b : ℝ) (f : ℝ → ℝ), smoothValue a b 0 f ↔ ContinuousOn f (Icc a b)

def jet_truncate_type : Prop :=
  ∀ {a b : ℝ} {r q : ℕ} {f : ℝ → ℝ} {D : ℕ → ℝ → ℝ},
    q ≤ r → jetValue a b r f D → jetValue a b q f D

def jet_left_deriv_type : Prop :=
  ∀ {a b : ℝ} {r : ℕ} {f : ℝ → ℝ} {D : ℕ → ℝ → ℝ},
    a < b → jetValue a b r f D → ∀ j, j < r →
      HasDerivWithinAt (D j) (D (j + 1) a) (Ici a) a

def jet_right_deriv_type : Prop :=
  ∀ {a b : ℝ} {r : ℕ} {f : ℝ → ℝ} {D : ℕ → ℝ → ℝ},
    a < b → jetValue a b r f D → ∀ j, j < r →
      HasDerivWithinAt (D j) (D (j + 1) b) (Iic b) b

def jet_interior_deriv_type : Prop :=
  ∀ {a b t : ℝ} {r : ℕ} {f : ℝ → ℝ} {D : ℕ → ℝ → ℝ},
    jetValue a b r f D → t ∈ Ioo a b → ∀ j, j < r →
      HasDerivAt (D j) (D (j + 1) t) t

end NumAnalysis206.Approximation.IntervalCalculusSpec
