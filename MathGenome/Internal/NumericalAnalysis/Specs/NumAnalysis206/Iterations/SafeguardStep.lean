import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Iterations.BracketExistence

/-! Independent one-step interface for paper.tex, p206:W65 (2557–2583).
The convergence assertion is allocated to SafeguardConvergence. All arithmetic
here is exact. `none` as a proposal includes an undefined Newton/secant step;
`none` as a selected point denotes failure to certify an available central point.
No assertion of availability in a finite number format is made. -/
namespace Specs.NumAnalysis206.Iterations.SafeguardStep

/-- Membership in the permitted central interval, including its boundaries. -/
def Central (α a b x : ℝ) : Prop :=
  a + α * (b - a) ≤ x ∧ x ≤ b - α * (b - a)

/-- An unavailable or rejected proposal falls back to the exact midpoint. -/
noncomputable def choose (α a b : ℝ) (proposal : Option ℝ) : ℝ := by
  classical
  exact match proposal with
    | none => (a + b) / 2
    | some x => if Central α a b x then x else (a + b) / 2

inductive Sign where
  | negative | zero | positive | unknown
  deriving DecidableEq

/-- A sign certificate is an assertion about the true function value.
`unknown` makes no assertion and never authorizes an update. -/
def Sound (f : ℝ → ℝ) (point : Option ℝ) (sign : Sign) : Prop :=
  match point with
  | none => True
  | some x => match sign with
    | .negative => f x < 0
    | .zero => f x = 0
    | .positive => 0 < f x
    | .unknown => True

inductive Result where
  | retained
  | root (x : ℝ)
  | updated (left right : ℝ)

/-- An attempt can use any certified central point, including `choose`.
Only a certified nonzero value authorizes endpoint replacement. -/
noncomputable def attempt (f : ℝ → ℝ) (α a b : ℝ)
    (point : Option ℝ) (sign : Sign) : Result := by
  classical
  exact match point with
  | none => .retained
  | some x => if Central α a b x then
      match sign with
      | .unknown => .retained
      | .zero => .root x
      | .negative | .positive =>
          if f a * f x < 0 then .updated a x else .updated x b
    else .retained

/-- Counts completed nonzero-sign updates, not attempts or root returns. -/
def advance (n : ℕ) (result : Result) : ℕ :=
  match result with
  | .updated _ _ => n + 1
  | _ => n

/-- Full geometric and sign conclusions for one attempt. -/
def Safe (f : ℝ → ℝ) (α a b : ℝ) (result : Result) : Prop :=
  match result with
  | .retained => True
  | .root x => x ∈ Set.Ioo a b ∧ f x = 0
  | .updated c d =>
      a ≤ c ∧ c < d ∧ d ≤ b ∧
      Set.Icc c d ⊆ Set.Icc a b ∧ f c * f d < 0 ∧
      d - c ≤ (1 - α) * (b - a) ∧
      ((c = a ∧ f d * f b > 0) ∨ (d = b ∧ f a * f c > 0))

def selection : Prop :=
  ∀ (α a b : ℝ), 0 < α → α ≤ 1 / 2 → a < b →
    (∀ proposal, Central α a b (choose α a b proposal)) ∧
    choose α a b none = (a + b) / 2 ∧
    (∀ x, Central α a b x → choose α a b (some x) = x) ∧
    (∀ x, ¬ Central α a b x → choose α a b (some x) = (a + b) / 2)

def stepSafety : Prop :=
  ∀ (f : ℝ → ℝ) (α a b : ℝ), 0 < α → α ≤ 1 / 2 → a < b →
    f a * f b < 0 → ∀ point sign, Sound f point sign →
    Safe f α a b (attempt f α a b point sign)

/-- All failure modes retain exactly the old bracket. -/
def failurePolicy : Prop :=
  ∀ (f : ℝ → ℝ) (α a b : ℝ),
    (∀ sign, attempt f α a b none sign = .retained) ∧
    (∀ point, attempt f α a b point .unknown = .retained) ∧
    (∀ x sign, ¬ Central α a b x → attempt f α a b (some x) sign = .retained)

def countPolicy : Prop :=
  ∀ n result,
    (advance n result = n + 1 ↔ ∃ c d, result = .updated c d) ∧
    (advance n result = n ↔ result = .retained ∨ ∃ x, result = .root x)

/-- Each result retains a root certificate under the original continuity
hypothesis, restricted to any current strict-sign subbracket. -/
def rootCertificate : Prop :=
  ∀ (f : ℝ → ℝ) (α A B a b : ℝ),
    0 < α → α ≤ 1 / 2 → A < B →
    ContinuousOn f (Set.Icc A B) → f A * f B < 0 →
    A ≤ a → a < b → b ≤ B → f a * f b < 0 →
    ∀ point sign, Sound f point sign →
      match attempt f α a b point sign with
      | .retained => ∃ p ∈ Set.Icc a b, f p = 0
      | .root x => x ∈ Set.Icc a b ∧ f x = 0
      | .updated c d => ∃ p ∈ Set.Icc c d, f p = 0

end Specs.NumAnalysis206.Iterations.SafeguardStep
