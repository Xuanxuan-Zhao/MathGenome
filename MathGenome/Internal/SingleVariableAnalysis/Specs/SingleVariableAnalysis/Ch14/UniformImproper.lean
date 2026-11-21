import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.Cauchy

/-! K03.14.uniform_improper, paper.tex:3360–3387.
These are limits of the existing proper Darboux integrals, for exactly ℝ or ℂ.
A parameter set is represented by a type (use a subtype for a subset T).
No nonemptiness, boundedness, absolute convergence or regularity in the parameter
is required. WithTop/WithBot endpoints include finite singular endpoints and
±∞. Thresholds are independent of the parameter. At finite right endpoints
r < u < v < b; at left endpoints a < u < v < r. A finite collection of
endpoints converges only if each endpoint family converges independently.
-/
namespace Specs.SingleVariableAnalysis.Ch14.UniformImproper
open _root_.SingleVariableAnalysis
open Ch10.OneEndpoint
open scoped ENNReal
universe u

abbrev rightFamilyRegularType := (k : ScalarKind) → (T : Type u) →
  (ℝ → T → S.scalarValue k) → ℝ → WithTop ℝ → Prop
noncomputable def rightFamilyRegularValue : rightFamilyRegularType := fun k T f a b =>
  (a : WithTop ℝ) < b ∧ ∀ t : T, rightRegularValue k (fun x => f x t) a b

abbrev leftFamilyRegularType := (k : ScalarKind) → (T : Type u) →
  (ℝ → T → S.scalarValue k) → WithBot ℝ → ℝ → Prop
noncomputable def leftFamilyRegularValue : leftFamilyRegularType := fun k T f a b =>
  a < (b : WithBot ℝ) ∧ ∀ t : T, leftRegularValue k (fun x => f x t) a b

abbrev rightUniformHasIntegralType := (k : ScalarKind) → (T : Type u) →
  (ℝ → T → S.scalarValue k) → ℝ → WithTop ℝ → (T → S.scalarValue k) → Prop
noncomputable def rightUniformHasIntegralValue : rightUniformHasIntegralType :=
  fun k T f a b F => ∃ h : rightFamilyRegularValue k T f a b,
    ∀ ε : ℝ, 0 < ε → ∃ r : rightIndexValue a b,
      ∀ R : rightIndexValue a b, r.val < R.val → ∀ t : T,
        dist (rightTruncationValue k (fun x => f x t) a b (h.2 t) R) (F t) < ε

abbrev leftUniformHasIntegralType := (k : ScalarKind) → (T : Type u) →
  (ℝ → T → S.scalarValue k) → WithBot ℝ → ℝ → (T → S.scalarValue k) → Prop
noncomputable def leftUniformHasIntegralValue : leftUniformHasIntegralType :=
  fun k T f a b F => ∃ h : leftFamilyRegularValue k T f a b,
    ∀ ε : ℝ, 0 < ε → ∃ r : leftIndexValue a b,
      ∀ R : leftIndexValue a b, R.val < r.val → ∀ t : T,
        dist (leftTruncationValue k (fun x => f x t) a b (h.2 t) R) (F t) < ε

abbrev rightUniformConvergesType := (k : ScalarKind) → (T : Type u) →
  (ℝ → T → S.scalarValue k) → ℝ → WithTop ℝ → Prop
noncomputable def rightUniformConvergesValue : rightUniformConvergesType :=
  fun k T f a b => ∃ F : T → S.scalarValue k, rightUniformHasIntegralValue k T f a b F

abbrev leftUniformConvergesType := (k : ScalarKind) → (T : Type u) →
  (ℝ → T → S.scalarValue k) → WithBot ℝ → ℝ → Prop
noncomputable def leftUniformConvergesValue : leftUniformConvergesType :=
  fun k T f a b => ∃ F : T → S.scalarValue k, leftUniformHasIntegralValue k T f a b F

/-- Proper tail integrals, with their actual integrability proofs. -/
abbrev rightUniformCauchyType := rightUniformConvergesType.{u}
noncomputable def rightUniformCauchyValue : rightUniformCauchyType := fun k T f a b =>
  ∀ ε : ℝ, 0 < ε → ∃ r : rightIndexValue a b,
    ∀ t : T, ∀ R S : rightIndexValue a b, r.val < R.val → R.val < S.val →
      ∃ hRS : I.scalarIntegrableValue k (fun x => f x t) R.val S.val,
        ‖I.scalarIntegralValue k (fun x => f x t) hRS‖ < ε

abbrev leftUniformCauchyType := leftUniformConvergesType.{u}
noncomputable def leftUniformCauchyValue : leftUniformCauchyType := fun k T f a b =>
  ∀ ε : ℝ, 0 < ε → ∃ r : leftIndexValue a b,
    ∀ t : T, ∀ R S : leftIndexValue a b, R.val < S.val → S.val < r.val →
      ∃ hRS : I.scalarIntegrableValue k (fun x => f x t) R.val S.val,
        ‖I.scalarIntegralValue k (fun x => f x t) hRS‖ < ε

def rightUniformCauchyCriterion : Prop := ∀ (k : ScalarKind) (T : Type u)
  (f : ℝ → T → S.scalarValue k) (a : ℝ) (b : WithTop ℝ),
  rightFamilyRegularValue k T f a b →
    (rightUniformConvergesValue k T f a b ↔ rightUniformCauchyValue k T f a b)

def leftUniformCauchyCriterion : Prop := ∀ (k : ScalarKind) (T : Type u)
  (f : ℝ → T → S.scalarValue k) (a : WithBot ℝ) (b : ℝ),
  leftFamilyRegularValue k T f a b →
    (leftUniformConvergesValue k T f a b ↔ leftUniformCauchyValue k T f a b)

/-- The displayed S ≥ R ≥ R₀ convention at +∞, including zero-length tails. -/
def rightInfiniteCauchyCriterion : Prop := ∀ (k : ScalarKind) (T : Type u)
  (f : ℝ → T → S.scalarValue k) (a : ℝ),
  rightFamilyRegularValue k T f a ⊤ →
    (rightUniformConvergesValue k T f a ⊤ ↔
      ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, a < R₀ ∧
        ∀ t : T, ∀ R S : ℝ, R₀ ≤ R → R ≤ S →
          ∃ hRS : I.scalarIntegrableValue k (fun x => f x t) R S,
            ‖I.scalarIntegralValue k (fun x => f x t) hRS‖ < ε)

def rightUniformPointwise : Prop := ∀ (k : ScalarKind) (T : Type u)
  (f : ℝ → T → S.scalarValue k) (a : ℝ) (b : WithTop ℝ) (F : T → S.scalarValue k),
  rightUniformHasIntegralValue k T f a b F →
    ∀ t : T, rightHasIntegralValue k (fun x => f x t) a b (F t)

def leftUniformPointwise : Prop := ∀ (k : ScalarKind) (T : Type u)
  (f : ℝ → T → S.scalarValue k) (a : WithBot ℝ) (b : ℝ) (F : T → S.scalarValue k),
  leftUniformHasIntegralValue k T f a b F →
    ∀ t : T, leftHasIntegralValue k (fun x => f x t) a b (F t)

def rightUniformEmpty : Prop := ∀ (k : ScalarKind) (T : Type u) [IsEmpty T]
  (f : ℝ → T → S.scalarValue k) (a : ℝ) (b : WithTop ℝ) (F : T → S.scalarValue k),
  (a : WithTop ℝ) < b → rightUniformHasIntegralValue k T f a b F

def leftUniformEmpty : Prop := ∀ (k : ScalarKind) (T : Type u) [IsEmpty T]
  (f : ℝ → T → S.scalarValue k) (a : WithBot ℝ) (b : ℝ) (F : T → S.scalarValue k),
  a < (b : WithBot ℝ) → leftUniformHasIntegralValue k T f a b F

/-- Extended supremum errors allow unbounded errors at early truncations.
The supremum of an empty family is zero. Their epsilon limits below are
precisely the supremum-error formulation in the source. -/
abbrev rightUniformErrorType := (k : ScalarKind) → (T : Type u) →
  (f : ℝ → T → S.scalarValue k) → (a : ℝ) → (b : WithTop ℝ) →
  rightFamilyRegularValue k T f a b → (T → S.scalarValue k) → rightIndexValue a b → ℝ≥0∞
noncomputable def rightUniformErrorValue : rightUniformErrorType := fun k T f a b h F R =>
  ⨆ t : T, ENNReal.ofReal (dist (rightTruncationValue k (fun x => f x t) a b (h.2 t) R) (F t))

abbrev leftUniformErrorType := (k : ScalarKind) → (T : Type u) →
  (f : ℝ → T → S.scalarValue k) → (a : WithBot ℝ) → (b : ℝ) →
  leftFamilyRegularValue k T f a b → (T → S.scalarValue k) → leftIndexValue a b → ℝ≥0∞
noncomputable def leftUniformErrorValue : leftUniformErrorType := fun k T f a b h F R =>
  ⨆ t : T, ENNReal.ofReal (dist (leftTruncationValue k (fun x => f x t) a b (h.2 t) R) (F t))

def rightUniformSupCriterion : Prop := ∀ (k : ScalarKind) (T : Type u)
  (f : ℝ → T → S.scalarValue k) (a : ℝ) (b : WithTop ℝ)
  (h : rightFamilyRegularValue k T f a b) (F : T → S.scalarValue k),
  rightUniformHasIntegralValue k T f a b F ↔
    ∀ ε : ℝ, 0 < ε → ∃ r : rightIndexValue a b, ∀ R : rightIndexValue a b,
      r.val < R.val → rightUniformErrorValue k T f a b h F R < ENNReal.ofReal ε

def leftUniformSupCriterion : Prop := ∀ (k : ScalarKind) (T : Type u)
  (f : ℝ → T → S.scalarValue k) (a : WithBot ℝ) (b : ℝ)
  (h : leftFamilyRegularValue k T f a b) (F : T → S.scalarValue k),
  leftUniformHasIntegralValue k T f a b F ↔
    ∀ ε : ℝ, 0 < ε → ∃ r : leftIndexValue a b, ∀ R : leftIndexValue a b,
      R.val < r.val → leftUniformErrorValue k T f a b h F R < ENNReal.ofReal ε

def rightUniformErrorEmpty : Prop := ∀ (k : ScalarKind) (T : Type u) [IsEmpty T]
  (f : ℝ → T → S.scalarValue k) (a : ℝ) (b : WithTop ℝ)
  (h : rightFamilyRegularValue k T f a b) (F : T → S.scalarValue k) (R : rightIndexValue a b),
  rightUniformErrorValue k T f a b h F R = 0

def leftUniformErrorEmpty : Prop := ∀ (k : ScalarKind) (T : Type u) [IsEmpty T]
  (f : ℝ → T → S.scalarValue k) (a : WithBot ℝ) (b : ℝ)
  (h : leftFamilyRegularValue k T f a b) (F : T → S.scalarValue k) (R : leftIndexValue a b),
  leftUniformErrorValue k T f a b h F R = 0

/-- Each constructor describes one side of one singularity. Include both sides
of an interior singularity as separate entries. Every section is the original
integrand restricted to that regular component. -/
inductive EndpointFamily (k : ScalarKind) (T : Type u) where
  | right (f : ℝ → T → S.scalarValue k) (a : ℝ) (b : WithTop ℝ)
  | left (f : ℝ → T → S.scalarValue k) (a : WithBot ℝ) (b : ℝ)

abbrev independentUniformConvergesType := (k : ScalarKind) → (T : Type u) →
  (n : ℕ) → (Fin n → EndpointFamily k T) → Prop
noncomputable def independentUniformConvergesValue : independentUniformConvergesType :=
  fun k T _ E => ∀ j, match E j with
    | .right f a b => rightUniformConvergesValue k T f a b
    | .left f a b => leftUniformConvergesValue k T f a b

/-- No shared cutoff or cancellation between divergent endpoints occurs. -/
def independentUniformCauchyCriterion : Prop := ∀ (k : ScalarKind) (T : Type u)
  (n : ℕ) (E : Fin n → EndpointFamily k T),
  (∀ j, match E j with
    | .right f a b => rightFamilyRegularValue k T f a b
    | .left f a b => leftFamilyRegularValue k T f a b) →
  (independentUniformConvergesValue k T n E ↔
    ∀ j, match E j with
      | .right f a b => rightUniformCauchyValue k T f a b
      | .left f a b => leftUniformCauchyValue k T f a b)

end Specs.SingleVariableAnalysis.Ch14.UniformImproper
