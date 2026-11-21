import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Oriented
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.OneSided
import Mathlib.Order.WithBot

/-! Independent specification of K03.10.one_endpoint (paper.tex:2906–2917).
A truncation index lies strictly between the regular and singular endpoints.
Its integral is the existing proper Darboux integral, with a proof of proper
integrability. Thus no value at a singular endpoint, no absolute integrability,
and no integral of nonintegrable data is used. WithTop ℝ and WithBot ℝ give
exactly the finite/infinite right and left endpoints of the source.
Finite values use cofinal ε limits. The bridge propositions below identify
these with the previously specified one-sided and infinite limits.
-/
namespace Specs.SingleVariableAnalysis.Ch10.OneEndpoint
open _root_.SingleVariableAnalysis
namespace I
export Specs.SingleVariableAnalysis.Ch08.Integral
  (scalarIntegrableValue scalarIntegralValue)
end I
namespace S
export Specs.SingleVariableAnalysis.Ch01.Scalar (scalarValue)
end S
namespace A
export Specs.SingleVariableAnalysis.Ch02.OneSided
  (leftRelativeLimitValue rightRelativeLimitValue
   limitAtPosInfinityValue limitAtNegInfinityValue)
end A

/-- Only the canonical metrics and additive groups on ℝ and ℂ. -/
noncomputable instance scalarNormedAddCommGroup (k : ScalarKind) : NormedAddCommGroup (S.scalarValue k) :=
  match k with
  | .real => inferInstanceAs (NormedAddCommGroup ℝ)
  | .complex => inferInstanceAs (NormedAddCommGroup ℂ)

/-- Real regular endpoints strictly below the singular right endpoint. -/
abbrev rightIndexType := ℝ → WithTop ℝ → Type
def rightIndexValue : rightIndexType := fun a b => {t : ℝ // a < t ∧ (t : WithTop ℝ) < b}
/-- Real regular endpoints strictly above the singular left endpoint. -/
abbrev leftIndexType := WithBot ℝ → ℝ → Type
def leftIndexValue : leftIndexType := fun a b => {t : ℝ // a < (t : WithBot ℝ) ∧ t < b}

abbrev rightRegularType := (k : ScalarKind) → (ℝ → S.scalarValue k) → ℝ → WithTop ℝ → Prop
noncomputable def rightRegularValue : rightRegularType := fun k f a b =>
  (a : WithTop ℝ) < b ∧ ∀ t : rightIndexValue a b,
    I.scalarIntegrableValue k f a t.val

abbrev leftRegularType := (k : ScalarKind) → (ℝ → S.scalarValue k) → WithBot ℝ → ℝ → Prop
noncomputable def leftRegularValue : leftRegularType := fun k f a b =>
  a < (b : WithBot ℝ) ∧ ∀ t : leftIndexValue a b,
    I.scalarIntegrableValue k f t.val b

abbrev rightTruncationType := (k : ScalarKind) → (f : ℝ → S.scalarValue k) → (a : ℝ) → (b : WithTop ℝ) → rightRegularValue k f a b → rightIndexValue a b → S.scalarValue k
noncomputable def rightTruncationValue : rightTruncationType := fun k f _ _ h t => I.scalarIntegralValue k f (h.2 t)

abbrev leftTruncationType := (k : ScalarKind) → (f : ℝ → S.scalarValue k) → (a : WithBot ℝ) → (b : ℝ) → leftRegularValue k f a b → leftIndexValue a b → S.scalarValue k
noncomputable def leftTruncationValue : leftTruncationType := fun k f _ _ h t => I.scalarIntegralValue k f (h.2 t)

abbrev rightHasIntegralType := (k : ScalarKind) → (ℝ → S.scalarValue k) → ℝ → WithTop ℝ → S.scalarValue k → Prop
noncomputable def rightHasIntegralValue : rightHasIntegralType := fun k f a b L => ∃ h : rightRegularValue k f a b,
  ∀ ε : ℝ, 0 < ε → ∃ r : rightIndexValue a b, ∀ t : rightIndexValue a b,
    r.val < t.val → dist (rightTruncationValue k f a b h t) L < ε

abbrev rightConvergesType := (k : ScalarKind) → (ℝ → S.scalarValue k) → ℝ → WithTop ℝ → Prop
noncomputable def rightConvergesValue : rightConvergesType := fun k f a b => ∃ L, rightHasIntegralValue k f a b L

abbrev rightIntegralType := (k : ScalarKind) → (f : ℝ → S.scalarValue k) → (a : ℝ) → (b : WithTop ℝ) → rightConvergesValue k f a b → S.scalarValue k
noncomputable def rightIntegralValue : rightIntegralType := fun _ _ _ _ h => Classical.choose h

abbrev rightReverseHasIntegralType := (k : ScalarKind) → (ℝ → S.scalarValue k) → ℝ → WithTop ℝ → S.scalarValue k → Prop
noncomputable def rightReverseHasIntegralValue : rightReverseHasIntegralType := fun k f a b L => rightHasIntegralValue k f a b (-L)

abbrev rightReverseIntegralType := (k : ScalarKind) → (f : ℝ → S.scalarValue k) → (a : ℝ) → (b : WithTop ℝ) → rightConvergesValue k f a b → S.scalarValue k
noncomputable def rightReverseIntegralValue : rightReverseIntegralType := fun k f a b h => -rightIntegralValue k f a b h

abbrev rightDivergesPosType := (ℝ → ℝ) → ℝ → WithTop ℝ → Prop
noncomputable def rightDivergesPosValue : rightDivergesPosType := fun f a b => ∃ h : rightRegularValue .real f a b,
  ∀ B : ℝ, ∃ r : rightIndexValue a b, ∀ t : rightIndexValue a b,
    r.val < t.val → B < (show ℝ from rightTruncationValue .real f a b h t)

abbrev rightDivergesNegType := (ℝ → ℝ) → ℝ → WithTop ℝ → Prop
noncomputable def rightDivergesNegValue : rightDivergesNegType := fun f a b => ∃ h : rightRegularValue .real f a b,
  ∀ B : ℝ, ∃ r : rightIndexValue a b, ∀ t : rightIndexValue a b,
    r.val < t.val → (show ℝ from rightTruncationValue .real f a b h t) < B

abbrev rightNormDivergesType := (k : ScalarKind) → (ℝ → S.scalarValue k) → ℝ → WithTop ℝ → Prop
noncomputable def rightNormDivergesValue : rightNormDivergesType := fun k f a b => ∃ h : rightRegularValue k f a b,
  ∀ B : ℝ, ∃ r : rightIndexValue a b, ∀ t : rightIndexValue a b,
    r.val < t.val → B < ‖rightTruncationValue k f a b h t‖

def rightUnique : Prop := ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k)
  (a : ℝ) (b : WithTop ℝ) (L M : S.scalarValue k),
  rightHasIntegralValue k f a b L → rightHasIntegralValue k f a b M → L = M

def rightIntegralHasValue : Prop := ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k)
  (a : ℝ) (b : WithTop ℝ) (h : rightConvergesValue k f a b),
  rightHasIntegralValue k f a b (rightIntegralValue k f a b h)

def rightIntegralEq : Prop := ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k)
  (a : ℝ) (b : WithTop ℝ) (h : rightConvergesValue k f a b) (L : S.scalarValue k),
  rightHasIntegralValue k f a b L → rightIntegralValue k f a b h = L

def rightReverseHasValue : Prop := ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k)
  (a : ℝ) (b : WithTop ℝ) (h : rightConvergesValue k f a b),
  rightReverseHasIntegralValue k f a b (rightReverseIntegralValue k f a b h)

def rightInfiniteNotConverges : Prop := ∀ (f : ℝ → ℝ) (a : ℝ) (b : WithTop ℝ),
  (rightDivergesPosValue f a b ∨ rightDivergesNegValue f a b) →
    ¬ rightConvergesValue .real f a b

def rightNormInfiniteNotConverges : Prop := ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k)
  (a : ℝ) (b : WithTop ℝ), rightNormDivergesValue k f a b →
    ¬ rightConvergesValue k f a b

abbrev leftHasIntegralType := (k : ScalarKind) → (ℝ → S.scalarValue k) → WithBot ℝ → ℝ → S.scalarValue k → Prop
noncomputable def leftHasIntegralValue : leftHasIntegralType := fun k f a b L => ∃ h : leftRegularValue k f a b,
  ∀ ε : ℝ, 0 < ε → ∃ r : leftIndexValue a b, ∀ t : leftIndexValue a b,
    t.val < r.val → dist (leftTruncationValue k f a b h t) L < ε

abbrev leftConvergesType := (k : ScalarKind) → (ℝ → S.scalarValue k) → WithBot ℝ → ℝ → Prop
noncomputable def leftConvergesValue : leftConvergesType := fun k f a b => ∃ L, leftHasIntegralValue k f a b L

abbrev leftIntegralType := (k : ScalarKind) → (f : ℝ → S.scalarValue k) → (a : WithBot ℝ) → (b : ℝ) → leftConvergesValue k f a b → S.scalarValue k
noncomputable def leftIntegralValue : leftIntegralType := fun _ _ _ _ h => Classical.choose h

abbrev leftReverseHasIntegralType := (k : ScalarKind) → (ℝ → S.scalarValue k) → WithBot ℝ → ℝ → S.scalarValue k → Prop
noncomputable def leftReverseHasIntegralValue : leftReverseHasIntegralType := fun k f a b L => leftHasIntegralValue k f a b (-L)

abbrev leftReverseIntegralType := (k : ScalarKind) → (f : ℝ → S.scalarValue k) → (a : WithBot ℝ) → (b : ℝ) → leftConvergesValue k f a b → S.scalarValue k
noncomputable def leftReverseIntegralValue : leftReverseIntegralType := fun k f a b h => -leftIntegralValue k f a b h

abbrev leftDivergesPosType := (ℝ → ℝ) → WithBot ℝ → ℝ → Prop
noncomputable def leftDivergesPosValue : leftDivergesPosType := fun f a b => ∃ h : leftRegularValue .real f a b,
  ∀ B : ℝ, ∃ r : leftIndexValue a b, ∀ t : leftIndexValue a b,
    t.val < r.val → B < (show ℝ from leftTruncationValue .real f a b h t)

abbrev leftDivergesNegType := (ℝ → ℝ) → WithBot ℝ → ℝ → Prop
noncomputable def leftDivergesNegValue : leftDivergesNegType := fun f a b => ∃ h : leftRegularValue .real f a b,
  ∀ B : ℝ, ∃ r : leftIndexValue a b, ∀ t : leftIndexValue a b,
    t.val < r.val → (show ℝ from leftTruncationValue .real f a b h t) < B

abbrev leftNormDivergesType := (k : ScalarKind) → (ℝ → S.scalarValue k) → WithBot ℝ → ℝ → Prop
noncomputable def leftNormDivergesValue : leftNormDivergesType := fun k f a b => ∃ h : leftRegularValue k f a b,
  ∀ B : ℝ, ∃ r : leftIndexValue a b, ∀ t : leftIndexValue a b,
    t.val < r.val → B < ‖leftTruncationValue k f a b h t‖

def leftUnique : Prop := ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k)
  (a : WithBot ℝ) (b : ℝ) (L M : S.scalarValue k),
  leftHasIntegralValue k f a b L → leftHasIntegralValue k f a b M → L = M

def leftIntegralHasValue : Prop := ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k)
  (a : WithBot ℝ) (b : ℝ) (h : leftConvergesValue k f a b),
  leftHasIntegralValue k f a b (leftIntegralValue k f a b h)

def leftIntegralEq : Prop := ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k)
  (a : WithBot ℝ) (b : ℝ) (h : leftConvergesValue k f a b) (L : S.scalarValue k),
  leftHasIntegralValue k f a b L → leftIntegralValue k f a b h = L

def leftReverseHasValue : Prop := ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k)
  (a : WithBot ℝ) (b : ℝ) (h : leftConvergesValue k f a b),
  leftReverseHasIntegralValue k f a b (leftReverseIntegralValue k f a b h)

def leftInfiniteNotConverges : Prop := ∀ (f : ℝ → ℝ) (a : WithBot ℝ) (b : ℝ),
  (leftDivergesPosValue f a b ∨ leftDivergesNegValue f a b) →
    ¬ leftConvergesValue .real f a b

def leftNormInfiniteNotConverges : Prop := ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k)
  (a : WithBot ℝ) (b : ℝ), leftNormDivergesValue k f a b →
    ¬ leftConvergesValue k f a b

def rightFiniteLimitIff : Prop := ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k)
  (a b : ℝ) (h : rightRegularValue k f a (b : WithTop ℝ))
  (H : ℝ → S.scalarValue k)
  (_extension : ∀ t : rightIndexValue a (b : WithTop ℝ), H t.val = rightTruncationValue k f a (b : WithTop ℝ) h t)
  (L : S.scalarValue k),
  rightHasIntegralValue k f a (b : WithTop ℝ) L ↔ A.leftRelativeLimitValue H (Set.Ioo a b) b L

def rightInfiniteLimitIff : Prop := ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k)
  (a : ℝ) (h : rightRegularValue k f a ⊤)
  (H : ℝ → S.scalarValue k)
  (_extension : ∀ t : rightIndexValue a ⊤, H t.val = rightTruncationValue k f a ⊤ h t)
  (L : S.scalarValue k),
  rightHasIntegralValue k f a ⊤ L ↔ A.limitAtPosInfinityValue H (Set.Ioi a) L

def leftFiniteLimitIff : Prop := ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k)
  (a b : ℝ) (h : leftRegularValue k f (a : WithBot ℝ) b)
  (H : ℝ → S.scalarValue k)
  (_extension : ∀ t : leftIndexValue (a : WithBot ℝ) b, H t.val = leftTruncationValue k f (a : WithBot ℝ) b h t)
  (L : S.scalarValue k),
  leftHasIntegralValue k f (a : WithBot ℝ) b L ↔ A.rightRelativeLimitValue H (Set.Ioo a b) a L

def leftInfiniteLimitIff : Prop := ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k)
  (b : ℝ) (h : leftRegularValue k f ⊥ b)
  (H : ℝ → S.scalarValue k)
  (_extension : ∀ t : leftIndexValue ⊥ b, H t.val = leftTruncationValue k f ⊥ b h t)
  (L : S.scalarValue k),
  leftHasIntegralValue k f ⊥ b L ↔ A.limitAtNegInfinityValue H (Set.Iio b) L


def rightRealOrientation : Prop := ∀ (f : ℝ → ℝ) (a : ℝ) (b : WithTop ℝ)
  (h : rightRegularValue .real f a b) (t : rightIndexValue a b),
  ∃ ho : Specs.SingleVariableAnalysis.Ch08.Oriented.realIntegrableValue f t.val a,
    Specs.SingleVariableAnalysis.Ch08.Oriented.realIntegralValue f ho =
      -rightTruncationValue .real f a b h t

def rightComplexOrientation : Prop := ∀ (f : ℝ → ℂ) (a : ℝ) (b : WithTop ℝ)
  (h : rightRegularValue .complex f a b) (t : rightIndexValue a b),
  ∃ ho : Specs.SingleVariableAnalysis.Ch08.Oriented.complexIntegrableValue f t.val a,
    Specs.SingleVariableAnalysis.Ch08.Oriented.complexIntegralValue f ho =
      -rightTruncationValue .complex f a b h t

def rightReverseConvergesIff : Prop := ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k)
  (a : ℝ) (b : WithTop ℝ),
  (∃ L, rightReverseHasIntegralValue k f a b L) ↔ rightConvergesValue k f a b

def leftRealOrientation : Prop := ∀ (f : ℝ → ℝ) (a : WithBot ℝ) (b : ℝ)
  (h : leftRegularValue .real f a b) (t : leftIndexValue a b),
  ∃ ho : Specs.SingleVariableAnalysis.Ch08.Oriented.realIntegrableValue f b t.val,
    Specs.SingleVariableAnalysis.Ch08.Oriented.realIntegralValue f ho =
      -leftTruncationValue .real f a b h t

def leftComplexOrientation : Prop := ∀ (f : ℝ → ℂ) (a : WithBot ℝ) (b : ℝ)
  (h : leftRegularValue .complex f a b) (t : leftIndexValue a b),
  ∃ ho : Specs.SingleVariableAnalysis.Ch08.Oriented.complexIntegrableValue f b t.val,
    Specs.SingleVariableAnalysis.Ch08.Oriented.complexIntegralValue f ho =
      -leftTruncationValue .complex f a b h t

def leftReverseConvergesIff : Prop := ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k)
  (a : WithBot ℝ) (b : ℝ),
  (∃ L, leftReverseHasIntegralValue k f a b L) ↔ leftConvergesValue k f a b

end Specs.SingleVariableAnalysis.Ch10.OneEndpoint
