import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.SeveralEndpoints

/-! K03.10.absolute, paper.tex:2989–3007.
All integrals are independent one-sided limits of proper Darboux integrals.
Local proper integrability of f remains an explicit hypothesis: integrability
of its norm alone does not imply even proper Riemann integrability of f.
The finite construction checks both sides of every singularity separately.
No total measure integral is used, including in conditional convergence. -/
namespace Specs.SingleVariableAnalysis.Ch10.Absolute
open _root_.SingleVariableAnalysis
open OneEndpoint
namespace J
export Specs.SingleVariableAnalysis.Ch10.SeveralEndpoints
  (regularPointValue locallyIntegrableValue hasIntegralAtSplitValue
   convergesAtSplitValue hasIntegralValue convergesValue integralValue
   componentLeftValue componentRightValue splitFamilyValue finiteHasIntegralValue
   finiteConvergesValue finiteIntegralValue)
end J
open scoped BigOperators

abbrev rightAbsoluteType := (k : ScalarKind) → (ℝ → S.scalarValue k) → ℝ → WithTop ℝ → Prop
noncomputable def rightAbsoluteValue : rightAbsoluteType := fun _ f a b =>
  rightConvergesValue .real (fun x => ‖f x‖) a b
abbrev rightConditionalType := rightAbsoluteType
noncomputable def rightConditionalValue : rightConditionalType := fun k f a b =>
  rightConvergesValue k f a b ∧ ¬ rightAbsoluteValue k f a b

abbrev leftAbsoluteType := (k : ScalarKind) → (ℝ → S.scalarValue k) → WithBot ℝ → ℝ → Prop
noncomputable def leftAbsoluteValue : leftAbsoluteType := fun _ f a b =>
  leftConvergesValue .real (fun x => ‖f x‖) a b
abbrev leftConditionalType := leftAbsoluteType
noncomputable def leftConditionalValue : leftConditionalType := fun k f a b =>
  leftConvergesValue k f a b ∧ ¬ leftAbsoluteValue k f a b

abbrev absoluteType := (k : ScalarKind) → (ℝ → S.scalarValue k) → WithBot ℝ → WithTop ℝ → Prop
noncomputable def absoluteValue : absoluteType := fun _ f a b =>
  J.convergesValue .real (fun x => ‖f x‖) a b
abbrev conditionalType := absoluteType
noncomputable def conditionalValue : conditionalType := fun k f a b =>
  J.convergesValue k f a b ∧ ¬ absoluteValue k f a b

abbrev finiteAbsoluteType := (k : ScalarKind) → (ℝ → S.scalarValue k) →
  (n : ℕ) → (a : WithBot ℝ) → (b : WithTop ℝ) → (s : Fin n → ℝ) →
  J.splitFamilyValue n a b s → Prop
noncomputable def finiteAbsoluteValue : finiteAbsoluteType := fun _ f n a b s c =>
  J.finiteConvergesValue .real (fun x => ‖f x‖) n a b s c
abbrev finiteConditionalType := finiteAbsoluteType
noncomputable def finiteConditionalValue : finiteConditionalType := fun k f n a b s c =>
  J.finiteConvergesValue k f n a b s c ∧ ¬ finiteAbsoluteValue k f n a b s c

def rightAbsoluteConverges : Prop := ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k)
  (a : ℝ) (b : WithTop ℝ), rightRegularValue k f a b →
    rightAbsoluteValue k f a b → rightConvergesValue k f a b

def rightNormBound : Prop := ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k)
  (a : ℝ) (b : WithTop ℝ) (L : S.scalarValue k) (A : ℝ),
  rightHasIntegralValue k f a b L →
    rightHasIntegralValue .real (fun x => ‖f x‖) a b A → ‖L‖ ≤ A

def leftAbsoluteConverges : Prop := ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k)
  (a : WithBot ℝ) (b : ℝ), leftRegularValue k f a b →
    leftAbsoluteValue k f a b → leftConvergesValue k f a b

def leftNormBound : Prop := ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k)
  (a : WithBot ℝ) (b : ℝ) (L : S.scalarValue k) (A : ℝ),
  leftHasIntegralValue k f a b L →
    leftHasIntegralValue .real (fun x => ‖f x‖) a b A → ‖L‖ ≤ A

def absoluteConverges : Prop := ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k)
  (a : WithBot ℝ) (b : WithTop ℝ), J.locallyIntegrableValue k f a b →
    absoluteValue k f a b → J.convergesValue k f a b

def normBound : Prop := ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k)
  (a : WithBot ℝ) (b : WithTop ℝ) (L : S.scalarValue k) (A : ℝ),
  J.hasIntegralValue k f a b L →
    J.hasIntegralValue .real (fun x => ‖f x‖) a b A → ‖L‖ ≤ A

def absoluteAtEverySplit : Prop := ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k)
  (a : WithBot ℝ) (b : WithTop ℝ) (c : J.regularPointValue a b),
  absoluteValue k f a b ↔
    J.locallyIntegrableValue .real (fun x => ‖f x‖) a b ∧
      leftAbsoluteValue k f a c.val ∧ rightAbsoluteValue k f c.val b

def finiteAbsoluteConverges : Prop := ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k)
  (n : ℕ) (a : WithBot ℝ) (b : WithTop ℝ) (s : Fin n → ℝ)
  (c : J.splitFamilyValue n a b s),
  (∀ i, J.locallyIntegrableValue k f (J.componentLeftValue n a s i)
    (J.componentRightValue n b s i)) →
  finiteAbsoluteValue k f n a b s c → J.finiteConvergesValue k f n a b s c

def finiteNormBound : Prop := ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k)
  (n : ℕ) (a : WithBot ℝ) (b : WithTop ℝ) (s : Fin n → ℝ)
  (c : J.splitFamilyValue n a b s) (L : S.scalarValue k) (A : ℝ),
  J.finiteHasIntegralValue k f n a b s c L →
    J.finiteHasIntegralValue .real (fun x => ‖f x‖) n a b s c A → ‖L‖ ≤ A

def finiteAbsoluteEndpoints : Prop := ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k)
  (n : ℕ) (a : WithBot ℝ) (b : WithTop ℝ) (s : Fin n → ℝ)
  (c : J.splitFamilyValue n a b s),
  finiteAbsoluteValue k f n a b s c ↔
    ∀ i, J.locallyIntegrableValue .real (fun x => ‖f x‖)
      (J.componentLeftValue n a s i) (J.componentRightValue n b s i) ∧
      leftAbsoluteValue k f (J.componentLeftValue n a s i) (c i).val ∧
      rightAbsoluteValue k f (c i).val (J.componentRightValue n b s i)

end Specs.SingleVariableAnalysis.Ch10.Absolute
