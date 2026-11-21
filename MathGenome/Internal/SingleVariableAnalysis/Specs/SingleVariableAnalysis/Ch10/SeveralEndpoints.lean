import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.OneEndpoint
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! K03.10.several_endpoints, paper.tex:2918–2938.
All values below are sums of independently finite one-sided Darboux limits.
The endpoints have precisely the allowed finite/±infinite types. Local proper
integrability is on every closed regular subinterval, including singletons.
A finite list of singular nodes defines its adjacent open components. Splits
are chosen independently in those components; no linked truncation is used.
-/
namespace Specs.SingleVariableAnalysis.Ch10.SeveralEndpoints
open _root_.SingleVariableAnalysis
open scoped BigOperators
namespace E
export Specs.SingleVariableAnalysis.Ch10.OneEndpoint
  (leftHasIntegralValue rightHasIntegralValue leftConvergesValue rightConvergesValue
   leftIntegralValue rightIntegralValue scalarNormedAddCommGroup)
end E
namespace I
export Specs.SingleVariableAnalysis.Ch08.Integral (scalarIntegrableValue scalarIntegralValue)
end I
namespace S
export Specs.SingleVariableAnalysis.Ch01.Scalar (scalarValue)
end S

abbrev regularPointType := WithBot ℝ → WithTop ℝ → Type
def regularPointValue : regularPointType := fun a b =>
  {c : ℝ // a < (c : WithBot ℝ) ∧ (c : WithTop ℝ) < b}

abbrev locallyIntegrableType := (k : ScalarKind) → (ℝ → S.scalarValue k) →
  WithBot ℝ → WithTop ℝ → Prop
def locallyIntegrableValue : locallyIntegrableType := fun k f a b =>
  ∀ u v : ℝ, a < (u : WithBot ℝ) → u ≤ v → (v : WithTop ℝ) < b →
    I.scalarIntegrableValue k f u v

abbrev hasIntegralAtSplitType := (k : ScalarKind) → (ℝ → S.scalarValue k) →
  (a : WithBot ℝ) → (b : WithTop ℝ) → regularPointValue a b → S.scalarValue k → Prop
noncomputable def hasIntegralAtSplitValue : hasIntegralAtSplitType := fun k f a b c L =>
  ∃ l r : S.scalarValue k, E.leftHasIntegralValue k f a c.val l ∧
    E.rightHasIntegralValue k f c.val b r ∧ L = l + r

abbrev convergesAtSplitType := (k : ScalarKind) → (ℝ → S.scalarValue k) →
  (a : WithBot ℝ) → (b : WithTop ℝ) → regularPointValue a b → Prop
noncomputable def convergesAtSplitValue : convergesAtSplitType := fun k f a b c =>
  E.leftConvergesValue k f a c.val ∧ E.rightConvergesValue k f c.val b

abbrev integralAtSplitType := (k : ScalarKind) → (f : ℝ → S.scalarValue k) →
  (a : WithBot ℝ) → (b : WithTop ℝ) → (c : regularPointValue a b) →
  convergesAtSplitValue k f a b c → S.scalarValue k
noncomputable def integralAtSplitValue : integralAtSplitType := fun k f a b c h =>
  E.leftIntegralValue k f a c.val h.1 + E.rightIntegralValue k f c.val b h.2

abbrev hasIntegralType := (k : ScalarKind) → (ℝ → S.scalarValue k) →
  WithBot ℝ → WithTop ℝ → S.scalarValue k → Prop
noncomputable def hasIntegralValue : hasIntegralType := fun k f a b L =>
  locallyIntegrableValue k f a b ∧ ∃ c, hasIntegralAtSplitValue k f a b c L

abbrev convergesType := (k : ScalarKind) → (ℝ → S.scalarValue k) →
  WithBot ℝ → WithTop ℝ → Prop
noncomputable def convergesValue : convergesType := fun k f a b => ∃ L, hasIntegralValue k f a b L

abbrev integralType := (k : ScalarKind) → (f : ℝ → S.scalarValue k) →
  (a : WithBot ℝ) → (b : WithTop ℝ) → convergesValue k f a b → S.scalarValue k
noncomputable def integralValue : integralType := fun _ _ _ _ h => Classical.choose h

/-- There are n interior singularities and n+1 open regular components.
Strict ordering is forced whenever a regular split in every component exists.
For an already sorted singular list these are exactly its adjacent endpoints. -/
abbrev componentLeftType := (n : ℕ) → WithBot ℝ → (Fin n → ℝ) → Fin (n+1) → WithBot ℝ
def componentLeftValue : componentLeftType := fun _ a s i =>
  if h : i.val = 0 then a else (s ⟨i.val - 1, by omega⟩ : WithBot ℝ)

abbrev componentRightType := (n : ℕ) → WithTop ℝ → (Fin n → ℝ) → Fin (n+1) → WithTop ℝ
def componentRightValue : componentRightType := fun n b s i =>
  if h : i.val < n then (s ⟨i.val, h⟩ : WithTop ℝ) else b

abbrev splitFamilyType := (n : ℕ) → WithBot ℝ → WithTop ℝ → (Fin n → ℝ) → Type
def splitFamilyValue : splitFamilyType := fun n a b s =>
  (i : Fin (n+1)) → regularPointValue (componentLeftValue n a s i) (componentRightValue n b s i)

abbrev finiteHasIntegralType := (k : ScalarKind) → (ℝ → S.scalarValue k) →
  (n : ℕ) → (a : WithBot ℝ) → (b : WithTop ℝ) → (s : Fin n → ℝ) →
  splitFamilyValue n a b s → S.scalarValue k → Prop
noncomputable def finiteHasIntegralValue : finiteHasIntegralType := fun k f n a b s c L =>
  ∃ v : Fin (n+1) → S.scalarValue k,
    (∀ i, locallyIntegrableValue k f (componentLeftValue n a s i) (componentRightValue n b s i) ∧
      hasIntegralAtSplitValue k f _ _ (c i) (v i)) ∧ L = ∑ i, v i

abbrev finiteConvergesType := (k : ScalarKind) → (ℝ → S.scalarValue k) →
  (n : ℕ) → (a : WithBot ℝ) → (b : WithTop ℝ) → (s : Fin n → ℝ) →
  splitFamilyValue n a b s → Prop
noncomputable def finiteConvergesValue : finiteConvergesType := fun k f n a b s c =>
  ∃ L, finiteHasIntegralValue k f n a b s c L

abbrev finiteIntegralType := (k : ScalarKind) → (f : ℝ → S.scalarValue k) →
  (n : ℕ) → (a : WithBot ℝ) → (b : WithTop ℝ) → (s : Fin n → ℝ) →
  (c : splitFamilyValue n a b s) → finiteConvergesValue k f n a b s c → S.scalarValue k
noncomputable def finiteIntegralValue : finiteIntegralType := fun _ _ _ _ _ _ _ h => Classical.choose h

def splitExistence : Prop := ∀ k f a b (c : regularPointValue a b),
  convergesAtSplitValue k f a b c ↔ ∃ L, hasIntegralAtSplitValue k f a b c L

def splitUnique : Prop := ∀ k f a b (c : regularPointValue a b) L M,
  hasIntegralAtSplitValue k f a b c L → hasIntegralAtSplitValue k f a b c M → L = M

def splitIntegralHasValue : Prop := ∀ k f a b (c : regularPointValue a b)
  (h : convergesAtSplitValue k f a b c),
  hasIntegralAtSplitValue k f a b c (integralAtSplitValue k f a b c h)

def splitIndependent : Prop := ∀ k f a b, locallyIntegrableValue k f a b →
  ∀ (c d : regularPointValue a b) L,
    hasIntegralAtSplitValue k f a b c L ↔ hasIntegralAtSplitValue k f a b d L

def splitConvergenceIndependent : Prop := ∀ k f a b, locallyIntegrableValue k f a b →
  ∀ (c d : regularPointValue a b),
    convergesAtSplitValue k f a b c ↔ convergesAtSplitValue k f a b d

def splitValueIndependent : Prop := ∀ k f a b, locallyIntegrableValue k f a b →
  ∀ (c d : regularPointValue a b) (hc : convergesAtSplitValue k f a b c)
    (hd : convergesAtSplitValue k f a b d),
    integralAtSplitValue k f a b c hc = integralAtSplitValue k f a b d hd

def hasIntegralAtEverySplit : Prop := ∀ k f a b (c : regularPointValue a b) L,
  hasIntegralValue k f a b L ↔
    locallyIntegrableValue k f a b ∧ hasIntegralAtSplitValue k f a b c L

def integralHasValue : Prop := ∀ k f a b (h : convergesValue k f a b),
  hasIntegralValue k f a b (integralValue k f a b h)

def integralEq : Prop := ∀ k f a b (h : convergesValue k f a b) L,
  hasIntegralValue k f a b L → integralValue k f a b h = L

/-- Failure of either independent endpoint condition rules out convergence. -/
def noCancellation : Prop := ∀ k f a b (c : regularPointValue a b),
  (¬ E.leftConvergesValue k f a c.val ∨ ¬ E.rightConvergesValue k f c.val b) →
    ¬ convergesValue k f a b

def finiteIndependent : Prop := ∀ k f n a b s (c d : splitFamilyValue n a b s) L,
  finiteHasIntegralValue k f n a b s c L ↔ finiteHasIntegralValue k f n a b s d L

def finiteConvergenceIndependent : Prop := ∀ k f n a b s (c d : splitFamilyValue n a b s),
  finiteConvergesValue k f n a b s c ↔ finiteConvergesValue k f n a b s d

def finiteUnique : Prop := ∀ k f n a b s (c : splitFamilyValue n a b s) L M,
  finiteHasIntegralValue k f n a b s c L → finiteHasIntegralValue k f n a b s c M → L = M

def finiteIntegralHasValue : Prop := ∀ k f n a b s (c : splitFamilyValue n a b s)
  (h : finiteConvergesValue k f n a b s c),
  finiteHasIntegralValue k f n a b s c (finiteIntegralValue k f n a b s c h)

def finiteValueIndependent : Prop := ∀ k f n a b s (c d : splitFamilyValue n a b s)
  (hc : finiteConvergesValue k f n a b s c) (hd : finiteConvergesValue k f n a b s d),
  finiteIntegralValue k f n a b s c hc = finiteIntegralValue k f n a b s d hd

def finiteExistence : Prop := ∀ k f n a b s (c : splitFamilyValue n a b s),
  finiteConvergesValue k f n a b s c ↔
    ∀ i, locallyIntegrableValue k f (componentLeftValue n a s i) (componentRightValue n b s i) ∧
      E.leftConvergesValue k f (componentLeftValue n a s i) (c i).val ∧
      E.rightConvergesValue k f (c i).val (componentRightValue n b s i)

/-- Every strictly ordered finite set of interior singularities admits regular
splits in all its components, with no extra spacing or analytic assumptions. -/
def splitFamilyExists : Prop := ∀ n a b (s : Fin n → ℝ),
  Nonempty (regularPointValue a b) → StrictMono s →
  (∀ i, a < (s i : WithBot ℝ) ∧ (s i : WithTop ℝ) < b) →
  Nonempty (splitFamilyValue n a b s)

/-- With no interior singularities the finite construction is the original one. -/
def finiteZero : Prop := ∀ k f a b (s : Fin 0 → ℝ)
  (c : splitFamilyValue 0 a b s) L,
  finiteHasIntegralValue k f 0 a b s c L ↔
    locallyIntegrableValue k f a b ∧ hasIntegralAtSplitValue k f a b (c 0) L

/-- Either adjacent one-sided failure at any component prevents a finite total. -/
def finiteNoCancellation : Prop := ∀ k f n a b s (c : splitFamilyValue n a b s)
  (i : Fin (n+1)),
  (¬ E.leftConvergesValue k f (componentLeftValue n a s i) (c i).val ∨
   ¬ E.rightConvergesValue k f (c i).val (componentRightValue n b s i)) →
  ¬ finiteConvergesValue k f n a b s c

end Specs.SingleVariableAnalysis.Ch10.SeveralEndpoints
