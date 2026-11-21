import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.SeveralEndpoints

/-! K03.10.principal_value, paper.tex:3157–3172.
All integrals are the upstream proper Darboux integrals, or independently
convergent improper integrals of those proper integrals. The center and the
linked rule (c-ε,c+ε), respectively (center-R,center+R), are explicit parameters.
The finite value is defined only with a convergence proof. No absolute
integrability or value of f at an interior singularity is imposed.
-/
namespace Specs.SingleVariableAnalysis.Ch10.PrincipalValue
open _root_.SingleVariableAnalysis
namespace E
export Specs.SingleVariableAnalysis.Ch10.OneEndpoint
  (rightIndexValue leftIndexValue rightRegularValue leftRegularValue
   rightTruncationValue leftTruncationValue rightHasIntegralValue leftHasIntegralValue
   scalarNormedAddCommGroup)
end E
namespace I
export Specs.SingleVariableAnalysis.Ch08.Integral (scalarIntegrableValue scalarIntegralValue)
end I
namespace S
export Specs.SingleVariableAnalysis.Ch01.Scalar (scalarValue)
end S
namespace V
export Specs.SingleVariableAnalysis.Ch10.SeveralEndpoints
  (regularPointValue locallyIntegrableValue hasIntegralValue hasIntegralAtSplitValue
   splitFamilyValue finiteHasIntegralValue)
end V

abbrev interiorIndexType := ℝ → ℝ → ℝ → Type
def interiorIndexValue : interiorIndexType := fun a b c =>
  {ε : ℝ // 0 < ε ∧ a < c - ε ∧ c + ε < b}

abbrev interiorRegularType := (k : ScalarKind) → (ℝ → S.scalarValue k) → ℝ → ℝ → ℝ → Prop
def interiorRegularValue : interiorRegularType := fun k f a b c =>
  E.rightRegularValue k f a (c : WithTop ℝ) ∧ E.leftRegularValue k f (c : WithBot ℝ) b

abbrev interiorTruncationType := (k : ScalarKind) → (f : ℝ → S.scalarValue k) →
  (a b c : ℝ) → interiorRegularValue k f a b c → interiorIndexValue a b c → S.scalarValue k
noncomputable def interiorTruncationValue : interiorTruncationType := fun k f a b c h t =>
  E.rightTruncationValue k f a (c : WithTop ℝ) h.1
    ⟨c-t.val, t.property.2.1, WithTop.coe_lt_coe.mpr (by linarith [t.property.1])⟩ +
  E.leftTruncationValue k f (c : WithBot ℝ) b h.2
    ⟨c+t.val, WithBot.coe_lt_coe.mpr (by linarith [t.property.1]), t.property.2.2⟩

abbrev interiorHasIntegralType := (k : ScalarKind) → (ℝ → S.scalarValue k) →
  ℝ → ℝ → ℝ → S.scalarValue k → Prop
noncomputable def interiorHasIntegralValue : interiorHasIntegralType := fun k f a b c L =>
  ∃ h : interiorRegularValue k f a b c, ∀ η : ℝ, 0 < η →
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : interiorIndexValue a b c,
      t.val < δ → dist (interiorTruncationValue k f a b c h t) L < η

abbrev interiorConvergesType := (k : ScalarKind) → (ℝ → S.scalarValue k) → ℝ → ℝ → ℝ → Prop
noncomputable def interiorConvergesValue : interiorConvergesType := fun k f a b c =>
  ∃ L, interiorHasIntegralValue k f a b c L

abbrev interiorIntegralType := (k : ScalarKind) → (f : ℝ → S.scalarValue k) →
  (a b c : ℝ) → interiorConvergesValue k f a b c → S.scalarValue k
noncomputable def interiorIntegralValue : interiorIntegralType := fun _ _ _ _ _ h => Classical.choose h

/-- Fixed regular anchors u<c<v separate the outer endpoint limits from the
single symmetric limit at c. Outer endpoints may be finite or infinite.
By improper interval additivity this is ∫a^(c-ε) + ∫(c+ε)^b, with the
outer endpoint limits taken independently first. -/
abbrev controlledInteriorHasIntegralType := (k : ScalarKind) → (ℝ → S.scalarValue k) →
  WithBot ℝ → WithTop ℝ → ℝ → ℝ → ℝ → S.scalarValue k → Prop
noncomputable def controlledInteriorHasIntegralValue : controlledInteriorHasIntegralType :=
  fun k f a b u v c L => ∃ l m r : S.scalarValue k,
    E.leftHasIntegralValue k f a u l ∧ interiorHasIntegralValue k f u v c m ∧
    E.rightHasIntegralValue k f v b r ∧ L = l + m + r

abbrev controlledInteriorConvergesType := (k : ScalarKind) → (ℝ → S.scalarValue k) →
  WithBot ℝ → WithTop ℝ → ℝ → ℝ → ℝ → Prop
noncomputable def controlledInteriorConvergesValue : controlledInteriorConvergesType :=
  fun k f a b u v c => ∃ L, controlledInteriorHasIntegralValue k f a b u v c L

abbrev controlledInteriorIntegralType := (k : ScalarKind) → (f : ℝ → S.scalarValue k) →
  (a : WithBot ℝ) → (b : WithTop ℝ) → (u v c : ℝ) →
  controlledInteriorConvergesValue k f a b u v c → S.scalarValue k
noncomputable def controlledInteriorIntegralValue : controlledInteriorIntegralType :=
  fun _ _ _ _ _ _ _ h => Classical.choose h

/-- A fixed whole-line core is either proper, or has an explicitly witnessed
finite singular list with both adjacent limits at every singularity. This
choice does not assign a principal value to any hidden interior singularity. -/
abbrev coreHasIntegralType := (k : ScalarKind) → (ℝ → S.scalarValue k) →
  ℝ → ℝ → S.scalarValue k → Prop
noncomputable def coreHasIntegralValue : coreHasIntegralType := fun k f u v J =>
  (∃ h : I.scalarIntegrableValue k f u v, I.scalarIntegralValue k f h = J) ∨
  ∃ (n : ℕ) (s : Fin n → ℝ) (d : V.splitFamilyValue n (u : WithBot ℝ) (v : WithTop ℝ) s),
    V.finiteHasIntegralValue k f n (u : WithBot ℝ) (v : WithTop ℝ) s d J

abbrev wholeLineIndexType := ℝ → ℝ → ℝ → Type
def wholeLineIndexValue : wholeLineIndexType := fun center u v =>
  {R : ℝ // 0 < R ∧ center-R < u ∧ v < center+R}

abbrev wholeLineRegularType := (k : ScalarKind) → (ℝ → S.scalarValue k) → ℝ → ℝ → Prop
def wholeLineRegularValue : wholeLineRegularType := fun k f u v =>
  u ≤ v ∧ E.leftRegularValue k f ⊥ u ∧ E.rightRegularValue k f v ⊤

abbrev wholeLineTruncationType := (k : ScalarKind) → (f : ℝ → S.scalarValue k) →
  (center u v : ℝ) → S.scalarValue k → wholeLineRegularValue k f u v →
  wholeLineIndexValue center u v → S.scalarValue k
noncomputable def wholeLineTruncationValue : wholeLineTruncationType := fun k f center u v J h t =>
  E.leftTruncationValue k f ⊥ u h.2.1
    ⟨center-t.val, WithBot.bot_lt_coe _, t.property.2.1⟩ + J +
  E.rightTruncationValue k f v ⊤ h.2.2
    ⟨center+t.val, t.property.2.2, WithTop.coe_lt_top _⟩

abbrev wholeLineHasIntegralType := (k : ScalarKind) → (ℝ → S.scalarValue k) →
  ℝ → ℝ → ℝ → S.scalarValue k → S.scalarValue k → Prop
noncomputable def wholeLineHasIntegralValue : wholeLineHasIntegralType := fun k f center u v J L =>
  coreHasIntegralValue k f u v J ∧ ∃ h : wholeLineRegularValue k f u v,
    ∀ η : ℝ, 0 < η → ∃ A : ℝ, 0 < A ∧ ∀ t : wholeLineIndexValue center u v,
      A < t.val → dist (wholeLineTruncationValue k f center u v J h t) L < η

abbrev wholeLineConvergesType := (k : ScalarKind) → (ℝ → S.scalarValue k) →
  ℝ → ℝ → ℝ → S.scalarValue k → Prop
noncomputable def wholeLineConvergesValue : wholeLineConvergesType := fun k f center u v J =>
  ∃ L, wholeLineHasIntegralValue k f center u v J L

abbrev wholeLineIntegralType := (k : ScalarKind) → (f : ℝ → S.scalarValue k) →
  (center u v : ℝ) → (J : S.scalarValue k) → wholeLineConvergesValue k f center u v J → S.scalarValue k
noncomputable def wholeLineIntegralValue : wholeLineIntegralType := fun _ _ _ _ _ _ h => Classical.choose h

def interiorUnique : Prop := ∀ k f a b c L M,
  interiorHasIntegralValue k f a b c L → interiorHasIntegralValue k f a b c M → L = M

def interiorIntegralHasValue : Prop := ∀ k f a b c (h : interiorConvergesValue k f a b c),
  interiorHasIntegralValue k f a b c (interiorIntegralValue k f a b c h)

def interiorIntegralEq : Prop := ∀ k f a b c (h : interiorConvergesValue k f a b c) L,
  interiorHasIntegralValue k f a b c L → interiorIntegralValue k f a b c h = L

def interiorOfIndependent : Prop := ∀ k f a b (c : ℝ) l r,
  E.rightHasIntegralValue k f a (c : WithTop ℝ) l →
  E.leftHasIntegralValue k f (c : WithBot ℝ) b r → interiorHasIntegralValue k f a b c (l+r)

def controlledInteriorUnique : Prop := ∀ k f a b u v c L M,
  controlledInteriorHasIntegralValue k f a b u v c L →
  controlledInteriorHasIntegralValue k f a b u v c M → L = M

def controlledInteriorIntegralHasValue : Prop := ∀ k f a b u v c
  (h : controlledInteriorConvergesValue k f a b u v c),
  controlledInteriorHasIntegralValue k f a b u v c (controlledInteriorIntegralValue k f a b u v c h)

def controlledInteriorIntegralEq : Prop := ∀ k f a b u v c
  (h : controlledInteriorConvergesValue k f a b u v c) L,
  controlledInteriorHasIntegralValue k f a b u v c L →
  controlledInteriorIntegralValue k f a b u v c h = L

/-- Independent convergence on the two open components implies the PV with
exactly their sum, for every choice of regular anchors. -/
def controlledInteriorOfIndependent : Prop := ∀ k f a b (c : ℝ)
  (u : V.regularPointValue a (c : WithTop ℝ))
  (v : V.regularPointValue (c : WithBot ℝ) b) L M,
  V.hasIntegralValue k f a (c : WithTop ℝ) L →
  V.hasIntegralValue k f (c : WithBot ℝ) b M →
  controlledInteriorHasIntegralValue k f a b u.val v.val c (L+M)

/-- The anchor construction is the displayed pair of outer improper
truncations, with their two endpoint limits taken separately. -/
def controlledInteriorFormula : Prop := ∀ k f a b (c : ℝ)
  (u : V.regularPointValue a (c : WithTop ℝ))
  (v : V.regularPointValue (c : WithBot ℝ) b),
  V.locallyIntegrableValue k f a (c : WithTop ℝ) →
  V.locallyIntegrableValue k f (c : WithBot ℝ) b →
  ∀ l r, E.leftHasIntegralValue k f a u.val l → E.rightHasIntegralValue k f v.val b r →
  ∀ (h : interiorRegularValue k f u.val v.val c) (t : interiorIndexValue u.val v.val c),
  ∃ lt rt : S.scalarValue k,
    E.leftHasIntegralValue k f a (c-t.val) lt ∧
    E.rightHasIntegralValue k f (c+t.val) b rt ∧
    lt + rt = l + interiorTruncationValue k f u.val v.val c h t + r

def wholeLineUnique : Prop := ∀ k f center u v J L M,
  wholeLineHasIntegralValue k f center u v J L → wholeLineHasIntegralValue k f center u v J M → L = M

def wholeLineIntegralHasValue : Prop := ∀ k f center u v J
  (h : wholeLineConvergesValue k f center u v J),
  wholeLineHasIntegralValue k f center u v J (wholeLineIntegralValue k f center u v J h)

def wholeLineIntegralEq : Prop := ∀ k f center u v J
  (h : wholeLineConvergesValue k f center u v J) L,
  wholeLineHasIntegralValue k f center u v J L → wholeLineIntegralValue k f center u v J h = L

def wholeLineOfIndependent : Prop := ∀ k f center u v J l r, u ≤ v →
  coreHasIntegralValue k f u v J → E.leftHasIntegralValue k f ⊥ u l →
  E.rightHasIntegralValue k f v ⊤ r → wholeLineHasIntegralValue k f center u v J (l+J+r)

/-- Ordinary convergence on ℝ implies the symmetric value about every center;
the singleton core has value zero and no interior singularity is hidden. -/
def wholeLineOfOrdinary : Prop := ∀ k f center L,
  V.hasIntegralValue k f ⊥ ⊤ L → wholeLineHasIntegralValue k f center center center 0 L

/-- When the core is proper, the whole-line truncation is precisely the
proper integral from center-R to center+R, rather than a new integral. -/
def wholeLineProperFormula : Prop := ∀ k f center u v J
  (h : wholeLineRegularValue k f u v) (t : wholeLineIndexValue center u v)
  (hc : I.scalarIntegrableValue k f u v), I.scalarIntegralValue k f hc = J →
  ∃ hp : I.scalarIntegrableValue k f (center-t.val) (center+t.val),
    wholeLineTruncationValue k f center u v J h t = I.scalarIntegralValue k f hp

end Specs.SingleVariableAnalysis.Ch10.PrincipalValue
