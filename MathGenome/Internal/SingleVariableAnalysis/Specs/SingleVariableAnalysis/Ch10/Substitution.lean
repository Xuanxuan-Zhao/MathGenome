import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.OneEndpoint
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.MonotoneSubstitution

/-! K03.10.substitution, paper.tex:3132–3157.
`Ray.right a b` is [a,b), `Ray.left a b` is (a,b], with the same finite/infinite
endpoints as OneEndpoint. Values below are oriented FROM the regular base TO
the singular endpoint: for a left ray they are the negatives of the existing
left improper integrals. Thus all four combinations of source/target rays
include increasing/decreasing maps and both endpoint approaches.
C¹ means C¹ on every regular compact truncation (one-sided at the base).
Monotonicity is non-strict; no injectivity or nonzero derivative is assumed.
Onto includes the base, so initial flat pieces are permitted. Cofinality is
proved from these hypotheses, not included as a certificate. Integrands are
only locally properly Darboux integrable; absolute convergence is not required.
-/
namespace Specs.SingleVariableAnalysis.Ch10.Substitution
open _root_.SingleVariableAnalysis Set
namespace E
export OneEndpoint (rightIndexValue leftIndexValue rightRegularValue leftRegularValue
  rightTruncationValue leftTruncationValue rightHasIntegralValue leftHasIntegralValue
  rightIntegralValue leftIntegralValue)
end E
namespace I
export Ch08.Integral (scalarIntegrableValue scalarIntegralValue)
end I
abbrev ScalarValue := Specs.SingleVariableAnalysis.Ch01.Scalar.scalarValue

inductive Ray where
  | right (base : ℝ) (endpoint : WithTop ℝ)
  | left (endpoint : WithBot ℝ) (base : ℝ)

def Ray.base : Ray → ℝ
  | .right a _ => a
  | .left _ b => b

def Ray.Index : Ray → Type
  | .right a b => E.rightIndexValue a b
  | .left a b => E.leftIndexValue a b

def Ray.point (r : Ray) : r.Index → ℝ := by
  cases r <;> exact Subtype.val

def Ray.domain : Ray → Set ℝ
  | .right a b => {x | a ≤ x ∧ (x : WithTop ℝ) < b}
  | .left a b => {x | a < (x : WithBot ℝ) ∧ x ≤ b}

/-- Order in the direction from the base towards the singular endpoint. -/
def Ray.le : Ray → ℝ → ℝ → Prop
  | .right _ _ => fun x y => x ≤ y
  | .left _ _ => fun x y => y ≤ x

def Ray.lt : Ray → ℝ → ℝ → Prop
  | .right _ _ => fun x y => x < y
  | .left _ _ => fun x y => y < x

def Ray.Regular (r : Ray) (k : ScalarKind) (f : ℝ → ScalarValue k) : Prop :=
  match r with
  | .right a b => E.rightRegularValue k f a b
  | .left a b => E.leftRegularValue k f a b

noncomputable def Ray.truncation (r : Ray) (k : ScalarKind)
    (f : ℝ → ScalarValue k) (h : r.Regular k f) (t : r.Index) : ScalarValue k :=
  match r with
  | .right a b => E.rightTruncationValue k f a b h t
  | .left a b => -E.leftTruncationValue k f a b h t

noncomputable def Ray.HasIntegral (r : Ray) (k : ScalarKind)
    (f : ℝ → ScalarValue k) (L : ScalarValue k) : Prop :=
  match r with
  | .right a b => E.rightHasIntegralValue k f a b L
  | .left a b => E.leftHasIntegralValue k f a b (-L)

noncomputable def Ray.Converges (r : Ray) (k : ScalarKind)
    (f : ℝ → ScalarValue k) : Prop := ∃ L, r.HasIntegral k f L

noncomputable def Ray.integral (r : Ray) (k : ScalarKind)
    (f : ℝ → ScalarValue k) (h : r.Converges k f) : ScalarValue k := Classical.choose h

def orientedIntegrable (k : ScalarKind) (f : ℝ → ScalarValue k) (a b : ℝ) : Prop :=
  I.scalarIntegrableValue k f (min a b) (max a b)

noncomputable def orientedIntegral (k : ScalarKind) (f : ℝ → ScalarValue k)
    {a b : ℝ} (h : orientedIntegrable k f a b) : ScalarValue k :=
  if a ≤ b then I.scalarIntegralValue k f h else -I.scalarIntegralValue k f h

def transform : (k : ScalarKind) → (ℝ → ScalarValue k) →
    (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ScalarValue k
  | .real, f, φ, dφ => fun t => (dφ t * (show ℝ from f (φ t)) : ℝ)
  | .complex, f, φ, dφ => fun t => ((dφ t : ℂ) * (show ℂ from f (φ t)) : ℂ)

/-- A monotone onto C¹ map, with the corresponding regular endpoint mapping.
Both ordinary directions of non-strict monotonicity are allowed; the endpoint
mapping determines the compatible direction. -/
structure Parameterization (s r : Ray) (φ dφ : ℝ → ℝ) : Prop where
  base_eq : φ s.base = r.base
  maps : MapsTo φ s.domain r.domain
  onto : SurjOn φ s.domain r.domain
  monotone : MonotoneOn φ s.domain ∨ AntitoneOn φ s.domain
  c1 : ∀ t : s.Index, Ch09.MonotoneSubstitution.C1OnInterval φ dφ
    (min s.base (s.point t)) (max s.base (s.point t))

def parameterizationCofinal : Prop := ∀ (s r : Ray) (φ dφ : ℝ → ℝ),
  Parameterization s r φ dφ → Nonempty r.Index →
  ∀ y ∈ r.domain, ∃ T : s.Index, ∀ t : s.Index,
    s.lt (s.point T) (s.point t) → r.lt y (φ (s.point t))

def substitutionRegular : Prop := ∀ (s r : Ray) (k : ScalarKind)
  (f : ℝ → ScalarValue k) (φ dφ : ℝ → ℝ),
  Parameterization s r φ dφ → r.Regular k f → s.Regular k (transform k f φ dφ)

def substitutionTruncation : Prop := ∀ (s r : Ray) (k : ScalarKind)
  (f : ℝ → ScalarValue k) (φ dφ : ℝ → ℝ)
  (_hp : Parameterization s r φ dφ) (_hf : r.Regular k f)
  (hg : s.Regular k (transform k f φ dφ)) (t : s.Index),
  ∃ hft : orientedIntegrable k f r.base (φ (s.point t)),
    s.truncation k (transform k f φ dφ) hg t = orientedIntegral k f hft

def substitutionHasIntegral : Prop := ∀ (s r : Ray) (k : ScalarKind)
  (f : ℝ → ScalarValue k) (φ dφ : ℝ → ℝ),
  Parameterization s r φ dφ → r.Regular k f → ∀ L,
    r.HasIntegral k f L ↔ s.HasIntegral k (transform k f φ dφ) L

def substitutionConverges : Prop := ∀ (s r : Ray) (k : ScalarKind)
  (f : ℝ → ScalarValue k) (φ dφ : ℝ → ℝ),
  Parameterization s r φ dφ → r.Regular k f →
    (r.Converges k f ↔ s.Converges k (transform k f φ dφ))

def substitutionIntegral : Prop := ∀ (s r : Ray) (k : ScalarKind)
  (f : ℝ → ScalarValue k) (φ dφ : ℝ → ℝ),
  Parameterization s r φ dφ → r.Regular k f →
  ∀ (hr : r.Converges k f) (hs : s.Converges k (transform k f φ dφ)),
    r.integral k f hr = s.integral k (transform k f φ dφ) hs

/-- Reversing the integration orientation negates its value on either side. -/
def substitutionReverse : Prop := ∀ (s r : Ray) (k : ScalarKind)
  (f : ℝ → ScalarValue k) (φ dφ : ℝ → ℝ),
  Parameterization s r φ dφ → r.Regular k f → ∀ L,
    r.HasIntegral k f (-L) ↔ s.HasIntegral k (transform k f φ dφ) (-L)

end Specs.SingleVariableAnalysis.Ch10.Substitution
