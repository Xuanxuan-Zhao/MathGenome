import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.SeveralEndpoints

/-!
K03.10.parts, paper.tex:3112–3131. These are finite limits of the upstream
proper Darboux integrals, for exactly ℝ and ℂ. `du` and `dv` denote the
functions appearing as derivatives in the proper formula. As in the source,
the hypothesis here is the proper formula on every regular truncation;
no additional differentiability or absolute convergence is imposed.

The boundary limits use the same cofinal cutoffs as OneEndpoint, covering
finite and infinite endpoints. In the finite singular-list statement, each
component has two separately quantified boundary limits; opposite sides of
an interior singularity need not have the same limit. All boundary values
are scalars. No subtraction of infinities or linked truncations occurs.
-/
namespace Specs.SingleVariableAnalysis.Ch10.Parts
open _root_.SingleVariableAnalysis
open scoped BigOperators
namespace E
export Specs.SingleVariableAnalysis.Ch10.OneEndpoint
  (rightIndexValue leftIndexValue rightRegularValue leftRegularValue
   rightTruncationValue leftTruncationValue rightHasIntegralValue leftHasIntegralValue
   rightConvergesValue leftConvergesValue scalarNormedAddCommGroup)
end E
namespace M
export Specs.SingleVariableAnalysis.Ch10.SeveralEndpoints
  (regularPointValue locallyIntegrableValue hasIntegralAtSplitValue hasIntegralValue
   convergesValue finiteHasIntegralValue finiteConvergesValue splitFamilyValue
   componentLeftValue componentRightValue)
end M
namespace I
export Specs.SingleVariableAnalysis.Ch08.Integral (scalarIntegralValue scalarIntegrableValue)
end I
namespace S
export Specs.SingleVariableAnalysis.Ch01.Scalar (scalarValue)
end S

/-- The usual multiplication, with no abstract scalar field parameter. -/
instance scalarMul (k : ScalarKind) : Mul (S.scalarValue k) :=
  match k with
  | .real => inferInstanceAs (Mul ℝ)
  | .complex => inferInstanceAs (Mul ℂ)

noncomputable section

def RightBoundaryLimit (k : ScalarKind) (w : ℝ → S.scalarValue k)
    (a : ℝ) (b : WithTop ℝ) (B : S.scalarValue k) : Prop :=
  (a : WithTop ℝ) < b ∧ ∀ ε : ℝ, 0 < ε →
    ∃ r : E.rightIndexValue a b, ∀ t : E.rightIndexValue a b,
      r.val < t.val → dist (w t.val) B < ε

def LeftBoundaryLimit (k : ScalarKind) (w : ℝ → S.scalarValue k)
    (a : WithBot ℝ) (b : ℝ) (A : S.scalarValue k) : Prop :=
  a < (b : WithBot ℝ) ∧ ∀ ε : ℝ, 0 < ε →
    ∃ r : E.leftIndexValue a b, ∀ t : E.leftIndexValue a b,
      t.val < r.val → dist (w t.val) A < ε

/-- Integrability and the given proper parts formula on each right truncation. -/
def RightPartsData (k : ScalarKind) (u v du dv : ℝ → S.scalarValue k)
    (a : ℝ) (b : WithTop ℝ) : Prop :=
  ∃ hf : E.rightRegularValue k (fun x => u x * dv x) a b,
  ∃ hg : E.rightRegularValue k (fun x => du x * v x) a b,
    ∀ t : E.rightIndexValue a b,
      E.rightTruncationValue k _ a b hf t =
        u t.val * v t.val - u a * v a - E.rightTruncationValue k _ a b hg t

def LeftPartsData (k : ScalarKind) (u v du dv : ℝ → S.scalarValue k)
    (a : WithBot ℝ) (b : ℝ) : Prop :=
  ∃ hf : E.leftRegularValue k (fun x => u x * dv x) a b,
  ∃ hg : E.leftRegularValue k (fun x => du x * v x) a b,
    ∀ t : E.leftIndexValue a b,
      E.leftTruncationValue k _ a b hf t =
        u b * v b - u t.val * v t.val - E.leftTruncationValue k _ a b hg t

/-- The same proper formula throughout an open regular component. -/
def PartsOn (k : ScalarKind) (u v du dv : ℝ → S.scalarValue k)
    (a : WithBot ℝ) (b : WithTop ℝ) : Prop :=
  ∃ hf : M.locallyIntegrableValue k (fun x => u x * dv x) a b,
  ∃ hg : M.locallyIntegrableValue k (fun x => du x * v x) a b,
    ∀ r s : M.regularPointValue a b, ∀ hrs : r.val ≤ s.val,
      I.scalarIntegralValue k _ (hf _ _ r.property.1 hrs s.property.2) =
        u s.val * v s.val - u r.val * v r.val -
          I.scalarIntegralValue k _ (hg _ _ r.property.1 hrs s.property.2)

def rightPartsFromDu : Prop := ∀ k (u v du dv : ℝ → S.scalarValue k) a b B J,
  RightPartsData k u v du dv a b →
  RightBoundaryLimit k (fun x => u x * v x) a b B →
  E.rightHasIntegralValue k (fun x => du x * v x) a b J →
  E.rightHasIntegralValue k (fun x => u x * dv x) a b (B - u a * v a - J)

def rightPartsFromDv : Prop := ∀ k (u v du dv : ℝ → S.scalarValue k) a b B H,
  RightPartsData k u v du dv a b →
  RightBoundaryLimit k (fun x => u x * v x) a b B →
  E.rightHasIntegralValue k (fun x => u x * dv x) a b H →
  E.rightHasIntegralValue k (fun x => du x * v x) a b (B - u a * v a - H)

def rightParts : Prop := ∀ k (u v du dv : ℝ → S.scalarValue k) a b B,
  RightPartsData k u v du dv a b →
  RightBoundaryLimit k (fun x => u x * v x) a b B →
  (E.rightConvergesValue k (fun x => u x * dv x) a b ↔
    E.rightConvergesValue k (fun x => du x * v x) a b) ∧
  ∀ H J, E.rightHasIntegralValue k (fun x => u x * dv x) a b H →
    E.rightHasIntegralValue k (fun x => du x * v x) a b J →
    H = B - u a * v a - J

def leftPartsFromDu : Prop := ∀ k (u v du dv : ℝ → S.scalarValue k) a b A J,
  LeftPartsData k u v du dv a b →
  LeftBoundaryLimit k (fun x => u x * v x) a b A →
  E.leftHasIntegralValue k (fun x => du x * v x) a b J →
  E.leftHasIntegralValue k (fun x => u x * dv x) a b (u b * v b - A - J)

def leftPartsFromDv : Prop := ∀ k (u v du dv : ℝ → S.scalarValue k) a b A H,
  LeftPartsData k u v du dv a b →
  LeftBoundaryLimit k (fun x => u x * v x) a b A →
  E.leftHasIntegralValue k (fun x => u x * dv x) a b H →
  E.leftHasIntegralValue k (fun x => du x * v x) a b (u b * v b - A - H)

def leftParts : Prop := ∀ k (u v du dv : ℝ → S.scalarValue k) a b A,
  LeftPartsData k u v du dv a b →
  LeftBoundaryLimit k (fun x => u x * v x) a b A →
  (E.leftConvergesValue k (fun x => u x * dv x) a b ↔
    E.leftConvergesValue k (fun x => du x * v x) a b) ∧
  ∀ H J, E.leftHasIntegralValue k (fun x => u x * dv x) a b H →
    E.leftHasIntegralValue k (fun x => du x * v x) a b J →
    H = u b * v b - A - J

def twoEndpointParts : Prop := ∀ k (u v du dv : ℝ → S.scalarValue k) a b
  (c : M.regularPointValue a b) A B,
  PartsOn k u v du dv a b →
  LeftBoundaryLimit k (fun x => u x * v x) a c.val A →
  RightBoundaryLimit k (fun x => u x * v x) c.val b B →
  (M.convergesValue k (fun x => u x * dv x) a b ↔
    M.convergesValue k (fun x => du x * v x) a b) ∧
  ∀ H J, M.hasIntegralValue k (fun x => u x * dv x) a b H →
    M.hasIntegralValue k (fun x => du x * v x) a b J → H = B - A - J

def finiteEndpointParts : Prop := ∀ k (u v du dv : ℝ → S.scalarValue k)
  n a b (s : Fin n → ℝ) (c : M.splitFamilyValue n a b s)
  (A B : Fin (n+1) → S.scalarValue k),
  (∀ i, PartsOn k u v du dv (M.componentLeftValue n a s i) (M.componentRightValue n b s i)) →
  (∀ i, LeftBoundaryLimit k (fun x => u x * v x) (M.componentLeftValue n a s i) (c i).val (A i)) →
  (∀ i, RightBoundaryLimit k (fun x => u x * v x) (c i).val (M.componentRightValue n b s i) (B i)) →
  (M.finiteConvergesValue k (fun x => u x * dv x) n a b s c ↔
    M.finiteConvergesValue k (fun x => du x * v x) n a b s c) ∧
  ∀ H J, M.finiteHasIntegralValue k (fun x => u x * dv x) n a b s c H →
    M.finiteHasIntegralValue k (fun x => du x * v x) n a b s c J →
    H = (∑ i, (B i - A i)) - J

end
end Specs.SingleVariableAnalysis.Ch10.Parts
