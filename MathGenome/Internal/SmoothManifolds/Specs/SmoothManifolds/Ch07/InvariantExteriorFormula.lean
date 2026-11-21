import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch07.ExteriorDerivative
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.LieBracket

/-! Independent statements for paper.tex 1520--1529.

The vector fields and exterior fibers are the original intrinsic ones. A form's
exterior derivative is specified by the full coordinate characterization, rather
than by an extra axiom about evaluations on fields. The functions whose
field derivatives occur in the formula are constructed as global smooth
functions, with their values specified exactly.

The positive-degree formula indexes pairs by `i j : Fin (k+1)`, `i ≤ j`.
They represent the original ordered pair `(i, j+1)` in `Fin (k+2)`.
Thus the sign is `(-1)^(i+j+1)`, and the two successive `removeNth`
operations leave every other argument in its original order. Degree zero is
stated separately because the bracket sum is empty.

No boundary-tangency, commutativity, positive dimension, or degree bound is
imposed. The imported coordinate characterization uses ambient extensions at
boundary points, retaining all tangent directions. -/
set_option autoImplicit false
noncomputable section

namespace Specs.SmoothManifolds.Ch07.InvariantExteriorFormula
open _root_.SmoothManifolds _root_.SmoothManifolds.BundleOperationsData
  _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.TangentData _root_.SmoothManifolds.TangentBundleData
  _root_.SmoothManifolds.CovectorData _root_.SmoothManifolds.ExteriorData
  _root_.SmoothManifolds.PartitionData
  _root_.SmoothManifolds.ExteriorDerivativeData
  _root_.SmoothManifolds.VectorFieldData _root_.SmoothManifolds.LieBracketData
universe u

/-- The invariant formula on functions, including existence of their smooth
evaluation representatives. This is the empty-bracket-sum case of the formula. -/
def invariant_zeroType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (B : FormBundle C 0)
    (ω : Field S 0) (η : Field S 1),
    IsForm B ω → HasExteriorDerivative C ω η →
    ∀ X : SmoothField C.tangent,
      ∃ (f : M → ℝ) (hf : ScalarSmooth S.smoothStructure.val f),
        (∀ p, f p = evaluate (TangentSpace S p) 0 (ω p) Fin.elim0) ∧
        ∀ p, evaluate (TangentSpace S p) 1 (η p) (fun _ => X.val p) =
          (X.val p).val (functionGerm S f hf p)

/-- The invariant evaluation formula on all positive-degree smooth forms.
The scalar functions in the first sum are exactly the evaluations of ω on the
fields with the indicated slot omitted; their smoothness is a conclusion. -/
def invariant_positiveType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (B : FormBundle C (k+1)) (ω : Field S (k+1)) (η : Field S (k+2)),
    IsForm B ω → HasExteriorDerivative C ω η →
    ∀ b : SmoothField C.tangent → SmoothField C.tangent → SmoothField C.tangent,
      BracketOperation b →
      ∀ X : Fin (k+2) → SmoothField C.tangent,
        ∃ (f : Fin (k+2) → M → ℝ)
          (hf : ∀ i, ScalarSmooth S.smoothStructure.val (f i)),
          (∀ i p, f i p = evaluate (TangentSpace S p) (k+1) (ω p)
            (i.removeNth (fun j => (X j).val p))) ∧
          ∀ p, evaluate (TangentSpace S p) (k+2) (η p) (fun j => (X j).val p) =
            (∑ i : Fin (k+2), (-1 : ℝ)^i.val *
              ((X i).val p).val (functionGerm S (f i) (hf i) p)) +
            ∑ i : Fin (k+1), ∑ j ∈ Finset.Ici i,
              (-1 : ℝ)^(i.val+j.val+1) *
                evaluate (TangentSpace S p) (k+1) (ω p)
                  (Matrix.vecCons ((b (X i.castSucc) (X j.succ)).val p)
                    (j.removeNth (i.castSucc.removeNth (fun l => (X l).val p))))

end Specs.SmoothManifolds.Ch07.InvariantExteriorFormula
