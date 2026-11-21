import MathGenome.Internal.Specs.D07.Ch12.AlgebraicClosure
import MathGenome.Internal.D07.Ch12.RelativeAlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
Algebraic closures: existence, uniqueness, and realization inside any
algebraically closed overfield (K07.12.algebraic_closure).

For existence we use Mathlib's abstract maximal-ideal construction of
`AlgebraicClosure K`. Its field and algebraicity instances come from the
polynomial quotient; its closedness is proved by splitting the base-field
polynomials and algebraicity. It does not use complex algebraic closedness.

`IsAlgClosure.equiv` proves uniqueness for arbitrary algebraic closures
with their prescribed base actions. The relative field is exactly the
canonical object already used in K07.12.relative_algebraic_closure.
Mathlib's `algebraicClosure.isAlgClosure` proves its closedness when the
ambient field is closed; it imposes no algebraicity condition on the ambient
extension. Membership and algebraicity are reused from the upstream goal.
-/

universe u v w

namespace D07.Ch12.AlgebraicClosure

open Specs.D07.Ch12.AlgebraicClosure

theorem existence : Existence.{u} := by
  intro K _
  exact ⟨_root_.AlgebraicClosure K, inferInstance, inferInstance,
    (algebraMap K (_root_.AlgebraicClosure K)).injective,
    inferInstance, inferInstance⟩

theorem uniqueness : Uniqueness.{u, v, w} := by
  intro K L M _ _ _ _ _ _ _ _ _
  let : IsAlgClosure K L := ⟨inferInstance, inferInstance⟩
  let : IsAlgClosure K M := ⟨inferInstance, inferInstance⟩
  exact ⟨IsAlgClosure.equiv K L M⟩

theorem relativeClosure : RelativeClosure.{u, v} := by
  intro K Ω _ _ _ _
  exact ⟨RelativeAlgebraicClosure.mem_relativeAlgebraicClosure_iff K Ω,
    RelativeAlgebraicClosure.relative_algebraic_closure_is_algebraic K Ω,
    IsAlgClosure.isAlgClosed K⟩

end D07.Ch12.AlgebraicClosure
