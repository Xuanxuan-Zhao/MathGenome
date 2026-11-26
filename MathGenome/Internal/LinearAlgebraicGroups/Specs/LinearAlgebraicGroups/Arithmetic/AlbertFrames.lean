import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.AutomorphismType
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.IntrinsicCubic
import Mathlib.FieldTheory.SeparableClosure

/-! Cubic-norm and rank-one frame constructions for the type F₄ case of F12. -/

namespace LinearAlgebraicGroups.Arithmetic.AlbertFramesSpecification

open TensorProduct
open scoped TensorProduct
open LinearAlgebraicGroups.Albert
open SplitSpecification IntrinsicCubicSpecification

universe u v

section Algebra

variable {k : Type u} [Field k] {M : Type v} [AddCommGroup M] [Module k M]

/-- The ground-field evaluation of the pointed law. -/
abbrev Ground (k : Type u) (M : Type v) [Field k] [AddCommGroup M] [Module k M] :=
  k ⊗[k] M

abbrev unit (J : ParaQuadratic k M) : Ground k M := 1 ⊗ₜ[k] J.unit
abbrev U (J : ParaQuadratic k M) := J.op k
abbrev trace (F : Coefficients k M) := F.trace.eval k
abbrev norm (F : Coefficients k M) := F.norm.eval k
abbrev sharp (J : ParaQuadratic k M) (F : Coefficients k M) := adjoint J F k

/-- Rank-one points are characterized by trace one and zero cubic adjoint. -/
def IsRankOne (J : ParaQuadratic k M) (F : Coefficients k M) (e : Ground k M) : Prop :=
  trace F e = 1 ∧ sharp J F e = 0

/-- The image of the quadratic Peirce-zero projector. -/
abbrev PeirceZero (J : ParaQuadratic k M) (e : Ground k M) :=
  LinearMap.range (U J (unit J - e))

/-- The intrinsic scalar formula on the Peirce-zero image. -/
def cornerNorm (J : ParaQuadratic k M) (F : Coefficients k M) (e : Ground k M)
    (z : PeirceZero J e) : k :=
  trace F (sharp J F z.val)

/-- A frame of trace-one idempotents with the Peirce-zero relation of the split incidence. -/
def IsFrame (J : ParaQuadratic k M) (F : Coefficients k M) (e : Fin 3 → Ground k M) : Prop :=
  (∀ i, IsRankOne J F (e i) ∧ U J (e i) (unit J) = e i) ∧
  (∀ i j, i ≠ j → U J (unit J - e i) (e j) = e j ∧ U J (e i) (e j) = 0) ∧
  e 0 + e 1 + e 2 = unit J

def ZeroAdjointFromNorm : Prop :=
  ∀ {k : Type u} [Field k] {M : Type v} [AddCommGroup M] [Module k M]
    (J : ParaQuadratic k M) (F : Coefficients k M), IsAlbert J → IsCharacteristic J F →
    (∃ x : Ground k M, x ≠ 0 ∧ norm F x = 0) →
    ∃ y : Ground k M, y ≠ 0 ∧ sharp J F y = 0

def IdempotentFromNorm : Prop :=
  ∀ {k : Type u} [Field k] [Infinite k] {M : Type v} [AddCommGroup M] [Module k M]
    (J : ParaQuadratic k M) (F : Coefficients k M), IsAlbert J → IsCharacteristic J F →
    (∃ x : Ground k M, x ≠ 0 ∧ norm F x = 0) →
    ∃ e : Ground k M, IsRankOne J F e ∧ U J e (unit J) = e

/-- The Peirce-zero module carries the regular quadratic trace and its original
polar formula, with no restriction on the characteristic. -/
def PeirceZeroStructure : Prop :=
  ∀ {k : Type u} [Field k] {M : Type v} [AddCommGroup M] [Module k M]
    (J : ParaQuadratic k M) (F : Coefficients k M), IsAlbert J → IsCharacteristic J F →
    ∀ e : Ground k M, IsRankOne J F e →
      let c := unit J - e
      (∀ z, U J c (U J c z) = U J c z) ∧
      ∃ hc : U J c c = c, trace F c = 2 ∧
      Module.finrank k (PeirceZero J e) = 10 ∧
      ∃ q : QuadraticForm k (PeirceZero J e),
        (∀ z : PeirceZero J e, (∀ w, QuadraticMap.polar q z w = 0) → z = 0) ∧
        (∀ z, q z = cornerNorm J F e z) ∧
        q ⟨c, ⟨c, hc⟩⟩ = 1 ∧
        (∀ z : PeirceZero J e, sharp J F z.val = q z • e ∧
          U J z.val (unit J) = trace F z.val • z.val - q z • c) ∧
        (∀ z w : PeirceZero J e,
          QuadraticMap.polar q z w = trace F z.val * trace F w.val - pairing F k z.val w.val) ∧
        ∀ z : PeirceZero J e, pairing F k c z.val = trace F z.val ∧
          QuadraticMap.polar q ⟨c, ⟨c, hc⟩⟩ z = trace F z.val

def FrameCompletion : Prop :=
  ∀ {k : Type u} [Field k] {M : Type v} [AddCommGroup M] [Module k M]
    (J : ParaQuadratic k M) (F : Coefficients k M), IsAlbert J → IsCharacteristic J F →
    ∀ e : Ground k M, IsRankOne J F e →
      (∃ z : PeirceZero J e, z ≠ 0 ∧ cornerNorm J F e z = 0) →
      ∃ f : Fin 3 → Ground k M, f 0 = e ∧ f 2 = unit J - e - f 1 ∧ IsFrame J F f ∧
        ∃ z : PeirceZero J e, z.val = f 1 ∧ trace F z.val = 1 ∧ cornerNorm J F e z = 0

end Algebra

open CategoryTheory
open scoped CategoryTheory.MonObj
open AutomorphismTypeSpecification
open LinearAlgebraicGroups.Specs

/-- Every separably split form of the specified split Chevalley group is the
automorphism scheme of an Albert algebra. A nontrivial split cocharacter
in such a form gives a norm-zero vector and a rank-one idempotent. -/
def FormsAndIsotropy : Prop :=
  ∃ S : IntegralSplitIdentification,
    ∀ {k K : Type} [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
      (H : AffineAlgebraicGroup k),
      Nonempty (((groupChange k K).obj H.val) ≅ (chevalleyChange K).obj S.chevalley.group) →
      ∃ (M : Type) (_ : AddCommGroup M) (_ : Module k M) (J : ParaQuadratic k M)
        (F : Coefficients k M), IsAlbert J ∧ IsCharacteristic J F ∧
        RepresentsAutomorphisms J H.val ∧
        (∀ (cochar : CharacterDescent.Cocharacter H.val), cochar.hom.hom ≠ 1 →
          (∃ x : Ground k M, x ≠ 0 ∧ norm F x = 0) ∧
          ∃ e : Ground k M, IsRankOne J F e ∧ U J e (unit J) = e)

end LinearAlgebraicGroups.Arithmetic.AlbertFramesSpecification
