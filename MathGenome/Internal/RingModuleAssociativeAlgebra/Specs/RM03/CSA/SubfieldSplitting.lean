import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.Degree
import Mathlib.Algebra.Module.Opposite

/-! The degree-sized subfield splitting step in RM03-C04.05 and RM03-C04.09. -/

namespace Specs.RM03.CSA

open scoped TensorProduct

set_option linter.checkUnivs false

universe u v w

variable {k : Type u} [Field k] {D : Type v} [DivisionRing D] [Algebra k D]
variable {E : Type w} [Field E] [Algebra k E]

/-- A subfield is presented by its inclusion `f`. A unital algebra homomorphism
from a field into a division algebra is injective, and a subfield with inherited
operations gives such an inclusion by its subtype map. Left scalar notation
records right multiplication. -/
abbrev rightSubfieldModule (f : E →ₐ[k] D) : Module E D :=
  Module.compHom D (f.toOpposite fun e e' => (Commute.all e e').map f).toRingHom

def RightSubfieldModuleType :=
  ∀ {k : Type u} [Field k] {D : Type v} [DivisionRing D] [Algebra k D]
    {E : Type w} [Field E] [Algebra k E], (E →ₐ[k] D) → Module E D

def RightSubfieldSMul : Prop :=
  ∀ {k : Type u} [Field k] {D : Type v} [DivisionRing D] [Algebra k D]
    {E : Type w} [Field E] [Algebra k E] (f : E →ₐ[k] D),
    letI := rightSubfieldModule f
    ∀ (e : E) (z : D), e • z = z * f e

theorem rightSubfieldTower (f : E →ₐ[k] D) :
    letI := rightSubfieldModule f
    IsScalarTower k E D := by
  let := rightSubfieldModule f
  apply IsScalarTower.of_algebraMap_smul
  intro r z
  change z * f (algebraMap k E r) = r • z
  rw [f.commutes, Algebra.smul_def, Algebra.commutes]

private theorem leftMulCommutes (f : E →ₐ[k] D) :
    letI := rightSubfieldModule f
    SMulCommClass D E D := by
  let := rightSubfieldModule f
  exact ⟨fun a e z => mul_assoc a z (f e) |>.symm⟩

def SubfieldTensorActionType :=
  ∀ {k : Type u} [Field k] {D : Type v} [DivisionRing D] [Algebra k D]
    {E : Type w} [Field E] [Algebra k E] (f : E →ₐ[k] D),
    letI := rightSubfieldModule f
    letI := Algebra.TensorProduct.rightAlgebra (R := k) (A := D) (B := E)
    D ⊗[k] E →ₐ[E] Module.End E D

/-- The scalar map and the left regular representation induce the tensor action. -/
def subfieldTensorAction (f : E →ₐ[k] D) :
    letI := rightSubfieldModule f
    letI := Algebra.TensorProduct.rightAlgebra (R := k) (A := D) (B := E)
    D ⊗[k] E →ₐ[E] Module.End E D :=
  letI := rightSubfieldModule f
  letI := Algebra.TensorProduct.rightAlgebra (R := k) (A := D) (B := E)
  haveI := rightSubfieldTower f
  haveI := leftMulCommutes f
  (Algebra.TensorProduct.lift (Algebra.ofId E (Module.End E D)) (Algebra.lsmul k E D)
    (fun e a => Algebra.commutes e (Algebra.lsmul k E D a))).comp
    (baseChangeEquivTensor k E D).symm.toAlgHom

def SubfieldTensorActionTmul : Prop :=
  ∀ {k : Type u} [Field k] {D : Type v} [DivisionRing D] [Algebra k D]
    {E : Type w} [Field E] [Algebra k E] (f : E →ₐ[k] D),
    letI := rightSubfieldModule f
    ∀ (a : D) (e : E) (z : D), subfieldTensorAction f (a ⊗ₜ[k] e) z = a * z * f e

def RightSubfieldDimension : Prop :=
  ∀ {k : Type u} [Field k] {D : Type v} [DivisionRing D] [Algebra k D]
    {E : Type w} [Field E] [Algebra k E] (f : E →ₐ[k] D),
    isCentralDivision k D → Module.finrank k E = degree k D →
    letI := rightSubfieldModule f
    FiniteDimensional E D ∧ Module.finrank E D = degree k D

def SubfieldTensorActionIsomorphism : Prop :=
  ∀ {k : Type u} [Field k] {D : Type v} [DivisionRing D] [Algebra k D]
    {E : Type w} [Field E] [Algebra k E] (f : E →ₐ[k] D),
    isCentralDivision k D → Module.finrank k E = degree k D →
    letI := rightSubfieldModule f
    letI := Algebra.TensorProduct.rightAlgebra (R := k) (A := D) (B := E)
    ∃ iso : D ⊗[k] E ≃ₐ[E] Module.End E D, iso.toAlgHom = subfieldTensorAction f

def SubfieldSplits : Prop :=
  ∀ {k : Type u} [Field k] {D : Type v} [DivisionRing D] [Algebra k D]
    {E : Type w} [Field E] [Algebra k E] (_f : E →ₐ[k] D),
    isCentralDivision k D → Module.finrank k E = degree k D →
    Nonempty (baseChange k E D ≃ₐ[E] Matrix (Fin (degree k D)) (Fin (degree k D)) E)

end Specs.RM03.CSA
