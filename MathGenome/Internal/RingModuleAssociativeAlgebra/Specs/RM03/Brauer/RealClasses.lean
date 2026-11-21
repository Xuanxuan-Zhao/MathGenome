import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Brauer.Group
import Mathlib.Algebra.Quaternion
import Mathlib.Basic.Real.Basic
import Mathlib.Data.ZMod.Defs

/-! The real classification in RM03-C04.12. -/

noncomputable section

namespace Specs.RM03.Brauer

open MulOpposite

/-- The Hamilton quaternions are a central division algebra over the reals. -/
def QuaternionIsCentralDivision : Prop :=
  CSA.isCentralDivision ℝ (Quaternion ℝ)

/-- Quaternion conjugation identifies the Hamilton algebra with its opposite. -/
def QuaternionConjugation : Prop :=
  ∃ e : Quaternion ℝ ≃ₐ[ℝ] (Quaternion ℝ)ᵐᵒᵖ, ∀ q, e q = op (star q)

/-- The class represented by the real field with its identity algebra structure. -/
def realClass : BrauerGroup.{0, 0} ℝ :=
  classOf (divisionCSA (D := ℝ) ⟨inferInstance, inferInstance⟩)

/-- The class represented by the Hamilton division algebra. -/
def quaternionClass (h : QuaternionIsCentralDivision) : BrauerGroup.{0, 0} ℝ :=
  classOf (divisionCSA h)

/-- The two classes and the isomorphism carrying the Hamilton class to one. -/
def RealClasses (h : QuaternionIsCentralDivision) (g : AddCommGroup (BrauerGroup.{0, 0} ℝ)) :
    Prop :=
  letI := g
  realClass = 0 ∧ quaternionClass h ≠ 0 ∧
    (∀ c : BrauerGroup.{0, 0} ℝ, c = realClass ∨ c = quaternionClass h) ∧
    2 • quaternionClass h = 0 ∧
    ∃ e : BrauerGroup.{0, 0} ℝ ≃+ ZMod 2, e (quaternionClass h) = 1

/-- The classification uses the group law induced by tensor products on the Brauer quotient. -/
def RealClassification : Prop :=
  ∃ (h : QuaternionIsCentralDivision) (g : AddCommGroup (BrauerGroup.{0, 0} ℝ)),
    GroupLaws.{0, 0} ℝ g ∧ RealClasses h g

end Specs.RM03.Brauer
