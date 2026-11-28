import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.Coproduct
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.AntipodeMap
import Mathlib.RingTheory.HopfAlgebra.Basic

noncomputable section

namespace Specs.LieNotes.Quantum.Hopf

open Presentation

universe u v

section HopfData

variable {A : Type u} {T : Type v} [CommRing A] [CommRing T] [Algebra A T]

/-- The linear endomorphism underlying an anti-algebra map into the opposite. -/
def antipodeLinear {C : Cartan A T} (S : U C →ₐ[A] (U C)ᵐᵒᵖ) : U C →ₗ[A] U C :=
  (MulOpposite.opLinearEquiv A).symm.toLinearMap.comp S.toLinearMap

/-- Both antipode identities for the given coproduct and counit. -/
structure ConvolutionIdentities {C : Cartan A T} (d : Coproduct.Data C)
    (S : U C →ₗ[A] U C) : Prop where
  left : LinearMap.mul' A (U C) ∘ₗ S.rTensor (U C) ∘ₗ d.comul.toLinearMap =
    Algebra.linearMap A (U C) ∘ₗ d.counit.toLinearMap
  right : LinearMap.mul' A (U C) ∘ₗ S.lTensor (U C) ∘ₗ d.comul.toLinearMap =
    Algebra.linearMap A (U C) ∘ₗ d.counit.toLinearMap

/-- An antipode with the stated generator values that makes the specified bialgebra Hopf. -/
structure Data (C : Cartan A T) (d : Coproduct.Data C) where
  antipode : U C →ₐ[A] (U C)ᵐᵒᵖ
  generatorFormulas : AntipodeMap.GeneratorFormulas C antipode
  antipode_K (i : Root) :
    (antipode (Coproduct.K C i : U C)).unop = (↑((Coproduct.K C i)⁻¹) : U C)
  bijective : Function.Bijective (antipodeLinear antipode)
  convolution : ConvolutionIdentities d (antipodeLinear antipode)

/-- The Mathlib Hopf structure on the same algebra with these three maps. -/
abbrev Data.toHopfAlgebra {C : Cartan A T} {d : Coproduct.Data C} (h : Data C d) :
    HopfAlgebra A (U C) where
  toBialgebra := d.toBialgebra
  antipode := antipodeLinear h.antipode
  mul_antipode_rTensor_comul := h.convolution.left
  mul_antipode_lTensor_comul := h.convolution.right

end HopfData

/-- In the formal presentation the polynomial Cartan generators are primitive
and the antipode negates them. -/
structure TruncatedData (k : Type u) [Field k] [CharZero k] (N : ℕ)
    (d : Coproduct.TruncatedData k N) extends Data (truncated k N) d.toData where
  antipode_H (i : Root) : (antipode (Coproduct.H k N i)).unop = -Coproduct.H k N i

def GenericProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (q : kˣ) (hq : (q : k)^2 ≠ 1),
    ∃ d : Coproduct.Data (generic q hq), Nonempty (Data (generic q hq) d)

def IndeterminateProp : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k],
    ∃ d : Coproduct.Data (indeterminate k), Nonempty (Data (indeterminate k) d)

def TruncatedProp : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (N : ℕ), 1 ≤ N →
    ∃ d : Coproduct.TruncatedData k N, Nonempty (TruncatedData k N d)

/-- Reduction of the presented algebra intertwines all three Hopf maps over
the accompanying reduction of scalars. -/
def ReductionProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {M N : ℕ} (_ : 1 ≤ M) (e : M ≤ N)
    {dN : Coproduct.TruncatedData k N} {dM : Coproduct.TruncatedData k M}
    (hN : TruncatedData k N dN) (hM : TruncatedData k M dM),
    (Coproduct.tensorReduce e).comp dN.comul.toRingHom = dM.comul.toRingHom.comp (reduce e) ∧
      (Truncations.reduce e).toRingHom.comp dN.counit.toRingHom =
        dM.counit.toRingHom.comp (reduce e) ∧
      ∀ x, reduce e (antipodeLinear hN.antipode x) = antipodeLinear hM.antipode (reduce e x)

end Specs.LieNotes.Quantum.Hopf
