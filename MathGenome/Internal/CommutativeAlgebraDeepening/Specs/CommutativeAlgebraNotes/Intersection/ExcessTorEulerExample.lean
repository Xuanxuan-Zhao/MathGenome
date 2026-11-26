import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.DimensionConventions
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Basic

noncomputable section

open scoped TensorProduct

namespace CommutativeAlgebraNotes.Intersection.ExcessTorEulerExample.Specs

universe u

abbrev Series (k : Type u) := MvPowerSeries (Fin 3) k

abbrev x (k : Type u) [Field k] : Series k := MvPowerSeries.X 2
abbrev y (k : Type u) [Field k] : Series k := MvPowerSeries.X 1
abbrev z (k : Type u) [Field k] : Series k := MvPowerSeries.X 0

abbrev xy (k : Type u) [Field k] : Ideal (Series k) := Ideal.span {x k, y k}
abbrev yz (k : Type u) [Field k] : Ideal (Series k) := Ideal.span {y k, z k}

abbrev firstModule (k : Type u) [Field k] : ModuleCat (Series k) :=
  ModuleCat.of _ (Series k ⧸ xy k)

abbrev secondModule (k : Type u) [Field k] : ModuleCat (Series k) :=
  ModuleCat.of _ (Series k ⧸ yz k)

open IsolatedTorSupport.Specs (Tor)
open IsolatedIntersectionEuler.Specs (intersectionEuler)
open P103.Specs.Ch06.DimensionConventions (moduleDimensionValue)

def quotientPowerSeries : Prop :=
  ∀ (k : Type u) [Field k],
    ∃ e : (Series k ⧸ yz k) ≃ₐ[k] PowerSeries k,
      e (Ideal.Quotient.mk _ (x k)) = PowerSeries.X ∧
      e (Ideal.Quotient.mk _ (y k)) = 0 ∧ e (Ideal.Quotient.mk _ (z k)) = 0

def excessTor : Prop :=
  ∀ (k : Type u) [Field k],
    letI : Algebra (Series k) k := MvPowerSeries.constantCoeff.toAlgebra
    let M := firstModule k
    let N := secondModule k
    Nonempty (Tor M N 0 ≃ₗ[Series k] k) ∧
      Nonempty (Tor M N 1 ≃ₗ[Series k] k) ∧
      ∀ i : ℕ, 1 < i → Subsingleton (Tor M N i)

def excessIntersection : Prop :=
  ∀ (k : Type u) [Field k],
    let R := Series k
    let M := firstModule k
    let N := secondModule k
    Module.length R (M ⊗[R] N) = 1 ∧
      Module.support R (M ⊗[R] N) = {IsLocalRing.closedPoint R} ∧
      Module.support R M ∩ Module.support R N = {IsLocalRing.closedPoint R} ∧
      moduleDimensionValue R M = 1 ∧ moduleDimensionValue R N = 1 ∧
      ringKrullDim R = 3 ∧
      moduleDimensionValue R M + moduleDimensionValue R N < ringKrullDim R ∧
      ∃ h : IsRegularLocalRing R, letI := h
        intersectionEuler M N = 0

end CommutativeAlgebraNotes.Intersection.ExcessTorEulerExample.Specs
