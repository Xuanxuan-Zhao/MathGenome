import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.QuotSMulTop

noncomputable section

open scoped TensorProduct

namespace CommutativeAlgebraNotes.Intersection.PlaneTangencyEuler.Specs

universe u

abbrev Plane (k : Type u) := MvPowerSeries (Fin 2) k

abbrev x (k : Type u) [Field k] : Plane k := MvPowerSeries.X 1
abbrev y (k : Type u) [Field k] : Plane k := MvPowerSeries.X 0

abbrev Branch {k : Type u} [Field k] (f : Plane k) :=
  Plane k ⧸ Ideal.span {f}

abbrev branchModule {k : Type u} [Field k] (f : Plane k) : ModuleCat.{u} (Plane k) :=
  ModuleCat.of _ (Branch f)

open IsolatedIntersectionEuler.Specs (intersectionEuler)

def tangency : Prop :=
  ∀ (k : Type u) [Field k] (b : ℕ), 1 ≤ b →
    let R := Plane k
    let f := y k - x k ^ b
    let N := branchModule f
    (∃ e : Branch f ≃ₐ[k] PowerSeries k,
      e (Ideal.Quotient.mk _ (x k)) = PowerSeries.X ∧
      e (Ideal.Quotient.mk _ (y k)) = (PowerSeries.X : PowerSeries k) ^ b) ∧
    Function.Injective (fun n : N => y k • n) ∧
    Module.length R (QuotSMulTop (y k) N) = b ∧
    IsFiniteLength R (branchModule (y k) ⊗[R] N) ∧
    ∃ h : IsRegularLocalRing R, letI := h
      intersectionEuler (branchModule (y k)) N = (b : ℤ)

def axes : Prop :=
  ∀ (k : Type u) [Field k],
    let R := Plane k
    let N := branchModule (x k)
    (∃ e : Branch (x k) ≃ₐ[k] PowerSeries k,
      e (Ideal.Quotient.mk _ (x k)) = 0 ∧
      e (Ideal.Quotient.mk _ (y k)) = PowerSeries.X) ∧
    Function.Injective (fun n : N => y k • n) ∧
    (letI : Algebra R k := (MvPowerSeries.constantCoeff (σ := Fin 2) (R := k)).toAlgebra
     Nonempty (QuotSMulTop (y k) N ≃ₗ[R] k)) ∧
    IsFiniteLength R (branchModule (y k) ⊗[R] N) ∧
    ∃ h : IsRegularLocalRing R, letI := h
      intersectionEuler (branchModule (y k)) N = 1

end CommutativeAlgebraNotes.Intersection.PlaneTangencyEuler.Specs
