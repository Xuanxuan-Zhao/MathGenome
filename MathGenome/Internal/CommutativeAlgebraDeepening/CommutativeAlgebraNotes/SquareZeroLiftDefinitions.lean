import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SquareZeroLiftDefinitions
import Batteries.Tactic.OpenPrivate

/-! Public bindings for the data of Theorem 6.1. -/

noncomputable section

namespace CommutativeAlgebraNotes.SquareZeroLiftDefinitions

open CommutativeAlgebraNotes.SquareZeroLift

abbrev BaseExtension := @SquareZeroLift.BaseExtension
abbrev baseKernelModule := @SquareZeroLift.kernelModule
abbrev CoefficientMap := @SquareZeroLift.BaseExtension.CoefficientMap
abbrev Lift := @SquareZeroLift.Lift
abbrev LiftIso := @SquareZeroLift.Lift.Iso
abbrev LiftClasses := @SquareZeroLift.Lift.Classes
abbrev Presentation := @SquareZeroLift.Presentation
abbrev relationIdeal := @SquareZeroLift.Presentation.Q
abbrev coefficientIdeal := @SquareZeroLift.Presentation.IP
abbrev ReducedPolynomialRing := @SquareZeroLift.Presentation.Bar
abbrev reducedPresentationMap := @SquareZeroLift.Presentation.barMap
abbrev reducedRelationIdeal := @SquareZeroLift.Presentation.J
abbrev Conormal := @SquareZeroLift.Presentation.Conormal
abbrev ReducedConormal := @SquareZeroLift.Presentation.BarConormal
abbrev conormalImage := @SquareZeroLift.Presentation.K
abbrev toConormal := @SquareZeroLift.Presentation.toConormal
abbrev prescribedMap := @SquareZeroLift.Presentation.prescribed

end CommutativeAlgebraNotes.SquareZeroLiftDefinitions

namespace CommutativeAlgebraNotes.SquareZeroLift.Presentation

open private coefficients sum_idealMonomial from MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SquareZeroLiftDefinitions

universe u v w t n

variable {A' : Type u} {A : Type v} {B : Type w} {σ : Type t} {N : Type n}
  [CommRing A'] [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup N] [Module B N] {e : BaseExtension A' A}

theorem prescribed_unique (p : Presentation e B σ) (c : e.CoefficientMap (B := B) N) :
    p.PrescribedUnique c := by
  let : Module p.extension.Ring N := p.targetModule N
  intro f h
  apply LinearMap.ext
  intro x
  classical
  calc
    f x = f (∑ i ∈ x.val.support, p.idealMonomial i (coefficients p x i)) := by
      rw [sum_idealMonomial]
    _ = (p.prescribed c) (∑ i ∈ x.val.support, p.idealMonomial i (coefficients p x i)) := by
      rw [map_sum f, map_sum (p.prescribed c)]
      apply Finset.sum_congr rfl
      intro i _
      rw [p.idealMonomial_eq_smul_constant, map_smul, map_smul, h, p.prescribed_C]
    _ = (p.prescribed c) x := by rw [sum_idealMonomial]

end CommutativeAlgebraNotes.SquareZeroLift.Presentation
