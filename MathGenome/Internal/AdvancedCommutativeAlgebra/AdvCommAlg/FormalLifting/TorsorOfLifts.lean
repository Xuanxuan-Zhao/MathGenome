import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Universal
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.SquareZeroLifts
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.TorsorOfLifts

/-! The fiber of reduction is a torsor whenever it is inhabited (FL-03). -/
namespace AdvCommAlg.FormalLifting

open AdvCommAlg.Differentials
open Specs.AdvCommAlg.Differentials.SquareZero
open Specs.AdvCommAlg.FormalLifting (LiftCoordinates)

universe u v w
noncomputable section

section Fiber
variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
variable (N : Ideal C) (hN : N ^ 2 = ⊥) (u : B →ₐ[A] C ⧸ N)

/-- The universal property composed with the difference-of-lifts equivalence. -/
def liftEquiv (v : Lifts N u) : LiftCoordinates N hN u ≃ Lifts N u := by
  letI := idealModule N hN u
  letI := idealTower N hN u
  exact (universalEquiv A B N).toEquiv.trans
    (Classical.choose (square_zero_lift_correspondence N hN u v.1 v.2))

@[simp] theorem liftEquiv_apply (v : Lifts N u) (h : LiftCoordinates N hN u) (b : B) :
    (liftEquiv N hN u v h).1 b = v.1 b + (h (KaehlerDifferential.D A B b) : C) := by
  letI := idealModule N hN u
  letI := idealTower N hN u
  exact (Classical.choose_spec
    (square_zero_lift_correspondence N hN u v.1 v.2)).1 (universalEquiv A B N h) b

/-- Adding a differential coordinate makes sense even if the fiber is empty. -/
@[instance_reducible] def liftsAddAction : AddAction (LiftCoordinates N hN u) (Lifts N u) where
  vadd h v := liftEquiv N hN u v h
  zero_vadd v := by
    apply Subtype.ext
    apply AlgHom.ext
    intro b
    change (liftEquiv N hN u v 0).1 b = v.1 b
    simp
  add_vadd h k v := by
    apply Subtype.ext
    apply AlgHom.ext
    intro b
    change (liftEquiv N hN u v (h + k)).1 b =
      (liftEquiv N hN u (liftEquiv N hN u v k) h).1 b
    simp only [liftEquiv_apply, LinearMap.add_apply, Submodule.coe_add]
    abel

end Fiber

theorem lift_parametrization : Specs.AdvCommAlg.FormalLifting.liftParametrization := by
  intro A B C _ _ _ _ _ N hN u v
  exact ⟨liftEquiv N hN u v, liftEquiv_apply N hN u v⟩

theorem reference_change : Specs.AdvCommAlg.FormalLifting.referenceChange := by
  intro A B C _ _ _ _ _ N hN u v e he h₀ e' he' h
  have eq : e' (h - h₀) = e h := by
    apply Subtype.ext
    apply AlgHom.ext
    intro b
    rw [he', he, he]
    simp only [LinearMap.sub_apply, Submodule.coe_sub]
    abel
  exact ⟨eq, (congrArg e'.symm eq).symm.trans (e'.symm_apply_apply _)⟩

theorem lifts_action : Specs.AdvCommAlg.FormalLifting.liftsAction := by
  intro A B C _ _ _ _ _ N hN u
  refine ⟨liftsAddAction N hN u, ?_⟩
  change (∀ (h : LiftCoordinates N hN u) (v : Lifts N u) (b : B),
    (liftEquiv N hN u v h).1 b = v.1 b + (h (KaehlerDifferential.D A B b) : C)) ∧
    (∀ (h k : LiftCoordinates N hN u) (v : Lifts N u),
      liftEquiv N hN u v h = liftEquiv N hN u v k → h = k) ∧
    (∀ v w : Lifts N u, ∃! h : LiftCoordinates N hN u, liftEquiv N hN u v h = w)
  refine ⟨fun h v b => liftEquiv_apply N hN u v h b, ?_, ?_⟩
  · intro h k v eq
    exact (liftEquiv N hN u v).injective eq
  · intro v w
    exact ⟨(liftEquiv N hN u v).symm w,
      (liftEquiv N hN u v).apply_symm_apply w,
      fun h hh => (liftEquiv N hN u v).injective
        (hh.trans ((liftEquiv N hN u v).apply_symm_apply w).symm)⟩

end
end AdvCommAlg.FormalLifting
