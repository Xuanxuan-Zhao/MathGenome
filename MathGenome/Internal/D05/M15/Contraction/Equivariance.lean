import MathGenome.Internal.D05.M15.Contraction
import MathGenome.Internal.Specs.D05.M15.Contraction.Equivariance

/-! Equivariance under the natural GL(V) action, using the canonical
upstream contraction rather than a coordinate-defined replacement. -/
namespace D05.M15.Contraction.Equivariance

open Specs.D05.M15.Contraction

theorem action_on_elementary : Specs.D05.M15.Contraction.Equivariance.action_on_elementary :=
  D05.M15.Contraction.action_tprod

theorem action_identity : Specs.D05.M15.Contraction.Equivariance.action_identity :=
  D05.M15.Contraction.action_identity

theorem action_composition : Specs.D05.M15.Contraction.Equivariance.action_composition :=
  D05.M15.Contraction.action_composition

theorem action_automorphism : Specs.D05.M15.Contraction.Equivariance.action_automorphism := by
  intro K V _ _ _ g p q
  obtain ⟨hl, hr⟩ := D05.M15.Contraction.action_inverse g p q
  let e : Mixed K V p q ≃ₗ[K] Mixed K V p q :=
    { mixedAction g p q with
      invFun := mixedAction g.symm p q
      left_inv := fun t => LinearMap.congr_fun hl t
      right_inv := fun t => LinearMap.congr_fun hr t }
  exact ⟨e, rfl, rfl⟩

theorem evaluation_invariant : Specs.D05.M15.Contraction.Equivariance.evaluation_invariant := by
  intro K V _ _ _ g f v
  change f (g.symm (g v)) = f v
  rw [g.symm_apply_apply]

theorem contraction_equivariant : Specs.D05.M15.Contraction.Equivariance.contraction_equivariant :=
  D05.M15.Contraction.contraction_equivariant

theorem scalar_action : Specs.D05.M15.Contraction.Equivariance.scalar_action := by
  intro K V _ _ _ g t
  have h : mixedAction g 0 0 = LinearMap.id := by
    apply D05.M15.Contraction.mixed_ext
    intro f v
    rw [D05.M15.Contraction.action_tprod]
    change elementary _ _ = elementary f v
    congr 1 <;> exact Subsingleton.elim _ _
  rw [h, LinearMap.id_apply]

theorem contracted_coordinate_transformation :
    Specs.D05.M15.Contraction.Equivariance.contracted_coordinate_transformation := by
  intro K V I _ _ _ _ b g p q r s t i j
  rw [← D05.M15.Contraction.coordinate_contraction b r s]
  exact congrArg (fun u => (mixedBasis b p q).repr u (i,j))
    (LinearMap.congr_fun (contraction_equivariant g r s) t)

end D05.M15.Contraction.Equivariance
