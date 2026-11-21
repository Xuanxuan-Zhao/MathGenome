import MathGenome.Internal.D07.Ch01.HomomorphismDefinition
import MathGenome.Internal.Specs.D07.Ch17.Definition

/-!
Linear representations, the endomorphism formulation, and matrices in a chosen
finite basis. No finiteness is imposed on the group or on the representation
space before a finite basis is explicitly chosen. Empty basis types are allowed.
-/
namespace D07.Ch17.Definition

universe u v w t

open scoped Matrix

/-- The source definition, with composition as the group operation on GL(V). -/
abbrev LinearRepresentation (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V] :=
  G →* (V ≃ₗ[K] V)

theorem endomorphism_characterization :
    Specs.D07.Ch17.Definition.EndomorphismCharacterization.{u, v, w} := by
  intro K G V _ _ _ _ r
  constructor
  · rintro ⟨h1, hmul⟩
    refine ⟨{ toFun := r, map_one' := h1, map_mul' := hmul }, rfl, ?_⟩
    intro ρ hρ
    exact MonoidHom.ext (fun g => congrFun hρ g)
  · rintro ⟨ρ, hρ, _⟩
    rw [← hρ]
    exact ⟨ρ.map_one, ρ.map_mul⟩

theorem endomorphism_laws :
    Specs.D07.Ch17.Definition.EndomorphismLaws.{u, v, w} := by
  intro K G V _ _ _ _ ρ
  refine ⟨ρ.map_one, ρ.map_mul, ?_⟩
  intro g
  constructor
  · rw [← map_mul, mul_inv_cancel, map_one]
  · rw [← map_mul, inv_mul_cancel, map_one]

theorem automorphism_correspondence :
    Specs.D07.Ch17.Definition.AutomorphismCorrespondence.{u, v, w} := by
  intro K G V _ _ _ _
  let e : Representation K G V ≃ LinearRepresentation K G V := {
    toFun := fun ρ =>
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).toMonoidHom.comp ρ.toHomUnits
    invFun := fun σ => LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp σ
    left_inv := fun ρ => by ext; rfl
    right_inv := fun σ => by ext; rfl
  }
  refine ⟨e, ?_, ?_, ?_⟩
  · intro ρ g
    rfl
  · intro σ g
    rfl
  · intro ρ g
    rfl

theorem matrix_laws :
    Specs.D07.Ch17.Definition.MatrixLaws.{u, v, w, t} := by
  intro K G V ι _ _ _ _ _ _ b ρ
  let T := LinearMap.toMatrixAlgEquiv b
  change T (ρ 1) = 1 ∧
    (∀ g h, T (ρ (g * h)) = T (ρ g) * T (ρ h)) ∧
    (∀ g, T (ρ g) * T (ρ g⁻¹) = 1 ∧ T (ρ g⁻¹) * T (ρ g) = 1)
  refine ⟨by simp, fun g h => by simp, ?_⟩
  intro g
  constructor
  · rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
  · rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]

theorem matrix_correspondence :
    Specs.D07.Ch17.Definition.MatrixCorrespondence.{u, v, w, t} := by
  intro K G V ι _ _ _ _ _ _ b
  let T := LinearMap.toMatrixAlgEquiv b
  let e : Representation K G V ≃ (G →* Matrix.GeneralLinearGroup ι K) := {
    toFun := fun ρ => (Units.map T.toMonoidHom).comp ρ.toHomUnits
    invFun := fun A => T.symm.toMonoidHom.comp ((Units.coeHom _).comp A)
    left_inv := fun ρ => by
      apply MonoidHom.ext
      intro g
      exact T.symm_apply_apply (ρ g)
    right_inv := fun A => by
      apply MonoidHom.ext
      intro g
      apply Units.ext
      exact T.apply_symm_apply (A g : Matrix ι ι K)
  }
  refine ⟨e, ?_, ?_⟩
  · intro ρ g
    rfl
  · intro A g x
    change b.equivFun (Matrix.toLin b b (A g : Matrix ι ι K) x) = _
    exact Matrix.repr_toLin b b (A g : Matrix ι ι K) x

theorem automorphism_matrix_correspondence :
    Specs.D07.Ch17.Definition.AutomorphismMatrixCorrespondence.{u, v, w, t} := by
  intro K G V _ι _ _ _ _ _ _ b
  obtain ⟨a, ha, ha', _⟩ := automorphism_correspondence K G V
  obtain ⟨m, hm, hm'⟩ := matrix_correspondence K G V _ι b
  refine ⟨a.symm.trans m, ?_, ?_⟩
  · intro σ g
    change (m (a.symm σ) g : Matrix _ι _ι K) = _
    rw [hm, ha']
  · intro A g x
    change b.equivFun (a (m.symm A) g x) = _
    have h := congrArg (fun f : Module.End K V => f x) (ha (m.symm A) g)
    change a (m.symm A) g x = m.symm A g x at h
    rw [h]
    exact hm' A g x

end D07.Ch17.Definition
