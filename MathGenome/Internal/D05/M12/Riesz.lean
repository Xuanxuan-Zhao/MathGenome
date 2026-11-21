import MathGenome.Internal.Specs.D05.M12.Riesz
import MathGenome.Internal.D05.M07.Dual
import MathGenome.Internal.D05.M12.OnBasis
import MathGenome.Internal.D05.M12.FourierParseval

/-! K05.12.riesz: algebraic finite-dimensional Riesz representation.
The proof uses a finite orthonormal basis and the finite Fourier expansion;
there is no appeal to representation of infinite-dimensional algebraic duals.
-/

noncomputable section

namespace D05.M12.Riesz

/-- The canonical map, defined on any real or complex inner-product space.
Its codomain contains all algebraic linear functionals. -/
def rieszMap (F V : Type*) [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V] :
    V →ₗ⋆[F] Module.Dual F V := innerₛₗ F

theorem map_apply : Specs.D05.M12.Riesz.map_apply := by
  intro F V _ _ _ w v
  rfl

theorem representation_in_basis : Specs.D05.M12.Riesz.representation_in_basis := by
  intro F V I _ _ _ _ b hb φ v
  calc
    φ v = φ (∑ j, D05.firstInner (F := F) v (b j) • b j) :=
      congrArg φ (FourierParseval.fourier_expansion b hb v)
    _ = ∑ j, D05.firstInner (F := F) v (b j) * φ (b j) := by simp
    _ = D05.firstInner (F := F) v (∑ j, starRingEnd F (φ (b j)) • b j) := by
      simp [D05.firstInner, sum_inner, inner_smul_left, mul_comm]

theorem representing_vector_unique : Specs.D05.M12.Riesz.representing_vector_unique := by
  intro F V _ _ _ φ w z hw hz
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := F)).mp
  rw [inner_sub_left]
  exact sub_eq_zero.mpr ((hw (w - z)).symm.trans (hz (w - z)))

theorem exists_unique_representation : Specs.D05.M12.Riesz.exists_unique_representation := by
  intro F V _ _ _ _ φ
  obtain ⟨b, hb⟩ := OnBasis.exists_orthonormal_basis (F := F) (V := V)
  refine ⟨∑ j, starRingEnd F (φ (b j)) • b j, representation_in_basis b hb φ, ?_⟩
  intro z hz
  exact representing_vector_unique φ z _ hz (representation_in_basis b hb φ)

theorem rieszMap_bijective : Specs.D05.M12.Riesz.rieszMap_bijective := by
  intro F V _ _ _ _
  constructor
  · intro w z h
    apply representing_vector_unique (innerₛₗ F w) w z
    · intro v
      rfl
    · intro v
      exact LinearMap.congr_fun h v
  · intro φ
    obtain ⟨w, hw, _⟩ := exists_unique_representation φ
    refine ⟨w, ?_⟩
    ext v
    exact (hw v).symm

theorem conjugate_linear : Specs.D05.M12.Riesz.conjugate_linear := by
  intro F V _ _ _ a b w z
  exact (innerₛₗ F).map_add (a • w) (b • z) |>.trans
    (congrArg₂ (· + ·) ((innerₛₗ F).map_smulₛₗ a w) ((innerₛₗ F).map_smulₛₗ b z))

theorem real_linear : Specs.D05.M12.Riesz.real_linear := by
  intro V _ _ a b w z
  exact conjugate_linear a b w z

theorem zero_space : Specs.D05.M12.Riesz.zero_space := by
  intro F V _ _ _ _ φ
  have hφ : φ = 0 := by
    ext v
    have hv : v = 0 := Subsingleton.elim v 0
    simp [hv]
  refine ⟨hφ, ?_, ?_⟩
  · intro v
    simp [hφ, D05.firstInner]
  · intro w _
    exact Subsingleton.elim w 0

end D05.M12.Riesz
