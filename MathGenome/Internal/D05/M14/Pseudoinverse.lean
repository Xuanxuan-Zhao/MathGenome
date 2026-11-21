import MathGenome.Internal.Specs.D05.M14.Pseudoinverse
import MathGenome.Internal.D05.M03.Isomorphism
import MathGenome.Internal.D05.M12.Projection

/-! K05.14.pseudoinverse: inverse restriction after orthogonal projection. -/

noncomputable section

namespace D05.M14.Pseudoinverse

abbrev restriction : Specs.D05.M14.Pseudoinverse.restriction_type :=
  @D05.pseudoinverseRestriction

abbrev pseudoinverse : Specs.D05.M14.Pseudoinverse.pseudoinverse_type :=
  @D05.pseudoinverse

theorem restriction_bijective : Specs.D05.M14.Pseudoinverse.restriction_bijective := by
  intro F V W _ _ _ _ _ _ _ T
  constructor
  · intro x y hxy
    apply Subtype.ext
    have ht : T ((x : V) - (y : V)) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Subtype.val hxy)
    have hz : (x : V) - (y : V) ∈ T.ker ⊓ T.ker.orthogonal :=
      ⟨ht, T.ker.orthogonal.sub_mem x.property y.property⟩
    rw [D05.M12.OrthogonalComplement.inf_orthogonal_eq_bot] at hz
    exact sub_eq_zero.mp (by simpa only [Submodule.mem_bot] using hz)
  · rintro ⟨w, v, rfl⟩
    obtain ⟨⟨k, m⟩, hv, _⟩ :=
      D05.M12.OrthogonalDecomposition.exists_unique_components T.ker v
    refine ⟨m, Subtype.ext ?_⟩
    change T (m : V) = T v
    rw [← hv, map_add, show T (k : V) = 0 from k.property, zero_add]

theorem restriction_isomorphism : Specs.D05.M14.Pseudoinverse.restriction_isomorphism := by
  intro F V W _ _ _ _ _ _ _ T
  exact (D05.M03.Isomorphism.isomorphism_iff_bijective _).mpr (restriction_bijective T)

theorem restriction_inverse : Specs.D05.M14.Pseudoinverse.restriction_inverse := by
  intro F V W _ _ _ _ _ _ _ T
  have hi := LinearMap.ker_eq_bot.mpr (restriction_bijective T).1
  refine ⟨LinearMap.leftInverse_comp_of_inj hi, ?_⟩
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := (restriction_bijective T).2 y
  exact congrArg (D05.pseudoinverseRestriction T)
    (LinearMap.leftInverse_apply_of_inj hi x)

theorem construction_formula : Specs.D05.M14.Pseudoinverse.construction_formula := by
  intro F V W _ _ _ _ _ _ _ T e he w
  have hi := LinearMap.ker_eq_bot.mpr (restriction_bijective T).1
  have hleft : (D05.pseudoinverseRestriction T).leftInverse = e.symm.toLinearMap := by
    apply LinearMap.ext
    intro y
    have hy : D05.pseudoinverseRestriction T (e.symm y) = y := by
      rw [← he]
      exact e.apply_symm_apply y
    calc
      (D05.pseudoinverseRestriction T).leftInverse y =
          (D05.pseudoinverseRestriction T).leftInverse
            (D05.pseudoinverseRestriction T (e.symm y)) :=
        congrArg (D05.pseudoinverseRestriction T).leftInverse hy.symm
      _ = e.symm y := LinearMap.leftInverse_apply_of_inj hi _
  change ((D05.pseudoinverseRestriction T).leftInverse
    (D05.pseudoinverseRangeProjection T w) : V) = _
  rw [hleft]
  rfl

theorem mem_kernel_orthogonal : Specs.D05.M14.Pseudoinverse.mem_kernel_orthogonal := by
  intro F V W _ _ _ _ _ _ _ T w
  exact ((D05.pseudoinverseRestriction T).leftInverse
    (D05.pseudoinverseRangeProjection T w)).property

theorem map_pseudoinverse : Specs.D05.M14.Pseudoinverse.map_pseudoinverse := by
  intro F V W _ _ _ _ _ _ _ T w
  have h := congrArg (fun f => f (D05.pseudoinverseRangeProjection T w))
    (restriction_inverse T).2
  exact congrArg Subtype.val h

theorem characterization : Specs.D05.M14.Pseudoinverse.characterization := by
  intro F V W _ _ _ _ _ _ _ T w v
  constructor
  · rintro rfl
    exact ⟨mem_kernel_orthogonal T w, map_pseudoinverse T w⟩
  · rintro ⟨hv, ht⟩
    let x : T.ker.orthogonal := ⟨v, hv⟩
    let y := (D05.pseudoinverseRestriction T).leftInverse
      (D05.pseudoinverseRangeProjection T w)
    have hxy : D05.pseudoinverseRestriction T x = D05.pseudoinverseRestriction T y := by
      apply Subtype.ext
      exact ht.trans (map_pseudoinverse T w).symm
    exact congrArg Subtype.val ((restriction_bijective T).1 hxy)

theorem unique_linear_map : Specs.D05.M14.Pseudoinverse.unique_linear_map := by
  intro F V W _ _ _ _ _ _ _ T
  refine ⟨D05.pseudoinverse T, ?_, ?_⟩
  · intro w
    exact ⟨mem_kernel_orthogonal T w, map_pseudoinverse T w⟩
  · intro S hS
    apply LinearMap.ext
    intro w
    exact (characterization T w (S w)).mpr (hS w)

/-- Any construction with the intrinsic characterization gives this same map;
in particular no coordinate basis or inverse choice can alter it. -/
theorem basis_independence : Specs.D05.M14.Pseudoinverse.basis_independence := by
  intro F V W _ _ _ _ _ _ _ T S hS
  apply LinearMap.ext
  intro w
  exact (characterization T w (S w)).mpr (hS w)

theorem map_add : Specs.D05.M14.Pseudoinverse.map_add := by
  intro F V W _ _ _ _ _ _ _ T x y
  exact (D05.pseudoinverse T).map_add x y

theorem map_smul : Specs.D05.M14.Pseudoinverse.map_smul := by
  intro F V W _ _ _ _ _ _ _ T a w
  exact (D05.pseudoinverse T).map_smul a w

theorem zero_restriction_spaces : Specs.D05.M14.Pseudoinverse.zero_restriction_spaces := by
  intro F V W _ _ _ _ _ _ _
  simp

theorem pseudoinverse_zero : Specs.D05.M14.Pseudoinverse.pseudoinverse_zero := by
  intro F V W _ _ _ _ _ _ _
  apply LinearMap.ext
  intro w
  have h := mem_kernel_orthogonal (0 : V →ₗ[F] W) w
  simpa using h

end D05.M14.Pseudoinverse
