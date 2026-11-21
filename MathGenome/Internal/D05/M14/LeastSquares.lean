import MathGenome.Internal.Specs.D05.M14.LeastSquares
import MathGenome.Internal.D05.M12.BestApproximation
import MathGenome.Internal.D05.M14.Pseudoinverse

/-! K05.14.least_squares: the full affine set of residual minimizers,
its unique minimum-norm member, and the exact criterion for uniqueness.
The proofs use the shared, intrinsically constructed pseudoinverse. -/

namespace D05.M14.LeastSquares

theorem minimizer_iff_projection : Specs.D05.M14.LeastSquares.minimizer_iff_projection := by
  intro F V W _ _ _ _ _ _ _ T w v
  constructor
  · intro hv
    apply (D05.M12.BestApproximation.minimizer_iff T.range w (T v)).mp
    refine ⟨⟨v, rfl⟩, ?_⟩
    rintro _ ⟨u, rfl⟩
    rw [norm_sub_rev w (T v), norm_sub_rev w (T u)]
    exact hv u
  · intro hv u
    have h := ((D05.M12.BestApproximation.minimizer_iff T.range w (T v)).mpr hv).2
    rw [norm_sub_rev (T v) w, norm_sub_rev (T u) w]
    exact h (T u) ⟨u, rfl⟩

theorem minimizer_iff_kernel : Specs.D05.M14.LeastSquares.minimizer_iff_kernel := by
  intro F V W _ _ _ _ _ _ _ T w v
  rw [minimizer_iff_projection, ← D05.M14.Pseudoinverse.map_pseudoinverse T w]
  change T v = T (D05.pseudoinverse T w) ↔ T (v - D05.pseudoinverse T w) = 0
  rw [map_sub, sub_eq_zero]

theorem minimizer_iff_exists_kernel :
    Specs.D05.M14.LeastSquares.minimizer_iff_exists_kernel := by
  intro F V W _ _ _ _ _ _ _ T w v
  rw [minimizer_iff_kernel]
  constructor
  · intro hk
    exact ⟨v - D05.pseudoinverse T w, hk, (add_sub_cancel _ _).symm⟩
  · rintro ⟨k, hk, rfl⟩
    simpa only [add_sub_cancel_left] using hk

theorem pseudoinverse_minimizes : Specs.D05.M14.LeastSquares.pseudoinverse_minimizes := by
  intro F V W _ _ _ _ _ _ _ T w
  apply (minimizer_iff_kernel T w (D05.pseudoinverse T w)).mpr
  rw [sub_self]
  exact T.ker.zero_mem

theorem norm_add_kernel_sq : Specs.D05.M14.LeastSquares.norm_add_kernel_sq := by
  intro F V W _ _ _ _ _ _ _ T w k hk
  apply D05.M12.NormLaws.firstInner_pythagoras (F := F)
  exact T.ker.inner_right_of_mem_orthogonal hk
    (D05.M14.Pseudoinverse.mem_kernel_orthogonal T w)

theorem minimum_norm : Specs.D05.M14.LeastSquares.minimum_norm := by
  intro F V W _ _ _ _ _ _ _ T w v hv
  obtain ⟨k, hk, rfl⟩ := (minimizer_iff_exists_kernel T w v).mp hv
  have hs := norm_add_kernel_sq T w k hk
  have ha := norm_nonneg (D05.pseudoinverse T w)
  have hb := norm_nonneg (D05.pseudoinverse T w + k)
  nlinarith [sq_nonneg ‖k‖]

theorem norm_eq_iff : Specs.D05.M14.LeastSquares.norm_eq_iff := by
  intro F V W _ _ _ _ _ _ _ T w v hv
  obtain ⟨k, hk, rfl⟩ := (minimizer_iff_exists_kernel T w v).mp hv
  constructor
  · intro he
    have hs := norm_add_kernel_sq T w k hk
    rw [he] at hs
    have hk2 : ‖k‖ ^ 2 = 0 := by linarith
    have hk0 : k = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hk2)
    simp only [hk0, add_zero]
  · intro he
    exact congrArg norm he

theorem exists_unique_minimum_norm :
    Specs.D05.M14.LeastSquares.exists_unique_minimum_norm := by
  intro F V W _ _ _ _ _ _ _ T w
  refine ⟨D05.pseudoinverse T w,
    ⟨pseudoinverse_minimizes T w, fun u hu => minimum_norm T w u hu⟩, ?_⟩
  intro v hv
  apply (norm_eq_iff T w v hv.1).mp
  exact le_antisymm (hv.2 _ (pseudoinverse_minimizes T w)) (minimum_norm T w v hv.1)

theorem unique_iff_injective : Specs.D05.M14.LeastSquares.unique_iff_injective := by
  intro F V W _ _ _ _ _ _ _ T w
  constructor
  · rintro ⟨v, _, huniq⟩
    have hp := huniq (D05.pseudoinverse T w) (pseudoinverse_minimizes T w)
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro k hk
    have hm := (minimizer_iff_exists_kernel T w (D05.pseudoinverse T w + k)).mpr
      ⟨k, hk, rfl⟩
    have he : D05.pseudoinverse T w + k = D05.pseudoinverse T w :=
      (huniq _ hm).trans hp.symm
    have hk0 : k = 0 := add_left_cancel (he.trans (add_zero _).symm)
    simpa only [Submodule.mem_bot] using hk0
  · intro hT
    refine ⟨D05.pseudoinverse T w, pseudoinverse_minimizes T w, ?_⟩
    intro v hv
    apply hT
    exact ((minimizer_iff_projection T w v).mp hv).trans
      (D05.M14.Pseudoinverse.map_pseudoinverse T w).symm

theorem zero_map : Specs.D05.M14.LeastSquares.zero_map := by
  intro F V W _ _ _ _ _ _ _ w v
  rw [D05.M14.Pseudoinverse.pseudoinverse_zero]
  simp

end D05.M14.LeastSquares
