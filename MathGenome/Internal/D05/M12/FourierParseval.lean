import MathGenome.Internal.Specs.D05.M12.FourierParseval
import MathGenome.Internal.D05.M02.Basis
import MathGenome.Internal.D05.M12.Orthonormal
import MathGenome.Internal.D05.M12.NormLaws

/-! K05.12.fourier_parseval: finite Fourier expansion, Parseval, and Bessel. -/

namespace D05.M12.FourierParseval

theorem norm_sq_finite_sum : Specs.D05.M12.FourierParseval.norm_sq_finite_sum := by
  intro F V I _ _ _ e he s a
  have h := (Orthonormal.orthonormal_iff_mathlib e).mp he
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := F), h.inner_sum a a s, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

theorem fourier_coefficient : Specs.D05.M12.FourierParseval.fourier_coefficient := by
  intro F V I _ _ _ b hb v j
  have h := (Orthonormal.orthonormal_iff_mathlib b).mp hb
  change b.repr v j = inner F (b j) v
  have hc := h.inner_right_finsupp (b.repr v) j
  rw [b.linearCombination_repr] at hc
  exact hc.symm

theorem fourier_expansion : Specs.D05.M12.FourierParseval.fourier_expansion := by
  intro F V I _ _ _ _ b hb v
  simpa only [fourier_coefficient b hb] using (b.sum_repr v).symm

theorem parseval : Specs.D05.M12.FourierParseval.parseval := by
  intro F V I _ _ _ _ b hb v
  calc
    ‖v‖ ^ 2 = ‖∑ j, D05.firstInner (F := F) v (b j) • b j‖ ^ 2 :=
      congrArg (fun x : V => ‖x‖ ^ 2) (fourier_expansion b hb v)
    _ = ∑ j, ‖D05.firstInner (F := F) v (b j)‖ ^ 2 :=
      norm_sq_finite_sum b hb Finset.univ _

theorem residual_orthogonal : Specs.D05.M12.FourierParseval.residual_orthogonal := by
  intro F V I _ _ _ e he s v k hk
  change inner F (e k) (v - _) = 0
  have h := (Orthonormal.orthonormal_iff_mathlib e).mp he
  rw [inner_sub_right, h.inner_right_sum _ hk]
  exact sub_self _

theorem residual_orthogonal_sum :
    Specs.D05.M12.FourierParseval.residual_orthogonal_sum := by
  intro F V I _ _ _ e he s v
  dsimp only
  change inner F (∑ j ∈ s, _ • e j) _ = 0
  rw [sum_inner]
  apply Finset.sum_eq_zero
  intro j hj
  rw [inner_smul_left]
  change _ * D05.firstInner (F := F) (v - _) (e j) = 0
  rw [residual_orthogonal e he s v j hj, mul_zero]

/-- Follow the source argument: the residual is perpendicular to the partial
sum, and Pythagoras separates the squared norm into the two contributions. -/
theorem bessel_identity : Specs.D05.M12.FourierParseval.bessel_identity := by
  intro F V I _ _ _ e he s v
  let p := ∑ j ∈ s, D05.firstInner (F := F) v (e j) • e j
  have hp := NormLaws.firstInner_pythagoras (F := F) (v - p) p
    (residual_orthogonal_sum e he s v)
  rw [sub_add_cancel] at hp
  change ‖v‖ ^ 2 = _ + ‖v - p‖ ^ 2
  rw [hp, norm_sq_finite_sum e he s]
  exact add_comm _ _

theorem bessel : Specs.D05.M12.FourierParseval.bessel := by
  intro F V I _ _ _ e he s v
  rw [bessel_identity e he s v]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem bessel_finite_family : Specs.D05.M12.FourierParseval.bessel_finite_family := by
  intro F V I _ _ _ _ e he v
  exact bessel e he Finset.univ v

end D05.M12.FourierParseval
