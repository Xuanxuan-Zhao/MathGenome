import MathGenome.Internal.Specs.D05.M12.Norm
import MathGenome.Internal.D05.M12.InnerProduct

/-! K05.12.norm: the real square-root definition, positivity and homogeneity. -/

noncomputable section

namespace D05.M12.Norm

open D05

abbrev inducedNorm : Specs.D05.M12.Norm.inducedNorm_type := @_root_.D05.inducedNorm

abbrev inducedDistance : Specs.D05.M12.Norm.inducedDistance_type :=
  @_root_.D05.inducedDistance

theorem diagonal_real_nonneg : Specs.D05.M12.Norm.diagonal_real_nonneg := by
  intro F V _ _ _ h hh v
  refine ⟨?_, ?_⟩
  · apply RCLike.ext
    · simp
    · simp [hh.2.2.1 v]
  · by_cases hv : v = 0
    · subst v
      rw [(InnerProduct.zero_of_axioms h hh 0).1, map_zero]
    · exact (hh.2.2.2 v hv).le

theorem inducedNorm_nonneg : Specs.D05.M12.Norm.inducedNorm_nonneg := by
  intro F V _ h v
  exact Real.sqrt_nonneg _

theorem inducedNorm_sq : Specs.D05.M12.Norm.inducedNorm_sq := by
  intro F V _ _ _ h hh v
  exact Real.sq_sqrt (diagonal_real_nonneg h hh v).2

theorem diagonal_eq_norm_sq : Specs.D05.M12.Norm.diagonal_eq_norm_sq := by
  intro F V _ _ _ h hh v
  rw [inducedNorm_sq h hh v]
  exact (diagonal_real_nonneg h hh v).1

theorem inducedNorm_eq_zero_iff : Specs.D05.M12.Norm.inducedNorm_eq_zero_iff := by
  intro F V _ _ _ h hh v
  constructor
  · intro hv
    by_contra hne
    have hpos := hh.2.2.2 v hne
    have hs := inducedNorm_sq h hh v
    rw [hv, zero_pow (by decide : 2 ≠ 0)] at hs
    exact (ne_of_gt hpos) hs.symm
  · intro hv
    subst v
    change Real.sqrt (RCLike.re (h 0 0)) = 0
    rw [(InnerProduct.zero_of_axioms h hh 0).1, map_zero, Real.sqrt_zero]

/-- The scalar diagonal identity follows from the two slot rules alone. -/
theorem diagonal_smul {F V : Type*} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F) (hh : IsFirstInnerProduct h) (a : F) (v : V) :
    h (a • v) (a • v) = ((‖a‖ ^ 2 : ℝ) : F) * h v v := by
  have hfirst : h (a • v) (a • v) = a * h v (a • v) := by
    simpa using hh.1 a 0 v 0 (a • v)
  have hsecond : h v (a • v) = starRingEnd F a * h v v := by
    simpa using InnerProduct.second_slot_of_axioms h hh a 0 v v 0
  rw [hfirst, hsecond, ← mul_assoc, RCLike.mul_conj, ← RCLike.ofReal_pow]

theorem inducedNorm_smul_sq : Specs.D05.M12.Norm.inducedNorm_smul_sq := by
  intro F V _ _ _ h hh a v
  rw [inducedNorm_sq h hh, inducedNorm_sq h hh, diagonal_smul h hh,
    RCLike.re_ofReal_mul]

theorem inducedNorm_smul : Specs.D05.M12.Norm.inducedNorm_smul := by
  intro F V _ _ _ h hh a v
  change Real.sqrt (RCLike.re (h (a • v) (a • v))) =
    ‖a‖ * Real.sqrt (RCLike.re (h v v))
  rw [diagonal_smul h hh, RCLike.re_ofReal_mul, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg a)]

theorem inducedDistance_nonneg : Specs.D05.M12.Norm.inducedDistance_nonneg := by
  intro F V _ _ h u v
  exact inducedNorm_nonneg h (u - v)

theorem inducedDistance_eq_zero_iff : Specs.D05.M12.Norm.inducedDistance_eq_zero_iff := by
  intro F V _ _ _ h hh u v
  change _root_.D05.inducedNorm h (u - v) = 0 ↔ u = v
  rw [inducedNorm_eq_zero_iff h hh, sub_eq_zero]

theorem inducedNorm_eq_norm : Specs.D05.M12.Norm.inducedNorm_eq_norm := by
  intro F V _ _ _ v
  exact (norm_eq_sqrt_re_inner (𝕜 := F) v).symm

theorem inducedDistance_eq_dist : Specs.D05.M12.Norm.inducedDistance_eq_dist := by
  intro F V _ _ _ u v
  change _root_.D05.inducedNorm (firstInner (F := F)) (u - v) = dist u v
  rw [inducedNorm_eq_norm, dist_eq_norm]

end D05.M12.Norm
