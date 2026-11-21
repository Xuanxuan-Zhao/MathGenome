import MathGenome.Internal.Specs.D05.M12.NormLaws
import MathGenome.Internal.D05.M12.CauchySchwarz
import Mathlib.Tactic.Linarith

/-! K05.12.norm_laws: norm and metric laws, Pythagoras, and triangle equality. -/

noncomputable section

namespace D05.M12.NormLaws

open D05

theorem inducedNorm_add_sq : Specs.D05.M12.NormLaws.inducedNorm_add_sq := by
  intro F V _ _ _ h hh u v
  have hfirst (x y z : V) : h (x + y) z = h x z + h y z := by
    simpa using hh.1 1 1 x y z
  have hsecond (x y z : V) : h x (y + z) = h x y + h x z := by
    simpa using InnerProduct.second_slot_of_axioms h hh 1 1 x y z
  rw [Norm.inducedNorm_sq h hh, Norm.inducedNorm_sq h hh, Norm.inducedNorm_sq h hh,
    hfirst, hsecond, hsecond, hh.2.1 u v]
  simp only [map_add, RCLike.conj_re]
  ring

theorem inducedNorm_add_sq_le : Specs.D05.M12.NormLaws.inducedNorm_add_sq_le := by
  intro F V _ _ _ h hh u v
  have hcs := (RCLike.re_le_norm (h u v)).trans (CauchySchwarz.cauchy_schwarz h hh u v)
  rw [inducedNorm_add_sq h hh]
  nlinarith

theorem inducedNorm_triangle : Specs.D05.M12.NormLaws.inducedNorm_triangle := by
  intro F V _ _ _ h hh u v
  have hsq := inducedNorm_add_sq_le h hh u v
  have ha := Norm.inducedNorm_nonneg h (u + v)
  have hb := add_nonneg (Norm.inducedNorm_nonneg h u) (Norm.inducedNorm_nonneg h v)
  nlinarith

theorem inducedNorm_neg : Specs.D05.M12.NormLaws.inducedNorm_neg := by
  intro F V _ _ _ h hh v
  simpa using Norm.inducedNorm_smul h hh (-1 : F) v

theorem norm_axioms : Specs.D05.M12.NormLaws.norm_axioms := by
  intro F V _ _ _ h hh
  exact ⟨Norm.inducedNorm_nonneg h, Norm.inducedNorm_eq_zero_iff h hh,
    Norm.inducedNorm_smul h hh, inducedNorm_triangle h hh⟩

theorem pythagoras : Specs.D05.M12.NormLaws.pythagoras := by
  intro F V _ _ _ h hh u v huv
  rw [inducedNorm_add_sq h hh, huv, map_zero, mul_zero, add_zero]

theorem inducedDistance_symm : Specs.D05.M12.NormLaws.inducedDistance_symm := by
  intro F V _ _ _ h hh u v
  change inducedNorm h (u - v) = inducedNorm h (v - u)
  rw [← neg_sub u v, inducedNorm_neg h hh]

theorem inducedDistance_triangle : Specs.D05.M12.NormLaws.inducedDistance_triangle := by
  intro F V _ _ _ h hh u v w
  change inducedNorm h (u - w) ≤ inducedNorm h (u - v) + inducedNorm h (v - w)
  simpa only [sub_add_sub_cancel] using inducedNorm_triangle h hh (u - v) (v - w)

theorem metric_axioms : Specs.D05.M12.NormLaws.metric_axioms := by
  intro F V _ _ _ h hh
  exact ⟨Norm.inducedDistance_nonneg h, Norm.inducedDistance_eq_zero_iff h hh,
    inducedDistance_symm h hh, inducedDistance_triangle h hh⟩

theorem firstInner_pythagoras : Specs.D05.M12.NormLaws.firstInner_pythagoras := by
  intro F V _ _ _ u v huv
  have hp := pythagoras (firstInner (F := F)) InnerProduct.firstInner_axioms u v huv
  simpa only [Norm.inducedNorm_eq_norm (F := F)] using hp

/-- Apply the real equality criterion after explicitly restricting scalars.
The norm and the vectors stay the same; real scalar action is `t ↦ (t : F)`. -/
theorem firstInner_triangle_equality : Specs.D05.M12.NormLaws.firstInner_triangle_equality := by
  intro F V _ _ _ u v
  let : InnerProductSpace ℝ V := InnerProductSpace.rclikeToReal F V
  constructor
  · intro he
    by_cases hu : u = 0
    · exact Or.inl hu
    by_cases hv : v = 0
    · exact Or.inr (Or.inl hv)
    have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hr : ‖v‖ • u = ‖u‖ • v := norm_add_eq_iff_real.mp he
    refine Or.inr (Or.inr ⟨‖v‖ / ‖u‖, div_pos hnv hnu, ?_⟩)
    calc
      v = (‖u‖⁻¹ : ℝ) • (‖u‖ • v) := by
        rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hnu), one_smul]
      _ = (‖u‖⁻¹ : ℝ) • (‖v‖ • u) := by rw [hr]
      _ = ((‖v‖ / ‖u‖ : ℝ) : F) • u := by
        rw [smul_smul]
        change (((‖u‖⁻¹ * ‖v‖ : ℝ) : F) • u) = _
        rw [div_eq_inv_mul]
  · rintro (hu | hv | ⟨t, ht, hv⟩)
    · simp [hu]
    · simp [hv]
    · apply norm_add_eq_iff_real.mpr
      have hv' : v = t • u := hv
      rw [hv', norm_smul, Real.norm_eq_abs, abs_of_pos ht, smul_smul,
        mul_comm]

theorem triangle_equality : Specs.D05.M12.NormLaws.triangle_equality := by
  intro F V _ _ _ h hh u v
  obtain ⟨c, hc⟩ := InnerProduct.axioms_iff_core h |>.mp hh
  let : InnerProductSpace.Core F V := c
  let : NormedAddCommGroup V := c.toNormedAddCommGroup
  let : InnerProductSpace F V := InnerProductSpace.ofCore c.toCore
  have hn (x : V) : ‖x‖ = inducedNorm h x := by
    change Real.sqrt (RCLike.re (c.inner x x)) = Real.sqrt (RCLike.re (h x x))
    rw [hc]
  simpa only [hn] using firstInner_triangle_equality (F := F) u v

theorem triangle_equality_of_ne_zero : Specs.D05.M12.NormLaws.triangle_equality_of_ne_zero := by
  intro F V _ _ _ h hh u v hu
  rw [triangle_equality h hh]
  constructor
  · rintro (hz | hz | ⟨t, ht, hv⟩)
    · exact (hu hz).elim
    · exact ⟨0, le_refl _, by simpa using hz⟩
    · exact ⟨t, ht.le, hv⟩
  · rintro ⟨t, ht, hv⟩
    rcases eq_or_lt_of_le ht with ht | ht
    · right; left
      simpa [← ht] using hv
    · exact Or.inr (Or.inr ⟨t, ht, hv⟩)

end D05.M12.NormLaws
