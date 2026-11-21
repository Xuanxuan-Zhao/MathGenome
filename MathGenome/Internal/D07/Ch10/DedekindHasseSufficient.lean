import MathGenome.Internal.Specs.D07.Ch10.DedekindHasseSufficient
import Mathlib.Data.Nat.Find

/-! The sufficient Dedekind–Hasse criterion, paper.tex:2079–2090. -/

universe u

namespace D07.Ch10.DedekindHasseSufficient

open Specs.D07.Ch10.DedekindHasseSufficient

/-- Choose a nonzero element of least norm in a nonzero ideal. Any failure
of divisibility would produce a smaller nonzero element in the same ideal. -/
theorem every_ideal_principal : EveryIdealPrincipal.{u} := by
  classical
  intro R _ _ N hNzero _hNpositive hHasse I
  by_cases hI : I = ⊥
  · subst I
    exact ⟨0, (Ideal.span_singleton_eq_bot.mpr rfl).symm⟩
  obtain ⟨x, hx, hxzero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  let P : ℕ → Prop := fun n => ∃ b : R, b ∈ I ∧ b ≠ 0 ∧ N b = n
  have hex : ∃ n, P n := ⟨N x, x, hx, hxzero, rfl⟩
  obtain ⟨b, hb, hbzero, hNb⟩ := Nat.find_spec hex
  refine ⟨b, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem I).mpr hb)⟩
  intro a ha
  rw [Ideal.mem_span_singleton]
  by_contra hdiv
  have hazero : a ≠ 0 := by
    intro haeq
    exact hdiv (haeq ▸ dvd_zero b)
  obtain ⟨s, t, hpos, hlt⟩ := hHasse a b hazero hbzero hdiv
  have hmem : s * a - t * b ∈ I :=
    I.sub_mem (I.mul_mem_left s ha) (I.mul_mem_left t hb)
  have hne : s * a - t * b ≠ 0 := by
    intro heq
    rw [heq, hNzero] at hpos
    exact (Nat.lt_irrefl 0) hpos
  have hmin : Nat.find hex ≤ N (s * a - t * b) :=
    Nat.find_min' hex ⟨s * a - t * b, hmem, hne, rfl⟩
  exact (Nat.not_lt_of_ge (hNb ▸ hmin)) hlt

/-- In the shared terminology, a domain satisfying the criterion is a PID. -/
theorem dedekind_hasse_pid : DedekindHassePID.{u} := by
  intro R _ _ N hNzero hNpositive hHasse
  exact ⟨inferInstance, every_ideal_principal R N hNzero hNpositive hHasse⟩

end D07.Ch10.DedekindHasseSufficient
