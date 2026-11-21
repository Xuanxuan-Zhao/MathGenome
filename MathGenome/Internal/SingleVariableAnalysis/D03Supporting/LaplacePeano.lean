import MathGenome.Internal.SingleVariableAnalysis.Specs.D03Supporting.LaplacePeano
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Filter Set
open scoped Topology

namespace D03Supporting

/-- Fermat's theorem and the two-sided Peano expansion at the minimum. -/
theorem laplacePeano : Specs.D03Supporting.LaplacePeano := by
  intro a b x₀ φ hab hax hxb hφ hmin _hunique _hd
  have hx : x₀ ∈ Ioo a b := ⟨hax, hxb⟩
  have hn : Ioo a b ∈ 𝓝 x₀ := Ioo_mem_nhds hax hxb
  have hφo : ContDiffOn ℝ 2 φ (Ioo a b) := hφ.mono Ioo_subset_Icc_self
  have hlocal : IsLocalMin φ x₀ :=
    (show IsMinOn φ (Icc a b) x₀ from hmin).isLocalMin
      (mem_of_superset hn Ioo_subset_Icc_self)
  have hfirst : deriv φ x₀ = 0 := hlocal.deriv_eq_zero
  refine ⟨hfirst, min (x₀ - a) (b - x₀), lt_min (sub_pos.mpr hax) (sub_pos.mpr hxb), ?_⟩
  let ρ : ℝ → ℝ := fun h =>
    (φ (x₀ + h) - φ x₀ - deriv (deriv φ) x₀ * h ^ 2 / 2) / h ^ 2
  refine ⟨ρ, ?_, ?_, ?_⟩
  · simp [ρ]
  · have ht := taylor_tendsto (n := 2) (convex_Ioo a b) hx hφo
    rw [nhdsWithin_eq_nhds.mpr hn] at ht
    have heval (x : ℝ) : taylorWithinEval φ 2 (Ioo a b) x₀ x =
        φ x₀ + deriv (deriv φ) x₀ * (x - x₀) ^ 2 / 2 := by
      simp [show (2 : ℕ) = 1 + 1 from rfl, taylorWithinEval_succ,
        iteratedDerivWithin_of_isOpen isOpen_Ioo hx, iteratedDeriv_succ,
        hfirst]
      ring
    simp_rw [heval] at ht
    have hc := ht.comp (show Tendsto (fun h : ℝ => x₀ + h) (𝓝 0) (𝓝 x₀) by
      simpa using tendsto_const_nhds.add (tendsto_id : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0)))
    simpa only [Function.comp_def, add_sub_cancel_left, smul_eq_mul, ρ,
      sub_add_eq_sub_sub, div_eq_mul_inv, mul_comm] using hc
  · intro h hh
    have hh' := abs_lt.mp hh
    have hm₁ := min_le_left (x₀ - a) (b - x₀)
    have hm₂ := min_le_right (x₀ - a) (b - x₀)
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    by_cases hz : h = 0
    · simp [hz]
    · dsimp [ρ]
      field_simp
      ring

end D03Supporting
