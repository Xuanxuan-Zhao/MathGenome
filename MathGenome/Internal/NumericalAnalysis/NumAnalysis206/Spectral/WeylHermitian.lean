import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Spectral.WeylHermitian
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Spectral.CourantFischer
import Mathlib.Tactic.Linarith

noncomputable section
namespace NumAnalysis206.WeylHermitian
open MatrixData

variable {K : Type*} [RCLike K] {n : ℕ}

lemma rayleigh_add (A E : Mat K n n) (x : Vec K n) :
    rayleigh (A + E) x = rayleigh A x + rayleigh E x := by
  simp [NumAnalysis206.MatrixDefinitions.rayleigh, map_add, inner_add_right]

/-- Cauchy--Schwarz bounds a quadratic form on the Euclidean unit sphere. -/
lemma abs_rayleigh_le_operatorNorm (E : Mat K n n) (x : Vec K n)
    (hx : ‖x‖ = 1) : |rayleigh E x| ≤ operatorNorm E := by
  calc
    |rayleigh E x| ≤ ‖inner K x (E.toEuclideanLin x)‖ :=
      RCLike.abs_re_le_norm _
    _ ≤ ‖x‖ * ‖E.toEuclideanLin x‖ := norm_inner_le_norm _ _
    _ ≤ operatorNorm E := by simpa [hx] using operatorNorm_apply_le E x

/-- A uniform upper bound on unit Rayleigh values passes to every ordered
eigenvalue by Courant--Fischer. -/
lemma eigenvalue_le_add_of_rayleigh_le (A B : Mat K n n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (i : Fin n) (c : ℝ)
    (h : ∀ x : Vec K n, ‖x‖ = 1 → rayleigh B x ≤ rayleigh A x + c) :
    eigenvalue B hB i ≤ eigenvalue A hA i + c := by
  obtain ⟨S, hS, hmax⟩ := CourantFischer.lower_span_extremizer A hA i
  obtain ⟨x, hxS, hx1, hxB⟩ := CourantFischer.exists_rayleigh_ge B hB i S hS
  have hxA : rayleigh A x ≤ eigenvalue A hA i :=
    hmax.2 ⟨x, hxS, hx1, rfl⟩
  have hx := h x hx1
  linarith

/-- Weyl's Hermitian perturbation bound, W37. -/
theorem weyl_hermitian : Specs.NumAnalysis206.WeylHermitian.weyl_hermitian := by
  intro K _ n A E hA hE i
  have hdiff (x : Vec K n) (hx : ‖x‖ = 1) :
      |rayleigh (A + E) x - rayleigh A x| ≤ operatorNorm E := by
    rw [rayleigh_add, add_sub_cancel_left]
    exact abs_rayleigh_le_operatorNorm E x hx
  have hu := eigenvalue_le_add_of_rayleigh_le A (A + E) hA (hA.add hE) i
    (operatorNorm E) (by
      intro x hx
      have hb := (abs_le.mp (hdiff x hx)).2
      linarith)
  have hl := eigenvalue_le_add_of_rayleigh_le (A + E) A (hA.add hE) hA i
    (operatorNorm E) (by
      intro x hx
      have hb := (abs_le.mp (hdiff x hx)).1
      linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end NumAnalysis206.WeylHermitian
