import MathGenome.Internal.Specs.D05.M12.CauchySchwarz
import MathGenome.Internal.D05.M12.Norm
import MathGenome.Internal.D05.M02.Independence
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! K05.12.cauchy_schwarz: inequality and the exact indexed-pair equality case. -/

noncomputable section

namespace D05.M12.CauchySchwarz

open D05

/-- The two-entry independence test keeps the case `v = 0` explicit. -/
theorem pair_dependent_iff {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (u v : V) :
    ¬ LinearIndependent F ![u, v] ↔ v = 0 ∨ ∃ a : F, u = a • v := by
  simp only [linearIndependent_fin2, Matrix.cons_val_one, Matrix.cons_val_zero,
    not_and_or, not_not, not_forall, ne_eq]
  simp only [eq_comm]

theorem firstInner_cauchy_schwarz :
    Specs.D05.M12.CauchySchwarz.firstInner_cauchy_schwarz := by
  intro F V _ _ _ u v
  simpa only [firstInner, mul_comm] using (norm_inner_le_norm (𝕜 := F) v u)

theorem firstInner_equality_iff_dependent :
    Specs.D05.M12.CauchySchwarz.firstInner_equality_iff_dependent := by
  intro F V _ _ _ u v
  rw [pair_dependent_iff]
  have he : ‖inner F v u‖ = ‖v‖ * ‖u‖ ↔ v = 0 ∨ ∃ a : F, u = a • v :=
    (norm_inner_eq_norm_tfae F v u).out 1 3
  simpa only [firstInner, mul_comm] using he

/-- Build the norm and inner-product structure from the proved algebraic bridge.
The new norm is definitionally `sqrt (re (h x x))`, on the given module. -/
theorem cauchy_schwarz : Specs.D05.M12.CauchySchwarz.cauchy_schwarz := by
  intro F V _ _ _ h hh u v
  obtain ⟨c, hc⟩ := InnerProduct.axioms_iff_core h |>.mp hh
  let : InnerProductSpace.Core F V := c
  let : NormedAddCommGroup V := c.toNormedAddCommGroup
  let : InnerProductSpace F V := InnerProductSpace.ofCore c.toCore
  have hn (x : V) : ‖x‖ = _root_.D05.inducedNorm h x := by
    change Real.sqrt (RCLike.re (c.inner x x)) = Real.sqrt (RCLike.re (h x x))
    rw [hc]
  have hi (x y : V) : firstInner (F := F) x y = h x y := hc y x
  simpa only [hi, hn] using firstInner_cauchy_schwarz (F := F) u v

theorem equality_iff_dependent : Specs.D05.M12.CauchySchwarz.equality_iff_dependent := by
  intro F V _ _ _ h hh u v
  obtain ⟨c, hc⟩ := InnerProduct.axioms_iff_core h |>.mp hh
  let : InnerProductSpace.Core F V := c
  let : NormedAddCommGroup V := c.toNormedAddCommGroup
  let : InnerProductSpace F V := InnerProductSpace.ofCore c.toCore
  have hn (x : V) : ‖x‖ = _root_.D05.inducedNorm h x := by
    change Real.sqrt (RCLike.re (c.inner x x)) = Real.sqrt (RCLike.re (h x x))
    rw [hc]
  have hi (x y : V) : firstInner (F := F) x y = h x y := hc y x
  simpa only [hi, hn] using firstInner_equality_iff_dependent (F := F) u v

end D05.M12.CauchySchwarz
