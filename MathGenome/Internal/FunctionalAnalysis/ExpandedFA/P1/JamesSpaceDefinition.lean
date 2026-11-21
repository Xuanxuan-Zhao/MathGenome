import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.JamesSpaceDefinition

/-!
The real James space with the cyclic-variation normalization of
paper.tex:4499–4511. Natural coordinate `n` is manuscript coordinate `n+1`.
-/

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal

namespace ExpandedFA.P1.James

/-- Sum of squared differences on a list of length `k+2`, including its
closing edge. Strict increase of the indices is imposed in `enorm`. -/
def cyclicEnergy (a : ℕ → ℝ) (k : ℕ) (p : Fin (k + 2) → ℕ) : ℝ :=
  (∑ j : Fin (k + 1), (a (p j.castSucc) - a (p j.succ)) ^ 2) +
    (a (p (Fin.last (k + 1))) - a (p 0)) ^ 2

/-- The manuscript's `2^(-1/2)` times the supremum of the square roots of
finite cyclic energies, with infinity allowed. This also extends the formula
to nonnull sequences; membership below still requires convergence to zero. -/
def enorm (a : ℕ → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / Real.sqrt 2) *
    ⨆ (k : ℕ) (p : Fin (k + 2) → ℕ) (_hp : StrictMono p),
      ENNReal.ofReal (Real.sqrt (cyclicEnergy a k p))

/-- A real null sequence of finite cyclic James variation. -/
def Mem (a : ℕ → ℝ) : Prop := Tendsto a atTop (𝓝 0) ∧ enorm a ≠ ⊤

/-- The actual sequence space, not an abstract isomorphic model. -/
def Space : Type := {a : ℕ → ℝ // Mem a}

/-- The real-valued James norm on the finite-variation subtype. -/
def norm (a : Space) : ℝ := (enorm a.val).toReal

instance instNorm : Norm Space := ⟨norm⟩

@[simp] theorem norm_eq (a : Space) : ‖a‖ = (enorm a.val).toReal := rfl

/-- The finite extended norm is recovered exactly from the real norm. -/
theorem norm_finite (a : Space) : ENNReal.ofReal (norm a) = enorm a.val :=
  ENNReal.ofReal_toReal a.property.2

/-- The subtype contains exactly the null sequences of finite displayed norm. -/
theorem space_characterization (a : ℕ → ℝ) :
    (∃ x : Space, x.val = a) ↔ Tendsto a atTop (𝓝 0) ∧ enorm a < ⊤ := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.property.1, lt_top_iff_ne_top.mpr x.property.2⟩
  · rintro ⟨hnull, hfinite⟩
    exact ⟨⟨a, hnull, ne_of_lt hfinite⟩, rfl⟩

@[simp] theorem cyclicEnergy_zero (k : ℕ) (p : Fin (k + 2) → ℕ) :
    cyclicEnergy (fun _ => 0) k p = 0 := by
  simp [cyclicEnergy]

@[simp] theorem enorm_zero : enorm (fun _ => 0) = 0 := by
  simp [enorm]

/-- Zero satisfies both defining conditions, without any nonzero hypothesis. -/
theorem zero_mem : Mem (fun _ => 0) := by
  exact ⟨tendsto_const_nhds, by simp⟩

end ExpandedFA.P1.James
