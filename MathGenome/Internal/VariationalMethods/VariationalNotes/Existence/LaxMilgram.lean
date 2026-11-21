import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Existence.LaxMilgram
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.LaxMilgramEnergy

noncomputable section
open scoped ComplexConjugate
universe u v
namespace VariationalNotes.Existence

section Bridges
variable {𝕜 H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- Conjugate transpose: change the source's unknown-first convention to
MathGenome's test-first convention without assuming Hermitian symmetry. -/
def laxMilgramTestFirst (a : H →L⋆[𝕜] H →L[𝕜] 𝕜) :
    H →L⋆[𝕜] H →L[𝕜] 𝕜 :=
  let B : H →ₗ⋆[𝕜] H →ₗ[𝕜] 𝕜 := LinearMap.mk₂'ₛₗ _ _
    (fun v u => conj (a u v))
    (by intro x y z; simp)
    (by intro c x y; simp)
    (by intro x y z; simp)
    (by intro c x y; simp)
  B.mkContinuous₂ ‖a‖ (by
    intro v u
    change ‖conj (a u v)‖ ≤ ‖a‖ * ‖v‖ * ‖u‖
    simpa only [RCLike.norm_conj, mul_right_comm] using a.le_opNorm₂ u v)

@[simp] theorem laxMilgramTestFirst_apply (a : H →L⋆[𝕜] H →L[𝕜] 𝕜) (v u : H) :
    laxMilgramTestFirst a v u = conj (a u v) := rfl

/-- The linear datum becomes an antidual by conjugation. -/
def laxMilgramAntidual (ℓ : H →L[𝕜] 𝕜) : H →L⋆[𝕜] 𝕜 :=
  { toFun := fun v => conj (ℓ v)
    map_add' := by intro x y; simp
    map_smul' := by intro c x; simp
    cont := RCLike.continuous_conj.comp ℓ.continuous }

@[simp] theorem laxMilgramAntidual_apply (ℓ : H →L[𝕜] 𝕜) (v : H) :
    laxMilgramAntidual ℓ v = conj (ℓ v) := rfl

@[simp] theorem laxMilgramAntidual_norm (ℓ : H →L[𝕜] 𝕜) :
    ‖laxMilgramAntidual ℓ‖ = ‖ℓ‖ := by
  apply ContinuousLinearMap.opNorm_ext
  intro v
  exact RCLike.norm_conj (ℓ v)

/-- Equality of the equations uses injectivity of conjugation. -/
theorem laxMilgram_equation_bridge (a : H →L⋆[𝕜] H →L[𝕜] 𝕜)
    (ℓ : H →L[𝕜] 𝕜) (u : H) :
    (∀ v, laxMilgramTestFirst a v u = laxMilgramAntidual ℓ v) ↔
      ∀ v, a u v = ℓ v := by
  constructor
  · intro h v
    have hv := congrArg (fun z : 𝕜 => conj z) (h v)
    simpa only [laxMilgramTestFirst_apply, laxMilgramAntidual_apply,
      RCLike.conj_conj] using hv
  · intro h v
    exact congrArg (fun z : 𝕜 => conj z) (h v)

/-- Conjugation preserves real parts, hence the exact original energy. -/
theorem laxMilgram_energy_bridge (a : H →L⋆[𝕜] H →L[𝕜] 𝕜)
    (ℓ : H →L[𝕜] 𝕜) (v : H) :
    ExpandedFA.Hilbert.LaxMilgramEnergy.Spec.energy
      (laxMilgramTestFirst a) (laxMilgramAntidual ℓ) v = Specs.laxMilgramEnergy a ℓ v := by
  simp only [ExpandedFA.Hilbert.LaxMilgramEnergy.Spec.energy,
    Specs.laxMilgramEnergy, laxMilgramTestFirst_apply, laxMilgramAntidual_apply,
    RCLike.conj_re]
  ring

end Bridges

theorem laxMilgram : Specs.laxMilgram.{u, v} := by
  intro 𝕜 H _ _ _ _ a α hα hc ℓ
  have hco : ExpandedFA.Hilbert.Conventions.Spec.FormCoerciveValue 𝕜 H
      (laxMilgramTestFirst a) α := by
    refine ⟨hα, ?_⟩
    intro w
    simpa only [laxMilgramTestFirst_apply, RCLike.conj_re] using hc w
  obtain ⟨u, hu, hnorm, huniq, henergy⟩ :=
    ExpandedFA.Hilbert.LaxMilgramEnergy.lax_milgram 𝕜 H
      (laxMilgramTestFirst a) α hco (laxMilgramAntidual ℓ)
  have hsol : ∀ v, a u v = ℓ v := (laxMilgram_equation_bridge a ℓ u).mp hu
  have hunique : ∀ w : H, (∀ v, a w v = ℓ v) → w = u := by
    intro w hw
    exact huniq w ((laxMilgram_equation_bridge a ℓ w).mpr hw)
  refine ⟨u, hsol, ?_, hunique, ?_⟩
  · simpa only [laxMilgramAntidual_norm] using hnorm
  · intro hsym
    have hherm : ExpandedFA.Hilbert.Conventions.Spec.FormHermitianValue 𝕜 H
        (laxMilgramTestFirst a) := by
      intro x y
      simpa only [laxMilgramTestFirst_apply, RCLike.conj_conj] using (hsym x y).symm
    obtain ⟨_, hmin, hminuniq⟩ := henergy hherm
    have hmin' : ∀ v, Specs.laxMilgramEnergy a ℓ u ≤ Specs.laxMilgramEnergy a ℓ v := by
      simpa only [laxMilgram_energy_bridge] using hmin
    have hminuniq' : ∀ w : H,
        (∀ v, Specs.laxMilgramEnergy a ℓ w ≤ Specs.laxMilgramEnergy a ℓ v) → w = u := by
      simpa only [laxMilgram_energy_bridge] using hminuniq
    refine ⟨?_, ?_, ⟨u, hmin', hminuniq'⟩⟩
    · exact ExpandedFA.Hilbert.LaxMilgramEnergy.hermitian_diagonal_real a hsym
    · intro w
      constructor
      · intro hw
        rw [hunique w hw]
        exact hmin'
      · intro hw
        rw [hminuniq' w hw]
        exact hsol

end VariationalNotes.Existence
