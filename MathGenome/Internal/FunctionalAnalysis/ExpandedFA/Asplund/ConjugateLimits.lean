import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Asplund.ConjugateLimits
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Asplund.OrderLimit
import Mathlib.Topology.Order.Monotone
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ExpandedFA.Asplund.ConjugateLimits

open Iteration OrderLimit Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem conjugate_eq (q : E → ℝ) (f : E →L[ℝ] ℝ) :
    conjugate E q f = ⨆ x, ((f x - q x : ℝ) : EReal) :=
  conjugate_formula E q f

/-- Conjugation reverses pointwise order, directly from its supremum. -/
theorem conjugate_antitone (q r : E → ℝ) (h : ∀ x, q x ≤ r x)
    (f : E →L[ℝ] ℝ) : conjugate E r f ≤ conjugate E q f := by
  rw [conjugate_eq, conjugate_eq]
  exact iSup_mono fun x => EReal.coe_le_coe (sub_le_sub_left (h x) _)

theorem conjugate_nonneg (q : E → ℝ) (hq : q 0 = 0) (f : E →L[ℝ] ℝ) :
    0 ≤ conjugate E q f := by
  rw [conjugate_eq]
  simpa [hq] using (le_iSup (fun x => ((f x - q x : ℝ) : EReal)) (0 : E))

theorem conjugate_order : Spec.ConjugateOrder := by
  intro E _ _ φ₀ ψ₀ h f
  refine ⟨?_, ?_⟩
  · intro n
    exact ⟨conjugate_nonneg _ (iterates_properties E φ₀ ψ₀ h n).2.2.2.2.1 f,
      conjugate_antitone _ _ (fun x => (theta_bounds φ₀ ψ₀ h n x).2) f,
      conjugate_antitone _ _ (fun x => (theta_bounds φ₀ ψ₀ h n x).1) f⟩
  · intro m n hmn
    exact conjugate_antitone _ _ (fun x => (monotone_sequences E φ₀ ψ₀ h x).2 hmn) f

theorem phi_conjugate_limit : Spec.PhiConjugateLimit := by
  intro E _ _ φ₀ ψ₀ h f
  have hm : Monotone (fun n => conjugate E (phi E φ₀ ψ₀ n) f) := by
    intro m n hmn
    exact conjugate_antitone _ _ (fun x => (monotone_sequences E φ₀ ψ₀ h x).1 hmn) f
  have heq : (⨆ n, conjugate E (phi E φ₀ ψ₀ n) f) =
      conjugate E (theta E φ₀ ψ₀) f := by
    apply le_antisymm
    · exact iSup_le fun n => (conjugate_order E φ₀ ψ₀ h f).1 n |>.2.1
    · rw [conjugate_eq]
      apply iSup_le
      intro x
      have ht : Tendsto (fun n => ((f x - phi E φ₀ ψ₀ n x : ℝ) : EReal))
          atTop (𝓝 ((f x - theta E φ₀ ψ₀ x : ℝ) : EReal)) :=
        continuous_coe_real_ereal.continuousAt.tendsto.comp
          (tendsto_const_nhds.sub (phi_tendsto φ₀ ψ₀ h x))
      apply le_of_tendsto ht
      exact Filter.Eventually.of_forall fun n =>
        (by
          rw [conjugate_eq]
          exact le_iSup (fun y : E => ((f y - phi E φ₀ ψ₀ n y : ℝ) : EReal)) x :
          ((f x - phi E φ₀ ψ₀ n x : ℝ) : EReal) ≤ conjugate E (phi E φ₀ ψ₀ n) f).trans
          (le_iSup (fun k => conjugate E (phi E φ₀ ψ₀ k) f) n)
  refine ⟨hm, heq, ?_⟩
  change Tendsto (fun n => conjugate E (phi E φ₀ ψ₀ n) f) atTop
    (𝓝 (conjugate E (theta E φ₀ ψ₀) f))
  rw [← heq]
  exact tendsto_atTop_iSup hm

/-- Adding a finite constant commutes with an arbitrary extended supremum. -/
theorem coe_add_iSup {ι : Type*} (a : ℝ) (b : ι → EReal) :
    (a : EReal) + (⨆ i, b i) = ⨆ i, ((a : EReal) + b i) := by
  apply Monotone.map_iSup_of_continuousAt
  · exact (EReal.continuousAt_add (Or.inl (EReal.coe_ne_top a))
      (Or.inl (EReal.coe_ne_bot a))).comp
        (continuousAt_const.prodMk continuousAt_id)
  · exact fun _ _ h => add_le_add le_rfl h
  · simp

/-- Two independent suprema of finite summands can be separated. -/
theorem iSup_real_add {ι κ : Type*} [Nonempty ι] [Nonempty κ]
    (a : ι → ℝ) (b : κ → ℝ) :
    (⨆ i, (a i : EReal)) + (⨆ j, (b j : EReal)) =
      ⨆ i, ⨆ j, ((a i + b j : ℝ) : EReal) := by
  have ha : (⨆ i, (a i : EReal)) ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot (a (Classical.arbitrary ι)))
      (le_iSup (fun i => (a i : EReal)) (Classical.arbitrary ι))
  have hb : (⨆ j, (b j : EReal)) ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot (b (Classical.arbitrary κ)))
      (le_iSup (fun j => (b j : EReal)) (Classical.arbitrary κ))
  have heq : (⨆ i, (a i : EReal)) + (⨆ j, (b j : EReal)) =
      ⨆ i, ((a i : EReal) + (⨆ j, (b j : EReal))) := by
    apply Monotone.map_iSup_of_continuousAt
      (f := fun t : EReal => t + (⨆ j, (b j : EReal)))
      (g := fun i => (a i : EReal))
    · exact (EReal.continuousAt_add (Or.inr hb) (Or.inl ha)).comp
        (continuousAt_id.prodMk continuousAt_const)
    · exact fun _ _ h => add_le_add h le_rfl
    · simp
  rw [heq]
  simp_rw [coe_add_iSup, ← EReal.coe_add]

/-- Positive finite scaling commutes with extended suprema, including infinity. -/
theorem half_iSup {ι : Type*} (a : ι → EReal) :
    ((1 / 2 : ℝ) : EReal) * (⨆ i, a i) =
      ⨆ i, ((1 / 2 : ℝ) : EReal) * a i := by
  apply Monotone.map_iSup_of_continuousAt
  · exact (EReal.continuousAt_mul
      (Or.inl (EReal.coe_ne_zero.mpr (by norm_num)))
      (Or.inl (EReal.coe_ne_zero.mpr (by norm_num)))
      (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))).comp
        (continuousAt_const.prodMk continuousAt_id)
  · exact fun _ _ h => mul_le_mul_of_nonneg_left h (by norm_num)
  · exact EReal.coe_mul_bot_of_pos (by norm_num)

/-- The conditional real infimum is genuine here; the decreasing continuous
map to EReal therefore sends it to a supremum. -/
theorem subtract_infimalMean (φ ψ : E → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    (hψ : ∀ x, 0 ≤ ψ x) (f : E →L[ℝ] ℝ) (x : E) :
    ((f x - infimalMean E φ ψ x : ℝ) : EReal) =
      ⨆ y, ((f x - (φ (x + y) + ψ (x - y)) / 2 : ℝ) : EReal) := by
  have hc : Continuous (fun r : ℝ => ((f x - r / 2 : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp (continuous_const.sub (continuous_id.div_const 2))
  exact Antitone.map_ciInf_of_continuousAt hc.continuousAt
    (fun _ _ h => EReal.coe_le_coe (by linarith)) (splitting_bddBelow φ ψ hφ hψ x)

/-- Conjugation of the infimal mean uses only nonnegativity of the functions. -/
theorem conjugate_infimalMean (φ ψ : E → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    (hψ : ∀ x, 0 ≤ ψ x) (f : E →L[ℝ] ℝ) :
    conjugate E (infimalMean E φ ψ) f =
      ((1 / 2 : ℝ) : EReal) * (conjugate E φ f + conjugate E ψ f) := by
  rw [conjugate_eq, conjugate_eq φ, conjugate_eq ψ, iSup_real_add, half_iSup]
  simp_rw [half_iSup, ← EReal.coe_mul]
  simp_rw [subtract_infimalMean φ ψ hφ hψ f]
  apply le_antisymm
  · apply iSup_le; intro x
    apply iSup_le; intro y
    have hf : f (x + y) + f (x - y) = 2 * f x := by
      rw [map_add, map_sub]; ring
    have heq : f x - (φ (x + y) + ψ (x - y)) / 2 =
        (1 / 2 : ℝ) * ((f (x + y) - φ (x + y)) + (f (x - y) - ψ (x - y))) := by
      linarith
    rw [heq]
    exact (le_iSup_of_le (x + y) (le_iSup_of_le (x - y) le_rfl))
  · apply iSup_le; intro u
    apply iSup_le; intro v
    let x : E := (1 / 2 : ℝ) • (u + v)
    let y : E := (1 / 2 : ℝ) • (u - v)
    have hp : x + y = u := by dsimp [x, y]; module
    have hm : x - y = v := by dsimp [x, y]; module
    have hf : f x = (f u + f v) / 2 := by
      dsimp [x]; rw [map_smul, map_add]; simp only [smul_eq_mul]; ring
    have heq : (1 / 2 : ℝ) * ((f u - φ u) + (f v - ψ v)) =
        f x - (φ (x + y) + ψ (x - y)) / 2 := by rw [hp, hm, hf]; ring
    rw [heq]
    exact le_iSup_of_le x (le_iSup_of_le y le_rfl)

theorem psi_conjugate_recurrence : Spec.PsiConjugateRecurrence := by
  intro E _ _ φ₀ ψ₀ h n f
  have hn := iterates_properties E φ₀ ψ₀ h n
  exact conjugate_infimalMean _ _
    (fun x => (hn.2.2.1 x).trans (hn.2.2.2.1 x)) hn.2.2.1 f

/-- At a finite initial conjugate value, monotone convergence and the arithmetic
recurrence force the decreasing limit to equal the increasing one. -/
theorem psi_conjugate_limit : Spec.PsiConjugateLimit := by
  intro E _ _ φ₀ ψ₀ h f hf
  let A : ℕ → EReal := fun n => conjugate E (phi E φ₀ ψ₀ n) f
  let B : ℕ → EReal := fun n => conjugate E (psi E φ₀ ψ₀ n) f
  let T : EReal := conjugate E (theta E φ₀ ψ₀) f
  let L : EReal := ⨅ n, B n
  have ho := conjugate_order E φ₀ ψ₀ h f
  have hm : Antitone B := ho.2
  have ht : Tendsto A atTop (𝓝 T) := (phi_conjugate_limit E φ₀ ψ₀ h f).2.2
  have hl : Tendsto B atTop (𝓝 L) := tendsto_atTop_iInf hm
  have hT₀ : 0 ≤ T := (ho.1 0).1.trans (ho.1 0).2.1
  have hB₀ : ∀ n, 0 ≤ B n := fun n => hT₀.trans (ho.1 n).2.2
  have hL₀ : 0 ≤ L := le_iInf hB₀
  have hTtop : T ≠ ⊤ := ne_top_of_le_ne_top hf.ne (ho.1 0).2.2
  have hLtop : L ≠ ⊤ := ne_top_of_le_ne_top hf.ne (iInf_le B 0)
  have hTbot : T ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) hT₀
  have hLbot : L ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) hL₀
  have hadd : Tendsto (fun n => A n + B n) atTop (𝓝 (T + L)) :=
    (EReal.continuousAt_add (Or.inl hTtop) (Or.inl hTbot)).tendsto.comp
      (ht.prodMk_nhds hl)
  have hmean : Tendsto (fun n => ((1 / 2 : ℝ) : EReal) * (A n + B n))
      atTop (𝓝 (((1 / 2 : ℝ) : EReal) * (T + L))) :=
    EReal.Tendsto.const_mul hadd (Or.inl (EReal.coe_ne_bot _))
      (Or.inl (EReal.coe_ne_top _))
  have hshift : Tendsto (fun n => B (n + 1)) atTop (𝓝 L) :=
    (tendsto_add_atTop_iff_nat 1).2 hl
  have hfix : L = ((1 / 2 : ℝ) : EReal) * (T + L) := by
    apply tendsto_nhds_unique_of_eventuallyEq hshift hmean
    exact Eventually.of_forall fun n => psi_conjugate_recurrence E φ₀ ψ₀ h n f
  have heq : L = T := by
    have hLc := EReal.coe_toReal hLtop hLbot
    have hTc := EReal.coe_toReal hTtop hTbot
    rw [← hLc, ← hTc, ← EReal.coe_add, ← EReal.coe_mul] at hfix
    have hr : L.toReal = (1 / 2 : ℝ) * (T.toReal + L.toReal) :=
      EReal.coe_injective hfix
    calc
      L = (L.toReal : EReal) := hLc.symm
      _ = (T.toReal : EReal) := congrArg (fun r : ℝ => (r : EReal)) (by linarith)
      _ = T := hTc
  refine ⟨hm, heq, ?_⟩
  change Tendsto B atTop (𝓝 T)
  rw [← heq]
  exact hl

theorem psi_conjugate_limit_fullDomain : Spec.PsiConjugateLimitFullDomain := by
  intro E _ _ φ₀ ψ₀ h hf f
  exact (psi_conjugate_limit E φ₀ ψ₀ h f (hf f)).2.2

end ExpandedFA.Asplund.ConjugateLimits
