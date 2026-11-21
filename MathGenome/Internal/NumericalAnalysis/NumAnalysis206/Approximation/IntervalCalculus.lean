import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.IntervalCalculus
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.TangentCone.Real

/-! Closed-interval calculus for the convention in paper.tex:1812–1815.
`IntervalJet` retains the derivative data even when the interval is a singleton.
Only on a nondegenerate interval are these data identified with Mathlib's
chosen iterated derivatives. No extension outside the interval is required. -/
namespace NumAnalysis206.Approximation
open Set

abbrev IntervalJet := IntervalCalculusSpec.jetValue
abbrev IntervalContDiff := IntervalCalculusSpec.smoothValue

variable {a b c d t : ℝ} {r q : ℕ} {f g : ℝ → ℝ} {D E : ℕ → ℝ → ℝ}

theorem jet_eq_iterated (hab : a < b) (hD : IntervalJet a b r f D)
    (j : ℕ) (hj : j ≤ r) :
    EqOn (D j) (iteratedDerivWithin j f (Icc a b)) (Icc a b) := by
  induction j with
  | zero => simpa using hD.1
  | succ j ih =>
    have heq := ih (Nat.le_of_succ_le hj)
    intro x hx
    rw [iteratedDerivWithin_succ]
    have hd := hD.2.2 j (Nat.lt_of_succ_le hj) x hx
    have hd' := hd.congr_of_mem (fun y hy => (heq hy).symm) hx
    exact (hd'.derivWithin (uniqueDiffOn_Icc hab x hx)).symm

theorem jet_singleton_iff : IntervalJet a a r f D ↔ D 0 a = f a := by
  constructor
  · intro h
    exact h.1 (by simp)
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa using h
    · intro j hj
      simp
    · intro j hj x hx
      simp only [Icc_self] at *
      exact HasFDerivWithinAt.singleton

theorem smooth_singleton (a : ℝ) (r : ℕ) (f : ℝ → ℝ) : IntervalContDiff a a r f := by
  exact ⟨fun _ => f, jet_singleton_iff.mpr rfl⟩

theorem jet_to_contDiff (hab : a ≤ b) (hD : IntervalJet a b r f D) :
    ContDiffOn ℝ r f (Icc a b) := by
  rcases hab.eq_or_lt with heq | hlt
  · subst b
    intro x hx
    have hxa : x = a := by simpa using hx
    subst x
    simpa using (contDiffWithinAt_singleton : ContDiffWithinAt ℝ r f {a} a)
  · apply (contDiffOn_nat_iff_continuousOn_differentiableOn_deriv
      (uniqueDiffOn_Icc hlt)).mpr
    constructor
    · intro j hj
      exact (hD.2.1 j hj).congr (jet_eq_iterated hlt hD j hj).symm
    · intro j hj x hx
      have heq := jet_eq_iterated hlt hD j hj.le
      exact ((hD.2.2 j hj x hx).congr_of_mem (fun y hy => (heq hy).symm) hx).differentiableWithinAt

theorem jet_of_contDiff (hab : a < b) (hf : ContDiffOn ℝ r f (Icc a b)) :
    IntervalJet a b r f (fun j => iteratedDerivWithin j f (Icc a b)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp
  · intro j hj
    exact hf.continuousOn_iteratedDerivWithin (by exact_mod_cast hj) (uniqueDiffOn_Icc hab)
  · intro j hj x hx
    dsimp only
    rw [iteratedDerivWithin_succ]
    exact (hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast hj)
      (uniqueDiffOn_Icc hab) x hx).hasDerivWithinAt

theorem smooth_iff_contDiff (hab : a ≤ b) :
    IntervalContDiff a b r f ↔ ContDiffOn ℝ r f (Icc a b) := by
  constructor
  · rintro ⟨D, hD⟩
    exact jet_to_contDiff hab hD
  · intro hf
    rcases hab.eq_or_lt with heq | hlt
    · subst b
      exact smooth_singleton a r f
    · exact ⟨_, jet_of_contDiff hlt hf⟩

theorem jet_restrict (hac : a ≤ c) (hdb : d ≤ b) (hD : IntervalJet a b r f D) :
    IntervalJet c d r f D := by
  have hsub : Icc c d ⊆ Icc a b := Icc_subset_Icc hac hdb
  exact ⟨hD.1.mono hsub, fun j hj => (hD.2.1 j hj).mono hsub,
    fun j hj x hx => (hD.2.2 j hj x (hsub hx)).mono hsub⟩

theorem smooth_restrict (hac : a ≤ c) (hdb : d ≤ b) (hf : IntervalContDiff a b r f) :
    IntervalContDiff c d r f := by
  obtain ⟨D, hD⟩ := hf
  exact ⟨D, jet_restrict hac hdb hD⟩

theorem jet_congr (hfg : EqOn f g (Icc a b)) :
    IntervalJet a b r f D ↔ IntervalJet a b r g D := by
  constructor
  · intro h
    exact ⟨h.1.trans hfg, h.2⟩
  · intro h
    exact ⟨h.1.trans hfg.symm, h.2⟩

theorem smooth_congr (hfg : EqOn f g (Icc a b)) :
    IntervalContDiff a b r f ↔ IntervalContDiff a b r g := by
  exact exists_congr fun D => jet_congr hfg

/-- Changing arbitrary values outside the interval changes none of the within derivatives. -/
theorem iterated_congr (hfg : EqOn f g (Icc a b)) (j : ℕ) :
    EqOn (iteratedDerivWithin j f (Icc a b))
      (iteratedDerivWithin j g (Icc a b)) (Icc a b) :=
  iteratedDerivWithin_congr hfg

theorem jet_unique (hab : a < b) (hfg : EqOn f g (Icc a b))
    (hD : IntervalJet a b r f D) (hE : IntervalJet a b r g E)
    (j : ℕ) (hj : j ≤ r) : EqOn (D j) (E j) (Icc a b) :=
  (jet_eq_iterated hab hD j hj).trans
    ((iterated_congr hfg j).trans (jet_eq_iterated hab hE j hj).symm)

theorem smooth_zero (a b : ℝ) (f : ℝ → ℝ) :
    IntervalContDiff a b 0 f ↔ ContinuousOn f (Icc a b) := by
  constructor
  · rintro ⟨D, hD⟩
    exact (hD.2.1 0 le_rfl).congr hD.1.symm
  · intro hf
    exact ⟨fun _ => f, ⟨fun _ _ => rfl, fun j hj => hf, by simp⟩⟩

theorem jet_truncate (hqr : q ≤ r) (hD : IntervalJet a b r f D) :
    IntervalJet a b q f D :=
  ⟨hD.1, fun j hj => hD.2.1 j (hj.trans hqr),
    fun j hj => hD.2.2 j (hj.trans_le hqr)⟩

theorem jet_left_deriv (hab : a < b) (hD : IntervalJet a b r f D)
    (j : ℕ) (hj : j < r) : HasDerivWithinAt (D j) (D (j + 1) a) (Ici a) a := by
  have h := hD.2.2 j hj a (left_mem_Icc.mpr hab.le)
  change HasDerivAtFilter (D j) (D (j + 1) a) _ at h ⊢
  simpa only [nhdsWithin_Icc_eq_nhdsGE hab] using h

theorem jet_right_deriv (hab : a < b) (hD : IntervalJet a b r f D)
    (j : ℕ) (hj : j < r) : HasDerivWithinAt (D j) (D (j + 1) b) (Iic b) b := by
  have h := hD.2.2 j hj b (right_mem_Icc.mpr hab.le)
  change HasDerivAtFilter (D j) (D (j + 1) b) _ at h ⊢
  simpa only [nhdsWithin_Icc_eq_nhdsLE hab] using h

theorem jet_interior_deriv (hD : IntervalJet a b r f D) (ht : t ∈ Ioo a b)
    (j : ℕ) (hj : j < r) : HasDerivAt (D j) (D (j + 1) t) t := by
  exact (hD.2.2 j hj t (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

end NumAnalysis206.Approximation
