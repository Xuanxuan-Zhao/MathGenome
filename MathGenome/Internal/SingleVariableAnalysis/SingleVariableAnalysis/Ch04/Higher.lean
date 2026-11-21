import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.OneSided
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Peano
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Higher

/-!
# Higher real-variable derivatives and regularity

K03.04.higher, paper.tex:718–725. The variable is real, including for complex
values. Total library derivative values are used only together with existence
predicates. In particular `KTimesDifferentiableOn` does not ask that the highest
derivative be continuous. The open-set results apply to every open interval,
including unbounded intervals.

For a compact interval we retain an actual family of continuous extensions.
Its derivative relations are within the interval, hence one-sided at its
nondegenerate endpoints. We prove the interior/endpoint interpretation, equality
with the interior iterated derivatives, and equivalence with `ContDiffOn`.
No differentiability of an arbitrary ambient extension at an endpoint is required.
-/

namespace SingleVariableAnalysis

open Set Filter
open scoped Topology ContDiff
universe u

noncomputable def RealIteratedDerivative {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (j : ℕ) (f : ℝ → F) : ℝ → F := iteratedDeriv j f

def KTimesDifferentiableOn {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (k : ℕ) (f : ℝ → F) (I : Set ℝ) : Prop :=
  ∀ j : ℕ, j < k → ∀ x ∈ I, DifferentiableAt ℝ (RealIteratedDerivative j f) x

def CkOn {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (k : ℕ) (f : ℝ → F) (I : Set ℝ) : Prop :=
  KTimesDifferentiableOn k f I ∧
    ∀ j : ℕ, j ≤ k → ContinuousOn (RealIteratedDerivative j f) I

def SmoothOn {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (I : Set ℝ) : Prop := ∀ k : ℕ, CkOn k f I

/-- The zeroth extension agrees with f, and each subsequent extension is the
within derivative of the preceding one. The data beyond order k is unused. -/
def ClosedDerivativeFamily {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (k : ℕ) (f : ℝ → F) (a b : ℝ) (D : ℕ → ℝ → F) : Prop :=
  EqOn (D 0) f (Icc a b) ∧
    (∀ j : ℕ, j ≤ k → ContinuousOn (D j) (Icc a b)) ∧
    ∀ j : ℕ, j < k → ∀ x ∈ Icc a b, HasDerivWithinAt (D j) (D (j + 1) x) (Icc a b) x

def CkOnClosed {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (k : ℕ) (f : ℝ → F) (a b : ℝ) : Prop :=
  ∃ D : ℕ → ℝ → F, ClosedDerivativeFamily k f a b D

def SmoothOnClosed {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (a b : ℝ) : Prop := ∀ k : ℕ, CkOnClosed k f a b

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]

@[simp] theorem realIteratedDerivative_zero (f : ℝ → F) : RealIteratedDerivative 0 f = f :=
  iteratedDeriv_zero

theorem realIteratedDerivative_succ (j : ℕ) (f : ℝ → F) :
    RealIteratedDerivative (j + 1) f = deriv (RealIteratedDerivative j f) :=
  iteratedDeriv_succ

theorem kTimesDifferentiableOn_zero (f : ℝ → F) (I : Set ℝ) :
    KTimesDifferentiableOn 0 f I := by
  intro j hj
  omega

theorem kTimesDifferentiableOn_succ_iff (k : ℕ) (f : ℝ → F) (I : Set ℝ) :
    KTimesDifferentiableOn (k + 1) f I ↔
      KTimesDifferentiableOn k f I ∧
        ∀ x ∈ I, DifferentiableAt ℝ (RealIteratedDerivative k f) x := by
  constructor
  · intro h
    exact ⟨fun j hj => h j (by omega), h k (by omega)⟩
  · rintro ⟨h, hk⟩ j hj
    by_cases heq : j = k
    · simpa only [heq] using hk
    · exact h j (by omega)

theorem kTimesDifferentiableOn_iff_increment (k : ℕ) (f : ℝ → F) (I : Set ℝ) :
    KTimesDifferentiableOn k f I ↔
      ∀ j : ℕ, j < k → ∀ x ∈ I,
        HasRealIncrementDerivative (RealIteratedDerivative j f)
          (RealIteratedDerivative (j + 1) f x) x := by
  simp only [KTimesDifferentiableOn, hasRealIncrementDerivative_iff_hasDerivAt,
    realIteratedDerivative_succ]
  exact forall_congr' fun j => forall_congr' fun _ => forall_congr' fun x =>
    forall_congr' fun _ => ⟨fun h => h.hasDerivAt, fun h => h.differentiableAt⟩

theorem kTimesDifferentiableOn_continuous_lower (k : ℕ) (f : ℝ → F) (I : Set ℝ)
    (h : KTimesDifferentiableOn k f I) (j : ℕ) (hj : j < k) :
    ContinuousOn (RealIteratedDerivative j f) I :=
  fun x hx => (h j hj x hx).continuousAt.continuousWithinAt

/-- Compatibility on open domains; there is no continuity requirement at order k
in the differentiability conjunct. -/
theorem ckOn_iff_contDiffOn (k : ℕ) (f : ℝ → F) (I : Set ℝ) (hI : IsOpen I) :
    CkOn k f I ↔ ContDiffOn ℝ k f I := by
  rw [contDiffOn_nat_iff_continuousOn_differentiableOn_deriv hI.uniqueDiffOn]
  have heq (j : ℕ) : EqOn (iteratedDerivWithin j f I) (RealIteratedDerivative j f) I :=
    iteratedDerivWithin_of_isOpen hI
  constructor
  · rintro ⟨hd, hc⟩
    refine ⟨fun j hj => (hc j hj).congr (heq j), fun j hj x hx => ?_⟩
    exact ((hd j hj x hx).differentiableWithinAt).congr_of_eventuallyEq
      (heq j).eventuallyEq_nhdsWithin (heq j hx)
  · rintro ⟨hc, hd⟩
    refine ⟨fun j hj x hx => ?_, fun j hj => (hc j hj).congr (heq j).symm⟩
    have hd' : DifferentiableOn ℝ (RealIteratedDerivative j f) I :=
      (hd j hj).congr (heq j).symm
    exact hd'.differentiableAt (hI.mem_nhds hx)

theorem smoothOn_iff_contDiffOn (f : ℝ → F) (I : Set ℝ) (hI : IsOpen I) :
    SmoothOn f I ↔ ContDiffOn ℝ ∞ f I := by
  simp only [SmoothOn, ckOn_iff_contDiffOn _ _ _ hI, contDiffOn_infty]

theorem ckOn_zero_iff (f : ℝ → F) (I : Set ℝ) :
    CkOn 0 f I ↔ ContinuousOn f I := by
  simp [CkOn, kTimesDifferentiableOn_zero]

/-- Translation from the manuscript's real increments to the library's within
slope. This lemma also applies at endpoints. -/
theorem withinIncrementDerivative_iff_hasDerivWithinAt (f : ℝ → F) (L : F)
    (I : Set ℝ) (x : ℝ) :
    HasRealIncrementDerivativeWithin f L I x ↔ HasDerivWithinAt f L I x := by
  rw [withinDerivative_epsilon_iff, hasDerivWithinAt_iff_tendsto_slope,
    Metric.tendsto_nhdsWithin_nhds]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hh⟩ := h ε hε
    refine ⟨δ, hδ, fun y hy hyd => ?_⟩
    have hne : y - x ≠ 0 := sub_ne_zero.mpr (by simpa using hy.2)
    have hd := hh (y - x) (by simpa using hy.1) (abs_pos.mpr hne)
      (by simpa only [Real.dist_eq] using hyd)
    simpa only [RealIncrementQuotient, add_sub_cancel, slope_def_module, dist_eq_norm] using hd
  · intro h ε hε
    obtain ⟨δ, hδ, hh⟩ := h ε hε
    refine ⟨δ, hδ, fun t ht hpos hlt => ?_⟩
    have hne : t ≠ 0 := (abs_pos.mp hpos)
    have hd := hh (x := x + t) ⟨ht, by simp [hne]⟩
      (by simpa only [Real.dist_eq, add_sub_cancel_left] using hlt)
    simpa only [RealIncrementQuotient, slope_def_module, add_sub_cancel_left,
      dist_eq_norm] using hd

/-- A derivative family consists exactly of continuous interior derivatives
with the available right/left derivatives at a/b. -/
theorem closedDerivativeFamily_iff_sides (k : ℕ) (f : ℝ → F) (a b : ℝ)
    (hab : a < b) (D : ℕ → ℝ → F) :
    ClosedDerivativeFamily k f a b D ↔
      EqOn (D 0) f (Icc a b) ∧
        (∀ j : ℕ, j ≤ k → ContinuousOn (D j) (Icc a b)) ∧
        ∀ j : ℕ, j < k →
          (∀ x ∈ Ioo a b, HasDerivAt (D j) (D (j + 1) x) x) ∧
          HasRightRealIncrementDerivativeWithin (D j) (D (j + 1) a) (Icc a b) a ∧
          HasLeftRealIncrementDerivativeWithin (D j) (D (j + 1) b) (Icc a b) b := by
  unfold ClosedDerivativeFamily
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply forall_congr'
  intro j
  apply forall_congr'
  intro _
  constructor
  · intro h
    refine ⟨fun x hx => (h x ⟨hx.1.le, hx.2.le⟩).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2), ?_, ?_⟩
    · apply (closedInterval_leftEndpoint_iff _ _ _ _ hab).mp
      exact (withinIncrementDerivative_iff_hasDerivWithinAt _ _ _ _).mpr
        (h a ⟨le_rfl, hab.le⟩)
    · apply (closedInterval_rightEndpoint_iff _ _ _ _ hab).mp
      exact (withinIncrementDerivative_iff_hasDerivWithinAt _ _ _ _).mpr
        (h b ⟨hab.le, le_rfl⟩)
  · rintro ⟨hi, ha, hb⟩ x hx
    rcases eq_or_lt_of_le hx.1 with rfl | hax
    · exact (withinIncrementDerivative_iff_hasDerivWithinAt _ _ _ _).mp
        ((closedInterval_leftEndpoint_iff _ _ _ _ hab).mpr ha)
    rcases eq_or_lt_of_le hx.2 with rfl | hxb
    · exact (withinIncrementDerivative_iff_hasDerivWithinAt _ _ _ _).mp
        ((closedInterval_rightEndpoint_iff _ _ _ _ hab).mpr hb)
    · exact (hi x ⟨hax, hxb⟩).hasDerivWithinAt

/-- Uniqueness of every continuous derivative extension, expressed using the
canonical library within derivative. -/
theorem closedDerivativeFamily_eq_iteratedDerivWithin (k : ℕ) (f : ℝ → F)
    (a b : ℝ) (hab : a < b) (D : ℕ → ℝ → F)
    (h : ClosedDerivativeFamily k f a b D) (j : ℕ) (hj : j ≤ k) :
    EqOn (D j) (iteratedDerivWithin j f (Icc a b)) (Icc a b) := by
  induction j with
  | zero => simpa only [iteratedDerivWithin_zero] using h.1
  | succ j ih =>
    have heq := ih (by omega)
    intro x hx
    rw [iteratedDerivWithin_succ]
    calc
      D (j + 1) x = derivWithin (D j) (Icc a b) x :=
        ((h.2.2 j (by omega) x hx).derivWithin (uniqueDiffOn_Icc hab x hx)).symm
      _ = derivWithin (iteratedDerivWithin j f (Icc a b)) (Icc a b) x :=
        derivWithin_congr heq (heq hx)

/-- Thus the chosen continuous family really extends the ordinary interior
iterates, independently of values of f outside the compact interval. -/
theorem closedDerivativeFamily_eq_interior (k : ℕ) (f : ℝ → F) (a b : ℝ)
    (D : ℕ → ℝ → F) (h : ClosedDerivativeFamily k f a b D) (j : ℕ) (hj : j ≤ k) :
    EqOn (D j) (RealIteratedDerivative j f) (Ioo a b) := by
  induction j with
  | zero =>
    intro x hx
    simpa only [realIteratedDerivative_zero] using h.1 ⟨hx.1.le, hx.2.le⟩
  | succ j ih =>
    have heq := ih (by omega)
    intro x hx
    rw [realIteratedDerivative_succ]
    have hd := (h.2.2 j (by omega) x ⟨hx.1.le, hx.2.le⟩).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)
    exact (hd.congr_of_eventuallyEq
      (heq.eventuallyEq_of_mem (Ioo_mem_nhds hx.1 hx.2)).symm).deriv.symm

theorem ckOnClosed_iff_contDiffOn (k : ℕ) (f : ℝ → F) (a b : ℝ) (hab : a < b) :
    CkOnClosed k f a b ↔ ContDiffOn ℝ k f (Icc a b) := by
  rw [contDiffOn_nat_iff_continuousOn_differentiableOn_deriv (uniqueDiffOn_Icc hab)]
  constructor
  · rintro ⟨D, hD⟩
    have heq := closedDerivativeFamily_eq_iteratedDerivWithin k f a b hab D hD
    refine ⟨fun j hj => (hD.2.1 j hj).congr (heq j hj).symm, fun j hj => ?_⟩
    have hd : DifferentiableOn ℝ (D j) (Icc a b) :=
      fun x hx => (hD.2.2 j hj x hx).differentiableWithinAt
    exact hd.congr (heq j (by omega)).symm
  · rintro ⟨hc, hd⟩
    refine ⟨fun j => iteratedDerivWithin j f (Icc a b), ?_, hc, ?_⟩
    · simp only [iteratedDerivWithin_zero]
      exact eqOn_refl _ _
    · intro j hj x hx
      dsimp only
      rw [iteratedDerivWithin_succ]
      exact (hd j hj x hx).hasDerivWithinAt

theorem smoothOnClosed_iff_contDiffOn (f : ℝ → F) (a b : ℝ) (hab : a < b) :
    SmoothOnClosed f a b ↔ ContDiffOn ℝ ∞ f (Icc a b) := by
  simp only [SmoothOnClosed, ckOnClosed_iff_contDiffOn _ _ _ _ hab, contDiffOn_infty]

theorem ckOnClosed_zero_iff (f : ℝ → F) (a b : ℝ) :
    CkOnClosed 0 f a b ↔ ContinuousOn f (Icc a b) := by
  constructor
  · rintro ⟨D, hD⟩
    exact (hD.2.1 0 le_rfl).congr hD.1.symm
  · intro hc
    refine ⟨fun _ => f, eqOn_refl _ _, fun j hj => hc, ?_⟩
    intro j hj
    omega

/-- Locality makes the total iterates independent of an ambient extension on
an open interval, even when differentiability has not yet been established. -/
theorem realIteratedDerivative_congr_on_open (f g : ℝ → F) (I : Set ℝ)
    (hI : IsOpen I) (hfg : EqOn f g I) (j : ℕ) :
    EqOn (RealIteratedDerivative j f) (RealIteratedDerivative j g) I := by
  induction j with
  | zero => simpa only [realIteratedDerivative_zero] using hfg
  | succ j ih =>
    simpa only [realIteratedDerivative_succ] using ih.deriv hI

theorem kTimesDifferentiableOn_congr (k : ℕ) (f g : ℝ → F) (I : Set ℝ)
    (hI : IsOpen I) (hfg : EqOn f g I) :
    KTimesDifferentiableOn k f I ↔ KTimesDifferentiableOn k g I := by
  have heq := realIteratedDerivative_congr_on_open f g I hI hfg
  constructor
  · intro h j hj x hx
    exact (h j hj x hx).congr_of_eventuallyEq
      ((heq j).eventuallyEq_of_mem (hI.mem_nhds hx)).symm
  · intro h j hj x hx
    exact (h j hj x hx).congr_of_eventuallyEq
      ((heq j).eventuallyEq_of_mem (hI.mem_nhds hx))

theorem ckOn_congr (k : ℕ) (f g : ℝ → F) (I : Set ℝ)
    (hI : IsOpen I) (hfg : EqOn f g I) : CkOn k f I ↔ CkOn k g I := by
  rw [ckOn_iff_contDiffOn k f I hI, ckOn_iff_contDiffOn k g I hI]
  exact contDiffOn_congr hfg

theorem ckOnClosed_congr (k : ℕ) (f g : ℝ → F) (a b : ℝ)
    (hfg : EqOn f g (Icc a b)) : CkOnClosed k f a b ↔ CkOnClosed k g a b := by
  constructor
  · rintro ⟨D, hD⟩
    exact ⟨D, hD.1.trans hfg, hD.2⟩
  · rintro ⟨D, hD⟩
    exact ⟨D, hD.1.trans hfg.symm, hD.2⟩

/-- On a singleton there is no available endpoint approach. This convention
puts no derivative constraint on the one value of the function. -/
theorem ckOnClosed_singleton (k : ℕ) (f : ℝ → F) (a : ℝ) : CkOnClosed k f a a := by
  refine ⟨fun j _ => if j = 0 then f a else 0, ?_, ?_, ?_⟩
  · intro x hx
    have hxa : x = a := le_antisymm hx.2 hx.1
    simp [hxa]
  · intro j _
    exact continuousOn_const
  · intro j _ x _
    simpa only [Nat.add_one_ne_zero, ite_false] using
      (hasDerivWithinAt_const x (Icc a a) (if j = 0 then f a else (0 : F)))

/-- Compatibility includes degenerate compact intervals as well. -/
theorem ckOnClosed_iff_contDiffOn_le (k : ℕ) (f : ℝ → F) (a b : ℝ) (hab : a ≤ b) :
    CkOnClosed k f a b ↔ ContDiffOn ℝ k f (Icc a b) := by
  rcases eq_or_lt_of_le hab with rfl | hab
  · have hc : ContDiffOn ℝ k f (Icc a a) :=
      (contDiffOn_const (c := f a)).congr (by
        intro x hx
        have hxa : x = a := le_antisymm hx.2 hx.1
        simp [hxa])
    exact ⟨fun _ => hc, fun _ => ckOnClosed_singleton k f a⟩
  · exact ckOnClosed_iff_contDiffOn k f a b hab

theorem smoothOnClosed_iff_contDiffOn_le (f : ℝ → F) (a b : ℝ) (hab : a ≤ b) :
    SmoothOnClosed f a b ↔ ContDiffOn ℝ ∞ f (Icc a b) := by
  simp only [SmoothOnClosed, ckOnClosed_iff_contDiffOn_le _ _ _ _ hab, contDiffOn_infty]

end SingleVariableAnalysis
