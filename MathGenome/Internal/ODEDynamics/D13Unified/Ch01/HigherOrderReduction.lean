import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.HigherOrderReduction
import MathGenome.Internal.ODEDynamics.D13Unified.Ch01.SolutionConcepts
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section
open Set

namespace D13Unified.HigherOrder

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[simp] theorem representative_apply (I : OpenTimeInterval) (y : I.carrier → E)
    (t : I.carrier) : representative I y t = y t := by
  simp [representative, t.property]

@[simp] theorem Equation.eval_of_mem {k : ℕ} (G : Equation E k) {t : ℝ}
    {X : Fin (k + 1) → E} (h : (t, X) ∈ G.domain) :
    G.eval t X = G.field ⟨(t, X), h⟩ := by
  simp [Equation.eval, h]

theorem Equation.toODE_eval {k : ℕ} (G : Equation E k) {t : ℝ}
    {X : Fin (k + 1) → E} (h : (t, X) ∈ G.domain) (j : Fin (k + 1)) :
    G.toODE.eval t X j =
      if hj : j.val < k then X ⟨j.val + 1, Nat.succ_lt_succ hj⟩ else G.eval t X := by
  rw [ODE.eval_of_mem _ h, G.eval_of_mem h]
  rfl

/-- On an open interval, differentiating the j-th derivative gives the next
iterated derivative, with no hypothesis about values outside the interval. -/
theorem hasDerivAt_iteratedDerivWithin (I : OpenTimeInterval) {k j : ℕ} {y : ℝ → E}
    (hy : ContDiffOn ℝ k y I.carrier) (hj : j < k) {t : ℝ} (ht : t ∈ I.carrier) :
    HasDerivAt (iteratedDerivWithin j y I.carrier)
      (iteratedDerivWithin (j + 1) y I.carrier t) t := by
  rw [iteratedDerivWithin_succ]
  exact (hy.differentiableOn_iteratedDerivWithin (by exact_mod_cast hj)
    I.isOpen.uniqueDiffOn t ht).hasDerivWithinAt.hasDerivAt (I.isOpen.mem_nhds ht)

/-- Forward construction for arbitrary ambient representatives. -/
theorem jet_isClassicalSolution {k : ℕ} (G : Equation E k) (I : OpenTimeInterval)
    (y : ℝ → E) (hc : ContDiffOn ℝ (k + 1 : ℕ) y I.carrier)
    (hg : ∀ t ∈ I.carrier, (t, jet I k y t) ∈ G.domain)
    (he : ∀ t ∈ I.carrier, iteratedDerivWithin (k + 1) y I.carrier t =
      G.eval t (jet I k y t)) : IsClassicalSolutionOn G.toODE I (jet I k y) := by
  refine ⟨?_, hg, ?_⟩
  · apply contDiffOn_pi.mpr
    intro j
    rw [contDiffOn_one_iff_derivWithin I.isOpen.uniqueDiffOn]
    refine ⟨hc.differentiableOn_iteratedDerivWithin (by exact_mod_cast j.isLt)
      I.isOpen.uniqueDiffOn, ?_⟩
    change ContinuousOn (derivWithin (iteratedDerivWithin j.val y I.carrier) I.carrier)
      I.carrier
    rw [← iteratedDerivWithin_succ]
    exact hc.continuousOn_iteratedDerivWithin (by exact_mod_cast j.isLt)
      I.isOpen.uniqueDiffOn
  · intro t ht
    apply hasDerivAt_pi.mpr
    intro j
    rw [G.toODE_eval (hg t ht)]
    have hd := hasDerivAt_iteratedDerivWithin I hc j.isLt ht
    by_cases hj : j.val < k
    · simpa only [dite_eq_left hj, jet] using hd
    · have hlast : j.val = k := by omega
      rw [dite_eq_right hj]
      simpa only [jet, hlast, he t ht] using hd

/-- A C¹ companion-system solution has precisely the claimed derivative
coordinates; the proof recovers them successively, rather than assuming them. -/
theorem system_derivative_coordinates {k : ℕ} (G : Equation E k) (I : OpenTimeInterval)
    (Y : ℝ → (Fin (k + 1) → E)) (hY : IsClassicalSolutionOn G.toODE I Y) :
    (∀ (j : Fin (k + 1)), EqOn
      (iteratedDerivWithin j.val (fun t => Y t 0) I.carrier) (fun t => Y t j) I.carrier) ∧
    (∀ t ∈ I.carrier, iteratedDerivWithin (k + 1) (fun t => Y t 0) I.carrier t =
      G.eval t (Y t)) := by
  have coord (j : Fin (k + 1)) (t : ℝ) (ht : t ∈ I.carrier) :=
    hasDerivAt_pi.mp (hY.2.2 t ht) j
  have hc : ∀ n : ℕ, ∀ hn : n < k + 1, EqOn
      (iteratedDerivWithin n (fun t => Y t 0) I.carrier)
      (fun t => Y t ⟨n, hn⟩) I.carrier := by
    intro n
    induction n with
    | zero => intro hn t ht; simp
    | succ n ih =>
      intro hn t ht
      have hn' : n < k + 1 := by omega
      have hn'' : n < k := by omega
      rw [iteratedDerivWithin_succ]
      rw [derivWithin_congr (ih hn') (ih hn' ht)]
      have hd := coord ⟨n, hn'⟩ t ht
      rw [G.toODE_eval (hY.2.1 t ht), dite_eq_left hn''] at hd
      exact hd.hasDerivWithinAt.derivWithin (I.isOpen.uniqueDiffOn t ht)
  refine ⟨fun j => hc j.val j.isLt, ?_⟩
  intro t ht
  rw [iteratedDerivWithin_succ]
  rw [derivWithin_congr (hc k (by omega)) (hc k (by omega) ht)]
  have hd := coord (Fin.last k) t ht
  rw [G.toODE_eval (hY.2.1 t ht), dite_eq_right (by simp)] at hd
  exact hd.hasDerivWithinAt.derivWithin (I.isOpen.uniqueDiffOn t ht)

/-- The first coordinate gains all k+1 continuous derivatives. -/
theorem system_first_contDiff {k : ℕ} (G : Equation E k) (I : OpenTimeInterval)
    (Y : ℝ → (Fin (k + 1) → E)) (hY : IsClassicalSolutionOn G.toODE I Y) :
    ContDiffOn ℝ (k + 1 : ℕ) (fun t => Y t 0) I.carrier := by
  have hcoords := (system_derivative_coordinates G I Y hY).1
  have hregular (j : Fin (k + 1)) : ContDiffOn ℝ 1
      (iteratedDerivWithin j.val (fun t => Y t 0) I.carrier) I.carrier :=
    (contDiffOn_pi.mp hY.1 j).congr (hcoords j)
  have hn : ∀ n : ℕ, n ≤ k + 1 →
      ContDiffOn ℝ n (fun t => Y t 0) I.carrier := by
    intro n
    induction n with
    | zero =>
      intro _
      exact (contDiffOn_pi.mp hY.1 0).of_le (by simp)
    | succ n ih =>
      intro hle
      apply (contDiffOn_nat_succ_iff_contDiffOn_one_iteratedDerivWithin
        I.isOpen.uniqueDiffOn).mpr
      exact ⟨ih (by omega), hregular ⟨n, by omega⟩⟩
  exact hn (k + 1) le_rfl

/-- Changing an ambient representative on the complement of the time interval
preserves the classical solution property. -/
theorem classicalSolution_congr {F : ODE E} {I : OpenTimeInterval}
    {x y : ℝ → E} (h : EqOn x y I.carrier) :
    IsClassicalSolutionOn F I x ↔ IsClassicalSolutionOn F I y :=
  (classical_iff_solutionOn F I x).trans
    ((solutionOn_congr F I.toTimeInterval x y h).trans
      (classical_iff_solutionOn F I y).symm)

/-- Extending a vector-valued curve and then taking a coordinate equals
extending that coordinate. -/
theorem representative_coordinate {k : ℕ} (I : OpenTimeInterval)
    (Y : I.carrier → (Fin (k + 1) → E)) (j : Fin (k + 1)) :
    (fun t => representative I Y t j) = representative I (fun t => Y t j) := by
  classical
  funext t
  by_cases ht : t ∈ I.carrier <;> simp [representative, ht]

/-- Forward map on the actual solution sets. -/
def toSystem {k : ℕ} (G : Equation E k) (I : OpenTimeInterval)
    (y : HigherSolutions G I) : SystemSolutions G I := by
  refine ⟨fun t => jet I k (representative I y.val) t, ?_⟩
  have h := jet_isClassicalSolution G I (representative I y.val)
    y.property.1 y.property.2.1 y.property.2.2
  apply (classicalSolution_congr (F := G.toODE) (I := I) ?_).mp h
  intro t ht
  simp only [representative, dite_eq_left ht]

/-- Projection to the first coordinate, with all higher regularity proved. -/
def toHigher {k : ℕ} (G : Equation E k) (I : OpenTimeInterval)
    (Y : SystemSolutions G I) : HigherSolutions G I := by
  refine ⟨fun t => Y.val t 0, ?_⟩
  have hY : IsClassicalSolutionOn G.toODE I (representative I Y.val) := Y.property
  have hcoords := system_derivative_coordinates G I (representative I Y.val) hY
  have hreg := system_first_contDiff G I (representative I Y.val) hY
  rw [representative_coordinate] at hcoords hreg
  refine ⟨hreg, ?_, ?_⟩
  · intro t ht
    have hj : jet I k (representative I (fun t => Y.val t 0)) t =
        representative I Y.val t := by
      funext j
      exact hcoords.1 j ht
    rw [hj]
    exact hY.2.1 t ht
  · intro t ht
    have hj : jet I k (representative I (fun t => Y.val t 0)) t =
        representative I Y.val t := by
      funext j
      exact hcoords.1 j ht
    rw [hj]
    exact hcoords.2 t ht

@[simp] theorem toHigher_toSystem {k : ℕ} (G : Equation E k) (I : OpenTimeInterval)
    (y : HigherSolutions G I) : toHigher G I (toSystem G I y) = y := by
  apply Subtype.ext
  funext t
  change iteratedDerivWithin 0 (representative I y.val) I.carrier t = y.val t
  simp

@[simp] theorem toSystem_toHigher {k : ℕ} (G : Equation E k) (I : OpenTimeInterval)
    (Y : SystemSolutions G I) : toSystem G I (toHigher G I Y) = Y := by
  apply Subtype.ext
  funext t j
  have hcoords := (system_derivative_coordinates G I (representative I Y.val)
    Y.property).1
  rw [representative_coordinate] at hcoords
  change iteratedDerivWithin j.val (representative I (fun t => Y.val t 0)) I.carrier t =
    Y.val t j
  simpa only [representative_apply] using hcoords j t.property

/-- paper.tex, d13:01:higher-order, including its converse and initial data.
All maps have exactly the original time interval as their domain. -/
theorem reduction : Specs.D13Unified.Ch01.HigherOrderReduction.reductionExpected := by
  intro E _ _ k G I
  let e : HigherSolutions G I ≃ SystemSolutions G I :=
    { toFun := toSystem G I
      invFun := toHigher G I
      left_inv := toHigher_toSystem G I
      right_inv := toSystem_toHigher G I }
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · intro y t j
    rfl
  · intro Y t
    rfl
  · intro Y
    have hc := system_derivative_coordinates G I (representative I Y.val) Y.property
    have hr := system_first_contDiff G I (representative I Y.val) Y.property
    rw [representative_coordinate] at hc hr
    refine ⟨hr, ?_, ?_⟩
    · intro t j
      simpa only [representative_apply] using hc.1 j t.property
    · intro t
      simpa only [representative_apply] using hc.2 t t.property
  · intro y s ξ
    change (∀ j : Fin (k + 1), jet I k (representative I y.val) s j = ξ j) ↔
      jet I k (representative I y.val) s = ξ
    exact ⟨fun h => funext h, fun h j => congrFun h j⟩

end D13Unified.HigherOrder
