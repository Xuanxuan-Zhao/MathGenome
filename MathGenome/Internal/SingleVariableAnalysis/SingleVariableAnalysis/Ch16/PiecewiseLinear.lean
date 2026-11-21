import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.PiecewiseLinear
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Partitions
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.HeineCantor
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch16.SupSpace
import Mathlib.Topology.LocallyFinite
import Mathlib.Tactic.FunProp

/-!
K03.16.piecewise_linear. We glue the affine functions on the finite closed
cell cover. Strict ordering makes two intersecting cells agree at their
common endpoint. The barycentric weights are nonnegative and sum to one,
so the endpoint errors give the modulus bound without differentiability.
Uniform continuity of a continuous map on a compact interval makes the
modulus tend to zero; the canonical sup norm gives uniform convergence.
-/
namespace SingleVariableAnalysis.PiecewiseLinear
open Riemann
open scoped Topology
namespace S
export Specs.SingleVariableAnalysis.Ch16.PiecewiseLinear (node cellValue)
end S
open S

noncomputable abbrev interpolant := @Specs.SingleVariableAnalysis.Ch16.PiecewiseLinear.interpolantValue
noncomputable abbrev modulus := @Specs.SingleVariableAnalysis.Ch16.PiecewiseLinear.modulusValue

lemma cell_left {a b : ℝ} (P : Partition a b) (f : C(Set.Icc a b, ℝ)) (i : Fin P.n) :
    cellValue P f i (P.point i.castSucc) = f (node P i.castSucc) := by
  simp [cellValue]

lemma cell_right {a b : ℝ} (P : Partition a b) (f : C(Set.Icc a b, ℝ)) (i : Fin P.n) :
    cellValue P f i (P.point i.succ) = f (node P i.succ) := by
  have h : P.point i.succ - P.point i.castSucc ≠ 0 := ne_of_gt (cell_positive P i)
  simp [cellValue, h]

/-- Ordered closed cells meet only at a common endpoint. -/
lemma cell_agree {a b x : ℝ} (P : Partition a b) (f : C(Set.Icc a b, ℝ))
    (i j : Fin P.n)
    (hi : x ∈ Set.Icc (P.point i.castSucc) (P.point i.succ))
    (hj : x ∈ Set.Icc (P.point j.castSucc) (P.point j.succ)) :
    cellValue P f i x = cellValue P f j x := by
  suffices h : ∀ i j : Fin P.n, i < j →
      x ∈ Set.Icc (P.point i.castSucc) (P.point i.succ) →
      x ∈ Set.Icc (P.point j.castSucc) (P.point j.succ) →
      cellValue P f i x = cellValue P f j x by
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · exact h i j hlt hi hj
    · rfl
    · exact (h j i hgt hj hi).symm
  intro i j hij hi hj
  have hle : i.succ ≤ j.castSucc := by change i.val + 1 ≤ j.val; exact hij
  have hp := P.strictMono.monotone hle
  have hx : x = P.point i.succ := le_antisymm hi.2 (hp.trans hj.1)
  have he : P.point i.succ = P.point j.castSucc := le_antisymm hp (hj.1.trans hi.2)
  have he' : node P i.succ = node P j.castSucc := Subtype.ext he
  rw [hx, cell_right, he, cell_left, he']

/-- Every point of a nondegenerate partition lies in one of its closed cells. -/
lemma cell_cover {a b x : ℝ} (P : Partition a b) (hn : 0 < P.n)
    (hx : x ∈ Set.Icc a b) :
    ∃ i : Fin P.n, x ∈ Set.Icc (P.point i.castSucc) (P.point i.succ) := by
  let q : ℕ → Prop := fun j => ∃ hj : j < P.n + 1, x ≤ P.point ⟨j, hj⟩
  have hex : ∃ j, q j := by
    refine ⟨P.n, Nat.lt_succ_self _, ?_⟩
    change x ≤ P.point (Fin.last P.n)
    rw [P.last]
    exact hx.2
  let k := Nat.find hex
  obtain ⟨hk, hxk⟩ := Nat.find_spec hex
  by_cases hzero : k = 0
  · let i : Fin P.n := ⟨0, hn⟩
    refine ⟨i, ?_, ?_⟩
    · change P.point 0 ≤ x
      rw [P.first]
      exact hx.1
    · have hx0 : x ≤ a := by
        have he : (⟨Nat.find hex, hk⟩ : Fin (P.n+1)) = 0 := Fin.ext hzero
        simpa only [he, P.first] using hxk
      exact hx0.trans (by simpa only [P.first] using P.strictMono.monotone (Fin.zero_le i.succ))
  · have hpred : k - 1 < k := Nat.sub_lt (Nat.pos_of_ne_zero hzero) (by decide)
    have hnot := Nat.find_min hex hpred
    let i : Fin P.n := ⟨k-1, by omega⟩
    refine ⟨i, ?_, ?_⟩
    · have h : ¬ x ≤ P.point i.castSucc := fun h => hnot ⟨i.castSucc.isLt, h⟩
      exact le_of_lt (lt_of_not_ge h)
    · have he : i.succ = (⟨k, hk⟩ : Fin (P.n+1)) := by apply Fin.ext; dsimp [i]; omega
      simpa only [he] using hxk

theorem cell_formula : Specs.SingleVariableAnalysis.Ch16.PiecewiseLinear.cellFormula := by
  intro a b P f i x hx
  have h : ∃ j : Fin P.n, x ∈ Set.Icc (P.point j.castSucc) (P.point j.succ) := ⟨i,hx⟩
  simp only [Specs.SingleVariableAnalysis.Ch16.PiecewiseLinear.interpolantValue, dite_eq_left h]
  exact cell_agree P f _ i h.choose_spec hx

theorem interpolant_degenerate : Specs.SingleVariableAnalysis.Ch16.PiecewiseLinear.degenerate := by
  intro a P f x
  have hn := n_eq_zero_of_degenerate a P
  have : IsEmpty (Fin P.n) := Fin.isEmpty_iff.mpr hn
  simp [Specs.SingleVariableAnalysis.Ch16.PiecewiseLinear.interpolantValue]

lemma cell_at_node {a b : ℝ} (P : Partition a b) (f : C(Set.Icc a b, ℝ))
    (i : Fin P.n) (j : Fin (P.n+1))
    (hx : P.point j ∈ Set.Icc (P.point i.castSucc) (P.point i.succ)) :
    cellValue P f i (P.point j) = f (node P j) := by
  have hlo : i.castSucc ≤ j := P.strictMono.le_iff_le.mp hx.1
  have hhi : j ≤ i.succ := P.strictMono.le_iff_le.mp hx.2
  by_cases he : j = i.castSucc
  · subst j
    exact cell_left P f i
  · have he' : j = i.succ := by
      apply Fin.ext
      have hne : j.val ≠ i.val := fun hv => he (Fin.ext hv)
      change i.val ≤ j.val at hlo
      change j.val ≤ i.val + 1 at hhi
      change j.val = i.val + 1
      omega
    subst j
    exact cell_right P f i

theorem node_values : Specs.SingleVariableAnalysis.Ch16.PiecewiseLinear.nodeValues := by
  intro a b P f j
  by_cases hn : P.n = 0
  · have : IsEmpty (Fin P.n) := Fin.isEmpty_iff.mpr hn
    have hj : j = 0 := Fin.ext (by have := j.isLt; omega)
    simp [Specs.SingleVariableAnalysis.Ch16.PiecewiseLinear.interpolantValue, hj]
  · obtain ⟨i, hi⟩ := cell_cover P (Nat.pos_of_ne_zero hn) (node P j).property
    exact (cell_formula P f i (P.point j) hi).trans (cell_at_node P f i j hi)

lemma cell_continuous {a b : ℝ} (P : Partition a b) (f : C(Set.Icc a b, ℝ))
    (i : Fin P.n) : Continuous (cellValue P f i) := by
  unfold cellValue
  fun_prop

theorem interpolant_continuous :
    Specs.SingleVariableAnalysis.Ch16.PiecewiseLinear.interpolantContinuous := by
  intro a b P f
  by_cases hn : P.n = 0
  · have : IsEmpty (Fin P.n) := Fin.isEmpty_iff.mpr hn
    have he : interpolant P f = fun _ => f (node P 0) := by
      funext x
      simp [interpolant, Specs.SingleVariableAnalysis.Ch16.PiecewiseLinear.interpolantValue]
    change ContinuousOn (interpolant P f) _
    rw [he]
    exact continuousOn_const
  · let cells : Fin P.n → Set ℝ := fun i => Set.Icc (P.point i.castSucc) (P.point i.succ)
    have hcont : ContinuousOn (interpolant P f) (⋃ i, cells i) := by
      apply (locallyFinite_of_finite cells).continuousOn_iUnion (fun _ => isClosed_Icc)
      intro i
      exact (cell_continuous P f i).continuousOn.congr (fun x hx => cell_formula P f i x hx)
    exact hcont.mono (fun x hx => Set.mem_iUnion.mpr (cell_cover P (Nat.pos_of_ne_zero hn) hx))

/-- The same interpolant as a member of the canonical continuous-function space. -/
noncomputable def interpolantMap {a b : ℝ} (P : Partition a b) (f : C(Set.Icc a b, ℝ)) :
    C(Set.Icc a b, ℝ) :=
  ⟨fun x => interpolant P f x, (interpolant_continuous P f).domRestrict⟩

/-- The set defining the modulus is bounded, rather than a default real supremum. -/
lemma modulus_bddAbove {a b δ : ℝ} (f : C(Set.Icc a b, ℝ)) :
    BddAbove {r : ℝ | ∃ x y : Set.Icc a b,
      |(x : ℝ) - (y : ℝ)| ≤ δ ∧ r = |f x - f y|} := by
  refine ⟨2 * ‖f‖, ?_⟩
  rintro r ⟨x, y, _, rfl⟩
  have hx : |f x| ≤ ‖f‖ := by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x
  have hy : |f y| ≤ ‖f‖ := by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm y
  have ht : |f x - f y| ≤ |f x| + |f y| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le (f x) (f y)
  linarith

lemma modulus_nonneg {a b : ℝ} (f : C(Set.Icc a b, ℝ)) (δ : ℝ) :
    0 ≤ modulus f δ := by
  apply Real.sSup_nonneg
  rintro r ⟨x, y, _, rfl⟩
  exact abs_nonneg _

lemma modulus_controls {a b δ : ℝ} (f : C(Set.Icc a b, ℝ))
    (x y : Set.Icc a b) (h : |(x : ℝ) - (y : ℝ)| ≤ δ) :
    |f x - f y| ≤ modulus f δ :=
  le_csSup (modulus_bddAbove f) ⟨x, y, h, rfl⟩

/-- Uniform continuity controls the actual supremum at all sufficiently small radii. -/
lemma modulus_small {a b : ℝ} (hab : a ≤ b) (f : C(Set.Icc a b, ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 ≤ r → r < δ → modulus f r < ε := by
  obtain ⟨δ, hδ, h⟩ := f.uniform_continuity (ε/2) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrd
  have hne : Set.Nonempty {s : ℝ | ∃ x y : Set.Icc a b,
      |(x : ℝ) - (y : ℝ)| ≤ r ∧ s = |f x - f y|} := by
    let z : Set.Icc a b := ⟨a, le_rfl, hab⟩
    exact ⟨0, z, z, by simpa using hr, by simp⟩
  apply lt_of_le_of_lt (csSup_le hne ?_) (show ε/2 < ε by linarith)
  rintro s ⟨x, y, hxy, rfl⟩
  have hdist : dist x y < δ := by
    simpa only [Subtype.dist_eq, Real.dist_eq] using hxy.trans_lt hrd
  have := h hdist
  exact le_of_lt (by simpa only [Real.dist_eq] using this)

theorem modulus_limit : Specs.SingleVariableAnalysis.Ch16.PiecewiseLinear.modulusLimit := by
  intro a b hab f
  apply Metric.tendsto_nhdsWithin_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := modulus_small hab f ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrd
  have hr' : 0 ≤ r := hr
  have hrδ : r < δ := by simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hr'] using hrd
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (modulus_nonneg f r)] using h r hr' hrδ

/-- The error of a convex combination is bounded by the two endpoint errors. -/
lemma affine_error (F A B t M : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hA : |F-A| ≤ M) (hB : |F-B| ≤ M) :
    |F - ((1-t)*A + t*B)| ≤ M := by
  calc
    |F - ((1-t)*A + t*B)| = |(1-t)*(F-A) + t*(F-B)| := by congr 1; ring
    _ ≤ |(1-t)*(F-A)| + |t*(F-B)| := abs_add_le _ _
    _ = (1-t)*|F-A| + t*|F-B| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht1), abs_of_nonneg ht]
    _ ≤ (1-t)*M + t*M := add_le_add
      (mul_le_mul_of_nonneg_left hA (sub_nonneg.mpr ht1))
      (mul_le_mul_of_nonneg_left hB ht)
    _ = M := by ring

lemma pointwise_error {a b : ℝ} (P : Partition a b) (f : C(Set.Icc a b, ℝ))
    (x : Set.Icc a b) : |f x - interpolant P f x| ≤ modulus f (mesh P) := by
  by_cases hn : P.n = 0
  · have hnode : (x : ℝ) = P.point 0 := by
      apply le_antisymm
      · calc
          (x : ℝ) ≤ b := x.property.2
          _ = P.point 0 := P.last.symm.trans (congrArg P.point (Fin.ext hn))
      · simpa only [P.first] using x.property.1
    have hx : x = node P 0 := Subtype.ext hnode
    rw [hx]
    change |f (node P 0) - interpolant P f (P.point 0)| ≤ _
    rw [show interpolant P f (P.point 0) = f (node P 0) from node_values P f 0]
    simpa using modulus_nonneg f (mesh P)
  · obtain ⟨i, hi⟩ := cell_cover P (Nat.pos_of_ne_zero hn) x.property
    change |f x - Specs.SingleVariableAnalysis.Ch16.PiecewiseLinear.interpolantValue P f x| ≤ _
    rw [cell_formula P f i (x : ℝ) hi]
    have hp : 0 < P.point i.succ - P.point i.castSucc := cell_positive P i
    have ht : 0 ≤ ((x : ℝ) - P.point i.castSucc) /
        (P.point i.succ - P.point i.castSucc) := div_nonneg (sub_nonneg.mpr hi.1) hp.le
    have ht1 : ((x : ℝ) - P.point i.castSucc) /
        (P.point i.succ - P.point i.castSucc) ≤ 1 :=
      (div_le_one₀ hp).mpr (by linarith [hi.2])
    apply affine_error _ _ _ _ _ ht ht1
    · apply modulus_controls
      change |(x : ℝ) - P.point i.castSucc| ≤ mesh P
      rw [abs_of_nonneg (sub_nonneg.mpr hi.1)]
      have hm := cellLength_le_mesh P i
      change P.point i.succ - P.point i.castSucc ≤ mesh P at hm
      linarith [hi.2]
    · apply modulus_controls
      change |(x : ℝ) - P.point i.succ| ≤ mesh P
      rw [abs_of_nonpos (sub_nonpos.mpr hi.2)]
      have hm := cellLength_le_mesh P i
      change P.point i.succ - P.point i.castSucc ≤ mesh P at hm
      linarith [hi.1]

lemma map_error_bound {a b : ℝ} (P : Partition a b) (f : C(Set.Icc a b, ℝ)) :
    ‖f - interpolantMap P f‖ ≤ modulus f (mesh P) := by
  apply ((f - interpolantMap P f).norm_le (modulus_nonneg f (mesh P))).mpr
  intro x
  change ‖f x - interpolant P f x‖ ≤ _
  simpa only [Real.norm_eq_abs] using pointwise_error P f x

theorem norm_bound : Specs.SingleVariableAnalysis.Ch16.PiecewiseLinear.normBound := by
  intro a b P f
  exact ⟨interpolantMap P f, fun _ => rfl, map_error_bound P f⟩

theorem approximation : Specs.SingleVariableAnalysis.Ch16.PiecewiseLinear.approximation := by
  intro a b hab f ε hε
  obtain ⟨δ, hδ, h⟩ := modulus_small hab f ε hε
  refine ⟨δ, hδ, ?_⟩
  intro P hP
  exact ⟨interpolantMap P f, fun _ => rfl,
    (map_error_bound P f).trans_lt (h (mesh P) (mesh_nonneg P) hP)⟩

theorem convergence : Specs.SingleVariableAnalysis.Ch16.PiecewiseLinear.convergence := by
  intro a b f P hP
  have hab : a ≤ b := by
    simpa only [(P 0).first, (P 0).last] using
      (P 0).strictMono.monotone (Fin.zero_le (Fin.last (P 0).n))
  have hmod : Filter.Tendsto (fun n => modulus f (mesh (P n))) Filter.atTop (𝓝 0) := by
    apply (modulus_limit hab f).comp
    exact tendsto_nhdsWithin_iff.mpr ⟨hP, Filter.Eventually.of_forall (fun n => mesh_nonneg (P n))⟩
  have hnorm : Filter.Tendsto (fun n => ‖f - interpolantMap (P n) f‖) Filter.atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun n => map_error_bound (P n) f) hmod
  refine ⟨fun n => interpolantMap (P n) f, fun _ _ => rfl, hnorm, ?_⟩
  apply (realSupSpace_norm_converges_iff_uniform (Set.Icc a b) (fun n => interpolantMap (P n) f) f).mp
  simpa only [norm_sub_rev] using hnorm

end SingleVariableAnalysis.PiecewiseLinear
