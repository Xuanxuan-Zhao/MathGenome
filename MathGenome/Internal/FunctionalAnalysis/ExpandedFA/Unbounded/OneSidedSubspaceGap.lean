import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.OneSidedSubspaceGap
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01RieszLemma
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith

/-!
One-sided subspace gaps (`fa2:p3:subspace-gap`, paper.tex:14216–14250).

The gap is the supremum of distance over the closed unit ball. Its operator
norm realization gives the homogeneous distance estimate. Quotient norming
functionals and norm-preserving Hahn–Banach identify the two gap suprema;
no bidual identification or reflexivity assumption enters the proof.
Riesz's lemma is applied inside the larger subspace for proper inclusions.
The helpers also establish the conclusions without ambient completeness.
-/

namespace ExpandedFA.Unbounded.OneSidedSubspaceGap

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

noncomputable def gap : Spec.GapType := Spec.gapValue

def annihilator : Spec.AnnihilatorType := Spec.annihilatorValue

lemma infDist_le_norm (N : Submodule 𝕜 X) (x : X) :
    Metric.infDist x (N : Set X) ≤ ‖x‖ := by
  simpa using (Metric.infDist_le_dist_of_mem (x := x) N.zero_mem)

lemma gap_set_nonempty (M N : Submodule 𝕜 X) :
    {r : ℝ | ∃ x : X, x ∈ M ∧ ‖x‖ ≤ 1 ∧ r = Metric.infDist x (N : Set X)}.Nonempty :=
  ⟨_, 0, M.zero_mem, by simp, rfl⟩

lemma gap_set_bddAbove (M N : Submodule 𝕜 X) :
    BddAbove {r : ℝ | ∃ x : X, x ∈ M ∧ ‖x‖ ≤ 1 ∧ r = Metric.infDist x (N : Set X)} := by
  refine ⟨1, ?_⟩
  rintro r ⟨x, hx, hn, rfl⟩
  exact (infDist_le_norm N x).trans hn

lemma gap_nonneg (M N : Submodule 𝕜 X) : 0 ≤ gap M N := by
  exact le_trans Metric.infDist_nonneg
    (le_csSup (gap_set_bddAbove M N) ⟨0, M.zero_mem, by simp, rfl⟩)

lemma gap_le_one (M N : Submodule 𝕜 X) : gap M N ≤ 1 := by
  apply csSup_le (gap_set_nonempty M N)
  rintro r ⟨x, hx, hn, rfl⟩
  exact (infDist_le_norm N x).trans hn

lemma infDist_le_gap (M N : Submodule 𝕜 X) {x : X} (hx : x ∈ M) (hn : ‖x‖ ≤ 1) :
    Metric.infDist x (N : Set X) ≤ gap M N :=
  le_csSup (gap_set_bddAbove M N) ⟨x, hx, hn, rfl⟩

lemma gap_le (M N : Submodule 𝕜 X) {c : ℝ}
    (h : ∀ x ∈ M, ‖x‖ ≤ 1 → Metric.infDist x (N : Set X) ≤ c) : gap M N ≤ c := by
  apply csSup_le (gap_set_nonempty M N)
  rintro r ⟨x, hx, hn, rfl⟩
  exact h x hx hn

lemma norm_mkQL (N : Submodule 𝕜 X) (x : X) :
    ‖N.mkQL x‖ = Metric.infDist x (N : Set X) := by
  exact QuotientAddGroup.norm_mk (S := N.toAddSubgroup) x

lemma gap_eq_opNorm (M N : Submodule 𝕜 X) :
    gap M N = ‖N.mkQL.comp M.subtypeL‖ := by
  apply le_antisymm
  · apply gap_le
    intro x hx hn
    rw [← norm_mkQL]
    exact (N.mkQL.comp M.subtypeL).unit_le_opNorm (x := ⟨x, hx⟩) hn
  · apply ContinuousLinearMap.opNorm_le_of_unit_norm (gap_nonneg M N)
    intro x hn
    exact (norm_mkQL N x).trans_le (infDist_le_gap M N x.property hn.le)

lemma infDist_le_gap_mul_norm (M N : Submodule 𝕜 X) {x : X} (hx : x ∈ M) :
    Metric.infDist x (N : Set X) ≤ gap M N * ‖x‖ := by
  rw [gap_eq_opNorm, ← norm_mkQL]
  exact (N.mkQL.comp M.subtypeL).le_opNorm ⟨x, hx⟩

/-- A unit dual functional on the quotient detects the distance to a subspace.
This works for the seminormed quotient and so does not need closedness. -/
lemma exists_distance_functional (N : Submodule 𝕜 X) (x : X) :
    ∃ f : X →L[𝕜] 𝕜, f ∈ annihilator N ∧ ‖f‖ ≤ 1 ∧
      ‖f x‖ = Metric.infDist x (N : Set X) := by
  obtain ⟨g, hg, hgx⟩ := exists_dual_vector'' 𝕜 (N.mkQL x)
  refine ⟨g.comp N.mkQL, ?_, ?_, ?_⟩
  · intro y hy
    change g (Submodule.Quotient.mk y : X ⧸ N) = 0
    rw [(Submodule.Quotient.mk_eq_zero N).2 hy, map_zero]
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y
    calc
      ‖g (N.mkQL y)‖ ≤ ‖N.mkQL y‖ := by simpa using g.le_of_opNorm_le hg (N.mkQL y)
      _ ≤ ‖y‖ := by rw [norm_mkQL]; exact infDist_le_norm N y
      _ = 1 * ‖y‖ := (one_mul _).symm
  · change ‖g (N.mkQL x)‖ = _
    rw [hgx, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _), norm_mkQL]

/-- Restricting a functional identifies its distance to the annihilator.
The upper estimate uses norm-preserving Hahn–Banach on the original space. -/
lemma infDist_annihilator (M : Submodule 𝕜 X) (f : X →L[𝕜] 𝕜) :
    Metric.infDist f (annihilator M : Set (X →L[𝕜] 𝕜)) = ‖f.comp M.subtypeL‖ := by
  apply le_antisymm
  · obtain ⟨F, hF, hFnorm⟩ := exists_extension_norm_eq M (f.comp M.subtypeL)
    have ha : f - F ∈ annihilator M := by
      intro x hx
      change f x - F x = 0
      exact sub_eq_zero.mpr (hF ⟨x, hx⟩).symm
    calc
      Metric.infDist f (annihilator M : Set (X →L[𝕜] 𝕜)) ≤ dist f (f - F) :=
        Metric.infDist_le_dist_of_mem ha
      _ = ‖F‖ := by rw [dist_eq_norm]; congr 1; abel
      _ = ‖f.comp M.subtypeL‖ := hFnorm
  · apply (Metric.le_infDist ⟨0, (annihilator M).zero_mem⟩).2
    intro a ha
    rw [dist_eq_norm]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have hx : a x = 0 := ha x x.property
    simpa [ContinuousLinearMap.comp_apply, map_sub, hx] using (f - a).le_opNorm (x : X)

lemma annihilator_apply_le (N : Submodule 𝕜 X) {f : X →L[𝕜] 𝕜}
    (hf : f ∈ annihilator N) (x : X) :
    ‖f x‖ ≤ ‖f‖ * Metric.infDist x (N : Set X) := by
  by_cases hzero : ‖f‖ = 0
  · have : f = 0 := norm_eq_zero.mp hzero
    simp [this]
  have hpos : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg f) (Ne.symm hzero)
  have hdiv : ‖f x‖ / ‖f‖ ≤ Metric.infDist x (N : Set X) := by
    apply (Metric.le_infDist ⟨0, N.zero_mem⟩).2
    intro y hy
    apply (div_le_iff₀ hpos).2
    simpa [map_sub, hf y hy, dist_eq_norm, mul_comm] using f.le_opNorm (x - y)
  nlinarith [(div_le_iff₀ hpos).1 hdiv]

lemma gap_annihilator_eq (M N : Submodule 𝕜 X) :
    gap M N = gap (annihilator N) (annihilator M) := by
  apply le_antisymm
  · apply gap_le
    intro x hx hn
    obtain ⟨f, hf, hfn, hfx⟩ := exists_distance_functional N x
    calc
      Metric.infDist x (N : Set X) = ‖f x‖ := hfx.symm
      _ ≤ ‖f.comp M.subtypeL‖ :=
        (f.comp M.subtypeL).unit_le_opNorm (x := ⟨x, hx⟩) hn
      _ = Metric.infDist f (annihilator M : Set (X →L[𝕜] 𝕜)) :=
        (infDist_annihilator M f).symm
      _ ≤ gap (annihilator N) (annihilator M) := infDist_le_gap _ _ hf hfn
  · apply gap_le
    intro f hf hn
    rw [infDist_annihilator]
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (gap_nonneg M N)
    intro x hx
    calc
      ‖f x‖ ≤ ‖f‖ * Metric.infDist (x : X) (N : Set X) := annihilator_apply_le N hf x
      _ ≤ 1 * gap M N := mul_le_mul hn (infDist_le_gap M N x.property hx.le)
        Metric.infDist_nonneg zero_le_one
      _ = gap M N := one_mul _

lemma gap_triangle (M N L : Submodule 𝕜 X) :
    gap M L ≤ gap M N + gap N L + gap M N * gap N L := by
  apply gap_le
  intro x hx hxn
  apply le_of_forall_pos_le_add
  intro ε hε
  let η := ε / (gap N L + 1)
  have hb := gap_nonneg N L
  have hden : 0 < gap N L + 1 := by linarith
  have hη : 0 < η := div_pos hε hden
  have hηeq : η * (gap N L + 1) = ε := div_mul_cancel₀ ε (ne_of_gt hden)
  obtain ⟨y, hy, hxy⟩ := (Metric.infDist_lt_iff ⟨0, N.zero_mem⟩).1
    (lt_add_of_pos_right (Metric.infDist x (N : Set X)) hη)
  have hdist : dist x y ≤ gap M N + η := by
    linarith [infDist_le_gap M N hx hxn]
  have hyn : ‖y‖ ≤ 1 + dist x y := by
    calc
      ‖y‖ ≤ ‖x‖ + ‖y - x‖ := norm_le_insert' y x
      _ ≤ 1 + dist x y := by rw [← dist_eq_norm, dist_comm y x]; linarith
  have hL : Metric.infDist x (L : Set X) ≤ gap N L * ‖y‖ + dist x y := by
    calc
      Metric.infDist x (L : Set X) ≤ Metric.infDist y (L : Set X) + dist x y :=
        Metric.infDist_le_infDist_add_dist
      _ ≤ gap N L * ‖y‖ + dist x y := add_le_add (infDist_le_gap_mul_norm N L hy) le_rfl
  have hmul := mul_le_mul_of_nonneg_left hyn hb
  have hmul' := mul_le_mul_of_nonneg_left hdist (le_of_lt hden)
  nlinarith

lemma gap_eq_one_of_lt (M N : Submodule 𝕜 X) (hN : IsClosed (N : Set X))
    (hNM : N < M) : gap M N = 1 := by
  apply le_antisymm (gap_le_one M N)
  by_contra! hgap
  obtain ⟨θ, hθgap, hθone⟩ := exists_between hgap
  have hθpos : 0 < θ := (gap_nonneg M N).trans_lt hθgap
  let P : Submodule 𝕜 M := N.comap M.subtype
  have hPclosed : IsClosed (P : Set M) := hN.preimage continuous_subtype_val
  have hPproper : P ≠ ⊤ := by
    intro hP
    have hMN : M ≤ N := by
      intro x hx
      have : (⟨x, hx⟩ : M) ∈ P := by rw [hP]; trivial
      exact this
    exact (not_le_of_gt hNM) hMN
  obtain ⟨x, hxn, hx⟩ := ExpandedFA.P1.C01RieszLemma.riesz_lemma 𝕜 M P
    hPproper hPclosed θ hθpos hθone
  have hsets : Subtype.val '' (P : Set M) = (N : Set X) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y, hNM.le hy⟩, hy, rfl⟩
  have hdist : Metric.infDist (x : X) (N : Set X) = Metric.infDist x (P : Set M) := by
    rw [← hsets]
    exact Metric.infDist_image isometry_subtype_coe
  have hbound := infDist_le_gap M N x.property hxn.le
  rw [hdist] at hbound
  linarith

theorem bounds : Spec.Bounds := by
  intro 𝕜 X _ _ _ _ M N _ _
  exact ⟨gap_nonneg M N, gap_le_one M N⟩

theorem annihilator_duality : Spec.AnnihilatorDuality := by
  intro 𝕜 X _ _ _ _ M N _ _
  exact gap_annihilator_eq M N

theorem triangle_estimate : Spec.TriangleEstimate := by
  intro 𝕜 X _ _ _ _ M N L _ _ _
  exact gap_triangle M N L

theorem proper_inclusion : Spec.ProperInclusion := by
  intro 𝕜 X _ _ _ _ M N _ hN hNM
  exact gap_eq_one_of_lt M N hN hNM

end ExpandedFA.Unbounded.OneSidedSubspaceGap
