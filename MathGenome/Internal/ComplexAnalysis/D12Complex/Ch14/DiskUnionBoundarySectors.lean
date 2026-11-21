import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.DiskUnionBoundarySectors
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open Set Metric
open scoped Topology ComplexConjugate

namespace D12Complex.DiskUnionBoundarySectors

def diskUnion (s : Finset ℂ) (r : ℂ → ℝ) : Set ℂ :=
  ⋃ c ∈ s, ball c (r c)

def GeneralPosition (s : Finset ℂ) (r : ℂ → ℝ) : Prop :=
  (∀ c ∈ s, 0 < r c) ∧
  (∀ c ∈ s, ∀ d ∈ s, c ≠ d →
    dist c d ≠ r c + r d ∧ dist c d ≠ |r c - r d|) ∧
  (∀ c ∈ s, ∀ d ∈ s, ∀ e ∈ s, c ≠ d → c ≠ e → d ≠ e →
    ¬ ∃ z : ℂ, dist z c = r c ∧ dist z d = r d ∧ dist z e = r e)

def SectorChart (D : Set ℂ) (ξ : ℂ) (θ : ℝ) : Prop :=
  ∃ (U V : Set ℂ) (f g : ℂ → ℂ), ξ ∈ U ∧
    BiholomorphicPair U V f g ∧ f ξ = 0 ∧ deriv f ξ ≠ 0 ∧
    ∀ z ∈ U, z ∈ D ↔
      ∃ ρ : ℝ, 0 < ρ ∧ ∃ t : ℝ, 0 < t ∧ t < θ ∧
        f z = (ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I)

def BoundarySectors (D : Set ℂ) : Prop :=
  ∃ F : Set ℂ, F.Finite ∧ F ⊆ frontier D ∧
    (∀ ξ ∈ frontier D \ F, SectorChart D ξ Real.pi) ∧
    (∀ ξ ∈ F, ∃ θ : ℝ, 0 < θ ∧ θ < 2 * Real.pi ∧ SectorChart D ξ θ)


theorem isOpen_diskUnion (s : Finset ℂ) (r : ℂ → ℝ) : IsOpen (diskUnion s r) :=
  isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball

theorem boundary_not_mem (s : Finset ℂ) (r : ℂ → ℝ) {ξ : ℂ}
    (hξ : ξ ∈ frontier (diskUnion s r)) : ξ ∉ diskUnion s r :=
  fun h => (disjoint_frontier_iff_isOpen.mpr (isOpen_diskUnion s r)).le_bot ⟨hξ, h⟩

theorem boundary_active (s : Finset ℂ) (r : ℂ → ℝ) {ξ : ℂ}
    (hξ : ξ ∈ frontier (diskUnion s r)) : ∃ c ∈ s, dist ξ c = r c := by
  have h := s.frontier_biUnion_subset (fun c => ball c (r c)) hξ
  obtain ⟨c, hc, h⟩ := mem_iUnion₂.mp h
  exact ⟨c, hc, mem_sphere.mp (frontier_ball_subset_sphere h)⟩

/-- A finite intersection of neighborhoods excludes all inactive closed disks. -/
theorem inactive_disks_avoided (s : Finset ℂ) (r : ℂ → ℝ) {ξ : ℂ}
    (hξ : ξ ∈ frontier (diskUnion s r)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ ball ξ ε, ∀ c ∈ s,
      dist ξ c ≠ r c → z ∉ closedBall c (r c) := by
  have hout : ∀ c ∈ s, r c ≤ dist ξ c := by
    intro c hc
    by_contra h
    exact boundary_not_mem s r hξ (mem_iUnion₂.mpr ⟨c, hc, not_le.mp h⟩)
  let U : Set ℂ := ⋂ c ∈ s, {z : ℂ | dist ξ c ≠ r c → z ∉ closedBall c (r c)}
  have ho : IsOpen U := by
    apply isOpen_biInter_finset
    intro c hc
    by_cases he : dist ξ c = r c
    · simp [he]
    · simpa [he] using (isOpen_lt continuous_const (continuous_id.dist continuous_const : Continuous (fun z : ℂ => dist z c)))
  have hmem : ξ ∈ U := by
    simp only [U, mem_iInter]
    intro c hc he
    exact not_le.mpr (lt_of_le_of_ne (hout c hc) (Ne.symm he))
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp ho ξ hmem
  refine ⟨ε, hε, ?_⟩
  intro z hz c hc
  exact mem_iInter₂.mp (hεU hz) c hc

theorem local_boundary_disk_model :
    Specs.D12Complex.Ch14.DiskUnionBoundarySectors.local_boundary_disk_model_type := by
  intro s r hg ξ hξ
  obtain ⟨c, hc, hca⟩ := boundary_active s r hξ
  obtain ⟨ε, hε, havoid⟩ := inactive_disks_avoided s r hξ
  refine ⟨c, hc, hca, ε, hε, ?_⟩
  by_cases hd : ∃ d ∈ s, c ≠ d ∧ dist ξ d = r d
  · obtain ⟨d, hd, hcd, hda⟩ := hd
    right
    refine ⟨d, hd, hcd, hda, ?_⟩
    intro z hz
    constructor
    · intro h
      obtain ⟨e, he, hze⟩ := mem_iUnion₂.mp h
      by_cases hec : e = c
      · subst e; exact Or.inl hze
      by_cases hed : e = d
      · subst e; exact Or.inr hze
      have hena : dist ξ e ≠ r e := fun hea =>
        hg.2.2 c hc d hd e he hcd (Ne.symm hec) (Ne.symm hed) ⟨ξ, hca, hda, hea⟩
      exact False.elim (havoid z hz e he hena (ball_subset_closedBall hze))
    · rintro (h | h)
      · exact mem_iUnion₂.mpr ⟨c, hc, h⟩
      · exact mem_iUnion₂.mpr ⟨d, hd, h⟩
  · left
    intro z hz
    constructor
    · intro h
      obtain ⟨d, hd', hzd⟩ := mem_iUnion₂.mp h
      by_cases he : c = d
      · simpa [he] using hzd
      have hna : dist ξ d ≠ r d := fun h => hd ⟨d, hd', he, h⟩
      exact False.elim (havoid z hz d hd' hna (ball_subset_closedBall hzd))
    · intro h
      exact mem_iUnion₂.mpr ⟨c, hc, h⟩

/-- A unit direction in an open set contains a nontrivial angular cap.
The inequality here is exactly the one used by `LocalExteriorCone`. -/
theorem angular_cap_in_open (O : Set ℂ) (hO : IsOpen O) {e : ℂ}
    (he : e ∈ O) (hen : ‖e‖ = 1) :
    ∃ (q : ℂ) (β : ℝ), ‖q‖ = 1 ∧ 0 < β ∧ β < Real.pi ∧
      ∀ h : ℂ, (q * h).re < Real.cos β * ‖q * h‖ →
        h ≠ 0 ∧ h / (‖h‖ : ℂ) ∈ O := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO e he
  let δ := min ε 1
  have hδ : 0 < δ := lt_min hε zero_lt_one
  have hδε : δ ≤ ε := min_le_left _ _
  have hδ1 : δ ≤ 1 := min_le_right _ _
  let k := -1 + δ ^ 2 / 2
  have hklo : -1 < k := by dsimp [k]; nlinarith
  have hkhi : k < 1 := by dsimp [k]; nlinarith [sq_nonneg (δ - 1)]
  refine ⟨-conj e, Real.arccos k, by simpa using hen,
    Real.arccos_pos.mpr hkhi, Real.arccos_lt_pi.mpr hklo, ?_⟩
  intro h hh
  rw [Real.cos_arccos hklo.le hkhi.le] at hh
  have hqn : ‖-conj e * h‖ = ‖h‖ := by simp [hen]
  rw [hqn] at hh
  have hn : h ≠ 0 := by intro hzero; simp [hzero] at hh
  have hN : 0 < ‖h‖ := norm_pos_iff.mpr hn
  let u := h / (‖h‖ : ℂ)
  have hun : ‖u‖ = 1 := by simp [u, ne_of_gt hN]
  have hrec : (‖h‖ : ℂ) * u = h := by
    dsimp [u]; field_simp [ne_of_gt hN]
  have hh' : -(conj e * u).re < k := by
    have hid : (-conj e * h).re = -(conj e * u).re * ‖h‖ := by
      conv_lhs => rw [← hrec]
      simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im, sub_zero, zero_mul]
      ring
    rw [hid] at hh
    nlinarith
  have he2 : e.re ^ 2 + e.im ^ 2 = 1 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hen
    rw [Complex.sq_norm, Complex.normSq_apply] at h
    nlinarith
  have hu2 : u.re ^ 2 + u.im ^ 2 = 1 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hun
    rw [Complex.sq_norm, Complex.normSq_apply] at h
    nlinarith
  have hdist : ‖u - e‖ ^ 2 = 2 - 2 * (conj e * u).re := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.conj_re, Complex.conj_im]
    nlinarith
  have hclose : dist u e < ε := by
    rw [dist_eq_norm]
    dsimp [k] at hh'
    have hsq : ‖u - e‖ ^ 2 < δ ^ 2 := by nlinarith
    have hlt : ‖u - e‖ < δ := by nlinarith [norm_nonneg (u - e)]
    exact lt_of_lt_of_le hlt hδε
  exact ⟨hn, hball hclose⟩

/-- A strictly outward direction lies outside the whole disk, not just its
linearized tangent half-plane. -/
theorem not_mem_ball_of_outward {ξ c h : ℂ} {R : ℝ}
    (hR : 0 < R) (hc : dist ξ c = R)
    (hout : 0 < (conj (ξ - c) * h).re) : ξ + h ∉ ball c R := by
  have hc2 : (ξ - c).re ^ 2 + (ξ - c).im ^ 2 = R ^ 2 := by
    rw [dist_eq_norm] at hc
    have h := congrArg (fun t : ℝ => t ^ 2) hc
    rw [Complex.sq_norm, Complex.normSq_apply] at h
    nlinarith
  intro hz
  have hz2 : ‖ξ + h - c‖ ^ 2 < R ^ 2 := by
    have := mem_ball_iff_norm.mp hz
    nlinarith [norm_nonneg (ξ + h - c)]
  rw [Complex.sq_norm] at hz2
  have heq : ξ + h - c = (ξ - c) + h := by ring
  rw [heq] at hz2
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im] at hz2
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im] at hout
  nlinarith [sq_nonneg h.re, sq_nonneg h.im]

/-- Normalization of a nonzero complex vector. -/
theorem norm_normalize (a : ℂ) (ha : a ≠ 0) : ‖a / (‖a‖ : ℂ)‖ = 1 := by
  simp [ne_of_gt (norm_pos_iff.mpr ha)]

theorem real_mul_normalize (a h : ℂ) :
    (conj a * (h / (‖h‖ : ℂ))).re = (conj a * h).re / ‖h‖ := by
  rw [← mul_div_assoc]
  simp

/-- Two nonopposite outward normals admit a common strict outward unit direction. -/
theorem common_outward_direction {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hopp : ‖a - b‖ ≠ ‖a‖ + ‖b‖) :
    ∃ e : ℂ, ‖e‖ = 1 ∧ 0 < (conj a * e).re ∧ 0 < (conj b * e).re := by
  let u := a / (‖a‖ : ℂ)
  let v := b / (‖b‖ : ℂ)
  have hu : ‖u‖ = 1 := norm_normalize a ha
  have hv : ‖v‖ = 1 := norm_normalize b hb
  have hA : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hB : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hau : (‖a‖ : ℂ) * u = a := by dsimp [u]; field_simp [ne_of_gt hA]
  have hbv : (‖b‖ : ℂ) * v = b := by dsimp [v]; field_simp [ne_of_gt hB]
  have hw : u + v ≠ 0 := by
    intro h
    have hvu : v = -u := by linear_combination h
    have hab : a - b = ((‖a‖ + ‖b‖ : ℝ) : ℂ) * u := by
      calc
        a - b = (‖a‖ : ℂ) * u - (‖b‖ : ℂ) * v := congrArg₂ (· - ·) hau.symm hbv.symm
        _ = ((‖a‖ + ‖b‖ : ℝ) : ℂ) * u := by rw [hvu]; push_cast; ring
    apply hopp
    rw [hab, norm_mul, hu, mul_one, Complex.norm_real, Real.norm_of_nonneg (add_pos hA hB).le]
  have hu2 : u.re ^ 2 + u.im ^ 2 = 1 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hu
    rw [Complex.sq_norm, Complex.normSq_apply] at h
    nlinarith
  have hv2 : v.re ^ 2 + v.im ^ 2 = 1 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hv
    rw [Complex.sq_norm, Complex.normSq_apply] at h
    nlinarith
  have hw2 : 0 < (u + v).re ^ 2 + (u + v).im ^ 2 := by
    have h : 0 < ‖u + v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw)
    rw [Complex.sq_norm, Complex.normSq_apply] at h
    nlinarith
  have huv : 0 < 1 + u.re * v.re + u.im * v.im := by
    simp only [Complex.add_re, Complex.add_im] at hw2
    nlinarith
  refine ⟨(u + v) / (‖u + v‖ : ℂ), norm_normalize _ hw, ?_, ?_⟩
  · rw [real_mul_normalize]
    apply div_pos _ (norm_pos_iff.mpr hw)
    have hid : (conj a * (u + v)).re = ‖a‖ * (1 + u.re * v.re + u.im * v.im) := by
      conv_lhs => rw [← hau]
      simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im]
      nlinarith [hu2]
    rw [hid]; exact mul_pos hA huv
  · rw [real_mul_normalize]
    apply div_pos _ (norm_pos_iff.mpr hw)
    have hid : (conj b * (u + v)).re = ‖b‖ * (1 + u.re * v.re + u.im * v.im) := by
      conv_lhs => rw [← hbv]
      simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im]
      nlinarith [hv2]
    rw [hid]; exact mul_pos hB huv

/-- A strict common outward normal for the active disks gives the actual
upstream cone. Inactive disks are excluded on a positive-radius ball. -/
theorem exterior_cone_of_outward (s : Finset ℂ) (r : ℂ → ℝ) {ξ e : ℂ}
    (hr : ∀ c ∈ s, 0 < r c) (hξ : ξ ∈ frontier (diskUnion s r))
    (hen : ‖e‖ = 1)
    (he : ∀ c ∈ s, dist ξ c = r c → 0 < (conj (ξ - c) * e).re) :
    LocalExteriorCone (diskUnion s r) ξ := by
  let O : Set ℂ := ⋂ c ∈ s, {u : ℂ | dist ξ c = r c →
    0 < (conj (ξ - c) * u).re}
  have hO : IsOpen O := by
    apply isOpen_biInter_finset
    intro c hc
    by_cases h : dist ξ c = r c
    · have ho : IsOpen {u : ℂ | (0 : ℝ) < (conj (ξ - c) * u).re} :=
        isOpen_lt continuous_const (Complex.continuous_re.comp
          (continuous_const.mul continuous_id))
      simpa only [h, true_implies] using ho
    · simp [h]
  have heO : e ∈ O := mem_iInter₂.mpr he
  obtain ⟨q, β, hq, hβ, hβπ, hcap⟩ := angular_cap_in_open O hO heO hen
  obtain ⟨ε, hε, havoid⟩ := inactive_disks_avoided s r hξ
  refine ⟨q, β, ε, hq, hβ, hβπ, hε, ?_⟩
  intro z hz hangle hzin
  obtain ⟨hzn, hdir⟩ := hcap (z - ξ) hangle
  obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.mp hzin
  by_cases hca : dist ξ c = r c
  · have hpos := mem_iInter₂.mp hdir c hc hca
    change 0 < (conj (ξ - c) * ((z - ξ) / (‖z - ξ‖ : ℂ))).re at hpos
    rw [real_mul_normalize] at hpos
    have hpos' : 0 < (conj (ξ - c) * (z - ξ)).re :=
      (div_pos_iff_of_pos_right (norm_pos_iff.mpr hzn)).mp hpos
    have hnot := not_mem_ball_of_outward (hr c hc) hca hpos'
    exact hnot (by simpa using hzc)
  · exact havoid z hz c hc hca (ball_subset_closedBall hzc)

/-- Every general-position finite disk union has a genuine exterior cone at
all frontier points. This includes empty families and disconnected unions. -/
theorem disk_union_exterior_cones :
    Specs.D12Complex.Ch14.DiskUnionBoundarySectors.disk_union_exterior_cones_type := by
  intro s r hg ξ hξ
  obtain ⟨c, hc, hca⟩ := boundary_active s r hξ
  have hcn : ξ - c ≠ 0 := by
    intro h
    have : dist ξ c = 0 := by simp [dist_eq_norm, h]
    linarith [hg.1 c hc]
  by_cases hd : ∃ d ∈ s, c ≠ d ∧ dist ξ d = r d
  · obtain ⟨d, hd, hcd, hda⟩ := hd
    have hdn : ξ - d ≠ 0 := by
      intro h
      have : dist ξ d = 0 := by simp [dist_eq_norm, h]
      linarith [hg.1 d hd]
    have hopp : ‖(ξ - c) - (ξ - d)‖ ≠ ‖ξ - c‖ + ‖ξ - d‖ := by
      have heq : (ξ - c) - (ξ - d) = d - c := by ring
      rw [heq, ← dist_eq_norm, dist_comm d c, ← dist_eq_norm, ← dist_eq_norm,
        hca, hda]
      exact (hg.2.1 c hc d hd hcd).1
    obtain ⟨e, hen, hec, hed⟩ := common_outward_direction hcn hdn hopp
    apply exterior_cone_of_outward s r hg.1 hξ hen
    intro a ha haa
    by_cases hac : a = c
    · simpa [hac] using hec
    by_cases had : a = d
    · simpa [had] using hed
    exact False.elim (hg.2.2 c hc d hd a ha hcd (Ne.symm hac)
      (Ne.symm had) ⟨ξ, hca, hda, haa⟩)
  · have hepos : 0 < (conj (ξ - c) * ((ξ - c) / (‖ξ - c‖ : ℂ))).re := by
      rw [real_mul_normalize]
      apply div_pos _ (norm_pos_iff.mpr hcn)
      have : 0 < ‖ξ - c‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hcn)
      rw [Complex.sq_norm, Complex.normSq_apply] at this
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      nlinarith
    apply exterior_cone_of_outward s r hg.1 hξ (norm_normalize _ hcn)
    intro a ha haa
    by_cases hac : c = a
    · simpa [hac] using hepos
    exact False.elim (hd ⟨a, ha, hac, haa⟩)

/-- Explicit rational coordinates, with no appeal to a chapter-10 Möbius theorem. -/
theorem rational_chart (a b A : ℂ) (hab : a ≠ b) (hA : A ≠ 0) :
    BiholomorphicPair {z : ℂ | z ≠ b} {w : ℂ | w ≠ A}
      (fun z => A * (z - a) / (z - b))
      (fun w => (w * b - A * a) / (w - A)) := by
  let f := fun z => A * (z - a) / (z - b)
  let g := fun w => (w * b - A * a) / (w - A)
  have hf : ∀ z, z ≠ b → DifferentiableAt ℂ f z := by
    intro z hz
    exact ((differentiableAt_const A).mul (differentiableAt_id.sub_const a)).div
      (differentiableAt_id.sub_const b) (sub_ne_zero.mpr hz)
  have hg : ∀ w, w ≠ A → DifferentiableAt ℂ g w := by
    intro w hw
    exact ((differentiableAt_id.mul_const b).sub_const (A * a)).div
      (differentiableAt_id.sub_const A) (sub_ne_zero.mpr hw)
  have hfm : ∀ z, z ≠ b → f z ≠ A := by
    intro z hz he
    have h := (div_eq_iff (sub_ne_zero.mpr hz)).mp he
    have : A * (a - b) = 0 := by linear_combination -h
    exact (mul_ne_zero hA (sub_ne_zero.mpr hab)) this
  have hgm : ∀ w, w ≠ A → g w ≠ b := by
    intro w hw he
    have h := (div_eq_iff (sub_ne_zero.mpr hw)).mp he
    have : A * (a - b) = 0 := by linear_combination -h
    exact (mul_ne_zero hA (sub_ne_zero.mpr hab)) this
  refine ⟨⟨isOpen_ne_fun continuous_id continuous_const, fun z hz => hf z hz⟩,
    ⟨isOpen_ne_fun continuous_id continuous_const, fun w hw => hg w hw⟩,
    hfm, hgm, ?_, ?_⟩
  · intro z hz
    change g (f z) = z
    have hfz := sub_ne_zero.mpr (hfm z hz)
    change (f z * b - A * a) / (f z - A) = z
    apply (div_eq_iff hfz).mpr
    dsimp [f]
    field_simp [sub_ne_zero.mpr hz]
    ring
  · intro w hw
    change f (g w) = w
    have hgw := sub_ne_zero.mpr (hgm w hw)
    change A * (g w - a) / (g w - b) = w
    apply (div_eq_iff hgw).mpr
    dsimp [g]
    field_simp [sub_ne_zero.mpr hw]
    ring

/-- Restrict explicit inverse maps to an arbitrary smaller open source. -/
theorem restrict_biholomorphicPair {U V W : Set ℂ} {f g : ℂ → ℂ}
    (h : BiholomorphicPair U V f g) (hW : IsOpen W) (hWU : W ⊆ U) :
    BiholomorphicPair W (V ∩ g ⁻¹' W) f g := by
  have hg : ContinuousOn g V := fun w hw =>
    (h.2.1.2 w hw).continuousAt.continuousWithinAt
  have hopen : IsOpen (V ∩ g ⁻¹' W) := hg.isOpen_inter_preimage h.2.1.1 hW
  refine ⟨⟨hW, fun z hz => h.1.2 z (hWU hz)⟩,
    ⟨hopen, fun w hw => h.2.1.2 w hw.1⟩, ?_, fun _ hw => hw.2,
    fun z hz => h.2.2.2.2.1 (hWU hz), fun w hw => h.2.2.2.2.2 hw.1⟩
  intro z hz
  exact ⟨h.2.2.1 (hWU hz), by simpa [h.2.2.2.2.1 (hWU hz)] using hz⟩

theorem rational_chart_derivative (a b A z : ℂ) (hz : z ≠ b) :
    HasDerivAt (fun w => A * (w - a) / (w - b))
      (A * (a - b) / (z - b) ^ 2) z := by
  have h := (((hasDerivAt_id z).sub_const a).const_mul A).div
    ((hasDerivAt_id z).sub_const b) (sub_ne_zero.mpr hz)
  have heq : (A * 1 * (z - b) - A * (z - a) * 1) / (z - b) ^ 2 =
      A * (a - b) / (z - b) ^ 2 := by ring
  convert h using 1
  · rfl
  · simpa only [id_eq] using heq.symm

/-- Polar sector of opening π is exactly the upper half-plane. -/
theorem upper_half_plane_iff_polar (w : ℂ) : 0 < w.im ↔
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ t : ℝ, 0 < t ∧ t < Real.pi ∧
      w = (ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I) := by
  constructor
  · intro hw
    have hw0 : w ≠ 0 := by intro h; simp [h] at hw
    refine ⟨‖w‖, norm_pos_iff.mpr hw0, w.arg, ?_, ?_,
      (Complex.norm_mul_exp_arg_mul_I w).symm⟩
    · have hnonneg : 0 ≤ w.arg := Complex.arg_nonneg_iff.mpr hw.le
      by_contra hn
      have heq : w.arg = 0 := le_antisymm (not_lt.mp hn) hnonneg
      have hs := Complex.norm_mul_sin_arg w
      rw [heq, Real.sin_zero, mul_zero] at hs
      linarith
    · exact Complex.arg_lt_pi_iff.mpr (Or.inr (ne_of_gt hw))
  · rintro ⟨ρ, hρ, t, ht, htπ, rfl⟩
    rw [Complex.exp_mul_I]
    simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.mul_im,
      Complex.add_im, Complex.ofReal_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, zero_add, zero_mul, add_zero]
    exact mul_pos hρ (Real.sin_pos_of_pos_of_lt_pi ht htπ)

/-- The antipodal rational coordinate maps the actual disk side onto the
upper half-plane; this identity is valid at every nonpole point. -/
theorem disk_rational_im (c ξ z : ℂ) (R : ℝ) (hξ : dist ξ c = R)
    (_hz : z ≠ 2 * c - ξ) :
    (-Complex.I * (z - ξ) / (z - (2 * c - ξ))).im =
      (R ^ 2 - ‖z - c‖ ^ 2) / ‖z - (2 * c - ξ)‖ ^ 2 := by
  have he : ‖ξ - c‖ ^ 2 = R ^ 2 := by rw [← dist_eq_norm, hξ]
  rw [← Complex.normSq_eq_norm_sq] at he
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.normSq_apply] at he ⊢
  rw [← sub_div]
  congr 1
  nlinarith

/-- A disk has a conformal angle-π chart at every boundary point. -/
theorem disk_sector_chart (c ξ : ℂ) (R : ℝ) (hR : 0 < R)
    (hξ : dist ξ c = R) : SectorChart (ball c R) ξ Real.pi := by
  let η := 2 * c - ξ
  have hξη : ξ ≠ η := by
    intro h
    have hxc : ξ = c := by dsimp [η] at h; linear_combination h / 2
    have : R = 0 := by simpa [hxc] using hξ.symm
    linarith
  let f := fun z => -Complex.I * (z - ξ) / (z - η)
  let g := fun w => (w * η - -Complex.I * ξ) / (w - -Complex.I)
  have hp := rational_chart ξ η (-Complex.I) hξη (by simp)
  refine ⟨{z | z ≠ η}, {w | w ≠ -Complex.I}, f, g, hξη, hp, ?_, ?_, ?_⟩
  · simp [f]
  · have hd := rational_chart_derivative ξ η (-Complex.I) ξ hξη
    rw [hd.deriv]
    exact div_ne_zero (mul_ne_zero (by simp) (sub_ne_zero.mpr hξη))
      (pow_ne_zero _ (sub_ne_zero.mpr hξη))
  · intro z hz
    rw [← upper_half_plane_iff_polar]
    change z ∈ ball c R ↔ 0 < (-Complex.I * (z - ξ) / (z - η)).im
    rw [disk_rational_im c ξ z R hξ hz]
    have hden : 0 < ‖z - (2 * c - ξ)‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hz))
    rw [div_pos_iff_of_pos_right hden, mem_ball_iff_norm]
    constructor
    · intro h; nlinarith [norm_nonneg (z - c)]
    · intro h; nlinarith [norm_nonneg (z - c)]

/-- Sector charts are local: only the set equality on an open neighborhood
is required to transport a chart to another domain. -/
theorem sectorChart_of_local_eq {D E W : Set ℂ} {ξ : ℂ} {θ : ℝ}
    (h : SectorChart E ξ θ) (hW : IsOpen W) (hξ : ξ ∈ W)
    (hlocal : ∀ z ∈ W, z ∈ D ↔ z ∈ E) : SectorChart D ξ θ := by
  obtain ⟨U, V, f, g, hξU, hpair, hf0, hdf, heq⟩ := h
  have hnew := restrict_biholomorphicPair hpair (hpair.1.1.inter hW)
    (show U ∩ W ⊆ U from inter_subset_left)
  refine ⟨U ∩ W, V ∩ g ⁻¹' (U ∩ W), f, g, ⟨hξU, hξ⟩,
    hnew, hf0, hdf, ?_⟩
  intro z hz
  exact (hlocal z hz.2).trans (heq z hz.1)

/-- Two circles with distinct centers have at most two intersection points. -/
theorem finite_circle_intersection (c d : ℂ) (R S : ℝ) (hcd : c ≠ d) :
    {z : ℂ | dist z c = R ∧ dist z d = S}.Finite := by
  let X := {z : ℂ | dist z c = R ∧ dist z d = S}
  by_cases hx : X.Nonempty
  · obtain ⟨x, hx⟩ := hx
    by_cases hy : ∃ y ∈ X, y ≠ x
    · obtain ⟨y, hy, hyx⟩ := hy
      apply (Set.toFinite ({x, y} : Set ℂ)).subset
      intro z hz
      have he := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
        Complex.finrank_real_complex hcd (Ne.symm hyx) hx.1 hy.1 hz.1 hx.2 hy.2 hz.2
      simpa only [mem_insert_iff, mem_singleton_iff] using he
    · apply (Set.finite_singleton x).subset
      intro z hz
      exact mem_singleton_iff.mpr (by_contra fun h => hy ⟨z, hz, h⟩)
  · have he : X = ∅ := Set.not_nonempty_iff_eq_empty.mp hx
    simpa [X] using (he ▸ Set.finite_empty : X.Finite)

/-- The entire collection of double-circle points is finite. It may contain
points lying inside the union; intersection with the frontier selects corners. -/
theorem finite_double_points (s : Finset ℂ) (r : ℂ → ℝ) :
    {ξ : ℂ | ∃ c ∈ s, ∃ d ∈ s, c ≠ d ∧
      dist ξ c = r c ∧ dist ξ d = r d}.Finite := by
  let X := ⋃ c ∈ s, ⋃ d ∈ s.filter (fun d => c ≠ d),
    {ξ : ℂ | dist ξ c = r c ∧ dist ξ d = r d}
  have hX : X.Finite := by
    apply Set.Finite.biUnion s.finite_toSet
    intro c hc
    apply Set.Finite.biUnion (s.filter (fun d => c ≠ d)).finite_toSet
    intro d hd
    exact finite_circle_intersection c d (r c) (r d) (Finset.mem_filter.mp hd).2
  apply hX.subset
  rintro ξ ⟨c, hc, d, hd, hcd, hξc, hξd⟩
  exact mem_iUnion₂.mpr ⟨c, hc,
    mem_iUnion₂.mpr ⟨d, Finset.mem_filter.mpr ⟨hd, hcd⟩, hξc, hξd⟩⟩

/-- All nondouble boundary points have actual conformal angle-π charts. -/
theorem sectors_away_from_double_points (s : Finset ℂ) (r : ℂ → ℝ)
    (hg : GeneralPosition s r) :
    ∃ F : Set ℂ, F.Finite ∧ F ⊆ frontier (diskUnion s r) ∧
      (∀ ξ ∈ frontier (diskUnion s r) \ F,
        SectorChart (diskUnion s r) ξ Real.pi) := by
  let X := {ξ : ℂ | ∃ c ∈ s, ∃ d ∈ s, c ≠ d ∧
    dist ξ c = r c ∧ dist ξ d = r d}
  let F := frontier (diskUnion s r) ∩ X
  refine ⟨F, (finite_double_points s r).subset inter_subset_right,
    inter_subset_left, ?_⟩
  intro ξ hξ
  obtain ⟨c, hc, hca, ε, hε, hmodel⟩ := local_boundary_disk_model s r hg ξ hξ.1
  have hsingle : ∀ z ∈ ball ξ ε, z ∈ diskUnion s r ↔ z ∈ ball c (r c) := by
    rcases hmodel with h | ⟨d, hd, hcd, hda, h⟩
    · exact h
    · exact False.elim (hξ.2 ⟨hξ.1, c, hc, d, hd, hcd, hca, hda⟩)
  exact sectorChart_of_local_eq (disk_sector_chart c ξ (r c) (hg.1 c hc) hca)
    isOpen_ball (mem_ball_self hε) hsingle

private theorem polar_im (ρ t : ℝ) :
    ((ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I)).im = ρ * Real.sin t := by
  rw [Complex.exp_mul_I]
  simp [← Complex.ofReal_sin, ← Complex.ofReal_cos]

private theorem sin_nonpos_on_second_half {t : ℝ}
    (ht : Real.pi ≤ t) (ht2 : t ≤ 2 * Real.pi) : Real.sin t ≤ 0 := by
  have h := Real.sin_nonpos_of_nonpos_of_neg_pi_le
    (show t - 2 * Real.pi ≤ 0 by linarith)
    (show -Real.pi ≤ t - 2 * Real.pi by linarith)
  simpa using h

private theorem union_sine_iff {φ t : ℝ} (hφ : 0 < φ) (hφπ : φ < Real.pi)
    (ht : 0 < t) (ht2 : t ≤ 2 * Real.pi) :
    (0 < Real.sin t ∨ 0 < Real.sin (t - φ)) ↔ t < Real.pi + φ := by
  constructor
  · intro h
    by_contra hn
    have hlow : Real.pi + φ ≤ t := not_lt.mp hn
    have h₁ := sin_nonpos_on_second_half (show Real.pi ≤ t by linarith) ht2
    have h₂ := sin_nonpos_on_second_half (show Real.pi ≤ t - φ by linarith)
      (show t - φ ≤ 2 * Real.pi by linarith)
    rcases h with h | h <;> linarith
  · intro h
    by_cases htπ : t < Real.pi
    · exact Or.inl (Real.sin_pos_of_pos_of_lt_pi ht htπ)
    · right
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

private theorem polar_coefficient (p : ℂ) (ρ t φ : ℝ) (hφ : φ = -p.arg) :
    p * ((ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) =
      ((‖p‖ * ρ : ℝ) : ℂ) * Complex.exp (((t - φ : ℝ) : ℂ) * Complex.I) := by
  have hp := Complex.norm_mul_exp_arg_mul_I p
  calc
    p * ((ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) =
        ((‖p‖ : ℂ) * Complex.exp ((p.arg : ℂ) * Complex.I)) *
          ((ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) := by rw [hp]
    _ = ((‖p‖ * ρ : ℝ) : ℂ) * Complex.exp (((t - φ : ℝ) : ℂ) * Complex.I) := by
      rw [hφ]
      push_cast
      rw [sub_neg_eq_add, add_mul, Complex.exp_add]
      ring

/-- A union of two appropriately ordered half-planes is a genuine reentrant
polar sector. The argument proves the exact set equality, including the rays. -/
theorem union_halfplanes_sector {p : ℂ} (hp : p.im < 0) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 2 * Real.pi ∧ ∀ w : ℂ,
      (0 < w.im ∨ 0 < (p * w).im) ↔
      ∃ ρ : ℝ, 0 < ρ ∧ ∃ t : ℝ, 0 < t ∧ t < θ ∧
        w = (ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I) := by
  let φ := -p.arg
  have hφ : 0 < φ := neg_pos.mpr (Complex.arg_neg_iff.mpr hp)
  have hφπ : φ < Real.pi := by dsimp [φ]; linarith [Complex.neg_pi_lt_arg p]
  have hpn : p ≠ 0 := by intro h; simp [h] at hp
  have hnp : 0 < ‖p‖ := norm_pos_iff.mpr hpn
  refine ⟨Real.pi + φ, by positivity, by linarith, ?_⟩
  intro w
  have hpolar : ∀ (ρ t : ℝ) (_ : 0 < ρ) (_ : 0 < t) (_ : t ≤ 2 * Real.pi),
      (0 < ((ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I)).im ∨
        0 < (p * ((ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I))).im) ↔
        t < Real.pi + φ := by
    intro ρ t hρ ht ht2
    rw [polar_coefficient p ρ t φ rfl, polar_im, polar_im,
      mul_pos_iff_of_pos_left hρ, mul_pos_iff_of_pos_left (mul_pos hnp hρ)]
    exact union_sine_iff hφ hφπ ht ht2
  constructor
  · intro hw
    have hw0 : w ≠ 0 := by intro h; simp [h] at hw
    let t := (-w).arg + Real.pi
    have ht : 0 < t := by dsimp [t]; linarith [Complex.neg_pi_lt_arg (-w)]
    have ht2 : t ≤ 2 * Real.pi := by dsimp [t]; linarith [Complex.arg_le_pi (-w)]
    have hwpolar : w = (‖w‖ : ℂ) * Complex.exp ((t : ℂ) * Complex.I) := by
      dsimp [t]
      push_cast
      rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
      have he := Complex.norm_mul_exp_arg_mul_I (-w)
      rw [norm_neg] at he
      linear_combination he
    refine ⟨‖w‖, norm_pos_iff.mpr hw0, t, ht, ?_, hwpolar⟩
    apply (hpolar ‖w‖ t (norm_pos_iff.mpr hw0) ht ht2).mp
    simpa only [← hwpolar] using hw
  · rintro ⟨ρ, hρ, t, ht, htθ, rfl⟩
    exact (hpolar ρ t hρ ht (by linarith)).mpr htθ

/-- Nontangency is exactly what is needed for independence of the two normals. -/
theorem two_circle_transverse {c d ξ : ℂ} {R S : ℝ}
    (hR : 0 < R) (hS : 0 < S) (hξc : dist ξ c = R) (hξd : dist ξ d = S)
    (hext : dist c d ≠ R + S) (hint : dist c d ≠ |R - S|) :
    (ξ - c).re * (ξ - d).im - (ξ - c).im * (ξ - d).re ≠ 0 := by
  let a := ξ - c
  let b := ξ - d
  let dot := a.re * b.re + a.im * b.im
  have ha2 : a.re ^ 2 + a.im ^ 2 = R ^ 2 := by
    have : ‖a‖ ^ 2 = R ^ 2 := by rw [← dist_eq_norm, hξc]
    rw [Complex.sq_norm, Complex.normSq_apply] at this
    nlinarith
  have hb2 : b.re ^ 2 + b.im ^ 2 = S ^ 2 := by
    have : ‖b‖ ^ 2 = S ^ 2 := by rw [← dist_eq_norm, hξd]
    rw [Complex.sq_norm, Complex.normSq_apply] at this
    nlinarith
  intro hdet
  have hdot : dot ^ 2 = (R * S) ^ 2 := by
    calc
      dot ^ 2 = (a.re ^ 2 + a.im ^ 2) * (b.re ^ 2 + b.im ^ 2) -
          (a.re * b.im - a.im * b.re) ^ 2 := by dsimp [dot]; ring
      _ = (R * S) ^ 2 := by rw [ha2, hb2, hdet]; ring
  have hdist : dist c d ^ 2 = R ^ 2 + S ^ 2 - 2 * dot := by
    have he : c - d = b - a := by dsimp [a, b]; ring
    rw [dist_eq_norm, he, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    dsimp [dot]
    nlinarith [ha2, hb2]
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hdot with h | h
  · apply hint
    rw [h] at hdist
    nlinarith [dist_nonneg (x := c) (y := d), abs_nonneg (R - S), sq_abs (R - S)]
  · apply hext
    rw [h] at hdist
    nlinarith [dist_nonneg (x := c) (y := d)]

/-- Solve the two real linear equations for a common circle-straightening
rational denominator. -/
theorem simultaneous_straightening_coefficient {a b : ℂ}
    (hdet : a.re * b.im - a.im * b.re ≠ 0) :
    ∃ K : ℂ, 2 * (a * K).re = 1 ∧ 2 * (b * K).re = 1 := by
  let Δ := a.re * b.im - a.im * b.re
  refine ⟨⟨(b.im - a.im) / (2 * Δ), (b.re - a.re) / (2 * Δ)⟩, ?_, ?_⟩
  · change 2 * (a.re * ((b.im - a.im) / (2 * Δ)) -
        a.im * ((b.re - a.re) / (2 * Δ))) = 1
    calc
      _ = (a.re * (b.im - a.im) - a.im * (b.re - a.re)) / Δ := by ring
      _ = 1 := by apply (div_eq_iff hdet).mpr; ring
  · change 2 * (b.re * ((b.im - a.im) / (2 * Δ)) -
        b.im * ((b.re - a.re) / (2 * Δ))) = 1
    calc
      _ = (b.re * (b.im - a.im) - b.im * (b.re - a.re)) / Δ := by ring
      _ = 1 := by apply (div_eq_iff hdet).mpr; ring

/-- The rational coordinate sends the full quadratic circle-side inequality
to a strict linear inequality. -/
theorem straightening_real_identity (a K h : ℂ) (hK : 2 * (a * K).re = 1) :
    2 * (conj a * (h / (1 + K * h))).re =
      (‖h‖ ^ 2 + 2 * (conj a * h).re) / ‖1 + K * h‖ ^ 2 := by
  rw [← mul_div_assoc, Complex.div_re, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq]
  rw [← add_div, ← mul_div_assoc]
  congr 1
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im] at hK ⊢
  linear_combination (h.re ^ 2 + h.im ^ 2) * hK

/-- Actual disk membership in the straightening coordinate. -/
theorem straightening_disk_side (ξ c K z : ℂ) (R : ℝ) (hR : 0 < R)
    (hξ : dist ξ c = R) (hK : 2 * ((ξ - c) * K).re = 1)
    (hz : 1 + K * (z - ξ) ≠ 0) :
    z ∈ ball c R ↔
      0 < (-Complex.I * conj (ξ - c) * ((z - ξ) / (1 + K * (z - ξ)))).im := by
  have he : ‖z - c‖ ^ 2 - R ^ 2 = ‖z - ξ‖ ^ 2 +
      2 * (conj (ξ - c) * (z - ξ)).re := by
    have hnorm : ‖ξ - c‖ ^ 2 = R ^ 2 := by rw [← dist_eq_norm, hξ]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.conj_re, Complex.conj_im] at hnorm ⊢
    nlinarith
  have hden : 0 < ‖1 + K * (z - ξ)‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hid := straightening_real_identity (ξ - c) K (z - ξ) hK
  rw [← he] at hid
  have him : (-Complex.I * conj (ξ - c) * ((z - ξ) / (1 + K * (z - ξ)))).im =
      -(conj (ξ - c) * ((z - ξ) / (1 + K * (z - ξ)))).re := by
    rw [mul_assoc]
    simp
  rw [him, mem_ball_iff_norm]
  have hnorm : 0 ≤ ‖z - c‖ := norm_nonneg _
  constructor
  · intro h
    have : (‖z - c‖ ^ 2 - R ^ 2) / ‖1 + K * (z - ξ)‖ ^ 2 < 0 :=
      div_neg_of_neg_of_pos (by nlinarith) hden
    linarith
  · intro h
    have : (‖z - c‖ ^ 2 - R ^ 2) / ‖1 + K * (z - ξ)‖ ^ 2 < 0 := by linarith
    have := (div_lt_iff₀ hden).mp this
    nlinarith

/-- The simultaneous circle-straightening map, including its explicit inverse
and the full open neighborhoods on which both maps are holomorphic. -/
theorem straightening_chart (ξ K C : ℂ) (hC : C ≠ 0) :
    BiholomorphicPair {z : ℂ | 1 + K * (z - ξ) ≠ 0}
      {w : ℂ | C - K * w ≠ 0}
      (fun z => C * (z - ξ) / (1 + K * (z - ξ)))
      (fun w => ξ + w / (C - K * w)) := by
  let f := fun z => C * (z - ξ) / (1 + K * (z - ξ))
  let g := fun w => ξ + w / (C - K * w)
  have hfm : ∀ z, 1 + K * (z - ξ) ≠ 0 → C - K * f z ≠ 0 := by
    intro z hz hn
    have hid : (C - K * f z) * (1 + K * (z - ξ)) = C := by
      dsimp [f]; field_simp [hz]; ring
    rw [hn, zero_mul] at hid
    exact hC hid.symm
  have hgm : ∀ w, C - K * w ≠ 0 → 1 + K * (g w - ξ) ≠ 0 := by
    intro w hw hn
    have hid : (1 + K * (g w - ξ)) * (C - K * w) = C := by
      dsimp [g]; field_simp [hw]; ring
    rw [hn, zero_mul] at hid
    exact hC hid.symm
  have hU : IsOpen {z : ℂ | 1 + K * (z - ξ) ≠ 0} :=
    isOpen_ne_fun (continuous_const.add (continuous_const.mul
      (continuous_id.sub continuous_const))) continuous_const
  have hV : IsOpen {w : ℂ | C - K * w ≠ 0} :=
    isOpen_ne_fun (continuous_const.sub (continuous_const.mul continuous_id)) continuous_const
  refine ⟨⟨hU, ?_⟩, ⟨hV, ?_⟩, hfm, hgm, ?_, ?_⟩
  · intro z hz
    exact ((differentiableAt_id.sub_const ξ).const_mul C).div
      (((differentiableAt_id.sub_const ξ).const_mul K).const_add 1) hz
  · intro w hw
    have hd : DifferentiableAt ℂ (fun y : ℂ => C - K * y) w :=
      (differentiableAt_id.const_mul K).const_sub C
    exact ((differentiableAt_id : DifferentiableAt ℂ (fun y : ℂ => y) w).div hd hw).const_add ξ
  · intro z hz
    have hinv : f z / (C - K * f z) = z - ξ := by
      apply (div_eq_iff (hfm z hz)).mpr
      have hid : f z * (1 + K * (z - ξ)) = C * (z - ξ) :=
        div_mul_cancel₀ _ hz
      linear_combination hid
    change ξ + f z / (C - K * f z) = z
    rw [hinv]; ring
  · intro w hw
    change C * (g w - ξ) / (1 + K * (g w - ξ)) = w
    apply (div_eq_iff (hgm w hw)).mpr
    have hid : (g w - ξ) * (C - K * w) = w := by
      dsimp [g]; rw [add_sub_cancel_left, div_mul_cancel₀ _ hw]
    linear_combination hid

theorem straightening_chart_derivative (ξ K C z : ℂ)
    (hz : 1 + K * (z - ξ) ≠ 0) :
    HasDerivAt (fun w => C * (w - ξ) / (1 + K * (w - ξ)))
      (C / (1 + K * (z - ξ)) ^ 2) z := by
  have h := (((hasDerivAt_id z).sub_const ξ).const_mul C).div
    ((((hasDerivAt_id z).sub_const ξ).const_mul K).const_add 1) hz
  convert h using 1
  · rfl
  · dsimp; ring

/-- A two-disk corner when the half-plane sides have been ordered counterclockwise. -/
theorem two_disk_sector_chart_ordered {c d ξ : ℂ} {R S : ℝ}
    (hR : 0 < R) (hS : 0 < S) (hξc : dist ξ c = R) (hξd : dist ξ d = S)
    (hdet : (ξ - c).re * (ξ - d).im - (ξ - c).im * (ξ - d).re ≠ 0)
    (hp : (conj (ξ - d) / conj (ξ - c)).im < 0) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 2 * Real.pi ∧
      SectorChart (ball c R ∪ ball d S) ξ θ := by
  let a := ξ - c
  let b := ξ - d
  have ha : a ≠ 0 := by
    intro h
    have : dist ξ c = 0 := by simpa [a, dist_eq_norm] using congrArg norm h
    linarith
  let C := -Complex.I * conj a
  have hC : C ≠ 0 := mul_ne_zero (by simp) (by simpa using ha)
  obtain ⟨K, hKa, hKb⟩ := simultaneous_straightening_coefficient hdet
  let f := fun z => C * (z - ξ) / (1 + K * (z - ξ))
  let g := fun w => ξ + w / (C - K * w)
  have hpair := straightening_chart ξ K C hC
  obtain ⟨θ, hθ, hθ2, hpolar⟩ := union_halfplanes_sector hp
  refine ⟨θ, hθ, hθ2, {z | 1 + K * (z - ξ) ≠ 0},
    {w | C - K * w ≠ 0}, f, g, by simp, hpair, by simp [f], ?_, ?_⟩
  · have hd := straightening_chart_derivative ξ K C ξ (by simp)
    rw [hd.deriv]
    simpa using hC
  · intro z hz
    rw [← hpolar]
    have hc := straightening_disk_side ξ c K z R hR hξc hKa hz
    have hd := straightening_disk_side ξ d K z S hS hξd hKb hz
    have hfa : f z = -Complex.I * conj (ξ - c) *
        ((z - ξ) / (1 + K * (z - ξ))) := by dsimp [f, C, a]; ring
    have hfb : (conj (ξ - d) / conj (ξ - c)) * f z =
        -Complex.I * conj (ξ - d) * ((z - ξ) / (1 + K * (z - ξ))) := by
      have hconj : conj (ξ - c) ≠ 0 := by
        change conj a ≠ 0
        simpa only [map_ne_zero] using ha
      rw [hfa]
      calc
        _ = (-Complex.I * ((z - ξ) / (1 + K * (z - ξ)))) *
            ((conj (ξ - d) / conj (ξ - c)) * conj (ξ - c)) := by ring
        _ = _ := by rw [div_mul_cancel₀ _ hconj]; ring
    rw [hfb, hfa]
    exact or_congr hc hd

private theorem ratio_im_neg_of_det_pos {a b : ℂ} (ha : a ≠ 0)
    (hd : 0 < a.re * b.im - a.im * b.re) : (conj b / conj a).im < 0 := by
  have hn : 0 < Complex.normSq (conj a) := by
    rw [Complex.normSq_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (by simpa using ha))
  simp only [Complex.div_im, Complex.conj_re, Complex.conj_im]
  rw [← sub_div]
  exact div_neg_of_neg_of_pos (by nlinarith) hn

/-- A transverse two-circle boundary has a conformal sector chart, including
its exact curved disk-side membership before applying the rational coordinate. -/
theorem two_disk_sector_chart {c d ξ : ℂ} {R S : ℝ}
    (hR : 0 < R) (hS : 0 < S) (hξc : dist ξ c = R) (hξd : dist ξ d = S)
    (hext : dist c d ≠ R + S) (hint : dist c d ≠ |R - S|) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 2 * Real.pi ∧
      SectorChart (ball c R ∪ ball d S) ξ θ := by
  have hdet := two_circle_transverse hR hS hξc hξd hext hint
  have hcn : ξ - c ≠ 0 := by
    intro h
    have : dist ξ c = 0 := by simp [dist_eq_norm, h]
    linarith
  have hdn : ξ - d ≠ 0 := by
    intro h
    have : dist ξ d = 0 := by simp [dist_eq_norm, h]
    linarith
  by_cases hd : 0 < (ξ - c).re * (ξ - d).im - (ξ - c).im * (ξ - d).re
  · exact two_disk_sector_chart_ordered hR hS hξc hξd hdet
      (ratio_im_neg_of_det_pos hcn hd)
  · have hdneg := lt_of_le_of_ne (not_lt.mp hd) hdet
    have hds : 0 < (ξ - d).re * (ξ - c).im - (ξ - d).im * (ξ - c).re := by
      nlinarith
    obtain ⟨θ, hθ, hθ2, hchart⟩ := two_disk_sector_chart_ordered hS hR hξd hξc
      (ne_of_gt hds) (ratio_im_neg_of_det_pos hdn hds)
    exact ⟨θ, hθ, hθ2, by simpa only [union_comm] using hchart⟩

/-- Complete sector geometry for the disk arrangement. -/
theorem disk_union_boundary_sectors :
    Specs.D12Complex.Ch14.DiskUnionBoundarySectors.disk_union_boundary_sectors_type := by
  intro s r hg
  refine ⟨?_, disk_union_exterior_cones s r hg⟩
  obtain ⟨F, hF, hFbd, hregular⟩ := sectors_away_from_double_points s r hg
  refine ⟨F, hF, hFbd, hregular, ?_⟩
  intro ξ hξF
  have hξ := hFbd hξF
  obtain ⟨c, hc, hca, ε, hε, hmodel⟩ := local_boundary_disk_model s r hg ξ hξ
  rcases hmodel with hsingle | ⟨d, hd, hcd, hda, hdouble⟩
  · refine ⟨Real.pi, Real.pi_pos, by linarith [Real.pi_pos], ?_⟩
    exact sectorChart_of_local_eq (disk_sector_chart c ξ (r c) (hg.1 c hc) hca)
      isOpen_ball (mem_ball_self hε) hsingle
  · obtain ⟨θ, hθ, hθ2, hchart⟩ := two_disk_sector_chart (hg.1 c hc) (hg.1 d hd)
      hca hda (hg.2.1 c hc d hd hcd).1 (hg.2.1 c hc d hd hcd).2
    exact ⟨θ, hθ, hθ2, sectorChart_of_local_eq hchart isOpen_ball
      (mem_ball_self hε) hdouble⟩

end D12Complex.DiskUnionBoundarySectors
