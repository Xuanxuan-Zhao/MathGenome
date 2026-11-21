import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.LogisticCantor
import MathGenome.Internal.ODEDynamics.D13Unified.Ch17.InverseBranchCoding
import MathGenome.Internal.ODEDynamics.D13Unified.Ch15.LogisticFixedPoints
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
namespace D13Unified.Ch17.LogisticCantor
open Set Topology NNReal
open D13Unified.Ch17.ShiftSpaces
open D13Unified.Ch17.InverseCodingConstruction
open D13Unified.Ch17.ChaosDefinitions
open D13Unified.Ch15.LogisticFixedPoints (logisticMap)

abbrev branchZero := Specs.D13Unified.Ch17.LogisticCantor.branchZero
abbrev branchOne := Specs.D13Unified.Ch17.LogisticCantor.branchOne
abbrev contractionRate := Specs.D13Unified.Ch17.LogisticCantor.contractionRate

lemma radicand_pos {μ u : ℝ} (hμ : 5 ≤ μ) (hu : u ∈ Icc (0 : ℝ) 1) :
    0 < 1 - 4 * u / μ := by
  have hp : 0 < μ := by linarith
  have : 4 * u / μ < 1 := (div_lt_one hp).mpr (by linarith [hu.2])
  linarith

lemma sqrt_bounds {μ u : ℝ} (hμ : 5 ≤ μ) (hu : u ∈ Icc (0 : ℝ) 1) :
    0 < Real.sqrt (1 - 4 * u / μ) ∧ Real.sqrt (1 - 4 * u / μ) ≤ 1 := by
  refine ⟨Real.sqrt_pos.mpr (radicand_pos hμ hu), ?_⟩
  apply Real.sqrt_le_one.mpr
  have : 0 ≤ 4 * u / μ := div_nonneg (by linarith [hu.1]) (by linarith)
  linarith

lemma branch_mem {μ u : ℝ} (hμ : 5 ≤ μ) (hu : u ∈ Icc (0 : ℝ) 1) :
    branchZero μ u ∈ Icc (0 : ℝ) 1 ∧ branchOne μ u ∈ Icc (0 : ℝ) 1 ∧
    branchZero μ u < 1 / 2 ∧ 1 / 2 < branchOne μ u := by
  obtain ⟨hp, hle⟩ := sqrt_bounds hμ hu
  dsimp [branchZero, branchOne, Specs.D13Unified.Ch17.LogisticCantor.branchZero,
    Specs.D13Unified.Ch17.LogisticCantor.branchOne]
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
    by linarith, by linarith⟩

lemma branch_inverse {μ u : ℝ} (hμ : 5 ≤ μ) (hu : u ∈ Icc (0 : ℝ) 1) :
    logisticMap μ (branchZero μ u) = u ∧ logisticMap μ (branchOne μ u) = u := by
  have hs := Real.sq_sqrt (radicand_pos hμ hu).le
  have hμ0 : μ ≠ 0 := by linarith
  have he : μ * (Real.sqrt (1 - 4 * u / μ)) ^ 2 = μ - 4 * u := by
    rw [hs]; field_simp
  dsimp [logisticMap, Specs.D13Unified.Ch15.LogisticFixedPoints.logisticMap,
    branchZero, branchOne, Specs.D13Unified.Ch17.LogisticCantor.branchZero,
    Specs.D13Unified.Ch17.LogisticCantor.branchOne]
  constructor <;> nlinarith [he]

lemma rate_bounds {μ : ℝ} (hμ : 5 ≤ μ) :
    0 < contractionRate μ ∧ contractionRate μ ≤ 1 / Real.sqrt 5 ∧
      (1 : ℝ) / Real.sqrt 5 < 1 := by
  have hm : 5 ≤ μ * (μ - 4) := by nlinarith
  have hp : 0 < Real.sqrt (μ * (μ - 4)) := Real.sqrt_pos.mpr (by linarith)
  have h5 : 1 < Real.sqrt (5 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg (5 : ℝ)]
  dsimp [contractionRate, Specs.D13Unified.Ch17.LogisticCantor.contractionRate]
  exact ⟨one_div_pos.mpr hp, one_div_le_one_div_of_le (by positivity)
    (Real.sqrt_le_sqrt hm), (div_lt_one (by positivity)).mpr h5⟩

/-- A uniform positive lower bound on the denominator after rationalizing
the difference of square roots. -/
lemma scaled_sqrt_lower {μ u : ℝ} (hμ : 5 ≤ μ) (hu : u ∈ Icc (0 : ℝ) 1) :
    Real.sqrt (μ * (μ - 4)) ≤ μ * Real.sqrt (1 - 4 * u / μ) := by
  have hp : 0 < μ := by linarith
  have he : μ ^ 2 * (1 - 4 / μ) = μ * (μ - 4) := by
    field_simp
  calc
    Real.sqrt (μ * (μ - 4)) = Real.sqrt (μ ^ 2 * (1 - 4 / μ)) := by rw [he]
    _ = μ * Real.sqrt (1 - 4 / μ) := by
      rw [Real.sqrt_mul (sq_nonneg μ), Real.sqrt_sq hp.le]
    _ ≤ μ * Real.sqrt (1 - 4 * u / μ) := by
      apply mul_le_mul_of_nonneg_left _ hp.le
      apply Real.sqrt_le_sqrt
      have : 4 * u / μ ≤ 4 / μ := (div_le_div_iff_of_pos_right hp).mpr (by linarith [hu.2])
      linarith

lemma sqrt_difference_bound {μ u v : ℝ} (hμ : 5 ≤ μ)
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    |Real.sqrt (1 - 4 * u / μ) - Real.sqrt (1 - 4 * v / μ)| / 2 ≤
      contractionRate μ * |u - v| := by
  have hp : 0 < μ := by linarith
  let a := Real.sqrt (1 - 4 * u / μ)
  let c := Real.sqrt (1 - 4 * v / μ)
  let R := Real.sqrt (μ * (μ - 4))
  have hR : 0 < R := Real.sqrt_pos.mpr (mul_pos hp (by linarith))
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have has : a ^ 2 = 1 - 4 * u / μ := Real.sq_sqrt (radicand_pos hμ hu).le
  have hcs : c ^ 2 = 1 - 4 * v / μ := Real.sq_sqrt (radicand_pos hμ hv).le
  have he : μ * (a - c) * (a + c) = -4 * (u - v) := by
    calc
      μ * (a - c) * (a + c) = μ * (a ^ 2 - c ^ 2) := by ring
      _ = -4 * (u - v) := by rw [has, hcs]; field_simp; ring
  have habs := congrArg abs he
  simp only [abs_mul, abs_of_pos hp, abs_of_nonneg (add_nonneg ha hc),
    abs_neg] at habs
  norm_num at habs
  have hden : 2 * R ≤ μ * (a + c) := by
    have hu' := scaled_sqrt_lower hμ hu
    have hv' := scaled_sqrt_lower hμ hv
    change R ≤ μ * a at hu'
    change R ≤ μ * c at hv'
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hden (abs_nonneg (a - c))
  have hfinal : |a - c| / 2 * R ≤ |u - v| := by nlinarith [habs]
  change |a - c| / 2 ≤ (1 / R) * |u - v|
  rw [one_div_mul_eq_div, le_div_iff₀ hR]
  exact hfinal

lemma branch_difference_bound {μ u v : ℝ} (hμ : 5 ≤ μ)
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    |branchZero μ u - branchZero μ v| ≤ contractionRate μ * |u - v| ∧
    |branchOne μ u - branchOne μ v| ≤ contractionRate μ * |u - v| := by
  have h := sqrt_difference_bound hμ hu hv
  have h0 : branchZero μ u - branchZero μ v =
      -(Real.sqrt (1 - 4 * u / μ) - Real.sqrt (1 - 4 * v / μ)) / 2 := by
    dsimp [branchZero, Specs.D13Unified.Ch17.LogisticCantor.branchZero]; ring
  have h1 : branchOne μ u - branchOne μ v =
      (Real.sqrt (1 - 4 * u / μ) - Real.sqrt (1 - 4 * v / μ)) / 2 := by
    dsimp [branchOne, Specs.D13Unified.Ch17.LogisticCantor.branchOne]; ring
  constructor <;> simpa only [h0, h1, abs_div, abs_neg, show |(2 : ℝ)| = 2 by norm_num] using h


theorem branch_properties :
    Specs.D13Unified.Ch17.LogisticCantor.branch_propertiesStatement := by
  intro μ hμ
  let b : Binary → Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 := fun i u =>
    if i = 0 then ⟨branchZero μ u, (branch_mem hμ u.property).1⟩
    else ⟨branchOne μ u, (branch_mem hμ u.property).2.1⟩
  have hb : ∀ i u, (b i u : ℝ) = if i = 0 then branchZero μ u else branchOne μ u := by
    intro i u; dsimp [b]; split <;> rfl
  have hside : ∀ u, (b 0 u : ℝ) < 1 / 2 ∧ 1 / 2 < (b 1 u : ℝ) := by
    intro u
    simpa [b] using (branch_mem hμ u.property).2.2
  have hinv : ∀ i u, logisticMap μ (b i u) = (u : ℝ) := by
    intro i u
    rw [hb]; split
    · exact (branch_inverse hμ u.property).1
    · exact (branch_inverse hμ u.property).2
  obtain ⟨hqpos, hqle, hq5⟩ := rate_bounds hμ
  let q : ℝ≥0 := ⟨contractionRate μ, hqpos.le⟩
  refine ⟨b, q, rfl, hqpos, hqle, hq5, hb, hside, hinv, ?_, ?_, ?_⟩
  · intro i
    apply LipschitzWith.of_dist_le_mul
    intro u v
    change |(b i u : ℝ) - (b i v : ℝ)| ≤ (q : ℝ) * |(u : ℝ) - (v : ℝ)|
    rw [hb, hb]
    split
    · exact (branch_difference_bound hμ u.property v.property).1
    · exact (branch_difference_bound hμ u.property v.property).2
  · intro i u v he
    apply Subtype.ext
    rw [← hinv i u, ← hinv i v, he]
  · rw [Set.disjoint_left]
    rintro x ⟨u, rfl⟩ ⟨v, he⟩
    have h0 := (hside u).1
    have h1 := (hside v).2
    rw [he] at h1
    linarith

theorem logistic_cantor :
    Specs.D13Unified.Ch17.LogisticCantor.logistic_cantorStatement := by
  intro μ hμ
  obtain ⟨b, q, hq, hqpos, hqle, hq5, hb, hside, hinv, hlip, hinj, hdisj⟩ :=
    branch_properties μ hμ
  let K := Icc (0 : ℝ) 1
  let F : ↥(Set.univ : Set ℝ) → ℝ := fun x => logisticMap μ x
  have hFc : Continuous F := by
    dsimp [F, logisticMap, Specs.D13Unified.Ch15.LogisticFixedPoints.logisticMap]
    exact (continuous_const.mul continuous_subtype_val).mul
      (continuous_const.sub continuous_subtype_val)
  obtain ⟨hcomp, _, _, hL, f, π, hfval, hfcont, hfsurj, hrange, hh, _, _⟩ :=
    InverseBranchCoding.ambient_inverse_branch_coding K isCompact_Icc
      (by exact ⟨0, by norm_num [K]⟩) b q (lt_of_le_of_lt hqle hq5)
      hlip hinj hdisj Set.univ isOpen_univ F hFc
      (by intro i x; trivial) (by intro i x; exact hinv i x)
  let Λ : Set ℝ := Subtype.val '' limitSet b
  let e : limitSet b ≃ₜ Λ :=
    Topology.IsEmbedding.subtypeVal.homeomorphImage (limitSet b)
  have heval (x : limitSet b) : (e x : ℝ) = ((x : K) : ℝ) := rfl
  let π' : OneSided ≃ₜ Λ := π.trans e
  let g : Λ → Λ := fun x => e (f (e.symm x))
  have hgval : ∀ x : Λ, (g x : ℝ) = logisticMap μ x := by
    intro x
    change (e (f (e.symm x)) : ℝ) = logisticMap μ x
    rw [heval, hfval]
    change logisticMap μ ((e.symm x : K) : ℝ) = logisticMap μ x
    rw [← heval, e.apply_symm_apply]
  have hgcont : Continuous g :=
    e.continuous.comp (hfcont.comp e.symm.continuous)
  have hgsurj : Function.Surjective g :=
    e.surjective.comp (hfsurj.comp e.symm.surjective)
  have hsemi : Function.Semiconj π' shiftPlus g := by
    intro s
    change e (π (shiftPlus s)) = e (f (e.symm (e (π s))))
    rw [e.symm_apply_apply, hh]
  refine ⟨Λ, ?_, ?_, hcomp, InverseBranchCoding.no_isolated_of_shift π',
    π'.totallyDisconnectedSpace, ?_, g, π', hgval, hgcont, hgsurj,
    fun s => (hsemi s).symm, InverseBranchCoding.chaotic_of_shift_conjugacy π' g hsemi⟩
  · exact ⟨(π' (fun _ => 0) : ℝ), (π' (fun _ => 0)).property⟩
  · rintro x ⟨u, hu, rfl⟩
    exact u.property
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change logisticMap μ x ∈ Λ
      rw [← hgval ⟨x, hx⟩]
      exact (g ⟨x, hx⟩).property
    · intro hy
      obtain ⟨x, hx⟩ := hgsurj ⟨y, hy⟩
      refine ⟨x, x.property, ?_⟩
      change logisticMap μ x = y
      rw [← hgval x, hx]

theorem midpoint : Specs.D13Unified.Ch17.LogisticCantor.midpointStatement := by
  intro μ hμ
  constructor
  · dsimp [Specs.D13Unified.Ch15.LogisticFixedPoints.logisticMap]; ring
  · linarith

theorem interval_not_invariant :
    Specs.D13Unified.Ch17.LogisticCantor.interval_not_invariantStatement := by
  intro μ hμ hinv
  have h := hinv (mem_image_of_mem _ (show (1 / 2 : ℝ) ∈ Icc 0 1 by norm_num))
  have hm := midpoint μ hμ
  rw [hm.1] at h
  exact (not_le_of_gt hm.2) h.2

end D13Unified.Ch17.LogisticCantor
