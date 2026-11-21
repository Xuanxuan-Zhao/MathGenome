import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.BernsteinExtremes
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C24KreinMilman
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# The normalized compact-extreme stage of Bernstein's theorem

For `fa2:p1:bernstein` (paper.tex:5534–5567). The proof uses the given
product topology and the upstream real Krein–Milman theorem. Multiplicativity
follows directly from the extreme-point decomposition, including its two
boundary cases. The monotone Cauchy equation is proved by floor estimates,
so no continuity assumption at zero or representation theorem is needed.
-/

noncomputable section

open scoped NNReal

namespace ExpandedFA.P1.Bernstein

open Set

@[simp] theorem difference_nil (f : FunctionSpace) : alternatingDifference [] f = f := rfl
@[simp] theorem difference_cons (h : ℝ≥0) (hs : List ℝ≥0) (f : FunctionSpace) (t : ℝ≥0) :
    alternatingDifference (h :: hs) f t =
      alternatingDifference hs f t - alternatingDifference hs f (t + h) := rfl

theorem difference_linear (hs : List ℝ≥0) (f g : FunctionSpace) (a b : ℝ) (t : ℝ≥0) :
    alternatingDifference hs (fun s => a * f s + b * g s) t =
      a * alternatingDifference hs f t + b * alternatingDifference hs g t := by
  induction hs generalizing t with
  | nil => rfl
  | cons h hs ih => simp only [difference_cons, ih]; ring

theorem difference_shift (hs : List ℝ≥0) (f : FunctionSpace) (a t : ℝ≥0) :
    alternatingDifference hs (fun s => f (s + a)) t = alternatingDifference hs f (t + a) := by
  induction hs generalizing t with
  | nil => rfl
  | cons h hs ih => simp only [difference_cons, ih, add_right_comm t h a]

theorem difference_continuous (hs : List ℝ≥0) (t : ℝ≥0) :
    Continuous (fun f : FunctionSpace => alternatingDifference hs f t) := by
  induction hs generalizing t with
  | nil => exact continuous_apply t
  | cons h hs ih => exact (ih t).sub (ih (t + h))

theorem normalized_iff : Specs.ExpandedFA.P1.BernsteinExtremes.differenceCharacterizationType := by
  intro f
  constructor
  · exact fun h => ⟨h.1, h.2.2⟩
  · rintro ⟨h0, hd⟩
    refine ⟨h0, fun t => ⟨hd [] t, ?_⟩, hd⟩
    have := hd [t] 0
    simp only [difference_cons, difference_nil, zero_add, h0] at this
    linarith

theorem difference_zero_of_mem (hs : List ℝ≥0) (f : FunctionSpace) (hz : 0 ∈ hs) (t : ℝ≥0) :
    alternatingDifference hs f t = 0 := by
  induction hs generalizing t with
  | nil => simp at hz
  | cons h hs ih =>
    rcases List.mem_cons.mp hz with rfl | hz
    · simp
    · simp only [difference_cons, ih hz, sub_self]

theorem normalized_iff_positive :
    Specs.ExpandedFA.P1.BernsteinExtremes.positiveIncrementCharacterizationType := by
  intro f
  constructor
  · intro hf
    exact ⟨hf.1, fun hs _ t => hf.2.2 hs t⟩
  · rintro ⟨h0, hd⟩
    apply (normalized_iff f).mpr
    refine ⟨h0, fun hs t => ?_⟩
    by_cases hz : 0 ∈ hs
    · rw [difference_zero_of_mem hs f hz t]
    · apply hd hs _ t
      intro h hh
      exact pos_iff_ne_zero.mpr (fun heq => hz (heq ▸ hh))

theorem antitone_of_mem {f : FunctionSpace} (hf : f ∈ normalizedFunctions) : Antitone f := by
  intro s t hst
  have := hf.2.2 [t - s] s
  simpa only [difference_cons, difference_nil, add_tsub_cancel_of_le hst, sub_nonneg] using this

theorem normalized_closed : IsClosed normalizedFunctions := by
  have h0 : IsClosed {f : FunctionSpace | f 0 = 1} := isClosed_eq (continuous_apply 0) continuous_const
  have hb : IsClosed {f : FunctionSpace | ∀ t, f t ∈ Icc (0 : ℝ) 1} :=
    by
      simp only [ofPred_forall]
      exact isClosed_iInter fun t => isClosed_Icc.preimage (continuous_apply t)
  have hd : IsClosed {f : FunctionSpace | ∀ hs t, 0 ≤ alternatingDifference hs f t} :=
    by
      simp only [ofPred_forall]
      exact isClosed_iInter fun hs => isClosed_iInter fun t =>
        isClosed_le continuous_const (difference_continuous hs t)
  exact h0.inter (hb.inter hd)

theorem normalized_compact : IsCompact normalizedFunctions := by
  apply (isCompact_pi_infinite fun _ : ℝ≥0 => isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset
    normalized_closed
  intro f hf t
  exact hf.2.1 t

theorem normalized_convex : Convex ℝ normalizedFunctions := by
  intro f hf g hg a b ha hb hab
  apply (normalized_iff _).mpr
  refine ⟨?_, fun hs t => ?_⟩
  · change a * f 0 + b * g 0 = 1
    rw [hf.1, hg.1, mul_one, mul_one, hab]
  · change 0 ≤ alternatingDifference hs (fun t => a * f t + b * g t) t
    rw [difference_linear]
    exact add_nonneg (mul_nonneg ha (hf.2.2 hs t)) (mul_nonneg hb (hg.2.2 hs t))

theorem difference_of_multiplicative (f : FunctionSpace)
    (hmul : ∀ s t, f (s + t) = f s * f t) (hs : List ℝ≥0) (t : ℝ≥0) :
    alternatingDifference hs f t = f t * (hs.map fun h => 1 - f h).prod := by
  induction hs generalizing t with
  | nil => simp
  | cons h hs ih => simp only [difference_cons, List.map_cons, List.prod_cons, ih, hmul]; ring

theorem mem_of_multiplicative (f : FunctionSpace) (h0 : f 0 = 1)
    (hb : ∀ t, f t ∈ Icc (0 : ℝ) 1) (hmul : ∀ s t, f (s + t) = f s * f t) :
    f ∈ normalizedFunctions := by
  refine ⟨h0, hb, fun hs t => ?_⟩
  rw [difference_of_multiplicative f hmul]
  apply mul_nonneg (hb t).1
  apply List.prod_nonneg
  intro x hx
  obtain ⟨h, _, rfl⟩ := List.mem_map.mp hx
  exact sub_nonneg.mpr (hb h).2

theorem finiteExponential_mem (rate : ℝ≥0) : finiteExponential rate ∈ normalizedFunctions := by
  apply mem_of_multiplicative
  · simp [finiteExponential]
  · intro t
    exact ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr (by nlinarith [rate.coe_nonneg, t.coe_nonneg])⟩
  · intro s t
    simp only [finiteExponential, NNReal.coe_add, mul_add, Real.exp_add]

theorem finiteExponential_zero : Specs.ExpandedFA.P1.BernsteinExtremes.constantOneType := by
  ext t
  simp [finiteExponential]

theorem infinityExponential_mem : infinityExponential ∈ normalizedFunctions := by
  apply mem_of_multiplicative
  · simp [infinityExponential]
  · intro t; by_cases ht : t = 0 <;> simp [infinityExponential, ht]
  · intro s t
    by_cases hs : s = 0 <;> by_cases ht : t = 0 <;> simp [infinityExponential, hs, ht]

theorem exponential_membership : Specs.ExpandedFA.P1.BernsteinExtremes.exponentialMembershipType := by
  rintro f (rfl | ⟨rate, rfl⟩)
  · exact infinityExponential_mem
  · exact finiteExponential_mem rate

theorem normalized_compact_convex : Specs.ExpandedFA.P1.BernsteinExtremes.compactConvexType :=
  ⟨⟨infinityExponential, infinityExponential_mem⟩, normalized_compact, normalized_convex⟩

/-- A compact parameterization with r = exp(-rate); r = 0 is the infinity endpoint. -/
def powerFunction (r : ℝ) : FunctionSpace := fun t => r ^ (t : ℝ)

theorem powerFunction_zero : powerFunction 0 = infinityExponential := by
  ext t
  by_cases ht : t = 0
  · simp [powerFunction, infinityExponential, ht]
  · simp [powerFunction, infinityExponential, ht, Real.zero_rpow (NNReal.coe_ne_zero.mpr ht)]

theorem powerFunction_exp (rate : ℝ≥0) :
    powerFunction (Real.exp (-(rate : ℝ))) = finiteExponential rate := by
  ext t
  exact (Real.exp_mul _ _).symm

theorem exponentials_eq_image : exponentials = powerFunction '' Icc (0 : ℝ) 1 := by
  ext f
  constructor
  · rintro (rfl | ⟨rate, rfl⟩)
    · exact ⟨0, by simp, powerFunction_zero⟩
    · exact ⟨Real.exp (-(rate : ℝ)),
        ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr rate.coe_nonneg)⟩,
        powerFunction_exp rate⟩
  · rintro ⟨r, hr, rfl⟩
    by_cases h0 : r = 0
    · exact Or.inl (h0 ▸ powerFunction_zero)
    · right
      have hpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm h0)
      let rate : ℝ≥0 := ⟨-Real.log r, neg_nonneg.mpr (Real.log_nonpos hr.1 hr.2)⟩
      refine ⟨rate, ?_⟩
      ext t
      change r ^ (t : ℝ) = Real.exp (-(-Real.log r) * (t : ℝ))
      rw [neg_neg, Real.rpow_def_of_pos hpos]

theorem exponentials_compact : Specs.ExpandedFA.P1.BernsteinExtremes.compactExponentialsType := by
  rw [Specs.ExpandedFA.P1.BernsteinExtremes.compactExponentialsType, exponentials_eq_image]
  apply isCompact_Icc.image
  exact continuous_pi fun t => Real.continuous_rpow_const t.coe_nonneg

theorem difference_div (hs : List ℝ≥0) (f : FunctionSpace) (c : ℝ) (t : ℝ≥0) :
    alternatingDifference hs (fun s => f s / c) t = alternatingDifference hs f t / c := by
  induction hs generalizing t with
  | nil => rfl
  | cons h hs ih => simp only [difference_cons, ih, sub_div]

theorem difference_sub (hs : List ℝ≥0) (f g : FunctionSpace) (t : ℝ≥0) :
    alternatingDifference hs (fun s => f s - g s) t =
      alternatingDifference hs f t - alternatingDifference hs g t := by
  simpa [sub_eq_add_neg] using difference_linear hs f g 1 (-1) t

/-- The extremal decomposition works for every intermediate value, without an
extra regularity premise at zero. The boundary values follow from first and
second differences. -/
theorem extreme_multiplicative {f : FunctionSpace}
    (he : f ∈ C24FacesSpec.extremePoints normalizedFunctions) :
    ∀ t a, f (t + a) = f t * f a := by
  have hf := he.1
  have hanti := antitone_of_mem hf
  intro t a
  by_cases ha0 : f a = 0
  · have hle : f (t + a) ≤ f a := hanti (le_add_left le_rfl)
    rw [ha0, mul_zero]
    exact le_antisymm (ha0 ▸ hle) (hf.2.1 _).1
  by_cases ha1 : f a = 1
  · have hsecond := hf.2.2 [a, t] 0
    simp only [difference_cons, difference_nil, zero_add, hf.1, ha1, add_comm a t] at hsecond
    rw [ha1, mul_one]
    exact le_antisymm (hanti (le_add_right le_rfl)) (by linarith)
  have hapos : 0 < f a := lt_of_le_of_ne (hf.2.1 a).1 (Ne.symm ha0)
  have halt : f a < 1 := lt_of_le_of_ne (hf.2.1 a).2 ha1
  let h : FunctionSpace := fun s => f (s + a) / f a
  let g : FunctionSpace := fun s => (f s - f (s + a)) / (1 - f a)
  have hh : h ∈ normalizedFunctions := by
    apply (normalized_iff _).mpr
    refine ⟨by dsimp [h]; rw [zero_add, div_self ha0], ?_⟩
    intro hs s
    dsimp [h]
    rw [difference_div, difference_shift]
    exact div_nonneg (hf.2.2 _ _) hapos.le
  have hg : g ∈ normalizedFunctions := by
    apply (normalized_iff _).mpr
    refine ⟨by dsimp [g]; rw [zero_add, hf.1, div_self (sub_ne_zero.mpr (Ne.symm ha1))], ?_⟩
    intro hs s
    dsimp [g]
    rw [difference_div, difference_sub, difference_shift]
    exact div_nonneg (hf.2.2 (a :: hs) s) (sub_pos.mpr halt).le
  have hdecomp : f = f a • h + (1 - f a) • g := by
    ext s
    change f s = f a * (f (s + a) / f a) +
      (1 - f a) * ((f s - f (s + a)) / (1 - f a))
    field_simp
    ring
  have heq := (he.2 h hh g hg (f a) hapos halt hdecomp).1
  have hv := congrFun heq t
  change f (t + a) / f a = f t at hv
  exact (div_eq_iff ha0).mp hv

/-- The elementary Archimedean form of the monotone Cauchy equation on ℝ≥0. -/
theorem additive_nonnegative_eq_mul (g : ℝ≥0 → ℝ) (hzero : g 0 = 0)
    (hadd : ∀ s t, g (s + t) = g s + g t) (hnonneg : ∀ t, 0 ≤ g t) (t : ℝ≥0) :
    g t = (t : ℝ) * g 1 := by
  have hmono : Monotone g := by
    intro s t hst
    have := hnonneg (t - s)
    have h := hadd s (t - s)
    rw [add_tsub_cancel_of_le hst] at h
    linarith
  have hnsmul : ∀ (n : ℕ) (s : ℝ≥0), g (n • s) = (n : ℝ) * g s := by
    intro n s
    induction n with
    | zero => simp [hzero]
    | succ n ih => rw [succ_nsmul, hadd, ih]; push_cast; ring
  have hnat (n : ℕ) : g (n : ℝ≥0) = (n : ℝ) * g 1 := by
    simpa using hnsmul n 1
  have hbound (n : ℕ) :
      (n : ℝ) * (g t - (t : ℝ) * g 1) ≤ g 1 ∧
      (n : ℝ) * ((t : ℝ) * g 1 - g t) ≤ g 1 := by
    let k : ℕ := ⌊((n • t : ℝ≥0) : ℝ)⌋₊
    have hlo : (k : ℝ) ≤ ((n • t : ℝ≥0) : ℝ) := Nat.floor_le (by positivity)
    have hhi : ((n • t : ℝ≥0) : ℝ) < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have hklo : (k : ℝ≥0) ≤ n • t := by exact_mod_cast hlo
    have hkhi : n • t ≤ (k + 1 : ℕ) := by exact_mod_cast hhi.le
    have hl := hmono hklo
    have hu := hmono hkhi
    rw [hnat, hnsmul] at hl
    rw [hnsmul, hnat] at hu
    simp only [Nat.cast_add, Nat.cast_one] at hu
    simp only [nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast] at hlo hhi
    have hc := hnonneg 1
    constructor
    · nlinarith [mul_nonneg hc (sub_nonneg.mpr hlo)]
    · nlinarith [mul_nonneg hc (sub_nonneg.mpr hhi.le)]
  apply le_antisymm
  · by_contra h
    have hpos : 0 < g t - (t : ℝ) * g 1 := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨n, hn⟩ := exists_lt_nsmul hpos (g 1)
    rw [nsmul_eq_mul] at hn
    exact (not_lt_of_ge (hbound n).1) hn
  · by_contra h
    have hpos : 0 < (t : ℝ) * g 1 - g t := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨n, hn⟩ := exists_lt_nsmul hpos (g 1)
    rw [nsmul_eq_mul] at hn
    exact (not_lt_of_ge (hbound n).2) hn

theorem multiplicative_classification {f : FunctionSpace} (hf : f ∈ normalizedFunctions)
    (hmul : ∀ s t, f (s + t) = f s * f t) : f ∈ exponentials := by
  classical
  by_cases hpositive : ∀ t, 0 < f t
  · right
    let g : ℝ≥0 → ℝ := fun t => -Real.log (f t)
    have hg0 : g 0 = 0 := by simp [g, hf.1]
    have hgadd : ∀ s t, g (s + t) = g s + g t := by
      intro s t
      simp only [g, hmul, Real.log_mul (hpositive s).ne' (hpositive t).ne', neg_add_rev]
      ring
    have hgpos : ∀ t, 0 ≤ g t := by
      intro t
      exact neg_nonneg.mpr (Real.log_nonpos (hf.2.1 t).1 (hf.2.1 t).2)
    let rate : ℝ≥0 := ⟨g 1, hgpos 1⟩
    refine ⟨rate, ?_⟩
    ext t
    have hlinear := additive_nonnegative_eq_mul g hg0 hgadd hgpos t
    change f t = Real.exp (-(g 1) * (t : ℝ))
    calc
      f t = Real.exp (Real.log (f t)) := (Real.exp_log (hpositive t)).symm
      _ = Real.exp (-(g 1) * (t : ℝ)) := by
        congr 1
        change -Real.log (f t) = (t : ℝ) * g 1 at hlinear
        nlinarith
  · left
    push Not at hpositive
    obtain ⟨a, ha⟩ := hpositive
    have hazero : f a = 0 := le_antisymm ha (hf.2.1 a).1
    have hnsmul : ∀ (n : ℕ) (t : ℝ≥0), f (n • t) = f t ^ n := by
      intro n t
      induction n with
      | zero => simp [hf.1]
      | succ n ih => rw [succ_nsmul, hmul, ih, pow_succ]
    have hanti := antitone_of_mem hf
    ext t
    by_cases ht : t = 0
    · simp [infinityExponential, ht, hf.1]
    · have htpos : 0 < t := pos_iff_ne_zero.mpr ht
      obtain ⟨n, hn⟩ := exists_lt_nsmul htpos a
      have hle := hanti hn.le
      rw [hazero, hnsmul] at hle
      have hz : f t ^ n = 0 := le_antisymm hle (pow_nonneg (hf.2.1 t).1 n)
      simpa [infinityExponential, ht] using eq_zero_of_pow_eq_zero hz

theorem extreme_classification : Specs.ExpandedFA.P1.BernsteinExtremes.extremeClassificationType := by
  intro f hf
  exact multiplicative_classification hf.1 (extreme_multiplicative hf)

theorem closed_convex_hull : Specs.ExpandedFA.P1.BernsteinExtremes.closedConvexHullType := by
  apply Set.Subset.antisymm
  · have hkm := real_krein_milman normalizedFunctions normalized_compact_convex.1
      normalized_compact normalized_convex
    rw [hkm]
    exact closure_mono (convexHull_mono extreme_classification)
  · exact closure_minimal (convexHull_min exponential_membership normalized_convex) normalized_closed

end ExpandedFA.P1.Bernstein
