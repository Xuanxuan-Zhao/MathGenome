import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Iterations.BisectionCertificates
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Iterations.BisectionInvariants
import Mathlib.Tactic.Positivity

namespace NumAnalysis206.Iterations.BisectionCertificates
open Specs.NumAnalysis206.Iterations.BisectionInvariants
open Specs.NumAnalysis206.Iterations.BisectionCertificates

theorem count_formula : countFormula := by
  intro a b ε
  simp only [updateCount, ← Int.ceil_toNat, Int.toNat_eq_max, max_comm]

theorem exact_threshold : exactThreshold := by
  intro a b ε hab hε n
  have hw : 0 < b-a := sub_pos.mpr hab
  have hpow : 0 < (2 : ℝ)^n := by positivity
  rw [updateCount, Nat.ceil_le,
    Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
      (div_pos hw (by positivity)), Real.rpow_natCast]
  have heq : (1/2 : ℝ)^(n+1) * (b-a) = (b-a) / (2 * (2 : ℝ)^n) := by
    rw [pow_succ, div_pow, one_pow]
    ring
  rw [heq, div_le_iff₀ (by positivity : 0 < 2 * (2 : ℝ)^n),
    div_le_iff₀ (by positivity : 0 < 2*ε)]
  constructor <;> intro h <;> nlinarith

theorem initial_threshold : initialThreshold := by
  intro a b ε hab hε
  have h := exact_threshold a b ε hab hε 0
  simpa [div_eq_mul_inv, mul_comm] using h.symm

theorem midpoint_certificate : midpointCertificate := by
  intro f a b ε K hab hε hf hs r n hn hbudget
  obtain ⟨_, _, _, _, p, hp, hroot, herr⟩ :=
    (BisectionInvariants.finite_invariants f a b K hab hf hs r).1 n hn
  exact ⟨p, hp, hroot, herr.trans ((exact_threshold a b ε hab hε n).mpr hbudget)⟩

/-- Legal exact halvings can be iterated any finite number of times. -/
theorem finite_run_exists (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hs : f a * f b ≤ 0) (N : ℕ) : Nonempty (FiniteRun f a b N) := by
  induction N with
  | zero =>
    exact ⟨{ left := fun _ => a, right := fun _ => b,
             left_zero := rfl, right_zero := rfl,
             step := by intro n hn; omega }⟩
  | succ N ih =>
    obtain ⟨r⟩ := ih
    have hsN := (BisectionInvariants.interval_invariants f a b N hab hs r N le_rfl).2.2.1
    obtain ⟨c, d, hhalf⟩ := BisectionInvariants.legal_half_exists f (r.left N) (r.right N) hsN
    refine ⟨{ left := fun i => if i ≤ N then r.left i else c,
              right := fun i => if i ≤ N then r.right i else d,
              left_zero := by simp [r.left_zero],
              right_zero := by simp [r.right_zero],
              step := ?_ }⟩
    intro n hn
    by_cases h : n < N
    · simpa only [ite_eq_left h.le, ite_eq_left (Nat.succ_le_of_lt h)] using r.step n h
    · have heq : n = N := by omega
      subst n
      simpa using hhalf

theorem budget_attainable : budgetAttainable := by
  intro f a b ε hab hε hf hs
  obtain ⟨r⟩ := finite_run_exists f a b hab hs (updateCount a b ε)
  exact ⟨r, midpoint_certificate f a b ε _ hab hε hf hs r _ le_rfl le_rfl⟩

theorem stopping_guarantee : stoppingGuarantee := by
  intro f a b ε K hab hε hf hs r hearly
  by_cases hK : K < updateCount a b ε
  · obtain ⟨p, hp⟩ := hearly hK
    obtain ⟨_, hmem, hroot⟩ :=
      BisectionInvariants.return_correctness f a b K hab hf hs r K le_rfl p hp
    exact Or.inl ⟨hK, p, hmem, hp, hroot⟩
  · have hle := le_of_not_gt hK
    exact Or.inr ⟨hle, midpoint_certificate f a b ε K hab hε hf hs r _ hle le_rfl⟩

theorem enclosure_certificates : enclosureCertificates := by
  intro f x l u hl hu
  exact ⟨fun h => h.trans_le hl, fun h => hu.trans_lt h, fun h₁ h₂ => by
    rw [h₁] at hl
    rw [h₂] at hu
    exact le_antisymm hu hl⟩

theorem universal_certificates : universalCertificates := by
  intro l u hlu
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h; exact h l ⟨le_rfl, hlu⟩
  · intro h y hy; exact h.trans_le hy.1
  · intro h; exact h u ⟨hlu, le_rfl⟩
  · intro h y hy; exact hy.2.trans_lt h
  · intro h; exact ⟨h l ⟨le_rfl, hlu⟩, h u ⟨hlu, le_rfl⟩⟩
  · rintro ⟨rfl, rfl⟩ y hy
    exact le_antisymm hy.2 hy.1

theorem ambiguous_enclosure : ambiguousEnclosure := by
  intro l u hl hu hne
  have hz : (0 : ℝ) ∈ Set.Icc l u := ⟨hl, hu⟩
  have hex : ∃ y ∈ Set.Icc l u, y ≠ 0 := by
    by_cases h : l = 0
    · exact ⟨u, ⟨hl.trans hu, le_rfl⟩, fun hu0 => hne ⟨h, hu0⟩⟩
    · exact ⟨l, ⟨le_rfl, hl.trans hu⟩, h⟩
  refine ⟨hz, hex, ?_, ?_, ?_⟩
  · intro h; exact (lt_irrefl (0 : ℝ)) (h 0 hz)
  · intro h; exact (lt_irrefl (0 : ℝ)) (h 0 hz)
  · intro h
    obtain ⟨y, hy, hny⟩ := hex
    exact hny (h y hy)

theorem strict_sign_updates : strictSignUpdates := by
  intro f a b x l u hl hu
  obtain ⟨hpos, hneg, _⟩ := enclosure_certificates f x l u hl hu
  exact ⟨fun ha hx => mul_neg_of_neg_of_pos ha (hpos hx),
    fun ha hx => mul_neg_of_pos_of_neg ha (hneg hx),
    fun hx hb => mul_neg_of_pos_of_neg (hpos hx) hb,
    fun hx hb => mul_neg_of_neg_of_pos (hneg hx) hb⟩

theorem stored_distance : storedDistance := by
  intro a b z p _ hp
  apply abs_le.mpr
  have h₁ := le_max_left (z-a) (b-z)
  have h₂ := le_max_right (z-a) (b-z)
  constructor <;> linarith [hp.1, hp.2]

theorem stored_root_certificate : storedRootCertificate := by
  intro f a b z R hab hf hs hz hR
  obtain ⟨p, hp, hroot⟩ := BracketExistence.root_exists_closed a b f hab hf hs
  exact ⟨p, hp, hroot, (stored_distance a b z p hz hp).trans hR⟩

theorem root_radius : rootRadius := by
  intro f a b z p R hz hp hroot hR
  exact ⟨hroot, (stored_distance a b z p hz hp).trans hR⟩

theorem unavailable_midpoint : unavailableMidpoint := by
  intro F a b hab hF hm
  apply hF (midpoint a b) hm
  dsimp [midpoint]
  constructor <;> linarith

end NumAnalysis206.Iterations.BisectionCertificates
