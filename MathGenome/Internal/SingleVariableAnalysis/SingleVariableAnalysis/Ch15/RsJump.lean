import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.RsJump
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.RsAlgebra
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Linarith

namespace SingleVariableAnalysis.Stieltjes
open Riemann
open scoped BigOperators
open private integral_integrator_add integral_integrator_mul from
  MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.RsAlgebra

variable {K : Type} [RCLike K]

/-- Changing an integrator off the integration interval has no effect. -/
theorem integral_congr_integrator {a b : ℝ} (hab : a ≤ b) (f : ℝ → K)
    {α β : ℝ → ℝ} {I : K} (h : HasIntegral a b f α I)
    (heq : Set.EqOn α β (Set.Icc a b)) : HasIntegral a b f β I := by
  have h := (integral_iff_of_le a b hab f α I).mp h
  apply (integral_iff_of_le a b hab f β I).mpr
  refine ⟨h.1, ?_, ?_⟩
  · obtain ⟨M, hM⟩ := h.2.1
    exact ⟨M, fun x hx => by rw [← heq hx]; exact hM x hx⟩
  · intro ε hε
    obtain ⟨P, hP⟩ := h.2.2 ε hε
    refine ⟨P, fun Q hQ t => ?_⟩
    have hs : Stieltjes.taggedSum Q t f β = Stieltjes.taggedSum Q t f α := by
      apply Finset.sum_congr rfl
      intro i _
      have hbound := (endpoints Q).2.2
      rw [← heq (hbound _ (Finset.mem_image.mpr ⟨i.succ, Finset.mem_univ _, rfl⟩)),
        ← heq (hbound _ (Finset.mem_image.mpr ⟨i.castSucc, Finset.mem_univ _, rfl⟩))]
    change ‖Stieltjes.taggedSum Q t f β - I‖ < ε
    rw [hs]
    exact hP Q hQ t

/-- A constant integrator has zero integral, for every bounded integrand. -/
theorem integral_const_integrator {a b : ℝ} (hab : a ≤ b) (f : ℝ → K)
    (hf : BoundedOn a b f) (r : ℝ) : HasIntegral a b f (fun _ => r) 0 := by
  apply (integral_iff_of_le a b hab f (fun _ => r) 0).mpr
  refine ⟨hf, ⟨‖r‖, fun _ _ => le_rfl⟩, ?_⟩
  intro ε hε
  obtain ⟨P, _⟩ := finite_representation (a := a) (b := b) ({a,b} : Finset ℝ)
    (by simp) (by simp) (by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact ⟨le_rfl, hab⟩
      · exact ⟨hab, le_rfl⟩)
  exact ⟨P, fun Q _ t => by
    simpa [Specs.SingleVariableAnalysis.Ch15.RsSums.sumValue] using hε⟩

private theorem partition_n_pos {a b : ℝ} (hab : a < b) (P : Partition a b) :
    0 < P.n := by
  by_contra h
  have hn : P.n = 0 := by omega
  have he : (0 : Fin (P.n+1)) = Fin.last P.n := Fin.ext (by simp [hn])
  have : a = b := by rw [← P.first, he, P.last]
  linarith

/-- Point membership exposes the actual ordered node index. -/
private theorem node_index {a b d : ℝ} {P : Partition a b} (hd : d ∈ points P) :
    ∃ j, P.point j = d := by
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hd
  exact ⟨j, hj⟩

/-- Isolate the left endpoint spike; the first cell is its only increment. -/
theorem integral_left_endpoint_spike {a b : ℝ} (hab : a < b) (f : ℝ → K)
    (hf : BoundedOn a b f) (hc : ContinuousWithinAt f (Set.Icc a b) a) :
    HasIntegral a b f (fun y => if y = a then (1 : ℝ) else 0) (-f a) := by
  apply (integral_iff_of_le a b hab.le f _ (-f a)).mpr
  refine ⟨hf, ⟨1, fun y _ => by dsimp only; split_ifs <;> norm_num⟩, ?_⟩
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousWithinAt_iff.mp hc ε hε
  let d := a + min ((b-a)/2) (δ/2)
  have had : a < d := by
    have hm : 0 < min ((b-a)/2) (δ/2) := lt_min (by linarith) (by linarith)
    dsimp [d]
    linarith
  have hdb : d < b := by dsimp [d]; have := min_le_left ((b-a)/2) (δ/2); linarith
  have hda : d-a < δ := by dsimp [d]; have := min_le_right ((b-a)/2) (δ/2); linarith
  let s : Finset ℝ := {a, d, b}
  have hs : ∀ y ∈ s, y ∈ Set.Icc a b := by
    intro y hy
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact ⟨le_rfl, hab.le⟩
    · exact ⟨had.le, hdb.le⟩
    · exact ⟨hab.le, le_rfl⟩
  let P₀ := ofPoints s (by simp [s]) (by simp [s]) hs
  refine ⟨P₀, fun P hP t => ?_⟩
  have hn := partition_n_pos hab P
  let z : Fin P.n := ⟨0, hn⟩
  have hz : P.point z.castSucc = a := P.first
  have hpos (i : Fin P.n) : a < P.point i.succ := by
    simpa only [P.first] using P.strictMono (show (0 : Fin (P.n+1)) < i.succ by
      change 0 < i.val+1; omega)
  have hsumm : Stieltjes.taggedSum P t f (fun y => if y = a then (1 : ℝ) else 0) =
      -f (t z) := by
    change Specs.SingleVariableAnalysis.Ch15.RsSums.sumValue P t f _ = _
    unfold Specs.SingleVariableAnalysis.Ch15.RsSums.sumValue
    rw [Finset.sum_eq_single z]
    · simp [hz, ne_of_gt (hpos z)]
    · intro i _ hiz
      have hi : a < P.point i.castSucc := by
        have him : (0 : Fin (P.n+1)) < i.castSucc := by
          change 0 < i.val
          have : i.val ≠ 0 := by intro hi; apply hiz; exact Fin.ext hi
          omega
        simpa only [P.first] using P.strictMono him
      simp [ne_of_gt hi, ne_of_gt (hpos i)]
    · simp
  have hdP : d ∈ points P := hP (by
    change d ∈ points (ofPoints s _ _ hs)
    rw [points_ofPoints]
    simp [s])
  obtain ⟨j, hj⟩ := node_index hdP
  have hjpos : 0 < j.val := by
    by_contra h
    have hj0 : j = 0 := Fin.ext (by change j.val = 0; omega)
    rw [hj0, P.first] at hj
    linarith
  have hpd : P.point z.succ ≤ d := by
    rw [← hj]
    exact P.strictMono.monotone (by change 1 ≤ j.val; omega)
  have hta : a ≤ (t z : ℝ) := by simpa [hz] using (t z).property.1
  have htd : (t z : ℝ) ≤ d := (t z).property.2.trans hpd
  have htδ : dist (t z : ℝ) a < δ := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hta)]
    linarith
  have ht := hcont (tag_mem_interval P t z) htδ
  change ‖Stieltjes.taggedSum P t f _ - (-f a)‖ < ε
  rw [hsumm]
  simpa only [dist_eq_norm, neg_sub_neg, norm_sub_rev] using ht

/-- The right endpoint spike has exactly the final-cell contribution. -/
theorem sum_right_endpoint_spike {a b : ℝ} (hab : a < b) (P : Partition a b)
    (t : Tagging P) (f : ℝ → K) :
    Stieltjes.taggedSum P t f (fun y => if y = b then (1 : ℝ) else 0) =
      f (t ⟨P.n-1, by have := partition_n_pos hab P; omega⟩) := by
  have hn := partition_n_pos hab P
  let z : Fin P.n := ⟨P.n-1, by omega⟩
  have hz : P.point z.succ = b := by
    convert P.last using 1
    congr 1
    apply Fin.ext
    dsimp [z]
    omega
  have hpos (i : Fin P.n) : P.point i.castSucc < b := by
    simpa only [P.last] using P.strictMono (show i.castSucc < Fin.last P.n by
      change i.val < P.n; exact i.isLt)
  change Specs.SingleVariableAnalysis.Ch15.RsSums.sumValue P t f _ = f (t z)
  unfold Specs.SingleVariableAnalysis.Ch15.RsSums.sumValue
  rw [Finset.sum_eq_single z]
  · simp [hz, ne_of_lt (hpos z)]
  · intro i _ hiz
    have hi : P.point i.succ < b := by
      have him : i.succ < Fin.last P.n := by
        change i.val+1 < P.n
        have hi := i.isLt
        have : i.val ≠ P.n-1 := by intro hi; apply hiz; exact Fin.ext hi
        omega
      simpa only [P.last] using P.strictMono him
    simp [ne_of_lt hi, ne_of_lt (hpos i)]
  · simp

/-- The last cell isolates the right endpoint spike. -/
theorem integral_right_endpoint_spike {a b : ℝ} (hab : a < b) (f : ℝ → K)
    (hf : BoundedOn a b f) (hc : ContinuousWithinAt f (Set.Icc a b) b) :
    HasIntegral a b f (fun y => if y = b then (1 : ℝ) else 0) (f b) := by
  apply (integral_iff_of_le a b hab.le f _ (f b)).mpr
  refine ⟨hf, ⟨1, fun y _ => by dsimp only; split_ifs <;> norm_num⟩, ?_⟩
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousWithinAt_iff.mp hc ε hε
  let d := b - min ((b-a)/2) (δ/2)
  have had : a < d := by dsimp [d]; have := min_le_left ((b-a)/2) (δ/2); linarith
  have hdb : d < b := by
    have hm : 0 < min ((b-a)/2) (δ/2) := lt_min (by linarith) (by linarith)
    dsimp [d]
    linarith
  have hbd : b-d < δ := by dsimp [d]; have := min_le_right ((b-a)/2) (δ/2); linarith
  let s : Finset ℝ := {a, d, b}
  have hs : ∀ y ∈ s, y ∈ Set.Icc a b := by
    intro y hy
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact ⟨le_rfl, hab.le⟩
    · exact ⟨had.le, hdb.le⟩
    · exact ⟨hab.le, le_rfl⟩
  let P₀ := ofPoints s (by simp [s]) (by simp [s]) hs
  refine ⟨P₀, fun P hP t => ?_⟩
  have hn := partition_n_pos hab P
  let z : Fin P.n := ⟨P.n-1, by omega⟩
  have hz : P.point z.succ = b := by
    convert P.last using 1
    congr 1
    apply Fin.ext
    dsimp [z]
    omega
  have hsumm := sum_right_endpoint_spike hab P t f
  have hdP : d ∈ points P := hP (by
    change d ∈ points (ofPoints s _ _ hs)
    rw [points_ofPoints]
    simp [s])
  obtain ⟨j, hj⟩ := node_index hdP
  have hjlt : j.val < P.n := by
    by_contra h
    have hjlast : j = Fin.last P.n := Fin.ext (by have := j.isLt; dsimp; omega)
    rw [hjlast, P.last] at hj
    linarith
  have hpd : d ≤ P.point z.castSucc := by
    rw [← hj]
    exact P.strictMono.monotone (by change j.val ≤ P.n-1; omega)
  have htb : (t z : ℝ) ≤ b := by simpa [hz] using (t z).property.2
  have htd : d ≤ (t z : ℝ) := hpd.trans (t z).property.1
  have htδ : dist (t z : ℝ) b < δ := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr htb)]
    linarith
  have ht := hcont (tag_mem_interval P t z) htδ
  change ‖Stieltjes.taggedSum P t f _ - f b‖ < ε
  rw [hsumm]
  simpa only [dist_eq_norm] using ht

/-- On one open constant cell, arbitrary endpoint values contribute separately.
No continuity is needed at an endpoint whose increment is zero. -/
theorem integral_constant_open_cell {a b : ℝ} (hab : a < b) (f : ℝ → K)
    (α : ℝ → ℝ) (v : ℝ) (hf : BoundedOn a b f)
    (hv : ∀ y ∈ Set.Ioo a b, α y = v)
    (ha : v - α a ≠ 0 → ContinuousWithinAt f (Set.Icc a b) a)
    (hb : α b - v ≠ 0 → ContinuousWithinAt f (Set.Icc a b) b) :
    HasIntegral a b f α ((v-α a) • f a + (α b-v) • f b) := by
  have hL : HasIntegral a b f
      (fun y => (α a-v) * (if y = a then (1 : ℝ) else 0)) ((v-α a) • f a) := by
    by_cases hr : α a-v = 0
    · have hr' : v-α a = 0 := by linarith
      simpa only [hr, hr', zero_mul, zero_smul] using
        integral_const_integrator hab.le f hf 0
    · have h := integral_integrator_mul
        (integral_left_endpoint_spike hab f hf (ha (by intro h; apply hr; linarith)))
        (α a-v)
      simpa only [smul_neg, ← neg_smul, neg_sub] using h
  have hR : HasIntegral a b f
      (fun y => (α b-v) * (if y = b then (1 : ℝ) else 0)) ((α b-v) • f b) := by
    by_cases hr : α b-v = 0
    · simpa only [hr, zero_mul, zero_smul] using integral_const_integrator hab.le f hf 0
    · exact integral_integrator_mul (integral_right_endpoint_spike hab f hf (hb hr)) _
  have h := integral_integrator_add
    (integral_integrator_add (integral_const_integrator hab.le f hf v) hL) hR
  simp only [zero_add] at h
  apply integral_congr_integrator hab.le f h
  intro y hy
  dsimp only
  by_cases hya : y = a
  · subst y
    simp [ne_of_lt hab]
  · by_cases hyb : y = b
    · subst y
      simp [ne_of_gt hab]
    · have hyv := hv y ⟨lt_of_le_of_ne hy.1 (Ne.symm hya), lt_of_le_of_ne hy.2 hyb⟩
      simp [hya, hyb, hyv]

/-- Finite interval additivity for an arbitrary chain of nodes. -/
theorem integral_chain (n : ℕ) (x : Fin (n+1) → ℝ) (hx : Monotone x)
    (f : ℝ → K) (α : ℝ → ℝ) (I : Fin n → K)
    (hI : ∀ i, HasIntegral (x i.castSucc) (x i.succ) f α (I i)) :
    HasIntegral (x 0) (x (Fin.last n)) f α (∑ i, I i) := by
  induction n with
  | zero =>
    simpa using (degenerate_integral (x 0) f α 0).mpr rfl
  | succ n ih =>
    have hleft := ih (fun j => x j.castSucc) (hx.comp (Fin.strictMono_castSucc.monotone))
      (fun i => I i.castSucc) (fun i => hI i.castSucc)
    have hright := hI (Fin.last n)
    have hxc : x (Fin.last n).castSucc ∈ Set.uIcc (x 0) (x (Fin.last (n+1))) :=
      Set.mem_uIcc_of_le (hx (Fin.zero_le _)) (hx (Fin.le_last _))
    apply (interval_additivity _ _ _ hxc f α _).mpr
    refine ⟨_, _, hleft, hright, ?_⟩
    exact Fin.sum_univ_castSucc I

/-- The incident cell contributions telescope to endpoint terms and full
interior jumps. In particular the arbitrary interior node values cancel. -/
theorem step_cell_sum (n : ℕ) (x : Fin (n+2) → ℝ) (v : Fin (n+1) → ℝ)
    (α : ℝ → ℝ) (f : ℝ → K) :
    (∑ i : Fin (n+1), ((v i-α (x i.castSucc)) • f (x i.castSucc) +
      (α (x i.succ)-v i) • f (x i.succ))) =
    (v 0-α (x 0)) • f (x 0) +
      (∑ i : Fin n, (v i.succ-v i.castSucc) • f (x i.succ.castSucc)) +
      (α (x (Fin.last (n+1)))-v (Fin.last n)) • f (x (Fin.last (n+1))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have hih := ih (fun j => x j.castSucc) (fun i => v i.castSucc)
    simp only [Fin.castSucc_succ] at hih
    rw [hih]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.castSucc_zero, Fin.succ_last, Fin.castSucc_succ, sub_smul]
    abel

/-- Full finite-step formula, with separate incident continuity assumptions. -/
theorem step_integral : Specs.SingleVariableAnalysis.Ch15.RsJump.stepIntegral := by
  intro K _ n x hx v α f hv hf hc
  have bound (i : Fin (n+1)) : Set.Icc (x i.castSucc) (x i.succ) ⊆
      Set.Icc (x 0) (x (Fin.last (n+1))) :=
    Set.Icc_subset_Icc (hx.monotone (Fin.zero_le _)) (hx.monotone (Fin.le_last _))
  have hcell (i : Fin (n+1)) := integral_constant_open_cell
    (hx (Fin.castSucc_lt_succ (i := i))) f α (v i)
    (by obtain ⟨M,hM⟩ := hf; exact ⟨M, fun y hy => hM y (bound i hy)⟩)
    (hv i) (fun hi => ((hc i).1 hi).mono (bound i))
    (fun hi => ((hc i).2 hi).mono (bound i))
  have h := integral_chain (n+1) x hx.monotone f α _ hcell
  rwa [step_cell_sum] at h

/-- An initial value already present at a has no atom. -/
theorem initial_value_no_atom : Specs.SingleVariableAnalysis.Ch15.RsJump.initialValueNoAtom := by
  intro K _ a b f hab hf
  apply integral_congr_integrator hab f (integral_const_integrator hab f hf 1)
  intro y hy
  simp [le_trans hy.1 le_rfl]

/-- The right-continuous step gives an atom at c ∈ (a,b], including c = b. -/
theorem right_continuous_atom : Specs.SingleVariableAnalysis.Ch15.RsJump.rightContinuousAtom := by
  intro K _ a b c f hac hcb hf hc
  have hab : a ≤ b := hac.le.trans hcb
  have hleftBound : BoundedOn a c f := by
    obtain ⟨M,hM⟩ := hf
    exact ⟨M, fun y hy => hM y ⟨hy.1, hy.2.trans hcb⟩⟩
  have hrightBound : BoundedOn c b f := by
    obtain ⟨M,hM⟩ := hf
    exact ⟨M, fun y hy => hM y ⟨hac.le.trans hy.1, hy.2⟩⟩
  have hleft : HasIntegral a c f (fun y => if c ≤ y then (1 : ℝ) else 0) (f c) := by
    have h := integral_constant_open_cell hac f (fun y => if c ≤ y then (1 : ℝ) else 0)
      0 hleftBound
      (fun y hy => by simp [not_le.mpr hy.2])
      (by simp [not_le.mpr hac])
      (fun _ => hc.mono (Set.Icc_subset_Icc le_rfl hcb))
    simpa [not_le.mpr hac] using h
  have hright := initial_value_no_atom c b f hcb hrightBound
  apply (interval_additivity a b c (Set.mem_uIcc_of_le hac.le hcb) f _ _).mpr
  exact ⟨f c, 0, hleft, hright, by simp⟩

/-- A constant open cell supplies both available endpoint limits. -/
theorem step_cell_limits : Specs.SingleVariableAnalysis.Ch15.RsJump.cellLimits := by
  intro a b v α hab hv
  constructor
  · apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [Ioo_mem_nhdsGT hab] with y hy
    exact (hv y hy).symm
  · apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [Ioo_mem_nhdsLT hab] with y hy
    exact (hv y hy).symm

private theorem endpoint_spike_not_integrable {a b : ℝ} (hab : a < b) :
    ¬ ∃ I : ℝ, HasIntegral a b (fun y => if y = b then (1 : ℝ) else 0)
      (fun y => if y = b then (1 : ℝ) else 0) I := by
  rintro ⟨I, hI⟩
  have h := (integral_iff_of_le a b hab.le _ _ I).mp hI
  obtain ⟨P, hP⟩ := h.2.2 (1/3) (by norm_num)
  have hn := partition_n_pos hab P
  let z : Fin P.n := ⟨P.n-1, by omega⟩
  have hz : P.point z.succ = b := by
    convert P.last using 1
    congr 1
    apply Fin.ext
    dsimp [z]
    omega
  have hp : P.point z.castSucc < b := by
    simpa only [P.last] using P.strictMono (show z.castSucc < Fin.last P.n by
      change P.n-1 < P.n; omega)
  let tr : Tagging P := fun i => ⟨P.point i.succ,
    (P.strictMono (Fin.castSucc_lt_succ (i := i))).le, le_rfl⟩
  let tm : Tagging P := fun i => ⟨(P.point i.castSucc + P.point i.succ)/2, by
    have hi := P.strictMono (Fin.castSucc_lt_succ (i := i))
    constructor <;> linarith⟩
  have htr : Stieltjes.taggedSum P tr (fun y => if y = b then (1 : ℝ) else 0)
      (fun y => if y = b then (1 : ℝ) else 0) = 1 := by
    rw [sum_right_endpoint_spike hab]
    change (if P.point z.succ = b then (1 : ℝ) else 0) = 1
    simp [hz]
  have htm : Stieltjes.taggedSum P tm (fun y => if y = b then (1 : ℝ) else 0)
      (fun y => if y = b then (1 : ℝ) else 0) = 0 := by
    rw [sum_right_endpoint_spike hab]
    change (if (P.point z.castSucc + P.point z.succ)/2 = b then (1 : ℝ) else 0) = 0
    rw [hz]
    have hmid : (P.point z.castSucc + b)/2 ≠ b := by linarith
    simp [hmid]
  have hr := hP P (Finset.Subset.refl _) tr
  have hm := hP P (Finset.Subset.refl _) tm
  change ‖Stieltjes.taggedSum P tr _ _ - I‖ < 1/3 at hr
  change ‖Stieltjes.taggedSum P tm _ _ - I‖ < 1/3 at hm
  rw [htr, Real.norm_eq_abs] at hr
  rw [htm, Real.norm_eq_abs] at hm
  have hr' := (abs_lt.mp hr).2
  have hm' := (abs_lt.mp hm).1
  linarith

/-- Cancellation of the two jumps at an isolated spike cannot cure its
independent closed-cell tag choices. -/
theorem zero_net_obstruction : Specs.SingleVariableAnalysis.Ch15.RsJump.zeroNetObstruction := by
  intro a b c hac hcb h
  obtain ⟨I,hI⟩ := h
  obtain ⟨J,L,hJ,_,_⟩ :=
    (interval_additivity a b c (Set.mem_uIcc_of_le hac.le hcb.le) _ _ I).mp hI
  exact endpoint_spike_not_integrable hac ⟨J,hJ⟩

end SingleVariableAnalysis.Stieltjes
