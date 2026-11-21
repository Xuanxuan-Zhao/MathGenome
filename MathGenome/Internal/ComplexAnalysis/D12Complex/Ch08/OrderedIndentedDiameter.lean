import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.OrderedIndentedDiameter
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PathOperations
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

noncomputable section
open Set
namespace D12Complex.OrderedIndentedDiameter
open Specs.D12Complex.Ch08.OrderedIndentedDiameter
open private glue_piecewise from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PathOperations

@[fun_prop] theorem ofReal_contDiff (k : WithTop ℕ∞) : ContDiff ℝ k Complex.ofReal :=
  Complex.ofRealCLM.contDiff

/-- Ordered gap endpoints, including the two exterior retained intervals. -/
theorem ordered_gaps : ordered_gaps_type := by
  intro s l u ε h
  classical
  let n := s.card
  let e : Fin n ≃ s := (s.orderIsoOfFin rfl).toEquiv
  let start : Fin (n+1) → ℝ := fun j =>
    if hj : j.val = 0 then l else
      let i : Fin n := ⟨j.val-1, by omega⟩
      (e i).val + ε (e i)
  let stop : Fin (n+1) → ℝ := fun j =>
    if hj : j.val < n then
      let i : Fin n := ⟨j.val, hj⟩
      (e i).val - ε (e i) else u
  have he : StrictMono (fun i => (e i).val) := (s.orderEmbOfFin rfl).strictMono
  refine ⟨n, e, start, stop, he, ?_, ?_, ?_, ?_, ?_⟩
  · simp [start]
  · simp [stop]
  · intro i; simp [stop, i.isLt]
  · intro i
    simp [start, Fin.val_succ]
  · intro j
    dsimp [start, stop]
    split_ifs with hj hk hk
    · exact (h.2.1 (e ⟨j.val, hk⟩)).2.1
    · exact h.1
    · exact h.2.2 _ _ (he (by change j.val-1 < j.val; omega))
    · exact (h.2.1 (e ⟨j.val-1, by omega⟩)).2.2

private def smoothPiece (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℂ)
    (hf : ContDiff ℝ 1 f) : PiecewiseC1Path :=
  ⟨⟨a,b,hab,f,hf.continuous.continuousOn⟩, ⟨C1Partition.single _ hf.contDiffOn⟩⟩

/-- Finite gluing without affine rescaling: piece k keeps the interval [k,k+1]. -/
theorem unit_pieces_exist (m : ℕ) (f : ℕ → ℝ → ℂ)
    (hs : ∀ k ≤ m, ContDiff ℝ 1 (f k))
    (hj : ∀ k < m, f k (k+1) = f (k+1) (k+1)) :
    ∃ γ : PiecewiseC1Path, γ.path.a = 0 ∧ γ.path.b = (m+1 : ℕ) ∧
      ∀ k ≤ m, EqOn γ (f k) (Icc (k:ℝ) (k+1)) := by
  induction m with
  | zero =>
    refine ⟨smoothPiece 0 1 (by norm_num) (f 0) (hs 0 (by omega)), rfl, ?_, ?_⟩
    · norm_num [smoothPiece, PiecewiseC1Path.path]
    · intro k hk
      have hk0 : k = 0 := by omega
      subst k
      exact fun _ _ => rfl
  | succ m ih =>
    obtain ⟨γ, ha, hb, hg⟩ := ih (fun k hk => hs k (by omega))
      (fun k hk => hj k (by omega))
    let δ := smoothPiece (m+1) (m+2) (by linarith) (f (m+1)) (hs _ (by omega))
    obtain ⟨η, hηa, hηb, hηg, hηδ⟩ := glue_piecewise γ δ (by
      change γ.path.b = (m:ℝ)+1
      simpa only [Nat.cast_add, Nat.cast_one] using hb) (by
      change γ γ.path.b = f (m+1) ((m:ℝ)+1)
      rw [hb]
      have hlast := hg m (le_refl _) (show ((m+1 : ℕ) : ℝ) ∈ Icc (m:ℝ) (m+1) by
        push_cast; constructor <;> linarith)
      rw [hlast]
      simpa only [Nat.cast_add, Nat.cast_one] using hj m (by omega))
    refine ⟨η, hηa.trans ha, ?_, ?_⟩
    · change η.path.b = (m:ℝ)+2 at hηb
      push_cast
      linarith
    · intro k hk t ht
      by_cases hkm : k ≤ m
      · have hmem : t ∈ Icc γ.path.a γ.path.b := by
          rw [ha, hb]
          have hcast : (k:ℝ) ≤ m := by exact_mod_cast hkm
          push_cast
          exact ⟨(Nat.cast_nonneg k).trans ht.1, by linarith [ht.2]⟩
        exact (hηg hmem).trans (hg k hkm ht)
      · have : k = m+1 := by omega
        subst k
        exact hηδ (by simpa [δ, smoothPiece, PiecewiseC1Path.path,
          Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using ht)

/-- Assemble the exact alternating line/clockwise-arc parametrization. -/
theorem path_exists : path_exists_type := by
  intro s l u ε n e start stop h
  classical
  let f : ℕ → ℝ → ℂ := fun k =>
    if heven : k % 2 = 0 then
      if hj : k / 2 < n+1 then
        fun t => ((start ⟨k/2,hj⟩ + (stop ⟨k/2,hj⟩-start ⟨k/2,hj⟩) *
          (t-2*(k/2:ℕ))) : ℝ) else fun _ => 0
    else if hi : k / 2 < n then
      fun t => circleMap ((e ⟨k/2,hi⟩).val : ℂ) (ε (e ⟨k/2,hi⟩))
        (Real.pi*(2*(k/2:ℕ)+2-t)) else fun _ => 0
  have fe (j : Fin (n+1)) : f (2*j.val) = fun t =>
      ((start j + (stop j-start j)*(t-2*(j.val:ℝ)) : ℝ) : ℂ) := by
    simp [f, show j.val ≤ n by omega]
  have fo (i : Fin n) : f (2*i.val+1) = fun t =>
      circleMap ((e i).val : ℂ) (ε (e i)) (Real.pi*(2*(i.val:ℝ)+2-t)) := by
    simp [f, i.isLt, Nat.add_div]
  have hsm (k : ℕ) (hk : k ≤ 2*n) : ContDiff ℝ 1 (f k) := by
    dsimp [f]
    split_ifs
    all_goals try simp only [circleMap]
    all_goals fun_prop
  have hj (k : ℕ) (hk : k < 2*n) : f k (k+1) = f (k+1) (k+1) := by
    by_cases hev : k % 2 = 0
    · let i : Fin n := ⟨k/2, by omega⟩
      have hki : k = 2*i.val := by dsimp [i]; omega
      rw [hki]
      have hei := fe i.castSucc
      simp only [Fin.val_castSucc] at hei
      rw [hei]
      have hnext : 2*i.val+1 = (2*i.val)+1 := rfl
      rw [fo i]
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      rw [show (2*(i.val:ℝ)+1-2*(i.val:ℝ)) = 1 by ring]
      rw [show (2*(i.val:ℝ)+2-(2*(i.val:ℝ)+1)) = 1 by ring]
      simp only [mul_one, add_sub_cancel, h.2.2.2.1 i, circleMap,
        Complex.ofReal_sub,
        Complex.exp_pi_mul_I, mul_neg_one]
      simp [sub_eq_add_neg]
    · let i : Fin n := ⟨k/2, by omega⟩
      have hki : k = 2*i.val+1 := by dsimp [i]; omega
      rw [hki, fo i]
      have heq : 2*i.val+1+1 = 2*i.succ.val := by simp; omega
      rw [heq, fe i.succ]
      simp only [Fin.val_succ, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add,
        Nat.cast_one]
      have hzero : 2*(i.val:ℝ)+2-(2*(i.val:ℝ)+1+1) = 0 := by ring
      have hzero' : 2*(i.val:ℝ)+1+1-2*((i.val:ℝ)+1) = 0 := by ring
      rw [hzero, hzero']
      simp [circleMap, h.2.2.2.2.1 i]
  obtain ⟨γ, ha, hb, hg⟩ := unit_pieces_exist (2*n) f hsm hj
  have ht : Traversal ε e start stop γ := by
    refine ⟨ha, hb, ?_, ?_⟩
    · intro j t ht
      have heq := hg (2*j.val) (by omega)
      rw [fe j] at heq
      exact heq (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using ht)
    · intro i t ht
      have heq := hg (2*i.val+1) (by omega)
      rw [fo i] at heq
      exact heq (by simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add,
        Nat.cast_one, add_assoc, one_add_one_eq_two] using ht)
  refine ⟨γ, ht, ?_, ?_⟩
  · change γ γ.path.a = _
    rw [ha, ht.2.2.1 0 0 (by norm_num)]
    simp [h.2.1]
  · change γ γ.path.b = _
    rw [hb]
    have hlast : ((2*n+1:ℕ):ℝ) ∈
        Icc (2*((Fin.last n).val:ℝ)) (2*((Fin.last n).val:ℝ)+1) := by
      simp only [Fin.val_last, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      constructor <;> linarith
    rw [ht.2.2.1 (Fin.last n) _ hlast]
    congr 1
    push_cast
    rw [h.2.2.1]
    ring

/-- The ordered retained segments cover precisely the real interval with open dents removed. -/
theorem retained_eq_union_gaps (s : Finset ℝ) (l u : ℝ) (ε : s → ℝ)
    (n : ℕ) (e : Fin n ≃ s) (start stop : Fin (n+1) → ℝ)
    (ha : Admissible s l u ε) (hg : Gaps l u ε e start stop) :
    Retained s l u ε = ⋃ j, Icc (start j) (stop j) := by
  classical
  rcases hg with ⟨he, hfirst, hlast, hstop, hstart, hpos⟩
  have hsep (i j : Fin n) (hij : i < j) :
      (e i).val + ε (e i) < (e j).val - ε (e j) := ha.2.2 _ _ (he hij)
  have hlo : Monotone (fun i : Fin n => (e i).val - ε (e i)) := by
    intro i j hij
    rcases lt_or_eq_of_le hij with hij | rfl
    · have hp := (ha.2.1 (e i)).1
      have h := hsep i j hij
      linarith
    · rfl
  have hup : Monotone (fun i : Fin n => (e i).val + ε (e i)) := by
    intro i j hij
    rcases lt_or_eq_of_le hij with hij | rfl
    · have hp := (ha.2.1 (e j)).1
      have h := hsep i j hij
      linarith
    · rfl
  have hsl (j : Fin (n+1)) : l ≤ start j := by
    refine Fin.cases ?_ (fun i => ?_) j
    · rw [hfirst]
    · rw [hstart]
      have h := ha.2.1 (e i)
      linarith [h.1, h.2.1]
  have hsu (j : Fin (n+1)) : stop j ≤ u := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [hlast]
    · rw [hstop]
      have h := ha.2.1 (e i)
      linarith [h.1, h.2.2]
  ext x
  constructor
  · intro hx
    have hxlu := hx.1
    have hnot : ∀ a : s, ¬ (a.val - ε a < x ∧ x < a.val + ε a) := by
      simpa only [mem_iUnion, mem_Ioo, not_exists] using hx.2
    let q : Finset (Fin (n+1)) := Finset.univ.filter (fun j => x ≤ stop j)
    have hq : q.Nonempty := ⟨Fin.last n, by simp [q, hlast, hxlu.2]⟩
    let j := q.min' hq
    have hjq : x ≤ stop j := (Finset.mem_filter.mp (Finset.min'_mem q hq)).2
    have hjlo : start j ≤ x := by
      by_cases hj0 : j.val = 0
      · have hj : j = 0 := Fin.ext hj0
        simpa [hj, hfirst] using hxlu.1
      · let i : Fin n := ⟨j.val-1, by have := j.isLt; omega⟩
        have hj : i.succ = j := Fin.ext (by dsimp [i]; omega)
        have hprev : ¬ x ≤ stop i.castSucc := by
          intro hxprev
          have hm := Finset.min'_le q i.castSucc (by simp [q, hxprev])
          change j ≤ i.castSucc at hm
          have hm' : j.val ≤ i.val := hm
          dsimp [i] at hm'
          omega
        rw [hstop] at hprev
        rw [← hj, hstart]
        have hn := hnot (e i)
        exact le_of_not_gt (fun hxupper => hn ⟨lt_of_not_ge hprev, hxupper⟩)
    exact mem_iUnion.mpr ⟨j, hjlo, hjq⟩
  · intro hx
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
    refine ⟨⟨(hsl j).trans hxj.1, hxj.2.trans (hsu j)⟩, ?_⟩
    simp only [mem_iUnion, mem_Ioo, not_exists]
    intro a
    let i := e.symm a
    have hei : e i = a := e.apply_symm_apply a
    by_cases hij : i.val < j.val
    · have hib : a.val + ε a ≤ start j := by
        revert hij
        refine Fin.cases ?_ (fun k hik => ?_) j
        · simp
        · rw [hstart]
          rw [← hei]
          exact hup (by change i.val ≤ k.val; simp only [Fin.val_succ] at hik; omega)
      intro hxoo
      linarith [hxoo.2, hxj.1]
    · have hib : stop j ≤ a.val - ε a := by
        let k : Fin n := ⟨j.val, by have := i.isLt; omega⟩
        have hj : k.castSucc = j := Fin.ext rfl
        rw [← hj, hstop, ← hei]
        exact hlo (by change j.val ≤ i.val; omega)
      intro hxoo
      linarith [hxoo.1, hxj.2]

private theorem unit_interval_cover (m : ℕ) (t : ℝ) (hl : 0 ≤ t)
    (hu : t ≤ (m:ℝ)+1) : ∃ k ≤ m, t ∈ Icc (k:ℝ) (k+1) := by
  induction m with
  | zero => exact ⟨0, le_refl _, by simpa using And.intro hl hu⟩
  | succ m ih =>
    by_cases h : t ≤ (m:ℝ)+1
    · obtain ⟨k,hk,ht⟩ := ih h
      exact ⟨k, by omega, ht⟩
    · refine ⟨m+1, le_refl _, ?_⟩
      push_cast at hu ⊢
      exact ⟨by linarith, hu⟩

/-- Trace equality for every representative of the explicit traversal. -/
theorem trace_of_traversal : trace_of_traversal_type := by
  intro s l u ε n e start stop γ ha hg ht
  rw [TraceSet, retained_eq_union_gaps s l u ε n e start stop ha hg]
  ext z
  constructor
  · rintro ⟨t, htd, rfl⟩
    have htl : 0 ≤ t := by simpa only [ht.1] using htd.1
    have htu : t ≤ 2*(n:ℝ)+1 := by
      simpa only [ht.2.1, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using htd.2
    obtain ⟨k,hk,htk⟩ := unit_interval_cover (2*n) t htl (by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using htu)
    by_cases hev : k % 2 = 0
    · let j : Fin (n+1) := ⟨k/2, by omega⟩
      have hkj : k = 2*j.val := by dsimp [j]; omega
      have htm : t ∈ Icc (2*(j.val:ℝ)) (2*(j.val:ℝ)+1) := by
        simpa only [hkj, Nat.cast_mul, Nat.cast_ofNat] using htk
      left
      refine ⟨start j + (stop j-start j)*(t-2*(j.val:ℝ)),
        mem_iUnion.mpr ⟨j, ?_⟩, (ht.2.2.1 j t htm).symm⟩
      have hp := hg.2.2.2.2.2 j
      constructor <;> nlinarith [htm.1, htm.2]
    · let i : Fin n := ⟨k/2, by omega⟩
      have hki : k = 2*i.val+1 := by dsimp [i]; omega
      have htm : t ∈ Icc (2*(i.val:ℝ)+1) (2*(i.val:ℝ)+2) := by
        simpa only [hki, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add,
          Nat.cast_one, add_assoc, one_add_one_eq_two] using htk
      right
      refine mem_iUnion.mpr ⟨e i, Real.pi*(2*(i.val:ℝ)+2-t), ?_,
        (ht.2.2.2 i t htm).symm⟩
      constructor <;> nlinarith [htm.1, htm.2, Real.pi_pos]
  · rintro (hz | hz)
    · obtain ⟨x,hx,rfl⟩ := hz
      obtain ⟨j,hxj⟩ := mem_iUnion.mp hx
      have hd : 0 < stop j-start j := sub_pos.mpr (hg.2.2.2.2.2 j)
      let v := (x-start j)/(stop j-start j)
      have hv0 : 0 ≤ v := div_nonneg (sub_nonneg.mpr hxj.1) hd.le
      have hv1 : v ≤ 1 := (div_le_one hd).mpr (by linarith [hxj.2])
      let t := 2*(j.val:ℝ)+v
      have htm : t ∈ Icc (2*(j.val:ℝ)) (2*(j.val:ℝ)+1) := by
        dsimp [t]; constructor <;> linarith
      refine ⟨t, ?_, ?_⟩
      · rw [ht.1, ht.2.1]
        have hj : (j.val:ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt_succ j.isLt)
        push_cast
        constructor <;> dsimp [t] <;> nlinarith [(show (0:ℝ) ≤ j.val from Nat.cast_nonneg _)]
      · rw [ht.2.2.1 j t htm]
        congr 1
        dsimp [t, v]
        field_simp
        ring
    · obtain ⟨a,θ,hθ,rfl⟩ := mem_iUnion.mp hz
      let i := e.symm a
      have hei : e i = a := e.apply_symm_apply a
      let t := 2*(i.val:ℝ)+2-θ/Real.pi
      have hv0 : 0 ≤ θ/Real.pi := div_nonneg hθ.1 Real.pi_pos.le
      have hv1 : θ/Real.pi ≤ 1 := (div_le_one Real.pi_pos).mpr hθ.2
      have htm : t ∈ Icc (2*(i.val:ℝ)+1) (2*(i.val:ℝ)+2) := by
        dsimp [t]; constructor <;> linarith
      refine ⟨t, ?_, ?_⟩
      · rw [ht.1, ht.2.1]
        have hi : (i.val:ℝ)+1 ≤ n := by exact_mod_cast i.isLt
        push_cast
        constructor <;> dsimp [t] <;> nlinarith [(show (0:ℝ) ≤ i.val from Nat.cast_nonneg _)]
      · rw [ht.2.2.2 i t htm, hei]
        congr 1
        dsimp [t]
        field_simp
        ring

/-- Actual canonical path, all ordered traversal data, endpoints and exact trace. -/
theorem ordered_indented_diameter_exists : ordered_indented_diameter_exists_type := by
  intro s l u ε ha
  obtain ⟨n,e,start,stop,hg⟩ := ordered_gaps s l u ε ha
  obtain ⟨γ,ht,hs,hu⟩ := path_exists s l u ε n e start stop hg
  exact ⟨n,e,start,stop,γ,hg,ht,hs,hu,
    trace_of_traversal s l u ε n e start stop γ ha hg ht⟩

end D12Complex.OrderedIndentedDiameter
