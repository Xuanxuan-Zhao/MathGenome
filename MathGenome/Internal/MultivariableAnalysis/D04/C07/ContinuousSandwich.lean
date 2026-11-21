import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.ContinuousSandwich
import MathGenome.Internal.MultivariableAnalysis.D04.C07.Localization
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Tactic.FunProp

/-! The continuous sandwich from paper.tex, d04:07:sandwich.
We use cutoffs strictly inside partition cells, retaining the bounds ±M on
faces. Inner boxes give a Darboux lower-sum estimate for each cutoff integral.
A final compact cutoff places both approximants inside the prescribed open
set. All integral values are the shared Riemann/Darboux values. -/

noncomputable section
open Set Function Filter Topology
open scoped BigOperators
namespace D04.ContinuousSandwich
open Darboux JordanRegions NullCovers

/-- Continuous ambient functions are Darboux integrable on every box,
including the evaluation convention in dimension zero. -/
lemma continuous_integrable {n : ℕ} (f : E n → ℝ) (hf : Continuous f) (Q : Box n) :
    Integrable f Q := by
  cases n with
  | zero => exact (Darboux.zero_dimension Q f).2.1
  | succ n => exact ExceptionalSets.integrable_continuous (Nat.succ_pos n) Q f hf.continuousOn

/-- A compactly supported continuous ambient function whose support stays in
V gives the actual open-domain Riemann integral. -/
lemma restrict_integrable {n : ℕ} {V : Set (E n)} {f : E n → ℝ}
    (hV : IsOpen V) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hs : tsupport f ⊆ V) : OpenIntegrable (fun x : V => f x) := by
  have hc : HasCompactSupport (fun x : V => f x) := by
    apply (Localization.compact_preimage_subtype hfc hs).of_isClosed_subset
      (isClosed_tsupport _)
    exact tsupport_comp_subset_preimage f continuous_subtype_val
  exact (Localization.compact_support_integrable _ hV
    (hf.comp continuous_subtype_val) hc).2

lemma zeroExtension_restrict {n : ℕ} {V : Set (E n)} {f : E n → ℝ}
    (hs : tsupport f ⊆ V) : zeroExtension (fun x : V => f x) = f := by
  funext x
  by_cases hx : x ∈ V
  · exact zeroExtension_apply (fun x : V => f x) ⟨x, hx⟩
  · rw [zeroExtension_of_not_mem _ hx]
    exact (image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))).symm

/-- Open-domain integrals can be estimated on any box enclosing the support. -/
lemma restrict_integral_eq {n : ℕ} {V : Set (E n)} {f : E n → ℝ}
    (hV : IsOpen V) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hs : tsupport f ⊆ V) (Q : Box n) (hQ : Encloses (support f) Q) :
    openIntegral (fun x : V => f x) = integral f Q (continuous_integrable f hf Q) := by
  have hi := restrict_integrable hV hf hfc hs
  have he := zeroExtension_restrict hs
  obtain ⟨h, heq⟩ := open_integral_eq_on_enclosing_box _ hi Q (by rwa [he])
  simpa only [he] using heq

/-- Closed cells meet interiors of other cells only when the indices agree.
This is stronger than disjointness of open cells and handles face values. -/
lemma cell_eq_of_mem_open {n : ℕ} {Q : Box n} (P : Grid Q)
    {c d : CellIndex P} {x : E n} (hc : x ∈ cell P c)
    (hd : x ∈ openCarrier (cellBox P d)) : c = d := by
  funext i
  apply Fin.ext
  by_contra h
  rcases lt_or_gt_of_ne h with h | h
  · have he := (P i).strictMono.monotone
      (show (c i).succ ≤ (d i).castSucc from Nat.succ_le_of_lt h)
    have hx := hc i
    have hy := hd i
    change (P i).point (c i).castSucc ≤ x i ∧ x i ≤ (P i).point (c i).succ at hx
    change (P i).point (d i).castSucc < x i ∧ x i < (P i).point (d i).succ at hy
    linarith
  · have he := (P i).strictMono.monotone
      (show (d i).succ ≤ (c i).castSucc from Nat.succ_le_of_lt h)
    have hx := hc i
    have hy := hd i
    change (P i).point (c i).castSucc ≤ x i ∧ x i ≤ (P i).point (c i).succ at hx
    change (P i).point (d i).castSucc < x i ∧ x i < (P i).point (d i).succ at hy
    linarith

/-- Shrink a nondegenerate box strictly on every side, losing arbitrarily
little content. The proof also works for the empty coordinate set. -/
lemma exists_inner_box {n : ℕ} (Q : Box n) (hQ : Nondegenerate Q)
    {ε : ℝ} (hε : 0 < ε) : ∃ R : Box n,
      Nondegenerate R ∧ (∀ i, Q.lower i < R.lower i) ∧
      (∀ i, R.upper i < Q.upper i) ∧ content Q - ε < content R := by
  let F : ℝ → ℝ := fun t => ∏ i, ((Q.upper i - t) - (Q.lower i + t))
  have hF : Continuous F := by unfold F; fun_prop
  have h0 : F 0 = content Q := by simp [F, content, Specs.D04.C06.DarbouxIntegral.Model.content]
  have he : ∀ᶠ t in 𝓝 (0 : ℝ), content Q - ε < F t :=
    hF.continuousAt.eventually (lt_mem_nhds (by rw [h0]; linarith))
  have hw : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, Q.lower i + t < Q.upper i - t := by
    rw [Filter.eventually_all]
    intro i
    exact (continuous_const.add continuous_id).continuousAt.eventually_lt
      (continuous_const.sub continuous_id).continuousAt (by simpa using hQ i)
  obtain ⟨δ, hδ, hd⟩ := Metric.eventually_nhds_iff.mp (he.and hw)
  let t := δ / 2
  have ht : 0 < t := half_pos hδ
  have h := hd (show dist t 0 < δ by simpa only [Real.dist_eq, sub_zero, abs_of_pos ht] using half_lt_self hδ)
  let R : Box n := ⟨WithLp.toLp 2 (fun i => Q.lower i + t),
    WithLp.toLp 2 (fun i => Q.upper i - t), fun i => (h.2 i).le⟩
  refine ⟨R, h.2, ?_, ?_, h.1⟩
  · intro i; change Q.lower i < Q.lower i + t; linarith
  · intro i; change Q.upper i - t < Q.upper i; linarith

/-- A nonnegative continuous function equal to one on an inner box has
integral at least the content of that box. This uses a Darboux lower sum. -/
lemma inner_box_integral_le {n : ℕ} (Q R : Box n) (hR : Nondegenerate R)
    (hl : ∀ i, Q.lower i < R.lower i) (hu : ∀ i, R.upper i < Q.upper i)
    (ρ : E n → ℝ) (hρ : Continuous ρ) (hpos : ∀ x, 0 ≤ ρ x)
    (hone : EqOn ρ (fun _ => 1) (carrier R)) :
    content R ≤ integral ρ Q (continuous_integrable ρ hρ Q) := by
  classical
  let P : Grid Q := fun i => threePartition (Q.lower i) (R.lower i) (R.upper i)
    (Q.upper i) (hl i) (hR i) (hu i)
  let c : CellIndex P := fun _ => (1 : Fin 3)
  have hc : cellBox P c = R := by apply Subdivision.box_ext <;> ext i <;> rfl
  have hci : cellInfimum ρ P c = 1 := by
    change sInf (ρ '' carrier (cellBox P c)) = 1
    rw [hc]
    have he : ρ '' carrier R = {1} := by
      apply Set.eq_singleton_iff_nonempty_unique_mem.mpr
      exact ⟨(carrier_nonempty R).image ρ, fun y hy => by
        obtain ⟨x, hx, rfl⟩ := hy; exact hone hx⟩
    rw [he, csInf_singleton]
  calc
    content R = cellInfimum ρ P c * cellContent P c := by
      rw [hci]; change _ = 1 * content (cellBox P c); rw [hc, one_mul]
    _ ≤ lowerSum ρ P := by
      change _ ≤ ∑ d, cellInfimum ρ P d * cellContent P d
      refine Finset.single_le_sum (f := fun d => cellInfimum ρ P d * cellContent P d)
        (fun d _ => ?_) (Finset.mem_univ c)
      apply mul_nonneg _ (cellContent_nonneg P d)
      apply le_csInf ((cell_nonempty P d).image ρ)
      rintro y ⟨x, hx, rfl⟩; exact hpos x
    _ ≤ _ := (integral_bounds ρ Q (continuous_integrable ρ hρ Q) P).1

/-- Continuous cell cutoffs whose integrals lose arbitrarily little content. -/
lemma exists_cell_cutoff {n : ℕ} (Q : Box n) (hQ : Nondegenerate Q)
    {ε : ℝ} (hε : 0 < ε) : ∃ ρ : E n → ℝ,
      ∃ hρ : Continuous ρ, HasCompactSupport ρ ∧ tsupport ρ ⊆ openCarrier Q ∧
      (∀ x, ρ x ∈ Icc 0 1) ∧
      content Q - ε < integral ρ Q (continuous_integrable ρ hρ Q) := by
  obtain ⟨R, hR, hl, hu, hcont⟩ := exists_inner_box Q hQ hε
  have hsub : carrier R ⊆ openCarrier Q := by
    intro x hx i; exact ⟨(hl i).trans_le (hx i).1, (hx i).2.trans_lt (hu i)⟩
  obtain ⟨ρ, hone, hcompact, hs, hbounds⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen
      (DiscontinuityCriterion.carrier_compact R) (isOpen_openCarrier Q) hsub
  exact ⟨ρ, ρ.continuous, hcompact, hs, hbounds,
    hcont.trans_le (inner_box_integral_le Q R hR hl hu ρ ρ.continuous
      (fun x => (hbounds x).1) hone)⟩

/-- Interior cell cutoffs vanish on every other closed cell. -/
lemma sum_cutoffs_on_cell {n : ℕ} {Q : Box n} (P : Grid Q)
    (ρ : CellIndex P → E n → ℝ)
    (hs : ∀ c, tsupport (ρ c) ⊆ openCarrier (cellBox P c))
    (w : CellIndex P → ℝ) (c : CellIndex P) {x : E n} (hx : x ∈ cell P c) :
    (∑ d, w d * ρ d x) = w c * ρ c x := by
  classical
  apply Finset.sum_eq_single c
  · intro d _ hdc
    have hz : ρ d x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hdc (cell_eq_of_mem_open P hx (hs d h)).symm)
    rw [hz, mul_zero]
  · simp

/-- The infima and suprema really lie within any bound on the original
function, with no attainment assumption. -/
lemma cell_extrema_bounds {n : ℕ} {Q : Box n} {f : E n → ℝ}
    (P : Grid Q) (hf : Bounded f Q) {M : ℝ}
    (hM : ∀ x ∈ carrier Q, |f x| ≤ M) (c : CellIndex P) :
    -M ≤ cellInfimum f P c ∧ cellInfimum f P c ≤ cellSupremum f P c ∧
      cellSupremum f P c ≤ M := by
  have hlo : -M ≤ cellInfimum f P c := by
    apply le_csInf ((cell_nonempty P c).image f)
    rintro y ⟨x, hx, rfl⟩
    exact (abs_le.mp (hM x (cell_subset P c hx))).1
  have hhi : cellSupremum f P c ≤ M := by
    apply csSup_le ((cell_nonempty P c).image f)
    rintro y ⟨x, hx, rfl⟩
    exact (abs_le.mp (hM x (cell_subset P c hx))).2
  obtain ⟨x, hx⟩ := cell_nonempty P c
  exact ⟨hlo, (cellInfimum_le f hf P c hx).trans (le_cellSupremum f hf P c hx), hhi⟩

/-- Continuous pointwise upper and lower bounds on a box with arbitrarily
small Riemann integral gap, including bounds at every partition face. -/
lemma box_sandwich {n : ℕ} {Q : Box n} (hQ : Nondegenerate Q)
    (f : E n → ℝ) (hf : Integrable f Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ hLower hUpper : E n → ℝ,
      Continuous hLower ∧ Continuous hUpper ∧
      (∀ x ∈ carrier Q, hLower x ≤ f x ∧ f x ≤ hUpper x) ∧
      lowerIntegral (fun x => hUpper x - hLower x) Q < ε := by
  classical
  obtain ⟨M, hM0, hM⟩ := exists_abs_bound hf.1
  obtain ⟨P, hP⟩ := (integrable_iff_gap f Q hf.1).mp hf (ε / 2) (half_pos hε)
  let N : ℝ := Fintype.card (CellIndex P)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  let δ := ε / (2 * ((2 * M + 1) * (N + 1)))
  have hden : 0 < 2 * ((2 * M + 1) * (N + 1)) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hδeq : δ * (2 * ((2 * M + 1) * (N + 1))) = ε :=
    div_mul_cancel₀ _ (ne_of_gt hden)
  choose ρ hρc hρk hρs hρb hρI using
    (show ∀ c : CellIndex P, ∃ ρ : E n → ℝ, ∃ hρ : Continuous ρ,
      HasCompactSupport ρ ∧ tsupport ρ ⊆ openCarrier (cellBox P c) ∧
      (∀ x, ρ x ∈ Icc 0 1) ∧
      content (cellBox P c) - δ < integral ρ (cellBox P c)
        (continuous_integrable ρ hρ (cellBox P c)) from
      fun c => exists_cell_cutoff (cellBox P c)
        (ExceptionalSets.cellBox_nondegenerate P c) hδ)
  let u : CellIndex P → ℝ := fun c => M - cellSupremum f P c
  let l : CellIndex P → ℝ := fun c => cellInfimum f P c + M
  let hUpper : E n → ℝ := fun x => M - ∑ c, u c * ρ c x
  let hLower : E n → ℝ := fun x => -M + ∑ c, l c * ρ c x
  have hUc : Continuous hUpper := continuous_const.sub
    (continuous_finsetSum _ fun c _ => continuous_const.mul (hρc c))
  have hLc : Continuous hLower := continuous_const.add
    (continuous_finsetSum _ fun c _ => continuous_const.mul (hρc c))
  have hDiff : Continuous (fun x => hUpper x - hLower x) := hUc.sub hLc
  have hUcell (c : CellIndex P) {x : E n} (hx : x ∈ cell P c) :
      hUpper x = M - u c * ρ c x := by
    exact congrArg (M - ·) (sum_cutoffs_on_cell P ρ hρs u c hx)
  have hLcell (c : CellIndex P) {x : E n} (hx : x ∈ cell P c) :
      hLower x = -M + l c * ρ c x := by
    exact congrArg (-M + ·) (sum_cutoffs_on_cell P ρ hρs l c hx)
  have hbound : ∀ x ∈ carrier Q, hLower x ≤ f x ∧ f x ≤ hUpper x := by
    intro x hx
    rw [cells_cover Q hQ P] at hx
    obtain ⟨c, hc⟩ := mem_iUnion.mp hx
    rw [hUcell c hc, hLcell c hc]
    have he := cell_extrema_bounds P hf.1 hM c
    have hmulU := mul_le_of_le_one_right (sub_nonneg.mpr he.2.2) (hρb c x).2
    have hmulL := mul_le_of_le_one_right (show 0 ≤ l c by dsimp [l]; linarith) (hρb c x).2
    have hlo := cellInfimum_le f hf.1 P c hc
    have hhi := le_cellSupremum f hf.1 P c hc
    dsimp [u, l] at *
    constructor <;> linarith
  have hcellI (c : CellIndex P) :
      lowerIntegral (fun x => hUpper x - hLower x) (cellBox P c) ≤
        (cellSupremum f P c - cellInfimum f P c) * cellContent P c + 2 * M * δ := by
    let A : ℝ := 2 * M - (cellSupremum f P c - cellInfimum f P c)
    have he := cell_extrema_bounds P hf.1 hM c
    have hA0 : 0 ≤ A := by dsimp [A]; linarith
    have hA : A ≤ 2 * M := by dsimp [A]; linarith
    have heq : EqOn (fun x => hUpper x - hLower x)
        (fun x => 2 * M - A * ρ c x) (carrier (cellBox P c)) := by
      intro x hx
      change hUpper x - hLower x = _
      rw [hUcell c hx, hLcell c hx]
      dsimp [u, l, A]; ring
    have hi := continuous_integrable (ρ c) (hρc c) (cellBox P c)
    have hsm := integrable_smul A hi
    have hconst := integrable_const (cellBox P c) (2 * M)
    have hsub := integrable_sub hconst hsm
    have heval : lowerIntegral (fun x => hUpper x - hLower x) (cellBox P c) =
        2 * M * cellContent P c - A * lowerIntegral (ρ c) (cellBox P c) := by
      calc
        _ = lowerIntegral (fun x => 2 * M - A * ρ c x) (cellBox P c) := lowerIntegral_congr heq
        _ = _ := by
          change integral _ _ hsub = _
          rw [integral_sub hconst hsm hsub, integral_smul A hi hsm,
            integral_const (cellBox P c) (2 * M) hconst]
          rfl
    rw [heval]
    have hloss := mul_le_mul_of_nonneg_left (hρI c).le hA0
    have herr := mul_le_mul_of_nonneg_right hA hδ.le
    change A * (cellContent P c - δ) ≤ A * lowerIntegral (ρ c) (cellBox P c) at hloss
    dsimp [A] at hloss herr ⊢
    nlinarith
  have hi := continuous_integrable (fun x => hUpper x - hLower x) hDiff Q
  have hic c := continuous_integrable (fun x => hUpper x - hLower x) hDiff (cellBox P c)
  have hsum := subdivision_integral (fun x => hUpper x - hLower x) Q P hi hic
  have herr : 2 * M * δ * N < ε / 2 := by
    have hcoef : 2 * M * N < (2 * M + 1) * (N + 1) := by nlinarith
    have hm := mul_lt_mul_of_pos_right hcoef hδ
    nlinarith [hδeq]
  refine ⟨hLower, hUpper, hLc, hUc, hbound, ?_⟩
  calc
    _ = ∑ c, lowerIntegral (fun x => hUpper x - hLower x) (cellBox P c) := hsum
    _ ≤ ∑ c, ((cellSupremum f P c - cellInfimum f P c) * cellContent P c + 2 * M * δ) :=
      Finset.sum_le_sum (fun c _ => hcellI c)
    _ = upperSum f P - lowerSum f P + 2 * M * δ * N := by
      simp only [Finset.sum_add_distrib, sub_mul, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      dsimp [upperSum, lowerSum, Specs.D04.C06.DarbouxIntegral.Model.upperSum,
        Specs.D04.C06.DarbouxIntegral.Model.lowerSum, N]
      ring
    _ < ε := by linarith

/-- Localizing box bounds by a cutoff preserves the inequalities everywhere:
on K the cutoff is one; off K the original function is zero. -/
lemma localize_box_sandwich {n : ℕ} {V K : Set (E n)} {f : E n → ℝ}
    (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V) (hsf : tsupport f ⊆ K)
    (Q : Box n) (hKQ : Encloses K Q) {hLower hUpper : E n → ℝ}
    (hLc : Continuous hLower) (hUc : Continuous hUpper)
    (hbound : ∀ x ∈ carrier Q, hLower x ≤ f x ∧ f x ≤ hUpper x)
    {ε : ℝ} (hgap : lowerIntegral (fun x => hUpper x - hLower x) Q < ε) :
    ∃ gLower gUpper : E n → ℝ,
      Continuous gLower ∧ Continuous gUpper ∧
      HasCompactSupport gLower ∧ HasCompactSupport gUpper ∧
      tsupport gLower ⊆ V ∧ tsupport gUpper ⊆ V ∧
      (∀ x, gLower x ≤ f x ∧ f x ≤ gUpper x) ∧
      OpenIntegrable (fun x : V => gLower x) ∧
      OpenIntegrable (fun x : V => gUpper x) ∧
      OpenIntegrable (fun x : V => gUpper x - gLower x) ∧
      openIntegral (fun x : V => gUpper x - gLower x) < ε := by
  have hsub : K ⊆ V ∩ interior (carrier Q) :=
    fun x hx => ⟨hKV hx, hKQ (subset_closure hx)⟩
  obtain ⟨η, hηone, hηk, hηs, hηb⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK (hV.inter isOpen_interior) hsub
  have hηkc : HasCompactSupport (η : E n → ℝ) := hηk
  let gLower : E n → ℝ := fun x => η x * hLower x
  let gUpper : E n → ℝ := fun x => η x * hUpper x
  let d : E n → ℝ := fun x => gUpper x - gLower x
  have hgcL : Continuous gLower := η.continuous.mul hLc
  have hgcU : Continuous gUpper := η.continuous.mul hUc
  have hgd : Continuous d := hgcU.sub hgcL
  have hgkL : HasCompactSupport gLower := hηkc.mul_right
  have hgkU : HasCompactSupport gUpper := hηkc.mul_right
  have hsd : tsupport d ⊆ tsupport (η : E n → ℝ) := by
    have he : d = fun x => η x * (hUpper x - hLower x) := by funext x; dsimp [d, gUpper, gLower]; ring
    rw [he]
    exact tsupport_mul_subset_left
  have hgkd : HasCompactSupport d := hηk.of_isClosed_subset (isClosed_tsupport d) hsd
  have hgsL : tsupport gLower ⊆ V := tsupport_mul_subset_left.trans (hηs.trans inter_subset_left)
  have hgsU : tsupport gUpper ⊆ V := tsupport_mul_subset_left.trans (hηs.trans inter_subset_left)
  have hgsd : tsupport d ⊆ V := hsd.trans (hηs.trans inter_subset_left)
  have hglobal : ∀ x, gLower x ≤ f x ∧ f x ≤ gUpper x := by
    intro x
    by_cases hx : x ∈ K
    · have hηx : η x = 1 := hηone hx
      dsimp [gLower, gUpper]
      rw [hηx, one_mul, one_mul]
      exact hbound x (encloses_subset hKQ hx)
    · have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hsf h))
      rw [hfx]
      by_cases hxQ : x ∈ carrier Q
      · have hb := hbound x hxQ
        rw [hfx] at hb
        exact ⟨mul_nonpos_of_nonneg_of_nonpos (hηb x).1 hb.1,
          mul_nonneg (hηb x).1 hb.2⟩
      · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport
          (fun h => hxQ (interior_subset (hηs h).2))
        dsimp [gLower, gUpper]; simp [hηx]
  have hQd : Encloses (support d) Q := hsd.trans (hηs.trans inter_subset_right)
  have hIntL := restrict_integrable hV hgcL hgkL hgsL
  have hIntU := restrict_integrable hV hgcU hgkU hgsU
  have hIntd := restrict_integrable hV hgd hgkd hgsd
  refine ⟨gLower, gUpper, hgcL, hgcU, hgkL, hgkU, hgsL, hgsU,
    hglobal, hIntL, hIntU, hIntd, ?_⟩
  calc
    openIntegral (fun x : V => d x) =
        integral d Q (continuous_integrable d hgd Q) :=
      restrict_integral_eq hV hgd hgkd hgsd Q hQd
    _ ≤ integral (fun x => hUpper x - hLower x) Q
        (continuous_integrable _ (hUc.sub hLc) Q) := by
      apply integral_mono
      intro x hx
      have hb := hbound x hx
      have hd : 0 ≤ hUpper x - hLower x := by linarith [hb.1, hb.2]
      change η x * hUpper x - η x * hLower x ≤ _
      rw [← mul_sub]
      exact mul_le_of_le_one_left hd (hηb x).2
    _ < ε := hgap

/-- The continuous case, including the zero function and R^0. -/
lemma continuous_case {n : ℕ} (V K : Set (E n)) (f : E n → ℝ)
    (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V) (hsf : tsupport f ⊆ K)
    (hf : Continuous f) (ε : ℝ) (hε : 0 < ε) :
    ∃ gLower gUpper : E n → ℝ,
      Continuous gLower ∧ Continuous gUpper ∧
      HasCompactSupport gLower ∧ HasCompactSupport gUpper ∧
      tsupport gLower ⊆ V ∧ tsupport gUpper ⊆ V ∧
      (∀ x, gLower x ≤ f x ∧ f x ≤ gUpper x) ∧
      OpenIntegrable (fun x : V => gLower x) ∧
      OpenIntegrable (fun x : V => gUpper x) ∧
      OpenIntegrable (fun x : V => gUpper x - gLower x) ∧
      openIntegral (fun x : V => gUpper x - gLower x) < ε := by
  obtain ⟨Q, hQ⟩ := (encloses_exists_iff_bounded K).mpr hK.isBounded
  apply localize_box_sandwich hV hK hKV hsf Q hQ hf hf
    (fun _ _ => ⟨le_rfl, le_rfl⟩)
  have hz : (fun x => f x - f x) = (fun _ : E n => (0 : ℝ)) := by funext x; ring
  rw [hz, (constant_integrals Q 0).1, zero_mul]
  exact hε

/-- Global boundedness follows from boundedness on a box enclosing the
actual support. No relationship to a larger compact containing set is needed. -/
lemma bounded_on_every_box {n : ℕ} {f : E n → ℝ} {Q : Box n}
    (hQ : Encloses (support f) Q) (hf : Bounded f Q) (R : Box n) : Bounded f R := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_bound hf
  apply bounded_of_abs_le (M := M)
  intro x _
  by_cases hx : x ∈ carrier Q
  · exact hM x hx
  · have hfx : f x = 0 := notMem_support.mp (fun h => hx (encloses_subset hQ h))
    simpa [hfx] using hM0

/-- Continuous pointwise upper and lower approximants, with compact support
inside the prescribed open set and arbitrarily small Riemann integral gap. -/
theorem continuous_sandwich :
    Specs.D04.C07.ContinuousSandwich.continuous_sandwichType := by
  intro n V K f hV hK hKV hsf hInt ε hε
  by_cases hKne : K.Nonempty
  · obtain ⟨R, hR, hfR⟩ := hInt
    obtain ⟨Q, hKQ⟩ := (encloses_exists_iff_bounded K).mpr hK.isBounded
    have hQf : Encloses (support f) Q :=
      (closure_mono ((subset_tsupport f).trans hsf)).trans hKQ
    have hfQ : Integrable f Q :=
      (supported_box_independence hR hQf (fun _ hx => notMem_support.mp hx)
        (bounded_on_every_box hR hfR.1)).1.mp hfR
    have hQ : Nondegenerate Q := by
      obtain ⟨x, hx⟩ := hKne
      have hxi := encloses_open hKQ (subset_closure hx)
      exact fun i => (hxi i).1.trans (hxi i).2
    obtain ⟨hLower, hUpper, hLc, hUc, hbounds, hgap⟩ := box_sandwich hQ f hfQ hε
    exact localize_box_sandwich hV hK hKV hsf Q hKQ hLc hUc hbounds hgap
  · have hfzero : f = fun _ => 0 := by
      funext x
      exact image_eq_zero_of_notMem_tsupport (fun h => hKne ⟨x, hsf h⟩)
    exact continuous_case V K f hV hK hKV hsf (by rw [hfzero]; exact continuous_const) ε hε

end D04.ContinuousSandwich
