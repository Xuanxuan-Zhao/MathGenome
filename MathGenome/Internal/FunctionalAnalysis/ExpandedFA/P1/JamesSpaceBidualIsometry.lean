import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.JamesSpaceBidualIsometry
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.JamesSpaceBidual

set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
namespace ExpandedFA.P1.JamesBidualIsometry
open JamesBidualSpec

/-- Energy of a path starting at `t` and closing at `s`. -/
def path (s t : ℝ) : List ℝ → ℝ
  | [] => (t-s)^2
  | x :: l => (t-x)^2 + path s x l

def cycle : List ℝ → ℝ
  | [] => 0
  | x :: l => path x x l

lemma path_repeat (s t u : ℝ) (n : ℕ) :
    path s t (List.replicate (n+1) u) = (t-u)^2 + (u-s)^2 := by
  induction n generalizing t with
  | zero => simp [path]
  | succ n ih => rw [List.replicate_succ, path, ih]; simp

lemma path_append_repeat (s t u : ℝ) (l : List ℝ) (n : ℕ) :
    path s t (l ++ List.replicate (n+1) u) = path u t l + (u-s)^2 := by
  induction l generalizing t with
  | nil => simp [path_repeat, path]
  | cons x l ih => simp [path, ih, add_assoc]

lemma cycle_append_repeat (u : ℝ) (l : List ℝ) (n : ℕ) :
    cycle (l ++ List.replicate (n+1) u) = cycle (u :: l) := by
  cases l with
  | nil =>
    cases n with
    | zero => simp [cycle, path]
    | succ n => rw [List.nil_append, List.replicate_succ]; simp only [cycle, path_repeat]; simp [path]
  | cons x l => simp only [List.cons_append, cycle, path, path_append_repeat]; ring

lemma path_sub_const (s t L : ℝ) (l : List ℝ) :
    path (s-L) (t-L) (l.map (fun x => x-L)) = path s t l := by
  induction l generalizing t with
  | nil => simp [path]
  | cons x l ih => simp only [List.map_cons, path, ih]; congr 1; ring

lemma cycle_sub_const (l : List ℝ) (L : ℝ) :
    cycle (l.map (fun x => x-L)) = cycle l := by
  cases l with
  | nil => rfl
  | cons x l => exact path_sub_const x x L l

lemma path_ofFn (s : ℝ) {n : ℕ} (v : Fin (n+1) → ℝ) :
    path s (v 0) (List.ofFn (fun i : Fin n => v i.succ)) =
      (∑ i : Fin n, (v i.castSucc - v i.succ)^2) + (v (Fin.last n)-s)^2 := by
  induction n with
  | zero => simp [path]
  | succ n ih =>
    rw [List.ofFn_succ, path, Fin.sum_univ_succ]
    have hh := ih (fun i => v i.succ)
    simp only [Fin.succ_zero_eq_one, Fin.castSucc_zero, Fin.succ_castSucc,
      Fin.succ_last] at *
    rw [hh]
    ring

lemma cycle_ofFn (a : ℕ → ℝ) (k : ℕ) (p : Fin (k+2) → ℕ) :
    cycle ((List.ofFn p).map a) = James.cyclicEnergy a k p := by
  rw [List.map_ofFn, List.ofFn_succ]
  exact path_ofFn (a (p 0)) (a ∘ p)

/-- A bound on all increasing finite cyclic lists. Empty and singleton lists
have energy zero and are included for convenient list manipulations. -/
def TestBound (a : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ l : List ℕ, l.Pairwise (· < ·) → cycle (l.map a) ≤ 2*C^2

lemma tests_of_variation (a : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ k p, StrictMono p → James.variation a k p ≤ C) : TestBound a C := by
  intro l hl
  cases l with
  | nil => simp [cycle]; positivity
  | cons i l =>
    cases l with
    | nil => simp [cycle, path]; positivity
    | cons j l =>
      have hp : StrictMono (List.get (i :: j :: l)) := List.pairwise_iff_get.mp hl
      have hh := JamesBidual.energy_of_variation_bound a hC h l.length _ hp
      rw [← cycle_ofFn, List.ofFn_get] at hh
      exact hh

lemma variation_of_tests (a : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : TestBound a C) (k : ℕ) (p : Fin (k+2) → ℕ) (hp : StrictMono p) :
    James.variation a k p ≤ C := by
  have hh := h (List.ofFn p) (List.pairwise_ofFn.mpr hp)
  rw [cycle_ofFn] at hh
  rw [James.variation, James.probe_norm, one_div_mul_eq_div]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2))).mpr
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg hC (Real.sqrt_nonneg _), ?_⟩
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]

/-- Insert the optional zero entry before the sequence. -/
def prepend (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => a n

def cut (a : ℕ → ℝ) (N n : ℕ) : ℝ := if n < N then a n else 0

lemma split_cut (l : List ℕ) (hl : l.Pairwise (· < ·)) (N : ℕ) :
    ∃ u v : List ℕ, l = u ++ v ∧
      (∀ i ∈ u, i < N) ∧ (∀ i ∈ v, N ≤ i) := by
  induction l with
  | nil => exact ⟨[], [], rfl, by simp, by simp⟩
  | cons i l ih =>
    obtain ⟨hi, ht⟩ := List.pairwise_cons.mp hl
    by_cases h : i < N
    · obtain ⟨u, v, rfl, hu, hv⟩ := ih ht
      exact ⟨i::u, v, rfl, by simpa using And.intro h hu, hv⟩
    · refine ⟨[], i::l, rfl, by simp, ?_⟩
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · omega
      · have := hi j hj; omega

lemma tests_cut_of_prepend (a : ℕ → ℝ) {C : ℝ} (h : TestBound (prepend a) C)
    (N : ℕ) : TestBound (cut a N) C := by
  intro l hl
  obtain ⟨u, v, rfl, hu, hv⟩ := split_cut l hl N
  have hpu : u.Pairwise (· < ·) := (List.pairwise_append.mp hl).1
  have humap : u.map (cut a N) = u.map a := by
    apply List.map_congr_left
    intro n hn
    simp [cut, hu n hn]
  have hvmap : v.map (cut a N) = List.replicate v.length 0 := by
    apply List.map_eq_replicate_iff.mpr
    intro n hn
    simp [cut, not_lt.mpr (hv n hn)]
  rw [List.map_append, humap, hvmap]
  have hsort : (u.map Nat.succ).Pairwise (· < ·) :=
    hpu.map _ (fun _ _ hh => Nat.succ_lt_succ hh)
  cases v with
  | nil =>
    have hh := h (u.map Nat.succ) hsort
    simpa [List.map_map, Function.comp_def, prepend] using hh
  | cons j v =>
    rw [List.length_cons, cycle_append_repeat]
    have hh := h (0 :: u.map Nat.succ) (List.pairwise_cons.mpr
      ⟨by simp, hsort⟩)
    simpa [List.map_map, Function.comp_def, prepend] using hh

lemma tests_prepend_of_cut (a : ℕ → ℝ) {C : ℝ}
    (h : ∀ N, TestBound (cut a N) C) : TestBound (prepend a) C := by
  have hplain (u : List ℕ) (hu : u.Pairwise (· < ·)) :
      cycle (u.map a) ≤ 2*C^2 := by
    have hh := h (u.sum+1) u hu
    have heq : u.map (cut a (u.sum+1)) = u.map a := by
      apply List.map_congr_left
      intro i hi
      have := List.le_sum_of_mem hi
      simp [cut, show i < u.sum+1 by omega]
    rwa [heq] at hh
  have hzero (u : List ℕ) (hu : u.Pairwise (· < ·)) :
      cycle (0 :: u.map a) ≤ 2*C^2 := by
    let N := u.sum+1
    have hi (i : ℕ) (hi : i ∈ u) : i < N := by
      have := List.le_sum_of_mem hi
      dsimp [N]; omega
    have hs : (u ++ [N]).Pairwise (· < ·) := by
      simpa [List.pairwise_append] using And.intro hu hi
    have hh := h N (u ++ [N]) hs
    have heq : (u ++ [N]).map (cut a N) = u.map a ++ [0] := by
      rw [List.map_append]
      congr 1
      · apply List.map_congr_left
        intro i hii
        simp [cut, hi i hii]
      · simp [cut]
    rw [heq] at hh
    simpa only [show [(0:ℝ)] = List.replicate (0+1) 0 from rfl,
      cycle_append_repeat] using hh
  intro l hl
  cases l with
  | nil => exact hplain [] (by simp)
  | cons i l =>
    obtain ⟨hi, ht⟩ := List.pairwise_cons.mp hl
    have hpos (j : ℕ) (hj : j ∈ l) : 0 < j := lt_of_le_of_lt (Nat.zero_le i) (hi j hj)
    have hsort : (l.map (fun j => j-1)).Pairwise (· < ·) := by
      apply List.Pairwise.map (fun j : ℕ => j-1) (fun _ _ hh => hh)
      exact ht.imp_of_mem (fun hj hk hjk => by have := hpos _ hj; omega)
    have heq : l.map (prepend a) = (l.map (fun j => j-1)).map a := by
      rw [List.map_map]
      apply List.map_congr_left
      intro j hj
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (hpos j hj))
      simp [prepend]
    cases i with
    | zero => simpa only [List.map_cons, prepend, heq] using hzero _ hsort
    | succ i =>
      have hs : ((i::l.map (fun j => j-1))).Pairwise (· < ·) := by
        apply List.pairwise_cons.mpr
        refine ⟨?_, hsort⟩
        intro j hj
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
        have := hi k hk
        omega
      simpa only [List.map_cons, prepend, heq] using hplain _ hs

lemma tests_sub_const (a : ℕ → ℝ) (L C : ℝ) :
    TestBound (fun n => a n-L) C ↔ TestBound a C := by
  unfold TestBound
  simp only [show (fun n => a n-L) = (fun x => x-L) ∘ a from rfl,
    ← List.map_map, cycle_sub_const]

section Model
variable (m : JamesBanachBasisSpec.BanachBasisModel)
local instance : CompleteSpace (ModelSpace m) := m.complete
local instance : NormedAddCommGroup (Dual m) := inferInstance
local instance : NormedSpace ℝ (Dual m) := inferInstance
local instance : NormedAddCommGroup (Bidual m) := inferInstance
local instance : NormedSpace ℝ (Bidual m) := inferInstance

lemma model_norm_le_iff (x : ModelSpace m) {C : ℝ} (hC : 0 ≤ C) :
    ‖x‖ ≤ C ↔ TestBound x.val C := by
  have hm : ‖x‖ = JamesSpec.normValue x := m.norm_eq x
  rw [hm]
  constructor
  · intro hx
    apply tests_of_variation x.val hC
    intro k p hp
    have hh := James.variation_le_norm x k p hp
    change James.variation x.val k p ≤ JamesSpec.normValue x at hh
    exact hh.trans hx
  · intro hx
    exact James.norm_le_of_variation_le x hC (variation_of_tests x.val hC hx)

lemma initial_bound_iff (a : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C) (N : ℕ) :
    ‖initialSum m a N‖ ≤ C ↔ TestBound (cut a N) C := by
  rw [model_norm_le_iff m _ hC, JamesBidual.initialSum_val]
  rfl

/-- The finite-list argument characterizes the initial-sum norm exactly. -/
lemma prepend_bound_iff (a : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C) :
    TestBound (prepend a) C ↔ ∀ N, ‖initialSum m a N‖ ≤ C := by
  constructor
  · intro h N
    exact (initial_bound_iff m a hC N).mpr (tests_cut_of_prepend a h N)
  · intro h
    exact tests_prepend_of_cut a (fun N => (initial_bound_iff m a hC N).mp (h N))

variable (b : SchauderBasis ℝ (ModelSpace m))
  (he : b.basis = m.e) (hc : ∀ i x, b.coord i x = x.val i)

/-- The unique scalar limit of the actual bidual coefficients. -/
def coefficientLimit (Φ : Bidual m) : ℝ :=
  (JamesBidual.bounded_decomposition m (coefficientMap m b Φ)
    (JamesBidual.bounded_coefficients m b he hc Φ)).exists.choose

lemma coefficientLimit_tendsto (Φ : Bidual m) :
    Tendsto (coefficientMap m b Φ) atTop (𝓝 (coefficientLimit m b he hc Φ)) :=
  (JamesBidual.bounded_decomposition m (coefficientMap m b Φ)
    (JamesBidual.bounded_coefficients m b he hc Φ)).exists.choose_spec.1

lemma coefficientLimit_add (Φ Ψ : Bidual m) :
    coefficientLimit m b he hc (Φ+Ψ) =
      coefficientLimit m b he hc Φ + coefficientLimit m b he hc Ψ :=
  tendsto_nhds_unique (coefficientLimit_tendsto m b he hc (Φ+Ψ))
    ((coefficientLimit_tendsto m b he hc Φ).add (coefficientLimit_tendsto m b he hc Ψ))

lemma coefficientLimit_smul (c : ℝ) (Φ : Bidual m) :
    coefficientLimit m b he hc (c • Φ) = c * coefficientLimit m b he hc Φ :=
  tendsto_nhds_unique (coefficientLimit_tendsto m b he hc (c • Φ))
    ((coefficientLimit_tendsto m b he hc Φ).const_smul c)

lemma transformed_mem (Φ : Bidual m) :
    JamesSpec.membershipValue
      (fun n => prepend (coefficientMap m b Φ) n - coefficientLimit m b he hc Φ) := by
  have ht : TestBound
      (fun n => prepend (coefficientMap m b Φ) n - coefficientLimit m b he hc Φ) ‖Φ‖ := by
    apply (tests_sub_const _ _ _).mpr
    exact (prepend_bound_iff m _ (norm_nonneg Φ)).mpr
      (JamesBidual.coefficient_initialSum_bound m b he hc Φ)
  refine ⟨?_, ?_⟩
  · apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [prepend, sub_self] using
      (coefficientLimit_tendsto m b he hc Φ).sub_const (coefficientLimit m b he hc Φ)
  · change James.enorm (fun n => prepend (coefficientMap m b Φ) n -
      coefficientLimit m b he hc Φ) ≠ ⊤
    apply ne_top_of_le_ne_top (ENNReal.ofReal_ne_top : ENNReal.ofReal ‖Φ‖ ≠ ⊤)
    exact James.enorm_le_of_variation_le (fun k p hp => ENNReal.ofReal_le_ofReal
      (variation_of_tests _ (norm_nonneg Φ) ht k p hp))

/-- The source's map T, as an element of the prescribed James sequence space. -/
def transform (Φ : Bidual m) : ModelSpace m :=
  ⟨fun n => prepend (coefficientMap m b Φ) n - coefficientLimit m b he hc Φ,
    transformed_mem m b he hc Φ⟩

lemma transform_norm (Φ : Bidual m) : ‖transform m b he hc Φ‖ = ‖Φ‖ := by
  apply le_antisymm
  · apply (model_norm_le_iff m _ (norm_nonneg Φ)).mpr
    apply (tests_sub_const _ _ _).mpr
    exact (prepend_bound_iff m _ (norm_nonneg Φ)).mpr
      (JamesBidual.coefficient_initialSum_bound m b he hc Φ)
  · rw [JamesBidual.coefficient_norm m b he hc]
    apply csSup_le (Set.range_nonempty _)
    rintro r ⟨N, rfl⟩
    have ht := (model_norm_le_iff m (transform m b he hc Φ)
      (norm_nonneg (transform m b he hc Φ))).mp le_rfl
    have hpre := (tests_sub_const _ _ _).mp ht
    exact (prepend_bound_iff m _ (norm_nonneg (transform m b he hc Φ))).mp hpre N

/-- Linearity includes the limit term; limits are unique over the real field. -/
def transformLinear : Bidual m →ₗ[ℝ] ModelSpace m where
  toFun := transform m b he hc
  map_add' Φ Ψ := by
    apply Subtype.ext
    have hh : (transform m b he hc Φ + transform m b he hc Ψ).val =
        fun n => (transform m b he hc Φ).val n + (transform m b he hc Ψ).val n := m.add_eq _ _
    rw [hh]
    funext n
    change prepend (coefficientMap m b (Φ+Ψ)) n - coefficientLimit m b he hc (Φ+Ψ) = _
    rw [coefficientLimit_add]
    cases n <;> simp [transform, prepend, map_add] <;> ring
  map_smul' c Φ := by
    apply Subtype.ext
    change (transform m b he hc (c • Φ)).val = (c • transform m b he hc Φ).val
    have hh : (c • transform m b he hc Φ).val =
        fun n => c * (transform m b he hc Φ).val n := m.smul_eq _ _
    rw [hh]
    funext n
    change prepend (coefficientMap m b (c • Φ)) n - coefficientLimit m b he hc (c • Φ) = _
    rw [coefficientLimit_smul]
    cases n <;> simp [transform, prepend, map_smul, smul_eq_mul]; ring

lemma transform_surjective : Function.Surjective (transform m b he hc) := by
  intro x
  let a : ℕ → ℝ := fun n => x.val (n+1) - x.val 0
  have hpre : prepend a = fun n => x.val n - x.val 0 := by
    funext n
    cases n <;> simp [prepend, a]
  have ht : TestBound (prepend a) ‖x‖ := by
    rw [hpre]
    apply (tests_sub_const _ _ _).mpr
    exact (model_norm_le_iff m x (norm_nonneg x)).mp le_rfl
  have ha : Bounded m a := ⟨‖x‖, by
    rintro r ⟨N, rfl⟩
    exact (prepend_bound_iff m a (norm_nonneg x)).mp ht N⟩
  obtain ⟨Φ, hΦ⟩ := JamesBidual.exists_bidual_of_bounded m b he hc a ha
  have hlim : Tendsto a atTop (𝓝 (-x.val 0)) := by
    simpa only [zero_sub, Function.comp_def, a] using
      (x.property.1.comp (tendsto_add_atTop_nat 1)).sub_const (x.val 0)
  have hL : coefficientLimit m b he hc Φ = -x.val 0 := by
    have hh := coefficientLimit_tendsto m b he hc Φ
    rw [hΦ] at hh
    exact tendsto_nhds_unique hh hlim
  refine ⟨Φ, ?_⟩
  apply Subtype.ext
  funext n
  change prepend (coefficientMap m b Φ) n - coefficientLimit m b he hc Φ = x.val n
  rw [hΦ, hpre, hL]
  ring

/-- The noncanonical real-linear isometric equivalence, with the source's
forward map as its function. -/
def bidualIsometry : Bidual m ≃ₗᵢ[ℝ] ModelSpace m :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := transformLinear m b he hc
      norm_map' := transform_norm m b he hc }
    (transform_surjective m b he hc)

lemma bidualIsometry_forward (Φ : Bidual m) (L : ℝ)
    (hL : Tendsto (coefficientMap m b Φ) atTop (𝓝 L)) :
    (bidualIsometry m b he hc Φ).val 0 = -L ∧
      ∀ n, (bidualIsometry m b he hc Φ).val (n+1) = coefficientMap m b Φ n - L := by
  have hh : coefficientLimit m b he hc Φ = L :=
    tendsto_nhds_unique (coefficientLimit_tendsto m b he hc Φ) hL
  change 0 - coefficientLimit m b he hc Φ = -L ∧ _
  rw [hh]
  refine ⟨zero_sub L, fun n => ?_⟩
  change coefficientMap m b Φ n - coefficientLimit m b he hc Φ = _
  rw [hh]

lemma bidualIsometry_inverse (x : ModelSpace m) (n : ℕ) :
    coefficientMap m b ((bidualIsometry m b he hc).symm x) n =
      x.val (n+1) - x.val 0 := by
  let e := bidualIsometry m b he hc
  have h0 := congrArg (fun y : ModelSpace m => y.val 0) (e.apply_symm_apply x)
  have hn := congrArg (fun y : ModelSpace m => y.val (n+1)) (e.apply_symm_apply x)
  change 0 - coefficientLimit m b he hc (e.symm x) = x.val 0 at h0
  change coefficientMap m b (e.symm x) n - coefficientLimit m b he hc (e.symm x) =
    x.val (n+1) at hn
  change coefficientMap m b (e.symm x) n = _
  linarith

end Model

theorem explicit_isometry : JamesBidualIsometrySpec.ExplicitIsometry := by
  intro m b he hc
  exact ⟨bidualIsometry m b he hc, bidualIsometry_forward m b he hc,
    bidualIsometry_inverse m b he hc⟩

theorem nonreflexive_isometric : JamesBidualIsometrySpec.NonreflexiveIsometric := by
  intro m
  let : NormedAddCommGroup JamesBanachBasisSpec.Sequence := m.group
  let : NormedSpace ℝ JamesBanachBasisSpec.Sequence := m.scalars
  obtain ⟨b, he, hc, _⟩ := JamesShrinking.shrinking.2 m
  refine ⟨⟨bidualIsometry m b he hc⟩, JamesBidual.codimension_one m, ?_⟩
  intro href
  obtain ⟨Φ, hΦ⟩ := JamesBidual.exists_bidual_of_bounded m b he hc (fun _ => 1)
    (JamesBidual.constant_sequence m).1
  obtain ⟨x, hx⟩ := href Φ
  have hnull := (JamesBidual.canonical_image_iff m b he hc Φ).mp
    (show Φ ∈ (canonical m).range from ⟨x, hx⟩)
  rw [hΦ] at hnull
  have h01 : (0:ℝ) = 1 := tendsto_nhds_unique hnull tendsto_const_nhds
  exact zero_ne_one h01

end ExpandedFA.P1.JamesBidualIsometry
