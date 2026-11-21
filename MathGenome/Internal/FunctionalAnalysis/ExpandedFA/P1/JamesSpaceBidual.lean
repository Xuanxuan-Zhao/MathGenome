import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.JamesSpaceBidual
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.JamesSpaceShrinking
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.DualBases
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05BidualIsometry
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.Isomorphisms

set_option maxHeartbeats 500000

noncomputable section
open Filter
open scoped BigOperators Topology ENNReal
namespace ExpandedFA.P1.JamesBidual
open JamesBidualSpec
open DualBasisBasicity.Spec (dualSpan dualVector)
open private chainEnergy_nonneg chainEnergy_append_le chainEnergy_ofFn
  chainEnergy_congr from MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.JamesSpaceBanachBasis

section Model
variable (m : JamesBanachBasisSpec.BanachBasisModel)
local instance : CompleteSpace (ModelSpace m) := m.complete
local instance : NormedAddCommGroup (Dual m) := inferInstance
local instance : NormedSpace ℝ (Dual m) := inferInstance
local instance : NormedAddCommGroup (Bidual m) := inferInstance
local instance : NormedSpace ℝ (Bidual m) := inferInstance

lemma initialSum_val (a : ℕ → ℝ) (N : ℕ) :
    (initialSum m a N).val = fun n => if n < N then a n else 0 := by
  classical
  letI : NormedAddCommGroup JamesBanachBasisSpec.Sequence := m.group
  letI : NormedSpace ℝ JamesBanachBasisSpec.Sequence := m.scalars
  change (C15Basis.Spec.orderedPartialSum m.e a N).val = _
  unfold C15Basis.Spec.orderedPartialSum
  rw [JamesShrinking.model_val_sum m]
  funext n
  simp [m.smul_eq, m.unit_eq, Pi.single_apply]


/-- A uniform bound on initial sums bounds every untruncated cyclic test. -/
lemma bounded_variation (a : ℕ → ℝ) (ha : Bounded m a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k p, StrictMono p → James.variation a k p ≤ C := by
  obtain ⟨C, hC⟩ := ha
  have hC0 : 0 ≤ C := (norm_nonneg (initialSum m a 0)).trans (hC (Set.mem_range_self 0))
  refine ⟨C, hC0, fun k p hp => ?_⟩
  let N := p (Fin.last (k+1)) + 1
  have hN (i : Fin (k+2)) : p i < N := Nat.lt_succ_of_le (hp.monotone (Fin.le_last i))
  have htest : James.variation a k p = James.variation (initialSum m a N).val k p := by
    simp only [James.variation, James.probe_norm, James.cyclicEnergy, initialSum_val,
      if_pos (hN _)]
  rw [htest]
  have hnorm := James.variation_le_norm (initialSum m a N) k p hp
  have hn : ‖initialSum m a N‖ ≤ C := hC (Set.mem_range_self N)
  have hmodel : ‖initialSum m a N‖ = JamesSpec.normValue (initialSum m a N) := m.norm_eq _
  rw [hmodel] at hn
  exact hnorm.trans hn

end Model

lemma energy_of_variation_bound (a : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ k p, StrictMono p → James.variation a k p ≤ C)
    (k : ℕ) (p : Fin (k+2) → ℕ) (hp : StrictMono p) :
    James.cyclicEnergy a k p ≤ 2 * C^2 := by
  have hs := hv k p hp
  rw [James.variation, James.probe_norm, one_div_mul_eq_div] at hs
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hh := mul_self_le_mul_self (Real.sqrt_nonneg _) ((div_le_iff₀ hpos).mp hs)
  have hn : 0 ≤ James.cyclicEnergy a k p := by unfold James.cyclicEnergy; positivity
  nlinarith [Real.sq_sqrt hn, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

lemma chain_of_variation_bound (a : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ k p, StrictMono p → James.variation a k p ≤ C)
    (l : List ℕ) (hl : l.Pairwise (· < ·)) : James.chainEnergy a l ≤ 2*C^2 := by
  cases l with
  | nil => simp [James.chainEnergy]; positivity
  | cons i l =>
    cases l with
    | nil => simp [James.chainEnergy]; positivity
    | cons j l =>
      have hget : StrictMono (List.get (i :: j :: l)) := List.pairwise_iff_get.mp hl
      rw [← List.ofFn_get (i :: j :: l), chainEnergy_ofFn]
      exact (le_add_of_nonneg_right (sq_nonneg _)).trans
        (energy_of_variation_bound a hC hv l.length _ hget)

/-- Supremal finite chain energy is exhausted by a finite prefix. This does
not require a null sequence, and so applies before convergence is known. -/
lemma late_energy_of_variation_bound (a : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ k p, StrictMono p → James.variation a k p ≤ C)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ l : List ℕ, l.Pairwise (· < ·) →
      (∀ n ∈ l, N ≤ n) → James.chainEnergy a l < δ := by
  let S : Set ℝ := {r | ∃ l : List ℕ, l.Pairwise (· < ·) ∧ James.chainEnergy a l = r}
  have hne : S.Nonempty := ⟨0, [], by simp, rfl⟩
  have hb : BddAbove S := ⟨2*C^2, by
    rintro r ⟨l, hl, rfl⟩
    exact chain_of_variation_bound a hC hv l hl⟩
  obtain ⟨r, ⟨l, hl, hr⟩, hnear⟩ :=
    exists_lt_of_lt_csSup hne (show sSup S - δ < sSup S by linarith)
  refine ⟨l.sum + 1, fun q hq hlate => ?_⟩
  have happ : (l ++ q).Pairwise (· < ·) := by
    rw [List.pairwise_append]
    refine ⟨hl, hq, fun i hi j hj => ?_⟩
    have hi' : i ≤ l.sum := List.le_sum_of_mem hi
    have hj' := hlate j hj
    omega
  have htotal : James.chainEnergy a (l ++ q) ≤ sSup S := le_csSup hb ⟨l ++ q, happ, rfl⟩
  have hsplit := chainEnergy_append_le a l q
  linarith

lemma cauchy_of_variation_bound (a : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ k p, StrictMono p → James.variation a k p ≤ C) : CauchySeq a := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := late_energy_of_variation_bound a hC hv (sq_pos_of_pos hε)
  refine ⟨N, fun i hi j hj => ?_⟩
  wlog hij : i ≤ j generalizing i j
  · simpa only [dist_comm] using this j hj i hi (le_of_not_ge hij)
  rcases hij.eq_or_lt with rfl | hij
  · simpa using hε
  have hh := hN [i,j] (by simpa using hij) (by simpa using And.intro hi hj)
  simp only [James.chainEnergy] at hh
  rw [Real.dist_eq]
  nlinarith [sq_abs (a i - a j), abs_nonneg (a i - a j)]

/-- Subtracting a constant preserves each cyclic difference exactly. -/
lemma variation_sub_const (a : ℕ → ℝ) (L : ℝ) (k : ℕ) (p : Fin (k+2) → ℕ) :
    James.variation (fun n => a n - L) k p = James.variation a k p := by
  simp only [James.variation, James.probe_norm, James.cyclicEnergy]
  congr 2
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    congr 1
    ring
  · congr 1
    ring

theorem bounded_decomposition : JamesBidualSpec.BoundedDecomposition := by
  intro m a ha
  obtain ⟨C, hC, hv⟩ := bounded_variation m a ha
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchy_of_variation_bound a hC hv)
  have hmem : JamesSpec.membershipValue (fun n => a n - L) := by
    refine ⟨?_, ?_⟩
    · simpa using hL.sub_const L
    · change James.enorm (fun n => a n - L) ≠ ⊤
      refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top : ENNReal.ofReal C ≠ ⊤) ?_
      apply James.enorm_le_of_variation_le
      intro k p hp
      rw [variation_sub_const]
      exact ENNReal.ofReal_le_ofReal (hv k p hp)
  exact ⟨L, ⟨hL, hmem⟩, fun M hM => tendsto_nhds_unique hM.1 hL⟩

section Model
variable (m : JamesBanachBasisSpec.BanachBasisModel)
local instance : CompleteSpace (ModelSpace m) := m.complete
local instance : NormedAddCommGroup (Dual m) := inferInstance
local instance : NormedSpace ℝ (Dual m) := inferInstance
local instance : NormedAddCommGroup (Bidual m) := inferInstance
local instance : NormedSpace ℝ (Bidual m) := inferInstance

variable (b : SchauderBasis ℝ (ModelSpace m))
  (he : b.basis = m.e) (hc : ∀ i x, b.coord i x = x.val i)
include he hc

lemma synthesis_eq (a : ℕ → ℝ) (N : ℕ) :
    C15Basis.Spec.orderedPartialSum b.basis a N = initialSum m a N := by
  unfold C15Basis.Spec.orderedPartialSum initialSum
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun v : ModelSpace m => a i • v) (congrFun he i)

lemma projection_bound (N : ℕ) : ‖b.proj N‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have hp : b.proj N x = initialSum m x.val N := by
    rw [SchauderBasis.proj_apply]
    change C15Basis.Spec.orderedPartialSum b.basis (fun i => b.coord i x) N = _
    have hh : (fun i => b.coord i x) = x.val := funext fun i => hc i x
    rw [hh]
    exact synthesis_eq m b he hc _ _
  rw [hp, one_mul]
  exact m.monotone N x

lemma coefficients_injective : Function.Injective (coefficientMap m b) := by
  intro Φ Ψ h
  ext f
  have hs := JamesShrinking.shrinking_of_coordinates m b he hc f
  have hΦ := Φ.continuous.tendsto f |>.comp hs
  have hΨ := Ψ.continuous.tendsto f |>.comp hs
  have heq (N : ℕ) : Φ (f.comp (b.proj N)) = Ψ (f.comp (b.proj N)) := by
    have hd := DualBasisBasicity.dualProjection_eq_sum b N f
    change f.comp (b.proj N) = _ at hd
    rw [hd]
    simp only [map_sum, map_smul]
    exact Finset.sum_congr rfl (fun i _ => congrArg (fun r : ℝ => f (b i) • r) (congrFun h i))
  exact tendsto_nhds_unique (hΦ.congr (fun N => heq N)) hΨ

lemma coefficient_initialSum_bound (Φ : Bidual m) (N : ℕ) :
    ‖initialSum m (coefficientMap m b Φ) N‖ ≤ ‖Φ‖ := by
  let Ψ := Φ.comp (dualSpan b).subtypeL
  have hh := DualBasisCoefficients.coefficient_sum_bound b (projection_bound m b he hc) Ψ N
  have hn : ‖Ψ‖ ≤ ‖Φ‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Φ)
    intro f
    exact Φ.le_opNorm f.val
  rw [synthesis_eq m b he hc] at hh
  change ‖initialSum m (coefficientMap m b Φ) N‖ ≤ 1 * ‖Ψ‖ at hh
  exact hh.trans (by simpa only [one_mul] using hn)

lemma bounded_coefficients (Φ : Bidual m) : Bounded m (coefficientMap m b Φ) :=
  ⟨‖Φ‖, by rintro _ ⟨N, rfl⟩; exact coefficient_initialSum_bound m b he hc Φ N⟩

lemma exists_bidual_of_bounded (a : ℕ → ℝ) (ha : Bounded m a) :
    ∃ Φ : Bidual m, coefficientMap m b Φ = a := by
  have ha' : BddAbove (Set.range fun N =>
      ‖C15Basis.Spec.orderedPartialSum b.basis a N‖) := by
    simp_rw [synthesis_eq m b he hc]
    exact ha
  obtain ⟨Ψ, hΨ⟩ := DualBasisCoefficients.exists_of_bounded b a ha'
  obtain ⟨Φ, hΦ, _⟩ := C05NormExtension.norm_preserving_extension
    ℝ (Dual m) (dualSpan b) Ψ
  refine ⟨Φ, funext fun i => ?_⟩
  exact (hΦ (dualVector b i)).trans (congrFun hΨ i)

lemma coefficient_norm (Φ : Bidual m) :
    ‖Φ‖ = sSup (Set.range fun N => ‖initialSum m (coefficientMap m b Φ) N‖) := by
  let S := Set.range fun N => ‖initialSum m (coefficientMap m b Φ) N‖
  have hne : S.Nonempty := Set.range_nonempty _
  have hb : BddAbove S := bounded_coefficients m b he hc Φ
  have h0 : 0 ≤ sSup S := (norm_nonneg (initialSum m (coefficientMap m b Φ) 0)).trans
    (le_csSup hb (Set.mem_range_self 0))
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ h0
    intro f
    have hs := JamesShrinking.shrinking_of_coordinates m b he hc f
    have ht := (Φ.continuous.tendsto f |>.comp hs).norm
    apply le_of_tendsto ht
    apply Eventually.of_forall
    intro N
    have hval : Φ (f.comp (b.proj N)) = f (initialSum m (coefficientMap m b Φ) N) := by
      have hd := DualBasisBasicity.dualProjection_eq_sum b N f
      change f.comp (b.proj N) = _ at hd
      rw [hd, ← synthesis_eq m b he hc]
      simp only [C15Basis.Spec.orderedPartialSum, map_sum, map_smul]
      apply Finset.sum_congr rfl
      intro i _
      change f (b i) * Φ (b.coord i) = Φ (b.coord i) * f (b i)
      exact mul_comm _ _
    change ‖Φ (f.comp (b.proj N))‖ ≤ sSup S * ‖f‖
    rw [hval]
    exact (f.le_opNorm _).trans (by
      rw [mul_comm (sSup S)]
      exact mul_le_mul_of_nonneg_left (le_csSup hb (Set.mem_range_self N)) (norm_nonneg f))
  · apply csSup_le hne
    rintro _ ⟨N, rfl⟩
    exact coefficient_initialSum_bound m b he hc Φ N

end Model

theorem coefficient_model : JamesBidualSpec.CoefficientModel := by
  intro m b he hc
  refine ⟨coefficients_injective m b he hc, ?_, coefficient_norm m b he hc⟩
  intro a
  constructor
  · rintro ⟨Φ, rfl⟩
    exact bounded_coefficients m b he hc Φ
  · exact exists_bidual_of_bounded m b he hc a

/-- Telescoping on a nonempty finite chain. -/
lemma sum_fin_differences {n : ℕ} (v : Fin (n+1) → ℝ) :
    (∑ j : Fin n, (v j.castSucc - v j.succ)) = v 0 - v (Fin.last n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have hh := ih (fun i => v i.succ)
    simp only [Fin.castSucc_zero, Fin.succ_castSucc] at *
    rw [hh]
    simp only [Fin.succ_last]
    ring

/-- An initial segment of ones has two jumps around any cyclic test. -/
lemma initial_ones_energy (N k : ℕ) (p : Fin (k+2) → ℕ) (hp : StrictMono p) :
    James.cyclicEnergy (fun n => if n < N then 1 else 0) k p ≤ 2 := by
  let v : Fin (k+2) → ℝ := fun i => if p i < N then 1 else 0
  have hedge (i j : Fin (k+2)) (hij : i ≤ j) : (v i - v j)^2 = v i - v j := by
    have hh := hp.monotone hij
    dsimp [v]
    split_ifs <;> norm_num <;> omega
  have hsum : (∑ j : Fin (k+1), (v j.castSucc - v j.succ)^2) =
      v 0 - v (Fin.last (k+1)) := by
    simp_rw [hedge _ _ (Fin.castSucc_le_succ _)]
    exact sum_fin_differences v
  have hclose : (v (Fin.last (k+1)) - v 0)^2 = v 0 - v (Fin.last (k+1)) := by
    rw [sub_sq_comm]
    exact hedge _ _ (Fin.zero_le _)
  change (∑ j : Fin (k+1), (v j.castSucc - v j.succ)^2) +
    (v (Fin.last (k+1)) - v 0)^2 ≤ 2
  rw [hsum, hclose]
  dsimp [v]
  split_ifs <;> norm_num

section Model
variable (m : JamesBanachBasisSpec.BanachBasisModel)

lemma initial_ones_norm (N : ℕ) : ‖initialSum m (fun _ => 1) N‖ ≤ 1 := by
  have hmodel : ‖initialSum m (fun _ => 1) N‖ = JamesSpec.normValue (initialSum m (fun _ => 1) N) := m.norm_eq _
  rw [hmodel]
  apply James.norm_le_of_variation_le _ (by norm_num)
  intro k p hp
  rw [James.variation, James.probe_norm, initialSum_val]
  have hh := Real.sqrt_le_sqrt (initial_ones_energy N k p hp)
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  calc
    _ ≤ (1 / Real.sqrt 2) * Real.sqrt 2 := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = 1 := one_div_mul_cancel hs

lemma initial_one_norm : ‖initialSum m (fun _ => 1) 1‖ = 1 := by
  have heq : initialSum m (fun _ => 1) 1 = (m.e 0 : ModelSpace m) := by
    apply Subtype.ext
    rw [initialSum_val, m.unit_eq]
    ext n
    simp [Pi.single_apply, Nat.lt_one_iff, eq_comm]
  exact (congrArg (fun x : ModelSpace m => ‖x‖) heq).trans (m.normalized 0)

end Model

theorem constant_sequence : JamesBidualSpec.ConstantSequence := by
  intro m
  have hb : Bounded m (fun _ => 1) :=
    ⟨1, by rintro _ ⟨N, rfl⟩; exact initial_ones_norm m N⟩
  refine ⟨hb, le_antisymm ?_ ?_⟩
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨N, rfl⟩
    exact initial_ones_norm m N
  · have hh := le_csSup hb (Set.mem_range_self 1)
    rwa [initial_one_norm] at hh

section Model
variable (m : JamesBanachBasisSpec.BanachBasisModel)
local instance : CompleteSpace (ModelSpace m) := m.complete
local instance : NormedAddCommGroup (Dual m) := inferInstance
local instance : NormedSpace ℝ (Dual m) := inferInstance
local instance : NormedAddCommGroup (Bidual m) := inferInstance
local instance : NormedSpace ℝ (Bidual m) := inferInstance
variable (b : SchauderBasis ℝ (ModelSpace m))
  (he : b.basis = m.e) (hc : ∀ i x, b.coord i x = x.val i)
include he hc

lemma canonical_coefficients (x : ModelSpace m) :
    coefficientMap m b (canonical m x) = x.val := by
  funext i
  change b.coord i x = x.val i
  exact hc i x

lemma canonical_image_iff (Φ : Bidual m) :
    Φ ∈ (canonical m).range ↔ Tendsto (coefficientMap m b Φ) atTop (𝓝 0) := by
  constructor
  · rintro ⟨x, rfl⟩
    change Tendsto (coefficientMap m b (canonical m x)) atTop (𝓝 0)
    rw [canonical_coefficients m b he hc]
    exact x.property.1
  · intro hnull
    obtain ⟨C, hC, hv⟩ := bounded_variation m (coefficientMap m b Φ)
      (bounded_coefficients m b he hc Φ)
    have hmem : JamesSpec.membershipValue (coefficientMap m b Φ) := by
      refine ⟨hnull, ne_top_of_le_ne_top (ENNReal.ofReal_ne_top : ENNReal.ofReal C ≠ ⊤) ?_⟩
      exact James.enorm_le_of_variation_le (fun k p hp => ENNReal.ofReal_le_ofReal (hv k p hp))
    let x : ModelSpace m := ⟨coefficientMap m b Φ, hmem⟩
    refine ⟨x, coefficients_injective m b he hc ?_⟩
    exact canonical_coefficients m b he hc x

lemma quotient_equiv_real : Nonempty ((Bidual m ⧸ (canonical m).range) ≃ₗ[ℝ] ℝ) := by
  let L (Φ : Bidual m) : ℝ :=
    (bounded_decomposition m (coefficientMap m b Φ)
      (bounded_coefficients m b he hc Φ)).exists.choose
  have hL (Φ : Bidual m) : Tendsto (coefficientMap m b Φ) atTop (𝓝 (L Φ)) :=
    (bounded_decomposition m (coefficientMap m b Φ)
      (bounded_coefficients m b he hc Φ)).exists.choose_spec.1
  let l : Bidual m →ₗ[ℝ] ℝ :=
    { toFun := L
      map_add' := by
        intro Φ Ψ
        exact tendsto_nhds_unique (hL (Φ + Ψ)) ((hL Φ).add (hL Ψ))
      map_smul' := by
        intro c Φ
        exact tendsto_nhds_unique (hL (c • Φ)) ((hL Φ).const_smul c) }
  have hk : l.ker = (canonical m).range := by
    ext Φ
    change L Φ = 0 ↔ Φ ∈ (canonical m).range
    rw [canonical_image_iff m b he hc]
    constructor
    · intro hz
      simpa only [hz] using hL Φ
    · intro hn
      exact tendsto_nhds_unique (hL Φ) hn
  obtain ⟨Ω, hΩ⟩ := exists_bidual_of_bounded m b he hc (fun _ => 1)
    (constant_sequence m).1
  have hΩL : l Ω = 1 := by
    change L Ω = 1
    have hh := hL Ω
    rw [hΩ] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  have hsurj : Function.Surjective l := by
    intro c
    refine ⟨c • Ω, ?_⟩
    rw [map_smul, hΩL, smul_eq_mul, mul_one]
  have e := l.quotKerEquivOfSurjective hsurj
  rw [hk] at e
  exact ⟨e⟩

end Model

theorem canonical_image : JamesBidualSpec.CanonicalImage := by
  intro m b he hc
  exact canonical_image_iff m b he hc

theorem codimension_one : JamesBidualSpec.CodimensionOne := by
  intro m
  letI : NormedAddCommGroup JamesBanachBasisSpec.Sequence := m.group
  letI : NormedSpace ℝ JamesBanachBasisSpec.Sequence := m.scalars
  obtain ⟨b, he, hc, _⟩ := JamesShrinking.shrinking.2 m
  exact quotient_equiv_real m b he hc

end ExpandedFA.P1.JamesBidual
