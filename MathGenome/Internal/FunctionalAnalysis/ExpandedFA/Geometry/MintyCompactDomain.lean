import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Geometry.MintyCompactDomain
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Geometry.CompactConvexMinimax
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14BallCharacterization
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12ConvexClosure
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ExpandedFA.Geometry.MintyCompactDomain
open Set
open scoped BigOperators Topology
open Specs.ExpandedFA.Geometry.MintyCompactDomain
universe u
noncomputable section

/-- Bilinear payoff for a finite family of Minty tests. -/
def matrixPayoff {ι : Type*} [Fintype ι] (M : ι → ι → ℝ)
    (s t : ι → ℝ) : ℝ := ∑ i, ∑ j, s i * t j * M i j

lemma matrixPayoff_add_left {ι : Type*} [Fintype ι] (M : ι → ι → ℝ)
    (s s' t : ι → ℝ) : matrixPayoff M (s+s') t = matrixPayoff M s t + matrixPayoff M s' t := by
  simp [matrixPayoff, add_mul, Finset.sum_add_distrib]

lemma matrixPayoff_smul_left {ι : Type*} [Fintype ι] (M : ι → ι → ℝ)
    (a : ℝ) (s t : ι → ℝ) : matrixPayoff M (a • s) t = a * matrixPayoff M s t := by
  simp [matrixPayoff, mul_assoc, Finset.mul_sum]

lemma matrixPayoff_add_right {ι : Type*} [Fintype ι] (M : ι → ι → ℝ)
    (s t t' : ι → ℝ) : matrixPayoff M s (t+t') = matrixPayoff M s t + matrixPayoff M s t' := by
  simp [matrixPayoff, mul_add, add_mul, Finset.sum_add_distrib]

lemma matrixPayoff_smul_right {ι : Type*} [Fintype ι] (M : ι → ι → ℝ)
    (a : ℝ) (s t : ι → ℝ) : matrixPayoff M s (a • t) = a * matrixPayoff M s t := by
  simp only [matrixPayoff, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1; ext i
  congr 1; ext j
  ring

/-- Only nonnegative probability weights enter the diagonal sign argument. -/
lemma matrixPayoff_diagonal_nonpos {ι : Type*} [Fintype ι]
    (M : ι → ι → ℝ) (hM : ∀ i j, M i j + M j i ≤ 0)
    (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i) : matrixPayoff M s s ≤ 0 := by
  have h : (∑ i, ∑ j, s i * s j * (M i j + M j i)) ≤ 0 := by
    apply Finset.sum_nonpos; intro i _
    apply Finset.sum_nonpos; intro j _
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hs i) (hs j)) (hM i j)
  have heq : (∑ i, ∑ j, s i * s j * (M i j + M j i)) =
      matrixPayoff M s s + matrixPayoff M s s := by
    simp only [mul_add, Finset.sum_add_distrib, matrixPayoff]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [heq] at h
  linarith

/-- Finite minimax produces simultaneous feasibility of all matrix columns. -/
lemma matrix_minty {ι : Type*} [Fintype ι] [Nonempty ι]
    (M : ι → ι → ℝ) (hM : ∀ i j, M i j + M j i ≤ 0) :
    ∃ s ∈ stdSimplex ℝ ι, ∀ j, (∑ i, s i * M i j) ≤ 0 := by
  classical
  let B := matrixPayoff M
  let S := stdSimplex ℝ ι
  have ne : S.Nonempty := ⟨Pi.single (Classical.arbitrary ι) 1, single_mem_stdSimplex _ _⟩
  have cv := convex_stdSimplex ℝ ι
  have kc := isCompact_stdSimplex ℝ ι
  have left (t : ι → ℝ) : ConvexOn ℝ S (fun s => B s t) := by
    refine ⟨cv, ?_⟩
    intro s hs s' hs' a b ha hb hab
    exact le_of_eq (by simp [B, matrixPayoff_add_left, matrixPayoff_smul_left])
  have right (s : ι → ℝ) : ConcaveOn ℝ S (B s) := by
    refine ⟨cv, ?_⟩
    intro t ht t' ht' a b ha hb hab
    exact le_of_eq (by simp [B, matrixPayoff_add_right, matrixPayoff_smul_right])
  have lc (t : ι → ℝ) : Continuous (fun s => B s t) := by
    dsimp [B, matrixPayoff]; fun_prop
  have rc (s : ι → ℝ) : Continuous (B s) := by
    change Continuous (fun t : ι → ℝ => ∑ i, ∑ j, s i * t j * M i j)
    fun_prop
  obtain ⟨_, _, _, _, _, ⟨s, hs, hsm, _⟩, ⟨t, ht, htm, _⟩, saddle⟩ :=
    ExpandedFA.Geometry.compact_convex_minimax S S B ne kc cv ne kc cv
      (fun t _ => left t) (fun t _ => (lc t).lowerSemicontinuous.lowerSemicontinuousOn S)
      (fun s _ => right s) (fun s _ => (rc s).upperSemicontinuous.upperSemicontinuousOn S)
  refine ⟨s, hs, fun j => ?_⟩
  have h := saddle s hs t ht hsm htm t ht (Pi.single j 1) (single_mem_stdSimplex _ _)
  have hd : B t t ≤ 0 := matrixPayoff_diagonal_nonpos M hM t ht.1
  have hj : B s (Pi.single j 1) = ∑ i, s i * M i j := by
    simp [B, matrixPayoff, Pi.single_apply]
  rw [hj] at h
  exact h.1.trans (h.2.trans hd)

/-- A finite family of domain tests admits a convex combination satisfying
all its Minty inequalities. No value of A at that combination is required. -/
lemma finite_minty {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {D K : Set X} (A : D → (X →L[ℝ] ℝ)) (hK : Convex ℝ K)
    (hA : DomainMonotone A) {ι : Type*} [Fintype ι] [Nonempty ι]
    (v : ι → D) (hv : ∀ i, (v i : X) ∈ K) :
    ∃ u ∈ K, ∀ j, A (v j) (u-v j) ≤ 0 := by
  let M := fun i j => A (v j) ((v i : X) - v j)
  have hm (i j) : M i j + M j i ≤ 0 := by
    have h := hA (v i) (v j)
    dsimp [M]
    simp only [sub_apply, map_sub] at *
    linarith
  obtain ⟨s, hs, hsm⟩ := matrix_minty M hm
  refine ⟨∑ i, s i • (v i : X), hK.sum_mem (fun i _ => hs.1 i) hs.2
    (fun i _ => hv i), fun j => ?_⟩
  have heq : A (v j) ((∑ i, s i • (v i : X)) - v j) = ∑ i, s i * M i j := by
    simp only [M, map_sub, map_sum, map_smul, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib, ← Finset.sum_mul, hs.2, one_mul]
  rw [heq]
  exact hsm j

/-- The weakly compact finite-intersection argument includes the empty
family of domain tests. -/
theorem weak_minty_exists : WeakMintyExistence.{u} := by
  intro X _ _ _ hX D K A neK clK bdK cvK hA
  classical
  let T := {v : D // (v : X) ∈ K}
  have wkcl := ExpandedFA.P1.C12ConvexClosure.isWeaklyClosed_of_isClosed_convex
    ℝ X K cvK clK
  have wkc := (ExpandedFA.P1.C14BallCharacterization.weakCompact_unitBall_iff_closed_bounded
    ℝ X).mp
    ((ExpandedFA.P1.C14BallCharacterization.reflexive_iff_weakCompact_unitBall ℝ X).mp hX)
    K bdK wkcl
  let V := X →L[ℝ] ℝ
  let tw := ExpandedFA.P1.C12DualPairSpec.DualPairTopologyValue
    ℝ X (X →L[ℝ] ℝ) (topDualPairing ℝ X)
  have ev (f : V) : @Continuous X ℝ tw inferInstance f := by
    rw [continuous_iff_le_induced]
    dsimp [tw]
    rw [ExpandedFA.P1.dualPairTopology_evaluation ℝ X]
    exact iInf_le (fun g : V => TopologicalSpace.induced (fun x : X => g x) inferInstance) f
  let : TopologicalSpace X := tw
  let C : T → Set X := fun v => {x | A v.1 (x - (v.1 : X)) ≤ 0}
  have closedC (v : T) : IsClosed (C v) := by
    change IsClosed {x | A v.1 (x-(v.1 : X)) ≤ 0}
    simp only [map_sub]
    exact isClosed_le ((ev (A v.1)).sub continuous_const) continuous_const
  have fip (s : Finset T) : (K ∩ ⋂ v ∈ s, C v).Nonempty := by
    by_cases hs : s.Nonempty
    · let : Nonempty s := hs.to_subtype
      obtain ⟨u, hu, htests⟩ := finite_minty A cvK hA
        (fun v : s => v.1.1) (fun v => v.1.2)
      refine ⟨u, hu, ?_⟩
      simp only [mem_iInter]
      intro v hv
      exact htests ⟨v, hv⟩
    · have : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      simpa [this] using neK
  obtain ⟨u, huK, hu⟩ := wkc.inter_iInter_nonempty C closedC fip
  refine ⟨u, huK, fun v hv => ?_⟩
  exact (mem_iInter.mp hu) ⟨v, hv⟩

@[simp] lemma operatorValue_subtype {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {D : Set X} (A : D → (X →L[ℝ] ℝ)) (v : D) : operatorValue A (v : X) = A v := by
  simp [operatorValue, v.property]

lemma operatorValue_of_mem {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {D : Set X} (A : D → (X →L[ℝ] ℝ)) {v : X} (hv : v ∈ D) :
    operatorValue A v = A ⟨v, hv⟩ := by
  simp [operatorValue, hv]

/-- Minty's segment argument needs only convexity, domain inclusion and
hemicontinuity, independently of the compactness hypotheses for existence. -/
lemma minty_iff_variational {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {D K : Set X} (A : D → (X →L[ℝ] ℝ)) (cvK : Convex ℝ K)
    (hA : DomainMonotone A) (hKD : K ⊆ D) (hH : SegmentHemicontinuous A K)
    (u : X) (hu : u ∈ K) : WeakMinty A K u ↔ VariationalInequality A K u := by
  constructor
  · intro hm w hw
    let φ : ℝ → ℝ := fun t => operatorValue A ((1-t) • u + t • w) (w-u)
    have hc : ContinuousWithinAt φ (Ioc 0 1) 0 :=
      (hH u hu w hw (w-u) 0 (by constructor <;> norm_num)).mono Ioc_subset_Icc_self
    have hn (t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) : 0 ≤ φ t := by
      let x : X := (1-t) • u + t • w
      have hx : x ∈ K := cvK hu hw (sub_nonneg.mpr ht.2) ht.1.le (by ring)
      have test := hm ⟨x, hKD hx⟩ hx
      have heq : u-x = (-t) • (w-u) := by dsimp [x]; module
      change A ⟨x, hKD hx⟩ (u-x) ≤ 0 at test
      rw [heq, map_smul, smul_eq_mul] at test
      have hv : φ t = A ⟨x, hKD hx⟩ (w-u) := by
        dsimp [φ]; rw [operatorValue_of_mem A (hKD hx)]
      rw [← hv] at test
      nlinarith [ht.1]
    have : Filter.NeBot (𝓝[Ioc (0:ℝ) 1] 0) := left_nhdsWithin_Ioc_neBot zero_lt_one
    have hlim : 0 ≤ φ 0 := ge_of_tendsto hc
      (eventually_nhdsWithin_of_forall hn)
    simpa [φ] using hlim
  · intro hv v hvK
    have hvi := hv v hvK
    rw [operatorValue_of_mem A (hKD hu)] at hvi
    have hmono := hA v ⟨u, hKD hu⟩
    simp only [sub_apply, map_sub] at hmono ⊢
    simp only [map_sub] at hvi
    linarith

/-- The final equivalence in the source, at every candidate point of K. -/
theorem minty_equivalence : MintyEquivalence.{u} := by
  intro X _ _ _ _ D K A _ _ _ cvK hA hKD hH u hu
  exact minty_iff_variational A cvK hA hKD hH u hu

end
end ExpandedFA.Geometry.MintyCompactDomain
