import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.BalancedBounded
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.MarkovKakutani
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open Set Filter Function
open scoped Topology BigOperators Pointwise

noncomputable section

namespace ExpandedFA.P1
namespace MarkovKakutani

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Affineness is required only on the indicated set. -/
def AffineOn (K : Set E) (T : E → E) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
    T (a • x + b • y) = a • T x + b • T y

private def average (x : ℕ → E) (n : ℕ) : E :=
  ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ j ∈ Finset.range (n + 1), x j

private theorem average_succ (x : ℕ → E) (n : ℕ) :
    average x (n + 1) =
      (((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) • average x n +
      (((n + 2 : ℕ) : ℝ)⁻¹) • x (n + 1) := by
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hcoef : (((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) *
      (((n + 1 : ℕ) : ℝ)⁻¹) = (((n + 2 : ℕ) : ℝ)⁻¹) := by
    field_simp
  unfold average
  rw [Finset.sum_range_succ, smul_add, smul_smul, hcoef]

private theorem average_mem_map {K : Set E} (hc : Convex ℝ K)
    {T : E → E} (haff : AffineOn K T) (x : ℕ → E) (hx : ∀ n, x n ∈ K) :
    ∀ n, average x n ∈ K ∧ T (average x n) = average (T ∘ x) n := by
  intro n
  induction n with
  | zero => simpa [average] using And.intro (hx 0) (Eq.refl (T (x 0)))
  | succ n ih =>
    have ha : 0 ≤ ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) := by positivity
    have hb : 0 ≤ (((n + 2 : ℕ) : ℝ)⁻¹) := by positivity
    have hab : ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) +
        (((n + 2 : ℕ) : ℝ)⁻¹) = 1 := by
      push_cast
      field_simp
      ring
    rw [average_succ, average_succ]
    exact ⟨hc ih.1 (hx _) ha hb hab,
      (haff _ ih.1 _ (hx _) _ _ ha hb hab).trans (by rw [ih.2]; rfl)⟩

/-- The Cesàro residual telescopes to the difference of the two orbit endpoints. -/
private theorem average_residual {K : Set E} (hc : Convex ℝ K)
    {T : E → E} (haff : AffineOn K T) (hm : MapsTo T K K)
    {x : E} (hx : x ∈ K) (n : ℕ) :
    T (average (fun j => T^[j] x) n) - average (fun j => T^[j] x) n =
      (((n + 1 : ℕ) : ℝ)⁻¹) • (T^[n + 1] x - x) := by
  have horb : ∀ j, T^[j] x ∈ K := fun j => hm.iterate j hx
  rw [(average_mem_map hc haff _ horb n).2]
  simp only [average, ← smul_sub, ← Finset.sum_sub_distrib, comp_apply,
    ← iterate_succ_apply']
  rw [Finset.sum_range_sub (fun j => T^[j] x)]
  rfl

section Topology

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [T2Space E]

/-- One continuous affine map of a nonempty compact convex set has a fixed point.
Local convexity is unnecessary for this intermediate result. -/
theorem exists_fixedPoint {K : Set E} (hne : K.Nonempty) (hk : IsCompact K)
    (hc : Convex ℝ K) {T : E → E} (hcont : ContinuousOn T K)
    (hm : MapsTo T K K) (haff : AffineOn K T) : ∃ x ∈ K, T x = x := by
  obtain ⟨x, hx⟩ := hne
  let z : ℕ → E := average (fun j => T^[j] x)
  have horb : ∀ j, T^[j] x ∈ K := fun j => hm.iterate j hx
  have hz : ∀ n, z n ∈ K := fun n => (average_mem_map hc haff _ horb n).1
  have hzK : Filter.map z atTop ≤ 𝓟 K := by
    apply Filter.le_principal_iff.mpr
    change ∀ᶠ n in atTop, z n ∈ K
    exact Filter.Eventually.of_forall hz
  have hε : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hsmall : Tendsto (fun n => T (z n) - z n) atTop (𝓝 0) := by
    have hbounded : Bornology.IsVonNBounded ℝ (K - K) :=
      (hk.isVonNBounded ℝ).sub (hk.isVonNBounded ℝ)
    have hh := hbounded.smul_tendsto_zero
      (Filter.Eventually.of_forall (fun n : ℕ =>
        show T^[n + 1] x - x ∈ K - K from sub_mem_sub (horb _) hx)) hε
    change Tendsto (fun n => (((n + 1 : ℕ) : ℝ)⁻¹) • (T^[n + 1] x - x))
      atTop (𝓝 0) at hh
    simpa only [z, average_residual hc haff hm hx] using hh
  obtain ⟨y, hy, hcluster⟩ := hk.exists_mapClusterPt hzK
  let l : Filter E := 𝓝 y ⊓ Filter.map z atTop
  have : l.NeBot := hcluster
  have hdiff : Tendsto (fun v => T v - v) l (𝓝 (T y - y)) :=
    ((hcont y hy).sub continuousWithinAt_id).mono_left (inf_le_inf_left _ hzK)
  have hzero : Tendsto (fun v => T v - v) (Filter.map z atTop) (𝓝 0) := by
    exact (Filter.tendsto_map'_iff).mpr hsmall
  exact ⟨y, hy, sub_eq_zero.mp (tendsto_nhds_unique hdiff (hzero.mono_left inf_le_right))⟩

/-- Fixed sets are closed and convex, and remain invariant under commuting maps. -/
theorem exists_common_fixedPoint {K : Set E} (hne : K.Nonempty) (hk : IsCompact K)
    (hc : Convex ℝ K) {ι : Type*} (T : ι → E → E)
    (hcont : ∀ i, ContinuousOn (T i) K) (hm : ∀ i, MapsTo (T i) K K)
    (haff : ∀ i, AffineOn K (T i))
    (hcomm : ∀ i j x, x ∈ K → T i (T j x) = T j (T i x)) :
    ∃ x ∈ K, ∀ i, T i x = x := by
  classical
  let C : ι → Set E := fun i => {x ∈ K | T i x = x}
  have hclosed : ∀ i, IsClosed (C i) :=
    fun i => hk.isClosed.isClosed_eq (hcont i) continuousOn_id
  have hfinite : ∀ s : Finset ι, ∃ x ∈ K, ∀ i ∈ s, T i x = x := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨x, hx⟩ := hne
      exact ⟨x, hx, by simp⟩
    | @insert i s hi ih =>
      let L : Set E := {x ∈ K | ∀ j ∈ s, T j x = x}
      have hLK : L ⊆ K := fun _ hx => hx.1
      have hLclosed : IsClosed L := by
        have heq : L = K ∩ ⋂ j ∈ s, C j := by
          ext x
          simp only [L, C, mem_ofPred, mem_inter_iff, mem_iInter]
          constructor
          · exact fun hx => ⟨hx.1, fun j hj => ⟨hx.1, hx.2 j hj⟩⟩
          · exact fun hx => ⟨hx.1, fun j hj => (hx.2 j hj).2⟩
        rw [heq]
        exact hk.isClosed.inter (isClosed_biInter fun j _ => hclosed j)
      have hLcompact : IsCompact L := hk.of_isClosed_subset hLclosed hLK
      have hLconvex : Convex ℝ L := by
        intro x hx y hy a b ha hb hab
        refine ⟨hc hx.1 hy.1 ha hb hab, fun j hj => ?_⟩
        rw [haff j x hx.1 y hy.1 a b ha hb hab, hx.2 j hj, hy.2 j hj]
      have hLmaps : MapsTo (T i) L L := by
        intro x hx
        refine ⟨hm i hx.1, fun j hj => ?_⟩
        rw [hcomm j i x hx.1, hx.2 j hj]
      obtain ⟨x, hx, hix⟩ := exists_fixedPoint ih hLcompact hLconvex
        ((hcont i).mono hLK) hLmaps
        (fun x hx y hy => haff i x hx.1 y hy.1)
      refine ⟨x, hx.1, fun j hj => ?_⟩
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hix
      · exact hx.2 j hj
  obtain ⟨x, hxK, hx⟩ := hk.inter_iInter_nonempty C hclosed (fun s => by
    obtain ⟨x, hxK, hx⟩ := hfinite s
    exact ⟨x, hxK, mem_iInter.mpr fun i => mem_iInter.mpr fun hi => ⟨hxK, hx i hi⟩⟩)
  exact ⟨x, hxK, fun i => (mem_iInter.mp hx i).2⟩

end Topology
end MarkovKakutani

/-- Markov--Kakutani for maps defined on the compact set itself. -/
theorem markov_kakutani : MarkovKakutaniSpec.CommonFixedPoint := by
  intro 𝕜 E _ _ _ _ _ _ _ _ _ _ K hne hk hc ι f hcont haff hcomm
  classical
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  -- Extend each set map arbitrarily outside K; all hypotheses and uses are on K.
  let T : ι → E → E := fun i x => if hx : x ∈ K then (f i ⟨x, hx⟩ : E) else x
  have hrestrict (i : ι) (x : K) : T i x = (f i x : E) := by
    simp only [T, dite_eq_left x.prop]
  have hTcont : ∀ i, ContinuousOn (T i) K := by
    intro i
    apply continuousOn_iff_continuous_domRestrict.mpr
    have heq : K.domRestrict (T i) = fun x : K => (f i x : E) := by
      funext x
      exact hrestrict i x
    rw [heq]
    exact continuous_subtype_val.comp (hcont i)
  have hTmaps : ∀ i, MapsTo (T i) K K := by
    intro i x hx
    rw [show T i x = (f i ⟨x, hx⟩ : E) from hrestrict i ⟨x, hx⟩]
    exact (f i ⟨x, hx⟩).prop
  have hTaff : ∀ i, MarkovKakutani.AffineOn K (T i) := by
    intro i x hx y hy a b ha hb hab
    have hm := hc hx hy ha hb hab
    rw [show T i (a • x + b • y) =
      (f i ⟨a • x + b • y, hm⟩ : E) from hrestrict i ⟨_, hm⟩,
      haff i ⟨x, hx⟩ ⟨y, hy⟩ a b ha hb hab,
      show T i x = (f i ⟨x, hx⟩ : E) from hrestrict i ⟨x, hx⟩,
      show T i y = (f i ⟨y, hy⟩ : E) from hrestrict i ⟨y, hy⟩]
  have hTcomm : ∀ i j x, x ∈ K → T i (T j x) = T j (T i x) := by
    intro i j x hx
    simpa only [T, dite_eq_left hx, dite_eq_left (f j ⟨x, hx⟩).prop,
      dite_eq_left (f i ⟨x, hx⟩).prop] using
      congrArg Subtype.val (hcomm i j ⟨x, hx⟩)
  obtain ⟨x, hx, hfixed⟩ := MarkovKakutani.exists_common_fixedPoint
    hne hk hc T hTcont hTmaps hTaff hTcomm
  refine ⟨⟨x, hx⟩, fun i => Subtype.ext ?_⟩
  exact (hrestrict i ⟨x, hx⟩).symm.trans (hfixed i)

end ExpandedFA.P1
