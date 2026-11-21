import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.RyllNardzewski
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.SmallCap
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.MarkovKakutani
import Mathlib.Data.Set.Countable
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.RCLike.Extend

noncomputable section

open Set TopologicalSpace
open scoped Topology BigOperators

universe u v w

namespace ExpandedFA.P1.RyllNardzewski

section Algebra

variable {E : Type v} [AddCommGroup E] [Module ℝ E] {ι : Type w}

/-- Stationarity survives deleting all terms already equal to the barycenter.
This is the deletion step in the manuscript's finite-family argument. -/
theorem sum_sub_filter_ne (s : Finset ι) (y : ι → E) (x : E) [DecidableEq E]
    (h : ∑ i ∈ s, (y i - x) = 0) :
    ∑ i ∈ s.filter (fun i => y i ≠ x), (y i - x) = 0 := by
  classical
  rw [Finset.sum_filter]
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs with hix
  · rfl
  · simp only [not_not] at hix
    simp [hix]

/-- A nonempty stationary finite family has its barycenter in every convex
set containing all its terms. No topological assumption is used. -/
theorem mem_convex_of_sum_sub_eq_zero {s : Finset ι} (hs : s.Nonempty)
    (y : ι → E) (x : E) (h : ∑ i ∈ s, (y i - x) = 0)
    {C : Set E} (hC : Convex ℝ C) (hy : ∀ i ∈ s, y i ∈ C) : x ∈ C := by
  have hn : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  have heq : ∑ i ∈ s, y i = (s.card : ℝ) • x := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, sub_eq_zero] at h
    simpa only [nsmul_eq_mul, Nat.cast_smul_eq_nsmul ℝ] using h
  have hw : ∑ _i ∈ s, (s.card : ℝ)⁻¹ = 1 := by
    simp [hn]
  have hm := hC.sum_mem (t := s) (w := fun _ => (s.card : ℝ)⁻¹)
    (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)) hw hy
  rw [← Finset.smul_sum, heq, smul_smul, inv_mul_cancel₀ hn, one_smul] at hm
  exact hm

/-- If the barycenter lies outside a convex set, one of its stationary terms
also lies outside. This avoids any strict-convexity assumption. -/
theorem exists_not_mem_of_sum_sub_eq_zero {s : Finset ι} (hs : s.Nonempty)
    (y : ι → E) (x : E) (h : ∑ i ∈ s, (y i - x) = 0)
    {C : Set E} (hC : Convex ℝ C) (hx : x ∉ C) :
    ∃ i ∈ s, y i ∉ C := by
  by_contra! hall
  exact hx (mem_convex_of_sum_sub_eq_zero hs y x h hC hall)

/-- The small-cap contradiction at one orbit point. A uniform separation
larger than the cap diameter rules out stationarity of the moving terms. -/
theorem cap_contradiction {s : Finset ι} (hs : s.Nonempty)
    (y : ι → E) (x : E) (h : ∑ i ∈ s, (y i - x) = 0)
    {Q C : Set E} (hC : Convex ℝ C) (hx : x ∈ Q \ C)
    (hy : ∀ i ∈ s, y i ∈ Q) (p : E → ℝ) (d η : ℝ) (hdη : d < η)
    (hdiam : ∀ a ∈ Q \ C, ∀ b ∈ Q \ C, p (a - b) ≤ d)
    (hsep : ∀ i ∈ s, η ≤ p (y i - x)) : False := by
  obtain ⟨i, hi, hiy⟩ := exists_not_mem_of_sum_sub_eq_zero hs y x h hC hx.2
  exact (hdη.trans_le (hsep i hi)).not_ge (hdiam (y i) ⟨hy i hi, hiy⟩ x hx)

end Algebra

section Separation

variable {E : Type v} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E]

/-- Original-topology noncontraction gives a continuous real seminorm
uniformly bounded below on the entire difference orbit. -/
theorem exists_seminorm_separating_zero {A : Set E}
    (hA : (0 : E) ∉ closure A) :
    ∃ p : Seminorm ℝ E, Continuous p ∧ ∀ x ∈ A, 1 ≤ p x := by
  have hU : (closure A)ᶜ ∈ 𝓝 (0 : E) :=
    isClosed_closure.isOpen_compl.mem_nhds hA
  obtain ⟨p, hp, hball⟩ := (PolynormableSpace.hasBasis_zero_ball ℝ E).mem_iff.mp hU
  refine ⟨p, hp, fun x hx => le_of_not_gt fun hpx => ?_⟩
  exact hball (by simpa only [Seminorm.mem_ball_zero] using hpx) (subset_closure hx)

/-- A finite family of noncontracting difference sets can be separated
simultaneously by one continuous seminorm. Empty index types are included. -/
theorem exists_seminorm_separating_finite {ι : Type w} [Fintype ι]
    (A : ι → Set E) (hA : ∀ i, (0 : E) ∉ closure (A i)) :
    ∃ p : Seminorm ℝ E, Continuous p ∧ ∀ i x, x ∈ A i → 1 ≤ p x := by
  classical
  choose p hp hsep using fun i => exists_seminorm_separating_zero (hA i)
  refine ⟨Finset.univ.sup p, Seminorm.continuous_finsetSup (fun i _ => hp i), ?_⟩
  intro i x hx
  exact (hsep i x hx).trans (show p i x ≤ (Finset.univ.sup p) x from
    Finset.le_sup (f := p) (Finset.mem_univ i) x)

end Separation

section OrbitCaps

variable {E : Type v} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- A proper closed convex subset of a closed convex orbit hull misses an
actual orbit point, not merely a limit or a convex combination. -/
theorem exists_outside_of_closure_convexHull {A Q C : Set E}
    (hQ : Q = closure (convexHull ℝ A)) (hCQ : C ⊂ Q)
    (hclosed : IsClosed C) (hconv : Convex ℝ C) : ∃ x ∈ A, x ∉ C := by
  by_contra! hall
  have hsub : Q ⊆ C := by
    rw [hQ]
    exact closure_minimal (convexHull_min hall hconv) hclosed
  exact hCQ.ne (Subset.antisymm hCQ.subset hsub)

/-- The finite stationary-orbit argument once its closed convex hull and a
small cap are available. It includes the possibility that the cap is empty. -/
theorem stationary_orbit_cap_contradiction
    {ι : Type w} {κ : Type*} (s : Finset ι) (hs : s.Nonempty)
    (x : κ → E) (y : κ → ι → E) (Q C : Set E)
    (hQ : Q = closure (convexHull ℝ (range x)))
    (hCQ : C ⊂ Q) (hclosed : IsClosed C) (hconv : Convex ℝ C)
    (hy : ∀ k i, i ∈ s → y k i ∈ Q)
    (hstat : ∀ k, ∑ i ∈ s, (y k i - x k) = 0)
    (p : E → ℝ) (d η : ℝ) (hdη : d < η)
    (hdiam : ∀ a ∈ Q \ C, ∀ b ∈ Q \ C, p (a - b) ≤ d)
    (hsep : ∀ k i, i ∈ s → η ≤ p (y k i - x k)) : False := by
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ :=
    exists_outside_of_closure_convexHull hQ hCQ hclosed hconv
  have hxQ : x k ∈ Q := by
    rw [hQ]
    exact subset_closure (subset_convexHull ℝ _ (mem_range_self k))
  exact cap_contradiction hs (y k) (x k) (hstat k) hconv ⟨hxQ, hk⟩
    (hy k) p d η hdη hdiam (hsep k)

end OrbitCaps

section ScalarRestriction

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [ContinuousSMul 𝕜 E]

/-- Restricting the original scalar field to ℝ preserves the weak topology:
each continuous real functional is the real part of a scalar-linear one. -/
theorem continuous_to_real_weak :
    Continuous (fun x : WeakSpace 𝕜 E =>
      toWeakSpace ℝ E ((toWeakSpace 𝕜 E).symm x)) := by
  apply WeakBilin.continuous_of_continuous_eval
  intro f
  change Continuous (fun x : WeakSpace 𝕜 E => f ((toWeakSpace 𝕜 E).symm x))
  have h := RCLike.continuous_re.comp
    (WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip (StrongDual.extendRCLike (𝕜 := 𝕜) f))
  change Continuous (fun x : WeakSpace 𝕜 E =>
    RCLike.re (StrongDual.extendRCLike (𝕜 := 𝕜) f ((toWeakSpace 𝕜 E).symm x))) at h
  simpa only [StrongDual.re_extendRCLike_apply] using h

/-- Conversely, real and imaginary parts of a scalar-linear functional are
continuous real functionals, so the inverse identity is weakly continuous. -/
theorem continuous_from_real_weak :
    Continuous (fun x : WeakSpace ℝ E =>
      toWeakSpace 𝕜 E ((toWeakSpace ℝ E).symm x)) := by
  apply WeakBilin.continuous_of_continuous_eval
  intro f
  change Continuous (fun x : WeakSpace ℝ E => f ((toWeakSpace ℝ E).symm x))
  let fr : StrongDual ℝ E := RCLike.reCLM.comp (f.restrictScalars ℝ)
  let fi : StrongDual ℝ E := RCLike.imCLM.comp (f.restrictScalars ℝ)
  have hr := WeakBilin.eval_continuous (topDualPairing ℝ E).flip fr
  have hi := WeakBilin.eval_continuous (topDualPairing ℝ E).flip fi
  have h := (RCLike.continuous_ofReal.comp hr).add
    ((RCLike.continuous_ofReal.comp hi).mul (continuous_const (y := (RCLike.I : 𝕜))))
  change Continuous (fun x : WeakSpace ℝ E =>
    (RCLike.re (f ((toWeakSpace ℝ E).symm x)) : 𝕜) +
    (RCLike.im (f ((toWeakSpace ℝ E).symm x)) : 𝕜) * RCLike.I) at h
  simpa only [RCLike.re_add_im] using h

end ScalarRestriction

section Compactness

variable {X : Type v} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- The final finite-intersection step works for arbitrary continuous maps;
no commutation or affine hypothesis is needed here. -/
theorem common_fixedPoint_of_finite {ι : Type w} (f : ι → X → X)
    (hcont : ∀ i, Continuous (f i))
    (hfinite : ∀ s : Finset ι, ∃ x : X, ∀ i ∈ s, f i x = x) :
    ∃ x : X, ∀ i, f i x = x := by
  let C : ι → Set X := fun i => {x | f i x = x}
  have hclosed : ∀ i, IsClosed (C i) :=
    fun i => isClosed_eq (hcont i) continuous_id
  obtain ⟨x, _, hx⟩ := isCompact_univ.inter_iInter_nonempty C hclosed (fun s => by
    obtain ⟨x, hx⟩ := hfinite s
    exact ⟨x, mem_univ x, mem_iInter.mpr fun i => mem_iInter.mpr fun hi => hx i hi⟩)
  exact ⟨x, fun i => mem_iInter.mp hx i⟩

end Compactness

/-- Finite common fixed points imply a common fixed point on the weakly
compact set itself. The compact topology here is the weak topology. -/
theorem common_fixedPoint_of_finite_weak
    {𝕜 : Type u} {E : Type v} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [SeparatingDual 𝕜 E] (K : Set E)
    (hK : IsCompact (toWeakSpace 𝕜 E '' K))
    {ι : Type w} (f : ι → K → K)
    (hcont : ∀ i, @Continuous K K (RyllNardzewskiSpec.weakSubtypeTopology 𝕜 E K)
      (RyllNardzewskiSpec.weakSubtypeTopology 𝕜 E K) (f i))
    (hfinite : ∀ s : Finset ι, ∃ x : K, ∀ i ∈ s, f i x = x) :
    ∃ x : K, ∀ i, f i x = x := by
  letI : TopologicalSpace K := RyllNardzewskiSpec.weakSubtypeTopology 𝕜 E K
  let g : K → WeakSpace 𝕜 E := fun x => toWeakSpace 𝕜 E (x : E)
  have he : Topology.IsEmbedding g :=
    ⟨⟨rfl⟩, (toWeakSpace 𝕜 E).injective.comp Subtype.val_injective⟩
  letI : T2Space K := he.t2Space
  have hg : g '' (univ : Set K) = toWeakSpace 𝕜 E '' K := by
    ext x
    simp only [mem_image, mem_univ, true_and, Subtype.exists, g]
    constructor
    · rintro ⟨a, ha, hax⟩
      exact ⟨a, ha, hax⟩
    · rintro ⟨a, ha, hax⟩
      exact ⟨a, ha, hax⟩
  letI : CompactSpace K := isCompact_univ_iff.mp (he.isCompact_iff.mpr (hg ▸ hK))
  exact common_fixedPoint_of_finite f hcont hfinite

section FiniteAverages

variable {E : Type v} [AddCommGroup E] [Module ℝ E]

/-- Affine maps on a convex domain preserve finite barycenters. The graph
is convex, so this follows directly from convexity of finite sums. -/
theorem map_finite_barycenter {K : Set E} (hc : Convex ℝ K)
    {G : E → E} (haff : MarkovKakutani.AffineOn K G)
    {ι : Type w} (s : Finset ι) (y : ι → E) (hy : ∀ i ∈ s, y i ∈ K)
    (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) (hsum : ∑ i ∈ s, a i = 1) :
    G (∑ i ∈ s, a i • y i) = ∑ i ∈ s, a i • G (y i) := by
  let graph : Set (E × E) := {z | z.1 ∈ K ∧ G z.1 = z.2}
  have hg : Convex ℝ graph := by
    rintro x ⟨hx, hGx⟩ z ⟨hz, hGz⟩ a b ha hb hab
    exact ⟨hc hx hz ha hb hab, (haff _ hx _ hz a b ha hb hab).trans
      (by simp only [hGx, hGz]; rfl)⟩
  have h := hg.sum_mem ha hsum (fun i hi => show (y i, G (y i)) ∈ graph from
    ⟨hy i hi, rfl⟩)
  change (∑ i ∈ s, a i • (y i, G (y i))).1 ∈ K ∧
    G (∑ i ∈ s, a i • (y i, G (y i))).1 =
      (∑ i ∈ s, a i • (y i, G (y i))).2 at h
  simpa only [Prod.fst_sum, Prod.snd_sum, Prod.smul_mk] using h.2

/-- A stationary family remains stationary under every affine map of its
convex domain. -/
theorem map_stationary_family {K : Set E} (hc : Convex ℝ K)
    {G : E → E} (haff : MarkovKakutani.AffineOn K G)
    {ι : Type w} {s : Finset ι} (hs : s.Nonempty)
    (y : ι → E) (hy : ∀ i ∈ s, y i ∈ K) (x : E)
    (hstat : ∑ i ∈ s, (y i - x) = 0) :
    ∑ i ∈ s, (G (y i) - G x) = 0 := by
  have hn : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  have heq : ∑ i ∈ s, y i = (s.card : ℝ) • x := by
    simpa only [Finset.sum_sub_distrib, Finset.sum_const,
      sub_eq_zero, Nat.cast_smul_eq_nsmul ℝ] using hstat
  have hw : ∑ _i ∈ s, (s.card : ℝ)⁻¹ = 1 := by simp [hn]
  have hx : ∑ i ∈ s, (s.card : ℝ)⁻¹ • y i = x := by
    rw [← Finset.smul_sum, heq, smul_smul, inv_mul_cancel₀ hn, one_smul]
  have h := map_finite_barycenter hc haff s y hy
    (fun _ => (s.card : ℝ)⁻¹) (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)) hw
  rw [hx, ← Finset.smul_sum] at h
  have hsum : ∑ i ∈ s, G (y i) = (s.card : ℝ) • G x := by
    rw [h, smul_smul, mul_inv_cancel₀ hn, one_smul]
  simpa only [Finset.sum_sub_distrib, Finset.sum_const, hsum,
    Nat.cast_smul_eq_nsmul ℝ, sub_self]

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [T2Space E]

/-- The arithmetic average of a nonempty finite affine family has a fixed
point on its compact convex domain. -/
theorem exists_stationary_point {K : Set E} (hne : K.Nonempty) (hk : IsCompact K)
    (hc : Convex ℝ K) {ι : Type w} (T : ι → E → E)
    (hcont : ∀ i, ContinuousOn (T i) K) (hm : ∀ i, MapsTo (T i) K K)
    (haff : ∀ i, MarkovKakutani.AffineOn K (T i))
    {s : Finset ι} (hs : s.Nonempty) :
    ∃ x ∈ K, ∑ i ∈ s, (T i x - x) = 0 := by
  have hn : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  let a : ℝ := (s.card : ℝ)⁻¹
  have ha : 0 ≤ a := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hw : ∑ _i ∈ s, a = 1 := by simp [a, hn]
  let A : E → E := fun x => ∑ i ∈ s, a • T i x
  have hAc : ContinuousOn A K := continuousOn_finsetSum s (fun i _ =>
    continuousOn_const.smul (hcont i))
  have hAm : MapsTo A K K := fun x hx => hc.sum_mem (fun _ _ => ha) hw
    (fun i _ => hm i hx)
  have hAa : MarkovKakutani.AffineOn K A := by
    intro x hx y hy b c hb hcc hbc
    dsimp [A]
    simp_rw [haff _ x hx y hy b c hb hcc hbc, smul_add,
      Finset.sum_add_distrib, smul_comm a b, smul_comm a c, ← Finset.smul_sum]
  obtain ⟨x, hx, hAx⟩ := MarkovKakutani.exists_fixedPoint hne hk hc hAc hAm hAa
  have heq : ∑ i ∈ s, T i x = (s.card : ℝ) • x := by
    change (∑ i ∈ s, a • T i x) = x at hAx
    rw [← Finset.smul_sum] at hAx
    calc
      ∑ i ∈ s, T i x = (s.card : ℝ) • (a • ∑ i ∈ s, T i x) := by
        rw [smul_smul, show (s.card : ℝ) * a = 1 from mul_inv_cancel₀ hn, one_smul]
      _ = (s.card : ℝ) • x := congrArg _ hAx
  exact ⟨x, hx, by simp only [Finset.sum_sub_distrib, heq, Finset.sum_const,
    Nat.cast_smul_eq_nsmul ℝ, sub_self]⟩

end FiniteAverages

/-- The closed convex hull of a countable set has a countable dense subset
in its own original topology. Finite simplices provide witnesses inside the
hull, avoiding any hereditary-separability assumption on the ambient TVS. -/
theorem separableSpace_closure_convexHull
    {E : Type v} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {A : Set E} (hA : A.Countable) : SeparableSpace (closure (convexHull ℝ A)) := by
  classical
  let Q := closure (convexHull ℝ A)
  let T := {t : Finset E // (t : Set E) ⊆ A}
  have hcount : Countable {t : Set E // t.Finite ∧ t ⊆ A} :=
    (Set.countable_ofPred_finite_subset hA).to_subtype
  letI := hcount
  let e : T → {t : Set E // t.Finite ∧ t ⊆ A} := fun t =>
    ⟨(t.val : Set E), t.val.finite_toSet, t.prop⟩
  letI : Countable T := (show Function.Injective e from by
    intro t u h
    apply Subtype.ext
    exact Finset.coe_injective (congrArg Subtype.val h)).countable
  let Δ (t : T) := {w : t.val → ℝ // (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}
  let g (t : T) (w : Δ t) : Q :=
    ⟨∑ i : t.val, w.val i • (i : E), subset_closure
      (mem_convexHull_of_exists_fintype w.val (fun i : t.val => (i : E))
        w.prop.1 w.prop.2 (fun i => t.prop i.prop) rfl)⟩
  have hg (t : T) : Continuous (g t) :=
    (continuous_finsetSum _ (fun i _ =>
      (continuous_apply i |>.comp continuous_subtype_val).smul continuous_const)).subtype_mk _
  let B : Set Q := ⋃ t : T, range (g t)
  have hB : IsSeparable B := .iUnion (fun t => isSeparable_range (hg t))
  have hcover : convexHull ℝ A ⊆ Subtype.val '' B := by
    intro x hx
    rw [convexHull_eq_union_convexHull_finite_subsets] at hx
    simp only [mem_iUnion] at hx
    obtain ⟨t, ht, hx⟩ := hx
    obtain ⟨w, hw, hsum, heq⟩ := t.mem_convexHull'.mp hx
    let tt : T := ⟨t, ht⟩
    have hsum' : ∑ i : t, w i = 1 := by simpa only [Finset.sum_coe_sort] using hsum
    let ww : Δ tt := ⟨fun i => w i, (fun i => hw i i.prop), hsum'⟩
    refine ⟨g tt ww, mem_iUnion.mpr ⟨tt, mem_range_self ww⟩, ?_⟩
    change (∑ i : t, w i • (i : E)) = x
    exact (Finset.sum_coe_sort t (fun i => w i • i)).trans heq
  have hdense : Dense B := Subtype.dense_iff.mpr (closure_mono hcover)
  exact hdense.isSeparable_iff.mp hB

/-- Finite averaging on the weakly compact domain; the conclusion is an
algebraic identity in the original space. -/
theorem exists_stationary_point_weak
    {𝕜 : Type u} {E : Type v} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [SeparatingDual 𝕜 E] (K : Set E) (hne : K.Nonempty)
    (hk : IsCompact (toWeakSpace 𝕜 E '' K)) (hc : Convex ℝ K)
    {ι : Type w} (f : ι → K → K)
    (hcont : ∀ i, @Continuous K K (RyllNardzewskiSpec.weakSubtypeTopology 𝕜 E K)
      (RyllNardzewskiSpec.weakSubtypeTopology 𝕜 E K) (f i))
    (haff : ∀ i (x y : K) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (hab : a + b = 1),
      (f i ⟨a • (x : E) + b • (y : E), hc x.prop y.prop ha hb hab⟩ : E) =
        a • (f i x : E) + b • (f i y : E))
    {s : Finset ι} (hs : s.Nonempty) :
    ∃ x : K, ∑ i ∈ s, ((f i x : E) - (x : E)) = 0 := by
  classical
  letI : TopologicalSpace K := RyllNardzewskiSpec.weakSubtypeTopology 𝕜 E K
  letI : ContinuousSMul ℝ (WeakSpace 𝕜 E) := IsScalarTower.continuousSMul 𝕜
  let w := (toWeakSpace 𝕜 E).restrictScalars ℝ
  let L := w '' K
  let r : L → K := fun z => ⟨w.symm z, by
    obtain ⟨x, hx, h⟩ := z.prop
    simpa only [← h, LinearEquiv.symm_apply_apply] using hx⟩
  have he : Topology.IsInducing (fun x : K => w (x : E)) := ⟨rfl⟩
  have hr : Continuous r := he.continuous_iff.mpr (by
    convert (continuous_subtype_val : Continuous (fun z : L => (z : WeakSpace 𝕜 E))) using 1
    funext z
    exact w.apply_symm_apply z)
  let T : ι → WeakSpace 𝕜 E → WeakSpace 𝕜 E := fun i z =>
    if hz : w.symm z ∈ K then w (f i ⟨w.symm z, hz⟩ : E) else z
  have hT (i : ι) (z : L) : T i z = w (f i (r z) : E) := by
    dsimp [T, r]
    rw [dite_eq_left (r z).prop]
  have hTc (i : ι) : ContinuousOn (T i) L := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h := he.continuous.comp ((hcont i).comp hr)
    convert h using 1
    funext z
    exact hT i z
  have hTm (i : ι) : MapsTo (T i) L L := by
    intro z hz
    rw [hT i ⟨z, hz⟩]
    exact ⟨_, (f i (r ⟨z, hz⟩)).prop, rfl⟩
  have hLconv : Convex ℝ L := hc.linear_image w.toLinearMap
  have hTa (i : ι) : MarkovKakutani.AffineOn L (T i) := by
    intro x hx y hy a b ha hb hab
    let xx : L := ⟨x, hx⟩
    let yy : L := ⟨y, hy⟩
    let zz : L := ⟨a • x + b • y, hLconv hx hy ha hb hab⟩
    rw [hT i zz, hT i xx, hT i yy]
    have hz : r zz = ⟨a • (r xx : E) + b • (r yy : E),
      hc (r xx).prop (r yy).prop ha hb hab⟩ := by
      apply Subtype.ext
      exact w.symm.map_add _ _ |>.trans (by rw [map_smul, map_smul])
    rw [hz, haff i (r xx) (r yy) a b ha hb hab, map_add, map_smul, map_smul]
  obtain ⟨z, hz, hstat⟩ := exists_stationary_point (hne.image w) hk hLconv T hTc hTm hTa hs
  refine ⟨r ⟨z, hz⟩, w.injective ?_⟩
  rw [map_sum, map_zero]
  convert hstat using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_sub, ← hT i ⟨z, hz⟩]
  congr 1

/-- A word acts by composition in the displayed order. Empty words are
useful algebraically, but the orbit below uses only nonempty words. -/
def wordMap {X : Type*} {α : Type*} (f : α → X → X) : List α → X → X
  | [] => id
  | i :: l => f i ∘ wordMap f l

@[simp] theorem wordMap_nil {X α : Type*} (f : α → X → X) :
    wordMap f [] = id := rfl

@[simp] theorem wordMap_cons {X α : Type*} (f : α → X → X) (i : α) (l : List α) :
    wordMap f (i :: l) = f i ∘ wordMap f l := rfl

theorem wordMap_append {X α : Type*} (f : α → X → X) (l m : List α) :
    wordMap f (l ++ m) = wordMap f l ∘ wordMap f m := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.cons_append, wordMap_cons, ih, Function.comp_assoc]

/-- Every nonempty word in a subfamily of a semigroup represents a member
of the original semigroup. No identity assumption is used. -/
theorem wordMap_mem_semigroup {X α ι : Type*} (f : ι → X → X)
    (hcomp : ∀ i j, ∃ k, f k = f i ∘ f j) (j : α → ι)
    {l : List α} (hl : l ≠ []) : ∃ i, f i = wordMap (f ∘ j) l := by
  induction l with
  | nil => exact (hl rfl).elim
  | cons a l ih =>
    by_cases h : l = []
    · exact ⟨j a, by simp [h, Function.comp_def]⟩
    · obtain ⟨i, hi⟩ := ih h
      obtain ⟨k, hk⟩ := hcomp (j a) i
      exact ⟨k, by rw [hk, hi]; rfl⟩

/-- Ryll--Nardzewski for the source's weakly compact convex sets.
Finite averages, the countable orbit hull, and small caps establish the
finite-intersection hypothesis. -/
theorem ryll_nardzewski : RyllNardzewskiSpec.CommonFixedPoint.{u, v, w} := by
  intro 𝕜 E _ _ _ _ _ _ _ _ _ _ K hne hK hc ι f hcomp hcont haff hnc
  letI : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  letI : SeparatingDual 𝕜 E := ⟨fun x hx => by
    obtain ⟨g, hg⟩ := RCLike.geometric_hahn_banach_point_point (𝕜 := 𝕜) hx
    exact ⟨g, by intro h; simpa [h] using hg⟩⟩
  apply common_fixedPoint_of_finite_weak K hK f hcont
  intro s
  classical
  by_cases hs : s = ∅
  · obtain ⟨x, hx⟩ := hne
    exact ⟨⟨x, hx⟩, by simp [hs]⟩
  · obtain ⟨x₀, hx₀⟩ := exists_stationary_point_weak K hne hK hc f hcont haff
      (Finset.nonempty_iff_ne_empty.mpr hs)
    let t := s.filter (fun i => (f i x₀ : E) ≠ (x₀ : E))
    by_cases ht : t = ∅
    · refine ⟨x₀, fun i hi => Subtype.ext ?_⟩
      by_contra h
      have him : i ∈ t := Finset.mem_filter.mpr ⟨hi, h⟩
      simpa [ht] using him
    have htne : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr ht
    have hstat : ∑ i ∈ t, ((f i x₀ : E) - (x₀ : E)) = 0 :=
      sum_sub_filter_ne s (fun i => (f i x₀ : E)) (x₀ : E) hx₀
    -- Extend only to use the graph lemma; every evaluation is on K.
    let T : ι → E → E := fun i x => if hx : x ∈ K then (f i ⟨x, hx⟩ : E) else x
    have hT (i : ι) (x : K) : T i x = (f i x : E) := by
      simp only [T, dite_eq_left x.prop]
    have hTa (i : ι) : MarkovKakutani.AffineOn K (T i) := by
      intro x hx y hy a b ha hb hab
      rw [hT i ⟨_, hc hx hy ha hb hab⟩, haff i ⟨x, hx⟩ ⟨y, hy⟩ a b ha hb hab,
        hT i ⟨x, hx⟩, hT i ⟨y, hy⟩]
    have hstationary (j : ι) :
        ∑ i ∈ t, ((f j (f i x₀) : E) - (f j x₀ : E)) = 0 := by
      have h := map_stationary_family hc (hTa j) htne
        (fun i => (f i x₀ : E)) (fun i _ => (f i x₀).prop) (x₀ : E) hstat
      simpa only [hT] using h
    let A : t → Set E := fun i => range (fun j => (f j (f i.val x₀) : E) - (f j x₀ : E))
    have hA (i : t) : (0 : E) ∉ closure (A i) :=
      hnc (f i.val x₀) x₀ (fun h =>
        (Finset.mem_filter.mp i.prop).2 (congrArg Subtype.val h))
    obtain ⟨p, hp, hsep⟩ := exists_seminorm_separating_finite A hA
    let κ := {l : List t // l ≠ []}
    let F : t → K → K := fun i => f i.val
    let x : κ → E := fun l => ((wordMap F l.val x₀ : K) : E)
    let y : κ → ι → E := fun l i => ((wordMap F l.val (f i x₀) : K) : E)
    have hrepr (l : κ) : ∃ j, f j = wordMap F l.val :=
      wordMap_mem_semigroup f hcomp Subtype.val l.prop
    have hxK : range x ⊆ K := by
      rintro _ ⟨l, rfl⟩
      exact (wordMap F l.val x₀).prop
    have hxne : (range x).Nonempty := by
      obtain ⟨i, hi⟩ := htne
      exact ⟨x ⟨[⟨i, hi⟩], by simp⟩, mem_range_self _⟩
    have hKr : IsCompact (toWeakSpace ℝ E '' K) := by
      have h := hK.image (continuous_to_real_weak (𝕜 := 𝕜) (E := E))
      simpa only [image_image, Function.comp_def, LinearEquiv.symm_apply_apply] using h
    have hKclosed : IsClosed K := by
      have h := hKr.isClosed.preimage (toWeakSpaceCLM ℝ E).continuous
      change IsClosed (toWeakSpace ℝ E ⁻¹' (toWeakSpace ℝ E '' K)) at h
      simpa only [Set.preimage_image_eq _ (toWeakSpace ℝ E).injective] using h
    let Q := closure (convexHull ℝ (range x))
    have hQne : Q.Nonempty := hxne.mono ((subset_convexHull ℝ _).trans subset_closure)
    have hQconv : Convex ℝ Q := (convex_convexHull ℝ _).closure
    have hQsep : SeparableSpace Q := separableSpace_closure_convexHull (countable_range x)
    have hQweak : IsCompact (toWeakSpace ℝ E '' Q) := by
      rw [show toWeakSpace ℝ E '' Q =
        closure (toWeakSpace ℝ E '' convexHull ℝ (range x)) from
        (convex_convexHull ℝ _).toWeakSpace_closure ℝ]
      exact hKr.of_isClosed_subset isClosed_closure
        (closure_minimal (image_mono (convexHull_min hxK hc)) hKr.isClosed)
    obtain ⟨C, hCQ, hCc, hCv, d, _hd₀, hd₁, hdiam⟩ :=
      ExpandedFA.P1.small_cap ℝ E Q hQne hQsep hQweak hQconv p hp 1 zero_lt_one
    have hCclosed : IsClosed C := by
      have h := hCc.preimage (toWeakSpaceCLM ℝ E).continuous
      change IsClosed (toWeakSpace ℝ E ⁻¹' (toWeakSpace ℝ E '' C)) at h
      simpa only [Set.preimage_image_eq _ (toWeakSpace ℝ E).injective] using h
    have hyQ : ∀ l i, i ∈ t → y l i ∈ Q := by
      intro l i hi
      let m : κ := ⟨l.val ++ [⟨i, hi⟩], by simp⟩
      have hxy : x m = y l i := by
        dsimp [x, y, m]
        rw [wordMap_append]
        rfl
      exact subset_closure (subset_convexHull ℝ _ ⟨m, hxy⟩)
    have hstatword : ∀ l, ∑ i ∈ t, (y l i - x l) = 0 := by
      intro l
      obtain ⟨j, hj⟩ := hrepr l
      simpa only [x, y, ← hj] using hstationary j
    have hsepword : ∀ l i, i ∈ t → 1 ≤ p (y l i - x l) := by
      intro l i hi
      obtain ⟨j, hj⟩ := hrepr l
      apply hsep ⟨i, hi⟩
      exact ⟨j, by simp only [y, x, ← hj]⟩
    exact (stationary_orbit_cap_contradiction t htne x y Q C rfl hCQ hCclosed hCv
      hyQ hstatword p d 1 hd₁ hdiam hsepword).elim

end ExpandedFA.P1.RyllNardzewski
