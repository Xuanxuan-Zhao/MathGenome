import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.FiniteCompactPartition
import MathGenome.Internal.MultivariableAnalysis.D04.C14.EuclideanSmoothCutoffs
import MathGenome.Internal.MultivariableAnalysis.D04.C14.EmbeddedManifoldCharts
import Mathlib.Tactic.Linarith

noncomputable section
open Set Filter Topology
open scoped ContDiff BigOperators
namespace D04.FiniteCompactPartition
open Specs.D04.C14.FiniteCompactPartition

/-- The parameter model is closed even in dimension zero and at a boundary. -/
theorem parameterSpace_isClosed (k : ℕ) (half : Bool) :
    IsClosed (D04.parameterSpace k half) := by
  cases half with
  | false => exact isClosed_univ
  | true =>
    cases k with
    | zero => exact isClosed_univ
    | succ d => exact isClosed_le continuous_const (EuclideanSpace.proj (Fin.last d)).continuous

/-- A chart supplies an ambient open neighborhood whose intersection with M
lies in a compact subset of any prescribed relative open neighborhood. -/
theorem chart_compact_neighborhood {r : ℕ∞ω} {k n : ℕ} {M : Set (D04.E n)}
    (c : D04.EmbeddedChart r k n M) (p : M) (hp : (p : D04.E n) ∈ c.ambient)
    (U : Set M) (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ (O L : Set (D04.E n)), IsOpen O ∧ (p : D04.E n) ∈ O ∧
      IsCompact L ∧ L ⊆ M ∧
      (∀ x : M, (x : D04.E n) ∈ L → x ∈ U) ∧ M ∩ O ⊆ L := by
  obtain ⟨A, hA, hAU⟩ := isOpen_induced_iff.mp hU
  let d := c.restrict A hA
  have hpA : (p : D04.E n) ∈ A := by change p ∈ Subtype.val ⁻¹' A; rw [hAU]; exact hpU
  have hpD : (p : D04.E n) ∈ M ∩ d.ambient := ⟨p.property, hp, hpA⟩
  let u := d.invFun p
  have hu : u ∈ d.source := d.map_target hpD
  obtain ⟨B, hB, hsource⟩ := d.source_open
  have huB : u ∈ B := (hsource ▸ hu).2
  obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.mp hB u huB
  let C := D04.parameterSpace k d.half ∩ Metric.closedBall u (ε / 2)
  have hC : IsCompact C := (isCompact_closedBall u (ε / 2)).inter_left
    (parameterSpace_isClosed k d.half)
  have hCs : C ⊆ d.source := by
    intro v hv
    rw [hsource]
    exact ⟨hv.1, hεB (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hv.2).trans_lt
      (by linarith)))⟩
  let L := d.toFun '' C
  have hL : IsCompact L := hC.image_of_continuousOn (d.continuous_toFun.mono hCs)
  obtain ⟨T, hT, heT⟩ := continuousOn_iff'.mp d.continuous_invFun
    (Metric.ball u (ε / 2)) Metric.isOpen_ball
  have hpT : (p : D04.E n) ∈ T := by
    have hx : (p : D04.E n) ∈ d.invFun ⁻¹' Metric.ball u (ε / 2) ∩ (M ∩ d.ambient) :=
      ⟨Metric.mem_ball_self (by linarith), hpD⟩
    rw [heT] at hx
    exact hx.1
  refine ⟨d.ambient ∩ T, L, d.ambient_open.inter hT, ⟨hpD.2, hpT⟩, hL,
    ?_, ?_, ?_⟩
  · rintro x ⟨v, hv, rfl⟩
    exact (d.map_source (hCs hv)).1
  · intro x hx
    obtain ⟨v, hv, hve⟩ := hx
    have hvA : d.toFun v ∈ A := (d.map_source (hCs hv)).2.2
    rw [← hAU]
    change (x : D04.E n) ∈ A
    rwa [hve] at hvA
  · intro x hx
    have hxd : x ∈ M ∩ d.ambient := ⟨hx.1, hx.2.1⟩
    have hxi : x ∈ T ∩ (M ∩ d.ambient) := ⟨hx.2.2, hxd⟩
    rw [← heT] at hxi
    refine ⟨d.invFun x, ⟨?_, Metric.ball_subset_closedBall hxi.1⟩, d.right_inv x hxd⟩
    exact (hsource ▸ d.map_target hxd).1

/-- Ambient smooth bumps with compact support relative to M. The ambient
support is first confined to a neighborhood with compact intersection control. -/
theorem chart_bump {r : ℕ∞ω} {k n : ℕ} {M : Set (D04.E n)}
    (c : D04.EmbeddedChart r k n M) (p : M) (hp : (p : D04.E n) ∈ c.ambient)
    (U : Set M) (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ (ρ : D04.E n → ℝ) (V : Set M),
      ContDiff ℝ ∞ ρ ∧ (∀ x, ρ x ∈ Icc (0 : ℝ) 1) ∧
      IsOpen V ∧ p ∈ V ∧ EqOn (fun x : M => ρ x) (fun _ => 1) V ∧
      IsCompact (tsupport (fun x : M => ρ x)) ∧
      tsupport (fun x : M => ρ x) ⊆ U := by
  obtain ⟨O, L, hO, hpO, hL, hLM, hLU, hOL⟩ := chart_compact_neighborhood c p hp U hU hpU
  obtain ⟨ρ, hρ⟩ := D04.EuclideanSmoothCutoffs.exists_smooth_cutoff
    {(p : D04.E n)} O (isCompact_singleton) hO (singleton_subset_iff.mpr hpO)
  rcases hρ with ⟨hsm, _, hvals, ⟨A, hA, hpA, hone⟩, _, hsupport⟩
  have hsupL : tsupport (fun x : M => ρ x) ⊆ Subtype.val ⁻¹' L := by
    apply closure_minimal _ (hL.isClosed.preimage continuous_subtype_val)
    intro x hx
    apply hOL
    exact ⟨x.property, hsupport (subset_tsupport ρ hx)⟩
  have hLc : IsCompact (Subtype.val ⁻¹' L : Set M) := by
    apply (Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage_iff ?_).mpr hL
    simpa only [Subtype.range_coe] using hLM
  refine ⟨ρ, Subtype.val ⁻¹' A, hsm, hvals, hA.preimage continuous_subtype_val,
    hpA (mem_singleton _), fun x hx => hone hx,
    hLc.of_isClosed_subset (isClosed_tsupport _) hsupL, ?_⟩
  exact fun x hx => hLU x (hsupL hx)

/-- Normalize a finite family of nonnegative bumps without a piecewise
extension across a zero denominator. The seed term vanishes for S ≥ 1. -/
theorem normalize_bumps {n m : ℕ} (ρ : Fin m → D04.E n → ℝ)
    (hsm : ∀ i, ContDiff ℝ ∞ (ρ i))
    (hnon : ∀ i x, 0 ≤ ρ i x) :
    ∃ f : Fin m → D04.E n → ℝ,
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ i x, 0 ≤ f i x) ∧
      (∀ {X : Type} [TopologicalSpace X] (g : X → D04.E n) i,
        tsupport (fun x => f i (g x)) ⊆ tsupport (fun x => ρ i (g x))) ∧
      (∀ x, (∑ i, f i x) ∈ Icc (0 : ℝ) 1) ∧
      (∀ x, 1 ≤ ∑ i, ρ i x → ∑ i, f i x = 1) := by
  let S := fun x => ∑ i, ρ i x
  let b := D04.EuclideanSmoothCutoffs.cutoffSeed
  let D := fun x => S x + b (1 - S x)
  have hSsm : ContDiff ℝ ∞ S := ContDiff.sum fun i _ => hsm i
  have hSnon x : 0 ≤ S x := Finset.sum_nonneg (fun i _ => hnon i x)
  have hbnon t : 0 ≤ b t := D04.EuclideanSmoothCutoffs.cutoffSeed_properties.2.2.1 t
  have hDpos x : 0 < D x := by
    by_cases h : 0 < S x
    · exact add_pos_of_pos_of_nonneg h (hbnon _)
    · have hz : S x = 0 := le_antisymm (le_of_not_gt h) (hSnon x)
      change 0 < S x + b (1 - S x)
      rw [hz, sub_zero, zero_add]
      exact D04.EuclideanSmoothCutoffs.cutoffSeed_properties.2.2.2.2 1 zero_lt_one
  have hDsm : ContDiff ℝ ∞ D := hSsm.add
    (D04.EuclideanSmoothCutoffs.cutoffSeed_properties.1.comp (contDiff_const.sub hSsm))
  let f := fun i x => ρ i x / D x
  have hsum x : ∑ i, f i x = S x / D x := by
    exact (Finset.sum_div _ _ _).symm
  refine ⟨f, fun i => (hsm i).div hDsm (fun x => ne_of_gt (hDpos x)),
    fun i x => div_nonneg (hnon i x) (hDpos x).le, ?_, ?_, ?_⟩
  · intro X _ g i
    simp only [f, div_eq_mul_inv]
    exact tsupport_mul_subset_left
  · intro x
    rw [hsum]
    exact ⟨div_nonneg (hSnon x) (hDpos x).le,
      (div_le_one (hDpos x)).mpr (le_add_of_nonneg_right (hbnon _))⟩
  · intro x hx
    rw [hsum]
    have hb : b (1 - S x) = 0 :=
      D04.EuclideanSmoothCutoffs.cutoffSeed_properties.2.2.2.1 _ (sub_nonpos.mpr hx)
    change S x / (S x + b (1 - S x)) = 1
    rw [hb, add_zero, div_self (ne_of_gt (lt_of_lt_of_le zero_lt_one hx))]

/-- Finite localization with all requested neighborhoods fixed in advance. -/
theorem finite_partition_refined : finite_partition_refinedType := by
  classical
  intro r k n M _ K hK ι U hU hcover c hc W hW hpW
  have hchoice : ∀ p : K, ∃ a, p.val ∈ U a :=
    fun p => mem_iUnion.mp (hcover p.property)
  choose a ha using hchoice
  let T := fun p : K => U (a p) ∩ W p ∩ Subtype.val ⁻¹' (c p).ambient
  have hT p : IsOpen (T p) :=
    ((hU _).inter (hW _)).inter ((c p).ambient_open.preimage continuous_subtype_val)
  have hpT p : p.val ∈ T p := ⟨⟨ha p, hpW p⟩, hc p⟩
  choose ρ V hρsm hρvals hV hpV hρone hρcompact hρsupport using
    fun p : K => chart_bump (c p) p.val (hc p) (T p) (hT p) (hpT p)
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover V hV (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hpV ⟨x, hx⟩⟩)
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let p : Fin (Fintype.card I) → K := fun i => (e i).val
  obtain ⟨f, hfsm, hfnon, hfsupport, hfrange, hfone⟩ := normalize_bumps
    (fun i => ρ (p i)) (fun i => hρsm (p i)) (fun i x => (hρvals (p i) x).1)
  have hsupp i : tsupport (fun x : M => f i x) ⊆ T (p i) :=
    (hfsupport (fun x : M => (x : D04.E n)) i).trans (hρsupport (p i))
  refine ⟨Fintype.card I, a ∘ p, p, f, ⟨hfsm, fun i x => hfnon i x, ?_, ?_,
    fun x => hfrange x⟩, ?_⟩
  · intro i
    exact ⟨(hρcompact (p i)).of_isClosed_subset (isClosed_tsupport _)
      (hfsupport (fun x : M => (x : D04.E n)) i), fun x hx => (hsupp i hx).1.1⟩
  · refine ⟨⋃ q ∈ I, V q, isOpen_biUnion fun q _ => hV q, hI, ?_⟩
    intro x hx
    obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp hx
    obtain ⟨i, hi⟩ := e.surjective ⟨q, hq⟩
    have hpi : p i = q := congrArg Subtype.val hi
    apply hfone
    have hval : ρ (p i) x = 1 := by rw [hpi]; exact hρone q hxq
    rw [← hval]
    exact Finset.single_le_sum (fun j _ => (hρvals (p j) x).1) (Finset.mem_univ i)
  · intro i x hx
    exact ⟨(hsupp i hx).1.2, (hsupp i hx).2⟩

/-- The original partition theorem, obtained by choosing charts at K and
using the whole manifold as the optional further neighborhood. -/
theorem finite_partition : finite_partitionType := by
  classical
  intro r k n M hM K hK ι U hU hcover
  have hcharts : ∀ p : K, ∃ c : D04.EmbeddedChart r k n M,
      (p.val : D04.E n) ∈ c.ambient := by
    intro p
    obtain ⟨c, u, hu, he⟩ := hM.2.2 p.val p.val.property
    exact ⟨c, he ▸ (c.map_source hu.1).2⟩
  choose c hc using hcharts
  obtain ⟨m, a, p, f, hf, hs⟩ := finite_partition_refined hM K hK U hU hcover
    c hc (fun _ => univ) (fun _ => isOpen_univ) (fun _ => mem_univ _)
  exact ⟨m, a, f, hf, fun i => ⟨c (p i), fun x hx => (hs i hx).2⟩⟩

/-- Specialization to the shared ambient compactness and relative-open cover
predicates, using the embedding of the subtype for the compactness bridge. -/
theorem finite_partition_ambient : finite_partition_ambientType := by
  intro r k n M hM K hK hKM ι U hU hcover
  have hKM' : K ⊆ Set.range (Subtype.val : M → D04.E n) := by
    simpa only [Subtype.range_coe] using hKM
  have hK' : IsCompact (Subtype.val ⁻¹' K : Set M) :=
    (Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage_iff hKM').mpr
      ((D04.compact_iff_isCompact K).mp hK)
  apply finite_partition hM _ hK' (fun a => Subtype.val ⁻¹' U a)
    (fun a => ((D04.relativelyOpen_subtype_iff M (U a)).mp (hU a)).2)
  intro x hx
  obtain ⟨a, ha⟩ := mem_iUnion.mp (hcover hx)
  exact mem_iUnion.mpr ⟨a, ha⟩

end D04.FiniteCompactPartition
