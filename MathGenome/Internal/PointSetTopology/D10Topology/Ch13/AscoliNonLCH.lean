import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.AscoliNonLCH
import MathGenome.Internal.PointSetTopology.D10Topology.Ch13.FunctionTopologies
import MathGenome.Internal.PointSetTopology.D10Topology.Ch13.FunctorialMaps
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.DiscreteSubset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Proof of the non-LCH Ascoli counterexample from paper.tex, chapter 13.
Countable sets are closed and discrete; consequently every compact set is
finite. A convergent sequence of triangular bumps with its zero limit is
then compact for the compact-open topology. Every neighborhood of zero,
however, meets an interval on which a sufficiently late bump exceeds 1/2.
-/
noncomputable section
open Set Filter
open scoped Topology
namespace D10Topology.Ch13.AscoliNonLCH
abbrev Domain := Specs.D10Topology.Ch13.AscoliNonLCH.Domain
abbrev toReal := Specs.D10Topology.Ch13.AscoliNonLCH.toReal
abbrev ofReal := Specs.D10Topology.Ch13.AscoliNonLCH.ofReal
abbrev generators := Specs.D10Topology.Ch13.AscoliNonLCH.generators
abbrev domainTopology := Specs.D10Topology.Ch13.AscoliNonLCH.domainTopology
abbrev tent := Specs.D10Topology.Ch13.AscoliNonLCH.tent
abbrev family := Specs.D10Topology.Ch13.AscoliNonLCH.family

lemma toReal_injective : Function.Injective toReal := fun _ _ h => h
lemma ofReal_toReal (x : Domain) : ofReal (toReal x) = x := rfl
lemma toReal_ofReal (x : ℝ) : toReal (ofReal x) = x := rfl

lemma basic_open (O : Set ℝ) (hO : IsOpen O) (C : Set ℝ) (hC : C.Countable) :
    IsOpen (toReal ⁻¹' (O \ C)) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨O, hO, C, hC, rfl⟩

lemma coordinate_continuous : Continuous toReal := by
  apply continuous_def.mpr
  intro O hO
  simpa using basic_open O hO ∅ countable_empty

lemma topology_basis : Specs.D10Topology.Ch13.AscoliNonLCH.topology_basis := by
  change TopologicalSpace.IsTopologicalBasis generators
  have h := TopologicalSpace.isTopologicalBasis_of_subbasis_of_inter
    (t := domainTopology) rfl (r := generators) (by
      rintro B ⟨O, hO, C, hC, rfl⟩ B' ⟨O', hO', C', hC', rfl⟩
      refine ⟨O ∩ O', hO.inter hO', C ∪ C', hC.union hC', ?_⟩
      ext x
      simp only [mem_inter_iff, mem_preimage, Set.mem_sdiff, mem_union]
      tauto)
  have hu : univ ∈ generators := ⟨univ, isOpen_univ, ∅, countable_empty, by simp⟩
  simpa only [insert_eq_of_mem hu] using h

lemma hausdorff : Specs.D10Topology.Ch13.AscoliNonLCH.hausdorff :=
  T2Space.of_injective_continuous toReal_injective coordinate_continuous

lemma countable_closed {B : Set Domain} (hB : B.Countable) : IsClosed B := by
  apply isOpen_compl_iff.mp
  convert basic_open univ isOpen_univ (toReal '' B) (hB.image toReal) using 1
  ext x
  simp only [mem_preimage, Set.mem_sdiff, mem_univ, true_and, mem_compl_iff]
  rw [toReal_injective.mem_set_image]

lemma countable_discrete {B : Set Domain} (hB : B.Countable) : IsDiscrete B := by
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro b hb
  refine ⟨(B \ {b})ᶜ, (countable_closed (hB.mono sdiff_subset)).isOpen_compl, ?_⟩
  ext x
  simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff, mem_singleton_iff]
  aesop

/-- An infinite compact set would contain a countably infinite closed discrete subset. -/
lemma compact_iff_finite : Specs.D10Topology.Ch13.AscoliNonLCH.compact_iff_finite := by
  intro K
  refine ⟨fun hK => ?_, fun hK => hK.isCompact⟩
  by_contra hInf
  obtain ⟨B, hBK, hB, hBi⟩ := (Set.not_finite.mp hInf).exists_subset_countable_infinite
  have hc : IsCompact B := hK.of_isClosed_subset (countable_closed hB) hBK
  exact hBi (hc.finite (countable_discrete hB))

/-- Every neighborhood contains an ordinary interval after a countable deletion. -/
lemma neighborhood_interval {x : Domain} {U : Set Domain} (hU : U ∈ 𝓝 x) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : Set ℝ, C.Countable ∧
      toReal ⁻¹' (Ioo (toReal x - δ) (toReal x + δ) \ C) ⊆ U := by
  obtain ⟨B, ⟨O, hO, C, hC, rfl⟩, hx, hBU⟩ := topology_basis.mem_nhds_iff.mp hU
  obtain ⟨δ, hδ, hδO⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hx.1)
  refine ⟨δ, hδ, C, hC, fun y hy => hBU ⟨hδO ?_, hy.2⟩⟩
  simpa only [Metric.mem_ball, Real.dist_eq, abs_lt] using
    (show -δ < toReal y - toReal x ∧ toReal y - toReal x < δ by
      constructor <;> linarith [hy.1.1, hy.1.2])

/-- Countable deletion cannot exhaust any nonempty ordinary real interval. -/
lemma interval_sdiff_nonempty {a b : ℝ} (hab : a < b) {C : Set ℝ} (hC : C.Countable) :
    (Ioo a b \ C).Nonempty := by
  by_contra h
  have hs : Ioo a b ⊆ C := sdiff_eq_empty.mp (not_nonempty_iff_eq_empty.mp h)
  have hc := hC.mono hs
  exact (not_le.mpr hab) (Cardinal.Real.Ioo_countable_iff.mp hc)

lemma neighborhood_infinite {x : Domain} {U : Set Domain} (hU : U ∈ 𝓝 x) :
    U.Infinite := by
  intro hF
  obtain ⟨δ, hδ, C, hC, hs⟩ := neighborhood_interval hU
  obtain ⟨y, hyI, hyC⟩ := interval_sdiff_nonempty
    (show toReal x - δ < toReal x + δ by linarith)
    (hC.union (hF.countable.image toReal))
  have hy : ofReal y ∈ U := hs ⟨hyI, fun h => hyC (Or.inl h)⟩
  exact hyC (Or.inr ⟨ofReal y, hy, rfl⟩)

lemma not_locally_compact : Specs.D10Topology.Ch13.AscoliNonLCH.not_locally_compact := by
  intro h
  letI : WeaklyLocallyCompactSpace Domain := h
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (ofReal 0)
  exact neighborhood_infinite hK0 ((compact_iff_finite K).mp hK)

lemma compactOpen_eq_pointwise :
    compactOpenContinuousTopology (X := Domain) (Y := ℝ) = pointwiseContinuousTopology := by
  have h : pointwiseTopology (X := Domain) (Y := ℝ) ≤ compactOpenTopology := by
    apply le_generateFrom
    rintro B ⟨K, hK, O, hO, rfl⟩
    have he : compactOpenSet K O = ⋂ x ∈ K, (fun f : Domain → ℝ => f x) ⁻¹' O := by
      ext f
      simp only [mem_iInter, mem_preimage, compactOpenSet_mem]
    change IsOpen (compactOpenSet K O)
    rw [he]
    exact ((compact_iff_finite K).mp hK).isOpen_biInter
      (fun x _ => hO.preimage (continuous_apply x))
  apply le_antisymm
  · rw [compactOpenContinuousTopology_eq_mathlib]
    exact continuous_iff_le_induced.mp continuous_coeFun
  · exact induced_mono h

lemma tents_continuous : Specs.D10Topology.Ch13.AscoliNonLCH.tents_continuous := by
  intro n
  exact continuous_const.max (continuous_const.sub
    ((continuous_const.mul coordinate_continuous).sub continuous_const).abs)

lemma tents_pointwise : Specs.D10Topology.Ch13.AscoliNonLCH.tents_pointwise := by
  intro x
  by_cases hx : toReal x ≤ 0
  · have hz : ∀ n, tent n x = 0 := by
      intro n
      have hnx : (n + 1 : ℝ) * toReal x ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hx
      change max 0 (1 - |(n + 1 : ℝ) * toReal x - 1|) = 0
      rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · have hp : 0 < toReal x := lt_of_not_ge hx
    have ht : Tendsto (fun n : ℕ => (n + 1 : ℝ) * toReal x) atTop atTop :=
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_mul_const hp
    have he : ∀ᶠ n : ℕ in atTop, tent n x = 0 := by
      filter_upwards [ht.eventually_ge_atTop 2] with n hn
      change max 0 (1 - |(n + 1 : ℝ) * toReal x - 1|) = 0
      rw [abs_of_nonneg (by linarith), max_eq_left (by linarith)]
    exact tendsto_const_nhds.congr' (he.mono fun _ hn => hn.symm)

/-- The bump maps retain their ordinary formula on the refined domain. -/
def tentMap (n : ℕ) : ContinuousMap Domain ℝ := ⟨tent n, tents_continuous n⟩

def zeroMap : ContinuousMap Domain ℝ := ContinuousMap.const Domain 0

lemma family_eq_insert_range : family = insert zeroMap (range tentMap) := by
  ext f
  constructor
  · rintro (hf | ⟨n, hn⟩)
    · exact Or.inl (DFunLike.ext _ _ hf)
    · exact Or.inr ⟨n, DFunLike.ext _ _ (fun x => (hn x).symm)⟩
  · rintro (rfl | ⟨n, rfl⟩)
    · exact Or.inl fun _ => rfl
    · exact Or.inr ⟨n, fun _ => rfl⟩

lemma tents_tendsto_compactOpen : Tendsto tentMap atTop
    (@nhds (ContinuousMap Domain ℝ) compactOpenContinuousTopology zeroMap) := by
  rw [compactOpen_eq_pointwise]
  change Tendsto tentMap atTop (@nhds _ (TopologicalSpace.induced
    (fun f : ContinuousMap Domain ℝ => (f : Domain → ℝ)) _) zeroMap)
  rw [nhds_induced, tendsto_comap_iff]
  exact tendsto_pi_nhds.mpr tents_pointwise

lemma family_compact :
    @IsCompact (ContinuousMap Domain ℝ) compactOpenContinuousTopology family := by
  rw [show family = insert zeroMap (range tentMap) from family_eq_insert_range]
  letI : TopologicalSpace (ContinuousMap Domain ℝ) := compactOpenContinuousTopology
  exact tents_tendsto_compactOpen.isCompact_insert_range

lemma family_not_equicontinuousAt_zero :
    ¬ EquicontinuousAt family (ofReal 0) := by
  intro h
  obtain ⟨U, hU, hsmall⟩ := h (1 / 2) (by norm_num)
  obtain ⟨δ, hδ, C, hC, hs⟩ := neighborhood_interval hU
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / δ)
  have hn2 : 0 < 2 * (n + 1 : ℝ) := by positivity
  have hδn : 2 < δ * (n + 1 : ℝ) := by
    have := (div_lt_iff₀ hδ).mp hn
    nlinarith
  have hab : 1 / (2 * (n + 1 : ℝ)) < 3 / (2 * (n + 1 : ℝ)) :=
    div_lt_div_of_pos_right (by norm_num) hn2
  obtain ⟨r, hr, hrC⟩ := interval_sdiff_nonempty hab hC
  have hr0 : 0 < r := (div_pos (by norm_num) hn2).trans hr.1
  have hrd : r < δ := by
    have : 3 / (2 * (n + 1 : ℝ)) < δ := (div_lt_iff₀ hn2).mpr (by nlinarith)
    exact hr.2.trans this
  have hrU : ofReal r ∈ U := by
    apply hs
    change (0 - δ < r ∧ r < 0 + δ) ∧ r ∉ C
    exact ⟨⟨by linarith, by linarith⟩, hrC⟩
  have hlow : 1 / 2 < (n + 1 : ℝ) * r := by
    have := (div_lt_iff₀ hn2).mp hr.1
    nlinarith
  have hupp : (n + 1 : ℝ) * r < 3 / 2 := by
    have := (lt_div_iff₀ hn2).mp hr.2
    nlinarith
  have habs : |(n + 1 : ℝ) * r - 1| < 1 / 2 :=
    abs_lt.mpr ⟨by linarith, by linarith⟩
  have hlarge : 1 / 2 < tent n (ofReal r) :=
    (show 1 / 2 < 1 - |(n + 1 : ℝ) * r - 1| by linarith).trans_le (le_max_right _ _)
  have hz : tent n (ofReal 0) = 0 := by
    norm_num [tent, Specs.D10Topology.Ch13.AscoliNonLCH.tent,
      ofReal, toReal, Specs.D10Topology.Ch13.AscoliNonLCH.ofReal,
      Specs.D10Topology.Ch13.AscoliNonLCH.toReal]
  have hm : tentMap n ∈ family := Or.inr ⟨n, fun _ => rfl⟩
  have hh := hsmall (ofReal r) hrU (tentMap n) hm
  change dist (tent n (ofReal r)) (tent n (ofReal 0)) < 1 / 2 at hh
  rw [hz, Real.dist_eq, sub_zero, abs_of_nonneg (le_max_left _ _)] at hh
  exact (not_lt_of_ge hlarge.le) hh

lemma counterexample : Specs.D10Topology.Ch13.AscoliNonLCH.counterexample := by
  letI : T2Space Domain := hausdorff
  letI : TopologicalSpace (ContinuousMap Domain ℝ) := compactOpenContinuousTopology
  letI : T2Space (ContinuousMap Domain ℝ) := compactOpen_hausdorff
  refine ⟨hausdorff, not_locally_compact, ?_, ?_⟩
  · exact family_compact.closure
  · intro h
    exact family_not_equicontinuousAt_zero (h (ofReal 0))

end D10Topology.Ch13.AscoliNonLCH


