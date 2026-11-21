import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.DomainDefiningFunctions
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.RegularDomains
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Localization.SmoothExhaustion
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.BoundaryCones

namespace SmoothManifolds.DomainDefiningFunctions
open ModelData AtlasData MapData BoundaryData MapClassData RegularDomainData
  DomainDefiningData PartitionData FiniteRegularityData Set Filter
open scoped Topology
universe u v

abbrev IsDefiningFunction := @DomainDefiningData.IsDefiningFunction

variable {m : ℕ} {b : ModelKind} {M : Type u} [TopologicalSpace M]

/-- Scalar local extensions and maps to the standard real manifold coincide. -/
theorem scalarSmooth_iff (T : SmoothManifold m b M)
    (R : SmoothManifold 1 .euclidean ℝ) (hR : HasStandardRealChart R) (f : M → ℝ) :
    ScalarSmooth T.smoothStructure.val f ↔ IsSmoothMap T R f := by
  constructor
  · intro hf p
    obtain ⟨e, he, hp⟩ := T.smoothStructure.property.1.1 p
    apply (manifoldContDiffAt_iff_oneChart _ _ _ T.smoothStructure.property.1
      R.smoothStructure.property.1 f p).mpr
    exact ⟨(scalarContDiffAt_iff _ _ _ p).mp (hf p) |>.1,
      e, he, realChart, hR, hp, mem_univ _, (hf p).2 e he hp⟩
  · intro hf p
    exact ⟨continuousAt_pi.mpr (fun _ => (hf p).1),
      fun e he hp => (hf p).2 e he realChart hR hp (mem_univ _)⟩

/-- Chart derivatives depend only on the germ of a map. -/
theorem chartDerivative_congr {n : ℕ} {a : ModelKind} {N : Type v}
    [TopologicalSpace N] (e : ModelChart m b M) (d : ModelChart n a N)
    {f g : M → N} {p : M} (h : f =ᶠ[𝓝 p] g) :
    chartDerivative e d f p = chartDerivative e d g p := by
  have hh : HasCoordinateDerivative e (fun y => (d (f y)).val) p =
      HasCoordinateDerivative e (fun y => (d (g y)).val) p := by
    funext L
    apply propext
    constructor <;> rintro ⟨F, hF, heq⟩
    · exact ⟨F, hF, heq.trans (h.fun_comp (fun z => (d z).val))⟩
    · exact ⟨F, hF, heq.trans (h.symm.fun_comp (fun z => (d z).val))⟩
  unfold chartDerivative coordinateDerivative
  rw [hh]

/-- In particular the full submersion condition is preserved by germ equality. -/
theorem isSubmersionAt_congr (T : SmoothManifold m b M)
    (R : SmoothManifold 1 .euclidean ℝ) (hR : HasStandardRealChart R)
    {f g : M → ℝ} (hf : IsSmoothMap T R f) (hg : IsSmoothMap T R g)
    {p : M} (h : f =ᶠ[𝓝 p] g) (hp : IsSubmersionAt T R f p) :
    IsSubmersionAt T R g p := by
  obtain ⟨e, he, hpe⟩ := T.smoothStructure.property.1.1 p
  have hf1 := manifoldContDiff_of_le (⊤ : ℕ∞) 1 _ _ f le_top hf
  have hg1 := manifoldContDiff_of_le (⊤ : ℕ∞) 1 _ _ g le_top hg
  apply (MapClasses.chart_invariants T R g hg1 p e realChart he hR hpe
    (mem_univ _)).2.2.mpr
  rw [← chartDerivative_congr e realChart h]
  exact (MapClasses.chart_invariants T R f hf1 p e realChart he hR hpe
    (mem_univ _)).2.2.mp hp

/-- Compactify only after constructing a defining function. Near the entire
closed domain the replacement is the original function, so the full boundary
differential, as well as its sign, is preserved. -/
theorem compactify_defining_function :
    Specs.SmoothManifolds.Ch03.DomainDefiningFunctions.compactify_defining_functionType.{u} := by
  intro m b M _ T R d f hR hd hf
  classical
  obtain ⟨ρ, hρsmooth, hρnonneg, hρcompact⟩ := exists_smooth_exhaustion T
  obtain ⟨χ, hχ, hχcompact⟩ := exists_compactly_supported_smooth_cutoff T d univ hd
    isOpen_univ (subset_univ _)
  obtain ⟨hχsmooth, hχ01, ⟨V, hV, hdV, hχV⟩, _⟩ := hχ
  let g : M → ℝ := fun x => χ x * f x + (1 - χ x) * (ρ x + 1)
  have hfsmooth : ScalarSmooth T.smoothStructure.val f :=
    (scalarSmooth_iff T R hR f).mpr hf.1
  have hgsmooth : ScalarSmooth T.smoothStructure.val g := by
    intro x
    exact ScalarContDiffAt.add (ScalarContDiffAt.mul (hχsmooth x) (hfsmooth x))
      (ScalarContDiffAt.mul
        (ScalarContDiffAt.add (ScalarContDiffAt.const _ _ 1 x)
          (ScalarContDiffAt.neg (hχsmooth x)))
        (ScalarContDiffAt.add (hρsmooth x) (ScalarContDiffAt.const _ _ 1 x)))
  have hgmap : IsSmoothMap T R g := (scalarSmooth_iff T R hR g).mp hgsmooth
  have hgf (p : M) (hp : p ∈ d) : g =ᶠ[𝓝 p] f := by
    filter_upwards [hV.mem_nhds (hdV hp)] with x hx
    simp [g, hχV hx]
  have hfpos (p : M) (hp : p ∉ d) : 0 < f p := by
    have h : ¬ f p ≤ 0 := by
      intro h
      exact hp (hf.2.1.symm ▸ h)
    exact lt_of_not_ge h
  have hgpos (p : M) (hp : p ∉ d) : 0 < g p := by
    have hfp := hfpos p hp
    have hrp : 0 < ρ p + 1 := by linarith [hρnonneg p]
    by_cases hc : χ p = 1
    · simpa [g, hc] using hfp
    · have hclt : χ p < 1 := lt_of_le_of_ne (hχ01 p).2 hc
      have hfirst : 0 ≤ χ p * f p := mul_nonneg (hχ01 p).1 hfp.le
      have hsecond : 0 < (1 - χ p) * (ρ p + 1) :=
        mul_pos (sub_pos.mpr hclt) hrp
      exact add_pos_of_nonneg_of_pos hfirst hsecond
  have hdg : d = sublevel g := by
    ext p
    constructor
    · intro hp
      change g p ≤ 0
      rw [(hgf p hp).eq_of_nhds]
      have hpf : p ∈ sublevel f := hf.2.1 ▸ hp
      exact hpf
    · intro hp
      by_contra hpd
      exact (not_lt_of_ge hp) (hgpos p hpd)
  have hzero : g ⁻¹' {0} = f ⁻¹' {0} := by
    ext p
    constructor
    · intro hp
      have hp0 : g p = 0 := hp
      have hpd : p ∈ d := by rw [hdg]; change g p ≤ 0; exact hp0.le
      change f p = 0
      rw [← (hgf p hpd).eq_of_nhds]
      exact hp0
    · intro hp
      have hp0 : f p = 0 := hp
      have hpd : p ∈ d := by rw [hf.2.1]; change f p ≤ 0; exact hp0.le
      change g p = 0
      rw [(hgf p hpd).eq_of_nhds]
      exact hp0
  refine ⟨g, ⟨hgmap, hdg, hf.2.2.1.trans hzero.symm, ?_⟩, hgf, ?_⟩
  · intro p hp0
    have hpd : p ∈ d := by rw [hdg]; change g p ≤ 0; exact hp0.le
    have hfp0 : f p = 0 := by rw [← (hgf p hpd).eq_of_nhds]; exact hp0
    exact isSubmersionAt_congr T R hR hf.1 hgmap (hgf p hpd).symm (hf.2.2.2 p hfp0)
  · intro c
    have hgcont : Continuous g := continuous_iff_continuousAt.mpr (fun x => (hgmap x).1)
    apply (hχcompact.union (hρcompact (c - 1))).of_isClosed_subset
      (isClosed_le hgcont continuous_const)
    intro p hp
    by_cases hps : p ∈ sectionSupport χ
    · exact Or.inl hps
    · right
      have hχp : χ p = 0 := Function.notMem_support.mp
        (fun h => hps (subset_closure h))
      change ρ p ≤ c - 1
      have : ρ p + 1 ≤ c := by simpa [g, hχp] using hp
      linarith

/-- The strict signs follow from the full sublevel and zero-set identities.
There is no nonempty-boundary assumption. -/
theorem defining_function_signs (T : SmoothManifold m b M)
    (R : SmoothManifold 1 .euclidean ℝ) (d : Set M) (f : M → ℝ)
    (hf : IsDefiningFunction T R d f) :
    interior d = {x | f x < 0} ∧ ∀ x ∉ d, 0 < f x := by
  have hfcont : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf.1 x).1)
  have hd : IsClosed d := by
    rw [hf.2.1]
    exact isClosed_le hfcont continuous_const
  have hzero (p : M) : p ∈ d \ interior d ↔ f p = 0 := by
    have h : p ∈ frontier d ↔ f p = 0 := by rw [hf.2.2.1]; rfl
    simpa only [frontier, hd.closure_eq] using h
  constructor
  · ext p
    constructor
    · intro hp
      have hpd : p ∈ sublevel f := hf.2.1 ▸ interior_subset hp
      change f p < 0
      apply lt_of_le_of_ne hpd
      intro hp0
      exact ((hzero p).mpr hp0).2 hp
    · intro hp
      change f p < 0 at hp
      by_contra hpi
      have hpd : p ∈ d := by rw [hf.2.1]; exact hp.le
      have hp0 := (hzero p).mp ⟨hpd, hpi⟩
      exact (ne_of_lt hp) hp0
  · intro p hp
    apply lt_of_not_ge
    intro hpf
    apply hp
    rw [hf.2.1]
    exact hpf

/-- Finish all source conclusions once the ordinary global construction has
been supplied. This lemma does not assert that the remaining premise is proved. -/
theorem assemble_defining_function :
    Specs.SmoothManifolds.Ch03.DomainDefiningFunctions.assemble_defining_functionType.{u} := by
  intro m a b M _ T R d S hT hR hd hex
  classical
  obtain ⟨f, hf⟩ := hex
  have hchoice : ∃ g : M → ℝ, IsDefiningFunction T R d g ∧
      (IsCompact d → ∀ c : ℝ, IsCompact {x | g x ≤ c}) := by
    by_cases hdc : IsCompact d
    · obtain ⟨g, hg, _, hgc⟩ := compactify_defining_function T R d f hR hdc hf
      exact ⟨g, hg, fun _ => hgc⟩
    · exact ⟨f, hf, fun h => (hdc h).elim⟩
  obtain ⟨g, hg, hgc⟩ := hchoice
  have htop := RegularDomains.regular_domain_inclusion_topology
    RegularDomains.regular_domain_topology T d S hT hd
  obtain ⟨hgi, hgpos⟩ := defining_function_signs T R d g hg
  exact ⟨g, hg, htop.1.trans hgi, htop.2.trans hg.2.2.1, hgi, hgpos, hgc⟩

/-- Extending a weighted local function by its zero weight is smooth because
subordination controls the closed support, not only the nonzero locus. -/
theorem scalarSmooth_mul_of_support_subset (T : SmoothManifold m b M)
    (U : Set M) (w f : M → ℝ)
    (hw : ScalarSmooth T.smoothStructure.val w)
    (hf : ∀ p ∈ U, ScalarContDiffAt ⊤ T.smoothStructure.val f p)
    (hs : sectionSupport w ⊆ U) :
    ScalarSmooth T.smoothStructure.val (fun p => w p * f p) := by
  intro p
  by_cases hp : p ∈ U
  · exact ScalarContDiffAt.mul (hw p) (hf p hp)
  · have hps : p ∉ sectionSupport w := fun h => hp (hs h)
    apply ScalarContDiffAt.congr (ScalarContDiffAt.const _ _ 0 p)
    filter_upwards [isClosed_closure.compl_mem_nhds hps] with q hq
    have hwq : w q = 0 := Function.notMem_support.mp (fun h => hq (subset_closure h))
    simp [hwq]

/-- Smoothness of the actual locally finite weighted sum of local functions. -/
theorem scalarSmooth_weighted_finsum (T : SmoothManifold m b M)
    {ι : Type v} (U : ι → Set M) (w f : ι → M → ℝ)
    (hw : IsSmoothPartition T.smoothStructure.val w)
    (hf : ∀ i p, p ∈ U i → ScalarContDiffAt ⊤ T.smoothStructure.val (f i) p)
    (hs : IsSubordinate U w) :
    ScalarSmooth T.smoothStructure.val (fun p => ∑ᶠ i, w i p * f i p) := by
  have hsupport (i : ι) : sectionSupport (fun p => w i p * f i p) ⊆
      sectionSupport (w i) := by
    apply closure_mono
    intro p hp
    exact left_ne_zero_of_mul hp
  exact scalarContDiff_finsum
    (fun i => scalarSmooth_mul_of_support_subset T (U i) (w i) (f i) (hw.1 i) (hf i) (hs i))
    (hw.2.2.1.subset hsupport)

/-- Empty frontier includes the empty domain, the entire manifold, and arbitrary
unions of connected components. Regularity is vacuous because the zero fiber
is empty. -/
theorem exists_defining_function_of_frontier_empty (T : SmoothManifold m b M)
    (R : SmoothManifold 1 .euclidean ℝ) (hR : HasStandardRealChart R)
    (d : Set M) (hd : frontier d = ∅) :
    ∃ f : M → ℝ, IsDefiningFunction T R d f := by
  classical
  have hdc : IsClopen d := isClopen_iff_frontier_eq_empty.mpr hd
  let f : M → ℝ := fun p => if p ∈ d then -1 else 1
  have hfs : ScalarSmooth T.smoothStructure.val f := by
    intro p
    by_cases hp : p ∈ d
    · apply ScalarContDiffAt.congr (ScalarContDiffAt.const _ _ (-1) p)
      filter_upwards [hdc.isOpen.mem_nhds hp] with q hq
      simp [f, hq]
    · apply ScalarContDiffAt.congr (ScalarContDiffAt.const _ _ 1 p)
      filter_upwards [hdc.isClosed.isOpen_compl.mem_nhds hp] with q hq
      change q ∉ d at hq
      simp [f, hq]
  have hzero : f ⁻¹' {0} = ∅ := by
    ext p
    simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
    dsimp [f]
    split_ifs <;> norm_num
  refine ⟨f, (scalarSmooth_iff T R hR f).mp hfs, ?_, hd.trans hzero.symm,
    RegularDomains.regular_value_empty_zero T R f hzero⟩
  ext p
  change p ∈ d ↔ (if p ∈ d then (-1 : ℝ) else 1) ≤ 0
  split_ifs <;> simp_all

/-- The noncancellation calculation at a boundary point. Evaluation of every
local defining function is zero, so derivatives of the weights disappear.
Strict negativity is tested on one common derivation. -/
theorem derivation_weighted_sum_neg {B : Type*} [CommRing B] [Algebra ℝ B]
    (ε : B →ₐ[ℝ] ℝ) (D : TangentData.pointDerivations ε)
    {ι : Type*} (s : Finset ι) (w h : ι → B)
    (hz : ∀ i ∈ s, ε (h i) = 0)
    (hw : ∀ i ∈ s, 0 ≤ ε (w i))
    (hD : ∀ i ∈ s, D.val (h i) < 0)
    (hpos : ∃ i ∈ s, 0 < ε (w i)) :
    D.val (∑ i ∈ s, w i * h i) < 0 := by
  classical
  have heq : D.val (∑ i ∈ s, w i * h i) =
      ∑ i ∈ s, ε (w i) * D.val (h i) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [D.property, hz i hi, zero_mul, add_zero]
  rw [heq]
  obtain ⟨i, hi, hwi⟩ := hpos
  exact Finset.sum_neg' (fun j hj =>
    mul_nonpos_of_nonneg_of_nonpos (hw j hj) (hD j hj).le)
    ⟨i, hi, mul_neg_of_pos_of_neg hwi (hD i hi)⟩

/-- The germ of an actual scalar function smooth at the specified point. -/
def scalarGerm (T : SmoothManifold m b M) (p : M) (f : M → ℝ)
    (hf : ScalarContDiffAt ⊤ T.smoothStructure.val f p) : TangentData.SmoothGerm T p :=
  ⟨Germ.ofFun f, (mem_smoothGermAlgebra_iff T p _).mpr ⟨f, hf, rfl⟩⟩

/-- A nonzero action on the scalar germ proves surjectivity of the actual
full tangent differential to the standard real line. -/
theorem isSubmersionAt_of_derivation (T : SmoothManifold m b M)
    (R : SmoothManifold 1 .euclidean ℝ) (hR : HasStandardRealChart R)
    (f : M → ℝ) (hf : IsSmoothMap T R f) (p : M)
    (D : TangentData.TangentSpace T p)
    (hD : D.val (scalarGerm T p f ((scalarSmooth_iff T R hR f).mpr hf p)) ≠ 0) :
    IsSubmersionAt T R f p := by
  classical
  obtain ⟨e, he, hp⟩ := T.smoothStructure.property.1.1 p
  obtain ⟨U, hU, hpU, G, hG, heG⟩ := (hf p).2 e he realChart hR hp (mem_univ _)
  have hdG : HasFDerivAt G (fderiv ℝ G (e p).val) (e p).val :=
    ((hG.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)).hasFDerivAt
  have hderiv : chartDerivative e realChart f p = fderiv ℝ G (e p).val :=
    FiniteRegularity.coordinateDerivative_eq e _ p hp _ ⟨G, hdG, heG⟩
  have hne : fderiv ℝ G (e p).val ≠ 0 := by
    intro hz
    apply hD
    let F : Euclidean m → ℝ := fun z => G z 0
    have hF : TangentData.GermChartExtension T p e
        (scalarGerm T p f ((scalarSmooth_iff T R hR f).mpr hf p)) F := by
      refine ⟨⟨U, hU, hpU, ?_⟩, ?_⟩
      · exact (ContinuousLinearMap.proj (0 : Fin 1) : Euclidean 1 →L[ℝ] ℝ).contDiff.comp_contDiffOn hG
      · exact Germ.coe_eq.mpr (heG.mono (fun y hy => congrFun hy 0))
    rw [derivation_coordinate_formula T p e he hp D _ F hF]
    have hdF : fderiv ℝ F (e p).val =
        (ContinuousLinearMap.proj (0 : Fin 1)).comp (fderiv ℝ G (e p).val) :=
      ((ContinuousLinearMap.proj (0 : Fin 1) : Euclidean 1 →L[ℝ] ℝ).hasFDerivAt.comp _ hdG).fderiv
    simp [hdF, hz]
  have hsurj : Function.Surjective (fderiv ℝ G (e p).val) := by
    have hex : ∃ v : Euclidean m, fderiv ℝ G (e p).val v 0 ≠ 0 := by
      by_contra hn
      apply hne
      ext v i
      rw [Fin.eq_zero i]
      simpa using (not_exists.mp hn v)
    obtain ⟨v, hv⟩ := hex
    intro y
    refine ⟨(y 0 / fderiv ℝ G (e p).val v 0) • v, ?_⟩
    ext i
    rw [Fin.eq_zero i]
    simp [div_mul_cancel₀ _ hv]
  apply (MapClasses.chart_invariants T R f
    (manifoldContDiff_of_le ⊤ 1 _ _ f le_top hf) p e realChart he hR hp (mem_univ _)).2.2.mpr
  rwa [hderiv]

/-- One finite set simultaneously represents the partition and its weighted
local sum on a neighborhood. This retains terms whose value vanishes at the
base point but whose derivative need not vanish. -/
theorem locallyFinite_eventuallyEq_weighted_finsum {ι : Type v}
    (w f : ι → M → ℝ) (hw : LocallyFinite (fun i => sectionSupport (w i))) (p : M) :
    ∃ s : Finset ι,
      (fun y => ∑ᶠ i, w i y) =ᶠ[𝓝 p] (fun y => ∑ i ∈ s, w i y) ∧
      (fun y => ∑ᶠ i, w i y * f i y) =ᶠ[𝓝 p]
        (fun y => ∑ i ∈ s, w i y * f i y) := by
  classical
  obtain ⟨V, hV, hfin⟩ := hw p
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · filter_upwards [hV] with y hy
    apply finsum_eq_sum_of_support_subset
    intro i hi
    exact hfin.mem_toFinset.mpr ⟨y, subset_closure hi, hy⟩
  · filter_upwards [hV] with y hy
    apply finsum_eq_sum_of_support_subset
    intro i hi
    exact hfin.mem_toFinset.mpr ⟨y, subset_closure (left_ne_zero_of_mul hi), hy⟩

/-- A signed local cover patches to an actual regular defining function.
The normal-direction premise is local geometric data, to be constructed from
the regular-domain embedding; it is not a premise of global existence. -/
theorem patch_signed_cover (T : SmoothManifold m b M)
    (R : SmoothManifold 1 .euclidean ℝ) (hR : HasStandardRealChart R)
    (d : Set M) (hd : IsClosed d) {ι : Type v} (U : ι → Set M) (f : ι → M → ℝ)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ p, ∃ i, p ∈ U i)
    (hf : ∀ i p, p ∈ U i → ScalarContDiffAt ⊤ T.smoothStructure.val (f i) p)
    (hneg : ∀ i p, p ∈ U i → p ∈ interior d → f i p < 0)
    (hzero : ∀ i p, p ∈ U i → p ∈ frontier d → f i p = 0)
    (hpos : ∀ i p, p ∈ U i → p ∉ d → 0 < f i p)
    (hnormal : ∀ p ∈ frontier d, ∃ D : TangentData.TangentSpace T p,
      ∀ i (hi : p ∈ U i), D.val (scalarGerm T p (f i) (hf i p hi)) < 0) :
    ∃ g : M → ℝ, IsDefiningFunction T R d g := by
  classical
  obtain ⟨w, hw, hsub⟩ := exists_smooth_partition T U hU hcover
  let g : M → ℝ := fun p => ∑ᶠ i, w i p * f i p
  have hgs := scalarSmooth_weighted_finsum T U w f hw hf hsub
  have hgm : IsSmoothMap T R g := (scalarSmooth_iff T R hR g).mp hgs
  have hactive (p : M) (s : Finset ι) (hs : ∑ i ∈ s, w i p = 1) :
      ∃ i ∈ s, 0 < w i p := by
    by_contra hn
    have hz : ∀ i ∈ s, w i p = 0 := by
      intro i hi
      exact le_antisymm (le_of_not_gt (fun h => hn ⟨i, hi, h⟩)) (hw.2.1 i p)
    have : (0 : ℝ) = 1 := (Finset.sum_eq_zero hz).symm.trans hs
    exact zero_ne_one this
  have hgp (p : M) :
      (p ∈ interior d → g p < 0) ∧ (p ∈ frontier d → g p = 0) ∧
        (p ∉ d → 0 < g p) := by
    obtain ⟨s, hws, hfs⟩ := locallyFinite_eventuallyEq_weighted_finsum w f hw.2.2.1 p
    have hsum : ∑ i ∈ s, w i p = 1 := hws.eq_of_nhds.symm.trans (hw.2.2.2 p)
    obtain ⟨i, hi, hwi⟩ := hactive p s hsum
    have hUi : p ∈ U i := hsub i (subset_closure (ne_of_gt hwi))
    have hterm (j : ι) (hjp : p ∉ U j) : w j p = 0 := by
      by_contra hj
      exact hjp (hsub j (subset_closure hj))
    change ((p ∈ interior d → _) ∧ (p ∈ frontier d → _) ∧ (p ∉ d → _))
    rw [show g p = ∑ j ∈ s, w j p * f j p from hfs.eq_of_nhds]
    refine ⟨?_, ?_, ?_⟩
    · intro hp
      apply Finset.sum_neg'
      · intro j hj
        by_cases hjp : p ∈ U j
        · exact mul_nonpos_of_nonneg_of_nonpos (hw.2.1 j p) (hneg j p hjp hp).le
        · simp [hterm j hjp]
      · exact ⟨i, hi, mul_neg_of_pos_of_neg hwi (hneg i p hUi hp)⟩
    · intro hp
      apply Finset.sum_eq_zero
      intro j hj
      by_cases hjp : p ∈ U j
      · rw [hzero j p hjp hp, mul_zero]
      · rw [hterm j hjp, zero_mul]
    · intro hp
      apply Finset.sum_pos'
      · intro j hj
        by_cases hjp : p ∈ U j
        · exact mul_nonneg (hw.2.1 j p) (hpos j p hjp hp).le
        · simp [hterm j hjp]
      · exact ⟨i, hi, mul_pos hwi (hpos i p hUi hp)⟩
  have hpartition (p : M) (hp : p ∈ d) : p ∈ interior d ∨ p ∈ frontier d := by
    by_cases hi : p ∈ interior d
    · exact Or.inl hi
    · exact Or.inr ⟨subset_closure hp, hi⟩
  have hdg : d = sublevel g := by
    ext p
    constructor
    · intro hp
      rcases hpartition p hp with hi | hb
      · exact (hgp p).1 hi |>.le
      · exact (hgp p).2.1 hb |>.le
    · intro hp
      by_contra hpd
      exact (not_lt_of_ge hp) ((hgp p).2.2 hpd)
  have hzg : frontier d = g ⁻¹' {0} := by
    ext p
    constructor
    · exact (hgp p).2.1
    · intro hp
      have hp0 : g p = 0 := hp
      have hpd : p ∈ d := by rw [hdg]; exact hp0.le
      rcases hpartition p hpd with hi | hb
      · exact ((ne_of_lt ((hgp p).1 hi)) hp0).elim
      · exact hb
  refine ⟨g, hgm, hdg, hzg, ?_⟩
  intro p hp0
  have hpb : p ∈ frontier d := hzg.symm ▸ (show p ∈ g ⁻¹' {0} from hp0)
  obtain ⟨D, hD⟩ := hnormal p hpb
  obtain ⟨s, hws, hfs⟩ := locallyFinite_eventuallyEq_weighted_finsum w f hw.2.2.1 p
  let W (i : ι) := scalarGerm T p (w i) (hw.1 i p)
  let H (i : ι) := scalarGerm T p (fun q => w i q * f i q)
    (scalarSmooth_mul_of_support_subset T (U i) (w i) (f i) (hw.1 i) (hf i) (hsub i) p)
  have hG : scalarGerm T p g (hgs p) = ∑ i ∈ s, H i := by
    apply Subtype.ext
    change Germ.ofFun g = (TangentData.smoothGermAlgebra T p).val (∑ i ∈ s, H i)
    rw [map_sum]
    change Germ.ofFun g = ∑ i ∈ s, (Germ.coeRingHom (𝓝 p)) (fun q => w i q * f i q)
    rw [← map_sum]
    apply Germ.coe_eq.mpr
    filter_upwards [hfs] with q hq
    simpa using hq
  have hHi (i : ι) (hi : p ∈ U i) :
      D.val (H i) = w i p * D.val (scalarGerm T p (f i) (hf i p hi)) := by
    have heq : H i = W i * scalarGerm T p (f i) (hf i p hi) := rfl
    rw [heq, D.property]
    change _ = w i p * _
    change w i p * D.val (scalarGerm T p (f i) (hf i p hi)) +
      f i p * D.val (W i) = _
    rw [hzero i p hi hpb, zero_mul, add_zero]
  have hHz (i : ι) (hi : p ∉ U i) : H i = 0 := by
    apply Subtype.ext
    change Germ.ofFun (fun q => w i q * f i q) = Germ.ofFun (fun _ => 0)
    apply Germ.coe_eq.mpr
    filter_upwards [isClosed_closure.compl_mem_nhds
      (show p ∉ sectionSupport (w i) from fun h => hi (hsub i h))] with q hq
    have hwq : w i q = 0 := Function.notMem_support.mp (fun h => hq (subset_closure h))
    simp [hwq]
  have hsum : ∑ i ∈ s, w i p = 1 := hws.eq_of_nhds.symm.trans (hw.2.2.2 p)
  obtain ⟨i, hi, hwi⟩ := hactive p s hsum
  have hUi : p ∈ U i := hsub i (subset_closure (ne_of_gt hwi))
  have hDG : D.val (scalarGerm T p g (hgs p)) < 0 := by
    rw [hG, map_sum]
    apply Finset.sum_neg'
    · intro j hj
      by_cases hjU : p ∈ U j
      · rw [hHi j hjU]
        exact mul_nonpos_of_nonneg_of_nonpos (hw.2.1 j p) (hD j hjU).le
      · rw [hHz j hjU, map_zero]
    · exact ⟨i, hi, by rw [hHi i hUi]; exact mul_neg_of_pos_of_neg hwi (hD i hUi)⟩
  exact isSubmersionAt_of_derivation T R hR g hgm p D (ne_of_lt hDG)

/-- A local ambient half-space chart together with its original domain chart.
Keeping the latter makes the common normal direction an upstream chart
transition calculation. -/
structure DomainBoundaryChart {n : ℕ} {b : ModelKind} {M : Type u}
    [TopologicalSpace M] (T : SmoothManifold (n + 1) b M) (d : Set M)
    (S : SmoothManifold (n + 1) .halfSpace d) where
  ambient : ModelChart (n + 1) .euclidean M
  domain : ModelChart (n + 1) .halfSpace d
  compatible : SliceData.CompatibleChart T ambient
  mem_atlas : domain ∈ S.smoothStructure.val
  membership : ∀ x ∈ ambient.source, x ∈ d ↔ 0 ≤ (ambient x).val (Fin.last n)
  coordinates : ∀ x : d, x.val ∈ ambient.source →
    x ∈ domain.source ∧ (ambient x.val).val = (domain x).val

/-- The embedding normal form can be shrunk without losing the original
source coordinates or allowing other pieces of the embedded domain. -/
theorem exists_domainBoundaryChart {n : ℕ} {b : ModelKind} {M : Type u}
    [TopologicalSpace M] (T : SmoothManifold (n + 1) b M) (d : Set M)
    (S : SmoothManifold (n + 1) .halfSpace d)
    (hT : intrinsicBoundary T = ∅) (hd : IsRegularDomain T d S)
    (p : d) (hp : p ∈ intrinsicBoundary S) :
    ∃ C : DomainBoundaryChart T d S, p.val ∈ C.ambient.source := by
  obtain ⟨_, e, he, hpe, c, hc, hpc, V, hV, hpV, hVe, hform⟩ :=
    SliceStructures.immersion_coordinates S T Subtype.val hd.2.1 p
      (hd.2.2.2.1 p) (SliceStructures.interior_of_boundary_empty T hT p.val)
  let e' := e.restrOpen V hV
  have hpe' : p ∈ e'.source := ⟨hpe, hpV⟩
  obtain ⟨A, hA, hpA, hslice⟩ := SliceStructures.localize_embedding_slice Subtype.val
    (SliceStructures.isEmbedding_of_range_homeomorph hd.2.2.2.2) e' c p hpe'
    le_rfl (fun _ => Nat.succ_pos _)
    (fun x hx => (hform x hx.2).1) (fun x hx => (hform x hx.2).2)
  obtain ⟨W, hW, hpre, _⟩ := SliceStructures.embedding_open_cut
    (SliceStructures.isEmbedding_of_range_homeomorph hd.2.2.2.2) hV
  let c' := (c.restrOpen A hA).restrOpen W hW
  have hpW : p.val ∈ W := by change p ∈ Subtype.val ⁻¹' W; rwa [hpre]
  refine ⟨⟨c', e,
    SliceStructures.compatibleChart_restrOpen T _
      (SliceStructures.compatibleChart_restrOpen T c hc A hA) W hW,
    he, ?_, ?_⟩, ⟨hpA, hpW⟩⟩
  · intro x hx
    have hmem := RegularDomains.mem_iff_slice hslice hx.1
    rw [Subtype.range_coe, SliceStructures.coordinateSlice_full] at hmem
    exact hmem
  · intro x hx
    have hxV : x ∈ V := by rw [← hpre]; exact hx.2
    exact ⟨hVe hxV, (hform x hxV).2.trans (SliceStructures.sliceEmbedding_self _ _)⟩

/-- Coordinates of a compatible ambient chart are smooth on its source. -/
theorem scalarContDiffAt_compatible_coordinate {n : ℕ} {b : ModelKind} {M : Type u}
    [TopologicalSpace M] (T : SmoothManifold n b M)
    (c : ModelChart n .euclidean M) (hc : SliceData.CompatibleChart T c)
    (i : Fin n) (p : M) (hp : p ∈ c.source) :
    ScalarContDiffAt ⊤ T.smoothStructure.val (fun x => -(c x).val i) p := by
  obtain ⟨e, he, hpe⟩ := T.smoothStructure.property.1.1 p
  obtain ⟨U, hU, hpU, F, hF, heF⟩ := (hc e he p hp hpe).2
  apply scalarContDiffAt_of_chart T.smoothStructure.property.1 he hpe
  refine ⟨U, hU, hpU, fun z => -F z i, ?_, ?_⟩
  · exact ((ContinuousLinearMap.proj i : Euclidean n →L[ℝ] ℝ).contDiff.comp_contDiffOn hF).neg
  · exact heF.mono (fun x hx => congrArg Neg.neg (congrFun hx i))

/-- Signs in each local boundary chart follow from the original domain
boundary/interior comparison, not from a chosen orientation certificate. -/
theorem domainBoundaryChart_signs {n : ℕ} {b : ModelKind} {M : Type u}
    [TopologicalSpace M] (T : SmoothManifold (n + 1) b M) (d : Set M)
    (S : SmoothManifold (n + 1) .halfSpace d)
    (hT : intrinsicBoundary T = ∅) (hd : IsRegularDomain T d S)
    (C : DomainBoundaryChart T d S) (p : M) (hp : p ∈ C.ambient.source) :
    (p ∈ interior d → -(C.ambient p).val (Fin.last n) < 0) ∧
    (p ∈ frontier d → -(C.ambient p).val (Fin.last n) = 0) ∧
    (p ∉ d → 0 < -(C.ambient p).val (Fin.last n)) := by
  have htop := RegularDomains.regular_domain_inclusion_topology
    RegularDomains.regular_domain_topology T d S hT hd
  refine ⟨?_, ?_, ?_⟩
  · intro hpi
    have hpd : p ∈ d := interior_subset hpi
    let q : d := ⟨p, hpd⟩
    obtain ⟨hqe, heq⟩ := C.coordinates q hp
    have hqb : q ∉ intrinsicBoundary S := by
      have hqi : q ∈ manifoldInterior S := by
        have him : p ∈ Subtype.val '' manifoldInterior S := htop.1.symm ▸ hpi
        obtain ⟨r, hr, hrp⟩ := him
        have hrq : r = q := Subtype.ext hrp
        exact hrq ▸ hr
      rwa [← mem_compl_iff, compl_intrinsicBoundary]
    have hne : (C.domain q).val (Fin.last n) ≠ 0 := by
      intro hz
      exact hqb ((intrinsicBoundary_iff_chart S C.domain C.mem_atlas q hqe).mpr hz)
    rw [heq]
    exact neg_neg_of_pos (lt_of_le_of_ne (C.domain q).property (Ne.symm hne))
  · intro hpb
    have him : p ∈ Subtype.val '' intrinsicBoundary S := htop.2.symm ▸ hpb
    obtain ⟨q, hq, rfl⟩ := him
    obtain ⟨hqe, heq⟩ := C.coordinates q hp
    rw [heq, (intrinsicBoundary_iff_chart S C.domain C.mem_atlas q hqe).mp hq, neg_zero]
  · intro hpd
    exact neg_pos.mpr (lt_of_not_ge (fun h => hpd ((C.membership p hp).mpr h)))

/-- Every local negative boundary coordinate has negative derivative on the
pushforward of one fixed intrinsic inward vector. -/
theorem domainBoundaryChart_common_normal {n : ℕ} {b : ModelKind} {M : Type u}
    [TopologicalSpace M] (T : SmoothManifold (n + 1) b M) (d : Set M)
    (S : SmoothManifold (n + 1) .halfSpace d)
    (hT : intrinsicBoundary T = ∅) (hd : IsRegularDomain T d S)
    (p : M) (hp : p ∈ frontier d) :
    ∃ D : TangentData.TangentSpace T p, ∀ C : DomainBoundaryChart T d S,
      ∀ hpc : p ∈ C.ambient.source,
        D.val (scalarGerm T p (fun x => -(C.ambient x).val (Fin.last n))
          (scalarContDiffAt_compatible_coordinate T C.ambient C.compatible _ p hpc)) < 0 := by
  classical
  have htop := RegularDomains.regular_domain_inclusion_topology
    RegularDomains.regular_domain_topology T d S hT hd
  have him : p ∈ Subtype.val '' intrinsicBoundary S := htop.2.symm ▸ hp
  obtain ⟨q, hq, rfl⟩ := him
  obtain ⟨e, he, hqe⟩ := S.smoothStructure.property.1.1 q
  let E := coordinateDerivationEquiv S q e he hqe
  let v := E.symm (Pi.single (Fin.last n) 1)
  let L := differential S T Subtype.val hd.2.1 q
  refine ⟨L v, ?_⟩
  intro C hpc
  obtain ⟨hqc, heq⟩ := C.coordinates q hpc
  let F := coordinateDerivationEquiv S q C.domain C.mem_atlas hqc
  obtain ⟨r, hr, hscale⟩ := boundary_transition_positive S ⟨q, hq⟩ e C.domain
    he C.mem_atlas hqe hqc E F
    (coordinateDerivationEquiv_isChartCoordinates S q e he hqe)
    (coordinateDerivationEquiv_isChartCoordinates S q C.domain C.mem_atlas hqc)
  let k := -coordinateGerm S q C.domain C.mem_atlas hqc (Fin.last n)
  have hrep : Germ.ofFun ((fun x => -(C.ambient x).val (Fin.last n)) ∘ Subtype.val) = k.val := by
    change Germ.ofFun (fun x : d => -(C.ambient x.val).val (Fin.last n)) =
      Germ.ofFun (fun x : d => -(C.domain x).val (Fin.last n))
    apply Germ.coe_eq.mpr
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
      (C.ambient.open_source.mem_nhds hpc)] with x hx
    exact congrArg (fun z : Euclidean (n + 1) => -z (Fin.last n)) (C.coordinates x hx).2
  have haction := differential_spec S T Subtype.val hd.2.1 q v
    (scalarGerm T q.val (fun x => -(C.ambient x).val (Fin.last n))
      (scalarContDiffAt_compatible_coordinate T C.ambient C.compatible _ q.val hpc)) k
    (fun x => -(C.ambient x).val (Fin.last n)) rfl hrep
  rw [haction]
  change v.val (-coordinateGerm S q C.domain C.mem_atlas hqc (Fin.last n)) < 0
  rw [map_neg]
  change -F v (Fin.last n) < 0
  rw [hscale v]
  have hv : E v (Fin.last n) = 1 := by simp [v]
  rw [hv, mul_one]
  exact neg_neg_of_pos hr

/-- Ordinary global construction in the only case with a possible boundary.
The cover consists of boundary coordinates and the two constant sign regions. -/
theorem exists_defining_function_halfSpace {n : ℕ} {b : ModelKind} {M : Type u}
    [TopologicalSpace M] (T : SmoothManifold (n + 1) b M)
    (R : SmoothManifold 1 .euclidean ℝ) (d : Set M)
    (S : SmoothManifold (n + 1) .halfSpace d)
    (hT : intrinsicBoundary T = ∅) (hR : HasStandardRealChart R)
    (hd : IsRegularDomain T d S) : ∃ g : M → ℝ, IsDefiningFunction T R d g := by
  classical
  let ι := DomainBoundaryChart T d S ⊕ Bool
  let U : ι → Set M
    | .inl C => C.ambient.source
    | .inr false => interior d
    | .inr true => dᶜ
  let f : ι → M → ℝ
    | .inl C => fun x => -(C.ambient x).val (Fin.last n)
    | .inr false => fun _ => -1
    | .inr true => fun _ => 1
  have hU : ∀ i, IsOpen (U i) := by
    intro i
    cases i with
    | inl C => exact C.ambient.open_source
    | inr j => cases j; exact isOpen_interior; exact hd.1.isOpen_compl
  have hcover : ∀ p, ∃ i, p ∈ U i := by
    intro p
    by_cases hpi : p ∈ interior d
    · exact ⟨.inr false, hpi⟩
    by_cases hpd : p ∈ d
    · have hpb : p ∈ frontier d := ⟨subset_closure hpd, hpi⟩
      have htop := RegularDomains.regular_domain_inclusion_topology
        RegularDomains.regular_domain_topology T d S hT hd
      have him : p ∈ Subtype.val '' intrinsicBoundary S := htop.2.symm ▸ hpb
      obtain ⟨q, hq, rfl⟩ := him
      obtain ⟨C, hC⟩ := exists_domainBoundaryChart T d S hT hd q hq
      exact ⟨.inl C, hC⟩
    · exact ⟨.inr true, hpd⟩
  have hf : ∀ i p, p ∈ U i → ScalarContDiffAt ⊤ T.smoothStructure.val (f i) p := by
    intro i p hp
    cases i with
    | inl C => exact scalarContDiffAt_compatible_coordinate T C.ambient C.compatible _ p hp
    | inr j => cases j <;> exact ScalarContDiffAt.const _ _ _ _
  have hsigns : ∀ i p, p ∈ U i →
      (p ∈ interior d → f i p < 0) ∧
      (p ∈ frontier d → f i p = 0) ∧ (p ∉ d → 0 < f i p) := by
    intro i p hp
    cases i with
    | inl C => exact domainBoundaryChart_signs T d S hT hd C p hp
    | inr j =>
      cases j with
      | false =>
        change p ∈ interior d at hp
        exact ⟨fun _ => by norm_num [f], fun hb => (hb.2 hp).elim,
          fun hout => (hout (interior_subset hp)).elim⟩
      | true =>
        change p ∉ d at hp
        exact ⟨fun hi => (hp (interior_subset hi)).elim,
          fun hb => (hp (hd.1.closure_eq ▸ hb.1)).elim, fun _ => by norm_num [f]⟩
  apply patch_signed_cover T R hR d hd.1 U f hU hcover hf
    (fun i p hp => (hsigns i p hp).1)
    (fun i p hp => (hsigns i p hp).2.1)
    (fun i p hp => (hsigns i p hp).2.2)
  intro p hp
  obtain ⟨D, hD⟩ := domainBoundaryChart_common_normal T d S hT hd p hp
  refine ⟨D, ?_⟩
  intro i hi
  cases i with
  | inl C => exact hD C hi
  | inr j =>
    cases j with
    | false => exact (hp.2 hi).elim
    | true => exact (hi (hd.1.closure_eq ▸ hp.1)).elim

/-- Every regular domain has a global defining function, with the compact
strengthening and both intrinsic/ambient comparisons in the original scope. -/
theorem exists_defining_function :
    Specs.SmoothManifolds.Ch03.DomainDefiningFunctions.exists_defining_functionType.{u} := by
  intro m a b M _ T R d S hT hR hd
  apply assemble_defining_function T R d S hT hR hd
  have htop := RegularDomains.regular_domain_inclusion_topology
    RegularDomains.regular_domain_topology T d S hT hd
  cases a with
  | euclidean =>
    apply exists_defining_function_of_frontier_empty T R hR d
    rw [← htop.2, intrinsicBoundary_euclidean S, image_empty]
  | halfSpace =>
    cases m with
    | zero =>
      apply exists_defining_function_of_frontier_empty T R hR d
      rw [← htop.2, intrinsicBoundary_zero S, image_empty]
    | succ n => exact exists_defining_function_halfSpace T R d S hT hR hd

end SmoothManifolds.DomainDefiningFunctions
