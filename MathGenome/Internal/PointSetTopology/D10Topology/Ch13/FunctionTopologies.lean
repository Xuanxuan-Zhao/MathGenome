import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.FunctionTopologies
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Order.Filter.Bases.Finite
import Mathlib.Tactic.Linarith

noncomputable section
open Set Filter
open scoped Topology Uniformity
universe u v
namespace D10Topology.Ch13

abbrev AllMaps := @Specs.D10Topology.Ch13.FunctionTopologies.AllMaps
abbrev ContinuousMaps := @Specs.D10Topology.Ch13.FunctionTopologies.ContinuousMaps
abbrev pointwiseTopology := @Specs.D10Topology.Ch13.FunctionTopologies.pointwiseTopology
abbrev compactOpenSet := @Specs.D10Topology.Ch13.FunctionTopologies.compactOpenSet
abbrev compactOpenTopology := @Specs.D10Topology.Ch13.FunctionTopologies.compactOpenTopology
abbrev pointwiseContinuousTopology := @Specs.D10Topology.Ch13.FunctionTopologies.pointwiseContinuousTopology
abbrev compactOpenContinuousTopology := @Specs.D10Topology.Ch13.FunctionTopologies.compactOpenContinuousTopology
abbrev boundedDistance := @Specs.D10Topology.Ch13.FunctionTopologies.boundedDistance
abbrev uniformDistance := @Specs.D10Topology.Ch13.FunctionTopologies.uniformDistance
abbrev compactDistance := @Specs.D10Topology.Ch13.FunctionTopologies.compactDistance
abbrev compactBall := @Specs.D10Topology.Ch13.FunctionTopologies.compactBall
abbrev uniformUniformity := @Specs.D10Topology.Ch13.FunctionTopologies.uniformUniformity
abbrev uniformTopology := @Specs.D10Topology.Ch13.FunctionTopologies.uniformTopology
abbrev compactConvergenceUniformity := @Specs.D10Topology.Ch13.FunctionTopologies.compactConvergenceUniformity
abbrev compactConvergenceTopology := @Specs.D10Topology.Ch13.FunctionTopologies.compactConvergenceTopology
abbrev uniformContinuousTopology := @Specs.D10Topology.Ch13.FunctionTopologies.uniformContinuousTopology
abbrev compactConvergenceContinuousUniformity := @Specs.D10Topology.Ch13.FunctionTopologies.compactConvergenceContinuousUniformity
abbrev compactConvergenceContinuousTopology := @Specs.D10Topology.Ch13.FunctionTopologies.compactConvergenceContinuousTopology
abbrev EquicontinuousAt := @Specs.D10Topology.Ch13.FunctionTopologies.EquicontinuousAt
abbrev Equicontinuous := @Specs.D10Topology.Ch13.FunctionTopologies.Equicontinuous
abbrev PointwiseRelativelyCompact := @Specs.D10Topology.Ch13.FunctionTopologies.PointwiseRelativelyCompact

variable {X : Type u} {Y : Type v}

section Distances
variable [MetricSpace Y]

theorem boundedDistance_nonneg (y z : Y) : 0 ≤ boundedDistance y z :=
  le_min zero_le_one dist_nonneg

theorem boundedDistance_le_one (y z : Y) : boundedDistance y z ≤ 1 := min_le_left _ _

theorem boundedDistance_self (y : Y) : boundedDistance y y = 0 := by
  simp [boundedDistance, Specs.D10Topology.Ch13.FunctionTopologies.boundedDistance]

theorem boundedDistance_comm (y z : Y) : boundedDistance y z = boundedDistance z y := by
  simp only [boundedDistance, Specs.D10Topology.Ch13.FunctionTopologies.boundedDistance, dist_comm]

theorem boundedDistance_triangle (x y z : Y) :
    boundedDistance x z ≤ boundedDistance x y + boundedDistance y z := by
  dsimp [boundedDistance, Specs.D10Topology.Ch13.FunctionTopologies.boundedDistance]
  by_cases h : 1 ≤ dist x y
  · rw [min_eq_left h]
    linarith [min_le_left (1 : ℝ) (dist x z), le_min zero_le_one (dist_nonneg (x := y) (y := z))]
  by_cases h' : 1 ≤ dist y z
  · rw [min_eq_left h']
    linarith [min_le_left (1 : ℝ) (dist x z), le_min zero_le_one (dist_nonneg (x := x) (y := y))]
  rw [min_eq_right (le_of_not_ge h), min_eq_right (le_of_not_ge h')]
  exact (min_le_right _ _).trans (dist_triangle x y z)

theorem boundedDistance_eq_zero (y z : Y) : boundedDistance y z = 0 ↔ y = z := by
  constructor
  · intro h
    by_contra hne
    have hp : 0 < min (1 : ℝ) (dist y z) := lt_min zero_lt_one (dist_pos.mpr hne)
    exact (ne_of_gt hp) h
  · rintro rfl
    exact boundedDistance_self _

theorem uniformDistance_nonneg (f g : X → Y) : 0 ≤ uniformDistance f g :=
  Real.iSup_nonneg fun x => boundedDistance_nonneg _ _

theorem uniformDistance_le_one (f g : X → Y) : uniformDistance f g ≤ 1 :=
  Real.iSup_le (fun x => boundedDistance_le_one _ _) zero_le_one

theorem boundedDistance_le_uniformDistance (f g : X → Y) (x : X) :
    boundedDistance (f x) (g x) ≤ uniformDistance f g :=
  le_ciSup (f := fun x : X => boundedDistance (f x) (g x)) ⟨1, by rintro _ ⟨x, rfl⟩; exact boundedDistance_le_one (f x) (g x)⟩ x

theorem uniformDistance_le (f g : X → Y) (r : ℝ) (hr : 0 ≤ r) :
    uniformDistance f g ≤ r ↔ ∀ x, boundedDistance (f x) (g x) ≤ r :=
  ⟨fun h x => (boundedDistance_le_uniformDistance f g x).trans h,
    fun h => Real.iSup_le h hr⟩

theorem uniformDistance_self (f : X → Y) : uniformDistance f f = 0 :=
  le_antisymm ((uniformDistance_le _ _ 0 le_rfl).mpr fun x => (boundedDistance_self _).le)
    (uniformDistance_nonneg _ _)

theorem uniformDistance_comm (f g : X → Y) : uniformDistance f g = uniformDistance g f := by
  unfold uniformDistance Specs.D10Topology.Ch13.FunctionTopologies.uniformDistance
  congr 1
  funext x
  exact boundedDistance_comm _ _

theorem uniformDistance_triangle (f g h : X → Y) :
    uniformDistance f h ≤ uniformDistance f g + uniformDistance g h := by
  apply (uniformDistance_le _ _ _ (add_nonneg (uniformDistance_nonneg _ _) (uniformDistance_nonneg _ _))).mpr
  intro x
  exact (boundedDistance_triangle _ _ _).trans
    (add_le_add (boundedDistance_le_uniformDistance f g x) (boundedDistance_le_uniformDistance g h x))

theorem uniformDistance_eq_zero (f g : X → Y) : uniformDistance f g = 0 ↔ f = g := by
  constructor
  · intro h
    funext x
    apply (boundedDistance_eq_zero _ _).mp
    exact le_antisymm (h ▸ boundedDistance_le_uniformDistance f g x) (boundedDistance_nonneg _ _)
  · rintro rfl
    exact uniformDistance_self _

/-- The actual finite metric with distance exactly the paper's supremum. -/
@[instance_reducible]
def uniformMetric : MetricSpace (X → Y) where
  dist := uniformDistance
  dist_self := uniformDistance_self
  dist_comm := uniformDistance_comm
  dist_triangle := uniformDistance_triangle
  eq_of_dist_eq_zero := (uniformDistance_eq_zero _ _).mp

/-- Restriction need not be injective, so this is a pseudometric for every K. -/
@[instance_reducible]
def compactPseudometric (K : Set X) : PseudoMetricSpace (X → Y) :=
  PseudoMetricSpace.induced (fun f : X → Y => fun x : K => f x) uniformMetric.toPseudoMetricSpace

theorem uniform_metric_exists : ∃ m : MetricSpace (X → Y), @dist _ m.toDist = uniformDistance :=
  ⟨uniformMetric, rfl⟩

theorem compact_pseudometric_exists (K : Set X) :
    ∃ m : PseudoMetricSpace (X → Y), @dist _ m.toDist = compactDistance K :=
  ⟨compactPseudometric K, rfl⟩

theorem compactDistance_empty (f g : X → Y) : compactDistance ∅ f g = 0 :=
  Real.iSup_of_isEmpty _

theorem uniformDistance_empty [IsEmpty X] (f g : X → Y) : uniformDistance f g = 0 :=
  Real.iSup_of_isEmpty _

end Distances

section TopologicalMaps
variable [TopologicalSpace X] [TopologicalSpace Y]

theorem continuousMaps_representation :
    Function.Bijective (fun f : ContinuousMaps X Y =>
      (⟨(f : X → Y), f.continuous⟩ : {g : X → Y // Continuous g})) := by
  constructor
  · intro f g h
    exact DFunLike.coe_injective (congrArg Subtype.val h)
  · intro f
    exact ⟨⟨f.val, f.property⟩, rfl⟩

theorem compactOpenSet_mem (K : Set X) (O : Set Y) (f : X → Y) :
    f ∈ compactOpenSet K O ↔ ∀ x ∈ K, f x ∈ O :=
  image_subset_iff

theorem compactOpenContinuousTopology_eq_mathlib :
    compactOpenContinuousTopology (X := X) (Y := Y) = ContinuousMap.compactOpen := by
  unfold compactOpenContinuousTopology Specs.D10Topology.Ch13.FunctionTopologies.compactOpenContinuousTopology
    Specs.D10Topology.Ch13.FunctionTopologies.compactOpenTopology
  rw [induced_generateFrom_eq, ContinuousMap.compactOpen_eq]
  congr 1
  ext B
  constructor
  · rintro ⟨U, ⟨K, hK, O, hO, rfl⟩, rfl⟩
    exact ⟨K, hK, O, hO, by ext f; exact image_subset_iff.symm⟩
  · rintro ⟨K, hK, O, hO, rfl⟩
    refine ⟨compactOpenSet K O, ⟨K, hK, O, hO, rfl⟩, ?_⟩
    ext f
    exact image_subset_iff

end TopologicalMaps

section MetricFamilies
variable [TopologicalSpace X] [MetricSpace Y]

theorem equicontinuousAt_iff_mathlib (A : Set (ContinuousMaps X Y)) (x : X) :
    EquicontinuousAt A x ↔ _root_.EquicontinuousAt (fun f : A => (f.val : X → Y)) x := by
  rw [Metric.equicontinuousAt_iff_right]
  constructor
  · intro h ε hε
    obtain ⟨U, hU, h⟩ := h ε hε
    filter_upwards [hU] with y hy f
    simpa only [dist_comm] using h y hy f.val f.property
  · intro h ε hε
    refine ⟨{y | ∀ f : A, dist (f.val x) (f.val y) < ε}, h ε hε, ?_⟩
    intro y hy f hf
    simpa only [dist_comm] using hy ⟨f, hf⟩

theorem equicontinuous_iff_mathlib (A : Set (ContinuousMaps X Y)) :
    Equicontinuous A ↔ _root_.Equicontinuous (fun f : A => (f.val : X → Y)) := by
  exact forall_congr' fun x => equicontinuousAt_iff_mathlib A x

theorem pointwiseRelativelyCompact_iff_range (A : Set (ContinuousMaps X Y)) :
    PointwiseRelativelyCompact A ↔
      ∀ x : X, IsCompact (closure (range (fun f : A => f.val x))) := by
  have h (x : X) : (fun f : ContinuousMaps X Y => f x) '' A = range (fun f : A => f.val x) := by
    ext y
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨⟨f, hf⟩, rfl⟩
    · rintro ⟨f, rfl⟩
      exact ⟨f.val, f.property, rfl⟩
  simp only [PointwiseRelativelyCompact, Specs.D10Topology.Ch13.FunctionTopologies.PointwiseRelativelyCompact, h]

end MetricFamilies

section UniformStructures
variable [MetricSpace Y]

private theorem dist_lt_of_boundedDistance_lt {y z : Y} {ε : ℝ} (hε : ε ≤ 1)
    (h : boundedDistance y z < ε) : dist y z < ε := by
  rcases min_lt_iff.mp h with h | h
  · exact False.elim ((not_lt_of_ge hε) h)
  · exact h

theorem compactDistance_nonneg (K : Set X) (f g : X → Y) : 0 ≤ compactDistance K f g :=
  uniformDistance_nonneg _ _

theorem compactDistance_le_one (K : Set X) (f g : X → Y) : compactDistance K f g ≤ 1 :=
  uniformDistance_le_one _ _

theorem boundedDistance_le_compactDistance (K : Set X) (f g : X → Y) (x : X) (hx : x ∈ K) :
    boundedDistance (f x) (g x) ≤ compactDistance K f g :=
  boundedDistance_le_uniformDistance (fun x : K => f x) (fun x : K => g x) ⟨x, hx⟩

theorem compactDistance_le (K : Set X) (f g : X → Y) (r : ℝ) (hr : 0 ≤ r) :
    compactDistance K f g ≤ r ↔ ∀ x ∈ K, boundedDistance (f x) (g x) ≤ r := by
  change uniformDistance (fun x : K => f x) (fun x : K => g x) ≤ r ↔ _
  rw [uniformDistance_le _ _ _ hr]
  exact ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x x.property⟩

theorem uniformUniformity_hasBasis :
    (@uniformity (X → Y) uniformUniformity).HasBasis (fun ε : ℝ => 0 < ε)
      (fun ε => {p | uniformDistance p.1 p.2 < ε}) := by
  have hb := (UniformFun.hasBasis_uniformity_of_basis X Y Metric.uniformity_basis_dist).comap
    (Prod.map (UniformFun.ofFun : (X → Y) → UniformFun X Y) UniformFun.ofFun)
  change (Filter.comap _ _).HasBasis _ _
  apply hb.to_hasBasis
  · intro ε hε
    refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
    intro p hp x
    exact (dist_lt_of_boundedDistance_lt (min_le_right _ _)
      ((boundedDistance_le_uniformDistance p.1 p.2 x).trans_lt hp)).trans_le (min_le_left _ _)
  · intro ε hε
    refine ⟨ε / 2, half_pos hε, ?_⟩
    intro p hp
    exact lt_of_le_of_lt ((uniformDistance_le _ _ _ (half_pos hε).le).mpr
      fun x => (min_le_right _ _).trans (hp x).le) (half_lt_self hε)

theorem uniformUniformity_eq_metric :
    uniformUniformity (X := X) (Y := Y) = uniformMetric.toUniformSpace := by
  apply UniformSpace.ext
  exact uniformUniformity_hasBasis.eq_of_same_basis
    (@Metric.uniformity_basis_dist (X → Y) uniformMetric.toPseudoMetricSpace)

theorem uniformTopology_eq_metric :
    uniformTopology (X := X) (Y := Y) = uniformMetric.toUniformSpace.toTopologicalSpace :=
  congrArg (fun U : UniformSpace (X → Y) => U.toTopologicalSpace)
    (uniformUniformity_eq_metric (X := X) (Y := Y))

variable [TopologicalSpace X]

theorem compactConvergenceUniformity_hasBasis :
    (@uniformity (X → Y) compactConvergenceUniformity).HasBasis
      (fun Ke : Set X × ℝ => IsCompact Ke.1 ∧ 0 < Ke.2)
      (fun Ke => {p | compactDistance Ke.1 p.1 p.2 < Ke.2}) := by
  have hb := (UniformOnFun.hasBasis_uniformity_of_basis X Y {K : Set X | IsCompact K}
    ⟨∅, isCompact_empty⟩ (fun K hK L hL => ⟨K ∪ L, hK.union hL, subset_union_left, subset_union_right⟩)
    Metric.uniformity_basis_dist).comap
      (Prod.map (UniformOnFun.ofFun {K : Set X | IsCompact K})
        (UniformOnFun.ofFun {K : Set X | IsCompact K}))
  change (Filter.comap _ _).HasBasis _ _
  apply hb.to_hasBasis
  · rintro ⟨K, ε⟩ ⟨hK, hε⟩
    refine ⟨(K, min ε 1), ⟨hK, lt_min hε zero_lt_one⟩, ?_⟩
    intro p hp x hx
    exact (dist_lt_of_boundedDistance_lt (min_le_right _ _)
      ((boundedDistance_le_compactDistance K p.1 p.2 x hx).trans_lt hp)).trans_le (min_le_left _ _)
  · rintro ⟨K, ε⟩ ⟨hK, hε⟩
    refine ⟨(K, ε / 2), ⟨hK, half_pos hε⟩, ?_⟩
    intro p hp
    exact lt_of_le_of_lt ((compactDistance_le K p.1 p.2 _ (half_pos hε).le).mpr
      fun x hx => (min_le_right _ _).trans (hp x hx).le) (half_lt_self hε)

theorem compactConvergence_uniformity_eq :
    @uniformity (X → Y) compactConvergenceUniformity =
      ⨅ (K : Set X) (_ : IsCompact K) (ε : ℝ) (_ : 0 < ε),
        𝓟 {p | compactDistance K p.1 p.2 < ε} := by
  rw [compactConvergenceUniformity_hasBasis.eq_biInf]
  simp only [iInf_prod, iInf_and]
  exact iInf_congr fun K => iInf_comm

theorem compactConvergence_nhds_hasBasis (f : X → Y) :
    (@nhds (X → Y) compactConvergenceTopology f).HasBasis
      (fun Ke : Set X × ℝ => IsCompact Ke.1 ∧ 0 < Ke.2)
      (fun Ke => compactBall Ke.1 f Ke.2) :=
  @nhds_basis_uniformity' (X → Y) _ compactConvergenceUniformity _ _
    compactConvergenceUniformity_hasBasis f

end UniformStructures

section FurtherInterfaces
variable [MetricSpace Y]

theorem uniform_metric_realizes : ∃ m : MetricSpace (X → Y),
    @dist _ m.toDist = uniformDistance ∧ m.toUniformSpace = uniformUniformity :=
  ⟨uniformMetric, rfl, uniformUniformity_eq_metric.symm⟩

theorem uniform_nhds_hasBasis (f : X → Y) :
    (@nhds (X → Y) uniformTopology f).HasBasis (fun ε : ℝ => 0 < ε)
      (fun ε => {g | uniformDistance f g < ε}) :=
  @nhds_basis_uniformity' (X → Y) _ uniformUniformity _ _ uniformUniformity_hasBasis f

variable [TopologicalSpace X]

@[instance_reducible]
def uniformContinuousMetric : MetricSpace (ContinuousMaps X Y) :=
  MetricSpace.induced (fun f : ContinuousMaps X Y => (f : X → Y)) DFunLike.coe_injective uniformMetric

@[instance_reducible]
def compactContinuousPseudometric (K : Set X) : PseudoMetricSpace (ContinuousMaps X Y) :=
  PseudoMetricSpace.induced (fun f : ContinuousMaps X Y => (f : X → Y)) (compactPseudometric K)

theorem uniform_continuous_metric_realizes : ∃ m : MetricSpace (ContinuousMaps X Y),
    (∀ f g, @dist _ m.toDist f g = uniformDistance (f : X → Y) (g : X → Y)) ∧
      m.toUniformSpace.toTopologicalSpace = uniformContinuousTopology := by
  refine ⟨uniformContinuousMetric, fun _ _ => rfl, ?_⟩
  change TopologicalSpace.induced _ uniformMetric.toUniformSpace.toTopologicalSpace =
    TopologicalSpace.induced _ uniformTopology
  rw [uniformTopology_eq_metric]

theorem compact_continuous_pseudometric_exists (K : Set X) :
    ∃ m : PseudoMetricSpace (ContinuousMaps X Y),
      ∀ f g, @dist _ m.toDist f g = compactDistance K (f : X → Y) (g : X → Y) :=
  ⟨compactContinuousPseudometric K, fun _ _ => rfl⟩

theorem compactConvergenceContinuousTopology_eq_induced :
    compactConvergenceContinuousTopology (X := X) (Y := Y) =
      TopologicalSpace.induced (fun f : ContinuousMaps X Y => (f : X → Y)) compactConvergenceTopology := rfl

theorem compactConvergenceContinuous_uniformity_eq :
    @uniformity (ContinuousMaps X Y) compactConvergenceContinuousUniformity =
      ⨅ (K : Set X) (_ : IsCompact K) (ε : ℝ) (_ : 0 < ε),
        𝓟 {p | compactDistance K (p.1 : X → Y) (p.2 : X → Y) < ε} := by
  change comap _ (@uniformity (X → Y) compactConvergenceUniformity) = _
  rw [compactConvergence_uniformity_eq]
  simp only [comap_iInf, comap_principal]
  rfl

theorem compactConvergenceContinuous_nhds_hasBasis (f : ContinuousMaps X Y) :
    (@nhds (ContinuousMaps X Y) compactConvergenceContinuousTopology f).HasBasis
      (fun Ke : Set X × ℝ => IsCompact Ke.1 ∧ 0 < Ke.2)
      (fun Ke => {g | compactDistance Ke.1 (f : X → Y) (g : X → Y) < Ke.2}) := by
  letI : TopologicalSpace (X → Y) := compactConvergenceTopology
  rw [compactConvergenceContinuousTopology_eq_induced, nhds_induced]
  exact (compactConvergence_nhds_hasBasis (f : X → Y)).comap _

private theorem finite_intersections_basis {T : Type*} {I : Type*} {l : Filter T}
    {p : I → Prop} {B : I → Set T} (hb : l.HasBasis p B) (N : Set T) :
    N ∈ l ↔ ∃ F : Finset I, (∀ i ∈ F, p i) ∧ (⋂ i ∈ F, B i) ⊆ N := by
  classical
  constructor
  · intro h
    obtain ⟨i, hi, hiN⟩ := hb.mem_iff.mp h
    refine ⟨{i}, by simpa, ?_⟩
    simpa using hiN
  · rintro ⟨F, hF, hFN⟩
    apply mem_of_superset _ hFN
    exact (biInter_mem F.finite_toSet).mpr fun i hi => hb.mem_of_mem (hF i hi)

theorem compactConvergence_finite_neighborhoods (f : X → Y) (N : Set (X → Y)) :
    N ∈ @nhds (X → Y) compactConvergenceTopology f ↔
      ∃ F : Finset (Set X × ℝ), (∀ Ke ∈ F, IsCompact Ke.1 ∧ 0 < Ke.2) ∧
        (⋂ Ke ∈ F, compactBall Ke.1 f Ke.2) ⊆ N :=
  finite_intersections_basis (compactConvergence_nhds_hasBasis f) N

theorem compactConvergenceContinuous_finite_neighborhoods (f : ContinuousMaps X Y)
    (N : Set (ContinuousMaps X Y)) :
    N ∈ @nhds (ContinuousMaps X Y) compactConvergenceContinuousTopology f ↔
      ∃ F : Finset (Set X × ℝ), (∀ Ke ∈ F, IsCompact Ke.1 ∧ 0 < Ke.2) ∧
        (⋂ Ke ∈ F, {g : ContinuousMaps X Y | compactDistance Ke.1 (f : X → Y) (g : X → Y) < Ke.2}) ⊆ N :=
  finite_intersections_basis (compactConvergenceContinuous_nhds_hasBasis f) N

end FurtherInterfaces

section EmptyCases

theorem empty_function_topology_unique [IsEmpty (X → Y)]
    (t s : TopologicalSpace (X → Y)) : t = s := Subsingleton.elim _ _

theorem empty_domain_unique_map [IsEmpty X] : ∃! f : X → Y, True := by
  exact ⟨fun x => isEmptyElim x, trivial, fun f _ => Subsingleton.elim _ _⟩

theorem empty_domain_unique_continuous_map [TopologicalSpace X] [TopologicalSpace Y]
    [IsEmpty X] : ∃! f : ContinuousMaps X Y, True := by
  refine ⟨⟨fun x => isEmptyElim x, continuous_iff_continuousAt.mpr (fun x => isEmptyElim x)⟩, trivial, ?_⟩
  intro f _
  exact DFunLike.coe_injective (Subsingleton.elim _ _)

end EmptyCases

end D10Topology.Ch13
