import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch10.EvaluationEmbedding
import MathGenome.Internal.PointSetTopology.D10Topology.Ch02.EmbeddingsAndCharacteristicMaps
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.Products
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.CompactImagesAndSeparation

/-! Evaluation embeddings, paper.tex `d10:10:evaluation-embedding` and
`d10:10:compact-point-separation`. The initial-topology and product bridges
are used with their actual open-set meanings. In particular, injectivity
is never inferred from the neighborhood condition without point separation. -/

open Set Topology
universe u v w

namespace D10Topology.Ch10

theorem evaluation_injective_iff {X : Type u} {ι : Type v} {Y : ι → Type w}
    (f : ∀ i, X → Y i) :
    Function.Injective (fun x i => f i x) ↔
      ∀ x y, x ≠ y → ∃ i, f i x ≠ f i y := by
  classical
  constructor
  · intro hi x y hxy
    by_contra h
    apply hxy
    apply hi
    funext i
    exact not_ne_iff.mp (not_exists.mp h i)
  · intro hs x y heq
    by_contra hxy
    obtain ⟨i, hi⟩ := hs x y hxy
    exact hi (congrFun heq i)

theorem evaluation_induced_topology {X : Type u} {ι : Type v} {Y : ι → Type w}
    [tY : ∀ i, TopologicalSpace (Y i)] (f : ∀ i, X → Y i) :
    TopologicalSpace.induced (fun x i => f i x) Pi.topologicalSpace =
      TopologicalSpace.generateFrom
        {U : Set X | ∃ i V, IsOpen V ∧ U = f i ⁻¹' V} := by
  have hinit : Ch03.initialTopology tY f =
      ⨅ i, TopologicalSpace.induced (f i) (tY i) := by
    apply le_antisymm
    · exact le_iInf fun i => continuous_iff_le_induced.mp
        (Ch03.initial_maps_continuous tY f i)
    · exact Ch03.initial_coarsest tY f _
        (fun i => continuous_iff_le_induced.mpr (iInf_le _ i))
  calc
    _ = ⨅ i, TopologicalSpace.induced (f i) (tY i) := by
      simp [Pi.topologicalSpace, induced_iInf, induced_compose, Function.comp_def]
    _ = Ch03.initialTopology tY f := hinit.symm
    _ = _ := rfl

theorem evaluation_continuous {X : Type u} {ι : Type v} {Y : ι → Type w}
    [TopologicalSpace X] [∀ i, TopologicalSpace (Y i)]
    (f : ∀ i, X → Y i) (hf : ∀ i, Continuous (f i)) :
    Continuous (fun x i => f i x) :=
  continuous_pi hf

theorem evaluation_embedding_iff {X : Type u} {ι : Type v} {Y : ι → Type w}
    [tX : TopologicalSpace X] [∀ i, TopologicalSpace (Y i)]
    (f : ∀ i, X → Y i) (_hf : ∀ i, Continuous (f i)) :
    IsEmbedding (fun x i => f i x) ↔
      Function.Injective (fun x i => f i x) ∧
        tX = TopologicalSpace.generateFrom
          {U : Set X | ∃ i V, IsOpen V ∧ U = f i ⁻¹' V} := by
  rw [Ch02.embedding_iff_induced, evaluation_induced_topology]

theorem evaluation_embedding_of_coordinates {X : Type u} {ι : Type v} {Y : ι → Type w}
    [tX : TopologicalSpace X] [tY : ∀ i, TopologicalSpace (Y i)]
    (f : ∀ i, X → Y i) (hf : ∀ i, Continuous (f i))
    (hs : ∀ x y, x ≠ y → ∃ i, f i x ≠ f i y)
    (hlocal : ∀ U : Set X, IsOpen U → ∀ x ∈ U,
      ∃ (i : ι) (V : Set (Y i)), IsOpen V ∧ x ∈ f i ⁻¹' V ∧ f i ⁻¹' V ⊆ U) :
    IsEmbedding (fun x i => f i x) := by
  apply (evaluation_embedding_iff f hf).mpr
  refine ⟨(evaluation_injective_iff f).mpr hs, ?_⟩
  change tX = Ch03.initialTopology tY f
  apply le_antisymm
  · exact Ch03.initial_coarsest tY f tX hf
  · intro U hU
    apply (@isOpen_iff_forall_mem_open X (Ch03.initialTopology tY f) U).mpr
    intro x hx
    obtain ⟨i, V, hV, hxV, hVU⟩ := hlocal U hU x hx
    exact ⟨f i ⁻¹' V, hVU,
      continuous_def.mp (Ch03.initial_maps_continuous tY f i) V hV, hxV⟩

theorem evaluation_embedding_unitInterval {X : Type u} {ι : Type v}
    [TopologicalSpace X] (f : ι → X → unitInterval)
    (hf : ∀ i, Continuous (f i))
    (hs : ∀ x y, x ≠ y → ∃ i, f i x ≠ f i y)
    (hlocal : ∀ U : Set X, IsOpen U → ∀ x ∈ U,
      ∃ i, 0 < (f i x : ℝ) ∧ ∀ y, y ∉ U → f i y = 0) :
    IsEmbedding (fun x i => f i x) := by
  apply evaluation_embedding_of_coordinates f hf hs
  intro U hU x hx
  obtain ⟨i, hi, hzero⟩ := hlocal U hU x hx
  refine ⟨i, {z : unitInterval | 0 < (z : ℝ)},
    isOpen_lt continuous_const continuous_subtype_val, hi, ?_⟩
  intro y hy
  by_contra hyU
  have hzy := hzero y hyU
  change 0 < (f i y : ℝ) at hy
  simp [hzy] at hy

theorem compact_injection_embedding {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (f : X → Y) (hX : Ch05.CoverCompact X)
    (hf : Continuous f) (hi : Function.Injective f) : IsEmbedding f :=
  Ch05.compact_to_hausdorff_injective f hX hf hi

theorem compact_evaluation_embedding {X : Type u} {ι : Type v} {Y : ι → Type w}
    [TopologicalSpace X] [∀ i, TopologicalSpace (Y i)] [∀ i, T2Space (Y i)]
    (f : ∀ i, X → Y i) (hX : Ch05.CoverCompact X)
    (hf : ∀ i, Continuous (f i))
    (hs : ∀ x y, x ≠ y → ∃ i, f i x ≠ f i y) :
    IsEmbedding (fun x i => f i x) :=
  compact_injection_embedding _ hX (evaluation_continuous f hf)
    ((evaluation_injective_iff f).mpr hs)

theorem discrete_real_counterexample :
    @Continuous ℝ ℝ ⊥ inferInstance id ∧
    Function.Injective (id : ℝ → ℝ) ∧
    ¬ @IsEmbedding ℝ ℝ ⊥ inferInstance id ∧
    ¬ @Continuous ℝ ℝ inferInstance ⊥ id := by
  have hn : ¬ @Continuous ℝ ℝ inferInstance ⊥ id := by
    intro h
    have hopen : IsOpen (id ⁻¹' ({0} : Set ℝ)) :=
      continuous_def.mp h _ (show @IsOpen ℝ ⊥ ({0} : Set ℝ) from trivial)
    exact not_isOpen_singleton (0 : ℝ) hopen
  refine ⟨continuous_bot, Function.injective_id, ?_, hn⟩
  intro he
  have hopen : @IsOpen ℝ ⊥ ({0} : Set ℝ) := trivial
  have hreal : IsOpen ({0} : Set ℝ) := by
    have ht := ((@Ch02.embedding_iff_induced ℝ ℝ ⊥
      (inferInstance : TopologicalSpace ℝ) id).mp he).2
    rw [ht] at hopen
    obtain ⟨V, hV, heq⟩ := hopen
    change V = {0} at heq
    exact heq ▸ hV
  exact not_isOpen_singleton (0 : ℝ) hreal

end D10Topology.Ch10
