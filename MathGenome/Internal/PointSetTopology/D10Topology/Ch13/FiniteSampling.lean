import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.FiniteSampling
import MathGenome.Internal.PointSetTopology.D10Topology.Ch13.FunctionTopologies
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.Pi

noncomputable section
open Set Filter
open scoped Topology Uniformity
universe u v
namespace D10Topology.Ch13
/-- A pointwise totally bounded family is totally bounded in its induced
pointwise uniformity. The ultrafilter proof also covers an empty index set. -/
private theorem pointwise_totallyBounded {X : Type u} {Y : Type v}
    [UniformSpace Y] {I : Type*} (F : I → X → Y)
    (h : ∀ x, TotallyBounded (range (fun i => F i x))) :
    @TotallyBounded I (UniformSpace.comap F (Pi.uniformSpace fun _ : X => Y)) univ := by
  let : UniformSpace I := UniformSpace.comap F (Pi.uniformSpace fun _ : X => Y)
  apply totallyBounded_iff_ultrafilter.mpr
  intro U _
  apply cauchy_comap_uniformSpace.mpr
  apply (cauchy_pi_iff' (fun _ : X => Y)).mpr
  intro x
  have hx := (U.map (fun i => F i x)).cauchy_of_totallyBounded (h x)
  apply hx
  exact le_principal_iff.mpr (by
    change (fun i => F i x) ⁻¹' range (fun i => F i x) ∈ (U : Filter I)
    exact mem_of_superset univ_mem (fun i _ => ⟨i, rfl⟩))

/-- Finite sampling gives finite epsilon nets with centers in the family. -/
theorem finite_sampling {X : Type u} {Y : Type v}
    [TopologicalSpace X] [CompactSpace X] [MetricSpace Y]
    (A : Set (ContinuousMaps X Y)) (he : Equicontinuous A)
    (hp : ∀ x : X, TotallyBounded ((fun f : ContinuousMaps X Y => f x) '' A))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Set (ContinuousMaps X Y), F.Finite ∧ F ⊆ A ∧
      ∀ f ∈ A, ∃ g ∈ F, uniformDistance (f : X → Y) (g : X → Y) < ε := by
  let F : A → X → Y := fun f => (f.val : X → Y)
  have hpoint : ∀ x, TotallyBounded (range (fun f : A => F f x)) := by
    intro x
    convert hp x using 1
    ext y
    simp [F]
  have ht := pointwise_totallyBounded F hpoint
  have he' : _root_.Equicontinuous F := (equicontinuous_iff_mathlib A).mp he
  rw [← he'.comap_uniformFun_eq] at ht
  let : MetricSpace (ContinuousMaps X Y) := uniformContinuousMetric
  let : UniformSpace (ContinuousMaps X Y) :=
    (uniformContinuousMetric (X := X) (Y := Y)).toUniformSpace
  have ht' : TotallyBounded (univ : Set A) := by
    convert ht using 1
    change UniformSpace.comap Subtype.val
      (UniformSpace.comap (fun f : ContinuousMaps X Y => (f : X → Y))
        (uniformMetric (X := X) (Y := Y)).toUniformSpace) = _
    rw [← UniformSpace.comap_comap, ← uniformUniformity_eq_metric]
    change UniformSpace.comap _ (UniformSpace.comap UniformFun.ofFun
      (UniformFun.uniformSpace X Y)) = _
    rw [← UniformSpace.comap_comap]
    rfl
  have hA : TotallyBounded A := by
    have := (totallyBounded_image_iff
      (isUniformEmbedding_subtype_val (p := fun f : ContinuousMaps X Y => f ∈ A)).isUniformInducing).mpr ht'
    simpa only [image_univ, Subtype.range_coe_subtype, ofPred_mem_eq] using this
  obtain ⟨B, hBA, hB, hcover⟩ := hA.exists_subset (Metric.dist_mem_uniformity hε)
  refine ⟨B, hB, hBA, ?_⟩
  intro f hf
  obtain ⟨g, hg, hfg⟩ := mem_iUnion₂.mp (hcover hf)
  exact ⟨g, hg, hfg⟩

end D10Topology.Ch13
