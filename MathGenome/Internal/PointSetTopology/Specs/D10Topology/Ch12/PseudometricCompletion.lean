import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.PseudometricQuotient
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.PseudometricFamilies
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.MetricFilterCompleteness
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.CompletionUniversal

/-! Independent specification of paper.tex, d10:12:pseudometric-completion.
The carrier is exactly the fixed metric completion of the zero-distance metric
quotient, and the map is exactly the composite of the two canonical maps.
Every uniformity and topology below belongs to the displayed pseudometric.
No separation, inhabitance, or factorization hypothesis on X is imposed. -/
open Set Filter
open scoped Uniformity
universe u v
namespace Specs.D10Topology.Ch12.PseudometricCompletion

open PseudometricQuotient

abbrev Completion {X : Type u} (q : PseudoMetricSpace X) : Type u :=
  Ch09.MetricCompletion.completionValue (metricQuotientMetric q)

@[instance_reducible] noncomputable def completionMetric {X : Type u} (q : PseudoMetricSpace X) :
    MetricSpace (Completion q) :=
  Ch09.MetricCompletion.completionMetricValue (metricQuotientMetric q)

def completionMap {X : Type u} (q : PseudoMetricSpace X) : X → Completion q :=
  Ch09.MetricCompletion.completionEmbeddingValue (metricQuotientMetric q) ∘ metricQuotientMap q

def completionType := {X : Type u} → PseudoMetricSpace X → Type u
def completionValue : completionType := @Completion

def completionMetricType := {X : Type u} → (q : PseudoMetricSpace X) → MetricSpace (Completion q)
noncomputable def completionMetricValue : completionMetricType := @completionMetric

def completionMapType := {X : Type u} → (q : PseudoMetricSpace X) → X → Completion q
def completionMapValue : completionMapType := @completionMap

def map_distance : Prop :=
  ∀ {X : Type u} (q : PseudoMetricSpace X) (x y : X),
    @dist _ (completionMetric q).toDist (completionMap q x) (completionMap q y) =
      @dist X q.toDist x y

def map_dense : Prop :=
  ∀ {X : Type u} (q : PseudoMetricSpace X),
    @DenseRange _ (completionMetric q).toUniformSpace.toTopologicalSpace X (completionMap q)

def inverse_image_uniformity : Prop :=
  ∀ {X : Type u} (q : PseudoMetricSpace X),
    UniformSpace.comap (completionMap q) (completionMetric q).toUniformSpace = q.toUniformSpace

def inverse_image_entourages : Prop :=
  ∀ {X : Type u} (q : PseudoMetricSpace X),
    Filter.comap (Prod.map (completionMap q) (completionMap q))
      (@uniformity _ (completionMetric q).toUniformSpace) = @uniformity X q.toUniformSpace

def map_eq_iff : Prop :=
  ∀ {X : Type u} (q : PseudoMetricSpace X) (x y : X),
    completionMap q x = completionMap q y ↔ @dist X q.toDist x y = 0

def embedding_iff : Prop :=
  ∀ {X : Type u} (q : PseudoMetricSpace X),
    @Topology.IsEmbedding X (Completion q) q.toUniformSpace.toTopologicalSpace
      (completionMetric q).toUniformSpace.toTopologicalSpace (completionMap q) ↔
    ∀ x y, @dist X q.toDist x y = 0 → x = y

def uniformEmbedding_iff : Prop :=
  ∀ {X : Type u} (q : PseudoMetricSpace X),
    @IsUniformEmbedding X (Completion q) q.toUniformSpace
      (completionMetric q).toUniformSpace (completionMap q) ↔
    ∀ x y, @dist X q.toDist x y = 0 → x = y

/-- Completeness uses proper Cauchy filters; separatedness is equality of the
intersection of all entourages with the diagonal. -/
def complete_separated : Prop :=
  ∀ {X : Type u} (q : PseudoMetricSpace X),
    @UniformConventions.Complete (Completion q) (completionMetric q).toUniformSpace ∧
    @UniformConventions.Separated (Completion q) (completionMetric q).toUniformSpace

def completion_empty : Prop :=
  ∀ {X : Type u} [IsEmpty X] (q : PseudoMetricSpace X), IsEmpty (Completion q)

/-- The required factorization is a conclusion, not a premise. -/
def zero_identification : Prop :=
  ∀ {X : Type u} {Y : Type v} (q : PseudoMetricSpace X) (e : MetricSpace Y) (f : X → Y),
    Ch09.MetricConventions.UniformlyContinuous q e.toPseudoMetricSpace f →
    ∀ x y, @dist X q.toDist x y = 0 → f x = f y

def quotient_factorization : Prop :=
  ∀ {X : Type u} {Y : Type v} (q : PseudoMetricSpace X) (e : MetricSpace Y) (f : X → Y),
    Ch09.MetricConventions.UniformlyContinuous q e.toPseudoMetricSpace f →
    ∃! f₀ : MetricQuotient q → Y,
      Ch09.MetricConventions.UniformlyContinuous (metricQuotientMetric q).toPseudoMetricSpace
        e.toPseudoMetricSpace f₀ ∧ f₀ ∘ metricQuotientMap q = f

def extension : Prop :=
  ∀ {X : Type u} {Y : Type v} (q : PseudoMetricSpace X) (e : MetricSpace Y) (f : X → Y),
    Ch09.MetricConventions.SequentiallyComplete e.toPseudoMetricSpace →
    Ch09.MetricConventions.UniformlyContinuous q e.toPseudoMetricSpace f →
    ∃! g : Completion q → Y,
      Ch09.MetricConventions.UniformlyContinuous (completionMetric q).toPseudoMetricSpace
        e.toPseudoMetricSpace g ∧ g ∘ completionMap q = f

/-- The same canonical construction for the specified weighted sum, with explicit
pullback from the original family uniformity, its exact separation test, and
extension of maps uniformly continuous for that family. Other assertions above
apply to the exhibited q, including completeness, density and the empty case. -/
def countable_family_completion : Prop :=
  ∀ {X : Type u} (p : ℕ → PseudoMetricSpace X),
    ∃ q : PseudoMetricSpace X,
      (@dist X q.toDist) = PseudometricFamilies.weightedDistance p ∧
      q.toUniformSpace = PseudometricFamilies.familyUniformity p ∧
      UniformSpace.comap (completionMap q) (completionMetric q).toUniformSpace =
        PseudometricFamilies.familyUniformity p ∧
      (@IsUniformEmbedding X (Completion q) (PseudometricFamilies.familyUniformity p)
        (completionMetric q).toUniformSpace (completionMap q) ↔
          PseudometricFamilies.SeparatesPairs p) ∧
      (@Topology.IsEmbedding X (Completion q)
        (PseudometricFamilies.familyUniformity p).toTopologicalSpace
        (completionMetric q).toUniformSpace.toTopologicalSpace (completionMap q) ↔
          PseudometricFamilies.SeparatesPairs p) ∧
      (∀ {Y : Type v} (e : MetricSpace Y) (f : X → Y),
        Ch09.MetricConventions.SequentiallyComplete e.toPseudoMetricSpace →
        @UniformContinuous X Y (PseudometricFamilies.familyUniformity p) e.toUniformSpace f →
        ∃! g : Completion q → Y,
          @UniformContinuous (Completion q) Y (completionMetric q).toUniformSpace
            e.toUniformSpace g ∧ g ∘ completionMap q = f)

end Specs.D10Topology.Ch12.PseudometricCompletion
