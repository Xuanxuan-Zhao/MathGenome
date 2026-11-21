import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions

/-! Metric conventions for paper.tex: d10:09:metric, d10:09:equivalences,
d10:09:complete-definition, d10:09:total-bounded, and the extended diameter
in d10:09:cantor-intersection.
All distances are finite real numbers. Only diameter takes values in the extended
nonnegative reals. No nonempty-space assumption is imposed.
-/
open Set Filter
open scoped Topology ENNReal NNReal
universe u v

namespace D10Topology.Ch09

/-- Canonical finite real-valued metrics. -/
abbrev Metric : (X : Type u) → Type u := fun X => MetricSpace X

/-- Distinct points may have zero distance. -/
abbrev Pseudometric : (X : Type u) → Type u := fun X => PseudoMetricSpace X

def distance : {X : Type u} → PseudoMetricSpace X → X → X → ℝ := fun d => @dist _ d.toDist

def PseudometricAxioms : {X : Type u} → (X → X → ℝ) → Prop := fun d =>
  (∀ x y, 0 ≤ d x y) ∧ (∀ x, d x x = 0) ∧
    (∀ x y, d x y = d y x) ∧ (∀ x y z, d x z ≤ d x y + d y z)

def MetricAxioms : {X : Type u} → (X → X → ℝ) → Prop := fun d => PseudometricAxioms d ∧ ∀ x y, d x y = 0 ↔ x = y

/-- For positive r this is the paper's open ball; other radii are also allowed. -/
def ball : {X : Type u} → PseudoMetricSpace X → X → ℝ → Set X := fun d x r => {y | distance d x y < r}

@[instance_reducible] def metricTopology : {X : Type u} → PseudoMetricSpace X → TopologicalSpace X := fun d => d.toUniformSpace.toTopologicalSpace

def Metrizable : {X : Type u} → TopologicalSpace X → Prop := fun t => ∃ d : MetricSpace _, metricTopology d.toPseudoMetricSpace = t

def TopologicallyEquivalent : {X : Type u} → PseudoMetricSpace X → PseudoMetricSpace X → Prop := fun d e => ∀ U : Set _, IsOpen[metricTopology d] U ↔ IsOpen[metricTopology e] U

/-- The same delta works for every pair of points. -/
def UniformlyContinuous : {X : Type u} → {Y : Type v} → PseudoMetricSpace X → PseudoMetricSpace Y → (X → Y) → Prop := fun d e f => ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
  ∀ x x', distance d x x' < δ → distance e (f x) (f x') < ε

def UniformlyEquivalent : {X : Type u} → PseudoMetricSpace X → PseudoMetricSpace X → Prop := fun d e => UniformlyContinuous d e id ∧ UniformlyContinuous e d id

/-- The full real-parameter inequality; the library bridge specializes to nonnegative L. -/
def Lipschitz : {X : Type u} → {Y : Type v} → PseudoMetricSpace X → PseudoMetricSpace Y → ℝ → (X → Y) → Prop := fun d e L f => ∀ x y, distance e (f x) (f y) ≤ L * distance d x y

def Isometry : {X : Type u} → {Y : Type v} → PseudoMetricSpace X → PseudoMetricSpace Y → (X → Y) → Prop := fun d e f => ∀ x y, distance e (f x) (f y) = distance d x y

def IsometricIsomorphism : {X : Type u} → {Y : Type v} → MetricSpace X → MetricSpace Y → (X → Y) → Prop := fun d e f => Isometry d.toPseudoMetricSpace e.toPseudoMetricSpace f ∧ Function.Surjective f

def BilipschitzEquivalent : {X : Type u} → PseudoMetricSpace X → PseudoMetricSpace X → Prop := fun d e => ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
  ∀ x y, c * distance d x y ≤ distance e x y ∧ distance e x y ≤ C * distance d x y

/-- Natural-number indices start at zero; reindexing the paper's n≥1 changes no tail condition. -/
def CauchySequence : {X : Type u} → PseudoMetricSpace X → (ℕ → X) → Prop := fun d s => ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
  ∀ m, N ≤ m → ∀ n, N ≤ n → distance d (s m) (s n) < ε

def SequenceConverges : {X : Type u} → PseudoMetricSpace X → (ℕ → X) → X → Prop := fun d s x => ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
  ∀ n, N ≤ n → distance d (s n) x < ε

def SequentiallyComplete : {X : Type u} → PseudoMetricSpace X → Prop := fun d => ∀ s : ℕ → _, CauchySequence d s → ∃ x, SequenceConverges d s x

/-- Existence of a compatible complete metric, not completeness of an arbitrary compatible metric. -/
def CompletelyMetrizable : {X : Type u} → TopologicalSpace X → Prop := fun t => ∃ d : MetricSpace _, metricTopology d.toPseudoMetricSpace = t ∧
  SequentiallyComplete d.toPseudoMetricSpace

/-- Finite centers lie in the actual space. The finite set may be empty. -/
def TotallyBounded : {X : Type u} → PseudoMetricSpace X → Prop := fun d => ∀ ε : ℝ, 0 < ε → ∃ F : Set _, F.Finite ∧
  (⋃ c ∈ F, ball d c ε) = Set.univ

/-- Extended diameter: no boundedness hypothesis or real-valued truncation. -/
noncomputable abbrev diameter : {X : Type u} → PseudoMetricSpace X → Set X → ℝ≥0∞ := fun d A => ⨆ x ∈ A, ⨆ y ∈ A, ENNReal.ofReal (distance d x y)

theorem pseudometric_representation :
  ∀ {X : Type u} (f : X → X → ℝ),
  PseudometricAxioms f ↔ ∃ d : PseudoMetricSpace X, distance d = f := by
  intro X f
  constructor
  · rintro ⟨_, hs, hc, ht⟩
    exact ⟨{dist := f, dist_self := hs, dist_comm := hc, dist_triangle := ht}, rfl⟩
  · rintro ⟨d, rfl⟩
    let := d
    exact ⟨fun _ _ => dist_nonneg, dist_self, dist_comm, dist_triangle⟩

theorem metric_representation :
  ∀ {X : Type u} (f : X → X → ℝ),
  MetricAxioms f ↔ ∃ d : MetricSpace X, distance d.toPseudoMetricSpace = f := by
  intro X f
  constructor
  · rintro ⟨hp, hz⟩
    obtain ⟨d, hd⟩ := (pseudometric_representation f).mp hp
    exact ⟨{d with eq_of_dist_eq_zero := fun {x y} h => (hz x y).mp (by simpa only [← hd, distance] using h)}, hd⟩
  · rintro ⟨d, rfl⟩
    let := d
    exact ⟨(pseudometric_representation _).mpr ⟨d.toPseudoMetricSpace, rfl⟩,
      fun _ _ => dist_eq_zero⟩

theorem ball_eq_mathlib :
  ∀ {X : Type u} (d : PseudoMetricSpace X) (x : X) (r : ℝ),
  ball d x r = @Metric.ball X d x r := by
  intro X d x r
  let := d
  ext y
  exact (congrArg (fun a : ℝ => a < r) (dist_comm x y)).to_iff

theorem metricTopology_open_iff :
  ∀ {X : Type u} (d : PseudoMetricSpace X) (U : Set X),
  IsOpen[metricTopology d] U ↔ ∀ x ∈ U, ∃ r > 0, ball d x r ⊆ U := by
  intro X d U
  let := d
  simpa only [ball_eq_mathlib, metricTopology] using (Metric.isOpen_iff (s := U))

theorem metrizable_iff_mathlib :
  ∀ {X : Type u} (t : TopologicalSpace X),
  Metrizable t ↔ @TopologicalSpace.MetrizableSpace X t := by
  intro X t
  constructor
  · rintro ⟨d, rfl⟩
    let := d
    change @TopologicalSpace.MetrizableSpace X d.toUniformSpace.toTopologicalSpace
    infer_instance
  · intro h
    let := t
    let := h
    exact ⟨TopologicalSpace.metrizableSpaceMetric X, rfl⟩

theorem topologicallyEquivalent_iff_topology_eq :
  ∀ {X : Type u} (d e : PseudoMetricSpace X),
  TopologicallyEquivalent d e ↔ metricTopology d = metricTopology e := by
  intro X d e
  exact TopologicalSpace.ext_iff.symm

theorem uniformlyContinuous_iff_mathlib :
  ∀ {X : Type u} {Y : Type v} (d : PseudoMetricSpace X)
    (e : PseudoMetricSpace Y) (f : X → Y),
  UniformlyContinuous d e f ↔ @UniformContinuous X Y d.toUniformSpace e.toUniformSpace f := by
  intro X Y d e f
  let := d
  let := e
  exact Metric.uniformContinuous_iff.symm.trans (by rfl)

theorem uniformlyEquivalent_iff_mathlib :
  ∀ {X : Type u} (d e : PseudoMetricSpace X),
  UniformlyEquivalent d e ↔
    @UniformContinuous X X d.toUniformSpace e.toUniformSpace id ∧
    @UniformContinuous X X e.toUniformSpace d.toUniformSpace id := by
  intro X d e
  exact and_congr (uniformlyContinuous_iff_mathlib d e id)
    (uniformlyContinuous_iff_mathlib e d id)

theorem lipschitz_iff_mathlib :
  ∀ {X : Type u} {Y : Type v} (d : PseudoMetricSpace X)
    (e : PseudoMetricSpace Y) (L : ℝ≥0) (f : X → Y),
  Lipschitz d e (L : ℝ) f ↔ @LipschitzWith X Y
    (@PseudoMetricSpace.toPseudoEMetricSpace X d)
    (@PseudoMetricSpace.toPseudoEMetricSpace Y e) L f := by
  intro X Y d e L f
  let := d
  let := e
  exact lipschitzWith_iff_dist_le_mul.symm

theorem isometry_iff_mathlib :
  ∀ {X : Type u} {Y : Type v} (d : PseudoMetricSpace X)
    (e : PseudoMetricSpace Y) (f : X → Y),
  Isometry d e f ↔ @_root_.Isometry X Y
    (@PseudoMetricSpace.toPseudoEMetricSpace X d)
    (@PseudoMetricSpace.toPseudoEMetricSpace Y e) f := by
  intro X Y d e f
  let := d
  let := e
  exact isometry_iff_dist_eq.symm

theorem isometricIsomorphism_iff_mathlib :
  ∀ {X : Type u} {Y : Type v} (d : MetricSpace X)
    (e : MetricSpace Y) (f : X → Y),
  IsometricIsomorphism d e f ↔ ∃ g : @IsometryEquiv X Y
    (@PseudoMetricSpace.toPseudoEMetricSpace X d.toPseudoMetricSpace)
    (@PseudoMetricSpace.toPseudoEMetricSpace Y e.toPseudoMetricSpace), (g : X → Y) = f := by
  intro X Y d e f
  let := d
  let := e
  constructor
  · rintro ⟨hi, hs⟩
    have hi' := (isometry_iff_mathlib _ _ f).mp hi
    exact ⟨{Equiv.ofBijective f ⟨hi'.injective, hs⟩ with isometry_toFun := hi'}, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨(isometry_iff_mathlib _ _ _).mpr g.isometry, g.surjective⟩

theorem cauchySequence_iff_mathlib :
  ∀ {X : Type u} (d : PseudoMetricSpace X) (s : ℕ → X),
  CauchySequence d s ↔ @CauchySeq X ℕ d.toUniformSpace _ s := by
  intro X d s
  let := d
  exact Metric.cauchySeq_iff.symm

theorem sequenceConverges_iff_mathlib :
  ∀ {X : Type u} (d : PseudoMetricSpace X) (s : ℕ → X) (x : X),
  SequenceConverges d s x ↔ Filter.Tendsto s Filter.atTop (@nhds X (metricTopology d) x) := by
  intro X d s x
  let := d
  exact Metric.tendsto_atTop.symm

theorem sequentiallyComplete_iff_mathlib :
  ∀ {X : Type u} (d : PseudoMetricSpace X),
  SequentiallyComplete d ↔ @CompleteSpace X d.toUniformSpace := by
  intro X d
  let := d
  constructor
  · intro h
    apply Metric.complete_of_cauchySeq_tendsto
    intro s hs
    obtain ⟨x, hx⟩ := h s ((cauchySequence_iff_mathlib d s).mpr hs)
    exact ⟨x, (sequenceConverges_iff_mathlib d s x).mp hx⟩
  · intro h s hs
    let := h
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete ((cauchySequence_iff_mathlib d s).mp hs)
    exact ⟨x, (sequenceConverges_iff_mathlib d s x).mpr hx⟩

theorem completelyMetrizable_iff_mathlib :
  ∀ {X : Type u} (t : TopologicalSpace X),
  CompletelyMetrizable t ↔ @TopologicalSpace.IsCompletelyMetrizableSpace X t := by
  intro X t
  constructor
  · rintro ⟨d, ht, hc⟩
    exact ⟨d, ht, (sequentiallyComplete_iff_mathlib _).mp hc⟩
  · rintro ⟨d, ht, hc⟩
    exact ⟨d, ht, (sequentiallyComplete_iff_mathlib _).mpr hc⟩

theorem totallyBounded_iff_mathlib :
  ∀ {X : Type u} (d : PseudoMetricSpace X),
  TotallyBounded d ↔ @_root_.TotallyBounded X d.toUniformSpace Set.univ := by
  intro X d
  let := d
  simp only [TotallyBounded, ball_eq_mathlib, Metric.totallyBounded_iff,
    Set.eq_univ_iff_forall, Set.univ_subset_iff]

theorem diameter_eq_mathlib :
  ∀ {X : Type u} (d : PseudoMetricSpace X) (A : Set X),
  diameter d A = @Metric.ediam X (@PseudoMetricSpace.toEDist X d) A := by
  intro X d A
  let := d
  simp only [diameter, Metric.ediam, edist_dist, distance]

theorem diameter_empty :
  ∀ {X : Type u} (d : PseudoMetricSpace X), diameter d (∅ : Set X) = 0 := by
  intro X d
  simp [diameter]

theorem diameter_le_iff :
  ∀ {X : Type u} (d : PseudoMetricSpace X) (A : Set X) (r : ℝ≥0∞),
  diameter d A ≤ r ↔ ∀ x ∈ A, ∀ y ∈ A, ENNReal.ofReal (distance d x y) ≤ r := by
  intro X d A r
  simp only [diameter, iSup_le_iff]

theorem diameter_eq_top_iff :
  ∀ {X : Type u} (d : PseudoMetricSpace X) (A : Set X),
  diameter d A = ⊤ ↔ ∀ R : ℝ≥0∞, R < ⊤ →
    ∃ x ∈ A, ∃ y ∈ A, R < ENNReal.ofReal (distance d x y) := by
  intro X d A
  simp only [diameter, iSup_eq_top, lt_iSup_iff, exists_prop]

theorem empty_complete :
  ∀ {X : Type u} [IsEmpty X] (d : PseudoMetricSpace X), SequentiallyComplete d := by
  intro X h d s hs
  exact isEmptyElim (s 0)

theorem empty_totallyBounded :
  ∀ {X : Type u} [IsEmpty X] (d : PseudoMetricSpace X), TotallyBounded d := by
  intro X h d ε hε
  refine ⟨∅, Set.finite_empty, ?_⟩
  ext x
  exact isEmptyElim x

end D10Topology.Ch09
