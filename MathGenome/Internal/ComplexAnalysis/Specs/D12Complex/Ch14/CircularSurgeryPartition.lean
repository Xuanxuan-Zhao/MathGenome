import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.CircularCornerRounding
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Data.Fintype.EquivFin

/-! Independent interface for the literal finite surgery and its parameter
partition, paper.tex:2669–2678. The full obligation is
`circular_surgery_partition_type`. The other theorem types are proper parts;
they do not assert that a supplied circle boundary has been subdivided. -/

noncomputable section
open Set Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace D12Complex.CircularSurgeryPartition
open CircularExhaustion CircularCornerRounding

/-- The supplied arrays, with precisely the raw geometric hypotheses. -/
def CircularBoundary (U : Set ℂ) (n : ℕ) (center : Fin n → ℂ)
    (radius start stop sign : Fin n → ℝ) : Prop :=
  (∀ i, 0 < radius i ∧ start i < stop i ∧ stop i - start i ≤ 2 * Real.pi) ∧
  (∀ i, sign i = 1 ∨ sign i = -1) ∧
  frontier U = ⋃ i, arcParam (center i) (radius i) '' Icc (start i) (stop i) ∧
  (∀ i j, i ≠ j → Disjoint
    (arcParam (center i) (radius i) '' Ioo (start i) (stop i))
    (arcParam (center j) (radius j) '' Ioo (start j) (stop j))) ∧
  (∀ i, InjOn (arcParam (center i) (radius i)) (Ioo (start i) (stop i))) ∧
  ∀ i t, t ∈ Ioo (start i) (stop i) → ∃ W : Set ℂ,
    IsOpen W ∧ arcParam (center i) (radius i) t ∈ W ∧
      ∀ z ∈ W, z ∈ U ↔ sign i * (‖z - center i‖ ^ 2 - radius i ^ 2) < 0

/-- Ordinary normalized, disjoint C1 sector charts and one inverse Lipschitz
bound. These are geometric data, containing no integral/display certificate. -/
def UniformCharts (U : Set ℂ) (J : Finset ℂ) (θ : ℂ → ℝ)
    (e : ℂ → OpenPartialHomeomorph ℂ ℂ) (R : ℝ) (L : ℝ≥0) : Prop :=
  0 < R ∧ 0 < L ∧
  (∀ p ∈ J, 0 < θ p ∧ θ p < 2 * Real.pi) ∧
  (∀ p ∈ J, (e p).IsImage U (sector (θ p))) ∧
  (∀ p ∈ J, ContDiffOn ℝ 1 (e p) (e p).source ∧
    ContDiffOn ℝ 1 (e p).symm (e p).target) ∧
  (∀ p ∈ J, p ∈ (e p).source ∧ e p p = 0) ∧
  (∀ p ∈ J, ∀ q ∈ J, p ≠ q → Disjoint (e p).source (e q).source) ∧
  ∀ p ∈ J, closedBall (0 : ℂ) R ⊆ (e p).target ∧
    LipschitzOnWith L (e p).symm (closedBall (0 : ℂ) R)

/-- The actual compact removal; the rounded set is its literal difference. -/
def removedTips (J : Finset ℂ) (e : ℂ → OpenPartialHomeomorph ℂ ℂ)
    (θ : ℂ → ℝ) (ε : ℝ) : Set ℂ :=
  ⋃ p ∈ J, (e p).symm '' sectorTip ε (θ p)

def surgeryDomain (U : Set ℂ) (J : Finset ℂ)
    (e : ℂ → OpenPartialHomeomorph ℂ ℂ) (θ : ℂ → ℝ) (ε : ℝ) : Set ℂ :=
  U \ removedTips J e θ ε

/-- Finite strict nodes cover the whole original interval. A true label means
retained. No bound on the number of intervals is presumed. -/
structure AngularSubdivision (a b : ℝ) where
  count : ℕ
  node : Fin (count + 1) → ℝ
  strict : StrictMono node
  first : node 0 = a
  last : node (Fin.last count) = b
  keep : Fin count → Bool

def RetainedIndex {n : ℕ} {a b : Fin n → ℝ}
    (P : ∀ i, AngularSubdivision (a i) (b i)) :=
  Σ i, {j : Fin (P i).count // (P i).keep j = true}

def DeletedIndex {n : ℕ} {a b : Fin n → ℝ}
    (P : ∀ i, AngularSubdivision (a i) (b i)) :=
  Σ i, {j : Fin (P i).count // (P i).keep j = false}

/-- The two literal model directions, with unit Euclidean norm. -/
def rayDirection (θ : ℝ) (upper : Bool) : ℂ :=
  if upper then Complex.exp ((θ : ℂ) * Complex.I) else 1

/-- An actual C1, regular, monotone or antitone change from a deleted angular
interval onto a specified radial subinterval of one model short ray. -/
structure DeletedRayChange (J : Finset ℂ)
    (e : ℂ → OpenPartialHomeomorph ℂ ℂ) (θ : ℂ → ℝ)
    (ε : ℝ) (c : ℂ) (r a b : ℝ) where
  join : ℂ
  join_mem : join ∈ J
  upper : Bool
  lo : ℝ
  hi : ℝ
  lo_nonneg : 0 ≤ lo
  lo_lt_hi : lo < hi
  hi_le_one : hi ≤ 1
  φ : ℝ → ℝ
  T : Set ℝ
  open_T : IsOpen T
  interval_subset : Icc a b ⊆ T
  smooth : ContDiffOn ℝ 1 φ T
  regular : ∀ t ∈ Icc a b, deriv φ t ≠ 0
  monotone : (StrictMonoOn φ (Icc a b) ∧ φ a = lo ∧ φ b = hi) ∨
    (StrictAntiOn φ (Icc a b) ∧ φ a = hi ∧ φ b = lo)
  image : φ '' Icc a b = Icc lo hi
  curve_eq : ∀ t ∈ Icc a b, arcParam c r t =
    (e join).symm ((ε * φ t) • rayDirection (θ join) upper)

/-- Ordinary local regular extensions at every closed parameter, including
the new joins. The open interval parametrizes exactly the local frontier and
is a topological embedding. Finite seams do not waive this condition. -/
def HasLocalRegularExtensions (V : Set ℂ) (γ : ℝ → ℂ) (a b : ℝ) : Prop :=
  ∀ t ∈ Icc a b, ∃ (δ : ℝ) (W : Set ℂ) (η : ℝ → ℂ),
    0 < δ ∧ IsOpen W ∧ γ t ∈ W ∧
    ContDiffOn ℝ 1 η (Ioo (t - δ) (t + δ)) ∧
    (∀ s ∈ Ioo (t - δ) (t + δ), deriv η s ≠ 0) ∧
    (∀ s ∈ Ioo (t - δ) (t + δ) ∩ Icc a b, η s = γ s) ∧
    Topology.IsEmbedding (fun s : Ioo (t - δ) (t + δ) => η s) ∧
    η '' Ioo (t - δ) (t + δ) = frontier V ∩ W

/-- All finite parameter and local geometric output at one scale. The indices
give each retained supplied interval once and each literal rounding arc once. -/
structure SurgeryPartitionAt (U : Set ℂ) (J : Finset ℂ) (n : ℕ)
    (center : Fin n → ℂ) (radius start stop sign : Fin n → ℝ)
    (e : ℂ → OpenPartialHomeomorph ℂ ℂ) (θ : ℂ → ℝ) (C ε : ℝ) where
  subdivision : ∀ i, AngularSubdivision (start i) (stop i)
  change : ∀ d : DeletedIndex subdivision,
    DeletedRayChange J e θ ε (center d.1) (radius d.1)
      ((subdivision d.1).node d.2.1.castSucc) ((subdivision d.1).node d.2.1.succ)
  radial_cover : ∀ p ∈ J, ∀ upper : Bool,
    (⋃ d : DeletedIndex subdivision,
      ⋃ (_ : (change d).join = p), ⋃ (_ : (change d).upper = upper),
        Icc (change d).lo (change d).hi) = Icc (0 : ℝ) 1
  radial_disjoint : ∀ d f : DeletedIndex subdivision, d ≠ f →
    (change d).join = (change f).join → (change d).upper = (change f).upper →
    Disjoint (Ioo (change d).lo (change d).hi) (Ioo (change f).lo (change f).hi)
  retained_closed : ∀ i j, (subdivision i).keep j = true →
    arcParam (center i) (radius i) ''
      Icc ((subdivision i).node j.castSucc) ((subdivision i).node j.succ) ⊆
        frontier (surgeryDomain U J e θ ε)
  classify_interior : ∀ i j t,
    t ∈ Ioo ((subdivision i).node j.castSucc) ((subdivision i).node j.succ) →
    (arcParam (center i) (radius i) t ∈ frontier (surgeryDomain U J e θ ε) ↔
      (subdivision i).keep j = true)
  retained_side : ∀ i j t, (subdivision i).keep j = true →
    t ∈ Ioo ((subdivision i).node j.castSucc) ((subdivision i).node j.succ) →
    ∃ W : Set ℂ, IsOpen W ∧ arcParam (center i) (radius i) t ∈ W ∧
      U ∩ W = surgeryDomain U J e θ ε ∩ W ∧
      ∀ z ∈ W, z ∈ surgeryDomain U J e θ ε ↔
        sign i * (‖z - center i‖ ^ 2 - radius i ^ 2) < 0
  deleted_length : (∑ i, ∑ j : Fin (subdivision i).count,
    if (subdivision i).keep j then 0 else
      radius i * ((subdivision i).node j.succ - (subdivision i).node j.castSucc)) ≤ C * ε
  m : ℕ
  index : Fin m ≃ RetainedIndex subdivision ⊕ {p : ℂ // p ∈ J}
  γ : Fin m → ℝ → ℂ
  a : Fin m → ℝ
  b : Fin m → ℝ
  retained_curve : ∀ q (d : RetainedIndex subdivision), index q = Sum.inl d →
    γ q = arcParam (center d.1) (radius d.1) ∧
    a q = (subdivision d.1).node d.2.1.castSucc ∧
    b q = (subdivision d.1).node d.2.1.succ
  inserted_curve : ∀ q (p : {p : ℂ // p ∈ J}), index q = Sum.inr p →
    γ q = (fun t => (e p).symm (roundingArc ε (θ p) t)) ∧ a q = 0 ∧ b q = 1
  ordered : ∀ q, a q < b q
  regular_neighborhood : ∀ q, ∃ T : Set ℝ, IsOpen T ∧ Icc (a q) (b q) ⊆ T ∧
    ContDiffOn ℝ 1 (γ q) T ∧ ∀ t ∈ Icc (a q) (b q), deriv (γ q) t ≠ 0
  frontier_eq : frontier (surgeryDomain U J e θ ε) =
    ⋃ q, γ q '' Icc (a q) (b q)
  injective_open : ∀ q, InjOn (γ q) (Ioo (a q) (b q))
  disjoint_open : ∀ q r, q ≠ r →
    Disjoint (γ q '' Ioo (a q) (b q)) (γ r '' Ioo (a r) (b r))
  extensions : ∀ q, HasLocalRegularExtensions (surgeryDomain U J e θ ε) (γ q) (a q) (b q)
  speed_integrable : ∀ p ∈ J, IntervalIntegrable
    (fun t => ‖deriv (fun s => (e p).symm (roundingArc ε (θ p) s)) t‖) volume 0 1
  added_length : (∑ p ∈ J, ∫ t in (0 : ℝ)..1,
    ‖deriv (fun s => (e p).symm (roundingArc ε (θ p) s)) t‖) ≤ C * ε

end D12Complex.CircularSurgeryPartition

namespace Specs.D12Complex.Ch14.CircularSurgeryPartition
open _root_.D12Complex.CircularExhaustion _root_.D12Complex.CircularCornerRounding
open _root_.D12Complex.CircularSurgeryPartition

/-- Full assigned result. All input assumptions are the original geometry;
partitions, changes of parameter, speed bounds and regular joins are outputs. -/
def circular_surgery_partition_type : Prop :=
  ∀ (U : Set ℂ) (J : Finset ℂ), RoundingGeometry U J →
    ∀ (n : ℕ) (center : Fin n → ℂ) (radius start stop sign : Fin n → ℝ),
      CircularBoundary U n center radius start stop sign →
      ∃ (θ : ℂ → ℝ) (e : ℂ → OpenPartialHomeomorph ℂ ℂ)
        (R : ℝ) (L : ℝ≥0) (C ε₀ : ℝ),
        UniformCharts U J θ e R L ∧ 0 < C ∧ 0 < ε₀ ∧ ε₀ ≤ R ∧
        ∀ ε : ℝ, 0 < ε → ε < ε₀ →
          IsOpen (surgeryDomain U J e θ ε) ∧
          HasC1DefiningFunctions (surgeryDomain U J e θ ε) ∧
          Specs.D04.C12.ClassicalRegularDomains.Model.IsClassicalRegularDomain
            (realPlane '' surgeryDomain U J e θ ε) ∧
          Nonempty (SurgeryPartitionAt U J n center radius start stop sign e θ C ε)

/-- Proper geometric component: literal surgery in uniform charts, including
the exact model side and unchanged local set/frontier away from the removal. -/
def literal_surgery_uniform_type : Prop :=
  ∀ (U : Set ℂ) (J : Finset ℂ), RoundingGeometry U J →
    ∃ (θ : ℂ → ℝ) (e : ℂ → OpenPartialHomeomorph ℂ ℂ) (R : ℝ) (L : ℝ≥0),
      UniformCharts U J θ e R L ∧
      ∀ ε : ℝ, 0 < ε → ε < R →
        IsCompact (removedTips J e θ ε) ∧ IsOpen (surgeryDomain U J e θ ε) ∧
        HasC1DefiningFunctions (surgeryDomain U J e θ ε) ∧
        Specs.D04.C12.ClassicalRegularDomains.Model.IsClassicalRegularDomain
          (realPlane '' surgeryDomain U J e θ ε) ∧
        HasRegularBoundaryParametrizations (surgeryDomain U J e θ ε) ∧
        (∀ z ∉ removedTips J e θ ε, ∃ W : Set ℂ, IsOpen W ∧ z ∈ W ∧
          U ∩ W = surgeryDomain U J e θ ε ∩ W ∧
          frontier U ∩ W = frontier (surgeryDomain U J e θ ε) ∩ W) ∧
        ∀ p ∈ J, (e p).IsImage (surgeryDomain U J e θ ε) (roundedSector ε (θ p))

/-- Actual parameter-speed estimate, independent of any Hausdorff measure. -/
def pullback_roundingArc_length_type : Prop :=
  ∀ (g : ℂ → ℂ) (R : ℝ) (L : ℝ≥0),
    ContDiffOn ℝ 1 g (ball (0 : ℂ) R) →
    LipschitzOnWith L g (closedBall (0 : ℂ) R) →
    ∀ ε θ : ℝ, 0 < ε → ε < R → 0 < θ →
      IntervalIntegrable (fun t => ‖deriv (fun s => g (roundingArc ε θ s)) t‖)
        volume 0 1 ∧
      (∫ t in (0 : ℝ)..1, ‖deriv (fun s => g (roundingArc ε θ s)) t‖) ≤
        (L : ℝ) * (Real.pi / 2 + 6 * θ) * ε

def pullback_shortRay_length_type : Prop :=
  ∀ (g : ℂ → ℂ) (R : ℝ) (L : ℝ≥0),
    ContDiffOn ℝ 1 g (ball (0 : ℂ) R) →
    LipschitzOnWith L g (closedBall (0 : ℂ) R) →
    ∀ (ε : ℝ) (ξ : ℂ), 0 < ε → ε < R → ‖ξ‖ ≤ 1 →
      IntervalIntegrable (fun t => ‖deriv (fun s : ℝ => g ((ε * s) • ξ)) t‖)
        volume 0 1 ∧
      (∫ t in (0 : ℝ)..1, ‖deriv (fun s : ℝ => g ((ε * s) • ξ)) t‖) ≤
        (L : ℝ) * ε

/-- Uniform charts can avoid every other marked point without changing their
underlying functions or inverse Lipschitz constant. -/
def uniformCharts_restrict_away_finite_type : Prop :=
  ∀ {U : Set ℂ} {J : Finset ℂ} {θ : ℂ → ℝ}
    {e : ℂ → OpenPartialHomeomorph ℂ ℂ} {R : ℝ} {L : ℝ≥0},
    UniformCharts U J θ e R L → ∀ F : Finset ℂ,
    ∃ (E : ℂ → OpenPartialHomeomorph ℂ ℂ) (r : ℝ),
      UniformCharts U J θ E r L ∧ r ≤ R ∧
      (∀ p : ℂ, (E p : ℂ → ℂ) = e p ∧ ((E p).symm : ℂ → ℂ) = (e p).symm) ∧
      ∀ p ∈ J, (E p).source ⊆ (e p).source ∧
        ∀ q ∈ F, q ≠ p → q ∉ (E p).source

/-- Finite marking of an injectively parametrized open arc, allowing repeated
closed endpoints. This says nothing yet about a retained/deleted label. -/
def finite_marked_nodes_type : Prop :=
  ∀ {β : Type*} {γ : ℝ → β} {a b : ℝ}, a < b → InjOn γ (Ioo a b) →
    ∀ F : Set β, F.Finite → ∃ (k : ℕ) (node : Fin (k + 1) → ℝ),
      StrictMono node ∧ node 0 = a ∧ node (Fin.last k) = b ∧
      (∀ t ∈ Icc a b, γ t ∈ F → t ∈ Set.range node) ∧
      ∀ (j : Fin k) (t : ℝ),
        t ∈ Ioo (node j.castSucc) (node j.succ) → γ t ∉ F

/-- Regularity of the literal inserted curve, including both closed ends. -/
def inserted_curve_regular_neighborhood_type : Prop :=
  ∀ {U : Set ℂ} {J : Finset ℂ} {θ : ℂ → ℝ}
    {e : ℂ → OpenPartialHomeomorph ℂ ℂ} {R ε : ℝ} {L : ℝ≥0},
    UniformCharts U J θ e R L → 0 < ε → ε < R →
    ∀ {p : ℂ}, p ∈ J → ∃ T : Set ℝ,
      IsOpen T ∧ Icc (0 : ℝ) 1 ⊆ T ∧
      ContDiffOn ℝ 1 (fun t => (e p).symm (roundingArc ε (θ p) t)) T ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        deriv (fun s => (e p).symm (roundingArc ε (θ p) s)) t ≠ 0) ∧
      InjOn (fun t => (e p).symm (roundingArc ε (θ p) t)) (Icc (0 : ℝ) 1)

/-- The added parameter-speed bound is uniform over all sufficiently small
scales, including the empty join set. -/
def inserted_curves_total_speed_type : Prop :=
  ∀ {U : Set ℂ} {J : Finset ℂ} {θ : ℂ → ℝ}
    {e : ℂ → OpenPartialHomeomorph ℂ ℂ} {R : ℝ} {L : ℝ≥0},
    UniformCharts U J θ e R L →
    let C := (L : ℝ) * (∑ p ∈ J, (Real.pi / 2 + 6 * θ p)) + 1
    0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < R →
      (∀ p ∈ J, IntervalIntegrable
        (fun t => ‖deriv (fun s => (e p).symm (roundingArc ε (θ p) s)) t‖)
        volume 0 1) ∧
      (∑ p ∈ J, ∫ t in (0 : ℝ)..1,
        ‖deriv (fun s => (e p).symm (roundingArc ε (θ p) s)) t‖) ≤ C * ε

/-- The old model frontier within the closed tip is exactly the two closed
short rays. -/
def frontier_sector_inter_tip_type : Prop :=
  ∀ {ε θ : ℝ}, 0 < ε → 0 < θ → θ < 2 * Real.pi →
    frontier (sector θ) ∩ sectorTip ε θ = shortRays ε θ

/-- Exact removed model parameters include the vertex and exclude the two
new joins; mere image containment would not give this endpoint information. -/
def removed_sector_frontier_type : Prop :=
  ∀ {ε θ : ℝ}, 0 < ε → 0 < θ → θ < 2 * Real.pi →
    frontier (sector θ) \ frontier (roundedSector ε θ) =
      (fun r : ℝ => (r : ℂ)) '' Ico 0 ε ∪
      (fun r : ℝ => (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) '' Ico 0 ε

/-- The literal inserted curves have genuine local regular embedded extensions
through both new joins in the actual finite surgery. -/
def surgery_inserted_extensions_type : Prop :=
  ∀ {U : Set ℂ} {J : Finset ℂ} {θ : ℂ → ℝ}
    {e : ℂ → OpenPartialHomeomorph ℂ ℂ} {R : ℝ} {L : ℝ≥0},
    UniformCharts U J θ e R L → ∀ {ε : ℝ}, 0 < ε → ε < R →
    ∀ p ∈ J, HasLocalRegularExtensions (surgeryDomain U J e θ ε)
      (fun t => (e p).symm (roundingArc ε (θ p) t)) 0 1

/-- The exact global old-frontier removal for the literal finite surgery. -/
def chart_surgery_removed_frontier_type : Prop :=
  ∀ {U : Set ℂ} {J : Finset ℂ}
    (e : ℂ → OpenPartialHomeomorph ℂ ℂ) (θ : ℂ → ℝ) {ε : ℝ}, 0 < ε →
    (∀ p ∈ J, 0 < θ p ∧ θ p < 2 * Real.pi) →
    (∀ p ∈ J, (e p).IsImage U (sector (θ p))) →
    (∀ p ∈ J, ∀ q ∈ J, p ≠ q → Disjoint (e p).source (e q).source) →
    (∀ p ∈ J, sectorTip ε (θ p) ⊆ (e p).target) →
    frontier U \ frontier (surgeryDomain U J e θ ε) = ⋃ p ∈ J, (e p).symm ''
      ((fun r : ℝ => (r : ℂ)) '' Ico 0 ε ∪
        (fun r : ℝ => (r : ℂ) * Complex.exp ((θ p : ℂ) * Complex.I)) '' Ico 0 ε)

/-- Exact unsigned substitution compares derivatives only at interior points,
and permits either direction of a C1 parameter change. -/
def unsigned_speed_substitution_type : Prop :=
  ∀ {γ η : ℝ → ℂ} {φ : ℝ → ℝ} {a b lo hi : ℝ} {T S : Set ℝ},
    a ≤ b → lo ≤ hi → IsOpen T → ContDiffOn ℝ 1 φ T → Icc a b ⊆ T →
    IsOpen S → ContDiffOn ℝ 1 η S → Icc lo hi ⊆ S →
    ((MonotoneOn φ (Icc a b) ∧ φ a = lo ∧ φ b = hi) ∨
      (AntitoneOn φ (Icc a b) ∧ φ a = hi ∧ φ b = lo)) →
    EqOn γ (η ∘ φ) (Icc a b) →
    IntervalIntegrable (fun t => ‖deriv γ t‖) volume a b ∧
      (∫ t in a..b, ‖deriv γ t‖) = ∫ s in lo..hi, ‖deriv η s‖

/-- One deleted literal curve has length controlled by its radial interval,
once the actual monotone ray change has been constructed. -/
def deleted_curve_length_type : Prop :=
  ∀ {γ : ℝ → ℂ} {g : ℂ → ℂ} {φ : ℝ → ℝ}
    {a b lo hi ε R : ℝ} {ξ : ℂ} {L : ℝ≥0} {T : Set ℝ},
    a ≤ b → lo ≤ hi → 0 ≤ lo → hi ≤ 1 → 0 < ε → ε < R → ‖ξ‖ ≤ 1 →
    ContDiffOn ℝ 1 g (ball (0 : ℂ) R) →
    LipschitzOnWith L g (closedBall (0 : ℂ) R) →
    IsOpen T → ContDiffOn ℝ 1 φ T → Icc a b ⊆ T →
    ((MonotoneOn φ (Icc a b) ∧ φ a = lo ∧ φ b = hi) ∨
      (AntitoneOn φ (Icc a b) ∧ φ a = hi ∧ φ b = lo)) →
    (∀ t ∈ Icc a b, γ t = g ((ε * φ t) • ξ)) →
    IntervalIntegrable (fun t => ‖deriv γ t‖) volume a b ∧
      (∫ t in a..b, ‖deriv γ t‖) ≤ (L : ℝ) * ε * (hi - lo)

/-- Disjoint radial parameter intervals have total length at most one. The
measure here is ordinary one-dimensional parameter measure. -/
def finite_disjoint_interval_lengths_type : Prop :=
  ∀ {ι : Type*} (s : Finset ι) (lo hi : ι → ℝ),
    (∀ i ∈ s, 0 ≤ lo i) → (∀ i ∈ s, lo i ≤ hi i) → (∀ i ∈ s, hi i ≤ 1) →
    Set.PairwiseDisjoint (↑s) (fun i => Ioo (lo i) (hi i)) →
    (∑ i ∈ s, (hi i - lo i)) ≤ 1

/-- The actual supplied circular speed integral is radius times angular
length; no image-measure conversion is used. -/
def circle_speed_integral_type : Prop :=
  ∀ (c : ℂ) {r a b : ℝ}, 0 < r →
    (∫ t in a..b, ‖deriv (arcParam c r) t‖) = r * (b - a)

end Specs.D12Complex.Ch14.CircularSurgeryPartition
