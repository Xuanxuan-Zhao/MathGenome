import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.Sequential
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.LimitAlgebra
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.Algebra

/-!
K03.02.algebra. The five approach-region predicates form a filter: take the
smaller radius at finite endpoints, and the larger threshold at infinity.
Its eventual predicates are definitionally the upstream ApproachEventually.
The epsilon characterization of Tendsto then transports the usual normed-field
limit laws. Nontriviality is retained in every FiniteApproachLimit conclusion.
For composition the map lands in D, so relative continuity suffices. The
punctured version uses eventual avoidance to land in D minus {b}.
Library provenance: Mathlib topological field operations and norm continuity;
no subsequent continuity chapter of this project is used as a prerequisite.
-/
namespace SingleVariableAnalysis
open scoped Topology
universe u v w

private theorem commonApproachRegion (q : RealApproach) (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) :
    ∃ t : ℝ, 0 < t ∧ ∀ x, x ∈ ApproachRegion q t →
      x ∈ ApproachRegion q r ∧ x ∈ ApproachRegion q s := by
  cases q with
  | punctured a =>
    refine ⟨min r s, lt_min hr hs, fun x hx => ?_⟩
    exact ⟨⟨hx.1, hx.2.trans_le (min_le_left _ _)⟩,
      ⟨hx.1, hx.2.trans_le (min_le_right _ _)⟩⟩
  | right a =>
    refine ⟨min r s, lt_min hr hs, fun x hx => ?_⟩
    change a < x ∧ x < a + min r s at hx
    change (a < x ∧ x < a + r) ∧ (a < x ∧ x < a + s)
    have h1 := min_le_left r s
    have h2 := min_le_right r s
    exact ⟨⟨hx.1, by linarith [hx.2]⟩, ⟨hx.1, by linarith [hx.2]⟩⟩
  | left a =>
    refine ⟨min r s, lt_min hr hs, fun x hx => ?_⟩
    change a - min r s < x ∧ x < a at hx
    change (a - r < x ∧ x < a) ∧ (a - s < x ∧ x < a)
    have h1 := min_le_left r s
    have h2 := min_le_right r s
    exact ⟨⟨by linarith [hx.1], hx.2⟩, ⟨by linarith [hx.1], hx.2⟩⟩
  | posInfinity =>
    refine ⟨max r s, hr.trans_le (le_max_left _ _), fun x hx => ?_⟩
    exact ⟨(le_max_left r s).trans_lt hx, (le_max_right r s).trans_lt hx⟩
  | negInfinity =>
    refine ⟨max r s, hr.trans_le (le_max_left _ _), fun x hx => ?_⟩
    change x < -(max r s) at hx
    change x < -r ∧ x < -s
    constructor <;> linarith [le_max_left r s, le_max_right r s]

/-- Intersect two eventual conditions along exactly the same approach. -/
theorem approachEventually_and {E : Set ℝ} {q : RealApproach} {P Q : ℝ → Prop}
    (hP : ApproachEventually E q P) (hQ : ApproachEventually E q Q) :
    ApproachEventually E q (fun x => P x ∧ Q x) := by
  obtain ⟨r, hr, hPr⟩ := hP
  obtain ⟨s, hs, hQs⟩ := hQ
  obtain ⟨t, ht, hb⟩ := commonApproachRegion q r s hr hs
  exact ⟨t, ht, fun x hx hxt => ⟨hPr x hx (hb x hxt).1, hQs x hx (hb x hxt).2⟩⟩

private def algebraApproachFilter (E : Set ℝ) (q : RealApproach) : Filter ℝ where
  sets := {s | ApproachEventually E q (fun x => x ∈ s)}
  univ_sets := ⟨1, zero_lt_one, fun _ _ _ => Set.mem_univ _⟩
  sets_of_superset := by
    rintro s t ⟨r, hr, hb⟩ hst
    exact ⟨r, hr, fun x hx hxr => hst (hb x hx hxr)⟩
  inter_sets := fun hP hQ => approachEventually_and hP hQ

private theorem approachLimit_filter_iff {Y : Type u} [MetricSpace Y]
    (f : ℝ → Y) (E : Set ℝ) (q : RealApproach) (L : Y) :
    FiniteApproachLimit f E q L ↔ ApproachNontrivial E q ∧
      Filter.Tendsto f (algebraApproachFilter E q) (𝓝 L) := by
  rw [Metric.tendsto_nhds]
  rfl

theorem finiteApproachLimit_linear_combination {K : Type u} [NormedField K]
    (f g : ℝ → K) (E : Set ℝ) (q : RealApproach) (A B : K) (c d : K)
    (hf : FiniteApproachLimit f E q A) (hg : FiniteApproachLimit g E q B) :
    FiniteApproachLimit (fun x => c * f x + d * g x) E q (c * A + d * B) := by
  have hfT := ((approachLimit_filter_iff f E q A).mp hf).2
  have hgT := ((approachLimit_filter_iff g E q B).mp hg).2
  exact (approachLimit_filter_iff _ E q _).mpr ⟨hf.1, ((hfT.const_mul c).add (hgT.const_mul d))⟩

theorem finiteApproachLimit_mul {K : Type u} [NormedField K]
    (f g : ℝ → K) (E : Set ℝ) (q : RealApproach) (A B : K)
    (hf : FiniteApproachLimit f E q A) (hg : FiniteApproachLimit g E q B) :
    FiniteApproachLimit (fun x => f x * g x) E q (A * B) := by
  have hfT := ((approachLimit_filter_iff f E q A).mp hf).2
  have hgT := ((approachLimit_filter_iff g E q B).mp hg).2
  exact (approachLimit_filter_iff _ E q _).mpr ⟨hf.1, (hfT.mul hgT)⟩

theorem finiteApproachLimit_div {K : Type u} [NormedField K]
    (f g : ℝ → K) (E : Set ℝ) (q : RealApproach) (A B : K)
    (hf : FiniteApproachLimit f E q A) (hg : FiniteApproachLimit g E q B) (hB : B ≠ 0) :
    FiniteApproachLimit (fun x => f x / g x) E q (A / B) := by
  have hfT := ((approachLimit_filter_iff f E q A).mp hf).2
  have hgT := ((approachLimit_filter_iff g E q B).mp hg).2
  exact (approachLimit_filter_iff _ E q _).mpr ⟨hf.1, (hfT.div hgT hB)⟩

theorem finiteApproachLimit_norm {K : Type u} [NormedField K]
    (f : ℝ → K) (E : Set ℝ) (q : RealApproach) (A : K)
    (hf : FiniteApproachLimit f E q A) :
    FiniteApproachLimit (fun x => ‖f x‖) E q ‖A‖ := by
  exact (approachLimit_filter_iff _ E q _).mpr
    ⟨hf.1, ((approachLimit_filter_iff f E q A).mp hf).2.norm⟩

theorem finiteApproachLimit_abs (f : ℝ → ℝ) (E : Set ℝ) (q : RealApproach) (A : ℝ)
    (hf : FiniteApproachLimit f E q A) :
    FiniteApproachLimit (fun x => |f x|) E q |A| := by
  simpa only [Real.norm_eq_abs] using finiteApproachLimit_norm f E q A hf

theorem finiteApproachLimit_eventually_ne_zero {K : Type u} [NormedField K]
    (g : ℝ → K) (E : Set ℝ) (q : RealApproach) (B : K)
    (hg : FiniteApproachLimit g E q B) (hB : B ≠ 0) :
    ApproachEventually E q (fun x => g x ≠ 0) := by
  exact ((approachLimit_filter_iff g E q B).mp hg).2.eventually_ne hB

theorem finiteApproachLimit_comp_continuousWithinAt {Y : Type u} {Z : Type v} [MetricSpace Y] [MetricSpace Z]
    (f : ℝ → Y) (g : Y → Z) (E : Set ℝ) (D : Set Y) (q : RealApproach) (b : Y)
    (hb : b ∈ D) (hmap : Set.MapsTo f E D)
    (hf : FiniteApproachLimit f E q b) (hg : ContinuousWithinAt g D b) :
    FiniteApproachLimit (fun x => g (f x)) E q (g b) := by
  refine ⟨hf.1, fun ε hε => ?_⟩
  obtain ⟨η, hη, hgη⟩ := Metric.continuousWithinAt_iff.mp hg ε hε
  obtain ⟨r, hr, hfr⟩ := hf.2 η hη
  exact ⟨r, hr, fun x hx hxr => hgη (hmap hx) (hfr x hx hxr)⟩

theorem finiteApproachLimit_comp_punctured {Y : Type u} {Z : Type v} [MetricSpace Y] [MetricSpace Z]
    (f : ℝ → Y) (g : Y → Z) (E : Set ℝ) (D : Set Y) (q : RealApproach) (b : Y) (C : Z)
    (hmap : Set.MapsTo f E D) (hf : FiniteApproachLimit f E q b)
    (hg : RelativePuncturedLimit g D b C)
    (havoid : ApproachEventually E q (fun x => f x ≠ b)) :
    FiniteApproachLimit (fun x => g (f x)) E q C := by
  refine ⟨hf.1, fun ε hε => ?_⟩
  obtain ⟨η, hη, hgη⟩ := hg ε hε
  obtain ⟨r, hr, hb⟩ := approachEventually_and (hf.2 η hη) havoid
  exact ⟨r, hr, fun x hx hxr => hgη (f x) (hmap hx)
    (dist_pos.mpr (hb x hx hxr).2) (hb x hx hxr).1⟩

theorem relativePuncturedLimit_linear_combination {X : Type u} {K : Type v} [MetricSpace X] [NormedField K]
    (f g : X → K) (E : Set X) (a : X) (A B : K) (c d : K)
    (ha : DomainAccumulation E a)
    (hf : RelativePuncturedLimit f E a A) (hg : RelativePuncturedLimit g E a B) :
    RelativePuncturedLimit (fun x => c * f x + d * g x) E a (c * A + d * B) := by
  have hfT := (relativePuncturedLimit_filter_iff f E a A).mp hf
  have hgT := (relativePuncturedLimit_filter_iff g E a B).mp hg
  exact (relativePuncturedLimit_filter_iff _ E a _).mpr ((hfT.const_mul c).add (hgT.const_mul d))

theorem relativePuncturedLimit_mul {X : Type u} {K : Type v} [MetricSpace X] [NormedField K]
    (f g : X → K) (E : Set X) (a : X) (A B : K)
    (ha : DomainAccumulation E a)
    (hf : RelativePuncturedLimit f E a A) (hg : RelativePuncturedLimit g E a B) :
    RelativePuncturedLimit (fun x => f x * g x) E a (A * B) := by
  have hfT := (relativePuncturedLimit_filter_iff f E a A).mp hf
  have hgT := (relativePuncturedLimit_filter_iff g E a B).mp hg
  exact (relativePuncturedLimit_filter_iff _ E a _).mpr (hfT.mul hgT)

theorem relativePuncturedLimit_div {X : Type u} {K : Type v} [MetricSpace X] [NormedField K]
    (f g : X → K) (E : Set X) (a : X) (A B : K)
    (ha : DomainAccumulation E a)
    (hf : RelativePuncturedLimit f E a A) (hg : RelativePuncturedLimit g E a B) (hB : B ≠ 0) :
    RelativePuncturedLimit (fun x => f x / g x) E a (A / B) := by
  have hfT := (relativePuncturedLimit_filter_iff f E a A).mp hf
  have hgT := (relativePuncturedLimit_filter_iff g E a B).mp hg
  exact (relativePuncturedLimit_filter_iff _ E a _).mpr (hfT.div hgT hB)

theorem relativePuncturedLimit_norm {X : Type u} {K : Type v} [MetricSpace X] [NormedField K]
    (f : X → K) (E : Set X) (a : X) (A : K) (ha : DomainAccumulation E a)
    (hf : RelativePuncturedLimit f E a A) :
    RelativePuncturedLimit (fun x => ‖f x‖) E a ‖A‖ := by
  exact (relativePuncturedLimit_filter_iff _ E a _).mpr
    ((relativePuncturedLimit_filter_iff f E a A).mp hf).norm

theorem relativePuncturedLimit_abs {X : Type u} [MetricSpace X]
    (f : X → ℝ) (E : Set X) (a : X) (A : ℝ) (ha : DomainAccumulation E a)
    (hf : RelativePuncturedLimit f E a A) :
    RelativePuncturedLimit (fun x => |f x|) E a |A| := by
  simpa only [Real.norm_eq_abs] using relativePuncturedLimit_norm f E a A ha hf

theorem relativePuncturedLimit_eventually_ne_zero {X : Type u} {K : Type v} [MetricSpace X] [NormedField K]
    (g : X → K) (E : Set X) (a : X) (B : K) (ha : DomainAccumulation E a)
    (hg : RelativePuncturedLimit g E a B) (hB : B ≠ 0) :
    ∀ᶠ x in PuncturedDomainFilter E a, g x ≠ 0 := by
  exact ((relativePuncturedLimit_filter_iff g E a B).mp hg).eventually_ne hB

theorem relativePuncturedLimit_comp_continuousWithinAt {X : Type u} {Y : Type v} {Z : Type w}
    [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
    (f : X → Y) (g : Y → Z) (E : Set X) (D : Set Y) (a : X) (b : Y)
    (ha : DomainAccumulation E a) (hb : b ∈ D) (hmap : Set.MapsTo f E D)
    (hf : RelativePuncturedLimit f E a b) (hg : ContinuousWithinAt g D b) :
    RelativePuncturedLimit (fun x => g (f x)) E a (g b) := by
  intro ε hε
  obtain ⟨η, hη, hgη⟩ := Metric.continuousWithinAt_iff.mp hg ε hε
  obtain ⟨δ, hδ, hfδ⟩ := hf η hη
  exact ⟨δ, hδ, fun x hx hpos hdist => hgη (hmap hx) (hfδ x hx hpos hdist)⟩

theorem relativePuncturedLimit_comp_punctured {X : Type u} {Y : Type v} {Z : Type w}
    [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
    (f : X → Y) (g : Y → Z) (E : Set X) (D : Set Y) (a : X) (b : Y) (C : Z)
    (ha : DomainAccumulation E a) (hmap : Set.MapsTo f E D)
    (hf : RelativePuncturedLimit f E a b) (hg : RelativePuncturedLimit g D b C)
    (havoid : ∀ᶠ x in PuncturedDomainFilter E a, f x ≠ b) :
    RelativePuncturedLimit (fun x => g (f x)) E a C := by
  apply (relativePuncturedLimit_filter_iff _ E a _).mpr
  have hfT := (relativePuncturedLimit_filter_iff f E a b).mp hf
  have hD : ∀ᶠ x in PuncturedDomainFilter E a, f x ∈ D := by
    have hE : ∀ᶠ x in PuncturedDomainFilter E a, x ∈ E := by
      change ∀ᶠ x in nhdsWithin a (E \ {a}), x ∈ E
      exact Filter.mem_of_superset self_mem_nhdsWithin (fun x hx => hx.1)
    exact hE.mono (fun _ hx => hmap hx)
  have hwithin : Filter.Tendsto f (PuncturedDomainFilter E a) (nhdsWithin b (D \ {b})) :=
    tendsto_nhdsWithin_iff.mpr ⟨hfT, (hD.and havoid).mono (fun x hx => ⟨hx.1, hx.2⟩)⟩
  exact ((relativePuncturedLimit_filter_iff g D b C).mp hg).comp hwithin

end SingleVariableAnalysis
