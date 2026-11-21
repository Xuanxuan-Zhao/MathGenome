import MathGenome.Internal.RealAnalysis.Specs.D11.Ch11.StepDensity
import MathGenome.Internal.RealAnalysis.D11.Ch03.EuclideanRegularity
import MathGenome.Internal.RealAnalysis.D11.Ch11.FinitePSimpleDensity
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Topology.Algebra.Module.Basic

/-!
Rectangle step density for the completed Euclidean Lebesgue space.

Compact/open approximation gives measure-density of finite rectangle unions.
Inclusion-exclusion puts their indicators in the algebraic rectangle span;
Mathlib's measure-density lemma and Lp induction then give dense range of
that span in the ordinary quotient. Zero extension proves the restriction
statement, without adding any regularity assumption on the measurable domain.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology symmDiff
namespace D11.Ch11.StepDensity
open D11.Ch03 D11.Ch03.LebesgueMeasures

variable {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]

lemma rectangle_measurable (a b : Fin d → ℝ) :
    MeasurableSet[lebesgueSpace d] (rectangle a b) :=
  borel_le_lebesgue d _ (endpointBox_borel d a b (fun _ => true) (fun _ => false))

lemma rectangle_finite (a b : Fin d → ℝ) : lebesgue d (rectangle a b) ≠ ∞ := by
  change Specs.D11.Ch03.LebesgueMeasures.lebesgue_value d
    (endpointBox a b (fun _ => true) (fun _ => false)) ≠ ∞
  rw [lebesgue_box]
  exact ENNReal.prod_ne_top (fun _ _ => ENNReal.ofReal_ne_top)

lemma rectangle_inter (a b a' b' : Fin d → ℝ) :
    rectangle a b ∩ rectangle a' b' =
      rectangle (fun j => max (a j) (a' j)) (fun j => min (b j) (b' j)) := by
  ext x
  simp only [rectangle, endpointBox, ite_true, Bool.false_eq_true, ite_false,
    mem_inter_iff, mem_ofPred_eq, max_le_iff, lt_min_iff]
  constructor
  · rintro ⟨h, h'⟩ j
    exact ⟨⟨(h j).1, (h' j).1⟩, ⟨(h j).2, (h' j).2⟩⟩
  · intro h
    exact ⟨fun j => ⟨(h j).1.1, (h j).2.1⟩, fun j => ⟨(h j).1.2, (h j).2.2⟩⟩

lemma steps_memLp {p : ℝ≥0∞} {g : Point d → 𝕜}
    (hg : g ∈ rectangleSteps d 𝕜) :
    @MemLp _ _ (lebesgueSpace d) _ _ g p (lebesgue d) := by
  letI := lebesgueSpace d
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨a, b, c, rfl⟩ := hg
    exact memLp_indicator_const p (rectangle_measurable a b).nullMeasurableSet c
      (.inr (rectangle_finite a b))
  | zero => exact MemLp.zero
  | add f g _ _ hf hg => exact hf.add hg
  | smul c f _ hf => exact hf.const_smul c

/-- Inclusion-exclusion makes indicators of finite rectangle unions into
rectangle step functions, without requiring the rectangles to be disjoint. -/
lemma finite_union_mem {ι : Type*} (t : Finset ι) (a b : ι → Fin d → ℝ) (c : 𝕜) :
    ((⋃ i ∈ t, rectangle (a i) (b i)).indicator (fun _ => c)) ∈ rectangleSteps d 𝕜 := by
  classical
  induction t using Finset.induction_on generalizing a b with
  | empty =>
    convert (rectangleSteps d 𝕜).zero_mem using 1
    ext x
    simp
  | @insert i t hi ih =>
    have hrect : (rectangle (a i) (b i)).indicator (fun _ => c) ∈ rectangleSteps d 𝕜 :=
      Submodule.subset_span ⟨a i, b i, c, rfl⟩
    have hinter := ih (fun k j => max (a k j) (a i j))
      (fun k j => min (b k j) (b i j))
    have heq :
        (⋃ k ∈ insert i t, rectangle (a k) (b k)).indicator (fun _ => c) =
        (rectangle (a i) (b i)).indicator (fun _ => c) +
          (⋃ k ∈ t, rectangle (a k) (b k)).indicator (fun _ => c) -
          (⋃ k ∈ t, rectangle (fun j => max (a k j) (a i j))
            (fun j => min (b k j) (b i j))).indicator (fun _ => c) := by
      simp_rw [← rectangle_inter, ← iUnion_inter, Finset.set_biUnion_insert]
      ext x
      by_cases hx : x ∈ rectangle (a i) (b i) <;>
        by_cases hy : x ∈ ⋃ k ∈ t, rectangle (a k) (b k) <;>
        simp [Set.indicator, hx, hy]
    rw [heq]
    exact (rectangleSteps d 𝕜).sub_mem ((rectangleSteps d 𝕜).add_mem hrect (ih a b)) hinter

/-- The algebraic step functions, mapped to the ordinary Lp quotient. -/
def stepsToLp (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    rectangleSteps d 𝕜 →ₗ[𝕜] @Lp (Point d) 𝕜 (lebesgueSpace d) _ p (lebesgue d) where
  toFun g := (steps_memLp g.property).toLp g.val
  map_add' f g := by
    exact MemLp.toLp_add (steps_memLp f.property) (steps_memLp g.property)
  map_smul' c f := by
    exact MemLp.toLp_const_smul c (steps_memLp f.property)

/-- Each open neighborhood contains a half-open rectangle which is itself
a neighborhood of the chosen point. -/
lemma exists_rectangle_nhds {U : Set (Point d)} (hU : IsOpen U) {x : Point d} (hx : x ∈ U) :
    ∃ a b : Fin d → ℝ, rectangle a b ∈ 𝓝 x ∧ rectangle a b ⊆ U := by
  let e := EuclideanSpace.equiv (Fin d) ℝ
  have hV : IsOpen (e.symm ⁻¹' U) := hU.preimage e.symm.continuous
  obtain ⟨u, hu, hsub⟩ := isOpen_pi_iff'.mp hV (e x) (by simpa)
  have h j : ∃ l r : ℝ, e x j ∈ Ioo l r ∧ Ioo l r ⊆ u j :=
    mem_nhds_iff_exists_Ioo_subset.mp ((hu j).1.mem_nhds (hu j).2)
  choose l r hxr hinterval using h
  let a : Fin d → ℝ := fun j => (l j + x j) / 2
  refine ⟨a, r, ?_, ?_⟩
  · have hc (j : Fin d) : Continuous (fun y : Point d => y j) :=
      (EuclideanSpace.proj j).continuous
    have hopen : IsOpen {y : Point d | ∀ j, a j < y j ∧ y j < r j} := by
      simp only [ofPred_forall]
      apply isOpen_iInter_of_finite
      intro j
      exact (isOpen_lt continuous_const (hc j)).inter (isOpen_lt (hc j) continuous_const)
    apply mem_of_superset (hopen.mem_nhds ?_)
    · intro y hy j
      exact ⟨(hy j).1.le, (hy j).2⟩
    · intro j
      have hj := hxr j
      change l j < x j ∧ x j < r j at hj
      dsimp [a]
      exact ⟨by linarith [hj.1], hj.2⟩
  · intro y hy
    have hyu : e y ∈ univ.pi u := by
      intro j _
      apply hinterval j
      have hj := hxr j
      change l j < x j ∧ x j < r j at hj
      have hyj := hy j
      change a j ≤ y j ∧ y j < r j at hyj
      change l j < y j ∧ y j < r j
      exact ⟨by dsimp [a] at hyj; linarith [hj.1, hyj.1], hyj.2⟩
    simpa using hsub hyu

/-- A compact set in an open set admits a finite covering by bounded half-open
rectangles contained in the open set. -/
lemma compact_rectangle_cover {K U : Set (Point d)} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (t : Finset (Point d)) (a b : Point d → Fin d → ℝ),
      K ⊆ ⋃ i ∈ t, rectangle (a i) (b i) ∧
      (⋃ i ∈ t, rectangle (a i) (b i)) ⊆ U := by
  classical
  have h (x : K) := exists_rectangle_nhds hU (hKU x.property)
  choose a b hn hs using h
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun x : K => interior (rectangle (a x) (b x))) (fun _ => isOpen_interior)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.mpr (hn ⟨x, hx⟩)⟩)
  let a' : Point d → Fin d → ℝ := fun x => if hx : x ∈ K then a ⟨x, hx⟩ else 0
  let b' : Point d → Fin d → ℝ := fun x => if hx : x ∈ K then b ⟨x, hx⟩ else 0
  refine ⟨t.image Subtype.val, a', b', ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (ht hx)
    apply mem_iUnion₂.mpr
    refine ⟨y.val, Finset.mem_image.mpr ⟨y, hyt, rfl⟩, ?_⟩
    simpa [a', b', y.property] using interior_subset hxy
  · intro x hx
    obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp hx
    obtain ⟨z, hzt, rfl⟩ := Finset.mem_image.mp hyt
    apply hs z
    simpa [a', b', z.property] using hxy

/-- The family of finite unions used below is measure-dense for the completed
measure, including its non-Borel measurable sets. -/
def rectangleUnions (d : ℕ) : Set (Set (Point d)) :=
  {A | ∃ (t : Finset (Point d)) (a b : Point d → Fin d → ℝ),
    A = ⋃ i ∈ t, rectangle (a i) (b i)}

lemma unions_measurable {A : Set (Point d)} (hA : A ∈ rectangleUnions d) :
    MeasurableSet[lebesgueSpace d] A := by
  obtain ⟨t, a, b, rfl⟩ := hA
  exact MeasurableSet.biUnion t.countable_toSet (fun i _ => rectangle_measurable (a i) (b i))

lemma rectangleUnions_measureDense :
    @Measure.MeasureDense (Point d) (lebesgueSpace d) (lebesgue d) (rectangleUnions d) := by
  letI := lebesgueSpace d
  refine ⟨fun _ h => unions_measurable h, ?_⟩
  intro E hE hfin ε hε
  obtain ⟨K, U, hK, hKE, hEU, hU, herr⟩ :=
    EuclideanRegularity.compact_open_approximation d E hE hfin.lt_top ε hε
  obtain ⟨t, a, b, hKA, hAU⟩ := compact_rectangle_cover hK hU (hKE.trans hEU)
  refine ⟨⋃ i ∈ t, rectangle (a i) (b i), ⟨t, a, b, rfl⟩, ?_⟩
  apply (measure_mono (show E ∆ (⋃ i ∈ t, rectangle (a i) (b i)) ⊆ U \ K from ?_)).trans_lt herr
  intro x hx
  rcases hx with hx | hx
  · exact ⟨hEU hx.1, fun h => hx.2 (hKA h)⟩
  · exact ⟨hAU hx.1, fun h => hx.2 (hKE h)⟩

lemma union_indicator_mem {A : Set (Point d)} (hA : A ∈ rectangleUnions d) (c : 𝕜) :
    A.indicator (fun _ => c) ∈ rectangleSteps d 𝕜 := by
  obtain ⟨t, a, b, rfl⟩ := hA
  exact finite_union_mem t a b c

lemma stepsToLp_denseRange (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    DenseRange (stepsToLp (d := d) (𝕜 := 𝕜) p) := by
  letI := lebesgueSpace d
  letI : Fact (p ≠ ∞) := ⟨hp⟩
  let S := (stepsToLp (d := d) (𝕜 := 𝕜) p).range
  have hind (c : 𝕜) {A : Set (Point d)} (hA : MeasurableSet A)
      (hfin : lebesgue d A ≠ ∞) : indicatorConstLp p hA hfin c ∈ S.topologicalClosure := by
    have hclosure := rectangleUnions_measureDense.indicatorConstLp_subset_closure p c
      (show indicatorConstLp p hA hfin c ∈
        {indicatorConstLp p hs hμs c | (s : Set (Point d))
          (hs : MeasurableSet s) (hμs : lebesgue d s ≠ ∞)} from ⟨A, hA, hfin, rfl⟩)
    apply closure_minimal ?_ S.isClosed_topologicalClosure hclosure
    rintro _ ⟨A, hA, hfin, rfl⟩
    apply S.le_topologicalClosure
    exact ⟨⟨A.indicator (fun _ => c), union_indicator_mem hA c⟩, rfl⟩
  have hall : ∀ f : Lp 𝕜 p (lebesgue d), f ∈ S.topologicalClosure := by
    apply Lp.induction hp (fun f => f ∈ S.topologicalClosure)
    · intro c A hA hfin
      exact hind c hA hfin.ne
    · intro f g hf hg _ hfm hgm
      exact S.topologicalClosure.add_mem hfm hgm
    · exact S.isClosed_topologicalClosure
  intro f
  exact hall f

/-- Density in the ordinary quotient of the completed Lebesgue space. -/
theorem step_density : Specs.D11.Ch11.StepDensity.step_density := by
  intro d _ 𝕜 _ _ _ p _ hp
  letI := lebesgueSpace d
  intro f ε hε
  change Lp 𝕜 p (lebesgue d) at f
  obtain ⟨g, hg⟩ := (stepsToLp_denseRange (d := d) (𝕜 := 𝕜) p hp).exists_dist_lt f hε
  refine ⟨g.val, g.property, steps_memLp g.property, ?_⟩
  rw [dist_eq_norm] at hg
  exact hg

/-- Zero extension and restriction give density on every measurable domain;
in dimension one these are the asserted finite-interval step functions. -/
theorem restricted_step_density : Specs.D11.Ch11.StepDensity.restricted_step_density := by
  intro d _ 𝕜 _ _ _ p _ hp
  letI := lebesgueSpace d
  intro I hI f ε hε
  change MeasurableSet I at hI
  change Lp 𝕜 p ((lebesgue d).restrict I) at f
  have hf : MemLp (I.indicator (f : Point d → 𝕜)) p (lebesgue d) :=
    (memLp_indicator_iff_restrict hI.nullMeasurableSet).mpr (Lp.memLp f)
  obtain ⟨g, hg, hgp, herr⟩ := step_density d 𝕜 p hp (hf.toLp _) ε hε
  change MemLp g p (lebesgue d) at hgp
  change ‖hf.toLp _ - hgp.toLp g‖ < ε at herr
  refine ⟨g, hg, hgp.restrict I, ?_⟩
  have herr' : eLpNorm (I.indicator (f : Point d → 𝕜) - g) p (lebesgue d) < ENNReal.ofReal ε := by
    rw [← MemLp.toLp_sub hf hgp, Lp.norm_toLp] at herr
    exact (ENNReal.toReal_lt_toReal (hf.sub hgp).eLpNorm_ne_top ENNReal.ofReal_ne_top).mp
      (by simpa [ENNReal.toReal_ofReal hε.le] using herr)
  have heq : f - g =ᵐ[(lebesgue d).restrict I]
      I.indicator (f : Point d → 𝕜) - g := by
    filter_upwards [ae_restrict_mem hI] with x hx
    simp [Set.indicator_of_mem hx]
  have hbound : eLpNorm ((f : Point d → 𝕜) - g) p ((lebesgue d).restrict I) < ENNReal.ofReal ε :=
    (eLpNorm_congr_ae heq).trans_lt
      ((eLpNorm_restrict_le _ _ _ _).trans_lt herr')
  change ‖f - (hgp.restrict I).toLp g‖ < ε
  rw [← Lp.toLp_coeFn f (Lp.memLp f), ← MemLp.toLp_sub, Lp.norm_toLp]
  exact (ENNReal.toReal_lt_toReal (ne_top_of_lt hbound) ENNReal.ofReal_ne_top).mpr hbound |>.trans_eq
    (ENNReal.toReal_ofReal hε.le)

end D11.Ch11.StepDensity
