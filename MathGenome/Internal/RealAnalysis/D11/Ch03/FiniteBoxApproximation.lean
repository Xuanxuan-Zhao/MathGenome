import MathGenome.Internal.RealAnalysis.D11.Ch03.EuclideanRegularity
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.FiniteBoxApproximation
import Mathlib.Analysis.BoxIntegral.Partition.Split

noncomputable section
open Set MeasureTheory BoxIntegral
open scoped ENNReal symmDiff Topology

namespace D11.Ch03.FiniteBoxApproximation

/-- A finite union of bounded half-open boxes admits an exact disjoint
refinement, by cutting at all coordinate faces. -/
theorem disjoint_refinement {ι : Type*} [Fintype ι] (s : Finset (Box ι)) :
    ∃ t : Finset (Box ι),
      (t : Set (Box ι)).PairwiseDisjoint (fun J => (J : Set (ι → ℝ))) ∧
      (⋃ J ∈ t, (J : Set (ι → ℝ))) = ⋃ J ∈ s, (J : Set (ι → ℝ)) := by
  classical
  let I : Box ι := (insert default s).sup' (Finset.insert_nonempty _ _) id
  have hJI (J : Box ι) (hJ : J ∈ s) : J ≤ I :=
    Finset.le_sup' id (Finset.mem_insert_of_mem hJ)
  obtain ⟨cuts, hcuts⟩ :=
    (Prepartition.eventually_not_disjoint_imp_le_of_mem_splitMany s).exists
  let π := Prepartition.splitMany I cuts
  let V : Set (ι → ℝ) := ⋃ J ∈ s, (J : Set (ι → ℝ))
  let ρ := π.filter (fun J => (J : Set (ι → ℝ)) ⊆ V)
  refine ⟨ρ.boxes, ρ.pairwiseDisjoint, ?_⟩
  change ρ.iUnion = V
  apply Subset.antisymm
  · intro x hx
    obtain ⟨J, hJ, hxJ⟩ := ρ.mem_iUnion.mp hx
    exact (π.mem_filter.mp hJ).2 hxJ
  · intro x hx
    obtain ⟨J, hJ, hxJ⟩ := mem_iUnion₂.mp hx
    have hxI : x ∈ I := hJI J hJ hxJ
    have hxπ : x ∈ π.iUnion := by
      simpa only [π, Prepartition.iUnion_splitMany, Box.mem_coe] using hxI
    obtain ⟨J', hJ', hxJ'⟩ := π.mem_iUnion.mp hxπ
    have hle : J' ≤ J := hcuts I J hJ J' hJ'
      (Box.not_disjoint_coe_iff_nonempty_inter.mpr ⟨x, hxJ, hxJ'⟩)
    exact ρ.mem_iUnion.mpr ⟨J', π.mem_filter.mpr ⟨hJ',
      fun y hy => mem_iUnion₂.mpr ⟨J, hJ, hle hy⟩⟩, hxJ'⟩

/-- Compact sets inside open sets can be sandwiched by finite disjoint
unions of half-open boxes. This assertion uses only finite-dimensional topology. -/
theorem boxes_between {ι : Type*} [Fintype ι] {K U : Set (ι → ℝ)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ s : Finset (Box ι),
      (s : Set (Box ι)).PairwiseDisjoint (fun J => (J : Set (ι → ℝ))) ∧
      K ⊆ ⋃ J ∈ s, (J : Set (ι → ℝ)) ∧
      (⋃ J ∈ s, (J : Set (ι → ℝ))) ⊆ U := by
  classical
  have hlocal (x : U) : ∃ J : Box ι,
      x.val ∈ interior (J : Set (ι → ℝ)) ∧ (J : Set (ι → ℝ)) ⊆ U := by
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x.val x.property
    let J : Box ι := ⟨fun i => x.val i - r / 2, fun i => x.val i + r / 2,
      fun i => by linarith⟩
    refine ⟨J, ?_, ?_⟩
    · apply mem_interior_iff_mem_nhds.mpr
      apply Filter.mem_of_superset
        ((isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)).mem_nhds
          (show x.val ∈ pi univ (fun i => Ioo (J.lower i) (J.upper i)) from
            fun i _ => ⟨by dsimp [J]; linarith, by dsimp [J]; linarith⟩))
      intro y hy i
      exact ⟨(hy i (mem_univ i)).1, (hy i (mem_univ i)).2.le⟩
    · intro y hy
      apply hball
      apply (dist_pi_lt_iff hr).mpr
      intro i
      rw [Real.dist_eq, abs_lt]
      have hi := hy i
      change x.val i - r / 2 < y i ∧ y i ≤ x.val i + r / 2 at hi
      constructor <;> linarith
  choose J hJint hJU using hlocal
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : U => interior (J x : Set (ι → ℝ)))
    (fun _ => isOpen_interior) (fun x hx => mem_iUnion.mpr ⟨⟨x, hKU hx⟩, hJint _⟩)
  let t := s.image J
  have hKt : K ⊆ ⋃ B ∈ t, (B : Set (ι → ℝ)) := by
    intro x hx
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion₂.mpr ⟨J u, Finset.mem_image.mpr ⟨u, hu, rfl⟩, interior_subset hxu⟩
  have htU : (⋃ B ∈ t, (B : Set (ι → ℝ))) ⊆ U := by
    intro x hx
    obtain ⟨B, hB, hxB⟩ := mem_iUnion₂.mp hx
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hB
    exact hJU u hxB
  obtain ⟨v, hv, heq⟩ := disjoint_refinement t
  exact ⟨v, hv, heq ▸ hKt, heq ▸ htU⟩

/-- The symmetric difference of two sets between K and U lies in U \ K. -/
theorem symmDiff_subset_sdiff_of_between {α : Type*} {K E V U : Set α}
    (hKE : K ⊆ E) (hEU : E ⊆ U) (hKV : K ⊆ V) (hVU : V ⊆ U) :
    E ∆ V ⊆ U \ K := by
  intro x hx
  rcases hx with h | h
  · exact ⟨hEU h.1, fun hxK => h.2 (hKV hxK)⟩
  · exact ⟨hVU h.1, fun hxK => h.2 (hKE hxK)⟩

/-- Finite disjoint box approximation of every finite-measure Lebesgue set. -/
theorem finite_box_approximation :
    Specs.D11.Ch03.FiniteBoxApproximation.finite_box_approximation := by
  classical
  intro d _ E hE hfin ε hε
  obtain ⟨K, U, hK, hKE, hEU, hU, herr⟩ :=
    EuclideanRegularity.compact_open_approximation d E hE hfin ε hε
  let e : Point d ≃ₜ (Fin d → ℝ) := (EuclideanSpace.equiv (Fin d) ℝ).toHomeomorph
  obtain ⟨s, hsdis, hKs, hsU⟩ := boxes_between
    (hK.image e.continuous) (e.isOpenMap U hU) (image_mono (hKE.trans hEU))
  let B : Box (Fin d) → Set (Point d) := fun J => e ⁻¹' (J : Set (Fin d → ℝ))
  let S : Finset (Set (Point d)) := s.image B
  have hbetween : K ⊆ ⋃₀ (S : Set (Set (Point d))) ∧
      (⋃₀ (S : Set (Set (Point d)))) ⊆ U := by
    constructor
    · intro x hx
      obtain ⟨J, hJ, hxJ⟩ := mem_iUnion₂.mp (hKs (mem_image_of_mem e hx))
      exact mem_sUnion.mpr ⟨B J, Finset.mem_image.mpr ⟨J, hJ, rfl⟩, hxJ⟩
    · intro x hx
      obtain ⟨_, hB, hxB⟩ := mem_sUnion.mp hx
      obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hB
      have hxU := hsU (mem_iUnion₂.mpr ⟨J, hJ, hxB⟩)
      exact e.injective.mem_set_image.mp hxU
  refine ⟨S, ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨J, _, rfl⟩ := Finset.mem_image.mp hC
    refine ⟨J.lower, J.upper, (fun _ => false), (fun _ => true), ?_⟩
    rfl
  · intro C hC D hD hCD
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨J', hJ', rfl⟩ := Finset.mem_image.mp hD
    have hne : J ≠ J' := fun h => hCD (congrArg B h)
    exact (hsdis hJ hJ' hne).preimage e
  · let : MeasurableSpace (Point d) := LebesgueMeasures.lebesgueSpace d
    exact (measure_mono (symmDiff_subset_sdiff_of_between hKE hEU
      hbetween.1 hbetween.2)).trans_lt herr

end D11.Ch03.FiniteBoxApproximation
