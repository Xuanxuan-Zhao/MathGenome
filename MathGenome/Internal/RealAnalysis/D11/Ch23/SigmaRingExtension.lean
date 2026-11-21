import MathGenome.Internal.RealAnalysis.D11.Ch23.SigmaRingInterfaces
import MathGenome.Internal.RealAnalysis.D11.Ch01.MeasureDefinitions
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.SigmaRingExtension

/-!
# Extending a measure from a sigma-ring

The generated sigma-algebra consists of ring sets and their complements.
A measurable subset of a ring set is itself in the ring. Thus a disjoint union
in the ring has all its members in the ring, and the original additivity law
applies. A union outside the ring has an outside member, giving an infinite
term in the extended sum. These arguments include infinite masses and empty X.
-/

open Set MeasureTheory
open scoped ENNReal
universe u

namespace D11.Ch23

namespace SigmaRing
variable {X : Type u} (R : SigmaRing X)

/-- Finite intersections require no whole-space member. -/
theorem inter_mem {A B : Set X} (hA : A ∈ R) (hB : B ∈ R) : A ∩ B ∈ R := by
  have h : A ∩ B = A \ (A \ B) := by
    ext x
    simp only [mem_inter_iff, mem_sdiff]
    tauto
  rw [h]
  exact R.diff_mem hA (R.diff_mem hA hB)

/-- Ring sets and complements of ring sets form a sigma-algebra. -/
private theorem iUnion_mem_or_compl (A : ℕ → Set X)
    (hA : ∀ n, A n ∈ R ∨ (A n)ᶜ ∈ R) :
    (⋃ n, A n) ∈ R ∨ (⋃ n, A n)ᶜ ∈ R := by
  classical
  by_cases h : ∀ n, A n ∈ R
  · exact Or.inl (R.iUnion_mem A h)
  · obtain ⟨k, hk⟩ := not_forall.mp h
    have hC : (A k)ᶜ ∈ R := (hA k).resolve_left hk
    have hI : ∀ n, (A k)ᶜ ∩ A n ∈ R := by
      intro n
      rcases hA n with hn | hn
      · exact R.inter_mem hC hn
      · have heq : (A k)ᶜ ∩ A n = (A k)ᶜ \ (A n)ᶜ := by
          simp only [sdiff_compl]
        rw [heq]
        exact R.diff_mem hC hn
    have heq : (⋃ n, A n)ᶜ = (A k)ᶜ \ ⋃ n, (A k)ᶜ ∩ A n := by
      ext x
      simp only [mem_compl_iff, mem_iUnion, mem_sdiff, mem_inter_iff]
      constructor
      · intro hx
        exact ⟨fun hxk => hx ⟨k, hxk⟩, fun ⟨n, _, hxn⟩ => hx ⟨n, hxn⟩⟩
      · rintro ⟨hxk, hx⟩ ⟨n, hn⟩
        exact hx ⟨n, hxk, hn⟩
    exact Or.inr (heq ▸ R.diff_mem hC (R.iUnion_mem _ hI))

/-- Membership characterization of the generated sigma-algebra. -/
theorem measurableSet_generateFrom_iff (A : Set X) :
    MeasurableSet[MeasurableSpace.generateFrom (R : Set (Set X))] A ↔
      A ∈ R ∨ Aᶜ ∈ R := by
  constructor
  · intro hA
    induction hA with
    | basic A hA => exact Or.inl hA
    | empty => exact Or.inl R.empty_mem
    | compl A _ ih => simpa only [compl_compl, or_comm] using ih
    | iUnion A _ ih => exact R.iUnion_mem_or_compl A ih
  · rintro (hA | hA)
    · exact MeasurableSpace.measurableSet_generateFrom hA
    · simpa only [compl_compl] using
        (MeasurableSpace.measurableSet_generateFrom hA).compl

/-- The displayed set-family equality in the manuscript. -/
theorem generated_domain :
    {A : Set X | MeasurableSet[MeasurableSpace.generateFrom (R : Set (Set X))] A} =
      (R : Set (Set X)) ∪ {A : Set X | ∃ B ∈ R, A = Bᶜ} := by
  ext A
  rw [mem_ofPred_eq, R.measurableSet_generateFrom_iff]
  constructor
  · rintro (hA | hA)
    · exact Or.inl hA
    · exact Or.inr ⟨Aᶜ, hA, (compl_compl A).symm⟩
  · rintro (hA | ⟨B, hB, rfl⟩)
    · exact Or.inl hA
    · exact Or.inr (by simpa only [compl_compl] using hB)

/-- Subsets here must be measurable; arbitrary subsets need not lie in R. -/
theorem mem_of_measurable_subset {A B : Set X}
    (hA : MeasurableSet[MeasurableSpace.generateFrom (R : Set (Set X))] A)
    (hB : B ∈ R) (hAB : A ⊆ B) : A ∈ R := by
  rcases (R.measurableSet_generateFrom_iff A).mp hA with h | h
  · exact h
  · have heq : A = B \ Aᶜ := by
      ext x
      simp only [mem_sdiff, mem_compl_iff, not_not]
      exact ⟨fun hx => ⟨hAB hx, hx⟩, fun hx => hx.2⟩
    rw [heq]
    exact R.diff_mem hB h

end SigmaRing

namespace SigmaRingMeasure
variable {X : Type u} (R : SigmaRing X) (μ : SigmaRingMeasure R)

/-- The displayed extension formula, to be used on the generated domain. -/
noncomputable def extensionMass (A : Set X) : ℝ≥0∞ := by
  classical
  exact if h : A ∈ R then μ ⟨A, h⟩ else ∞

@[simp]
theorem extensionMass_of_mem {A : Set X} (h : A ∈ R) :
    extensionMass R μ A = μ ⟨A, h⟩ := by
  classical
  simp only [extensionMass, dite_eq_left h]

@[simp]
theorem extensionMass_of_not_mem {A : Set X} (h : A ∉ R) :
    extensionMass R μ A = ∞ := by
  classical
  simp only [extensionMass, dite_eq_right h]

theorem extension_empty : extensionMass R μ ∅ = 0 := by
  rw [extensionMass_of_mem R μ R.empty_mem]
  exact μ.empty'

/-- Both the finite and infinite cases of countable additivity. -/
theorem extension_countably_additive (A : ℕ → Set X)
    (hA : ∀ n, MeasurableSet[MeasurableSpace.generateFrom (R : Set (Set X))] (A n))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) :
    extensionMass R μ (⋃ n, A n) = ∑' n, extensionMass R μ (A n) := by
  classical
  by_cases hU : (⋃ n, A n) ∈ R
  · have hR : ∀ n, A n ∈ R :=
      fun n => R.mem_of_measurable_subset (hA n) hU (subset_iUnion A n)
    rw [extensionMass_of_mem R μ hU, μ.iUnion' A hR hd]
    exact tsum_congr (fun n => (extensionMass_of_mem R μ (hR n)).symm)
  · have hn : ∃ n, A n ∉ R := by
      by_contra h
      exact hU (R.iUnion_mem A (not_exists_not.mp h))
    obtain ⟨n, hn⟩ := hn
    rw [extensionMass_of_not_mem R μ hU]
    exact (ENNReal.tsum_eq_top_of_eq_top ⟨n, extensionMass_of_not_mem R μ hn⟩).symm

/-- A measure in the source representation, with its sigma-algebra explicit. -/
noncomputable def extendedSource :
    @D11.Ch01.MeasureDefinitions.SourceMeasure X
      (MeasurableSpace.generateFrom (R : Set (Set X))) := by
  letI : MeasurableSpace X := MeasurableSpace.generateFrom (R : Set (Set X))
  exact
    { value := fun A => extensionMass R μ A.1
      empty := extension_empty R μ
      iUnion := fun A hd => extension_countably_additive R μ (fun n => (A n).1)
        (fun n => (A n).2) hd }

/-- The corresponding native measure on exactly the generated sigma-algebra. -/
noncomputable def extension :
    @Measure X (MeasurableSpace.generateFrom (R : Set (Set X))) :=
  @D11.Ch01.MeasureDefinitions.measureOfSource X
    (MeasurableSpace.generateFrom (R : Set (Set X))) (extendedSource R μ)

/-- Formula only on the specified measurable domain. -/
theorem extension_apply (A : Set X)
    (hA : MeasurableSet[MeasurableSpace.generateFrom (R : Set (Set X))] A) :
    extension R μ A = extensionMass R μ A :=
  @D11.Ch01.MeasureDefinitions.measureOfSource_apply X
    (MeasurableSpace.generateFrom (R : Set (Set X))) (extendedSource R μ) A hA

theorem exists_extension :
    ∃ ν : @Measure X (MeasurableSpace.generateFrom (R : Set (Set X))),
      ∀ A : Set X,
        MeasurableSet[MeasurableSpace.generateFrom (R : Set (Set X))] A →
          ν A = extensionMass R μ A :=
  ⟨extension R μ, extension_apply R μ⟩

end SigmaRingMeasure
end D11.Ch23
