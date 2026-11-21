import MathGenome.Internal.RealAnalysis.D11.Ch02.PremeasureAgreement
import MathGenome.Internal.RealAnalysis.D11.Ch01.GeneratorUniqueness
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch02.Extension

/-!
# Extension of a premeasure

The canonical extension is the covering outer measure restricted to the
generated sigma-algebra. For finite-set equality it suffices to choose one
finite-cost algebra cover. Both extensions agree on its union by disjointifying
the cover. Maximality on the complement inside this finite union, followed by
finite cancellation, gives equality on the original set. This avoids an
epsilon argument and makes no sigma-finiteness assumption.
-/

open Set MeasureTheory MeasurableSpace
open scoped ENNReal

universe u

namespace D11.Ch02.Extension

open PremeasureAgreement

variable {α : Type u} {A : Set (Set α)} {hA : IsSetAlgebra A}

theorem generated_le_caratheodory (p : Premeasure A hA) :
    generateFrom A ≤ (coveringOuterMeasure p).caratheodory := by
  apply generateFrom_le
  intro s hs
  exact algebra_measurable p hs

/-- Restrict the covering outer measure to precisely the generated sigma-algebra. -/
noncomputable def extension (p : Premeasure A hA) : @Measure α (generateFrom A) :=
  @OuterMeasure.toMeasure α (generateFrom A) (coveringOuterMeasure p)
    (generated_le_caratheodory p)

theorem extension_apply (p : Premeasure A hA) (E : Set α)
    (hE : MeasurableSet[generateFrom A] E) :
    extension p E = coveringOuterMeasure p E :=
  @toMeasure_apply α (generateFrom A) (coveringOuterMeasure p)
    (generated_le_caratheodory p) E hE

theorem extension_agrees (p : Premeasure A hA) (s : A) :
    extension p s.1 = p.value s := by
  rw [extension_apply p s.1 (measurableSet_generateFrom s.2)]
  exact coveringOuterMeasure_agrees p s

/-- Every other extension is bounded by the covering outer measure. -/
theorem extension_le_outer (p : Premeasure A hA)
    (ν : @Measure α (generateFrom A)) (hν : ∀ s : A, ν s.1 = p.value s)
    (E : Set α) : ν E ≤ coveringOuterMeasure p E := by
  rw [coveringOuterMeasure_apply]
  refine le_iInf fun F => le_iInf fun hF => le_iInf fun hc => ?_
  calc
    ν E ≤ ν (⋃ n, F n) := measure_mono hc
    _ ≤ ∑' n, ν (F n) := measure_iUnion_le F
    _ = ∑' n, p.value ⟨F n, hF n⟩ := by
      congr 1
      funext n
      exact hν ⟨F n, hF n⟩

/-- Extensions agree on countable unions of algebra sets, even at infinity. -/
theorem extensions_agree_iUnion (p : Premeasure A hA)
    (μ ν : @Measure α (generateFrom A))
    (hμ : ∀ s : A, μ s.1 = p.value s) (hν : ∀ s : A, ν s.1 = p.value s)
    (F : ℕ → A) : μ (⋃ n, (F n).1) = ν (⋃ n, (F n).1) := by
  let D := disjointed (fun n => (F n).1)
  have hD : ∀ n, D n ∈ A := hA.isSetRing.disjointed_mem (fun n => (F n).2)
  have hmD : ∀ n, MeasurableSet[generateFrom A] (D n) :=
    fun n => measurableSet_generateFrom (hD n)
  have hd : Pairwise fun i j => Disjoint (D i) (D j) :=
    disjoint_disjointed _
  rw [← iUnion_disjointed (f := fun n => (F n).1)]
  rw [measure_iUnion hd hmD, measure_iUnion hd hmD]
  congr 1
  funext n
  exact (hμ ⟨D n, hD n⟩).trans (hν ⟨D n, hD n⟩).symm

theorem extension_eq_of_finite (p : Premeasure A hA)
    (ν : @Measure α (generateFrom A)) (hν : ∀ s : A, ν s.1 = p.value s)
    (E : Set α) (hE : MeasurableSet[generateFrom A] E)
    (hfinite : extension p E < ∞) : ν E = extension p E := by
  let : MeasurableSpace α := generateFrom A
  have hcost : (⨅ (F : ℕ → Set α) (hF : ∀ n, F n ∈ A)
      (_ : E ⊆ ⋃ n, F n), ∑' n, p.value ⟨F n, hF n⟩) < ∞ := by
    rw [← coveringOuterMeasure_apply, ← extension_apply p E hE]
    exact hfinite
  obtain ⟨F, hF⟩ := iInf_lt_iff.mp hcost
  obtain ⟨hFA, hF⟩ := iInf_lt_iff.mp hF
  obtain ⟨hcover, hsum⟩ := iInf_lt_iff.mp hF
  let B := ⋃ n, F n
  have hUB : E ∪ B = B := union_eq_right.mpr hcover
  have hB : MeasurableSet B := MeasurableSet.iUnion fun n =>
    measurableSet_generateFrom (hFA n)
  have hBF : extension p B < ∞ := lt_of_le_of_lt
    ((measure_iUnion_le F).trans_eq (by
      congr 1
      funext n
      exact extension_agrees p ⟨F n, hFA n⟩)) hsum
  have hBeq : extension p B = ν B := extensions_agree_iUnion p
    (extension p) ν (extension_agrees p) hν (fun n => ⟨F n, hFA n⟩)
  have hdiff : ν (B \ E) ≤ extension p (B \ E) := by
    rw [extension_apply p (B \ E) (hB.diff hE)]
    exact extension_le_outer p ν hν (B \ E)
  have hdiffF : extension p (B \ E) ≠ ∞ :=
    (lt_of_le_of_lt (measure_mono sdiff_subset) hBF).ne
  have hreverse : extension p E ≤ ν E := by
    apply (ENNReal.add_le_add_iff_right hdiffF).mp
    calc
      extension p E + extension p (B \ E) = extension p B := by
        simpa only [hUB] using
          measure_add_sdiff (μ := extension p) hE.nullMeasurableSet B
      _ = ν B := hBeq
      _ = ν E + ν (B \ E) := by
        simpa only [hUB] using
          (measure_add_sdiff (μ := ν) hE.nullMeasurableSet B).symm
      _ ≤ ν E + extension p (B \ E) := add_le_add_right hdiff _
  apply le_antisymm
  · rw [extension_apply p E hE]
    exact extension_le_outer p ν hν E
  · exact hreverse

theorem extension_unique (p : Premeasure A hA) (hfinite : isSigmaFinite p)
    (ν : @Measure α (generateFrom A)) (hν : ∀ s : A, ν s.1 = p.value s) :
    ν = extension p := by
  let : MeasurableSpace α := generateFrom A
  obtain ⟨F, hF, hcover⟩ := hfinite
  apply Measure.ext_of_generateFrom_of_iUnion A (fun n => (F n).1) rfl
    (fun s hs t ht _ => hA.inter_mem hs ht) hcover (fun n => (F n).2)
  · intro n
    rw [hν (F n)]
    exact (hF n).ne
  · intro s hs
    exact (hν ⟨s, hs⟩).trans (extension_agrees p ⟨s, hs⟩).symm

/-- Existence, maximality, finite-set equality, and sigma-finite uniqueness. -/
theorem extension_existence_uniqueness :
    Specs.D11.Ch02.Extension.extension_existence_uniqueness.{u} := by
  intro α A hA p
  refine ⟨extension p, extension_apply p, extension_agrees p, ?_, ?_⟩
  · intro ν hν E hE
    constructor
    · rw [extension_apply p E hE]
      exact extension_le_outer p ν hν E
    · exact extension_eq_of_finite p ν hν E hE
  · exact extension_unique p

end D11.Ch02.Extension
