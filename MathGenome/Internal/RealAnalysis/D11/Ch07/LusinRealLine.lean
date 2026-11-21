import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.LusinRealLine
import MathGenome.Internal.RealAnalysis.D11.Ch03.GlobalClosedOpen
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Analysis.Complex.Tietze

noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

namespace D11.Ch07.LusinRealLine

/-- For a sigma-finite measure, its completed measurable domain is exactly
its full Carathéodory domain. Finiteness is used only on the spanning pieces. -/
theorem nullMeasurable_of_caratheodory {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] {A : Set α}
    (hA : MeasurableSet[μ.toOuterMeasure.caratheodory] A) :
    NullMeasurableSet A μ := by
  have hfinite {S : Set α} (hS : MeasurableSet[μ.toOuterMeasure.caratheodory] S)
      (hfin : μ S ≠ ∞) : NullMeasurableSet S μ := by
    let U := toMeasurable μ S
    have hSU : S ⊆ U := subset_toMeasurable μ S
    have hsplit := (OuterMeasure.isCaratheodory_iff μ.toOuterMeasure).mp hS U
    change μ U = μ (U ∩ S) + μ (U \ S) at hsplit
    rw [inter_eq_right.mpr hSU] at hsplit
    have hμU : μ U = μ S := measure_toMeasurable S
    have hzero : μ (U \ S) = 0 := by
      apply (ENNReal.add_right_inj hfin).mp
      simpa only [add_zero, hμU] using hsplit.symm
    have hae : U =ᵐ[μ] S := ae_eq_set.mpr ⟨hzero, by simp [sdiff_eq_empty.mpr hSU]⟩
    exact (measurableSet_toMeasurable μ S).nullMeasurableSet.congr hae
  have hpieces (n : ℕ) : NullMeasurableSet (A ∩ spanningSets μ n) μ := by
    apply hfinite (hA.inter (le_toOuterMeasure_caratheodory μ _
      (measurableSet_spanningSets μ n)))
    exact ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top μ n)).ne
  have heq : A = ⋃ n, A ∩ spanningSets μ n := by
    simp only [← inter_iUnion, iUnion_spanningSets, inter_univ]
  rw [heq]
  exact NullMeasurableSet.iUnion hpieces

/-- Check that the completed-real structure in the statements admits exactly
all sets satisfying the Lebesgue outer-measure splitting test. -/
theorem lebesgue_caratheodory :
    Specs.D11.Ch07.LusinRealLine.lebesgue_caratheodory := by
  intro A
  constructor
  · intro hA
    exact (OuterMeasure.isCaratheodory_iff _).mp
      (le_toOuterMeasure_caratheodory (volume : Measure ℝ).completion A hA)
  · intro hA
    exact nullMeasurable_of_caratheodory (volume : Measure ℝ)
      ((OuterMeasure.isCaratheodory_iff _).mpr hA)

/-- The countable-basis proof of Lusin's theorem only needs global closed
approximation of measurable sets. -/
theorem exists_closed_continuous_restriction
    {α β : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [MeasurableSpace β] [TopologicalSpace β] [SecondCountableTopology β]
    [OpensMeasurableSpace β] (μ : Measure α)
    (happrox : ∀ (A : Set α), MeasurableSet A → ∀ δ : ℝ≥0∞, δ ≠ 0 →
      ∃ P : Set α, IsClosed P ∧ P ⊆ A ∧ μ (A \ P) < δ)
    {E : Set α} (hE : MeasurableSet E) {f : α → β} (hf : Measurable f)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ F : Set α, IsClosed F ∧ F ⊆ E ∧ μ (E \ F) < ε ∧
      Continuous (fun x : F => f x) := by
  classical
  let B := countableBasis β
  let J := B × Bool
  obtain ⟨δ, hδ, hδsum⟩ := ENNReal.exists_pos_sum_of_countable' hε (Option J)
  let A : J → Set α := fun j => if j.2 then f ⁻¹' j.1.val else (f ⁻¹' j.1.val)ᶜ
  have hA (j : J) : MeasurableSet (A j) := by
    have hm := hf ((isOpen_of_mem_countableBasis j.1.property).measurableSet)
    dsimp [A]
    split
    · exact hm
    · exact hm.compl
  obtain ⟨F₀, hF₀, hF₀E, herror₀⟩ := happrox E hE (δ none) (hδ none).ne'
  choose P hPclosed hPA hPerror using fun j : J =>
    happrox (A j) (hA j) (δ (some j)) (hδ (some j)).ne'
  let F := F₀ ∩ ⋂ b : B, (P (b, true) ∪ P (b, false))
  have hFclosed : IsClosed F :=
    hF₀.inter (isClosed_iInter fun b => (hPclosed (b, true)).union (hPclosed (b, false)))
  have hFE : F ⊆ E := fun _ hx => hF₀E hx.1
  let bad : Option J → Set α := fun j => match j with
    | none => E \ F₀
    | some j => A j \ P j
  have hbad (j : Option J) : μ (bad j) ≤ δ j := by
    cases j with
    | none => exact herror₀.le
    | some j => exact (hPerror j).le
  have hcover : E \ F ⊆ ⋃ j, bad j := by
    intro x hx
    by_cases hx₀ : x ∈ F₀
    · have hn : ¬ ∀ b : B, x ∈ P (b, true) ∪ P (b, false) := by
        intro h
        exact hx.2 ⟨hx₀, mem_iInter.mpr h⟩
      obtain ⟨b, hb⟩ := not_forall.mp hn
      have hnot : x ∉ P (b, true) ∧ x ∉ P (b, false) := not_or.mp hb
      by_cases hxb : f x ∈ b.val
      · exact mem_iUnion.mpr ⟨some (b, true), by simpa [bad, A] using And.intro hxb hnot.1⟩
      · exact mem_iUnion.mpr ⟨some (b, false), by simpa [bad, A] using And.intro hxb hnot.2⟩
    · exact mem_iUnion.mpr ⟨none, hx.1, hx₀⟩
  refine ⟨F, hFclosed, hFE, ?_, ?_⟩
  · exact ((measure_mono hcover).trans ((measure_iUnion_le bad).trans
      (ENNReal.tsum_le_tsum hbad))).trans_lt hδsum
  · apply (isBasis_countableBasis β).continuous_iff.mpr
    intro U hU
    let b : B := ⟨U, hU⟩
    have heq : ((fun x : F => f x) ⁻¹' U)ᶜ =
        (Subtype.val : F → α) ⁻¹' P (b, false) := by
      ext x
      change (f x.val ∉ U) ↔ x.val ∈ P (b, false)
      constructor
      · intro hx
        rcases mem_iInter.mp x.property.2 b with h | h
        · have := hPA (b, true) h
          simp only [A, ite_true, mem_preimage] at this
          exact (hx this).elim
        · exact h
      · intro hx
        have := hPA (b, false) hx
        simpa [A] using this
    have hc : IsClosed (((fun x : F => f x) ⁻¹' U)ᶜ) :=
      heq ▸ (hPclosed (b, false)).preimage continuous_subtype_val
    simpa only [compl_compl] using hc.isOpen_compl

/-- Global closed approximation on the completed real Lebesgue space.
The completion keeps the outer evaluation of Borel volume; hence its outer
regularity and finite spanning sets transfer without restricting the domain. -/
theorem exists_closed_lebesgue_subset {A : Set ℝ}
    (hA : MeasurableSet[Specs.D11.Ch07.LusinRealLine.realLebesgueSpace] A)
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ P : Set ℝ, IsClosed P ∧ P ⊆ A ∧
      (volume : Measure ℝ).completion (A \ P) < δ := by
  let μ₀ : Measure ℝ := volume
  have houter (S : Set ℝ) (r : ℝ≥0∞) (hr : μ₀ S < r) :
      ∃ U, S ⊆ U ∧ IsOpen U ∧ μ₀ U < r :=
    S.exists_isOpen_lt_of_lt r hr
  have hborel : borel ℝ ≤ Specs.D11.Ch07.LusinRealLine.realLebesgueSpace :=
    fun _ hS => hS.nullMeasurableSet
  have hfinite (n : ℕ) : μ₀ (spanningSets μ₀ n) < ∞ :=
    measure_spanningSets_lt_top μ₀ n
  have hspan : (⋃ n, spanningSets μ₀ n) = univ := iUnion_spanningSets μ₀
  let : MeasurableSpace ℝ := Specs.D11.Ch07.LusinRealLine.realLebesgueSpace
  let μ : Measure ℝ := μ₀.completion
  let : OpensMeasurableSpace ℝ := ⟨hborel⟩
  let : μ.OuterRegular := ⟨fun S _ r hr => houter S r hr⟩
  let : SigmaFinite μ := ⟨⟨{
    set := spanningSets μ₀
    set_mem := fun _ => trivial
    finite := hfinite
    spanning := hspan }⟩⟩
  obtain ⟨U, hAU, hU, herror⟩ :=
    D11.Ch03.GlobalClosedOpen.exists_open_superset_small_excess μ hA.compl hδ
  refine ⟨Uᶜ, hU.isClosed_compl, ?_, ?_⟩
  · intro x hx
    by_contra hxA
    exact hx (hAU hxA)
  · have heq : A \ Uᶜ = U \ Aᶜ := by
      ext x
      simp only [mem_sdiff, mem_compl_iff, not_not, and_comm]
    change μ (A \ Uᶜ) < δ
    rw [heq]
    exact herror

/-- Lusin and extension for either scalar field (indeed for any second
countable target satisfying the Tietze extension property). -/
theorem lusin_scalar {𝕜 : Type*} [TopologicalSpace 𝕜] [MeasurableSpace 𝕜]
    [BorelSpace 𝕜] [SecondCountableTopology 𝕜] [Nonempty 𝕜] [TietzeExtension.{0} 𝕜]
    (E : Set ℝ) (hE : MeasurableSet[Specs.D11.Ch07.LusinRealLine.realLebesgueSpace] E)
    (f : E → 𝕜)
    (hf : @Measurable E 𝕜
      (Specs.D11.Ch07.LusinRealLine.realLebesgueSpace.comap Subtype.val) _ f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (F : Set ℝ) (hFE : F ⊆ E) (g : ℝ → 𝕜),
      IsClosed F ∧ Continuous g ∧
      (volume : Measure ℝ).completion (E \ F) < ENNReal.ofReal ε ∧
      ∀ x : F, g x = f ⟨x, hFE x.property⟩ := by
  let μ₀ : Measure ℝ := volume
  let : MeasurableSpace ℝ := Specs.D11.Ch07.LusinRealLine.realLebesgueSpace
  let μ : Measure ℝ := μ₀.completion
  obtain ⟨f', hf', hext⟩ :=
    (MeasurableEmbedding.subtype_coe hE).exists_measurable_extend hf (fun _ => inferInstance)
  obtain ⟨F, hFc, hFE, herror, hcont⟩ :=
    exists_closed_continuous_restriction μ
      (fun A hA δ hδ => exists_closed_lebesgue_subset hA hδ) hE hf'
      (ne_of_gt (ENNReal.ofReal_pos.mpr hε))
  obtain ⟨g, hg⟩ := (⟨_, hcont⟩ : C(F, 𝕜)).exists_restrict_eq hFc
  refine ⟨F, hFE, g, hFc, g.continuous, herror, ?_⟩
  intro x
  calc
    g x = f' x := congrArg (fun k : C(F, 𝕜) => k x) hg
    _ = f ⟨x, hFE x.property⟩ := congrFun hext ⟨x, hFE x.property⟩

theorem lusin_real : Specs.D11.Ch07.LusinRealLine.lusin_real := by
  intro E hE f hf ε hε
  exact lusin_scalar E hE f hf ε hε

theorem lusin_complex : Specs.D11.Ch07.LusinRealLine.lusin_complex := by
  intro E hE f hf ε hε
  exact lusin_scalar E hE f hf ε hε

end D11.Ch07.LusinRealLine
