import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.FiniteProductPermutations
import MathGenome.Internal.RealAnalysis.D11.Ch08.Fubini
import MathGenome.Internal.RealAnalysis.D11.Ch08.Tonelli

open Set MeasureTheory
open scoped ENNReal
open Specs.D11.Ch08.FiniteProductPermutations

universe u v
noncomputable section
set_option linter.style.haveILetI false
namespace D11.Ch08.FiniteProductPermutations

theorem rectangle_sigma : Specs.D11.Ch08.FiniteProductPermutations.rectangle_sigma.{u} := by
  intro ι _ X _
  exact generateFrom_pi

theorem rectangle_measure : Specs.D11.Ch08.FiniteProductPermutations.rectangle_measure.{u} := by
  intro ι _ X _ μ _
  exact ⟨inferInstance, fun A _ => Measure.pi_pi μ A, fun η hη => (Measure.pi_eq hη).symm⟩

theorem tuple_rectangle_sigma :
    Specs.D11.Ch08.FiniteProductPermutations.tuple_rectangle_sigma.{u} := by
  intro t X _
  rw [← MeasurableSpace.comap_generateFrom, rectangle_sigma X]
  exact (flatten t X).measurableEmbedding.comap_eq

instance tuple_sigmaFinite : (t : Bracketing) → {X : Leaves t → Type u} →
    [∀ i, MeasurableSpace (X i)] → (μ : ∀ i, Measure (X i)) →
    [∀ i, SigmaFinite (μ i)] → SigmaFinite (tupleMeasure t μ)
  | .atom, _, _, μ, hμ => hμ PUnit.unit
  | .pair l r, X, m, μ, hμ => by
      letI : ∀ i, MeasurableSpace (X (.inl i)) := fun i => m (.inl i)
      letI : ∀ i, MeasurableSpace (X (.inr i)) := fun i => m (.inr i)
      haveI : ∀ i, SigmaFinite (μ (.inl i)) := fun i => hμ (.inl i)
      haveI : ∀ i, SigmaFinite (μ (.inr i)) := fun i => hμ (.inr i)
      haveI := tuple_sigmaFinite l (fun i => μ (.inl i))
      haveI := tuple_sigmaFinite r (fun i => μ (.inr i))
      exact inferInstanceAs (SigmaFinite
        ((tupleMeasure l (fun i => μ (.inl i))).prod (tupleMeasure r (fun i => μ (.inr i)))))

theorem flatten_preserving : Specs.D11.Ch08.FiniteProductPermutations.flatten_preserving.{u} := by
  intro t
  induction t with
  | atom =>
      intro X _ μ _
      exact (measurePreserving_piUnique μ).symm
  | pair l r hl hr =>
      intro X m μ hμ
      letI : ∀ i, MeasurableSpace (X (.inl i)) := fun i => m (.inl i)
      letI : ∀ i, MeasurableSpace (X (.inr i)) := fun i => m (.inr i)
      haveI : ∀ i, SigmaFinite (μ (.inl i)) := fun i => hμ (.inl i)
      haveI : ∀ i, SigmaFinite (μ (.inr i)) := fun i => hμ (.inr i)
      exact (measurePreserving_sumPiEquivProdPi_symm μ).comp
        ((hl (fun i => μ (.inl i))).prod (hr (fun i => μ (.inr i))))

theorem tuple_rectangle_measure :
    Specs.D11.Ch08.FiniteProductPermutations.tuple_rectangle_measure.{u} := by
  intro t X _ μ _ A _
  rw [← (flatten t X).map_apply, (flatten_preserving t μ).map_eq, Measure.pi_pi]

theorem rebracket_preserving :
    Specs.D11.Ch08.FiniteProductPermutations.rebracket_preserving.{u} := by
  intro s t e X _ μ _
  exact (flatten_preserving t μ).symm.comp
    ((measurePreserving_piCongrLeft μ e).comp (flatten_preserving s (fun i => μ (e i))))

theorem rebracket_coordinates :
    Specs.D11.Ch08.FiniteProductPermutations.rebracket_coordinates.{u} := by
  intro s t e X _ x i
  change (flatten t X) ((flatten t X).symm
    (MeasurableEquiv.piCongrLeft X e (flatten s (fun j => X (e j)) x))) (e i) = _
  rw [(flatten t X).apply_symm_apply]
  exact MeasurableEquiv.piCongrLeft_apply_apply e _ i

theorem positive_arity : Specs.D11.Ch08.FiniteProductPermutations.positive_arity := by
  intro n
  exact ⟨rightBracketing n, ⟨rightLeafOrder n⟩⟩

theorem permutation_preserving :
    Specs.D11.Ch08.FiniteProductPermutations.permutation_preserving.{u} := by
  intro ι κ _ _ e X _ μ _
  exact measurePreserving_piCongrLeft μ e

theorem one_factor : Specs.D11.Ch08.FiniteProductPermutations.one_factor.{u} := by
  intro X _ μ
  refine ⟨?_, rfl, fun _ => rfl, fun _ => rfl⟩
  ext x
  rfl

theorem coordinates_preserving {ι : Type} [Fintype ι]
    (t : Bracketing) (e : Leaves t ≃ ι)
    {X : ι → Type u} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (coordinates t e X)
      (tupleMeasure t (fun i => μ (e i))) (Measure.pi μ) :=
  (measurePreserving_piCongrLeft μ e).comp (flatten_preserving t (fun i => μ (e i)))

/-- Parameter measurability for every intermediate nonnegative integral,
on the given sigma-algebras, without completing any factor. -/
theorem measurable_iteratedLIntegral :
    ∀ (t : Bracketing) {X : Leaves t → Type u} [∀ i, MeasurableSpace (X i)]
      (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
      {P : Type (max u v)} [MeasurableSpace P] (f : P × Tuple t X → ℝ≥0∞),
      Measurable f → Measurable (fun p => iteratedLIntegral t μ (fun x => f (p, x))) := by
  intro t
  induction t with
  | atom =>
      intro X _ μ _ P _ f hf
      exact hf.lintegral_prod_right'
  | pair l r hl hr =>
      intro X m μ hμ P _ f hf
      letI : ∀ i, MeasurableSpace (X (.inl i)) := fun i => m (.inl i)
      letI : ∀ i, MeasurableSpace (X (.inr i)) := fun i => m (.inr i)
      haveI : ∀ i, SigmaFinite (μ (.inl i)) := fun i => hμ (.inl i)
      haveI : ∀ i, SigmaFinite (μ (.inr i)) := fun i => hμ (.inr i)
      have hm : Measurable (fun q : (P × Tuple l (fun i => X (.inl i))) ×
          Tuple r (fun i => X (.inr i)) => f (q.1.1, (q.1.2, q.2))) :=
        hf.comp ((measurable_fst.comp measurable_fst).prodMk
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
      exact hl (fun i => μ (.inl i)) _ (hr (fun i => μ (.inr i)) _ hm)

/-- Parameter measurability for successive scalar integrals, including their
specified zero values when an individual one-factor section is not integrable. -/
theorem measurable_iteratedIntegral {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] :
    ∀ (t : Bracketing) {X : Leaves t → Type u} [∀ i, MeasurableSpace (X i)]
      (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
      {P : Type (max u v)} [MeasurableSpace P] (f : P × Tuple t X → 𝕜),
      Measurable f → Measurable (fun p => iteratedIntegral t μ (fun x => f (p, x))) := by
  intro t
  induction t with
  | atom =>
      intro X _ μ _ P _ f hf
      exact hf.stronglyMeasurable.integral_prod_right'.measurable
  | pair l r hl hr =>
      intro X m μ hμ P _ f hf
      letI : ∀ i, MeasurableSpace (X (.inl i)) := fun i => m (.inl i)
      letI : ∀ i, MeasurableSpace (X (.inr i)) := fun i => m (.inr i)
      haveI : ∀ i, SigmaFinite (μ (.inl i)) := fun i => hμ (.inl i)
      haveI : ∀ i, SigmaFinite (μ (.inr i)) := fun i => hμ (.inr i)
      have hm : Measurable (fun q : (P × Tuple l (fun i => X (.inl i))) ×
          Tuple r (fun i => X (.inr i)) => f (q.1.1, (q.1.2, q.2))) :=
        hf.comp ((measurable_fst.comp measurable_fst).prodMk
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
      exact hl (fun i => μ (.inl i)) _ (hr (fun i => μ (.inr i)) _ hm)

theorem tonelli_tree : Specs.D11.Ch08.FiniteProductPermutations.tonelli_tree.{u} := by
  intro t
  induction t with
  | atom => intro X _ μ _ f hf; rfl
  | pair l r hl hr =>
      intro X m μ hμ f hf
      letI : ∀ i, MeasurableSpace (X (.inl i)) := fun i => m (.inl i)
      letI : ∀ i, MeasurableSpace (X (.inr i)) := fun i => m (.inr i)
      haveI : ∀ i, SigmaFinite (μ (.inl i)) := fun i => hμ (.inl i)
      haveI : ∀ i, SigmaFinite (μ (.inr i)) := fun i => hμ (.inr i)
      have hm := measurable_iteratedLIntegral r (fun i => μ (.inr i)) f hf
      calc
        (∫⁻ p, f p ∂tupleMeasure (.pair l r) μ) =
            ∫⁻ x, ∫⁻ y, f (x, y) ∂tupleMeasure r (fun i => μ (.inr i))
              ∂tupleMeasure l (fun i => μ (.inl i)) := lintegral_prod f hf.aemeasurable
        _ = ∫⁻ x, iteratedLIntegral r (fun i => μ (.inr i)) (fun y => f (x, y))
              ∂tupleMeasure l (fun i => μ (.inl i)) := by
          apply lintegral_congr
          intro x
          exact hr (fun i => μ (.inr i)) _ (hf.comp measurable_prodMk_left)
        _ = iteratedLIntegral (.pair l r) μ f := hl (fun i => μ (.inl i)) _ hm

theorem nonnegative_sections :
    ∀ (t : Bracketing) {X : Leaves t → Type u} [∀ i, MeasurableSpace (X i)]
      (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
      (f : Tuple t X → ℝ≥0∞), Measurable f → NonnegativeSections t μ f := by
  intro t
  induction t with
  | atom => intro X _ μ _ f hf; exact hf
  | pair l r hl hr =>
      intro X m μ hμ f hf
      letI : ∀ i, MeasurableSpace (X (.inl i)) := fun i => m (.inl i)
      letI : ∀ i, MeasurableSpace (X (.inr i)) := fun i => m (.inr i)
      haveI : ∀ i, SigmaFinite (μ (.inl i)) := fun i => hμ (.inl i)
      haveI : ∀ i, SigmaFinite (μ (.inr i)) := fun i => hμ (.inr i)
      refine ⟨hf, fun x => hr (fun i => μ (.inr i)) _
        (hf.comp measurable_prodMk_left), ?_⟩
      exact hl (fun i => μ (.inl i)) _
        (measurable_iteratedLIntegral r (fun i => μ (.inr i)) f hf)

theorem fubini_tree : Specs.D11.Ch08.FiniteProductPermutations.fubini_tree.{u} := by
  intro t
  induction t with
  | atom => intro X _ μ _ 𝕜 _ _ _ f hf hi; exact ⟨⟨hf, hi⟩, rfl⟩
  | pair l r hl hr =>
      intro X m μ hμ 𝕜 _ _ _ f hf hi
      letI : ∀ i, MeasurableSpace (X (.inl i)) := fun i => m (.inl i)
      letI : ∀ i, MeasurableSpace (X (.inr i)) := fun i => m (.inr i)
      haveI : ∀ i, SigmaFinite (μ (.inl i)) := fun i => hμ (.inl i)
      haveI : ∀ i, SigmaFinite (μ (.inr i)) := fun i => hμ (.inr i)
      have hsec : ∀ᵐ x ∂tupleMeasure l (fun i => μ (.inl i)),
          ScalarSections r (fun i => μ (.inr i)) (fun y => f (x, y)) ∧
          (∫ y, f (x, y) ∂tupleMeasure r (fun i => μ (.inr i))) =
            iteratedIntegral r (fun i => μ (.inr i)) (fun y => f (x, y)) := by
        filter_upwards [hi.prod_right_ae] with x hx
        exact hr (fun i => μ (.inr i)) _ (hf.comp measurable_prodMk_left) hx
      have hae : (fun x => ∫ y, f (x, y) ∂tupleMeasure r (fun i => μ (.inr i))) =ᵐ[
          tupleMeasure l (fun i => μ (.inl i))]
          (fun x => iteratedIntegral r (fun i => μ (.inr i)) (fun y => f (x, y))) :=
        hsec.mono fun _ hx => hx.2
      have hm := measurable_iteratedIntegral r (fun i => μ (.inr i)) f hf
      have hi' := hi.integral_prod_left.congr hae
      obtain ⟨hs, he⟩ := hl (fun i => μ (.inl i)) _ hm hi'
      refine ⟨⟨⟨hf, hi⟩, hsec.mono (fun _ hx => hx.1), hs⟩, ?_⟩
      calc
        (∫ p, f p ∂tupleMeasure (.pair l r) μ) =
            ∫ x, ∫ y, f (x, y) ∂tupleMeasure r (fun i => μ (.inr i))
              ∂tupleMeasure l (fun i => μ (.inl i)) := integral_prod f hi
        _ = ∫ x, iteratedIntegral r (fun i => μ (.inr i)) (fun y => f (x, y))
              ∂tupleMeasure l (fun i => μ (.inl i)) := integral_congr_ae hae
        _ = iteratedIntegral (.pair l r) μ f := he

theorem tonelli_all_orders :
    Specs.D11.Ch08.FiniteProductPermutations.tonelli_all_orders.{u} := by
  intro n t e X _ μ _ f hf
  have hm := hf.comp (coordinates t e X).measurable
  refine ⟨nonnegative_sections t (fun i => μ (e i)) _ hm, ?_⟩
  rw [D11.Ch05.NonnegativeIntegral.eq_lintegral _ _ hf]
  exact ((coordinates_preserving t e μ).lintegral_comp hf).symm.trans
    (tonelli_tree t (fun i => μ (e i)) _ hm)

theorem fubini_all_orders :
    Specs.D11.Ch08.FiniteProductPermutations.fubini_all_orders.{u} := by
  intro n t e X _ μ _ 𝕜 _ _ _ f hf
  have hi := (D11.Ch06.ScalarIntegral.scalarIntegrable_iff (Measure.pi μ) f).mp hf
  have hm := hi.1.comp (coordinates t e X).measurable
  have hif := (coordinates_preserving t e μ).integrable_comp_of_integrable hi.2
  obtain ⟨hs, he⟩ := fubini_tree t (fun i => μ (e i)) _ hm hif
  refine ⟨hs, ?_⟩
  exact ((coordinates_preserving t e μ).integral_comp' f).symm.trans he

end D11.Ch08.FiniteProductPermutations
