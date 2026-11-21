import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.FilteredComplexes
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.FiltrationExactSequences

/-! HA-F02: exact quotient sequences, naturality, and the connecting map.
All arguments take place in arbitrary abelian categories. -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u
namespace AdvancedHomologicalAlgebra
variable {A : Type u} [Category.{v} A] [Abelian A]
namespace Filtration
variable {K : CochainComplex A ℤ}

instance doubleTransition_mono (F : Filtration K) (p : ℤ) : Mono (F.doubleTransition p) :=
  inferInstanceAs (Mono (F.transition (p + 1) ≫ F.transition p))

instance twoStepProjection_epi (F : Filtration K) (p : ℤ) : Epi (F.twoStepProjection p) :=
  inferInstanceAs (Epi (cokernel.π _))

@[reassoc (attr := simp)]
theorem projection_gradedToTwoStep (F : Filtration K) (p : ℤ) :
    F.projection (p + 1) ≫ F.gradedToTwoStep p = F.transition p ≫ F.twoStepProjection p := by
  exact F.projection_quotientDesc _ _ _

@[reassoc (attr := simp)]
theorem twoStepProjection_toGraded (F : Filtration K) (p : ℤ) :
    F.twoStepProjection p ≫ F.twoStepToGraded p = F.projection p :=
  cokernel.π_desc _ _ _

/-- The defining quotient sequence is short exact as a sequence of complexes. -/
theorem firstSequence_shortExact (F : Filtration K) (p : ℤ) :
    (F.firstSequence p).ShortExact where
  exact := (F.firstSequence p).exact_of_g_is_cokernel (F.projectionIsCokernel p)
  mono_f := F.transition_mono p
  epi_g := F.projection_epi p

/-- Monicity of the map between the two quotients. A lift is taken only
after an epic refinement, and its vanishing descends along that cover. -/
instance gradedToTwoStep_mono (F : Filtration K) (p : ℤ) : Mono (F.gradedToTwoStep p) := by
  apply Preadditive.mono_of_cancel_zero
  intro T z hz
  obtain ⟨T', e, he, x, hx⟩ :=
    surjective_up_to_refinements_of_epi (F.projection (p + 1)) z
  have hxr : (x ≫ F.transition p) ≫ cokernel.π (F.doubleTransition p) = 0 := by
    change (x ≫ F.transition p) ≫ F.twoStepProjection p = 0
    rw [Category.assoc, ← F.projection_gradedToTwoStep, ← Category.assoc, ← hx,
      Category.assoc, hz, comp_zero]
  let y := Abelian.monoLift (F.doubleTransition p) (x ≫ F.transition p) hxr
  have hy : y ≫ F.transition (p + 1) = x := by
    apply (cancel_mono (F.transition p)).1
    rw [Category.assoc]
    exact Abelian.monoLift_comp (F.doubleTransition p) (x ≫ F.transition p) hxr
  apply (cancel_epi e).1
  rw [comp_zero, hx, ← hy, Category.assoc, F.transition_projection, comp_zero]

instance twoStepToGraded_epi (F : Filtration K) (p : ℤ) : Epi (F.twoStepToGraded p) :=
  epi_of_epi_fac (F.twoStepProjection_toGraded p)

/-- The right arrow is the cokernel of the left arrow. -/
def twoStepToGradedIsCokernel (F : Filtration K) (p : ℤ) :
    IsColimit (CokernelCofork.ofπ (F.twoStepToGraded p) (F.secondSequence p).zero) := by
  apply CokernelCofork.IsColimit.ofπ'
  intro L g hg
  change F.gradedToTwoStep p ≫ g = 0 at hg
  have ht : F.transition p ≫ (F.twoStepProjection p ≫ g) = 0 := by
    rw [← Category.assoc, ← F.projection_gradedToTwoStep, Category.assoc, hg, comp_zero]
  refine ⟨F.quotientDesc p (F.twoStepProjection p ≫ g) ht, ?_⟩
  apply (cancel_epi (F.twoStepProjection p)).1
  rw [← Category.assoc, F.twoStepProjection_toGraded, F.projection_quotientDesc]

/-- The quotient of nested filtration steps is short exact. -/
theorem secondSequence_shortExact (F : Filtration K) (p : ℤ) :
    (F.secondSequence p).ShortExact where
  exact := (F.secondSequence p).exact_of_g_is_cokernel (F.twoStepToGradedIsCokernel p)
  mono_f := F.gradedToTwoStep_mono p
  epi_g := F.twoStepToGraded_epi p
end Filtration

namespace FilteredMap
variable {X Y : FilteredComplex A}

@[reassoc (attr := simp)]
theorem twoStepProjection_naturality (f : FilteredMap X Y) (p : ℤ) :
    X.filtration.twoStepProjection p ≫ f.twoStepMap p =
      f.stepMap p ≫ Y.filtration.twoStepProjection p := by
  exact cokernel.π_desc _ _ _

@[reassoc]
theorem gradedToTwoStep_naturality (f : FilteredMap X Y) (p : ℤ) :
    X.filtration.gradedToTwoStep p ≫ f.twoStepMap p =
      f.gradedMap (p + 1) ≫ Y.filtration.gradedToTwoStep p := by
  apply (cancel_epi (X.filtration.projection (p + 1))).1
  rw [← Category.assoc, X.filtration.projection_gradedToTwoStep, Category.assoc,
    f.twoStepProjection_naturality, ← Category.assoc, f.transition_naturality,
    Category.assoc, ← Y.filtration.projection_gradedToTwoStep,
    ← Category.assoc, ← f.projection_naturality, Category.assoc]

@[reassoc]
theorem twoStepToGraded_naturality (f : FilteredMap X Y) (p : ℤ) :
    X.filtration.twoStepToGraded p ≫ f.gradedMap p =
      f.twoStepMap p ≫ Y.filtration.twoStepToGraded p := by
  apply (cancel_epi (X.filtration.twoStepProjection p)).1
  rw [← Category.assoc, X.filtration.twoStepProjection_toGraded,
    f.projection_naturality, ← Category.assoc, f.twoStepProjection_naturality,
    Category.assoc, Y.filtration.twoStepProjection_toGraded]

/-- The morphism between the second short exact sequences. -/
def secondSequenceMap (f : FilteredMap X Y) (p : ℤ) :
    X.filtration.secondSequence p ⟶ Y.filtration.secondSequence p where
  τ₁ := f.gradedMap (p + 1)
  τ₂ := f.twoStepMap p
  τ₃ := f.gradedMap p
  comm₁₂ := (f.gradedToTwoStep_naturality p).symm
  comm₂₃ := (f.twoStepToGraded_naturality p).symm
end FilteredMap

/-- Evaluation preserves the cokernel defining the middle quotient. -/
theorem filtration_twoStep_degreewise_quotient : F02Specs.DegreewiseQuotient.{v,u} := by
  intro A _ _ K F p n
  exact ⟨(CokernelCofork.ofπ (cokernel.π (F.doubleTransition p))
    (cokernel.condition (F.doubleTransition p))).mapIsColimit
      (cokernelIsCokernel (F.doubleTransition p)) (HomologicalComplex.eval A _ n)⟩

/-- The two short exact sequences in HA-F02. -/
theorem filtration_exact_sequences : F02Specs.ExactSequences.{v,u} := by
  intro A _ _ K F p
  exact ⟨F.firstSequence_shortExact p, F.secondSequence_shortExact p⟩

/-- Functoriality of the middle quotient, together with the accepted
functoriality of the filtration steps and graded pieces. -/
theorem filtration_twoStep_functorial : F02Specs.QuotientFunctoriality.{v,u} := by
  intro A _ _
  constructor
  · intro X p
    apply (cancel_epi (X.filtration.twoStepProjection p)).1
    rw [FilteredMap.twoStepProjection_naturality, FilteredMap.stepMap_id,
      Category.id_comp, Category.comp_id]
  · intro X Y Z f g p
    apply (cancel_epi (X.filtration.twoStepProjection p)).1
    rw [FilteredMap.twoStepProjection_naturality, FilteredMap.stepMap_comp,
      Category.assoc, ← g.twoStepProjection_naturality,
      ← Category.assoc, ← f.twoStepProjection_naturality, Category.assoc]

/-- Naturality of the short exact sequences. -/
theorem filtration_exact_sequences_natural : F02Specs.Naturality.{v,u} := by
  intro A _ _ X Y f p
  exact ⟨f.transition_naturality p, f.projection_naturality p,
    f.gradedToTwoStep_naturality p, f.twoStepToGraded_naturality p⟩

/-- Naturality of the connecting morphism on cohomology. -/
theorem filtration_connecting_natural : F02Specs.ConnectingNaturality.{v,u} := by
  intro A _ _ X Y f p n hX hY
  exact HomologicalComplex.HomologySequence.δ_naturality (f.secondSequenceMap p)
    hX hY n (n + 1) (by simp)
/-- Lift any quotient cycle over an epic cover; factor its differential using
normality of the monomorphism of filtration steps. -/
theorem filtration_representative_lifts : F02Specs.RepresentativeLifts.{v,u} := by
  intro A _ _ K F p n T z hz
  obtain ⟨T', e, he, x, hx⟩ :=
    surjective_up_to_refinements_of_epi ((F.projection p).f n) z
  have hd : (x ≫ (F.step p).d n (n + 1)) ≫
      (F.projection p).f (n + 1) = 0 := by
    rw [Category.assoc, ← (F.projection p).comm n (n + 1), ← Category.assoc,
      ← hx, Category.assoc, hz, comp_zero]
  refine ⟨T', e, he, x, Abelian.monoLift ((F.transition p).f (n + 1))
    (x ≫ (F.step p).d n (n + 1)) hd, hx.symm, ?_⟩
  exact Abelian.monoLift_comp _ _ _

/-- The differential of a lift gives the connecting map, with the positive
cochain sign and the degree shift from `n` to `n+1`. -/
theorem filtration_connecting_formula : F02Specs.ConnectingFormula.{v,u} := by
  intro A _ _ K F p n h T x hx y hy
  have hyd : y ≫ (F.step (p + 1)).d (n + 1) (n + 1 + 1) = 0 := by
    apply (cancel_mono ((F.transition p).f (n + 1 + 1))).1
    rw [zero_comp, Category.assoc, ← (F.transition p).comm (n + 1) (n + 1 + 1),
      ← Category.assoc, hy, Category.assoc, HomologicalComplex.d_comp_d, comp_zero]
  have hz : (y ≫ (F.projection (p + 1)).f (n + 1)) ≫
      (F.graded (p + 1)).d (n + 1) (n + 1 + 1) = 0 := by
    rw [Category.assoc, (F.projection (p + 1)).comm (n + 1) (n + 1 + 1),
      ← Category.assoc, hyd, zero_comp]
  refine ⟨hz, ?_⟩
  have hx₂ : (x ≫ (F.twoStepProjection p).f n) ≫ (F.twoStepToGraded p).f n =
      x ≫ (F.projection p).f n := by
    rw [Category.assoc, ← HomologicalComplex.comp_f, F.twoStepProjection_toGraded]
  have hx₁ : (y ≫ (F.projection (p + 1)).f (n + 1)) ≫
      (F.gradedToTwoStep p).f (n + 1) =
      (x ≫ (F.twoStepProjection p).f n) ≫ (F.twoStepQuotient p).d n (n + 1) := by
    rw [Category.assoc, ← HomologicalComplex.comp_f, F.projection_gradedToTwoStep]
    change y ≫ ((F.transition p).f (n + 1) ≫ (F.twoStepProjection p).f (n + 1)) = _
    rw [← Category.assoc, hy, Category.assoc, ← (F.twoStepProjection p).comm n (n + 1),
      Category.assoc]
  exact h.δ_eq n (n + 1) (by simp) (x ≫ (F.projection p).f n) hx
    (x ≫ (F.twoStepProjection p).f n) hx₂
    (y ≫ (F.projection (p + 1)).f (n + 1)) hx₁ (n + 1 + 1) (by simp)
end AdvancedHomologicalAlgebra
