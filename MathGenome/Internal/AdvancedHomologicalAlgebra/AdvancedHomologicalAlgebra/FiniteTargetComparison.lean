import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.FiniteFiltrationConvergence
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.FiniteTargetComparison
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! HA-S03: comparison with the degreewise finitely filtered target. -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u
namespace AdvancedHomologicalAlgebra
namespace FiniteTargetComparison
open FiniteFiltrationConvergence
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {X Y : FilteredComplex A}

/-- Comparison and the canonical stable-page square identify the induced map
on each associated graded cohomology object as an isomorphism. -/
theorem graded_isIso (f : FilteredMap X Y)
    (hX : DegreewiseFinite X.filtration) (hY : DegreewiseFinite Y.filtration)
    (D : F03Specs.PageData X.filtration) (E : F03Specs.PageData Y.filtration)
    (M : FilteredPageFunctoriality.MapData f D E) (r : ℤ) (hr : 0 ≤ r)
    (h : ∀ p n, IsIso (M.map r p n)) (p n : ℤ) :
    IsIso (gradedCohomologyMap f p n) := by
  obtain ⟨R, hR, hsX⟩ := uniform_stabilization X.filtration hX n
  obtain ⟨S, hS, hsY⟩ := uniform_stabilization Y.filtration hY n
  let s := max r (max R S)
  have hx := hsX s (by dsimp [s]; omega) p
  have hy := hsY s (by dsimp [s]; omega) p
  let L := limitIso X.filtration D s p n hx
  let L' := limitIso Y.filtration E s p n hy
  have : IsIso (M.map s p n) :=
    FilteredPageFunctoriality.comparison M r hr h s (by dsimp [s]; omega) p n
  have heq : gradedCohomologyMap f p n = L.iso.inv ≫ M.map s p n ≫ L'.iso.hom := by
    rw [limitIso_naturality f D E M s p n L L' hx, Iso.inv_hom_id_assoc]
  rw [heq]
  infer_instance

/-- The short exact sequence of two adjacent cohomology filtration steps. -/
def stepSequence {K : CochainComplex A ℤ} (F : Filtration K) (p n : ℤ) : ShortComplex A :=
  ShortComplex.mk (Subobject.ofLE _ _ (cohomologyPiece_decreasing F p n))
    (cokernel.π _) (cokernel.condition _)

theorem stepSequence_shortExact {K : CochainComplex A ℤ} (F : Filtration K) (p n : ℤ) :
    (stepSequence F p n).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _
  mono_f := by dsimp [stepSequence]; infer_instance
  epi_g := by dsimp [stepSequence]; infer_instance

/-- The restriction map and its graded quotient form a morphism of the step
short exact sequences. -/
def stepSequenceMap (f : FilteredMap X Y) (p n : ℤ) :
    stepSequence X.filtration p n ⟶ stepSequence Y.filtration p n where
  τ₁ := cohomologyStepMap f (p+1) n
  τ₂ := cohomologyStepMap f p n
  τ₃ := gradedCohomologyMap f p n
  comm₁₂ := (cohomologyStepMap_comm f p n).symm
  comm₂₃ := by simp [stepSequence, gradedCohomologyMap, cokernel.map]

/-- Descending one step uses the short five lemma. -/
theorem step_isIso_of_succ (f : FilteredMap X Y) (p n : ℤ)
    (hs : IsIso (cohomologyStepMap f (p+1) n))
    (hg : IsIso (gradedCohomologyMap f p n)) :
    IsIso (cohomologyStepMap f p n) := by
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃' (stepSequenceMap f p n)
    (stepSequence_shortExact X.filtration p n)
    (stepSequence_shortExact Y.filtration p n) hs hg

/-- A subobject equal to bottom has zero domain, regardless of the chosen
representative of that subobject. -/
theorem subobject_isZero_of_eq_bot {H : A} (P : Subobject H) (h : P = ⊥) :
    IsZero (P : A) := by
  subst P
  apply (IsZero.iff_id_eq_zero _).2
  apply (cancel_mono (⊥ : Subobject H).arrow).1
  simp

/-- A graded isomorphism between finite filtrations is an isomorphism at
every step. The descending induction starts at a common upper bound. -/
theorem steps_isIso (f : FilteredMap X Y)
    (hX : DegreewiseFinite X.filtration) (hY : DegreewiseFinite Y.filtration)
    (hg : ∀ p n, IsIso (gradedCohomologyMap f p n)) (p n : ℤ) :
    IsIso (cohomologyStepMap f p n) := by
  obtain ⟨aX, bX, haX, hbX⟩ := (cohomology_filtration X.filtration hX).finite n
  obtain ⟨aY, bY, haY, hbY⟩ := (cohomology_filtration Y.filtration hY).finite n
  let b := max bX bY
  have hz : ∀ k, b ≤ k → IsIso (cohomologyStepMap f k n) := by
    intro k hk
    exact (subobject_isZero_of_eq_bot _ (hbX k (by dsimp [b] at hk; omega))).isIso
      (subobject_isZero_of_eq_bot _ (hbY k (by dsimp [b] at hk; omega))) _
  refine Int.inductionOn' p b (hz b le_rfl) ?_ ?_
  · intro k hk _
    exact hz (k+1) (by omega)
  · intro k hk ih
    exact step_isIso_of_succ f (k-1) n (by rw [sub_add_cancel]; exact ih) (hg (k-1) n)

/-- At a common exhaustive step the inclusions are isomorphisms; hence the
underlying cohomology map is also an isomorphism. -/
theorem cohomology_isIso (f : FilteredMap X Y)
    (hX : DegreewiseFinite X.filtration) (hY : DegreewiseFinite Y.filtration)
    (hs : ∀ p n, IsIso (cohomologyStepMap f p n)) (n : ℤ) :
    IsIso (HomologicalComplex.homologyMap f.hom n) := by
  obtain ⟨aX, bX, haX, hbX⟩ := (cohomology_filtration X.filtration hX).finite n
  obtain ⟨aY, bY, haY, hbY⟩ := (cohomology_filtration Y.filtration hY).finite n
  let a := min aX aY
  have : IsIso (cohomologyPiece X.filtration a n).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2 (haX a (by dsimp [a]; omega))
  have : IsIso (cohomologyPiece Y.filtration a n).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2 (haY a (by dsimp [a]; omega))
  have := hs a n
  have heq : HomologicalComplex.homologyMap f.hom n =
      inv (cohomologyPiece X.filtration a n).arrow ≫ cohomologyStepMap f a n ≫
        (cohomologyPiece Y.filtration a n).arrow := by
    rw [cohomologyStepMap_arrow, IsIso.inv_hom_id_assoc]
  rw [heq]
  infer_instance

/-- The inverse of the underlying map restricts to the inverse of each step
map, so it preserves exactly the original image filtrations. -/
theorem inverse_preserves (f : FilteredMap X Y) (p n : ℤ)
    [IsIso (cohomologyStepMap f p n)]
    [IsIso (HomologicalComplex.homologyMap f.hom n)] :
    inv (cohomologyStepMap f p n) ≫ (cohomologyPiece X.filtration p n).arrow =
      (cohomologyPiece Y.filtration p n).arrow ≫
        inv (HomologicalComplex.homologyMap f.hom n) := by
  apply (cancel_mono (HomologicalComplex.homologyMap f.hom n)).1
  rw [Category.assoc, ← cohomologyStepMap_arrow, IsIso.inv_hom_id_assoc]
  simp

/-- Full comparison, together with the compatible inverse on each step. -/
theorem target_isomorphisms (f : FilteredMap X Y)
    (hX : DegreewiseFinite X.filtration) (hY : DegreewiseFinite Y.filtration)
    (D : F03Specs.PageData X.filtration) (E : F03Specs.PageData Y.filtration)
    (M : FilteredPageFunctoriality.MapData f D E) (r : ℤ) (hr : 0 ≤ r)
    (h : ∀ p n, IsIso (M.map r p n)) : S03Specs.TargetIsomorphisms f := by
  have hg := graded_isIso f hX hY D E M r hr h
  have hs := steps_isIso f hX hY hg
  have hu := cohomology_isIso f hX hY hs
  intro n
  have := hu n
  refine ⟨asIso (HomologicalComplex.homologyMap f.hom n), rfl, ?_⟩
  intro p
  have := hs p n
  exact ⟨asIso (cohomologyStepMap f p n), rfl, inverse_preserves f p n⟩

end FiniteTargetComparison

/-- HA-S03, comparison with the target for degreewise finite filtrations
in an arbitrary abelian category. -/
theorem finite_target_comparison : S03Specs.FullStatement.{v,u} := by
  intro A _ _ X Y f hX hY D E M r hr h
  exact FiniteTargetComparison.target_isomorphisms f hX hY D E M r hr h
end AdvancedHomologicalAlgebra
