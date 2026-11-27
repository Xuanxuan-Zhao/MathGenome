import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Complexes.Projective
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Model.Complexes.CellFactorization
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Model.Localization

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty ZeroObject
open HomologicalComplex HomotopicalAlgebra

universe u

namespace DerivedFormalization.Model.Complexes

/-- The cofibrations of the projective model structure. -/
def projectiveCofibrations (A : Type u) [Ring A] : MorphismProperty (Cochains A) :=
  (degreewiseSurjective A ⊓ quasiIso (ModuleCat A) (ComplexShape.up ℤ)).llp

instance (A : Type u) [Ring A] : (projectiveCofibrations A).IsStableUnderRetracts := by
  unfold projectiveCofibrations
  infer_instance

theorem iCell_le_projectiveCofibrations (A : Type u) [Ring A] :
    iCell A ≤ projectiveCofibrations A := by
  simpa only [iCell, projectiveCofibrations, ← i_rlp A] using
    (I A).transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp ℕ

private theorem jCell_le_llp (A : Type u) [Ring A] :
    jCell A ≤ (degreewiseSurjective A).llp := by
  simpa only [jCell, ← j_rlp A] using
    (J A).transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp ℕ

private theorem quasiIso_coprod_inl_of_contractible {A : Type u} [Ring A]
    (X D : Cochains A) (h : Homotopy (𝟙 D) 0) :
    QuasiIso (coprod.inl : X ⟶ X ⨿ D) := by
  let p : X ⨿ D ⟶ X := coprod.desc (𝟙 X) 0
  let q : X ⨿ D ⟶ D := coprod.desc 0 (𝟙 D)
  have hsum : p ≫ coprod.inl + q ≫ coprod.inr = 𝟙 (X ⨿ D) := by
    apply coprod.hom_ext <;> simp [Preadditive.comp_add, p, q]
  have hq : Homotopy (q ≫ (coprod.inr : D ⟶ X ⨿ D)) 0 := by
    simpa only [Category.comp_id, comp_zero, zero_comp] using
      ((h.compLeft q).compRight (coprod.inr : D ⟶ X ⨿ D))
  let e : HomotopyEquiv X (X ⨿ D) :=
    { hom := coprod.inl
      inv := p
      homotopyHomInvId := Homotopy.ofEq (by simp [p])
      homotopyInvHomId := by
        have h' := (Homotopy.refl (p ≫ coprod.inl)).add hq.symm
        simpa only [add_zero, hsum] using h' }
  exact e.quasiIso_hom

/-- A disk cell map lifts against surjections and induces isomorphisms on cohomology. -/
theorem jCell_le_projectiveTrivialCofibrations (A : Type u) [Ring A] :
    jCell A ≤ projectiveCofibrations A ⊓ quasiIso (ModuleCat A) (ComplexShape.up ℤ) := by
  intro X Y f hf
  refine ⟨fun _ _ p hp ↦ jCell_le_llp A f hf p hp.1, ?_⟩
  obtain ⟨_, _, ⟨e, he⟩, ⟨hD⟩⟩ := jCellDecomposition A f hf
  have := quasiIso_coprod_inl_of_contractible X _ hD
  rw [← he, mem_quasiIso_iff]
  exact quasiIso_comp coprod.inl e.hom

private theorem iCellFactorizationWithTrivialFibrations (A : Type u) [Ring A] :
    HasFunctorialFactorization (iCell A)
      (degreewiseSurjective A ⊓ quasiIso (ModuleCat A) (ComplexShape.up ℤ)) := by
  obtain ⟨F, _⟩ := iCellFactorization A
  have h : HasFunctorialFactorization (iCell A) (I A).rlp := ⟨⟨F⟩⟩
  rwa [i_rlp A] at h

private theorem jCellFactorizationWithFibrations (A : Type u) [Ring A] :
    HasFunctorialFactorization (jCell A) (degreewiseSurjective A) := by
  obtain ⟨F, _⟩ := jCellFactorization A
  have h : HasFunctorialFactorization (jCell A) (J A).rlp := ⟨⟨F⟩⟩
  rwa [j_rlp A] at h

/-- The projective cofibrations are precisely the arrow retracts of I-cell maps. -/
theorem iCellRetracts_eq_projectiveCofibrations (A : Type u) [Ring A] :
    (iCell A).retracts = projectiveCofibrations A := by
  refine le_antisymm (retracts_le_iff.mpr (iCell_le_projectiveCofibrations A)) ?_
  have := iCellFactorizationWithTrivialFibrations A
  intro X Y f hf
  let F := factorizationData (iCell A)
    (degreewiseSurjective A ⊓ quasiIso (ModuleCat A) (ComplexShape.up ℤ)) f
  have := hf F.p F.hp
  exact ⟨_, _, F.i, RetractArrow.ofLeftLiftingProperty F.fac, F.hi⟩

/-- The projective trivial cofibrations are precisely the arrow retracts of J-cell maps. -/
theorem jCellRetracts_eq_projectiveTrivialCofibrations (A : Type u) [Ring A] :
    (jCell A).retracts =
      projectiveCofibrations A ⊓ quasiIso (ModuleCat A) (ComplexShape.up ℤ) := by
  refine le_antisymm (retracts_le_iff.mpr (jCell_le_projectiveTrivialCofibrations A)) ?_
  have := jCellFactorizationWithFibrations A
  intro X Y f hf
  let F := factorizationData (jCell A) (degreewiseSurjective A) f
  have hp := (quasiIso (ModuleCat A) (ComplexShape.up ℤ)).of_precomp F.i F.p
    (jCell_le_projectiveTrivialCofibrations A F.i F.hi).2 (F.fac.symm ▸ hf.2)
  have := hf.1 F.p ⟨F.hp, hp⟩
  exact ⟨_, _, F.i, RetractArrow.ofLeftLiftingProperty F.fac, F.hi⟩

/-- Lifting against the fibrations characterizes the projective trivial cofibrations. -/
theorem projectiveTrivialCofibrations_eq_llp (A : Type u) [Ring A] :
    (degreewiseSurjective A).llp =
      projectiveCofibrations A ⊓ quasiIso (ModuleCat A) (ComplexShape.up ℤ) := by
  rw [← jCellRetracts_eq_projectiveTrivialCofibrations A]
  refine le_antisymm ?_ (retracts_le_iff.mpr (jCell_le_llp A))
  have := jCellFactorizationWithFibrations A
  intro X Y f hf
  let F := factorizationData (jCell A) (degreewiseSurjective A) f
  have := hf F.p F.hp
  exact ⟨_, _, F.i, RetractArrow.ofLeftLiftingProperty F.fac, F.hi⟩

theorem projectiveCofibrationFactorization (A : Type u) [Ring A] :
    HasFunctorialFactorization (projectiveCofibrations A)
      (degreewiseSurjective A ⊓ quasiIso (ModuleCat A) (ComplexShape.up ℤ)) := by
  have := iCellFactorizationWithTrivialFibrations A
  exact ⟨⟨(functorialFactorizationData (iCell A) _).ofLE
    (iCell_le_projectiveCofibrations A) le_rfl⟩⟩

theorem projectiveFibrationFactorization (A : Type u) [Ring A] :
    HasFunctorialFactorization
      (projectiveCofibrations A ⊓ quasiIso (ModuleCat A) (ComplexShape.up ℤ))
      (degreewiseSurjective A) := by
  have := jCellFactorizationWithFibrations A
  exact ⟨⟨(functorialFactorizationData (jCell A) _).ofLE
    (jCell_le_projectiveTrivialCofibrations A) le_rfl⟩⟩

open Specs.ComplexProjective in
theorem projectiveModelExists : projectiveModelExistsType.{u} := by
  intro A _
  let fibs : CategoryWithFibrations (Cochains A) := ⟨degreewiseSurjective A⟩
  let cofs : CategoryWithCofibrations (Cochains A) := ⟨projectiveCofibrations A⟩
  let weqs : CategoryWithWeakEquivalences (Cochains A) :=
    ⟨quasiIso (ModuleCat A) (ComplexShape.up ℤ)⟩
  have : HasFunctorialFactorization (cofibrations (Cochains A)) (trivialFibrations (Cochains A)) :=
    projectiveCofibrationFactorization A
  have : HasFunctorialFactorization (trivialCofibrations (Cochains A)) (fibrations (Cochains A)) :=
    projectiveFibrationFactorization A
  have : HasLimits (Cochains A) := (degreewiseLimitsAndColimits A).1
  have : HasColimits (Cochains A) := (degreewiseLimitsAndColimits A).2.1
  let model : ModelCategory (Cochains A) :=
    { categoryWithFibrations := fibs
      categoryWithCofibrations := cofs
      categoryWithWeakEquivalences := weqs
      cm2 := by
        change (quasiIso (ModuleCat A) (ComplexShape.up ℤ)).HasTwoOutOfThreeProperty
        infer_instance
      cm3a := by
        change (quasiIso (ModuleCat A) (ComplexShape.up ℤ)).IsStableUnderRetracts
        infer_instance
      cm3b := by
        change (degreewiseSurjective A).IsStableUnderRetracts
        rw [← j_rlp A]
        infer_instance
      cm3c := by
        change (projectiveCofibrations A).IsStableUnderRetracts
        infer_instance
      cm4a := by
        intro X Y Z T i p _ _ _
        have hi := mem_trivialCofibrations i
        change (projectiveCofibrations A ⊓ quasiIso (ModuleCat A) (ComplexShape.up ℤ)) i at hi
        rw [← projectiveTrivialCofibrations_eq_llp A] at hi
        exact hi p (mem_fibrations p)
      cm4b := by
        intro X Y Z T i p _ _ _
        exact (show projectiveCofibrations A i from mem_cofibrations i) p (mem_trivialFibrations p) }
  exact ⟨⟨FunctorialModelCategory.ofInstances (Cochains A), rfl, rfl, rfl⟩⟩

/-- The map to the zero complex is surjective in each degree. -/
theorem projectiveAllFibrant : Specs.ComplexProjective.allFibrantType.{u} := by
  intro A _ M
  let model := M.model
  intro X
  apply (isFibrant_iff_of_isTerminal (0 : X ⟶ 0) (isZero_zero _).isTerminal).2
  rw [fibration_iff, M.fibrations_eq]
  intro n y
  have hz : IsZero (((0 : Cochains A)).X n) :=
    (eval (ModuleCat A) (ComplexShape.up ℤ) n).map_isZero (isZero_zero _)
  have := ModuleCat.isZero_iff_subsingleton.mp hz
  exact ⟨0, Subsingleton.elim _ _⟩

/-- The two localizations at quasi-isomorphisms give the derived comparison. -/
theorem projectiveDerivedComparison : Specs.ComplexProjective.derivedComparisonType.{u} := by
  intro A _ M
  let model := M.model
  let derived := HasDerivedCategory.standard (ModuleCat.{u} A)
  obtain ⟨r⟩ := Model.replacementExists (Cochains A)
  have : r.localization.IsLocalization (quasiIso (ModuleCat A) (ComplexShape.up ℤ)) :=
    M.weakEquivalences_eq ▸ r.isLocalization
  let e := Localization.uniq r.localization (DerivedCategory.Q (C := ModuleCat A))
    (quasiIso (ModuleCat A) (ComplexShape.up ℤ))
  exact ⟨r, e, ⟨Localization.compUniqFunctor _ _ _⟩⟩

end DerivedFormalization.Model.Complexes
