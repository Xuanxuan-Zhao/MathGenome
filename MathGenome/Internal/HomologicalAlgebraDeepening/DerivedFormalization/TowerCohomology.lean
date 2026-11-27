import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.TowerExactSequence
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.TowerCohomology
import Mathlib.Algebra.Homology.HomologySequenceLemmas

namespace DerivedFormalization

open CategoryTheory CategoryTheory.Limits Opposite
open HomologicalComplex HomologicalComplex.HomologySequence
open Specs.DerivedFormalization.TowerExactSequence (transition towerProduct)

universe u v

/-- The inverse limit of a degreewise-surjective tower of acyclic cochain complexes
is acyclic. -/
theorem towerLimit_acyclic (R : Type u) [Ring R] (A : ℕᵒᵖ ⥤ Comp.{v} R)
    (hs : ∀ (n : ℕ) (i : ℤ), Function.Surjective ((transition A n).f i))
    (ha : ∀ n : ℕ, (A.obj (op n)).Acyclic) : (limit A).Acyclic := by
  have hProduct (i : ℤ) : IsZero ((towerProduct A).homology i) := by
    let cmp := piComparison (cohomologyFunctor R i) (fun n : ℕ ↦ A.obj (op n))
    have hCmp : IsIso cmp := cohomology_preservesProduct R ℕ (fun n ↦ A.obj (op n)) i
    refine IsZero.of_iso ?_ (@asIso _ _ _ _ cmp hCmp)
    rw [IsZero.iff_id_eq_zero]
    apply Pi.hom_ext
    intro n
    exact ((ha n i).isZero_homology).eq_of_tgt _ _
  intro i
  rw [exactAt_iff_isZero_homology]
  have hi := ComplexShape.up_mk (i - 1) i (sub_add_cancel i 1)
  have hExact := (towerShortComplex_shortExact R A hs).homology_exact₁ (i - 1) i hi
  exact hExact.isZero_X₂ ((hProduct (i - 1)).eq_of_src _ _) ((hProduct i).eq_of_tgt _ _)

/-- A stagewise quasi-isomorphism between degreewise-surjective towers induces
a quasi-isomorphism on their inverse limits. -/
theorem towerLimitMap_quasiIso (R : Type u) [Ring R] (A B : ℕᵒᵖ ⥤ Comp.{v} R)
    (f : A ⟶ B)
    (hA : ∀ (n : ℕ) (i : ℤ), Function.Surjective ((transition A n).f i))
    (hB : ∀ (n : ℕ) (i : ℤ), Function.Surjective ((transition B n).f i))
    (hf : ∀ n : ℕ, QuasiIso (f.app (op n))) : QuasiIso (limMap f) := by
  let p : towerProduct A ⟶ towerProduct B :=
    CategoryTheory.Limits.Pi.map (fun n : ℕ ↦ f.app (op n))
  have hProduct (i : ℤ) : IsIso (homologyMap p i) := by
    let a := fun n : ℕ ↦ A.obj (op n)
    let b := fun n : ℕ ↦ B.obj (op n)
    let H := cohomologyFunctor R i
    have (n : ℕ) : IsIso (H.map (f.app (op n))) :=
      (quasiIsoAt_iff_isIso_homologyMap _ i).1 ((quasiIso_iff _).1 (hf n) i)
    have : IsIso (piComparison H a) := cohomology_preservesProduct R ℕ a i
    have : IsIso (piComparison H b) := cohomology_preservesProduct R ℕ b i
    let pH := CategoryTheory.Limits.Pi.map (f := fun n ↦ H.obj (a n))
      (g := fun n ↦ H.obj (b n)) (fun n ↦ H.map (f.app (op n)))
    have h :
        H.map p ≫ piComparison H b = piComparison H a ≫ pH := by
      apply Pi.hom_ext
      intro n
      have hπ : pH ≫ Pi.π (fun n ↦ H.obj (b n)) n =
          Pi.π (fun n ↦ H.obj (a n)) n ≫ H.map (f.app (op n)) :=
        Limits.Pi.map_π (fun n ↦ H.map (f.app (op n))) n
      rw [Category.assoc, Category.assoc, piComparison_comp_π, hπ,
        piComparison_comp_π_assoc, ← H.map_comp, ← H.map_comp]
      exact congrArg H.map (Limits.Pi.map_π (fun n ↦ f.app (op n)) n)
    have : IsIso (H.map p ≫ piComparison H b) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right (H.map p) (piComparison H b)
  let φ : towerShortComplex A ⟶ towerShortComplex B :=
    { τ₁ := limMap f
      τ₂ := p
      τ₃ := p
      comm₁₂ := (towerShortComplex_naturality R A B f).1
      comm₂₃ := (towerShortComplex_naturality R A B f).2 }
  have hExactA := towerShortComplex_shortExact R A hA
  have hExactB := towerShortComplex_shortExact R B hB
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  -- Center the five-term comparison at the cohomology of the limit in degree i.
  have hi := ComplexShape.up_mk (i - 1) i (sub_add_cancel i 1)
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono' (k := 1) (by decide)
    (composableArrows₅_exact hExactA (i - 1) i hi)
    (composableArrows₅_exact hExactB (i - 1) i hi)
    (mapComposableArrows₅ φ hExactA hExactB (i - 1) i hi)
    1 2 3 4 5 rfl rfl rfl rfl rfl
    (by have := hProduct (i - 1); exact IsIso.epi_of_iso (homologyMap p (i - 1)))
    (hProduct (i - 1)) (hProduct i)
    (by have := hProduct i; exact IsIso.mono_of_iso (homologyMap p i))

end DerivedFormalization
