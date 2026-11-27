import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.UnboundedAmitsurDescent
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainCoefficientLift
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.AmitsurHorizontalLimit
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.AmitsurTruncationTower
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.BoundedAmitsurComparison
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.TowerCohomology

/-! Unbounded Amitsur descent. -/

namespace DerivedFormalization.Descent.UnboundedAmitsurDescent

open CategoryTheory Limits
open AmitsurTotalComplexSpec.Independent (Input augmentation)
open AmitsurTruncationTower (stage)
open AmitsurTruncationTower.Independent

universe u v w

/-- The canonical augmentation into the product totalization is a
quasi-isomorphism for arbitrary cochain complexes under faithfully flat base change. -/
theorem augmentation_quasiIso (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] [Module.FaithfullyFlat A B] (X : Input.{u, w} A) :
    QuasiIso (augmentation.{u, v, w} A B X) := by
  have hLimit : QuasiIso (limMap (augmentationOfTowers A B X)) :=
    towerLimitMap_quasiIso A (liftedTower A B X) (totalTower A B X)
      (augmentationOfTowers A B X)
      (fun n i => lifted_transition_surjective A B X (Nat.le_add_right n 1) i)
      (fun n i => total_transition_surjective A B X (Nat.le_add_right n 1) i)
      (fun n => BoundedAmitsurComparison.augmentation_quasiIso A B (stage X n)
        (-(n : ℤ)) (inferInstanceAs ((X.truncGE (-(n : ℤ))).IsStrictlyGE (-(n : ℤ)))))
  have hLifted := liftedComparison_isIso A B X
  have hTotal := totalComparison_isIso A B X
  have hSquare :
      liftedComparison A B X ≫ limMap (augmentationOfTowers A B X) =
        augmentation A B X ≫ totalComparison A B X :=
    (congrArg (fun f => f ≫ limMap (augmentationOfTowers A B X))
      (source_comparison A B X).symm).trans
      ((Category.assoc _ _ _).trans (augmentation_on_limits A B X))
  have hComparison :
      QuasiIso (augmentation A B X ≫ totalComparison A B X) := by
    rw [← hSquare]
    exact quasiIso_comp _ _ (hφ' := hLimit)
  exact quasiIso_of_comp_right _ _ (hφφ' := hComparison)

/-- The augmentation induces a bijective linear map over A on the cohomology
of the original coefficient complex. -/
theorem augmentation_originalCohomology_bijective
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] [Module.FaithfullyFlat A B] (X : Input.{u, w} A) (q : ℤ) :
    Function.Bijective
      (CochainCoefficientLift.fromOriginalCohomology.{max u v}
        (X := X) (augmentation.{u, v, w} A B X) q) :=
  (CochainCoefficientLift.fromOriginal_quasiIso_iff.{max u v}
    (X := X) (augmentation.{u, v, w} A B X)).mp (augmentation_quasiIso A B X) q

/-- The canonical comparison with the homotopy limit of the finite-column
quotients is a natural isomorphism after localization. -/
theorem derived_holim_comparison :
    Specs.DerivedFormalization.Descent.UnboundedAmitsurDescent.DerivedHolimComparison.{u, v, w} :=
  AmitsurHorizontalLimit.natural_derived_iso.{u, v, w}

end DerivedFormalization.Descent.UnboundedAmitsurDescent
