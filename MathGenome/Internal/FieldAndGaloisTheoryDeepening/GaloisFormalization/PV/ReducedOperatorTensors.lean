import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.ReducedOperatorTensors
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.ReducedFieldBaseChange
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Pi

open scoped TensorProduct
open Algebra

namespace GaloisFormalization.PV

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Evaluation at a field factor amounts to inverting its characteristic idempotent. -/
private theorem isLocalizationAway_eval (F : ι → Type*) [∀ i, Field (F i)]
    [DecidableEq ι] (i : ι) :
    letI := (Pi.evalRingHom F i).toAlgebra
    IsLocalization.Away (Pi.single i 1 : ∀ i, F i) (F i) := by
  let := (Pi.evalRingHom F i).toAlgebra
  refine IsLocalization.away_of_isIdempotentElem ?_ (RingHom.ker_evalRingHom F i)
    (Function.surjective_eval i)
  simp [IsIdempotentElem, ← Pi.single_mul_left]

/-- Base change to a finite product of field extensions of the corresponding
characteristic-zero factors preserves reducedness. -/
theorem reducedProductBaseChange.{uι, uκ, uF, uL, uA} :
    Specs.GaloisFormalization.PV.reducedProductBaseChange.{uι, uκ, uF, uL, uA} := by
  classical
  intro ι κ _ _ F L component _ _ _ _ A _ _ productAlgebra _ _ compatible
  let R := ∀ i, F i
  let : Fintype κ := Fintype.ofFinite κ
  let (i : ι) : Algebra R (F i) := (Pi.evalRingHom F i).toAlgebra
  let (j : κ) : Algebra R (L j) :=
    ((algebraMap (F (component j)) (L j)).comp (Pi.evalRingHom F (component j))).toAlgebra
  have sameAlgebra : productAlgebra = Pi.algebra κ L := by
    apply Algebra.algebra_ext
    intro f
    funext j
    exact compatible f j
  subst productAlgebra
  -- Each factor is the localization of A at the image of its base idempotent.
  let B (i : ι) := F i ⊗[R] A
  have (i : ι) : FiniteType (F i) (B i) := FiniteType.baseChange (F i)
  have (i : ι) : IsReduced (B i) := by
    have : IsLocalization.Away (Pi.single i 1 : R) (F i) := isLocalizationAway_eval F i
    have : IsLocalization.Away (algebraMap R A (Pi.single i 1)) (B i) :=
      IsLocalization.Away.tensorRight _ _
    let M := Submonoid.powers (algebraMap R A (Pi.single i 1))
    let e := IsLocalization.algEquiv M (B i) (Localization M)
    exact isReduced_of_injective e e.injective
  have (j : κ) : IsScalarTower R (F (component j)) (L j) := .of_algebraMap_eq' rfl
  have (j : κ) : IsReduced (L j ⊗[F (component j)] B (component j)) :=
    reducedFieldBaseChange (F (component j)) (L j) (B (component j))
  let factorEquiv (j : κ) : A ⊗[R] L j ≃+* L j ⊗[F (component j)] B (component j) :=
    let i := component j
    let cancel := IsPushout.cancelBaseChangeAlg R A (F i) (B i) (L j)
    cancel.symm.toRingEquiv.trans (Algebra.TensorProduct.comm (F i) (B i) (L j)).toRingEquiv
  let equiv := (Algebra.TensorProduct.comm R (∀ j, L j) A).toRingEquiv.trans
    ((Algebra.TensorProduct.piRight R A A L).toRingEquiv.trans (RingEquiv.piCongrRight factorEquiv))
  exact isReduced_of_injective equiv equiv.injective

/-- The two cases of the reduced tensor lemma. -/
theorem reducedOperatorTensors.{uK, uE, uB, uι, uκ, uF, uL, uA} :
    Specs.GaloisFormalization.PV.reducedFieldBaseChange.{uK, uE, uB} ∧
      Specs.GaloisFormalization.PV.reducedProductBaseChange.{uι, uκ, uF, uL, uA} :=
  ⟨reducedFieldBaseChange, reducedProductBaseChange⟩

end GaloisFormalization.PV
