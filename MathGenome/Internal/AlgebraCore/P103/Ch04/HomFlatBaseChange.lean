import MathGenome.Internal.AlgebraCore.Specs.P103.Ch04.HomFlatBaseChange

namespace P103.Ch04.HomFlatBaseChange
open TensorProduct
open P103.Specs.Ch04.HomFlatBaseChange

/-- Extension of scalars on Hom, extended B-linearly in its coefficient. -/
def canonical : canonicalType := canonicalValue

theorem formula : formulaType := by
  intro R _ B _ _ M _ _ N _ _ b b' f m
  simp [canonicalValue, LinearMap.tensorProduct, TensorProduct.smul_tmul']

/-- The library theorem uses a finite free presentation of M and preservation
of its Hom kernel by flat tensoring. Its hypotheses impose no restriction on N. -/
theorem bijective : bijectiveType := by
  intro R _ B _ _ M _ _ N _ _ _ _
  let e := (Module.FinitePresentation.isBaseChange_map R M N B).equiv
  have he : e.toLinearMap = canonicalValue R B M N := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b f
    exact (Module.FinitePresentation.isBaseChange_map R M N B).equiv_tmul b f
  rw [← he]
  exact e.bijective

theorem naturalitySource.{u,v,w,x,y} : naturalitySourceType.{u,v,w,x,y} := by
  intro R _ B _ _ M M' N _ _ _ _ _ _ h z t
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp_all
  | tmul b f =>
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' => simp_all
    | tmul b' m =>
      simp [canonicalValue, LinearMap.tensorProduct, TensorProduct.smul_tmul']

theorem naturalityTarget : naturalityTargetType := by
  intro R _ B _ _ M N N' _ _ _ _ _ _ g z t
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp_all
  | tmul b f =>
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' => simp_all
    | tmul b' m =>
      simp [canonicalValue, LinearMap.tensorProduct, TensorProduct.smul_tmul']

theorem localization : localizationType := by
  intro R _ S M _ _ N _ _ _
  let : Module.Flat R (Localization S) := IsLocalization.flat (Localization S) S
  exact bijective R (Localization S) M N

end P103.Ch04.HomFlatBaseChange
