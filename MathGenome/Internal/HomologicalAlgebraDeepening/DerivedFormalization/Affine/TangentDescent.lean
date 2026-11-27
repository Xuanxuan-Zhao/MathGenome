import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.TangentDescent
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.CotangentAmitsurModels
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.SquareZeroHomotopy
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.PerfectMappingDescent
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

open CategoryTheory
open scoped TensorProduct ZeroObject

namespace DerivedFormalization.Affine.TangentDescent

noncomputable section

universe u v w s t j
attribute [local instance] HasDerivedCategory.standard

open Specs.DerivedFormalization
open Specs.DerivedFormalization.Affine.TangentDescent
open Cochains (compValue derivedValue qValue)
open CochainModels (internalHomValue internalHomMapValue)
open Affine.CotangentAmitsurModels (BP baseMap columnMap)
open AmitsurAlgebrasSpec
open Specs.DerivedFormalization.Descent.PerfectHomBaseChange (extend restrict)
open CochainComplex.HomComplex (Cochain)

open Specs.DerivedFormalization.Descent.PerfectHomBaseChange
  (comparison changeCoefficients changeHomCoefficients)
open DerivedFormalization.Descent
  (homBaseChange_isIso homBaseChange_changeCoefficients changeCoefficients_apply)

open private tensorRestrictionIso from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.PerfectMappingDescent
open private powerRingEquiv powerRingEquiv_algebraMap powerRingEquiv_map
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.AmitsurRingTransport

set_option backward.isDefEq.respectTransparency false
set_option linter.checkUnivs false
set_option linter.style.haveILetI false
set_option maxHeartbeats 600000

section Coefficients

variable {R : Type v} {S : Type u} {T : Type w}
  [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

private def extendRingIso (e : S ≃ₐ[R] T) (X : compValue.{max u w t} R) :
    (restrict.{v,u,max u w t} R S).obj ((extend.{v,u,max u w t} R S).obj X) ≅
    (restrict.{v,w,max u w t} R T).obj ((extend.{v,w,max u w t} R T).obj X) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (tensorRestrictionIso R S (X.X n)).symm ≪≫
      (e.toLinearEquiv.rTensor (X.X n)).toModuleIso ≪≫ tensorRestrictionIso R T (X.X n)) (by
    intro i j _
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    let f := (((tensorRestrictionIso R S (X.X i)).symm ≪≫
      (e.toLinearEquiv.rTensor (X.X i)).toModuleIso ≪≫ tensorRestrictionIso R T (X.X i)).hom ≫
        ((restrict.{v,w,max u w t} R T).obj ((extend.{v,w,max u w t} R T).obj X)).d i j).hom
    let g := ((((restrict.{v,u,max u w t} R S).obj ((extend.{v,u,max u w t} R S).obj X)).d i j) ≫
      ((tensorRestrictionIso R S (X.X j)).symm ≪≫
        (e.toLinearEquiv.rTensor (X.X j)).toModuleIso ≪≫ tensorRestrictionIso R T (X.X j)).hom).hom
    change f z = g z
    let x : S ⊗[R] X.X i := z
    change f x = g x
    induction x using TensorProduct.inductionOn with
    | tmul s x => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy])

private theorem extendRingIso_apply (e : S ≃ₐ[R] T) (X : compValue.{max u w t} R)
    (n : ℤ) (s : S) (z : X.X n) :
    (extendRingIso.{u,v,w,t} e X).hom.f n (s ⊗ₜ[R] z) = e s ⊗ₜ[R] z := rfl

private def restrictedHomComparison (P X : compValue.{max u t} R)
    (hP : Affine.CotangentAmitsurModels.FiniteProjective P) :=
  letI := homBaseChange_isIso R S P X hP.1 hP.2.1 hP.2.2
  (restrict.{v,u,max u t} R S).mapIso (asIso (comparison S P X))

private theorem homCoface_on_comparison {T : Type u} [CommRing T] [Algebra R T]
    (φ : S →ₐ[R] T) (P X : compValue.{max u t} R) (n : ℤ) (s : S)
    (z : Cochain P X n) :
    letI : Algebra S T := φ.toRingHom.toAlgebra
    letI : IsScalarTower R S T := IsScalarTower.of_algHom φ
    (changeHomCoefficients R S T P X).f n ((comparison S P X).f n (s ⊗ₜ[R] z)) =
      (comparison T P X).f n (φ s ⊗ₜ[R] z) := by
  letI : Algebra S T := φ.toRingHom.toAlgebra
  letI : IsScalarTower R S T := IsScalarTower.of_algHom φ
  have hc := homBaseChange_changeCoefficients R S T φ P X
  have hq := ConcreteCategory.congr_hom (HomologicalComplex.congr_hom hc n)
    (show S ⊗[R] (internalHomValue P X).X n from s ⊗ₜ[R] z)
  change (comparison T P X).f n
      ((changeCoefficients R S T (internalHomValue P X)).f n (s ⊗ₜ[R] z)) =
    (changeHomCoefficients R S T P X).f n ((comparison S P X).f n (s ⊗ₜ[R] z)) at hq
  rw [changeCoefficients_apply R S T φ (internalHomValue P X) n s z] at hq
  exact hq.symm

private theorem comparison_unit_apply (P X : compValue.{t} R) (n : ℤ) (z : Cochain P X n) :
    (comparison S P X).f n (1 ⊗ₜ[R] z) =
      Specs.DerivedFormalization.Descent.PerfectHomBaseChange.extendCochain S n z :=
  by
    letI := Module.restrictScalars R S
      (Cochain ((extend R S).obj P) ((extend R S).obj X) n)
    letI := IsScalarTower.restrictScalars R S
      (Cochain ((extend R S).obj P) ((extend R S).obj X) n)
    let f := Specs.DerivedFormalization.Descent.PerfectHomBaseChange.extendCochain S n
      (P := P) (X := X)
    change f.liftBaseChange S (1 ⊗ₜ[R] z) = f z
    exact LinearMap.liftBaseChange_one_tmul S f z

private theorem scalarExtension_natural {T : Type u} [CommRing T] [Algebra R T]
    (φ : S →ₐ[R] T) {P L : compValue.{max u t} R} (f : P ⟶ L) :
    letI : Algebra S T := φ.toRingHom.toAlgebra
    letI : IsScalarTower R S T := IsScalarTower.of_algHom φ
    (restrict.{v,u,max u t} R S).map ((extend.{v,u,max u t} R S).map f) ≫
        changeCoefficients.{v,u,max u t} R S T L =
      changeCoefficients.{v,u,max u t} R S T P ≫
        (restrict.{v,u,max u t} R T).map ((extend.{v,u,max u t} R T).map f) := by
  letI : Algebra S T := φ.toRingHom.toAlgebra
  letI : IsScalarTower R S T := IsScalarTower.of_algHom φ
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let c := ((restrict.{v,u,max u t} R S).map ((extend.{v,u,max u t} R S).map f) ≫
    changeCoefficients.{v,u,max u t} R S T L).f n
  let d := (changeCoefficients.{v,u,max u t} R S T P ≫
    (restrict.{v,u,max u t} R T).map ((extend.{v,u,max u t} R T).map f)).f n
  let y : S ⊗[R] P.X n := x
  change c y = d y
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul s z =>
    change (changeCoefficients.{v,u,max u t} R S T L).f n (s ⊗ₜ[R] f.f n z) =
      ((extend.{v,u,max u t} R T).map f).f n
        ((changeCoefficients.{v,u,max u t} R S T P).f n (s ⊗ₜ[R] z))
    rw [changeCoefficients_apply R S T φ L n s _, changeCoefficients_apply R S T φ P n s z]
    rfl

end Coefficients

theorem columnComparison : ColumnComparisonType.{u,v,w,s,t,j} := by
  intro A B C _ _ _ _ _ _
  obtain ⟨_, _, e₀, _, _, he⟩ := CotangentAmitsurModels.ringPowers A B C
  let up : BaseChange A B C ≃ₐ[B] coverRing.{u,v,w,j} A B C := (ULift.algEquiv (R := B)).symm
  let r (p : ℕ) := powerRingEquiv (RingEquiv.refl B) up.toRingEquiv up.commutes (p + 1)
  let e (p : ℕ) : BP A B C p ≃ₐ[B] powerRing.{u,v,w,j} A B C p :=
    (e₀ p).trans { r p with commutes' := powerRingEquiv_algebraMap _ _ _ _ }
  have hn {p q : ℕ} (f : Fin (p+1) → Fin (q+1)) (z : BP A B C p) :
      e q (columnMap (A := A) (B := B) (C := C) f z) = map f (e p z) :=
    (congrArg (r q) (DFunLike.congr_fun (he f) z)).trans
      (powerRingEquiv_map (RingEquiv.refl B) up.toRingEquiv up.commutes f (e₀ p z))
  let hL (p : ℕ) (P X : compValue.{max u v w s t j} B)
      (hP : Affine.CotangentAmitsurModels.FiniteProjective P) :=
    restrictedHomComparison.{max u v w,v,max u v w s t j} (S := BP A B C p) P X hP
  let hR (p : ℕ) (P X : compValue.{max u v w s t j} B)
      (hP : Affine.CotangentAmitsurModels.FiniteProjective P) :=
    restrictedHomComparison.{max u v w j,v,max u v w s t j} (S := powerRing.{u,v,w,j} A B C p) P X hP
  let a (p : ℕ) (P X : compValue.{max u v w s t j} B)
      (hP : Affine.CotangentAmitsurModels.FiniteProjective P) :=
    (hL p P X hP).symm ≪≫ extendRingIso.{max u v w,v,max u v w j,max u v w s t j}
      (e p) (internalHomValue P X) ≪≫ hR p P X hP
  refine ⟨{ ring := e, ring_natural := hn, iso := a, cofaces := ?_, unit := ?_ }⟩
  · intro p q f P X hP
    apply (cancel_epi (hL p P X hP).hom).mp
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    let m₁ := (((hL p P X hP).hom ≫ onColumn.{u,v,w,s,t,j} (A := A) (C := C) f P X ≫
      (a q P X hP).hom).f n).hom
    let m₂ := (((hL p P X hP).hom ≫ (a p P X hP).hom ≫
      onPower.{u,v,w,s,t,j} (A := A) (C := C) f P X).f n).hom
    intro y
    let bz : BP A B C p ⊗[B] (internalHomValue P X).X n := y
    change m₁ bz = m₂ bz
    induction bz using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul b z =>
      have eval (j : ℕ) (b : BP A B C j) :
          (a j P X hP).hom.f n ((comparison (BP A B C j) P X).f n (b ⊗ₜ[B] z)) =
            (comparison (powerRing.{u,v,w,j} A B C j) P X).f n (e j b ⊗ₜ[B] z) := by
        have h := HomologicalComplex.congr_hom ((hL j P X hP).hom_inv_id) n
        have hh := ConcreteCategory.congr_hom h
          (show BP A B C j ⊗[B] (internalHomValue P X).X n from b ⊗ₜ[B] z)
        change (hL j P X hP).inv.f n ((comparison (BP A B C j) P X).f n (b ⊗ₜ[B] z)) =
          b ⊗ₜ[B] z at hh
        change (comparison (powerRing.{u,v,w,j} A B C j) P X).f n
            ((extendRingIso.{max u v w,v,max u v w j,max u v w s t j} (e j) (internalHomValue P X)).hom.f n
              ((hL j P X hP).inv.f n ((comparison (BP A B C j) P X).f n (b ⊗ₜ[B] z)))) = _
        rw [hh, extendRingIso_apply.{max u v w,v,max u v w j,max u v w s t j}]
      let fL : BP A B C p →ₐ[B] BP A B C q := columnMap f
      let fR : powerRing.{u,v,w,j} A B C p →ₐ[B] powerRing.{u,v,w,j} A B C q := map f
      change (a q P X hP).hom.f n
          ((onColumn.{u,v,w,s,t,j} (A := A) (C := C) f P X).f n
            ((comparison (BP A B C p) P X).f n (b ⊗ₜ[B] z))) =
        (onPower.{u,v,w,s,t,j} (A := A) (C := C) f P X).f n
          ((a p P X hP).hom.f n ((comparison (BP A B C p) P X).f n (b ⊗ₜ[B] z)))
      rw [show _ = (comparison (BP A B C q) P X).f n (fL b ⊗ₜ[B] z) from
            homCoface_on_comparison.{max u v w,v,max u v w s t j} fL P X n b z,
        eval, eval, show _ = (comparison (powerRing.{u,v,w,j} A B C q) P X).f n (fR (e p b) ⊗ₜ[B] z) from
            homCoface_on_comparison.{max u v w j,v,max u v w s t j} fR P X n (e p b) z, hn f b]
  · intro p P X hP n z
    rw [← comparison_unit_apply (S := BP A B C p), ← comparison_unit_apply (S := powerRing.{u,v,w,j} A B C p)]
    have h := ConcreteCategory.congr_hom
      (HomologicalComplex.congr_hom ((hL p P X hP).hom_inv_id) n)
      (show BP A B C p ⊗[B] (internalHomValue P X).X n from 1 ⊗ₜ[B] z)
    change (hL p P X hP).inv.f n ((comparison (BP A B C p) P X).f n (1 ⊗ₜ[B] z)) =
      1 ⊗ₜ[B] z at h
    change (comparison (powerRing.{u,v,w,j} A B C p) P X).f n
        ((extendRingIso.{max u v w,v,max u v w j,max u v w s t j} (e p) (internalHomValue P X)).hom.f n
          ((hL p P X hP).inv.f n ((comparison (BP A B C p) P X).f n (1 ⊗ₜ[B] z)))) = _
    rw [h, extendRingIso_apply.{max u v w,v,max u v w j,max u v w s t j}, map_one]


section Descent

open Opposite
open Specs.DerivedFormalization.Descent.PerfectMappingDescent hiding P X
open Specs.DerivedFormalization.DerivedHomModels (Models rHomValue)
open private liftedPerfect boundedAbove_kProjective homFunctor
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.PerfectMappingDescent

private def fixedHomModelIso {K : Type*} [Category K]
    {R : Type v} [CommRing R] (H : Models.{v,t} R)
    {P : compValue.{t} R} {L : derivedValue.{t} R}
    (α : (qValue R).obj P ≅ L) (hP : P.IsKProjective)
    (V : K ⥤ compValue.{t} R) :
    homInTarget P V (homFunctor R) ⋙ qValue R ≅ derivedHomInTarget L V H :=
  NatIso.ofComponents
    (fun X => DerivedHomModels.modelIso H
      (DerivedHomModels.representative α)
      (DerivedHomModels.representative (Iso.refl ((qValue R).obj (V.obj X))))
      (Or.inl hP))
    (by
      intro X Y f
      exact DerivedHomModels.modelIso_chain_natural H α α (Iso.refl _) (Iso.refl _)
        (Or.inl hP) (Or.inl hP) (𝟙 L) ((qValue R).map (V.map f))
        (𝟙 P) (V.map f) (by simp) (by simp))

private theorem extensionKProjective {R : Type v} {S : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    (P : compValue.{max w t} R) (hP : Affine.CotangentAmitsurModels.FiniteProjective P) :
    CochainComplex.IsKProjective ((extend.{v,w,max w t} R S).obj P) := by
  obtain ⟨⟨_, U, hU⟩, _, hproj⟩ := hP
  apply boundedAbove_kProjective.{w,t} _ U
  · intro i hi
    letI := hU i (Or.inr hi)
    change Subsingleton (S ⊗[R] P.X i)
    infer_instance
  · intro i
    letI := hproj i
    change Module.Projective S (S ⊗[R] P.X i)
    infer_instance

open AmitsurTotalComplexSpec (rowIndex)
open scoped BigOperators

section OriginalProduct

variable (A : Type u) (B : Type v) (C : Type w)
  [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
variable (I : Inputs.{v,s,t} B)


set_option maxHeartbeats 1200000 in
/-- Products preserve the comparison of columns, including their signed
horizontal and vertical differentials. -/
private def compareOriginalProduct
    (E : ColumnComparison.{u,v,w,s,t,j} A B C)
    (hP : Affine.CotangentAmitsurModels.FiniteProjective
      (Specs.DerivedFormalization.Descent.PerfectMappingDescent.P.{v,max u v w j,s,t} B I))
    (sq : ∀ n, totalStep B (coverRing.{u,v,w,j} A B C) I n ≫
      totalStep B (coverRing.{u,v,w,j} A B C) I (n + 1) = 0) :
    ProductComparison.{u,v,w,s,t,j} A B C I E hP sq := by
  let S₀ := coverRing.{u,v,w,j} A B C
  let Pₗ := Specs.DerivedFormalization.Descent.PerfectMappingDescent.P.{v,max u v w j,s,t} B I
  let Mₗ := Specs.DerivedFormalization.Descent.PerfectMappingDescent.X.{v,max u v w j,s,t} B I
  let K₀ := originalColumn.{u,v,w,s,t,j} A B C I
  let K₁ := column.{v,max u v w j,s,t} B S₀ I
  let e (p : ℕ) (m : ℤ) : (K₀ p).X m ≅ (K₁ p).X m :=
    (HomologicalComplex.eval _ _ m).mapIso (E.iso p Pₗ Mₗ hP)
  have vertical (p : ℕ) (n m : ℤ) :
      (e p n).hom ≫ (K₁ p).d n m = (K₀ p).d n m ≫ (e p m).hom :=
    (E.iso p Pₗ Mₗ hP).hom.comm n m
  have coface (p : ℕ) (i : Fin (p + 2)) (m : ℤ) :
      (e p m).hom ≫ (localCoface B S₀ I i).f m =
        (onColumn.{u,v,w,s,t,j} (A := A) (C := C) i.succAbove Pₗ Mₗ).f m ≫
          (e (p + 1) m).hom :=
    (HomologicalComplex.congr_hom (E.cofaces i.succAbove Pₗ Mₗ hP) m).symm
  have horizontal (p : ℕ) (m : ℤ) :
      (e p m).hom ≫ (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (localCoface B S₀ I i).f m) =
        (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
          (onColumn.{u,v,w,s,t,j} (A := A) (C := C) i.succAbove Pₗ Mₗ).f m) ≫
          (e (p + 1) m).hom := by
    simp only [Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.comp_zsmul,
      Preadditive.zsmul_comp, coface]
  have diagonal (n : ℤ) (p : ℕ) :
      (e p (rowIndex n p)).hom ≫ diagonalHorizontal B S₀ I n p =
        originalHorizontal.{u,v,w,s,t,j} A B C I n p ≫
          (e (p + 1) (rowIndex (n + 1) (p + 1))).hom := by
    unfold diagonalHorizontal originalHorizontal
    rw [← Category.assoc, horizontal, Category.assoc, Category.assoc]
    congr 1
    exact eqToHom_iso_hom_naturality (e (p + 1)) (diagonalIndex n p)
  let a (n : ℤ) : originalTotalTerm.{u,v,w,s,t,j} A B C I n ≅ totalTerm B S₀ I n :=
    (LinearEquiv.piCongrRight fun p => (e p (rowIndex n p)).toLinearEquiv).toModuleIso
  have step (n : ℤ) :
      (a n).hom ≫ totalStep B S₀ I n =
        originalTotalStep.{u,v,w,s,t,j} A B C I n ≫ (a (n + 1)).hom := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext p
    cases p with
    | zero =>
      exact ConcreteCategory.congr_hom (vertical 0 n (n + 1)) (x 0)
    | succ p =>
      change diagonalHorizontal B S₀ I n p ((e p (rowIndex n p)).hom (x p)) +
        (-1 : ℤ) ^ (p + 1) • (K₁ (p + 1)).d (rowIndex n (p + 1)) (rowIndex (n + 1) (p + 1))
          ((e (p + 1) (rowIndex n (p + 1))).hom (x (p + 1))) =
        (e (p + 1) (rowIndex (n + 1) (p + 1))).hom
          (originalHorizontal.{u,v,w,s,t,j} A B C I n p (x p) +
            (-1 : ℤ) ^ (p + 1) • (K₀ (p + 1)).d (rowIndex n (p + 1)) (rowIndex (n + 1) (p + 1))
              (x (p + 1)))
      rw [map_add, map_zsmul]
      exact congrArg₂ (· + ·) (ConcreteCategory.congr_hom (diagonal n p) (x p))
        (congrArg ((-1 : ℤ) ^ (p + 1) • ·)
          (ConcreteCategory.congr_hom
            (vertical (p + 1) (rowIndex n (p + 1)) (rowIndex (n + 1) (p + 1))) (x (p + 1))))
  have sqOriginal (n : ℤ) :
      originalTotalStep.{u,v,w,s,t,j} A B C I n ≫ originalTotalStep.{u,v,w,s,t,j} A B C I (n + 1) = 0 := by
    apply (cancel_mono (a (n + 1 + 1)).hom).mp
    rw [Category.assoc, ← step (n + 1), ← Category.assoc, ← step n,
      Category.assoc, sq n, Limits.comp_zero, Limits.zero_comp]
  let product : originalTotal.{u,v,w,s,t,j} A B C I sqOriginal ≅ localTotal B S₀ I sq :=
    HomologicalComplex.Hom.isoOfComponents a fun n m h => by
      obtain rfl : n + 1 = m := h
      simpa only [CochainComplex.of_d] using step n
  exact ⟨sqOriginal, product, fun n x p => rfl⟩

end OriginalProduct

set_option maxHeartbeats 1800000 in
theorem perfectCotangentDescent : PerfectCotangentDescent.{u,v,w,s,t,j} := by
  intro A B C _ _ _ _ _ _ P₀ L α H Hₚ
  let S₀ := coverRing.{u,v,w,j} A B C
  have hf := CotangentAmitsurModels.ringPowers A B C
  letI : Module.FaithfullyFlat B (BaseChange A B C) := hf.1
  letI : Module.FaithfullyFlat B S₀ :=
    Module.FaithfullyFlat.of_linearEquiv B (BaseChange A B C)
      (ULift.algEquiv (R := B)).toLinearEquiv
  let I := input.{v,s,t} B P₀
  let U := perfectLift.{u,v,w,s,t,j} A B C P₀
  let V := targetLift.{u,v,w,s,t,j} A B C
  have hU : Affine.CotangentAmitsurModels.FiniteProjective U :=
    liftedPerfect.{v,max u v w j,s,t} B (I.obj 0)
  have hK : U.IsKProjective :=
    Descent.PerfectMappingDescent.globalKProjective.{v,max u v w j,s,t} B (I.obj 0)
  obtain ⟨c, hc, hα⟩ := CotangentAmitsurModels.chainRepresentativeOfIso hK α
  obtain ⟨E⟩ := columnComparison.{u,v,w,s,t,j} A B C
  have localQuasi (p : ℕ) :
      QuasiIso ((extend.{v,max u v w,max u v w s t j} B (BP A B C p)).map c) := by
    letI := (hf.2.1 p).2
    exact CotangentAmitsurModels.quasiIso_extend c hc
  let F := I ⋙ Descent.PerfectMappingDescent.totalFunctor.{v,max u v w j,s,t} B S₀
  let G := I ⋙ Descent.PerfectMappingDescent.globalHomFunctor.{v,max u v w j,s,t} B
  let a := Functor.whiskerLeft I
    (Descent.PerfectMappingDescent.augmentation.{v,max u v w j,s,t} B S₀)
  have qa (X : compValue.{t} B) : QuasiIso (a.app X) :=
    Descent.PerfectMappingDescent.augmentation_quasiIso B S₀ (I.obj X)
  let g : G ⋙ qValue B ≅ derivedHomInTarget ((qValue B).obj L) V H :=
    fixedHomModelIso H α hK V
  let aq := Functor.whiskerRight a (qValue B)
  letI : IsIso aq := (NatTrans.isIso_iff_isIso_app aq).mpr (fun X => by
    letI := qa X
    change IsIso ((qValue B).map (a.app X))
    infer_instance)
  let d := g.symm ≪≫ asIso aq
  let J (p : ℕ) := homInTarget
    ((extend.{v,max u v w,max u v w s t j} B (BP A B C p)).obj U)
    (localTarget.{u,v,w,s,t,j} A B C p) (homFunctor (BP A B C p))
  refine ⟨⟨c, E, hU, fun X => Descent.PerfectMappingDescent.totalStep_sq B S₀ (I.obj X),
    (fun X => compareOriginalProduct.{u,v,w,s,t,j} A B C (I.obj X) E hU
      (Descent.PerfectMappingDescent.totalStep_sq B S₀ (I.obj X))),
    F, G, fun _ => rfl, fun _ => rfl, a, g, d, J, hc, hα, qa, fun _ => rfl,
    ?_, localQuasi, ?_, ?_, fun _ _ => rfl, ?_⟩⟩
  · intro X Y f n
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change ((Descent.PerfectMappingDescent.totalFunctor.{v,max u v w j,s,t} B S₀).map
      (I.map f)).f n = totalComponent.{v,max u v w j,s,t} S₀ (I.map f) n
    exact Descent.PerfectMappingDescent.totalFunctor_map.{v,max u v w j,s,t} B S₀ (I.obj X) (I.map f) n
  · intro p q f
    exact scalarExtension_natural.{max u v w,v,max u v w s t j}
      (columnMap (A := A) (C := C) f) c
  · intro p
    letI := localQuasi p
    exact fixedHomModelIso (Hₚ p)
      (asIso ((qValue (BP A B C p)).map
        ((extend.{v,max u v w,max u v w s t j} B (BP A B C p)).map c)))
      (extensionKProjective.{v,max u v w,max u v w s t j} U hU)
      (localTarget.{u,v,w,s,t,j} A B C p)
  · intro X n z
    have ha := Descent.PerfectMappingDescent.augmentation_coordinates B S₀ (I.obj X) n z
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    refine ⟨ha.1.trans ?_, ha.2⟩
    exact (comparison_unit_apply (S := powerRing.{u,v,w,j} A B C 0) U (V.obj X) n z).trans
      (E.unit 0 U (V.obj X) hU n z).symm

private theorem originalUnit {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C] [Module.FaithfullyFlat A C]
    {P₀ : (perfect.{v,s} B).FullSubcategory}
    {L : compValue.{max u v w s t j} B}
    {α : (qValue B).obj (perfectLift.{u,v,w,s,t,j} A B C P₀) ≅ (qValue B).obj L}
    {H : Models.{v,max u v w s t j} B}
    {Hₚ : ∀ p, Models.{max u v w,max u v w s t j} (BP A B C p)}
    (Z : DescentData.{u,v,w,s,t,j} A B C P₀ L α H Hₚ) :
    Z.OriginalAugmentationFormula := by
  intro X n z
  let A₀ := eqToHom (Z.global_obj X).symm
  let f := A₀ ≫ Z.originalAugmentation.app X
  let g := A₀ ≫ Z.augmentation.app X ≫ eqToHom (Z.total_obj X)
  let e := (Z.product X).iso
  have hf : f ≫ e.hom = g := by
    change (A₀ ≫ Z.augmentation.app X ≫ eqToHom (Z.total_obj X) ≫ e.inv) ≫ e.hom = _
    simp [g]
  have h (p : ℕ) : e.hom.f n (f.f n z) p = (g.f n z) p :=
    congrFun (ConcreteCategory.congr_hom (HomologicalComplex.congr_hom hf n) z) p
  have hi (p : ℕ) := (Z.product X).coordinates n (f.f n z) p
  let a (p : ℕ) :=
    (HomologicalComplex.eval _ _ (rowIndex n p)).mapIso
      (Z.columns.iso p (perfectLift.{u,v,w,s,t,j} A B C P₀)
        ((targetLift.{u,v,w,s,t,j} A B C).obj X) Z.perfect)
  have inj (p : ℕ) : Function.Injective (a p).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hz := Z.augmentation_coordinates X n z
  constructor
  · apply inj 0
    exact (hi 0).symm.trans ((h 0).trans hz.1)
  · intro p
    apply inj (p + 1)
    exact (hi (p + 1)).symm.trans ((h (p + 1)).trans ((hz.2 p).trans (map_zero _).symm))

end Descent
section SquareZero

open Specs.DerivedFormalization.Affine.CotangentAmitsurModels
  (RingBridge transported ordinaryRestriction)
open Specs.DerivedFormalization.Affine.CotangentComplex (Model)
open Specs.DerivedFormalization.Affine.SquareZeroMaps (IsNonpositive)
open Specs.DerivedFormalization.Affine.Tensor (ModuleTensor regular)
open RightDGModuleModel (eval)
open Specs.DerivedFormalization.DG.HomComplex (homComplex)

universe k₀ r z

open private pre_id pre_comp from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.DerivedHom

private def preIso {k : Type k₀} [Field k] [CharZero k] {A : CommDGAlgebra.{k₀,z} k}
    {L M : A.Module} (e : L ≅ M) (X : A.Module) :
    Specs.DerivedFormalization.Affine.DerivedHom.internalHom M X ≅
      Specs.DerivedFormalization.Affine.DerivedHom.internalHom L X where
  hom := DerivedHom.pre X e.hom
  inv := DerivedHom.pre X e.inv
  hom_inv_id := by rw [← pre_comp, e.inv_hom_id, pre_id]
  inv_hom_id := by rw [← pre_comp, e.hom_inv_id, pre_id]

private theorem ordinaryPre_quasiIso {R : Type r} [CommRing R]
    {P L : compValue.{max r z} R} (c : P ⟶ L) (hc : QuasiIso c)
    (hP : P.IsKProjective) (hL : L.IsKProjective) (X : compValue.{max r z} R) :
    QuasiIso (internalHomMapValue c (𝟙 X)) := by
  letI := hP
  letI := hL
  obtain ⟨e, rfl⟩ := (CochainComplex.IsKProjective.quasiIso_iff c).mp hc
  change QuasiIso (internalHomMap e.hom (𝟙 X))
  apply homotopyEquivalences_le_quasiIso _ _ _
  refine ⟨{
    hom := internalHomMap e.hom (𝟙 X)
    inv := internalHomMap e.inv (𝟙 X)
    homotopyHomInvId := ?_
    homotopyInvHomId := ?_ }, rfl⟩
  · rw [internalHomMap_comp, Category.id_comp, ← internalHomMap_id L X]
    exact internalHomMapHomotopy e.homotopyInvHomId (Homotopy.ofEq rfl)
  · rw [internalHomMap_comp, Category.id_comp, ← internalHomMap_id P X]
    exact internalHomMapHomotopy e.homotopyHomInvId (Homotopy.ofEq rfl)

set_option maxHeartbeats 1200000 in
theorem squareZeroCohomology : SquareZeroCohomology.{k₀,r,z} := by
  intro k _ _ R _ _ E A b M T hT hB P L X e c hc hP hX
  let B := transported.{k₀,r,z} k R
  let Xdg := E.strict.functor.obj X
  have hXd : IsNonpositive Xdg := by
    intro i hi
    letI := hX i hi
    let e := (HomologicalComplex.eval _ _ i).mapIso (E.terms X)
    let e' : (Xdg.complex ()).X i → X.X i := fun x => e.inv x
    have h : Function.Injective e' := (ModuleCat.mono_iff_injective e.inv).1 inferInstance
    exact h.subsingleton
  obtain ⟨S, _⟩ := SquareZeroMaps.extensionConstruction (B := B)
  let W := PolynomialPath.modulePathModel Xdg
  obtain ⟨Y, D₀, _, q, hq⟩ := SquareZeroHomotopy.pathQuotient M T hT hXd (S Xdg) W (S W.obj)
  have hm := (CotangentModelProperties.cotangentModelProperties T b M.base M.augmentation
    M.differentials M.triangle M.semifree M.surjective M.quasiIso hT hB).1
  -- Transport K-projectivity along the strict isomorphism of cotangent models.
  let ev := eval (A := Specs.DerivedFormalization.Affine.Tensor.dgCat B.toCommDGAlgebra) ()
  have hL : L.IsKProjective := (E.projective L).mpr (by
    intro N hN
    let i := ev.mapIso (preIso e N)
    intro n
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact ((HomologicalComplex.exactAt_iff_isZero_homology _ n).mp (hm N hN n)).of_iso
      ((HomologicalComplex.homologyFunctor _ _ n).mapIso i).symm)
  let H (P : compValue.{max r z} R) :=
    (ordinaryRestriction.{k₀,r,z} k R).obj (internalHomValue P X)
  let u : (homComplex (M.module T) Xdg) ≅ H L :=
    ev.mapIso (preIso e Xdg) ≪≫
      (ev.mapIso (E.hom L X)).symm ≪≫ (E.terms (internalHomValue L X)).symm
  let f : H L ⟶ H P := (ordinaryRestriction.{k₀,r,z} k R).map (internalHomMapValue c (𝟙 X))
  have qf : QuasiIso f :=
    HomologicalComplex.quasiIso_map_of_preservesHomology _
      (ModuleCat.restrictScalars.{max r z} (algebraMap k R))
      (hφ := ordinaryPre_quasiIso c hc hP hL X)
  letI := qf
  let a (i : ℤ) := (HomologicalComplex.homologyFunctor _ _ i).mapIso u ≪≫
    isoOfQuasiIsoAt f i
  refine ⟨S Xdg, W, S W.obj, Y, D₀, a, q.trans (a 0).toLinearEquiv.toEquiv, ?_⟩
  intro g
  exact congrArg ((a 0).hom : _ → _) (hq g)

end SquareZero

section Affine

open Specs.DerivedFormalization.Affine.CotangentAmitsurModels (transported)
open Specs.DerivedFormalization.Affine.CotangentComplex (oneObject)
universe k₀ r z


open Specs.DerivedFormalization.Affine.CotangentAmitsurModels
  (changeRepresentative RingBridge transported ordinaryRestriction FiniteProjective)
open Specs.DerivedFormalization.Affine.CotangentComplex (Model)
open Specs.DerivedFormalization.Affine.Tensor (ModuleTensor regular)
open private homIso from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.AmitsurRingTransport

private def restrictChangeIso {k : Type k₀} [Field k]
    {R : Type v} {S : Type w} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (e : R ≃ₐ[k] S) (Y : compValue.{max v w z} R) :
    (ordinaryRestriction.{k₀,v,max w z} k R).obj Y ≅
      (ordinaryRestriction.{k₀,w,max v z} k S).obj
        ((changeRepresentative.{v,w,max v w z} e.toRingEquiv).obj Y) := by
  -- Use an identity on the underlying module, with the scalar tower
  -- identified by the fact that the ring equivalence is over k.
  let h : algebraMap k R = e.symm.toRingHom.comp (algebraMap k S) :=
    RingHom.ext (fun x => (e.symm.commutes x).symm)
  let i := ModuleCat.restrictScalarsComp'.{max v w z} (algebraMap k S)
      e.symm.toRingHom (algebraMap k R) h
  exact HomologicalComplex.Hom.isoOfComponents
    (fun n => i.app (Y.X n)) (fun n m _ => (i.hom.naturality (Y.d n m)).symm)

private theorem changeKProjective {R : Type v} {S : Type w} [CommRing R] [CommRing S]
    (e : R ≃+* S) (P : compValue.{max v w z} R) (hP : FiniteProjective P) :
    CochainComplex.IsKProjective ((changeRepresentative e).obj P) := by
  obtain ⟨⟨_, U, hU⟩, _, hproj⟩ := hP
  let E : ModuleCat.{max v w z} R ≌ ModuleCat.{max v w z} S :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.symm
  let Q := (changeRepresentative e).obj P
  letI : Q.IsStrictlyLE U := (CochainComplex.isStrictlyLE_iff Q U).mpr
    (fun i hi => ModuleCat.isZero_iff_subsingleton.mpr (hU i (Or.inr hi)))
  letI : ∀ i, Projective (Q.X i) := fun i => (E.map_projective_iff (P.X i)).mpr
    ((IsProjective.iff_projective (P.X i)).mp (hproj i))
  exact CochainComplex.isKProjective_of_projective Q U

private theorem extensionPerfect {R : Type v} {S : Type w} [CommRing R] [CommRing S]
    [Algebra R S] {P : compValue.{max w z} R} (hP : FiniteProjective P) :
    FiniteProjective ((extend.{v,w,max w z} R S).obj P) := by
  obtain ⟨⟨L, U, hU⟩, hf, hp⟩ := hP
  refine ⟨⟨L,U,?_⟩, ?_, ?_⟩
  · intro i hi
    letI := hU i hi
    change Subsingleton (S ⊗[R] P.X i)
    infer_instance
  · intro i
    letI := hf i
    change Module.Finite S (S ⊗[R] P.X i)
    infer_instance
  · intro i
    letI := hp i
    change Module.Projective S (S ⊗[R] P.X i)
    infer_instance

private theorem SquareZeroClasses.transport {k : Type k₀} [Field k] [CharZero k]
    {A B : NonpositiveCDGA.{k₀,z} k} {b : A ⟶ B} (M : Model b) (T : ModuleTensor.{k₀,z} k)
    {X : B.Module} {H K : ModuleCochain.{k₀,z} k} (f : H ⟶ K) (hf : QuasiIso f)
    (classes : SquareZeroClasses M T X H) : SquareZeroClasses M T X K := by
  letI := hf
  obtain ⟨S, W, U, Y, D₀, a, q, hq⟩ := classes
  let e (i : ℤ) := isoOfQuasiIsoAt f i
  refine ⟨S, W, U, Y, D₀, fun i => a i ≪≫ e i, q.trans (e 0).toLinearEquiv.toEquiv, ?_⟩
  intro g
  exact congrArg ((e 0).hom : _ → _) (hq g)

private theorem squareZeroOriginal {k : Type k₀} [Field k] [CharZero k]
    {R : Type v} {R' : Type w} [CommRing R] [CommRing R'] [Algebra k R] [Algebra k R']
    (e : R ≃ₐ[k] R') (E : RingBridge.{k₀,w,max v z} k R')
    {A : NonpositiveCDGA.{k₀,max v w z} k}
    {b : A ⟶ transported.{k₀,w,max v z} k R'} (M : Model b)
    (T : ModuleTensor.{k₀,max v w z} k)
    (hT : T.Formulas (M.augmentation : _ ⟶ (transported.{k₀,w,max v z} k R').toCommDGAlgebra) (regular _))
    (hB : ∀ N : (transported.{k₀,w,max v z} k R').Module, T.Formulas (𝟙 _) N)
    {P L X : compValue.{max v w z} R}
    (i : E.strict.functor.obj ((changeRepresentative e.toRingEquiv).obj L) ≅ M.module T)
    (c : P ⟶ L) (hc : QuasiIso c) (hP : FiniteProjective P)
    (hX : ∀ n : ℤ, 0 < n → Subsingleton (X.X n)) :
    SquareZeroClasses M T (E.strict.functor.obj ((changeRepresentative e.toRingEquiv).obj X))
      ((ordinaryRestriction.{k₀,v,max w z} k R).obj (internalHomValue P X)) := by
  let C := changeRepresentative.{v,w,max v w z} e.toRingEquiv
  let F := ModuleCat.restrictScalars.{max v w z} e.symm.toRingHom
  have hq : QuasiIso (C.map c) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology c F (hφ := hc)
  have hkc : CochainComplex.IsKProjective (C.obj P) :=
    changeKProjective.{v,w,max v z} e.toRingEquiv P hP
  have hs := squareZeroCohomology.{k₀,w,max v z} E M T hT hB (C.obj P) (C.obj L) (C.obj X) i (C.map c) hq hkc
    (fun n hn => hX n hn)
  let iH := restrictChangeIso.{v,w,k₀,max v w z} e (internalHomValue P X) ≪≫
      (ordinaryRestriction.{k₀,w,max v z} k R').mapIso (homIso e.toRingEquiv P X)
  exact SquareZeroClasses.transport M T iH.inv inferInstance hs

set_option maxHeartbeats 2400000 in
theorem cotangentDiagramDescent : CotangentDiagramDescent.{u,v,w,s,t,k₀,r} := by
  intro k _ _ A B C _ _ _ _ _ _ _ _ A' B' C' _ _ _ _ _ _ _ _ _ e eₚ O T M E F D forms h
  let Bdg := transported.{k₀,r,max k₀ u v w s t} k B'
  letI := Specs.DerivedFormalization.DG.Derived.homotopyCategory (oneObject Bdg) h
  letI := Specs.DerivedFormalization.DG.DerivedKProjective.derivedCategoryInstance (oneObject Bdg) h
  obtain ⟨L, a, K, I, b, τ, l, hb, hl, hlₚ, _⟩ :=
    CotangentAmitsurModels.originalCotangentComparison.{k₀,r,max u v w,max k₀ s t,v}
      e.toRingEquiv (fun p => (eₚ p).toRingEquiv)
      (fun f => columnMap (A := A) (B := B) (C := C) f) O T M E F D h
  choose lₚ he using hlₚ
  refine ⟨L, a, O.d.trans I, l, lₚ, he, ?_⟩
  intro P₀ α H Hₚ
  obtain ⟨Z⟩ := perfectCotangentDescent.{u,v,w,s,t,max k₀ r} A B C P₀ L α H Hₚ
  refine ⟨Z, originalUnit Z, ?_⟩
  intro X hX
  let U := perfectLift.{u,v,w,s,t,max k₀ r} A B C P₀
  let V := (targetLift.{u,v,w,s,t,max k₀ r} A B C).obj X
  have hV (n : ℤ) (hn : 0 < n) : Subsingleton (V.X n) := by
    letI := hX n (ne_of_gt hn)
    exact (CochainCoefficientLift.termEquiv.{max k₀ u v w r s} X n).symm.injective.subsingleton
  constructor
  · have hS := squareZeroOriginal.{v,r,k₀,max k₀ u v w s t} e E M T
      (forms M.augmentation (regular _)) (forms (𝟙 _))
      (E.strict.functor.mapIso a ≪≫ D.global) Z.c Z.representative Z.perfect hV
    let F := ModuleCat.restrictScalars.{max k₀ u v w r s t} (algebraMap k B)
    let f := eqToHom (Z.global_obj X).symm ≫ Z.augmentation.app X ≫ (Z.productIso X).inv
    have hf : QuasiIso f := quasiIso_comp _ _ (hφ' :=
      quasiIso_comp _ _ (hφ := Z.augmentation_quasiIso X))
    exact SquareZeroClasses.transport M T ((F.mapHomologicalComplex (.up ℤ)).map f)
      (HomologicalComplex.quasiIso_map_of_preservesHomology f F (hφ := hf)) hS
  · intro p
    let Gp := extend.{v,max u v w,max k₀ u v w r s t} B (BP A B C p)
    let Xₚ := Gp.obj V
    have hXp (n : ℤ) (hn : 0 < n) : Subsingleton (Xₚ.X n) := by
      letI := hV n hn
      change Subsingleton (BP A B C p ⊗[B] V.X n)
      infer_instance
    have hS := squareZeroOriginal.{max u v w,r,k₀,max k₀ u v w s t} (eₚ p) (F p)
      (D.column p).model T (forms _ (regular _)) (forms (𝟙 _)) (lₚ p) (Gp.map Z.c)
      (Z.localRepresentative p) (extensionPerfect.{v,max u v w,max k₀ u v w r s t} Z.perfect) hXp
    let f := (ordinaryRestriction.{k₀,max u v w,max k₀ u v w r s t} k (BP A B C p)).map
      (eqToHom (Z.local_obj p X).symm)
    exact SquareZeroClasses.transport (D.column p).model T f inferInstance hS

open Specs.DerivedFormalization.Affine.CotangentAmitsurModels
  (originalBaseMap liftedBaseMap)

set_option maxHeartbeats 1800000 in
theorem faithfullyFlatTangentDescent : FaithfullyFlatTangentDescent.{u,v,w,s,t,k₀} := by
  intro k _ _ A B C _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨A', B', C', eA, eB, eC, f, g, hf, hg, h⟩ :=
    CotangentAmitsurModels.ringDiagramTransport.{k₀,u,max k₀ s t,v,w} k A B C
  letI : Algebra A' B' := f.toRingHom.toAlgebra
  letI : Algebra A' C' := g.toRingHom.toAlgebra
  letI : IsScalarTower k A' B' := IsScalarTower.of_algHom f
  letI : IsScalarTower k A' C' := IsScalarTower.of_algHom g
  obtain ⟨ff, eCP, eBP, fe, te, be, co, ⟨O⟩⟩ := h
  letI : Module.FaithfullyFlat A' C' := ff
  obtain ⟨T₀, _, hT₀, ⟨P⟩⟩ :=
    CotangentComplex.cotangentExists (originalBaseMap (k := k) (A := A') (B := B'))
  obtain ⟨T, U, E, F, forms, hE, hF, _, _, hHom, D, _, hExt, _⟩ :=
    CotangentAmitsurModels.commonCotangentModels.{k₀,max k₀ u v w,0,max k₀ u v w s t,0}
      (C := C') T₀ hT₀ P.chosen
  refine ⟨A', B', C', eA, eB, eC, f, g, hf, hg, ff, eCP, eBP, fe, te, be,
    (fun d z => (co d 0 z).2), O, T, U.model, E, F, D, hE, hF, hHom, hExt, ?_⟩
  exact cotangentDiagramDescent.{u,v,w,s,t,k₀,max k₀ u v w} k A B C
    eB eBP O T U.model E F D forms

end Affine

end
end DerivedFormalization.Affine.TangentDescent
