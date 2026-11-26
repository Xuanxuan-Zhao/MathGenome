import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.FiniteFreeDualityModel
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DerivedCechComparison
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.GorensteinTopLocalCohomology
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.EndomorphismsOfResidueHull
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CochainLinearTensorHomAdjunction
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Batteries.Tactic.OpenPrivate

open CategoryTheory HomologicalComplex IsLocalRing
open MonoidalCategory (curriedTensor)
open CategoryTheory.Limits (IsZero)
open CochainComplex (linearHomComplex)
open CochainComplex.HomComplex (Cochain)
open scoped TensorProduct

noncomputable section

namespace CommutativeAlgebraNotes

open CochainTensorHom (Complex tensorHomIso homMap)
open Specs.CommutativeAlgebraNotes.FiniteFreeDualityModel
open Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules (Completion)
open Specs.CommutativeAlgebraNotes.GorensteinTopLocalCohomology (derivedTorsionOfRing)

universe u w

variable {R : Type u} [CommRing R]

open private tensor_d_apply tensorHom_apply map_sign sign_apply from
  MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CochainLinearTensorHomAdjunction

private theorem tensor_hom_ext {A B : Complex R} {n : ℤ} {M : ModuleCat.{u} R}
    {f g : (tensorObj A B).X n ⟶ M}
    (h : ∀ i j (e : i + j = n) (x : A.X i) (y : B.X j),
      f (ιTensorObj A B i j n e (x ⊗ₜ[R] y)) =
        g (ιTensorObj A B i j n e (x ⊗ₜ[R] y))) : f = g := by
  apply mapBifunctor.hom_ext
  intro i j e
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  exact h i j e

private def tensorSwapAt (A B : Complex R) (n : ℤ) :
    (tensorObj A B).X n ⟶ (tensorObj B A).X n :=
  mapBifunctorDesc (fun i j e => (i * j).negOnePow •
    (TensorProduct.comm R (A.X i) (B.X j)).toModuleIso.hom ≫
      ιTensorObj B A j i n (by
        change i + j = n at e
        omega))

private theorem tensorSwapAt_apply (A B : Complex R) (i j n : ℤ) (e : i + j = n)
    (x : A.X i) (y : B.X j) :
    tensorSwapAt A B n (ιTensorObj A B i j n e (x ⊗ₜ[R] y)) =
      (i * j).negOnePow • ιTensorObj B A j i n (by omega) (y ⊗ₜ[R] x) := by
  have h := ι_mapBifunctorDesc (K₁ := A) (K₂ := B) (F := curriedTensor (ModuleCat R))
    (c := ComplexShape.up ℤ) (fun i j e => (i * j).negOnePow •
      (TensorProduct.comm R (A.X i) (B.X j)).toModuleIso.hom ≫
        ιTensorObj B A j i n (by
          change i + j = n at e
          omega)) i j e
  change ιTensorObj A B i j n e ≫ tensorSwapAt A B n = _ at h
  have hswap : (TensorProduct.comm R (A.X i) (B.X j)).toModuleIso.hom (x ⊗ₜ[R] y) =
      y ⊗ₜ[R] x := TensorProduct.comm_tmul R (A.X i) (B.X j) x y
  simpa only [ModuleCat.comp_apply, sign_apply, map_sign, hswap] using
    ConcreteCategory.congr_hom h (x ⊗ₜ[R] y)

private def tensorSwapHom (A B : Complex R) : tensorObj A B ⟶ tensorObj B A where
  f := tensorSwapAt A B
  comm' n m h := by
    change n + 1 = m at h
    apply tensor_hom_ext
    intro i j e x y
    simp only [ModuleCat.comp_apply, tensorSwapAt_apply, map_sign, tensor_d_apply _ _ _ _ _ h,
      map_add, smul_add, smul_smul]
    have hs₁ : ((i + 1) * j).negOnePow = (i * j).negOnePow * j.negOnePow := by
      rw [add_mul, one_mul, Int.negOnePow_add]
    have hs₂ : i.negOnePow * (i * (j + 1)).negOnePow = (i * j).negOnePow := by
      rw [mul_add, mul_one, Int.negOnePow_add]
      rw [mul_comm (i * j).negOnePow, ← mul_assoc, ← Int.negOnePow_add, ← two_mul, Int.negOnePow_two_mul, one_mul]
    rw [hs₁, hs₂, add_comm]

private theorem tensorSwapHom_comp (A B : Complex R) :
    tensorSwapHom A B ≫ tensorSwapHom B A = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply tensor_hom_ext
  intro i j e x y
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.comp_apply,
    ModuleCat.id_apply, tensorSwapHom, tensorSwapAt_apply, map_sign, smul_smul]
  rw [mul_comm j i, ← Int.negOnePow_add, ← two_mul, Int.negOnePow_two_mul, one_smul]

private def tensorSwap (A B : Complex R) : tensorObj A B ≅ tensorObj B A where
  hom := tensorSwapHom A B
  inv := tensorSwapHom B A
  hom_inv_id := tensorSwapHom_comp A B
  inv_hom_id := tensorSwapHom_comp B A

private theorem tensorSwap_natural_left {A A' : Complex R} (f : A ⟶ A') (B : Complex R) :
    tensorHom f (𝟙 B) ≫ (tensorSwap A' B).hom =
      (tensorSwap A B).hom ≫ tensorHom (𝟙 B) f := by
  apply HomologicalComplex.hom_ext
  intro n
  apply tensor_hom_ext
  intro i j e x y
  subst n
  have hs (k : ℤ) (h : j + i = k) (z : B.X j) (w : A.X i) :
      (tensorHom (𝟙 B) f).f k (ιTensorObj B A j i k h (z ⊗ₜ[R] w)) =
        ιTensorObj B A' j i k h (z ⊗ₜ[R] f.f i w) := by
    subst k
    simpa only [HomologicalComplex.id_f, ModuleCat.id_apply] using
      tensorHom_apply (𝟙 B) f j i z w
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, tensorHom_apply,
    HomologicalComplex.id_f, ModuleCat.id_apply, tensorSwap, tensorSwapHom,
    tensorSwapAt_apply, map_sign, hs]

private theorem cech_represents_shifted_hull [IsLocalRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (hG : AdvCommAlg.Gorenstein.Specs.LocalGorensteinValue R) (d : ℕ)
    (hd : ringKrullDim R = (d : WithBot ℕ∞)) (E : ResidueFieldEnvelope R)
    (rs : List R) (hrs : Ideal.span {r | r ∈ rs} = maximalIdeal R) :
    Nonempty (DerivedCategory.Q.obj (CechComplex rs) ≅
      DerivedCategory.Q.obj (stalk (d : ℤ) (ModuleCat.of R E.carrier))) := by
  let M := ModuleCat.{u} R
  let A := ModuleCat.of R E.carrier
  let I := maximalIdeal R
  obtain ⟨T, ⟨compute⟩, ⟨compare⟩⟩ :=
    derivedCechComparison (I := I) rs hrs
  let K : CochainComplex.Plus M := ⟨stalk 0 (ModuleCat.of R R), ⟨0, inferInstance⟩⟩
  let e₀ : (DerivedCategory.Plus.singleFunctor M 0).obj (ModuleCat.of R R) ≅
      DerivedCategory.Plus.Q.obj K :=
    ((Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.Plus.ι (C := M))).preimageIso
      ((DerivedCategory.singleFunctorIsoCompQ M 0).app (ModuleCat.of R R)))
  let e₁ : derivedTorsionOfRing R ≅ DerivedCategory.Q.obj (CechComplex rs) :=
    DerivedCategory.Plus.ι.mapIso
      (((_root_.CommutativeAlgebraNotes.idealTorsionFunctor I).rightDerivedFunctorPlus.mapIso e₀) ≪≫
        compare.app (DerivedCategory.Plus.Q.obj K)) ≪≫
      compute.app K ≪≫ DerivedCategory.Q.mapIso (HomologicalComplex.rightUnitor (CechComplex rs))
  obtain ⟨e₂⟩ := gorenstein_top_localCohomology hG d hd E
  let e₃ := ((DerivedCategory.singleFunctors M).shiftIso
    (-(d : ℤ)) (d : ℤ) 0 (neg_add_cancel _)).app A
  exact ⟨e₁.symm ≪≫ e₂ ≪≫ e₃ ≪≫
    (DerivedCategory.singleFunctorIsoCompQ M (d : ℤ)).app A⟩

/-- The finite-free resolution gives the augmentation quasi-isomorphism and a
roof of quasi-isomorphisms to the tensor with the shifted residue-field hull. -/
theorem finiteFreeDualityTensorComparisons : TensorComparisons.{u} := by
  intro R _ _ _ hG d hd E rs hrs X _ P π hπ hfree _ hbounded
  let C := CechComplex rs
  let : HasDerivedCategory.{u+1} (ModuleCat.{u} R) := HasDerivedCategory.standard _
  change QuasiIso (tensorHom π (𝟙 C)) ∧ _
  constructor
  · have hC : ∃ N : ℤ, C.IsStrictlyLE N := by
      refine ⟨rs.length, (CochainComplex.isStrictlyLE_iff _ _).mpr ?_⟩
      intro i hi
      exact Cech.isZero_X rs i (Or.inr hi)
    have : QuasiIso (tensorHom (𝟙 C) π) :=
      boundedAboveFlatTensorQuasiIso R C (Cech.flat rs) hC π hπ
    have h := tensorSwap_natural_left π C
    have : QuasiIso (tensorHom π (𝟙 C) ≫ (tensorSwap (stalk 0 X) C).hom) := by
      rw [h]
      infer_instance
    exact (quasiIso_iff_comp_right _ _).mp this
  · obtain ⟨e⟩ := cech_represents_shifted_hull hG d hd E rs hrs
    obtain ⟨W, s, hs, t, ht⟩ := DerivedCategory.right_fac e.hom
    have ht' : IsIso (DerivedCategory.Q.map t) := by
      rw [← IsIso.hom_inv_id_assoc (DerivedCategory.Q.map s) (DerivedCategory.Q.map t), ← ht]
      infer_instance
    have hflat (i : ℤ) : Module.Flat R (P.X i) := by
      let := hfree i
      infer_instance
    exact ⟨W, s, t,
      boundedAboveFlatTensorQuasiIso R P hflat hbounded s
        ((DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} R) s).mp hs),
      boundedAboveFlatTensorQuasiIso R P hflat hbounded t
        ((DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} R) t).mp ht')⟩

private theorem stalk_cochain_component_eq_zero {a b n : ℤ} {A B : ModuleCat.{u} R}
    (f : Cochain (stalk a A) (stalk b B) n) (i j : ℤ) (h : i + n = j)
    (hne : i ≠ a ∨ j ≠ b) : f.v i j h = 0 := by
  rcases hne with hi | hj
  · exact (isZero_single_obj_X (.up ℤ) a A i hi).eq_of_src _ _
  · exact (isZero_single_obj_X (.up ℤ) b B j hj).eq_of_tgt _ _

private def stalkCochainEquiv {a b n : ℤ} (h : a + n = b) (A B : ModuleCat.{u} R) :
    Cochain (stalk a A) (stalk b B) n ≃ₗ[R] ((stalk a A).X a ⟶ (stalk b B).X b) where
  toFun f := f.v a b h
  invFun f := Cochain.single f n
  left_inv f := by
    apply Cochain.ext
    intro i j hij
    by_cases hi : i = a
    · subst i
      obtain rfl : j = b := hij.symm.trans h
      exact Cochain.single_v _ _ _
    · rw [Cochain.single_v_eq_zero _ _ _ _ _ hi,
        stalk_cochain_component_eq_zero f i j hij (Or.inl hi)]
  right_inv f := Cochain.single_v f n h
  map_add' f g := Cochain.add_v f g a b h
  map_smul' r f := Cochain.smul_v r f a b h

private theorem stalk_hom_isZero {a b n : ℤ} (h : a + n ≠ b) (A B : ModuleCat.{u} R) :
    IsZero ((linearHomComplex R (stalk a A) (stalk b B)).X n) := by
  change IsZero (ModuleCat.of R (Cochain (stalk a A) (stalk b B) n))
  let : Subsingleton (Cochain (stalk a A) (stalk b B) n) := by
    refine ⟨fun f g => ?_⟩
    apply Cochain.ext
    intro i j hij
    have hn : i ≠ a ∨ j ≠ b := by omega
    rw [stalk_cochain_component_eq_zero f i j hij hn,
      stalk_cochain_component_eq_zero g i j hij hn]
  exact ModuleCat.isZero_of_subsingleton _

private theorem stalk_hom_d (a b n m : ℤ) (A B : ModuleCat.{u} R) :
    (linearHomComplex R (stalk a A) (stalk b B)).d n m = 0 := by
  by_cases h : a + n = b
  · by_cases hn : n + 1 = m
    · exact (stalk_hom_isZero (n := m) (by omega) A B).eq_of_tgt _ _
    · exact HomologicalComplex.shape _ _ _ hn
  · exact (stalk_hom_isZero h A B).eq_of_src _ _

private def stalkEndIsoAt [IsLocalRing R] [IsNoetherianRing R]
    (d : ℕ) (E : ResidueFieldEnvelope R) :
    ((linearHomComplex R (stalk (d : ℤ) (ModuleCat.of R E.carrier))
      (stalk 0 (ModuleCat.of R E.carrier))).X (-(d : ℤ))) ≅
      ModuleCat.of R (Completion R) :=
  let A := ModuleCat.of R E.carrier
  let eQ := (singleObjXSelf (.up ℤ) (d : ℤ) A).toLinearEquiv
  let eJ := (singleObjXSelf (.up ℤ) 0 A).toLinearEquiv
  ((stalkCochainEquiv (add_neg_cancel (d : ℤ)) A A).trans
    ((ModuleCat.homLinearEquiv (S := R)).trans
      ((eQ.arrowCongr eJ).trans (residueHullEndomorphismEquiv E).symm.toLinearEquiv))).toModuleIso

private def stalkEndIso [IsLocalRing R] [IsNoetherianRing R]
    (d : ℕ) (E : ResidueFieldEnvelope R) :
    linearHomComplex R (stalk (d : ℤ) (ModuleCat.of R E.carrier))
      (stalk 0 (ModuleCat.of R E.carrier)) ≅
      stalk (-(d : ℤ)) (ModuleCat.of R (Completion R)) := by
  let A := ModuleCat.of R E.carrier
  let B := ModuleCat.of R (Completion R)
  refine HomologicalComplex.Hom.isoOfComponents (fun n => ?_) (fun n m _ => ?_)
  · by_cases hn : n = -(d : ℤ)
    · subst n
      exact stalkEndIsoAt d E ≪≫ (singleObjXSelf (.up ℤ) (-(d : ℤ)) B).symm
    · exact (stalk_hom_isZero (n := n) (by omega) A A).iso
        (isZero_single_obj_X (.up ℤ) (-(d : ℤ)) B n hn)
  · rw [stalk_hom_d, show (stalk (-(d : ℤ)) B).d n m = 0 from single_obj_d _ _ _ _ _]
    simp

private theorem stalkEndIso_apply [IsLocalRing R] [IsNoetherianRing R]
    (d : ℕ) (E : ResidueFieldEnvelope R)
    (f : Cochain (stalk (d : ℤ) (ModuleCat.of R E.carrier))
      (stalk 0 (ModuleCat.of R E.carrier)) (-(d : ℤ)))
    (y : (stalk (d : ℤ) (ModuleCat.of R E.carrier)).X (d : ℤ)) :
    let A := ModuleCat.of R E.carrier
    let B := ModuleCat.of R (Completion R)
    residueHullEndomorphismEquiv E
      ((singleObjXSelf (.up ℤ) (-(d : ℤ)) B).hom ((stalkEndIso d E).hom.f _ f))
      ((singleObjXSelf (.up ℤ) (d : ℤ) A).hom y) =
    (singleObjXSelf (.up ℤ) 0 A).hom (f.v (d : ℤ) 0 (add_neg_cancel _) y) := by
  dsimp only
  have he : (stalkEndIso d E).hom.f (-(d : ℤ)) =
      (stalkEndIsoAt d E).hom ≫
        (singleObjXSelf (.up ℤ) (-(d : ℤ)) (ModuleCat.of R (Completion R))).inv := by
    simp only [stalkEndIso, Hom.isoOfComponents, ↓reduceDIte, Iso.trans_hom, Iso.symm_hom]
  rw [he, ← ModuleCat.comp_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change residueHullEndomorphismEquiv E
    ((residueHullEndomorphismEquiv E).symm _) _ = _
  rw [AlgEquiv.apply_symm_apply]
  let A := ModuleCat.of R E.carrier
  let eQ := (singleObjXSelf (.up ℤ) (d : ℤ) A).toLinearEquiv
  let eJ := (singleObjXSelf (.up ℤ) 0 A).toLinearEquiv
  let g := f.v (d : ℤ) 0 (add_neg_cancel _)
  change eQ.arrowCongr eJ g.hom (eQ y) = eJ (g y)
  simp only [LinearEquiv.arrowCongr_apply, LinearEquiv.symm_apply_apply]

private def homPostcomposeIso {P H L : Complex R} (e : H ≅ L) :
    linearHomComplex R P H ≅ linearHomComplex R P L where
  hom := homMap (𝟙 P) e.hom
  inv := homMap (𝟙 P) e.inv
  hom_inv_id := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    ext f : 1
    apply Cochain.ext
    intro i j hij
    apply ModuleCat.hom_ext
    ext x : 1
    simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, CochainTensorHom.homMap_apply,
      HomologicalComplex.id_f, ModuleCat.id_apply]
    exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom e.hom_inv_id j) _
  inv_hom_id := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    ext f : 1
    apply Cochain.ext
    intro i j hij
    apply ModuleCat.hom_ext
    ext x : 1
    simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, CochainTensorHom.homMap_apply,
      HomologicalComplex.id_f, ModuleCat.id_apply]
    exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom e.inv_hom_id j) _

/-- Currying the hull-valued dual of the tensor model gives the completed-ring
Hom complex via the canonical scalar action on the hull. -/
theorem finiteFreeDualityDualComparison : DualComparison.{u} := by
  intro R _ _ _ d E P A B Q J L
  refine ⟨residueHull_powerTorsion E, tensorHomIso P Q J ≪≫ homPostcomposeIso (stalkEndIso d E), ?_⟩
  intro n i hi f x y
  rw [Iso.trans_hom, HomologicalComplex.comp_f, ModuleCat.comp_apply]
  change Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules.scalar
      (residueHull_powerTorsion E) ((singleObjXSelf (.up ℤ) (-(d : ℤ)) B).hom
      (((homMap (𝟙 P) (stalkEndIso d E).hom).f n ((tensorHomIso P Q J).hom.f n f)).v
        i _ hi x)) _ = _
  rw [CochainTensorHom.homMap_apply, HomologicalComplex.id_f, ModuleCat.id_apply,
    ← residueHullEndomorphismEquiv_apply, stalkEndIso_apply,
    CochainTensorHom.tensorHomIso_apply]

end CommutativeAlgebraNotes
