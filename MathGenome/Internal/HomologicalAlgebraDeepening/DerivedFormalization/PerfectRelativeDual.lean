import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.PerfectRelativeDual
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedCoinduction
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedTensor
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.PerfectChainEvaluation
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.ModelQuasiIsoInvariance
import Mathlib.Algebra.Category.ModuleCat.Projective
import Batteries.Tactic.OpenPrivate

/-! Finite relative duality for a perfect algebra. -/

namespace DerivedFormalization.PerfectRelativeDual

universe u w v

noncomputable abbrev relativeDual : Specs.DerivedFormalization.PerfectRelativeDual.RelativeDualType.{u,w,v} :=
  @Specs.DerivedFormalization.PerfectRelativeDual.relativeDual.{u,w,v}

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Specs.DerivedFormalization.PerfectRelativeDual hiding relativeDual
open Specs.DerivedFormalization.Cochains (compValue derivedValue qValue qhValue quotientValue
  quotientCompQhIsoValue)
open Specs.DerivedFormalization.CochainModels (isKInjectiveValue isKProjectiveValue
  internalHomValue internalHomMapValue)
open Specs.DerivedFormalization.CochainTensor (tensor pure map isKFlat)
open Specs.DerivedFormalization.CochainTensorTransport (AdequateModel representedUnit)
open Specs.DerivedFormalization.CoinductionComplex (coinduceValue evaluationValue)
open Specs.DerivedFormalization.DerivedRestriction (restrictScalarsComplexValue
  derivedRestrictScalarsValue derivedRestrictScalarsFactorsValue)
open Specs.DerivedFormalization.ScalarExtensionTransport (ModelStability extension extendPure)
open CochainComplex.HomComplex
open scoped TensorProduct MonoidalCategory

attribute [local instance] HasDerivedCategory.standard

set_option linter.checkUnivs false
set_option linter.style.haveILetI false

noncomputable section

variable {A : Type u} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)

private theorem coinduction_transpose_apply {X : Comp.{max u w v} B}
    {Y : Comp.{max u w v} A} (g : (restrictScalarsComplexValue f).obj X ⟶ Y)
    (n : ℤ) (x : X.X n) (b : B) :
    ModuleCat.CoextendScalars.equiv f (Y.X n)
        (((coinductionAdjunction.{u,w,v} f).homEquiv X Y g).f n x) b =
      g.f n (b • x) := by
  rw [Adjunction.homEquiv_unit]
  rfl

private theorem pure_smul_left {R : Type u} [CommRing R] {X Y : Comp.{v} R}
    {i j n : ℤ} (h : i + j = n) (r : R) (x : X.X i) (y : Y.X j) :
    r • pure X Y h x y = pure X Y h (r • x) y := by
  let a := Specs.DerivedFormalization.CochainTensor.ι X Y i j n h
  change r • a.hom (x ⊗ₜ[R] y) = a.hom ((r • x) ⊗ₜ[R] y)
  rw [← map_smul, TensorProduct.smul_tmul']

theorem chainEvaluationFormula : ChainEvaluationFormula.{u,w,v} := by
  intro A B _ _ f B' _ d S I P i j n h z s b p
  unfold Specs.DerivedFormalization.PerfectRelativeDual.chainEvaluation
  rw [coinduction_transpose_apply, pure_smul_left]
  have hc := S.cancel_on_pure ((coinduceValue.{max u v} f).obj I) P h (b • z) s p
  have hm := congrArg (fun x => (map (evaluationValue.{max u v} f I) (𝟙 P)).f n x) hc
  refine hm.trans ?_
  rw [DerivedFormalization.CochainTensor.map_on_pure]
  change pure I P h ((evaluationValue.{max u v} f I).f i (s • b • z)) p = _
  rw [← mul_smul, DerivedFormalization.Coinduction.evaluation_apply,
    DerivedFormalization.Coinduction.coinduce_smul_apply, mul_one]

section Evaluation

variable {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
variable {e : R ≃+* R'} (M : AdequateModel e)

private abbrev H (X Y : Comp.{v} R) := internalHomValue X Y

private def assoc (X Y Z : Comp.{v} R) :
    tensor (tensor X Y) Z ≅ tensor X (tensor Y Z) :=
  letI := M.chainMonoidal
  let L := M.tensorModel (tensor X Y) Z ≪≫
    MonoidalCategory.tensorIso (M.tensorModel X Y) (Iso.refl Z)
  let U := M.tensorModel X (tensor Y Z) ≪≫
    MonoidalCategory.tensorIso (Iso.refl X) (M.tensorModel Y Z)
  L ≪≫ MonoidalCategory.associator X Y Z ≪≫ U.symm

private theorem assoc_apply (X Y Z : Comp.{v} R) (i j k : ℤ) {m l n : ℤ}
    (h : i + j = m) (hn : m + k = n) (h' : j + k = l) (hn' : i + l = n)
    (x : X.X i) (y : Y.X j) (z : Z.X k) :
    (assoc M X Y Z).hom.f n (pure (tensor X Y) Z hn (pure X Y h x y) z) =
      pure X (tensor Y Z) hn' x (pure Y Z h' y z) :=
  M.associator_on_pure X Y Z i j k h hn h' hn' x y z

private theorem assoc_inv_apply (X Y Z : Comp.{v} R) (i j k : ℤ) {m l n : ℤ}
    (h : i + j = m) (hn : m + k = n) (h' : j + k = l) (hn' : i + l = n)
    (x : X.X i) (y : Y.X j) (z : Z.X k) :
    (assoc M X Y Z).inv.f n (pure X (tensor Y Z) hn' x (pure Y Z h' y z)) =
      pure (tensor X Y) Z hn (pure X Y h x y) z := by
  rw [← assoc_apply M X Y Z i j k h hn h' hn' x y z]
  change ((assoc M X Y Z).hom ≫ (assoc M X Y Z).inv).f n _ = _
  rw [Iso.hom_inv_id]
  rfl

private def swap (X Y : Comp.{v} R) : tensor X Y ≅ tensor Y X :=
  letI := M.chainMonoidal
  letI := M.chainSymmetric
  M.tensorModel X Y ≪≫ β_ X Y ≪≫ (M.tensorModel Y X).symm

private theorem swap_apply (X Y : Comp.{v} R) {i j n : ℤ} (h : i + j = n)
    (x : X.X i) (y : Y.X j) :
    (swap M X Y).hom.f n (pure X Y h x y) =
      (i * j).negOnePow • pure Y X (by omega : j + i = n) y x :=
  M.braiding_on_pure X Y h x y

private theorem map_sign {R : Type u} [CommRing R] {X Y : ModuleCat.{v} R} (f : X ⟶ Y)
    (a : ℤˣ) (x : X) : f (a • x) = a • f x := by
  change f.hom (a • x) = a • f.hom x
  simp only [Units.smul_def, map_zsmul]

/-- The signed pairing obtained by moving the tensor factor past the Hom's argument. -/
private def evaluationPairing (Q I P : Comp.{v} R) :
    tensor (tensor (H Q I) P) Q ⟶ tensor I P :=
  (assoc M (H Q I) P Q).hom ≫ map (𝟙 _) (swap M P Q).hom ≫
    (assoc M (H Q I) Q P).inv ≫ map ((M.rawClosed Q).adj.counit.app I) (𝟙 P)

private def signedEvaluation (Q I P : Comp.{v} R) :
    tensor (H Q I) P ⟶ H Q (tensor I P) :=
  (M.rawClosed Q).adj.homEquiv _ _ (evaluationPairing M Q I P)

private theorem signedEvaluation_apply (Q I P : Comp.{v} R) {i j k n l : ℤ}
    (hn : i + j = n) (hl : k + n = l)
    (z : (H Q I).X i) (p : P.X j) (x : Q.X k) :
    (((signedEvaluation M Q I P).f n (pure (H Q I) P hn z p)).v k l hl) x =
      (j * k).negOnePow • pure I P (by omega : i + k + j = l)
        (z.v k (i + k) (add_comm k i) x) p := by
  subst n
  obtain rfl : l = i + j + k := by omega
  have h := (M.rawClosed Q).on_pure _ _ (evaluationPairing M Q I P) (i+j) k
    (pure (H Q I) P rfl z p) x
  change _ = (evaluationPairing M Q I P).f _ _ at h
  change (((signedEvaluation M Q I P).f (i+j) (pure (H Q I) P rfl z p)).v
    k (i+j+k) hl) x = _ at h
  rw [h]
  unfold evaluationPairing
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
  rw [assoc_apply M (H Q I) P Q i j k rfl rfl rfl (by omega) z p,
    DerivedFormalization.CochainTensor.map_on_pure]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
  rw [swap_apply]
  have hpure : ∀ (a : ℤˣ) (u : (tensor Q P).X (j + k)),
      pure (H Q I) (tensor Q P) (by omega : i + (j + k) = i + j + k) z (a • u) =
      a • pure (H Q I) (tensor Q P) (by omega : i + (j + k) = i + j + k) z u := by
    intro a u
    unfold Specs.DerivedFormalization.CochainTensor.pure
    rw [TensorProduct.tmul_smul, ← map_sign]
    rfl
  rw (config := {transparency := .default}) [hpure, map_sign, map_sign,
    assoc_inv_apply M (H Q I) Q P i k j rfl (by omega) (by omega) (by omega) z x p,
    DerivedFormalization.CochainTensor.map_on_pure, (M.rawClosed Q).counit_on_pure]
  rfl

private theorem signedEvaluation_apply_at (Q I P : Comp.{v} R) {i j k n l m : ℤ}
    (hn : i+j=n) (hl : k+n=l) (hm : i+k=m)
    (z : (H Q I).X i) (p : P.X j) (x : Q.X k) :
    ((signedEvaluation M Q I P).f n (pure (H Q I) P hn z p)).v k l hl x =
      (j * k).negOnePow • pure I P (by omega : m+j=l) (z.v k m (by omega) x) p := by
  subst m
  exact signedEvaluation_apply M Q I P hn hl z p x

private theorem homMap_apply {Q Q' I I' : Comp.{v} R} (b : Q' ⟶ Q) (c : I ⟶ I')
    {i k l : ℤ} (h : k + i = l) (z : (H Q I).X i) (x : Q'.X k) :
    (((internalHomMapValue b c).f i z).v k l h) x = c.f l (z.v k l h (b.f k x)) := by
  change (((Cochain.ofHom b).comp z (zero_add i)).comp (Cochain.ofHom c) (add_zero i)).v k l h x = _
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v]
  rfl

private theorem tensorMap_id (X Y : Comp.{v} R) :
    map (𝟙 X) (𝟙 Y) = 𝟙 (tensor X Y) := by
  apply DerivedFormalization.CochainTensor.hom_ext
  intro i j n h x y
  rw [DerivedFormalization.CochainTensor.map_on_pure]
  rfl

private theorem tensorMap_comp {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Comp.{v} R}
    (b : X₀ ⟶ X₁) (c : Y₀ ⟶ Y₁) (b' : X₁ ⟶ X₂) (c' : Y₁ ⟶ Y₂) :
    map b c ≫ map b' c' = map (b ≫ b') (c ≫ c') := by
  apply DerivedFormalization.CochainTensor.hom_ext
  intro i j n h x y
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
  rw (config := {transparency := .default}) [DerivedFormalization.CochainTensor.map_on_pure,
    DerivedFormalization.CochainTensor.map_on_pure, DerivedFormalization.CochainTensor.map_on_pure]
  rfl

private def tensorIsoRaw {X Y X' Y' : Comp.{v} R} (a : X ≅ X') (b : Y ≅ Y') :
    tensor X Y ≅ tensor X' Y' where
  hom := map a.hom b.hom
  inv := map a.inv b.inv
  hom_inv_id := by rw [tensorMap_comp, Iso.hom_inv_id, Iso.hom_inv_id, tensorMap_id]
  inv_hom_id := by rw [tensorMap_comp, Iso.inv_hom_id, Iso.inv_hom_id, tensorMap_id]

private theorem signedEvaluation_natural {Q Q' I I' P P' : Comp.{v} R}
    (b : Q' ⟶ Q) (c : I ⟶ I') (k : P ⟶ P') :
    map (internalHomMapValue b c) k ≫ signedEvaluation M Q' I' P' =
      signedEvaluation M Q I P ≫ internalHomMapValue b (map c k) := by
  apply DerivedFormalization.CochainTensor.hom_ext
  intro i j n hn z p
  apply Cochain.ext
  intro l m hm
  apply ModuleCat.hom_ext
  ext x : 1
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
  rw (config := {transparency := .default}) [DerivedFormalization.CochainTensor.map_on_pure]
  simp only [signedEvaluation_apply, homMap_apply, map_sign]
  rw (config := {transparency := .default}) [DerivedFormalization.CochainTensor.map_on_pure]

include M in
private theorem tensor_quasiIso_left (P : Comp.{v} R) (hP : isKFlat P)
    {X Y : Comp.{v} R} (g : X ⟶ Y) (hg : QuasiIso g) :
    QuasiIso (map g (𝟙 P)) := by
  have hswap : map g (𝟙 P) ≫ (swap M Y P).hom =
      (swap M X P).hom ≫ map (𝟙 P) g := by
    apply DerivedFormalization.CochainTensor.hom_ext
    intro i j n h x y
    simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
    rw (config := {transparency := .default}) [DerivedFormalization.CochainTensor.map_on_pure]
    simp only [HomologicalComplex.id_f, ModuleCat.id_apply, swap_apply, map_sign]
    rw (config := {transparency := .default}) [DerivedFormalization.CochainTensor.map_on_pure]
    rfl
  letI : QuasiIso (map (𝟙 P) g) :=
    DerivedFormalization.CochainTensorInvariance.tensorMapQuasiIso P hP g hg
  haveI : QuasiIso (map g (𝟙 P) ≫ (swap M Y P).hom) := by
    rw [hswap]
    infer_instance
  exact quasiIso_of_comp_right _ (swap M Y P).hom

private theorem boundedFiniteProjective_kProjective {Q : Comp.{v} R}
    (hQ : Specs.DerivedFormalization.PerfectComplex.isBoundedFiniteProjectiveValue Q) :
    Q.IsKProjective := by
  obtain ⟨h, a, b, _, hb⟩ := hQ
  letI (i : ℤ) : Module.Projective R (Q.X i) := (h i).2
  letI : Q.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff Q b).2
    (fun i hi => hb i (Or.inr hi))
  exact CochainComplex.isKProjective_of_projective Q b

private theorem perfect_has_projective_model {X : Comp.{v} R}
    (hX : Specs.DerivedFormalization.PerfectComplex.isPerfectValue ((qValue R).obj X)) :
    ∃ (Q : Comp.{v} R) (g : Q ⟶ X),
      Specs.DerivedFormalization.PerfectComplex.isBoundedFiniteProjectiveValue Q ∧ QuasiIso g := by
  obtain ⟨Q, hQ, ⟨iso⟩⟩ := hX
  letI := boundedFiniteProjective_kProjective hQ
  obtain ⟨g, hg⟩ :=
    (DerivedFormalization.DerivedTensor.kProjectiveMapLifting (Iso.refl _) (Iso.refl _) iso.inv).1
  refine ⟨Q, g, hQ, (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{v} R) g).1 ?_⟩
  simp only [Iso.refl_hom, Category.comp_id, Category.id_comp] at hg
  rw [hg]
  infer_instance

private def leftUnit (P : Comp.{v} R) : tensor (representedUnit e) P ≅ P :=
  letI := M.chainMonoidal
  M.tensorModel (representedUnit e) P ≪≫
    MonoidalCategory.tensorIso M.unitModel (Iso.refl P) ≪≫ λ_ P

open Specs.DerivedFormalization.CochainRingTransport (complexFunctorValue rankOneComparisonValue)
open Specs.DerivedFormalization.CochainTensorTransport (representedUnitZero)
open private rankOneComparison_zero from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainTensorTransport

private theorem finiteProjective_transport {Q : Comp.{v} R}
    (hQ : Specs.DerivedFormalization.PerfectComplex.isBoundedFiniteProjectiveValue Q) :
    Specs.DerivedFormalization.PerfectChainEvaluation.boundedFiniteProjectiveValue
      ((complexFunctorValue e).obj Q) := by
  obtain ⟨h, a, b, _, hab⟩ := hQ
  refine ⟨⟨a, b, fun i hi => (Specs.DerivedFormalization.CochainRingTransport.moduleEquivalenceValue e).functor.map_isZero (hab i hi)⟩, ?_, ?_⟩
  · intro i
    exact (DerivedFormalization.CochainRingTransport.moduleProperties e (Q.X i)).2.2.2 (h i).1
  · intro i
    letI : Module.Projective R (Q.X i) := (h i).2
    haveI : Projective (((complexFunctorValue e).obj Q).X i) :=
      (DerivedFormalization.CochainRingTransport.moduleProperties e (Q.X i)).1.2 inferInstance
    infer_instance

-- The transport comparison uses U10a with the opposite tensor ordering.
set_option maxHeartbeats 1400000 in
private theorem signedEvaluation_unit_isIso (Q P : Comp.{v} R)
    (hQ : Specs.DerivedFormalization.PerfectComplex.isBoundedFiniteProjectiveValue Q) :
    IsIso (signedEvaluation M Q (representedUnit e) P ≫
      internalHomMapValue (𝟙 Q) (leftUnit M P).hom) := by
  let F := complexFunctorValue e
  let W := representedUnit e
  let W' := ringStalk R'
  let uW : F.obj W ≅ W' := rankOneComparisonValue e
  let hW := M.homIso Q W
  let hP := M.homIso Q P
  let b := M.tensorIso P (H Q W)
  let s := swap M P (H Q W)
  let g := signedEvaluation M Q W P ≫ internalHomMapValue (𝟙 Q) (leftUnit M P).hom
  let k := hW.hom ≫ internalHomMapValue (𝟙 (F.obj Q)) uW.hom
  have hk : IsIso k := by
    haveI : IsIso (internalHomMapValue (𝟙 (F.obj Q)) uW.hom) :=
      (Specs.DerivedFormalization.CochainTensorTransport.homFrom (F.obj Q)).map_isIso _
    apply IsIso.comp_isIso
  have ht : IsIso (map (𝟙 (F.obj P)) k) := by
    letI := hk
    exact (tensorIsoRaw (Iso.refl (F.obj P)) (asIso k)).isIso_hom
  let q' := F.obj Q
  let p' := F.obj P
  let cmp : tensor p' (H q' W') ⟶ H q' p' := chainEvaluationComparison q' p'
  have hc : IsIso cmp := by
    change IsIso (chainEvaluationComparison q' p')
    rw [← chainEvaluationIso_hom q' (finiteProjective_transport hQ) p']
    infer_instance
  have hw :
      b.hom ≫ F.map s.hom ≫ F.map g ≫ hP.hom =
        map (𝟙 p') k ≫ cmp := by
    apply DerivedFormalization.CochainTensor.hom_ext
    intro j i n hn p z
    apply Cochain.ext
    intro l m hm
    apply ModuleCat.hom_ext
    ext x : 1
    simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
    have hmap := DerivedFormalization.CochainTensor.map_on_pure (𝟙 p') k j i n hn p z
    rw [hmap]
    have htb := M.tensor_on_pure P (H Q W) hn p z
    change Cochain.v (hP.hom.f n ((F.map g).f n ((F.map s.hom).f n
      (b.hom.f n (pure p' (F.obj (H Q W)) hn p z))))) l m hm x =
      Cochain.v ((chainEvaluationComparison q' p').f n
        (pure p' (H q' W') hn p (k.f i z))) l m hm x
    rw [htb]
    have hs := swap_apply M P (H Q W) hn p z
    change s.hom.f n (pure P (H Q W) hn p z) = _ at hs
    change Cochain.v (hP.hom.f n (g.f n (s.hom.f n (pure P (H Q W) hn p z)))) l m hm x = _
    rw [hs, map_sign (g.f n)]
    let z' : (H Q P).X n := g.f n (pure (H Q W) P (by omega : i+j=n) z p)
    change ((hP.hom.f n (show (F.obj (H Q P)).X n from (j * i).negOnePow • z')).v l m hm) x = _
    have hms := map_sign (hP.hom.f n) (j*i).negOnePow (show (F.obj (H Q P)).X n from z')
    rw (config := {transparency := .default}) [hms]
    have hsign (a : ℤˣ) (y : (H q' p').X n) :
        (a • y).v l m hm x = a • y.v l m hm x := by
      exact ConcreteCategory.congr_hom
        (Cochain.units_smul_v (R := ℤ) a (y : Cochain q' p' n) l m hm) x
    rw [hsign]
    have heval := M.hom_on_eval Q P hm z' (show Q.X l from x)
    rw [heval]
    let p₀ : P.X j := p
    let z₀ : (H Q W).X i := z
    let x₀ : Q.X l := x
    let hpji : i+j=n := by omega
    let y₀ : (H Q (tensor W P)).X n :=
      (signedEvaluation M Q W P).f n (pure (H Q W) P hpji z₀ p₀)
    change (j*i).negOnePow •
        ((internalHomMapValue (𝟙 Q) (leftUnit M P).hom).f n y₀).v l m hm x₀ = _
    rw [homMap_apply]
    change (j*i).negOnePow • (leftUnit M P).hom.f m (y₀.v l m hm x₀) = _
    by_cases hiz : l + i = 0
    · have hj : m = j := by omega
      clear heval hsign
      revert hm
      subst m
      intro hm
      have hz : i + l = 0 := by omega
      have he := signedEvaluation_apply_at M Q W P hpji hm hz z₀ p₀ x₀
      change y₀.v l j hm x₀ = _ at he
      rw [he, map_sign, show j * l = -(j * i) by rw [show l = -i by omega, mul_neg],
        Int.negOnePow_neg, smul_smul, Int.units_mul_self, one_smul]
      let y : W.X 0 := z₀.v l 0 hiz x₀
      let r : R' := (representedUnitZero e).hom y
      have hr : (representedUnitZero e).inv r = y := by
        exact ConcreteCategory.congr_hom (representedUnitZero e).hom_inv_id y
      have hleft := M.leftUnitor_on_pure P j r p₀
      rw [hr] at hleft
      have hleft' : (leftUnit M P).hom.f j (pure W P (zero_add j) y p₀) = e.symm r • p₀ := hleft
      rw [hleft']
      have hdiag := DerivedFormalization.chainEvaluationComparison_apply q' p' hn hiz p (k.f i z) x
      change _ = (chainDualTerm q' hiz (k.f i z) x) • p at hdiag
      refine Eq.trans ?_ hdiag.symm
      change r • p = (chainDualTerm q' hiz (k.f i z) x) • p
      congr 1
      change r = (Specs.DerivedFormalization.PerfectChainEvaluation.ringAtZero (R := R')).hom
        ((k.f i z).v l 0 hiz x)
      change r = (Specs.DerivedFormalization.PerfectChainEvaluation.ringAtZero (R := R')).hom
        (((internalHomMapValue (𝟙 q') uW.hom).f i (hW.hom.f i z)).v l 0 hiz x)
      rw [homMap_apply]
      change r = (Specs.DerivedFormalization.PerfectChainEvaluation.ringAtZero (R := R')).hom
        (uW.hom.f 0 ((hW.hom.f i z).v l 0 hiz x))
      rw (config := {transparency := .default}) [M.hom_on_eval Q W hiz z₀ x₀]
      change r = (Specs.DerivedFormalization.PerfectChainEvaluation.ringAtZero (R := R')).hom
        (uW.hom.f 0 y)
      have hrW : uW.hom.f 0 ((representedUnitZero e).inv r) =
          (Specs.DerivedFormalization.PerfectChainEvaluation.ringAtZero (R := R')).inv r :=
        rankOneComparison_zero e r
      rw [← hr, hrW]
      exact (ConcreteCategory.congr_hom
        (Specs.DerivedFormalization.PerfectChainEvaluation.ringAtZero (R := R')).inv_hom_id r).symm
    · have hdiag := DerivedFormalization.chainEvaluationComparison_apply_off q' p' hn hm hiz p (k.f i z) x
      refine Eq.trans ?_ hdiag.symm
      have he := signedEvaluation_apply M Q W P (by omega : i+j=n) hm z₀ p₀ x₀
      change y₀.v l m hm x₀ = _ at he
      rw [he]
      have hz : IsZero (W.X (i+l)) :=
        HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
      have := ModuleCat.subsingleton_of_isZero hz
      rw [Subsingleton.elim (z₀.v l (i+l) (add_comm l i) x₀) 0]
      simp only [Specs.DerivedFormalization.CochainTensor.pure, TensorProduct.zero_tmul,
        map_zero, smul_zero]
      rfl
  have : IsIso (b.hom ≫ F.map s.hom ≫ F.map g ≫ hP.hom) := by
    rw [hw]
    infer_instance
  haveI : IsIso ((b.hom ≫ F.map s.hom) ≫ (F.map g ≫ hP.hom)) := by
    simpa only [Category.assoc] using (inferInstance : IsIso (b.hom ≫ F.map s.hom ≫ F.map g ≫ hP.hom))
  have : IsIso (F.map g ≫ hP.hom) := IsIso.of_isIso_comp_left (b.hom ≫ F.map s.hom) _
  have : IsIso (F.map g) := IsIso.of_isIso_comp_right _ hP.hom
  exact isIso_of_reflects_iso g F

private theorem signedEvaluation_quasiIso (Q I P J : Comp.{v} R)
    (hQ : Specs.DerivedFormalization.PerfectComplex.isBoundedFiniteProjectiveValue Q)
    (a : representedUnit e ⟶ I) (ha : QuasiIso a) (hP : isKFlat P)
    (j : tensor I P ⟶ J) (hj : QuasiIso j) :
    QuasiIso (signedEvaluation M Q I P ≫ internalHomMapValue (𝟙 Q) j) := by
  let W := representedUnit e
  have hproj := boundedFiniteProjective_kProjective hQ
  have inv {X Y : Comp.{v} R} (g : X ⟶ Y) (hg : QuasiIso g) :
      QuasiIso (internalHomMapValue (𝟙 Q) g) :=
    DerivedFormalization.internalHomMap_quasiIso_of_isKProjective Q hproj g hg
  haveI : IsIso (internalHomMapValue (𝟙 Q) (leftUnit M P).hom) :=
    (Specs.DerivedFormalization.CochainTensorTransport.homFrom Q).map_isIso _
  haveI := signedEvaluation_unit_isIso M Q P hQ
  haveI : QuasiIso (signedEvaluation M Q W P) :=
    quasiIso_of_comp_right _ (internalHomMapValue (𝟙 Q) (leftUnit M P).hom)
  haveI : QuasiIso (internalHomMapValue (𝟙 Q) (map a (𝟙 P))) :=
    inv _ (tensor_quasiIso_left M P hP a ha)
  haveI : QuasiIso (map (internalHomMapValue (𝟙 Q) a) (𝟙 P)) :=
    tensor_quasiIso_left M P hP _ (inv a ha)
  haveI : QuasiIso (map (internalHomMapValue (𝟙 Q) a) (𝟙 P) ≫ signedEvaluation M Q I P) := by
    rw [signedEvaluation_natural M (𝟙 Q) a (𝟙 P)]
    infer_instance
  haveI : QuasiIso (signedEvaluation M Q I P) := quasiIso_of_comp_left
    (map (internalHomMapValue (𝟙 Q) a) (𝟙 P)) _
  haveI := inv j hj
  infer_instance

end Evaluation

section RestrictedEvaluation

variable {A' B' : Type (max u w v)} [CommRing A'] [CommRing B']
variable {e : A ≃+* A'} {d : B ≃+* B'} (M : AdequateModel e) (S : ModelStability d f)

private abbrev stalkIso (I : Comp.{max u w v} A) :
    H (algebraStalk.{u,w,v} f) I ≅
      (restrictScalarsComplexValue f).obj ((coinduceValue.{max u v} f).obj I) :=
  DerivedFormalization.Coinduction.stalkIso.{max u v} f I

open Specs.DerivedFormalization.CoinductionComplex (restrictedRegular)

private abbrev stalkElement (b : B) : (algebraStalk.{u,w,v} f).X 0 :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (restrictedRegular.{max u v} f)).inv (ULift.up b)

private theorem stalkIso_on_element (I : Comp.{max u w v} A) (n : ℤ)
    (z : (H (algebraStalk.{u,w,v} f) I).X n) (b : B) :
    ModuleCat.CoextendScalars.equiv f (I.X n) ((stalkIso.{u,w,v} f I).hom.f n z) b =
      z.v 0 n (zero_add n) (stalkElement.{u,w,v} f b) := rfl

private theorem cancel_inv_on_one (E : Comp.{max u w v} B) (P : Comp.{max u w v} A)
    {i j n : ℤ} (h : i + j = n) (x : E.X i) (p : P.X j) :
    (S.cancel E P).inv.f n (pure ((restrictScalarsComplexValue f).obj E) P h x p) =
      pure E ((extension d f).obj P) h x (extendPure d f P j 1 p) := by
  have hh := S.cancel_on_pure E P h x 1 p
  simp only [one_smul] at hh
  have hi := ConcreteCategory.congr_hom
    (congrArg (fun k => k.f n) (S.cancel E P).hom_inv_id)
    (show ((restrictScalarsComplexValue f).obj (tensor E ((extension d f).obj P))).X n from
      pure E ((extension d f).obj P) h x (extendPure d f P j 1 p))
  change (S.cancel E P).inv.f n ((S.cancel E P).hom.f n _) = _ at hi
  exact (congrArg (fun y => (S.cancel E P).inv.f n y) hh).symm.trans hi

private theorem coinducedTerm_ext (J : Comp.{max u w v} A) (n : ℤ)
    {x y : ((coinduceValue.{max u v} f).obj J).X n}
    (h : ∀ b : B, ModuleCat.CoextendScalars.equiv f (J.X n) x b =
      ModuleCat.CoextendScalars.equiv f (J.X n) y b) : x = y :=
  ModuleCat.CoextendScalars.ext (LinearMap.ext h)

private theorem signedEvaluation_degree_zero {R : Type u} {R' : Type v}
    [CommRing R] [CommRing R'] {e : R ≃+* R'} (M : AdequateModel e)
    (Q I P : Comp.{v} R) {i l n : ℤ} (h : i+l=n)
    (z : (H Q I).X i) (p : P.X l) (x : Q.X 0) :
    ((signedEvaluation M Q I P).f n (pure (H Q I) P h z p)).v 0 n (zero_add n) x =
      pure I P h (z.v 0 i (zero_add i) x) p := by
  simpa only [mul_zero, Int.negOnePow_zero, one_smul] using
    signedEvaluation_apply_at M Q I P h (zero_add n) (add_zero i) z p x

set_option maxHeartbeats 600000 in
private theorem restricted_chainEvaluation (I P J : Comp.{max u w v} A) (j : tensor I P ⟶ J) :
    map (stalkIso.{u,w,v} f I).hom (𝟙 P) ≫
      (S.cancel ((coinduceValue.{max u v} f).obj I) P).inv ≫
      (restrictScalarsComplexValue f).map (chainComparison.{u,w,v} f d S I P J j) ≫
      (stalkIso.{u,w,v} f J).inv =
    signedEvaluation M (algebraStalk.{u,w,v} f) I P ≫
      internalHomMapValue (𝟙 (algebraStalk.{u,w,v} f)) j := by
  let T := algebraStalk.{u,w,v} f
  let C := coinduceValue.{max u v} f
  let U := restrictScalarsComplexValue.{max u w v} f
  let E := extension d f
  let s := stalkIso.{u,w,v} f I
  let t := stalkIso.{u,w,v} f J
  let c := S.cancel (C.obj I) P
  let ev := Specs.DerivedFormalization.PerfectRelativeDual.chainEvaluation.{u,w,v} f d S I P
  let k := U.map (chainComparison.{u,w,v} f d S I P J j)
  let g := signedEvaluation M T I P
  let p := internalHomMapValue (𝟙 T) j
  change map s.hom (𝟙 P) ≫ c.inv ≫ k ≫ t.inv = g ≫ p
  apply (cancel_mono t.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply DerivedFormalization.CochainTensor.hom_ext
  intro i l n h z y
  let x := s.hom.f i z
  let z₀ := pure (H T I) P h z y
  change k.f n (c.inv.f n ((map s.hom (𝟙 P)).f n z₀)) = t.hom.f n (p.f n (g.f n z₀))
  have hm : (map s.hom (𝟙 P)).f n z₀ = pure (U.obj (C.obj I)) P h x y :=
    DerivedFormalization.CochainTensor.map_on_pure s.hom (𝟙 P) i l n h z y
  rw [hm]
  have hc := cancel_inv_on_one.{u,w,v} f S (C.obj I) P h x y
  rw [hc]
  apply coinducedTerm_ext.{u,w,v} f J n
  intro b
  have hform := chainEvaluationFormula.{u,w,v} f d S I P h x 1 b y
  simp only [one_mul] at hform
  change j.f n (ModuleCat.CoextendScalars.equiv f ((tensor I P).X n)
      (ev.f n (pure (C.obj I) (E.obj P) h x (extendPure d f P l 1 y))) b) =
    ModuleCat.CoextendScalars.equiv f (J.X n) (t.hom.f n (p.f n (g.f n z₀))) b
  rw [hform]
  have hs := stalkIso_on_element.{u,w,v} f I i z b
  have ht := stalkIso_on_element.{u,w,v} f J n (p.f n (g.f n z₀)) b
  change ModuleCat.CoextendScalars.equiv f (I.X i) x b = _ at hs
  change ModuleCat.CoextendScalars.equiv f (J.X n) (t.hom.f n (p.f n (g.f n z₀))) b = _ at ht
  rw [hs, ht]
  dsimp only [p, g, z₀]
  rw [homMap_apply]
  change _ = j.f n (((signedEvaluation M T I P).f n (pure (H T I) P h z y)).v 0 n
    (zero_add n) (stalkElement.{u,w,v} f b))
  rw [signedEvaluation_degree_zero]

theorem chainComparisonQuasiIso : ChainComparisonQuasiIso.{u,w,v} := by
  intro A B _ _ f A' B' _ _ e d S hp I P J a j ha hI hP hj hJ
  let T := algebraStalk.{u,w,v} f
  obtain ⟨M⟩ := DerivedFormalization.CochainTensorTransport.adequateModel e
  obtain ⟨Q, g, hQ, hg⟩ := perfect_has_projective_model hp
  let p := internalHomMapValue g (𝟙 I)
  let q := internalHomMapValue g (𝟙 J)
  have hp' : QuasiIso p := DerivedFormalization.internalHomMap_quasiIso_of_isKInjective I hI g hg
  have hq : QuasiIso q := DerivedFormalization.internalHomMap_quasiIso_of_isKInjective J hJ g hg
  let l := signedEvaluation M T I P ≫ internalHomMapValue (𝟙 T) j
  let r := signedEvaluation M Q I P ≫ internalHomMapValue (𝟙 Q) j
  have hr : QuasiIso r := signedEvaluation_quasiIso M Q I P J hQ a ha hP j hj
  have hh : map p (𝟙 P) ≫ r = l ≫ q := by
    dsimp only [r, l, p, q]
    rw [← Category.assoc, signedEvaluation_natural M g (𝟙 I) (𝟙 P), Category.assoc]
    have hc : internalHomMapValue g (map (𝟙 I) (𝟙 P)) ≫ internalHomMapValue (𝟙 Q) j =
        internalHomMapValue (𝟙 T) j ≫ internalHomMapValue g (𝟙 J) := by
      rw [tensorMap_id]
      apply HomologicalComplex.hom_ext
      intro n
      apply ModuleCat.hom_ext
      ext z : 1
      apply Cochain.ext
      intro i k h
      apply ModuleCat.hom_ext
      ext x : 1
      simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, homMap_apply,
        HomologicalComplex.id_f, ModuleCat.id_apply]
    exact congrArg (fun k => signedEvaluation M T I P ≫ k) hc
  letI := tensor_quasiIso_left M P hP p hp'
  haveI : QuasiIso (l ≫ q) := by rw [← hh]; infer_instance
  have hl : QuasiIso l := quasiIso_of_comp_right _ q
  let s := tensorIsoRaw (stalkIso.{u,w,v} f I) (Iso.refl P)
  let c := S.cancel ((coinduceValue.{max u v} f).obj I) P
  let b := (restrictScalarsComplexValue.{max u w v} f).map
    (chainComparison.{u,w,v} f d S I P J j)
  let t := (stalkIso.{u,w,v} f J).inv
  have h : (s.hom ≫ c.inv) ≫ (b ≫ t) = l := by
    rw [Category.assoc]
    exact restricted_chainEvaluation.{u,w,v} f M S I P J j
  haveI : QuasiIso ((s.hom ≫ c.inv) ≫ (b ≫ t)) := h ▸ hl
  haveI : QuasiIso (b ≫ t) := quasiIso_of_comp_left (s.hom ≫ c.inv) _
  exact quasiIso_of_comp_right b t

end RestrictedEvaluation

section DerivedNaturality

open Specs.DerivedFormalization.DerivedCoinduction (Coinduction comparison evaluation)
open Specs.DerivedFormalization.DerivedScalarExtension (Extension flatComplexes)
open Specs.DerivedFormalization.DerivedTensor (Model Descent kFlatHomotopy flatObject flatQh flatQuasiIso)

private theorem leftUnit_natural {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
    {e : R ≃+* R'} (M : AdequateModel e) {P P' : Comp.{v} R} (k : P ⟶ P') :
    map (𝟙 (representedUnit e)) k ≫ (leftUnit M P').hom = (leftUnit M P).hom ≫ k := by
  letI := M.chainMonoidal
  unfold leftUnit
  simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, Category.assoc]
  rw [reassoc_of% (M.tensorModel_natural (𝟙 (representedUnit e)) k)]
  rw [tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
  rw [← leftUnitor_naturality, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
    Category.comp_id, Category.id_comp]

set_option maxHeartbeats 600000 in
private theorem targetAugmentation_natural {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
    {e : R ≃+* R'} (M : AdequateModel e) {I I' P P' : Comp.{v} R}
    (a : representedUnit e ⟶ I) (c : I ⟶ I') (k : P ⟶ P') :
    ((leftUnit M P).inv ≫ map a (𝟙 P) ≫ 𝟙 (tensor I P)) ≫ map c k =
      k ≫ (leftUnit M P').inv ≫ map (a ≫ c) (𝟙 P') ≫ 𝟙 (tensor I' P') := by
  simp only [Category.comp_id, Category.assoc, tensorMap_comp, Category.id_comp]
  have h : (leftUnit M P).inv ≫ map (𝟙 (representedUnit e)) k =
      k ≫ (leftUnit M P').inv := by
    apply (cancel_mono (leftUnit M P').hom).1
    simp only [Category.assoc, leftUnit_natural, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id]
  rw [← Category.assoc k, ← h, Category.assoc, tensorMap_comp, Category.id_comp, Category.comp_id]

set_option maxHeartbeats 600000 in
private theorem targetAugmentation_quasiIso {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
    {e : R ≃+* R'} (M : AdequateModel e) {I P J : Comp.{v} R}
    (a : representedUnit e ⟶ I) [QuasiIso a] (j : tensor I P ⟶ J) [QuasiIso j]
    (hP : isKFlat P) : QuasiIso ((leftUnit M P).inv ≫ map a (𝟙 P) ≫ j) := by
  haveI : QuasiIso (map a (𝟙 P)) := tensor_quasiIso_left M P hP a inferInstance
  infer_instance

variable {A' B' : Type (max u w v)} [CommRing A'] [CommRing B']
variable {e : A ≃+* A'} {d : B ≃+* B'} (MA : AdequateModel e) {MB : AdequateModel d}
variable (T : Model MB) (L : Extension d f) (G : Coinduction.{max u v} f) (S : ModelStability d f)

private def chainTrace (I P : Comp.{max u w v} A) :
    (restrictScalarsComplexValue.{max u w v} f).obj
      (tensor ((coinduceValue.{max u v} f).obj I) ((extension d f).obj P)) ⟶ tensor I P :=
  (S.cancel ((coinduceValue.{max u v} f).obj I) P).hom ≫ map (evaluationValue.{max u v} f I) (𝟙 P)

private theorem chainTrace_natural {I I' P P' : Comp.{max u w v} A}
    (c : I ⟶ I') (k : P ⟶ P') :
    (restrictScalarsComplexValue.{max u w v} f).map
        (map ((coinduceValue.{max u v} f).map c) ((extension d f).map k)) ≫
        chainTrace.{u,w,v} f S I' P' =
      chainTrace.{u,w,v} f S I P ≫ map c k := by
  let U := restrictScalarsComplexValue.{max u w v} f
  let C := coinduceValue.{max u v} f
  let E := extension d f
  let a := coinductionAdjunction.{u,w,v} f
  have hn := a.counit.naturality c
  change U.map (C.map c) ≫ evaluationValue.{max u v} f I' = evaluationValue.{max u v} f I ≫ c at hn
  simp only [chainTrace]
  rw [reassoc_of% (S.cancel_natural (C.map c) k), tensorMap_comp, Category.comp_id,
    Category.assoc, tensorMap_comp, Category.id_comp, hn]

private theorem comparison_natural (I I' : Comp.{max u w v} A) (c : I ⟶ I') :
    (qValue B).map ((coinduceValue.{max u v} f).map c) ≫ comparison.{max u v} f G.adjunction I' =
      comparison.{max u v} f G.adjunction I ≫ G.functor.map ((qValue A).map c) := by
  let C := coinduceValue.{max u v} f
  let U := restrictScalarsComplexValue.{max u w v} f
  let U' := derivedRestrictScalarsValue.{max u w v} f
  let qA := qValue.{max u w v} A
  let qB := qValue.{max u w v} B
  let factor := derivedRestrictScalarsFactorsValue.{max u w v} f
  let a := G.adjunction
  have hn := (coinductionAdjunction.{u,w,v} f).counit.naturality c
  change U.map (C.map c) ≫ evaluationValue.{max u v} f I' =
    evaluationValue.{max u v} f I ≫ c at hn
  unfold comparison Specs.DerivedFormalization.DerivedCoinduction.evaluation
  rw [← a.homEquiv_naturality_left, ← a.homEquiv_naturality_right]
  congr 1
  have hf := factor.hom.naturality (C.map c)
  change U'.map (qB.map (C.map c)) ≫ factor.hom.app (C.obj I') =
    factor.hom.app (C.obj I) ≫ qA.map (U.map (C.map c)) at hf
  rw [reassoc_of% hf, ← qA.map_comp, hn, qA.map_comp, Category.assoc]

private theorem sourceModel_natural {I I' P P' : Comp.{max u w v} A}
    (a : representedUnit e ⟶ I) (a' : representedUnit e ⟶ I')
    [QuasiIso a] [QuasiIso a'] (hI : isKInjectiveValue I) (hI' : isKInjectiveValue I')
    (hP : isKFlat P) (hP' : isKFlat P') (c : I ⟶ I') (k : P ⟶ P')
    (hc : (qValue A).map a ≫ (qValue A).map c = (qValue A).map a') :
    (source f e d T L G).map ((qValue A).map k) ≫ (sourceModel f e d T L G a' hI' P' hP').hom =
      (sourceModel f e d T L G a hI P hP).hom ≫
        (qValue B).map (map ((coinduceValue.{max u v} f).map c) ((extension d f).map k)) := by
  let C := coinduceValue.{max u v} f
  let E := extension d f
  let qA := qValue.{max u w v} A
  let qB := qValue.{max u w v} B
  letI := T.toDescent.monoidal
  letI := G.comparison_isIso I hI
  letI := G.comparison_isIso I' hI'
  haveI : IsIso (qA.map a) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{max u w v} A) a).2 inferInstance
  haveI : IsIso (qA.map a') :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{max u w v} A) a').2 inferInstance
  let sa := G.modelIso f I (asIso (qA.map a)) hI
  let sa' := G.modelIso f I' (asIso (qA.map a')) hI'
  have hIcmp : sa.hom ≫ qB.map (C.map c) = sa'.hom := by
    apply (cancel_mono (comparison.{max u v} f G.adjunction I')).1
    rw [Category.assoc, comparison_natural f G]
    change (G.functor.map (qA.map a) ≫ inv (comparison.{max u v} f G.adjunction I)) ≫
      comparison.{max u v} f G.adjunction I ≫ G.functor.map (qA.map c) =
      (G.functor.map (qA.map a') ≫ inv (comparison.{max u v} f G.adjunction I')) ≫
        comparison.{max u v} f G.adjunction I'
    simp only [Category.assoc, IsIso.inv_hom_id_assoc, IsIso.inv_hom_id, Category.comp_id,
      ← Functor.map_comp]
    congr 1
    rw [qA.map_comp]
    exact hc
  have hPcmp := L.factors.hom.naturality
    (show (⟨P, hP⟩ : (flatComplexes.{u,max u w v} A).FullSubcategory) ⟶ ⟨P', hP'⟩
      from ObjectProperty.homMk k)
  change L.derived.map (qA.map k) ≫ (L.toLift.model P' hP').hom =
    (L.toLift.model P hP).hom ≫ qB.map (E.map k) at hPcmp
  let aP := T.compare (C.obj I) (E.obj P) (Or.inr (L.preservesFlat P hP))
  let aP' := T.compare (C.obj I') (E.obj P') (Or.inr (L.preservesFlat P' hP'))
  change ((𝟙 _) ⊗ₘ L.derived.map (qA.map k)) ≫
      (tensorIso sa' (L.toLift.model P' hP') ≪≫ aP').hom =
    (tensorIso sa (L.toLift.model P hP) ≪≫ aP).hom ≫ qB.map (map (C.map c) (E.map k))
  simp only [Iso.trans_hom, tensorIso_hom, Category.assoc]
  have hn := T.compare_natural (C.map c) (E.map k)
    (Or.inr (L.preservesFlat P hP)) (Or.inr (L.preservesFlat P' hP'))
  change ((qB.map (C.map c)) ⊗ₘ (qB.map (E.map k))) ≫ aP'.hom =
    aP.hom ≫ qB.map (map (C.map c) (E.map k)) at hn
  rw [← hn, tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc,
    Category.id_comp, hPcmp, hIcmp]

private def modelAugmentation {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
    {e : R ≃+* R'} (M : AdequateModel e) {I : Comp.{v} R} (a : representedUnit e ⟶ I)
    (P : Comp.{v} R) : P ⟶ tensor I P :=
  (leftUnit M P).inv ≫ map a (𝟙 P) ≫ 𝟙 (tensor I P)

private theorem modelAugmentation_isIso {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
    {e : R ≃+* R'} (M : AdequateModel e) {I : Comp.{v} R} (a : representedUnit e ⟶ I)
    [QuasiIso a] (P : Comp.{v} R) (hP : isKFlat P) :
    IsIso ((qValue R).map (modelAugmentation M a P)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{v} R) _).2
    (targetAugmentation_quasiIso M a (𝟙 _) hP)

/-- Transpose the localized balanced cancellation and the coinduction counit on
a K-flat presentation of the variable. -/
private def modelMap {I : Comp.{max u w v} A} (a : representedUnit e ⟶ I) [QuasiIso a]
    (hI : isKInjectiveValue I) (P : Comp.{max u w v} A) (hP : isKFlat P) :
    (source f e d T L G).obj ((qValue A).obj P) ⟶ G.functor.obj ((qValue A).obj P) :=
  letI := modelAugmentation_isIso MA a P hP
  G.adjunction.homEquiv _ _
    ((derivedRestrictScalarsValue.{max u w v} f).map (sourceModel f e d T L G a hI P hP).hom ≫
      (derivedRestrictScalarsFactorsValue.{max u w v} f).hom.app
        (tensor ((coinduceValue.{max u v} f).obj I) ((extension d f).obj P)) ≫
      (qValue A).map (chainTrace.{u,w,v} f S I P) ≫
      inv ((qValue A).map (modelAugmentation MA a P)))

set_option maxHeartbeats 600000 in
private theorem modelAugmentation_comm {I I' P P' : Comp.{max u w v} A}
    (a : representedUnit e ⟶ I) (a' : representedUnit e ⟶ I')
    (c : I ⟶ I') (k : P ⟶ P') (hP' : isKFlat P')
    (hc : (qValue A).map a ≫ (qValue A).map c = (qValue A).map a') :
    (qValue A).map (modelAugmentation MA a P) ≫ (qValue A).map (map c k) =
      (qValue A).map k ≫ (qValue A).map (modelAugmentation MA a' P') := by
  let qA := qValue.{max u w v} A
  change qA.map (modelAugmentation MA a P) ≫ qA.map (map c k) =
    qA.map k ≫ qA.map (modelAugmentation MA a' P')
  have htA : modelAugmentation MA a P ≫ map c k =
      k ≫ modelAugmentation MA (a ≫ c) P' := targetAugmentation_natural MA a c k
  rw [← qA.map_comp, htA, qA.map_comp]
  congr 1
  simp only [modelAugmentation, Category.comp_id, qA.map_comp]
  congr 1
  let T := DerivedFormalization.DerivedTensor.model MA
  let U := representedUnit e
  have ht := T.compare_natural (a ≫ c) (𝟙 P') (Or.inr hP') (Or.inr hP')
  have ht' := T.compare_natural a' (𝟙 P') (Or.inr hP') (Or.inr hP')
  have hqa : qA.map (a ≫ c) = qA.map a' := (qA.map_comp a c).trans hc
  have he := congrArg (fun (z : qA.obj U ⟶ qA.obj I') =>
    T.tensorFunctor.map
      (show (qA.obj U, qA.obj P') ⟶ (qA.obj I', qA.obj P') from (z, qA.map (𝟙 P'))) ≫
      (T.compare I' P' (Or.inr hP')).hom) hqa
  exact (cancel_epi (T.compare U P' (Or.inr hP')).hom).1 (ht.symm.trans (he.trans ht'))

set_option maxHeartbeats 800000 in
private theorem modelMap_natural {I I' P P' : Comp.{max u w v} A}
    (a : representedUnit e ⟶ I) (a' : representedUnit e ⟶ I')
    [QuasiIso a] [QuasiIso a'] (hI : isKInjectiveValue I) (hI' : isKInjectiveValue I')
    (hP : isKFlat P) (hP' : isKFlat P') (c : I ⟶ I') (k : P ⟶ P')
    (hc : (qValue A).map a ≫ (qValue A).map c = (qValue A).map a') :
    (source f e d T L G).map ((qValue A).map k) ≫ modelMap f MA T L G S a' hI' P' hP' =
      modelMap f MA T L G S a hI P hP ≫ G.functor.map ((qValue A).map k) := by
  let U := restrictScalarsComplexValue.{max u w v} f
  let U' := derivedRestrictScalarsValue.{max u w v} f
  let qA := qValue.{max u w v} A
  let qB := qValue.{max u w v} B
  let δ := derivedRestrictScalarsFactorsValue.{max u w v} f
  let c₀ := map ((coinduceValue.{max u v} f).map c) ((extension d f).map k)
  haveI := modelAugmentation_isIso MA a P hP
  haveI := modelAugmentation_isIso MA a' P' hP'
  apply (G.adjunction.homEquiv _ _).symm.injective
  rw [G.adjunction.homEquiv_naturality_left_symm, G.adjunction.homEquiv_naturality_right_symm]
  simp only [modelMap, Equiv.symm_apply_apply]
  simp only [← Category.assoc, ← Functor.map_comp]
  rw [sourceModel_natural f T L G a a' hI hI' hP hP' c k hc]
  simp only [Functor.map_comp, Category.assoc]
  have hn := δ.hom.naturality c₀
  change U'.map (qB.map c₀) ≫ δ.hom.app _ = δ.hom.app _ ≫ qA.map (U.map c₀) at hn
  have htrace := chainTrace_natural.{u,w,v} f S c k
  change U.map c₀ ≫ chainTrace.{u,w,v} f S I' P' =
    chainTrace.{u,w,v} f S I P ≫ map c k at htrace
  rw [reassoc_of% hn, ← Functor.map_comp_assoc qA (U.map c₀) (chainTrace.{u,w,v} f S I' P'),
    htrace, Functor.map_comp_assoc]
  have ht : qA.map (map c k) ≫ inv (qA.map (modelAugmentation MA a' P')) =
      inv (qA.map (modelAugmentation MA a P)) ≫ qA.map k := by
    apply (cancel_mono (qA.map (modelAugmentation MA a' P'))).1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [← modelAugmentation_comm.{u,w,v} MA a a' c k hP' hc, IsIso.inv_hom_id_assoc]
  rw [ht]

set_option maxHeartbeats 800000 in
private theorem modelMap_on_replacement {I P J : Comp.{max u w v} A}
    (a : representedUnit e ⟶ I) [QuasiIso a] (hI : isKInjectiveValue I)
    (hP : isKFlat P) (j : tensor I P ⟶ J) :
    modelMap f MA T L G S a hI P hP ≫ G.functor.map ((qValue A).map (targetAugmentation.{u,w,v} e MA a j)) =
      (sourceModel f e d T L G a hI P hP).hom ≫
        (qValue B).map (chainComparison.{u,w,v} f d S I P J j) ≫
        comparison.{max u v} f G.adjunction J := by
  let U := restrictScalarsComplexValue.{max u w v} f
  let U' := derivedRestrictScalarsValue.{max u w v} f
  let qA := qValue.{max u w v} A
  let qB := qValue.{max u w v} B
  let δ := derivedRestrictScalarsFactorsValue.{max u w v} f
  let b := chainComparison.{u,w,v} f d S I P J j
  let aug := modelAugmentation MA a P
  let a₀ := coinductionAdjunction.{u,w,v} f
  haveI := modelAugmentation_isIso MA a P hP
  have haug : targetAugmentation.{u,w,v} e MA a j = aug ≫ j := by
    change (leftUnit MA P).inv ≫ map a (𝟙 P) ≫ j =
      ((leftUnit MA P).inv ≫ map a (𝟙 P) ≫ 𝟙 _) ≫ j
    simp
  have htrace : U.map b ≫ evaluationValue.{max u v} f J = chainTrace.{u,w,v} f S I P ≫ j := by
    have h := a₀.homEquiv_counit (g := b)
    change (a₀.homEquiv _ _).symm b = U.map b ≫ evaluationValue.{max u v} f J at h
    rw [← h]
    change (a₀.homEquiv _ _).symm (a₀.homEquiv _ _ (chainTrace.{u,w,v} f S I P) ≫
      (coinduceValue.{max u v} f).map j) = _
    rw [a₀.homEquiv_naturality_right_symm, Equiv.symm_apply_apply]
  apply (G.adjunction.homEquiv _ _).symm.injective
  rw [G.adjunction.homEquiv_naturality_right_symm, G.adjunction.homEquiv_naturality_left_symm,
    G.adjunction.homEquiv_naturality_left_symm]
  simp only [modelMap, comparison, Equiv.symm_apply_apply, Category.assoc]
  change U'.map (sourceModel f e d T L G a hI P hP).hom ≫ δ.hom.app _ ≫
    qA.map (chainTrace.{u,w,v} f S I P) ≫ inv (qA.map aug) ≫
      qA.map (targetAugmentation.{u,w,v} e MA a j) =
    U'.map (sourceModel f e d T L G a hI P hP).hom ≫ U'.map (qB.map b) ≫
      δ.hom.app _ ≫ qA.map (evaluationValue.{max u v} f J)
  have hn := δ.hom.naturality b
  change U'.map (qB.map b) ≫ δ.hom.app _ = δ.hom.app _ ≫ qA.map (U.map b) at hn
  rw [haug, qA.map_comp, IsIso.inv_hom_id_assoc, reassoc_of% hn,
    ← qA.map_comp (U.map b) (evaluationValue.{max u v} f J), htrace,
    qA.map_comp (chainTrace.{u,w,v} f S I P) j]

open private localizedHomEquiv localizedHomEquiv_map from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedCoinduction

private theorem injectiveModelMap_exists {I I' : Comp.{max u w v} A}
    (a : representedUnit e ⟶ I) (a' : representedUnit e ⟶ I')
    [QuasiIso a] (hI' : isKInjectiveValue I') :
    ∃ c : I ⟶ I', (qValue A).map a ≫ (qValue A).map c = (qValue A).map a' := by
  let qA := qValue.{max u w v} A
  letI := hI'
  letI : IsIso (qA.map a) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{max u w v} A) a).2 inferInstance
  obtain ⟨g, hg⟩ := (localizedHomEquiv I I').surjective (inv (qA.map a) ≫ qA.map a')
  obtain ⟨c, rfl⟩ := (HomotopyCategory.quotient (ModuleCat.{max u w v} A) (.up ℤ)).map_surjective g
  rw [localizedHomEquiv_map] at hg
  exact ⟨c, by rw [hg, IsIso.hom_inv_id_assoc]⟩

private def modelTransformation {I : Comp.{max u w v} A}
    (a : representedUnit e ⟶ I) [QuasiIso a] (hI : isKInjectiveValue I) :
    flatQh.{u,max u w v} A ⋙ source f e d T L G ⟶ flatQh.{u,max u w v} A ⋙ G.functor where
  app X :=
    (source f e d T L G).map ((quotientCompQhIsoValue A).hom.app X.obj.as) ≫
      modelMap f MA T L G S a hI X.obj.as X.property ≫
      G.functor.map ((quotientCompQhIsoValue A).inv.app X.obj.as)
  naturality {X Y} k := by
    let F := source f e d T L G
    let qK := quotientValue.{max u w v} A
    let qD := qhValue.{max u w v} A
    let Q := qValue.{max u w v} A
    let ζ := quotientCompQhIsoValue.{max u w v} A
    let h : X.obj ⟶ Y.obj := (kFlatHomotopy.{u,max u w v} A).ι.map k
    obtain ⟨r, hr⟩ := (HomotopyCategory.quotient (ModuleCat.{max u w v} A) (.up ℤ)).map_surjective h
    change qK.map r = h at hr
    have h₁ : qD.map h ≫ ζ.hom.app Y.obj.as = ζ.hom.app X.obj.as ≫ Q.map r := by
      rw [← hr]
      exact ζ.hom.naturality r
    have h₂ : Q.map r ≫ ζ.inv.app Y.obj.as = ζ.inv.app X.obj.as ≫ qD.map h := by
      rw [← hr]
      exact ζ.inv.naturality r
    have hm := modelMap_natural f MA T L G S a a hI hI X.property Y.property (𝟙 I) r
      (by rw [(qValue.{max u w v} A).map_id, Category.comp_id])
    change F.map (qD.map h) ≫ F.map (ζ.hom.app _) ≫ _ ≫ G.functor.map (ζ.inv.app _) =
      (F.map (ζ.hom.app _) ≫ _ ≫ G.functor.map (ζ.inv.app _)) ≫ G.functor.map (qD.map h)
    simp only [Category.assoc]
    rw (config := {transparency := .default})
      [← Functor.map_comp_assoc F (qD.map h) (ζ.hom.app Y.obj.as), h₁,
        Functor.map_comp_assoc F (ζ.hom.app X.obj.as) (Q.map r), reassoc_of% hm,
        ← G.functor.map_comp, h₂, G.functor.map_comp]
    all_goals rfl

private theorem modelMap_isIso
    (hp : Specs.DerivedFormalization.PerfectComplex.isPerfectValue
      ((qValue A).obj (algebraStalk.{u,w,v} f)))
    {I : Comp.{max u w v} A} (a : representedUnit e ⟶ I) [QuasiIso a]
    (hI : isKInjectiveValue I) (P : Comp.{max u w v} A) (hP : isKFlat P) :
    IsIso (modelMap f MA T L G S a hI P hP) := by
  obtain ⟨J, j, _, hj, hJ, _⟩ :=
    DerivedFormalization.kInjectiveReplacement.{u,max w v} (tensor I P)
  let b := chainComparison.{u,w,v} f d S I P J j
  let aug := targetAugmentation.{u,w,v} e MA a j
  have hb : QuasiIso ((restrictScalarsComplexValue.{max u w v} f).map b) :=
    chainComparisonQuasiIso.{u,w,v} f e d S hp I P J a j inferInstance hI hP hj hJ
  haveI : QuasiIso b := (HomologicalComplex.quasiIso_map_iff_of_preservesHomology b
    (ModuleCat.restrictScalars.{max u w v} f)).1 hb
  haveI : QuasiIso j := hj
  haveI : IsIso ((qValue A).map aug) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{max u w v} A) aug).2
      (targetAugmentation_quasiIso MA a j hP)
  haveI := G.comparison_isIso J hJ
  haveI : IsIso (modelMap f MA T L G S a hI P hP ≫ G.functor.map ((qValue A).map aug)) := by
    rw [modelMap_on_replacement]
    change IsIso ((sourceModel f e d T L G a hI P hP).hom ≫
      (qValue B).map b ≫ comparison.{max u v} f G.adjunction J)
    infer_instance
  exact IsIso.of_isIso_comp_right _ (G.functor.map ((qValue A).map aug))

set_option maxHeartbeats 650000 in
theorem relativeDuality : RelativeDuality.{u,w,v} := by
  intro A B _ _ f A' B' _ _ e d MA MB T L G S hp
  obtain ⟨I, a, _, ha, hI, _⟩ :=
    DerivedFormalization.kInjectiveReplacement.{u,max w v} (representedUnit e)
  letI : QuasiIso a := ha
  let F := source f e d T L G
  let Q := qValue.{max u w v} A
  let q := flatQh.{u,max u w v} A
  let W := flatQuasiIso.{u,max u w v} A
  letI : q.IsLocalization W := (DerivedFormalization.DerivedTensor.model MA).localization
  let tr := modelTransformation f MA T L G S a hI
  let full := Localization.fullyFaithfulWhiskeringLeft q W (derivedValue.{max u w v} B)
  let η : F ⟶ G.functor := full.preimage tr
  have hi (X : (kFlatHomotopy.{u,max u w v} A).FullSubcategory) :
      η.app (q.obj X) = tr.app X :=
    congrArg (fun h : q ⋙ F ⟶ q ⋙ G.functor => h.app X) (full.map_preimage tr)
  have hη (P : Comp.{max u w v} A) (hP : isKFlat P) :
      η.app (Q.obj P) = modelMap f MA T L G S a hI P hP := by
    let X := flatObject A P hP
    let ζ := (quotientCompQhIsoValue A).app P
    have hn := η.naturality ζ.hom
    change F.map ζ.hom ≫ η.app (Q.obj P) = η.app (q.obj X) ≫ G.functor.map ζ.hom at hn
    rw [hi X] at hn
    change F.map ζ.hom ≫ η.app (Q.obj P) =
      (F.map ζ.hom ≫ modelMap f MA T L G S a hI P hP ≫ G.functor.map ζ.inv) ≫
        G.functor.map ζ.hom at hn
    apply (cancel_epi (F.map ζ.hom)).1
    have hi' : G.functor.map ζ.inv ≫ G.functor.map ζ.hom = 𝟙 _ := by
      rw [← G.functor.map_comp, Iso.inv_hom_id]
      exact G.functor.map_id _
    simpa only [Category.assoc, hi', Category.comp_id] using hn
  refine ⟨η, ?_, ?_⟩
  · rw [NatTrans.isIso_iff_isIso_app]
    haveI := Localization.essSurj q W
    intro Y
    let X := q.objPreimage Y
    let s := q.objObjPreimageIso Y
    haveI : IsIso (η.app (q.obj X)) := by
      rw [hi X]
      haveI := modelMap_isIso f MA T L G S hp a hI X.obj.as X.property
      let ζ := (quotientCompQhIsoValue A).app X.obj.as
      change IsIso (F.map ζ.hom ≫ modelMap f MA T L G S a hI X.obj.as X.property ≫ G.functor.map ζ.inv)
      infer_instance
    haveI : IsIso (F.map s.hom ≫ η.app Y) := by rw [η.naturality]; infer_instance
    exact IsIso.of_isIso_comp_left (F.map s.hom) _
  · intro I' P J a' _ hI' hP j _ _
    refine ⟨targetAugmentation_quasiIso MA a' j hP, ?_⟩
    rw [hη P hP]
    obtain ⟨c, hc⟩ := injectiveModelMap_exists.{u,w,v} a a' hI'
    have hn := modelMap_natural f MA T L G S a a' hI hI' hP hP c (𝟙 P) hc
    change F.map (Q.map (𝟙 P)) ≫ _ = _ ≫ G.functor.map (Q.map (𝟙 P)) at hn
    rw [Q.map_id P, F.map_id (Q.obj P), G.functor.map_id (Q.obj P),
      Category.id_comp, Category.comp_id] at hn
    rw [← hn, modelMap_on_replacement]


open Specs.DerivedFormalization.CochainCoefficientLift (lift liftDFactors)

set_option maxHeartbeats 700000 in
theorem relativeDualityOnOriginal : RelativeDualityOnOriginal.{u,w,v} := by
  intro A B _ _ f A' B' _ _ e d MA MB T L G S qA qB F hp
  obtain ⟨η, hη, hmodel⟩ := relativeDuality.{u,w,v} f MA T L G S hp
  refine ⟨η, hη, ?_⟩
  intro X I a _ hI X' Y
  obtain ⟨P, p, hpQ, _, _, _, hP, _, _⟩ :=
    DerivedFormalization.SemifreeReplacement.adequateReplacement.{u,v,w} A X
  obtain ⟨J, i, hiQ, hJ, _, _, _, _, _⟩ :=
    DerivedFormalization.derivedCoinductionLiftedModel.{v,u,w,0} f G X
  letI := hpQ
  letI := hiQ
  letI : IsIso (qA.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{max u w v} A) p).2 hpQ
  letI : IsIso (qA.map i) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{max u w v} A) i).2 hiQ
  let α := (liftDFactors.{max u w, v} A).app X ≪≫ (asIso (qA.map p)).symm
  let β := (liftDFactors.{max u w, v} A).app X ≪≫ asIso (qA.map i)
  let aug := modelAugmentation MA a P
  haveI : IsIso (qA.map aug) := modelAugmentation_isIso MA a P hP
  let m := inv (qA.map aug) ≫ qA.map p ≫ qA.map i
  letI := hJ
  obtain ⟨g, hg⟩ := (localizedHomEquiv (tensor I P) J).surjective m
  obtain ⟨j, rfl⟩ := (HomotopyCategory.quotient (ModuleCat.{max u w v} A) (.up ℤ)).map_surjective g
  rw [localizedHomEquiv_map] at hg
  change qA.map j = m at hg
  have hjQ : QuasiIso j :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{max u w v} A) j).1
      (by change IsIso (qA.map j); rw [hg]; dsimp only [m]; infer_instance)
  letI := hjQ
  have hau : qA.map (targetAugmentation.{u,w,v} e MA a j) = qA.map p ≫ qA.map i := by
    have h : targetAugmentation.{u,w,v} e MA a j = aug ≫ j := by
      change (leftUnit MA P).inv ≫ map a (𝟙 P) ≫ j =
        ((leftUnit MA P).inv ≫ map a (𝟙 P) ≫ 𝟙 _) ≫ j
      simp
    rw [h, qA.map_comp, hg, IsIso.hom_inv_id_assoc]
  refine ⟨P, J, p, i, j, hpQ, hiQ, hP, hJ, hjQ, hau.trans (qA.map_comp p i).symm, ?_⟩
  change η.app _ ≫ (G.modelIso f J β hJ).hom =
    F.map α.hom ≫ (sourceModel f e d T L G a hI P hP).hom ≫
      qB.map (chainComparison.{u,w,v} f d S I P J j)
  let c := comparison.{max u v} f G.adjunction J
  haveI : IsIso c := G.comparison_isIso J hJ
  have hcmp : (G.modelIso f J β hJ).hom ≫ c = G.functor.map β.hom := by
    change (G.functor.map β.hom ≫ inv c) ≫ c = _
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hβ : α.hom ≫ qA.map (targetAugmentation.{u,w,v} e MA a j) = β.hom := by
    rw [hau]
    change ((liftDFactors.{max u w, v} A).hom.app X ≫ inv (qA.map p)) ≫
      qA.map p ≫ qA.map i = (liftDFactors.{max u w, v} A).hom.app X ≫ qA.map i
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  apply (cancel_mono c).1
  simp only [Category.assoc, hcmp]
  have hnat := η.naturality α.hom
  change F.map α.hom ≫ η.app (qA.obj P) = η.app Y ≫ G.functor.map α.hom at hnat
  rw [← (hmodel I P J a hI hP j hJ).2, reassoc_of% hnat, ← G.functor.map_comp, hβ]
  rfl

end DerivedNaturality

end

end DerivedFormalization.PerfectRelativeDual
