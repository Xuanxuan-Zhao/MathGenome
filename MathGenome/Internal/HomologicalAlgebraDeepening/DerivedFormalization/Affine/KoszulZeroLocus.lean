import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.KoszulZeroLocus
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.DerivedAffineBaseChange
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.KoszulCochainResolution
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.PolynomialExample
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Data.Finsupp.Indicator
import Batteries.Tactic.OpenPrivate

/-! The Koszul model of the derived zero locus over a characteristic-zero field. -/

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Specs.DerivedFormalization.Affine.KoszulZeroLocus
open Specs.DerivedFormalization.Affine.TensorResolutionComparison
open Specs.DerivedFormalization.KoszulCochainResolution (cochainValue termIsoValue augmentationValue)

namespace DerivedFormalization.Affine.KoszulZeroLocus

open NonpositiveCDGA (ordinary ordinaryMap ordinaryFunctor)
open Semifree
open _root_.AdvCommAlg.Koszul (listIdeal listForm)
open _root_.AdvCommAlg.Koszul.PolynomialExample
open _root_.DerivedFormalization

universe u v

noncomputable section

variable {k : Type u} [Field k] [CharZero k]
variable {r : ℕ} {R : CommAlgCat.{v} k} {f : Fin r → R}

omit [CharZero k] in
private theorem chainMap_d_apply {X Y : ModuleCochain.{u,v} k} (q : X ⟶ Y)
    (i j : ℤ) (x : X.X i) : q.f j (X.d i j x) = Y.d i j (q.f i x) :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (q.comm i j).symm) x

theorem wedgeDifferential (P : KoszulAlgebra R f) : P.WedgeDifferential := by
  intro n x
  let Y := (restrictCochains R).obj (cochainValue (List.ofFn f))
  let i : ℤ := -((n + 1 : ℕ) : ℤ)
  let j : ℤ := -(n : ℤ)
  let y : Y.X i := (termIsoValue (List.ofFn f) (n + 1)).inv (exteriorPower.ιMulti R (n + 1) x)
  let F : Y.X j → ⋀[R]^n (Fin (List.ofFn f).length → R) :=
    fun z => (termIsoValue (List.ofFn f) n).hom z
  change F (P.cochain.hom.f j (P.obj.complex.d i j (P.cochain.inv.f i y))) = _
  rw [chainMap_d_apply]
  have h : P.cochain.hom.f i (P.cochain.inv.f i y) = y :=
    DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (congrArg
      (fun t => t.f i) P.cochain.inv_hom_id)) y
  rw [h]
  exact koszulCochain_d_wedge (List.ofFn f) n x

private theorem augmentation_quasiIso_of_cochain (P : KoszulAlgebra R f)
    (hq : QuasiIso (augmentationValue (List.ofFn f))) :
    NonpositiveCDGA.IsQuasiIso P.augmentation := by
  change QuasiIso P.augmentation.chainMap
  rw [P.augmentation_cochain]
  have : QuasiIso ((restrictCochains R).map (augmentationValue (List.ofFn f))) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology _ (ModuleCat.restrictScalars (algebraMap k R))
  infer_instance

theorem augmentation_isResolution (P : KoszulAlgebra R f)
    (h : RingTheory.Sequence.IsRegular R (List.ofFn f)) :
    NonpositiveCDGA.DegreewiseSurjective P.augmentation ∧
      NonpositiveCDGA.IsQuasiIso P.augmentation := by
  obtain ⟨hq, hs, -, -⟩ := koszulCochain_finiteFree_resolution (List.ofFn f) h
  constructor
  · intro i
    change Function.Surjective (P.augmentation.chainMap.f i)
    rw [P.augmentation_cochain]
    have hm := (ModuleCat.epi_iff_surjective _).mp (hs i)
    exact ((ModuleCat.epi_iff_surjective _).mp
      (inferInstance : Epi ((quotientStalkIso R f).hom.f i))).comp
        (hm.comp ((ModuleCat.epi_iff_surjective _).mp
          (inferInstance : Epi (P.cochain.hom.f i))))
  · exact augmentation_quasiIso_of_cochain P hq

private def oneStage (r : ℕ) : Stages (exteriorVariables.{v} r) where
  Stage := PUnit.{v+1}
  order := inferInstance
  wellFounded := wellFounded_lt
  stage _ := PUnit.unit

private def equationValues (R : CommAlgCat.{v} k) (f : Fin r → R)
    (i : (exteriorVariables.{v} r).Index) :
    Polynomial (ordinary R) (exteriorVariables r) ((exteriorVariables r).degree i + 1) :=
  coefficient (ordinary R) (exteriorVariables r) 0 (f i.down)

private theorem equationCycles (R : CommAlgCat.{v} k) (f : Fin r → R) :
    EarlierCycles (ordinary R) (exteriorVariables r) (oneStage r) (equationValues R f) := by
  intro i dy D _
  let a : (ordinary R).complex.X 0 := f i.down
  change D.d 0 (coefficient (ordinary R) (exteriorVariables r) 0 a) = 0
  have h : (ordinary R).complex.d 0 (0+1) a = 0 := (ordinary R).d_zero_apply a
  rw [D.on_base 0 a, h, map_zero]

def exteriorAlgebra (R : CommAlgCat.{v} k) (f : Fin r → R) : NonpositiveCDGA.{u,v} k :=
  stagedAlgebra (oneStage r) (equationValues R f) (equationCycles R f)

def exteriorBase (R : CommAlgCat.{v} k) (f : Fin r → R) : ordinary R ⟶ exteriorAlgebra R f :=
  stagedBase (oneStage r) (equationValues R f) (equationCycles R f)

def exteriorPresentation (R : CommAlgCat.{v} k) (f : Fin r → R) :
    StagedPresentation (ordinary R) (exteriorVariables r) (exteriorBase R f) :=
  stagedPresentation (oneStage r) (equationValues R f)
    (fun i => (show UsesOnly (ordinary R) (exteriorVariables r) _
      (coefficient (ordinary R) (exteriorVariables r) 0 (f i.down)) from coefficient_usesOnly 0 _)) (equationCycles R f)

theorem exterior_d_generator (R : CommAlgCat.{v} k) (f : Fin r → R) (i : Fin r) :
    (exteriorAlgebra R f).complex.d (-1) 0
      ((exteriorPresentation R f).component (-1)
        (variableTerm (ordinary R) (exteriorVariables r) (ULift.up i))) =
      (exteriorBase R f).chainMap.f 0 (f i) := by
  let D := extendDerivation (equationValues R f)
  let hc : ∀ x, D.d ((exteriorVariables.{v} r).degree x + 1) (equationValues R f x) = 0 :=
    fun x => equationCycles R f x _ D fun _ _ => rfl
  change (polynomialComplex D hc).d (-1) (-1+1)
    (variableTerm (ordinary R) (exteriorVariables r) (ULift.up i)) = _
  rw [polynomialComplex_d]
  change (extendDerivation (equationValues R f)).d ((exteriorVariables.{v} r).degree (ULift.up i))
    (variableTerm (ordinary R) (exteriorVariables r) (ULift.up i)) = _
  rw [(extendDerivation (equationValues R f)).on_var]
  rfl

open private evaluate generatorDifferential evaluation_comm_on polynomialDifferential
  component_polynomialDifferential from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.SemifreeLifting

private theorem hom_ext_apply {A B : NonpositiveCDGA.{u,v} k} {g h : A ⟶ B}
    (H : ∀ i (x : A.complex.X i), g.chainMap.f i x = h.chainMap.f i x) : g = h :=
  CommDGAlgebra.Hom.ext_chainMap (HomologicalComplex.Hom.ext
    (funext fun i => ModuleCat.hom_ext (LinearMap.ext (H i))))

private theorem hom_congr_apply {A B : NonpositiveCDGA.{u,v} k} {g h : A ⟶ B}
    (H : g = h) (i : ℤ) (x : A.complex.X i) : g.chainMap.f i x = h.chainMap.f i x :=
  congrArg (fun m : A ⟶ B => m.chainMap.f i x) H

section PresentationMaps

variable {P Y : NonpositiveCDGA.{u,v} k} {b : ordinary R ⟶ P}

private abbrev gen (E : StagedPresentation (ordinary R) (exteriorVariables r) b) (i : Fin r) :
    P.complex.X (-1) := E.component (-1) (variableTerm (ordinary R) (exteriorVariables r) (ULift.up i))

/-- Maps from the exterior presentation are determined by the base and generators. -/
private theorem exterior_hom_ext (E : StagedPresentation (ordinary R) (exteriorVariables r) b)
    {g h : P ⟶ Y} (hb : b ≫ g = b ≫ h)
    (he : ∀ i : Fin r, g.chainMap.f (-1) (gen E i) = h.chainMap.f (-1) (gen E i)) :
    g = h := by
  apply hom_ext_apply
  suffices H : ∀ j p, g.chainMap.f j (E.component j p) = h.chainMap.f j (E.component j p) by
    intro j x
    obtain ⟨p, rfl⟩ := (E.component j).surjective x
    exact H j p
  apply polynomial_generated (ordinary R) (exteriorVariables r)
  · intro i
    simp
  · intro i a c ha hc
    simp only [map_add, ha, hc]
  · intro i s a ha
    change (g.chainMap.f i).hom (E.component i (s • a)) =
      (h.chainMap.f i).hom (E.component i (s • a))
    simp only [LinearMap.map_smul_of_tower, ← LinearEquiv.coe_coe]
    exact congrArg (fun z : Y.complex.X i => s • z) ha
  · intro i a
    rw [E.map_base]
    exact hom_congr_apply hb i a
  · intro x
    exact he x.down
  · intro i j n hij a c ha hc
    rw [E.map_mul, g.map_mul, h.map_mul, ha, hc]

/-- Extend a base map and compatible values of generators to a cdga map. -/
private theorem exists_exterior_hom
    (E : StagedPresentation (ordinary R) (exteriorVariables r) b)
    (hd : ∀ i : Fin r, P.complex.d (-1) 0 (gen E i) = b.chainMap.f 0 (f i))
    (g : ordinary R ⟶ Y) (y : Fin r → Y.complex.X (-1))
    (hy : ∀ i, Y.complex.d (-1) 0 (y i) = g.chainMap.f 0 (f i)) :
    ∃ q : P ⟶ Y, b ≫ q = g ∧ ∀ i, q.chainMap.f (-1) (gen E i) = y i := by
  let Yg : ∀ x : (exteriorVariables.{v} r).Index, Y.complex.X ((exteriorVariables.{v} r).degree x) :=
    fun x => y x.down
  let F := evaluate g Yg
  have hvar (x : (exteriorVariables.{v} r).Index) :
      Y.complex.d (-1) 0 (Yg x) = F.component 0 (generatorDifferential E x) := by
    change Y.complex.d (-1) 0 (y x.down) =
      F.component 0 ((E.component 0).symm (P.complex.d (-1) 0 (gen E x.down)))
    let a : (ordinary R).complex.X 0 := f x.down
    have h := E.map_base 0 a
    rw [hd x.down, ← h, LinearEquiv.symm_apply_apply, F.map_base]
    exact hy x.down
  have hc (i : ℤ) (p : Polynomial (ordinary R) (exteriorVariables r) i) :=
    evaluation_comm_on E F Set.univ (fun x _ => hvar x) i p (fun _ _ _ _ => Set.mem_univ _)
  let q : P ⟶ Y :=
    { chainMap :=
        { f := fun i => ModuleCat.ofHom ((F.component i).comp (E.component i).symm.toLinearMap)
          comm' := by
            intro i j hij
            change i + 1 = j at hij
            subst j
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro x
            change Y.complex.d i (i+1) (F.component i ((E.component i).symm x)) =
              F.component (i+1) ((E.component (i+1)).symm (P.complex.d i (i+1) x))
            rw [hc]
            change F.component (i+1) ((E.component (i+1)).symm
              (P.complex.d i (i+1) (E.component i ((E.component i).symm x)))) = _
            rw [LinearEquiv.apply_symm_apply] }
      map_one := by
        change F.component 0 ((E.component 0).symm P.one) = Y.one
        rw [← E.map_one, LinearEquiv.symm_apply_apply, F.map_base, g.map_one]
      map_mul := by
        intro i j n hij a c
        change F.component n ((E.component n).symm (P.mul i j n hij a c)) =
          Y.mul i j n hij (F.component i ((E.component i).symm a))
            (F.component j ((E.component j).symm c))
        have hm := E.map_mul i j n hij ((E.component i).symm a) ((E.component j).symm c)
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at hm
        rw [← hm, LinearEquiv.symm_apply_apply, F.map_mul] }
  refine ⟨q, hom_ext_apply ?_, ?_⟩
  · intro i a
    change F.component i ((E.component i).symm (b.chainMap.f i a)) = g.chainMap.f i a
    rw [← E.map_base, LinearEquiv.symm_apply_apply, F.map_base]
  · intro i
    change F.component (-1) ((E.component (-1)).symm (gen E i)) = y i
    rw [show gen E i = E.component (-1)
      (variableTerm (ordinary R) (exteriorVariables r) (ULift.up i)) from rfl,
      LinearEquiv.symm_apply_apply]
    exact F.map_var (ULift.up i)

end PresentationMaps

open private tensorIsPushout from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.DerivedAffineBaseChange

variable {T : Specs.DerivedFormalization.Affine.Tensor.ModuleTensor.{u,v} k}

theorem tensorComparison (S : CoproductModel T) {B : CommAlgCat.{v} k} {a : Fin r → B}
    (P : KoszulAlgebra B a) (g : ordinary B ⟶ ordinary R) (Q : KoszulAlgebra R f)
    (hg : ∀ i, g.chainMap.f 0 (a i) = (f i : (ordinary R).complex.X 0)) :
    TensorComparison S P g Q := by
  have H := tensorIsPushout S P.base g
  have hbase := H.w
  obtain ⟨p, hp, hpgen⟩ := exists_exterior_hom P.exterior P.d_generator (g ≫ Q.base)
    Q.generator (fun i => (Q.d_generator i).trans (by
      change Q.base.chainMap.f 0 (f i) = Q.base.chainMap.f 0 (g.chainMap.f 0 (a i))
      rw [hg]))
  let l := S.inl P.base g
  let s := S.inr P.base g
  let X := S.tensor P.base g
  let m : X ⟶ Q.obj := H.desc p Q.base hp
  have hm₁ : l ≫ m = p := H.inl_desc p Q.base hp
  have hm₂ : s ≫ m = Q.base := H.inr_desc p Q.base hp
  have hx (i : Fin r) : X.complex.d (-1) 0 (l.chainMap.f (-1) (P.generator i)) =
      s.chainMap.f 0 (f i) := by
    rw [← chainMap_d_apply, P.d_generator]
    have h := hom_congr_apply (g := P.base ≫ l) (h := g ≫ s) hbase 0 (a i)
    change l.chainMap.f 0 (P.base.chainMap.f 0 (a i)) =
      s.chainMap.f 0 (g.chainMap.f 0 (a i)) at h
    rw [h, hg]
  obtain ⟨q, hq, hqgen⟩ := exists_exterior_hom Q.exterior Q.d_generator s
    (fun i => l.chainMap.f (-1) (P.generator i)) hx
  let e : X ≅ Q.obj :=
    { hom := m
      inv := q
      hom_inv_id := by
        have h₁ : l ≫ m ≫ q = l := by
          rw [← Category.assoc, hm₁]
          apply exterior_hom_ext P.exterior
          · rw [← Category.assoc, hp, Category.assoc, hq]
            exact hbase.symm
          · intro i
            change q.chainMap.f (-1) (p.chainMap.f (-1) (gen P.exterior i)) = _
            rw [hpgen, hqgen]
        have h₂ : s ≫ m ≫ q = s := by rw [← Category.assoc, hm₂, hq]
        exact H.hom_ext (h₁.trans (Category.comp_id l).symm)
          (h₂.trans (Category.comp_id s).symm)
      inv_hom_id := by
        apply exterior_hom_ext Q.exterior
        · rw [← Category.assoc, hq, hm₂, Category.comp_id]
        · intro i
          change m.chainMap.f (-1) (q.chainMap.f (-1) (gen Q.exterior i)) = Q.generator i
          rw [hqgen]
          exact (hom_congr_apply hm₁ (-1) (P.generator i)).trans (hpgen i) }
  exact ⟨e, hm₂, fun i => (hom_congr_apply hm₁ (-1) (P.generator i)).trans (hpgen i)⟩

private theorem quotientMap_equation (i : Fin r) :
    (quotientMap R f).chainMap.f 0 (f i) = 0 := by
  change Ideal.Quotient.mk (listIdeal (List.ofFn f)) (f i) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (List.mem_ofFn.mpr ⟨i, rfl⟩))

theorem exists_exterior_augmentation (R : CommAlgCat.{v} k) (f : Fin r → R) :
    ∃ e : exteriorAlgebra R f ⟶ ordinary (quotientAlg R f),
      exteriorBase R f ≫ e = quotientMap R f ∧
      ∀ i : Fin r, e.chainMap.f (-1) (gen (exteriorPresentation R f) i) = 0 :=
  exists_exterior_hom (exteriorPresentation R f) (exterior_d_generator R f)
    (quotientMap R f) (fun _ => 0) (fun i => (map_zero _).trans (quotientMap_equation i).symm)

private theorem polynomialMap_variable (K : CommAlgCat.{v} k) (e : K ≃ₐ[k] k)
    (i : Fin r) : (polynomialMap K e R f).chainMap.f 0 (MvPolynomial.X i) =
      (f i : (ordinary R).complex.X 0) := by
  let g : K →ₐ[k] R := (Algebra.ofId k R).comp e.toAlgHom
  change MvPolynomial.aevalTower g f (MvPolynomial.X i) = f i
  exact MvPolynomial.aevalTower_X g f i

private theorem zeroSection_variable (K : CommAlgCat.{v} k) (i : Fin r) :
    (zeroSection K r).chainMap.f 0 (MvPolynomial.X i) = 0 := by
  let z : Fin r → K := fun _ => 0
  change (MvPolynomial.aeval z) (MvPolynomial.X i) = z i
  exact MvPolynomial.aeval_X z i

theorem polynomialTensorComparison (S : CoproductModel T) (K : CommAlgCat.{v} k)
    (e : K ≃ₐ[k] k) (P : polynomialKoszul K r) (Q : KoszulAlgebra R f) :
    TensorComparison S P (polynomialMap K e R f) Q :=
  tensorComparison S P _ Q (polynomialMap_variable K e)

theorem quotientTensorComparison (S : CoproductModel T) (P : KoszulAlgebra R f)
    (Q : KoszulAlgebra (quotientAlg R f) (fun _ : Fin r => 0)) :
    TensorComparison S P (quotientMap R f) Q :=
  tensorComparison S P _ Q quotientMap_equation

open private presentationDerivation from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.SemifreeLifting

theorem zeroKoszul_differential (P : KoszulAlgebra R (fun _ : Fin r => 0)) (i j : ℤ) :
    P.obj.complex.d i j = 0 := by
  by_cases h : i + 1 = j
  · subst j
    let E := P.exterior
    let D := presentationDerivation E
    have hz (a : ℤ) (p : Polynomial (ordinary R) (exteriorVariables r) a) : D.d a p = 0 := by
      apply polynomial_generated (ordinary R) (exteriorVariables r) (fun a p => D.d a p = 0)
      · intro n
        simp
      · intro n x y hx hy
        simp only [map_add, hx, hy, add_zero]
      · intro n s x hx
        simp only [LinearMap.map_smul_of_tower, hx, smul_zero]
      · intro n a
        rw [D.on_base]
        have hd : (ordinary R).complex.d n (n+1) = 0 :=
          single_obj_d (.up ℤ) 0 (ModuleCat.of k R) n (n+1)
        have hda : (ordinary R).complex.d n (n+1) a = 0 := by rw [hd]; rfl
        rw [hda, map_zero]
      · intro x
        rw [D.on_var]
        change (E.component 0).symm (P.obj.complex.d (-1) 0 (gen E x.down)) = 0
        rw [P.d_generator x.down]
        change (E.component 0).symm ((P.base.chainMap.f 0).hom 0) = 0
        rw [map_zero, map_zero]
      · intro a b n hab x y hx hy
        rw [D.leibniz, hx, hy]
        simp
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨p, rfl⟩ := (E.component i).surjective x
    exact (component_polynomialDifferential E i p).symm.trans (by
      change E.component (i+1) (D.d i p) = _
      rw [hz, map_zero]
      rfl)
  · exact P.obj.complex.shape i j h

open private ordinaryHom_ext from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.DerivedAffineBaseChange

omit [CharZero k] in
theorem polynomial_regular (K : CommAlgCat.{v} k) (e : K ≃ₐ[k] k) (r : ℕ) :
    RingTheory.Sequence.IsRegular (MvPolynomial (Fin r) K) (variableList K r) := by
  have : Nontrivial K := e.symm.injective.nontrivial
  exact variableList_regular K r

omit [CharZero k] in
/-- Relate the ordinary polynomial augmentation to the cochain augmentation
to the same quotient before changing coefficient rings. -/
private theorem polynomialQuotient_quasiIso (K : CommAlgCat.{v} k) (e : K ≃ₐ[k] k) (r : ℕ) :
    QuasiIso (augmentationValue (List.ofFn (MvPolynomial.X (R := K) (σ := Fin r)))) := by
  have : Nontrivial K := e.symm.injective.nontrivial
  let A := MvPolynomial (Fin r) K
  let : Algebra A K := evaluationAlgebra K r
  obtain ⟨π, hπ, hq, -, -⟩ := resolves_coefficients K r
  have hname : π = polynomialAugmentation K r := by
    apply HomologicalComplex.to_single_hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    let p : A := exteriorPower.zeroEquiv A _ z
    change π.f 0 z = quotientCoefficientsEquiv (A := K) (r := r) (Ideal.Quotient.mk _ p)
    exact (hπ z).trans (quotientCoefficientsEquiv_mk p).symm
  rw [hname] at hq
  change QuasiIso (_ ≫ _) at hq
  have : QuasiIso (AdvCommAlg.Koszul.augmentation (variableList K r)) :=
    quasiIso_of_comp_right _ ((ChainComplex.single₀ _).map
      (quotientCoefficientsLinearEquiv K r).toModuleIso.hom)
  change QuasiIso (extendMap (AdvCommAlg.Koszul.augmentation (variableList K r))
    ComplexShape.embeddingDownNat ≫ (Specs.DerivedFormalization.KoszulCochainResolution.stalkIsoValue _).hom)
  infer_instance

/-- The comparison to the polynomial quotient uses evaluation at the zero section. -/
def polynomialResolution (K : CommAlgCat.{v} k) (e : K ≃ₐ[k] k)
    (r : ℕ) (P : polynomialKoszul K r) : PolynomialResolution K r := by
  let c : quotientRing (R := MvPolynomial (Fin r) K) MvPolynomial.X ≃ₐ[k] K :=
    (quotientCoefficientsEquiv (A := K) (r := r)).restrictScalars k
  let g : ordinary (quotientAlg (polynomial K r) MvPolynomial.X) ⟶ ordinary K :=
    ordinaryMap (CommAlgCat.ofHom c.toAlgHom)
  let G : CommAlgCat.of k (quotientRing (R := MvPolynomial (Fin r) K) MvPolynomial.X) ≅ K :=
    CommAlgCat.isoMk c
  have hg (p : MvPolynomial (Fin r) K) :
      c (Ideal.Quotient.mk _ p) = MvPolynomial.eval (fun _ => 0) p :=
    quotientCoefficientsEquiv_mk p
  have hcomm : P.base ≫ P.augmentation ≫ g = zeroSection K r := by
    rw [← Category.assoc, P.augmentation_base]
    apply ordinaryHom_ext
    intro p
    exact hg p
  have h := augmentation_isResolution P (polynomial_regular K e r)
  let φ := (ordinaryFunctor k).mapIso G
  have hg_iso : IsIso (g.chainMap) :=
    ((NonpositiveCDGA.forgetComplex k).mapIso φ).isIso_hom
  refine ⟨P, c, hg, hcomm, ?_, ?_⟩
  · intro i
    exact ((ModuleCat.epi_iff_surjective _).mp
      (inferInstance : Epi (((NonpositiveCDGA.forgetComplex k).mapIso φ).hom.f i))).comp
      (h.1 i)
  · change QuasiIso (P.augmentation.chainMap ≫ g.chainMap)
    have : QuasiIso P.augmentation.chainMap :=
      augmentation_quasiIso_of_cochain P (polynomialQuotient_quasiIso K e r)
    infer_instance


/-! Identify the homogeneous monomials with the ordered exterior powers. -/

private theorem exteriorExponent_le_one (m : (exteriorVariables.{v} r).Monomial)
    (x : (exteriorVariables.{v} r).Index) : m.val x ≤ 1 :=
  m.prop x (show Odd (-1 : ℤ) by decide)

private theorem exteriorExponent_eq_one (m : (exteriorVariables.{v} r).Monomial)
    {x : (exteriorVariables.{v} r).Index} (hx : x ∈ m.val.support) : m.val x = 1 := by
  have h := exteriorExponent_le_one m x
  have hn := Finsupp.mem_support_iff.mp hx
  omega

private def supportEquiv (r : ℕ) :
    (exteriorVariables.{v} r).Monomial ≃ Finset (exteriorVariables.{v} r).Index where
  toFun m := m.val.support
  invFun s := ⟨Finsupp.indicator s fun _ _ => 1, by
    classical
    intro x _
    simp only [Finsupp.indicator_apply]
    split <;> omega⟩
  left_inv m := by
    classical
    apply Subtype.ext
    ext x
    change (Finsupp.indicator m.val.support fun _ _ => (1 : ℕ)) x = m.val x
    by_cases h : x ∈ m.val.support
    · rw [Finsupp.indicator_of_mem h, exteriorExponent_eq_one m h]
    · rw [Finsupp.indicator_of_notMem h, Finsupp.notMem_support_iff.mp h]
  right_inv s := by
    classical
    ext x
    simp [Finsupp.mem_support_iff, Finsupp.indicator_apply]

private theorem exteriorWeight (m : (exteriorVariables.{v} r).Monomial) :
    (exteriorVariables.{v} r).weight m.val = -(m.val.support.card : ℤ) := by
  classical
  rw [Variables.weight, Finsupp.weight_apply, Finsupp.sum]
  calc
    _ = ∑ _x ∈ m.val.support, (-1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [exteriorExponent_eq_one m hx]
      rfl
    _ = _ := by simp

private theorem ordinaryTerm_isZero (R : CommAlgCat.{v} k) (i : ℤ) (h : i ≠ 0) :
    IsZero ((ordinary R).complex.X i) :=
  isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of k R) i h

private def ordinaryDegreeZero (R : CommAlgCat.{v} k) : (ordinary R).complex.X 0 ≃ₗ[k] R :=
  LinearEquiv.refl k R

/-- Discard the zero summands over the stalk and reindex the rest by their supports. -/
private def exteriorCoefficients (R : CommAlgCat.{v} k) (r n : ℕ) :
    Polynomial (ordinary R) (exteriorVariables r) (-(n : ℤ)) ≃ₗ[k]
      (Set.powersetCard (exteriorVariables.{v} r).Index n → R) := by
  classical
  let V := exteriorVariables.{v} r
  let I := Set.powersetCard V.Index n
  let C := Coefficient (ordinary R) V (-(n : ℤ))
  letI : Fintype V.Monomial := Fintype.ofEquiv (Finset V.Index) (supportEquiv r).symm
  let active : V.Monomial → Prop := fun m => m.val.support.card = n
  let J := {m : V.Monomial // active m}
  let reindex : J ≃ I :=
    { toFun := fun m => ⟨m.val.val.support, m.prop⟩
      invFun := fun s => ⟨(supportEquiv r).symm s.val, by
        change ((supportEquiv r) ((supportEquiv r).symm s.val)).card = n
        rw [Equiv.apply_symm_apply]
        exact s.prop⟩
      left_inv := fun m => Subtype.ext ((supportEquiv r).symm_apply_apply m.val)
      right_inv := fun s => Subtype.ext ((supportEquiv r).apply_symm_apply s.val) }
  have degreeZero (m : V.Monomial) (h : active m) : -(n : ℤ) - V.weight m.val = 0 := by
    change m.val.support.card = n at h
    rw [exteriorWeight, h]
    omega
  have vanish (m : V.Monomial) (h : ¬ active m) : Subsingleton (C m) := by
    apply ModuleCat.subsingleton_of_isZero
    apply ordinaryTerm_isZero
    change m.val.support.card ≠ n at h
    rw [exteriorWeight]
    omega
  let cut : (∀ m, C m) ≃ₗ[k] (∀ m : J, C m.val) :=
    { toFun := fun x m => x m.val
      invFun := fun x m => if h : active m then x ⟨m, h⟩ else 0
      left_inv := by
        intro x
        funext m
        change (if h : active m then x m else 0) = x m
        split
        · rfl
        · exact (vanish m ‹_›).elim _ _
      right_inv := by
        intro x
        funext m
        exact dite_eq_left m.prop
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let trim : (∀ m : J, C m.val) ≃ₗ[k] (J → R) := LinearEquiv.piCongrRight fun m =>
    (eqToIso (congrArg (ordinary R).complex.X (degreeZero m.val m.prop))).toLinearEquiv.trans
      (ordinaryDegreeZero R)
  exact (DirectSum.linearEquivFunOnFintype k _ _).trans
    (cut.trans (trim.trans (LinearEquiv.funCongrLeft k R reindex.symm)))

/-- The exterior basis indexed by the same order that writes the monomials. -/
private def exteriorBasis (R : CommAlgCat.{v} k) (f : Fin r → R) (n : ℕ) :
    Module.Basis (Set.powersetCard (exteriorVariables.{v} r).Index n) R
      (⋀[R]^n (Fin (List.ofFn f).length → R)) :=
  letI := (exteriorVariables.{v} r).normalOrder
  ((Pi.basisFun R (Fin (List.ofFn f).length)).reindex
    (((finCongr List.length_ofFn).trans Equiv.ulift.symm) :
      Fin (List.ofFn f).length ≃ (exteriorVariables.{v} r).Index)).exteriorPower n

/-- Compare the two objects in each nonpositive degree using the common basis of supports. -/
def exteriorTermEquiv (R : CommAlgCat.{v} k) (f : Fin r → R) (n : ℕ) :
    (exteriorAlgebra R f).complex.X (-(n : ℤ)) ≃ₗ[k]
      ⋀[R]^n (Fin (List.ofFn f).length → R) := by
  classical
  exact (exteriorCoefficients R r n).trans ((exteriorBasis R f n).equivFun.symm.restrictScalars k)


private def supportMonomial {n : ℕ} (s : Set.powersetCard (exteriorVariables.{v} r).Index n) :
    (exteriorVariables.{v} r).Monomial :=
  (supportEquiv r).symm s.val

@[simp] private theorem support_supportMonomial {n : ℕ}
    (s : Set.powersetCard (exteriorVariables.{v} r).Index n) :
    (supportMonomial s).val.support = s.val :=
  (supportEquiv r).apply_symm_apply s.val

private theorem weight_supportMonomial {n : ℕ}
    (s : Set.powersetCard (exteriorVariables.{v} r).Index n) :
    (exteriorVariables.{v} r).weight (supportMonomial s).val = -(n : ℤ) := by
  rw [exteriorWeight, support_supportMonomial]
  exact congrArg (fun a : ℕ => -(a : ℤ)) s.prop

private def monomialTerm (R : CommAlgCat.{v} k) {n : ℕ}
    (s : Set.powersetCard (exteriorVariables.{v} r).Index n) :
    R →ₗ[k] Polynomial (ordinary R) (exteriorVariables r) (-(n : ℤ)) :=
  (homogeneousTerm (ordinary R) (exteriorVariables r) (-(n : ℤ)) (supportMonomial s)
    (by rw [zero_add, weight_supportMonomial])).comp (ordinaryDegreeZero R).symm.toLinearMap

private theorem exteriorCoefficients_monomial (R : CommAlgCat.{v} k) {n : ℕ}
    (s t : Set.powersetCard (exteriorVariables.{v} r).Index n) (a : R) :
    exteriorCoefficients R r n (monomialTerm R s a) t = if s = t then a else 0 := by
  classical
  let A := ordinary R
  let V := exteriorVariables.{v} r
  let : DecidableEq V.Index := Classical.decEq _
  let m := supportMonomial s
  let p := supportMonomial t
  let C : V.Monomial → Type v := fun m => A.complex.X (-(n : ℤ) - V.weight m.val)
  let a₀ := (ordinaryDegreeZero R).symm a
  let e : (0 : ℤ) = -(n : ℤ) - V.weight m.val := by rw [weight_supportMonomial]; omega
  let e' : -(n : ℤ) - V.weight p.val = 0 := by rw [weight_supportMonomial]; omega
  change (ordinaryDegreeZero R) (castDegree A.complex.X e'
    ((term A V (-(n : ℤ)) m (castDegree A.complex.X e a₀)) p)) = _
  by_cases h : s = t
  · subst t
    let b : C m := castDegree A.complex.X e a₀
    have hb : (term A V (-(n : ℤ)) m b) m = b := by
      rw [term]
      exact DirectSum.lof_apply k (M := C) m b
    rw [ite_eq_left rfl]
    change (ordinaryDegreeZero R) (castDegree A.complex.X e' ((term A V (-(n : ℤ)) m b) m)) = _
    rw [hb]
    have he : castDegree A.complex.X e' (castDegree A.complex.X e a₀) = a₀ := by
      change castDegree A.complex.X e.symm (castDegree A.complex.X e a₀) = a₀
      let g := eqToIso (congrArg A.complex.X e)
      exact g.toLinearEquiv.symm_apply_apply a₀
    change (ordinaryDegreeZero R) (castDegree A.complex.X e' (castDegree A.complex.X e a₀)) = a
    rw [he]
    exact (ordinaryDegreeZero R).apply_symm_apply a
  · have hmp : m ≠ p := by
      intro hmp
      apply h
      apply Subtype.ext
      rw [← support_supportMonomial s, ← support_supportMonomial t]
      exact congrArg (fun q : V.Monomial => q.val.support) hmp
    let b : C m := castDegree A.complex.X e a₀
    have hb : (term A V (-(n : ℤ)) m b) p = 0 := by
      rw [term, DirectSum.lof_eq_of]
      exact DirectSum.of_eq_of_ne (β := C) m p b (Ne.symm hmp)
    change (ordinaryDegreeZero R) (castDegree A.complex.X e' ((term A V (-(n : ℤ)) m b) p)) = _
    rw [ite_eq_right h, hb]
    rw [map_zero, map_zero]

private theorem exteriorTermEquiv_monomial (R : CommAlgCat.{v} k) (f : Fin r → R) {n : ℕ}
    (s : Set.powersetCard (exteriorVariables.{v} r).Index n) (a : R) :
    exteriorTermEquiv R f n (monomialTerm R s a) = a • exteriorBasis R f n s := by
  classical
  let B := exteriorBasis R f n
  change B.equivFun.symm (exteriorCoefficients R r n (monomialTerm R s a)) = a • B s
  apply B.equivFun.injective
  rw [LinearEquiv.apply_symm_apply, map_smul]
  funext t
  rw [exteriorCoefficients_monomial]
  change _ = a * B.equivFun (B s) t
  rw [Module.Basis.equivFun_self]
  split <;> simp_all

private abbrev restrictedModule (R : CommAlgCat.{v} k) (M : Type v)
    [AddCommGroup M] [Module R M] : ModuleCat.{v} k :=
  (ModuleCat.restrictScalars (algebraMap k R)).obj (ModuleCat.of R M)

open Set.powersetCard in
/-- Sorting two increasing disjoint blocks contributes exactly their cross inversions. -/
private theorem shuffleSign {I : Type v} [LinearOrder I] {m n : ℕ}
    {s : Set.powersetCard I m} {t : Set.powersetCard I n} (h : Disjoint s.val t.val) :
    (permOfDisjoint h).sign =
      ∏ x ∈ s.val, ∏ y ∈ t.val, if y < x then (-1 : ℤˣ) else 1 := by
  classical
  let σ := permOfDisjoint h
  let u := orderIsoOfFin (disjUnion h)
  let a (i : Fin m) : I := orderIsoOfFin s i
  let b (i : Fin n) : I := orderIsoOfFin t i
  have hleft (i : Fin m) : (u (σ (Fin.castAdd n i))).val = a i := by
    simp only [σ, permOfDisjoint, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd]
    let x : ↥(disjUnion h).val :=
      Equiv.Finset.disjUnionEquiv s.val t.val h (Sum.inl (orderIsoOfFin s i))
    change (u (u.symm x)).val = a i
    exact congrArg Subtype.val (u.apply_symm_apply x)
  have hright (j : Fin n) : (u (σ (Fin.natAdd m j))).val = b j := by
    simp only [σ, permOfDisjoint, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd]
    let y : ↥(disjUnion h).val :=
      Equiv.Finset.disjUnionEquiv s.val t.val h (Sum.inr (orderIsoOfFin t j))
    change (u (u.symm y)).val = b j
    exact congrArg Subtype.val (u.apply_symm_apply y)
  let F (i j : Fin (m+n)) : ℤˣ := if i < j ∧ σ j < σ i then -1 else 1
  have hsign : σ.sign = ∏ i, ∏ j, F i j := by
    rw [Equiv.Perm.sign_eq_prod_prod_Ioi]
    apply Finset.prod_congr rfl
    intro i _
    have he : ∏ j ∈ Finset.Ioi i, (if σ i < σ j then (1 : ℤˣ) else -1) =
        ∏ j, if i < j then (if σ i < σ j then (1 : ℤˣ) else -1) else 1 := by
      rw [← Finset.prod_filter]
      congr 1
      ext j
      simp
    rw [he]
    apply Finset.prod_congr rfl
    intro j _
    dsimp only [F]
    by_cases hij : i < j
    · have hne := σ.injective.ne (ne_of_lt hij)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · simp [hij, hlt, asymm hlt]
      · simp [hij, hgt, asymm hgt]
    · simp [hij]
  have ha : StrictMono a := fun _ _ hij => (orderIsoOfFin s).strictMono hij
  have hb : StrictMono b := fun _ _ hij => (orderIsoOfFin t).strictMono hij
  have hLL (i j : Fin m) : F (Fin.castAdd n i) (Fin.castAdd n j) = 1 := by
    dsimp only [F]
    by_cases hij : i < j
    · have hh : σ (Fin.castAdd n i) < σ (Fin.castAdd n j) := by
        rw [← u.lt_iff_lt]
        change (u (σ (Fin.castAdd n i))).val < (u (σ (Fin.castAdd n j))).val
        rw [hleft, hleft]
        exact ha hij
      simp [asymm hh]
    · have : ¬ Fin.castAdd n i < Fin.castAdd n j := hij
      simp [this]
  have hRR (i j : Fin n) : F (Fin.natAdd m i) (Fin.natAdd m j) = 1 := by
    dsimp only [F]
    by_cases hij : i < j
    · have hh : σ (Fin.natAdd m i) < σ (Fin.natAdd m j) := by
        rw [← u.lt_iff_lt]
        change (u (σ (Fin.natAdd m i))).val < (u (σ (Fin.natAdd m j))).val
        rw [hright, hright]
        exact hb hij
      simp [asymm hh]
    · have hh : ¬ Fin.natAdd m i < Fin.natAdd m j := by simpa using hij
      simp [hh]
  have hRL (i : Fin n) (j : Fin m) : F (Fin.natAdd m i) (Fin.castAdd n j) = 1 := by
    have hh : ¬ Fin.natAdd m i < Fin.castAdd n j := by
      change ¬ m + i.val < j.val
      omega
    simp [F, hh]
  have hLR (i : Fin m) (j : Fin n) :
      F (Fin.castAdd n i) (Fin.natAdd m j) = if b j < a i then -1 else 1 := by
    have hlt : Fin.castAdd n i < Fin.natAdd m j := by
      change i.val < m + j.val
      omega
    have hh : σ (Fin.natAdd m j) < σ (Fin.castAdd n i) ↔ b j < a i := by
      rw [← u.lt_iff_lt]
      change (u (σ (Fin.natAdd m j))).val < (u (σ (Fin.castAdd n i))).val ↔ _
      rw [hleft, hright]
    simp [F, hlt, hh]
  change σ.sign = _
  rw [hsign, Fin.prod_univ_add]
  simp_rw [Fin.prod_univ_add]
  simp only [hLL, hRR, hRL, hLR, Finset.prod_const_one, one_mul, mul_one]
  rw [← Finset.prod_coe_sort s.val (fun x => ∏ y ∈ t.val, if y < x then (-1 : ℤˣ) else 1)]
  refine Fintype.prod_equiv (orderIsoOfFin s).toEquiv _ _ fun i => ?_
  change (∏ j, if b j < a i then (-1 : ℤˣ) else 1) =
    ∏ y ∈ t.val, if y < a i then -1 else 1
  rw [← Finset.prod_coe_sort t.val (fun y => if y < a i then (-1 : ℤˣ) else 1)]
  exact Fintype.prod_equiv (orderIsoOfFin t).toEquiv _ _ (fun j => rfl)


open Set.powersetCard in
private theorem inversionSign {m n : ℕ}
    (s : Set.powersetCard (exteriorVariables.{v} r).Index m)
    (t : Set.powersetCard (exteriorVariables.{v} r).Index n) (h : Disjoint s.val t.val) :
    letI := (exteriorVariables.{v} r).normalOrder
    ((exteriorVariables.{v} r).inversions (supportMonomial s).val (supportMonomial t).val).negOnePow =
      (permOfDisjoint h).sign := by
  classical
  let V := exteriorVariables.{v} r
  let a := supportMonomial s
  let b := supportMonomial t
  let ltV : V.Index → V.Index → Prop := @LT.lt V.Index V.normalOrder.toLT
  let : DecidableRel ltV := fun x y => Classical.propDecidable (ltV x y)
  have hsum : V.inversions a.val b.val = ∑ x ∈ s.val, ∑ y ∈ t.val, if ltV y x then (1 : ℤ) else 0 := by
    unfold Variables.inversions Finsupp.sum
    rw [← support_supportMonomial s, ← support_supportMonomial t]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    rw [exteriorExponent_eq_one a hx, exteriorExponent_eq_one b hy]
    have hx' : V.degree x = -1 := rfl
    have hy' : V.degree y = -1 := rfl
    simp only [hx', hy', Nat.cast_one, mul_neg, neg_neg, mul_one]
    rfl
  change (V.inversions a.val b.val).negOnePow = (@permOfDisjoint V.Index V.normalOrder m n s t h).sign
  rw [hsum, @shuffleSign V.Index V.normalOrder m n s t h]
  let F : ℤ →+ Additive ℤˣ :=
    { toFun := fun i => Additive.ofMul i.negOnePow
      map_zero' := rfl
      map_add' := Int.negOnePow_add }
  apply Additive.toMul.injective
  change F _ = Additive.ofMul _
  simp only [map_sum, ofMul_prod]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  by_cases hxy : ltV y x
  · have hxy' : @LT.lt V.Index V.normalOrder.toLT y x := hxy
    simp only [ite_eq_left hxy, ite_eq_left hxy']
    rfl
  · have hxy' : ¬ @LT.lt V.Index V.normalOrder.toLT y x := hxy
    simp only [ite_eq_right hxy, ite_eq_right hxy']
    rfl

private theorem admissible_add_iff {m n : ℕ}
    (s : Set.powersetCard (exteriorVariables.{v} r).Index m)
    (t : Set.powersetCard (exteriorVariables.{v} r).Index n) :
    (exteriorVariables.{v} r).Admissible ((supportMonomial s).val + (supportMonomial t).val) ↔
      Disjoint s.val t.val := by
  classical
  let a := (supportMonomial s).val
  let b := (supportMonomial t).val
  rw [← support_supportMonomial s, ← support_supportMonomial t, Finset.disjoint_left]
  constructor
  · intro h x hx hy
    have hle := h x (show Odd (-1 : ℤ) by decide)
    change (a + b) x ≤ 1 at hle
    rw [Finsupp.add_apply, exteriorExponent_eq_one (supportMonomial s) hx,
      exteriorExponent_eq_one (supportMonomial t) hy] at hle
    omega
  · intro h x _
    change (a + b) x ≤ 1
    rw [Finsupp.add_apply]
    by_cases hx : x ∈ a.support
    · rw [Finsupp.notMem_support_iff.mp (h hx), add_zero]
      exact exteriorExponent_le_one (supportMonomial s) x
    · rw [Finsupp.notMem_support_iff.mp hx, zero_add]
      exact exteriorExponent_le_one (supportMonomial t) x

open Set.powersetCard in
private theorem supportMonomial_disjUnion {m n : ℕ}
    (s : Set.powersetCard (exteriorVariables.{v} r).Index m)
    (t : Set.powersetCard (exteriorVariables.{v} r).Index n) (h : Disjoint s.val t.val) :
    supportMonomial (disjUnion h) =
      ⟨(supportMonomial s).val + (supportMonomial t).val, (admissible_add_iff s t).2 h⟩ := by
  classical
  apply (supportEquiv r).injective
  change (supportMonomial (disjUnion h)).val.support = (_ + _ : (exteriorVariables.{v} r).Exponent).support
  rw [support_supportMonomial, Finsupp.support_add_eq_union, support_supportMonomial,
    support_supportMonomial, coe_disjUnion, Finset.disjUnion_eq_union]

open private homogeneousTerm_congr from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.SemifreeAlgebras

open Set.powersetCard in
private theorem monomialTerm_mul (R : CommAlgCat.{v} k) {m n : ℕ}
    (s : Set.powersetCard (exteriorVariables.{v} r).Index m)
    (t : Set.powersetCard (exteriorVariables.{v} r).Index n) (a b : R) :
    letI := (exteriorVariables.{v} r).normalOrder
    polynomialMul (ordinary R) (exteriorVariables r) (-(m : ℤ)) (-(n : ℤ)) (-((m+n : ℕ) : ℤ))
      (by omega) (monomialTerm R s a) (monomialTerm R t b) =
      if h : Disjoint s.val t.val then (permOfDisjoint h).sign •
        monomialTerm R (disjUnion h) (a * b) else 0 := by
  classical
  let A := ordinary R
  let V := exteriorVariables.{v} r
  let := V.normalOrder
  let e := supportMonomial s
  let l := supportMonomial t
  let a₀ := (ordinaryDegreeZero R).symm a
  let b₀ := (ordinaryDegreeZero R).symm b
  let h₁ : 0 + V.weight e.val = -(m : ℤ) := by rw [zero_add, weight_supportMonomial]
  let h₂ : 0 + V.weight l.val = -(n : ℤ) := by rw [zero_add, weight_supportMonomial]
  change polynomialMul A V _ _ _ _ (homogeneousTerm A V _ e h₁ a₀)
    (homogeneousTerm A V _ l h₂ b₀) = _
  rw [polynomialMul_homogeneousTerm A V]
  by_cases hd : Disjoint s.val t.val
  · rw [dite_eq_left hd, dite_eq_left ((admissible_add_iff s t).2 hd), mul_zero, zero_add,
      inversionSign s t hd]
    have hm : A.mul 0 0 (0+0) rfl a₀ b₀ = (ordinaryDegreeZero R).symm (a * b) := rfl
    rw [hm]
    dsimp only [monomialTerm, LinearMap.comp_apply, LinearEquiv.coe_coe]
    congr 1
    exact homogeneousTerm_congr A V (supportMonomial_disjUnion s t hd).symm _ _ _
  · rw [dite_eq_right hd, dite_eq_right (fun h => hd ((admissible_add_iff s t).1 h))]


private theorem monomial_expansion (R : CommAlgCat.{v} k) {n : ℕ}
    (p : Polynomial (ordinary R) (exteriorVariables r) (-(n : ℤ))) :
    p = ∑ s, monomialTerm R s (exteriorCoefficients R r n p s) := by
  classical
  apply (exteriorCoefficients R r n).injective
  rw [map_sum]
  funext t
  change exteriorCoefficients R r n p t = (∑ s, exteriorCoefficients R r n
    (monomialTerm R s (exteriorCoefficients R r n p s))) t
  rw [Finset.sum_apply]
  symm
  rw [Finset.sum_eq_single t]
  · exact (exteriorCoefficients_monomial R t t _).trans (ite_eq_left rfl)
  · intro s _ hst
    exact (exteriorCoefficients_monomial R s t _).trans (ite_eq_right hst)
  · simp

private abbrev exteriorRing (R : CommAlgCat.{v} k) (f : Fin r → R) :=
  ExteriorAlgebra R (Fin (List.ofFn f).length → R)

private def exteriorImage (R : CommAlgCat.{v} k) (f : Fin r → R) (n : ℕ) :
    Polynomial (ordinary R) (exteriorVariables r) (-(n : ℤ)) →ₗ[k] exteriorRing R f :=
  ((⋀[R]^n (Fin (List.ofFn f).length → R)).subtype.restrictScalars k).comp
    (exteriorTermEquiv R f n).toLinearMap

open Set.powersetCard in
private theorem exteriorImage_mul_monomial (R : CommAlgCat.{v} k) (f : Fin r → R) {m n : ℕ}
    (s : Set.powersetCard (exteriorVariables.{v} r).Index m)
    (t : Set.powersetCard (exteriorVariables.{v} r).Index n) (a b : R) :
    exteriorImage R f (m+n) (polynomialMul (ordinary R) (exteriorVariables r)
      (-(m : ℤ)) (-(n : ℤ)) (-((m+n : ℕ) : ℤ)) (by omega)
      (monomialTerm R s a) (monomialTerm R t b)) =
      exteriorImage R f m (monomialTerm R s a) * exteriorImage R f n (monomialTerm R t b) := by
  classical
  let V := exteriorVariables.{v} r
  let := V.normalOrder
  let c := (Pi.basisFun R (Fin (List.ofFn f).length)).reindex
    (((finCongr List.length_ofFn).trans Equiv.ulift.symm) : _ ≃ V.Index)
  have hB {n : ℕ} (s : Set.powersetCard V.Index n) (x : R) :
      exteriorImage R f n (monomialTerm R s x) = x • ExteriorAlgebra.ιMulti_family R n c s := by
    change (exteriorTermEquiv R f n (monomialTerm R s x) : exteriorRing R f) = _
    rw [exteriorTermEquiv_monomial]
    change x • ((c.exteriorPower n s : ⋀[R]^n _) : exteriorRing R f) = _
    rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family_apply_coe]
  rw [monomialTerm_mul, hB, hB, smul_mul_smul_comm]
  by_cases h : Disjoint s.val t.val
  · rw [dite_eq_left h, LinearMap.map_smul_of_tower, hB,
      ExteriorAlgebra.ιMulti_family_mul_of_disjoint R c s t h]
    exact smul_comm _ _ _
  · rw [dite_eq_right h, map_zero, ExteriorAlgebra.ιMulti_family_mul_of_not_disjoint R c s t h,
      smul_zero]

private theorem exteriorImage_mul (R : CommAlgCat.{v} k) (f : Fin r → R) {m n : ℕ}
    (x : (exteriorAlgebra R f).complex.X (-(m : ℤ))) (y : (exteriorAlgebra R f).complex.X (-(n : ℤ))) :
    exteriorImage R f (m+n) ((exteriorAlgebra R f).mul (-(m : ℤ)) (-(n : ℤ))
      (-((m+n : ℕ) : ℤ)) (by omega) x y) = exteriorImage R f m x * exteriorImage R f n y := by
  classical
  let A := ordinary R
  let V := exteriorVariables.{v} r
  let M := polynomialMul A V (-(m : ℤ)) (-(n : ℤ)) (-((m+n : ℕ) : ℤ)) (by omega)
  let x' : Polynomial A V (-(m : ℤ)) := x
  let y' : Polynomial A V (-(n : ℤ)) := y
  change exteriorImage R f (m+n) (M x' y') = exteriorImage R f m x' * exteriorImage R f n y'
  rw [monomial_expansion R x', monomial_expansion R y']
  simp only [map_sum, LinearMap.sum_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun s _ => exteriorImage_mul_monomial R f s t _ _


private def coordinateVector (R : CommAlgCat.{v} k) (f : Fin r → R)
    (i : Fin r) : Fin (List.ofFn f).length → R :=
  Pi.basisFun R _ (Fin.cast List.length_ofFn.symm i)

private theorem exteriorImage_coefficient (R : CommAlgCat.{v} k) (f : Fin r → R) (a : R) :
    exteriorImage R f 0 (coefficient (ordinary R) (exteriorVariables r) 0 a) =
      algebraMap R (exteriorRing R f) a := by
  classical
  let V := exteriorVariables.{v} r
  let s : Set.powersetCard V.Index 0 := Set.powersetCard.ofCard Finset.card_empty
  have hm : supportMonomial s = V.constant := by
    apply (supportEquiv r).injective
    change (supportMonomial s).val.support = (0 : V.Exponent).support
    rw [support_supportMonomial, Finsupp.support_zero]
    rfl
  let a₀ : (ordinary R).complex.X 0 := a
  have ht : monomialTerm R s a = coefficient (ordinary R) V 0 a₀ :=
    homogeneousTerm_congr (ordinary R) V hm
      (by rw [zero_add, weight_supportMonomial]) (by rw [← hm, zero_add, weight_supportMonomial]) a₀
  rw [← ht]
  change (exteriorTermEquiv R f 0 (monomialTerm R s a) : exteriorRing R f) = _
  rw [exteriorTermEquiv_monomial]
  let := V.normalOrder
  change a • ((exteriorBasis R f 0 s : ⋀[R]^0 _) : exteriorRing R f) = _
  rw [exteriorBasis, exteriorPower.basis_apply, exteriorPower.ιMulti_family_apply_coe,
    ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_zero_apply, Algebra.algebraMap_eq_smul_one]

private theorem exteriorImage_generator (R : CommAlgCat.{v} k) (f : Fin r → R) (i : Fin r) :
    exteriorImage R f 1 (variableTerm (ordinary R) (exteriorVariables r) (ULift.up i)) =
      ExteriorAlgebra.ι R (coordinateVector R f i) := by
  classical
  let V := exteriorVariables.{v} r
  let x : V.Index := ULift.up i
  let s : Set.powersetCard V.Index 1 := Set.powersetCard.ofCard (Finset.card_singleton x)
  have hm : supportMonomial s = V.singleton x := by
    apply (supportEquiv r).injective
    change (supportMonomial s).val.support = (Finsupp.single x 1).support
    rw [support_supportMonomial, Finsupp.support_single _ (by decide : (1 : ℕ) ≠ 0)]
    rfl
  have ht : monomialTerm R s 1 = variableTerm (ordinary R) V x :=
    homogeneousTerm_congr (ordinary R) V hm
      (by rw [zero_add, weight_supportMonomial]) (by rw [← hm, zero_add, weight_supportMonomial])
      (ordinary R).one
  rw [← ht]
  change (exteriorTermEquiv R f 1 (monomialTerm R s 1) : exteriorRing R f) = _
  rw [exteriorTermEquiv_monomial, one_smul]
  let := V.normalOrder
  rw [exteriorBasis, exteriorPower.basis_apply, exteriorPower.ιMulti_family_apply_coe,
    ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  congr 1
  let e := Set.powersetCard.ofFinEmbEquiv.symm s
  have he : e 0 = x := by
    have ha : e 0 ∈ s := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s (e 0)).mp ⟨0, rfl⟩
    exact Finset.mem_singleton.mp ha
  change ((Pi.basisFun R (Fin (List.ofFn f).length)).reindex
    (((finCongr List.length_ofFn).trans Equiv.ulift.symm) : _ ≃ V.Index)) (e 0) = _
  rw [he, Module.Basis.reindex_apply]
  rfl

private def exteriorImageZ (R : CommAlgCat.{v} k) (f : Fin r → R) :
    (i : ℤ) → Polynomial (ordinary R) (exteriorVariables r) i →ₗ[k] exteriorRing R f
  | .ofNat 0 => exteriorImage R f 0
  | .ofNat (_ + 1) => 0
  | .negSucc n => exteriorImage R f (n + 1)

@[simp] private theorem exteriorImageZ_neg (R : CommAlgCat.{v} k) (f : Fin r → R) (n : ℕ) :
    exteriorImageZ R f (-(n : ℤ)) = exteriorImage R f n := by
  cases n <;> rfl

private theorem exists_eq_neg_of_nonpos {i : ℤ} (h : i ≤ 0) : ∃ n : ℕ, -(n : ℤ) = i :=
  ⟨(-i).toNat, by rw [Int.toNat_of_nonneg (by omega : 0 ≤ -i), neg_neg]⟩

private theorem exteriorImageZ_mul (R : CommAlgCat.{v} k) (f : Fin r → R)
    (i j n : ℤ) (h : i + j = n)
    (x : Polynomial (ordinary R) (exteriorVariables r) i)
    (y : Polynomial (ordinary R) (exteriorVariables r) j) :
    exteriorImageZ R f n (polynomialMul (ordinary R) (exteriorVariables r) i j n h x y) =
      exteriorImageZ R f i x * exteriorImageZ R f j y := by
  by_cases hi : 0 < i
  · rw [(polynomial_nonpositive (ordinary R) (exteriorVariables r) i hi).elim x 0]
    simp
  by_cases hj : 0 < j
  · rw [(polynomial_nonpositive (ordinary R) (exteriorVariables r) j hj).elim y 0]
    simp
  obtain ⟨p, rfl⟩ := exists_eq_neg_of_nonpos (le_of_not_gt hi)
  obtain ⟨q, rfl⟩ := exists_eq_neg_of_nonpos (le_of_not_gt hj)
  have hn : -((p + q : ℕ) : ℤ) = n := by omega
  subst hn
  rw [exteriorImageZ_neg, exteriorImageZ_neg, exteriorImageZ_neg]
  exact exteriorImage_mul R f x y

private theorem exteriorImage_orderedProduct (R : CommAlgCat.{v} k) (f : Fin r → R)
    (n : ℕ) (s : Fin n → Fin r) :
    exteriorImage R f n
      (orderedProduct (exteriorAlgebra R f)
        (fun i => gen (exteriorPresentation R f) i) n s) =
      (coordinateWedge f n s : exteriorRing R f) := by
  induction n with
  | zero =>
    change exteriorImage R f 0 (coefficient (ordinary R) (exteriorVariables r) 0 (1 : R)) = _
    rw [exteriorImage_coefficient, map_one, coordinateWedge, exteriorPower.ιMulti_apply_coe,
      ExteriorAlgebra.ιMulti_zero_apply]
  | succ n ih =>
    let x := variableTerm (ordinary R) (exteriorVariables r) (ULift.up (s 0))
    let y : Polynomial (ordinary R) (exteriorVariables r) (-(n : ℤ)) :=
      orderedProduct (exteriorAlgebra R f) (fun i => gen (exteriorPresentation R f) i) n (Fin.tail s)
    have hy : exteriorImage R f n y = (coordinateWedge f n (Fin.tail s) : exteriorRing R f) :=
      ih (Fin.tail s)
    change exteriorImageZ R f (-((n+1 : ℕ) : ℤ)) (polynomialMul (ordinary R) (exteriorVariables r)
      (-1) (-(n : ℤ)) (-((n+1 : ℕ) : ℤ)) (by omega) x y) = _
    rw [exteriorImageZ_mul]
    change exteriorImage R f 1 x * exteriorImageZ R f (-(n : ℤ)) y = _
    rw [exteriorImageZ_neg, exteriorImage_generator, hy]
    change _ = ExteriorAlgebra.ιMulti R (n+1) (fun j => coordinateVector R f (s j))
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    rfl

open _root_.AdvCommAlg.Koszul (contraction contraction_leibniz contraction_scalar
  contraction_generator listForm_basis)

private theorem contraction_exteriorImage_mul (R : CommAlgCat.{v} k) (f : Fin r → R)
    (i : ℤ) (x : Polynomial (ordinary R) (exteriorVariables r) i) (y : exteriorRing R f) :
    contraction (listForm (List.ofFn f)) (exteriorImageZ R f i x * y) =
      contraction (listForm (List.ofFn f)) (exteriorImageZ R f i x) * y +
        i.negOnePow • (exteriorImageZ R f i x * contraction (listForm (List.ofFn f)) y) := by
  by_cases hi : 0 < i
  · rw [(polynomial_nonpositive (ordinary R) (exteriorVariables r) i hi).elim x 0]
    simp
  obtain ⟨n, rfl⟩ := exists_eq_neg_of_nonpos (le_of_not_gt hi)
  rw [exteriorImageZ_neg]
  have hx : exteriorImage R f n x ∈ ⋀[R]^n (Fin (List.ofFn f).length → R) :=
    (exteriorTermEquiv R f n x).property
  rw [contraction_leibniz (listForm (List.ofFn f)) n _ _ hx]
  congr 1
  rw [Int.negOnePow_neg, Units.smul_def, ← Int.cast_smul_eq_zsmul R,
    Int.cast_negOnePow_natCast]

private theorem exteriorImage_derivation (R : CommAlgCat.{v} k) (f : Fin r → R)
    (i : ℤ) (x : Polynomial (ordinary R) (exteriorVariables r) i) :
    exteriorImageZ R f (i+1) ((extendDerivation (equationValues R f)).d i x) =
      contraction (listForm (List.ofFn f)) (exteriorImageZ R f i x) := by
  let A := ordinary R
  let V := exteriorVariables.{v} r
  let D := extendDerivation (equationValues R f)
  let E := exteriorImageZ R f
  let δ := contraction (listForm (List.ofFn f))
  change E (i+1) (D.d i x) = δ (E i x)
  apply polynomial_generated A V (fun i x => E (i+1) (D.d i x) = δ (E i x))
  · intro j
    simp
  · intro j x y hx hy
    simp only [map_add, hx, hy]
  · intro j s x hx
    simp only [LinearMap.map_smul_of_tower, hx]
  · intro j a
    by_cases hj : j = 0
    · subst j
      have hda : A.complex.d 0 (0+1) a = 0 := A.d_zero_apply a
      rw [D.on_base, hda, map_zero, map_zero]
      change 0 = δ (exteriorImage R f 0 (coefficient A V 0 a))
      let ar : R := a
      have he : exteriorImage R f 0 (coefficient A V 0 a) = algebraMap R (exteriorRing R f) ar :=
        exteriorImage_coefficient R f ar
      rw [he]
      exact (contraction_scalar _ _).symm
    · rw [(ModuleCat.subsingleton_of_isZero (ordinaryTerm_isZero R j hj)).elim a 0]
      simp
  · intro x
    let i : Fin r := x.down
    have h := D.on_var x
    change E (V.degree x + 1) (D.d (V.degree x) (variableTerm A V x)) =
      δ (E (V.degree x) (variableTerm A V x))
    rw [h]
    change exteriorImage R f 0 (coefficient A V 0 (f i)) =
      δ (exteriorImage R f 1 (variableTerm A V (ULift.up i)))
    rw [exteriorImage_coefficient, exteriorImage_generator, contraction_generator]
    have hi : listForm (List.ofFn f) (coordinateVector R f i) = f i := by
      unfold coordinateVector
      rw [listForm_basis]
      simp
    rw [hi]
  · intro a b c h x y hx hy
    dsimp only [E] at hx hy ⊢
    rw [D.leibniz, map_add, LinearMap.map_smul_of_tower, exteriorImageZ_mul,
      exteriorImageZ_mul, exteriorImageZ_mul, hx, hy]
    exact (contraction_exteriorImage_mul R f a x (exteriorImageZ R f b y)).symm


private def nativeToRestricted (R : CommAlgCat.{v} k) (M : Type v)
    [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] :
    ModuleCat.of k M ≅ restrictedModule R M :=
  ({ toFun := id
     invFun := id
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl
     map_add' := fun _ _ => rfl
     map_smul' := fun a x => by
       change a • x = algebraMap k R a • x
       exact (IsScalarTower.algebraMap_smul R a x).symm } : M ≃ₗ[k] restrictedModule R M).toModuleIso

private abbrev restrictedKoszul (R : CommAlgCat.{v} k) (f : Fin r → R) :=
  (restrictCochains R).obj (cochainValue (List.ofFn f))

private def cochainComponentNeg (R : CommAlgCat.{v} k) (f : Fin r → R) (n : ℕ) :
    (exteriorAlgebra R f).complex.X (-(n : ℤ)) ≅ (restrictedKoszul R f).X (-(n : ℤ)) :=
  (exteriorTermEquiv R f n).toModuleIso ≪≫ nativeToRestricted R _ ≪≫
    (ModuleCat.restrictScalars (algebraMap k R)).mapIso (termIsoValue (List.ofFn f) n).symm

open private koszulCochain_isZero_pos koszulCochain_d_apply from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.KoszulCochainResolution

omit [CharZero k] in
private theorem restrictedKoszul_isZero_pos (R : CommAlgCat.{v} k) (f : Fin r → R)
    (i : ℤ) (hi : 0 < i) : IsZero ((restrictedKoszul R f).X i) :=
  (ModuleCat.restrictScalars (algebraMap k R)).map_isZero (koszulCochain_isZero_pos (List.ofFn f) i hi)

private def cochainComponent (R : CommAlgCat.{v} k) (f : Fin r → R) :
    ∀ i : ℤ, (exteriorAlgebra R f).complex.X i ≅ (restrictedKoszul R f).X i
  | .ofNat 0 => cochainComponentNeg R f 0
  | .ofNat (n+1) => IsZero.iso
      (ModuleCat.isZero_iff_subsingleton.mpr ((exteriorAlgebra R f).nonpositive _ (by change (0 : ℤ) < ((n+1 : ℕ) : ℤ); omega)))
      (restrictedKoszul_isZero_pos R f _ (by change (0 : ℤ) < ((n+1 : ℕ) : ℤ); omega))
  | .negSucc n => cochainComponentNeg R f (n+1)

@[simp] private theorem cochainComponent_neg_apply (R : CommAlgCat.{v} k) (f : Fin r → R)
    (n : ℕ) (x : (exteriorAlgebra R f).complex.X (-(n : ℤ))) :
    (cochainComponent R f (-(n : ℤ))).hom x =
      (termIsoValue (List.ofFn f) n).inv (exteriorTermEquiv R f n x) := by
  cases n <;> rfl

private theorem exterior_d_of_succ (R : CommAlgCat.{v} k) (f : Fin r → R)
    (p q : ℤ) (hpq : p+1 = q) :
    (exteriorAlgebra R f).complex.d p q =
      ModuleCat.ofHom (Y := (exteriorAlgebra R f).complex.X q)
        (castDegree (exteriorAlgebra R f).complex.X hpq ∘ₗ (extendDerivation (equationValues R f)).d p) := by
  subst q
  let D := extendDerivation (equationValues R f)
  let hc : ∀ x, D.d ((exteriorVariables.{v} r).degree x + 1) (equationValues R f x) = 0 :=
    fun x => equationCycles R f x _ D fun _ _ => rfl
  change (polynomialComplex D hc).d p (p+1) = _
  rw [polynomialComplex_d]
  rfl

private theorem cochainComponent_comm (R : CommAlgCat.{v} k) (f : Fin r → R)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    (cochainComponent R f i).hom ≫ (restrictedKoszul R f).d i j =
      (exteriorAlgebra R f).complex.d i j ≫ (cochainComponent R f j).hom := by
  change i + 1 = j at hij
  subst j
  by_cases hi : 0 ≤ i
  · exact (restrictedKoszul_isZero_pos R f (i+1) (by omega)).eq_of_tgt _ _
  obtain ⟨p, rfl⟩ := exists_eq_neg_of_nonpos (by omega : i ≤ 0)
  cases p with
  | zero => exact (hi (by decide)).elim
  | succ n =>
    let p : ℤ := -((n + 1 : ℕ) : ℤ)
    let q : ℤ := -(n : ℤ)
    have hpq : p + 1 = q := by dsimp [p, q]; omega
    have hδ := exterior_d_of_succ R f p q hpq
    change (cochainComponent R f p).hom ≫ (restrictedKoszul R f).d p (p+1) =
      (exteriorAlgebra R f).complex.d p (p+1) ≫ (cochainComponent R f (p+1)).hom
    rw [hpq, hδ]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let form := listForm (List.ofFn f)
    let v := exteriorTermEquiv R f (n+1) x
    let w := (castDegree (exteriorAlgebra R f).complex.X hpq)
      ((extendDerivation (equationValues R f)).d p x)
    let v' := exteriorTermEquiv R f n w
    let G : (restrictedKoszul R f).X q → ⋀[R]^n (Fin (List.ofFn f).length → R) :=
      fun y => (termIsoValue (List.ofFn f) n).hom y
    have hG : Function.Injective G := (termIsoValue (List.ofFn f) n).toLinearEquiv.injective
    apply hG
    have hc := cochainComponent_neg_apply R f (n+1) x
    have hc' := cochainComponent_neg_apply R f n w
    have h₁ : (cochainComponent R f p).hom x =
        (termIsoValue (List.ofFn f) (n+1)).inv v := hc
    have h₂ : (cochainComponent R f q).hom w =
        (termIsoValue (List.ofFn f) n).inv v' := hc'
    change G ((restrictedKoszul R f).d p q ((cochainComponent R f p).hom x)) =
      G ((cochainComponent R f q).hom w)
    rw [h₁, h₂]
    have hd : G ((restrictedKoszul R f).d p q ((termIsoValue (List.ofFn f) (n+1)).inv v)) =
        AdvCommAlg.Koszul.differential form n v := koszulCochain_d_apply (List.ofFn f) n v
    rw [hd, show G ((termIsoValue (List.ofFn f) n).inv v') = v' from
      ModuleCat.hom_inv_apply (termIsoValue (List.ofFn f) n) v']
    apply Subtype.ext
    change contraction form (exteriorImage R f (n+1) x) = exteriorImage R f n w
    have he := exteriorImage_derivation R f p x
    have transport (l j : ℤ) (h : l = j) (x : (exteriorAlgebra R f).complex.X l) :
        exteriorImageZ R f j (castDegree (exteriorAlgebra R f).complex.X h x) =
          exteriorImageZ R f l x := by
      subst j
      rfl
    rw [← exteriorImageZ_neg R f (n+1), ← exteriorImageZ_neg R f n]
    change contraction form (exteriorImageZ R f p x) = exteriorImageZ R f q w
    exact he.symm.trans (transport (p+1) q hpq ((extendDerivation (equationValues R f)).d p x)).symm

/-- The cochain comparison obtained from the signed exterior basis. -/
def exteriorCochainIso (R : CommAlgCat.{v} k) (f : Fin r → R) :
    (exteriorAlgebra R f).complex ≅ restrictedKoszul R f :=
  HomologicalComplex.Hom.isoOfComponents (cochainComponent R f) (cochainComponent_comm R f)


private theorem exteriorCochainIso_apply (R : CommAlgCat.{v} k) (f : Fin r → R)
    (n : ℕ) (x : (exteriorAlgebra R f).complex.X (-(n : ℤ))) :
    (termIsoValue (List.ofFn f) n).hom ((exteriorCochainIso R f).hom.f (-(n : ℤ)) x) =
      exteriorTermEquiv R f n x :=
  (congrArg (fun y : (restrictedKoszul R f).X (-(n : ℤ)) => (termIsoValue (List.ofFn f) n).hom y)
    (cochainComponent_neg_apply R f n x)).trans
    (ModuleCat.hom_inv_apply (termIsoValue (List.ofFn f) n) (exteriorTermEquiv R f n x))

private theorem exteriorCochain_scalar (R : CommAlgCat.{v} k) (f : Fin r → R)
    (i : ℤ) (a : R) (x : (exteriorAlgebra R f).complex.X i) :
    (show (cochainValue (List.ofFn f)).X i from
      (exteriorCochainIso R f).hom.f i ((exteriorAlgebra R f).mul 0 i i (zero_add i)
        ((exteriorBase R f).chainMap.f 0 a) x)) =
      a • (show (cochainValue (List.ofFn f)).X i from (exteriorCochainIso R f).hom.f i x) := by
  by_cases hi : 0 < i
  · exact (ModuleCat.isZero_iff_subsingleton.mp (koszulCochain_isZero_pos (List.ofFn f) i hi)).elim _ _
  obtain ⟨n, rfl⟩ := exists_eq_neg_of_nonpos (le_of_not_gt hi)
  let F := exteriorCochainIso R f
  let E := termIsoValue (List.ofFn f) n
  let P := exteriorAlgebra R f
  let b := (exteriorBase R f).chainMap.f 0 a
  let y := P.mul 0 (-(n : ℤ)) (-(n : ℤ)) (zero_add _) b x
  let z : (cochainValue (List.ofFn f)).X (-(n : ℤ)) := F.hom.f (-(n : ℤ)) x
  apply E.toLinearEquiv.injective
  change E.hom (F.hom.f (-(n : ℤ)) y) = E.hom (a • z)
  calc
    _ = exteriorTermEquiv R f n y := exteriorCochainIso_apply R f n y
    _ = a • exteriorTermEquiv R f n x := by
      apply Subtype.ext
      let x' : Polynomial (ordinary R) (exteriorVariables r) (-(n : ℤ)) := x
      let a' : (ordinary R).complex.X 0 := a
      let b' := coefficient (ordinary R) (exteriorVariables r) 0 a'
      change exteriorImage R f n (polynomialMul (ordinary R) (exteriorVariables r)
        0 (-(n : ℤ)) (-(n : ℤ)) (zero_add _) b' x') = a • exteriorImage R f n x'
      rw [← exteriorImageZ_neg R f n, exteriorImageZ_mul]
      have hb : exteriorImageZ R f 0 b' = algebraMap R (exteriorRing R f) a := exteriorImage_coefficient R f a
      rw [hb, Algebra.smul_def]
    _ = a • E.hom z := congrArg (fun w : ⋀[R]^n (Fin (List.ofFn f).length → R) => a • w)
      (exteriorCochainIso_apply R f n x).symm
    _ = _ := (E.hom.hom.map_smul a z).symm

private theorem exteriorCochain_monomial (R : CommAlgCat.{v} k) (f : Fin r → R)
    (n : ℕ) (s : Fin n → Fin r) (a : R) :
    (termIsoValue (List.ofFn f) n).hom ((exteriorCochainIso R f).hom.f (-(n : ℤ))
      ((exteriorAlgebra R f).mul 0 (-(n : ℤ)) (-(n : ℤ)) (zero_add _)
        ((exteriorBase R f).chainMap.f 0 a)
        (orderedProduct (exteriorAlgebra R f) (fun i => gen (exteriorPresentation R f) i) n s))) =
      a • coordinateWedge f n s := by
  let a' : (ordinary R).complex.X 0 := a
  let b := coefficient (ordinary R) (exteriorVariables r) 0 a'
  let x : Polynomial (ordinary R) (exteriorVariables r) (-(n : ℤ)) :=
    orderedProduct (exteriorAlgebra R f) (fun i => gen (exteriorPresentation R f) i) n s
  let y : (exteriorAlgebra R f).complex.X (-(n : ℤ)) := polynomialMul (ordinary R) (exteriorVariables r)
    0 (-(n : ℤ)) (-(n : ℤ)) (zero_add _) b x
  change (termIsoValue (List.ofFn f) n).hom ((exteriorCochainIso R f).hom.f _ y) = _
  rw [exteriorCochainIso_apply R f n y]
  apply Subtype.ext
  change exteriorImage R f n (polynomialMul (ordinary R) (exteriorVariables r)
    0 (-(n : ℤ)) (-(n : ℤ)) (zero_add _) b x) = a • (coordinateWedge f n s : exteriorRing R f)
  rw [← exteriorImageZ_neg R f n, exteriorImageZ_mul, exteriorImageZ_neg]
  have hb : exteriorImageZ R f 0 b = algebraMap R (exteriorRing R f) a := exteriorImage_coefficient R f a
  have hx : exteriorImage R f n x = (coordinateWedge f n s : exteriorRing R f) :=
    exteriorImage_orderedProduct R f n s
  rw [hb, hx, Algebra.smul_def]

private theorem exteriorDegreeZero (R : CommAlgCat.{v} k) (f : Fin r → R) (a : R) :
    exteriorPower.zeroEquiv R _ (exteriorTermEquiv R f 0 ((exteriorBase R f).chainMap.f 0 a)) = a := by
  let E := exteriorPower.zeroEquiv R (Fin (List.ofFn f).length → R)
  change E (exteriorTermEquiv R f 0 ((exteriorBase R f).chainMap.f 0 a)) = a
  apply E.symm.injective
  rw [LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  let a' : (ordinary R).complex.X 0 := a
  change exteriorImage R f 0 (coefficient (ordinary R) (exteriorVariables r) 0 a') =
    ((exteriorPower.zeroEquiv R (Fin (List.ofFn f).length → R)).symm a : exteriorRing R f)
  have h := exteriorImage_coefficient R f a
  change exteriorImage R f 0 (coefficient (ordinary R) (exteriorVariables r) 0 a') = _ at h
  rw [h, exteriorPower.zeroEquiv_symm_apply, SetLike.val_smul, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti_zero_apply, Algebra.algebraMap_eq_smul_one]

private theorem exteriorBase_zero_surjective (R : CommAlgCat.{v} k) (f : Fin r → R) :
    Function.Surjective ((exteriorBase R f).chainMap.f 0) := by
  intro x
  let q := (exteriorTermEquiv R f 0)
  let e := exteriorPower.zeroEquiv R (Fin (List.ofFn f).length → R)
  let a : R := e (q x)
  exact ⟨a, q.injective (e.injective (exteriorDegreeZero R f a))⟩


private theorem quotientStalkIso_zero (R : CommAlgCat.{v} k) (f : Fin r → R)
    (x : ((restrictCochains R).obj
      ((Specs.DerivedFormalization.Cochains.stalkValue R).obj (ModuleCat.of R (quotientRing f)))).X 0) :
    (quotientStalkIso R f).hom.f 0 x =
      (singleObjXSelf (.up ℤ) 0 (ModuleCat.of R (quotientRing f))).hom x := by
  rfl

private theorem exteriorAugmentation_cochain (R : CommAlgCat.{v} k) (f : Fin r → R)
    (e : exteriorAlgebra R f ⟶ ordinary (quotientAlg R f))
    (he : exteriorBase R f ≫ e = quotientMap R f) :
    e.chainMap = (exteriorCochainIso R f).hom ≫
      (restrictCochains R).map (augmentationValue (List.ofFn f)) ≫ (quotientStalkIso R f).hom := by
  apply HomologicalComplex.to_single_hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := exteriorBase_zero_surjective R f x
  let y := (exteriorBase R f).chainMap.f 0 a
  let z : (cochainValue (List.ofFn f)).X 0 := (exteriorCochainIso R f).hom.f 0 y
  let c := augmentationValue (List.ofFn f)
  let q := quotientStalkIso R f
  let L := listIdeal (List.ofFn f)
  let σ := singleObjXSelf (.up ℤ) 0 (ModuleCat.of R (quotientRing f))
  have h₀ : e.chainMap.f 0 y = Ideal.Quotient.mk L a :=
    hom_congr_apply he 0 a
  have h₁ : σ.hom (c.f 0 z) =
      Ideal.Quotient.mk L (exteriorPower.zeroEquiv R _ ((termIsoValue (List.ofFn f) 0).hom z)) :=
    congrArg (fun t => t z) (koszulCochainAugmentation_f_zero (List.ofFn f))
  have h₂ : exteriorPower.zeroEquiv R _ ((termIsoValue (List.ofFn f) 0).hom z) = (a : R) :=
    (congrArg (exteriorPower.zeroEquiv R _) (exteriorCochainIso_apply R f 0 y)).trans
      (exteriorDegreeZero R f a)
  let w : ((restrictCochains R).obj
      ((Specs.DerivedFormalization.Cochains.stalkValue R).obj (ModuleCat.of R (quotientRing f)))).X 0 := c.f 0 z
  change e.chainMap.f 0 y = q.hom.f 0 w
  have hq : q.hom.f 0 w = σ.hom (c.f 0 z) := quotientStalkIso_zero R f w
  exact h₀.trans ((congrArg (Ideal.Quotient.mk L) h₂).symm.trans (h₁.symm.trans hq.symm))

/-- The one-stage exterior extension realizes the ordinary Koszul complex,
with its distinguished coordinates and its canonical quotient augmentation. -/
theorem exists_koszulAlgebra (R : CommAlgCat.{v} k) (r : ℕ) (f : Fin r → R) :
    Nonempty (KoszulAlgebra R f) := by
  obtain ⟨ε, hε, _⟩ := exists_exterior_augmentation R f
  exact ⟨{
    obj := exteriorAlgebra R f
    base := exteriorBase R f
    exterior := exteriorPresentation R f
    d_generator := exterior_d_generator R f
    cochain := exteriorCochainIso R f
    cochain_scalar := exteriorCochain_scalar R f
    monomial := exteriorCochain_monomial R f
    augmentation := ε
    augmentation_base := hε
    augmentation_cochain := exteriorAugmentation_cochain R f ε hε }⟩

/-! The marked classes at the origin. -/

private def forgetTerm (P : KoszulAlgebra R f) (n : ℕ) :
    P.obj.complex.X (-(n : ℤ)) ≅ restrictedModule R (⋀[R]^n (Fin (List.ofFn f).length → R)) :=
  ((HomologicalComplex.eval _ _ _).mapIso P.cochain) ≪≫
    (ModuleCat.restrictScalars (algebraMap k R)).mapIso (termIsoValue (List.ofFn f) n)

private theorem base_zero_bijective (P : KoszulAlgebra R f) :
    Function.Bijective (P.base.chainMap.f 0) := by
  let φ := (forgetTerm P 0).toLinearEquiv
  let ψ := exteriorPower.zeroEquiv R (Fin (List.ofFn f).length → R)
  have h (a : (ordinary R).complex.X 0) : ψ (φ (P.base.chainMap.f 0 a)) = (a : R) := by
    let s : Fin 0 → Fin r := Fin.elim0
    have hm := P.monomial 0 s (a : R)
    have hu := P.obj.toDGAlgebra.comp_id (a := ()) (b := ()) 0 (P.base.chainMap.f 0 a)
    change P.obj.mul 0 0 0 rfl (P.base.chainMap.f 0 a) P.obj.one = _ at hu
    let ar : R := a
    have hφ : φ (P.base.chainMap.f 0 a) = ar • coordinateWedge f 0 s := by
      change φ (P.obj.mul 0 0 0 rfl (P.base.chainMap.f 0 a) P.obj.one) = _ at hm
      exact (congrArg φ hu).symm.trans hm
    change ψ (φ (P.base.chainMap.f 0 a)) = a
    dsimp only [ψ]
    rw [hφ]
    change exteriorPower.zeroEquiv R _ (ar • coordinateWedge f 0 s) = ar
    rw [map_smul, coordinateWedge, exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one]
  constructor
  · intro a b hab
    exact (h a).symm.trans ((congrArg (fun x => ψ (φ x)) hab).trans (h b))
  · intro x
    let a : (ordinary R).complex.X 0 := ψ (φ x)
    exact ⟨a, φ.injective (ψ.injective (h a))⟩

private def h0CoefficientMap (P : KoszulAlgebra R f) : R →ₐ[k] P.obj.H0 :=
  P.obj.h0Class.comp
    { toFun := fun a => P.base.chainMap.f 0 a
      map_one' := P.base.map_one
      map_mul' := P.base.map_mul 0 0 0 rfl
      map_zero' := map_zero (P.base.chainMap.f 0).hom
      map_add' := map_add (P.base.chainMap.f 0).hom
      commutes' := fun c => by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
        change (P.base.chainMap.f 0).hom (c • (ordinary R).one) = c • P.obj.one
        rw [map_smul, P.base.map_one] }

private theorem h0Coefficients_bijective (P : KoszulAlgebra R f)
    (h : P.obj.complex.d (-1) 0 = 0) : Function.Bijective (h0CoefficientMap P) := by
  have hinj : Function.Injective P.obj.h0Class := by
    intro a b hab
    change Ideal.Quotient.mk P.obj.boundaryIdeal a = Ideal.Quotient.mk P.obj.boundaryIdeal b at hab
    obtain ⟨x, hx⟩ := Ideal.Quotient.eq.mp hab
    have hz : P.obj.complex.d (-1) 0 x = 0 := by rw [h]; rfl
    exact sub_eq_zero.mp (hx.symm.trans hz)
  have hsur : Function.Surjective P.obj.h0Class := Ideal.Quotient.mk_surjective
  exact ⟨hinj.comp (base_zero_bijective P).1, hsur.comp (base_zero_bijective P).2⟩

private def restrictedCoefficientIso (K : CommAlgCat.{v} k) :
    restrictedModule K K ≅ ModuleCat.of k K :=
  ({ toFun := id
     invFun := id
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl
     map_add' := fun _ _ => rfl
     map_smul' := fun a x => by
       let y : K := x
       change algebraMap k K a * y = a • y
       exact (Algebra.smul_def a y).symm } : restrictedModule K K ≃ₗ[k] K).toModuleIso

private def singletonCoordinates (K : CommAlgCat.{v} k) (f : Fin 1 → K) :
    (Fin (List.ofFn f).length → K) ≃ₗ[K] K :=
  (LinearEquiv.funCongrLeft K K (finCongr List.length_ofFn.symm)).trans
    (LinearEquiv.funUnique (Fin 1) K K)

private def originDegreeNegOne {K : CommAlgCat.{v} k} {f : Fin 1 → K}
    (P : KoszulAlgebra K f) : P.obj.complex.X (-1) ≃ₗ[k] K :=
  let q : (⋀[K]^1 (Fin (List.ofFn f).length → K)) ≃ₗ[K] K :=
    (exteriorPower.oneEquiv K _).trans (singletonCoordinates K f)
  ((forgetTerm P 1) ≪≫ (ModuleCat.restrictScalars (algebraMap k K)).mapIso q.toModuleIso ≪≫
    restrictedCoefficientIso K).toLinearEquiv

private theorem originDegreeNegOne_generator {K : CommAlgCat.{v} k} {f : Fin 1 → K}
    (P : KoszulAlgebra K f) : originDegreeNegOne P (P.generator 0) = 1 := by
  let s : Fin 1 → Fin 1 := fun _ => 0
  let g := P.generator 0
  have hm := P.monomial 1 s 1
  have hp : orderedProduct P.obj P.generator 1 s = g :=
    P.obj.toDGAlgebra.comp_id (a := ()) (b := ()) (-1) g
  change (forgetTerm P 1).hom (P.obj.mul 0 (-1) (-1) (zero_add _)
    (P.base.chainMap.f 0 (1 : (ordinary K).complex.X 0)) (orderedProduct P.obj P.generator 1 s)) =
      (1 : K) • coordinateWedge f 1 s at hm
  change _ = (1 : K) • coordinateWedge f 1 s at hm
  rw [hp, show P.base.chainMap.f 0 (1 : (ordinary K).complex.X 0) = P.obj.one from P.base.map_one,
    P.obj.toDGAlgebra.id_comp (a := ()) (b := ()) (-1) g, one_smul] at hm
  change singletonCoordinates K f (exteriorPower.oneEquiv K _
    ((forgetTerm P 1).hom g)) = _
  have he : (fun z : restrictedModule K (⋀[K]^1 (Fin (List.ofFn f).length → K)) =>
    singletonCoordinates K f (exteriorPower.oneEquiv K _ z)) ((forgetTerm P 1).hom g) = (1 : K) := by
    rw [hm]
    simp [coordinateWedge, singletonCoordinates, LinearEquiv.funUnique_apply,
      LinearEquiv.funCongrLeft_apply, s]
  exact he


private def homologyTermOfZeroDifferential (C : ModuleCochain.{u,v} k)
    (h : ∀ i j, C.d i j = 0) (i : ℤ) :
    C.homology i ≅ C.X i :=
  (C.isoHomologyπ (i-1) i (by simp) (h _ _)).symm ≪≫
    C.iCyclesIso i (i+1) (by simp) (h _ _)

omit [CharZero k] in
private theorem homologyTermOfZeroDifferential_hom (C : ModuleCochain.{u,v} k)
    (h : ∀ i j, C.d i j = 0) (i : ℤ) :
    C.homologyπ i ≫ (homologyTermOfZeroDifferential C h i).hom = C.iCycles i := by
  simp [homologyTermOfZeroDifferential]

theorem origin_of_zeroKoszul (S : CoproductModel T) (K : CommAlgCat.{v} k)
    (eK : K ≃ₐ[k] k) (P : PolynomialResolution K 1)
    (Q : KoszulAlgebra K (fun _ : Fin 1 => 0)) :
    let X := S.tensor P.resolution.base (zeroSection K 1)
    let e₁ := (S.inl P.resolution.base (zeroSection K 1)).chainMap.f (-1) (P.koszul.generator 0)
    (∃ e : X.H0 ≃ₐ[k] k,
      ∀ a : K, e (X.h0Class ((S.inr P.resolution.base (zeroSection K 1)).chainMap.f 0 a)) =
        eK a) ∧
    (∃ (e : X.complex.homology (-1) ≃ₗ[k] k) (z : X.complex.cycles (-1)),
      X.complex.iCycles (-1) z = e₁ ∧ e (X.complex.homologyπ (-1) z) = 1) ∧
    ∀ i : ℤ, i ≠ 0 → i ≠ -1 → IsZero (X.complex.homology i) := by
  let X := S.tensor P.koszul.base (zeroSection K 1)
  let e₁ : X.complex.X (-1) :=
    (S.inl P.koszul.base (zeroSection K 1)).chainMap.f (-1) (P.koszul.generator 0)
  change (∃ e : X.H0 ≃ₐ[k] k,
      ∀ a : K, e (X.h0Class ((S.inr P.koszul.base (zeroSection K 1)).chainMap.f 0 a)) =
        eK a) ∧
    (∃ (e : X.complex.homology (-1) ≃ₗ[k] k) (z : X.complex.cycles (-1)),
      X.complex.iCycles (-1) z = e₁ ∧ e (X.complex.homologyπ (-1) z) = 1) ∧
    ∀ i : ℤ, i ≠ 0 → i ≠ -1 → IsZero (X.complex.homology i)
  obtain ⟨φ, hbase, hgen⟩ := tensorComparison S P.koszul (zeroSection K 1) Q
    (zeroSection_variable K)
  let φC : X.complex ≅ Q.obj.complex := (NonpositiveCDGA.forgetComplex k).mapIso φ
  have hgen₀ : φC.hom.f (-1) e₁ = Q.generator 0 := hgen 0
  have hdQ := zeroKoszul_differential Q
  have hdX (i j : ℤ) : X.complex.d i j = 0 := by
    apply (cancel_mono (φC.hom.f j)).mp
    have hc : X.complex.d i j ≫ φC.hom.f j = φC.hom.f i ≫ Q.obj.complex.d i j :=
      (φC.hom.comm i j).symm
    exact hc.trans (by rw [hdQ, comp_zero, zero_comp])
  refine ⟨?_, ?_, ?_⟩
  · let A := AlgEquiv.ofBijective _ (h0Coefficients_bijective Q (hdQ (-1) 0))
    let B := CommAlgCat.algEquivOfIso ((NonpositiveCDGA.h0Functor k).mapIso φ)
    refine ⟨B.trans (A.symm.trans eK), ?_⟩
    intro a
    let a₀ : (ordinary K).complex.X 0 := a
    have hmark := hom_congr_apply hbase 0 a₀
    have hm : B (X.h0Class ((S.inr P.koszul.base (zeroSection K 1)).chainMap.f 0 a₀)) = A a := by
      change Q.obj.h0Class (φ.hom.chainMap.f 0
        ((S.inr P.koszul.base (zeroSection K 1)).chainMap.f 0 a₀)) = Q.obj.h0Class (Q.base.chainMap.f 0 a₀)
      exact congrArg Q.obj.h0Class hmark
    change eK (A.symm (B (X.h0Class _))) = eK a
    rw [hm, AlgEquiv.symm_apply_apply]
  · let z := (X.complex.iCyclesIso (-1) 0 (by simp) (hdX (-1) 0)).inv e₁
    let H := homologyTermOfZeroDifferential X.complex hdX (-1)
    let e := H.toLinearEquiv.trans
      ((((HomologicalComplex.eval _ _ (-1)).mapIso φC).toLinearEquiv).trans (originDegreeNegOne Q))
    have hz : X.complex.iCycles (-1) z = e₁ :=
      DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
        (X.complex.iCyclesIso_inv_hom_id (-1) 0 (by simp) (hdX (-1) 0))) e₁
    refine ⟨e.trans eK.toLinearEquiv, z, hz, ?_⟩
    have hz' : H.hom (X.complex.homologyπ (-1) z) = X.complex.iCycles (-1) z :=
      DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
        (homologyTermOfZeroDifferential_hom X.complex hdX (-1))) z
    change eK (originDegreeNegOne Q
      (φC.hom.f (-1) (H.hom (X.complex.homologyπ (-1) z)))) = 1
    rw [hz', hz, hgen₀, originDegreeNegOne_generator, map_one]
  · intro i h0 h1
    apply IsZero.of_iso _ (homologyTermOfZeroDifferential X.complex hdX i)
    apply IsZero.of_iso _ ((HomologicalComplex.eval _ _ i).mapIso φC)
    by_cases hi : 0 < i
    · exact ModuleCat.isZero_iff_subsingleton.mpr (Q.obj.nonpositive i hi)
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, -(n : ℤ) = i :=
        ⟨(-i).toNat, by rw [Int.toNat_of_nonneg (by omega : 0 ≤ -i), neg_neg]⟩
      have hn : 1 < n := by omega
      apply IsZero.of_iso _ (forgetTerm Q n)
      apply (ModuleCat.restrictScalars (algebraMap k K)).map_isZero
      apply ModuleCat.isZero_iff_subsingleton.mpr
      exact AdvCommAlg.Koszul.listComplex_vanish _ n (by simpa using hn)

/-- Apply the calculations to the signed tensor models of affine base change. -/
theorem koszulZeroLocus_conditional
    (h : Specs.DerivedFormalization.Affine.DerivedAffineBaseChange.BaseChange.{u,v}) :
    ZeroLocus.{u,v} := by
  intro k _ _
  obtain ⟨T, S, _⟩ := h.1 (k := k)
  refine ⟨T, S, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro R r f
      obtain ⟨P⟩ := exists_koszulAlgebra R r f
      exact ⟨P, wedgeDifferential P⟩
    · intro K e r
      obtain ⟨P⟩ := exists_koszulAlgebra (polynomial K r) r MvPolynomial.X
      exact ⟨polynomial_regular K e r, polynomialResolution K e r P,
        fun _ _ Q => polynomialTensorComparison S K e P Q⟩
    · intro R r f P hf
      obtain ⟨Q⟩ := exists_koszulAlgebra (quotientAlg R f) r (fun _ => 0)
      obtain ⟨hs, hq⟩ := augmentation_isResolution P hf
      exact ⟨hs, hq, Q, quotientTensorComparison S P Q, zeroKoszul_differential Q⟩
  · intro K eK P
    obtain ⟨Q⟩ := exists_koszulAlgebra K 1 (fun _ => 0)
    exact origin_of_zeroKoszul S K eK P Q

/-- The derived zero locus and its regular and rank-one specializations. -/
theorem koszulZeroLocus : ZeroLocus.{u,v} :=
  koszulZeroLocus_conditional DerivedAffineBaseChange.derivedAffineBaseChange

end
end DerivedFormalization.Affine.KoszulZeroLocus
