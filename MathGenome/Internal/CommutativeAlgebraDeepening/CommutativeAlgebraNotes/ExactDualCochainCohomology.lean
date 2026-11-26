import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ExactDualCochainCohomology
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.MatlisDualExactDetection
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! Exact duality for cochain complexes with values in the residue-field hull. -/

noncomputable section

open CategoryTheory Opposite
open HomologicalComplex
open CochainComplex.HomComplex

namespace CommutativeAlgebraNotes

universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The contravariant linear Hom complex into the common Matlis hull in degree zero. -/
abbrev matlisDualCochain (E : ResidueFieldEnvelope R) :=
  ExactDualCochainCohomologySpecs.dualComplexValue E

namespace ExactDualCochainCohomology

open ExactDualCochainCohomologySpecs

private abbrev Modules (R : Type u) [CommRing R] := ModuleCat.{u} R

local notation "C" => Modules R
local notation "K" => CochainComplex C ℤ

variable (E : ResidueFieldEnvelope R)

private instance dualPreservesHomology : (MatlisDual E).PreservesHomology :=
  ((MatlisDual E).exact_tfae.out 1 3
    (a := ∀ S : ShortComplex Cᵒᵖ, S.ShortExact → (S.map (MatlisDual E)).ShortExact)).mp
    (fun S hS => matlisDual_shortExact E S.unop hS.unop)

/-- Evaluating a cochain at its only possibly nonzero component. -/
private def singleTerm (U : K) (j : ℤ) :
    Cochain U (hullInDegreeZero E) j ≃ₗ[R] MatlisDualModule E (U.X (-j)) :=
  (Cochain.toSingleLinearEquiv (R := R) (neg_add_cancel j)).trans ModuleCat.homLinearEquiv

private lemma singleTerm_precomp {U V : K} (f : U ⟶ V) (j : ℤ)
    (z : Cochain V (hullInDegreeZero E) j) :
    singleTerm E U j ((Cochain.ofHom f).comp z (zero_add j)) =
      (singleTerm E V j z).comp (f.f (-j)).hom := by
  change (((Cochain.ofHom f).comp z _).v (-j) 0 _ ≫ _).hom = _
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Category.assoc]
  rfl

private lemma singleTerm_postcomp (U : K) (a : hull E ⟶ hull E) (j : ℤ)
    (z : Cochain U (hullInDegreeZero E) j) :
    singleTerm E U j (z.comp (Cochain.ofHom ((CochainComplex.singleFunctor C 0).map a))
      (add_zero j)) = a.hom.comp (singleTerm E U j z) := by
  change ((z.comp _ _).v (-j) 0 _ ≫ _).hom = _
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, Category.assoc]
  change (z.v (-j) 0 _ ≫ ((HomologicalComplex.single C (.up ℤ) 0).map a).f 0 ≫ _).hom = _
  rw [HomologicalComplex.single_map_f_self]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

private lemma singleTerm_mk (U : K) (j : ℤ) (f : U.X (-j) ⟶ hull E) :
    singleTerm E U j (Cochain.toSingleMk f (neg_add_cancel j)) = f.hom :=
  congrArg ModuleCat.Hom.hom (Cochain.toSingleEquiv_toSingleMk f (neg_add_cancel j))

private lemma singleTerm_δ (U : K) (j k : ℤ)
    (z : Cochain U (hullInDegreeZero E) j) :
    singleTerm E U k (δ j k z) =
      k.negOnePow • ((singleTerm E U j z).comp (U.d (-k) (-j)).hom) := by
  obtain ⟨f, rfl⟩ := Cochain.toSingleMk_surjective z (-j) (neg_add_cancel j)
  rw [Cochain.δ_toSingleMk f _ k (-k) (neg_add_cancel k)]
  simp only [Units.smul_def, map_zsmul, singleTerm_mk, ModuleCat.hom_comp]

private abbrev dualWindow (j : ℤ) :=
  shortComplexFunctor' C (.up ℤ) (j - 1) j (j + 1)

private abbrev sourceWindow (j : ℤ) :=
  shortComplexFunctor' C (.up ℤ) (-(j + 1)) (-j) (-(j - 1))

private abbrev oppositeWindow (j : ℤ) :=
  (sourceWindow (R := R) j).op ⋙ ShortComplex.opFunctor C

/-- The signs on the outer two terms account for the Hom differential.
The middle component is the unscaled evaluation map. -/
private def windowIso (U : K) (j : ℤ) :
    (dualWindow j).obj ((matlisDualCochain E).obj (op U)) ≅
      ((oppositeWindow j).obj (op U)).map (MatlisDual E) :=
  ShortComplex.isoMk
    (((singleTerm E U (j - 1)).trans
      (DistribMulAction.toLinearEquiv R _ j.negOnePow)).toModuleIso)
    (singleTerm E U j).toModuleIso
    (((singleTerm E U (j + 1)).trans
      (DistribMulAction.toLinearEquiv R _ (j + 1).negOnePow)).toModuleIso)
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change Cochain U (hullInDegreeZero E) (j - 1) at z
      change (j.negOnePow • singleTerm E U (j - 1) z).comp (U.d _ _).hom =
        singleTerm E U j (δ (j - 1) j z)
      rw [singleTerm_δ E U, LinearMap.smul_comp])
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change Cochain U (hullInDegreeZero E) j at z
      change (singleTerm E U j z).comp (U.d _ _).hom =
        (j + 1).negOnePow • singleTerm E U (j + 1) (δ j (j + 1) z)
      rw [singleTerm_δ E U, smul_smul, Int.units_mul_self, one_smul])

private def windowNatIso (j : ℤ) :
    matlisDualCochain E ⋙ dualWindow j ≅
      oppositeWindow j ⋙ (MatlisDual E).mapShortComplex :=
  NatIso.ofComponents (fun U => windowIso E U.unop j) (by
    intro V U f
    apply ShortComplex.hom_ext
    <;> apply ModuleCat.hom_ext
    <;> apply LinearMap.ext
    <;> intro z
    · change Cochain V.unop (hullInDegreeZero E) (j - 1) at z
      change j.negOnePow • singleTerm E U.unop (j - 1) ((Cochain.ofHom f.unop).comp z (zero_add (j - 1))) =
        (j.negOnePow • singleTerm E V.unop (j - 1) z).comp (f.unop.f _).hom
      rw [singleTerm_precomp, LinearMap.smul_comp]
    · change Cochain V.unop (hullInDegreeZero E) j at z
      exact singleTerm_precomp E f.unop j z
    · change Cochain V.unop (hullInDegreeZero E) (j + 1) at z
      change (j + 1).negOnePow • singleTerm E U.unop (j + 1) ((Cochain.ofHom f.unop).comp z (zero_add (j + 1))) =
        ((j + 1).negOnePow • singleTerm E V.unop (j + 1) z).comp (f.unop.f _).hom
      rw [singleTerm_precomp, LinearMap.smul_comp])

private def dualWindowCohomology (j : ℤ) :
    (matlisDualCochain E ⋙ homologyFunctor C (.up ℤ) j) ≅
      ((matlisDualCochain E ⋙ dualWindow j) ⋙ ShortComplex.homologyFunctor C) :=
  Functor.isoWhiskerLeft _ (homologyFunctorIso' C (.up ℤ) _ j _ (by simp) (by simp))

private def sourceWindowCohomology (j : ℤ) :
    homologyFunctor C (.up ℤ) (-j) ≅ sourceWindow j ⋙ ShortComplex.homologyFunctor C :=
  homologyFunctorIso' C (.up ℤ) _ (-j) _ (by simp; omega) (by simp; omega)

/-- Cohomology of the actual linear Hom complex identifies naturally with the
Matlis dual of cohomology in the opposite degree. -/
def cohomologyIso (j : ℤ) :
    dualCohomology E j ≅ cohomologyDual E j :=
  dualWindowCohomology E j ≪≫
    Functor.isoWhiskerRight (windowNatIso E j) _ ≪≫
    Functor.isoWhiskerLeft (oppositeWindow j) (ShortComplex.homologyFunctorIso (MatlisDual E)) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (sourceWindow j).op (ShortComplex.homologyFunctorOpNatIso C).symm)
      (MatlisDual E) ≪≫
    Functor.isoWhiskerRight
      ((Functor.opComp (sourceWindow j) (ShortComplex.homologyFunctor C)).symm ≪≫
        NatIso.op (sourceWindowCohomology (R := R) j)) (MatlisDual E)

private def postcompNatTrans (a : hull E ⟶ hull E) : MatlisDual E ⟶ MatlisDual E where
  app X := dualPostcomp E X.unop a
  naturality _ _ _ := ModuleCat.hom_ext (LinearMap.ext fun _ => LinearMap.ext fun _ => rfl)

private lemma window_postcomp (U : K) (j : ℤ) (a : hull E ⟶ hull E) :
    (dualWindow j).map (hullPostcomp E U a) ≫ (windowIso E U j).hom =
      (windowIso E U j).hom ≫
        ((oppositeWindow j).obj (op U)).mapNatTrans (postcompNatTrans E a) := by
  apply ShortComplex.hom_ext
  <;> apply ModuleCat.hom_ext
  <;> apply LinearMap.ext
  <;> intro z
  · change Cochain U (hullInDegreeZero E) (j - 1) at z
    change j.negOnePow • singleTerm E U (j - 1) (z.comp (Cochain.ofHom _) (add_zero (j - 1))) =
      a.hom.comp (j.negOnePow • singleTerm E U (j - 1) z)
    rw [singleTerm_postcomp]
    ext x
    simp [Units.smul_def]
  · change Cochain U (hullInDegreeZero E) j at z
    exact singleTerm_postcomp E U a j z
  · change Cochain U (hullInDegreeZero E) (j + 1) at z
    change (j + 1).negOnePow • singleTerm E U (j + 1) (z.comp (Cochain.ofHom _) (add_zero (j + 1))) =
      a.hom.comp ((j + 1).negOnePow • singleTerm E U (j + 1) z)
    rw [singleTerm_postcomp]
    ext x
    simp [Units.smul_def]

set_option backward.isDefEq.respectTransparency false in
/-- The exact-dual comparison commutes with the induced action of every hull endomorphism. -/
theorem cohomologyIso_postcomp (j : ℤ) : comparison E j (cohomologyIso E j) := by
  intro U a
  let b := hullPostcomp E U a
  let F := MatlisDual E
  let S := (oppositeWindow j).obj (op U)
  let τ := postcompNatTrans E a
  let W := ShortComplex.homologyFunctor C
  let p := (dualWindowCohomology E j).hom.app (op U)
  let q := W.map (windowIso E U j).hom
  let r := (S.mapHomologyIso F).hom
  let middle := op ((sourceWindow j).obj U).homology
  let α : S.homology ⟶ middle :=
    (ShortComplex.homologyFunctorOpNatIso C).symm.hom.app (op ((sourceWindow j).obj U))
  let β : middle ⟶ op (U.homology (-j)) :=
    (((Functor.opComp (sourceWindow j) W).symm ≪≫
      NatIso.op (sourceWindowCohomology (R := R) j)).hom.app (op U))
  let t := F.map α
  let w := F.map β
  change homologyMap b j ≫ (p ≫ (q ≫ (r ≫ (t ≫ w)))) =
    (p ≫ (q ≫ (r ≫ (t ≫ w)))) ≫ τ.app (op (U.homology (-j)))
  have hp : homologyMap b j ≫ p = p ≫ W.map ((dualWindow j).map b) :=
    (homologyFunctorIso' C (.up ℤ) (j - 1) j (j + 1)
      (by simp) (by simp)).hom.naturality b
  have hq : W.map ((dualWindow j).map b) ≫ q = q ≫ W.map (S.mapNatTrans τ) := by
    dsimp only [q]
    rw [← W.map_comp, window_postcomp E U j a, W.map_comp]
  have hr : W.map (S.mapNatTrans τ) ≫ r = r ≫ τ.app S.homology := by
    change ShortComplex.homologyMap (S.mapNatTrans τ) ≫ (S.mapHomologyIso F).hom =
      (S.mapHomologyIso F).hom ≫ τ.app S.homology
    dsimp only [F]
    rw [ShortComplex.homologyMap_mapNatTrans S τ]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have ht : τ.app S.homology ≫ t = t ≫ τ.app middle := (τ.naturality α).symm
  have hw : τ.app middle ≫ w = w ≫ τ.app (op (U.homology (-j))) := (τ.naturality β).symm
  simp only [Category.assoc, reassoc_of% hp, reassoc_of% hq, reassoc_of% hr,
    reassoc_of% ht, hw]


end ExactDualCochainCohomology

open ExactDualCochainCohomologySpecs

/-- Matlis duality commutes with cohomology, reversing the cohomological degree. -/
theorem exactDualCochainCohomology (E : ResidueFieldEnvelope R) (j : ℤ) :
    ∃ e : dualCohomology E j ≅ cohomologyDual E j, comparison E j e :=
  ⟨ExactDualCochainCohomology.cohomologyIso E j,
    ExactDualCochainCohomology.cohomologyIso_postcomp E j⟩

/-- The complex Matlis dual takes quasi-isomorphisms to quasi-isomorphisms. -/
theorem matlisDualCochain_quasiIso (E : ResidueFieldEnvelope R)
    {U V : CochainComplex (ModuleCat.{u} R) ℤ} (f : U ⟶ V) (hf : QuasiIso f) :
    QuasiIso ((matlisDualCochain E).map f.op) := by
  constructor
  intro j
  rw [quasiIsoAt_iff_isIso_homologyMap]
  change IsIso ((dualCohomology E j).map f.op)
  let e := ExactDualCochainCohomology.cohomologyIso E j
  have : IsIso (homologyMap f (-j)) :=
    (quasiIsoAt_iff_isIso_homologyMap f (-j)).mp (hf.quasiIsoAt (-j))
  have : IsIso ((cohomologyDual E j).map f.op) := by
    change IsIso ((MatlisDual E).map (homologyMap f (-j)).op)
    infer_instance
  have : IsIso (e.hom.app (op U)) := (e.app (op U)).isIso_hom
  have : IsIso (e.hom.app (op V)) := (e.app (op V)).isIso_hom
  exact IsIso.of_isIso_fac_right (e.hom.naturality f.op)

end CommutativeAlgebraNotes
