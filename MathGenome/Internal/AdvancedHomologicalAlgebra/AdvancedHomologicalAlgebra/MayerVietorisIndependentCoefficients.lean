import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.MayerVietoris
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
import Batteries.Tactic.OpenPrivate
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.Algebra.Category.ModuleCat.Projective

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AdvancedHomologicalAlgebra.SheafUniverseTransport
open AdvancedHomologicalAlgebra.MayerVietorisIndependentData
open Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
open Specs.AdvancedHomologicalAlgebra.SheafCohomology (resolutionModelMap)

universe a u r

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients

section HomologyTransport
open HomologicalComplex

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C]

private abbrev mapped (F : A ⥤ B) [F.Additive] (K : CochainComplex A ℤ) :=
  (F.mapHomologicalComplex (.up ℤ)).obj K

@[reassoc]
private lemma homologyπ_mapHomologyIso (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (S : ShortComplex A) :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  rw [ShortComplex.mapHomologyIso, ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
  let h := S.homologyData.left
  have hp : S.homologyπ = h.cyclesIso.hom ≫ h.π := by
    have hp' := h.homologyπ_comp_homologyIso_hom
    change S.homologyπ ≫ (S.leftHomologyIso.inv ≫ S.leftHomologyIso.hom) =
      h.cyclesIso.hom ≫ h.π at hp'
    simpa only [Iso.inv_hom_id, Category.comp_id] using hp'
  change (h.map F).cyclesIso.hom ≫ F.map h.π =
    (S.mapCyclesIso F).hom ≫ F.map S.homologyπ
  rw [hp, F.map_comp, ← Category.assoc]
  apply congrArg (fun f ↦ f ≫ F.map h.π)
  haveI : Mono (F.map h.i) := by
    change Mono (h.map F).i
    infer_instance
  apply (cancel_mono (F.map h.i)).mp
  rw [Category.assoc, ← F.map_comp, h.cyclesIso_hom_comp_i,
    S.mapCyclesIso_hom_iCycles]
  exact (h.map F).cyclesIso_hom_comp_i

@[reassoc]
private lemma homologyIso_naturality (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ) :
    homologyMap ((F.mapHomologicalComplex (.up ℤ)).map f) n ≫ ((L.sc n).mapHomologyIso F).hom =
      ((K.sc n).mapHomologyIso F).hom ≫ F.map (homologyMap f n) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor A (.up ℤ) n).map f) F

@[reassoc]
private lemma homologyIso_comp (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] [F.PreservesHomology] [G.PreservesHomology]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] [PreservesFiniteColimits F] [PreservesFiniteColimits G]
    (K : CochainComplex A ℤ) (n : ℤ) :
    (((mapped F K).sc n).mapHomologyIso G).hom ≫ G.map ((K.sc n).mapHomologyIso F).hom =
      ((K.sc n).mapHomologyIso (F ⋙ G)).hom := by
  let S := K.sc n
  change ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom =
    (S.mapHomologyIso (F ⋙ G)).hom
  apply (cancel_epi ((S.map F).map G).homologyπ).mp
  have hFG :
      ((S.map F).map G).homologyπ ≫ (S.mapHomologyIso (F ⋙ G)).hom =
        (S.mapCyclesIso (F ⋙ G)).hom ≫ G.map (F.map S.homologyπ) :=
    homologyπ_mapHomologyIso (F ⋙ G) S
  rw [homologyπ_mapHomologyIso_assoc, ← G.map_comp, homologyπ_mapHomologyIso,
    G.map_comp, ← Category.assoc, hFG]
  apply congrArg (fun f ↦ f ≫ G.map (F.map S.homologyπ))
  apply (cancel_mono (G.map (F.map S.iCycles))).mp
  have hFG' :
      (S.mapCyclesIso (F ⋙ G)).hom ≫ G.map (F.map S.iCycles) = ((S.map F).map G).iCycles :=
    S.mapCyclesIso_hom_iCycles (F ⋙ G)
  rw [Category.assoc, ← G.map_comp, ShortComplex.mapCyclesIso_hom_iCycles,
    ShortComplex.mapCyclesIso_hom_iCycles, hFG']

private abbrev cycleClass (K : CochainComplex A ℤ) {P : A} (n : ℤ)
    (c : P ⟶ K.X n) (hc : c ≫ K.d n (n + 1) = 0) :=
  K.liftCycles c (n + 1) (by simp) hc ≫ K.homologyπ n

@[reassoc]
private lemma map_cycleClass (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (K : CochainComplex A ℤ) {P : A} (n : ℤ)
    (c : P ⟶ K.X n) (hc : c ≫ K.d n (n + 1) = 0)
    (hc' : F.map c ≫ (mapped F K).d n (n + 1) = 0) :
    cycleClass (mapped F K) n (F.map c) hc' ≫ ((K.sc n).mapHomologyIso F).hom =
      F.map (cycleClass K n c hc) := by
  have hs :
      (mapped F K).liftCycles (F.map c) (n + 1) (by simp) hc' ≫ ((K.sc n).mapCyclesIso F).hom =
        F.map (K.liftCycles c (n + 1) (by simp) hc) := by
    apply (cancel_mono (F.map (K.iCycles n))).mp
    rw [Category.assoc]
    change _ ≫ (((K.sc n).mapCyclesIso F).hom ≫ F.map (K.sc n).iCycles) = _
    rw [ShortComplex.mapCyclesIso_hom_iCycles]
    change _ ≫ (mapped F K).iCycles n = _
    rw [liftCycles_i, ← F.map_comp, liftCycles_i]
  have hπ :
      (mapped F K).homologyπ n ≫ ((K.sc n).mapHomologyIso F).hom =
        ((K.sc n).mapCyclesIso F).hom ≫ F.map (K.homologyπ n) :=
    homologyπ_mapHomologyIso F (K.sc n)
  rw [cycleClass, Category.assoc, hπ, ← Category.assoc, hs, cycleClass, F.map_comp]

/-- Preservation of the connecting map follows by applying the exact functor
to a lift and its differential. A projective cover of the cycles provides
a single lift on which to check the equality. -/
@[reassoc]
private lemma map_connecting [EnoughProjectives A]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (S : ShortComplex (CochainComplex A ℤ)) (h : S.ShortExact)
    (h' : (S.map (F.mapHomologicalComplex (.up ℤ))).ShortExact) (n : ℤ) :
    h'.δ n (n + 1) rfl ≫ ((S.X₁.sc (n + 1)).mapHomologyIso F).hom =
      ((S.X₃.sc n).mapHomologyIso F).hom ≫ F.map (h.δ n (n + 1) rfl) := by
  let L := F.mapHomologicalComplex (.up ℤ)
  let T := S.map L
  let p := Projective.π (S.X₃.cycles n)
  let c := p ≫ S.X₃.iCycles n
  have hc : c ≫ S.X₃.d n (n + 1) = 0 := by simp [c]
  haveI := h.epi_g
  let b := Projective.factorThru c (S.g.f n)
  have hb : b ≫ S.g.f n = c := Projective.factorThru_comp c _
  have hbd : (b ≫ S.X₂.d n (n + 1)) ≫ S.g.f (n + 1) = 0 := by
    rw [Category.assoc, ← S.g.comm, ← Category.assoc, hb, hc]
  let k := (shortExact_iff_degreewise_shortExact S).mp h (n + 1)
  let z := k.fIsKernel.lift (KernelFork.ofι (b ≫ S.X₂.d n (n + 1)) hbd)
  have hz : z ≫ S.f.f (n + 1) = b ≫ S.X₂.d n (n + 1) :=
    k.fIsKernel.fac _ WalkingParallelPair.zero
  have hz' : z ≫ S.X₁.d (n + 1) (n + 1 + 1) = 0 := by
    haveI := h.mono_f
    rw [← cancel_mono (S.f.f (n + 1 + 1)), Category.assoc,
      ← S.f.comm, reassoc_of% hz, d_comp_d, comp_zero, zero_comp]
  have hcF : F.map c ≫ T.X₃.d n (n + 1) = 0 := by
    change F.map c ≫ F.map (S.X₃.d n (n + 1)) = 0
    rw [← F.map_comp, hc, F.map_zero]
  have hbF : F.map b ≫ T.g.f n = F.map c := by
    change F.map b ≫ F.map (S.g.f n) = F.map c
    rw [← F.map_comp, hb]
  have hzF : F.map z ≫ T.f.f (n + 1) = F.map b ≫ T.X₂.d n (n + 1) := by
    change F.map z ≫ F.map (S.f.f (n + 1)) = F.map b ≫ F.map (S.X₂.d n (n + 1))
    rw [← F.map_comp, ← F.map_comp, hz]
  have hzF' : F.map z ≫ T.X₁.d (n + 1) (n + 1 + 1) = 0 := by
    change F.map z ≫ F.map (S.X₁.d (n + 1) (n + 1 + 1)) = 0
    rw [← F.map_comp, hz', F.map_zero]
  have hd : cycleClass S.X₃ n c hc ≫ h.δ n (n + 1) rfl =
      cycleClass S.X₁ (n + 1) z hz' := by
    simpa only [cycleClass, Category.assoc] using
      h.δ_eq n (n + 1) rfl c hc b hb z hz (n + 1 + 1) (by simp)
  have hdF : cycleClass T.X₃ n (F.map c) hcF ≫ h'.δ n (n + 1) rfl =
      cycleClass T.X₁ (n + 1) (F.map z) hzF' :=
    by
      simpa only [cycleClass, Category.assoc] using
        h'.δ_eq n (n + 1) rfl (F.map c) hcF (F.map b) hbF (F.map z) hzF (n + 1 + 1) (by simp)
  have hp : S.X₃.liftCycles c (n + 1) (by simp) hc = p := by
    apply (cancel_mono (S.X₃.iCycles n)).mp
    exact liftCycles_i _ _ _ _ _
  haveI : Epi (cycleClass S.X₃ n c hc) := by
    dsimp only [cycleClass]
    rw [hp]
    infer_instance
  have hmc : cycleClass T.X₃ n (F.map c) hcF ≫ ((S.X₃.sc n).mapHomologyIso F).hom =
      F.map (cycleClass S.X₃ n c hc) := map_cycleClass F S.X₃ n c hc hcF
  have hmz : cycleClass T.X₁ (n + 1) (F.map z) hzF' ≫ ((S.X₁.sc (n + 1)).mapHomologyIso F).hom =
      F.map (cycleClass S.X₁ (n + 1) z hz') := map_cycleClass F S.X₁ (n + 1) z hz' hzF'
  haveI : Epi (cycleClass T.X₃ n (F.map c) hcF ≫ ((S.X₃.sc n).mapHomologyIso F).hom) := by
    rw [hmc]
    infer_instance
  haveI : Epi (cycleClass T.X₃ n (F.map c) hcF) := by
    have he : Epi ((cycleClass T.X₃ n (F.map c) hcF ≫ ((S.X₃.sc n).mapHomologyIso F).hom) ≫
      ((S.X₃.sc n).mapHomologyIso F).inv) := inferInstance
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id] at he
    exact he
  apply (cancel_epi (cycleClass T.X₃ n (F.map c) hcF)).mp
  rw [← Category.assoc, hdF, hmz, ← Category.assoc, hmc, ← F.map_comp, hd]

end HomologyTransport

open MayerVietorisData (sectionsFunctor sectionComplex complexRow)

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})

private lemma complexTransport_res
    (U T S : Open.{a,u,r} (X := X)) (hT : T ≤ U) (hS : S ≤ U) (h : S ≤ T)
    (I : CochainComplex (AmbientSheaves.{a} R) ℤ) :
    ((scalars.{a,u,r} R U).mapHomologicalComplex (.up ℤ)).map (kRes.{a,u,r} R U T S hT hS h I) ≫
        (complexTransport.{a,u,r} R U S hS I).hom =
      (complexTransport.{a,u,r} R U T hT I).hom ≫
        (((MayerVietorisData.res (liftedRing.{a} R) U T S hT hS h).mapHomologicalComplex
          (.up ℤ)).app (kLift.{a,u,r} R I)) := by
  ext q x
  rfl

variable (V W : Open.{a,u,r} (X := X))
  (I : CochainComplex (AmbientSheaves.{a} R) ℤ)

/-- The comparison uses actual section transport at every term and the
canonical comparison of biproducts in the middle. -/
def rowTransport :
    (row.{a,u,r} R V W I).map ((scalars.{a,u,r} R (V ⊔ W)).mapHomologicalComplex (.up ℤ)) ≅
      complexRow (liftedRing.{a} R) V W (kLift.{a,u,r} R I) := by
  let L := (scalars.{a,u,r} R (V ⊔ W)).mapHomologicalComplex (.up ℤ)
  let eA := complexTransport.{a,u,r} R (V ⊔ W) (V ⊔ W) le_rfl I
  let eB := complexTransport.{a,u,r} R (V ⊔ W) V le_sup_left I
  let eC := complexTransport.{a,u,r} R (V ⊔ W) W le_sup_right I
  let eD := complexTransport.{a,u,r} R (V ⊔ W) (V ⊓ W) (inf_le_left.trans le_sup_left) I
  haveI : L.IsEquivalence := by
    exact ((scalars.{a,u,r} R (V ⊔ W)).asEquivalence.mapHomologicalComplex (.up ℤ)).isEquivalence_functor
  letI := preservesBinaryBiproducts_of_preservesBinaryProducts L
  refine ShortComplex.isoMk eA (L.mapBiprod _ _ ≪≫ biprod.mapIso eB eC) eD ?_ ?_
  · change eA.hom ≫ _ = L.map (biprod.lift _ _) ≫ (L.mapBiprod _ _).hom ≫ _
    rw [← Category.assoc, biprod.map_lift_mapBiprod]
    apply biprod.hom_ext
    · simp only [complexRow, Category.assoc, biprod.lift_fst, biprod.lift_fst_assoc,
        biprod.mapIso_hom, biprod.map_fst]
      exact (complexTransport_res.{a,u,r} R _ _ _ _ _ _ I).symm
    · simp only [complexRow, Category.assoc, biprod.lift_snd, biprod.lift_snd_assoc,
        biprod.mapIso_hom, biprod.map_snd]
      exact (complexTransport_res.{a,u,r} R _ _ _ _ _ _ I).symm
  · change ((L.mapBiprod _ _).hom ≫ (biprod.mapIso eB eC).hom) ≫ _ =
      L.map (biprod.desc _ _) ≫ eD.hom
    rw [Category.assoc, ← biprod.mapBiprod_hom_desc, Category.assoc]
    congr 1
    apply biprod.hom_ext'
    · simp only [complexRow, biprod.mapIso_hom, biprod.inl_map_assoc,
        biprod.inl_desc, biprod.inl_desc_assoc]
      exact (complexTransport_res.{a,u,r} R _ _ _ _ _ _ I).symm
    · simp only [complexRow, biprod.mapIso_hom, biprod.inr_map_assoc,
        biprod.inr_desc, biprod.inr_desc_assoc, Preadditive.comp_neg,
        Preadditive.neg_comp, Functor.map_neg]
      exact congrArg Neg.neg (complexTransport_res.{a,u,r} R _ _ _ _ _ _ I).symm

end AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients

namespace AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients

open Specs.AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients
open HomologicalComplex
open CategoryTheory.Functor

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (V W : Open.{a,u,r} (X := X))

theorem flasqueRow : flasqueRowType.{a,u,r} := by
  intro X R V W I h
  let L := (scalars.{a,u,r} R (V ⊔ W)).mapHomologicalComplex (.up ℤ)
  haveI : L.IsEquivalence :=
    ((scalars.{a,u,r} R (V ⊔ W)).asEquivalence.mapHomologicalComplex (.up ℤ)).isEquivalence_functor
  apply ShortExact.reflects_shortExact_of_faithful L
  apply ShortComplex.shortExact_of_iso (rowTransport.{a,u,r} R V W I).symm
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro q
  apply ShortComplex.shortExact_of_iso (MayerVietoris.degreeRowIso _ V W (kLift.{a,u,r} R I) q).symm
  exact MayerVietoris.sectionsExact _ V W _
    ((ambient_flasque.{a,u,r} X R (I.X q)).2 (h q))

theorem liftDifferential : liftDifferentialType.{a,u,r} := by
  intro X R V W I h n P c hc b hb z hz
  exact h.δ_eq n (n + 1) rfl c hc b hb z hz (n + 2)
    (by apply (ComplexShape.up ℤ).next_eq'; change (n + 1) + 1 = n + 2; omega)

theorem negativeModel : negativeModelType.{a,u,r} := by
  intro X R U T h I _ n hn
  exact CochainComplex.isZero_of_isGE _ 0 n hn

private theorem modelFirstMono (I : CochainComplex (AmbientSheaves.{a} R) ℤ)
    [I.IsStrictlyGE 0] (h : (row.{a,u,r} R V W I).ShortExact) :
    Mono (homologyMap (row.{a,u,r} R V W I).f (0 : ℤ)) := by
  have hz : IsZero ((row.{a,u,r} R V W I).X₃.homology (-1)) := by
    change IsZero ((D.{a,u,r} R V W I).homology (-1))
    exact negativeModel.{a,u,r} R (V ⊔ W) (V ⊓ W) (inf_le_left.trans le_sup_left) I (-1)
      (by decide)
  exact ((ShortComplex.mk _ _ (h.δ_comp (-1) 0 (by decide))).exact_iff_mono
    (hz.eq_of_src _ _)).mp (h.homology_exact₁ (-1) 0 (by decide))

variable [EnoughInjectives (AmbientSheaves.{a} R)]

private def comparison {M : AmbientSheaves.{a} R} (m : Resolution.{a,u,r} R M) : Comparison.{a,u,r} R V W m :=
  fun T h n ↦ by
    letI := m.bounded
    haveI := SheafCohomologyOriginalCoefficients.resolution.{a,u,r} R (originalOpen.{a,u,r} T)
      M m.I m.i m.quasiIso m.injective n
    haveI : IsIso (modelMap.{a,u,r} R (V ⊔ W) T h m n) := by
      unfold modelMap
      infer_instance
    exact asIso (modelMap.{a,u,r} R (V ⊔ W) T h m n)

private abbrev homologyAt (n : ℤ) := HomologicalComplex.homologyFunctor (Sections.{a,u,r} R (V ⊔ W)) (.up ℤ) n

private def middleComparison {M : AmbientSheaves.{a} R} (m : Resolution.{a,u,r} R M)
    (e : Comparison.{a,u,r} R V W m) (n : ℕ) :
    (row.{a,u,r} R V W m.I).X₂.homology (n : ℤ) ≅
      (H.{a,u,r} R (V ⊔ W) V le_sup_left n).obj M ⊞ (H.{a,u,r} R (V ⊔ W) W le_sup_right n).obj M := by
  let L := homologyAt.{a,u,r} R V W (n : ℤ)
  letI := preservesBinaryBiproducts_of_preservesBinaryProducts L
  exact L.mapBiprod (B.{a,u,r} R V W m.I) (C.{a,u,r} R V W m.I) ≪≫
    biprod.mapIso (eB.{a,u,r} R V W m e n) (eC.{a,u,r} R V W m e n)

@[reassoc]
private lemma alpha_square {M : AmbientSheaves.{a} R} (m : Resolution.{a,u,r} R M)
    (e : Comparison.{a,u,r} R V W m) (n : ℕ) :
    (eA.{a,u,r} R V W m e n).hom ≫ alpha.{a,u,r} R V W m e n =
      homologyMap (row.{a,u,r} R V W m.I).f (n : ℤ) ≫ (middleComparison.{a,u,r} R V W m e n).hom := by
  let L := homologyAt.{a,u,r} R V W (n : ℤ)
  letI := preservesBinaryBiproducts_of_preservesBinaryProducts L
  change _ = L.map (biprod.lift (fV.{a,u,r} R V W m.I) (fW.{a,u,r} R V W m.I)) ≫
    (L.mapBiprod _ _).hom ≫ _
  rw [← Category.assoc, biprod.map_lift_mapBiprod]
  apply biprod.hom_ext <;>
    simp [alpha, Category.assoc, biprod.lift_fst_assoc, biprod.lift_snd_assoc, L]

@[reassoc]
private lemma beta_square {M : AmbientSheaves.{a} R} (m : Resolution.{a,u,r} R M)
    (e : Comparison.{a,u,r} R V W m) (n : ℕ) :
    (middleComparison.{a,u,r} R V W m e n).hom ≫ beta.{a,u,r} R V W m e n =
      homologyMap (row.{a,u,r} R V W m.I).g (n : ℤ) ≫ (eD.{a,u,r} R V W m e n).hom := by
  let L := homologyAt.{a,u,r} R V W (n : ℤ)
  letI := preservesBinaryBiproducts_of_preservesBinaryProducts L
  change ((L.mapBiprod _ _).hom ≫ (biprod.mapIso _ _).hom) ≫ _ =
    L.map (biprod.desc (gV.{a,u,r} R V W m.I) (-gW.{a,u,r} R V W m.I)) ≫ _
  rw [Category.assoc, ← biprod.mapBiprod_hom_desc, Category.assoc]
  congr 1
  apply biprod.hom_ext' <;> simp [beta, L]

private def sequenceIso {M : AmbientSheaves.{a} R} (m : Resolution.{a,u,r} R M)
    (e : Comparison.{a,u,r} R V W m) (h : (row.{a,u,r} R V W m.I).ShortExact) (n : ℕ) :
    HomologySequence.composableArrows₅ h (n : ℤ) ((n : ℤ) + 1) rfl ≅
      cohomologySequence.{a,u,r} R V W m e h n :=
  ComposableArrows.isoMk₅ (eA.{a,u,r} R V W m e n) (middleComparison.{a,u,r} R V W m e n) (eD.{a,u,r} R V W m e n)
    (eA.{a,u,r} R V W m e (n + 1)) (middleComparison.{a,u,r} R V W m e (n + 1)) (eD.{a,u,r} R V W m e (n + 1))
    (alpha_square.{a,u,r} R V W m e n).symm (beta_square.{a,u,r} R V W m e n).symm
    (by
      change h.δ (n : ℤ) ((n : ℤ) + 1) rfl ≫ (eA.{a,u,r} R V W m e (n + 1)).hom =
        (eD.{a,u,r} R V W m e n).hom ≫ delta.{a,u,r} R V W m e h n
      simp [delta])
    (alpha_square.{a,u,r} R V W m e (n + 1)).symm
    (beta_square.{a,u,r} R V W m e (n + 1)).symm

private theorem sequenceExact_of_model {M : AmbientSheaves.{a} R} (m : Resolution.{a,u,r} R M)
    (h : (row.{a,u,r} R V W m.I).ShortExact) (e : Comparison.{a,u,r} R V W m) :
    Mono (alpha.{a,u,r} R V W m e 0) ∧
      ∀ n, (cohomologySequence.{a,u,r} R V W m e h n).Exact := by
  refine ⟨?_, fun n ↦ ?_⟩
  · letI := m.bounded
    haveI := modelFirstMono.{a,u,r} R V W m.I h
    have ha : alpha.{a,u,r} R V W m e 0 =
        (eA.{a,u,r} R V W m e 0).inv ≫
          homologyMap (row.{a,u,r} R V W m.I).f 0 ≫ (middleComparison.{a,u,r} R V W m e 0).hom := by
      erw [← alpha_square.{a,u,r} R V W m e 0, Iso.inv_hom_id_assoc]
    rw [ha]
    infer_instance
  · exact ComposableArrows.exact_of_iso (sequenceIso.{a,u,r} R V W m e h n)
      (HomologySequence.composableArrows₅_exact h (n : ℤ) ((n : ℤ) + 1) rfl)

theorem sequenceExact : sequenceType.{a,u,r} := by
  intro X R V W _ M m
  let e := comparison.{a,u,r} R V W m
  let h := flasqueRow.{a,u,r} R V W m.I
    (fun q ↦ original_injectives_flasque.{a,u,r} X R _ (m.injective q))
  exact ⟨h, e, fun _ _ _ ↦ rfl, sequenceExact_of_model.{a,u,r} R V W m h e⟩

end AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients

namespace AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients

open Specs.AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients
open CategoryTheory.Functor HomologicalComplex

private lemma naturality_of_conjugate {C : Type*} [Category C]
    {A B D E A' B' D' E' : C}
    (x : A ≅ D) (y : B ≅ E) (x' : A' ≅ D') (y' : B' ≅ E')
    {a : A ⟶ B} {a' : A' ⟶ B'} {p : A ⟶ A'} {q : B ⟶ B'}
    {f : D ⟶ D'} {g : E ⟶ E'}
    (hx : x.hom ≫ f = p ≫ x'.hom) (hy : y.hom ≫ g = q ≫ y'.hom)
    (hs : p ≫ a' = a ≫ q) :
    f ≫ (x'.inv ≫ a' ≫ y'.hom) = (x.inv ≫ a ≫ y.hom) ≫ g := by
  apply (cancel_epi x.hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc x.hom f, hx, Category.assoc, Iso.hom_inv_id_assoc, hy,
    ← reassoc_of% hs]

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) [EnoughInjectives (AmbientSheaves.{a} R)]

private lemma modelMap_naturality (U T : Open.{a,u,r} (X := X)) (h : T ≤ U)
    {M N : AmbientSheaves.{a} R} (m : Resolution.{a,u,r} R M) (l : Resolution.{a,u,r} R N)
    (f : M ⟶ N) (φ : m.I ⟶ l.I)
    (hφ : m.i ≫ φ = (CochainComplex.singleFunctor (AmbientSheaves.{a} R) 0).map f ≫ l.i)
    (n : ℕ) :
    modelMap.{a,u,r} R U T h m n ≫ (H.{a,u,r} R U T h n).map f =
      homologyMap (((E.{a,u,r} R U T h).mapHomologicalComplex (.up ℤ)).map φ) (n : ℤ) ≫
        modelMap.{a,u,r} R U T h l n := by
  letI := m.bounded
  letI := l.bounded
  let Γ := sectionsValue.{a} R (originalOpen.{a,u,r} T)
  let G := Sc.{a,u,r} R U T h
  let J := (Γ.mapHomologicalComplex (.up ℤ)).map φ
  have hn := SheafCohomologyOriginalCoefficients.resolutionNaturality.{a,u,r}
    R (originalOpen.{a,u,r} T) m.i m.quasiIso l.i l.quasiIso f φ hφ n
  let K₁ := (Γ.mapHomologicalComplex (.up ℤ)).obj m.I
  let K₂ := (Γ.mapHomologicalComplex (.up ℤ)).obj l.I
  let b₁ := (K₁.sc (n : ℤ)).mapHomologyIso G
  let b₂ := (K₂.sc (n : ℤ)).mapHomologyIso G
  let a₁ := resolutionModelMap Γ m.i m.quasiIso n
  let a₂ := resolutionModelMap Γ l.i l.quasiIso n
  change (b₁.hom ≫ G.map a₁) ≫ G.map ((cohomologyValue.{a} R (originalOpen.{a,u,r} T) n).map f) =
    homologyMap ((G.mapHomologicalComplex (.up ℤ)).map J) (n : ℤ) ≫ (b₂.hom ≫ G.map a₂)
  rw [Category.assoc, ← G.map_comp]
  have h' : a₁ ≫ (cohomologyValue.{a} R (originalOpen.{a,u,r} T) n).map f =
      homologyMap J (n : ℤ) ≫ a₂ := hn
  rw [h', G.map_comp]
  exact (homologyIso_naturality_assoc G J (n : ℤ) (G.map a₂)).symm

variable (V W : Open.{a,u,r} (X := X))
variable {M N : AmbientSheaves.{a} R} (m : Resolution.{a,u,r} R M) (l : Resolution.{a,u,r} R N)
variable (f : M ⟶ N) (φ : m.I ⟶ l.I)
variable (hφ : m.i ≫ φ = (CochainComplex.singleFunctor (AmbientSheaves.{a} R) 0).map f ≫ l.i)

private abbrev cohomRes (T S : Open.{a,u,r} (X := X)) (hT : T ≤ V ⊔ W) (hS : S ≤ V ⊔ W)
    (h : S ≤ T) (n : ℕ) :=
  ((comparison.{a,u,r} R V W m) T hT n).inv ≫
    homologyMap (kRes.{a,u,r} R (V ⊔ W) T S hT hS h m.I) (n : ℤ) ≫
    ((comparison.{a,u,r} R V W m) S hS n).hom

include φ hφ

private lemma cohomRes_naturality (T S : Open.{a,u,r} (X := X)) (hT : T ≤ V ⊔ W)
    (hS : S ≤ V ⊔ W) (h : S ≤ T) (n : ℕ) :
    (H.{a,u,r} R (V ⊔ W) T hT n).map f ≫ cohomRes.{a,u,r} R V W l T S hT hS h n =
      cohomRes.{a,u,r} R V W m T S hT hS h n ≫ (H.{a,u,r} R (V ⊔ W) S hS n).map f := by
  refine naturality_of_conjugate
    ((comparison.{a,u,r} R V W m) T hT n) ((comparison.{a,u,r} R V W m) S hS n)
    ((comparison.{a,u,r} R V W l) T hT n) ((comparison.{a,u,r} R V W l) S hS n)
    (modelMap_naturality.{a,u,r} R _ _ _ m l f φ hφ n)
    (modelMap_naturality.{a,u,r} R _ _ _ m l f φ hφ n) ?_
  simp only [← homologyMap_comp]
  exact congrArg (fun q ↦ homologyMap q (n : ℤ))
    (((res.{a,u,r} R (V ⊔ W) T S hT hS h).mapHomologicalComplex (.up ℤ)).naturality φ)

private lemma alpha_naturality (n : ℕ) :
    (cohomologyValue.{a} R (originalOpen.{a,u,r} (V ⊔ W)) n).map f ≫
        alpha.{a,u,r} R V W l (comparison.{a,u,r} R V W l) n =
      alpha.{a,u,r} R V W m (comparison.{a,u,r} R V W m) n ≫
        biprod.map ((H.{a,u,r} R (V ⊔ W) V le_sup_left n).map f)
          ((H.{a,u,r} R (V ⊔ W) W le_sup_right n).map f) := by
  let e := unionIso.{a,u,r} R V W n
  let a (T : Open.{a,u,r} (X := X)) (h : T ≤ V ⊔ W) :=
    cohomRes.{a,u,r} R V W m (V ⊔ W) T le_rfl h h n
  let a' (T : Open.{a,u,r} (X := X)) (h : T ≤ V ⊔ W) :=
    cohomRes.{a,u,r} R V W l (V ⊔ W) T le_rfl h h n
  have step (T : Open.{a,u,r} (X := X)) (h : T ≤ V ⊔ W) :
      (cohomologyValue.{a} R (originalOpen.{a,u,r} (V ⊔ W)) n).map f ≫ e.inv.app N ≫ a' T h =
        (e.inv.app M ≫ a T h) ≫ (H.{a,u,r} R (V ⊔ W) T h n).map f := by
    rw [← Category.assoc, e.inv.naturality, Category.assoc, Category.assoc]
    exact congrArg (fun k ↦ e.inv.app M ≫ k)
      (cohomRes_naturality.{a,u,r} R V W m l f φ hφ (V ⊔ W) T le_rfl h h n)
  apply biprod.hom_ext
  · simpa only [alpha, e, a, a', cohomRes, Iso.app_inv, Iso.trans_inv, Category.assoc,
      biprod.lift_fst_assoc, biprod.lift_fst, biprod.map_fst] using step V le_sup_left
  · simpa only [alpha, e, a, a', cohomRes, Iso.app_inv, Iso.trans_inv, Category.assoc,
      biprod.lift_snd_assoc, biprod.lift_snd, biprod.map_snd] using step W le_sup_right

private lemma beta_naturality (n : ℕ) :
    biprod.map ((H.{a,u,r} R (V ⊔ W) V le_sup_left n).map f)
        ((H.{a,u,r} R (V ⊔ W) W le_sup_right n).map f) ≫
        beta.{a,u,r} R V W l (comparison.{a,u,r} R V W l) n =
      beta.{a,u,r} R V W m (comparison.{a,u,r} R V W m) n ≫
        (H.{a,u,r} R (V ⊔ W) (V ⊓ W) (inf_le_left.trans le_sup_left) n).map f := by
  apply biprod.hom_ext'
  · simpa only [beta, Category.assoc, biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc] using
      cohomRes_naturality.{a,u,r} R V W m l f φ hφ V (V ⊓ W) le_sup_left
        (inf_le_left.trans le_sup_left) inf_le_left n
  · simpa only [beta, Category.assoc, biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc,
      Preadditive.comp_neg, Preadditive.neg_comp] using
      congrArg Neg.neg (cohomRes_naturality.{a,u,r} R V W m l f φ hφ W (V ⊓ W) le_sup_right
        (inf_le_left.trans le_sup_left) inf_le_right n)

private lemma delta_naturality (hm : (row.{a,u,r} R V W m.I).ShortExact)
    (hl : (row.{a,u,r} R V W l.I).ShortExact) (n : ℕ) :
    (H.{a,u,r} R (V ⊔ W) (V ⊓ W) (inf_le_left.trans le_sup_left) n).map f ≫
        delta.{a,u,r} R V W l (comparison.{a,u,r} R V W l) hl n =
      delta.{a,u,r} R V W m (comparison.{a,u,r} R V W m) hm n ≫
        (cohomologyValue.{a} R (originalOpen.{a,u,r} (V ⊔ W)) (n + 1)).map f := by
  let e := unionIso.{a,u,r} R V W (n + 1)
  refine naturality_of_conjugate
    (eD.{a,u,r} R V W m (comparison.{a,u,r} R V W m) n)
    (eA.{a,u,r} R V W m (comparison.{a,u,r} R V W m) (n + 1))
    (eD.{a,u,r} R V W l (comparison.{a,u,r} R V W l) n)
    (eA.{a,u,r} R V W l (comparison.{a,u,r} R V W l) (n + 1))
    (modelMap_naturality.{a,u,r} R _ _ _ m l f φ hφ n) ?_
    (HomologySequence.δ_naturality (rowMap.{a,u,r} R V W φ) hm hl (n : ℤ) ((n : ℤ) + 1) rfl).symm
  change (_ ≫ e.hom.app M) ≫ _ = _ ≫ (_ ≫ e.hom.app N)
  rw [Category.assoc, ← e.hom.naturality, ← Category.assoc]
  exact congrArg (fun k ↦ k ≫ e.hom.app N)
    (modelMap_naturality.{a,u,r} R (V ⊔ W) (V ⊔ W) le_rfl m l f φ hφ (n + 1))

omit φ hφ

/-- Choose ambient injective resolutions, then use comparison cochain maps
to obtain the natural sequence on the original coefficients. -/
theorem naturalSequence : naturalSequenceType.{a,u,r} := by
  intro X R V W _
  let S := CochainComplex.singleFunctor (AmbientSheaves.{a} R) 0
  have hRes (M : AmbientSheaves.{a} R) : ∃ m : Resolution.{a,u,r} R M, Mono m.i := by
    obtain ⟨I, i, hmono, hq, hI, hb⟩ :=
      InjectiveComplexReplacement.replacement (AmbientSheaves.{a} R) (S.obj M) 0 inferInstance
    exact ⟨⟨I, hb, i, hq, hI⟩, HomologicalComplex.mono_of_mono_f i hmono⟩
  choose m hm using hRes
  let e M := comparison.{a,u,r} R V W (m M)
  let h M := flasqueRow.{a,u,r} R V W (m M).I
    (fun q ↦ original_injectives_flasque.{a,u,r} X R _ ((m M).injective q))
  refine ⟨m, h, e, fun _ _ _ _ ↦ rfl,
    fun M ↦ (sequenceExact_of_model.{a,u,r} R V W (m M) (h M) (e M)).1,
    fun M ↦ (sequenceExact_of_model.{a,u,r} R V W (m M) (h M) (e M)).2, ?_⟩
  intro M N f n
  letI := (m M).bounded
  letI := (m N).bounded
  letI := hm M
  letI := (m M).quasiIso
  obtain ⟨φ, hφ⟩ := SheafCohomology.injectiveResolutionLift (m M).i
    (S.map f ≫ (m N).i) (m N).injective
  exact ⟨alpha_naturality.{a,u,r} R V W _ _ f φ hφ n,
    beta_naturality.{a,u,r} R V W _ _ f φ hφ n,
    delta_naturality.{a,u,r} R V W _ _ f φ hφ _ _ n⟩

end AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients

namespace AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients

open Specs.AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients
open HomologicalComplex

theorem originalOpens : originalOpensType.{a,u,r} := by
  intro X V W
  let e := opensEquiv.{max a u r} X
  exact ⟨e.symm V, e.symm W, e.apply_symm_apply V, e.apply_symm_apply W,
    (e.map_sup _ _).trans (congrArg₂ (· ⊔ ·) (e.apply_symm_apply V) (e.apply_symm_apply W)),
    (e.map_inf _ _).trans (congrArg₂ (· ⊓ ·) (e.apply_symm_apply V) (e.apply_symm_apply W))⟩

theorem sectionTransportComparison : sectionTransportType.{a,u,r} := by
  intro X R V W I
  let L := (scalars.{a,u,r} R (V ⊔ W)).mapHomologicalComplex (.up ℤ)
  let e := rowTransport.{a,u,r} R V W I
  haveI : L.IsEquivalence :=
    ((scalars.{a,u,r} R (V ⊔ W)).asEquivalence.mapHomologicalComplex (.up ℤ)).isEquivalence_functor
  letI := preservesBinaryBiproducts_of_preservesBinaryProducts L
  let eB := complexTransport.{a,u,r} R (V ⊔ W) V le_sup_left I
  let eC := complexTransport.{a,u,r} R (V ⊔ W) W le_sup_right I
  refine ⟨e, rfl, rfl, ?_, ?_⟩
  · change ((L.mapBiprod _ _).hom ≫ (biprod.mapIso eB eC).hom) ≫ biprod.fst =
      L.map biprod.fst ≫ eB.hom
    simp only [Category.assoc, biprod.mapIso_hom, biprod.map_fst, Functor.mapBiprod_hom]
    erw [biprod.lift_fst_assoc]
  · change ((L.mapBiprod _ _).hom ≫ (biprod.mapIso eB eC).hom) ≫ biprod.snd =
      L.map biprod.snd ≫ eC.hom
    simp only [Category.assoc, biprod.mapIso_hom, biprod.map_snd, Functor.mapBiprod_hom]
    erw [biprod.lift_snd_assoc]

private lemma complexTransport_hom {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
    (U T : Open.{a,u,r} (X := X)) (h : T ≤ U) (I : CochainComplex (AmbientSheaves.{a} R) ℤ) :
    (complexTransport.{a,u,r} R U T h I).hom =
      𝟙 (((scalars.{a,u,r} R U).mapHomologicalComplex (.up ℤ)).obj (K.{a,u,r} R U T h I)) := by
  ext q x
  rfl

theorem modelBoundaryTransport : modelBoundaryTransportType.{a,u,r} := by
  intro X R V W I h h' n
  let S := scalars.{a,u,r} R (V ⊔ W)
  let L := S.mapHomologicalComplex (.up ℤ)
  let e := rowTransport.{a,u,r} R V W I
  haveI : L.IsEquivalence :=
    (S.asEquivalence.mapHomologicalComplex (.up ℤ)).isEquivalence_functor
  let hL := h.map_of_exact L
  have he₁ : e.hom.τ₁ = 𝟙 _ := complexTransport_hom.{a,u,r} R (V ⊔ W) (V ⊔ W) le_rfl I
  have he₃ : e.hom.τ₃ = 𝟙 _ := complexTransport_hom.{a,u,r} R (V ⊔ W) (V ⊓ W) _ I
  have hδ := HomologySequence.δ_naturality e.hom hL h' n (n + 1) rfl
  rw [he₁, he₃, homologyMap_id, homologyMap_id, Category.comp_id, Category.id_comp] at hδ
  have hh := map_connecting S (row.{a,u,r} R V W I) h hL n
  change h'.δ n (n + 1) rfl ≫ _ = _
  exact (congrArg (fun k ↦ k ≫ (((A.{a,u,r} R V W I).sc (n + 1)).mapHomologyIso S).hom) hδ.symm).trans hh

end AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients

namespace AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients

open Specs.AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients
open CategoryTheory.Functor HomologicalComplex
open AdvancedHomologicalAlgebra.SheafTheory (Modules sectionCohomology)
open MayerVietorisData (sectionComplex localCohomology ResolutionModel directAlpha
  cohomologyBeta directDelta sameOpenCohomologyIso)

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) [EnoughInjectives (AmbientSheaves.{a} R)]

private lemma site_model_square
    (U T : Open.{a,u,r} (X := X)) (h : T ≤ U)
    (s : SiteComparison.{a,u,r} R T)
    (hs : IsResolutionComparison (sectionsValue.{a} R (originalOpen.{a,u,r} T))
      (sectionsValue.{0} (liftedRing.{a} R) T) (transport.{a} R)
      (scalars.{a,u,r} R T) (siteSectionsIso.{a} R T) s)
    {M : AmbientSheaves.{a} R} (m : Resolution.{a,u,r} R M)
    (q : QuasiIso (raisedAugmentation.{a,u,r} R m))
    (j : ∀ k : ℤ, Injective ((kLift.{a,u,r} R m.I).X k))
    (n : ℕ) :
    (((K.{a,u,r} R U T h m.I).sc (n : ℤ)).mapHomologyIso (scalars.{a,u,r} R U)).hom ≫
        (scalars.{a,u,r} R U).map (modelMap.{a,u,r} R U T h m n) ≫
        ((localSiteComparison.{a,u,r} R U T h s n).app M).hom =
      (MayerVietoris.canonicalModelIso (liftedRing.{a} R) U T h ((transport.{a} R).obj M)
        (kLift.{a,u,r} R m.I) (raisedResolution.{a,u,r} R m q j).bounded
        (raisedAugmentation.{a,u,r} R m) q j n).inv := by
  letI := m.bounded
  letI := (raisedResolution.{a,u,r} R m q j).bounded
  let Γ := sectionsValue.{a} R (originalOpen.{a,u,r} T)
  let Γ' := sectionsValue.{0} (liftedRing.{a} R) T
  let F := Sc.{a,u,r} R U T h
  let G := raisedRestriction.{a,u,r} R U T h
  let L := scalars.{a,u,r} R T
  let S := scalars.{a,u,r} R U
  let K₀ := (Γ.mapHomologicalComplex (.up ℤ)).obj m.I
  let K₁ := (Γ'.mapHomologicalComplex (.up ℤ)).obj (kLift.{a,u,r} R m.I)
  let orig := resolutionModelMap Γ m.i m.quasiIso n
  let raised := resolutionModelMap Γ' (raisedAugmentation.{a,u,r} R m) q n
  let a := ((K₀.sc (n : ℤ)).mapHomologyIso F)
  let b := ((K₀.sc (n : ℤ)).mapHomologyIso L)
  let c := ((K₁.sc (n : ℤ)).mapHomologyIso G)
  let d := (((K.{a,u,r} R U T h m.I).sc (n : ℤ)).mapHomologyIso S)
  obtain ⟨q', hq⟩ := hs M m.I m.i m.quasiIso m.injective
  have hid : (NatIso.mapHomologicalComplex (siteSectionsIso.{a} R T) (.up ℤ)).hom.app m.I = 𝟙 K₁ := by
    ext z x
    rfl
  have hsite : L.map orig ≫ (s n).hom.app M = b.inv ≫ raised := by
    have hn := hq n
    dsimp only [modelComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Iso.app_hom] at hn
    erw [hid, CategoryTheory.Functor.map_id, Category.comp_id] at hn
    exact hn
  have hcomp : d.hom ≫ S.map a.hom = c.hom ≫ G.map b.hom :=
    (homologyIso_comp F S K₀ (n : ℤ)).trans (homologyIso_comp L G K₀ (n : ℤ)).symm
  have hcanon :
      (MayerVietoris.canonicalModelIso (liftedRing.{a} R) U T h ((transport.{a} R).obj M)
        (kLift.{a,u,r} R m.I) (raisedResolution.{a,u,r} R m q j).bounded
        (raisedAugmentation.{a,u,r} R m) q j n).inv = c.hom ≫ G.map raised := by
    simp only [MayerVietoris.canonicalModelIso, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv]
    congr 1
  change d.hom ≫ S.map (a.hom ≫ F.map orig) ≫ G.map ((s n).hom.app M) = _
  rw [hcanon, S.map_comp]
  calc
    _ = (d.hom ≫ S.map a.hom) ≫ S.map (F.map orig) ≫ G.map ((s n).hom.app M) := by
      simp only [Category.assoc]
    _ = c.hom ≫ G.map (b.hom ≫ L.map orig ≫ (s n).hom.app M) := by
      rw [hcomp]
      simp only [G.map_comp, Category.assoc]
      rfl
    _ = _ := by rw [hsite, Iso.hom_inv_id_assoc]

private lemma mapped_conjugate_square
    {A B : Type*} [Category* A] [Category* B] (F : A ⥤ B)
    {P Q H K : A} {P' Q' H' K' : B} (e : P ≅ H) (f : Q ≅ K) (e' : P' ≅ H') (f' : Q' ≅ K')
    (x : P' ≅ F.obj P) (y : Q' ≅ F.obj Q)
    (u : F.obj H ≅ H') (v : F.obj K ≅ K') (a : P ⟶ Q) (a' : P' ⟶ Q')
    (hx : x.hom ≫ F.map e.hom ≫ u.hom = e'.hom)
    (hy : y.hom ≫ F.map f.hom ≫ v.hom = f'.hom)
    (ha : a' ≫ y.hom = x.hom ≫ F.map a) :
    F.map (e.inv ≫ a ≫ f.hom) ≫ v.hom = u.hom ≫ (e'.inv ≫ a' ≫ f'.hom) := by
  have h₁ : F.map e.hom ≫ u.hom = x.inv ≫ e'.hom := by
    apply (cancel_epi x.hom).mp
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact hx
  have h₂ : F.map f.hom ≫ v.hom = y.inv ≫ f'.hom := by
    apply (cancel_epi y.hom).mp
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact hy
  have h₃ : x.inv ≫ a' = F.map a ≫ y.inv := by
    apply (cancel_epi x.hom).mp
    apply (cancel_mono y.hom).mp
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
    exact ha
  simpa only [Functor.map_comp, Functor.mapIso_inv, Functor.mapIso_hom, Category.assoc] using
    (naturality_of_conjugate (F.mapIso e) (F.mapIso f) e' f' h₁ h₂ h₃).symm

private lemma union_site_model_square
    (V W : Open.{a,u,r} (X := X))
    (s : SiteComparison.{a,u,r} R (V ⊔ W))
    (hs : IsResolutionComparison (sectionsValue.{a} R (originalOpen.{a,u,r} (V ⊔ W)))
      (sectionsValue.{0} (liftedRing.{a} R) (V ⊔ W)) (transport.{a} R)
      (scalars.{a,u,r} R (V ⊔ W)) (siteSectionsIso.{a} R (V ⊔ W)) s)
    {M : AmbientSheaves.{a} R} (m : Resolution.{a,u,r} R M)
    (q : QuasiIso (raisedAugmentation.{a,u,r} R m))
    (j : ∀ k : ℤ, Injective ((kLift.{a,u,r} R m.I).X k))
    (n : ℕ) :
    (((A.{a,u,r} R V W m.I).sc (n : ℤ)).mapHomologyIso
      (scalars.{a,u,r} R (V ⊔ W))).hom ≫
      (scalars.{a,u,r} R (V ⊔ W)).map
        (eA.{a,u,r} R V W m (comparison.{a,u,r} R V W m) n).hom ≫ (s n).hom.app M =
      (commonUnionIso.{a,u,r} R V W (raisedResolution.{a,u,r} R m q j) n).hom := by
  let U := V ⊔ W
  let S := scalars.{a,u,r} R U
  let N := (transport.{a} R).obj M
  let t := (localSiteComparison.{a,u,r} R U U le_rfl s n).app M
  let e := (unionIso.{a,u,r} R V W n).app M
  let e' := (sameOpenCohomologyIso (liftedRing.{a} R) U n).app N
  have hunit : S.map e.hom ≫ (s n).hom.app M = t.hom ≫ e'.hom := by
    ext x
    rfl
  change (((A.{a,u,r} R V W m.I).sc (n : ℤ)).mapHomologyIso S).hom ≫
    S.map (modelMap.{a,u,r} R U U le_rfl m n ≫ e.hom) ≫ (s n).hom.app M = _
  rw [S.map_comp, Category.assoc, hunit]
  let l := raisedResolution.{a,u,r} R m q j
  have hmodel : (((A.{a,u,r} R V W m.I).sc (n : ℤ)).mapHomologyIso S).hom ≫
      S.map (modelMap.{a,u,r} R U U le_rfl m n) ≫ t.hom =
    (commonModelIso.{a,u,r} R V W l U le_rfl n).hom :=
    site_model_square.{a,u,r} R U U le_rfl s hs m q j n
  change _ = (commonModelIso.{a,u,r} R V W l U le_rfl n).hom ≫ e'.hom
  rw [reassoc_of% hmodel]

private lemma homology_restriction_transport
    (U T P : Open.{a,u,r} (X := X)) (hT : T ≤ U) (hP : P ≤ U) (h : P ≤ T)
    (I : CochainComplex (AmbientSheaves.{a} R) ℤ) (n : ℤ) :
    homologyMap (((MayerVietorisData.res (liftedRing.{a} R) U T P hT hP h).mapHomologicalComplex
          (.up ℤ)).app (kLift.{a,u,r} R I)) n ≫
      (((K.{a,u,r} R U P hP I).sc n).mapHomologyIso (scalars.{a,u,r} R U)).hom =
    (((K.{a,u,r} R U T hT I).sc n).mapHomologyIso (scalars.{a,u,r} R U)).hom ≫
      (scalars.{a,u,r} R U).map (homologyMap (kRes.{a,u,r} R U T P hT hP h I) n) := by
  have hr := complexTransport_res.{a,u,r} R U T P hT hP h I
  rw [complexTransport_hom.{a,u,r} R U P hP I, complexTransport_hom.{a,u,r} R U T hT I,
    Category.comp_id, Category.id_comp] at hr
  rw [← hr]
  exact homologyIso_naturality (scalars.{a,u,r} R U) _ n

private lemma mapped_lift_square
    {A B : Type*} [Category* A] [Category* B] [HasZeroMorphisms A] [HasZeroMorphisms B]
    [HasBinaryBiproducts A] [HasBinaryBiproducts B]
    (F : A ⥤ B) [F.PreservesZeroMorphisms] [PreservesBinaryBiproducts F]
    {P Q T : A} {P' Q' T' : B} (p : F.obj P ≅ P') (q : F.obj Q ≅ Q') (t : F.obj T ≅ T')
    {f : P ⟶ Q} {g : P ⟶ T} {f' : P' ⟶ Q'} {g' : P' ⟶ T'}
    (hf : F.map f ≫ q.hom = p.hom ≫ f') (hg : F.map g ≫ t.hom = p.hom ≫ g') :
    F.map (biprod.lift f g) ≫ (F.mapBiprod Q T ≪≫ biprod.mapIso q t).hom =
      p.hom ≫ biprod.lift f' g' := by
  rw [Iso.trans_hom, ← Category.assoc, biprod.map_lift_mapBiprod]
  apply biprod.hom_ext
  · simpa only [Category.assoc, biprod.mapIso_hom, biprod.map_fst, biprod.lift_fst,
      biprod.lift_fst_assoc] using hf
  · simpa only [Category.assoc, biprod.mapIso_hom, biprod.map_snd, biprod.lift_snd,
      biprod.lift_snd_assoc] using hg

private lemma mapped_difference_square
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    [HasBinaryBiproducts A] [HasBinaryBiproducts B]
    (F : A ⥤ B) [F.Additive] [PreservesBinaryBiproducts F]
    {P Q T : A} {P' Q' T' : B} (p : F.obj P ≅ P') (q : F.obj Q ≅ Q') (t : F.obj T ≅ T')
    {f : P ⟶ T} {g : Q ⟶ T} {f' : P' ⟶ T'} {g' : Q' ⟶ T'}
    (hf : F.map f ≫ t.hom = p.hom ≫ f') (hg : F.map g ≫ t.hom = q.hom ≫ g') :
    F.map (biprod.desc f (-g)) ≫ t.hom =
      (F.mapBiprod P Q ≪≫ biprod.mapIso p q).hom ≫ biprod.desc f' (-g') := by
  rw [← biprod.mapBiprod_hom_desc, Iso.trans_hom, Category.assoc, Category.assoc]
  congr 1
  apply biprod.hom_ext'
  · simpa only [Category.assoc, biprod.mapIso_hom, biprod.inl_map_assoc, biprod.inl_desc,
      biprod.inl_desc_assoc] using hf
  · simpa only [Category.assoc, biprod.mapIso_hom, biprod.inr_map_assoc, biprod.inr_desc,
      biprod.inr_desc_assoc, Functor.map_neg, Preadditive.neg_comp,
      Preadditive.comp_neg] using congrArg Neg.neg hg

set_option maxHeartbeats 4000000 in
/-- The comparison of the original and raised section cohomology identifies
the two restrictions, their signed difference, and the boundary. -/
theorem cohomologyTransport : cohomologyTransportType.{a,u,r} := by
  intro X R V W _
  have hsite (T : Open.{a,u,r} (X := X)) :=
    SheafCohomologyOriginalCoefficients.siteComparison.{a,u,r} R T
  choose s hs using hsite
  refine ⟨s, hs, ?_⟩
  intro M m
  let U := V ⊔ W
  let D := V ⊓ W
  let hD : D ≤ U := inf_le_left.trans le_sup_left
  let S := scalars.{a,u,r} R U
  letI := m.bounded
  obtain ⟨q, _⟩ := hs U M m.I m.i m.quasiIso m.injective
  have j (k : ℤ) : Injective ((kLift.{a,u,r} R m.I).X k) :=
    ((transportEquivalence.{a} R).map_injective_iff (m.I.X k)).2 (m.injective k)
  let l := raisedResolution.{a,u,r} R m q j
  let h := flasqueRow.{a,u,r} R V W m.I
    (fun k ↦ original_injectives_flasque.{a,u,r} X R _ (m.injective k))
  let h' := MayerVietoris.complexesExact (liftedRing.{a} R) V W (kLift.{a,u,r} R m.I) j
  let e := comparison.{a,u,r} R V W m
  refine ⟨q, j, h', h, e, fun _ _ _ ↦ rfl, ?_⟩
  intro n
  let site (T : Open.{a,u,r} (X := X)) (hT : T ≤ U) (k : ℕ) :=
    (localSiteComparison.{a,u,r} R U T hT (s T) k).app M
  let x (T : Open.{a,u,r} (X := X)) (hT : T ≤ U) (k : ℕ) :=
    ((K.{a,u,r} R U T hT m.I).sc (k : ℤ)).mapHomologyIso S
  let common (T : Open.{a,u,r} (X := X)) (hT : T ≤ U) (k : ℕ) :=
    commonModelIso.{a,u,r} R V W l T hT k
  let commonU (k : ℕ) := commonUnionIso.{a,u,r} R V W l k
  have hl (T : Open.{a,u,r} (X := X)) (hT : T ≤ U) (k : ℕ) :
      (x T hT k).hom ≫ S.map (e T hT k).hom ≫ (site T hT k).hom =
        (common T hT k).hom :=
    site_model_square.{a,u,r} R U T hT (s T) (hs T) m q j k
  have hu (k : ℕ) :
      (x U le_rfl k).hom ≫ S.map (eA.{a,u,r} R V W m e k).hom ≫ (s U k).hom.app M =
        (commonU k).hom :=
    union_site_model_square.{a,u,r} R V W (s U) (hs U) m q j k
  let origRes (T P : Open.{a,u,r} (X := X)) (hT : T ≤ U) (hP : P ≤ U) (hPT : P ≤ T) :=
    homologyMap (kRes.{a,u,r} R U T P hT hP hPT m.I) (n : ℤ)
  let raisedRes (T P : Open.{a,u,r} (X := X)) (hT : T ≤ U) (hP : P ≤ U) (hPT : P ≤ T) :=
    homologyMap (commonRes.{a,u,r} R V W l T P hT hP hPT) (n : ℤ)
  have fromUnion (T : Open.{a,u,r} (X := X)) (hT : T ≤ U) :
      S.map ((eA.{a,u,r} R V W m e n).inv ≫ origRes U T le_rfl hT hT ≫ (e T hT n).hom) ≫
        (site T hT n).hom =
      (s U n).hom.app M ≫ ((commonU n).inv ≫ raisedRes U T le_rfl hT hT ≫ (common T hT n).hom) :=
    mapped_conjugate_square S (eA.{a,u,r} R V W m e n) (e T hT n) (commonU n) (common T hT n)
      (x U le_rfl n) (x T hT n) ((s U n).app M) (site T hT n)
      (origRes U T le_rfl hT hT) (raisedRes U T le_rfl hT hT) (hu n) (hl T hT n)
      (homology_restriction_transport.{a,u,r} R U U T le_rfl hT hT m.I (n : ℤ))
  have toIntersection (T : Open.{a,u,r} (X := X)) (hT : T ≤ U) (hDT : D ≤ T) :
      S.map ((e T hT n).inv ≫ origRes T D hT hD hDT ≫ (e D hD n).hom) ≫ (site D hD n).hom =
      (site T hT n).hom ≫ ((common T hT n).inv ≫ raisedRes T D hT hD hDT ≫ (common D hD n).hom) :=
    mapped_conjugate_square S (e T hT n) (e D hD n) (common T hT n) (common D hD n)
      (x T hT n) (x D hD n) (site T hT n) (site D hD n)
      (origRes T D hT hD hDT) (raisedRes T D hT hD hDT) (hl T hT n) (hl D hD n)
      (homology_restriction_transport.{a,u,r} R U T D hT hD hDT m.I (n : ℤ))
  have hα := mapped_lift_square S ((s U n).app M) (site V le_sup_left n) (site W le_sup_right n)
    (fromUnion V le_sup_left) (fromUnion W le_sup_right)
  have hβ := mapped_difference_square S (site V le_sup_left n) (site W le_sup_right n) (site D hD n)
    (toIntersection V le_sup_left inf_le_left) (toIntersection W le_sup_right inf_le_right)
  let next : ℤ := ((n + 1 : ℕ) : ℤ)
  have hnext : (n : ℤ) + 1 = next := by
    dsimp only [next]
    omega
  have boundaryAt (k : ℤ) (hk : (n : ℤ) + 1 = k) :
      h'.δ (n : ℤ) k (ComplexShape.up_mk _ _ hk) ≫
          (((A.{a,u,r} R V W m.I).sc k).mapHomologyIso S).hom =
        (x D hD n).hom ≫ S.map (h.δ (n : ℤ) k (ComplexShape.up_mk _ _ hk)) := by
    subst k
    exact modelBoundaryTransport.{a,u,r} R V W m.I h h' (n : ℤ)
  have hδ := mapped_conjugate_square S (e D hD n) (eA.{a,u,r} R V W m e (n + 1)) (common D hD n)
    (commonU (n + 1)) (x D hD n) (x U le_rfl (n + 1)) (site D hD n) ((s U (n + 1)).app M)
    (h.δ (n : ℤ) next (ComplexShape.up_mk _ _ hnext))
    (h'.δ (n : ℤ) next (ComplexShape.up_mk _ _ hnext))
    (hl D hD n) (hu (n + 1)) (boundaryAt next hnext)
  refine ⟨?_, ?_, ?_⟩
  · unfold alpha commonAlpha
    exact hα
  · unfold beta commonBeta
    exact hβ
  · unfold delta commonDelta
    exact hδ

end AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients

namespace AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients

open Specs.AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients
open AdvancedHomologicalAlgebra.MayerVietorisData

theorem commonMaps : commonMapsType.{a,u,r} := by
  intro X R V W l h' N n
  refine ⟨?_, ?_, ?_⟩
  · apply biprod.hom_ext
    · simp only [commonAlpha, commonUnionIso, commonModelIso, directAlpha, cohomologyAlpha,
        cohomologyRestriction, cohomologyComparison, Iso.trans_inv, Iso.symm_inv, Iso.symm_hom,
        Iso.app_inv, Category.assoc, biprod.lift_fst]
      erw [biprod.lift_fst]
    · simp only [commonAlpha, commonUnionIso, commonModelIso, directAlpha, cohomologyAlpha,
        cohomologyRestriction, cohomologyComparison, Iso.trans_inv, Iso.symm_inv, Iso.symm_hom,
        Iso.app_inv, Category.assoc, biprod.lift_snd]
      erw [biprod.lift_snd]
  · rfl
  · simp only [commonDelta, commonUnionIso, commonModelIso, directDelta, cohomologyDelta,
      cohomologyComparison, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, Iso.app_hom, Category.assoc]

end AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients

namespace AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients

open Specs.AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients

theorem coefficientNaturalSequence : coefficientNaturalSequenceType.{a,u,r} := by
  intro X R V W
  letI hInj := SheafCohomologyOriginalCoefficients.enoughInjectives.{a,u,r} R
  let L := coefficientLift.{a,u,r} R
  obtain ⟨m, h, e, he, hm, hx, hn⟩ := naturalSequence.{a,u,r} (X := X) R V W
  exact ⟨hInj, fun M ↦ m (L.obj M), fun M ↦ h (L.obj M), fun M ↦ e (L.obj M),
    fun M ↦ he (L.obj M), fun M ↦ hm (L.obj M), fun M ↦ hx (L.obj M),
    fun M N f n ↦ hn (L.obj M) (L.obj N) (L.map f) n⟩

end AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients

namespace AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients

open Specs.AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients
open HomologicalComplex

private lemma mono_augmentation {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
    {M : AmbientSheaves.{a} R} (m : Resolution.{a,u,r} R M) : Mono m.i := by
  letI := m.quasiIso
  apply HomologicalComplex.mono_of_mono_f
  intro q
  by_cases hq : q = 0
  · subst q
    haveI : Mono (m.i.f (0 + 1)) :=
      (isZero_single_obj_X (.up ℤ) 0 M (0 + 1) (by decide)).mono _
    exact InjectiveComplexReplacement.mono_at_lower_bound m.i 0
  · exact (isZero_single_obj_X (.up ℤ) 0 M q hq).mono _

theorem modelIndependence : modelIndependenceType.{a,u,r} := by
  intro X R V W _ M m l h h' e e' he he' n
  have em : e = comparison.{a,u,r} R V W m := by
    funext T hT k
    apply Iso.ext
    exact he T hT k
  have el : e' = comparison.{a,u,r} R V W l := by
    funext T hT k
    apply Iso.ext
    exact he' T hT k
  subst e
  subst e'
  letI := m.bounded
  letI := l.bounded
  letI := m.quasiIso
  letI := mono_augmentation R m
  obtain ⟨φ, hφ⟩ := SheafCohomology.injectiveResolutionLift m.i l.i l.injective
  have hφ' : m.i ≫ φ =
      (CochainComplex.singleFunctor (AmbientSheaves.{a} R) 0).map (𝟙 M) ≫ l.i := by
    rw [(CochainComplex.singleFunctor (AmbientSheaves.{a} R) 0).map_id, Category.id_comp]
    exact hφ
  have unionMapId (k : ℕ) :
      (cohomologyValue.{a} R (originalOpen.{a,u,r} (V ⊔ W)) k).map (𝟙 M) = 𝟙 _ :=
    (cohomologyValue.{a} R (originalOpen.{a,u,r} (V ⊔ W)) k).map_id M
  have localMapId (T : Open.{a,u,r} (X := X)) (hT : T ≤ V ⊔ W) :
      (H.{a,u,r} R (V ⊔ W) T hT n).map (𝟙 M) = 𝟙 _ :=
    (H.{a,u,r} R (V ⊔ W) T hT n).map_id M
  have id_biprod {P Q : Sections.{a,u,r} R (V ⊔ W)} :
      biprod.map (𝟙 P) (𝟙 Q) = 𝟙 (P ⊞ Q) := by
    apply biprod.hom_ext <;> simp
  refine ⟨?_, ?_, ?_⟩
  · have hα := alpha_naturality.{a,u,r} R V W m l (𝟙 M) φ hφ' n
    rw [unionMapId n, localMapId V le_sup_left, localMapId W le_sup_right,
      id_biprod, Category.id_comp, Category.comp_id] at hα
    exact hα.symm
  · have hβ := beta_naturality.{a,u,r} R V W m l (𝟙 M) φ hφ' n
    rw [localMapId V le_sup_left, localMapId W le_sup_right,
      localMapId (V ⊓ W) (inf_le_left.trans le_sup_left),
      id_biprod, Category.id_comp, Category.comp_id] at hβ
    exact hβ.symm
  · have hδ := delta_naturality.{a,u,r} R V W m l (𝟙 M) φ hφ' h h' n
    rw [localMapId (V ⊓ W) (inf_le_left.trans le_sup_left), unionMapId (n + 1),
      Category.id_comp, Category.comp_id] at hδ
    exact hδ.symm

end AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients

/-! Coefficient enlargement and naturality for independently sized sheaves. -/

universe b c v w

set_option maxHeartbeats 2400000

namespace AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients

open Specs.AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients
open CategoryTheory.Functor HomologicalComplex

private local instance uliftPreservesBinaryBiproducts (S : Type r) [Ring S] :
    PreservesBinaryBiproducts (ModuleCat.uliftFunctor.{a,b} S) :=
  preservesBinaryBiproducts_of_preservesBinaryProducts _

section SectionPairs

variable {S : Type r} [Ring S]
  {B C : ModuleCat.{b} S} {B' C' : ModuleCat.{c} S} {B'' C'' : ModuleCat.{v} S}

private lemma biprod_element_ext {x y : ↥(B ⊞ C)}
    (hB : (biprod.fst : B ⊞ C ⟶ B) x = (biprod.fst : B ⊞ C ⟶ B) y)
    (hC : (biprod.snd : B ⊞ C ⟶ C) x = (biprod.snd : B ⊞ C ⟶ C) y) : x = y := by
  have h := congrArg (fun g : B ⊞ C ⟶ B ⊞ C ↦ g x) (biprod.total (X := B) (Y := C))
  have h' := congrArg (fun g : B ⊞ C ⟶ B ⊞ C ↦ g y) (biprod.total (X := B) (Y := C))
  change (biprod.inl : B ⟶ B ⊞ C) ((biprod.fst : B ⊞ C ⟶ B) x) +
    (biprod.inr : C ⟶ B ⊞ C) ((biprod.snd : B ⊞ C ⟶ C) x) = x at h
  change (biprod.inl : B ⟶ B ⊞ C) ((biprod.fst : B ⊞ C ⟶ B) y) +
    (biprod.inr : C ⟶ B ⊞ C) ((biprod.snd : B ⊞ C ⟶ C) y) = y at h'
  rw [hB, hC] at h
  exact h.symm.trans h'

@[simp]
private lemma pairMap_fst (p : B → B') (q : C → C') (x : ↥(B ⊞ C)) :
    (biprod.fst : B' ⊞ C' ⟶ B') (pairMap p q x) = p ((biprod.fst : B ⊞ C ⟶ B) x) := by
  unfold pairMap
  rw [_root_.map_add]
  change (biprod.inl ≫ biprod.fst : B' ⟶ B') (p ((biprod.fst : B ⊞ C ⟶ B) x)) +
    (biprod.inr ≫ biprod.fst : C' ⟶ B') (q ((biprod.snd : B ⊞ C ⟶ C) x)) = _
  rw [biprod.inl_fst, biprod.inr_fst]
  exact add_zero _

@[simp]
private lemma pairMap_snd (p : B → B') (q : C → C') (x : ↥(B ⊞ C)) :
    (biprod.snd : B' ⊞ C' ⟶ C') (pairMap p q x) = q ((biprod.snd : B ⊞ C ⟶ C) x) := by
  unfold pairMap
  rw [_root_.map_add]
  change (biprod.inl ≫ biprod.snd : B' ⟶ C') (p ((biprod.fst : B ⊞ C ⟶ B) x)) +
    (biprod.inr ≫ biprod.snd : C' ⟶ C') (q ((biprod.snd : B ⊞ C ⟶ C) x)) = _
  rw [biprod.inl_snd, biprod.inr_snd]
  exact zero_add _

private lemma pairMap_injective {p : B → B'} {q : C → C'}
    (hp : Function.Injective p) (hq : Function.Injective q) :
    Function.Injective (pairMap p q) := by
  intro x y h
  apply biprod_element_ext
  · exact hp (by simpa only [pairMap_fst] using congrArg (fun z ↦ (biprod.fst : B' ⊞ C' ⟶ B') z) h)
  · exact hq (by simpa only [pairMap_snd] using congrArg (fun z ↦ (biprod.snd : B' ⊞ C' ⟶ C') z) h)

private lemma pairMap_naturality
    (p : B → B') (q : C → C') (p' : B' → B'') (q' : C' → C'')
    {B₀ C₀ : ModuleCat.{w} S}
    (p₀ : B → B₀) (q₀ : C → C₀) (p₁ : B₀ → B'') (q₁ : C₀ → C'')
    (hB : ∀ x, p' (p x) = p₁ (p₀ x)) (hC : ∀ x, q' (q x) = q₁ (q₀ x))
    (x : ↥(B ⊞ C)) :
    pairMap p' q' (pairMap p q x) = pairMap p₁ q₁ (pairMap p₀ q₀ x) := by
  apply biprod_element_ext
  · simpa only [pairMap_fst] using hB ((biprod.fst : B ⊞ C ⟶ B) x)
  · simpa only [pairMap_snd] using hC ((biprod.snd : B ⊞ C ⟶ C) x)

private lemma pairMap_of_biprodMap {B' C' : ModuleCat.{b} S} (p : B ⟶ B') (q : C ⟶ C') (x : ↥(B ⊞ C)) :
    pairMap (fun x ↦ p x) (fun y ↦ q y) x = (biprod.map p q) x := by
  apply biprod_element_ext
  · rw [pairMap_fst]
    change _ = (biprod.map p q ≫ biprod.fst : B ⊞ C ⟶ B') x
    rw [biprod.map_fst]
    rfl
  · rw [pairMap_snd]
    change _ = (biprod.map p q ≫ biprod.snd : B ⊞ C ⟶ C') x
    rw [biprod.map_snd]
    rfl

private lemma pairMap_of_lift {B' C' : ModuleCat.{max a b} S}
    (p : (ModuleCat.uliftFunctor.{a,b} S).obj B ≅ B')
    (q : (ModuleCat.uliftFunctor.{a,b} S).obj C ≅ C') (x : ↥(B ⊞ C)) :
    pairMap (fun x ↦ p.hom (ULift.up x)) (fun y ↦ q.hom (ULift.up y)) x =
      ((ModuleCat.uliftFunctor.{a,b} S).mapBiprod B C ≪≫ biprod.mapIso p q).hom (ULift.up x) := by
  apply biprod_element_ext
  · rw [pairMap_fst]
    change _ = (((ModuleCat.uliftFunctor.{a,b} S).mapBiprod B C ≪≫ biprod.mapIso p q).hom ≫
      biprod.fst : (ModuleCat.uliftFunctor.{a,b} S).obj (B ⊞ C) ⟶ B') (ULift.up x)
    simp only [Iso.trans_hom, Category.assoc, biprod.mapIso_hom, biprod.map_fst, Functor.mapBiprod_hom]
    rw [biprod.lift_fst_assoc]
    rfl
  · rw [pairMap_snd]
    change _ = (((ModuleCat.uliftFunctor.{a,b} S).mapBiprod B C ≪≫ biprod.mapIso p q).hom ≫
      biprod.snd : (ModuleCat.uliftFunctor.{a,b} S).obj (B ⊞ C) ⟶ C') (ULift.up x)
    simp only [Iso.trans_hom, Category.assoc, biprod.mapIso_hom, biprod.map_snd, Functor.mapBiprod_hom]
    rw [biprod.lift_snd_assoc]
    rfl

end SectionPairs

private abbrev liftedLE {X : TopCat.{u}} {T U : Opens X} (h : T ≤ U) :
    liftedOpen.{a,u,r} T ≤ liftedOpen.{a,u,r} U :=
  (opensEquiv X).symm.monotone h

section Enlarge

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})

private lemma enlarge_restriction (U T P : Opens X) (hT : T ≤ U) (hP : P ≤ U) (h : P ≤ T)
    (I : CochainComplex (AmbientSheaves.{b} R) ℤ) :
    ((enlargeSection.{a,u,r,b} R U).mapHomologicalComplex (.up ℤ)).map
        (kRes.{b,u,r} R (liftedOpen.{b,u,r} U) (liftedOpen.{b,u,r} T) (liftedOpen.{b,u,r} P)
          (liftedLE.{b,u,r} hT) (liftedLE.{b,u,r} hP) (liftedLE.{b,u,r} h) I) =
      kRes.{max a b,u,r} R (liftedOpen.{max a b,u,r} U) (liftedOpen.{max a b,u,r} T)
        (liftedOpen.{max a b,u,r} P) (liftedLE.{max a b,u,r} hT) (liftedLE.{max a b,u,r} hP)
        (liftedLE.{max a b,u,r} h) (enlargeComplex.{a,u,r,b} R I) := by
  ext n x
  rfl

private def enlargedRowIso (V W : Opens X) (I : CochainComplex (AmbientSheaves.{b} R) ℤ) :
    (row.{b,u,r} R (liftedOpen.{b,u,r} V) (liftedOpen.{b,u,r} W) I).map
      ((enlargeSection.{a,u,r,b} R (V ⊔ W)).mapHomologicalComplex (.up ℤ)) ≅
        row.{max a b,u,r} R (liftedOpen.{max a b,u,r} V) (liftedOpen.{max a b,u,r} W)
          (enlargeComplex.{a,u,r,b} R I) := by
  let L := (enlargeSection.{a,u,r,b} R (V ⊔ W)).mapHomologicalComplex (.up ℤ)
  letI := preservesBinaryBiproducts_of_preservesBinaryProducts L
  refine ShortComplex.isoMk (Iso.refl _) (L.mapBiprod _ _) (Iso.refl _) ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp, ShortComplex.map_f, row]
    rw [biprod.map_lift_mapBiprod]
    exact congrArg₂ biprod.lift
      (enlarge_restriction.{a,u,r,b} R (V ⊔ W) (V ⊔ W) V le_rfl le_sup_left le_sup_left I).symm
      (enlarge_restriction.{a,u,r,b} R (V ⊔ W) (V ⊔ W) W le_rfl le_sup_right le_sup_right I).symm
  · simp only [Iso.refl_hom, Category.comp_id, ShortComplex.map_g, row]
    rw [← biprod.mapBiprod_hom_desc, L.map_neg]
    apply congrArg (fun g ↦ (L.mapBiprod _ _).hom ≫ g)
    exact congrArg₂ biprod.desc
      (enlarge_restriction.{a,u,r,b} R (V ⊔ W) V (V ⊓ W) le_sup_left
        (inf_le_left.trans le_sup_left) inf_le_left I).symm
      (congrArg Neg.neg (enlarge_restriction.{a,u,r,b} R (V ⊔ W) W (V ⊓ W) le_sup_right
        (inf_le_left.trans le_sup_left) inf_le_right I)).symm

private lemma enlargeSectionHomologyIso_hom (U T : Opens X) (h : T ≤ U)
    (I : CochainComplex (AmbientSheaves.{b} R) ℤ) (n : ℤ) :
    (enlargeSectionHomologyIso.{a,u,r,b} R U T h I n).hom =
      (((K.{b,u,r} R (liftedOpen.{b,u,r} U) (liftedOpen.{b,u,r} T)
        (liftedLE.{b,u,r} h) I).sc n).mapHomologyIso (enlargeSection.{a,u,r,b} R U)).inv := by
  simp only [enlargeSectionHomologyIso, enlargeSectionComplexIso, Functor.mapIso_refl, Iso.trans_hom,
    Iso.refl_hom, Iso.symm_hom]
  exact Category.comp_id _

private lemma enlarge_boundary (V W : Opens X) (I : CochainComplex (AmbientSheaves.{b} R) ℤ)
    (h : (row.{b,u,r} R (liftedOpen.{b,u,r} V) (liftedOpen.{b,u,r} W) I).ShortExact)
    (h' : (row.{max a b,u,r} R (liftedOpen.{max a b,u,r} V) (liftedOpen.{max a b,u,r} W)
      (enlargeComplex.{a,u,r,b} R I)).ShortExact) (n : ℤ) :
    (enlargeSection.{a,u,r,b} R (V ⊔ W)).map (h.δ n (n + 1) rfl) ≫
        (enlargeSectionHomologyIso.{a,u,r,b} R (V ⊔ W) (V ⊔ W) le_rfl I (n + 1)).hom =
      (enlargeSectionHomologyIso.{a,u,r,b} R (V ⊔ W) (V ⊓ W)
        (inf_le_left.trans le_sup_left) I n).hom ≫ h'.δ n (n + 1) rfl := by
  let S := enlargeSection.{a,u,r,b} R (V ⊔ W)
  let L := S.mapHomologicalComplex (.up ℤ)
  let T := row.{b,u,r} R (liftedOpen.{b,u,r} V) (liftedOpen.{b,u,r} W) I
  let hL := h.map_of_exact L
  let e := enlargedRowIso.{a,u,r,b} R V W I
  have hδ := HomologySequence.δ_naturality e.hom hL h' n (n + 1) rfl
  change hL.δ n (n + 1) rfl ≫ homologyMap (𝟙 _) (n + 1) =
    homologyMap (𝟙 _) n ≫ h'.δ n (n + 1) rfl at hδ
  rw [homologyMap_id, homologyMap_id, Category.comp_id, Category.id_comp] at hδ
  have hc := map_connecting S T h hL n
  rw [hδ] at hc
  let e₁ := (T.X₁.sc (n + 1)).mapHomologyIso S
  let e₃ := (T.X₃.sc n).mapHomologyIso S
  change h'.δ n (n + 1) rfl ≫ e₁.hom = e₃.hom ≫ S.map (h.δ n (n + 1) rfl) at hc
  rw [enlargeSectionHomologyIso_hom, enlargeSectionHomologyIso_hom]
  change S.map (h.δ n (n + 1) rfl) ≫ e₁.inv = e₃.inv ≫ h'.δ n (n + 1) rfl
  apply (cancel_epi e₃.hom).mp
  rw [← Category.assoc e₃.hom, ← hc, Category.assoc, e₁.hom_inv_id, e₃.hom_inv_id_assoc]
  exact Category.comp_id _

private abbrev enlargedModelArrow (U T : Opens X) (h : T ≤ U)
    {I : CochainComplex (AmbientSheaves.{b} R) ℤ} {K' : CochainComplex (AmbientSheaves.{max a b} R) ℤ}
    (φ : enlargeComplex.{a,u,r,b} R I ⟶ K') (n : ℤ) :=
  (enlargeSectionHomologyIso.{a,u,r,b} R U T h I n).hom ≫
    homologyMap (((E.{max a b,u,r} R (liftedOpen.{max a b,u,r} U)
      (liftedOpen.{max a b,u,r} T) (liftedLE.{max a b,u,r} h)).mapHomologicalComplex (.up ℤ)).map φ) n

private lemma enlargedModelArrow_restriction (U T P : Opens X)
    (hT : T ≤ U) (hP : P ≤ U) (h : P ≤ T)
    {I : CochainComplex (AmbientSheaves.{b} R) ℤ} {K' : CochainComplex (AmbientSheaves.{max a b} R) ℤ}
    (φ : enlargeComplex.{a,u,r,b} R I ⟶ K') (n : ℤ) :
    (enlargeSection.{a,u,r,b} R U).map
        (homologyMap (kRes.{b,u,r} R (liftedOpen.{b,u,r} U) (liftedOpen.{b,u,r} T)
          (liftedOpen.{b,u,r} P) (liftedLE.{b,u,r} hT) (liftedLE.{b,u,r} hP) (liftedLE.{b,u,r} h) I) n) ≫
      enlargedModelArrow.{a,u,r,b} R U P hP φ n =
    enlargedModelArrow.{a,u,r,b} R U T hT φ n ≫
      homologyMap (kRes.{max a b,u,r} R (liftedOpen.{max a b,u,r} U) (liftedOpen.{max a b,u,r} T)
        (liftedOpen.{max a b,u,r} P) (liftedLE.{max a b,u,r} hT) (liftedLE.{max a b,u,r} hP)
        (liftedLE.{max a b,u,r} h) K') n := by
  let S := enlargeSection.{a,u,r,b} R U
  let f := kRes.{b,u,r} R (liftedOpen.{b,u,r} U) (liftedOpen.{b,u,r} T) (liftedOpen.{b,u,r} P)
    (liftedLE.{b,u,r} hT) (liftedLE.{b,u,r} hP) (liftedLE.{b,u,r} h) I
  have hmap := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) n).map f) S
  change S.map (homologyMap f n) ≫ _ =
    _ ≫ homologyMap ((S.mapHomologicalComplex (.up ℤ)).map f) n at hmap
  have hnat := ((res.{max a b,u,r} R (liftedOpen.{max a b,u,r} U) (liftedOpen.{max a b,u,r} T)
    (liftedOpen.{max a b,u,r} P) (liftedLE.{max a b,u,r} hT) (liftedLE.{max a b,u,r} hP)
    (liftedLE.{max a b,u,r} h)).mapHomologicalComplex (.up ℤ)).naturality φ
  simp only [enlargedModelArrow, enlargeSectionHomologyIso_hom, Category.assoc]
  change S.map (homologyMap f n) ≫ _ = _
  rw [reassoc_of% hmap]
  rw [enlarge_restriction.{a,u,r,b} R U T P hT hP h I, ← homologyMap_comp, ← homologyMap_comp]
  rw [hnat]

variable [EnoughInjectives (AmbientSheaves.{b} R)] [EnoughInjectives (AmbientSheaves.{max a b} R)]

private def enlargedValueIso (U T : Opens X) (h : T ≤ U) (M : SheafOfModules.{b} R)
    (s : IndividualCohomologyComparison.{a,u,r,b} X R T) (n : ℕ) :
    (enlargeSection.{a,u,r,b} R U).obj
      ((H.{b,u,r} R (liftedOpen.{b,u,r} U) (liftedOpen.{b,u,r} T) (liftedLE.{b,u,r} h) n).obj
        ((coefficientLift.{b,u,r} R).obj M)) ≅
      (H.{max a b,u,r} R (liftedOpen.{max a b,u,r} U) (liftedOpen.{max a b,u,r} T)
        (liftedLE.{max a b,u,r} h) n).obj ((commonCoefficientLift.{a,u,r,b} R).obj M) :=
  (Sc.{max a b,u,r} R (liftedOpen.{max a b,u,r} U) (liftedOpen.{max a b,u,r} T)
    (liftedLE.{max a b,u,r} h)).mapIso ((s n).app M)

set_option maxHeartbeats 4000000 in
private lemma enlarged_model_square (V W T : Opens X) (hT : T ≤ V ⊔ W)
    (M : SheafOfModules.{b} R)
    (m : SequenceModel.{u,r,b} R V W ((coefficientLift.{b,u,r} R).obj M))
    (l : SequenceModel.{u,r,max a b} R V W ((commonCoefficientLift.{a,u,r,b} R).obj M))
    (k : (enlargeCoefficients.{a,u,r,b} R).obj ((coefficientLift.{b,u,r} R).obj M) ≅
      (commonCoefficientLift.{a,u,r,b} R).obj M)
    (hk : ∀ (P : (Opens X)ᵒᵖ) (x : (enlargeCoefficients.{a,u,r,b} R |>.obj
      ((coefficientLift.{b,u,r} R).obj M)).val.obj P), k.hom.val.app P x = ULift.up x.down.down)
    (φ : enlargeComplex.{a,u,r,b} R m.resolution.I ⟶ l.resolution.I)
    (q : QuasiIso (mapAugmentation (enlargeCoefficients.{a,u,r,b} R) m.resolution.i))
    (hφ : mapAugmentation (enlargeCoefficients.{a,u,r,b} R) m.resolution.i ≫ φ =
      (CochainComplex.singleFunctor (AmbientSheaves.{max a b} R) 0).map k.hom ≫ l.resolution.i)
    (s : IndividualCohomologyComparison.{a,u,r,b} X R T)
    (hs : IsIndividualCohomologyComparison X R T s) (n : ℕ) :
    (enlargeSection.{a,u,r,b} R (V ⊔ W)).map
        (m.comparison (liftedOpen.{b,u,r} T) (liftedLE.{b,u,r} hT) n).hom ≫
      (enlargedValueIso.{a,u,r,b} R (V ⊔ W) T hT M s n).hom =
    enlargedModelArrow.{a,u,r,b} R (V ⊔ W) T hT φ (n : ℤ) ≫
      (l.comparison (liftedOpen.{max a b,u,r} T) (liftedLE.{max a b,u,r} hT) n).hom := by
  let U := V ⊔ W
  let J := enlargeCoefficients.{a,u,r,b} R
  let M₁ := (coefficientLift.{b,u,r} R).obj M
  let I := m.resolution.I
  let I' : CochainComplex (AmbientSheaves.{max a b} R) ℤ := enlargeComplex.{a,u,r,b} R I
  let Q := l.resolution.I
  let i' := mapAugmentation J m.resolution.i
  let j := l.resolution.i
  letI : I.IsStrictlyGE 0 := m.resolution.bounded
  letI : I'.IsStrictlyGE 0 := inferInstance
  letI : Q.IsStrictlyGE 0 := l.resolution.bounded
  let F := sectionsValue.{b} R T
  let G := sectionsValue.{max a b} R T
  let S := enlargeSection.{a,u,r,b} R U
  let L := enlargeSection.{a,u,r,b} R T
  let G₁ := Sc.{b,u,r} R (liftedOpen.{b,u,r} U) (liftedOpen.{b,u,r} T) (liftedLE.{b,u,r} hT)
  let G₂ := Sc.{max a b,u,r} R (liftedOpen.{max a b,u,r} U) (liftedOpen.{max a b,u,r} T)
    (liftedLE.{max a b,u,r} hT)
  let P := (F.mapHomologicalComplex (.up ℤ)).obj I
  let P' := (G.mapHomologicalComplex (.up ℤ)).obj I'
  let Q' := (G.mapHomologicalComplex (.up ℤ)).obj Q
  let g := (G.mapHomologicalComplex (.up ℤ)).map φ
  let p := resolutionModelMap F m.resolution.i m.resolution.quasiIso n
  let p' := resolutionModelMap G i' q n
  let t := resolutionModelMap G j l.resolution.quasiIso n
  let a₁ := (P.sc (n : ℤ)).mapHomologyIso G₁
  let a₂ := (P'.sc (n : ℤ)).mapHomologyIso G₂
  let a₃ := (Q'.sc (n : ℤ)).mapHomologyIso G₂
  let b₁ := (P.sc (n : ℤ)).mapHomologyIso L
  let d := (((G₁.mapHomologicalComplex (.up ℤ)).obj P).sc (n : ℤ)).mapHomologyIso S
  obtain ⟨kT, e, hkT, he, _, hs⟩ := hs
  have hkT' : kT.hom.app M = k.hom := by
    apply SheafOfModules.hom_ext
    ext P x
    exact (hkT M P x).trans (hk P x).symm
  obtain ⟨qT, hmodel⟩ := he M₁ I m.resolution.i m.resolution.quasiIso m.resolution.injective
  have he' : L.map p ≫ (e n).hom.app M₁ = b₁.inv ≫ p' := by
    let eqv : F ⋙ L ≅ J ⋙ G := Iso.refl _
    have h := hmodel n
    change L.map p ≫ (e n).hom.app M₁ = (modelComparison F G J L eqv I n).hom ≫ p' at h
    have hid : (NatIso.mapHomologicalComplex eqv (.up ℤ)).hom.app I = 𝟙 P' := by
      ext z x
      rfl
    have hm : (modelComparison F G J L eqv I n).hom = b₁.inv := by
      change b₁.inv ≫ homologyMap ((NatIso.mapHomologicalComplex eqv (.up ℤ)).hom.app I) (n : ℤ) = _
      rw [hid]
      exact (congrArg (fun f ↦ b₁.inv ≫ f) (homologyMap_id P' (n : ℤ))).trans
        (Category.comp_id _)
    exact h.trans (congrArg (fun f ↦ f ≫ p') hm)
  have hn : p' ≫ (cohomologyValue.{max a b} R T n).map k.hom = homologyMap g (n : ℤ) ≫ t :=
    SheafCohomologyOriginalCoefficients.resolutionNaturality.{max a b,u,r}
      R T i' q j l.resolution.quasiIso k.hom φ hφ n
  have hT' : L.map p ≫ (s n).hom.app M =
      b₁.inv ≫ homologyMap g (n : ℤ) ≫ t := by
    rw [hs M n, hkT', ← Category.assoc, he', Category.assoc]
    exact congrArg (fun f ↦ b₁.inv ≫ f) hn
  have hcomp : d.hom ≫ S.map a₁.hom = a₂.hom ≫ G₂.map b₁.hom :=
    (homologyIso_comp G₁ S P (n : ℤ)).trans (homologyIso_comp L G₂ P (n : ℤ)).symm
  rw [m.normalized, l.normalized]
  simp only [enlargedModelArrow, enlargeSectionHomologyIso_hom]
  change S.map (a₁.hom ≫ G₁.map p) ≫ G₂.map ((s n).hom.app M) =
    (d.inv ≫ homologyMap ((G₂.mapHomologicalComplex (.up ℤ)).map g) (n : ℤ)) ≫
      (a₃.hom ≫ G₂.map t)
  apply (cancel_epi d.hom).mp
  simp only [S.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  calc
    _ = (d.hom ≫ S.map a₁.hom) ≫ S.map (G₁.map p) ≫ G₂.map ((s n).hom.app M) :=
      (Category.assoc _ _ _).symm
    _ = a₂.hom ≫ G₂.map (b₁.hom ≫ L.map p ≫ (s n).hom.app M) := by
      rw [hcomp]
      simp only [G₂.map_comp, Category.assoc]
      rfl
    _ = _ := by
      rw [hT', Iso.hom_inv_id_assoc, G₂.map_comp]
      exact (homologyIso_naturality_assoc G₂ g (n : ℤ) (G₂.map t)).symm

private lemma map_conjugate_square {P Q : Type*} [Category* P] [Category* Q]
    (F : P ⥤ Q) {X Y H K : P} {X' Y' H' K' : Q}
    (e : X ≅ H) (f : Y ≅ K) (e' : X' ≅ H') (f' : Y' ≅ K')
    (a : X ⟶ Y) (a' : X' ⟶ Y')
    {p : F.obj X ⟶ X'} {q : F.obj Y ⟶ Y'} {s : F.obj H ⟶ H'} {t : F.obj K ⟶ K'}
    (he : F.map e.hom ≫ s = p ≫ e'.hom) (hf : F.map f.hom ≫ t = q ≫ f'.hom)
    (h : F.map a ≫ q = p ≫ a') :
    F.map (e.inv ≫ a ≫ f.hom) ≫ t = s ≫ (e'.inv ≫ a' ≫ f'.hom) := by
  simpa only [Functor.map_comp, Functor.mapIso_inv, Functor.mapIso_hom, Category.assoc] using
    (naturality_of_conjugate (F.mapIso e) (F.mapIso f) e' f' he hf h.symm).symm

end Enlarge

set_option maxHeartbeats 6000000 in
/-- Compare the native row with the common injective model through the
coefficient lift, preserving the augmentation and the ordinary connector. -/
theorem coefficientModelEnlargement : coefficientModelEnlargementType.{a,u,r,b} := by
  intro X R V W _ _ s hs M m l
  dsimp only
  let U := V ⊔ W
  let D := V ⊓ W
  let hD : D ≤ U := inf_le_left.trans le_sup_left
  let V₁ := liftedOpen.{b,u,r} V
  let W₁ := liftedOpen.{b,u,r} W
  let V₂ := liftedOpen.{max a b,u,r} V
  let W₂ := liftedOpen.{max a b,u,r} W
  let J := enlargeCoefficients.{a,u,r,b} R
  let I := m.resolution.I
  let I' : CochainComplex (AmbientSheaves.{max a b} R) ℤ := enlargeComplex.{a,u,r,b} R I
  let S := enlargeSection.{a,u,r,b} R U
  let L := S.mapHomologicalComplex (.up ℤ)
  letI := preservesBinaryBiproducts_of_preservesBinaryProducts L
  let e := enlargedRowIso.{a,u,r,b} R V W I
  let row₂ := row.{max a b,u,r} R V₂ W₂ I'
  let M₁ := (coefficientLift.{b,u,r} R).obj M
  let N := (commonCoefficientLift.{a,u,r,b} R).obj M
  let Γ := CochainComplex.singleFunctor (AmbientSheaves.{max a b} R) 0
  let iJ := mapAugmentation J m.resolution.i
  letI : I.IsStrictlyGE 0 := m.resolution.bounded
  letI : I'.IsStrictlyGE 0 := inferInstance
  letI := l.resolution.bounded
  obtain ⟨kU, eU, hkU, hres, _, _⟩ := hs U
  let k := kU.app M
  obtain ⟨hqJ, _⟩ := hres M₁ I m.resolution.i m.resolution.quasiIso m.resolution.injective
  letI : QuasiIso iJ := hqJ
  let i := Γ.map k.inv ≫ iJ
  have hJ := coefficient_lift_ambient_sheaf_exact.{a,u,r,b} X R
  letI : PreservesFiniteLimits J := hJ.1
  letI : Mono m.resolution.i := mono_augmentation R m.resolution
  haveI : Mono iJ := by unfold iJ mapAugmentation; infer_instance
  haveI : Mono i := by dsimp only [i]; infer_instance
  haveI hq : QuasiIso i := by dsimp only [i]; infer_instance
  obtain ⟨φ, hφ⟩ := SheafCohomology.injectiveResolutionLift i l.resolution.i l.resolution.injective
  have hφ' : iJ ≫ φ = Γ.map k.hom ≫ l.resolution.i := by
    calc
      iJ ≫ φ = (Γ.map k.hom ≫ Γ.map k.inv) ≫ iJ ≫ φ := by
        rw [← Γ.map_comp, k.hom_inv_id, Γ.map_id]
        exact (Category.id_comp _).symm
      _ = Γ.map k.hom ≫ i ≫ φ := by simp only [i, Category.assoc]
      _ = _ := by rw [hφ]
  have hfl (q : ℤ) : IsFlasque R (I'.X q) :=
    (coefficient_lift_flasque.{a,u,r,max b u r} X R (I.X q)).2
      (original_injectives_flasque.{b,u,r} X R (I.X q) (m.resolution.injective q))
  let h : row₂.ShortExact := flasqueRow.{max a b,u,r} R V₂ W₂ I' hfl
  have hboundary (n : ℤ) :
      S.map (m.exactRow.δ n (n + 1) rfl) ≫
        (enlargeSectionHomologyIso.{a,u,r,b} R U U le_rfl I (n + 1)).hom =
      (enlargeSectionHomologyIso.{a,u,r,b} R U D hD I n).hom ≫ h.δ n (n + 1) rfl :=
    enlarge_boundary.{a,u,r,b} R V W I m.exactRow h n
  have hδ (n : ℤ) :=
    HomologySequence.δ_naturality (rowMap.{max a b,u,r} R V₂ W₂ φ) h l.exactRow n (n + 1) rfl
  let v (T : Opens X) (hT : T ≤ U) (n : ℕ) := enlargedValueIso.{a,u,r,b} R U T hT M (s T) n
  let p (T : Opens X) (hT : T ≤ U) (n : ℤ) :=
    enlargedModelArrow.{a,u,r,b} R U T hT φ n
  have hv (T : Opens X) (hT : T ≤ U) (n : ℕ) :
      S.map (m.comparison (liftedOpen.{b,u,r} T) (liftedLE.{b,u,r} hT) n).hom ≫ (v T hT n).hom =
        p T hT (n : ℤ) ≫
          (l.comparison (liftedOpen.{max a b,u,r} T) (liftedLE.{max a b,u,r} hT) n).hom :=
    enlarged_model_square.{a,u,r,b} R V W T hT M m l k (hkU M) φ hqJ hφ' (s T) (hs T) n
  refine ⟨k, e, φ, h, hkU M, ⟨hq, hφ⟩, hfl, rfl, rfl, ?_, ?_, hboundary, hδ, ?_, ?_⟩
  · change (L.mapBiprod _ _).hom ≫ biprod.fst = L.map biprod.fst ≫ 𝟙 _
    rw [Category.comp_id, Functor.mapBiprod_hom, biprod.lift_fst]
  · change (L.mapBiprod _ _).hom ≫ biprod.snd = L.map biprod.snd ≫ 𝟙 _
    rw [Category.comp_id, Functor.mapBiprod_hom, biprod.lift_snd]
  · intro T hT n x
    exact congrArg (fun f ↦ f (ULift.up x)) (hv T hT n)
  · intro n
    let vU (k : ℕ) := (s U k).app M
    have hvU (k : ℕ) :
        S.map (eA.{b,u,r} R V₁ W₁ m.resolution m.comparison k).hom ≫ (vU k).hom =
          p U le_rfl (k : ℤ) ≫ (eA.{max a b,u,r} R V₂ W₂ l.resolution l.comparison k).hom := by
      let e₁ := (unionIso.{b,u,r} R V₁ W₁ k).app M₁
      let e₂ := (unionIso.{max a b,u,r} R V₂ W₂ k).app N
      have hunit : S.map e₁.hom ≫ (vU k).hom = (v U le_rfl k).hom ≫ e₂.hom := by
        ext x
        rfl
      change S.map (_ ≫ e₁.hom) ≫ _ = _ ≫ (_ ≫ e₂.hom)
      rw [S.map_comp, Category.assoc, hunit]
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f ↦ f ≫ e₂.hom) (hv U le_rfl k)).trans (Category.assoc _ _ _))
    let e₁ (T : Opens X) (hT : T ≤ U) :=
      m.comparison (liftedOpen.{b,u,r} T) (liftedLE.{b,u,r} hT) n
    let e₂ (T : Opens X) (hT : T ≤ U) :=
      l.comparison (liftedOpen.{max a b,u,r} T) (liftedLE.{max a b,u,r} hT) n
    have hfrom (T : Opens X) (hT : T ≤ U) :=
      map_conjugate_square S
        (eA.{b,u,r} R V₁ W₁ m.resolution m.comparison n) (e₁ T hT)
        (eA.{max a b,u,r} R V₂ W₂ l.resolution l.comparison n) (e₂ T hT)
        _ _ (hvU n) (hv T hT n)
        (enlargedModelArrow_restriction.{a,u,r,b} R U U T le_rfl hT hT φ (n : ℤ))
    have hto (T : Opens X) (hT : T ≤ U) (hDT : D ≤ T) :=
      map_conjugate_square S (e₁ T hT) (e₁ D hD) (e₂ T hT) (e₂ D hD)
        _ _ (hv T hT n) (hv D hD n)
        (enlargedModelArrow_restriction.{a,u,r,b} R U T D hT hD hDT φ (n : ℤ))
    have hα := mapped_lift_square S (vU n) (v V le_sup_left n) (v W le_sup_right n)
      (hfrom V le_sup_left) (hfrom W le_sup_right)
    have hβ := mapped_difference_square S (v V le_sup_left n) (v W le_sup_right n) (v D hD n)
      (hto V le_sup_left inf_le_left) (hto W le_sup_right inf_le_right)
    have hb : S.map (m.exactRow.δ (n : ℤ) ((n : ℤ) + 1) rfl) ≫ p U le_rfl ((n : ℤ) + 1) =
        p D hD (n : ℤ) ≫ l.exactRow.δ (n : ℤ) ((n : ℤ) + 1) rfl := by
      dsimp only [p, enlargedModelArrow]
      rw [reassoc_of% (hboundary (n : ℤ)), Category.assoc]
      exact congrArg (fun f ↦ (enlargeSectionHomologyIso.{a,u,r,b} R U D hD I (n : ℤ)).hom ≫ f)
        (hδ (n : ℤ))
    have hγ := map_conjugate_square S (e₁ D hD) (eA.{b,u,r} R V₁ W₁ m.resolution m.comparison (n + 1))
      (e₂ D hD) (eA.{max a b,u,r} R V₂ W₂ l.resolution l.comparison (n + 1))
      _ _ (hv D hD n) (hvU (n + 1)) hb
    let vB := v V le_sup_left n
    let vC := v W le_sup_right n
    have hp (x) := pairMap_of_lift (S := R.obj.obj (op U)) vB vC x
    refine ⟨fun x ↦ ?_, fun x ↦ ?_, fun x ↦ ?_⟩
    · exact (hp (alpha.{b,u,r} R V₁ W₁ m.resolution m.comparison n x)).trans
        (congrArg (fun f ↦ f (ULift.up x)) hα)
    · exact (congrArg (fun f ↦ f (ULift.up x)) hβ).trans
        (congrArg (fun y ↦ beta.{max a b,u,r} R V₂ W₂ l.resolution l.comparison n y) (hp x).symm)
    · exact congrArg (fun f ↦ f (ULift.up x)) hγ

section ComparingSequences

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (V W : Opens X)

private abbrev cohomologyOverUnion [EnoughInjectives (AmbientSheaves.{b} R)]
    (T : Opens X) (h : T ≤ V ⊔ W) (M : AmbientSheaves.{b} R) (n : ℕ) :=
  (H.{b,u,r} R (liftedOpen.{b,u,r} V ⊔ liftedOpen.{b,u,r} W) (liftedOpen.{b,u,r} T)
    ((opensEquiv X).symm.monotone h) n).obj M

variable [EnoughInjectives (AmbientSheaves.{b} R)] [EnoughInjectives (AmbientSheaves.{c} R)]
  [EnoughInjectives (AmbientSheaves.{v} R)]

set_option maxHeartbeats 4000000 in
private lemma arrowsCommute_of_comparison
    {M : AmbientSheaves.{b} R} {N : AmbientSheaves.{c} R} {M' N' : AmbientSheaves.{v} R}
    (m : SequenceModel.{u,r,b} R V W M) (l : SequenceModel.{u,r,c} R V W N)
    (m' : SequenceModel.{u,r,v} R V W M') (l' : SequenceModel.{u,r,v} R V W N')
    (s : ∀ T n, (cohomologyValue.{b} R T n).obj M → (cohomologyValue.{v} R T n).obj M')
    (t : ∀ T n, (cohomologyValue.{c} R T n).obj N → (cohomologyValue.{v} R T n).obj N')
    (p : ∀ T n, (cohomologyValue.{b} R T n).obj M → (cohomologyValue.{c} R T n).obj N)
    (f : ∀ T n, (cohomologyValue.{v} R T n).obj M' → (cohomologyValue.{v} R T n).obj N')
    (hm : arrowsCommute R V W m.resolution m'.resolution m.exactRow m'.exactRow m.comparison m'.comparison s)
    (hl : arrowsCommute R V W l.resolution l'.resolution l.exactRow l'.exactRow l.comparison l'.comparison t)
    (hf : arrowsCommute R V W m'.resolution l'.resolution m'.exactRow l'.exactRow m'.comparison l'.comparison f)
    (h : ∀ T n x, f T n (s T n x) = t T n (p T n x))
    (ht : ∀ T n, Function.Injective (t T n)) :
    arrowsCommute R V W m.resolution l.resolution m.exactRow l.exactRow m.comparison l.comparison p := by
  intro n
  let B := cohomologyOverUnion.{u,r,b} R V W V le_sup_left M n
  let C := cohomologyOverUnion.{u,r,b} R V W W le_sup_right M n
  let B₁ := cohomologyOverUnion.{u,r,c} R V W V le_sup_left N n
  let C₁ := cohomologyOverUnion.{u,r,c} R V W W le_sup_right N n
  let B₂ := cohomologyOverUnion.{u,r,v} R V W V le_sup_left M' n
  let C₂ := cohomologyOverUnion.{u,r,v} R V W W le_sup_right M' n
  let B₃ := cohomologyOverUnion.{u,r,v} R V W V le_sup_left N' n
  let C₃ := cohomologyOverUnion.{u,r,v} R V W W le_sup_right N' n
  have hpair (x : ↥(B ⊞ C)) :=
    pairMap_naturality (B := B) (C := C) (B' := B₁) (C' := C₁)
      (B'' := B₃) (C'' := C₃) (B₀ := B₂) (C₀ := C₂)
      (p V n) (p W n) (t V n) (t W n) (s V n) (s W n) (f V n) (f W n)
      (fun x ↦ (h V n x).symm) (fun x ↦ (h W n x).symm) x
  have hpairInj := pairMap_injective (B := B₁) (C := C₁) (B' := B₃) (C' := C₃)
    (ht V n) (ht W n)
  obtain ⟨hmα, hmβ, hmδ⟩ := hm n
  obtain ⟨hlα, hlβ, hlδ⟩ := hl n
  obtain ⟨hfα, hfβ, hfδ⟩ := hf n
  refine ⟨fun x ↦ ?_, fun x ↦ ?_, fun x ↦ ?_⟩
  · apply hpairInj
    rw [hpair, hmα, hfα, h, ← hlα]
  · apply ht (V ⊓ W) n
    rw [← h, hmβ, hfβ, ← hpair, ← hlβ]
  · apply ht (V ⊔ W) (n + 1)
    rw [← h, hmδ, hfδ, h, ← hlδ]

end ComparingSequences

open private individualCohomologyEquiv conjugateLinearMap_apply
  from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients

set_option maxHeartbeats 6000000 in
/-- Naturality on the two original models follows from the three squares
in the common category and the normalized comparisons on the four opens. -/
theorem sectionwiseNaturality : sectionwiseNaturalityType.{a,u,r,b,c} := by
  intro X R V W _ _ _ M N f m l
  dsimp only
  let V' := liftedOpen.{max a b c,u,r} V
  let W' := liftedOpen.{max a b c,u,r} W
  let M' := (commonCoefficientLift.{max a c,u,r,b} R).obj M
  let N' := (commonCoefficientLift.{max a b,u,r,c} R).obj N
  let f' : M' ⟶ N' := f.lift.{max a u r}
  obtain ⟨models, hrow, comp, hcomp, _, _, hnat⟩ := naturalSequence.{max a b c,u,r} R V' W'
  let m' : SequenceModel.{u,r,max a b c} R V W M' :=
    ⟨models M', hrow M', comp M', hcomp M'⟩
  let l' : SequenceModel.{u,r,max a b c} R V W N' :=
    ⟨models N', hrow N', comp N', hcomp N'⟩
  let s (T : Opens X) := SheafCohomologyOriginalCoefficients.individualCohomologyIso.{max a c,u,r,b} X R T
  let t (T : Opens X) := SheafCohomologyOriginalCoefficients.individualCohomologyIso.{max a b,u,r,c} X R T
  have hs (T : Opens X) : IsIndividualCohomologyComparison X R T (s T) :=
    SheafCohomologyOriginalCoefficients.individualCohomologyIso_normalized.{max a c,u,r,b} X R T
  have ht (T : Opens X) : IsIndividualCohomologyComparison X R T (t T) :=
    SheafCohomologyOriginalCoefficients.individualCohomologyIso_normalized.{max a b,u,r,c} X R T
  let p (T : Opens X) (n : ℕ) :=
    SheafCohomologyOriginalCoefficients.sectionwiseCohomologyMap.{a,u,r,b,c} R T f n
  let s' (T : Opens X) (n : ℕ) (x : (coefficientCohomologyValue.{b} X R T n).obj M) :=
    (s T n).hom.app M (ULift.up x)
  let t' (T : Opens X) (n : ℕ) (x : (coefficientCohomologyValue.{c} X R T n).obj N) :=
    (t T n).hom.app N (ULift.up x)
  let F (T : Opens X) (n : ℕ) := (cohomologyValue.{max a b c} R T n).map f'
  have hp (T : Opens X) (n : ℕ) (x : (coefficientCohomologyValue.{b} X R T n).obj M) :
      F T n (s' T n x) = t' T n (p T n x) :=
    (conjugateLinearMap_apply
      (individualCohomologyEquiv.{max a c,u,r,b} R T M n)
      (individualCohomologyEquiv.{max a b,u,r,c} R T N n) (F T n) x).symm
  refine ⟨s, t, p, fun T ↦ ⟨hs T, ht T⟩, hp, ?_⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hM⟩ :=
    coefficientModelEnlargement.{max a c,u,r,b} R V W s hs M m m'
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hN⟩ :=
    coefficientModelEnlargement.{max a b,u,r,c} R V W t ht N l l'
  have hc : arrowsCommute R V W m'.resolution l'.resolution m'.exactRow l'.exactRow
      m'.comparison l'.comparison (fun T n x ↦ F T n x) := by
    intro n
    obtain ⟨hα, hβ, hδ⟩ := hnat M' N' f' n
    let fB := (H.{max a b c,u,r} R (V' ⊔ W') V' le_sup_left n).map f'
    let fC := (H.{max a b c,u,r} R (V' ⊔ W') W' le_sup_right n).map f'
    refine ⟨fun x ↦ ?_, fun x ↦ ?_, fun x ↦ ?_⟩
    · exact (pairMap_of_biprodMap fB fC (alpha.{max a b c,u,r} R V' W' m'.resolution m'.comparison n x)).trans
        (congrArg (fun g ↦ g x) hα).symm
    · exact (congrArg (fun g ↦ g x) hβ).symm.trans
        (congrArg (fun y ↦ beta.{max a b c,u,r} R V' W' l'.resolution l'.comparison n y)
          (pairMap_of_biprodMap fB fC x).symm)
    · exact (congrArg (fun g ↦ g x) hδ).symm
  apply arrowsCommute_of_comparison R V W m l m' l' s' t' (fun T n x ↦ p T n x)
    (fun T n x ↦ F T n x) hM hN hc hp
  intro T n x y h
  exact congrArg ULift.down (((t T n).app N).toLinearEquiv.injective h)

end AdvancedHomologicalAlgebra.MayerVietorisIndependentCoefficients
