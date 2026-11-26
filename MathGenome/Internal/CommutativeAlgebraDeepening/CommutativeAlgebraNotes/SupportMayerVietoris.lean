import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SupportMayerVietoris
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CechCohomologyOfOpenComplement
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.TorsionOfInjectives
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! Mayer–Vietoris via the short exact sequence of torsion on injective modules. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Specs.CommutativeAlgebraNotes.SupportMayerVietoris

namespace CommutativeAlgebraNotes

universe u v

variable {R : Type u} [CommRing R] (I J : Ideal R)

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem mem_torsion_sup {M : ModuleCat.{v} R} {x : M}
    (hI : x ∈ idealTorsion I M) (hJ : x ∈ idealTorsion J M) :
    x ∈ idealTorsion (I ⊔ J) M := by
  obtain ⟨m, hm, ha⟩ := (mem_idealTorsion I x).mp hI
  obtain ⟨n, _, hb⟩ := (mem_idealTorsion J x).mp hJ
  refine (mem_idealTorsion (I ⊔ J) x).mpr ⟨m + n, by omega, fun a h => ?_⟩
  obtain ⟨b, hb', c, hc', rfl⟩ := Submodule.mem_sup.mp
    (Ideal.sup_pow_add_le_pow_sup_pow (I := I) (J := J) h)
  rw [add_smul, ha b hb', hb c hc', add_zero]

private theorem torsion_inf_decompose [IsNoetherianRing R] (Q : ModuleCat.{v} R) [Injective Q]
    (x : idealTorsion (I ⊓ J) Q) :
    ∃ (a : idealTorsion I Q) (b : idealTorsion J Q), (a : Q) - b = x := by
  have hQ : Module.Injective R Q :=
    (Module.injective_iff_injective_object R Q).mpr inferInstance
  obtain ⟨p, hp⟩ := (idealTorsion_injective I hQ).out
    (idealTorsion I Q).subtype (Submodule.subtype_injective _) LinearMap.id
  obtain ⟨n, hn, hx⟩ := (mem_idealTorsion (I ⊓ J) (x : Q)).mp x.property
  let a := p x
  have hres : (x : Q) - (a : Q) ∈ idealTorsion J Q := by
    refine (mem_idealTorsion J _).mpr ⟨n, hn, fun b hb => ?_⟩
    have ht : b • (x : Q) ∈ idealTorsion I Q := by
      refine (mem_idealTorsion I _).mpr ⟨n, hn, fun c hc => ?_⟩
      rw [smul_smul]
      apply hx
      have hmul : c * b ∈ I ^ n * J ^ n := Ideal.mul_mem_mul hc hb
      rw [← mul_pow] at hmul
      exact pow_le_pow_left' Ideal.mul_le_inf n hmul
    have hp' := congrArg Subtype.val (hp (⟨b • (x : Q), ht⟩ : idealTorsion I Q))
    change (p (b • (x : Q)) : Q) = b • (x : Q) at hp'
    rw [map_smul] at hp'
    change b • (a : Q) = b • (x : Q) at hp'
    rw [smul_sub, hp', sub_self]
  exact ⟨a, ⟨-((x : Q) - a), Submodule.neg_mem _ hres⟩, by
    change (a : Q) - -((x : Q) - a) = x
    abel⟩

private abbrev T (I : Ideal R) (Q : ModuleCat.{v} R) := (idealTorsionFunctor I).obj Q

private def moduleRow (Q : ModuleCat.{v} R) : ShortComplex (ModuleCat.{v} R) :=
  let f := (inclusion (le_sup_left : I ≤ I ⊔ J)).app Q
  let g := (inclusion (le_sup_right : J ≤ I ⊔ J)).app Q
  let h := (inclusion (inf_le_left : I ⊓ J ≤ I)).app Q
  let k := (inclusion (inf_le_right : I ⊓ J ≤ J)).app Q
  ShortComplex.mk
    (ModuleCat.ofHom (Y := ModuleCat.of R (T I Q × T J Q)) (f.hom.prod g.hom))
    (ModuleCat.ofHom (X := ModuleCat.of R (T I Q × T J Q))
      (h.hom.comp (LinearMap.fst R _ _) - k.hom.comp (LinearMap.snd R _ _))) (by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (h.hom (f.hom x) - k.hom (g.hom x) : idealTorsion (I ⊓ J) Q).val = 0
    calc
      _ = Subtype.val (h.hom (f.hom x)) - Subtype.val (k.hom (g.hom x)) :=
        Submodule.coe_sub (idealTorsion (I ⊓ J) Q) _ _
      _ = Subtype.val (f.hom x) - Subtype.val (g.hom x) :=
        congrArg₂ Sub.sub (inclusion_app_val _ Q _) (inclusion_app_val _ Q _)
      _ = Subtype.val x - Subtype.val x :=
        congrArg₂ Sub.sub (inclusion_app_val _ Q x) (inclusion_app_val _ Q x)
      _ = 0 := sub_self _)

/-- The last map of the module row is the difference in the ambient module. -/
private lemma moduleRow_g_val (Q : ModuleCat.{v} R) (a : idealTorsion I Q)
    (b : idealTorsion J Q) :
    Subtype.val ((moduleRow I J Q).g.hom (a, b)) = a.val - b.val := by
  let h := (inclusion (inf_le_left : I ⊓ J ≤ I)).app Q
  let k := (inclusion (inf_le_right : I ⊓ J ≤ J)).app Q
  change (h.hom a - k.hom b : idealTorsion (I ⊓ J) Q).val = a.val - b.val
  exact (Submodule.coe_sub (idealTorsion (I ⊓ J) Q) _ _).trans
    (congrArg₂ Sub.sub (inclusion_app_val _ Q a) (inclusion_app_val _ Q b))

private theorem moduleRow_shortExact [IsNoetherianRing R] (Q : ModuleCat.{v} R) [Injective Q] :
    (moduleRow I J Q).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro y hy
    let a : idealTorsion I Q := y.1
    let b : idealTorsion J Q := y.2
    have hzero := congrArg (Subtype.val : idealTorsion (I ⊓ J) Q → Q) hy
    have he : a.val = b.val := sub_eq_zero.mp ((moduleRow_g_val I J Q a b).symm.trans hzero)
    have haJ : a.val ∈ idealTorsion J Q := he.symm ▸ b.property
    let x : idealTorsion (I ⊔ J) Q := ⟨a, mem_torsion_sup I J a.property haJ⟩
    refine ⟨x, Prod.ext ?_ ?_⟩
    · apply Subtype.ext
      exact inclusion_app_val _ Q x
    · apply Subtype.ext
      exact (inclusion_app_val _ Q x).trans he
  · apply (ModuleCat.mono_iff_injective _).mpr
    intro x y h
    have hw := congrArg (fun z : T I Q × T J Q => Subtype.val z.1) h
    apply Subtype.ext
    change Subtype.val (((inclusion (le_sup_left : I ≤ I ⊔ J)).app Q).hom x) =
      Subtype.val (((inclusion (le_sup_left : I ≤ I ⊔ J)).app Q).hom y) at hw
    simpa only [inclusion_app_val] using hw
  · apply (ModuleCat.epi_iff_surjective _).mpr
    intro x
    obtain ⟨a, b, hab⟩ := torsion_inf_decompose I J Q x
    exact ⟨(a, b), Subtype.ext ((moduleRow_g_val I J Q a b).trans hab)⟩

private def degreeRowIso (K : Cochains.{u,v} R) (n : ℕ) :
    (cochainRow I J K).map (eval (ModuleCat.{v} R) (.up ℕ) n) ≅ moduleRow I J (K.X n) := by
  let E := eval (ModuleCat.{v} R) (.up ℕ) n
  let A := (torsionCochains I).obj K
  let B := (torsionCochains J).obj K
  refine ShortComplex.isoMk (Iso.refl _) (E.mapBiprod A B ≪≫ ModuleCat.biprodIsoProd _ _)
    (Iso.refl _) ?_ ?_
  · change 𝟙 _ ≫ (moduleRow I J (K.X n)).f =
      E.map (cochainRow I J K).f ≫
        ((E.mapBiprod A B).hom ≫ (ModuleCat.biprodIsoProd (E.obj A) (E.obj B)).hom)
    rw [Category.id_comp, ← Category.assoc]
    unfold cochainRow
    rw [biprod.map_lift_mapBiprod]
    apply (cancel_mono (ModuleCat.biprodIsoProd (E.obj A) (E.obj B)).inv).mp
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    apply biprod.hom_ext
    · rw [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_fst, biprod.lift_fst]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl
    · rw [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_snd, biprod.lift_snd]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl
  · change ((E.mapBiprod A B).hom ≫ (ModuleCat.biprodIsoProd (E.obj A) (E.obj B)).hom) ≫
      (moduleRow I J (K.X n)).g = E.map (cochainRow I J K).g ≫ 𝟙 _
    rw [Category.comp_id, Category.assoc]
    unfold cochainRow
    rw [← biprod.mapBiprod_hom_desc, Functor.map_neg]
    congr 1
    apply (cancel_epi (ModuleCat.biprodIsoProd (E.obj A) (E.obj B)).inv).mp
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    simp only [biprod.desc_eq, Preadditive.comp_add]
    rw [← Category.assoc (ModuleCat.biprodIsoProd (E.obj A) (E.obj B)).inv biprod.fst,
      ModuleCat.biprodIsoProd_inv_comp_fst]
    rw [← Category.assoc (ModuleCat.biprodIsoProd (E.obj A) (E.obj B)).inv biprod.snd,
      ModuleCat.biprodIsoProd_inv_comp_snd]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact sub_eq_add_neg _ _

private theorem cochainRow_shortExact [IsNoetherianRing R] (K : Cochains.{u,v} R)
    (hK : ∀ n, Injective (K.X n)) : (cochainRow I J K).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have := hK n
  exact ShortComplex.shortExact_of_iso (degreeRowIso I J K n).symm
    (moduleRow_shortExact I J (K.X n))

private def cochainRowMap {K L : Cochains.{u,v} R} (f : K ⟶ L) :
    cochainRow I J K ⟶ cochainRow I J L := by
  refine ShortComplex.homMk ((torsionCochains (I ⊔ J)).map f)
    (biprod.map ((torsionCochains I).map f) ((torsionCochains J).map f))
    ((torsionCochains (I ⊓ J)).map f) ?_ ?_
  · apply biprod.hom_ext
    · simpa only [cochainRow, Category.assoc, biprod.lift_fst, biprod.map_fst,
        biprod.lift_fst_assoc] using (cochainInclusion (le_sup_left : I ≤ I ⊔ J)).naturality f
    · simpa only [cochainRow, Category.assoc, biprod.lift_snd, biprod.map_snd,
        biprod.lift_snd_assoc] using (cochainInclusion (le_sup_right : J ≤ I ⊔ J)).naturality f
  · apply biprod.hom_ext'
    · simpa only [cochainRow, Category.assoc, biprod.inl_map_assoc, biprod.inl_desc,
        biprod.inl_desc_assoc] using (cochainInclusion (inf_le_left : I ⊓ J ≤ I)).naturality f
    · simpa only [cochainRow, Category.assoc, biprod.inr_map_assoc, biprod.inr_desc,
        biprod.inr_desc_assoc, Preadditive.comp_neg, Preadditive.neg_comp] using
        congrArg Neg.neg ((cochainInclusion (inf_le_right : I ⊓ J ≤ J)).naturality f)

private abbrev cohomology (n : ℕ) :=
  homologyFunctor (ModuleCat.{v} R) (.up ℕ) n

private theorem mapBiprod_inv_naturality (n : ℕ) {A B A' B' : Cochains.{u,v} R}
    (f : A ⟶ A') (g : B ⟶ B') :
    biprod.map ((cohomology n).map f) ((cohomology n).map g) ≫
        ((cohomology n).mapBiprod A' B').inv =
      ((cohomology n).mapBiprod A B).inv ≫ (cohomology n).map (biprod.map f g) := by
  let F := cohomology (R := R) n
  have h : F.map (biprod.map f g) ≫ (F.mapBiprod A' B').hom =
      (F.mapBiprod A B).hom ≫ biprod.map (F.map f) (F.map g) := by
    apply biprod.hom_ext
    · simp only [Functor.mapBiprod_hom, Category.assoc, biprod.lift_fst,
        biprod.lift_fst_assoc, biprod.map_fst, ← Functor.map_comp]
    · simp only [Functor.mapBiprod_hom, Category.assoc, biprod.lift_snd,
        biprod.lift_snd_assoc, biprod.map_snd, ← Functor.map_comp]
  change biprod.map (F.map f) (F.map g) ≫ (F.mapBiprod A' B').inv =
    (F.mapBiprod A B).inv ≫ F.map (biprod.map f g)
  apply (cancel_mono (F.mapBiprod A' B').hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, h, Iso.inv_hom_id_assoc]

variable [Small.{v} R]

private abbrev liftResolution {M N : ModuleCat.{v} R} (f : M ⟶ N) :=
  InjectiveResolution.desc f (injectiveResolution N) (injectiveResolution M)

private theorem compare_naturality (A : Ideal R) (n : ℕ) {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    (H A n).map f ≫ (compare A N n).hom =
      (compare A M n).hom ≫ (cohomology n).map ((torsionCochains A).map (liftResolution f)) :=
  InjectiveResolution.isoRightDerivedObj_hom_naturality f (injectiveResolution M)
    (injectiveResolution N) _ (InjectiveResolution.desc_commutes_zero f _ _) _ n

private theorem compareSum_naturality (n : ℕ) {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    (sumFunctor (H I n) (H J n)).map f ≫ (compareSum I J N n).hom =
      (compareSum I J M n).hom ≫ (cohomology n).map (cochainRowMap I J (liftResolution f)).τ₂ := by
  let F := cohomology (R := R) n
  let a := (torsionCochains I).map (liftResolution f)
  let b := (torsionCochains J).map (liftResolution f)
  have w := mapBiprod_inv_naturality n a b
  dsimp only [sumFunctor, compareSum, Iso.trans_hom, Iso.symm_hom, biprod.mapIso_hom]
  change biprod.map ((H I n).map f) ((H J n).map f) ≫
      biprod.map (compare I N n).hom (compare J N n).hom ≫ _ =
    (biprod.map (compare I M n).hom (compare J M n).hom ≫ _) ≫ F.map (biprod.map a b)
  simp only [Category.assoc]
  rw [← w, ← Category.assoc, ← Category.assoc]
  congr 1
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, biprod.map_fst_assoc, a,
      compare_naturality I n f]
  · simp only [Category.assoc, biprod.map_snd, biprod.map_snd_assoc, b,
      compare_naturality J n f]

private def transportMap {F G : ModuleCat.{v} R ⥤ ModuleCat.{v} R}
    {A B : ModuleCat.{v} R → ModuleCat.{v} R}
    (s : ∀ M, F.obj M ≅ A M) (t : ∀ M, G.obj M ≅ B M)
    (g : ∀ M, A M ⟶ B M)
    (a : ∀ {M N}, (M ⟶ N) → (A M ⟶ A N))
    (b : ∀ {M N}, (M ⟶ N) → (B M ⟶ B N))
    (hs : ∀ {M N} (f : M ⟶ N), F.map f ≫ (s N).hom = (s M).hom ≫ a f)
    (ht : ∀ {M N} (f : M ⟶ N), G.map f ≫ (t N).hom = (t M).hom ≫ b f)
    (hg : ∀ {M N} (f : M ⟶ N), a f ≫ g N = g M ≫ b f) : F ⟶ G where
  app M := (s M).hom ≫ g M ≫ (t M).inv
  naturality M N f := by
    apply (cancel_mono (t N).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [reassoc_of% hs, hg f, ht f, Iso.inv_hom_id_assoc]

private def alpha (n : ℕ) : H (I ⊔ J) n ⟶ sumFunctor (H I n) (H J n) :=
  transportMap (fun M => compare (I ⊔ J) M n) (fun M => compareSum I J M n)
    (fun M => homologyMap (resolutionRow I J M).f n)
    (fun f => (cohomology n).map (cochainRowMap I J (liftResolution f)).τ₁)
    (fun f => (cohomology n).map (cochainRowMap I J (liftResolution f)).τ₂)
    (compare_naturality (I ⊔ J) n) (compareSum_naturality I J n)
    (fun f => by
      let m := cochainRowMap I J (liftResolution f)
      simpa only [homologyFunctor_map, homologyMap_comp] using congrArg (fun k => homologyMap k n) m.comm₁₂)

private def beta (n : ℕ) : sumFunctor (H I n) (H J n) ⟶ H (I ⊓ J) n :=
  transportMap (fun M => compareSum I J M n) (fun M => compare (I ⊓ J) M n)
    (fun M => homologyMap (resolutionRow I J M).g n)
    (fun f => (cohomology n).map (cochainRowMap I J (liftResolution f)).τ₂)
    (fun f => (cohomology n).map (cochainRowMap I J (liftResolution f)).τ₃)
    (compareSum_naturality I J n) (compare_naturality (I ⊓ J) n)
    (fun f => by
      let m := cochainRowMap I J (liftResolution f)
      simpa only [homologyFunctor_map, homologyMap_comp] using congrArg (fun k => homologyMap k n) m.comm₂₃)

variable [IsNoetherianRing R]

private theorem resolutionRow_shortExact (M : ModuleCat.{v} R) :
    (resolutionRow I J M).ShortExact :=
  cochainRow_shortExact I J _ (injectiveResolution M).injective

private def boundary (n : ℕ) : H (I ⊓ J) n ⟶ H (I ⊔ J) (n + 1) :=
  transportMap (fun M => compare (I ⊓ J) M n) (fun M => compare (I ⊔ J) M (n + 1))
    (fun M => (resolutionRow_shortExact I J M).δ n (n + 1) rfl)
    (fun f => (cohomology n).map (cochainRowMap I J (liftResolution f)).τ₃)
    (fun f => (cohomology (n + 1)).map (cochainRowMap I J (liftResolution f)).τ₁)
    (compare_naturality (I ⊓ J) n) (compare_naturality (I ⊔ J) (n + 1))
    (fun {M N} f => (HomologySequence.δ_naturality (cochainRowMap I J (liftResolution f))
      (resolutionRow_shortExact I J M) (resolutionRow_shortExact I J N) n (n + 1) rfl).symm)

/-- Mayer–Vietoris for local cohomology with two ideal supports. -/
theorem support_mayerVietoris : MayerVietoris.{u,v} := by
  intro R _ _ _ I J
  refine ⟨alpha I J, beta I J, boundary I J, fun M => ⟨?_, resolutionRow_shortExact I J M, ?_⟩⟩
  · let S := resolutionRow I J M
    have h := resolutionRow_shortExact I J M
    have := h.mono_f
    have : Mono (S.f.f 0) := by infer_instance
    have : Mono (homologyMap S.f 0) :=
      mono_homologyMap_of_mono_of_not_rel S.f 0 (fun i hi => by
        change i + 1 = 0 at hi
        omega)
    change Mono ((compare (I ⊔ J) M 0).hom ≫ homologyMap S.f 0 ≫ (compareSum I J M 0).inv)
    infer_instance
  · intro n
    have hα (m : ℕ) : (alpha I J m).app M ≫ (compareSum I J M m).hom =
        (compare (I ⊔ J) M m).hom ≫ homologyMap (resolutionRow I J M).f m := by
      simp [alpha, transportMap, Category.assoc]
    have hβ (m : ℕ) : (beta I J m).app M ≫ (compare (I ⊓ J) M m).hom =
        (compareSum I J M m).hom ≫ homologyMap (resolutionRow I J M).g m := by
      simp [beta, transportMap, Category.assoc]
    have hδ : (boundary I J n).app M ≫ (compare (I ⊔ J) M (n + 1)).hom =
        (compare (I ⊓ J) M n).hom ≫ (resolutionRow_shortExact I J M).δ n (n + 1) rfl := by
      simp [boundary, transportMap, Category.assoc]
    refine ⟨hα n, hβ n, hδ, ?_⟩
    refine ComposableArrows.exact_of_iso ?_ (HomologySequence.composableArrows₅_exact
      (resolutionRow_shortExact I J M) n (n + 1) rfl)
    exact (ComposableArrows.isoMk₅
      (compare (I ⊔ J) M n) (compareSum I J M n) (compare (I ⊓ J) M n)
      (compare (I ⊔ J) M (n + 1)) (compareSum I J M (n + 1)) (compare (I ⊓ J) M (n + 1))
      (hα n) (hβ n) hδ (hα (n + 1)) (hβ (n + 1))).symm

section OpenComplements

open AlgebraicGeometry TopologicalSpace
open Specs.CommutativeAlgebraNotes.CechCohomologyOfOpenComplement (complement restrict)

private lemma complement_lattice (S : CommRingCat.{u}) (A B : Ideal S) :
    complement S (A ⊔ B) = complement S A ⊔ complement S B ∧
      complement S (A ⊓ B) = complement S A ⊓ complement S B := by
  constructor
  · apply SetLike.coe_injective
    change (PrimeSpectrum.zeroLocus ((A ⊔ B : Ideal S) : Set S))ᶜ =
      (PrimeSpectrum.zeroLocus (A : Set S))ᶜ ∪ (PrimeSpectrum.zeroLocus (B : Set S))ᶜ
    rw [PrimeSpectrum.zeroLocus_sup, Set.compl_inter]
  · apply SetLike.coe_injective
    change (PrimeSpectrum.zeroLocus ((A ⊓ B : Ideal S) : Set S))ᶜ =
      (PrimeSpectrum.zeroLocus (A : Set S))ᶜ ∩ (PrimeSpectrum.zeroLocus (B : Set S))ᶜ
    rw [PrimeSpectrum.zeroLocus_inf, Set.compl_union]

private lemma support_toOpen_zero (S : CommRingCat.{u}) [IsNoetherianRing S]
    (K : Cochains.{u,u} S) (hK : ∀ n, Injective (K.X n)) (A : Ideal S) :
    (ambientInclusion S A).app K ≫ (toOpenCochains S (complement S A)).app K = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  have := hK n
  obtain ⟨w, _⟩ := tildeComplement_injectiveSectionsExact S A (K.X n)
  exact w

private lemma support_toOpen_shortExact (S : CommRingCat.{u}) [IsNoetherianRing S]
    (K : Cochains.{u,u} S) (hK : ∀ n, Injective (K.X n)) (A : Ideal S) :
    (ShortComplex.mk _ _ (support_toOpen_zero S K hK A)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have := hK n
  obtain ⟨_, h⟩ := tildeComplement_injectiveSectionsExact S A (K.X n)
  exact h

private lemma comp_toAmbient (S : CommRingCat.{u}) (K : Cochains.{u,u} S)
    {A B : Ideal S} (h : A ≤ B) :
    (cochainInclusion h).app K ≫ (ambientInclusion S A).app K = (ambientInclusion S B).app K := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [comp_f, ambientInclusion, NatTrans.comp_app, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplexIdIso_hom_app_f]
  exact inclusion_comp_ambient h (K.X n)

private abbrev openRestriction (S : CommRingCat.{u}) {A B : Ideal S} (h : A ≤ B) :=
  NatTrans.mapHomologicalComplex
    (Functor.whiskerLeft (tilde.functor S) (restrict S (complement_mono h))) (.up ℕ)

private lemma toOpen_comp_restrict (S : CommRingCat.{u}) (K : Cochains.{u,u} S)
    {A B : Ideal S} (h : A ≤ B) :
    (toOpenCochains S (complement S B)).app K ≫ (openRestriction S h).app K =
      (toOpenCochains S (complement S A)).app K := by
  apply HomologicalComplex.hom_ext
  intro n
  exact tilde.toOpen_res (K.X n) (complement S B) (complement S A)
    (homOfLE (complement_mono h))

/-- On the associated sheaves of an injective resolution, supported cochains are
the strict kernels of restriction, compatibly with the inclusions of supports. -/
theorem support_mayerVietoris_openComplement : OpenComplementKernels.{u} := by
  intro S _inst
  refine ⟨complement_lattice S, fun K hK => ⟨support_toOpen_zero S K hK,
    support_toOpen_shortExact S K hK, ?_⟩⟩
  intro A B h
  refine ⟨ShortComplex.homMk ((cochainInclusion h).app K) (𝟙 K)
    ((openRestriction S h).app K) ?_ ?_, rfl, rfl, rfl⟩
  · exact (comp_toAmbient S K h).trans (Category.comp_id ((ambientInclusion S B).app K)).symm
  · exact (Category.id_comp ((toOpenCochains S (complement S A)).app K)).trans
      (toOpen_comp_restrict S K h).symm

end OpenComplements

end CommutativeAlgebraNotes
