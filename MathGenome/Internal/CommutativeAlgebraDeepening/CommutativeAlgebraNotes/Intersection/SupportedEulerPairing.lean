import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.SupportedEulerPairing
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.TensorComplexIsolatedHomology
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler
import MathGenome.Internal.AlgebraCore.P103.Ch11.FreeComplexReplacement
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.BifunctorHomotopy

open CategoryTheory CategoryTheory.Limits Category HomologicalComplex MonoidalCategory
open scoped BigOperators TensorProduct

noncomputable section

namespace CommutativeAlgebraNotes.Intersection.SupportedEulerPairing

open CommutativeAlgebraNotes.Intersection.SupportedEulerPairing.Specs

universe u

variable {R : Type u} [CommRing R]

private abbrev down := ComplexShape.down ℤ
private abbrev tensor (R : Type u) [CommRing R] := curriedTensor (ModuleCat.{u} R)

abbrev pairing : Specs.pairingType.{u} := @Specs.pairing

private theorem homology_isZero_of_X (K : Complex R) (i : ℤ) (h : IsZero (K.X i)) :
    IsZero (K.homology i) := by
  rw [← exactAt_iff_isZero_homology, exactAt_iff]
  exact ShortComplex.exact_of_isZero_X₂ _ h

private theorem tensorBounded (F G : Complex R) (hF : Bounded F) (hG : Bounded G) :
    Bounded (tensorTotal F G) := by
  obtain ⟨a, b, hf⟩ := hF
  obtain ⟨c, d, hg⟩ := hG
  refine ⟨a + c, b + d, fun n hn => ?_⟩
  rw [IsZero.iff_id_eq_zero]
  apply mapBifunctor.hom_ext
  intro i j hij
  change i + j = n at hij
  by_cases hi : i < a ∨ b < i
  · exact ((tensorRight (G.X j)).map_isZero (hf i hi)).eq_of_src _ _
  · exact ((tensorLeft (F.X i)).map_isZero (hg j (by omega))).eq_of_src _ _

private theorem homologyLengthFiniteSupport {K : Complex R} (h : Bounded K) :
    (Function.support (fun i => Module.length R (K.homology i))).Finite := by
  obtain ⟨a, b, h⟩ := h
  apply (Finset.finite_toSet (Finset.Icc a b)).subset
  intro i hi
  by_contra hout
  simp only [Finset.mem_coe, Finset.mem_Icc] at hout
  have hz := homology_isZero_of_X K i (h i (by omega))
  have : Subsingleton ↑(K.homology i) := ModuleCat.isZero_iff_subsingleton.mp hz
  exact hi Module.length_eq_zero

private theorem tensorFiniteLength [IsNoetherianRing R] [IsLocalRing R]
    (F G : Complex R) (hf : BoundedFiniteFree F) (hg : BoundedFiniteFree G)
    (h : Isolated F G) : ∀ i, IsFiniteLength R ((tensorTotal F G).homology i) :=
  tensorTotalFiniteLength F G hf.1 hg.1 hf.2.1 hf.2.2 hg.2.1 hg.2.2 h

theorem finite : Specs.finiteType.{u} := by
  intro R _ _ _ F G hf hg h
  exact ⟨tensorFiniteLength F G hf hg h, homologyLengthFiniteSupport (tensorBounded F G hf.1 hg.1)⟩


private abbrev Bicomplex (R : Type u) [CommRing R] :=
  HomologicalComplex₂ (ModuleCat.{u} R) down down

private abbrev tensorBicomplex (F G : Complex R) : Bicomplex R :=
  (((tensor R).mapBifunctorHomologicalComplex down down).obj F).obj G

private def shortComplexOfExactComponents {A B C : Complex R} (f : A ⟶ B) (g : B ⟶ C)
    (h : P103.Specs.Ch10.HomologySequence.DegreewiseExact f g) :
    ShortComplex (Complex R) :=
  ShortComplex.mk f g (by
    ext n : 1
    apply ModuleCat.hom_ext
    exact (h n).2.1.linearMap_comp_eq_zero)

private theorem shortExactOfExactComponents {A B C : Complex R} (f : A ⟶ B) (g : B ⟶ C)
    (h : P103.Specs.Ch10.HomologySequence.DegreewiseExact f g) :
    (shortComplexOfExactComponents f g h).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro n
  let T := (shortComplexOfExactComponents f g h).map (eval (ModuleCat.{u} R) down n)
  exact
    { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).2 (h n).2.1
      mono_f := (ModuleCat.mono_iff_injective T.f).2 (h n).1
      epi_g := (ModuleCat.epi_iff_surjective T.g).2 (h n).2.2 }

private theorem tensorLeftComponents (S : ShortComplex (Complex R)) (G : Complex R)
    (hs : S.ShortExact) (hf : ∀ i, Module.Flat R (G.X i)) :
    P103.Specs.Ch10.HomologySequence.DegreewiseExact
      (HomologicalComplex.tensorHom S.f (𝟙 G)) (HomologicalComplex.tensorHom S.g (𝟙 G)) := by
  let T := (tensor R).mapBifunctorHomologicalComplex down down
  let f : tensorBicomplex S.X₁ G ⟶ tensorBicomplex S.X₂ G := (T.map S.f).app G
  let g : tensorBicomplex S.X₂ G ⟶ tensorBicomplex S.X₃ G := (T.map S.g).app G
  have h := P103.Ch11.FreeComplexReplacement.total_degreewiseExact f g (by
    intro i j
    let : Module.Flat R (G.X j) := hf j
    have h'S := (shortExact_iff_degreewise_shortExact S).1 hs i
    change Function.Injective ((S.f.f i).hom.rTensor (G.X j)) ∧
      Function.Exact ((S.f.f i).hom.rTensor (G.X j)) ((S.g.f i).hom.rTensor (G.X j)) ∧
      Function.Surjective ((S.g.f i).hom.rTensor (G.X j))
    exact ⟨Module.Flat.rTensor_preserves_injective_linearMap _
      ((ModuleCat.mono_iff_injective _).1 h'S.mono_f),
      Module.Flat.rTensor_exact _ ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        h'S.exact),
      LinearMap.rTensor_surjective _ ((ModuleCat.epi_iff_surjective _).1 h'S.epi_g)⟩)
  change P103.Specs.Ch10.HomologySequence.DegreewiseExact
    (HomologicalComplex₂.total.map (f ≫ (T.obj S.X₂).map (𝟙 G)) down)
    (HomologicalComplex₂.total.map (g ≫ (T.obj S.X₃).map (𝟙 G)) down)
  erw [(T.obj S.X₂).map_id, (T.obj S.X₃).map_id, Category.comp_id, Category.comp_id]
  exact h

private theorem tensorRightComponents (F : Complex R) (S : ShortComplex (Complex R))
    (hs : S.ShortExact) (hf : ∀ i, Module.Flat R (F.X i)) :
    P103.Specs.Ch10.HomologySequence.DegreewiseExact
      (HomologicalComplex.tensorHom (𝟙 F) S.f) (HomologicalComplex.tensorHom (𝟙 F) S.g) := by
  let B := (tensor R).mapBifunctorHomologicalComplex down down
  let T := B.obj F
  have h := P103.Ch11.FreeComplexReplacement.total_degreewiseExact (T.map S.f) (T.map S.g) (by
    intro i j
    let : Module.Flat R (F.X i) := hf i
    have h'S := (shortExact_iff_degreewise_shortExact S).1 hs j
    change Function.Injective ((S.f.f j).hom.lTensor (F.X i)) ∧
      Function.Exact ((S.f.f j).hom.lTensor (F.X i)) ((S.g.f j).hom.lTensor (F.X i)) ∧
      Function.Surjective ((S.g.f j).hom.lTensor (F.X i))
    exact ⟨Module.Flat.lTensor_preserves_injective_linearMap _
      ((ModuleCat.mono_iff_injective _).1 h'S.mono_f),
      Module.Flat.lTensor_exact _ ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        h'S.exact),
      LinearMap.lTensor_surjective _ ((ModuleCat.epi_iff_surjective _).1 h'S.epi_g)⟩)
  change P103.Specs.Ch10.HomologySequence.DegreewiseExact
    (HomologicalComplex₂.total.map ((B.map (𝟙 F)).app S.X₁ ≫ T.map S.f) down)
    (HomologicalComplex₂.total.map ((B.map (𝟙 F)).app S.X₂ ≫ T.map S.g) down)
  erw [B.map_id, NatTrans.id_app, NatTrans.id_app, Category.id_comp, Category.id_comp]
  exact h

private def intLength (M : ModuleCat.{u} R) : ℤ := (Module.length R M).toNat

private def imageLength {M N : ModuleCat.{u} R} (f : M ⟶ N) : ℤ :=
  (Module.length R (LinearMap.range f.hom)).toNat

private theorem length_eq_image_add_image {A B C : ModuleCat.{u} R}
    {f : A ⟶ B} {g : B ⟶ C} {w : f ≫ g = 0}
    (h : (ShortComplex.mk f g w).Exact)
    (hB : IsFiniteLength R B) (hC : IsFiniteLength R C) :
    intLength B = imageLength f + imageLength g := by
  have he := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 h
  change LinearMap.range f.hom = LinearMap.ker g.hom at he
  have hr₁ : IsFiniteLength R (LinearMap.range f.hom) :=
    hB.of_injective (f := (LinearMap.range f.hom).subtype) Subtype.val_injective
  have hr₂ : IsFiniteLength R (LinearMap.range g.hom) :=
    hC.of_injective (f := (LinearMap.range g.hom).subtype) Subtype.val_injective
  have hlen := Module.length_eq_add_of_exact (LinearMap.ker g.hom).subtype
    (LinearMap.ker g.hom).mkQ Subtype.val_injective (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _)
  rw [g.hom.quotKerEquivRange.length_eq, ← he] at hlen
  simp only [intLength, imageLength, hlen,
    ENat.toNat_add (Module.length_ne_top_iff.mpr hr₁) (Module.length_ne_top_iff.mpr hr₂),
    Nat.cast_add]

private theorem signedFiniteSupport {a : ℤ → ℤ} (h : a.HasFiniteSupport) :
    (fun i : ℤ => (i.negOnePow : ℤ) * a i).HasFiniteSupport :=
  h.subset (fun i hi hai => hi (by simp [hai]))

private theorem signedHomologyFiniteSupport {K : Complex R} (hK : Bounded K) :
    (fun i => (i.negOnePow : ℤ) * intLength (K.homology i)).HasFiniteSupport :=
  signedFiniteSupport ((homologyLengthFiniteSupport hK).subset (fun i hi hz => hi (by
    simp [intLength, show Module.length R (K.homology i) = 0 from hz])))

private theorem homologyLengthEuler_additive (S : ShortComplex (Complex R)) (h : S.ShortExact)
    (h₁ : Bounded S.X₁) (h₂ : Bounded S.X₂) (h₃ : Bounded S.X₃)
    (l₁ : ∀ i, IsFiniteLength R (S.X₁.homology i))
    (l₂ : ∀ i, IsFiniteLength R (S.X₂.homology i))
    (l₃ : ∀ i, IsFiniteLength R (S.X₃.homology i)) :
    homologyLengthEuler S.X₂ = homologyLengthEuler S.X₁ + homologyLengthEuler S.X₃ := by
  let δ (i : ℤ) := imageLength (h.δ i (i - 1) (by change i - 1 + 1 = i; omega))
  let a (i : ℤ) := (i.negOnePow : ℤ) * intLength (S.X₁.homology i)
  let b (i : ℤ) := (i.negOnePow : ℤ) * intLength (S.X₂.homology i)
  let c (i : ℤ) := (i.negOnePow : ℤ) * intLength (S.X₃.homology i)
  let t (i : ℤ) := (i.negOnePow : ℤ) * δ i
  have ht : t.HasFiniteSupport := signedFiniteSupport ((homologyLengthFiniteSupport h₃).subset
    (fun i hi hz => by
      have : Subsingleton ↑(S.X₃.homology i) := Module.length_eq_zero_iff.mp hz
      have hz' : Subsingleton (LinearMap.range (h.δ i (i - 1) (by
          change i - 1 + 1 = i; omega)).hom) :=
        (LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict _)).subsingleton
      exact hi (by simp [δ, imageLength])))
  have hpoint (i : ℤ) : a i + c i = b i + (t i - t (i + 1)) := by
    have hB := length_eq_image_add_image (h.homology_exact₂ i) (l₂ i) (l₃ i)
    have hC := length_eq_image_add_image
      (h.homology_exact₃ i (i - 1) (by change i - 1 + 1 = i; omega))
      (l₃ i) (l₁ (i - 1))
    have hA (j : ℤ) (hj : j = i + 1 - 1) :
        intLength (S.X₁.homology j) = δ (i + 1) + imageLength (homologyMap S.f j) := by
      subst j
      exact length_eq_image_add_image (h.homology_exact₁ _ _
        (by change i + 1 - 1 + 1 = i + 1; omega)) (l₁ _) (l₂ _)
    have hA' := hA i (by omega)
    have hC' : intLength (S.X₃.homology i) =
        imageLength (homologyMap S.g i) + δ i := hC
    have hp : intLength (S.X₁.homology i) + intLength (S.X₃.homology i) =
        intLength (S.X₂.homology i) + (δ i + δ (i + 1)) := by omega
    simpa only [a, b, c, t, Int.negOnePow_succ, Units.val_neg, neg_mul, sub_neg_eq_add,
      mul_add, add_assoc] using congrArg (fun x : ℤ => (i.negOnePow : ℤ) * x) hp
  let e : ℤ ≃ ℤ := Equiv.addRight 1
  have hte : (fun i => t (e i)).HasFiniteSupport :=
    ht.preimage e.injective.injOn
  have hs : (∑ᶠ i, (a i + c i)) = ∑ᶠ i, (b i + (t i - t (e i))) :=
    congrArg finsum (funext hpoint)
  have ha : a.HasFiniteSupport := signedHomologyFiniteSupport h₁
  have hb : b.HasFiniteSupport := signedHomologyFiniteSupport h₂
  have hc : c.HasFiniteSupport := signedHomologyFiniteSupport h₃
  have hzero : (∑ᶠ i, (t i - t (e i))) = 0 := calc
    _ = (∑ᶠ i, t i) - (∑ᶠ i, t (e i)) := finsum_sub_distrib ht hte
    _ = 0 := by rw [finsum_comp_equiv e, sub_self]
  change (∑ᶠ i, b i) = (∑ᶠ i, a i) + (∑ᶠ i, c i)
  calc
    _ = (∑ᶠ i, b i) + (∑ᶠ i, (t i - t (e i))) := by rw [hzero, add_zero]
    _ = ∑ᶠ i, (b i + (t i - t (e i))) := (finsum_add_distrib hb (ht.sub hte)).symm
    _ = ∑ᶠ i, (a i + c i) := hs.symm
    _ = _ := finsum_add_distrib ha hc

private theorem flatOfFree {M : ModuleCat.{u} R} (hM : Module.Free R M) : Module.Flat R M := by
  let := hM
  infer_instance

set_option maxHeartbeats 750000 in
theorem additiveLeft : Specs.additiveLeft.{u} := by
  intro R _ _ _ S G h₁ h₂ h₃ hg hs hi₁ hi₂ hi₃
  let h := tensorLeftComponents S G hs (fun i => flatOfFree (hg.2.1 i))
  let T := shortComplexOfExactComponents _ _ h
  change homologyLengthEuler T.X₂ = homologyLengthEuler T.X₁ + homologyLengthEuler T.X₃
  exact homologyLengthEuler_additive T (shortExactOfExactComponents _ _ h)
    (tensorBounded _ _ h₁.1 hg.1) (tensorBounded _ _ h₂.1 hg.1) (tensorBounded _ _ h₃.1 hg.1)
    (tensorFiniteLength _ _ h₁ hg hi₁) (tensorFiniteLength _ _ h₂ hg hi₂)
    (tensorFiniteLength _ _ h₃ hg hi₃)

set_option maxHeartbeats 750000 in
theorem additiveRight : Specs.additiveRight.{u} := by
  intro R _ _ _ F S hf h₁ h₂ h₃ hs hi₁ hi₂ hi₃
  let h := tensorRightComponents F S hs (fun i => flatOfFree (hf.2.1 i))
  let T := shortComplexOfExactComponents _ _ h
  change homologyLengthEuler T.X₂ = homologyLengthEuler T.X₁ + homologyLengthEuler T.X₃
  exact homologyLengthEuler_additive T (shortExactOfExactComponents _ _ h)
    (tensorBounded _ _ hf.1 h₁.1) (tensorBounded _ _ hf.1 h₂.1) (tensorBounded _ _ hf.1 h₃.1)
    (tensorFiniteLength _ _ hf h₁ hi₁) (tensorFiniteLength _ _ hf h₂ hi₂)
    (tensorFiniteLength _ _ hf h₃ hi₃)


private abbrev tensorFunctor (R : Type u) [CommRing R] :=
  (tensor R).map₂HomologicalComplex down down down

private def tensorHomotopyEquivLeft {F F' : Complex R} (e : HomotopyEquiv F F') (G : Complex R) :
    HomotopyEquiv (tensorTotal F G) (tensorTotal F' G) where
  hom := (tensorFunctor R).flip.obj G |>.map e.hom
  inv := (tensorFunctor R).flip.obj G |>.map e.inv
  homotopyHomInvId := by
    let T : Complex R ⥤ Complex R := (tensorFunctor R).flip.obj G
    change Homotopy (T.map _ ≫ T.map _) (𝟙 (T.obj _))
    rw [← T.map_comp, ← T.map_id]
    exact mapBifunctorMapHomotopy₁ e.homotopyHomInvId (𝟙 G) (tensor R) down
  homotopyInvHomId := by
    let T : Complex R ⥤ Complex R := (tensorFunctor R).flip.obj G
    change Homotopy (T.map _ ≫ T.map _) (𝟙 (T.obj _))
    rw [← T.map_comp, ← T.map_id]
    exact mapBifunctorMapHomotopy₁ e.homotopyInvHomId (𝟙 G) (tensor R) down

private def tensorHomotopyEquivRight (F : Complex R) {G G' : Complex R} (e : HomotopyEquiv G G') :
    HomotopyEquiv (tensorTotal F G) (tensorTotal F G') where
  hom := (tensorFunctor R).obj F |>.map e.hom
  inv := (tensorFunctor R).obj F |>.map e.inv
  homotopyHomInvId := by
    let T : Complex R ⥤ Complex R := (tensorFunctor R).obj F
    change Homotopy (T.map _ ≫ T.map _) (𝟙 (T.obj _))
    rw [← T.map_comp, ← T.map_id]
    exact mapBifunctorMapHomotopy₂ (𝟙 F) e.homotopyHomInvId (tensor R) down
  homotopyInvHomId := by
    let T : Complex R ⥤ Complex R := (tensorFunctor R).obj F
    change Homotopy (T.map _ ≫ T.map _) (𝟙 (T.obj _))
    rw [← T.map_comp, ← T.map_id]
    exact mapBifunctorMapHomotopy₂ (𝟙 F) e.homotopyInvHomId (tensor R) down

private theorem euler_eq_of_homotopyEquiv {K L : Complex R} (e : HomotopyEquiv K L) :
    homologyLengthEuler K = homologyLengthEuler L := by
  unfold homologyLengthEuler
  apply congrArg finsum
  funext i
  rw [(e.toHomologyIso i).toLinearEquiv.length_eq]

private theorem support_eq_of_homotopyEquiv {K L : Complex R} (e : HomotopyEquiv K L) :
    homologySupport K = homologySupport L := by
  unfold homologySupport
  simp only [(e.toHomologyIso _).toLinearEquiv.support_eq]

private theorem reversedKProjective (K : Complex R) (hK : Bounded K)
    (hp : ∀ i, Projective (K.X i)) : CochainComplex.IsKProjective (K.extend reverseDegrees) := by
  obtain ⟨a, _, h⟩ := hK
  let : ∀ i : ℤ, Projective ((K.extend reverseDegrees).X i) := fun i =>
    Projective.of_iso (K.extendXIso reverseDegrees (i := -i) (i' := i)
      (show - -i = i by omega)).symm (hp (-i))
  let : CochainComplex.IsStrictlyLE (K.extend reverseDegrees) (-a) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact (h (-i) (.inl (by omega))).of_iso
      (K.extendXIso reverseDegrees (i := -i) (i' := i) (show - -i = i by omega))
  exact CochainComplex.isKProjective_of_projective _ (-a)

private theorem quasiIso_isHomotopyEquivalence {F G : Complex R} (f : F ⟶ G)
    (hf : QuasiIso f) (hF : Bounded F) (hG : Bounded G)
    (pF : ∀ i, Projective (F.X i)) (pG : ∀ i, Projective (G.X i)) :
    homotopyEquivalences _ _ f := by
  let := reversedKProjective F hF pF
  let := reversedKProjective G hG pG
  exact (homotopyEquivalences_extendMap_iff f reverseDegrees).1
    ((CochainComplex.IsKProjective.quasiIso_iff _).1
      ((quasiIso_extendMap_iff f reverseDegrees).2 hf))

private theorem projectiveOfFree {M : ModuleCat.{u} R} (hM : Module.Free R M) : Projective M := by
  let := hM
  infer_instance

theorem quasiIsoLeft : Specs.quasiIsoLeft.{u} := by
  intro R _ _ _ F F' f G hF hF' _ hf h
  obtain ⟨e, _⟩ := quasiIso_isHomotopyEquivalence f hf hF.1 hF'.1
    (fun i => projectiveOfFree (hF.2.1 i)) (fun i => projectiveOfFree (hF'.2.1 i))
  refine ⟨?_, euler_eq_of_homotopyEquiv (tensorHomotopyEquivLeft e G)⟩
  simpa only [Isolated, ← support_eq_of_homotopyEquiv e] using h

theorem quasiIsoRight : Specs.quasiIsoRight.{u} := by
  intro R _ _ _ F G G' g _ hG hG' hg h
  obtain ⟨e, _⟩ := quasiIso_isHomotopyEquivalence g hg hG.1 hG'.1
    (fun i => projectiveOfFree (hG.2.1 i)) (fun i => projectiveOfFree (hG'.2.1 i))
  refine ⟨?_, euler_eq_of_homotopyEquiv (tensorHomotopyEquivRight F e)⟩
  simpa only [Isolated, ← support_eq_of_homotopyEquiv e] using h

private theorem freeOfFiniteProjective [IsLocalRing R] (F : Complex R)
    (hF : BoundedFiniteProjective F) : BoundedFiniteFree F := by
  refine ⟨hF.1, fun i => ?_, hF.2.2⟩
  let : Projective (F.X i) := hF.2.1 i
  let : Module.Projective R (F.X i) := inferInstance
  let : Module.Finite R (F.X i) := hF.2.2 i
  exact Module.free_of_flat_of_isLocalRing

private theorem homotopyEquiv_of_derivedIso [HasDerivedCategory.{u+1} (ModuleCat.{u} R)]
    {K L : Complex R} (hK : BoundedFiniteProjective K) (hL : BoundedFiniteProjective L)
    (e : DerivedCategory.Q.obj (K.extend reverseDegrees) ≅
      DerivedCategory.Q.obj (L.extend reverseDegrees)) :
    Nonempty (HomotopyEquiv K L) := by
  let := reversedKProjective K hK.1 hK.2.1
  let K' := K.extend reverseDegrees
  let L' := L.extend reverseDegrees
  let q := HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)
  let cmp := DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)
  obtain ⟨f, hf⟩ := (CochainComplex.IsKProjective.Qh_map_bijective K' (q.obj L')).surjective
    ((cmp.app K').hom ≫ e.hom ≫ (cmp.app L').inv)
  obtain ⟨f', rfl⟩ := q.map_surjective f
  obtain ⟨g, rfl⟩ := (reverseDegrees.extendFunctor (ModuleCat.{u} R)).map_surjective f'
  change DerivedCategory.Qh.map (q.map (extendMap g reverseDegrees)) = _ at hf
  have hq : DerivedCategory.Q.map (extendMap g reverseDegrees) = e.hom := by
    have h := cmp.hom.naturality (extendMap g reverseDegrees)
    change DerivedCategory.Qh.map (q.map (extendMap g reverseDegrees)) ≫ (cmp.app L').hom =
      (cmp.app K').hom ≫ DerivedCategory.Q.map (extendMap g reverseDegrees) at h
    apply (cancel_epi (cmp.app K').hom).1
    calc
      _ = DerivedCategory.Qh.map (q.map (extendMap g reverseDegrees)) ≫
          (cmp.app L').hom := h.symm
      _ = _ := by rw [hf]; simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let : IsIso (DerivedCategory.Q.map (extendMap g reverseDegrees)) := hq.symm ▸
    (inferInstance : IsIso e.hom)
  have hg := (quasiIso_extendMap_iff g reverseDegrees).1
    ((DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} R) _).1 inferInstance)
  obtain ⟨h, _⟩ := quasiIso_isHomotopyEquivalence g hg hK.1 hL.1 hK.2.1 hL.2.1
  exact ⟨h⟩

abbrev perfectPairing : Specs.perfectPairingType.{u} := @Specs.perfectPairing

theorem perfectPairingWellDefined : Specs.perfectPairingWellDefined.{u} := by
  intro R _ _ _ _ D E h F G hF hG
  let F₀ := h.choose
  let G₀ := h.choose_spec.choose
  obtain ⟨hF₀, hG₀, hiso⟩ := h.choose_spec.choose_spec
  obtain ⟨hFp, ⟨eF⟩⟩ := hF
  obtain ⟨hGp, ⟨eG⟩⟩ := hG
  obtain ⟨eF₀⟩ := hF₀.2
  obtain ⟨eG₀⟩ := hG₀.2
  obtain ⟨f⟩ := homotopyEquiv_of_derivedIso hFp hF₀.1 (eF ≪≫ eF₀.symm)
  obtain ⟨g⟩ := homotopyEquiv_of_derivedIso hGp hG₀.1 (eG ≪≫ eG₀.symm)
  have hi : Isolated F G := by
    unfold Isolated
    rw [support_eq_of_homotopyEquiv f, support_eq_of_homotopyEquiv g]
    exact hiso
  refine ⟨hi, tensorFiniteLength F G (freeOfFiniteProjective F hFp)
    (freeOfFiniteProjective G hGp) hi, ?_⟩
  exact (euler_eq_of_homotopyEquiv (tensorHomotopyEquivLeft f G)).trans
    (euler_eq_of_homotopyEquiv (tensorHomotopyEquivRight F₀ g))

section Resolutions

open P103.Specs.Ch10.Comparison (LeftResolution)
open P103.Specs.Ch10.Complexes (extendNonnegativeChain nonnegativeChainEmbedding SupportedIn)
open P103.Ch10.Complexes (extendNonnegativeChain_supported)

private theorem extendedTermZero (K : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℤ) (hi : i < 0) :
    IsZero ((extendNonnegativeChain K).X i) :=
  ModuleCat.isZero_iff_subsingleton.mpr (extendNonnegativeChain_supported K i (by simpa using hi))

private theorem nonnegativeTensor (F G : Complex R)
    (hF : ∀ i < 0, IsZero (F.X i)) (hG : ∀ i < 0, IsZero (G.X i))
    (n : ℤ) (hn : n < 0) : IsZero ((tensorTotal F G).X n) := by
  rw [IsZero.iff_id_eq_zero]
  apply mapBifunctor.hom_ext
  intro i j hij
  change i + j = n at hij
  by_cases hi : i < 0
  · exact ((tensorRight (G.X j)).map_isZero (hF i hi)).eq_of_src _ _
  · exact ((tensorLeft (F.X i)).map_isZero (hG j (by omega))).eq_of_src _ _

private def explicitHomologyEquiv {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{u} R) c) (i : ι) :
    K.homology i ≃ₗ[R] P103.Specs.Ch10.Complexes.Homology K i := by
  refine (K.sc i).moduleCatHomologyIso.toLinearEquiv.trans (Submodule.quotEquivOfEq _ _ ?_)
  change LinearMap.range (K.sc i).moduleCatToCycles =
    P103.Specs.Ch10.Complexes.cycleBoundaries K i
  ext z
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, congrArg Subtype.val hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩

private def resolutionAugmentation {M : ModuleCat.{u} R} (P : LeftResolution R M) :
    (extendNonnegativeChain P.complex).X 0 ⟶ M :=
  ModuleCat.ofHom (P.ε.comp (P.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).hom.hom)

private theorem resolutionAugmentation_surjective {M : ModuleCat.{u} R}
    (P : LeftResolution R M) : Function.Surjective (resolutionAugmentation P).hom :=
  P.surjective.comp (P.complex.extendXIso nonnegativeChainEmbedding (i := 0) rfl).toLinearEquiv.surjective

private abbrev coefficientComplex (M : ModuleCat.{u} R) (G : Complex R) : Complex R :=
  ((tensorLeft M).mapHomologicalComplex down).obj G

private def columnAugmentation {M : ModuleCat.{u} R} (P : LeftResolution R M) (G : Complex R) :
    (tensorBicomplex (extendNonnegativeChain P.complex) G).X 0 ⟶ coefficientComplex M G where
  f j := resolutionAugmentation P ▷ G.X j
  comm' i j _ := by
    change (resolutionAugmentation P ▷ G.X i) ≫ (M ◁ G.d i j) =
      ((extendNonnegativeChain P.complex).X 0 ◁ G.d i j) ≫ (resolutionAugmentation P ▷ G.X j)
    rw [whisker_exchange]

set_option backward.isDefEq.respectTransparency false in
private theorem existsTensorAugmentation {M N : ModuleCat.{u} R}
    (P : LeftResolution R M) (Q : LeftResolution R N)
    (hQ : ∀ j, Module.Free R ((extendNonnegativeChain Q.complex).X j)) :
    ∃ f : tensorTotal (extendNonnegativeChain P.complex) (extendNonnegativeChain Q.complex) ⟶
      coefficientComplex M (extendNonnegativeChain Q.complex),
      P103.Specs.Ch10.Complexes.QuasiIsomorphism f := by
  let F := extendNonnegativeChain P.complex
  let G := extendNonnegativeChain Q.complex
  let K := tensorBicomplex F G
  let L := coefficientComplex M G
  let ε := columnAugmentation P G
  have w : K.d 1 0 ≫ ε = 0 := by
    ext j : 1
    change (tensorRight (G.X j)).map (F.d 1 0) ≫
      (tensorRight (G.X j)).map (resolutionAugmentation P) = 0
    rw [← (tensorRight (G.X j)).map_comp]
    have he : F.d 1 0 ≫ resolutionAugmentation P = 0 := by
      apply ModuleCat.hom_ext
      exact (P103.Ch11.TorBalance.resolution_extended_exact_zero P).linearMap_comp_eq_zero
    rw [he, Functor.map_zero]
  have hs : P103.Specs.Ch10.TotalComplexAssembly.SupportedQuadrant K 0 0 := by
    intro i j hij
    apply ModuleCat.isZero_iff_subsingleton.mp
    change IsZero ((tensorRight (G.X j)).obj (F.X i))
    rcases hij with hi | hj
    · exact (tensorRight (G.X j)).map_isZero (extendedTermZero P.complex i hi)
    · exact (tensorLeft (F.X i)).map_isZero (extendedTermZero Q.complex j hj)
  have hL : SupportedIn L (Set.Ici 0) := by
    intro j hj
    exact ModuleCat.isZero_iff_subsingleton.mp
      ((tensorLeft M).map_isZero (extendedTermZero Q.complex j (by simpa using hj)))
  have hr := P103.Ch11.TorBalance.augmentedColumns_rows_acyclic K L ε w
    (fun j => LinearMap.rTensor_surjective (G.X j) (resolutionAugmentation_surjective P))
    (fun j => by
      let := flatOfFree (hQ j)
      exact Module.Flat.rTensor_exact (G.X j)
        (P103.Ch11.TorBalance.resolution_extended_exact_zero P))
    (fun n j => by
      let := flatOfFree (hQ j)
      exact Module.Flat.rTensor_exact (G.X j)
        (P103.Ch11.TorBalance.resolution_extended_exact_succ P n))
  obtain ⟨f, hf, _⟩ := P103.Ch11.TorBalance.totalAugmentation_quasi K L ε w
    (P103.Ch11.TorBalance.column_isZero_of_supported K hs) 0 hs hL hr
  exact ⟨f, hf⟩

private def coefficientFunctorIso (M : ModuleCat.{u} R) :
    tensorLeft M ≅
      (P103.Specs.Ch12.TorBaseChange.coefficientTensorFunctor R R M :
        ModuleCat.{u} R ⥤ ModuleCat.{u} R) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro A B f
    simp only [Iso.refl_hom]
    erw [Category.comp_id])

private def coefficientRestrictionIso (M N : ModuleCat.{u} R) (Q : LeftResolution R N) :
    (coefficientComplex M (extendNonnegativeChain Q.complex)).restriction nonnegativeChainEmbedding ≅
      P103.Specs.Ch12.TorBaseChange.coefficientComplex (S := R) Q.complex M :=
  P103.Ch11.TorBalance.restrictExtendMapIso Q.complex (tensorLeft M) ≪≫
    HomologicalComplex.Hom.isoOfComponents (fun i => (coefficientFunctorIso M).app (Q.complex.X i))
      (by
        intro i j _
        exact ((coefficientFunctorIso M).hom.naturality (Q.complex.d i j)).symm)

private theorem resolutionProjective {N : ModuleCat.{u} R} (Q : LeftResolution R N)
    (hQ : ∀ j, Module.Free R ((extendNonnegativeChain Q.complex).X j)) : Q.IsProjective := by
  intro j
  let e := Q.complex.extendXIso nonnegativeChainEmbedding (i := j) rfl
  let : Projective (Q.complex.X j) := Projective.of_iso e (projectiveOfFree (hQ (j : ℤ)))
  exact (Q.complex.X j).projective_of_module_projective

private theorem tensorResolutionHomology (M N : ModuleCat.{u} R)
    (P : LeftResolution R M) (Q : LeftResolution R N)
    (hQ : ∀ j, Module.Free R ((extendNonnegativeChain Q.complex).X j)) (n : ℕ) :
    Nonempty ((tensorTotal (extendNonnegativeChain P.complex)
      (extendNonnegativeChain Q.complex)).homology (n : ℤ) ≃ₗ[R] IsolatedTorSupport.Tor M N n) := by
  obtain ⟨f, hf⟩ := existsTensorAugmentation P Q hQ
  let L := coefficientComplex M (extendNonnegativeChain Q.complex)
  have hL : SupportedIn L (Set.Ici 0) := by
    intro j hj
    exact ModuleCat.isZero_iff_subsingleton.mp
      ((tensorLeft M).map_isZero (extendedTermZero Q.complex j (by simpa using hj)))
  let r := P103.Ch11.TorBalance.restrictionHomologyEquiv L hL n
  let I := coefficientRestrictionIso M N Q
  let e := LinearEquiv.ofBijective _ (P103.Ch11.TorBalance.quasiIsomorphism_of_iso_any I n)
  exact ⟨(explicitHomologyEquiv _ _).trans
    ((LinearEquiv.ofBijective _ (hf (n : ℤ))).trans
      (r.symm.trans (e.trans (IsolatedTorSupport.torRightEquiv M N Q (resolutionProjective Q hQ) n).symm)))⟩

private theorem resolutionSupport (M : ModuleCat.{u} R) (P : LeftResolution R M) :
    homologySupport (extendNonnegativeChain P.complex) = Module.support R M := by
  let F := extendNonnegativeChain P.complex
  have e (n : ℕ) : F.homology (n : ℤ) ≃ₗ[R]
      P103.Specs.Ch10.Complexes.Homology P.complex n :=
    (P.complex.extendHomologyIso nonnegativeChainEmbedding (j := n) rfl).toLinearEquiv.trans
      (explicitHomologyEquiv P.complex n)
  obtain ⟨e₀, _⟩ := P103.Ch10.ProjectiveResolutions.homology_zero R M P
  have hzero : Module.support R (F.homology 0) = Module.support R M :=
    ((e 0).trans e₀).support_eq
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    cases i with
    | ofNat n =>
      cases n with
      | zero =>
        rwa [← hzero]
      | succ n =>
        let : Subsingleton (P103.Specs.Ch10.Complexes.Homology P.complex (n + 1)) :=
          P103.Ch10.ProjectiveResolutions.homology_succ R M P n
        let : Subsingleton ↑(F.homology ((n + 1 : ℕ) : ℤ)) := (e (n + 1)).injective.subsingleton
        have hEmpty : Module.support R (F.homology ((n + 1 : ℕ) : ℤ)) = ∅ :=
          Module.support_eq_empty
        exact False.elim ((Set.notMem_empty p) (hEmpty ▸ hi))
    | negSucc n =>
      let : Subsingleton ↑(F.homology (Int.negSucc n)) :=
        ModuleCat.isZero_iff_subsingleton.mp
          (homology_isZero_of_X F _ (extendedTermZero P.complex _ (Int.negSucc_lt_zero n)))
      have hEmpty : Module.support R (F.homology (Int.negSucc n)) = ∅ := Module.support_eq_empty
      exact False.elim ((Set.notMem_empty p) (hEmpty ▸ hi))
  · intro p hp
    exact Set.mem_iUnion.mpr ⟨0, hzero.symm ▸ hp⟩

theorem agreesWithIntersectionEuler : Specs.agreesWithIntersectionEuler.{u} := by
  intro R _ _ M N _ _ P Q _ hQ h
  refine ⟨?_, ?_⟩
  · unfold Isolated
    rw [resolutionSupport M P, resolutionSupport N Q]
    exact (IsolatedTorSupport.isolated_tensor_iff M N).mp h
  let d := IsolatedIntersectionEuler.regularLocalDimension R
  let F := extendNonnegativeChain P.complex
  let G := extendNonnegativeChain Q.complex
  let T := tensorTotal F G
  let s (i : ℤ) := (i.negOnePow : ℤ) * intLength (T.homology i)
  let e : ℕ ↪ ℤ := ⟨fun n => (n : ℤ), Int.ofNat_injective⟩
  have hl (n : ℕ) : Module.length R (T.homology (n : ℤ)) =
      Module.length R (IsolatedTorSupport.Tor M N n) :=
    (tensorResolutionHomology M N P Q hQ.2.1 n).some.length_eq
  have hvan : ∀ n : ℕ, d < n → Subsingleton (IsolatedTorSupport.Tor M N n) :=
    IsolatedIntersectionEuler.tor_vanishes_above M N d
      (IsolatedIntersectionEuler.ringKrullDim_eq_regularLocalDimension R)
  have hs : Function.support s ⊆ ↑((Finset.range (d + 1)).map e) := by
    intro i hi
    by_cases hneg : i < 0
    · have hz := nonnegativeTensor F G (extendedTermZero P.complex) (extendedTermZero Q.complex) i hneg
      let : Subsingleton ↑(T.homology i) :=
        ModuleCat.isZero_iff_subsingleton.mp (homology_isZero_of_X T i hz)
      exact False.elim (hi (by simp [s, intLength]))
    · have he : (i.toNat : ℤ) = i := Int.toNat_of_nonneg (by omega)
      have hn : i.toNat ≤ d := by
        by_contra! h
        let : Subsingleton (IsolatedTorSupport.Tor M N i.toNat) := hvan i.toNat h
        have hzTor : Module.length R (IsolatedTorSupport.Tor M N i.toNat) = 0 :=
          Module.length_eq_zero
        have hz := (hl i.toNat).trans hzTor
        rw [he] at hz
        exact hi (by simp only [s, intLength, hz, ENat.toNat_zero, Nat.cast_zero, mul_zero])
      exact Finset.mem_map.mpr ⟨i.toNat, Finset.mem_range.mpr (by omega), he⟩
  change (∑ᶠ i, s i) = IsolatedIntersectionEuler.Specs.intersectionEuler M N
  rw [finsum_eq_sum_of_support_subset _ hs, Finset.sum_map]
  unfold IsolatedIntersectionEuler.Specs.intersectionEuler IsolatedIntersectionEuler.Specs.cutoffEuler
  apply Finset.sum_congr rfl
  intro i hi
  change (((i : ℤ).negOnePow) : ℤ) * intLength (T.homology (i : ℤ)) = _
  simp only [Int.coe_negOnePow_natCast, intLength, hl]

end Resolutions

end CommutativeAlgebraNotes.Intersection.SupportedEulerPairing
