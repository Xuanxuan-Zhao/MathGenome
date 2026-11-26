import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.TensorComplexIsolatedHomology
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.RingTheory.TensorProduct.Finite
import MathGenome.Internal.AlgebraCore.P103.Ch06.FiniteColength

open CategoryTheory Category Limits HomologicalComplex MonoidalCategory

noncomputable section

universe u v

namespace CommutativeAlgebraNotes.Intersection

private abbrev down := ComplexShape.down ℤ
private abbrev up := ComplexShape.up ℤ
private abbrev tensorFunctor (R : Type u) [CommRing R] := curriedTensor (ModuleCat.{u} R)

set_option backward.isDefEq.respectTransparency false in
/-- A bounded-below acyclic chain complex of projective objects is contractible. -/
private theorem contractibleOfBoundedBelow {C : Type*} [Category* C] [Abelian C]
    (K : ChainComplex C ℤ) (a : ℤ) (hK : ∀ i < a, IsZero (K.X i))
    (hproj : ∀ i, Projective (K.X i)) (he : K.Acyclic) :
    Nonempty (Homotopy (𝟙 K) 0) := by
  let e := ComplexShape.embeddingUpIntDownInt
  let L : CochainComplex C ℤ := K.restriction e
  have hL : L.Acyclic := by
    intro i
    apply (exactAt_iff_isZero_homology L i).mpr
    apply (he (-i)).isZero_homology.of_iso
    exact K.restrictionHomologyIso e (i - 1) i (i + 1)
      (up.prev_eq' (by change i - 1 + 1 = i; omega))
      (up.next_eq' (by change i + 1 = i + 1; rfl))
      (i' := -i + 1) (j' := -i) (k' := -i - 1)
      (by change -(i - 1) = -i + 1; omega) rfl
      (by change -(i + 1) = -i - 1; omega)
      (down.prev_eq' (by change -i + 1 = -i + 1; rfl))
      (down.next_eq' (by change -i - 1 + 1 = -i; omega))
  let : ∀ i, Projective (L.X i) := fun i => hproj (-i)
  let : L.IsStrictlyLE (-a) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact hK (-i) (by omega)
  let : L.IsKProjective := CochainComplex.isKProjective_of_projective L (-a)
  let H := CochainComplex.IsKProjective.homotopyZero (𝟙 L) hL
  -- Transport the homotopy by reversing the degrees.
  let t (i : ℤ) : K.X i ≅ L.X (-i) := K.XIsoOfEq (by change i = - -i; omega)
  have td (i j : ℤ) :
      K.d i j ≫ (t j).hom = (t i).hom ≫ L.d (-i) (-j) := by
    change K.d i j ≫ _ = _ ≫ K.d (e.f (-i)) (e.f (-j))
    simp only [t, d_comp_XIsoOfEq_hom, XIsoOfEq_hom_comp_d]
  refine ⟨{
    hom := fun i j => (t i).hom ≫ H.hom (-i) (-j) ≫ (t j).inv
    zero := ?_
    comm := ?_ }⟩
  · intro i j hij
    have hu : ¬ up.Rel (-j) (-i) := by
      change ¬ -j + 1 = -i
      change ¬ i + 1 = j at hij
      omega
    simp [H.zero _ _ hu]
  · intro i
    have hn : down.Rel i (i - 1) := by change i - 1 + 1 = i; omega
    have hp : down.Rel (i + 1) i := rfl
    have hnu : up.Rel (-i) (-(i - 1)) := by change -i + 1 = -(i - 1); omega
    have hpu : up.Rel (-(i + 1)) (-i) := by change -(i + 1) + 1 = -i; omega
    rw [dNext_eq _ hn, prevD_eq _ hp]
    have hc := H.comm (-i)
    rw [dNext_eq _ hnu, prevD_eq _ hpu] at hc
    simp only [HomologicalComplex.id_f, HomologicalComplex.zero_f, add_zero] at hc ⊢
    have td' (j k : ℤ) : (t j).inv ≫ K.d j k = L.d (-j) (-k) ≫ (t k).inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, td]
    calc
      𝟙 (K.X i) = (t i).hom ≫ 𝟙 (L.X (-i)) ≫ (t i).inv := by simp
      _ = _ := by
        nth_rw 1 [hc]
        simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
          td', ← Category.assoc (K.d i (i - 1)), td, Category.assoc]

theorem boundedExactProjectiveContractible : Specs.boundedExactProjectiveContractibleType.{u,v} := by
  intro R _ K hK hproj he
  obtain ⟨a, _, ha⟩ := hK
  exact contractibleOfBoundedBelow K a (fun i hi => ha i (.inl hi)) hproj he

private theorem exactOfContractible {R : Type u} [CommRing R]
    {K : ChainComplex (ModuleCat.{u} R) ℤ} (h : Homotopy (𝟙 K) 0) : K.Acyclic := by
  intro i
  apply (exactAt_iff_isZero_homology K i).mpr
  exact (IsZero.iff_id_eq_zero _).mpr (by simpa using h.homologyMap_eq i)

private theorem tensorMap_id {R : Type u} [CommRing R]
    (F G : ChainComplex (ModuleCat.{u} R) ℤ) : tensorHom (𝟙 F) (𝟙 G) = 𝟙 (tensorTotal F G) := by
  ext n : 1
  apply mapBifunctor.hom_ext
  intro i j h
  simp

private theorem tensorMap_zero_left {R : Type u} [CommRing R]
    (F G : ChainComplex (ModuleCat.{u} R) ℤ) :
    tensorHom (0 : F ⟶ F) (𝟙 G) = (0 : tensorTotal F G ⟶ _) := by
  ext n : 1
  apply mapBifunctor.hom_ext
  intro i j h
  simp

private theorem tensorMap_zero_right {R : Type u} [CommRing R]
    (F G : ChainComplex (ModuleCat.{u} R) ℤ) :
    tensorHom (𝟙 F) (0 : G ⟶ G) = (0 : tensorTotal F G ⟶ _) := by
  ext n : 1
  apply mapBifunctor.hom_ext
  intro i j h
  simp

/-- Tensoring a contractible complex in either slot gives a contractible signed total. -/
theorem tensorTotalContractible : Specs.tensorTotalContractibleType.{u} := by
  intro R _ F G h
  rcases h with ⟨⟨h⟩⟩ | ⟨⟨h⟩⟩
  · exact ⟨by simpa only [← tensorMap_id F G, ← tensorMap_zero_left F G] using
      mapBifunctorMapHomotopy₁ h (𝟙 G) (tensorFunctor R) down⟩
  · exact ⟨by simpa only [← tensorMap_id F G, ← tensorMap_zero_right F G] using
      mapBifunctorMapHomotopy₂ (𝟙 F) h (tensorFunctor R) down⟩

section TensorComparison

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D] [HasCoproducts.{0} C] [HasCoproducts.{0} D]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalPreadditive C] [MonoidalPreadditive D]
  (E : C ⥤ D) [E.Additive] [E.Monoidal] [PreservesColimitsOfSize.{0,0} E]

/-- The comparison of degreewise scalar extension with the coproduct tensor terms. -/
private def tensorTermComparison (F G : ChainComplex C ℤ) (n : ℤ) :
    (tensorObj ((E.mapHomologicalComplex down).obj F) ((E.mapHomologicalComplex down).obj G)).X n ≅
      ((E.mapHomologicalComplex down).obj (tensorObj F G)).X n :=
  (Sigma.mapIso (fun i : {i : ℤ × ℤ // i.1 + i.2 = n} =>
    Functor.Monoidal.μIso E (F.X i.1.1) (G.X i.1.2))) ≪≫
      (PreservesCoproduct.iso E
        (fun i : {i : ℤ × ℤ // i.1 + i.2 = n} => F.X i.1.1 ⊗ G.X i.1.2)).symm

omit [HasZeroObject C] [HasZeroObject D] in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private lemma inclusionTensorTermComparison (F G : ChainComplex C ℤ)
    (i j n : ℤ) (h : i + j = n) :
    ιTensorObj ((E.mapHomologicalComplex down).obj F) ((E.mapHomologicalComplex down).obj G) i j n h ≫
        (tensorTermComparison E F G n).hom =
      Functor.LaxMonoidal.μ E (F.X i) (G.X j) ≫
        E.map (ιTensorObj F G i j n h) := by
  let p : {p : ℤ × ℤ // p.1 + p.2 = n} := ⟨(i, j), h⟩
  change Sigma.ι (fun k : {p : ℤ × ℤ // p.1 + p.2 = n} =>
      E.obj (F.X k.1.1) ⊗ E.obj (G.X k.1.2)) p ≫ _ =
    _ ≫ E.map (Sigma.ι (fun k : {p : ℤ × ℤ // p.1 + p.2 = n} =>
      F.X k.1.1 ⊗ G.X k.1.2) p)
  unfold tensorTermComparison
  rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, Sigma.ι_mapIso_hom,
    Category.assoc, PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]
  rfl

omit [HasZeroObject C] in
private lemma inclusionTensorDifferential
    (F G : ChainComplex C ℤ) (i j n m : ℤ)
    (h : i + j = n) (hm : m + 1 = n) :
    ιTensorObj F G i j n h ≫ (tensorObj F G).d n m =
      (F.d i (i - 1) ▷ G.X j) ≫ ιTensorObj F G (i - 1) j m (by omega) +
        i.negOnePow • ((F.X i ◁ G.d j (j - 1)) ≫
          ιTensorObj F G i (j - 1) m (by omega)) := by
  have hi : down.Rel i (i - 1) := by change i - 1 + 1 = i; omega
  have hj : down.Rel j (j - 1) := by change j - 1 + 1 = j; omega
  rw [mapBifunctor.d_eq, Preadditive.comp_add,
    mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq _ _ _ _ hi _ _ (show i - 1 + j = m by omega),
    mapBifunctor.d₂_eq _ _ _ _ _ hj _ (show i + (j - 1) = m by omega)]
  exact congrArg (fun x => x + i.negOnePow •
    ((F.X i ◁ G.d j (j - 1)) ≫ ιTensorObj F G i (j - 1) m (by omega))) (one_smul _ _)

set_option backward.isDefEq.respectTransparency false in
private def monoidalFunctorTensorIso (F G : ChainComplex C ℤ) :
    tensorObj ((E.mapHomologicalComplex down).obj F) ((E.mapHomologicalComplex down).obj G) ≅
      (E.mapHomologicalComplex down).obj (tensorObj F G) := by
  let F' := (E.mapHomologicalComplex down).obj F
  let G' := (E.mapHomologicalComplex down).obj G
  refine HomologicalComplex.Hom.isoOfComponents (tensorTermComparison E F G) ?_
  intro n m hnm
  change m + 1 = n at hnm
  apply mapBifunctor.hom_ext
  intro i j hij
  change i + j = n at hij
  change ιTensorObj F' G' i j n hij ≫
      (tensorTermComparison E F G n).hom ≫ E.map ((tensorObj F G).d n m) =
    ιTensorObj F' G' i j n hij ≫ (tensorObj F' G').d n m ≫
      (tensorTermComparison E F G m).hom
  rw [inclusionTensorTermComparison_assoc, ← E.map_comp,
    inclusionTensorDifferential _ _ _ _ _ _ hij hnm,
    ← Category.assoc (ιTensorObj F' G' i j n hij),
    inclusionTensorDifferential _ _ _ _ _ _ hij hnm]
  simp only [Functor.map_add, Functor.map_units_smul, Functor.map_comp,
    Preadditive.comp_add, Preadditive.add_comp, Linear.comp_units_smul,
    Linear.units_smul_comp, Category.assoc]
  rw [inclusionTensorTermComparison E F G (i - 1) j m (by omega),
      inclusionTensorTermComparison E F G i (j - 1) m (by omega)]
  simp only [F', G', Functor.mapHomologicalComplex_obj_d, Functor.mapHomologicalComplex_obj_X]
  rw [Functor.LaxMonoidal.μ_natural_left_assoc E, Functor.LaxMonoidal.μ_natural_right_assoc E]

end TensorComparison

section BaseChange

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

private abbrev extend := ModuleCat.extendScalars.{u,u,u} f

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts

private theorem extendAdditive : (extend f).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

attribute [local instance] extendAdditive

private abbrev extendComplex := (extend f).mapHomologicalComplex down

private lemma extendProjective (M : ModuleCat.{u} R) (hM : Projective M) :
    Projective ((extend f).obj M) := by
  let : (ModuleCat.restrictScalars.{u,u,u} f).PreservesEpimorphisms :=
    ⟨fun {X Y} g hg => (ModuleCat.epi_iff_surjective _).mpr
      ((ModuleCat.epi_iff_surjective g).mp hg)⟩
  exact (ModuleCat.extendRestrictScalarsAdj f).map_projective M hM

private lemma extendBounded {K : ChainComplex (ModuleCat.{u} R) ℤ} (hK : Bounded K) :
    Bounded ((extendComplex f).obj K) := by
  obtain ⟨a, b, h⟩ := hK
  exact ⟨a, b, fun i hi => (extend f).map_isZero (h i hi)⟩

private def extendHomology (hf : f.Flat) (K : ChainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    ((extendComplex f).obj K).homology i ≅ (extend f).obj (K.homology i) := by
  let : PreservesFiniteLimits (extend f) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  exact (K.sc i).mapHomologyIso (extend f)

end BaseChange

section Localization

attribute [local instance] extendAdditive

variable {R : Type u} [CommRing R]

private abbrev primeMap (p : PrimeSpectrum R) := algebraMap R (Localization.AtPrime p.asIdeal)

private lemma primeMapFlat (p : PrimeSpectrum R) : (primeMap p).Flat :=
  RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ p.asIdeal.primeCompl)

private lemma localizedExactAt (p : PrimeSpectrum R)
    (K : ChainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    ((extendComplex (primeMap p)).obj K).ExactAt i ↔ p ∉ Module.support R (K.homology i) := by
  rw [exactAt_iff_isZero_homology, Module.notMem_support_iff]
  let e := extendHomology (primeMap p) (primeMapFlat p) K i
  let S := Localization.AtPrime p.asIdeal
  let A := (ModuleCat.restrictScalars (primeMap p)).obj (ModuleCat.of S S)
  let eA : S ≃ₗ[R] A :=
    { toEquiv := Equiv.refl S
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        change (r • x : S) = (primeMap p) r * x
        exact Algebra.smul_def r x }
  let e' : LocalizedModule p.asIdeal.primeCompl (K.homology i) ≃
      ((extend (primeMap p)).obj (K.homology i)) :=
    (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl (K.homology i)).toEquiv.trans
      (TensorProduct.congr eA (LinearEquiv.refl R (K.homology i))).toEquiv
  constructor
  · intro h
    let : Subsingleton ↑((extend (primeMap p)).obj (K.homology i)) :=
      ModuleCat.isZero_iff_subsingleton.mp (h.of_iso e.symm)
    exact e'.injective.subsingleton
  · intro h
    let : Subsingleton (LocalizedModule p.asIdeal.primeCompl (K.homology i)) := h
    have h' : Subsingleton ↑((extend (primeMap p)).obj (K.homology i)) :=
      e'.surjective.subsingleton
    exact (ModuleCat.isZero_iff_subsingleton.mpr h').of_iso e

private theorem localizedContractible (p : PrimeSpectrum R)
    (K : ChainComplex (ModuleCat.{u} R) ℤ) (hK : Bounded K)
    (hproj : ∀ i, Projective (K.X i)) (hp : p ∉ homologySupport K) :
    Nonempty (Homotopy (𝟙 ((extendComplex (primeMap p)).obj K)) 0) := by
  apply boundedExactProjectiveContractible _ (extendBounded _ hK)
    (fun i => extendProjective _ _ (hproj i))
  intro i
  exact (localizedExactAt p K i).2 (fun h => hp (Set.mem_iUnion.mpr ⟨i, h⟩))

private theorem tensorHomologySupport (F G : ChainComplex (ModuleCat.{u} R) ℤ)
    (hF : Bounded F) (hG : Bounded G)
    (hFp : ∀ i, Projective (F.X i)) (hGp : ∀ i, Projective (G.X i)) :
    homologySupport (tensorTotal F G) ⊆ homologySupport F ∩ homologySupport G := by
  classical
  intro p hp
  by_contra h
  have hd : p ∉ homologySupport F ∨ p ∉ homologySupport G := not_and_or.mp h
  have htot := tensorTotalContractible ((extendComplex (primeMap p)).obj F)
    ((extendComplex (primeMap p)).obj G)
    (hd.imp (localizedContractible p F hF hFp) (localizedContractible p G hG hGp))
  obtain ⟨hh⟩ := htot
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
  apply ((localizedExactAt p (tensorTotal F G) i).mp ?_) hi
  exact ((exactOfContractible hh) i).of_iso
    (monoidalFunctorTensorIso (extend (primeMap p)) F G)

end Localization

private theorem finiteTensorTerm {R : Type u} [CommRing R]
    (F G : ChainComplex (ModuleCat.{u} R) ℤ) (hF : Bounded F)
    (hFfin : ∀ i, Module.Finite R (F.X i)) (hGfin : ∀ j, Module.Finite R (G.X j))
    (n : ℤ) : Module.Finite R ((tensorTotal F G).X n) := by
  classical
  obtain ⟨a, b, h⟩ := hF
  let I := {i : ℤ // i ∈ Finset.Icc a b}
  let A (i : I) := F.X i.val ⊗ G.X (n - i.val)
  let inc (i : I) : A i ⟶ (tensorTotal F G).X n :=
    ιTensorObj F G i.val (n - i.val) n (by omega)
  let g := Sigma.desc inc
  have hg : Epi g := by
    constructor
    intro Z f₁ f₂ eq
    apply mapBifunctor.hom_ext
    intro i j hr
    change i + j = n at hr
    by_cases hmem : i ∈ Finset.Icc a b
    · have hj : j = n - i := by omega
      subst j
      have he := congrArg (fun f => Sigma.ι A (⟨i, hmem⟩ : I) ≫ f) eq
      simpa only [g, Category.assoc, Sigma.ι_comp_desc_assoc] using he
    · have hout : i < a ∨ b < i := by
        simp only [Finset.mem_Icc] at hmem
        omega
      exact ((tensorRight (G.X j)).map_isZero (h i hout)).eq_of_src _ _
  have : ∀ i : I, Module.Finite R (A i) := fun i => by
    let : Module.Finite R (F.X i.val) := hFfin _
    let : Module.Finite R (G.X (n - i.val)) := hGfin _
    change Module.Finite R (TensorProduct R (F.X i.val) (G.X (n - i.val)))
    infer_instance
  let e := (ModuleCat.coprodIsoDirectSum A).toLinearEquiv
  have : Module.Finite R (∐ A : ModuleCat.{u} R) :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  exact Module.Finite.of_surjective g.hom ((ModuleCat.epi_iff_surjective g).mp hg)

private theorem finiteHomology {R : Type u} [CommRing R] [IsNoetherianRing R]
    (K : ChainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) [Module.Finite R (K.X i)] :
    Module.Finite R (K.homology i) := by
  have : Module.Finite R (K.cycles i) :=
    Module.Finite.of_injective (K.iCycles i).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  exact Module.Finite.of_surjective (K.homologyπ i).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

private theorem finiteLengthOfSupport {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (M : Type v) [AddCommGroup M]
    [Module R M] [Module.Finite R M]
    (h : Module.support R M ⊆ {IsLocalRing.closedPoint R}) : IsFiniteLength R M := by
  rcases subsingleton_or_nontrivial M with hM | hM
  · exact IsFiniteLength.of_subsingleton
  · apply P103.Ch06.FiniteColength.finite_length_of_support_singleton R M
    exact Set.Subset.antisymm h (Set.singleton_subset_iff.mpr (IsLocalRing.closedPoint_mem_support R M))

/-- Isolated intersection of the homology supports gives finite-length homology
for every degree of the signed tensor total. -/
theorem tensorTotalFiniteLength : Specs.tensorTotalFiniteLengthType.{u} := by
  intro R _ _ _ F G hF hG hFfree hFfin hGfree hGfin h i
  have hFp (j : ℤ) : Projective (F.X j) := by
    let : Module.Free R (F.X j) := hFfree j
    infer_instance
  have hGp (j : ℤ) : Projective (G.X j) := by
    let : Module.Free R (G.X j) := hGfree j
    infer_instance
  let : Module.Finite R ((tensorTotal F G).X i) := finiteTensorTerm F G hF hFfin hGfin i
  let : Module.Finite R ((tensorTotal F G).homology i) := finiteHomology (tensorTotal F G) i
  apply finiteLengthOfSupport
  intro p hp
  exact h (tensorHomologySupport F G hF hG hFp hGp (Set.mem_iUnion.mpr ⟨i, hp⟩))

end CommutativeAlgebraNotes.Intersection
