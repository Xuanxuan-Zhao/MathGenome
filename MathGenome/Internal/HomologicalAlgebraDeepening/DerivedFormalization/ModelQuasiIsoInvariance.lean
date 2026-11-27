import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainModels
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! Quasi-isomorphism invariance for the signed tensor and internal Hom. -/

namespace DerivedFormalization

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CochainComplex (linearHomComplex mappingCone)
open CochainComplex.HomComplex

universe u v

variable {R : Type u} [CommRing R]

noncomputable section

private abbrev homotopyQ := HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)

private def mapCocycle {A A' B B' : Comp.{v} R} (a : A' ⟶ A) (b : B ⟶ B') (n : ℤ)
    (z : Cocycle A B n) : Cocycle A' B' n :=
  Cocycle.mk ((internalHomMap a b).f n z.1) (n + 1) rfl (by
    change ((linearHomComplex R A' B').d n (n + 1)) ((internalHomMap a b).f n z.1) = 0
    rw [← ModuleCat.comp_apply, (internalHomMap a b).comm n (n + 1),
      ModuleCat.comp_apply]
    change (internalHomMap a b).f (n + 1) (δ n (n + 1) z.1) = 0
    rw [z.δ_eq_zero, map_zero])

private lemma equivHomShift_mapCocycle {A A' B B' : Comp.{v} R}
    (a : A' ⟶ A) (b : B ⟶ B') (n : ℤ) (z : Cocycle A B n) :
    Cocycle.equivHomShift.symm (mapCocycle a b n z) =
      a ≫ Cocycle.equivHomShift.symm z ≫ (shiftFunctor (Comp R) n).map b := by
  apply HomologicalComplex.hom_ext
  intro i
  simp only [Cocycle.equivHomShift_symm_apply, comp_f, Cocycle.homOf_f,
    Cocycle.rightShift_coe, Cochain.rightShift_v _ _ _ _ _ _ _ _ rfl,
    CochainComplex.shiftFunctor_map_f']
  apply ModuleCat.hom_ext
  ext x : 1
  change ((internalHomMap a b).f n z.1).v i (i + n) rfl x = _
  exact internalHomMap_apply a b rfl z.1 x

private lemma internalHomCohomology_natural {A A' B B' : Comp.{v} R}
    (a : A' ⟶ A) (b : B ⟶ B') (n : ℤ) (x : (internalHom A B).homology n) :
    internalHomCohomology A' B' n (homologyMap (internalHomMap a b) n x) =
      homotopyQ.map a ≫ internalHomCohomology A B n x ≫
        homotopyQ.map ((shiftFunctor (Comp R) n).map b) := by
  let d := linearLeftHomologyData R A B n
  let d' := linearLeftHomologyData R A' B' n
  let m := internalHomMap a b
  change ↥(sc (linearHomComplex R A B) n).homology at x
  have hz : ∃ z : Cocycle A B n, x = d.homologyIso.inv (CohomologyClass.mk z) := by
    obtain ⟨z, hz⟩ := CohomologyClass.mk_surjective (d.homologyIso.hom x)
    refine ⟨z, ?_⟩
    rw [hz, ← ModuleCat.comp_apply, Iso.hom_inv_id, ModuleCat.id_apply]
  obtain ⟨z, rfl⟩ := hz
  let φ := (shortComplexFunctor (ModuleCat R) (.up ℤ) n).map m
  let f := ShortComplex.cyclesMap' φ d d'
  have hf : f z = mapCocycle a b n z := by
    apply Subtype.ext
    change d'.i (f z) = d'.i (mapCocycle a b n z)
    rw [← ModuleCat.comp_apply, ShortComplex.cyclesMap'_i, ModuleCat.comp_apply]
    rfl
  have hm : d'.homologyIso.hom (homologyMap m n (d.homologyIso.inv (CohomologyClass.mk z))) =
      CohomologyClass.mk (mapCocycle a b n z) := by
    change (d.π ≫ d.homologyIso.inv ≫ ShortComplex.homologyMap φ ≫ d'.homologyIso.hom) z = _
    rw [ShortComplex.LeftHomologyMapData.homologyMap_comm φ
      (ShortComplex.leftHomologyMapData φ d d'), Iso.inv_hom_id_assoc,
      ← ShortComplex.leftHomologyMap', ShortComplex.leftHomologyπ_naturality']
    change d'.π (f z) = _
    rw [hf]
    rfl
  change CohomologyClass.toHom (d'.homologyIso.hom (homologyMap m n
    (d.homologyIso.inv (CohomologyClass.mk z)))) = _
  rw [hm, CohomologyClass.toHom_mk, equivHomShift_mapCocycle, Functor.map_comp, Functor.map_comp]
  have hx : internalHomCohomology A B n (d.homologyIso.inv (CohomologyClass.mk z)) =
      homotopyQ.map (Cocycle.equivHomShift.symm z) := by
    change CohomologyClass.toHom (d.homologyIso.hom (d.homologyIso.inv (CohomologyClass.mk z))) = _
    rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply, CohomologyClass.toHom_mk]
  rw [hx]

attribute [local instance] HasDerivedCategory.standard

private lemma homotopyQ_map_isIso_in_derived {X Y : Comp.{v} R} (g : X ⟶ Y)
    (hg : QuasiIso g) : IsIso (DerivedCategory.Qh.map (homotopyQ.map g)) := by
  let : QuasiIso g := hg
  have e := DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)
  exact (NatIso.isIso_map_iff e g).2 inferInstance

/-- Internal Hom out of a K-projective complex preserves quasi-isomorphisms. -/
theorem internalHomMap_quasiIso_of_isKProjective (P : Comp.{v} R) (hP : IsKProjective P)
    {X Y : Comp.{v} R} (g : X ⟶ Y) (hg : QuasiIso g) :
    QuasiIso (internalHomMap (𝟙 P) g) := by
  let : IsKProjective P := hP
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  let t := (shiftFunctor (Comp R) n).map g
  let := homotopyQ_map_isIso_in_derived t ((CochainComplex.quasiIso_shift_iff g n).2 hg)
  let e (Z : Comp.{v} R) := (DerivedCategory.Qh.map :
      (homotopyQ.obj P ⟶ homotopyQ.obj (Z⟦n⟧)) → _) ∘ internalHomCohomology P Z n
  have he (Z : Comp.{v} R) : Function.Bijective (e Z) :=
    (CochainComplex.IsKProjective.Qh_map_bijective _ _).comp
      (internalHomCohomology P Z n).bijective
  apply (Function.Bijective.of_comp_iff' (he Y) _).1
  have hb : e Y ∘ homologyMap (internalHomMap (𝟙 P) g) n =
      (fun f => f ≫ DerivedCategory.Qh.map (homotopyQ.map t)) ∘ e X := by
    funext x
    simp [e, t, internalHomCohomology_natural]
  rw [hb]
  simpa [Iso.homCongr, Function.comp_def] using (Iso.homCongr (Iso.refl _) (asIso (DerivedCategory.Qh.map (homotopyQ.map t)))).bijective.comp
    (he X)

/-- Internal Hom into a K-injective complex reverses quasi-isomorphisms. -/
theorem internalHomMap_quasiIso_of_isKInjective (I : Comp.{v} R) (hI : IsKInjective I)
    {X Y : Comp.{v} R} (g : X ⟶ Y) (hg : QuasiIso g) :
    QuasiIso (internalHomMap g (𝟙 I)) := by
  let : IsKInjective I := hI
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  let := homotopyQ_map_isIso_in_derived g hg
  let e (Z : Comp.{v} R) := (DerivedCategory.Qh.map :
      (homotopyQ.obj Z ⟶ homotopyQ.obj (I⟦n⟧)) → _) ∘ internalHomCohomology Z I n
  have he (Z : Comp.{v} R) : Function.Bijective (e Z) :=
    (CochainComplex.IsKInjective.Qh_map_bijective _ _).comp
      (internalHomCohomology Z I n).bijective
  apply (Function.Bijective.of_comp_iff' (he X) _).1
  have hb : e X ∘ homologyMap (internalHomMap g (𝟙 I)) n =
      (fun f => DerivedCategory.Qh.map (homotopyQ.map g) ≫ f) ∘ e Y := by
    funext x
    simp [e, internalHomCohomology_natural]
  rw [hb]
  simpa [Iso.homCongr, Function.comp_def] using (Iso.homCongr (asIso (DerivedCategory.Qh.map (homotopyQ.map g))).symm
    (Iso.refl _)).bijective.comp (he Y)

open private add_apply sign_apply map_sign differential_apply from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainModels

section Tensor

open MonoidalCategory
open scoped TensorProduct
open CochainComplex.mappingCone

private lemma tensor_hom_ext {A B : Comp.{u} R} {n : ℤ} {M : ModuleCat.{u} R}
    {f g : (tensorComplex A B).X n ⟶ M}
    (h : ∀ i j (e : i + j = n) (x : A.X i) (y : B.X j),
      f (ιTensorObj A B i j n e (x ⊗ₜ[R] y)) =
        g (ιTensorObj A B i j n e (x ⊗ₜ[R] y))) : f = g := by
  apply mapBifunctor.hom_ext
  intro i j e
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  exact h i j e

/-- Tensoring a graded cochain with the identity in the second factor. -/
private def tensorRightCochain (P : Comp.{u} R) {A B : Comp.{u} R} {n : ℤ}
    (a : Cochain A B n) : Cochain (tensorComplex A P) (tensorComplex B P) n :=
  Cochain.mk fun t s hs => mapBifunctorDesc (fun i j hij =>
    (a.v i (i + n) rfl ▷ P.X j) ≫ ιTensorObj B P (i + n) j s (by
      change i + j = t at hij
      omega))

private lemma tensorRightCochain_apply (P : Comp.{u} R) {A B : Comp.{u} R} {n : ℤ}
    (a : Cochain A B n) {i j t s i' : ℤ}
    (ht : i + j = t) (hs : t + n = s) (hi : i + n = i')
    (x : A.X i) (y : P.X j) :
    (tensorRightCochain P a).v t s hs (ιTensorObj A P i j t ht (x ⊗ₜ[R] y)) =
      ιTensorObj B P i' j s (by omega) (a.v i i' hi x ⊗ₜ[R] y) := by
  subst i'
  have h := ι_mapBifunctorDesc (K₁ := A) (K₂ := P) (F := curriedTensor (ModuleCat R))
    (c := ComplexShape.up ℤ) (fun k l hkl =>
      (a.v k (k + n) rfl ▷ P.X l) ≫ ιTensorObj B P (k + n) l s (by
        change k + l = t at hkl
        omega)) i j ht
  change ιTensorObj A P i j t ht ≫ (tensorRightCochain P a).v t s hs =
    (a.v i (i + n) rfl ▷ P.X j) ≫ _ at h
  simpa only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.whiskerRight_apply] using
    ConcreteCategory.congr_hom h (x ⊗ₜ[R] y)

private lemma tensorRightCochain_ofHom (P : Comp.{u} R) {A B : Comp.{u} R}
    (f : A ⟶ B) :
    tensorRightCochain P (Cochain.ofHom f) = Cochain.ofHom (tensorMap f (𝟙 P)) := by
  apply Cochain.ext₀
  intro t
  apply tensor_hom_ext
  intro i j ht x y
  subst t
  rw [tensorRightCochain_apply P _ rfl (add_zero _) (add_zero i)]
  simpa only [Cochain.ofHom_v, id_f, ModuleCat.id_apply] using
    (tensorMap_apply f (𝟙 P) i j x y).symm

private lemma tensorRightCochain_comp (P : Comp.{u} R) {A B C : Comp.{u} R}
    {n m k : ℤ} (a : Cochain A B n) (b : Cochain B C m) (hk : n + m = k) :
    tensorRightCochain P (a.comp b hk) =
      (tensorRightCochain P a).comp (tensorRightCochain P b) hk := by
  apply Cochain.ext
  intro t s ht
  apply tensor_hom_ext
  intro i j hij x y
  rw [Cochain.comp_v _ _ hk t (t + n) s rfl (by omega), ModuleCat.comp_apply,
    tensorRightCochain_apply P a hij rfl rfl,
    tensorRightCochain_apply P b (show i + n + j = t + n by omega) _
      (show i + n + m = i + k by omega),
    tensorRightCochain_apply P (a.comp b hk) hij ht rfl,
    Cochain.comp_v _ _ hk i (i + n) (i + k) rfl (by omega), ModuleCat.comp_apply]

private lemma tensorRightCochain_add (P : Comp.{u} R) {A B : Comp.{u} R} {n : ℤ}
    (a b : Cochain A B n) :
    tensorRightCochain P (a + b) = tensorRightCochain P a + tensorRightCochain P b := by
  apply Cochain.ext
  intro t s ht
  apply tensor_hom_ext
  intro i j hij x y
  simp only [Cochain.add_v, add_apply, tensorRightCochain_apply P _ hij ht rfl,
    TensorProduct.add_tmul, map_add]

private lemma tensorRightCochain_neg (P : Comp.{u} R) {A B : Comp.{u} R} {n : ℤ}
    (a : Cochain A B n) :
    tensorRightCochain P (-a) = -tensorRightCochain P a := by
  apply Cochain.ext
  intro t s ht
  apply tensor_hom_ext
  intro i j hij x y
  have neg_apply {M N : ModuleCat.{u} R} (f : M ⟶ N) (x : M) : (-f) x = -f x := rfl
  simp only [Cochain.neg_v, neg_apply, tensorRightCochain_apply P _ hij ht rfl,
    TensorProduct.neg_tmul, map_neg]

private lemma tensorRightCochain_zero (P A B : Comp.{u} R) (n : ℤ) :
    tensorRightCochain P (0 : Cochain A B n) = 0 := by
  apply Cochain.ext
  intro t s ht
  apply tensor_hom_ext
  intro i j hij x y
  have zero_apply {M N : ModuleCat.{u} R} (x : M) : (0 : M ⟶ N) x = 0 := rfl
  simp only [Cochain.zero_v, zero_apply, tensorRightCochain_apply P _ hij ht rfl,
    TensorProduct.zero_tmul, map_zero]

private lemma tensor_d_apply_first_index {A B : Comp.{u} R} {i j t s i' : ℤ}
    (ht : i + j = t) (hs : t + 1 = s) (hi : i + 1 = i')
    (x : A.X i) (y : B.X j) :
    (tensorComplex A B).d t s (ιTensorObj A B i j t ht (x ⊗ₜ[R] y)) =
      ιTensorObj A B i' j s (by omega) (A.d i i' x ⊗ₜ[R] y) +
        i.negOnePow • ιTensorObj A B i (j + 1) s (by omega) (x ⊗ₜ[R] B.d j (j + 1) y) := by
  subst i'
  exact tensor_d_apply _ _ _ _ ht hs x y

private lemma tensorRightCochain_δ (P : Comp.{u} R) {A B : Comp.{u} R} {n m : ℤ}
    (hn : n + 1 = m) (a : Cochain A B n) :
    tensorRightCochain P (δ n m a) = δ n m (tensorRightCochain P a) := by
  apply Cochain.ext
  intro t s hs
  apply tensor_hom_ext
  intro i j ht x y
  have hi : i + n + 1 = i + m := by omega
  rw [tensorRightCochain_apply P _ ht hs rfl, differential_apply hn rfl (v₀ := i + n)
    (i₁ := i + 1) (by omega) rfl,
    differential_apply hn hs (v₀ := t + n) (i₁ := t + 1) (by omega) rfl,
    tensorRightCochain_apply P a ht rfl rfl, tensor_d_apply_first_index _ (by omega) hi,
    tensor_d_apply i j t (t + 1) ht rfl,
    map_add, map_sign,
    tensorRightCochain_apply P a (show i + 1 + j = t + 1 by omega) _
      (show i + 1 + n = i + m by omega),
    tensorRightCochain_apply P a (show i + (j + 1) = t + 1 by omega) _ rfl]
  have smul_tmul_units (s : ℤˣ) (w : B.X (i + m)) :
      (s • w) ⊗ₜ[R] y = s • (w ⊗ₜ[R] y) := by
    simp only [Units.smul_def]
    exact map_zsmul ((TensorProduct.mk R _ _).flip y) _ w
  simp only [TensorProduct.add_tmul, smul_tmul_units, map_add, smul_add, smul_smul]
  rw [map_sign m.negOnePow (ιTensorObj B P (i + m) j s (by omega))]
  have hu : (i + n).negOnePow = -(m.negOnePow * i.negOnePow) := by
    rw [← hn, Int.negOnePow_succ, Int.negOnePow_add, neg_mul, mul_comm n.negOnePow]
    simp
  rw [hu, Units.neg_smul]
  abel

private lemma quasiIso_iff_acyclic_cone {A B : Comp.{v} R} (f : A ⟶ B) :
    QuasiIso f ↔ (mappingCone f).Acyclic := by
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  let T := mappingCone.triangleh f
  change QuasiIso f ↔ HomotopyCategory.subcategoryAcyclic _ T.obj₃
  rw [← (HomotopyCategory.subcategoryAcyclic _).trW_iff_of_distinguished T
    (HomotopyCategory.mappingCone_triangleh_distinguished f),
    ← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).symm

/-- Tensoring on the right carries the inclusions and projections of a cone
to a splitting with the same differential and off-diagonal map. -/
private def tensorRightConeComparison (P : Comp.{u} R) {A B : Comp.{u} R} (f : A ⟶ B) :
    mappingCone (tensorMap f (𝟙 P)) ≅ tensorComplex (mappingCone f) P := by
  let g := tensorMap f (𝟙 P)
  let l := tensorRightCochain P (inl f)
  let r := tensorMap (inr f) (𝟙 P)
  let p : Cocycle (tensorComplex (mappingCone f) P) (tensorComplex A P) 1 :=
    Cocycle.mk (tensorRightCochain P (fst f).1) 2 rfl (by
      rw [← tensorRightCochain_δ P (show (1 : ℤ) + 1 = 2 by decide),
        Cocycle.δ_eq_zero, tensorRightCochain_zero])
  let q := tensorRightCochain P (snd f)
  have hl : δ (-1) 0 l = Cochain.ofHom (g ≫ r) := by
    dsimp only [l, g, r]
    rw [← tensorRightCochain_δ P (show (-1 : ℤ) + 1 = 0 by decide), δ_inl,
      tensorRightCochain_ofHom, tensorMap_comp, Category.comp_id]
  have hq : δ 0 1 q + p.1.comp (Cochain.ofHom g) (add_zero 1) = 0 := by
    change δ 0 1 (tensorRightCochain P (snd f)) +
      (tensorRightCochain P (fst f).1).comp (Cochain.ofHom g) (add_zero 1) = 0
    rw [← tensorRightCochain_δ P (zero_add 1), δ_snd, tensorRightCochain_neg,
      ← tensorRightCochain_ofHom, ← tensorRightCochain_comp, neg_add_cancel]
  let forward := desc g l r hl
  let backward := lift g p q hq
  refine ⟨forward, backward, ?_, ?_⟩
  · change desc g l r hl ≫ lift g p q hq = 𝟙 _
    apply Cochain.ofHom_injective
    rw [Cochain.ofHom_comp, ext_cochain_from_iff g (-1) 0 (neg_add_cancel 1)]
    constructor
    · rw [← Cochain.comp_assoc_of_third_is_zero_cochain, inl_desc, Cochain.comp_id,
        ext_cochain_to_iff g (-1) 0 (neg_add_cancel 1)]
      simp only [Cochain.comp_assoc_of_second_is_zero_cochain, ofHom_lift,
        liftCochain_fst, liftCochain_snd, inl_fst, inl_snd]
      change l.comp (tensorRightCochain P (fst f).1) (neg_add_cancel 1) = _ ∧
        l.comp (tensorRightCochain P (snd f)) (add_zero _) = _
      simp only [l, ← tensorRightCochain_comp, inl_fst, inl_snd, tensorRightCochain_zero,
        tensorRightCochain_ofHom, tensorMap_id, and_self]
    · rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, inr_desc,
        Cochain.comp_id, ext_cochain_to_iff g 0 1 (zero_add 1)]
      simp only [Cochain.comp_assoc_of_first_is_zero_cochain, ofHom_lift,
        liftCochain_fst, liftCochain_snd, inr_fst, inr_snd]
      change (Cochain.ofHom r).comp (tensorRightCochain P (fst f).1) (zero_add 1) = _ ∧
        (Cochain.ofHom r).comp (tensorRightCochain P (snd f)) (add_zero _) = _
      rw [show Cochain.ofHom r = tensorRightCochain P (Cochain.ofHom (inr f)) from
        (tensorRightCochain_ofHom P _).symm]
      rw [← tensorRightCochain_comp, ← tensorRightCochain_comp]
      simp only [inr_fst, inr_snd, tensorRightCochain_zero, tensorRightCochain_ofHom,
        tensorMap_id, and_self]
  · apply Cochain.ofHom_injective
    simp only [Cochain.ofHom_comp, forward, backward, ofHom_lift, ofHom_desc,
      liftCochain_descCochain]
    change (tensorRightCochain P (fst f).1).comp l (add_neg_cancel 1) +
      q.comp (Cochain.ofHom r) (add_zero 0) = _
    rw [show Cochain.ofHom r = tensorRightCochain P (Cochain.ofHom (inr f)) from
        (tensorRightCochain_ofHom P _).symm]
    rw [show l = tensorRightCochain P (inl f) from rfl, show q = tensorRightCochain P (snd f) from rfl,
      ← tensorRightCochain_comp, ← tensorRightCochain_comp, ← tensorRightCochain_add,
      mappingCone.id, tensorRightCochain_ofHom, tensorMap_id]

/-- A K-flat complex in the second tensor factor preserves quasi-isomorphisms. -/
theorem tensorMap_right_quasiIso_of_isKFlat (P : Comp.{u} R) (hP : IsKFlat P)
    {X Y : Comp.{u} R} (f : X ⟶ Y) (hf : QuasiIso f) :
    QuasiIso (tensorMap f (𝟙 P)) := by
  apply (quasiIso_iff_acyclic_cone _).2
  have h := hP _ ((quasiIso_iff_acyclic_cone f).1 hf)
  intro n
  rw [exactAt_iff_isZero_homology]
  exact (h n).isZero_homology.of_iso ((homologyFunctor _ _ n).mapIso (tensorRightConeComparison P f))

-- Adapted from the signed swap in MathGenome's FiniteFreeDualityModel.
private def tensorSwapAt (A B : Comp.{u} R) (n : ℤ) :
    (tensorComplex A B).X n ⟶ (tensorComplex B A).X n :=
  mapBifunctorDesc (fun i j h => (i * j).negOnePow •
    (TensorProduct.comm R (A.X i) (B.X j)).toModuleIso.hom ≫
      ιTensorObj B A j i n (by
        change i + j = n at h
        omega))

private lemma tensorSwapAt_apply (A B : Comp.{u} R) (i j n : ℤ) (e : i + j = n)
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

private def tensorSwapHom (A B : Comp.{u} R) : tensorComplex A B ⟶ tensorComplex B A where
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
      rw [mul_add, mul_one, Int.negOnePow_add, mul_comm (i * j).negOnePow, ← mul_assoc,
        ← Int.negOnePow_add, ← two_mul, Int.negOnePow_two_mul, one_mul]
    rw [hs₁, hs₂, add_comm]

private lemma tensorSwapHom_comp (A B : Comp.{u} R) :
    tensorSwapHom A B ≫ tensorSwapHom B A = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply tensor_hom_ext
  intro i j e x y
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.comp_apply,
    ModuleCat.id_apply, tensorSwapHom, tensorSwapAt_apply, map_sign, smul_smul]
  rw [mul_comm j i, ← Int.negOnePow_add, ← two_mul, Int.negOnePow_two_mul, one_smul]

private def tensorSwap (A B : Comp.{u} R) : tensorComplex A B ≅ tensorComplex B A where
  hom := tensorSwapHom A B
  inv := tensorSwapHom B A
  hom_inv_id := tensorSwapHom_comp A B
  inv_hom_id := tensorSwapHom_comp B A

private lemma tensorSwap_natural {A A' : Comp.{u} R} (f : A ⟶ A') (B : Comp.{u} R) :
    tensorMap f (𝟙 B) ≫ (tensorSwap A' B).hom =
      (tensorSwap A B).hom ≫ tensorMap (𝟙 B) f := by
  apply HomologicalComplex.hom_ext
  intro n
  apply tensor_hom_ext
  intro i j e x y
  subst n
  have hs (k : ℤ) (h : j + i = k) (z : B.X j) (w : A.X i) :
      (tensorMap (𝟙 B) f).f k (ιTensorObj B A j i k h (z ⊗ₜ[R] w)) =
        ιTensorObj B A' j i k h (z ⊗ₜ[R] f.f i w) := by
    subst k
    simpa only [HomologicalComplex.id_f, ModuleCat.id_apply] using
      tensorMap_apply (𝟙 B) f j i z w
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, tensorMap_apply,
    HomologicalComplex.id_f, ModuleCat.id_apply, tensorSwap, tensorSwapHom,
    tensorSwapAt_apply, map_sign, hs]

/-- A K-flat complex in the first tensor factor preserves quasi-isomorphisms. -/
theorem tensorMap_quasiIso_of_isKFlat (P : Comp.{u} R) (hP : IsKFlat P)
    {X Y : Comp.{u} R} (f : X ⟶ Y) (hf : QuasiIso f) :
    QuasiIso (tensorMap (𝟙 P) f) := by
  have := tensorMap_right_quasiIso_of_isKFlat P hP f hf
  apply (quasiIso_iff_comp_left (tensorSwap X P).hom _).1
  rw [← tensorSwap_natural]
  infer_instance

end Tensor

end
end DerivedFormalization
