import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.InfiniteDiagonalTotalizations
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DoubleTotalization
import Mathlib.LinearAlgebra.Dimension.ErdosKaplansky

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category Opposite
open AdvancedHomologicalAlgebra.DoubleTotalization

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
namespace AdvancedHomologicalAlgebra.InfiniteDiagonalTotalizations
variable (k : Type u) [Field k]

@[simp] theorem horizontal_zero (p p' q : ℤ) : ((bicomplex k).d p p').f q = 0 := rfl
@[simp] theorem vertical_zero (p q q' : ℤ) : ((bicomplex k).X p).d q q' = 0 := rfl

/-- Zero bicomplex differentials give a zero total differential, for either
shape. This also applies to the opposite bicomplex used for products. -/
theorem total_d_zero {C : Type*} [Category* C] [Preadditive C]
    {c : ComplexShape ℤ} [ComplexShape.TensorSigns c]
    (K : HomologicalComplex₂ C c c) [K.HasTotal c]
    (hh : ∀ p p' q, (K.d p p').f q = 0)
    (hv : ∀ p q q', (K.X p).d q q' = 0) (i j : ℤ) :
    (K.total c).d i j = 0 := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q h
  simp only [HomologicalComplex₂.total_d, Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
    HomologicalComplex₂.d₁, HomologicalComplex₂.d₂, hh, hv,
    zero_comp, smul_zero, add_zero, comp_zero]

@[simp] theorem sum_d_zero (i j : ℤ) : (sumComplex k).d i j = 0 :=
  total_d_zero _ (horizontal_zero k) (vertical_zero k) i j

@[simp] theorem product_d_zero (i j : ℤ) : (productComplex k).d i j = 0 := by
  have e := total_d_zero (oppositeBicomplex (bicomplex k))
    (by intros; simp [oppositeBicomplex])
    (by intros; simp [oppositeBicomplex, HomologicalComplex.op_d]) j i
  exact congrArg Quiver.Hom.unop e

noncomputable def sumCofan : Cofan (fun _ : ℤ => ModuleCat.of k k) :=
  Cofan.mk _ (sumι k)

noncomputable def sumIsColimit : IsColimit (sumCofan k) where
  desc s := (bicomplex k).totalDesc (fun p q h => (termIso k p q h).hom ≫ s.ι.app ⟨p⟩)
  fac s j := by
    rcases j with ⟨p⟩
    simp [sumCofan, sumι, Category.assoc, HomologicalComplex₂.ι_totalDesc]
  uniq s m h := by
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    have hq : q = -p := by dsimp at hpq; omega
    subst q
    apply (cancel_epi (termIso k p (-p) (by omega)).inv).mp
    simpa [sumCofan, sumι, Category.assoc, HomologicalComplex₂.ι_totalDesc] using h ⟨p⟩

noncomputable def productFan : Fan (fun _ : ℤ => ModuleCat.of k k) :=
  Fan.mk _ (productπ k)

noncomputable def productIsLimit : IsLimit (productFan k) where
  lift s := ((oppositeBicomplex (bicomplex k)).totalDesc
    (fun p q h => (s.π.app ⟨p⟩ ≫ (termIso k p q h).inv).op)).unop
  fac s j := by
    rcases j with ⟨p⟩
    have e := (oppositeBicomplex (bicomplex k)).ι_totalDesc
      (c₁₂ := (ComplexShape.up ℤ).symm)
      (fun p q h => (s.π.app ⟨p⟩ ≫ (termIso k p q h).inv).op) p (-p) (by dsimp; omega)
    have e' := congrArg Quiver.Hom.unop e
    simp only [unop_comp, Quiver.Hom.unop_op] at e'
    change _ ≫ _ ≫ (termIso k p (-p) (by omega)).hom = _
    rw [← Category.assoc, e', Category.assoc, Iso.inv_hom_id, Category.comp_id]
  uniq s m h := by
    apply Quiver.Hom.op_inj
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    have hq : q = -p := by dsimp at hpq; omega
    subst q
    apply Quiver.Hom.unop_inj
    apply (cancel_mono (termIso k p (-p) (by omega)).hom).mp
    simpa [productFan, productπ, productProjection, Category.assoc,
      unop_comp] using h ⟨p⟩

noncomputable def finsuppCofan : Cofan (fun _ : ℤ => ModuleCat.of k k) :=
  Cofan.mk (ModuleCat.of k (ℤ →₀ k)) (fun p => ModuleCat.ofHom (Finsupp.lsingle p))

noncomputable def finsuppIsColimit : IsColimit (finsuppCofan k) where
  desc s := ModuleCat.ofHom (Finsupp.lsum k (fun p => (s.ι.app ⟨p⟩).hom))
  fac s j := by rcases j with ⟨p⟩; ext; simp [finsuppCofan]
  uniq s m h := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro p
    simpa [finsuppCofan] using congrArg ModuleCat.Hom.hom (h ⟨p⟩)

/-- Identification of the actual sum totalization in degree zero. -/
noncomputable def sumIso : (sumComplex k).X 0 ≅ ModuleCat.of k (ℤ →₀ k) :=
  (sumIsColimit k).coconePointUniqueUpToIso (finsuppIsColimit k)

/-- Identification of the actual product totalization in degree zero. -/
noncomputable def productIso : (productComplex k).X 0 ≅ ModuleCat.of k (ℤ → k) :=
  (productIsLimit k).conePointUniqueUpToIso
    (ModuleCat.productConeIsLimit (fun _ : ℤ => ModuleCat.of k k))

@[reassoc (attr := simp)] theorem sumι_sumIso (p : ℤ) :
    sumι k p ≫ (sumIso k).hom = ModuleCat.ofHom (Finsupp.lsingle p) :=
  (sumIsColimit k).comp_coconePointUniqueUpToIso_hom (finsuppIsColimit k) ⟨p⟩

@[reassoc (attr := simp)] theorem productIso_productπ (p : ℤ) :
    (productIso k).inv ≫ productπ k p = ModuleCat.ofHom (LinearMap.proj p) :=
  (productIsLimit k).conePointUniqueUpToIso_inv_comp
    (ModuleCat.productConeIsLimit (fun _ : ℤ => ModuleCat.of k k)) ⟨p⟩

/-- The comparison transported through the degree-zero universal properties.
All other degree maps are zero. -/
noncomputable def comparison : sumComplex k ⟶ productComplex k where
  f n := if hn : n = 0 then
    eqToHom (congrArg (fun j => (sumComplex k).X j) hn) ≫
    (sumIso k).hom ≫ sequenceInclusion k ≫ (productIso k).inv ≫
    eqToHom (congrArg (fun j => (productComplex k).X j) hn.symm) else 0
  comm' i j _ := by
    simp only [sum_d_zero, product_d_zero, comp_zero, zero_comp]

@[simp] theorem comparison_f_zero : (comparison k).f 0 =
    (sumIso k).hom ≫ sequenceInclusion k ≫ (productIso k).inv := by
  simp [comparison]

@[reassoc] theorem comparison_coordinate (p p' : ℤ) :
    sumι k p ≫ (comparison k).f 0 ≫ productπ k p' =
    if p = p' then 𝟙 (ModuleCat.of k k) else 0 := by
  rw [comparison_f_zero]
  simp only [Category.assoc, productIso_productπ, sumι_sumIso_assoc]
  by_cases h : p = p'
  · subst p'
    ext
    simp [sequenceInclusion]
  · ext
    simp [sequenceInclusion, h, Ne.symm h]

theorem comparison_isComparison : Specs.IsComparison k (comparison k) := by
  intro n p q p' q' h h'
  by_cases hn : n = 0
  · subst hn
    have hq : q = -p := by omega
    have hq' : q' = -p' := by omega
    subst q
    subst q'
    apply (cancel_epi (termIso k p (-p) (by omega)).inv).mp
    apply (cancel_mono (termIso k p' (-p') (by omega)).hom).mp
    change sumι k p ≫ (comparison k).f 0 ≫ productπ k p' = _
    rw [comparison_coordinate]
    by_cases hp : p = p'
    · subst p'
      simp
    · have hpq : (p, -p) ≠ (p', -p') := by intro e; exact hp (congrArg Prod.fst e)
      simp [hp, hpq]
  · have ht : p + q ≠ 0 := by omega
    have hz : IsZero (term k p q) := by
      simp only [term, ite_eq_right ht]
      exact ModuleCat.isZero_of_subsingleton _
    exact hz.eq_of_src _ _

theorem comparison_unique (f : sumComplex k ⟶ productComplex k)
    (hf : Specs.IsComparison k f) : f = comparison k := by
  ext n : 1
  apply HomologicalComplex₂.total.hom_ext
  intro p q h
  apply Quiver.Hom.op_inj
  apply HomologicalComplex₂.total.hom_ext
  intro p' q' h'
  apply Quiver.Hom.unop_inj
  simpa only [unop_comp, Quiver.Hom.unop_op, productProjection, Category.assoc] using
    (hf n p q p' q' h h').trans (comparison_isComparison k n p q p' q' h h').symm

theorem inclusion_injective : Function.Injective (sequenceInclusion k) := by
  intro f g h
  exact Finsupp.ext (congrFun h)

theorem inclusion_not_surjective : ¬ Function.Surjective (sequenceInclusion k) := by
  intro h
  obtain ⟨f, hf⟩ := h (fun _ => 1)
  obtain ⟨p, hp⟩ := Infinite.exists_notMem_finset f.support
  have e := congrFun hf p
  change f p = 1 at e
  rw [Finsupp.notMem_support_iff.mp hp] at e
  exact zero_ne_one e

/-- For a complex with zero differentials, its categorical homology is its term. -/
noncomputable def zeroHomologyIso (K : CochainComplex (ModuleCat.{u} k) ℤ)
    (h : ∀ i j, K.d i j = 0) (n : ℤ) : K.homology n ≅ K.X n :=
  (ShortComplex.LeftHomologyData.ofZeros (K.sc n) (h _ _) (h _ _)).homologyIso

/-- Naturality keeps track of the actual map on cohomology. -/
theorem zeroHomologyIso_naturality
    (K L : CochainComplex (ModuleCat.{u} k) ℤ)
    (hK : ∀ i j, K.d i j = 0) (hL : ∀ i j, L.d i j = 0)
    (f : K ⟶ L) (n : ℤ) :
    HomologicalComplex.homologyMap f n ≫ (zeroHomologyIso k L hL n).hom =
      (zeroHomologyIso k K hK n).hom ≫ f.f n :=
  (ShortComplex.LeftHomologyMapData.ofZeros
    ((HomologicalComplex.shortComplexFunctor _ _ n).map f)
    (hK _ _) (hK _ _) (hL _ _) (hL _ _)).homologyMap_comm

noncomputable def sumHomologyIso :
    (sumComplex k).homology 0 ≅ ModuleCat.of k (ℤ →₀ k) :=
  zeroHomologyIso k _ (sum_d_zero k) 0 ≪≫ sumIso k

noncomputable def productHomologyIso :
    (productComplex k).homology 0 ≅ ModuleCat.of k (ℤ → k) :=
  zeroHomologyIso k _ (product_d_zero k) 0 ≪≫ productIso k

theorem homology_comparison :
    HomologicalComplex.homologyMap (comparison k) 0 ≫ (productHomologyIso k).hom =
      (sumHomologyIso k).hom ≫ sequenceInclusion k := by
  dsimp only [sumHomologyIso, productHomologyIso, Iso.trans_hom]
  rw [← Category.assoc,
    zeroHomologyIso_naturality k _ _ (sum_d_zero k) (product_d_zero k),
    Category.assoc, comparison_f_zero]
  simp

theorem infinite_diagonal :
    Set.Infinite {i : ℤ × ℤ | i.1 + i.2 = 0 ∧ ¬ IsZero (term k i.1 i.2)} := by
  apply Set.infinite_of_injective_forall_mem (f := fun p : ℤ => (p, -p))
    (by intro p q h; exact congrArg Prod.fst h)
  intro p
  refine ⟨by simp, ?_⟩
  simp only [term, add_neg_cancel, ite_true]
  intro h
  have hs := ModuleCat.subsingleton_of_isZero h
  exact zero_ne_one (@Subsingleton.elim k hs 0 1)

/-- The distinction is also abstract: the product has strictly larger dimension.
This uses Erdős–Kaplansky, valid for every field, finite or infinite. -/
theorem sequence_rank_lt : Module.rank k (ℤ →₀ k) < Module.rank k (ℤ → k) := by
  rw [rank_finsupp_self, Cardinal.mk_int, Cardinal.lift_aleph0,
    rank_fun_infinite, Cardinal.mk_arrow, Cardinal.mk_int, Cardinal.lift_aleph0]
  apply Cardinal.cantor'
  simp only [Cardinal.one_lt_lift_iff, Cardinal.one_lt_iff_nontrivial]
  infer_instance

theorem homology_not_iso :
    ¬ Nonempty ((sumComplex k).homology 0 ≅ (productComplex k).homology 0) := by
  rintro ⟨e⟩
  have h := ((sumHomologyIso k).symm ≪≫ e ≪≫ productHomologyIso k).toLinearEquiv.rank_eq
  exact (sequence_rank_lt k).ne h

theorem homology_comparison_not_isIso :
    ¬ IsIso (HomologicalComplex.homologyMap (comparison k) 0) := by
  intro h
  exact homology_not_iso k ⟨asIso (HomologicalComplex.homologyMap (comparison k) 0)⟩

/-- The infinite-diagonal counterexample, with its actual cohomology comparison. -/
theorem infiniteDiagonalExample : Specs.ExpectedResult.{u} := by
  intro k _
  refine ⟨(by intros; rfl), horizontal_zero k, vertical_zero k,
    sum_d_zero k, product_d_zero k, infinite_diagonal k,
    comparison k, sumHomologyIso k, productHomologyIso k,
    comparison_isComparison k, comparison_unique k, homology_comparison k,
    inclusion_injective k, inclusion_not_surjective k,
    homology_comparison_not_isIso k, homology_not_iso k⟩

end AdvancedHomologicalAlgebra.InfiniteDiagonalTotalizations
