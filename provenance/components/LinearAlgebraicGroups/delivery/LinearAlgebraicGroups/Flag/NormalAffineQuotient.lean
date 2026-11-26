import Specs.LinearAlgebraicGroups.Flag.NormalAffineQuotient
import LinearAlgebraicGroups.Affine.SchemeImageQuotient
import LinearAlgebraicGroups.Affine.ChevalleyLine
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.HopfAlgebra.GroupLike
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite WithConv
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups

open Specs

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]

open private quotientRepresentsImage schemeKernel_exists schemeKernel_sections
  from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private coordinateLine_iff from LinearAlgebraicGroups.Affine.ChevalleyLine
open private frobeniusPowers
  from LinearAlgebraicGroups.Affine.HopfFaithfulFlatness
open private reduced_hopf_of_isAlgClosed
  from LinearAlgebraicGroups.Affine.CharacteristicZeroSmoothness
open private eq_zero_of_algHom_eq_zero
  from LinearAlgebraicGroups.Affine.RationalRepresentations
open private tensorCoordinate_sum_basis
  from LinearAlgebraicGroups.Affine.RationalRepresentations
open private pointMatrix pointMatrix_evaluation pointMatrix_isCoactionMatrix
  from LinearAlgebraicGroups.Affine.RationalRepresentations
open private groupPresentation from LinearAlgebraicGroups.Affine.SchemeImageQuotient

theorem normalSubgroup_conjugate_sections {G H : GroupScheme k} {i : H ⟶ G}
    (hn : IsNormalSubgroup i) {T : SchemeOver k} (g : T ⟶ G.X) (h : T ⟶ H.X) :
    ∃ h' : T ⟶ H.X, h' ≫ i.hom.hom = g * (h ≫ i.hom.hom) * g⁻¹ := by
  obtain ⟨c, hc⟩ := hn
  refine ⟨lift g h ≫ c, ?_⟩
  rw [Category.assoc, hc]
  simp [subgroupConjugation, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc]

private theorem normalSubgroup_of_iso {G H G' H' : GroupScheme k}
    {i : H ⟶ G} {i' : H' ⟶ G'} (eG : G' ≅ G) (eH : H' ≅ H)
    (he : i' ≫ eG.hom = eH.hom ≫ i) (hn : IsNormalSubgroup i) :
    IsNormalSubgroup i' := by
  let U := Grp.forget (SchemeOver k)
  have he' : i'.hom.hom ≫ eG.hom.hom.hom = eH.hom.hom.hom ≫ i.hom.hom :=
    congrArg U.map he
  have : IsIso eG.hom.hom.hom := U.map_isIso eG.hom
  have hinv : eH.inv.hom.hom ≫ eH.hom.hom.hom = 𝟙 H.X := (U.mapIso eH).inv_hom_id
  let g := fst G'.X H'.X
  let h := snd G'.X H'.X
  obtain ⟨n, hconj⟩ := normalSubgroup_conjugate_sections hn
    (g ≫ eG.hom.hom.hom) (h ≫ eH.hom.hom.hom)
  refine ⟨n ≫ eH.inv.hom.hom, (cancel_mono eG.hom.hom.hom).mp ?_⟩
  change ((n ≫ eH.inv.hom.hom) ≫ i'.hom.hom) ≫ eG.hom.hom.hom =
    (g * (h ≫ i'.hom.hom) * g⁻¹) ≫ eG.hom.hom.hom
  simp only [Category.assoc, he', ← Category.assoc eH.inv.hom.hom eH.hom.hom.hom,
    hinv, Category.id_comp, hconj]
  simp [MonObj.mul_comp, GrpObj.inv_comp, he', Category.assoc]

/-- The pure and mixed entries of a tensor product detect the original line
even when the test algebra has nilpotents. -/
theorem coordinateLine_of_tensor_coefficients {R Index : Type u} [CommRing R] [Fintype Index]
    [DecidableEq Index] (M : Matrix.GeneralLinearGroup Index R) (i : Index) (b : R) (m : ℕ)
    (hm : 0 < m) (hpure : M.val i i ^ m * b = 1)
    (hmixed : ∀ j ≠ i, M.val j i * M.val i i ^ (m - 1) * b = 0) :
    StabilizesCoordinateLine M i := by
  apply (coordinateLine_iff M i).mpr
  intro j hj
  have hpow : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hmul : M.val i i ^ (m - 1) * (M.val i i * b) = 1 := by
    rw [← mul_assoc, ← pow_succ, hpow, hpure]
  calc
    M.val j i = M.val j i * (M.val i i ^ (m - 1) * (M.val i i * b)) := by rw [hmul, mul_one]
    _ = (M.val j i * M.val i i ^ (m - 1) * b) * M.val i i := by ac_rfl
    _ = 0 := by rw [hmixed j hj, zero_mul]

/-- After a uniform Frobenius power, linear combinations of powered
coordinates are detected by points over the algebraically closed field. -/
theorem exists_powerSubalgebra [IsAlgClosed k] (A : HopfAlgebraCategory k)
    [Algebra.FiniteType k A] (p : ℕ) [ExpChar k p] :
    ∃ (r : ℕ) (D : Subalgebra k A), (∀ x : A, x ^ (p ^ r) ∈ D) ∧
      (∀ x ∈ D, ∃ y : A, y ^ (p ^ r) = x) ∧
      (∀ x ∈ D, (∀ f : A →ₐ[k] k, f x = 0) → x = 0) := by
  rcases expChar_is_prime_or_one k p with hp | hp
  · have : PerfectRing k p := inferInstance
    have : ExpChar A p :=
      expChar_of_injective_algebraMap (Bialgebra.algebraMap_injective (R := k) A) p
    have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
    obtain ⟨r, hr⟩ := IsNoetherianRing.isNilpotent_nilradical A
    refine ⟨r, frobeniusPowers k A p r, fun x ↦ ⟨x, rfl⟩, fun _ hx ↦ hx, ?_⟩
    intro x hx h
    let J := nilradical A
    have : IsReduced (A ⧸ J) :=
      J.isRadical_iff_quotient_reduced.mp (Ideal.radical_isRadical ⊥)
    have hn : IsNilpotent x := by
      apply mem_nilradical.mp
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      apply eq_zero_of_algHom_eq_zero (F := k)
      intro f
      exact h (f.comp (Ideal.Quotient.mkₐ k J))
    obtain ⟨y, rfl⟩ : ∃ y : A, y ^ (p ^ r) = x := hx
    have hz : y ^ r ∈ nilradical A ^ r :=
      Ideal.pow_mem_pow (mem_nilradical.mpr (IsNilpotent.of_pow hn)) r
    rw [hr, Ideal.zero_eq_bot, Ideal.mem_bot] at hz
    exact pow_eq_zero_of_le (Nat.lt_pow_self hp.one_lt).le hz
  · subst p
    have : CharZero k := charZero_of_expChar_one' k
    have : IsReduced A := reduced_hopf_of_isAlgClosed (k := k) (A := A)
    exact ⟨0, ⊤, fun _ ↦ by simp, fun x _ ↦ ⟨x, pow_one x⟩,
      fun x _ ↦ eq_zero_of_algHom_eq_zero x⟩

/-- A linear functional can select one character among the group-like elements. -/
theorem exists_groupLikeFunctional (B : HopfAlgebraCategory k) (c : B)
    (hc : IsGroupLikeElem k c) :
    ∃ f : B →ₗ[k] k, f c = 1 ∧
      ∀ d : B, IsGroupLikeElem k d → d ≠ c → f d = 0 := by
  classical
  let h := linearIndepOn_isGroupLikeElem (R := k) (A := B)
  let b := Module.Basis.extend h
  let j : h.extend (Set.subset_univ _) := ⟨c, h.subset_extend _ hc⟩
  have hj : b j = c := Module.Basis.extend_apply_self h j
  refine ⟨b.coord j, ?_, ?_⟩
  · rw [← hj]
    simp
  · intro d hd hdc
    let l : h.extend (Set.subset_univ _) := ⟨d, h.subset_extend _ hd⟩
    have hl : b l = d := Module.Basis.extend_apply_self h l
    have hlj : l ≠ j := fun he ↦ hdc (congrArg Subtype.val he)
    rw [← hl]
    simp [Module.Basis.coord_apply, hlj]

section InvariantFunctions

open Coalgebra

variable {A B : HopfAlgebraCategory k} (a : A ⟶ B)

private def leftTranslationDifference : A →ₗ[k] B ⊗[k] A :=
  a.hom.toAlgHom.toLinearMap.rTensor A ∘ₗ comul - TensorProduct.mk k B A 1

/-- Regular functions invariant under multiplication by the subgroup on the left. -/
def leftInvariantFunctions : Submodule k A :=
  LinearMap.ker (leftTranslationDifference a)

theorem mem_leftInvariantFunctions (x : A) :
    x ∈ leftInvariantFunctions a ↔
      a.hom.toAlgHom.toLinearMap.rTensor A (comul x) = (1 : B) ⊗ₜ[k] x := by
  simp [leftInvariantFunctions, leftTranslationDifference, sub_eq_zero]

/-- Right translation preserves the left-invariant functions. -/
theorem leftInvariantFunctions_isSubcomodule :
    (RightComodule.regular (k := k) (C := A)).IsSubcomodule (leftInvariantFunctions a) := by
  let f := a.hom.toAlgHom.toLinearMap
  let δ := comul (R := k) (A := A)
  let assocA := TensorProduct.assoc k A A A
  let assocB := TensorProduct.assoc k B A A
  have hassoc (t : (A ⊗[k] A) ⊗[k] A) :
      assocB (((f.rTensor A).rTensor A) t) = f.rTensor (A ⊗[k] A) (assocA t) := by
    induction t with
    | add x y hx hy => simp [hx, hy]
    | tmul x y =>
      induction x with
      | add x z hx hz => simp only [TensorProduct.add_tmul, map_add, hx, hz]
      | tmul x z => simp [assocA, assocB]
  have hcomul (t : A ⊗[k] A) :
      f.rTensor (A ⊗[k] A) (δ.lTensor A t) = δ.lTensor B (f.rTensor A t) := by
    induction t with
    | add x y hx hy => simp [hx, hy]
    | tmul x y => simp
  have hone (t : A ⊗[k] A) :
      assocB (((TensorProduct.mk k B A 1).rTensor A) t) = (1 : B) ⊗ₜ[k] t := by
    induction t with
    | add x y hx hy => simp [hx, hy, TensorProduct.tmul_add]
    | tmul x y => simp [assocB]
  intro x
  have hx := (mem_leftInvariantFunctions a x.val).mp x.property
  change f.rTensor A (δ x.val) = _ at hx
  have hex := Module.Flat.rTensor_exact A (leftTranslationDifference a).exact_subtype_ker_map
  change δ x.val ∈ LinearMap.range ((LinearMap.ker (leftTranslationDifference a)).subtype.rTensor A)
  apply (hex (δ x.val)).mp
  apply assocB.injective
  rw [map_zero]
  change assocB (((f.rTensor A ∘ₗ δ - TensorProduct.mk k B A 1).rTensor A) (δ x.val)) = 0
  rw [LinearMap.rTensor_sub, LinearMap.sub_apply, map_sub, LinearMap.rTensor_comp_apply,
    hone, hassoc]
  change f.rTensor (A ⊗[k] A) (assocA (δ.rTensor A (δ x.val))) -
    (1 : B) ⊗ₜ[k] δ x.val = 0
  rw [show assocA (δ.rTensor A (δ x.val)) = δ.lTensor A (δ x.val) from
    Coalgebra.coassoc_apply x.val, hcomul, hx, LinearMap.lTensor_tmul, sub_self]

private theorem leftProduct_apply (x : A) {R : Type u} [CommRing R] [Algebra k R]
    (g : WithConv (A →ₐ[k] R)) (h : B →ₐ[k] R) :
    (toConv (h.comp a.hom.toAlgHom) * g) x =
      Algebra.TensorProduct.lift h g.ofConv (fun _ _ ↦ Commute.all _ _)
        (a.hom.toAlgHom.toLinearMap.rTensor A (comul x)) := by
  rw [AlgHom.convMul_apply]
  let E := Algebra.TensorProduct.lift h g.ofConv (fun _ _ ↦ Commute.all _ _)
  have he : (Algebra.TensorProduct.lift (h.comp a.hom.toAlgHom) g.ofConv
      (fun _ _ ↦ Commute.all _ _)).toLinearMap =
      E.toLinearMap ∘ₗ a.hom.toAlgHom.toLinearMap.rTensor A := by
    apply TensorProduct.ext'
    intro x y
    rfl
  exact DFunLike.congr_fun he _

/-- The invariance equation can be checked on all pairs of points. -/
theorem leftInvariantFunctions_iff (x : A) :
    x ∈ leftInvariantFunctions a ↔
      ∀ (R : TestAlgebra k) (g : WithConv (A →ₐ[k] R)) (h : B →ₐ[k] R),
        (toConv (h.comp a.hom.toAlgHom) * g) x = g x := by
  rw [mem_leftInvariantFunctions]
  constructor
  · intro hx R g h
    rw [leftProduct_apply, hx, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  · intro hx
    let R := CommAlgCat.of k (B ⊗[k] A)
    let g : WithConv (A →ₐ[k] R) := toConv Algebra.TensorProduct.includeRight
    let h : B →ₐ[k] R := Algebra.TensorProduct.includeLeft
    have he : Algebra.TensorProduct.lift h g.ofConv (fun _ _ ↦ Commute.all _ _) =
        AlgHom.id k (B ⊗[k] A) := by
      ext <;> simp [g, h, R]
    have hh := hx R g h
    rw [leftProduct_apply, he] at hh
    exact hh

private theorem rightProduct_apply (x : A) {R : Type u} [CommRing R] [Algebra k R]
    (g : WithConv (A →ₐ[k] R)) (h : B →ₐ[k] R) :
    (g * toConv (h.comp a.hom.toAlgHom)) x =
      Algebra.TensorProduct.lift g.ofConv h (fun _ _ ↦ Commute.all _ _)
        (a.hom.toAlgHom.toLinearMap.lTensor A (comul x)) := by
  rw [AlgHom.convMul_apply]
  let E := Algebra.TensorProduct.lift g.ofConv h (fun _ _ ↦ Commute.all _ _)
  have he : (Algebra.TensorProduct.lift g.ofConv (h.comp a.hom.toAlgHom)
      (fun _ _ ↦ Commute.all _ _)).toLinearMap =
      E.toLinearMap ∘ₗ a.hom.toAlgHom.toLinearMap.lTensor A := by
    apply TensorProduct.ext'
    intro x y
    rfl
  exact DFunLike.congr_fun he _

private theorem rightInvariant_iff (x : A) :
    a.hom.toAlgHom.toLinearMap.lTensor A (comul x) = x ⊗ₜ[k] (1 : B) ↔
      ∀ (R : TestAlgebra k) (g : WithConv (A →ₐ[k] R)) (h : B →ₐ[k] R),
        (g * toConv (h.comp a.hom.toAlgHom)) x = g x := by
  constructor
  · intro hx R g h
    rw [rightProduct_apply, hx, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  · intro hx
    let R := CommAlgCat.of k (A ⊗[k] B)
    let g : WithConv (A →ₐ[k] R) := toConv Algebra.TensorProduct.includeLeft
    let h : B →ₐ[k] R := Algebra.TensorProduct.includeRight
    have he : Algebra.TensorProduct.lift g.ofConv h (fun _ _ ↦ Commute.all _ _) =
        AlgHom.id k (A ⊗[k] B) := by
      ext <;> simp [g, h, R]
    have hh := hx R g h
    rw [rightProduct_apply, he] at hh
    exact hh

/-- The subgroup is normal in the functor-of-points description of Hopf spectra. -/
def ConvolutionNormal : Prop :=
  ∀ (R : TestAlgebra k) (g : WithConv (A →ₐ[k] R)) (h : B →ₐ[k] R),
    ∃ h' : B →ₐ[k] R,
      g * toConv (h.comp a.hom.toAlgHom) = toConv (h'.comp a.hom.toAlgHom) * g

theorem convolutionNormal_of_schemeNormal (hn : IsNormalSubgroup (specGroupMap a)) :
    ConvolutionNormal a := by
  obtain ⟨E, _, hE⟩ := hopfSpecPoints k
  intro R g h
  let g' : Points (specGroup A).X R := (E A).hom.app R g
  let h' : Points (specGroup B).X R := (E B).hom.app R (toConv h)
  obtain ⟨n, hn'⟩ := normalSubgroup_conjugate_sections hn g' h'
  obtain ⟨v, hv⟩ := (ConcreteCategory.bijective_of_isIso ((E B).hom.app R)).2 n
  refine ⟨v.ofConv, (ConcreteCategory.bijective_of_isIso ((E A).hom.app R)).1 ?_⟩
  rw [map_mul, map_mul, hE a R (toConv h), hE a R v, hv]
  change g' * (h' ≫ (specGroupMap a).hom.hom) =
    (n ≫ (specGroupMap a).hom.hom) * g'
  rw [hn', mul_assoc, inv_mul_cancel, mul_one]

theorem leftInvariant_of_rightInvariant (hn : ConvolutionNormal a) (x : A)
    (hx : ∀ (R : TestAlgebra k) (g : WithConv (A →ₐ[k] R)) (h : B →ₐ[k] R),
      (g * toConv (h.comp a.hom.toAlgHom)) x = g x) :
    x ∈ leftInvariantFunctions a := by
  apply (leftInvariantFunctions_iff a x).mpr
  intro R g h
  let : Group (WithConv (A →ₐ[k] R)) := convolutionGroup A R
  obtain ⟨h', he⟩ := hn R g⁻¹ h
  have he' := congrArg (fun t : WithConv (A →ₐ[k] R) ↦ g * t * g) he
  have he'' : toConv (h.comp a.hom.toAlgHom) * g =
      g * toConv (h'.comp a.hom.toAlgHom) := by
    calc
      _ = g * (g⁻¹ * toConv (h.comp a.hom.toAlgHom)) * g := by
        rw [← mul_assoc g g⁻¹, mul_inv_cancel, one_mul]
      _ = _ := by rw [he, mul_assoc g, mul_assoc, inv_mul_cancel, mul_one]
  rw [he'', hx]

open HopfAlgebra in
theorem rightInverseWeight_of_leftWeight (c : B) (hc : IsGroupLikeElem k c)
    (m : ℕ) (w : A)
    (hw : a.hom.toAlgHom.toLinearMap.rTensor A (comul w) = (c ^ m) ⊗ₜ[k] w)
    (R : TestAlgebra k) (g : WithConv (A →ₐ[k] R)) (h : B →ₐ[k] R) :
    (g * toConv (h.comp a.hom.toAlgHom)) (antipode k w) * h c ^ m = g (antipode k w) := by
  let : Group (WithConv (A →ₐ[k] R)) := convolutionGroup A R
  let : Group (WithConv (B →ₐ[k] R)) := convolutionGroup B R
  let d := toConv (h.comp a.hom.toAlgHom)
  let hInv := (toConv h)⁻¹
  have hd : d⁻¹ = toConv (hInv.ofConv.comp a.hom.toAlgHom) := by
    apply WithConv.ofConv_injective
    change (h.comp a.hom.toAlgHom).comp (antipodeAlgHom k A) =
      (h.comp (antipodeAlgHom k B)).comp a.hom.toAlgHom
    rw [AlgHom.comp_assoc, (hopfSpecMorphism k a).2, ← AlgHom.comp_assoc]
  have hv (z : WithConv (A →ₐ[k] R)) : z (antipode k w) = z⁻¹ w := rfl
  have hch : hInv (c ^ m) * h c ^ m = 1 := by
    change h (antipodeAlgHom k B (c ^ m)) * h c ^ m = 1
    rw [map_pow, map_pow, ← mul_pow, ← map_mul,
      show antipodeAlgHom k B c * c = 1 from hc.antipode_mul_cancel, map_one, one_pow]
  change (g * d) (antipode k w) * h c ^ m = g (antipode k w)
  rw [hv, mul_inv_rev, hd, leftProduct_apply a w, hw, Algebra.TensorProduct.lift_tmul]
  change (hInv (c ^ m) * g⁻¹ w) * h c ^ m = _
  calc
    _ = (hInv (c ^ m) * h c ^ m) * g⁻¹ w := by ac_rfl
    _ = g (antipode k w) := by rw [hch, one_mul, hv]

open LinearAlgebraicGroups.RationalRepresentations

private def comoduleRepresentation {V Index : Type u} [AddCommGroup V]
    [Module k V] [Fintype Index] [DecidableEq Index]
    (b : Module.Basis Index k V) (ρ : RightComodule k A V) :
    convolutionPoints A ⟶ Specs.StandardGroups.generalLinearPoints k Index :=
  matrixPointHom A (coefficients A b ρ) (coefficients_isCoactionMatrix A b ρ)

private theorem matrixRepresentation_eq_one_iff {V Index : Type u} [AddCommGroup V]
    [Module k V] [Fintype Index] [DecidableEq Index]
    (b : Module.Basis Index k V) (ρ : RightComodule k A V) (R : TestAlgebra k)
    (g : WithConv (A →ₐ[k] R)) :
    (comoduleRepresentation b ρ).app R g = 1 ↔
      ∀ v : V, evaluate A ρ g.ofConv v = v ⊗ₜ[k] (1 : R) := by
  have hmatrix : ∀ i j,
      ((comoduleRepresentation b ρ).app R g : Matrix.GeneralLinearGroup Index R).val i j =
        g (coefficients A b ρ i j) := fun _ _ ↦ rfl
  have heval (j : Index) : evaluate A ρ g.ofConv (b j) =
      ∑ i, b i ⊗ₜ[k] g (coefficients A b ρ i j) := by
    unfold evaluate
    rw [LinearMap.comp_apply, coaction_apply_basis]
    simp
  constructor
  · intro hg
    have hlin : evaluate A ρ g.ofConv = (TensorProduct.mk k V R).flip 1 := by
      apply b.ext
      intro j
      rw [heval]
      have hentry (i : Index) : g (coefficients A b ρ i j) = (1 : Matrix Index Index R) i j :=
        (hmatrix i j).symm.trans (congrArg (fun x : Matrix.GeneralLinearGroup Index R ↦
          x.val i j) hg)
      change (∑ i, b i ⊗ₜ[k] g (coefficients A b ρ i j)) = b j ⊗ₜ[k] (1 : R)
      simp [hentry, Matrix.one_apply, TensorProduct.tmul_ite]
    intro v
    rw [hlin]
    rfl
  · intro hg
    apply Units.ext
    ext i j
    rw [hmatrix]
    change g (coefficients A b ρ i j) = (1 : Matrix Index Index R) i j
    have h := congrArg (tensorCoordinate b i) ((heval j).symm.trans (hg (b j)))
    rw [tensorCoordinate_sum_basis] at h
    simpa [tensorCoordinate, Matrix.one_apply, Module.Basis.coord_apply, Finsupp.single_apply,
      eq_comm] using h

private theorem counit_value_of_fixed_translation (R : TestAlgebra k)
    (g : A →ₐ[k] R) (x : A)
    (hx : g.toLinearMap.lTensor A (comul x) = x ⊗ₜ[k] (1 : R)) :
    g x = algebraMap k R (counit x) := by
  have hc (t : A ⊗[k] A) :
      (TensorProduct.lid k R) (counit.rTensor R (g.toLinearMap.lTensor A t)) =
        g ((TensorProduct.lid k A) (counit.rTensor A t)) := by
    induction t with
    | add x y hx hy => simp [hx, hy]
    | tmul x y => simp
  have hh := congrArg (fun t : A ⊗[k] R ↦
    (TensorProduct.lid k R) (counit.rTensor R t)) hx
  rw [hc, rTensor_counit_comul] at hh
  simpa [Algebra.smul_def] using hh

private theorem invariantCoaction_representation (hn : ConvolutionNormal a)
    {V J : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (σ : RightComodule k A V) (i : V →ₗ[k] A)
    (hi : Function.Injective i) (hmem : ∀ v, i v ∈ leftInvariantFunctions a)
    (hcoact : ∀ v, i.rTensor A (σ.coaction v) = comul (i v))
    (v : J → V) (s : J → A) (hv : ∀ j, i (v j) = s j) :
    ∃ (Index : Type u) (_ : Fintype Index) (_ : DecidableEq Index)
      (α : convolutionPoints A ⟶ Specs.StandardGroups.generalLinearPoints k Index),
      ∀ (R : TestAlgebra k) (g : WithConv (A →ₐ[k] R)),
        (∀ h : B →ₐ[k] R, g = toConv (h.comp a.hom.toAlgHom) → α.app R g = 1) ∧
        (α.app R g = 1 → ∀ j, g (s j) = algebraMap k R (counit (s j))) := by
  classical
  let : Module.Free k V := Module.Free.of_divisionRing k V
  let Index := ULift.{u} (Fin (Module.finrank k V))
  let fI : Fintype Index := inferInstanceAs (Fintype (ULift.{u} (Fin (Module.finrank k V))))
  let dI : DecidableEq Index := Classical.decEq Index
  let b : Module.Basis Index k V := (Module.finBasis k V).reindex Equiv.ulift.symm
  let α := @comoduleRepresentation k _ A V Index _ _ fI dI b σ
  refine ⟨Index, fI, dI, α, fun R g ↦ ?_⟩
  have hmatrix (x : WithConv (A →ₐ[k] R)) :
      α.app R x = 1 ↔ ∀ w : V, evaluate A σ x.ofConv w = w ⊗ₜ[k] (1 : R) :=
    @matrixRepresentation_eq_one_iff k _ A V Index _ _ fI dI b σ R x
  have heval (f : A →ₐ[k] R) (w : V) :
      i.rTensor R (evaluate A σ f w) = f.toLinearMap.lTensor A (comul (i w)) := by
    change (i.rTensor R ∘ₗ f.toLinearMap.lTensor V) (σ.coaction w) = _
    rw [LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
      LinearMap.comp_apply, hcoact]
  constructor
  · rintro h rfl
    apply (hmatrix _).mpr
    intro w
    apply Module.Flat.rTensor_preserves_injective_linearMap i hi
    rw [heval, LinearMap.rTensor_tmul]
    have hw := (rightInvariant_iff a (i w)).mpr (fun T g' h' ↦ by
      obtain ⟨z, hz⟩ := hn T g' h'
      rw [hz, (leftInvariantFunctions_iff a (i w)).mp (hmem w) T g' z])
    change (h.comp a.hom.toAlgHom).toLinearMap.lTensor A (comul (i w)) = _
    rw [show (h.comp a.hom.toAlgHom).toLinearMap =
      h.toLinearMap ∘ₗ a.hom.toAlgHom.toLinearMap from rfl,
      LinearMap.lTensor_comp_apply, hw, LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, map_one]
  · intro hg j
    have h := (hmatrix g).mp hg (v j)
    rw [← hv j]
    apply counit_value_of_fixed_translation R g.ofConv (i (v j))
    rw [← heval, h, LinearMap.rTensor_tmul]

/-- A finite list of invariant functions lies in a finite-dimensional representation
trivial on the subgroup, whose kernel preserves the values at the identity of the list. -/
theorem exists_representation_of_invariantFunctions (hn : ConvolutionNormal a)
    {J : Type u} [Finite J] (s : J → A)
    (hs : ∀ j, s j ∈ leftInvariantFunctions a) :
    ∃ (Index : Type u) (_ : Fintype Index) (_ : DecidableEq Index)
      (α : convolutionPoints A ⟶ Specs.StandardGroups.generalLinearPoints k Index),
      ∀ (R : TestAlgebra k) (g : WithConv (A →ₐ[k] R)),
        (∀ h : B →ₐ[k] R, g = toConv (h.comp a.hom.toAlgHom) → α.app R g = 1) ∧
        (α.app R g = 1 → ∀ j, g (s j) = algebraMap k R (counit (s j))) := by
  classical
  let U := leftInvariantFunctions a
  let sU (j : J) : U := ⟨s j, hs j⟩
  let reg := RightComodule.regular (k := k) (C := A)
  obtain ⟨ρ, hρ⟩ := (RightComodule.isSubcomodule_iff_exists_coaction reg U).mp
    (leftInvariantFunctions_isSubcomodule a)
  obtain ⟨⟨W, hstable, hfinite⟩, hW⟩ := ρ.exists_finiteSubcomodule_containing_range sU
  obtain ⟨σ, hσ⟩ := (RightComodule.isSubcomodule_iff_exists_coaction ρ W).mp hstable
  let : FiniteDimensional k W := hfinite
  let i : W →ₗ[k] A := U.subtype.comp W.subtype
  have hi : Function.Injective i := U.injective_subtype.comp W.injective_subtype
  have hmem (w : W) : i w ∈ leftInvariantFunctions a := w.val.property
  have hcoact (w : W) : i.rTensor A (σ.coaction w) = comul (i w) := by
    have h₁ := DFunLike.congr_fun hσ w
    have h₂ := DFunLike.congr_fun hρ (W.subtype w)
    simp only [LinearMap.comp_apply] at h₁ h₂
    rw [LinearMap.rTensor_comp_apply, h₁, h₂]
    rfl
  let v (j : J) : W := ⟨sU j, hW j⟩
  exact invariantCoaction_representation (V := ↥W) a hn σ i hi hmem hcoact v s (fun _ ↦ rfl)

end InvariantFunctions

/-- A subgroup with the kernel's points over every test algebra is the scheme kernel. -/
theorem schemeKernel_of_testPoints {G L : GroupScheme k} [IsAffine G.X.left]
    [IsAffine L.X.left] (f : G ⟶ L) (H : ClosedSubgroup G)
    (h : ∀ (R : TestAlgebra k) (g : Points G.X R),
      (∃ x : Points H.group.X R, x ≫ H.inclusion.hom.hom = g) ↔
        g ≫ f.hom.hom = 1) :
    IsSchemeKernel f H := by
  obtain ⟨N, hN⟩ := schemeKernel_exists f
  have : IsClosedImmersion H.inclusion.hom.hom.left := H.isClosedImmersion
  have : IsClosedImmersion N.inclusion.hom.hom.left := N.isClosedImmersion
  obtain ⟨A, ⟨eH⟩⟩ := essImage_algSpec.mpr
    (isAffine_of_isAffineHom H.inclusion.hom.hom.left)
  obtain ⟨B, ⟨eN⟩⟩ := essImage_algSpec.mpr
    (isAffine_of_isAffineHom N.inclusion.hom.hom.left)
  have hex : ∃ a : Points N.group.X A.unop,
      a ≫ N.inclusion.hom.hom = eH.hom ≫ H.inclusion.hom.hom :=
    (schemeKernel_sections hN (eH.hom ≫ H.inclusion.hom.hom)).mpr
      ((h A.unop _).mp ⟨eH.hom, rfl⟩)
  obtain ⟨a, ha⟩ := hex
  obtain ⟨b, hb⟩ := (h B.unop (eN.hom ≫ N.inclusion.hom.hom)).mpr
    ((schemeKernel_sections hN _).mp ⟨eN.hom, rfl⟩)
  let s := eH.inv ≫ a
  let t := eN.inv ≫ b
  have hs : s ≫ N.inclusion.hom.hom = H.inclusion.hom.hom := by
    change (eH.inv ≫ a) ≫ N.inclusion.hom.hom = _
    rw [Category.assoc, ha, Iso.inv_hom_id_assoc]
  have ht : t ≫ H.inclusion.hom.hom = N.inclusion.hom.hom := by
    change (eN.inv ≫ b) ≫ H.inclusion.hom.hom = _
    rw [Category.assoc, hb, Iso.inv_hom_id_assoc]
  have : Mono H.inclusion.hom.hom := Over.mono_of_mono_left _
  have : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
  let e : H.group.X ≅ N.group.X :=
    ⟨s, t, (cancel_mono H.inclusion.hom.hom).mp (by simp [Category.assoc, ht, hs]),
      (cancel_mono N.inclusion.hom.hom).mp (by simp [Category.assoc, hs, ht])⟩
  exact hN.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simpa using hs) ((isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _)
    (by simp) (by simp)

private def closedSubgroupOfHopfMap {A B : HopfAlgebraCategory k}
    (a : A ⟶ B) (ha : Function.Surjective a.hom) : ClosedSubgroup (specGroup A) :=
  ⟨specGroup B, specGroupMap a, (hopfMapClosedImmersion k a).mpr ha⟩

/-- Invariant regular functions separating the closed subgroup from the other
points over every test algebra give a homomorphism with the prescribed kernel. -/
theorem exists_schemeKernel_of_invariantFunctions {A B : HopfAlgebraCategory k}
    (a : A ⟶ B) (ha : Function.Surjective a.hom) (hn : ConvolutionNormal a)
    {J : Type u} [Finite J] (s : J → A) (hs : ∀ j, s j ∈ leftInvariantFunctions a)
    (hsep : ∀ (R : TestAlgebra k) (g : WithConv (A →ₐ[k] R)),
      (∀ j, g (s j) = algebraMap k R (Coalgebra.counit (s j))) →
        ∃ h : B →ₐ[k] R, g = toConv (h.comp a.hom.toAlgHom)) :
    ∃ (L : AffineAlgebraicGroup k) (f : specGroup A ⟶ L.val),
      IsSchemeKernel f (closedSubgroupOfHopfMap a ha) := by
  obtain ⟨Index, _, _, α, hα⟩ := exists_representation_of_invariantFunctions a hn s hs
  obtain ⟨E, _, hE⟩ := hopfSpecPoints k
  let L := StandardGroups.generalLinearGroup k Index
  let e : (groupPointsFunctor k).obj L.val ≅ Specs.StandardGroups.generalLinearPoints k Index :=
    StandardGroups.generalLinearGroupPointsIso k Index
  let H := closedSubgroupOfHopfMap a ha
  have hG : IsAffine (specGroup A).X.left := ((affineHopfSpec k).obj (op A)).property
  let F := groupHomEquiv (specGroup A) L.val hG
  let f := F.symm ((E A).inv ≫ α ≫ e.inv)
  have hf : (groupPointsFunctor k).map f = (E A).inv ≫ α ≫ e.inv :=
    F.apply_symm_apply _
  let : IsAffine (specGroup A).X.left := hG
  let : IsAffine L.val.X.left := L.property.1
  refine ⟨L, f, schemeKernel_of_testPoints f H fun R x ↦ ?_⟩
  obtain ⟨g, rfl⟩ := (ConcreteCategory.bijective_of_isIso ((E A).hom.app R)).2 x
  have heval : (e.hom.app R) (((groupPointsFunctor k).map f).app R ((E A).hom.app R g)) =
      α.app R g := by simp [hf]
  have hpoint :
      ((E A).hom.app R g : Points (specGroup A).X R) ≫ f.hom.hom = 1 ↔ α.app R g = 1 := by
    change ((groupPointsFunctor k).map f).app R ((E A).hom.app R g) = 1 ↔ _
    rw [← heval, ← map_one (e.hom.app R).hom]
    exact (ConcreteCategory.bijective_of_isIso (e.hom.app R)).1.eq_iff.symm
  rw [hpoint]
  constructor
  · rintro ⟨h, hh⟩
    obtain ⟨v, rfl⟩ := (ConcreteCategory.bijective_of_isIso ((E B).hom.app R)).2 h
    apply (hα R g).1 v.ofConv
    apply (ConcreteCategory.bijective_of_isIso ((E A).hom.app R)).1
    rw [hE a R v]
    exact hh.symm
  · intro hg
    obtain ⟨h, rfl⟩ := hsep R g ((hα R g).2 hg)
    exact ⟨(E B).hom.app R (toConv h), (hE a R (toConv h)).symm⟩

section WeightFunctions

open Coalgebra Bialgebra

variable {A B : HopfAlgebraCategory k}

private def leftWeightCoaction (a : A ⟶ B) : A →ₐ[k] B ⊗[k] A :=
  (Algebra.TensorProduct.map a.hom.toAlgHom (AlgHom.id k A)).comp (comulAlgHom k A)

private theorem leftWeightCoaction_apply (a : A ⟶ B) (x : A) :
    leftWeightCoaction a x = a.hom.toAlgHom.toLinearMap.rTensor A (comul x) := rfl

private def sliceLeft {V W : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (l : V →ₗ[k] k) : V ⊗[k] W →ₗ[k] W :=
  (TensorProduct.lid k W).toLinearMap.comp (l.rTensor W)

private def sliceRight {V W : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (l : W →ₗ[k] k) : V ⊗[k] W →ₗ[k] V :=
  (TensorProduct.rid k V).toLinearMap.comp (l.lTensor V)

@[simp] private theorem sliceLeft_tmul {V W : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (l : V →ₗ[k] k) (x : V) (y : W) :
    sliceLeft l (x ⊗ₜ[k] y) = l x • y := by simp [sliceLeft]

@[simp] private theorem sliceRight_tmul {V W : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (l : W →ₗ[k] k) (x : V) (y : W) :
    sliceRight l (x ⊗ₜ[k] y) = l y • x := by simp [sliceRight]

private theorem apply_sliceLeft {V W U : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]
    (l : V →ₗ[k] k) (f : W →ₗ[k] U) (z : V ⊗[k] W) :
    f (sliceLeft l z) = sliceLeft l (f.lTensor V z) := by
  induction z <;> simp_all

private theorem eval_sliceLeft {V W : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (l : V →ₗ[k] k) (g : W →ₗ[k] k)
    (z : V ⊗[k] W) :
    g (sliceLeft l z) = l (sliceRight g z) := by
  induction z <;> simp_all [mul_comm]

open private precomposePoint postcomposePoint from LinearAlgebraicGroups.Affine.HopfFaithfulFlatness

/-- Conjugation by a rational point, restricted to the normal subgroup. -/
private theorem exists_conjugationMap (a : A ⟶ B) (ha : Function.Surjective a.hom)
    (hn : ConvolutionNormal a) (g : A →ₐ[k] k) :
    ∃ v : B →ₐc[k] B,
      toConv a.hom.toAlgHom * toConv ((Algebra.ofId k B).comp g) =
        toConv ((Algebra.ofId k B).comp g) * toConv (v.toAlgHom.comp a.hom.toAlgHom) := by
  let γ (R : TestAlgebra k) : WithConv (A →ₐ[k] R) :=
    toConv ((Algebra.ofId k R).comp g)
  let B₀ := CommAlgCat.of k B
  let : Group (WithConv (A →ₐ[k] B₀)) := convolutionGroup A B₀
  obtain ⟨v, hv⟩ := hn B₀ (γ B₀)⁻¹ (AlgHom.id k B)
  have eqB : toConv a.hom.toAlgHom * γ B₀ =
      γ B₀ * toConv (v.comp a.hom.toAlgHom) := by
    have h := congrArg (fun z : WithConv (A →ₐ[k] B₀) ↦ γ B₀ * z * γ B₀) hv
    rw [← mul_assoc (γ B₀) (γ B₀)⁻¹, mul_inv_cancel, one_mul, AlgHom.id_comp,
      mul_assoc (γ B₀), mul_assoc _ (γ B₀)⁻¹, inv_mul_cancel, mul_one] at h
    exact h
  let P (R : TestAlgebra k) := precomposePoint (T := R) a.hom
  let V (R : TestAlgebra k) (h : WithConv (B →ₐ[k] R)) := toConv (h.ofConv.comp v)
  have P_inj (R : TestAlgebra k) : Function.Injective (P R) := by
    intro x y h
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro b
    obtain ⟨a₀, rfl⟩ := ha b
    exact DFunLike.congr_fun (congrArg WithConv.ofConv h) a₀
  have conj (R : TestAlgebra k) (h : WithConv (B →ₐ[k] R)) :
      P R h * γ R = γ R * P R (V R h) := by
    have eq := congrArg (postcomposePoint (X := A) h.ofConv) eqB
    rw [map_mul, map_mul] at eq
    have hg : postcomposePoint h.ofConv (γ B₀) = γ R := by
      apply WithConv.ofConv_injective
      ext x
      exact h.ofConv.commutes (g x)
    rw [hg] at eq
    exact eq
  have v_one (R : TestAlgebra k) : V R 1 = 1 := by
    apply P_inj R
    let : Group (WithConv (A →ₐ[k] R)) := convolutionGroup A R
    apply mul_left_cancel (a := γ R)
    rw [← conj, map_one, one_mul, mul_one]
  have v_mul (R : TestAlgebra k) (x y : WithConv (B →ₐ[k] R)) :
      V R (x * y) = V R x * V R y := by
    apply P_inj R
    let : Group (WithConv (A →ₐ[k] R)) := convolutionGroup A R
    apply mul_left_cancel (a := γ R)
    rw [← conj, map_mul, map_mul, mul_assoc (P R x), conj R y,
      ← mul_assoc (P R x), conj R x, mul_assoc]
  have hv_counit : (counitAlgHom k B).comp v = counitAlgHom k B :=
    congrArg WithConv.ofConv (v_one (CommAlgCat.of k k))
  have hv_comul : (Algebra.TensorProduct.map v v).comp (comulAlgHom k B) =
      (comulAlgHom k B).comp v := by
    let R := CommAlgCat.of k (B ⊗[k] B)
    let l : B →ₐ[k] R := Algebra.TensorProduct.includeLeft
    let r : B →ₐ[k] R := Algebra.TensorProduct.includeRight
    apply AlgHom.ext
    intro x
    have h := DFunLike.congr_fun (congrArg WithConv.ofConv (v_mul R (toConv l) (toConv r))) x
    change (toConv l * toConv r) (v x) =
      (toConv (l.comp v) * toConv (r.comp v)) x at h
    rw [AlgHom.convMul_apply, AlgHom.convMul_apply] at h
    have hlr : Algebra.TensorProduct.lift l r (fun _ _ ↦ Commute.all _ _) = AlgHom.id k R := by
      ext <;> simp [l, r, R]
    have hvr : Algebra.TensorProduct.lift (l.comp v) (r.comp v) (fun _ _ ↦ Commute.all _ _) =
        Algebra.TensorProduct.map v v := by
      ext <;> simp [l, r, R]
    rw [hlr, hvr] at h
    exact h.symm
  exact ⟨BialgHom.ofAlgHom v hv_counit hv_comul, eqB⟩

private theorem rightWeight_apply (a : A ⟶ B) {x : A} {d : B}
    (hx : a.hom.toAlgHom.toLinearMap.lTensor A (comul x) = x ⊗ₜ[k] d)
    (R : TestAlgebra k) (g : WithConv (A →ₐ[k] R)) (h : B →ₐ[k] R) :
    (g * toConv (h.comp a.hom.toAlgHom)) x = g x * h d := by
  rw [rightProduct_apply, hx, Algebra.TensorProduct.lift_tmul]

/-- The left translates of a right weight, evaluated at a rational point
in the second factor, are scalar multiples of characters. -/
private theorem leftWeight_sliceRight (a : A ⟶ B) (ha : Function.Surjective a.hom)
    (hn : ConvolutionNormal a) {x : A} {d : B} (hd : IsGroupLikeElem k d)
    (hx : a.hom.toAlgHom.toLinearMap.lTensor A (comul x) = x ⊗ₜ[k] d) (g : A →ₐ[k] k) :
    ∃ d' : B, IsGroupLikeElem k d' ∧
      sliceRight g.toLinearMap (leftWeightCoaction a x) = g x • d' := by
  obtain ⟨v, hv⟩ := exists_conjugationMap a ha hn g
  refine ⟨v d, hd.map v, ?_⟩
  let R := CommAlgCat.of k B
  let gB : WithConv (A →ₐ[k] R) := toConv ((Algebra.ofId k B).comp g)
  have eval (z : B ⊗[k] A) :
      sliceRight g.toLinearMap z =
        Algebra.TensorProduct.lift (AlgHom.id k B) gB.ofConv (fun _ _ ↦ Commute.all _ _) z := by
    induction z with
    | add x y hx hy => simp [hx, hy]
    | tmul b x =>
      simp [gB, Algebra.smul_def, mul_comm]
  rw [leftWeightCoaction_apply, eval]
  have hleft := leftProduct_apply a x gB (AlgHom.id k B)
  rw [← hleft]
  change (toConv a.hom.toAlgHom * gB) x = g x • v d
  rw [hv, rightWeight_apply a hx R gB v.toAlgHom]
  exact (Algebra.smul_def (g x) (v d)).symm

private theorem comul_sliceRight_coaction (a : A ⟶ B) (g : A →ₗ[k] k) (x : A) :
    comul (sliceRight g (leftWeightCoaction a x)) =
      (sliceRight g ∘ₗ (leftWeightCoaction a).toLinearMap).lTensor B
        (leftWeightCoaction a x) := by
  let f := a.hom.toAlgHom.toLinearMap
  let ΔA := comul (R := k) (A := A)
  let ΔB := comul (R := k) (A := B)
  let P : (A ⊗[k] A) ⊗[k] A →ₗ[k] B ⊗[k] B :=
    sliceRight g ∘ₗ (TensorProduct.map f f).rTensor A
  have h₁ (t : A ⊗[k] A) :
      ΔB (sliceRight g (f.rTensor A t)) = P (ΔA.rTensor A t) := by
    induction t with
    | add y z hy hz => simp [hy, hz]
    | tmul y z =>
      simp only [LinearMap.rTensor_tmul, sliceRight_tmul, map_smul, P, LinearMap.comp_apply]
      exact congrArg (fun t : B ⊗[k] B ↦ g z • t)
        (CoalgHomClass.map_comp_comul_apply (f := a.hom) y).symm
  have h₂ (t : A ⊗[k] A) :
      P ((TensorProduct.assoc k A A A).symm (ΔA.lTensor A t)) =
        (sliceRight g ∘ₗ (leftWeightCoaction a).toLinearMap).lTensor B (f.rTensor A t) := by
    induction t with
    | add y z hy hz => simp [hy, hz]
    | tmul y z =>
      simp only [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, LinearMap.comp_apply,
        AlgHom.toLinearMap_apply, leftWeightCoaction_apply]
      change P ((TensorProduct.assoc k A A A).symm (y ⊗ₜ[k] ΔA z)) =
        f y ⊗ₜ[k] sliceRight g (f.rTensor A (ΔA z))
      generalize ΔA z = s
      induction s with
      | add v w hv hw => simp only [TensorProduct.tmul_add, map_add, hv, hw]
      | tmul v w =>
        simp [P, TensorProduct.tmul_smul]
  rw [leftWeightCoaction_apply, h₁, ← Coalgebra.coassoc_symm_apply]
  exact h₂ _

private theorem sliceLeft_coaction_eval (a : A ⟶ B) (l : B →ₗ[k] k) (g : A →ₗ[k] k) (x : A) :
    sliceRight g (leftWeightCoaction a (sliceLeft l (leftWeightCoaction a x))) =
      sliceLeft l (comul (sliceRight g (leftWeightCoaction a x))) := by
  rw [comul_sliceRight_coaction, ← apply_sliceLeft]
  rfl

private theorem leftWeightCoaction_mem_range (a : A ⟶ B) {p r : ℕ} [ExpChar k p]
    (D : Subalgebra k A) (hpow : ∀ x : A, x ^ (p ^ r) ∈ D)
    (hroot : ∀ x ∈ D, ∃ y : A, y ^ (p ^ r) = x) {x : A} (hx : x ∈ D) :
    leftWeightCoaction a x ∈ (Algebra.TensorProduct.map (AlgHom.id k B) D.val).range := by
  let F := Algebra.TensorProduct.map (AlgHom.id k B) D.val
  have : ExpChar (B ⊗[k] A) p := expChar_of_injective_algebraMap
    (Bialgebra.algebraMap_injective (R := k) (B ⊗[k] A)) p
  obtain ⟨y, rfl⟩ := hroot x hx
  rw [map_pow]
  generalize leftWeightCoaction a y = z
  change iterateFrobenius (B ⊗[k] A) p r z ∈ F.range
  induction z with
  | add v w hv hw => rw [map_add]; exact F.range.add_mem hv hw
  | tmul b v =>
    exact ⟨(b ^ (p ^ r)) ⊗ₜ[k] (⟨v ^ (p ^ r), hpow v⟩ : D),
      (Algebra.TensorProduct.tmul_pow b v (p ^ r)).symm⟩

private theorem sliceLeft_map_subalgebra (l : B →ₗ[k] k) (D : Subalgebra k A)
    (z : B ⊗[k] D) :
    sliceLeft l (Algebra.TensorProduct.map (AlgHom.id k B) D.val z) =
      (sliceLeft l z : D).val := by
  induction z <;> simp_all

/-- Points detecting a subalgebra detect tensors with all right coefficients in it. -/
private theorem tensor_range_eq_zero (D : Subalgebra k A)
    (hsep : ∀ x ∈ D, (∀ g : A →ₐ[k] k, g x = 0) → x = 0)
    (z : B ⊗[k] A) (hz : z ∈ (Algebra.TensorProduct.map (AlgHom.id k B) D.val).range)
    (h : ∀ g : A →ₐ[k] k, sliceRight g.toLinearMap z = 0) : z = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace k B
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  ext i
  rw [map_zero, Finsupp.zero_apply, TensorProduct.equivFinsuppOfBasisLeft_apply]
  change sliceLeft (b.coord i) z = 0
  apply hsep
  · obtain ⟨z', rfl⟩ := hz
    change sliceLeft (b.coord i) (Algebra.TensorProduct.map (AlgHom.id k B) D.val z') ∈ D
    rw [sliceLeft_map_subalgebra]
    exact Subtype.prop _
  · intro g
    change g.toLinearMap (sliceLeft (b.coord i) z) = 0
    rw [eval_sliceLeft, h, map_zero]

private theorem exists_leftWeight_over_isAlgClosed [IsAlgClosed k]
    [Algebra.FiniteType k A] (a : A ⟶ B) (ha : Function.Surjective a.hom)
    (hn : ConvolutionNormal a) (c : B) (hc : IsGroupLikeElem k c)
    (t : A) (ht₁ : counit (R := k) t = 1)
    (ht : a.hom.toAlgHom.toLinearMap.lTensor A (comul t) = t ⊗ₜ[k] c) :
    ∃ (m : ℕ) (w : A), 0 < m ∧ counit (R := k) w = 1 ∧
      a.hom.toAlgHom.toLinearMap.rTensor A (comul w) = (c ^ m) ⊗ₜ[k] w := by
  let p := ringExpChar k
  obtain ⟨r, D, hpow, hroot, hsep⟩ := exists_powerSubalgebra A p
  let m := p ^ r
  have hm : 0 < m := by
    rcases expChar_is_prime_or_one k p with hp | hp
    · exact pow_pos hp.pos _
    · simp [m, hp]
  let x := t ^ m
  let d := c ^ m
  have hd : IsGroupLikeElem k d := hc.pow
  have hx : a.hom.toAlgHom.toLinearMap.lTensor A (comul x) = x ⊗ₜ[k] d := by
    let F := (Algebra.TensorProduct.map (AlgHom.id k A) a.hom.toAlgHom).comp (comulAlgHom k A)
    change F (t ^ m) = _
    rw [map_pow, show F t = t ⊗ₜ[k] c from ht, Algebra.TensorProduct.tmul_pow]
  obtain ⟨l, hl, hkill⟩ := exists_groupLikeFunctional B d hd
  let w := sliceLeft l (leftWeightCoaction a x)
  have hwmem : w ∈ D := by
    obtain ⟨z, hz⟩ := leftWeightCoaction_mem_range a D hpow hroot (hpow t)
    change sliceLeft l (leftWeightCoaction a x) ∈ D
    rw [← hz]
    change sliceLeft l (Algebra.TensorProduct.map (AlgHom.id k B) D.val z) ∈ D
    rw [sliceLeft_map_subalgebra]
    exact Subtype.prop _
  have hε : counit (R := k) w = 1 := by
    have hc' : a.hom t = c := by
      have e := congrArg (sliceLeft (counit (R := k) (A := A))) ht
      have he (z : A ⊗[k] A) :
          sliceLeft (counit (R := k) (A := A)) (a.hom.toAlgHom.toLinearMap.lTensor A z) =
            a.hom.toAlgHom.toLinearMap (sliceLeft (counit (R := k) (A := A)) z) :=
        (apply_sliceLeft _ _ _).symm
      rw [he, sliceLeft_tmul, ht₁, one_smul] at e
      simpa [sliceLeft, AlgHom.toLinearMap_apply] using e
    have he (z : A ⊗[k] A) :
        sliceRight (counit (R := k) (A := A)) (a.hom.toAlgHom.toLinearMap.rTensor A z) =
          a.hom.toAlgHom.toLinearMap (sliceRight (counit (R := k) (A := A)) z) := by
      induction z <;> simp_all
    change counit (R := k) (sliceLeft l (leftWeightCoaction a x)) = _
    rw [eval_sliceLeft, leftWeightCoaction_apply, he]
    have hεx : sliceRight (counit (R := k) (A := A)) (comul x) = x := by
      rw [sliceRight, LinearMap.comp_apply, lTensor_counit_comul]
      simp
    rw [hεx]
    change l (a.hom.toAlgHom (t ^ m)) = 1
    rw [map_pow, show a.hom.toAlgHom t = c from hc']
    exact hl
  refine ⟨m, w, hm, hε, ?_⟩
  rw [← leftWeightCoaction_apply, ← sub_eq_zero]
  apply tensor_range_eq_zero D hsep
  · apply Subalgebra.sub_mem
    · exact leftWeightCoaction_mem_range a D hpow hroot hwmem
    · exact ⟨d ⊗ₜ[k] (⟨w, hwmem⟩ : D), rfl⟩
  · intro g
    have hw : g w = l (sliceRight g.toLinearMap (leftWeightCoaction a x)) :=
      eval_sliceLeft l g.toLinearMap _
    change sliceRight g.toLinearMap
      (leftWeightCoaction a (sliceLeft l (leftWeightCoaction a x)) - d ⊗ₜ[k] w) = 0
    rw [map_sub, sliceRight_tmul, AlgHom.toLinearMap_apply, hw, sliceLeft_coaction_eval]
    obtain ⟨d', hd', he⟩ := leftWeight_sliceRight a ha hn hd hx g
    rw [he, map_smul, hd'.comul_eq_tmul_self, map_smul, sliceLeft_tmul, map_smul]
    by_cases h : d' = d
    · simp [h, hl]
    · simp [hkill d' hd' h]

end WeightFunctions

section WeightDescent

open Coalgebra Bialgebra TensorProduct.AlgebraTensorModule
open LinearAlgebraicGroups.RationalRepresentations

variable {A B : HopfAlgebraCategory k}
variable (K : Type u) [Field K] [Algebra k K]

open private restrictCoordinatePointMulEquiv from LinearAlgebraicGroups.Affine.RationalRepresentations

private theorem convolutionNormal_extend (a : A ⟶ B) (hn : ConvolutionNormal a) :
    ConvolutionNormal (extendedHopfMap K a) := by
  intro R g h
  let eA := restrictCoordinatePointMulEquiv A K R
  let eB := restrictCoordinatePointMulEquiv B K R
  obtain ⟨v, hv⟩ := hn ((restrictTestAlgebra k K).obj R) (eA g) (eB (toConv h)).ofConv
  let w := eB.symm (toConv v)
  have he (x : WithConv (extendedHopf K B →ₐ[K] R)) :
      eA (toConv (x.ofConv.comp (extendedHopfMap K a).hom.toAlgHom)) =
        toConv ((eB x).ofConv.comp a.hom.toAlgHom) := by
    apply WithConv.ofConv_injective
    exact AlgHom.ext fun _ ↦ rfl
  refine ⟨w.ofConv, eA.injective ?_⟩
  change eA (g * toConv (h.comp (extendedHopfMap K a).hom.toAlgHom)) =
    eA (toConv (w.ofConv.comp (extendedHopfMap K a).hom.toAlgHom) * g)
  have hh := he (toConv h)
  change eA (toConv (h.comp (extendedHopfMap K a).hom.toAlgHom)) =
    toConv ((eB (toConv h)).ofConv.comp a.hom.toAlgHom) at hh
  rw [map_mul, map_mul, hh, he w, show eB w = toConv v from eB.apply_symm_apply _]
  exact hv

private theorem extend_comul_one_tmul (x : A) :
    comul (R := K) ((1 : K) ⊗ₜ[k] x) =
      distribBaseChange k K A A ((1 : K) ⊗ₜ[k] comul x) := by
  rw [TensorProduct.comul_tmul, Bialgebra.comul_one]
  generalize comul (R := k) x = t
  induction t with
  | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
  | tmul y z => rfl

private theorem extend_rightCoaction_one_tmul (a : A ⟶ B) (x : A) :
    (extendedHopfMap K a).hom.toAlgHom.toLinearMap.lTensor (extendedHopf K A)
      (comul ((1 : K) ⊗ₜ[k] x)) =
    distribBaseChange k K A B ((1 : K) ⊗ₜ[k] (a.hom.toAlgHom.toLinearMap.lTensor A (comul x))) := by
  rw [extend_comul_one_tmul]
  generalize comul (R := k) x = t
  induction t with
  | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
  | tmul y z => rfl

private theorem extend_leftCoaction (a : A ⟶ B) (z : K ⊗[k] A) :
    leftWeightCoaction (extendedHopfMap K a) z =
      distribBaseChange k K B A ((leftWeightCoaction a).toLinearMap.baseChange K z) := by
  let G := (leftWeightCoaction (extendedHopfMap K a)).toLinearMap
  let F := (leftWeightCoaction a).toLinearMap.baseChange K
  change G z = distribBaseChange k K B A (F z)
  have h (x : A) : G ((1 : K) ⊗ₜ[k] x) =
      distribBaseChange k K B A (F ((1 : K) ⊗ₜ[k] x)) := by
    change leftWeightCoaction (extendedHopfMap K a) ((1 : K) ⊗ₜ[k] x) = _
    rw [leftWeightCoaction_apply, extend_comul_one_tmul, LinearMap.baseChange_tmul,
      AlgHom.toLinearMap_apply, leftWeightCoaction_apply]
    generalize comul (R := k) x = t
    induction t with
    | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
    | tmul y z => rfl
  induction z with
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul s x =>
    rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul, map_smul, h, map_smul]

private theorem exists_leftWeight [Algebra.FiniteType k A] (a : A ⟶ B)
    (ha : Function.Surjective a.hom) (hn : ConvolutionNormal a) (c : B)
    (hc : IsGroupLikeElem k c) (t : A) (ht₁ : counit (R := k) t = 1)
    (ht : a.hom.toAlgHom.toLinearMap.lTensor A (comul t) = t ⊗ₜ[k] c) :
    ∃ (m : ℕ) (w : A), 0 < m ∧ counit (R := k) w = 1 ∧
      a.hom.toAlgHom.toLinearMap.rTensor A (comul w) = (c ^ m) ⊗ₜ[k] w := by
  let K := AlgebraicClosure k
  let F := extendedHopfMap K a
  have haK : Function.Surjective F.hom :=
    LinearMap.lTensor_surjective K (g := a.hom.toAlgHom.toLinearMap) ha
  let tK : extendedHopf K A := (1 : K) ⊗ₜ[k] t
  let cK : extendedHopf K B := (1 : K) ⊗ₜ[k] c
  have htK : F.hom.toAlgHom.toLinearMap.lTensor (extendedHopf K A) (comul tK) =
      tK ⊗ₜ[K] cK := by
    rw [show tK = (1 : K) ⊗ₜ[k] t from rfl, extend_rightCoaction_one_tmul, ht]
    rfl
  have hcK : IsGroupLikeElem K cK := by
    constructor
    · simp [cK, hc.counit_eq_one]
    · rw [show cK = (1 : K) ⊗ₜ[k] c from rfl, extend_comul_one_tmul, hc.comul_eq_tmul_self]
      rfl
  have htK₁ : counit (R := K) tK = 1 := by simp [tK, ht₁]
  obtain ⟨m, z, hm, hz₁, hz⟩ :=
    exists_leftWeight_over_isAlgClosed F haK (convolutionNormal_extend K a hn)
      cK hcK tK htK₁ htK
  let j : k →ₗ[k] K := (Algebra.ofId k K).toLinearMap
  have hj : LinearMap.ker j = ⊥ := LinearMap.ker_eq_bot.mpr (FaithfulSMul.algebraMap_injective k K)
  obtain ⟨l, hl⟩ := j.exists_leftInverse_of_injective hj
  have hl₁ : l 1 = 1 := by
    have h := DFunLike.congr_fun hl (1 : k)
    simpa [j] using h
  let w := sliceLeft l z
  have hε (y : K ⊗[k] A) :
      counit (R := k) (sliceLeft l y) = l (counit (R := K) y) := by
    induction y with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul s x => simp [mul_comm]
  refine ⟨m, w, hm, (hε z).trans ((congrArg l hz₁).trans hl₁), ?_⟩
  let L := (leftWeightCoaction a).toLinearMap
  let J := TensorProduct.mk k B A (c ^ m)
  let e := distribBaseChange k K B A
  have he : e (L.baseChange K z) = (cK ^ m) ⊗ₜ[K] z := by
    rw [← extend_leftCoaction, leftWeightCoaction_apply, hz]
  have hJ (y : K ⊗[k] A) : e.symm ((cK ^ m) ⊗ₜ[K] y) = J.baseChange K y := by
    induction y with
    | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
    | tmul s x =>
      simp [e, cK, Algebra.TensorProduct.tmul_pow, J]
  have h := congrArg (sliceLeft l) ((e.eq_symm_apply.mpr he).trans (hJ z))
  simp only [LinearMap.baseChange_eq_lTensor, ← apply_sliceLeft] at h
  exact h

end WeightDescent

section MatrixColumn

open Coalgebra LinearAlgebraicGroups.RationalRepresentations

variable {A B : HopfAlgebraCategory k} (a : A ⟶ B)
  {Index : Type u} [Fintype Index] [DecidableEq Index]
  (M : Matrix Index Index A) (hM : IsCoactionMatrix A M) (i : Index)
  (hcol : ∀ j ≠ i, a.hom (M j i) = 0)

include hM hcol

private theorem weight_of_column_isGroupLike : IsGroupLikeElem k (a.hom (M i i)) where
  counit_eq_one := by simp [CoalgHomClass.counit_comp_apply, hM.counit]
  comul_eq_tmul_self := by
    rw [← CoalgHomClass.map_comp_comul_apply, hM.comul, map_sum]
    simp only [TensorProduct.map_tmul]
    rw [Finset.sum_eq_single i]
    · rfl
    · intro j _ hj
      change a.hom (M i j) ⊗ₜ[k] a.hom (M j i) = 0
      rw [hcol j hj, TensorProduct.tmul_zero]
    · simp

private theorem rightWeight_of_column (R : TestAlgebra k) (g : WithConv (A →ₐ[k] R))
    (h : B →ₐ[k] R) (j : Index) :
    (g * toConv (h.comp a.hom.toAlgHom)) (M j i) = g (M j i) * h (a.hom (M i i)) := by
  rw [AlgHom.convMul_apply, hM.comul, map_sum]
  simp only [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply]
  rw [Finset.sum_eq_single i]
  · rfl
  · intro l _ hl
    rw [show a.hom.toAlgHom (M l i) = 0 from hcol l hl, map_zero, mul_zero]
  · simp

/-- A normalized function of inverse weight yields invariant mixed coefficients
that still detect the original line on arbitrary test rings. -/
theorem exists_schemeKernel_of_inverseWeight (ha : Function.Surjective a.hom)
    (hn : ConvolutionNormal a)
    (hdetect : ∀ (R : TestAlgebra k) (g : WithConv (A →ₐ[k] R)),
      (∀ j ≠ i, g (M j i) = 0) → ∃ h : B →ₐ[k] R, g = toConv (h.comp a.hom.toAlgHom))
    (m : ℕ) (hm : 0 < m) (b : A) (hb : counit (R := k) b = 1)
    (hweight : ∀ (R : TestAlgebra k) (g : WithConv (A →ₐ[k] R)) (h : B →ₐ[k] R),
      (g * toConv (h.comp a.hom.toAlgHom)) b * h (a.hom (M i i)) ^ m = g b) :
    ∃ (L : AffineAlgebraicGroup k) (f : specGroup A ⟶ L.val),
      IsSchemeKernel f (closedSubgroupOfHopfMap a ha) := by
  let s (j : Index) := M j i * M i i ^ (m - 1) * b
  have hpow : m - 1 + 1 = m := Nat.sub_add_cancel hm
  apply exists_schemeKernel_of_invariantFunctions a ha hn s
  · intro j
    apply leftInvariant_of_rightInvariant a hn
    intro R g h
    change ((g * toConv (h.comp a.hom.toAlgHom)).ofConv) (s j) = g.ofConv (s j)
    simp only [s, map_mul, map_pow]
    rw [rightWeight_of_column a M hM i hcol R g h j, rightWeight_of_column a M hM i hcol R g h i,
      mul_pow]
    let q := h (a.hom (M i i))
    change g (M j i) * q * (g (M i i) ^ (m - 1) * q ^ (m - 1)) *
      (g * toConv (h.comp a.hom.toAlgHom)) b = g (M j i) * g (M i i) ^ (m - 1) * g b
    have hq := pow_succ q (m - 1)
    rw [hpow] at hq
    calc
      _ = g (M j i) * g (M i i) ^ (m - 1) *
          ((g * toConv (h.comp a.hom.toAlgHom)) b * q ^ m) := by
        rw [hq]
        ring
      _ = _ := by rw [hweight R g h]
  · intro R g hg
    apply hdetect R g
    intro j hj
    have he (l : Index) : g (s l) = if l = i then 1 else 0 := by
      rw [hg]
      simp [s, Bialgebra.counit_mul, hM.counit, hb, Matrix.one_apply]
    have hpure : g (M i i) ^ m * g b = 1 := by
      have h := he i
      change g.ofConv (s i) = _ at h
      simp only [s, map_mul, map_pow, ite_true] at h
      rwa [← pow_succ', hpow] at h
    have hmixed : g (M j i) * g (M i i) ^ (m - 1) * g b = 0 := by
      have h := he j
      change g.ofConv (s j) = _ at h
      simpa [s, hj] using h
    calc
      g (M j i) = g (M j i) * (g (M i i) ^ m * g b) := by rw [hpure, mul_one]
      _ = (g (M j i) * g (M i i) ^ (m - 1) * g b) * g (M i i) := by
        have h := pow_succ (g (M i i)) (m - 1)
        rw [hpow] at h
        rw [h]
        ac_rfl
      _ = 0 := by rw [hmixed, zero_mul]

end MatrixColumn

open Coalgebra LinearAlgebraicGroups.RationalRepresentations in
/-- A normal closed subgroup of an affine algebraic group is the scheme kernel
of a representation over the original field. -/
theorem normalClosedSubgroupKernel : Specs.NormalClosedSubgroupKernel.{u} := by
  intro k _ G H hnormal
  classical
  obtain ⟨A, hA, ⟨eG⟩⟩ := groupPresentation G
  let : Algebra.FiniteType k A := hA
  let : IsAffine G.val.X.left := G.property.1
  let : IsClosedImmersion H.inclusion.hom.hom.left := H.isClosedImmersion
  obtain ⟨B', ⟨eH⟩⟩ := essImage_hopfSpec.mpr
    (isAffine_of_isAffineHom H.inclusion.hom.hom.left)
  let B := B'.unop
  let ff := hopfSpec.fullyFaithful (R := CommRingCat.of k)
  let a : A ⟶ B := (ff.preimage (eH.hom ≫ H.inclusion ≫ eG.inv)).unop
  have ha : specGroupMap a = eH.hom ≫ H.inclusion ≫ eG.inv := ff.map_preimage _
  have hcomm : specGroupMap a ≫ eG.hom = eH.hom ≫ H.inclusion := by
    rw [ha]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have haNormal : IsNormalSubgroup (specGroupMap a) :=
    normalSubgroup_of_iso eG eH hcomm hnormal
  let U := Grp.forget (SchemeOver k)
  let V := U ⋙ Over.forget (Spec (CommRingCat.of k))
  have hcomm' : (specGroupMap a).hom.hom ≫ eG.hom.hom.hom =
      eH.hom.hom.hom ≫ H.inclusion.hom.hom := congrArg U.map hcomm
  have haSurj : Function.Surjective a.hom := by
    apply (hopfMapClosedImmersion k a).mp
    rw [ha]
    have : IsIso eH.hom.hom.hom.left := V.map_isIso eH.hom
    have : IsIso eG.inv.hom.hom.left := V.map_isIso eG.inv
    change IsClosedImmersion (eH.hom.hom.hom.left ≫
      H.inclusion.hom.hom.left ≫ eG.inv.hom.hom.left)
    infer_instance
  obtain ⟨Index, _, _, i, L, e, f, hf⟩ := chevalleyLine k G H
  obtain ⟨E, _, hE⟩ := hopfSpecPoints k
  let eg := E A ≪≫ (groupPointsFunctor k).mapIso eG
  let eh := E B ≪≫ (groupPointsFunctor k).mapIso eH
  let α := eg.hom ≫ (groupPointsFunctor k).map f ≫ e.hom
  let M := pointMatrix A α
  have hM := pointMatrix_isCoactionMatrix A α
  have hpoint (R : TestAlgebra k) (g : WithConv (A →ₐ[k] R)) :
      (∀ j ≠ i, g (M j i) = 0) ↔
        ∃ h : B →ₐ[k] R, g = toConv (h.comp a.hom.toAlgHom) := by
    have hentry (j : Index) :
        ((α.app R g : Matrix.GeneralLinearGroup Index R).val j i) = g (M j i) :=
      congrArg (fun T : Matrix Index Index R ↦ T j i) (pointMatrix_evaluation A α R g)
    have hLift (h : B →ₐ[k] R) :
        (eg.hom.app R (toConv (h.comp a.hom.toAlgHom)) : Points G.val.X R) =
          (eh.hom.app R (toConv h) : Points H.group.X R) ≫ H.inclusion.hom.hom := by
      change ((E A).hom.app R (toConv (h.comp a.hom.toAlgHom)) :
        Points (specGroup A).X R) ≫ eG.hom.hom.hom =
        (((E B).hom.app R (toConv h) : Points (specGroup B).X R) ≫ eH.hom.hom.hom) ≫
          H.inclusion.hom.hom
      rw [hE a R (toConv h)]
      change (((E B).hom.app R (toConv h) : Points (specGroup B).X R) ≫
        (specGroupMap a).hom.hom) ≫ eG.hom.hom.hom = _
      rw [Category.assoc, Category.assoc, hcomm']
    simp_rw [← hentry]
    rw [← coordinateLine_iff]
    change StabilizesCoordinateLine
      (e.hom.app R (((groupPointsFunctor k).map f).app R (eg.hom.app R g))) i ↔ _
    rw [hf R]
    constructor
    · rintro ⟨h, hh⟩
      obtain ⟨v, rfl⟩ := (ConcreteCategory.bijective_of_isIso (eh.hom.app R)).2 h
      refine ⟨v.ofConv, (ConcreteCategory.bijective_of_isIso (eg.hom.app R)).1 ?_⟩
      exact hh.symm.trans (hLift v.ofConv).symm
    · rintro ⟨h, rfl⟩
      exact ⟨eh.hom.app R (toConv h), (hLift h).symm⟩
  have hcol : ∀ j ≠ i, a.hom (M j i) = 0 :=
    (hpoint (CommAlgCat.of k B) (toConv a.hom.toAlgHom)).mpr ⟨AlgHom.id k B, rfl⟩
  let c := a.hom (M i i)
  have hc := weight_of_column_isGroupLike a M hM i hcol
  have ht : a.hom.toAlgHom.toLinearMap.lTensor A (comul (M i i)) =
      M i i ⊗ₜ[k] c := by
    rw [hM.comul, map_sum]
    simp only [LinearMap.lTensor_tmul]
    rw [Finset.sum_eq_single i]
    · rfl
    · intro j _ hj
      rw [show a.hom.toAlgHom.toLinearMap (M j i) = 0 from hcol j hj, TensorProduct.tmul_zero]
    · simp
  have hnormalPoints := convolutionNormal_of_schemeNormal a haNormal
  obtain ⟨m, w, hm, hw, hleft⟩ :=
    exists_leftWeight a haSurj hnormalPoints c hc (M i i)
      (by rw [hM.counit, Matrix.one_apply_eq]) ht
  let b := HopfAlgebra.antipode k w
  have hb : counit (R := k) b = 1 := (HopfAlgebra.counit_antipode w).trans hw
  obtain ⟨L', f', hK⟩ := exists_schemeKernel_of_inverseWeight a M hM i hcol haSurj
    hnormalPoints (fun R g ↦ (hpoint R g).mp)
    m hm b hb (rightInverseWeight_of_leftWeight a c hc m w hleft)
  refine ⟨L', eG.inv ≫ f', hK.of_iso' (U.mapIso eH.symm) (U.mapIso eG.symm)
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_⟩
  · change eH.inv.hom.hom ≫ (specGroupMap a).hom.hom =
      H.inclusion.hom.hom ≫ eG.inv.hom.hom
    have h := congrArg U.map ha
    change (specGroupMap a).hom.hom = _ at h
    rw [h]
    change (U.mapIso eH).inv ≫ (U.mapIso eH).hom ≫ _ = _
    rw [Iso.inv_hom_id_assoc]
    rfl
  · exact (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
  · rfl
  · simp

private theorem schemeKernel_imageProjection {G L Q : GroupScheme k} {f : G ⟶ L}
    {q : G ⟶ Q} {i : Q ⟶ L} (hqi : q ≫ i = f)
    (hi : IsClosedImmersion i.hom.hom.left)
    {H : ClosedSubgroup G} (hH : IsSchemeKernel f H) :
    IsSchemeKernel q H := by
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have hcomp : q.hom.hom ≫ i.hom.hom = f.hom.hom :=
    congrArg (fun a : G ⟶ L ↦ a.hom.hom) hqi
  have he : η[Q.X] ≫ i.hom.hom = η[L.X] := IsMonHom.one_hom i.hom.hom
  refine ⟨⟨(cancel_mono i.hom.hom).mp ?_⟩, ?_⟩
  · rw [Category.assoc, Category.assoc, hcomp, he, hH.w]
  · constructor
    refine PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_
    · intro T
      have hw : T.fst ≫ f.hom.hom = T.snd ≫ η[L.X] := by
        rw [← hcomp, ← he, ← Category.assoc, T.condition, Category.assoc]
      exact hH.lift T.fst T.snd hw
    · intro T
      exact hH.lift_fst _ _ _
    · intro T
      exact hH.lift_snd _ _ _
    · intro T m hm₁ hm₂
      exact hH.hom_ext (hm₁.trans (hH.lift_fst _ _ _).symm)
        (hm₂.trans (hH.lift_snd _ _ _).symm)

/-- A homomorphism with the given scheme kernel supplies the affine right quotient. -/
theorem normalAffineQuotient : Specs.NormalAffineQuotient.{u} := by
  intro k _ G H hnormal
  obtain ⟨L, f, hH⟩ := normalClosedSubgroupKernel G H hnormal
  obtain ⟨Q, q, i, hqi, himage, _⟩ := schemeImageFactorization G L f
  exact ⟨L, f, Q, q, i, hH, schemeKernel_imageProjection hqi.1 hqi.2.2.2.2.2 hH,
    hqi, himage, quotientRepresentsImage hqi hH⟩

end

end LinearAlgebraicGroups
