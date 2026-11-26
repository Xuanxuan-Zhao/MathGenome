import Specs.LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus
import LinearAlgebraicGroups.Multiplicative.ExactInvariants
import LinearAlgebraicGroups.Affine.Stabilizers
import LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
import Batteries.Tactic.OpenPrivate
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.Functor (LaxMonoidal OplaxMonoidal)
open scoped TensorProduct CategoryTheory.MonObj CategoryTheory.Obj

universe u

namespace LinearAlgebraicGroups.DiagonalizableFixedLocus

open WeightDecomposition
open private quotientProjection factorsThrough_affineQuotient closedImmersion_over_affineSpec
  isFixedBy_groupIso whiskerLeft_pullback over_product_isPullback isFixedBy_comp
  from LinearAlgebraicGroups.Affine.FixedPointSchemes
open private weightProjection projection_of_mem projection_mem tensorCoefficients tensorCoefficients_tmul
  from LinearAlgebraicGroups.Multiplicative.WeightDecomposition

noncomputable section

variable {k M A : Type u} [Field k] [CommGroup M] [CommRing A] [Algebra k A]

local notation "B" => MonoidAlgebra k M
local notation "χ" => MonoidAlgebra.of k M

variable (ρ : CoordinateCoaction (k := k) (M := M) (A := A))

private theorem weight_induction (motive : A → Prop) {x : A}
    (homogeneous : ∀ m, ∀ b ∈ weightSpace ρ.toRightComodule m, motive b)
    (zero : motive 0) (add : ∀ b c, motive b → motive c → motive (b + c)) : motive x := by
  classical
  have h := (weightDecomposition ρ.toRightComodule).submodule_iSup_eq_top
  exact Submodule.iSup_induction (motive := motive) (weightSpace ρ.toRightComodule)
    (h ▸ Submodule.mem_top (R := k) (M := A) (x := x)) homogeneous zero add

private theorem hom_of_weight {m : M} {x : A} (hx : x ∈ weightSpace ρ.toRightComodule m) :
    ρ.hom x = x ⊗ₜ[k] χ m := by
  simpa only [ρ.coaction_eq, AlgHom.toLinearMap_apply] using mem_weightSpace.mp hx

private theorem weight_mul {m n : M} {x y : A}
    (hx : x ∈ weightSpace ρ.toRightComodule m) (hy : y ∈ weightSpace ρ.toRightComodule n) :
    x * y ∈ weightSpace ρ.toRightComodule (m * n) := by
  apply mem_weightSpace.mpr
  simp only [ρ.coaction_eq, AlgHom.toLinearMap_apply, map_mul, hom_of_weight ρ hx,
    hom_of_weight ρ hy, Algebra.TensorProduct.tmul_mul_tmul]

private theorem weight_algebraMap (c : k) :
    algebraMap k A c ∈ weightSpace ρ.toRightComodule 1 := by
  apply mem_weightSpace.mpr
  rw [ρ.coaction_eq, AlgHom.toLinearMap_apply, AlgHom.commutes, map_one,
    Algebra.TensorProduct.algebraMap_apply]

private theorem coaction_linear_trivial_iff {V : Type u} [AddCommGroup V] [Module k V]
    (f : A →ₗ[k] V) :
    (∀ a, f.rTensor B (ρ.hom a) = f a ⊗ₜ[k] (1 : B)) ↔
      ∀ m ≠ 1, ∀ a ∈ weightSpace ρ.toRightComodule m, f a = 0 := by
  classical
  constructor
  · intro h m hm a ha
    specialize h a
    rw [hom_of_weight ρ ha, LinearMap.rTensor_tmul, ← map_one (MonoidAlgebra.of k M)] at h
    have he := congrArg (fun t ↦ tensorCoefficients t m) h
    simpa only [tensorCoefficients_tmul, Finsupp.single_apply, ite_true,
      Ne.symm hm, ite_false] using he
  · intro h a
    refine weight_induction ρ (fun a ↦ f.rTensor B (ρ.hom a) = f a ⊗ₜ[k] (1 : B))
      ?_ (by simp) ?_
    · intro m b hb
      rw [hom_of_weight ρ hb, LinearMap.rTensor_tmul]
      by_cases hm : m = 1
      · rw [hm, map_one]
      · simp [h m hm b hb]
    · intro b c hb hc
      simp only [map_add, TensorProduct.add_tmul, hb, hc]

theorem fixedAlgebraPoints : Specs.DiagonalizableFixedLocus.FixedAlgebraPoints.{u} := by
  intro k M A R _ _ _ _ _ _ ρ x
  change (∀ a, x.toLinearMap.rTensor (MonoidAlgebra k M) (ρ.hom a) =
    x.toLinearMap a ⊗ₜ[k] (1 : MonoidAlgebra k M)) ↔ _
  rw [coaction_linear_trivial_iff ρ x.toLinearMap, fixedIdeal, Ideal.span_le]
  constructor
  · rintro h a ⟨m, hm, ha⟩
    exact h m hm a ha
  · intro h m hm a ha
    exact h ⟨m, hm, ha⟩

private theorem lift_with_zero_nontrivial_weights {R : Type u} [CommRing R] [Algebra k R]
    [Algebra.FormallySmooth k A] (I : Ideal R) (hI : I ^ 2 = ⊥)
    (f : (A ⧸ fixedIdeal ρ) →ₐ[k] (R ⧸ I)) :
    ∃ g : A →ₐ[k] R, (Ideal.Quotient.mkₐ k I).comp g =
        f.comp (Ideal.Quotient.mkₐ k (fixedIdeal ρ)) ∧ fixedIdeal ρ ≤ RingHom.ker g := by
  classical
  let q := Ideal.Quotient.mkₐ k (fixedIdeal ρ)
  let π := Ideal.Quotient.mkₐ k I
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.iff_comp_surjective.mp
    (inferInstance : Algebra.FormallySmooth k A) I hI (f.comp q)
  let p := weightProjection ρ.toRightComodule 1
  have proj {m : M} {x : A} (hx : x ∈ weightSpace ρ.toRightComodule m) :
      p x = if m = 1 then x else 0 := projection_of_mem hx 1
  have killed {m : M} {x : A} (hm : m ≠ 1) (hx : x ∈ weightSpace ρ.toRightComodule m) :
      g x ∈ I := by
    have hx' : x ∈ fixedIdeal ρ := Ideal.subset_span ⟨m, hm, hx⟩
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change π (g x) = 0
    rw [← AlgHom.comp_apply, hg, AlgHom.comp_apply]
    change f (Ideal.Quotient.mk (fixedIdeal ρ) x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx', map_zero]
  let L := g.toLinearMap.comp p
  have mul_homogeneous (m n : M) (x y : A) (hx : x ∈ weightSpace ρ.toRightComodule m)
      (hy : y ∈ weightSpace ρ.toRightComodule n) : L (x * y) = L x * L y := by
    change g (p (x * y)) = g (p x) * g (p y)
    rw [proj (weight_mul ρ hx hy), proj hx, proj hy]
    by_cases hm : m = 1
    · subst m
      by_cases hn : n = 1 <;> simp [hn]
    · by_cases hn : n = 1
      · subst n
        simp [hm]
      · have hxy : g x * g y = 0 := by
          have hmem := Ideal.mul_mem_mul (killed hm hx) (killed hn hy)
          simpa [← pow_two, hI] using hmem
        by_cases hmn : m * n = 1 <;> simp [hm, hn, hmn, hxy]
  have mul (x y : A) : L (x * y) = L x * L y := by
    refine weight_induction ρ (fun x ↦ ∀ y, L (x * y) = L x * L y) ?_ ?_ ?_ y
    · intro m b hb y
      refine weight_induction ρ (fun y ↦ L (b * y) = L b * L y) ?_ (by simp) ?_
      · exact fun n c hc ↦ mul_homogeneous m n b c hb hc
      · intro c d hc hd
        rw [mul_add, map_add, hc, hd, map_add, mul_add]
    · simp
    · intro b c hb hc y
      rw [add_mul, map_add, hb, hc, map_add, add_mul]
  have scalar (c : k) : L (algebraMap k A c) = algebraMap k R c := by
    change g (p (algebraMap k A c)) = _
    rw [proj (weight_algebraMap ρ c), ite_eq_left rfl, g.commutes]
  let g' : A →ₐ[k] R :=
    { toFun := L
      map_zero' := map_zero L
      map_add' := map_add L
      map_one' := by simpa using scalar 1
      map_mul' := mul
      commutes' := scalar }
  refine ⟨g', ?_, ?_⟩
  · ext x
    change π (L x) = f (q x)
    refine weight_induction ρ (fun x ↦ π (L x) = f (q x)) ?_ (by simp) ?_
    · intro m b hb
      change π (g (p b)) = _
      rw [proj hb]
      by_cases hm : m = 1
      · rw [ite_eq_left hm]
        exact DFunLike.congr_fun hg b
      · have hb' : b ∈ fixedIdeal ρ := Ideal.subset_span ⟨m, hm, hb⟩
        have h : q b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hb'
        simp [hm, h]
    · intro b c hb hc
      simp only [map_add, hb, hc]
  · rw [fixedIdeal, Ideal.span_le]
    rintro b ⟨m, hm, hb⟩
    change g (p b) = 0
    simp [proj hb, hm]

theorem fixedAlgebraSmooth : Specs.DiagonalizableFixedLocus.FixedAlgebraSmooth.{u} := by
  intro k M A _ _ _ _ _ ρ
  have : Algebra.FiniteType k (A ⧸ fixedIdeal ρ) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k (fixedIdeal ρ))
      (Ideal.Quotient.mkₐ_surjective k _)
  constructor
  · exact Algebra.FormallySmooth.iff_comp_surjective.mpr (by
      intro R _ _ I hI f
      obtain ⟨g, hg, hker⟩ := lift_with_zero_nontrivial_weights ρ I hI f
      refine ⟨Ideal.Quotient.liftₐ _ g (fun a ha ↦ hker ha), ?_⟩
      ext z
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact DFunLike.congr_fun hg a)
  · exact Algebra.FinitePresentation.of_finiteType.mp inferInstance

set_option maxHeartbeats 800000 in
theorem affineFixedTangentLinear : Specs.DiagonalizableFixedLocus.AffineFixedTangentLinear.{u} := by
  intro k M A K _ _ _ _ _ _ ρ z
  let I := fixedIdeal ρ
  let q := Ideal.Quotient.mkₐ k I
  let x := z.comp q
  change (_ ∧ ∃ e : coordinateTangent z ≃ₗ[K] invariantCoordinateTangent ρ x, _)
  constructor
  · intro d
    rw [coaction_linear_trivial_iff ρ d.val]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨d.property, h⟩⟩
  have hqx (a : A) (ha : a ∈ I) : x a = 0 := by
    change z (Ideal.Quotient.mk I a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  have dfact (d : invariantCoordinateTangent ρ x) :
      I.restrictScalars k ≤ LinearMap.ker d.val := by
    intro a ha
    change d.val a = 0
    change a ∈ Submodule.span A {a | ∃ m : M, m ≠ 1 ∧ a ∈ weightSpace ρ.toRightComodule m} at ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
        obtain ⟨m, hm, ha⟩ := ha
        exact d.property.2 m hm a ha
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | smul b a ha hd =>
        change d.val (b * a) = 0
        rw [d.property.1 b a, hd, hqx a ha, mul_zero, mul_zero, add_zero]
  let F : coordinateTangent z →ₗ[K] invariantCoordinateTangent ρ x :=
    { toFun := fun d ↦ ⟨d.val.comp q.toLinearMap, by
        refine ⟨?_, ?_⟩
        · intro a b
          change d.val (q (a * b)) = x a * d.val (q b) + d.val (q a) * x b
          rw [map_mul]
          exact d.property (q a) (q b)
        · intro m hm a ha
          have h : a ∈ I := Ideal.subset_span ⟨m, hm, ha⟩
          change d.val (Ideal.Quotient.mk I a) = 0
          rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]⟩
      map_add' := by intros; ext; rfl
      map_smul' := by intros; ext; rfl }
  refine ⟨LinearEquiv.ofBijective F ⟨?_, ?_⟩, fun d a ↦ rfl⟩
  · intro d d' h
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mkₐ_surjective k I a
    exact congrArg (fun t : invariantCoordinateTangent ρ x ↦ t.val b) h
  · intro d
    let l : (A ⧸ I) →ₗ[k] K := (I.restrictScalars k).liftQ d.val (dfact d)
    have hl (a : A) : l (q a) = d.val a := rfl
    have hd : l ∈ coordinateTangent z := by
      intro a b
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective k I a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mkₐ_surjective k I b
      rw [← map_mul, hl, hl, hl]
      exact d.property.1 a b
    exact ⟨⟨l, hd⟩, Subtype.ext (LinearMap.ext hl)⟩

theorem coordinateTangentDualNumbers :
    Specs.DiagonalizableFixedLocus.CoordinateTangentDualNumbers.{u} := by
  classical
  intro k A K _ _ _ _ _ x
  let F (d : coordinateTangent x) :
      {f : A →ₐ[k] DualNumber K // (TrivSqZeroExt.fstHom k K K).comp f = x} := by
    have one : d.val 1 = 0 := by
      have h := d.property 1 1
      simp only [mul_one, map_one, one_mul] at h
      exact (add_right_inj (a := d.val 1)).mp (h.symm.trans (add_zero (d.val 1)).symm)
    have scalar (r : k) : d.val (algebraMap k A r) = 0 := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, one, smul_zero]
    let f : A →ₐ[k] DualNumber K :=
      { toFun := fun a ↦ ⟨x a, d.val a⟩
        map_zero' := by apply TrivSqZeroExt.ext <;> simp
        map_one' := by apply TrivSqZeroExt.ext <;> simp [one]
        map_add' := fun a b ↦ TrivSqZeroExt.ext (map_add x a b) (map_add d.val a b)
        map_mul' := fun a b ↦ TrivSqZeroExt.ext (map_mul x a b) (d.property a b)
        commutes' := fun r ↦ TrivSqZeroExt.ext (x.commutes r) (scalar r) }
    exact ⟨f, AlgHom.ext fun _ ↦ rfl⟩
  refine ⟨Equiv.ofBijective F ⟨?_, ?_⟩, fun _ _ ↦ rfl⟩
  · intro d e h
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    exact congrArg (fun f ↦ TrivSqZeroExt.snd (f.val a)) h
  · intro f
    let d : A →ₗ[k] K := ((TrivSqZeroExt.sndHom K K).restrictScalars k).comp f.val.toLinearMap
    have hfst (a : A) : TrivSqZeroExt.fst (f.val a) = x a := DFunLike.congr_fun f.property a
    have hd : d ∈ coordinateTangent x := by
      intro a b
      change TrivSqZeroExt.snd (f.val (a * b)) =
        x a * TrivSqZeroExt.snd (f.val b) + TrivSqZeroExt.snd (f.val a) * x b
      rw [map_mul, DualNumber.snd_mul, hfst, hfst]
    exact ⟨⟨d, hd⟩, Subtype.ext (AlgHom.ext fun a ↦ TrivSqZeroExt.ext (hfst a).symm rfl)⟩

theorem fixedTangentDirections : Specs.DiagonalizableFixedLocus.FixedTangentDirections.{u} := by
  classical
  intro k K _ _ _ H X Z a i hi hfix z
  let : IsClosedImmersion i.left := hi
  let : Mono i := Over.mono_of_mono_left i
  let F : TangentDirections Z z → {v : TangentDirections X (z ≫ i) // IsFixedBy a v.val} :=
    fun v ↦ ⟨⟨v.val ≫ i, by
      simpa only [mapPoints, Category.assoc] using congrArg (· ≫ i) v.property⟩,
      (hfix _ (v.val ≫ i)).mpr ⟨v.val, rfl⟩⟩
  have hF : Function.Bijective F := by
    constructor
    · intro v w h
      apply Subtype.ext
      exact (cancel_mono i).mp (congrArg (fun t ↦ t.val.val) h)
    · intro v
      obtain ⟨w, hw⟩ := (hfix _ v.val.val).mp v.property
      refine ⟨⟨w, (cancel_mono i).mp ?_⟩, ?_⟩
      · simpa [mapPoints, Category.assoc, hw] using v.val.property
      · exact Subtype.ext (Subtype.ext hw)
  exact ⟨Equiv.ofBijective F hF, fun _ ↦ rfl⟩

local instance testSpecBraided (k : Type u) [Field k] : (testSpec k).Braided :=
  braidedAlgSpec (R := CommRingCat.of k)

local instance testSpecMonObj (k : Type u) [Field k] (G : (TestAlgebra k)ᵒᵖ) [MonObj G] :
    MonObj ((testSpec k).obj G) :=
  Functor.monObjObj (F := testSpec k) G

section Transport

/-- Reflect an action along a fully faithful strong monoidal functor. -/
private abbrev reflectAction {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal]
    (hF : F.FullyFaithful) (M Y : C) [MonObj M]
    (a : ModObj (F.obj M) (F.obj Y)) : ModObj M Y where
  smul := hF.preimage (OplaxMonoidal.δ F M Y ≫ a.smul)
  one_smul := by
    change η[M] ▷ Y ≫ _ = (λ_ Y).hom
    apply hF.map_injective
    apply (cancel_epi (LaxMonoidal.μ F (𝟙_ C) Y)).mp
    apply (cancel_epi (LaxMonoidal.ε F ▷ F.obj Y)).mp
    simp only [F.map_comp, hF.map_preimage,
      ← LaxMonoidal.μ_natural_left_assoc, Functor.Monoidal.μ_δ_assoc,
      ← comp_whiskerRight_assoc, ← LaxMonoidal.left_unitality]
    exact a.one_smul
  mul_smul := by
    change μ[M] ▷ Y ≫ _ = (α_ M M Y).hom ≫ M ◁ _ ≫ _
    apply hF.map_injective
    apply (cancel_epi (LaxMonoidal.μ F (M ⊗ M) Y)).mp
    apply (cancel_epi (LaxMonoidal.μ F M M ▷ F.obj Y)).mp
    simp only [F.map_comp, hF.map_preimage]
    rw [← LaxMonoidal.μ_natural_left_assoc, Functor.Monoidal.μ_δ_assoc,
      ← comp_whiskerRight_assoc, LaxMonoidal.associativity_assoc,
      ← LaxMonoidal.μ_natural_right_assoc, hF.map_preimage]
    simp only [← whiskerLeft_comp_assoc, Functor.Monoidal.μ_δ_assoc]
    exact a.mul_smul

variable (k A) in
private abbrev AlgSpecObj := (testSpec k).obj (op (CommAlgCat.of k A))

private abbrev diagonalSource := op (CommAlgCat.of k B)

private def coordinateCoaction
    (a : ModObj (diagonalSource (k := k) (M := M)) (op (CommAlgCat.of k A))) :
    CoordinateCoaction (k := k) (M := M) (A := A) := by
  let l : A →ₐ[k] B ⊗[k] A := a.smul.unop.hom
  let r : A →ₐ[k] A ⊗[k] B := (Algebra.TensorProduct.comm k B A).toAlgHom.comp l
  let Δ := Coalgebra.comul (R := k) (A := B)
  let ε := Coalgebra.counit (R := k) (A := B)
  have hl (x : A) : Δ.rTensor A (l x) =
      (TensorProduct.assoc k B B A).symm (l.toLinearMap.lTensor B (l x)) := by
    have h := congrArg (fun f ↦ f.unop.hom x) a.mul_smul
    change (Algebra.TensorProduct.map (Bialgebra.comulAlgHom k B) (AlgHom.id k A)) (l x) =
      (Algebra.TensorProduct.assoc k k k B B A).symm
        ((Algebra.TensorProduct.map (AlgHom.id k B) l) (l x)) at h
    exact h
  have he (x : A) : TensorProduct.lid k A (ε.rTensor A (l x)) = x := by
    have h := congrArg (fun f ↦ f.unop.hom x) a.one_smul
    change (Algebra.TensorProduct.map (Bialgebra.counitAlgHom k B) (AlgHom.id k A)) (l x) =
      (Algebra.TensorProduct.lid k A).symm x at h
    exact (LinearEquiv.eq_symm_apply (TensorProduct.lid k A)).mp h
  refine ⟨r, ⟨r.toLinearMap, ?_, ?_⟩, rfl⟩
  · intro x
    let rev : (B ⊗[k] B) ⊗[k] A →ₗ[k] A ⊗[k] (B ⊗[k] B) :=
      (TensorProduct.comm k B B).toLinearMap.lTensor A ∘ₗ
        (TensorProduct.comm k (B ⊗[k] B) A).toLinearMap
    have lhs (t : B ⊗[k] A) :
        TensorProduct.assoc k A B B (r.toLinearMap.rTensor B (TensorProduct.comm k B A t)) =
        rev ((TensorProduct.assoc k B B A).symm (l.toLinearMap.lTensor B t)) := by
      induction t using TensorProduct.inductionOn with
      | add x y hx hy => simp [hx, hy]
      | tmul b a =>
        simp only [TensorProduct.comm_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
          LinearMap.lTensor_tmul, rev, LinearMap.comp_apply, LinearEquiv.coe_coe, r,
          AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
        generalize l a = t
        induction t using TensorProduct.inductionOn with
        | add x y hx hy => simp [TensorProduct.add_tmul, TensorProduct.tmul_add, hx, hy]
        | tmul c d => rfl
    have rhs (t : B ⊗[k] A) :
        rev (Δ.rTensor A t) = Δ.lTensor A (TensorProduct.comm k B A t) := by
      induction t using TensorProduct.inductionOn with
      | add x y hx hy => simp [hx, hy]
      | tmul b a => simp [rev, Δ, Coalgebra.comm_comul]
    change TensorProduct.assoc k A B B (r.toLinearMap.rTensor B (TensorProduct.comm k B A (l x))) =
      Δ.lTensor A (TensorProduct.comm k B A (l x))
    rw [lhs, ← hl, rhs]
  · intro x
    have h (t : B ⊗[k] A) : TensorProduct.rid k A (ε.lTensor A (TensorProduct.comm k B A t)) =
        TensorProduct.lid k A (ε.rTensor A t) := by
      induction t using TensorProduct.inductionOn with
      | add x y hx hy => simp [hx, hy]
      | tmul b a => simp
    exact (h (l x)).trans (he x)

set_option maxHeartbeats 800000 in
private theorem reflectAction_fixed {k : Type u} [Field k]
    (G Y T : (TestAlgebra k)ᵒᵖ) [MonObj G]
    (a : ModObj ((testSpec k).obj G) ((testSpec k).obj Y)) (x : T ⟶ Y) :
    IsFixedBy a.smul ((testSpec k).map x) ↔
      (G ◁ x) ≫ (reflectAction (testSpec k)
        (algSpec.fullyFaithful (R := CommRingCat.of k)) G Y a).smul = snd G T ≫ x := by
  let F := testSpec k
  let : F.Braided := testSpecBraided k
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  unfold IsFixedBy
  rw [← cancel_epi (OplaxMonoidal.δ F G T), OplaxMonoidal.δ_natural_right_assoc]
  have h := CartesianMonoidalCategory.prodComparison_snd F G T
  rw [← OplaxMonoidal.δ_of_cartesianMonoidalCategory] at h
  rw [← Category.assoc (OplaxMonoidal.δ F G T), h, ← F.map_comp]
  let b := ff.preimage (OplaxMonoidal.δ F G Y ≫ a.smul)
  have hb : F.map b = OplaxMonoidal.δ F G Y ≫ a.smul := ff.map_preimage _
  change (F.map (G ◁ x) ≫ _) = _ ↔ (G ◁ x) ≫ b = _
  rw [← hb, ← F.map_comp]
  exact ⟨fun h ↦ ff.map_injective h, fun h ↦ congrArg F.map h⟩

set_option backward.isDefEq.respectTransparency false in
private theorem affine_fixed_criterion {R : Type u} [CommRing R] [Algebra k R]
    (a : ModObj (AlgSpecObj k B) (AlgSpecObj k A)) (x : A →ₐ[k] R) :
    let ρ := coordinateCoaction (reflectAction (testSpec k)
      (algSpec.fullyFaithful (R := CommRingCat.of k))
      (diagonalSource (k := k) (M := M)) (op (CommAlgCat.of k A)) a)
    IsFixedBy a.smul ((testSpec k).map (CommAlgCat.ofHom x).op) ↔ fixedIdeal ρ ≤ RingHom.ker x := by
  dsimp
  let G := diagonalSource (k := k) (M := M)
  let Y := op (CommAlgCat.of k A)
  let a' := reflectAction (testSpec k) (algSpec.fullyFaithful (R := CommRingCat.of k)) G Y a
  rw [reflectAction_fixed G Y _ a (CommAlgCat.ofHom x).op,
    ← fixedAlgebraPoints (coordinateCoaction a') x]
  let l : A →ₐ[k] B ⊗[k] A := a'.smul.unop.hom
  have h (t : B ⊗[k] A) :
      x.toLinearMap.rTensor B (TensorProduct.comm k B A t) =
        TensorProduct.comm k B R ((Algebra.TensorProduct.map (AlgHom.id k B) x) t) := by
    induction t using TensorProduct.inductionOn with
    | tmul b a => rfl
    | add p q hp hq => simp [hp, hq]
  constructor
  · intro he z
    have hz := congrArg (fun f ↦ f.unop.hom z) he
    change (Algebra.TensorProduct.map (AlgHom.id k B) x) (l z) =
      (1 : B) ⊗ₜ[k] x z at hz
    change x.toLinearMap.rTensor B (TensorProduct.comm k B A (l z)) = _
    rw [h, hz, TensorProduct.comm_tmul]
  · intro hz
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    ext z
    change (Algebra.TensorProduct.map (AlgHom.id k B) x) (l z) =
      (1 : B) ⊗ₜ[k] x z
    apply (TensorProduct.comm k B R).injective
    rw [← h, TensorProduct.comm_tmul]
    exact hz z

set_option backward.isDefEq.respectTransparency false in
theorem affineActionTangentInvariants : Specs.DiagonalizableFixedLocus.AffineActionTangentInvariants.{u} := by
  intro k M A K _ _ _ _ _ _ _ a
  let F := testSpec k
  let G := diagonalSource (k := k) (M := M)
  let X := op (CommAlgCat.of k A)
  let a' := reflectAction F (algSpec.fullyFaithful (R := CommRingCat.of k)) G X a
  let ρ := coordinateCoaction a'
  refine ⟨ρ, ?_, ?_⟩
  · unfold affineActionCoactionHom
    change (Algebra.TensorProduct.comm k (MonoidAlgebra k M) A).toAlgHom.comp
      ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
        (OplaxMonoidal.δ F G X ≫ a.smul)).unop.hom = _
    rw [OplaxMonoidal.δ_of_cartesianMonoidalCategory]
  · intro x hx
    obtain ⟨e, he⟩ := coordinateTangentDualNumbers x
    refine ⟨e, he, fun d ↦ ?_⟩
    have hx' : fixedIdeal ρ ≤ RingHom.ker x := (affine_fixed_criterion a x).mp hx
    change d.val ∈ invariantCoordinateTangent ρ x ↔
      IsFixedBy a.smul (F.map (CommAlgCat.ofHom (e d).val).op)
    have hfixed : IsFixedBy a.smul (F.map (CommAlgCat.ofHom (e d).val).op) ↔
        fixedIdeal ρ ≤ RingHom.ker (e d).val := affine_fixed_criterion a (e d).val
    rw [hfixed, fixedIdeal, Ideal.span_le]
    constructor
    · intro hd b hb
      obtain ⟨m, hm, hmb⟩ := hb
      have hzero : x b = 0 := hx' (Ideal.subset_span ⟨m, hm, hmb⟩)
      change (e d).val b = 0
      apply TrivSqZeroExt.ext
      · exact (DFunLike.congr_fun (e d).property b).trans hzero
      · exact (he d b).trans (hd.2 m hm b hmb)
    · intro h
      refine ⟨d.property, fun m hm b hmb ↦ ?_⟩
      have hz : (e d).val b = 0 := h ⟨m, hm, hmb⟩
      rw [← he d b, hz]
      rfl

private theorem smooth_spec_iff : Smooth (AlgSpecObj k A).hom ↔ Algebra.Smooth k A := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k A))) ↔ _
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap

set_option backward.isDefEq.respectTransparency false in
private theorem smooth_fixed_on_spec [Algebra.Smooth k A]
    (a : ModObj (AlgSpecObj k B) (AlgSpecObj k A)) {Z : SchemeOver k} (i : Z ⟶ AlgSpecObj k A)
    (hi : IsClosedImmersion i.left) (hrep : RepresentsFixedPoints a.smul i) : Smooth Z.hom := by
  let F := testSpec k
  let : F.Braided := testSpecBraided k
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let a' := reflectAction F ff (diagonalSource (k := k) (M := M)) (op (CommAlgCat.of k A)) a
  let ρ := coordinateCoaction a'
  let I := fixedIdeal ρ
  let q := F.map (quotientProjection (A := CommAlgCat.of k A) I).op
  have hq : IsClosedImmersion q.left :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hfactor (C : TestAlgebra k) (x : F.obj (op C) ⟶ AlgSpecObj k A) :
      IsFixedBy a.smul x ↔ ∃ y, y ≫ q = x := by
    let x' := (ff.preimage x).unop.hom
    have hx : F.map (CommAlgCat.ofHom x').op = x := ff.map_preimage x
    have hc : IsFixedBy a.smul (F.map (CommAlgCat.ofHom x').op) ↔ I ≤ RingHom.ker x' :=
      affine_fixed_criterion (M := M) a x'
    rw [← hx, hc, factorsThrough_affineQuotient, ff.preimage_map]
    rfl
  obtain ⟨u, hu⟩ := (hrep _ q).mp ((hfactor _ q).mpr ⟨𝟙 _, Category.id_comp _⟩)
  obtain ⟨J, e, he⟩ := closedImmersion_over_affineSpec i hi
  obtain ⟨v, hv⟩ := (hfactor _ (e.inv ≫ i)).mp ((hrep _ _).mpr ⟨e.inv, rfl⟩)
  let w := e.hom ≫ v
  have hw : w ≫ q = i := by simp [w, hv]
  let : IsClosedImmersion i.left := hi
  let : IsClosedImmersion q.left := hq
  let : Mono i := Over.mono_of_mono_left i
  let : Mono q := Over.mono_of_mono_left q
  let e' : Z ≅ AlgSpecObj k (A ⧸ I) :=
    { hom := w
      inv := u
      hom_inv_id := (cancel_mono i).mp (by simp [hu, hw])
      inv_hom_id := (cancel_mono q).mp (by simp [hw, hu]) }
  have h := (smooth_spec_iff (k := k) (A := A ⧸ I)).mpr (fixedAlgebraSmooth ρ)
  rw [← Over.w e'.hom]
  let : Smooth (AlgSpecObj k (A ⧸ I)).hom := h
  let e'' := (Over.forget (Spec (CommRingCat.of k))).mapIso e'
  let : IsIso e'.hom.left := inferInstanceAs (IsIso e''.hom)
  infer_instance

end Transport

set_option backward.isDefEq.respectTransparency false in
theorem affineFixedLocusSmooth : Specs.DiagonalizableFixedLocus.AffineFixedLocusSmooth.{u} := by
  intro k M _ _ _ X hX hSm a Z i hi hrep
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr hX
  let H := (Specs.DiagonalizableGroups.diagonalGroup k M).val.X
  let : ModObj H X := a
  let : IsMonHom (Iso.refl H).hom := by change IsMonHom (𝟙 H); infer_instance
  let a' : ModObj H ((testSpec k).obj A) := ModObj.ofIso (Iso.refl H) e.symm
  let i' := i ≫ e.inv
  have hi' : IsClosedImmersion i'.left := by
    let : IsClosedImmersion i.left := hi
    exact IsClosedImmersion.comp i.left e.inv.left
  have hrep' : RepresentsFixedPoints a'.smul i' := by
    intro T t
    have eq : IsFixedBy a'.smul t ↔ IsFixedBy a.smul (t ≫ e.hom) := by
      unfold IsFixedBy
      rw [← cancel_mono e.hom]
      change ((H ◁ t) ≫ (𝟙 H ⊗ₘ e.hom) ≫ a.smul ≫ e.inv) ≫ e.hom = _ ↔ _
      simp [whiskerLeft_comp, H]
    rw [eq, hrep]
    exact exists_congr fun f ↦ by
      change f ≫ i = t ≫ e.hom ↔ f ≫ i ≫ e.inv = t
      rw [← cancel_mono e.hom]
      simp
  have hSm' : Smooth ((testSpec k).obj A).hom := by
    change Smooth ((algSpec (CommRingCat.of k)).obj A).hom
    rw [← Over.w e.hom]
    let : Smooth X.hom := hSm
    have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
    infer_instance
  let : Algebra.Smooth k A.unop := smooth_spec_iff.mp hSm'
  exact smooth_fixed_on_spec (M := M) a' i' hi' hrep'


set_option backward.isDefEq.respectTransparency false in
theorem fixedLocusSmoothOnInvariantCharts :
    Specs.DiagonalizableFixedLocus.FixedLocusSmoothOnInvariantCharts.{u} := by
  classical
  intro k M _ _ _ X hX a Z i hi hrep hcharts
  let D := (Specs.DiagonalizableGroups.diagonalGroup k M).val.X
  let U (z : Z.left) := (hcharts z).choose
  let j (z : Z.left) : U z ⟶ X := (hcharts z).choose_spec.choose
  have chart (z : Z.left) := (hcharts z).choose_spec.choose_spec
  let Y (z : Z.left) := pullback i (j z)
  let p (z : Z.left) : Y z ⟶ Z := pullback.fst i (j z)
  let q (z : Z.left) : Y z ⟶ U z := pullback.snd i (j z)
  have sq (z : Z.left) : IsPullback (p z).left (q z).left i.left (j z).left :=
    (IsPullback.of_hasPullback i (j z)).map (Over.forget _)
  have hp (z : Z.left) : IsOpenImmersion (p z).left :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (sq z).flip (chart z).2.1
  have cover (z : Z.left) : ∃ t : (Y z).left, (p z).left t = z := by
    let : IsOpenImmersion (j z).left := (chart z).2.1
    have hz : z ∈ Set.range (pullback.fst i.left (j z).left) := by
      rw [IsOpenImmersion.range_pullbackFst]
      exact (chart z).2.2.1
    obtain ⟨v, hv⟩ := hz
    have hs : Surjective (sq z).isoPullback.hom := inferInstance
    obtain ⟨w, hw⟩ := hs.surj v
    refine ⟨w, ?_⟩
    rw [← IsPullback.isoPullback_hom_fst (sq z), Scheme.Hom.comp_apply, hw, hv]
  let oc : Z.left.OpenCover := Scheme.Cover.mkOfCovers _
    (fun z ↦ (Y z).left) (fun z ↦ (p z).left) (fun z ↦ ⟨z, cover z⟩) hp
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth) oc).mpr
  intro z
  obtain ⟨haff, hop, _, b, hb⟩ := chart z
  have hq : IsClosedImmersion (q z).left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (sq z) hi
  have hU : Smooth (U z).hom := by
    rw [← Over.w (j z)]
    let : Smooth X.hom := hX
    let : IsOpenImmersion (j z).left := hop
    infer_instance
  have hqrep : RepresentsFixedPoints b.smul (q z) := by
    intro T t
    let : IsOpenImmersion (j z).left := hop
    let : Mono (j z) := Over.mono_of_mono_left _
    have he : IsFixedBy b.smul t ↔ IsFixedBy a.smul (t ≫ j z) := by
      unfold IsFixedBy
      rw [← cancel_mono (j z), Category.assoc, hb, whiskerLeft_comp, Category.assoc, Category.assoc]
    rw [he, hrep]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨pullback.lift y t hy, pullback.lift_snd _ _ _⟩
    · rintro ⟨y, hy⟩
      refine ⟨y ≫ p z, ?_⟩
      rw [Category.assoc, pullback.condition, ← Category.assoc, hy]
  change Smooth ((p z).left ≫ Z.hom)
  rw [Over.w (p z)]
  let : IsAffine (U z).left := haff
  let : Smooth (U z).hom := hU
  exact affineFixedLocusSmooth (U z) b (Y z) (q z) hq hqrep

theorem existsWeightBasis : Specs.DiagonalizableFixedLocus.ExistsWeightBasis.{u} := by
  classical
  intro k M V _ _ _ _ _ ρ
  let b (m : M) := Module.Free.chooseBasis k (weightSpace ρ m)
  let h := weightDecomposition ρ
  let c := h.collectedBasis b
  exact ⟨_, Module.Finite.finite_basis c, c, Sigma.fst, h.collectedBasis_mem b⟩

private abbrev restrictAction {H U X : SchemeOver k} [MonObj H]
    (a : ModObj H X) (j : U ⟶ X) [Mono j] (b : H ⊗ U ⟶ U)
    (hb : b ≫ j = (H ◁ j) ≫ a.smul) : ModObj H U where
  smul := b
  one_smul := by
    change η[H] ▷ U ≫ b = (λ_ U).hom
    apply (cancel_mono j).mp
    have h : η[H] ▷ X ≫ a.smul = (λ_ X).hom := a.one_smul
    rw [Category.assoc, hb, ← whisker_exchange_assoc, h]
    simp
  mul_smul := by
    change μ[H] ▷ U ≫ b = (α_ H H U).hom ≫ H ◁ b ≫ b
    apply (cancel_mono j).mp
    have h : μ[H] ▷ X ≫ a.smul = (α_ H H X).hom ≫ H ◁ a.smul ≫ a.smul :=
      a.mul_smul
    simp only [Category.assoc, hb]
    rw [← whisker_exchange_assoc, h, associator_naturality_right_assoc]
    simp only [← whiskerLeft_comp_assoc, hb]

private theorem exists_field_point (Y : SchemeOver k) (z : Y.left) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (p : Points Y (CommAlgCat.of k K)),
      p.left (IsLocalRing.closedPoint K) = z := by
  let R := Y.left.residueField z
  let f := Spec.fullyFaithful.preimage (Y.left.fromSpecResidueField z ≫ Y.hom)
  let : Algebra k R := f.unop.hom.toAlgebra
  have eq : Y.left.fromSpecResidueField z ≫ Y.hom = (AlgSpecObj k R).hom :=
    (Spec.fullyFaithful.map_preimage _).symm
  let p : Points Y (CommAlgCat.of k R) := Over.homMk (Y.left.fromSpecResidueField z) eq
  exact ⟨R, inferInstance, inferInstance, p, Y.left.fromSpecResidueField_apply z _⟩

section ProjectiveCharts

attribute [local instance] MvPolynomial.gradedAlgebra

variable {J : Type u}

private theorem projectiveChart_affine (j : J) : IsAffineOpen (projectiveChart k J j) :=
  Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule J k) (MvPolynomial.X j)
    (projectiveVariable_mem k J j) Nat.one_pos

private theorem projectiveCharts_cover (x : (projectiveSpace k J).left) :
    ∃ j, x ∈ projectiveChart k J j := by
  have heq : ⨆ j : J, projectiveChart k J j = ⊤ := by
    change ⨆ j : J, Proj.basicOpen (MvPolynomial.homogeneousSubmodule J k) (MvPolynomial.X j) = ⊤
    apply Proj.iSup_basicOpen_eq_top
    rw [HomogeneousIdeal.toIdeal_irrelevant_le]
    intro n hn
    change MvPolynomial.homogeneousSubmodule J k n ≤
      (Ideal.span (Set.range MvPolynomial.X)).restrictScalars k
    rw [← MvPolynomial.homogeneousSubmodule_one_pow, MvPolynomial.homogeneousSubmodule_one_eq_span_X]
    have hincl : Submodule.span k (Set.range (MvPolynomial.X (R := k) (σ := J))) ≤
        (Ideal.span (Set.range MvPolynomial.X)).restrictScalars k :=
      Submodule.span_le.mpr fun _ ha ↦ Ideal.subset_span ha
    exact (pow_le_pow_left' hincl _).trans (by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
      rw [pow_succ]
      exact Submodule.mul_le.mpr fun a _ b hb ↦ Ideal.mul_mem_left _ a hb)
  exact TopologicalSpace.Opens.mem_iSup.mp (heq.symm ▸ TopologicalSpace.Opens.mem_top x)

private theorem projectiveRatio_self (j : J) : projectiveRatio k J j j = 1 := by
  unfold projectiveRatio HomogeneousLocalization.Away.isLocalizationElem
  apply HomogeneousLocalization.val_injective (Submonoid.powers (MvPolynomial.X j))
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one,
    Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  simp

private theorem exists_spec_map {R S : CommRingCat.{u}} (y : Spec R ⟶ Spec S) :
    ∃ f : S →+* R, Spec.map (CommRingCat.ofHom f) = y := by
  let f := Spec.fullyFaithful.preimage y
  exact ⟨f.unop.hom, Spec.fullyFaithful.map_preimage y⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem exists_projective_coordinates {K : Type u} [Field K] [Algebra k K]
    (x : Points (projectiveSpace k J) (CommAlgCat.of k K)) :
    ∃ v, HasProjectiveCoordinates x v := by
  obtain ⟨j, hj⟩ := projectiveCharts_cover (x.left (IsLocalRing.closedPoint K))
  have h (q : Spec (CommRingCat.of K)) : q = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  let m := projectiveChartInclusion k J j
  let : IsOpenImmersion m := by
    unfold m projectiveChartInclusion Proj.awayι
    exact IsOpenImmersion.comp _ _
  have hm : m.opensRange = projectiveChart k J j :=
    Proj.opensRange_awayι (MvPolynomial.homogeneousSubmodule J k) (MvPolynomial.X j)
      (projectiveVariable_mem k J j) Nat.one_pos
  have hrange : Set.range x.left ⊆ Set.range m := by
    rintro _ ⟨q, rfl⟩
    rw [h q, ← Scheme.Hom.coe_opensRange, hm]
    exact hj
  let y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (projectiveChartRing k J j)) :=
    IsOpenImmersion.lift m x.left hrange
  have hy : y ≫ m = x.left := IsOpenImmersion.lift_fac m x.left hrange
  obtain ⟨f, hf⟩ := exists_spec_map y
  refine ⟨fun i ↦ f (projectiveRatio k J j i), j, f, ?_, ?_, ?_⟩
  · exact (congrArg (· ≫ m) hf).trans hy
  · change f (projectiveRatio k J j j) ≠ 0
    rw [projectiveRatio_self, map_one]
    exact one_ne_zero
  · intro i
    change f (projectiveRatio k J j i) = f (projectiveRatio k J j i) / f (projectiveRatio k J j j)
    rw [projectiveRatio_self, map_one, div_one]

set_option backward.isDefEq.respectTransparency false in
private theorem mem_projectiveChart_iff {K : Type u} [Field K] [Algebra k K]
    {x : Points (projectiveSpace k J) (CommAlgCat.of k K)} {v : J → K}
    (h : HasProjectiveCoordinates x v) (i : J) :
    x.left (IsLocalRing.closedPoint K) ∈ projectiveChart k J i ↔ v i ≠ 0 := by
  obtain ⟨j, f, hf, hj, hv⟩ := h
  have he : x.left (IsLocalRing.closedPoint K) = _ :=
    congrArg (fun p : Spec (CommRingCat.of K) ⟶ (projectiveSpace k J).left ↦
      p (IsLocalRing.closedPoint K)) hf.symm
  rw [he]
  change (Spec.map (CommRingCat.ofHom f)) (IsLocalRing.closedPoint K) ∈
    (projectiveChartInclusion k J j) ⁻¹ᵁ (projectiveChart k J i) ↔ _
  rw [projectiveChartInclusion, projectiveChart,
    Proj.awayι_preimage_basicOpen (MvPolynomial.homogeneousSubmodule J k)
      (projectiveVariable_mem k J j) Nat.one_pos (projectiveVariable_mem k J i) Nat.one_pos]
  change PrimeSpectrum.comap f (IsLocalRing.closedPoint K) ∈
    PrimeSpectrum.basicOpen (projectiveRatio k J j i) ↔ _
  rw [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  change f (projectiveRatio k J j i) ∉ IsLocalRing.maximalIdeal K ↔ _
  rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot, hv]
  exact (div_ne_zero_iff (a := v i) (b := v j)).trans (and_iff_left hj)


set_option backward.isDefEq.respectTransparency false in
private theorem diagonal_action_preserves_chart {M : Type u} [CommGroup M] [Group.FG M]
    (w : J → M)
    (b : ModObj (Specs.DiagonalizableGroups.diagonalGroup k M).val.X (projectiveSpace k J))
    (hb : IsDiagonalProjectiveAction w b) {K : Type u} [Field K] [Algebra k K]
    (g : Points (Specs.DiagonalizableGroups.diagonalGroup k M).val.X (CommAlgCat.of k K))
    (x : Points (projectiveSpace k J) (CommAlgCat.of k K)) (j : J)
    (hx : x.left (IsLocalRing.closedPoint K) ∈ projectiveChart k J j) :
      (lift g x ≫ b.smul).left (IsLocalRing.closedPoint K) ∈ projectiveChart k J j := by
  obtain ⟨v, hv⟩ := exists_projective_coordinates x
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let f : MonoidAlgebra k M →ₐ[k] K :=
    (ff.preimage (show Points (AlgSpecObj k (MonoidAlgebra k M)) (CommAlgCat.of k K) from g)).unop.hom
  have hg : (testSpec k).map (CommAlgCat.ofHom f).op = g := ff.map_preimage g
  have hh := hb K f x v hv
  rw [hg] at hh
  apply (mem_projectiveChart_iff hh j).mpr
  have hunit : IsUnit (MonoidAlgebra.of k M (w j)) :=
    ⟨⟨_, MonoidAlgebra.of k M ((w j)⁻¹),
      by rw [← map_mul, mul_inv_cancel, map_one],
      by rw [← map_mul, inv_mul_cancel, map_one]⟩, rfl⟩
  exact mul_ne_zero (hunit.map f).ne_zero ((mem_projectiveChart_iff hv j).mp hx)

set_option backward.isDefEq.respectTransparency false in
theorem projectivelyEmbeddedFixedLocusSmooth :
    Specs.DiagonalizableFixedLocus.ProjectivelyEmbeddedFixedLocusSmooth.{u} := by
  classical
  intro k M J _ _ _ _ X Z hX w b a hb e he heq i hi hrep
  let : Smooth X.hom := hX
  apply fixedLocusSmoothOnInvariantCharts X a Z i hi hrep
  intro z
  obtain ⟨j, hmem⟩ := projectiveCharts_cover (e.left (i.left z))
  let W := e.left ⁻¹ᵁ projectiveChart k J j
  let U : SchemeOver k := Over.mk (W.ι ≫ X.hom)
  let j' : U ⟶ X := Over.homMk W.ι rfl
  let : IsClosedImmersion e.left := he
  have hW : IsAffineOpen W := IsAffineHom.isAffine_preimage (f := e.left) _ (projectiveChart_affine j)
  let : IsOpenImmersion j'.left := inferInstanceAs (IsOpenImmersion W.ι)
  let : Mono j' := Over.mono_of_mono_left j'
  let D := (Specs.DiagonalizableGroups.diagonalGroup k M).val.X
  let m := (D ◁ j') ≫ a.smul
  have hr : Set.range m.left ⊆ Set.range j'.left := by
    rintro y ⟨s, rfl⟩
    change m.left s ∈ Set.range W.ι
    rw [Scheme.Opens.range_ι]
    change e.left (m.left s) ∈ projectiveChart k J j
    obtain ⟨L, _, _, t, ht⟩ := exists_field_point (D ⊗ U) s
    let g := t ≫ fst D U
    let u := t ≫ snd D U
    let xx := u ≫ j' ≫ e
    have hxx : xx.left (IsLocalRing.closedPoint L) ∈ projectiveChart k J j := by
      change e.left (W.ι (u.left (IsLocalRing.closedPoint L))) ∈ projectiveChart k J j
      exact (u.left (IsLocalRing.closedPoint L)).property
    have hm := diagonal_action_preserves_chart w b hb g xx j hxx
    have hmap : lift g xx = t ≫ (D ◁ (j' ≫ e)) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [g, xx, u]
    have eq : lift g xx ≫ b.smul = t ≫ m ≫ e := by
      change a.smul ≫ e = (D ◁ e) ≫ b.smul at heq
      simp only [hmap, m, Category.assoc, heq, whiskerLeft_comp]
    rw [eq] at hm
    simpa only [Over.comp_left, Scheme.Hom.comp_apply, ht] using hm
  let r := IsOpenImmersion.lift j'.left m.left hr
  have hrj : r ≫ j'.left = m.left := IsOpenImmersion.lift_fac _ _ _
  let rr : D ⊗ U ⟶ U := Over.homMk r (by
    change r ≫ (j'.left ≫ X.hom) = _
    rw [← Category.assoc, hrj, Over.w m])
  have hrr : rr ≫ j' = m := Over.OverMorphism.ext hrj
  refine ⟨U, j', hW, inferInstance, ?_, restrictAction a j' rr hrr, hrr⟩
  change i.left z ∈ Set.range W.ι
  rw [Scheme.Opens.range_ι]
  exact hmem

set_option backward.isDefEq.respectTransparency false in
theorem existsProjectivelyEmbeddedFixedLocus :
    Specs.DiagonalizableFixedLocus.ExistsProjectivelyEmbeddedFixedLocus.{u} := by
  intro k M J _ _ _ _ X hX w b a hb e he heq
  let D := Specs.DiagonalizableGroups.diagonalGroup k M
  let : IsClosedImmersion e.left := he
  let q := Proj.toSpecZero (MvPolynomial.homogeneousSubmodule J k)
  let p := Spec.map (CommRingCat.ofHom
    (algebraMap k ↥(MvPolynomial.homogeneousSubmodule J k 0)))
  let : IsScalarTower k ↥(MvPolynomial.homogeneousSubmodule J k 0) (MvPolynomial J k) := by
    constructor
    intro c f g
    change (c • f.val) * g = c • (f.val * g)
    exact smul_mul_assoc _ _ _
  let : Algebra.FiniteType ↥(MvPolynomial.homogeneousSubmodule J k 0) (MvPolynomial J k) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k _ _
  have hsep : IsSeparated X.hom := by
    rw [← Over.w e]
    change IsSeparated (e.left ≫ q ≫ p)
    infer_instance
  have hqc : QuasiCompact X.hom := by
    rw [← Over.w e]
    change QuasiCompact (e.left ≫ q ≫ p)
    infer_instance
  obtain ⟨Z, i, hi, hrep⟩ := fixedPointScheme k D X a hsep inferInstance hqc
  exact ⟨Z, i, hi, hrep, projectivelyEmbeddedFixedLocusSmooth X Z w b a hb e he heq i hi hrep⟩

end ProjectiveCharts

section AffineNeighborhoods

set_option backward.isDefEq.respectTransparency false

private theorem range_eq_preimage {P X Y Z : Scheme.{u}} {f : P ⟶ X} {g : P ⟶ Y}
    {e : X ⟶ Z} {j : Y ⟶ Z} (h : IsPullback f g e j) : Set.range f = e ⁻¹' Set.range j := by
  rw [← h.isoPullback_hom_fst, ← Scheme.Pullback.range_fst, Scheme.Hom.comp_base,
    TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr h.isoPullback.hom.surjective,
    Set.image_univ]

/-- The automorphism `(g, y) ↦ (g, g • y)` of the product. -/
private def actionProductIso {D Y : SchemeOver k} [GrpObj D] (a : ModObj D Y) : D ⊗ Y ≅ D ⊗ Y := by
  let : ModObj D Y := a
  have smul_eq : a.smul = fst D Y • snd D Y := by rw [Hom.smul_def, lift_fst_snd, Category.id_comp]
  let g := lift (fst D Y) ((fst D Y)⁻¹ • snd D Y)
  refine ⟨lift (fst D Y) a.smul, g, ?_, ?_⟩
  · rw [smul_eq]
    apply CartesianMonoidalCategory.hom_ext
    · simp [g]
    · dsimp only [g]
      rw [Category.assoc, lift_snd, ModObj.comp_smul, GrpObj.comp_inv, lift_fst, lift_snd]
      simp
  · rw [smul_eq]
    apply CartesianMonoidalCategory.hom_ext
    · simp [g]
    · rw [Category.assoc, lift_snd, ModObj.comp_smul]
      simp [g]

@[reassoc (attr := simp)]
private theorem actionProductIso_hom_snd {D Y : SchemeOver k} [GrpObj D] (a : ModObj D Y) :
    (actionProductIso a).hom ≫ snd _ _ = a.smul := lift_snd _ _

private theorem action_pullback {D X Y : SchemeOver k} [GrpObj D]
    (a : ModObj D X) (b : ModObj D Y) (e : X ⟶ Y)
    (he : a.smul ≫ e = (D ◁ e) ≫ b.smul) :
    IsPullback (D ◁ e) a.smul b.smul e := by
  let h := actionProductIso a
  let j := actionProductIso b
  have hnat : (D ◁ e) ≫ j.hom = h.hom ≫ (D ◁ e) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [h, j, actionProductIso]
    · simp [h, j, he]
  refine (whiskerLeft_pullback e).of_iso h.symm j.symm (Iso.refl X) (Iso.refl Y) ?_ ?_ ?_ (by simp)
  · change (D ◁ e) ≫ j.inv = h.inv ≫ (D ◁ e)
    rw [← cancel_mono j.hom, Category.assoc, j.inv_hom_id, Category.comp_id,
      Category.assoc, hnat, h.inv_hom_id_assoc]
  · change snd D X ≫ 𝟙 X = h.inv ≫ a.smul
    rw [← actionProductIso_hom_snd a, Category.comp_id]
    exact (h.inv_hom_id_assoc _).symm
  · change snd D Y ≫ 𝟙 Y = j.inv ≫ b.smul
    rw [← actionProductIso_hom_snd b, Category.comp_id]
    exact (j.inv_hom_id_assoc _).symm

/-- The open complement of the boundary of an equivariant image is invariant.
Both maps out of the product are open, so their inverse images commute with closure. -/
private theorem action_preimage_coborder {D X Y : SchemeOver k} [GrpObj D]
    [UniversallyOpen D.hom] (a : ModObj D X) (b : ModObj D Y) (e : X ⟶ Y)
    (he : a.smul ≫ e = (D ◁ e) ≫ b.smul) :
    b.smul.left ⁻¹' coborder (Set.range e.left) =
      (snd D Y).left ⁻¹' coborder (Set.range e.left) := by
  let q := (snd D Y).left
  have : UniversallyOpen q :=
    MorphismProperty.of_isPullback (P := @UniversallyOpen) (over_product_isPullback D Y) inferInstance
  have hop : IsOpenMap b.smul.left := by
    have h := congrArg Over.Hom.left (actionProductIso_hom_snd b)
    change (actionProductIso b).hom.left ≫ q = b.smul.left at h
    rw [← h]
    exact q.isOpenMap.comp (actionProductIso b).hom.left.homeomorph.isOpenMap
  have hs : b.smul.left ⁻¹' Set.range e.left = q ⁻¹' Set.range e.left := by
    have h₁ := range_eq_preimage ((action_pullback a b e he).map (Over.forget _))
    have h₂ := range_eq_preimage ((whiskerLeft_pullback (H := D) e).map (Over.forget _))
    exact h₁.symm.trans h₂
  rw [← coborder_preimage hop b.smul.left.continuous,
    ← coborder_preimage q.isOpenMap q.continuous, hs]

private theorem diagonal_universallyOpen [Group.FG M] :
    UniversallyOpen (Specs.DiagonalizableGroups.diagonalGroup k M).val.X.hom := by
  let D := Specs.DiagonalizableGroups.diagonalGroup k M
  let : LocallyOfFiniteType D.val.X.hom := D.property.2.1
  let : Flat D.val.X.hom := by
    change Flat (Spec.map (CommRingCat.ofHom (algebraMap k B)))
    rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
    infer_instance
  exact inferInstanceAs (UniversallyOpen D.val.X.hom)

private theorem restrict_action_open {D X : SchemeOver k} [MonObj D]
    (a : ModObj D X) (W : X.left.Opens)
    (h : ∀ s : (D ⊗ X).left, (snd D X).left s ∈ W → a.smul.left s ∈ W) :
    ∃ b : ModObj D (Over.mk (W.ι ≫ X.hom)),
      b.smul ≫ Over.homMk W.ι rfl = (D ◁ Over.homMk W.ι rfl) ≫ a.smul := by
  let U : SchemeOver k := Over.mk (W.ι ≫ X.hom)
  let j : U ⟶ X := Over.homMk W.ι rfl
  let : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion W.ι)
  let : Mono j := Over.mono_of_mono_left j
  let m := (D ◁ j) ≫ a.smul
  have hr : Set.range m.left ⊆ Set.range j.left := by
    rintro _ ⟨s, rfl⟩
    change m.left s ∈ Set.range W.ι
    rw [Scheme.Opens.range_ι]
    apply h ((D ◁ j).left s)
    have hp := congrArg (fun f : D ⊗ U ⟶ X ↦ f.left s) (whiskerLeft_snd D j)
    change (snd D X).left ((D ◁ j).left s) = W.ι ((snd D U).left s) at hp
    rw [hp]
    exact ((snd D U).left s).property
  let r := IsOpenImmersion.lift j.left m.left hr
  have hrj : r ≫ j.left = m.left := IsOpenImmersion.lift_fac _ _ _
  let rr : D ⊗ U ⟶ U := Over.homMk r (by
    change r ≫ (j.left ≫ X.hom) = _
    rw [← Category.assoc, hrj, Over.w m])
  have hrr : rr ≫ j = m := Over.OverMorphism.ext hrj
  exact ⟨restrictAction a j rr hrr, hrr⟩

private theorem preimage_preserved_open {D X Y : SchemeOver k} [MonObj D]
    (a : ModObj D X) (b : ModObj D Y) (e : X ⟶ Y)
    (he : a.smul ≫ e = (D ◁ e) ≫ b.smul) (W : Y.left.Opens)
    (hW : ∀ s : (D ⊗ Y).left, (snd D Y).left s ∈ W → b.smul.left s ∈ W) :
    ∀ s : (D ⊗ X).left, (snd D X).left s ∈ e.left ⁻¹ᵁ W →
      a.smul.left s ∈ e.left ⁻¹ᵁ W := by
  intro s hs
  have h1 := congrArg (fun f : D ⊗ X ⟶ Y ↦ f.left s) he
  have h2 := congrArg (fun f : D ⊗ X ⟶ Y ↦ f.left s) (whiskerLeft_snd D e)
  change e.left (a.smul.left s) = b.smul.left ((D ◁ e).left s) at h1
  change (snd D Y).left ((D ◁ e).left s) = e.left ((snd D X).left s) at h2
  change e.left (a.smul.left s) ∈ W
  rw [h1]
  exact hW _ (h2 ▸ hs)

private theorem isClosedImmersion_restrict_coborder {X Y : Scheme.{u}} (e : X ⟶ Y)
    [IsImmersion e] (W : Y.Opens) (hW : W ≤ e.coborderRange) : IsClosedImmersion (e ∣_ W) := by
  apply IsClosedImmersion.of_isPreimmersion
  rw [range_eq_preimage (isPullback_morphismRestrict e W)]
  have h : W.ι ⁻¹' Set.range e = W.ι ⁻¹' closure (Set.range e) := by
    ext x
    change W.ι x ∈ Set.range e ↔ W.ι x ∈ closure (Set.range e)
    exact ⟨fun hx ↦ subset_closure hx, mem_coborder_iff_imp.mp (hW x.property)⟩
  rw [h]
  exact isClosed_closure.preimage W.ι.continuous

omit [CommGroup M] in
private theorem tensorCoefficients_rTensor {V V' : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup V'] [Module k V'] [DecidableEq M] (f : V →ₗ[k] V') (t : V ⊗[k] B) (m : M) :
    tensorCoefficients (f.rTensor B t) m = f (tensorCoefficients t m) := by
  induction t using TensorProduct.inductionOn with
  | add p q hp hq => simp only [map_add, Finsupp.add_apply, hp, hq]
  | tmul v b =>
    simp only [LinearMap.rTensor_tmul, tensorCoefficients, LinearEquiv.trans_apply,
      LinearEquiv.lTensor_tmul, TensorProduct.finsuppScalarRight_apply_tmul_apply, map_smul]

private theorem fixedPoint_weightOne [Group.FG M] {K : Type u} [Field K] [Algebra k K]
    [DecidableEq M] (a : ModObj (AlgSpecObj k B) (AlgSpecObj k A)) (x : A →ₐ[k] K)
    (hx : IsFixedBy a.smul ((testSpec k).map (CommAlgCat.ofHom x).op)) (f : A) :
    let D := op (CommAlgCat.of k B)
    let Y := op (CommAlgCat.of k A)
    let ρ := coordinateCoaction (reflectAction (testSpec k)
      (algSpec.fullyFaithful (R := CommRingCat.of k)) D Y a)
    x (weightProjection ρ.toRightComodule 1 f) = x f := by
  dsimp only
  let D := op (CommAlgCat.of k B)
  let Y := op (CommAlgCat.of k A)
  let ρ := coordinateCoaction (reflectAction (testSpec k)
    (algSpec.fullyFaithful (R := CommRingCat.of k)) D Y a)
  have h := (fixedAlgebraPoints ρ x).mpr ((affine_fixed_criterion a x).mp hx) f
  have hcoeff := congrArg (fun t ↦ tensorCoefficients t (1 : M)) h
  rw [tensorCoefficients_rTensor, ← map_one (MonoidAlgebra.of k M), tensorCoefficients_tmul,
    Finsupp.single_eq_same] at hcoeff
  exact hcoeff

set_option maxHeartbeats 500000 in
private theorem preserved_basicOpen_of_weightOne [Group.FG M]
    (a : ModObj (AlgSpecObj k B) (AlgSpecObj k A))
    (f : A)
    (hf : let D := op (CommAlgCat.of k B)
          let Y := op (CommAlgCat.of k A)
          let ρ := coordinateCoaction (reflectAction (testSpec k)
            (algSpec.fullyFaithful (R := CommRingCat.of k)) D Y a)
          f ∈ weightSpace ρ.toRightComodule (1 : M)) :
    ∀ s : (AlgSpecObj k B ⊗ AlgSpecObj k A).left,
      (snd (AlgSpecObj k B) (AlgSpecObj k A)).left s ∈ PrimeSpectrum.basicOpen f →
        a.smul.left s ∈ PrimeSpectrum.basicOpen f := by
  let D := op (CommAlgCat.of k B)
  let Y := op (CommAlgCat.of k A)
  let F := testSpec k
  let : F.Braided := braidedAlgSpec (R := CommRingCat.of k)
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let a' := reflectAction F ff D Y a
  let ρ := coordinateCoaction a'
  let δ := OplaxMonoidal.δ F D Y
  have ha : F.map a'.smul = δ ≫ a.smul := ff.map_preimage _
  have hs : F.map (snd D Y) = δ ≫ snd (F.obj D) (F.obj Y) := by
    change _ = OplaxMonoidal.δ F D Y ≫ _
    rw [OplaxMonoidal.δ_of_cartesianMonoidalCategory]
    exact (CartesianMonoidalCategory.prodComparison_snd F D Y).symm
  have h : a'.smul.unop.hom f = (snd D Y).unop.hom f := by
    apply (TensorProduct.comm k B A).injective
    change ρ.hom f = f ⊗ₜ[k] (1 : B)
    rw [hom_of_weight ρ hf, map_one]
  let : IsIso δ := inferInstanceAs (IsIso (OplaxMonoidal.δ F D Y))
  let : IsIso δ.left := (Over.forget _).map_isIso δ
  intro s
  obtain ⟨t, rfl⟩ := δ.left.surjective s
  have hp₁ : (F.map a'.smul).left t = a.smul.left (δ.left t) :=
    congrArg (fun g : F.obj (D ⊗ Y) ⟶ F.obj Y ↦ g.left t) ha
  have hp₂ : (F.map (snd D Y)).left t = (snd (F.obj D) (F.obj Y)).left (δ.left t) :=
    congrArg (fun g : F.obj (D ⊗ Y) ⟶ F.obj Y ↦ g.left t) hs
  change (snd (F.obj D) (F.obj Y)).left (δ.left t) ∈ PrimeSpectrum.basicOpen f →
    a.smul.left (δ.left t) ∈ PrimeSpectrum.basicOpen f
  rw [← hp₁, ← hp₂]
  change PrimeSpectrum.comap (snd D Y).unop.hom.toRingHom t ∈ PrimeSpectrum.basicOpen f →
    PrimeSpectrum.comap a'.smul.unop.hom.toRingHom t ∈ PrimeSpectrum.basicOpen f
  simp only [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  change _ ∉ t.asIdeal → a'.smul.unop.hom f ∉ t.asIdeal
  rw [h]
  exact id

set_option maxHeartbeats 700000 in
/-- An invariant open in an affine scheme contains an invariant principal open
about each fixed field-valued point. A power of a function vanishing on the
complement has coaction zero modulo the ideal of the complement. Its
trivial-weight coefficient is therefore a suitable defining function. -/
private theorem invariant_basicOpen [Group.FG M] {K : Type u} [Field K] [Algebra k K]
    (a : ModObj (AlgSpecObj k B) (AlgSpecObj k A))
    (W : (AlgSpecObj k A).left.Opens)
    (hW : a.smul.left ⁻¹' (W : Set (AlgSpecObj k A).left) =
      (snd (AlgSpecObj k B) (AlgSpecObj k A)).left ⁻¹' (W : Set (AlgSpecObj k A).left))
    (x : A →ₐ[k] K) (hx : IsFixedBy a.smul ((testSpec k).map (CommAlgCat.ofHom x).op))
    (hxW : ((testSpec k).map (CommAlgCat.ofHom x).op).left (IsLocalRing.closedPoint K) ∈ W) :
    ∃ f : A, ((testSpec k).map (CommAlgCat.ofHom x).op).left (IsLocalRing.closedPoint K) ∈
      PrimeSpectrum.basicOpen f ∧ PrimeSpectrum.basicOpen f ≤ W ∧
      ∀ s : (AlgSpecObj k B ⊗ AlgSpecObj k A).left,
        (snd (AlgSpecObj k B) (AlgSpecObj k A)).left s ∈ PrimeSpectrum.basicOpen f →
          a.smul.left s ∈ PrimeSpectrum.basicOpen f := by
  classical
  let D := op (CommAlgCat.of k B)
  let Y := op (CommAlgCat.of k A)
  let F := testSpec k
  let : F.Braided := braidedAlgSpec (R := CommRingCat.of k)
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let a' := reflectAction F ff D Y a
  let ρ := coordinateCoaction a'
  let p := PrimeSpectrum.comap x.toRingHom (IsLocalRing.closedPoint K)
  let S : Set (PrimeSpectrum A) := (W : Set (AlgSpecObj k A).left)
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Sᶜ).mp
    W.isOpen.isClosed_compl
  have hp : p ∉ PrimeSpectrum.zeroLocus I := by
    rw [← hI]
    exact fun hc ↦ hc hxW
  obtain ⟨f, hfI, hf⟩ := Set.not_subset.mp (fun h ↦ hp ((PrimeSpectrum.mem_zeroLocus _ _).mpr h))
  let Q := op (CommAlgCat.of k (A ⧸ I))
  let q := Ideal.Quotient.mkₐ k I
  let π : Q ⟶ Y := (CommAlgCat.ofHom q).op
  let τ : D ⊗ Q ⟶ Y := (D ◁ π) ≫ a'.smul
  let v : A →ₐ[k] B ⊗[k] (A ⧸ I) := τ.unop.hom
  let δ := OplaxMonoidal.δ F D Q
  have ha : F.map a'.smul = OplaxMonoidal.δ F D Y ≫ a.smul := ff.map_preimage _
  have hvSpec : F.map τ = δ ≫ (F.obj D ◁ F.map π) ≫ a.smul := by
    rw [show τ = (D ◁ π) ≫ a'.smul from rfl, F.map_comp, ha]
    exact (OplaxMonoidal.δ_natural_right_assoc F D π a.smul).symm
  have hnil : IsNilpotent (v f) := by
    apply mem_nilradical.mp
    apply (PrimeSpectrum.zeroLocus_eq_univ_iff {v f}).mp _ (Set.mem_singleton _)
    apply Set.eq_univ_of_forall
    intro z
    apply (PrimeSpectrum.mem_zeroLocus _ _).mpr
    rintro _ rfl
    let s := (F.obj D ◁ F.map π).left (δ.left z)
    have hproj : (snd (F.obj D) (F.obj Y)).left s ∈ PrimeSpectrum.zeroLocus (↑I : Set A) := by
      have eq := congrArg (fun f : F.obj D ⊗ F.obj Q ⟶ F.obj Y ↦ f.left (δ.left z))
        (whiskerLeft_snd (F.obj D) (F.map π))
      change (snd (F.obj D) (F.obj Y)).left s =
        (F.map π).left ((snd (F.obj D) (F.obj Q)).left (δ.left z)) at eq
      rw [eq]
      apply (PrimeSpectrum.mem_zeroLocus _ _).mpr
      intro r hr
      change r ∈ (PrimeSpectrum.comap q.toRingHom _).asIdeal
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
      change Ideal.Quotient.mk I r ∈ _
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr]
      exact zero_mem _
    have hact : a.smul.left s ∈ PrimeSpectrum.zeroLocus (↑I : Set A) := by
      rw [← hI] at hproj ⊢
      intro hs
      exact hproj ((Set.ext_iff.mp hW s).mp hs)
    have eq := congrArg (fun g : F.obj (D ⊗ Q) ⟶ F.obj Y ↦ g.left z) hvSpec
    change PrimeSpectrum.comap v.toRingHom z = a.smul.left s at eq
    have hz : f ∈ (PrimeSpectrum.comap v.toRingHom z).asIdeal := by
      rw [eq]
      exact (PrimeSpectrum.mem_zeroLocus _ _).mp hact hfI
    exact hz
  obtain ⟨n, hn⟩ := hnil
  let g := weightProjection ρ.toRightComodule (1 : M) (f ^ n)
  have hgI : g ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q g = 0
    have hq (t : B ⊗[k] A) : q.toLinearMap.rTensor B (TensorProduct.comm k B A t) =
        TensorProduct.comm k B (A ⧸ I) ((Algebra.TensorProduct.map (AlgHom.id k B) q) t) := by
      induction t using TensorProduct.inductionOn with
      | tmul b a => rfl
      | add p r hp hr => simp [hp, hr]
    rw [show q g = tensorCoefficients (q.toLinearMap.rTensor B (ρ.hom (f ^ n))) (1 : M) from
      (tensorCoefficients_rTensor q.toLinearMap _ _).symm]
    change tensorCoefficients
      (q.toLinearMap.rTensor B (TensorProduct.comm k B A (a'.smul.unop.hom (f ^ n)))) 1 = 0
    rw [hq]
    change tensorCoefficients (TensorProduct.comm k B (A ⧸ I) (v (f ^ n))) 1 = 0
    rw [map_pow, hn, map_zero, map_zero, Finsupp.zero_apply]
  have hxg : x g ≠ 0 := by
    rw [fixedPoint_weightOne a x hx, map_pow]
    have hxf : x f ≠ 0 := by
      intro hz
      apply hf
      change x f ∈ IsLocalRing.maximalIdeal K
      rw [hz]
      exact zero_mem _
    exact pow_ne_zero _ hxf
  refine ⟨g, ?_, ?_, preserved_basicOpen_of_weightOne a g (projection_mem _ _ _)⟩
  · change x g ∉ IsLocalRing.maximalIdeal K
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot]
    exact hxg
  · intro z hz
    by_contra hzW
    have hzI : z ∈ PrimeSpectrum.zeroLocus (↑I : Set A) := hI ▸ hzW
    exact hz ((PrimeSpectrum.mem_zeroLocus _ _).mp hzI hgI)

private theorem isFixedBy_comp_equivariant {D T X Y : SchemeOver k}
    {a : D ⊗ X ⟶ X} {b : D ⊗ Y ⟶ Y} {j : X ⟶ Y}
    (hj : a ≫ j = (D ◁ j) ≫ b) {x : T ⟶ X} (hx : IsFixedBy a x) :
    IsFixedBy b (x ≫ j) := by
  unfold IsFixedBy at hx ⊢
  rw [whiskerLeft_comp, Category.assoc, ← hj, ← Category.assoc, hx, Category.assoc]

private theorem isFixedBy_of_comp_equivariant {D T X Y : SchemeOver k}
    {a : D ⊗ X ⟶ X} {b : D ⊗ Y ⟶ Y} {j : X ⟶ Y} [Mono j]
    (hj : a ≫ j = (D ◁ j) ≫ b) {x : T ⟶ X} (hx : IsFixedBy b (x ≫ j)) :
    IsFixedBy a x := by
  unfold IsFixedBy at hx ⊢
  apply (cancel_mono j).mp
  rw [Category.assoc, hj, ← whiskerLeft_comp_assoc, hx, Category.assoc]

private theorem invariant_affine_neighborhood [Group.FG M] {K : Type u} [Field K] [Algebra k K]
    {X Y : SchemeOver k} [IsAffine Y.left]
    (a : ModObj (Specs.DiagonalizableGroups.diagonalGroup k M).val.X X)
    (b : ModObj (Specs.DiagonalizableGroups.diagonalGroup k M).val.X Y)
    (e : X ⟶ Y) [IsImmersion e.left]
    (he : a.smul ≫ e = ((Specs.DiagonalizableGroups.diagonalGroup k M).val.X ◁ e) ≫ b.smul)
    (x : Points X (CommAlgCat.of k K)) (hx : IsFixedBy a.smul x) :
    ∃ (U : SchemeOver k) (j : U ⟶ X), IsAffine U.left ∧ IsOpenImmersion j.left ∧
      x.left (IsLocalRing.closedPoint K) ∈ Set.range j.left ∧
      ∃ aU : ModObj (Specs.DiagonalizableGroups.diagonalGroup k M).val.X U,
        aU.smul ≫ j = ((Specs.DiagonalizableGroups.diagonalGroup k M).val.X ◁ j) ≫ a.smul := by
  let D := (Specs.DiagonalizableGroups.diagonalGroup k M).val.X
  let : UniversallyOpen D.hom := diagonal_universallyOpen (k := k) (M := M)
  obtain ⟨R, ⟨r⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr (show IsAffine Y.left from inferInstance)
  let : ModObj D Y := b
  let : IsMonHom (Iso.refl D).hom := by change IsMonHom (𝟙 D); infer_instance
  let b' : ModObj D ((testSpec k).obj R) := ModObj.ofIso (Iso.refl D) r.symm
  let e' := e ≫ r.inv
  let : IsIso r.inv.left := (Over.forget _).map_isIso r.inv
  let : IsImmersion e'.left := IsImmersion.comp e.left r.inv.left
  have he' : a.smul ≫ e' = (D ◁ e') ≫ b'.smul := by
    apply (cancel_mono r.hom).mp
    have hb : b'.smul ≫ r.hom = (D ◁ r.hom) ≫ b.smul := by
      change ((𝟙 D ⊗ₘ r.hom) ≫ b.smul ≫ r.inv) ≫ r.hom = _
      simp [whiskerLeft]
    simp only [Category.assoc, hb, ← whiskerLeft_comp_assoc, e', Iso.inv_hom_id, Category.comp_id]
    exact he
  let W := e'.left.coborderRange
  have hW : b'.smul.left ⁻¹' (W : Set ((testSpec k).obj R).left) =
      (snd D ((testSpec k).obj R)).left ⁻¹' (W : Set ((testSpec k).obj R).left) :=
    action_preimage_coborder a b' e' he'
  let f : R.unop →ₐ[k] K := ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage (x ≫ e')).unop.hom
  have hf : (testSpec k).map (CommAlgCat.ofHom f).op = x ≫ e' :=
    (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage _
  have hf_fix : IsFixedBy b'.smul ((testSpec k).map (CommAlgCat.ofHom f).op) :=
    hf ▸ isFixedBy_comp_equivariant he' hx
  have hfW : ((testSpec k).map (CommAlgCat.ofHom f).op).left (IsLocalRing.closedPoint K) ∈ W := by
    rw [hf]
    exact subset_coborder ⟨x.left (IsLocalRing.closedPoint K), rfl⟩
  obtain ⟨g, hg_mem, hg_le, hg_pres⟩ := invariant_basicOpen b' W hW f hf_fix hfW
  let O : ((testSpec k).obj R).left.Opens := PrimeSpectrum.basicOpen g
  let V := e'.left ⁻¹ᵁ O
  let : IsAffine O.toScheme := IsAffineOpen.Spec_basicOpen (R := CommRingCat.of R.unop) g
  let : IsClosedImmersion (e'.left ∣_ O) := isClosedImmersion_restrict_coborder e'.left O hg_le
  have hV : IsAffine V.toScheme := by
    let j : V.toScheme ⟶ O.toScheme := e'.left ∣_ O
    have : IsClosedImmersion j := inferInstanceAs (IsClosedImmersion (e'.left ∣_ O))
    exact isAffine_of_isAffineHom j
  obtain ⟨aU, haU⟩ := restrict_action_open a V (preimage_preserved_open a b' e' he' O hg_pres)
  refine ⟨Over.mk (V.ι ≫ X.hom), Over.homMk V.ι rfl, hV,
    inferInstanceAs (IsOpenImmersion V.ι), ?_, aU, haU⟩
  change x.left (IsLocalRing.closedPoint K) ∈ Set.range V.ι
  rw [Scheme.Opens.range_ι]
  change e'.left (x.left (IsLocalRing.closedPoint K)) ∈ O
  change (x ≫ e').left (IsLocalRing.closedPoint K) ∈ O
  rw [← hf]
  exact hg_mem

end AffineNeighborhoods

section LinearCharts

set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
variable {J V : Type u} [Fintype J] [AddCommGroup V] [Module k V]

private def linearPolynomial (c : Module.Basis J k V) (l : V →ₗ[k] k) : MvPolynomial J k :=
  ∑ i, MvPolynomial.C (l (c i)) * MvPolynomial.X i

private theorem linearPolynomial_mem (c : Module.Basis J k V) (l : V →ₗ[k] k) :
    linearPolynomial c l ∈ MvPolynomial.homogeneousSubmodule J k 1 :=
  (MvPolynomial.homogeneousSubmodule J k 1).sum_mem fun i _ ↦
    MvPolynomial.isHomogeneous_C_mul_X (l (c i)) i

private def linearChart (c : Module.Basis J k V) (l : V →ₗ[k] k) :
    (projectiveSpace k J).left.Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule J k) (linearPolynomial c l)

private theorem linearChart_affine (c : Module.Basis J k V) (l : V →ₗ[k] k) :
    IsAffineOpen (linearChart c l) :=
  Proj.isAffineOpen_basicOpen _ _ (linearPolynomial_mem c l) Nat.one_pos

private def chartConstant (j : J) : k →+* projectiveChartRing k J j :=
  (HomogeneousLocalization.fromZeroRingHom (MvPolynomial.homogeneousSubmodule J k)
    (Submonoid.powers (MvPolynomial.X j))).comp (algebraMap k _)

omit [Fintype J] in
private theorem map_chartConstant {K : Type u} [Field K] [Algebra k K]
    {x : Points (projectiveSpace k J) (CommAlgCat.of k K)} (j : J)
    (f : projectiveChartRing k J j →+* K)
    (hf : Spec.map (CommRingCat.ofHom f) ≫ projectiveChartInclusion k J j = x.left) (a : k) :
    f (chartConstant j a) = algebraMap k K a := by
  have h := Over.w x
  rw [← hf, Category.assoc] at h
  change Spec.map (CommRingCat.ofHom f) ≫
    Proj.awayι _ _ (projectiveVariable_mem k J j) Nat.one_pos ≫
    Proj.toSpecZero (MvPolynomial.homogeneousSubmodule J k) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k ↥(MvPolynomial.homogeneousSubmodule J k 0))) =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) at h
  rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp] at h
  exact congrArg (fun g : CommRingCat.of k ⟶ CommRingCat.of K ↦ g.hom a)
    (Spec.map_injective h)

set_option maxHeartbeats 500000 in
set_option backward.isDefEq.respectTransparency true in
private theorem linearPolynomial_ratio (c : Module.Basis J k V) (l : V →ₗ[k] k) (j : J) :
    HomogeneousLocalization.Away.isLocalizationElem (projectiveVariable_mem k J j)
      (linearPolynomial_mem c l) = ∑ i, chartConstant j (l (c i)) * projectiveRatio k J j i := by
  let s : Submonoid.powers (MvPolynomial.X (R := k) j) :=
    ⟨_, Submonoid.mem_powers _⟩
  let L := Localization (Submonoid.powers (MvPolynomial.X (R := k) j))
  have ratio_val (p : MvPolynomial J k) (hp : p ∈ MvPolynomial.homogeneousSubmodule J k 1) :
      (HomogeneousLocalization.Away.isLocalizationElem (projectiveVariable_mem k J j) hp).val =
        IsLocalization.mk' L p s := by
    unfold HomogeneousLocalization.Away.isLocalizationElem
    simp only [pow_one, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
    rfl
  have const_val (a : k) : (chartConstant j a).val = algebraMap (MvPolynomial J k) L (MvPolynomial.C a) := by
    change Localization.mk ((algebraMap k ↥(MvPolynomial.homogeneousSubmodule J k 0) a).val) 1 = _
    rw [Localization.mk_one_eq_algebraMap]
    rfl
  have term_eq (i : J) : algebraMap (projectiveChartRing k J j) L
      (chartConstant j (l (c i)) * projectiveRatio k J j i) =
      algebraMap (MvPolynomial J k) L (MvPolynomial.C (l (c i))) *
        IsLocalization.mk' L (MvPolynomial.X i) s := by
    rw [map_mul]
    change (chartConstant j (l (c i))).val * (projectiveRatio k J j i).val = _
    rw [const_val, projectiveRatio, ratio_val]
  apply HomogeneousLocalization.val_injective (Submonoid.powers (MvPolynomial.X j))
  change _ = algebraMap (projectiveChartRing k J j) L (∑ i, _)
  rw [map_sum, ratio_val]
  simp_rw [term_eq]
  apply (IsLocalization.map_units L s).mul_right_cancel
  rw [IsLocalization.mk'_spec, Finset.sum_mul, linearPolynomial]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, IsLocalization.mk'_spec, map_mul]

private theorem mem_linearChart_iff {K : Type u} [Field K] [Algebra k K]
    {x : Points (projectiveSpace k J) (CommAlgCat.of k K)} {v : J → K}
    (h : HasProjectiveCoordinates x v) (c : Module.Basis J k V) (l : V →ₗ[k] k) :
    x.left (IsLocalRing.closedPoint K) ∈ linearChart c l ↔
      ∑ i, algebraMap k K (l (c i)) * v i ≠ 0 := by
  obtain ⟨j, f, hf, hj, hv⟩ := h
  have he : x.left (IsLocalRing.closedPoint K) = _ :=
    congrArg (fun p : Spec (CommRingCat.of K) ⟶ (projectiveSpace k J).left ↦
      p (IsLocalRing.closedPoint K)) hf.symm
  rw [he]
  change (Spec.map (CommRingCat.ofHom f)) (IsLocalRing.closedPoint K) ∈
    (projectiveChartInclusion k J j) ⁻¹ᵁ (linearChart c l) ↔ _
  rw [projectiveChartInclusion, linearChart, Proj.awayι_preimage_basicOpen _
    (projectiveVariable_mem k J j) Nat.one_pos (linearPolynomial_mem c l) Nat.one_pos]
  change PrimeSpectrum.comap f (IsLocalRing.closedPoint K) ∈ PrimeSpectrum.basicOpen _ ↔ _
  rw [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  change f _ ∉ IsLocalRing.maximalIdeal K ↔ _
  rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot, linearPolynomial_ratio, map_sum]
  simp_rw [map_mul, map_chartConstant j f hf, hv, ← mul_div_assoc, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← div_eq_mul_inv]
  exact div_ne_zero_iff.trans (and_iff_left hj)

private theorem mem_weightChart_iff {K I : Type u} [Field K] [Algebra k K]
    {x : Points (projectiveSpace k J) (CommAlgCat.of k K)} {v : J → K}
    (h : HasProjectiveCoordinates x v) (c : Module.Basis J k V) (d : Module.Basis I k V) (i : I) :
    x.left (IsLocalRing.closedPoint K) ∈ linearChart c (d.coord i) ↔
      (d.baseChange K).coord i (∑ j, v j • (c.baseChange K) j) ≠ 0 := by
  rw [mem_linearChart_iff h, map_sum]
  simp only [map_smul, Module.Basis.baseChange_apply, Module.Basis.coord_apply,
    Module.Basis.baseChange_repr_tmul, Algebra.smul_def, Algebra.algebraMap_self_apply, mul_one]
  simp only [mul_comm]

private theorem linearActionAt_of_weight {K M : Type u} [Field K] [Algebra k K] [CommGroup M]
    (ρ : RightComodule k (MonoidAlgebra k M) V) (g : MonoidAlgebra k M →ₐ[k] K)
    {m : M} {v : V} (hv : v ∈ weightSpace ρ m) :
    linearActionAt ρ g (1 ⊗ₜ[k] v) = g (MonoidAlgebra.of k M m) ⊗ₜ[k] v := by
  simp [linearActionAt, mem_weightSpace.mp hv]

private theorem weightCoordinate_action {K M I : Type u} [Field K] [Algebra k K] [CommGroup M]
    (ρ : RightComodule k (MonoidAlgebra k M) V) (g : MonoidAlgebra k M →ₐ[k] K)
    (d : Module.Basis I k V) (w : I → M) (hw : ∀ i, d i ∈ weightSpace ρ (w i))
    (i : I) (v : K ⊗[k] V) :
    (d.baseChange K).coord i (linearActionAt ρ g v) =
      g (MonoidAlgebra.of k M (w i)) * (d.baseChange K).coord i v := by
  classical
  let b := d.baseChange K
  have h : (b.coord i).comp (linearActionAt ρ g) = g (MonoidAlgebra.of k M (w i)) • b.coord i := by
    apply b.ext
    intro j
    change b.coord i (linearActionAt ρ g (b j)) =
      g (MonoidAlgebra.of k M (w i)) * b.coord i (b j)
    by_cases e : j = i
    · subst j
      simp [b, linearActionAt_of_weight ρ g (hw i), Module.Basis.coord_apply, Algebra.smul_def]
    · simp [b, linearActionAt_of_weight ρ g (hw j), Module.Basis.coord_apply, e]
  exact DFunLike.congr_fun h v

/-- The nonvanishing opens of the weight-basis coordinate functionals cover
the original projective space and are invariant under the given action. -/
private theorem invariant_linearCharts {M : Type u} [CommGroup M] [Group.FG M]
    (c : Module.Basis J k V) (ρ : RightComodule k (MonoidAlgebra k M) V)
    (b : ModObj (Specs.DiagonalizableGroups.diagonalGroup k M).val.X (projectiveSpace k J))
    (hb : IsProjectivizedLinearAction c ρ b) (x : (projectiveSpace k J).left) :
    ∃ W : (projectiveSpace k J).left.Opens, IsAffineOpen W ∧ x ∈ W ∧
      ∀ s : ((Specs.DiagonalizableGroups.diagonalGroup k M).val.X ⊗
          projectiveSpace k J).left,
        (snd (Specs.DiagonalizableGroups.diagonalGroup k M).val.X (projectiveSpace k J)).left s ∈ W →
          b.smul.left s ∈ W := by
  classical
  let P := projectiveSpace k J
  let D := (Specs.DiagonalizableGroups.diagonalGroup k M).val.X
  have : FiniteDimensional k V := Module.Finite.of_basis c
  obtain ⟨I, hI, d, w, hw⟩ := existsWeightBasis ρ
  obtain ⟨K, _, _, t, ht⟩ := exists_field_point P x
  obtain ⟨v, hv⟩ := exists_projective_coordinates t
  have hne : ∑ j, v j • (c.baseChange K) j ≠ 0 := by
    obtain ⟨j, _, _, hj, _⟩ := hv
    rw [← Module.Basis.equivFun_symm_apply]
    intro h
    have hv0 := (c.baseChange K).equivFun.symm.injective (h.trans (map_zero _).symm)
    exact hj (congrFun hv0 j)
  obtain ⟨i, hi⟩ : ∃ i, (d.baseChange K).coord i (∑ j, v j • (c.baseChange K) j) ≠ 0 := by
    by_contra! h
    apply hne
    apply (d.baseChange K).repr.injective
    ext i
    exact h i
  refine ⟨linearChart c (d.coord i), linearChart_affine c (d.coord i), ?_, ?_⟩
  · rw [← ht]
    exact (mem_weightChart_iff hv c d i).mpr hi
  · intro s hs
    obtain ⟨L, _, _, p, hp⟩ := exists_field_point (D ⊗ P) s
    let g := p ≫ fst D P
    let y := p ≫ snd D P
    have hy : y.left (IsLocalRing.closedPoint L) ∈ linearChart c (d.coord i) := by
      simpa only [y, Over.comp_left, Scheme.Hom.comp_apply, hp] using hs
    obtain ⟨v', hv'⟩ := exists_projective_coordinates y
    let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
    let f : MonoidAlgebra k M →ₐ[k] L := (ff.preimage g).unop.hom
    have hg : (testSpec k).map (CommAlgCat.ofHom f).op = g := ff.map_preimage g
    have hz := hb L f y v' hv'
    rw [hg, show lift g y = p by apply CartesianMonoidalCategory.hom_ext <;> simp [g, y]] at hz
    have hh := (mem_weightChart_iff hz c d i).mpr (by
      rw [Module.Basis.sum_repr, weightCoordinate_action ρ f d w hw]
      have hunit : IsUnit (MonoidAlgebra.of k M (w i)) :=
        (Group.isUnit (w i)).map (MonoidAlgebra.of k M)
      exact mul_ne_zero (hunit.map f).ne_zero ((mem_weightChart_iff hv' c d i).mp hy))
    have hh' : b.smul.left (p.left (IsLocalRing.closedPoint L)) ∈ linearChart c (d.coord i) := hh
    exact (congrArg (fun q : (D ⊗ P).left ↦ b.smul.left q) hp) ▸ hh'

end LinearCharts

section ProjectiveApplication

set_option backward.isDefEq.respectTransparency false

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem fixed_points_in_affine_projective_chart
    {J : Type u} [Group.FG M]
    {X : SchemeOver k} (b : ModObj (Specs.DiagonalizableGroups.diagonalGroup k M).val.X
      (projectiveSpace k J)) (a : ModObj (Specs.DiagonalizableGroups.diagonalGroup k M).val.X X)
    (e : X ⟶ projectiveSpace k J) [IsImmersion e.left]
    (he : a.smul ≫ e = ((Specs.DiagonalizableGroups.diagonalGroup k M).val.X ◁ e) ≫ b.smul)
    {K : Type u} [Field K] [Algebra k K]
    (x : Points X (CommAlgCat.of k K)) (hx : IsFixedBy a.smul x)
    (W : (projectiveSpace k J).left.Opens) (hW : IsAffineOpen W)
    (hmem : e.left (x.left (IsLocalRing.closedPoint K)) ∈ W)
    (hpres : ∀ s : ((Specs.DiagonalizableGroups.diagonalGroup k M).val.X ⊗
      projectiveSpace k J).left,
      (snd (Specs.DiagonalizableGroups.diagonalGroup k M).val.X (projectiveSpace k J)).left s ∈ W →
        b.smul.left s ∈ W) :
    ∃ (U : SchemeOver k) (j : U ⟶ X), IsAffine U.left ∧ IsOpenImmersion j.left ∧
      x.left (IsLocalRing.closedPoint K) ∈ Set.range j.left ∧
      ∃ aU : ModObj (Specs.DiagonalizableGroups.diagonalGroup k M).val.X U,
        aU.smul ≫ j = ((Specs.DiagonalizableGroups.diagonalGroup k M).val.X ◁ j) ≫ a.smul := by
  let D := (Specs.DiagonalizableGroups.diagonalGroup k M).val.X
  let P := projectiveSpace k J
  let V := e.left ⁻¹ᵁ W
  let X' : SchemeOver k := Over.mk (V.ι ≫ X.hom)
  let Y : SchemeOver k := Over.mk (W.ι ≫ P.hom)
  let j : X' ⟶ X := Over.homMk V.ι rfl
  let jP : Y ⟶ P := Over.homMk W.ι rfl
  let : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion V.ι)
  let : Mono j := Over.mono_of_mono_left j
  let : IsOpenImmersion jP.left := inferInstanceAs (IsOpenImmersion W.ι)
  let : Mono jP := Over.mono_of_mono_left jP
  let : IsAffine Y.left := hW
  let e' : X' ⟶ Y := Over.homMk (e.left ∣_ W) (by
    change (e.left ∣_ W) ≫ (W.ι ≫ P.hom) = V.ι ≫ X.hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w e])
  let : IsImmersion e'.left := inferInstanceAs (IsImmersion (e.left ∣_ W))
  have hres : e' ≫ jP = j ≫ e := Over.OverMorphism.ext (morphismRestrict_ι e.left W)
  obtain ⟨a', ha'⟩ := restrict_action_open a V (preimage_preserved_open a b e he W hpres)
  obtain ⟨b', hb'⟩ := restrict_action_open b W hpres
  have he' : a'.smul ≫ e' = (D ◁ e') ≫ b'.smul := by
    apply (cancel_mono jP).mp
    change a'.smul ≫ e' ≫ jP = ((D ◁ e') ≫ b'.smul) ≫ jP
    rw [hres, ← Category.assoc, ha', Category.assoc, he, ← whiskerLeft_comp_assoc,
      Category.assoc (D ◁ e'), hb', ← whiskerLeft_comp_assoc, hres]
  have hxrange : Set.range x.left ⊆ Set.range j.left := by
    rintro _ ⟨q, rfl⟩
    change x.left q ∈ Set.range V.ι
    rw [Scheme.Opens.range_ι]
    have hq : q = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
    exact hq ▸ hmem
  let f := IsOpenImmersion.lift j.left x.left hxrange
  have hfac : f ≫ j.left = x.left := IsOpenImmersion.lift_fac _ _ _
  let y : Points X' (CommAlgCat.of k K) := Over.homMk f (by
    change f ≫ (j.left ≫ X.hom) = _
    rw [← Category.assoc, hfac, Over.w x])
  have hy : y ≫ j = x := Over.OverMorphism.ext hfac
  have hyfix : IsFixedBy a'.smul y := isFixedBy_of_comp_equivariant ha' (hy ▸ hx)
  obtain ⟨U, j', hAff, hOpen, hyj', aU, haU⟩ := invariant_affine_neighborhood a' b' e' he' y hyfix
  let : IsOpenImmersion j'.left := hOpen
  refine ⟨U, j' ≫ j, hAff, IsOpenImmersion.comp j'.left j.left, ?_, aU, ?_⟩
  · obtain ⟨z, hz⟩ := hyj'
    refine ⟨z, ?_⟩
    change j.left (j'.left z) = _
    rw [hz]
    exact congrArg (fun f : Points X (CommAlgCat.of k K) ↦ f.left (IsLocalRing.closedPoint K)) hy
  · rw [← Category.assoc, haU, Category.assoc, ha', ← whiskerLeft_comp_assoc]

/-- An eigenfunctional yields an invariant affine projective chart. Shrinking
inside that chart gives an invariant affine open of the immersed scheme. -/
theorem linearProjectiveInvariantAffineNeighborhoods :
    Specs.DiagonalizableFixedLocus.LinearProjectiveInvariantAffineNeighborhoods.{u} := by
  intro k M J V _ _ _ _ _ _ c ρ X T b a hb e he heq x hx t
  let : IsImmersion e.left := he
  obtain ⟨K, _, _, p, hp⟩ := exists_field_point T t
  let y := p ≫ x
  have hy : y.left (IsLocalRing.closedPoint K) = x.left t :=
    congrArg (fun t' : T.left ↦ x.left t') hp
  obtain ⟨W, hW, hmem, hpres⟩ := invariant_linearCharts c ρ b hb
    (e.left (y.left (IsLocalRing.closedPoint K)))
  rw [← hy]
  exact fixed_points_in_affine_projective_chart b a e heq y (isFixedBy_comp hx p) W hW hmem hpres

/-- The fixed scheme is smooth for a locally closed equivariant embedding. -/
theorem linearProjectivelyEmbeddedFixedLocusSmooth :
    Specs.DiagonalizableFixedLocus.LinearProjectivelyEmbeddedFixedLocusSmooth.{u} := by
  intro k M J V _ _ _ _ _ _ c ρ X Z hX b a hb e he heq i hi hrep
  let : Smooth X.hom := hX
  have hfix : IsFixedBy a.smul i := (hrep Z i).mpr ⟨𝟙 _, Category.id_comp _⟩
  exact fixedLocusSmoothOnInvariantCharts X a Z i hi hrep
    (linearProjectiveInvariantAffineNeighborhoods c ρ X Z b a hb e he heq i hfix)

private theorem projectiveSpace_properties {J : Type u} [Finite J] :
    IsSeparated (projectiveSpace k J).hom ∧ IsNoetherian (projectiveSpace k J).left := by
  let q := Proj.toSpecZero (MvPolynomial.homogeneousSubmodule J k)
  let S := ↥(MvPolynomial.homogeneousSubmodule J k 0)
  let p := Spec.map (CommRingCat.ofHom (algebraMap k S))
  let : IsScalarTower k S (MvPolynomial J k) := by
    constructor
    intro c f g
    change (c • f.val) * g = c • (f.val * g)
    exact smul_mul_assoc _ _ _
  let : Algebra.FiniteType S (MvPolynomial J k) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k _ _
  have hsurj : Function.Surjective (algebraMap k S) := by
    intro v
    have hv : v.val ∈ (1 : Submodule k (MvPolynomial J k)) := by
      rw [← MvPolynomial.homogeneousSubmodule_zero]
      exact v.property
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp hv
    exact ⟨r, Subtype.ext hr⟩
  let : LocallyOfFiniteType p := HasRingHomProperty.Spec_iff.mpr
    (RingHom.FiniteType.of_surjective (algebraMap k S) hsurj)
  let : LocallyOfFiniteType (q ≫ p) := inferInstance
  refine ⟨inferInstanceAs (IsSeparated (q ≫ p)), ?_⟩
  exact { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (q ≫ p)
          toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (q ≫ p) }

/-- The closed fixed-point functor in the locally closed projective case is
represented by a smooth scheme. -/
theorem existsLinearProjectivelyEmbeddedFixedLocus :
    Specs.DiagonalizableFixedLocus.ExistsLinearProjectivelyEmbeddedFixedLocus.{u} := by
  intro k M J V _ _ _ _ _ _ c ρ X hX b a hb e he heq
  let : Smooth X.hom := hX
  let : IsImmersion e.left := he
  obtain ⟨hsep, hnoeth⟩ := projectiveSpace_properties (k := k) (J := J)
  let : IsSeparated (projectiveSpace k J).hom := hsep
  let : IsNoetherian (projectiveSpace k J).left := hnoeth
  let : TopologicalSpace.NoetherianSpace X.left := e.left.isEmbedding.isInducing.noetherianSpace
  have hsepX : IsSeparated X.hom := by
    rw [← Over.w e]
    infer_instance
  obtain ⟨Z, i, hi, hrep⟩ := fixedPointScheme k (Specs.DiagonalizableGroups.diagonalGroup k M)
    X a hsepX inferInstance inferInstance
  exact ⟨Z, i, hi, hrep, linearProjectivelyEmbeddedFixedLocusSmooth c ρ X Z b a hb e he heq i hi hrep⟩

/-- The projective result is invariant under isomorphism of the acting group. -/
theorem splitLinearProjectivelyEmbeddedFixedLocus :
    Specs.DiagonalizableFixedLocus.SplitLinearProjectivelyEmbeddedFixedLocus.{u} := by
  intro k M J V _ _ _ _ _ _ H d c ρ X hX b a hb e he heq
  let D := (Specs.DiagonalizableGroups.diagonalGroup k M).val.X
  let : ModObj H.X X := a
  let : ModObj H.X (projectiveSpace k J) := b
  let aD := Mod.scalarRestriction d.hom.hom.hom X
  let bD := Mod.scalarRestriction d.hom.hom.hom (projectiveSpace k J)
  have heD : aD.smul ≫ e = (D ◁ e) ≫ bD.smul := by
    change ((d.hom.hom.hom ▷ X) ≫ a.smul) ≫ e =
      (D ◁ e) ≫ (d.hom.hom.hom ▷ projectiveSpace k J) ≫ b.smul
    rw [Category.assoc, heq, whisker_exchange_assoc]
  have hfixed (T : SchemeOver k) (x : T ⟶ X) :
      IsFixedBy aD.smul x ↔ IsFixedBy a.smul x :=
    isFixedBy_groupIso ((Grp.forget _).mapIso d) a.smul x
  constructor
  · intro Z i hi hrep
    exact linearProjectivelyEmbeddedFixedLocusSmooth c ρ X Z bD aD hb e he heD i hi
      (fun T x ↦ (hfixed T x).trans (hrep T x))
  · obtain ⟨Z, i, hi, hrep, hs⟩ := existsLinearProjectivelyEmbeddedFixedLocus c ρ X bD aD hb e he heD
    exact ⟨Z, i, hi, fun T x ↦ (hfixed T x).symm.trans (hrep T x), hs⟩

end ProjectiveApplication

set_option backward.isDefEq.respectTransparency false in
theorem splitDiagonalizableFixedLocusSmooth :
    Specs.DiagonalizableFixedLocus.SplitDiagonalizableFixedLocusSmooth.{u} := by
  intro k M _ _ _ H e X _ _ a Z i hi hrep
  let : ModObj H.X X := a
  let aD := Mod.scalarRestriction e.hom.hom.hom X
  apply affineFixedLocusSmooth (M := M) X aD Z i hi
  intro T x
  change IsFixedBy ((e.hom.hom.hom ▷ X) ≫ a.smul) x ↔ _
  exact (isFixedBy_groupIso ((Grp.forget _).mapIso e) a.smul x).trans (hrep T x)

theorem splitTorusFixedLocusSmooth :
    Specs.DiagonalizableFixedLocus.SplitTorusFixedLocusSmooth.{u} := by
  intro k J _ _ H e X _ _ a Z i hi hrep
  obtain ⟨f⟩ := DiagonalizableGroups.diagonalIntegerPowers k J
  exact splitDiagonalizableFixedLocusSmooth H (f ≪≫ e) X a Z i hi hrep

theorem closedDiagonalizableFixedLocusSmooth :
    Specs.DiagonalizableFixedLocus.ClosedDiagonalizableFixedLocusSmooth.{u} := by
  intro k M _ _ _ D d hd X _ _ a Z i hi hrep
  obtain ⟨N, ⟨f, _⟩, _⟩ := (DiagonalizableGroups.diagonalClosedSubgroups k M D d).mp hd
  exact splitDiagonalizableFixedLocusSmooth (M := M ⧸ N) D f.symm X a Z i hi hrep

theorem existsAffineFixedLocus : Specs.DiagonalizableFixedLocus.ExistsAffineFixedLocus.{u} := by
  intro k M _ _ _ X _ _ a
  let D := Specs.DiagonalizableGroups.diagonalGroup k M
  obtain ⟨Z, i, hi, hrep⟩ := fixedPointScheme k D X a inferInstance inferInstance inferInstance
  exact ⟨Z, i, hi, hrep, affineFixedLocusSmooth X a Z i hi hrep⟩

private abbrev conjugationAction {H G : Specs.GroupScheme k} (d : H ⟶ G) : ModObj H.X G.X where
  smul := (d.hom.hom ▷ G.X) ≫ GrpObj.conj G.X
  one_smul := by
    change η[H.X] ▷ G.X ≫ (d.hom.hom ▷ G.X) ≫ GrpObj.conj G.X = (λ_ G.X).hom
    rw [← comp_whiskerRight_assoc, IsMonHom.one_hom]
    have h : fst (𝟙_ (SchemeOver k)) G.X ≫ η[G.X] = (1 : 𝟙_ (SchemeOver k) ⊗ G.X ⟶ G.X) := by
      rw [CategoryTheory.Hom.one_def, toUnit_unique (fst _ _)]
    simp [GrpObj.conj, MonObj.comp_mul, GrpObj.comp_inv, h,
      CartesianMonoidalCategory.leftUnitor_hom]
  mul_smul := by
    change μ[H.X] ▷ G.X ≫ (d.hom.hom ▷ G.X) ≫ GrpObj.conj G.X =
      (α_ H.X H.X G.X).hom ≫ (H.X ◁ ((d.hom.hom ▷ G.X) ≫ GrpObj.conj G.X)) ≫
        (d.hom.hom ▷ G.X) ≫ GrpObj.conj G.X
    have hm : (d.hom.hom ⊗ₘ d.hom.hom) ≫ μ[G.X] =
        (fst H.X H.X ≫ d.hom.hom) * (snd H.X H.X ≫ d.hom.hom) := by
      rw [CategoryTheory.Hom.mul_def]
      congr 1
    rw [← comp_whiskerRight_assoc, IsMonHom.mul_hom, hm]
    simp [GrpObj.conj, MonObj.comp_mul, GrpObj.comp_inv, mul_assoc]

private theorem isFixedBy_conjugation_iff {H G : Specs.GroupScheme k} (d : H ⟶ G)
    {T : SchemeOver k} (p : T ⟶ G.X) : IsFixedBy (conjugationAction d).smul p ↔ Centralizes d p := by
  let x := fst H.X T ≫ d.hom.hom
  let y := snd H.X T ≫ p
  have lhs : (H.X ◁ p) ≫ (conjugationAction d).smul = x * y * x⁻¹ := by
    change (H.X ◁ p) ≫ (d.hom.hom ▷ G.X) ≫ GrpObj.conj G.X = x * y * x⁻¹
    simp [GrpObj.conj, MonObj.comp_mul, GrpObj.comp_inv, x, y]
  rw [IsFixedBy, lhs]
  change x * y * x⁻¹ = y ↔ y * x * y⁻¹ = x
  rw [mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]
  exact eq_comm

theorem diagonalizableCentralizerSmooth :
    Specs.DiagonalizableFixedLocus.DiagonalizableCentralizerSmooth.{u} := by
  intro k M _ _ _ G _ D d hd
  obtain ⟨C, hC⟩ := centralizerScheme k G D
  let : IsAffine G.val.X.left := G.property.1
  refine ⟨C, hC, ?_⟩
  apply closedDiagonalizableFixedLocusSmooth D.group d hd G.val.X (conjugationAction D.inclusion)
    C.group.X C.inclusion.hom.hom C.isClosedImmersion
  intro T p
  exact (isFixedBy_conjugation_iff D.inclusion p).trans (hC T p)

end
end LinearAlgebraicGroups.DiagonalizableFixedLocus
