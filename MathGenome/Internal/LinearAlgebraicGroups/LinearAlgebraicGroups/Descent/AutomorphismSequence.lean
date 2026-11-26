import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AutomorphismSequence
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.SchemeCentre
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.NormalAffineQuotient
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Forms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeBasedAction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeBorelAlignment
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeTorusAlignment
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SchemeCentre
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedUniqueness
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u v w z

namespace LinearAlgebraicGroups.Descent.AutomorphismSequence

open LinearAlgebraicGroups.Specs LinearAlgebraicGroups.Specs.AutomorphismSequence Coalgebra
open Fppf (schemeTopology IsFppf)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private theorem transportHom {C : Type*} [Category C] {X Y X' Y' : C}
    (e : X = X') (d : Y = Y') (f : X ⟶ Y) :
    (show X' ⟶ Y' from e ▸ d ▸ f) = eqToHom e.symm ≫ f ≫ eqToHom d := by
  subst X'
  subst Y'
  simp

private theorem pinnedLifts : PinnedLifts.{u} := by
  intro k _ A P
  obtain ⟨D, F, hObj, hMap, hEq, _⟩ :=
    LinearAlgebraicGroups.Classification.PinnedEquivalence.pinnedEquivalence.1 A
  let : F.IsEquivalence := hEq
  have hAction (P Q : Pinning.PinnedGroup A) (f : P ⟶ Q) :
      let e : Pinning.BasedIso (D P).toBased (D Q).toBased :=
        eqToHom (hObj P).symm ≫ F.map f ≫ eqToHom (hObj Q)
      (∀ χ : CharacterDescent.Character P.pair.T.group, e.val.weightEquiv (Additive.ofMul χ) =
        Additive.ofMul (Pinning.transportCharacter f.torus χ)) ∧
      (∀ c : CharacterDescent.Cocharacter Q.pair.T.group, e.val.coweightEquiv (Additive.ofMul c) =
        Additive.ofMul (c ≫ f.torus.inv)) := by
    dsimp only
    rw [← transportHom (hObj P) (hObj Q) (F.map f)]
    exact hMap P Q f
  let e := Aut.autMulEquivOfIso (eqToIso (hObj P))
  let l := (F.asEquivalence.fullyFaithfulFunctor.autMulEquivOfFullyFaithful P).symm
  refine ⟨D P, e.symm.trans l, ?_⟩
  intro d
  have hd : eqToHom (hObj P).symm ≫ F.map (l (e.symm d)).asIso.hom ≫ eqToHom (hObj P) =
      d.asIso.hom := by
    have h : Functor.mapAut P F (l (e.symm d)) = e.symm d := l.symm.apply_symm_apply _
    have h' := congrArg (fun a => a.asIso.hom) (e.apply_symm_apply d)
    rw [show F.map (l (e.symm d)).asIso.hom = (e.symm d).asIso.hom from
      congrArg (fun a => a.asIso.hom) h]
    change ((eqToIso (hObj P)).symm ≪≫ (e.symm d).asIso ≪≫ eqToIso (hObj P)).hom =
      d.asIso.hom at h'
    simpa only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv, Category.assoc] using h'
  have h := hAction P P ((l (e.symm d)).asIso.hom)
  dsimp only at h
  rw [hd] at h
  exact h

section MonomialCoefficients

variable {R M : Type*} [CommRing R]

private theorem tensor_coeff (x y : MonoidAlgebra R M) (i j : M) :
    (MonoidAlgebra.tensorEquiv R (x ⊗ₜ[R] y)).coeff (i, j) = x.coeff i * y.coeff j := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp [TensorProduct.add_tmul, add_mul]
  | single m r =>
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => simp [TensorProduct.tmul_add, mul_add]
    | single n s =>
      rw [MonoidAlgebra.tensorEquiv_single_tmul_single]
      classical
      simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply, Prod.mk.injEq]
      by_cases hm : m = i <;> by_cases hn : n = j <;> simp [hm, hn]

private theorem comul_coeff (x : MonoidAlgebra R M) (i j : M) [DecidableEq M] :
    (MonoidAlgebra.tensorEquiv R (comul (R := R) x)).coeff (i, j) =
      if i = j then x.coeff i else 0 := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy]
    by_cases h : i = j <;> simp [h]
  | single m r =>
    rw [MonoidAlgebra.comul_single]
    change (MonoidAlgebra.tensorEquiv R (MonoidAlgebra.single m 1 ⊗ₜ[R]
      MonoidAlgebra.single m r)).coeff (i, j) = _
    rw [MonoidAlgebra.tensorEquiv_single_tmul_single, one_mul]
    simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply, Prod.mk.injEq]
    by_cases hi : m = i <;> by_cases hj : m = j
    · subst i; subst j; simp
    · subst i; simp [hj]
    · subst j; simp [hi]
    · simp [hi, hj]
/-- Over any commutative ring the coefficients of a group-like element in a group
algebra are pairwise orthogonal idempotents. -/
theorem groupLike_coeff {x : MonoidAlgebra R M} (hx : IsGroupLikeElem R x) :
    (∀ i, x.coeff i * x.coeff i = x.coeff i) ∧
      (∀ i j, i ≠ j → x.coeff i * x.coeff j = 0) := by
  classical
  have eqn (i j : M) := tensor_coeff x x i j
  simp_rw [← hx.comul_eq_tmul_self, comul_coeff] at eqn
  exact ⟨fun i => (eqn i i).symm.trans (by simp),
    fun i j h => (eqn i j).symm.trans (by simp [h])⟩

private theorem counit_eq_sum (x : MonoidAlgebra R M) :
    counit (R := R) x = ∑ m ∈ x.coeff.support, x.coeff m := by
  classical
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single x]
  simp [Finsupp.sum]

theorem existsUnique_coeff_not_mem {x : MonoidAlgebra R M} (hx : IsGroupLikeElem R x)
    (p : PrimeSpectrum R) : ∃! i, x.coeff i ∉ p.asIdeal := by
  classical
  have hex : ∃ i, x.coeff i ∉ p.asIdeal := by
    by_contra! h
    have hs : counit (R := R) x ∈ p.asIdeal := by
      rw [counit_eq_sum]
      exact p.asIdeal.sum_mem fun i _ => h i
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem p.asIdeal
      (hx.counit_eq_one ▸ hs) isUnit_one)
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, hi, fun j hj => ?_⟩
  by_contra h
  have hz := (groupLike_coeff hx).2 i j (Ne.symm h)
  have hp : x.coeff i * x.coeff j ∈ p.asIdeal := hz ▸ p.asIdeal.zero_mem
  exact (p.isPrime.mem_or_mem hp).elim hi hj

/-- On the spectrum of the scalar ring a group-like element selects a locally
constant monomial, using its unique coefficient that is a unit at each prime. -/
noncomputable def groupLikeMonomial {x : MonoidAlgebra R M} (hx : IsGroupLikeElem R x) :
    LocallyConstant (PrimeSpectrum R) M where
  toFun p := (existsUnique_coeff_not_mem hx p).choose
  isLocallyConstant := IsLocallyConstant.iff_isOpen_fiber.2 fun i => by
    convert PrimeSpectrum.isOpen_basicOpen (a := x.coeff i) using 1
    ext p
    rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
    change (existsUnique_coeff_not_mem hx p).choose = i ↔ x.coeff i ∉ p.asIdeal
    refine ⟨fun h => h ▸ (existsUnique_coeff_not_mem hx p).choose_spec.1, ?_⟩
    intro hi
    exact ((existsUnique_coeff_not_mem hx p).choose_spec.2 _ hi).symm


variable [Monoid M]

/-- A group-like element specializes at each prime to the monomial selected
by its unique nonzero coefficient. -/
theorem groupLike_specialize {x : MonoidAlgebra R M} (hx : IsGroupLikeElem R x)
    (p : PrimeSpectrum R) :
    (MonoidAlgebra.mapRingHom M (Ideal.Quotient.mk p.asIdeal)) x =
      MonoidAlgebra.single (groupLikeMonomial hx p) 1 := by
  classical
  let m := groupLikeMonomial hx p
  have hm : x.coeff m ∉ p.asIdeal := (existsUnique_coeff_not_mem hx p).choose_spec.1
  let q := Ideal.Quotient.mk p.asIdeal
  let := p.isPrime
  have he : q (x.coeff m) = 1 := by
    have hn : q (x.coeff m) ≠ 0 :=
      fun hz => hm (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    have hs : q (x.coeff m) * q (x.coeff m) = q (x.coeff m) := by
      rw [← map_mul, (groupLike_coeff hx).1]
    have hz : q (x.coeff m) * (q (x.coeff m) - 1) = 0 := by
      rw [mul_sub, mul_one, hs, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hn)
  ext i
  rw [MonoidAlgebra.coeff_mapRingHom]
  change q (x.coeff i) = (MonoidAlgebra.single m 1).coeff i
  by_cases hi : m = i
  · subst i
    simpa using he
  · have hz : x.coeff i ∈ p.asIdeal := by
      by_contra hn
      exact hi ((existsUnique_coeff_not_mem hx p).choose_spec.2 i hn).symm
    simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply, hi, ite_false]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hz

/-- The local monomial of a product is the product of its local monomials. -/
theorem groupLikeMonomial_mul {x y : MonoidAlgebra R M}
    (hx : IsGroupLikeElem R x) (hy : IsGroupLikeElem R y) :
    groupLikeMonomial (hx.mul hy) = groupLikeMonomial hx * groupLikeMonomial hy := by
  ext p
  let := p.isPrime
  apply MonoidAlgebra.single_left_injective (R := R ⧸ p.asIdeal) one_ne_zero
  change MonoidAlgebra.single (groupLikeMonomial (hx.mul hy) p) (1 : R ⧸ p.asIdeal) =
    MonoidAlgebra.single (groupLikeMonomial hx p * groupLikeMonomial hy p) 1
  rw [← groupLike_specialize (hx.mul hy) p, map_mul, groupLike_specialize hx p, groupLike_specialize hy p]
  simp

end MonomialCoefficients

section AutomorphismSheaf

variable {k : Type u} [Field k]

/-- Isomorphisms of relative group functors glue by gluing their two directions. -/
theorem automorphisms_isSheaf (G : GroupScheme k) : IsGroupSheaf (automorphisms G) := by
  let J := Fppf.schemeTopology k
  let P := yonedaGrp.obj G
  have hP : Presheaf.IsSheaf J P := by
    apply Presheaf.isSheaf_of_isSheaf_comp J P (forget GrpCat)
    change Presheaf.IsSheaf J (yoneda.obj G.X)
    exact (isSheaf_iff_isSheaf_of_type _ _).2
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := J) (yoneda.obj G.X))
  let M := presheafHom P P
  have hM : Presheaf.IsSheaf J M := hP.hom P
  intro S V hV a ha
  let homs : Presieve.FamilyOfElements M V.arrows := fun _ b hb => (a b hb).asIso.hom
  let invs : Presieve.FamilyOfElements M V.arrows := fun _ b hb => (a b hb).asIso.inv
  have homsCompatible : homs.Compatible := by
    intro U₁ U₂ W b₁ b₂ f₁ f₂ h₁ h₂ eq
    exact congrArg (fun x : RelativeAut G W => x.asIso.hom) (ha b₁ b₂ h₁ h₂ eq)
  have invsCompatible : invs.Compatible := by
    intro U₁ U₂ W b₁ b₂ f₁ f₂ h₁ h₂ eq
    exact congrArg (fun x : RelativeAut G W => x.asIso.inv) (ha b₁ b₂ h₁ h₂ eq)
  have gluing := hM.isSheafFor V hV
  obtain ⟨f, hf, _⟩ := gluing homs homsCompatible
  obtain ⟨g, hg, _⟩ := gluing invs invsCompatible
  have comp_eq (x y : M.obj (op S))
      (h : ∀ ⦃U : SchemeOver k⦄ (b : U ⟶ S), V b →
        M.map b.op x ≫ M.map b.op y = 𝟙 (relativePoints G U)) :
      x ≫ y = 𝟙 (relativePoints G S) := by
    apply gluing.isSeparatedFor.ext
    intro U b hb
    exact h b hb
  let fg : RelativeAut G S := Aut.of
    { hom := f
      inv := g
      hom_inv_id := comp_eq f g fun _ b hb => by rw [hf b hb, hg b hb]; exact (a b hb).asIso.hom_inv_id
      inv_hom_id := comp_eq g f fun _ b hb => by rw [hg b hb, hf b hb]; exact (a b hb).asIso.inv_hom_id }
  refine ⟨fg, ?_, ?_⟩
  · intro U b hb
    apply Aut.ext
    apply Iso.ext
    exact hf b hb
  · intro e he
    apply Aut.ext
    apply Iso.ext
    apply gluing.isSeparatedFor.ext
    intro U b hb
    exact (congrArg (fun x : RelativeAut G U => x.asIso.hom) (he b hb)).trans (hf b hb).symm

end AutomorphismSheaf

section InnerAutomorphisms

open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

variable {k : Type u} [Field k]

theorem innerAut_eq_one_iff {G : GroupScheme k} {S : SchemeOver k} (s : S ⟶ G.X) :
    innerAut s = 1 ↔ Centralizes (𝟙 G) s := by
  rw [centralizes_iff]
  constructor
  · intro h U b x
    have h' := congrArg (fun f : RelativeAut G S =>
      (f.asIso.hom.app (op (Over.mk b))).hom x) h
    change (b ≫ s) * x * (b ≫ s)⁻¹ = x at h'
    change Commute (b ≫ s) (x ≫ 𝟙 G.X)
    rw [Category.comp_id]
    exact mul_inv_eq_iff_eq_mul.mp h'
  · intro h
    apply Aut.ext
    apply Iso.ext
    apply NatTrans.ext
    funext U
    apply GrpCat.ext
    intro x
    change U.unop.left ⟶ G.X at x
    change (U.unop.hom ≫ s) * x * (U.unop.hom ≫ s)⁻¹ = x
    apply mul_inv_eq_iff_eq_mul.mpr
    exact (h U.unop.left U.unop.hom x).eq

private theorem centre_normal {G : GroupScheme k} (Z : ClosedSubgroup G)
    (hZ : RepresentsSubgroup Z (fun _ z ↦ Centralizes (𝟙 G) z)) : IsNormalSubgroup Z.inclusion := by
  let Y := G.X ⊗ Z.group.X
  let z : Y ⟶ G.X := snd G.X Z.group.X ≫ Z.inclusion.hom.hom
  let g : Y ⟶ G.X := fst G.X Z.group.X
  have hz : Centralizes (𝟙 G) z := (hZ Y z).2 ⟨snd _ _, rfl⟩
  have commute : Commute z g := by
    simpa using (centralizes_iff (𝟙 G) z).mp hz Y (𝟙 Y) g
  have hcz : subgroupConjugation Z.inclusion = z := by
    change g * z * g⁻¹ = z
    exact mul_inv_eq_iff_eq_mul.mpr commute.symm.eq
  refine (hZ Y _).mp ?_
  rwa [hcz]

/-- The affine quotient by the actual scheme centre. This works also for
the nonsplit forms and retains all non-smooth central factors. -/
theorem adjointQuotient_exists (G : AffineAlgebraicGroup k) : Nonempty (AdjointQuotient G) := by
  let whole : ClosedSubgroup G.val := ⟨G.val, 𝟙 _, by change IsClosedImmersion (𝟙 _); infer_instance⟩
  obtain ⟨Z, hZ⟩ := LinearAlgebraicGroups.centralizerScheme k G whole
  change RepresentsSubgroup Z (fun _ z ↦ Centralizes (𝟙 G.val) z) at hZ
  obtain ⟨L, f, Q, q, i, _, hq, hqi, _, _⟩ :=
    LinearAlgebraicGroups.normalAffineQuotient G Z (centre_normal Z hZ)
  exact ⟨⟨Z, hZ, Q, q, ⟨hqi.2.1, hqi.2.2.1, hqi.2.2.2.1⟩, hq⟩⟩

end InnerAutomorphisms


section Descent

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
variable {F G H : Cᵒᵖ ⥤ GrpCat.{z}}

private theorem groupSheaf_separated (hH : Presieve.IsSheaf J (H ⋙ forget GrpCat))
    {U : C} {S : Sieve U} (hS : S ∈ J U) (x y : H.obj (op U))
    (h : ∀ ⦃V : C⦄ (a : V ⟶ U), S a → H.map a.op x = H.map a.op y) :
    x = y :=
  (hH _ hS).isSeparatedFor.ext h

/-- A morphism to a sheaf descends along a locally surjective map if its
values agree on pairs of lifts. -/
private theorem descends_locallySurjective (p : F ⟶ G) (q : F ⟶ H)
    (hp : Presheaf.IsLocallySurjective J p)
    (hH : Presieve.IsSheaf J (H ⋙ forget GrpCat))
    (h : ∀ (U : Cᵒᵖ) (x y : F.obj U), p.app U x = p.app U y → q.app U x = q.app U y) :
    ∃ r : G ⟶ H, p ≫ r = q := by
  classical
  let := hp
  have exists_value (U : C) (g : G.obj (op U)) :
      ∃ z : H.obj (op U), ∀ ⦃V : C⦄ (a : V ⟶ U) (x : F.obj (op V)),
        p.app _ x = G.map a.op g → H.map a.op z = q.app _ x := by
    let S := Presheaf.imageSieve p g
    let values : Presieve.FamilyOfElements (H ⋙ forget GrpCat) S.arrows :=
      fun _ a ha => q.app _ (Presheaf.localPreimage p g a ha)
    have compatible : values.Compatible := by
      intro V₁ V₂ W b₁ b₂ a₁ a₂ ha₁ ha₂ he
      change H.map b₁.op (q.app _ _) = H.map b₂.op (q.app _ _)
      rw [← NatTrans.naturality_apply q, ← NatTrans.naturality_apply q]
      apply h
      rw [NatTrans.naturality_apply p, NatTrans.naturality_apply p,
        Presheaf.app_localPreimage, Presheaf.app_localPreimage,
        ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, he]
    obtain ⟨z, hz, _⟩ := hH S (Presheaf.imageSieve_mem J p g) values compatible
    refine ⟨z, ?_⟩
    intro V a x hx
    have ha : S a := ⟨x, hx⟩
    have hz' : H.map a.op z = q.app _ (Presheaf.localPreimage p g a ha) := hz a ha
    exact hz'.trans (h _ _ _ ((Presheaf.app_localPreimage p g a ha).trans hx.symm))
  let value (U : Cᵒᵖ) (g : G.obj U) : H.obj U := (exists_value U.unop g).choose
  have value_lift {U V : C} (a : V ⟶ U) (g : G.obj (op U)) (x : F.obj (op V))
      (hx : p.app _ x = G.map a.op g) : H.map a.op (value _ g) = q.app _ x :=
    (exists_value U g).choose_spec a x hx
  let r : G ⟶ H :=
    { app U := GrpCat.ofHom {
        toFun := value U
        map_one' := by
          have hv := value_lift (𝟙 U.unop) 1 1 (by simp)
          simpa using hv
        map_mul' g g' := by
          change G.obj (op U.unop) at g g'
          refine groupSheaf_separated hH (J.intersection_covering
            (Presheaf.imageSieve_mem J p g) (Presheaf.imageSieve_mem J p g')) _ _ ?_
          rintro V a ⟨⟨x, hx⟩, ⟨x', hx'⟩⟩
          rw [map_mul, value_lift a g x hx, value_lift a g' x' hx',
            value_lift a (g * g') (x * x') (by rw [map_mul, map_mul, hx, hx']), map_mul] }
      naturality U V a := by
        apply GrpCat.ext
        intro g
        change value V (G.map a g) = H.map a (value U g)
        refine groupSheaf_separated hH (Presheaf.imageSieve_mem J p (G.map a g)) _ _ ?_
        rintro W b ⟨x, hx⟩
        have hx' : p.app (op W) x = G.map (b ≫ a.unop).op g := by
          simpa only [op_comp, Quiver.Hom.op_unop, Functor.map_comp_apply] using hx
        rw [value_lift b (G.map a g) x hx, ← Functor.map_comp_apply]
        simpa only [op_comp, Quiver.Hom.op_unop] using (value_lift (b ≫ a.unop) g x hx').symm }
  refine ⟨r, ?_⟩
  apply NatTrans.ext
  funext U
  apply GrpCat.ext
  intro x
  change value U (p.app U x) = q.app U x
  have hv := value_lift (𝟙 U.unop) (p.app U x) x (by simp)
  simpa using hv

/-- Maps to a sheaf agree as soon as they agree on local lifts. -/
private theorem hom_ext_of_locallySurjective (p : F ⟶ G)
    (hp : Presheaf.IsLocallySurjective J p)
    (hH : Presieve.IsSheaf J (H ⋙ forget GrpCat))
    {f g : G ⟶ H} (h : p ≫ f = p ≫ g) : f = g := by
  let := hp
  apply NatTrans.ext
  funext U
  apply GrpCat.ext
  intro x
  refine groupSheaf_separated hH (Presheaf.imageSieve_mem J p x) _ _ ?_
  rintro V a ⟨y, hy⟩
  rw [← NatTrans.naturality_apply f, ← NatTrans.naturality_apply g, ← hy]
  exact ConcreteCategory.congr_hom (congrArg (fun q => q.app (op V)) h) y

/-- Compatible changes of trivialization descend along locally surjective projections. -/
private theorem descends_iso_of_locallySurjective
    {F' G' : Cᵒᵖ ⥤ GrpCat.{z}} (p : F ⟶ G) (p' : F' ⟶ G') (e : F ≅ F')
    (hp : Presheaf.IsLocallySurjective J p) (hp' : Presheaf.IsLocallySurjective J p')
    (hG : Presieve.IsSheaf J (G ⋙ forget GrpCat))
    (hG' : Presieve.IsSheaf J (G' ⋙ forget GrpCat))
    (h : ∀ (U : Cᵒᵖ) (x y : F.obj U),
      p.app U x = p.app U y ↔ p'.app U (e.hom.app U x) = p'.app U (e.hom.app U y)) :
    ∃ a : G ≅ G', p ≫ a.hom = e.hom ≫ p' := by
  have agrees U (x y : F.obj U) (he : p.app U x = p.app U y) :
      (e.hom ≫ p').app U x = (e.hom ≫ p').app U y := (h U x y).1 he
  have agrees' U (x y : F'.obj U) (he : p'.app U x = p'.app U y) :
      (e.inv ≫ p).app U x = (e.inv ≫ p).app U y := by
    apply (h U (e.inv.app U x) (e.inv.app U y)).2
    have cancel (z : F'.obj U) : e.hom.app U (e.inv.app U z) = z := by
      have eq := congrArg (fun a => a.app U) e.inv_hom_id
      exact ConcreteCategory.congr_hom eq z
    rwa [cancel, cancel]
  obtain ⟨a, ha⟩ := descends_locallySurjective p (e.hom ≫ p') hp hG' agrees
  obtain ⟨b, hb⟩ := descends_locallySurjective p' (e.inv ≫ p) hp' hG agrees'
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · apply hom_ext_of_locallySurjective p hp hG
    rw [← Category.assoc, ha, Category.assoc, hb, Iso.hom_inv_id_assoc, Category.comp_id]
  · apply hom_ext_of_locallySurjective p' hp' hG'
    rw [← Category.assoc, hb, Category.assoc, ha, Iso.inv_hom_id_assoc, Category.comp_id]

end Descent

section ConstantSections

variable {k : Type u} [Field k]

private theorem openCover_mem {S : SchemeOver k} (U : S.left.OpenCover) :
    Sieve.ofArrows (fun i => Over.mk (U.f i ≫ S.hom))
      (fun i => (Over.homMk (U.f i) : Over.mk (U.f i ≫ S.hom) ⟶ S)) ∈ schemeTopology k S := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage _
    U.mem_grothendieckTopology

private theorem fppf_empty_cover (S : SchemeOver k) [IsEmpty S.left] :
    (⊥ : Sieve S) ∈ schemeTopology k S := by
  rw [GrothendieckTopology.mem_over_iff, OrderIso.map_bot]
  exact Scheme.bot_mem_grothendieckTopology _

/-- Locally constant maps into a discrete group satisfy fppf descent. -/
theorem constantGroup_isSheaf (D : Type u) [Group D] :
    IsGroupSheaf (constantGroup (k := k) D) := by
  let : TopologicalSpace D := ⊥
  let : DiscreteTopology D := discreteTopology_bot D
  let F := (Over.forget (Spec (CommRingCat.of k))).op ⋙ continuousMapPresheaf D
  have hF : Presieve.IsSheaf (schemeTopology k) F := by
    exact (Over.forget (Spec (CommRingCat.of k))).op_comp_isSheaf_of_types
      (schemeTopology k) Scheme.fppfTopology
      ⟨continuousMapPresheaf D, (isSheaf_fpqcTopology_continuousMapPresheaf D).of_le
        Scheme.fppfTopology_le_fpqcTopology⟩
  let e (S : (SchemeOver k)ᵒᵖ) :
      (constantGroup (k := k) D ⋙ forget GrpCat).obj S ≃ (F ⋙ uliftFunctor.{u+1,u}).obj S :=
    { toFun := fun f => ⟨f.down.toContinuousMap⟩
      invFun := fun f =>
        let f' : C(S.unop.left, D) := f.down
        ⟨⟨f'.toFun, (IsLocallyConstant.iff_continuous f'.toFun).2 f'.continuous⟩⟩
      left_inv := by intro f; rfl
      right_inv := by intro f; rfl }
  let i : constantGroup (k := k) D ⋙ forget GrpCat ≅ F ⋙ uliftFunctor.{u+1,u} :=
    NatIso.ofComponents (fun S => equivEquivIso (e S)) (by intro S T a; rfl)
  exact Presieve.isSheaf_iso _ i.symm ((Presieve.isSheaf_comp_uliftFunctor_iff _).2 hF)

private abbrev copiesOfBase (D : Type u) : D → Scheme.{u} :=
  fun _ => Spec (CommRingCat.of k)

private theorem constantScheme_etale (D : Type u) : Etale (constantScheme (k := k) D).hom := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Etale) (sigmaOpenCover _)]
  intro d
  change Etale (Sigma.ι (copiesOfBase (k := k) D) d ≫
    Sigma.desc (fun _ : D => 𝟙 (Spec (CommRingCat.of k))))
  rw [Sigma.ι_comp_desc]
  infer_instance

private theorem constantScheme_label_eq {D : Type u}
    (x : (constantScheme (k := k) D).left) (d : D) :
    ((sigmaMk (copiesOfBase (k := k) D)).symm x).1 = d ↔
      x ∈ Set.range (Sigma.ι (copiesOfBase (k := k) D) d) := by
  let e := sigmaMk (copiesOfBase (k := k) D)
  constructor
  · intro h
    change (e.symm x).1 = d at h
    rcases eq : e.symm x with ⟨i, y⟩
    rw [eq] at h
    change i = d at h
    subst i
    have hy := e.apply_symm_apply x
    rw [eq] at hy
    exact ⟨y, (sigmaMk_mk _ d y).symm.trans hy⟩
  · rintro ⟨y, rfl⟩
    rw [← sigmaMk_mk, Homeomorph.symm_apply_apply]

private def constantScheme_label (D : Type u) :
    LocallyConstant (constantScheme (k := k) D).left D :=
  ⟨fun x => ((sigmaMk (copiesOfBase (k := k) D)).symm x).1,
    IsLocallyConstant.iff_isOpen_fiber.mpr (fun d => by
      let l (x : (constantScheme (k := k) D).left) :=
        ((sigmaMk (copiesOfBase (k := k) D)).symm x).1
      have h : l ⁻¹' ({d} : Set D) = Set.range (Sigma.ι (copiesOfBase (k := k) D) d) :=
        Set.ext (fun x => constantScheme_label_eq x d)
      change IsOpen (l ⁻¹' ({d} : Set D))
      rw [h]
      exact (Sigma.ι (copiesOfBase (k := k) D) d).isOpenEmbedding.isOpen_range)⟩

private def constantScheme_labelMap {D : Type u} {Y : SchemeOver k}
    (f : Y ⟶ constantScheme D) : LocallyConstant Y.left D :=
  (constantScheme_label D).comap ⟨f.left, f.left.continuous⟩

private theorem constantScheme_labelMap_injective {D : Type u} (Y : SchemeOver k) :
    Function.Injective (constantScheme_labelMap (D := D) (Y := Y)) := by
  intro f g h
  apply Over.OverMorphism.ext
  apply Scheme.hom_ext_of_forall
  intro x
  let d := constantScheme_labelMap f x
  let U : Y.left.Opens :=
    ⟨{y | constantScheme_labelMap f y = d}, (constantScheme_labelMap f).isLocallyConstant.isOpen_fiber d⟩
  refine ⟨U, rfl, ?_⟩
  have lift (a : Y ⟶ constantScheme D)
      (ha : constantScheme_labelMap a = constantScheme_labelMap f) :
      U.ι ≫ a.left = (U.ι ≫ Y.hom) ≫ Sigma.ι (copiesOfBase (k := k) D) d := by
    let j := Sigma.ι (copiesOfBase (k := k) D) d
    have hRange : Set.range (U.ι ≫ a.left) ⊆ Set.range j := by
      rintro _ ⟨y, rfl⟩
      exact (constantScheme_label_eq _ _).mp
        (congrArg (fun l : LocallyConstant Y.left D => l y.val) ha |>.trans y.property)
    let b := IsOpenImmersion.lift j (U.ι ≫ a.left) hRange
    have hb : b ≫ j = U.ι ≫ a.left := IsOpenImmersion.lift_fac j _ hRange
    have hbase : j ≫ (constantScheme (k := k) D).hom = 𝟙 _ := Sigma.ι_comp_desc _ _
    have he : b = U.ι ≫ Y.hom := by
      calc
        b = (b ≫ j) ≫ (constantScheme (k := k) D).hom := by
          rw [Category.assoc, hbase, Category.comp_id]
        _ = U.ι ≫ Y.hom := by rw [hb, Category.assoc, Over.w a]
    rw [← hb, he]
  exact (lift f rfl).trans (lift g h.symm).symm

private theorem constantScheme_labelMap_surjective {D : Type u} (Y : SchemeOver k) :
    Function.Surjective (constantScheme_labelMap (D := D) (Y := Y)) := by
  intro l
  let opens (d : D) : Y.left.Opens := ⟨{x | l x = d}, l.isLocallyConstant.isOpen_fiber d⟩
  let C := Y.left.openCoverOfIsOpenCover opens (by
    show iSup opens = ⊤
    apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨l x, rfl⟩)
  let f (d : D) := C.f d ≫ Y.hom ≫ Sigma.ι (copiesOfBase (k := k) D) d
  have hf (i j : D) : pullback.fst (C.f i) (C.f j) ≫ f i =
      pullback.snd _ _ ≫ f j := by
    by_cases h : i = j
    · subst j
      simp only [f, pullback.condition_assoc]
    · have : IsEmpty (pullback (C.f i) (C.f j) : Scheme) := by
        constructor
        intro x
        let xi := pullback.fst (C.f i) (C.f j) x
        let xj := pullback.snd (C.f i) (C.f j) x
        have he : (C.f i) xi = (C.f j) xj :=
          congrArg (fun a : pullback (C.f i) (C.f j) ⟶ Y.left => a x) pullback.condition
        exact h (xi.property.symm.trans ((congrArg (fun y => l y) he).trans xj.property))
      exact isInitialOfIsEmpty.hom_ext _ _
  let g := C.glueMorphisms f hf
  have hg : g ≫ (constantScheme (k := k) D).hom = Y.hom := by
    apply C.hom_ext
    intro d
    rw [C.ι_glueMorphisms_assoc]
    simp [f, constantScheme]
  refine ⟨Over.homMk g hg, ?_⟩
  apply LocallyConstant.ext
  intro x
  obtain ⟨d, y, rfl⟩ := C.exists_eq x
  have he : (constantScheme_labelMap (Over.homMk g hg)) (C.f d y) = d := by
    apply (constantScheme_label_eq _ _).mpr
    refine ⟨Y.hom (C.f d y), ?_⟩
    change _ = (C.f d ≫ g) y
    rw [C.ι_glueMorphisms]
    rfl
  exact he.trans y.property.symm

private def constantGroupSmall (D : Type u) [Group D] : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{u} where
  obj S := GrpCat.of (LocallyConstant S.unop.left D)
  map a := GrpCat.ofHom
    { toFun := fun x => x.comap ⟨a.unop.left, a.unop.left.continuous⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  map_id _ := by ext x y; rfl
  map_comp _ _ := by ext x y; rfl

private def constantGroupSmall_representable (D : Type u) [Group D] :
    (constantGroupSmall (k := k) D ⋙ forget GrpCat).RepresentableBy (constantScheme D) where
  homEquiv {Y} := Equiv.ofBijective constantScheme_labelMap
    ⟨constantScheme_labelMap_injective Y, constantScheme_labelMap_surjective Y⟩
  homEquiv_comp _ _ := rfl

/-- The constant automorphism labels are represented by the disjoint union of copies of the base. -/
theorem constantGroup_represented (D : Type u) [Group D] :
    ∃ H : GroupScheme k, H.X = constantScheme D ∧ Etale H.X.hom ∧
      Nonempty (groupSections H ≅ constantGroup D) := by
  let F := constantGroupSmall (k := k) D
  let X := constantScheme (k := k) D
  let e := constantGroupSmall_representable (k := k) D
  let := GrpObj.ofRepresentableBy X F e
  let H : GroupScheme k := ⟨X⟩
  refine ⟨H, rfl, constantScheme_etale D, ⟨?_⟩⟩
  change (yonedaGrpObj X ⋙ Fppf.liftGroups.{u,u+1}) ≅ constantGroup D
  exact Functor.isoWhiskerRight (yonedaGrpObjIsoOfRepresentableBy X F e) _


private def constants (D : Type u) [Group D] :
    (Functor.const (SchemeOver k)ᵒᵖ).obj (GrpCat.of (ULift.{u+1} D)) ⟶ constantGroup D where
  app _ := GrpCat.ofHom {
    toFun := fun x => ⟨LocallyConstant.const _ x.down⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  naturality _ _ _ := rfl

private theorem constants_locallySurjective (D : Type u) [Group D] :
    Presheaf.IsLocallySurjective (schemeTopology k) (constants (k := k) D) := by
  constructor
  intro S s
  let opens (d : D) : S.left.Opens :=
    ⟨{x | s.down x = d}, s.down.isLocallyConstant.isOpen_fiber d⟩
  let C := S.left.openCoverOfIsOpenCover opens (by
    show iSup opens = ⊤
    apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨s.down x, rfl⟩)
  refine (schemeTopology k).superset_covering ((Sieve.generate_le_iff _ _).2 ?_) (openCover_mem C)
  intro U a ha
  obtain ⟨d⟩ := ha
  refine ⟨⟨d⟩, ?_⟩
  apply ULift.ext
  apply LocallyConstant.ext
  intro x
  exact x.property.symm

private def constantAut {D : Type u} [Group D] (G : GroupScheme k) (l : D →* Aut G) :
    (Functor.const (SchemeOver k)ᵒᵖ).obj (GrpCat.of (ULift.{u+1} D)) ⟶ automorphisms G where
  app S := GrpCat.ofHom ((Functor.mapAut G
    (yonedaGrp ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.forget S.unop).op)).comp
      (l.comp MulEquiv.ulift.toMonoidHom))
  naturality _ _ _ := by
    apply GrpCat.ext
    intro d
    apply Aut.ext
    apply Iso.ext
    rfl

/-- A family of ground-field automorphisms extends to locally constant coefficients. -/
theorem extendConstantAutomorphisms {D : Type u} [Group D] (G : GroupScheme k)
    (l : D →* Aut G) (hG : IsGroupSheaf (automorphisms G)) :
    ∃ s : constantGroup D ⟶ automorphisms G, ∀ (S : SchemeOver k) (d : D),
      s.app (op S) ⟨LocallyConstant.const _ d⟩ = scalarAut (l d) S := by
  have agrees (U : (SchemeOver k)ᵒᵖ) (x y : ULift.{u+1} D)
      (h : (constants (k := k) D).app U x = (constants D).app U y) :
      (constantAut G l).app U x = (constantAut G l).app U y := by
    cases isEmpty_or_nonempty U.unop.left with
    | inl he =>
      exact groupSheaf_separated hG (fppf_empty_cover U.unop) _ _ (by
        intro V a ha
        exact False.elim ha)
    | inr hn =>
      obtain ⟨z⟩ := hn
      have eq : x.down = y.down := congrArg (fun f => f.down z) h
      rw [ULift.ext eq]
  obtain ⟨s, hs⟩ := descends_locallySurjective (constants D) (constantAut G l)
    (constants_locallySurjective D) hG agrees
  refine ⟨s, fun S d => ?_⟩
  have heq := congrArg (fun a => a.app (op S)) hs
  exact ConcreteCategory.congr_hom heq (ULift.up d)

end ConstantSections

section Conjugation

variable {k : Type u} [Field k]

private abbrev groupSectionsMap {G H : GroupScheme k} (p : G ⟶ H) :
    groupSections G ⟶ groupSections H :=
  Functor.whiskerRight (yonedaGrp.map p) Fppf.liftGroups.{u,u+1}

private def groupSectionsFullyFaithful :
    (yonedaGrp (C := SchemeOver k) ⋙
      (Functor.whiskeringRight _ _ _).obj Fppf.liftGroups.{u,u+1}).FullyFaithful := by
  let h : Fppf.liftGroups.{u,u+1}.FullyFaithful :=
    { preimage := fun f => GrpCat.ofHom
        { toFun := fun x => (f ⟨x⟩).down
          map_one' := congrArg ULift.down (map_one f.hom)
          map_mul' := fun x y => congrArg ULift.down (map_mul f.hom ⟨x⟩ ⟨y⟩) }
      map_preimage := by
        intro X Y f
        apply GrpCat.ext
        intro x
        rfl
      preimage_map := by
        intro X Y f
        apply GrpCat.ext
        intro x
        rfl }
  exact yonedaGrpFullyFaithful.comp (h.whiskeringRight (SchemeOver k)ᵒᵖ)

/-- A single fppf map over the ground field generates a covering sieve. -/
private theorem fppf_mem {V U : SchemeOver k} (a : V ⟶ U) (ha : IsFppf a.left)
    {S : Sieve U} (h : S a) : S ∈ schemeTopology k U := by
  obtain ⟨hf, hs, hl⟩ := ha
  rw [GrothendieckTopology.mem_over_iff]
  apply Scheme.fppfTopology.superset_covering
    ((Sieve.generate_le_iff _ _).mpr (fun _ _ hb ↦ ?_))
    (Precoverage.generate_mem_toGrothendieck a.left.singleton_mem_fppfPrecoverage)
  cases hb
  exact ⟨V, a, 𝟙 V.left, h, by simp⟩

private theorem groupSectionsMap_locallySurjective {G H : GroupScheme k}
    (p : G ⟶ H) (hp : IsFppf p.hom.hom.left) :
    Presheaf.IsLocallySurjective (schemeTopology k) (groupSectionsMap p) := by
  constructor
  intro U y
  let a : pullback p.hom.hom y.down ⟶ U := pullback.snd _ _
  have hpb := (IsPullback.of_hasPullback p.hom.hom y.down).map
    (Over.forget (Spec (CommRingCat.of k)))
  apply fppf_mem a
  · exact ⟨MorphismProperty.of_isPullback hpb hp.1,
      MorphismProperty.of_isPullback hpb hp.2.1,
      MorphismProperty.of_isPullback hpb hp.2.2⟩
  refine ⟨⟨pullback.fst _ _⟩, ULift.ext ?_⟩
  exact pullback.condition (f := p.hom.hom) (g := y.down)

private theorem groupSections_isSheaf (G : GroupScheme k) :
    IsGroupSheaf (groupSections G) :=
  (isSheaf_iff_isSheaf_of_type _ _).mp
    ((schemeTopology k).uliftYoneda.{u+1}.obj G.X).property

private theorem innerAut_mul {G : GroupScheme k} {S : SchemeOver k} (g h : S ⟶ G.X) :
    innerAut (g * h) = innerAut g * innerAut h := by
  apply Aut.ext
  apply Iso.ext
  apply NatTrans.ext
  funext U
  apply GrpCat.ext
  intro x
  change U.unop.left ⟶ G.X at x
  change (U.unop.hom ≫ (g * h)) * x * (U.unop.hom ≫ (g * h))⁻¹ =
    (U.unop.hom ≫ g) * ((U.unop.hom ≫ h) * x * (U.unop.hom ≫ h)⁻¹) *
      (U.unop.hom ≫ g)⁻¹
  rw [MonObj.comp_mul, mul_inv_rev]
  simp only [mul_assoc]

private def conjugationMap (G : GroupScheme k) : groupSections G ⟶ automorphisms G where
  app S := GrpCat.ofHom {
    toFun := fun g => innerAut g.down
    map_one' := by
      apply Aut.ext
      apply Iso.ext
      apply NatTrans.ext
      funext U
      apply GrpCat.ext
      intro x
      change U.unop.left ⟶ G.X at x
      change (U.unop.hom ≫ (1 : S.unop ⟶ G.X)) * x *
        (U.unop.hom ≫ (1 : S.unop ⟶ G.X))⁻¹ = x
      simp
    map_mul' g h := innerAut_mul g.down h.down }
  naturality _ _ a := by
    apply GrpCat.ext
    intro g
    apply Aut.ext
    apply Iso.ext
    apply NatTrans.ext
    funext U
    apply GrpCat.ext
    intro x
    change U.unop.left ⟶ G.X at x
    change (U.unop.hom ≫ (a.unop ≫ g.down)) * x * (U.unop.hom ≫ (a.unop ≫ g.down))⁻¹ =
      ((U.unop.hom ≫ a.unop) ≫ g.down) * x * ((U.unop.hom ≫ a.unop) ≫ g.down)⁻¹
    simp only [Category.assoc]

private theorem projection_eq_one_iff {G : AffineAlgebraicGroup k} (Q : AdjointQuotient G)
    {S : SchemeOver k} (g : S ⟶ G.val.X) :
    g ≫ Q.projection.hom.hom = 1 ↔ innerAut g = 1 := by
  rw [innerAut_eq_one_iff]
  refine Iff.trans ?_ (Q.isCentre S g).symm
  constructor
  · intro h
    refine ⟨Q.kernel.lift g (toUnit _) ?_, Q.kernel.lift_fst _ _ _⟩
    exact h
  · rintro ⟨z, rfl⟩
    change (z ≫ Q.centre.inclusion.hom.hom) ≫ Q.projection.hom.hom =
      toUnit S ≫ η[Q.quotient.val.X]
    rw [Category.assoc, Q.kernel.w, ← Category.assoc]
    congr 1
    exact toUnit_unique _ _

/-- Conjugation by a representative descends to the central quotient,
and the resulting map to the automorphism sheaf is injective. -/
theorem adjointInner (G : AffineAlgebraicGroup k) (Q : AdjointQuotient G) :
    ∃ inn : groupSections Q.quotient.val ⟶ automorphisms G.val,
      (∀ (S : SchemeOver k) (g : S ⟶ G.val.X),
        inn.app (op S) ⟨g ≫ Q.projection.hom.hom⟩ = innerAut g) ∧
      ∀ S, Function.Injective (inn.app S) := by
  let p := groupSectionsMap Q.projection
  let c := conjugationMap G.val
  have hp : Presheaf.IsLocallySurjective (schemeTopology k) p :=
    groupSectionsMap_locallySurjective Q.projection Q.fppf
  let := hp
  have ker (U : (SchemeOver k)ᵒᵖ) (x : (groupSections G.val).obj U) :
      p.app U x = 1 ↔ c.app U x = 1 := by
    change ULift.up (x.down ≫ Q.projection.hom.hom) = ULift.up 1 ↔ innerAut x.down = 1
    rw [ULift.up_inj, projection_eq_one_iff]
  have agrees (U : (SchemeOver k)ᵒᵖ) (x y : (groupSections G.val).obj U)
      (h : p.app U x = p.app U y) : c.app U x = c.app U y := by
    have he : p.app U (x / y) = 1 := by
      rw [map_div, h]
      exact div_eq_one.mpr rfl
    have hc := (ker U (x / y)).1 he
    rwa [map_div, div_eq_one] at hc
  obtain ⟨inn, hi⟩ := descends_locallySurjective p c hp (automorphisms_isSheaf G.val) agrees
  have onLift (U : (SchemeOver k)ᵒᵖ) (x : (groupSections G.val).obj U) :
      inn.app U (p.app U x) = c.app U x :=
    ConcreteCategory.congr_hom (congrArg (fun j => j.app U) hi) x
  refine ⟨inn, fun S g => onLift (op S) ⟨g⟩, ?_⟩
  intro U x y h
  have eq : inn.app U (x / y) = 1 := by
    rw [map_div, h]
    exact div_eq_one.mpr rfl
  apply div_eq_one.mp
  refine groupSheaf_separated (groupSections_isSheaf Q.quotient.val)
    (Presheaf.imageSieve_mem (schemeTopology k) p (x / y)) _ _ ?_
  rintro W a ⟨z, hz⟩
  rw [map_one, ← hz]
  apply (ker _ _).2
  rw [← onLift, hz, NatTrans.naturality_apply inn, eq, map_one]

end Conjugation

section Transport

variable {k : Type u} [Field k] {G H : GroupScheme k} {S : SchemeOver k}

private theorem restrictAut_id (f : RelativeAut G S) : restrictAut (𝟙 S) f = f :=
  ConcreteCategory.congr_hom ((automorphisms G).map_id (op S)) f

private theorem transportInner
    (i : relativePoints G S ≅ relativePoints H S) (U : Over S) (g : U.left ⟶ G.X) :
    Aut.autMulEquivOfIso (restrictIso U.hom i) (innerAut g) =
      innerAut (i.hom.app (op U) g) := by
  apply Aut.ext
  apply Iso.ext
  apply NatTrans.ext
  funext W
  apply GrpCat.ext
  intro x
  change W.unop.left ⟶ H.X at x
  let V := (Over.map U.hom).obj W.unop
  let a : V ⟶ U := Over.homMk W.unop.hom
  let f : (W.unop.left ⟶ G.X) →* (W.unop.left ⟶ H.X) := (i.hom.app (op V)).hom
  let f' : (W.unop.left ⟶ H.X) →* (W.unop.left ⟶ G.X) := (i.inv.app (op V)).hom
  change f ((W.unop.hom ≫ g) * f' x * (W.unop.hom ≫ g)⁻¹) =
    (W.unop.hom ≫ i.hom.app (op U) g) * x * (W.unop.hom ≫ i.hom.app (op U) g)⁻¹
  have hres : f (W.unop.hom ≫ g) = W.unop.hom ≫ i.hom.app (op U) g :=
    NatTrans.naturality_apply i.hom a.op g
  have hcancel : f (f' x) = x :=
    (i.app (op V)).groupIsoToMulEquiv.apply_symm_apply x
  rw [map_mul, map_mul, map_inv, hres, hcancel]

private def transportAutomorphisms (i : relativePoints G S ≅ relativePoints H S) :
    onSlice S (automorphisms G) ≅ onSlice S (automorphisms H) :=
  NatIso.ofComponents (fun U => (Aut.autMulEquivOfIso (restrictIso U.unop.hom i)).toGrpIso)
    (by
      intro U V a
      apply GrpCat.ext
      intro f
      apply Aut.ext
      apply Iso.ext
      apply NatTrans.ext
      funext W
      apply GrpCat.ext
      intro x
      have hw : W.unop.hom ≫ V.unop.hom = (W.unop.hom ≫ a.unop.left) ≫ U.unop.hom := by
        rw [Category.assoc, Over.w a.unop]
      let h (b : W.unop.left ⟶ S) : W.unop.left ⟶ H.X :=
        (i.hom.app (op (Over.mk b))).hom
          ((f.asIso.hom.app (op ((Over.map a.unop.left).obj W.unop))).hom
            ((i.inv.app (op (Over.mk b))).hom x))
      exact congrArg h hw)

private theorem isSheaf_onSlice {F : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{u+1}} (hF : IsGroupSheaf F)
    (S : SchemeOver k) :
    Presieve.IsSheaf ((schemeTopology k).over S) ((onSlice S F) ⋙ forget GrpCat) :=
  (Over.forget S).op_comp_isSheaf_of_types _ _ ⟨_, (isSheaf_iff_isSheaf_of_type _ _).2 hF⟩

private theorem locallySurjective_onSlice {F G : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{u+1}}
    (p : F ⟶ G) (h : Presheaf.IsLocallySurjective (schemeTopology k) p) (S : SchemeOver k) :
    Presheaf.IsLocallySurjective ((schemeTopology k).over S) ((Over.forget S).op.whiskerLeft p) := by
  let := h
  constructor
  intro U x
  rw [GrothendieckTopology.mem_over_iff]
  apply (schemeTopology k).superset_covering _ (Presheaf.imageSieve_mem (schemeTopology k) p x)
  intro V a ha
  rw [Sieve.overEquiv_iff]
  exact ha

end Transport

section AdjointTransport

variable {k : Type u} [Field k] {G H : AffineAlgebraicGroup k}
variable {QG : AdjointQuotient G} {QH : AdjointQuotient H}

private theorem adjointComparison {S : SchemeOver k}
    (j : relativePoints G.val S ≅ relativePoints H.val S)
    (innG : groupSections QG.quotient.val ⟶ automorphisms G.val)
    (innH : groupSections QH.quotient.val ⟶ automorphisms H.val)
    (hG : ∀ (S : SchemeOver k) (g : S ⟶ G.val.X),
      innG.app (op S) ⟨g ≫ QG.projection.hom.hom⟩ = innerAut g)
    (hH : ∀ (S : SchemeOver k) (g : S ⟶ H.val.X),
      innH.app (op S) ⟨g ≫ QH.projection.hom.hom⟩ = innerAut g)
    (injG : ∀ U, Function.Injective (innG.app U))
    (injH : ∀ U, Function.Injective (innH.app U)) :
    ∃ a : onSlice S (groupSections QG.quotient.val) ≅ onSlice S (groupSections QH.quotient.val),
      (∀ (U : Over S) (g : U.left ⟶ G.val.X),
        a.hom.app (op U) ⟨g ≫ QG.projection.hom.hom⟩ =
          ⟨j.hom.app (op U) g ≫ QH.projection.hom.hom⟩) ∧
      ∀ (U : Over S) (x : (groupSections QG.quotient.val).obj (op U.left)),
        Aut.autMulEquivOfIso (restrictIso U.hom j) (innG.app (op U.left) x) =
          innH.app (op U.left) (a.hom.app (op U) x) := by
  let t := (Over.forget S).op
  let p := t.whiskerLeft (groupSectionsMap QG.projection)
  let p' := t.whiskerLeft (groupSectionsMap QH.projection)
  let e := Functor.isoWhiskerRight j Fppf.liftGroups.{u,u+1}
  have hp := locallySurjective_onSlice (groupSectionsMap QG.projection)
    (groupSectionsMap_locallySurjective QG.projection QG.fppf) S
  have hp' := locallySurjective_onSlice (groupSectionsMap QH.projection)
    (groupSectionsMap_locallySurjective QH.projection QH.fppf) S
  have he (U : (Over S)ᵒᵖ) (x y : (onSlice S (groupSections G.val)).obj U) :
      p.app U x = p.app U y ↔ p'.app U (e.hom.app U x) = p'.app U (e.hom.app U y) := by
    have left (z : (onSlice S (groupSections G.val)).obj U) :
        innG.app (op U.unop.left) (p.app U z) = innerAut z.down := hG _ _
    have right (z : (onSlice S (groupSections G.val)).obj U) :
        innH.app (op U.unop.left) (p'.app U (e.hom.app U z)) =
          innerAut (j.hom.app U z.down) := hH _ _
    rw [← (injG (op U.unop.left)).eq_iff, left, left,
      ← (injH (op U.unop.left)).eq_iff, right, right,
      ← transportInner j U.unop x.down, ← transportInner j U.unop y.down]
    exact (Aut.autMulEquivOfIso (restrictIso U.unop.hom j)).injective.eq_iff.symm
  obtain ⟨a, ha⟩ := descends_iso_of_locallySurjective p p' e hp hp'
    (isSheaf_onSlice (groupSections_isSheaf QG.quotient.val) S)
    (isSheaf_onSlice (groupSections_isSheaf QH.quotient.val) S) he
  have ha' (U : Over S) (g : U.left ⟶ G.val.X) :
      a.hom.app (op U) ⟨g ≫ QG.projection.hom.hom⟩ =
        ⟨j.hom.app (op U) g ≫ QH.projection.hom.hom⟩ :=
    congrArg (fun h => (h.app (op U)).hom
      (ULift.up g : (onSlice S (groupSections G.val)).obj (op U))) ha
  let b := transportAutomorphisms j
  have comm : t.whiskerLeft innG ≫ b.hom = a.hom ≫ t.whiskerLeft innH := by
    apply hom_ext_of_locallySurjective p hp (isSheaf_onSlice (automorphisms_isSheaf H.val) S)
    apply NatTrans.ext
    funext U
    apply GrpCat.ext
    intro x
    change Aut.autMulEquivOfIso (restrictIso U.unop.hom j)
        (innG.app (op U.unop.left) ⟨x.down ≫ QG.projection.hom.hom⟩) =
      innH.app (op U.unop.left) (a.hom.app U ⟨x.down ≫ QG.projection.hom.hom⟩)
    rw [hG, ha' U.unop, hH]
    exact transportInner j U.unop x.down
  refine ⟨a, ha', fun U x => ?_⟩
  exact ConcreteCategory.congr_hom (congrArg (fun h => h.app (op U)) comm) x

private theorem innerRange_normal (inn : groupSections QG.quotient.val ⟶ automorphisms G.val)
    (hG : ∀ (S : SchemeOver k) (g : S ⟶ G.val.X),
      inn.app (op S) ⟨g ≫ QG.projection.hom.hom⟩ = innerAut g)
    (inj : ∀ U, Function.Injective (inn.app U)) (U : (SchemeOver k)ᵒᵖ) :
    (inn.app U).hom.range.Normal := by
  constructor
  rintro _ ⟨x, rfl⟩ f
  change RelativeAut G.val U.unop at f
  obtain ⟨a, _, ha⟩ := adjointComparison f.asIso inn inn hG hG inj inj
  refine ⟨a.hom.app (op (Over.mk (𝟙 U.unop))) x, ?_⟩
  have he := ha (Over.mk (𝟙 U.unop)) x
  change Aut.autMulEquivOfIso (restrictIso (𝟙 U.unop) f.asIso) (inn.app U x) =
    inn.app U (a.hom.app (op (Over.mk (𝟙 U.unop))) x) at he
  have h : restrictIso (𝟙 U.unop) f.asIso = f.asIso :=
    congrArg Aut.asIso (restrictAut_id f)
  rw [h] at he
  exact he.symm

end AdjointTransport

section Quotient

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
variable {K G : Cᵒᵖ ⥤ GrpCat.{u+1}} (i : K ⟶ G)

private theorem range_of_local_sections
    (hK : Presieve.IsSheaf J (K ⋙ forget GrpCat)) (hi : ∀ U, Function.Injective (i.app U))
    {U : C} (g : G.obj (op U)) (hG : Presieve.IsSheaf J (G ⋙ forget GrpCat))
    {S : Sieve U} (hS : S ∈ J U)
    (h : ∀ ⦃V : C⦄ (a : V ⟶ U), S a → G.map a.op g ∈ (i.app (op V)).hom.range) :
    g ∈ (i.app (op U)).hom.range := by
  classical
  let e : Presieve.FamilyOfElements (K ⋙ forget GrpCat) S.arrows :=
    fun _ a ha => (h a ha).choose
  have he : e.Compatible := by
    intro V₁ V₂ W b₁ b₂ a₁ a₂ ha₁ ha₂ eq
    apply hi (op W)
    change i.app _ (K.map b₁.op (e a₁ ha₁)) = i.app _ (K.map b₂.op (e a₂ ha₂))
    rw [NatTrans.naturality_apply i, NatTrans.naturality_apply i]
    have h₁ : i.app (op V₁) (e a₁ ha₁) = G.map a₁.op g := (h a₁ ha₁).choose_spec
    have h₂ : i.app (op V₂) (e a₂ ha₂) = G.map a₂.op g := (h a₂ ha₂).choose_spec
    rw [h₁, h₂, ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, eq]
  obtain ⟨x, hx, _⟩ := hK S hS e he
  refine ⟨x, groupSheaf_separated hG hS _ _ ?_⟩
  intro V a ha
  rw [← NatTrans.naturality_apply i]
  have hv : K.map a.op x = e a ha := hx a ha
  rw [hv]
  exact (h a ha).choose_spec

local instance grpHasFilteredColimits : HasFilteredColimitsOfSize.{u+1,u+1} GrpCat.{u+1} where
  HasColimitsOfShape _ := ⟨fun F => ⟨⟨GrpCat.FilteredColimits.colimitCocone.{u+1,u+1} F,
    GrpCat.FilteredColimits.colimitCoconeIsColimit.{u+1,u+1} F⟩⟩⟩

private theorem maps_range {U V : Cᵒᵖ} (a : U ⟶ V) :
    (i.app U).hom.range ≤ (i.app V).hom.range.comap (G.map a).hom := by
  rintro _ ⟨x, rfl⟩
  exact ⟨K.map a x, NatTrans.naturality_apply i a x⟩

variable [hn : ∀ U, (i.app U).hom.range.Normal]

private def rangeQuotient : Cᵒᵖ ⥤ GrpCat.{u+1} where
  obj U := GrpCat.of (G.obj U ⧸ (i.app U).hom.range)
  map a := GrpCat.ofHom (QuotientGroup.map _ _ (G.map a).hom (maps_range i a))
  map_id U := by
    apply GrpCat.ext
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
    change QuotientGroup.mk' _ (G.map (𝟙 U) x) = QuotientGroup.mk' _ x
    rw [G.map_id]; rfl
  map_comp a b := by
    apply GrpCat.ext
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
    change QuotientGroup.mk' _ (G.map (a ≫ b) x) = QuotientGroup.mk' _ (G.map b (G.map a x))
    rw [Functor.map_comp_apply]

private def toRangeQuotient : G ⟶ rangeQuotient i where
  app U := GrpCat.ofHom (QuotientGroup.mk' (i.app U).hom.range)
  naturality _ _ _ := by apply GrpCat.ext; intro x; rfl

/-- Sheafifying the sectionwise quotient gives a locally surjective map
whose kernel is the subsheaf used in the quotient. -/
theorem groupSheafQuotient (hK : Presieve.IsSheaf J (K ⋙ forget GrpCat))
    (hG : Presieve.IsSheaf J (G ⋙ forget GrpCat)) (hi : ∀ U, Function.Injective (i.app U)) :
    ∃ (O : Cᵒᵖ ⥤ GrpCat.{u+1}) (out : G ⟶ O), Presieve.IsSheaf J (O ⋙ forget GrpCat) ∧
      Presheaf.IsLocallySurjective J out ∧
      ∀ (U : Cᵒᵖ) (g : G.obj U), out.app U g = 1 ↔ g ∈ (i.app U).hom.range := by
  let Q : Cᵒᵖ ⥤ GrpCat.{u+1} := rangeQuotient i
  let p : G ⟶ Q := toRangeQuotient i
  let Os : Sheaf J GrpCat.{u+1} := (presheafToSheaf J GrpCat.{u+1}).obj Q
  let O : Cᵒᵖ ⥤ GrpCat.{u+1} := Os.obj
  let r : Q ⟶ O := toSheafify J Q
  have hO : Presieve.IsSheaf J (O ⋙ forget GrpCat.{u+1}) :=
    (isSheaf_iff_isSheaf_of_type J (O ⋙ forget GrpCat.{u+1})).mp
      (Presheaf.isSheaf_comp_of_isSheaf J O (forget GrpCat.{u+1}) Os.property)
  let : Presheaf.IsLocallySurjective J p :=
    Presheaf.isLocallySurjective_of_surjective J p fun _ => QuotientGroup.mk'_surjective _
  refine ⟨O, p ≫ r, hO, inferInstance, ?_⟩
  intro U g
  constructor
  · intro h
    have hr : r.app U (p.app U g) = r.app U 1 :=
      h.trans (map_one (r.app U).hom).symm
    apply range_of_local_sections i hK hi g hG
      (Presheaf.equalizerSieve_mem J r (p.app U g) 1 hr)
    intro V a ha
    have hres : Q.map a.op (p.app U g) = Q.map a.op 1 := ha
    rw [← NatTrans.naturality_apply p, map_one] at hres
    exact (QuotientGroup.eq_one_iff _).mp hres
  · intro h
    have he : p.app U g = 1 := (QuotientGroup.eq_one_iff _).mpr h
    change r.app U (p.app U g) = 1
    rw [he, map_one]

end Quotient

section ExactSequences

variable {k : Type u} [Field k] {G H : AffineAlgebraicGroup k}
variable {QG : AdjointQuotient G} {QH : AdjointQuotient H}
variable {OG OH : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{u+1}}

theorem exactSequence_exists (G : AffineAlgebraicGroup k) :
    ∃ (Q : AdjointQuotient G) (O : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{u+1}),
      Nonempty (ExactSequence G Q O) := by
  obtain ⟨Q⟩ := adjointQuotient_exists G
  obtain ⟨inn, h, hinj⟩ := adjointInner G Q
  let := innerRange_normal inn h hinj
  have hG := automorphisms_isSheaf G.val
  obtain ⟨O, out, hO, hsur, hex⟩ :=
    groupSheafQuotient inn (groupSections_isSheaf Q.quotient.val) hG hinj
  exact ⟨Q, O, ⟨⟨hG, hO, inn, out, h, hinj, hex, hsur⟩⟩⟩

/-- Transport of the original group identifies the exact sequences on the slice. -/
theorem sequenceComparison (E : ExactSequence G QG OG) (F : ExactSequence H QH OH)
    {S : SchemeOver k} (j : relativePoints G.val S ≅ relativePoints H.val S) :
    Nonempty (SequenceComparison E F j) := by
  obtain ⟨a, ha, hac⟩ := adjointComparison j E.inner F.inner E.onLift F.onLift
    E.innerInjective F.innerInjective
  let t := (Over.forget S).op
  let p := t.whiskerLeft E.outer
  let p' := t.whiskerLeft F.outer
  let e := transportAutomorphisms j
  have hc (U : (Over S)ᵒᵖ) (f : (onSlice S (automorphisms G.val)).obj U) :
      p.app U f = 1 ↔ p'.app U (e.hom.app U f) = 1 := by
    change E.outer.app (op U.unop.left) f = 1 ↔
      F.outer.app (op U.unop.left) (Aut.autMulEquivOfIso (restrictIso U.unop.hom j) f) = 1
    rw [E.exact, F.exact]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨a.hom.app U x, (hac U.unop x).symm⟩
    · rintro ⟨x, hx⟩
      obtain ⟨y, rfl⟩ := (a.app U).groupIsoToMulEquiv.surjective x
      refine ⟨y, (Aut.autMulEquivOfIso (restrictIso U.unop.hom j)).injective ?_⟩
      exact (hac U.unop y).trans hx
  have h (U : (Over S)ᵒᵖ) (f g : (onSlice S (automorphisms G.val)).obj U) :
      p.app U f = p.app U g ↔ p'.app U (e.hom.app U f) = p'.app U (e.hom.app U g) := by
    simpa only [map_div, div_eq_one] using hc U (f / g)
  obtain ⟨b, hb⟩ := descends_iso_of_locallySurjective p p' e
    (locallySurjective_onSlice E.outer E.outerLocallySurjective S)
    (locallySurjective_onSlice F.outer F.outerLocallySurjective S)
    (isSheaf_onSlice E.outerSheaf S) (isSheaf_onSlice F.outerSheaf S) h
  refine ⟨⟨a, b, ha, hac, fun U f => ?_⟩⟩
  have eq := congrArg (fun n => (n.app (op U)).hom f) hb
  exact eq

/-- The comparison maps are determined by their actions on local lifts. -/
theorem sequenceComparison_subsingleton (E : ExactSequence G QG OG) (F : ExactSequence H QH OH)
    {S : SchemeOver k} (j : relativePoints G.val S ≅ relativePoints H.val S) :
    Subsingleton (SequenceComparison E F j) := by
  constructor
  intro a b
  have ha : a.adjointIso = b.adjointIso := by
    apply Iso.ext
    ext U q
    exact F.innerInjective (op U.unop.left)
      ((a.innerComm U.unop q).symm.trans (b.innerComm U.unop q))
  have hb : a.outerIso = b.outerIso := by
    apply Iso.ext
    apply hom_ext_of_locallySurjective ((Over.forget S).op.whiskerLeft E.outer)
      (locallySurjective_onSlice E.outer E.outerLocallySurjective S)
      (isSheaf_onSlice F.outerSheaf S)
    ext U f
    exact (a.outerComm U.unop f).trans (b.outerComm U.unop f).symm
  cases a
  cases b
  cases ha
  cases hb
  rfl

end ExactSequences

section RelativeYoneda

variable {k : Type u} [Field k] {S : SchemeOver k}

private abbrev relativeTest {S : SchemeOver k} (U : Over S) : Over S.left :=
  (Over.iteratedSliceForward S).obj U

private def relativeSectionEquiv (U : Over S) (X : SchemeOver k) :
    (relativeTest U ⟶ (Over.pullback S.hom).obj X) ≃ (U.left ⟶ X) where
  toFun p := Over.homMk (p.left ≫ pullback.fst X.hom S.hom) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (p.left ≫ ((Over.pullback S.hom).obj X).hom) ≫ S.hom = U.left.hom
    rw [Over.w p]
    exact Over.w U.hom)
  invFun p := Over.homMk (pullback.lift p.left U.hom.left (by
    rw [Over.w p]
    exact (Over.w U.hom).symm))
    (pullback.lift_snd ..)
  left_inv p := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst ..
    · exact (pullback.lift_snd ..).trans (Over.w p).symm
  right_inv p := Over.OverMorphism.ext (pullback.lift_fst ..)

private theorem relativeSection_natural (U : Over S)
    {X Y : SchemeOver k} (a : X ⟶ Y) (p : relativeTest U ⟶ (Over.pullback S.hom).obj X) :
    relativeSectionEquiv U Y (p ≫ (Over.pullback S.hom).map a) =
      relativeSectionEquiv U X p ≫ a := by
  apply Over.OverMorphism.ext
  change (p.left ≫ ((Over.pullback S.hom).map a).left) ≫ pullback.fst Y.hom S.hom =
    (p.left ≫ pullback.fst X.hom S.hom) ≫ a.left
  simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst]

private def relativeSectionGroupEquiv (U : Over S) (G : GroupScheme k) :
    (relativeTest U ⟶ ((Over.pullback S.hom).mapGrp.obj G).X) ≃* (U.left ⟶ G.X) where
  toEquiv := relativeSectionEquiv U G.X
  map_mul' p q := by
    let F := Over.pullback S.hom
    change relativeTest U ⟶ F.obj G.X at p q
    let m : relativeTest U ⟶ F.obj (G.X ⊗ G.X) :=
      lift p q ≫ Functor.LaxMonoidal.μ F G.X G.X
    have hd : relativeSectionEquiv U (G.X ⊗ G.X) m =
        lift (relativeSectionEquiv U G.X p) (relativeSectionEquiv U G.X q) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [← relativeSection_natural U (fst G.X G.X), lift_fst]
        change relativeSectionEquiv U G.X ((lift p q ≫ Functor.LaxMonoidal.μ F G.X G.X) ≫
          F.map (fst G.X G.X)) = _
        rw [Category.assoc, Functor.Monoidal.μ_fst, lift_fst]
      · rw [← relativeSection_natural U (snd G.X G.X), lift_snd]
        change relativeSectionEquiv U G.X ((lift p q ≫ Functor.LaxMonoidal.μ F G.X G.X) ≫
          F.map (snd G.X G.X)) = _
        rw [Category.assoc, Functor.Monoidal.μ_snd, lift_snd]
    change relativeSectionEquiv U G.X (lift p q ≫
      (Functor.LaxMonoidal.μ F G.X G.X ≫ F.map μ[G.X])) = _
    rw [← Category.assoc]
    change relativeSectionEquiv U G.X (m ≫ F.map μ[G.X]) = _
    rw [relativeSection_natural, hd]
    rfl

private def relativeYonedaIso (S : SchemeOver k) (G : GroupScheme k) :
    (Over.iteratedSliceForward S).op ⋙
      yonedaGrp.obj ((Over.pullback S.hom).mapGrp.obj G) ≅ relativePoints G S :=
  NatIso.ofComponents (fun U => (relativeSectionGroupEquiv U.unop G).toGrpIso)
    (by
      intro U V a
      apply GrpCat.ext
      intro x
      apply Over.OverMorphism.ext
      change (a.unop.left.left ≫ x.left) ≫ pullback.fst G.X.hom S.hom =
        a.unop.left.left ≫ (x.left ≫ pullback.fst G.X.hom S.hom)
      exact Category.assoc ..)

private abbrev relativeYoneda (S : SchemeOver k) :
    Grp (Over S.left) ⥤ (Over S)ᵒᵖ ⥤ GrpCat.{u} :=
  yonedaGrp ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.iteratedSliceForward S).op

private def relativeYonedaFullyFaithful (S : SchemeOver k) : (relativeYoneda S).FullyFaithful :=
  yonedaGrpFullyFaithful.comp
    ((S.iteratedSliceEquiv.op.congrLeft (E := GrpCat.{u})).symm.fullyFaithfulFunctor)

private def relativeSchemeIso {G H : GroupScheme k}
    (i : relativePoints G S ≅ relativePoints H S) :
    (Over.pullback S.hom).mapGrp.obj G ≅ (Over.pullback S.hom).mapGrp.obj H :=
  (relativeYonedaFullyFaithful S).preimageIso
    (relativeYonedaIso S G ≪≫ i ≪≫ (relativeYonedaIso S H).symm)

private theorem relativeSchemeIso_natural {G H : GroupScheme k}
    (i : relativePoints G S ≅ relativePoints H S)
    (U : Over S) (p : relativeTest U ⟶ ((Over.pullback S.hom).mapGrp.obj G).X) :
    relativeSectionEquiv U _ (p ≫ (relativeSchemeIso i).hom.hom.hom) =
      (i.hom.app (op U)).hom (relativeSectionEquiv U _ p) := by
  let e := relativeYonedaIso S H
  have h := (relativeYonedaFullyFaithful S).map_preimage
    (relativeYonedaIso S G ≪≫ i ≪≫ e.symm).hom
  let b := (e.app (op U)).groupIsoToMulEquiv
  have eq : p ≫ (relativeSchemeIso i).hom.hom.hom =
      b.symm ((i.hom.app (op U)).hom (relativeSectionEquiv U G.X p)) :=
    congrArg (fun n => (n.app (op U)).hom p) h
  change b (p ≫ (relativeSchemeIso i).hom.hom.hom) = _
  rw [eq, b.apply_symm_apply]

end RelativeYoneda

section Forms

open private exists_coordinate_model spectrumIsoEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Forms
open private extendedGroupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

variable {k : Type u} [Field k] (L : Type u) [Field L] [Algebra k L]

private abbrev fieldExtension : SchemeOver k := Over.mk (fieldSpecMap k L)

variable {G H : AffineAlgebraicGroup k}

private theorem formTrivializes (h : IsSeparableForm G H) :
    ∃ S : SchemeOver k, IsFppf S.hom ∧ Nonempty (relativePoints G.val S ≅ relativePoints H.val S) := by
  obtain ⟨K, _, _, _, ⟨j⟩⟩ := h
  obtain ⟨A, hA, ⟨a⟩⟩ := exists_coordinate_model G
  obtain ⟨B, hB, ⟨b⟩⟩ := exists_coordinate_model H
  let onSpectrum (L : Type u) [Field L] [Algebra k L] :=
    (extendedGroupIso (k := k) L A ≪≫ (groupBaseChange k L).mapIso a,
      extendedGroupIso (k := k) L B ≪≫ (groupBaseChange k L).mapIso b)
  let aj := (onSpectrum K).1 ≪≫ j ≪≫ (onSpectrum K).2.symm
  let aK := (spectrumIsoEquiv _ _).symm aj
  obtain ⟨L, aL, _, _⟩ :=
    LinearAlgebraicGroups.Descent.Forms.finiteLevelIsomorphisms A B hA hB ⊥ aK
  let S := fieldExtension (k := k) L
  let jL : (groupBaseChange k L).obj G.val ≅ (groupBaseChange k L).obj H.val :=
    (onSpectrum L).1.symm ≪≫ spectrumIsoEquiv _ _ aL ≪≫ (onSpectrum L).2
  refine ⟨S, ?_, ⟨(relativeYonedaIso (fieldExtension L) G.val).symm ≪≫
    Functor.isoWhiskerLeft (Over.iteratedSliceForward S).op (yonedaGrp.mapIso jL) ≪≫
    relativeYonedaIso (fieldExtension L) H.val⟩⟩
  change IsFppf (fieldSpecMap k L)
  have : LocallyOfFiniteType (fieldSpecMap k L) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
      (RingHom.finiteType_algebraMap.2 inferInstance)
  exact ⟨inferInstance, ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩, inferInstance⟩

/-- The automorphism sequence of a separable form is obtained by descent
with transport of automorphisms on any slice trivializing the form. -/
theorem twists_of_exactSequence {Q : AdjointQuotient G}
    {O : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{u+1}} (E : ExactSequence G Q O) :
    Twists E := by
  intro H h
  obtain ⟨QH, OH, ⟨F⟩⟩ := exactSequence_exists H
  exact ⟨QH, OH, F, formTrivializes h,
    fun _ i => ⟨sequenceComparison E F i, sequenceComparison_subsingleton E F i⟩⟩

end Forms

section SplitQuotient

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {Q : AdjointQuotient G}
variable {O : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{u+1}} {D : Type u} [Group D]

/-- Local factorization and trivial intersection identify the outer sheaf via
the chosen section of automorphisms with locally constant labels. -/
theorem split_of_local_decomposition (E : ExactSequence G Q O)
    (s : constantGroup D ⟶ automorphisms G.val)
    (decomposes : ∀ (U : SchemeOver k) (f : RelativeAut G.val U),
      ∃ R : Sieve U, R ∈ schemeTopology k U ∧
        ∀ ⦃V : SchemeOver k⦄ (a : V ⟶ U), R a →
          ∃ (q : (groupSections Q.quotient.val).obj (op V))
            (d : (constantGroup (k := k) D).obj (op V)),
            restrictAut a f = E.inner.app (op V) q * s.app (op V) d)
    (trivial : ∀ (U : (SchemeOver k)ᵒᵖ) (d : (constantGroup (k := k) D).obj U),
      s.app U d ∈ (E.inner.app U).hom.range → d = 1) :
    ∃ F : ExactSequence G Q (constantGroup D), F.inner = E.inner ∧ s ≫ F.outer = 𝟙 _ := by
  let r := s ≫ E.outer
  have inj (U : (SchemeOver k)ᵒᵖ) : Function.Injective (r.app U) := by
    intro d e he
    apply div_eq_one.mp
    apply trivial U
    apply (E.exact U _).mp
    have he' : r.app U (d / e) = 1 := by
      rw [map_div, he]
      exact div_self' _
    exact he'
  have sur : Presheaf.IsLocallySurjective (schemeTopology k) r := by
    constructor
    intro U x
    let J := schemeTopology k
    let := E.outerLocallySurjective
    refine J.transitive (Presheaf.imageSieve_mem J E.outer x) _ ?_
    rintro V a ⟨f, hf⟩
    obtain ⟨R, hR, hd⟩ := decomposes V f
    refine J.superset_covering ?_ hR
    intro W b hb
    obtain ⟨q, d, he⟩ := hd b hb
    refine ⟨d, ?_⟩
    change E.outer.app (op W) (s.app (op W) d) = O.map (b ≫ a).op x
    rw [op_comp, Functor.map_comp_apply, ← hf, ← NatTrans.naturality_apply E.outer]
    -- On the covering arrows the inner factor maps to the identity.
    have hq := (E.exact (op W) (E.inner.app (op W) q)).mpr ⟨q, rfl⟩
    change E.outer.app (op W) (s.app (op W) d) = E.outer.app (op W) (restrictAut b f)
    rw [he, map_mul, hq, one_mul]
  have hD := constantGroup_isSheaf (k := k) D
  let shD : Sheaf (schemeTopology k) GrpCat.{u+1} :=
    ⟨_, Presheaf.isSheaf_of_isSheaf_comp _ _ (forget GrpCat)
      ((isSheaf_iff_isSheaf_of_type _ _).mpr hD)⟩
  let shO : Sheaf (schemeTopology k) GrpCat.{u+1} :=
    ⟨_, Presheaf.isSheaf_of_isSheaf_comp _ _ (forget GrpCat)
      ((isSheaf_iff_isSheaf_of_type _ _).mpr E.outerSheaf)⟩
  let rSh : shD ⟶ shO := ⟨r⟩
  have hIso : IsIso rSh := (Sheaf.isLocallyBijective_iff_isIso rSh).1
    ⟨Presheaf.isLocallyInjective_of_injective _ _ inj, sur⟩
  let e := (sheafToPresheaf (schemeTopology k) GrpCat.{u+1}).mapIso (asIso rSh)
  have he : e.hom = r := rfl
  let F : ExactSequence G Q (constantGroup D) :=
    { E with
      outerSheaf := hD
      outer := E.outer ≫ e.inv
      exact := fun U f => by
        change e.inv.app U (E.outer.app U f) = 1 ↔ f ∈ (E.inner.app U).hom.range
        rw [← E.exact]
        have h : Function.Injective (e.inv.app U) := (e.app U).groupIsoToMulEquiv.symm.injective
        exact ((map_one (e.inv.app U).hom).symm ▸ h.eq_iff)
      outerLocallySurjective := by
        let := E.outerLocallySurjective
        infer_instance }
  refine ⟨F, rfl, ?_⟩
  change s ≫ E.outer ≫ e.inv = 𝟙 _
  rw [← Category.assoc]
  change r ≫ e.inv = 𝟙 _
  rw [← he, Iso.hom_inv_id]

end SplitQuotient

section AdjointTorusCoordinates

open Pinning (PinnedGroup AttachedDatum SimpleRoot)
open RootGroups (AdditiveLine)
open Specs.SchemeCentre (rootLattice)
open Specs.DiagonalizableGroups (diagonalClosedInclusion diagonalGroup diagonalRestriction
  groupAlgebra groupAlgebraMap IntegerCharacters integerGenerator)
open private schemeKernel_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private specGroupMap_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private integerHomEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups

variable {k : Type u} [Field k]

private abbrev monomialCharacter {M : Type u} [CommGroup M] (m : M) :
    CharacterDescent.Character (specGroup (groupAlgebra k M)) :=
  specGroupMap (groupAlgebraMap k ((zpowersHom M m).comp MulEquiv.ulift.toMonoidHom))

private theorem monomialCharacter_natural {M N : Type u} [CommGroup M] [CommGroup N]
    (f : M →* N) (m : M) :
    specGroupMap (groupAlgebraMap k f) ≫ monomialCharacter (k := k) m =
      monomialCharacter (k := k) (f m) := by
  rw [← specGroupMap_comp]
  congr 1
  apply CommHopfAlgCat.hom_ext
  change (MonoidAlgebra.mapDomainBialgHom k f).comp
    (MonoidAlgebra.mapDomainBialgHom k ((zpowersHom M m).comp MulEquiv.ulift.toMonoidHom)) =
      MonoidAlgebra.mapDomainBialgHom k ((zpowersHom N (f m)).comp MulEquiv.ulift.toMonoidHom)
  rw [← MonoidAlgebra.mapDomainBialgHom_comp]
  congr 1
  ext z
  exact map_zpow f m z.down.toAdd

private def sectionsOfDiagonal (M : Type u) [CommGroup M] (S : SchemeOver k) :
    (S ⟶ (specGroup (groupAlgebra k M)).X) ≃ (M →* (coordinates S)ˣ) :=
  ((algΓAlgSpecAdjunction (CommRingCat.of k)).homEquiv S
      (op (CommAlgCat.of k (MonoidAlgebra k M)))).symm.trans
    (Equiv.trans
      (show ((algΓ (CommRingCat.of k)).obj S ⟶ op (CommAlgCat.of k (MonoidAlgebra k M))) ≃
          (MonoidAlgebra k M →ₐ[k] coordinates S) from
        { toFun := fun f => f.unop.hom
          invFun := fun f => (CommAlgCat.ofHom f).op
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl })
      ((MonoidAlgebra.lift k (coordinates S) M).symm.trans
        MonoidHom.toHomUnitsMulEquiv.toEquiv))

private theorem sectionsOfDiagonal_precompose
    {M N : Type u} [CommGroup M] [CommGroup N] (S : SchemeOver k)
    (f : M →* N) (x : S ⟶ (specGroup (groupAlgebra k N)).X) (a : M) :
    sectionsOfDiagonal M S (x ≫ (specGroupMap (groupAlgebraMap k f)).hom.hom) a =
      sectionsOfDiagonal N S x (f a) := by
  apply Units.ext
  let m := op (CommAlgCat.of k (MonoidAlgebra k M))
  let n := op (CommAlgCat.of k (MonoidAlgebra k N))
  let φ : n ⟶ m := (CommAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom k f).toAlgHom).op
  let adj := algΓAlgSpecAdjunction (CommRingCat.of k)
  change ((adj.homEquiv S m).symm (x ≫ (testSpec k).map φ)).unop.hom
    (MonoidAlgebra.of k M a) = ((adj.homEquiv S n).symm x).unop.hom
      (MonoidAlgebra.of k N (f a))
  rw [adj.homEquiv_naturality_right_symm x φ, unop_comp]
  let F := ((adj.homEquiv S n).symm x).unop.hom
  change F (MonoidAlgebra.mapDomainBialgHom k f (MonoidAlgebra.single a 1)) =
    F (MonoidAlgebra.single (f a) 1)
  rw [MonoidAlgebra.mapDomainBialgHom_single]

private theorem diagonal_basis_sections {M I : Type u} [CommGroup M]
    (b : Module.Basis I ℤ (Additive M)) (S : SchemeOver k) :
    Function.Bijective (fun t : S ⟶ (specGroup (groupAlgebra k M)).X =>
      fun α => t ≫ (monomialCharacter (k := k) (Additive.toMul (b α))).hom.hom) := by
  let ev : (S ⟶ (specGroup (groupAlgebra k IntegerCharacters)).X) ≃ (coordinates S)ˣ :=
    (sectionsOfDiagonal IntegerCharacters S).trans
      (integerHomEquiv ((coordinates S)ˣ)).symm.toEquiv
  let eval : (I → (S ⟶ (specGroup (groupAlgebra k IntegerCharacters)).X)) ≃
      (I → (coordinates S)ˣ) :=
    Equiv.piCongrRight fun _ => ev
  have heval (t : S ⟶ (specGroup (groupAlgebra k M)).X) (i : I) :
      eval (fun α => t ≫ (monomialCharacter (k := k) (Additive.toMul (b α))).hom.hom) i =
        sectionsOfDiagonal M S t (Additive.toMul (b i)) := by
    change sectionsOfDiagonal IntegerCharacters S
      (t ≫ (monomialCharacter (k := k) (Additive.toMul (b i))).hom.hom) integerGenerator = _
    rw [sectionsOfDiagonal_precompose]
    congr 1
    exact zpow_one _
  let e : (M →* (coordinates S)ˣ) ≃ (I → (coordinates S)ˣ) :=
    { toFun := fun f i => f (Additive.toMul (b i))
      invFun := fun g =>
        let l : Additive M →ₗ[ℤ] Additive ((coordinates S)ˣ) :=
          b.constr ℤ (fun i => Additive.ofMul (g i))
        { toFun := fun m => Additive.toMul (l (Additive.ofMul m))
          map_one' := l.map_zero
          map_mul' := fun m n => l.map_add (Additive.ofMul m) (Additive.ofMul n) }
      left_inv := by
        intro f
        let l : Additive M →ₗ[ℤ] Additive ((coordinates S)ˣ) :=
          (show Additive M →+ Additive ((coordinates S)ˣ) from
            { toFun := fun m => Additive.ofMul (f (Additive.toMul m))
              map_zero' := f.map_one
              map_add' := fun m n => f.map_mul (Additive.toMul m) (Additive.toMul n) }).toIntLinearMap
        have hl : b.constr ℤ (fun i => Additive.ofMul (f (Additive.toMul (b i)))) = l := by
          apply b.ext
          intro i
          rw [Module.Basis.constr_basis]
          rfl
        apply MonoidHom.ext
        intro m
        exact congrArg (fun L : Additive M →ₗ[ℤ] Additive ((coordinates S)ˣ) =>
          Additive.toMul (L (Additive.ofMul m))) hl
      right_inv := by
        intro g
        funext i
        change Additive.toMul (b.constr ℤ (fun j => Additive.ofMul (g j)) (b i)) = _
        rw [Module.Basis.constr_basis]
        rfl }
  let iso := ((sectionsOfDiagonal M S).trans e).trans eval.symm
  convert iso.bijective using 1
  funext t
  apply eval.injective
  funext i
  exact (heval t i).trans
    (congrFun (eval.apply_symm_apply (e (sectionsOfDiagonal M S t))) i).symm

set_option maxHeartbeats 800000 in
/-- The simple roots form an integral basis of the character lattice of the adjoint torus. -/
theorem simpleRootsBasis {k : Type u} [Field k] {A : AdditiveLine k}
    (P : PinnedGroup A) (D : AttachedDatum P.pair) :
    ∃ b : Module.Basis (SimpleRoot P.pair) ℤ (Additive (rootLattice P.pair.T)),
      ∀ α, (Additive.toMul (b α)).val = α.val.val := by
  let := D.comm
  let R := D.datum.rootDatum
  let N := rootLattice P.pair.T
  have hroots : Set.range R.root = Additive.ofMul '' CharacterPairing.absoluteRoots P.pair.T := by
    ext x
    constructor
    · rintro ⟨α, rfl⟩
      exact ⟨α.val, α.property, (D.datum.root_eq α).symm⟩
    · rintro ⟨α, hα, rfl⟩
      exact ⟨⟨α, hα⟩, D.datum.root_eq ⟨α, hα⟩⟩
  have h : (R.rootSpan ℤ).toAddSubgroup = N.toAddSubgroup := by
    change (Submodule.span ℤ (Set.range R.root)).toAddSubgroup = N.toAddSubgroup
    rw [Submodule.span_int_eq_addSubgroupClosure, hroots]
    change AddSubgroup.closure _ =
      (Subgroup.closure (CharacterPairing.absoluteRoots P.pair.T)).toAddSubgroup
    rw [Subgroup.toAddSubgroup_closure]
    congr 1
    ext x
    exact ⟨fun ⟨α, hα, h⟩ => by simpa [← h] using hα,
      fun hx => ⟨Additive.toMul x, hx, rfl⟩⟩
  let e : R.rootSpan ℤ ≃ₗ[ℤ] Additive N :=
    { toFun := fun x => Additive.ofMul ⟨Additive.toMul x.val,
        show x.val ∈ N.toAddSubgroup from h ▸ x.property⟩
      invFun := fun x => ⟨Additive.ofMul (Additive.toMul x).val,
        show Additive.ofMul (Additive.toMul x).val ∈ (R.rootSpan ℤ).toAddSubgroup from
          h.symm ▸ (Additive.toMul x).property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let i := Equiv.subtypeEquivRight D.simple_iff
  refine ⟨(D.base.toWeightBasisInt.map e).reindex i, ?_⟩
  intro α
  rw [Module.Basis.reindex_apply, Module.Basis.map_apply]
  change Additive.toMul (D.base.toWeightBasisInt (i.symm α)).val = α.val.val
  rw [RootPairing.Base.coe_toWeightBasisInt_apply, D.datum.root_eq]
  rfl

set_option maxHeartbeats 900000 in
/-- The adjoint image of the pinned torus is the diagonal group of the root lattice. -/
theorem adjointTorus_exists {A : AdditiveLine k} (P : PinnedGroup A)
    (D : AttachedDatum P.pair) (Q : AdjointQuotient P.pair.G) :
    Nonempty (AdjointTorus P Q) := by
  let T := P.pair.T
  let M := CharacterDescent.Character T.group
  let N := rootLattice T
  obtain ⟨hfg, e, he, hc, hZ, _⟩ := RootData.SchemeCentre.schemeCentre
    P.pair.G P.pair.reductive T P.pair.split P.pair.maximal
  letI : Group.FG M := hfg
  let X := diagonalGroup k M
  let Y := specGroup (groupAlgebra k N)
  let q : X.val ⟶ Y := diagonalRestriction k N
  let i : X.val ⟶ P.pair.G.val := e.hom ≫ T.inclusion
  obtain ⟨I, p, j, hp, _, _⟩ := LinearAlgebraicGroups.schemeImageFactorization
    X Q.quotient (i ≫ Q.projection)
  obtain ⟨hdc, hqflat, hqsurj, hqfp, hqker, _⟩ :=
    LinearAlgebraicGroups.DiagonalizableGroups.diagonalRestrictionKernelAndQuotient k M N
  have hq : IsFppf q.hom.hom.left := ⟨hqflat, hqsurj, hqfp⟩
  have hpf : IsFppf p.hom.hom.left := ⟨hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
  let v := Grp.forget (SchemeOver k)
  haveI := T.isClosedImmersion
  haveI : Mono T.inclusion.hom.hom := Over.mono_of_mono_left T.inclusion.hom.hom
  haveI : Mono (v.map i) := by
    change Mono (v.map (e.hom ≫ T.inclusion))
    rw [Functor.map_comp]
    haveI : IsIso (v.map e.hom) := v.map_isIso e.hom
    haveI : Mono (v.map T.inclusion) := inferInstanceAs (Mono T.inclusion.hom.hom)
    exact mono_comp _ _
  haveI : Mono j.hom.hom := by
    haveI : IsClosedImmersion j.hom.hom.left := hp.2.2.2.2.2
    exact Over.mono_of_mono_left _
  have ker (S : SchemeOver k) (g : S ⟶ X.val.X) :
      g ≫ p.hom.hom = 1 ↔ g ≫ q.hom.hom = 1 := by
    have hp' : g ≫ p.hom.hom = 1 ↔ (g ≫ p.hom.hom) ≫ j.hom.hom = 1 := by
      rw [← MonObj.one_comp j.hom.hom]
      exact (cancel_mono j.hom.hom).symm
    have hpi := congrArg (fun f => f.hom.hom) hp.1
    change p.hom.hom ≫ j.hom.hom = i.hom.hom ≫ Q.projection.hom.hom at hpi
    rw [hp', Category.assoc, hpi, ← Category.assoc, projection_eq_one_iff,
      innerAut_eq_one_iff]
    refine (hZ S (g ≫ i.hom.hom)).trans
      (Iff.trans ?_ (schemeKernel_sections hqker g))
    change (∃ z : S ⟶ (specGroup (groupAlgebra k (M ⧸ N))).X,
      z ≫ ((diagonalClosedInclusion k N).hom.hom ≫ v.map i) = g ≫ v.map i) ↔
      (∃ z : S ⟶ (specGroup (groupAlgebra k (M ⧸ N))).X,
        z ≫ (diagonalClosedInclusion k N).hom.hom = g)
    simp only [← Category.assoc, cancel_mono]
  have equivKer (S : (SchemeOver k)ᵒᵖ) (x y : (groupSections X.val).obj S) :
      (groupSectionsMap q).app S x = (groupSectionsMap q).app S y ↔
      (groupSectionsMap p).app S (((Iso.refl (groupSections X.val)).hom.app S) x) =
        (groupSectionsMap p).app S (((Iso.refl (groupSections X.val)).hom.app S) y) := by
    simp only [Iso.refl_hom, NatTrans.id_app, GrpCat.id_apply]
    change (groupSectionsMap q).app S x = (groupSectionsMap q).app S y ↔
      (groupSectionsMap p).app S x = (groupSectionsMap p).app S y
    rw [← div_eq_one (a := (groupSectionsMap q).app S x),
      ← div_eq_one (a := (groupSectionsMap p).app S x), ← map_div, ← map_div]
    change ULift.up ((x / y).down ≫ q.hom.hom) = ULift.up 1 ↔
      ULift.up ((x / y).down ≫ p.hom.hom) = ULift.up 1
    simpa only [ULift.up_inj] using (ker S.unop (x / y).down).symm
  obtain ⟨a, ha⟩ := descends_iso_of_locallySurjective (groupSectionsMap q)
    (groupSectionsMap p) (Iso.refl _)
    (groupSectionsMap_locallySurjective q hq) (groupSectionsMap_locallySurjective p hpf)
    (groupSections_isSheaf Y) (groupSections_isSheaf I.val) equivKer
  let ff := groupSectionsFullyFaithful (k := k)
  let r : Y ≅ I.val := ff.preimageIso a
  have hr : q ≫ r.hom = p := by
    apply ff.map_injective
    change groupSectionsMap (q ≫ r.hom) = groupSectionsMap p
    rw [show groupSectionsMap (q ≫ r.hom) = groupSectionsMap q ≫ groupSectionsMap r.hom
      from (yonedaGrp ⋙
        (Functor.whiskeringRight _ _ _).obj Fppf.liftGroups.{u,u+1}).map_comp q r.hom,
      show groupSectionsMap r.hom = a.hom from ff.map_preimage _]
    simpa using ha
  let inc : Y ⟶ Q.quotient.val := r.hom ≫ j
  let proj : T.group ⟶ Y := e.inv ≫ q
  have hInc : IsClosedImmersion inc.hom.hom.left := by
    let f := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
    haveI : IsIso r.hom.hom.hom.left := f.map_isIso r.hom
    haveI : IsClosedImmersion j.hom.hom.left := hp.2.2.2.2.2
    change IsClosedImmersion (r.hom.hom.hom.left ≫ j.hom.hom.left)
    exact IsClosedImmersion.comp _ _
  have hProj : IsFppf proj.hom.hom.left := by
    let f := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
    haveI : IsIso e.inv.hom.hom.left := f.map_isIso e.inv
    change IsFppf (e.inv.hom.hom.left ≫ q.hom.hom.left)
    letI : Flat q.hom.hom.left := hqflat
    letI : Surjective q.hom.hom.left := hqsurj
    letI : LocallyOfFinitePresentation q.hom.hom.left := hqfp
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨b, hb⟩ := simpleRootsBasis P D
  let c (α : SimpleRoot P.pair) := monomialCharacter (k := k) (Additive.toMul (b α))
  refine ⟨⟨⟨Y, inc, hInc⟩, proj, hProj, ?_, c, ?_, diagonal_basis_sections b⟩⟩
  · change (e.inv ≫ q) ≫ r.hom ≫ j = T.inclusion ≫ Q.projection
    simp only [Category.assoc, ← Category.assoc q, hr, hp.1, i, Iso.inv_hom_id_assoc]
  · intro α
    change (e.inv ≫ q) ≫ c α = α.val.val
    have hmon : e.hom ≫ α.val.val = monomialCharacter (k := k) α.val.val := he α.val.val
    rw [Category.assoc, show q ≫ c α = monomialCharacter (k := k) α.val.val from
      (monomialCharacter_natural N.subtype _).trans (congrArg monomialCharacter (hb α)),
      ← hmon, Iso.inv_hom_id_assoc]

end AdjointTorusCoordinates

section ScalarTorusCharacters

open Specs.DiagonalizableGroups (characterValuedPoints)

variable {k : Type u} [Field k] (R : TestAlgebra k)
variable {M N : Type u} [CommGroup M] [CommGroup N]

/-- Characters with values in the units of scalar test algebras. -/
private abbrev scalarCharacters (M : Type u) [CommGroup M] :=
  Under.forget R ⋙ characterValuedPoints k M

private abbrev scalarTest (S : Type u) [CommRing S] [Algebra k S] [Algebra R S]
    [IsScalarTower k R S] : Under R :=
  Under.mk (CommAlgCat.ofHom (IsScalarTower.toAlgHom k R S))

private def scalarTestMap {S T : Type u} [CommRing S] [CommRing T]
    [Algebra k S] [Algebra k T] [Algebra R S] [Algebra R T]
    [IsScalarTower k R S] [IsScalarTower k R T] (φ : S →ₐ[R] T) :
    scalarTest R S ⟶ scalarTest R T :=
  Under.homMk (CommAlgCat.ofHom (φ.restrictScalars k)) (by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    exact φ.commutes)

private abbrev universalCharacter (R M : Type u) [CommRing R] [CommGroup M] :
    M →* (MonoidAlgebra R M)ˣ := (MonoidAlgebra.of R M).toHomUnits

private abbrev scalarTransform (f : scalarCharacters R N ⟶ scalarCharacters R M)
    (U : Under R) : (N →* U.rightˣ) →* (M →* U.rightˣ) := (f.app U).hom

private def characterExpansion (f : scalarCharacters R N ⟶ scalarCharacters R M) :
    M →* MonoidAlgebra R N :=
  MonoidHom.toHomUnitsMulEquiv.symm <|
    scalarTransform R f (scalarTest R (MonoidAlgebra R N)) (universalCharacter R N)

private theorem characterExpansion_map (f : scalarCharacters R N ⟶ scalarCharacters R M)
    {S : Type u} [CommRing S] [Algebra R S] [Algebra k S] [IsScalarTower k R S]
    (φ : MonoidAlgebra R N →ₐ[R] S) (m : M) :
    φ (characterExpansion R f m) =
      (scalarTransform R f (scalarTest R S) ((Units.map φ.toMonoidHom).comp (universalCharacter R N)) m).val := by
  have h := NatTrans.naturality_apply f (scalarTestMap R φ) (universalCharacter R N)
  exact congrArg (fun h : M →* Sˣ => (h m).val) h.symm

private theorem characterExpansion_isGroupLike
    (f : scalarCharacters R N ⟶ scalarCharacters R M) (m : M) :
    IsGroupLikeElem R (characterExpansion R f m) := by
  let A := MonoidAlgebra R N
  let : CommRing A := inferInstanceAs (CommRing (MonoidAlgebra R N))
  constructor
  · change Bialgebra.counitAlgHom R A (characterExpansion R f m) = 1
    rw [characterExpansion_map]
    have h : (Units.map (Bialgebra.counitAlgHom R A).toMonoidHom).comp
        (universalCharacter R N) = 1 := by
      apply MonoidHom.ext
      intro n
      apply Units.ext
      exact (MonoidAlgebra.isGroupLikeElem_of (R := R) n).counit_eq_one
    rw [h, map_one]
    rfl
  · let : CommMonoid (A ⊗[R] A)ˣ := inferInstance
    let a : A →ₐ[R] A ⊗[R] A := Algebra.TensorProduct.includeLeft
    let b : A →ₐ[R] A ⊗[R] A := Algebra.TensorProduct.includeRight
    have h : (Units.map (Bialgebra.comulAlgHom R A).toMonoidHom).comp
          (universalCharacter R N) =
        (Units.map a.toMonoidHom).comp (universalCharacter R N) *
          (Units.map b.toMonoidHom).comp (universalCharacter R N) := by
      apply MonoidHom.ext
      intro n
      apply Units.ext
      change comul (R := R) (MonoidAlgebra.of R N n) =
        a (MonoidAlgebra.of R N n) * b (MonoidAlgebra.of R N n)
      rw [(MonoidAlgebra.isGroupLikeElem_of (R := R) n).comul_eq_tmul_self]
      simp [a, b, Algebra.TensorProduct.tmul_mul_tmul]
    change Bialgebra.comulAlgHom R A (characterExpansion R f m) = _
    rw [characterExpansion_map, h, map_mul]
    change ((scalarTransform R f (scalarTest R (A ⊗[R] A))
      ((Units.map a.toMonoidHom).comp (universalCharacter R N)) m).val) *
        ((scalarTransform R f (scalarTest R (A ⊗[R] A))
          ((Units.map b.toMonoidHom).comp (universalCharacter R N)) m).val) = _
    rw [← characterExpansion_map R f a, ← characterExpansion_map R f b]
    change (characterExpansion R f m ⊗ₜ[R] (1 : A)) *
      ((1 : A) ⊗ₜ[R] characterExpansion R f m) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

private theorem counit_mapCoefficients {R S N : Type u} [CommRing R] [CommRing S]
    [CommGroup N] (a : R →+* S) (x : MonoidAlgebra R N) :
    counit (R := S) (MonoidAlgebra.mapRingHom N a x) = a (counit (R := R) x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single n r => rw [MonoidAlgebra.mapRingHom_single, MonoidAlgebra.counit_single,
      MonoidAlgebra.counit_single]; rfl

/-- If a monomial label is constant after a change of coefficients, then the
base-changed group-like element is that monomial, including over nonreduced rings. -/
theorem groupLike_map_eq_single {R S N : Type u} [CommRing R] [CommRing S] [CommGroup N]
    {x : MonoidAlgebra R N} (hx : IsGroupLikeElem R x) (a : R →+* S) (n : N)
    (h : ∀ p : PrimeSpectrum S, groupLikeMonomial hx (PrimeSpectrum.comap a p) = n) :
    MonoidAlgebra.mapRingHom N a x = MonoidAlgebra.single n 1 := by
  classical
  let y := MonoidAlgebra.mapRingHom N a x
  have hzero (j : N) (hj : j ≠ n) : y.coeff j = 0 := by
    have idem : IsIdempotentElem (y.coeff j) := by
      change y.coeff j * y.coeff j = y.coeff j
      simp only [y, MonoidAlgebra.coeff_mapRingHom, ← map_mul, (groupLike_coeff hx).1]
    apply idem.eq_zero_of_isNilpotent
    rw [← mem_nilradical, PrimeSpectrum.nilradical_eq_iInf, Ideal.mem_iInf]
    intro p
    change a (x.coeff j) ∈ p.asIdeal
    by_contra hn
    have hm := (existsUnique_coeff_not_mem hx (PrimeSpectrum.comap a p)).choose_spec.2 j hn
    exact hj (hm.trans (h p))
  have hy : y = MonoidAlgebra.single n (y.coeff n) := by
    ext j
    by_cases hj : j = n
    · subst j
      simp
    · rw [hzero j hj]
      simp [Ne.symm hj]
  have hc : counit (R := S) y = 1 := by
    rw [counit_mapCoefficients, hx.counit_eq_one, map_one]
  have hn : y.coeff n = 1 := by
    rw [hy, MonoidAlgebra.counit_single] at hc
    exact hc
  change y = _
  conv_lhs => rw [hy]
  rw [hn]

private def exponentAt (f : scalarCharacters R N ⟶ scalarCharacters R M)
    (p : PrimeSpectrum R) : M →* N where
  toFun m := groupLikeMonomial (characterExpansion_isGroupLike R f m) p
  map_one' := by
    let := p.isPrime
    apply MonoidAlgebra.single_left_injective (R := R ⧸ p.asIdeal) one_ne_zero
    change MonoidAlgebra.single (groupLikeMonomial (characterExpansion_isGroupLike R f 1) p)
      (1 : R ⧸ p.asIdeal) = MonoidAlgebra.single (1 : N) 1
    rw [← groupLike_specialize (characterExpansion_isGroupLike R f 1) p, map_one, map_one]
    rfl
  map_mul' m n := by
    let := p.isPrime
    apply MonoidAlgebra.single_left_injective (R := R ⧸ p.asIdeal) one_ne_zero
    change MonoidAlgebra.single
      (groupLikeMonomial (characterExpansion_isGroupLike R f (m * n)) p)
      (1 : R ⧸ p.asIdeal) = MonoidAlgebra.single
      (groupLikeMonomial (characterExpansion_isGroupLike R f m) p *
        groupLikeMonomial (characterExpansion_isGroupLike R f n) p) 1
    rw [← groupLike_specialize (characterExpansion_isGroupLike R f (m * n)) p,
      map_mul, map_mul, groupLike_specialize (characterExpansion_isGroupLike R f m) p,
      groupLike_specialize (characterExpansion_isGroupLike R f n) p, MonoidAlgebra.single_mul_single,
      one_mul]

private theorem exponentAt_locallyConstant [Group.FG M]
    (f : scalarCharacters R N ⟶ scalarCharacters R M) : IsLocallyConstant (exponentAt R f) := by
  classical
  obtain ⟨s, hs, hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG M)
  let : Finite s := hfin
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro g
  have h : {p | exponentAt R f p = g} =
      ⋂ m : s, {p | groupLikeMonomial (characterExpansion_isGroupLike R f m.val) p = g m.val} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    refine ⟨fun h m => DFunLike.congr_fun h m.val, fun h => ?_⟩
    apply MonoidHom.ext
    intro m
    apply MonoidHom.eqOn_closure (s := s) (fun j hj => h ⟨j, hj⟩)
    simp [hs]
  change IsOpen {p | exponentAt R f p = g}
  rw [h]
  exact isOpen_iInter_of_finite fun m =>
    (groupLikeMonomial (characterExpansion_isGroupLike R f m.val)).isLocallyConstant.isOpen_fiber _

private theorem scalarTransform_eq_of_expansion
    (f : scalarCharacters R N ⟶ scalarCharacters R M)
    {S : Type u} [CommRing S] [Algebra R S] [Algebra k S] [IsScalarTower k R S]
    (e : M →* N)
    (he : ∀ m, MonoidAlgebra.mapRingHom N (algebraMap R S) (characterExpansion R f m) =
      MonoidAlgebra.single (e m) 1)
    (x : N →* Sˣ) : scalarTransform R f (scalarTest R S) x = x.comp e := by
  let b : MonoidAlgebra S N →ₐ[S] S := MonoidAlgebra.lift S S N
    (MonoidHom.toHomUnitsMulEquiv.symm x)
  let a : MonoidAlgebra R N →ₐ[R] MonoidAlgebra S N :=
    MonoidAlgebra.mapAlgHom N (Algebra.ofId R S)
  let φ := (b.restrictScalars R).comp a
  have hu : (Units.map φ.toMonoidHom).comp (universalCharacter R N) = x := by
    apply MonoidHom.ext
    intro n
    apply Units.ext
    change b (MonoidAlgebra.mapRingHom N (algebraMap R S) (MonoidAlgebra.single n 1)) = _
    rw [MonoidAlgebra.mapRingHom_single, map_one]
    exact MonoidAlgebra.lift_of (MonoidHom.toHomUnitsMulEquiv.symm x) n
  apply MonoidHom.ext
  intro m
  apply Units.ext
  have h := characterExpansion_map R f φ m
  rw [hu] at h
  rw [← h]
  change b (MonoidAlgebra.mapRingHom N (algebraMap R S) (characterExpansion R f m)) = _
  rw [he]
  exact MonoidAlgebra.lift_of (MonoidHom.toHomUnitsMulEquiv.symm x) (e m)

private theorem scalarTransform_eq_over_prime
    (f : scalarCharacters R N ⟶ scalarCharacters R M) (p : PrimeSpectrum R)
    {S : Type u} [CommRing S] [Algebra (R ⧸ p.asIdeal) S] [Algebra R S] [Algebra k S]
    [IsScalarTower R (R ⧸ p.asIdeal) S] [IsScalarTower k R S]
    (x : N →* Sˣ) :
    scalarTransform R f (scalarTest R S) x = x.comp (exponentAt R f p) := by
  apply scalarTransform_eq_of_expansion R f (exponentAt R f p) _ x
  intro m
  rw [IsScalarTower.algebraMap_eq R (R ⧸ p.asIdeal) S,
    MonoidAlgebra.mapRingHom_comp, RingHom.comp_apply]
  change MonoidAlgebra.mapRingHom N (algebraMap (R ⧸ p.asIdeal) S)
    (MonoidAlgebra.mapRingHom N (Ideal.Quotient.mk p.asIdeal) (characterExpansion R f m)) = _
  rw [groupLike_specialize (characterExpansion_isGroupLike R f m) p,
    MonoidAlgebra.mapRingHom_single, map_one]
  rfl

/-- At each prime, the exponents of a scalar torus isomorphism are inverse
lattice isomorphisms for the two directions of the original map. -/
private def exponentIsoAt (f : scalarCharacters R N ≅ scalarCharacters R M)
    (p : PrimeSpectrum R) : M ≃* N where
  toFun := exponentAt R f.hom p
  invFun := exponentAt R f.inv p
  left_inv m := by
    let := p.isPrime
    let S := MonoidAlgebra (R ⧸ p.asIdeal) M
    let U := scalarTest R S
    let x := universalCharacter (R ⧸ p.asIdeal) M
    have h := (f.app U).groupIsoToMulEquiv.apply_symm_apply x
    change scalarTransform R f.hom U (scalarTransform R f.inv U x) = x at h
    unfold U at h
    rw [scalarTransform_eq_over_prime R f.inv p, scalarTransform_eq_over_prime R f.hom p] at h
    apply MonoidAlgebra.single_left_injective (R := R ⧸ p.asIdeal) one_ne_zero
    exact congrArg (fun g : M →* Sˣ => (g m).val) h
  right_inv n := by
    let := p.isPrime
    let S := MonoidAlgebra (R ⧸ p.asIdeal) N
    let U := scalarTest R S
    let x := universalCharacter (R ⧸ p.asIdeal) N
    have h := (f.app U).groupIsoToMulEquiv.symm_apply_apply x
    change scalarTransform R f.inv U (scalarTransform R f.hom U x) = x at h
    unfold U at h
    rw [scalarTransform_eq_over_prime R f.hom p, scalarTransform_eq_over_prime R f.inv p] at h
    apply MonoidAlgebra.single_left_injective (R := R ⧸ p.asIdeal) one_ne_zero
    exact congrArg (fun g : N →* Sˣ => (g n).val) h
  map_mul' := (exponentAt R f.hom p).map_mul

/-- Scalar isomorphisms of diagonalizable groups are locally constant on their
finitely generated character lattices. Over any scalar algebra whose spectrum
lands in one fiber of the label, the original relative map acts through that
lattice isomorphism. -/
theorem scalarCharacterIsomorphism_locallyConstant [Group.FG M]
    (f : (Under.forget R ⋙ characterValuedPoints k N) ≅
      (Under.forget R ⋙ characterValuedPoints k M)) :
    ∃ label : LocallyConstant (PrimeSpectrum R) (M ≃* N),
      ∀ (U : Under R) (e : M ≃* N),
        (∀ p : PrimeSpectrum U.right, label (PrimeSpectrum.comap U.hom.hom.toRingHom p) = e) →
        ∀ x : N →* U.rightˣ,
          (show M →* U.rightˣ from (f.hom.app U).hom x) = x.comp e.toMonoidHom := by
  refine ⟨⟨exponentIsoAt R f, ?_⟩, ?_⟩
  · rw [IsLocallyConstant.iff_isOpen_fiber]
    intro e
    have eq : {p | exponentIsoAt R f p = e} = {p | exponentAt R f.hom p = e.toMonoidHom} := by
      ext p
      refine ⟨fun h => congrArg MulEquiv.toMonoidHom h, fun h => ?_⟩
      exact MulEquiv.ext fun m => DFunLike.congr_fun h m
    change IsOpen {p | exponentIsoAt R f p = e}
    rw [eq]
    exact (exponentAt_locallyConstant R f.hom).isOpen_fiber _
  · intro U
    obtain ⟨S, a, rfl⟩ := Under.mk_surjective U
    intro e he x
    let : Algebra R S := a.hom.toAlgebra
    let : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq' a.hom.comp_algebraMap.symm
    change scalarTransform R f.hom (Under.mk a) x = _
    -- The scalar structure used in the expansion is given by the structure map of `U`.
    have hh := scalarTransform_eq_of_expansion R f.hom e.toMonoidHom
      (fun m => groupLike_map_eq_single (characterExpansion_isGroupLike R f.hom m)
        a.hom.toRingHom (e m) (fun p => congrArg (fun g : M ≃* N => g m) (he p))) x
    exact hh

end ScalarTorusCharacters

section LocallyScalarTorus

open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap)
open Specs.GeometricRadicals (IsSplitTorus)
open private specGroupMap_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private pointsIso_precompose from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private splitPresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing

variable {k : Type u} [Field k]

/-- The affine test schemes of the big slice over the spectrum of a test algebra. -/
private def affineSlice (R : TestAlgebra k) : (Under R)ᵒᵖ ⥤ Over ((testSpec k).obj (op R)) where
  obj U := Over.mk ((testSpec k).map U.unop.hom.op)
  map a := Over.homMk ((testSpec k).map a.unop.right.op) (by
    change (testSpec k).map a.unop.right.op ≫ (testSpec k).map _ = (testSpec k).map _
    rw [← Functor.map_comp, ← op_comp, Under.w])
  map_id _ := Over.OverMorphism.ext (by simp)
  map_comp _ _ := Over.OverMorphism.ext (by simp [op_comp])

private abbrev relativeEvaluate {G H : GroupScheme k} {S : SchemeOver k}
    (f : relativePoints G S ⟶ relativePoints H S) (U : Over S) (x : U.left ⟶ G.X) :
    U.left ⟶ H.X := (f.app (op U)).hom x

private theorem relativeEvaluate_naturality {G H : GroupScheme k} {S : SchemeOver k}
    (f : relativePoints G S ⟶ relativePoints H S) {U V : Over S} (a : V ⟶ U)
    (x : U.left ⟶ G.X) : relativeEvaluate f V (a.left ≫ x) =
    a.left ≫ relativeEvaluate f U x := NatTrans.naturality_apply f a.op x

/-- Relative morphisms of group schemes are determined on the affine test
schemes of the slice, even over a nonaffine base. -/
private theorem relativeHom_ext_affine {G H : GroupScheme k} {S : SchemeOver k}
    (f g : relativePoints G S ⟶ relativePoints H S)
    (h : ∀ (R : TestAlgebra k) (a : (testSpec k).obj (op R) ⟶ S)
      (x : (testSpec k).obj (op R) ⟶ G.X),
        relativeEvaluate f (Over.mk a) x = relativeEvaluate g (Over.mk a) x) : f = g := by
  apply NatTrans.ext
  funext U
  apply GrpCat.ext
  intro x
  let C := U.unop.left.left.affineCover
  change relativeEvaluate f U.unop x = relativeEvaluate g U.unop x
  apply Over.OverMorphism.ext
  apply C.hom_ext
  intro i
  let W : SchemeOver k := Over.mk (C.f i ≫ U.unop.left.hom)
  let b : W ⟶ U.unop.left := Over.homMk (C.f i)
  obtain ⟨R, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr
    (show IsAffine W.left from Scheme.isAffine_affineCover _ _)
  let a := e.hom ≫ b
  let c : Over.mk (a ≫ U.unop.hom) ⟶ U.unop := Over.homMk a
  have ha := h R.unop (a ≫ U.unop.hom) (a ≫ x)
  change relativeEvaluate f _ (c.left ≫ x) = relativeEvaluate g _ (c.left ≫ x) at ha
  rw [relativeEvaluate_naturality f c x, relativeEvaluate_naturality g c x] at ha
  have ha' := congrArg (fun p => p.left) ha
  change (e.hom.left ≫ C.f i) ≫ (relativeEvaluate f U.unop x).left =
    (e.hom.left ≫ C.f i) ≫ (relativeEvaluate g U.unop x).left at ha'
  let : IsIso e.hom.left := ((Over.forget _).mapIso e).isIso_hom
  simpa only [Category.assoc, cancel_epi] using ha'

private def diagonalGroundAut {M : Type u} [CommGroup M] (e : M ≃* M) :
    Aut (specGroup (groupAlgebra k M)) :=
  Aut.of {
    hom := specGroupMap (groupAlgebraMap k e.toMonoidHom)
    inv := specGroupMap (groupAlgebraMap k e.symm.toMonoidHom)
    hom_inv_id := by
      rw [← specGroupMap_comp]
      have eq : groupAlgebraMap k e.symm.toMonoidHom ≫ groupAlgebraMap k e.toMonoidHom = 𝟙 _ := by
        apply CommHopfAlgCat.hom_ext
        rw [show (groupAlgebraMap k e.symm.toMonoidHom ≫ groupAlgebraMap k e.toMonoidHom).hom =
          (MonoidAlgebra.mapDomainBialgHom k e.toMonoidHom).comp
            (MonoidAlgebra.mapDomainBialgHom k e.symm.toMonoidHom) from rfl,
          ← MonoidAlgebra.mapDomainBialgHom_comp, (show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id M by ext x; exact e.apply_symm_apply x),
          MonoidAlgebra.mapDomainBialgHom_id]
        rfl
      rw [eq]
      exact (hopfSpec (R := CommRingCat.of k)).map_id _
    inv_hom_id := by
      rw [← specGroupMap_comp]
      have eq : groupAlgebraMap k e.toMonoidHom ≫ groupAlgebraMap k e.symm.toMonoidHom = 𝟙 _ := by
        apply CommHopfAlgCat.hom_ext
        rw [show (groupAlgebraMap k e.toMonoidHom ≫ groupAlgebraMap k e.symm.toMonoidHom).hom =
          (MonoidAlgebra.mapDomainBialgHom k e.symm.toMonoidHom).comp
            (MonoidAlgebra.mapDomainBialgHom k e.toMonoidHom) from rfl,
          ← MonoidAlgebra.mapDomainBialgHom_comp, (show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id M by ext x; exact e.symm_apply_apply x),
          MonoidAlgebra.mapDomainBialgHom_id]
        rfl
      rw [eq]
      exact (hopfSpec (R := CommRingCat.of k)).map_id _ }

/-- The sieve on which the split-torus automorphism comes from a field
lattice automorphism through scalar extension. -/
def scalarAutomorphismSieve {G : GroupScheme k} {S : SchemeOver k}
    (f : RelativeAut G S) : Sieve S where
  arrows U b := ∃ e : Aut G, restrictAut b f = scalarAut e U
  downward_closed := by
    intro U V b h a
    obtain ⟨e, he⟩ := h
    refine ⟨e, ?_⟩
    have hcomp : restrictAut a (restrictAut b f) = restrictAut (a ≫ b) f :=
      (ConcreteCategory.congr_hom ((automorphisms G).map_comp b.op a.op) f).symm
    rw [← hcomp, he]
    rfl

private theorem diagonalScalar_on_fibers {M : Type u} [CommGroup M] [Group.FG M]
    (R : TestAlgebra k) (f : RelativeAut (specGroup (groupAlgebra k M))
      ((testSpec k).obj (op R))) :
    ∃ label : LocallyConstant (PrimeSpectrum R) (M ≃* M),
      ∀ (V : SchemeOver k) (b : V ⟶ (testSpec k).obj (op R)) (e : M ≃* M),
        (∀ p : V.left, label (b.left p) = e) →
        restrictAut b f = scalarAut (diagonalGroundAut e) V := by
  let G := specGroup (groupAlgebra k M)
  let points := LinearAlgebraicGroups.DiagonalizableGroups.groupAlgebraPointsIso k M
  let i := Functor.isoWhiskerLeft (Under.forget R) points
  let fₐ : (Under.forget R ⋙ (groupPointsFunctor k).obj G) ≅
      (Under.forget R ⋙ (groupPointsFunctor k).obj G) :=
    Functor.isoWhiskerLeft (affineSlice R).rightOp f.asIso
  obtain ⟨label, hl⟩ := scalarCharacterIsomorphism_locallyConstant R (i.symm ≪≫ fₐ ≪≫ i)
  refine ⟨label, fun V b e he => ?_⟩
  apply Aut.ext
  apply Iso.ext
  apply relativeHom_ext_affine
  intro S a x
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let φ : R ⟶ S := (ff.preimage (a ≫ b)).unop
  have hφ : (testSpec k).map φ.op = a ≫ b := ff.map_preimage (a ≫ b)
  let U : Under R := Under.mk φ
  have hU (p : PrimeSpectrum S) : label (PrimeSpectrum.comap U.hom.hom.toRingHom p) = e := by
    change label (((testSpec k).map φ.op).left p) = e
    rw [hφ]
    exact he (a.left p)
  let v := ((i.app U).groupIsoToMulEquiv : _ ≃* (M →* Sˣ))
  have ht := hl U e hU (v x)
  have ht' : v (relativeEvaluate f.asIso.hom (Over.mk ((testSpec k).map φ.op)) x) =
      (v x).comp e.toMonoidHom := by
    change v ((fₐ.hom.app U).hom (v.symm (v x))) = _ at ht
    rw [v.symm_apply_apply] at ht
    exact ht
  have hw : v (x ≫ (diagonalGroundAut (k := k) e).asIso.hom.hom.hom) =
      (v x).comp e.toMonoidHom := by
    apply MonoidHom.ext
    intro m
    exact pointsIso_precompose e.toMonoidHom S x m
  apply v.injective
  change v (relativeEvaluate f.asIso.hom (Over.mk (a ≫ b)) x) =
    v (x ≫ (diagonalGroundAut (k := k) e).asIso.hom.hom.hom)
  rw [← hφ, ht', hw]

private theorem diagonalScalar_cover {M : Type u} [CommGroup M] [Group.FG M]
    (R : TestAlgebra k) (f : RelativeAut (specGroup (groupAlgebra k M))
      ((testSpec k).obj (op R))) :
    scalarAutomorphismSieve f ∈ schemeTopology k ((testSpec k).obj (op R)) := by
  obtain ⟨label, hl⟩ := diagonalScalar_on_fibers R f
  let S := (testSpec k).obj (op R)
  let opens (e : M ≃* M) : S.left.Opens :=
    ⟨{p | label p = e}, label.isLocallyConstant.isOpen_fiber e⟩
  let C := S.left.openCoverOfIsOpenCover opens (by
    apply top_unique
    intro p _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨label p, rfl⟩)
  refine (schemeTopology k).superset_covering ((Sieve.generate_le_iff _ _).2 ?_) (openCover_mem C)
  intro U a ha
  obtain ⟨e⟩ := ha
  exact ⟨diagonalGroundAut e, hl _ _ e fun p => p.property⟩

private theorem restrictAut_comp {G : GroupScheme k} {S U V : SchemeOver k}
    (b : U ⟶ S) (a : V ⟶ U) (f : RelativeAut G S) :
    restrictAut a (restrictAut b f) = restrictAut (a ≫ b) f :=
  (ConcreteCategory.congr_hom ((automorphisms G).map_comp b.op a.op) f).symm

private theorem pullback_scalarAutomorphismSieve {G : GroupScheme k} {S U : SchemeOver k}
    (b : U ⟶ S) (f : RelativeAut G S) :
    (scalarAutomorphismSieve f).pullback b = scalarAutomorphismSieve (restrictAut b f) := by
  ext V a
  change (∃ e : Aut G, restrictAut (a ≫ b) f = scalarAut e V) ↔
    (∃ e : Aut G, restrictAut a (restrictAut b f) = scalarAut e V)
  rw [restrictAut_comp]

private abbrev scalarGroupIso {G H : GroupScheme k} (e : G ≅ H) (S : SchemeOver k) :
    relativePoints G S ≅ relativePoints H S :=
  (yonedaGrp ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.forget S).op).mapIso e

private theorem restrictAut_transportScalar {G H : GroupScheme k} (e : G ≅ H)
    {S V : SchemeOver k} (b : V ⟶ S) (f : RelativeAut G S) :
    restrictAut b (Aut.autMulEquivOfIso (scalarGroupIso e S) f) =
      Aut.autMulEquivOfIso (scalarGroupIso e V) (restrictAut b f) := by
  apply Aut.ext
  apply Iso.ext
  rfl

private theorem transport_scalarAut {G H : GroupScheme k} (e : G ≅ H)
    (f : Aut G) (S : SchemeOver k) :
    Aut.autMulEquivOfIso (scalarGroupIso e S) (scalarAut f S) =
      scalarAut (Aut.autMulEquivOfIso e f) S := by
  apply Aut.ext
  apply Iso.ext
  let F := yonedaGrp ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.forget S).op
  change F.map e.inv ≫ F.map f.asIso.hom ≫ F.map e.hom =
    F.map (e.inv ≫ f.asIso.hom ≫ e.hom)
  simp only [Functor.map_comp]

private theorem scalarTorus_cover_affine {T : GroupScheme k} (hT : IsSplitTorus T)
    (R : TestAlgebra k) (f : RelativeAut T ((testSpec k).obj (op R))) :
    scalarAutomorphismSieve f ∈ schemeTopology k ((testSpec k).obj (op R)) := by
  obtain ⟨r, ⟨e⟩⟩ := splitPresentation hT
  let S := (testSpec k).obj (op R)
  let g := Aut.autMulEquivOfIso (scalarGroupIso e.symm S) f
  apply (schemeTopology k).superset_covering _ (diagonalScalar_cover R g)
  rintro V b ⟨d, hd⟩
  refine ⟨Aut.autMulEquivOfIso e d, ?_⟩
  apply (Aut.autMulEquivOfIso (scalarGroupIso e.symm V)).injective
  rw [← restrictAut_transportScalar, show Aut.autMulEquivOfIso (scalarGroupIso e.symm S) f = g
    from rfl, hd, transport_scalarAut]
  congr 1
  exact ((Aut.autMulEquivOfIso e).symm_apply_apply d).symm

private theorem covering_of_affine_tests {S : SchemeOver k} (Q : Sieve S)
    (h : ∀ (R : TestAlgebra k) (a : (testSpec k).obj (op R) ⟶ S),
      (schemeTopology k).Covers Q a) : Q ∈ schemeTopology k S := by
  let J := schemeTopology k
  let C := S.left.affineCover
  let V (i : C.I₀) : SchemeOver k := Over.mk (C.f i ≫ S.hom)
  let a (i : C.I₀) : V i ⟶ S := Over.homMk (C.f i)
  refine J.transitive (openCover_mem C) Q ?_
  rintro U b ⟨W, c, v, hW, rfl⟩
  cases hW with
  | mk i =>
    obtain ⟨R, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr
      (show IsAffine (V i).left from Scheme.isAffine_affineCover _ _)
    have hcov : J.Covers Q (e.hom ≫ a i) := h R.unop _
    have ha : J.Covers Q (a i) := by
      simpa only [Iso.inv_hom_id_assoc] using J.arrow_stable _ Q hcov e.inv
    exact J.arrow_stable _ Q ha c

/-- An automorphism of the split torus on any test scheme is locally the
scalar extension of a ground-field torus automorphism. -/
theorem scalarTorus_cover {T : GroupScheme k} (hT : IsSplitTorus T)
    {S : SchemeOver k} (f : RelativeAut T S) :
    scalarAutomorphismSieve f ∈ schemeTopology k S := by
  apply covering_of_affine_tests
  intro R a
  rw [GrothendieckTopology.covers_iff, pullback_scalarAutomorphismSieve]
  exact scalarTorus_cover_affine hT R _

end LocallyScalarTorus


section PairNormalizer

open Pinning (PinnedGroup AttachedDatum)
open RootGroups (AdditiveLine)
open SchemeDerivedGroup (FactorsThrough)
open private extendSubgroup subgroup_extend reductive_geometric normalizes_iff_sections
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer
open private factor_of_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private splitTorus_sectionsCommute from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.NormalizerLatticeAction

variable {k : Type u} [Field k]

/-- The simultaneous scheme normalizer of the pinned Borel pair is the torus.
In particular this factorization holds over nonreduced test schemes. -/
theorem pairNormalizer_factors {A : AdditiveLine k} (P : PinnedGroup A)
    {S : SchemeOver k} (g : S ⟶ P.pair.G.val.X)
    (hB : Normalizes P.pair.B.inclusion g) (hT : Normalizes P.pair.T.inclusion g) :
    FactorsThrough P.pair.T g := by
  let G := P.pair.G
  let B := P.pair.B
  let T := P.pair.T
  let K := AlgebraicClosure k
  let F := baseChange k K
  obtain ⟨b, hb⟩ := (RootData.BorelNormalizer.groundFieldBorelNormalizer G P.pair.reductive
    B P.pair.borel S g).mp hB
  obtain ⟨N, hN⟩ := LinearAlgebraicGroups.normalizerScheme k G T
  obtain ⟨_, hNK⟩ := LinearAlgebraicGroups.normalizerSchemeBaseChange k K T.inclusion N
    T.isClosedImmersion hN
  obtain ⟨n, hn⟩ := (hN S g).mp hT
  obtain ⟨_, hBK : GeometricBorelConjugacy.IsBorel (extendSubgroup K B)⟩ := P.pair.borel
  obtain ⟨_, hTK : GeometricRadicals.IsMaximalTorus (extendSubgroup K T)⟩ := P.pair.maximal
  have hI := RootData.BorelNormalizer.borelNormalizerIntersection (GeometricRadicals.GeometricGroup G)
    (reductive_geometric G P.pair.reductive) _ _ hTK hBK
    (subgroup_extend K P.pair.containsTorus) (extendSubgroup K N) hNK
  have factorB : F.map g ∈ SubgroupSections (extendSubgroup K B) (F.obj S) :=
    ⟨F.map b, (F.map_comp _ _).symm.trans (F.congr_map hb)⟩
  have factorN : F.map g ∈ SubgroupSections (extendSubgroup K N) (F.obj S) :=
    ⟨F.map n, (F.map_comp _ _).symm.trans (F.congr_map hn)⟩
  obtain ⟨t, ht⟩ := (hI (F.obj S) (F.map g)).mpr (by
    intro H hH
    rcases Set.mem_insert_iff.mp hH with rfl | hH
    · exact factorN
    · rw [Set.mem_singleton_iff.mp hH]
      exact factorB)
  let := T.isClosedImmersion
  exact factor_of_baseChange K g T.inclusion.hom.hom t ht

private abbrev relativeInclusion {G H : GroupScheme k} (i : H ⟶ G) (S : SchemeOver k) :
    relativePoints H S ⟶ relativePoints G S :=
  Functor.whiskerLeft (Over.forget S).op (yonedaGrp.map i)

private theorem relative_comm_inv {G H : GroupScheme k} {S : SchemeOver k}
    (i : H ⟶ G) (a : RelativeAut G S) (b : RelativeAut H S)
    (h : relativeInclusion i S ≫ a.asIso.hom = b.asIso.hom ≫ relativeInclusion i S) :
    relativeInclusion i S ≫ a.asIso.inv = b.asIso.inv ≫ relativeInclusion i S := by
  apply (cancel_mono a.asIso.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, h, Iso.inv_hom_id_assoc]

private theorem normalizes_of_inner_preserves {G : GroupScheme k} (B : ClosedSubgroup G)
    {S : SchemeOver k} (g : S ⟶ G.X) (b : RelativeAut B.group S)
    (h : relativeInclusion B.inclusion S ≫ (innerAut g).asIso.hom =
      b.asIso.hom ≫ relativeInclusion B.inclusion S) : Normalizes B.inclusion g := by
  apply (normalizes_iff_sections B g).mpr
  intro Y y b₀
  let U : Over S := Over.mk y
  have H := congrArg (fun f => relativeEvaluate f U b₀) h
  have H' := congrArg (fun f => relativeEvaluate f U b₀)
    (relative_comm_inv B.inclusion (innerAut g) b h)
  change (y ≫ g)⁻¹ * (b₀ ≫ B.inclusion.hom.hom) * ((y ≫ g)⁻¹)⁻¹ =
    relativeEvaluate b.asIso.inv U b₀ ≫ B.inclusion.hom.hom at H'
  exact ⟨⟨relativeEvaluate b.asIso.hom U b₀, H.symm⟩,
    ⟨relativeEvaluate b.asIso.inv U b₀, by simpa only [inv_inv] using H'.symm⟩⟩

private theorem inner_preserves_pair_acts_trivially_on_torus {A : AdditiveLine k} (P : PinnedGroup A)
    {S : SchemeOver k} {f : RelativeAut P.pair.G.val S} (g : S ⟶ P.pair.G.val.X)
    (a : Aligned P f) (hf : f = innerAut g) : a.torus = 1 := by
  have hb := (congrArg (fun z => relativeInclusion P.pair.B.inclusion S ≫ z.asIso.hom)
    hf).symm.trans a.borel_comm
  have hc := (congrArg (fun z => relativeInclusion P.pair.T.inclusion S ≫ z.asIso.hom)
    hf).symm.trans a.torus_comm
  obtain ⟨t, ht⟩ := pairNormalizer_factors P g
    (normalizes_of_inner_preserves P.pair.B g a.borel hb)
    (normalizes_of_inner_preserves P.pair.T g a.torus hc)
  apply Aut.ext
  apply Iso.ext
  apply NatTrans.ext
  funext U
  apply GrpCat.ext
  intro s
  change U.unop.left ⟶ P.pair.T.group.X at s
  have h := congrArg (fun f => relativeEvaluate f U.unop s) hc
  let T := P.pair.T
  let i := T.inclusion.hom.hom
  let := T.isClosedImmersion
  let : Mono i := Over.mono_of_mono_left i
  let := splitTorus_sectionsCommute P.pair.split U.unop.left
  change (relativeEvaluate a.torus.asIso.hom U.unop s) = s
  apply (cancel_mono i).mp
  change ((U.unop.hom ≫ g) * ((s : U.unop.left ⟶ T.group.X) ≫ i) *
    (U.unop.hom ≫ g)⁻¹) = (relativeEvaluate a.torus.asIso.hom U.unop s) ≫ i at h
  rw [← h, ← ht]
  change (U.unop.hom ≫ t ≫ i) * (s ≫ i) * (U.unop.hom ≫ t ≫ i)⁻¹ = s ≫ i
  let m := IsMonHom.monoidHom i U.unop.left
  change m (U.unop.hom ≫ t) * m s * (m (U.unop.hom ≫ t))⁻¹ = m s
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  rw [mul_comm' (U.unop.hom ≫ t), mul_assoc, mul_inv_cancel, mul_one]

private def Aligned.mul {A : AdditiveLine k} {P : PinnedGroup A} {S : SchemeOver k}
    {f g : RelativeAut P.pair.G.val S} (a : Aligned P f) (b : Aligned P g) :
    Aligned P (f * g) where
  torus := a.torus * b.torus
  borel := a.borel * b.borel
  torus_comm := by
    change relativeInclusion P.pair.T.inclusion S ≫ (g.asIso.hom ≫ f.asIso.hom) =
      (b.torus.asIso.hom ≫ a.torus.asIso.hom) ≫ relativeInclusion P.pair.T.inclusion S
    rw [← Category.assoc, b.torus_comm, Category.assoc, a.torus_comm, Category.assoc]
  borel_comm := by
    change relativeInclusion P.pair.B.inclusion S ≫ (g.asIso.hom ≫ f.asIso.hom) =
      (b.borel.asIso.hom ≫ a.borel.asIso.hom) ≫ relativeInclusion P.pair.B.inclusion S
    rw [← Category.assoc, b.borel_comm, Category.assoc, a.borel_comm, Category.assoc]

private def Aligned.inv {A : AdditiveLine k} {P : PinnedGroup A} {S : SchemeOver k}
    {f : RelativeAut P.pair.G.val S} (a : Aligned P f) : Aligned P f⁻¹ where
  torus := a.torus⁻¹
  borel := a.borel⁻¹
  torus_comm := relative_comm_inv P.pair.T.inclusion f a.torus a.torus_comm
  borel_comm := relative_comm_inv P.pair.B.inclusion f a.borel a.borel_comm

private def pinnedScalarAligned {A : AdditiveLine k} {P : PinnedGroup A} (f : Aut P)
    (S : SchemeOver k) : Aligned P (scalarAut (Functor.mapAut P (forgetPinning (A := A)) f) S) where
  torus := scalarAut (Aut.of f.asIso.hom.torus) S
  borel := scalarAut (Aut.of f.asIso.hom.borel) S
  torus_comm := by
    let F := yonedaGrp ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.forget S).op
    change F.map P.pair.T.inclusion ≫ F.map f.asIso.hom.group.hom =
      F.map f.asIso.hom.torus.hom ≫ F.map P.pair.T.inclusion
    rw [← F.map_comp, ← F.map_comp, f.asIso.hom.torus_comm]
  borel_comm := by
    let F := yonedaGrp ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.forget S).op
    change F.map P.pair.B.inclusion ≫ F.map f.asIso.hom.group.hom =
      F.map f.asIso.hom.borel.hom ≫ F.map P.pair.B.inclusion
    rw [← F.map_comp, ← F.map_comp, f.asIso.hom.borel_comm]

private theorem scalarAut_injective_of_nonempty {G : GroupScheme k} {S : SchemeOver k}
    [Nonempty S.left] : Function.Injective (fun f : Aut G => scalarAut f S) := by
  intro f g heq
  let X := (Over.pullback S.hom).obj G.X
  let W := (Over.map S.hom).obj X
  let w : W ⟶ S := Over.homMk X.hom
  let x : W ⟶ G.X := Over.homMk (pullback.fst G.X.hom S.hom) pullback.condition
  have he := congrArg (fun a : RelativeAut G S => relativeEvaluate a.asIso.hom (Over.mk w) x) heq
  change x ≫ f.asIso.hom.hom.hom = x ≫ g.asIso.hom.hom.hom at he
  have hs : Surjective S.hom := ⟨Function.surjective_to_subsingleton S.hom⟩
  have hp := IsPullback.of_hasPullback G.X.hom S.hom
  let : Flat x.left := MorphismProperty.of_isPullback hp.flip (inferInstance : Flat S.hom)
  let : Surjective x.left := MorphismProperty.of_isPullback hp.flip hs
  let : Epi x.left := Flat.epi_of_flat_of_surjective x.left
  apply Aut.ext
  apply Iso.ext
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  exact (cancel_epi x.left).mp (congrArg (fun a => a.left) he)

private theorem basedAut_eq_one_of_weight {D : Pinning.BasedRootDatum.{u}} (d : Aut D)
    (h : ∀ x, d.asIso.hom.val.weightEquiv x = x) : d = 1 := by
  apply Aut.ext
  apply Iso.ext
  apply Subtype.ext
  apply RootPairing.Equiv.weightHom_injective D.datum
  ext x
  exact h x

private theorem paired_inner_scalar_is_trivial {A : AdditiveLine k} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} (l : Aut D.toBased ≃* Aut P)
    (hl : ∀ (d : Aut D.toBased) (χ : CharacterDescent.Character P.pair.T.group),
      d.asIso.hom.val.weightEquiv (Additive.ofMul χ) =
        Additive.ofMul (Pinning.transportCharacter (l d).asIso.hom.torus χ))
    {S : SchemeOver k} [Nonempty S.left] (d : Aut D.toBased) (g : S ⟶ P.pair.G.val.X)
    (h : scalarAut (Functor.mapAut P (forgetPinning (A := A)) (l d)) S = innerAut g) : d = 1 := by
  let a := pinnedScalarAligned (l d) S
  have ht := inner_preserves_pair_acts_trivially_on_torus P g a h
  have he : scalarAut (Aut.of (l d).asIso.hom.torus) S = scalarAut (1 : Aut P.pair.T.group) S := by
    change scalarAut (Aut.of (l d).asIso.hom.torus) S = 1 at ht
    simpa only [map_one] using ht
  have h₁ := scalarAut_injective_of_nonempty he
  have h₂ : (l d).asIso.hom.torus = Iso.refl _ := by
    apply Iso.ext
    exact congrArg (fun a : Aut P.pair.T.group => a.asIso.hom) h₁
  apply basedAut_eq_one_of_weight
  intro x
  let χ : CharacterDescent.Character P.pair.T.group := Additive.toMul x
  change d.asIso.hom.val.weightEquiv (Additive.ofMul χ) = Additive.ofMul χ
  rw [hl, h₂, Pinning.transportCharacter, Iso.refl_inv, Category.id_comp]

/-- An inner automorphism which preserves the pair comes from the adjoint
image of the torus, even when the original adjoint section lifts only fppf-locally. -/
theorem adjointInner_aligned_factors {A : AdditiveLine k} {P : PinnedGroup A}
    {Q : AdjointQuotient P.pair.G}
    {O : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{u+1}} (E : ExactSequence P.pair.G Q O)
    (T : AdjointTorus P Q) {S : SchemeOver k} {f : RelativeAut P.pair.G.val S}
    (q : (groupSections Q.quotient.val).obj (op S)) (a : Aligned P f)
    (hf : f = E.inner.app (op S) q) :
    ∃ t : S ⟶ T.subgroup.group.X, t ≫ T.subgroup.inclusion.hom.hom = q.down := by
  let J := schemeTopology k
  let p := groupSectionsMap Q.projection
  let i := groupSectionsMap T.subgroup.inclusion
  let : Presheaf.IsLocallySurjective J p := groupSectionsMap_locallySurjective Q.projection Q.fppf
  have injective (U : (SchemeOver k)ᵒᵖ) : Function.Injective (i.app U) := by
    intro x y h
    let := T.subgroup.isClosedImmersion
    let : Mono T.subgroup.inclusion.hom.hom := Over.mono_of_mono_left _
    apply ULift.ext
    exact (cancel_mono T.subgroup.inclusion.hom.hom).mp (congrArg ULift.down h)
  have h := range_of_local_sections i (groupSections_isSheaf T.subgroup.group) injective q
    (groupSections_isSheaf Q.quotient.val) (Presheaf.imageSieve_mem J p q) (by
      rintro V b ⟨⟨g⟩, h⟩
      have eq : restrictAut b (E.inner.app (op S) q) = innerAut g := by
        change (automorphisms P.pair.G.val).map b.op (E.inner.app (op S) q) = _
        rw [← NatTrans.naturality_apply E.inner, ← h]
        exact E.onLift V g
      let a' := a.restrict b
      have eq' := (congrArg (restrictAut b) hf).trans eq
      have hb := (congrArg (fun z => relativeInclusion P.pair.B.inclusion V ≫ z.asIso.hom)
        eq').symm.trans a'.borel_comm
      have htor := (congrArg (fun z => relativeInclusion P.pair.T.inclusion V ≫ z.asIso.hom)
        eq').symm.trans a'.torus_comm
      obtain ⟨t, ht⟩ := pairNormalizer_factors P g
        (normalizes_of_inner_preserves P.pair.B g a'.borel hb)
        (normalizes_of_inner_preserves P.pair.T g a'.torus htor)
      refine ⟨⟨t ≫ T.projection.hom.hom⟩, ?_⟩
      rw [← h]
      apply ULift.ext
      have hh := congrArg (fun e => e.hom.hom) T.comm
      change T.projection.hom.hom ≫ T.subgroup.inclusion.hom.hom =
        P.pair.T.inclusion.hom.hom ≫ Q.projection.hom.hom at hh
      change t ≫ P.pair.T.inclusion.hom.hom = g at ht
      change (t ≫ T.projection.hom.hom) ≫ T.subgroup.inclusion.hom.hom = g ≫ Q.projection.hom.hom
      rw [Category.assoc, hh, ← Category.assoc, ht])
  obtain ⟨⟨t⟩, ht⟩ := h
  exact ⟨t, congrArg ULift.down ht⟩

private theorem adjointInner_aligned_torus {A : AdditiveLine k} {P : PinnedGroup A}
    {Q : AdjointQuotient P.pair.G}
    {O : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{u+1}} (E : ExactSequence P.pair.G Q O)
    {S : SchemeOver k} {f : RelativeAut P.pair.G.val S}
    (q : (groupSections Q.quotient.val).obj (op S)) (a : Aligned P f)
    (hf : f = E.inner.app (op S) q) : a.torus = 1 := by
  let J := schemeTopology k
  let p := groupSectionsMap Q.projection
  let : Presheaf.IsLocallySurjective J p := groupSectionsMap_locallySurjective Q.projection Q.fppf
  apply groupSheaf_separated (automorphisms_isSheaf P.pair.T.group) (Presheaf.imageSieve_mem J p q)
  rintro V b ⟨⟨g⟩, h⟩
  have eq : restrictAut b (E.inner.app (op S) q) = innerAut g := by
    change (automorphisms P.pair.G.val).map b.op (E.inner.app (op S) q) = _
    rw [← NatTrans.naturality_apply E.inner, ← h]
    exact E.onLift V g
  have he := inner_preserves_pair_acts_trivially_on_torus P g (a.restrict b)
    ((congrArg (restrictAut b) hf).trans eq)
  change restrictAut b a.torus = 1 at he
  change restrictAut b a.torus = _
  rw [he]
  exact (map_one (restrictAut b)).symm

private theorem pinnedSection_intersection_trivial {A : AdditiveLine k} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} (l : Aut D.toBased ≃* Aut P)
    (hl : ∀ (d : Aut D.toBased) (χ : CharacterDescent.Character P.pair.T.group),
      d.asIso.hom.val.weightEquiv (Additive.ofMul χ) =
        Additive.ofMul (Pinning.transportCharacter (l d).asIso.hom.torus χ))
    {Q : AdjointQuotient P.pair.G} {O : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{u+1}}
    (E : ExactSequence P.pair.G Q O)
    (s : constantGroup (Aut D.toBased) ⟶ automorphisms P.pair.G.val)
    (hs : ∀ (S : SchemeOver k) (d : Aut D.toBased),
      s.app (op S) ⟨LocallyConstant.const _ d⟩ =
        scalarAut (Functor.mapAut P (forgetPinning (A := A)) (l d)) S) :
    ∀ (S : (SchemeOver k)ᵒᵖ) (d : (constantGroup (Aut D.toBased)).obj S),
      s.app S d ∈ (E.inner.app S).hom.range → d = 1 := by
  intro S d h
  obtain ⟨q, hq⟩ := h
  let J := schemeTopology k
  let p := groupSectionsMap Q.projection
  let c := constants (k := k) (Aut D.toBased)
  let : Presheaf.IsLocallySurjective J p := groupSectionsMap_locallySurjective Q.projection Q.fppf
  let : Presheaf.IsLocallySurjective J c := constants_locallySurjective _
  apply groupSheaf_separated (constantGroup_isSheaf _) (J.intersection_covering
    (Presheaf.imageSieve_mem J p q) (Presheaf.imageSieve_mem J c d))
  rintro V b ⟨⟨⟨g⟩, hg⟩, ⟨⟨e⟩, he⟩⟩
  rcases isEmpty_or_nonempty V.left with hEmpty | hNonempty
  · apply ULift.ext
    apply LocallyConstant.ext
    intro x
    exact (hEmpty.false x).elim
  · have eq := congrArg (fun f : RelativeAut P.pair.G.val S.unop => restrictAut b f) hq
    change (automorphisms P.pair.G.val).map b.op (E.inner.app S q) =
      (automorphisms P.pair.G.val).map b.op (s.app S d) at eq
    rw [← NatTrans.naturality_apply E.inner, ← NatTrans.naturality_apply s, ← hg, ← he] at eq
    change E.inner.app (op V) ⟨g ≫ Q.projection.hom.hom⟩ =
      s.app (op V) ⟨LocallyConstant.const _ e⟩ at eq
    rw [E.onLift, hs] at eq
    have h₁ := paired_inner_scalar_is_trivial l hl e g eq.symm
    rw [← he]
    change (⟨LocallyConstant.const V.left e⟩ : (constantGroup (Aut D.toBased)).obj (op V)) = _
    rw [h₁, map_one]
    rfl


end PairNormalizer

section RootSubgroupsOverTests

open Pinning (PinnedGroup AttachedDatum)
open RootGroups (AdditiveLine)
open Specs.SchemeDerivedGroup (FactorsThrough)
open CharacterDescent (Cocharacter)
open Specs.AdjointRepresentation (GroupPoints)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition HasLimit polynomialAlgebra
  laurentAlgebra polynomialToLaurent polynomialEvaluate laurentConstants laurentParameter orbit
  cocharacterPoint)
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private polynomialConstants polynomialConstants_laurent polynomialConstants_zero
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

variable {k : Type u} [Field k] {S : SchemeOver k} {G : GroupScheme k}

private theorem fixes_torus_of_aligned {A : AdditiveLine k} {P : PinnedGroup A}
    {f : RelativeAut P.pair.G.val S} (a : Aligned P f) (h : a.torus = 1)
    (U : Over S) (t : U.left ⟶ P.pair.T.group.X) :
    relativeEvaluate f.asIso.hom U (t ≫ P.pair.T.inclusion.hom.hom) =
      t ≫ P.pair.T.inclusion.hom.hom := by
  have hcomm := a.torus_comm
  rw [h] at hcomm
  exact congrArg (fun m => relativeEvaluate m U t) hcomm

private theorem relative_centralizes {H : GroupScheme k} (i : H ⟶ G)
    (f : relativePoints G S ⟶ relativePoints G S)
    (fixes : ∀ (U : Over S) (t : U.left ⟶ H.X),
      relativeEvaluate f U (t ≫ i.hom.hom) = t ≫ i.hom.hom)
    {U : Over S} {x : U.left ⟶ G.X} (h : Centralizes i x) :
    Centralizes i (relativeEvaluate f U x) := by
  apply (centralizes_iff _ _).mpr
  intro Y b t
  let V : Over S := Over.mk (b ≫ U.hom)
  let a : V ⟶ U := Over.homMk b
  have hc := (centralizes_iff i x).mp h Y b t
  have hm := hc.map (f.app (op V)).hom
  change Commute (relativeEvaluate f V (a.left ≫ x))
    (relativeEvaluate f V (t ≫ i.hom.hom)) at hm
  rw [relativeEvaluate_naturality, fixes] at hm
  exact hm

private theorem map_orbit_inclusion {H : GroupScheme k} (i : H ⟶ G) (c : Cocharacter H)
    (R : TestAlgebra k) (x : GroupPoints H R) :
    orbit c x ≫ i.hom.hom = orbit (c ≫ i) (x ≫ i.hom.hom) := by
  let L := (testSpec k).obj (op (laurentAlgebra R))
  let a : L ⟶ (specGroup (DiagonalizableGroups.groupAlgebra k
    DiagonalizableGroups.IntegerCharacters)).X := CocharacterDynamics.unitPoint _ (laurentParameter R)
  let b : L ⟶ (testSpec k).obj (op R) := (testSpec k).map (laurentConstants R).op
  let t : L ⟶ H.X := a ≫ c.hom.hom
  change (t * (b ≫ x) * t⁻¹) ≫ i.hom.hom =
    (a ≫ (c ≫ i).hom.hom) * (b ≫ x ≫ i.hom.hom) * (a ≫ (c ≫ i).hom.hom)⁻¹
  simp only [MonObj.mul_comp, GrpObj.inv_comp, t, Category.assoc]
  rfl

private theorem relative_contracts (C : ClosedSubgroup G)
    (f : relativePoints G S ⟶ relativePoints G S) (c : Cocharacter C.group)
    (preserves : ∀ (U : Over S) (x : U.left ⟶ C.group.X),
      FactorsThrough C (relativeEvaluate f U (x ≫ C.inclusion.hom.hom)))
    (fixes : ∀ (U : Over S) (z : U.left ⟶
      (specGroup (DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters)).X),
        relativeEvaluate f U (z ≫ (c ≫ C.inclusion).hom.hom) = z ≫ (c ≫ C.inclusion).hom.hom)
    (R : TestAlgebra k) (b : (testSpec k).obj (op R) ⟶ S)
    (x : GroupPoints C.group R) (h : HasLimit c x 1) :
    ∃ y : GroupPoints C.group R,
      y ≫ C.inclusion.hom.hom =
        relativeEvaluate f (Over.mk b) (x ≫ C.inclusion.hom.hom) ∧ HasLimit c y 1 := by
  let i := C.inclusion.hom.hom
  let := C.isClosedImmersion
  let : Mono i := Over.mono_of_mono_left i
  let aP := (testSpec k).map (polynomialConstants R).op
  let aL := (testSpec k).map (laurentConstants R).op
  let r := (testSpec k).map (polynomialToLaurent R).op
  let s := (testSpec k).map (polynomialEvaluate R 0).op
  let U : Over S := Over.mk b
  let P : Over S := Over.mk (aP ≫ b)
  let L : Over S := Over.mk (aL ≫ b)
  have hr : r ≫ aP = aL := by
    rw [show r ≫ aP = (testSpec k).map (polynomialConstants R ≫ polynomialToLaurent R).op by
      rw [op_comp, Functor.map_comp], polynomialConstants_laurent]
  have hs : s ≫ aP = 𝟙 _ := by
    rw [show s ≫ aP = (testSpec k).map (polynomialConstants R ≫ polynomialEvaluate R 0).op by
      rw [op_comp, Functor.map_comp], polynomialConstants_zero, op_id]
    exact (testSpec k).map_id _
  let rp : L ⟶ P := Over.homMk r (by change r ≫ aP ≫ b = _; rw [← Category.assoc, hr]; rfl)
  let zr : U ⟶ P := Over.homMk s (by change s ≫ aP ≫ b = _; rw [← Category.assoc, hs, Category.id_comp]; rfl)
  let l : L ⟶ U := Over.homMk aL
  obtain ⟨p, hp₁, hp₂⟩ := h
  obtain ⟨y, hy⟩ := preserves U x
  obtain ⟨q, hq⟩ := preserves P p
  change y ≫ i = relativeEvaluate f U (x ≫ i) at hy
  change q ≫ i = relativeEvaluate f P (p ≫ i) at hq
  refine ⟨y, hy, q, ?_, ?_⟩
  · apply (cancel_mono i).mp
    change (r ≫ q) ≫ i = orbit c y ≫ i
    rw [Category.assoc, hq]
    refine (relativeEvaluate_naturality f rp (p ≫ i)).symm.trans ?_
    have hp : r ≫ p ≫ i = orbit (c ≫ C.inclusion) (x ≫ i) := by
      rw [← Category.assoc, show r ≫ p = orbit c x from hp₁]
      exact map_orbit_inclusion C.inclusion c R x
    change relativeEvaluate f L (r ≫ p ≫ i) = _
    rw [hp, map_orbit_inclusion]
    let m : (L.left ⟶ G.X) →* (L.left ⟶ G.X) := (f.app (op L)).hom
    let t : L.left ⟶ G.X :=
      cocharacterPoint (c ≫ C.inclusion) (laurentAlgebra R) (laurentParameter R)
    have ht : m t = t := fixes L (CocharacterDynamics.unitPoint _ (laurentParameter R))
    have hnat : m (l.left ≫ (x ≫ i)) = l.left ≫ (y ≫ i) := by
      change relativeEvaluate f L (l.left ≫ (x ≫ i)) = l.left ≫ (y ≫ i)
      rw [relativeEvaluate_naturality, hy]
    change m (t * (l.left ≫ (x ≫ i)) * t⁻¹) = t * (l.left ≫ (y ≫ i)) * t⁻¹
    rw [map_mul, map_mul, map_inv, ht, hnat]
  · apply (cancel_mono i).mp
    change (s ≫ q) ≫ i = _
    rw [Category.assoc, hq]
    refine (relativeEvaluate_naturality f zr (p ≫ i)).symm.trans ?_
    change relativeEvaluate f U (s ≫ p ≫ i) = _
    rw [← Category.assoc, show s ≫ p = 1 from hp₂, MonObj.one_comp]
    exact ((f.app (op U)).hom.map_one).trans (MonObj.one_comp _).symm


open AbstractPairing (Root)
open RankOneFlag (SameSubgroup)
open GeometricBorelConjugacy (subgroupOfSubgroup)
open private subgroup_trans from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer

/-- A relative automorphism fixing the torus pointwise preserves each root
subgroup. Its points are the contracting points in the centralizer of the
kernel subtorus, two conditions preserved on the scalar test algebras. -/
theorem fixesTorus_preservesRootSubgroups {A : AdditiveLine k} {P : PinnedGroup A}
    (D : AttachedDatum P.pair) {f : RelativeAut P.pair.G.val S} (a : Aligned P f)
    (h : a.torus = 1) (R : TestAlgebra k) (b : (testSpec k).obj (op R) ⟶ S)
    (α : Root P.pair.T) (x : GroupPoints (P.roots α).val.group R) :
    FactorsThrough (P.roots α).val
      (relativeEvaluate f.asIso.hom (Over.mk b) (x ≫ (P.roots α).val.inclusion.hom.hom)) := by
  let := D.comm
  obtain ⟨C, c, _, _, L, E, _, Q, F, M, A', p, n, hL, _, _, _, r, _⟩ := D.datum.attached α
  let V := subgroupOfSubgroup C.subgroup L.contracting
  let W := (P.roots α).val
  obtain ⟨_, _, U, _, _, _, _, huniq⟩ := (RootData.RootGroups.rootSubgroups
    P.pair.G P.pair.reductive P.pair.T P.pair.split P.pair.maximal).2 α.val α.property
  have hUV : SameSubgroup U V := huniq V hL
  have hUW : SameSubgroup U W := huniq W (P.roots α).property
  obtain ⟨i, hi⟩ := subgroup_trans hUW.2 hUV.1
  obtain ⟨j, hj⟩ := subgroup_trans hUV.2 hUW.1
  let q := c ≫ C.torusIso.hom ≫ C.torus.inclusion
  let iC := C.subgroup.inclusion
  let iV := L.contracting.inclusion
  let s := C.kernelTorus.inclusion ≫ P.pair.T.inclusion
  have hfix (Y : Over S) (t : Y.left ⟶ C.kernelTorus.group.X) :
      relativeEvaluate f.asIso.hom Y (t ≫ s.hom.hom) = t ≫ s.hom.hom := by
    exact fixes_torus_of_aligned a h Y (t ≫ C.kernelTorus.inclusion.hom.hom)
  have hC (Y : Over S) (t : Y.left ⟶ C.subgroup.group.X) :
      FactorsThrough C.subgroup (relativeEvaluate f.asIso.hom Y (t ≫ iC.hom.hom)) := by
    apply (C.centralizes Y.left _).mp
    apply relative_centralizes s f.asIso.hom hfix
    exact (C.centralizes Y.left _).mpr ⟨t, rfl⟩
  have hq : q ≫ iC = c ≫ P.pair.T.inclusion := by
    simp only [q, iC, Category.assoc, C.torus_inclusion]
  have hfixq (Y : Over S) (t : Y.left ⟶
    (specGroup (DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters)).X) :
      relativeEvaluate f.asIso.hom Y (t ≫ (q ≫ iC).hom.hom) = t ≫ (q ≫ iC).hom.hom := by
    rw [hq]
    exact fixes_torus_of_aligned a h Y (t ≫ c.hom.hom)
  let y : GroupPoints L.contracting.group R := x ≫ i.hom.hom
  let z : GroupPoints C.subgroup.group R := y ≫ iV.hom.hom
  have hz : HasLimit q z 1 := (L.contracting_points R z).mpr ⟨y, rfl⟩
  obtain ⟨z', hz', hzlim⟩ := relative_contracts C.subgroup f.asIso.hom q hC hfixq R b z hz
  obtain ⟨y', hy'⟩ := (L.contracting_points R z').mp hzlim
  refine ⟨y' ≫ j.hom.hom, ?_⟩
  have hi' : i.hom.hom ≫ iV.hom.hom ≫ iC.hom.hom = W.inclusion.hom.hom :=
    congrArg (fun m => m.hom.hom) hi
  have hj' : j.hom.hom ≫ W.inclusion.hom.hom = iV.hom.hom ≫ iC.hom.hom :=
    congrArg (fun m => m.hom.hom) hj
  change y' ≫ iV.hom.hom = z' at hy'
  change (y' ≫ j.hom.hom) ≫ W.inclusion.hom.hom =
    relativeEvaluate f.asIso.hom (Over.mk b) (x ≫ W.inclusion.hom.hom)
  rw [Category.assoc, hj', ← Category.assoc, hy', hz']
  simp only [z, y, Category.assoc]
  change relativeEvaluate f.asIso.hom (Over.mk b) (x ≫ i.hom.hom ≫ iV.hom.hom ≫ iC.hom.hom) = _
  rw [hi']


open RootGroups (rootPoint)
open Pinning (SimpleRoot)
open CharacterPairing (pairing characterValue)
open private rootPoint_natural rootPoint_comp rootPoint_eq rootPoint_injective_of_mono
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private laurentParameter_zpow from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLieWeights

/-- The Laurent variable detects the degree of a polynomial commuting with a
nontrivial multiplicative weight, even over an arbitrary coefficient ring. -/
theorem equivariantPolynomial_eq_linear {R : Type u} [CommRing R] (p : Polynomial R)
    {n : ℤ} (hn : n ≠ 0)
    (h : (p.map LaurentPolynomial.C).comp (Polynomial.C (LaurentPolynomial.T n) * Polynomial.X) =
      Polynomial.C (LaurentPolynomial.T n) * p.map LaurentPolynomial.C) :
    p = Polynomial.C (p.coeff 1) * Polynomial.X := by
  ext j
  rw [Polynomial.coeff_C_mul_X]
  by_cases hj : j = 1
  · simp [hj]
  simp only [ite_eq_right hj]
  have hj' : (j : ℤ) * n ≠ n := by
    intro he
    apply hj
    exact_mod_cast mul_right_cancel₀ hn (he.trans (one_mul n).symm)
  have hc := congrArg (fun q : Polynomial (LaurentPolynomial R) => q.coeff j) h
  rw [Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_map,
    LaurentPolynomial.T_pow, mul_comm (LaurentPolynomial.T n)] at hc
  have hc' := congrArg (fun q : LaurentPolynomial R => q.coeff ((j : ℤ) * n)) hc
  rw [← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T] at hc'
  simpa only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, eq_self, ite_true,
    ite_eq_right hj'.symm] using hc'

private theorem relative_preserves_pin_coordinates {A : AdditiveLine k} {P : PinnedGroup A}
    (D : AttachedDatum P.pair) {f : RelativeAut P.pair.G.val S} (a : Aligned P f)
    (h : a.torus = 1) (R : TestAlgebra k) (b : (testSpec k).obj (op R) ⟶ S)
    (α : SimpleRoot P.pair) (z : R) :
    let x := (P.pin α).val.hom ≫ (P.roots α.val).val.inclusion
    ∃ w : R, relativeEvaluate f.asIso.hom (Over.mk b) (rootPoint x R z) = rootPoint x R w := by
  let U := (P.roots α.val).val
  let e := (P.pin α).val
  let x := e.hom ≫ U.inclusion
  obtain ⟨y, hy⟩ := fixesTorus_preservesRootSubgroups D a h R b α.val (rootPoint e.hom R z)
  obtain ⟨w, hw⟩ := (RootData.RootGroups.additivePoints A R).surjective (y ≫ e.inv.hom.hom)
  refine ⟨w, ?_⟩
  change relativeEvaluate f.asIso.hom (Over.mk b) (rootPoint x R z) = rootPoint x R w
  rw [rootPoint_comp, ← hy, rootPoint_eq, hw]
  change y ≫ U.inclusion.hom.hom = (y ≫ e.inv.hom.hom) ≫ (e.hom.hom.hom ≫ U.inclusion.hom.hom)
  rw [Category.assoc, ← Category.assoc e.inv.hom.hom,
    show e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ from ((Grp.forget _).mapIso e).inv_hom_id,
    Category.id_comp]

private theorem relative_pin_polynomial {A : AdditiveLine k} {P : PinnedGroup A}
    (D : AttachedDatum P.pair) {R : TestAlgebra k}
    {f : RelativeAut P.pair.G.val ((testSpec k).obj (op R))} (a : Aligned P f)
    (h : a.torus = 1) (α : SimpleRoot P.pair) :
    let x := (P.pin α).val.hom ≫ (P.roots α.val).val.inclusion
    ∃ p : Polynomial R, ∀ (B : TestAlgebra k) (b : R ⟶ B) (z : B),
      relativeEvaluate f.asIso.hom (Over.mk ((testSpec k).map b.op)) (rootPoint x B z) =
        rootPoint x B (Polynomial.aevalTower b.hom z p) := by
  let x := (P.pin α).val.hom ≫ (P.roots α.val).val.inclusion
  let Q := polynomialAlgebra R
  let c := polynomialConstants R
  obtain ⟨p, hp⟩ := relative_preserves_pin_coordinates D a h Q ((testSpec k).map c.op) α Polynomial.X
  refine ⟨p, fun B b z => ?_⟩
  let d : Q ⟶ B := CommAlgCat.ofHom (Polynomial.aevalTower b.hom z)
  have hcd : c ≫ d = b := CommAlgCat.hom_ext (Polynomial.aevalTower_comp_toAlgHom b.hom z)
  let U := Over.mk ((testSpec k).map c.op)
  let V := Over.mk ((testSpec k).map b.op)
  let v : V ⟶ U := Over.homMk ((testSpec k).map d.op) (by
    change (testSpec k).map d.op ≫ (testSpec k).map c.op = _
    rw [← Functor.map_comp, ← op_comp, hcd]; rfl)
  have he : relativeEvaluate f.asIso.hom V (v.left ≫ rootPoint x Q Polynomial.X) =
      v.left ≫ rootPoint x Q p := by
    rw [relativeEvaluate_naturality]
    exact congrArg (fun u => v.left ≫ u) hp
  change relativeEvaluate f.asIso.hom V (mapPoints d (rootPoint x Q Polynomial.X)) =
    mapPoints d (rootPoint x Q p) at he
  rw [rootPoint_natural, rootPoint_natural, show d.hom Polynomial.X = z from
    Polynomial.aevalTower_X b.hom z] at he
  exact he


private theorem pin_coordinate_commutes_with_weight {A : AdditiveLine k} {P : PinnedGroup A}
    {R : TestAlgebra k} {f : RelativeAut P.pair.G.val ((testSpec k).obj (op R))} (a : Aligned P f)
    (h : a.torus = 1) (α : SimpleRoot P.pair) (p : Polynomial R)
    (hp : ∀ (B : TestAlgebra k) (b : R ⟶ B) (z : B),
      let x := (P.pin α).val.hom ≫ (P.roots α.val).val.inclusion
      relativeEvaluate f.asIso.hom (Over.mk ((testSpec k).map b.op)) (rootPoint x B z) =
        rootPoint x B (Polynomial.aevalTower b.hom z p))
    (B : TestAlgebra k) (b : R ⟶ B) (t : GroupPoints P.pair.T.group B) (z : B) :
    let c := characterValue α.val.val B t
    Polynomial.aevalTower b.hom (c * z) p = c * Polynomial.aevalTower b.hom z p := by
  let x := (P.pin α).val.hom ≫ (P.roots α.val).val.inclusion
  let c := characterValue α.val.val B t
  let U := Over.mk ((testSpec k).map b.op)
  let g : GroupPoints P.pair.G.val B := t ≫ P.pair.T.inclusion.hom.hom
  let e : GroupPoints P.pair.G.val B →* GroupPoints P.pair.G.val B := (f.asIso.hom.app (op U)).hom
  have hg : e g = g := fixes_torus_of_aligned a h U t
  have hmono := (P.roots α.val).val.isClosedImmersion
  let : Mono (P.roots α.val).val.inclusion.hom.hom := Over.mono_of_mono_left _
  let : Mono x.hom.hom := mono_comp _ _
  apply rootPoint_injective_of_mono x B
  have he (z : B) : e (rootPoint x B z) = rootPoint x B (Polynomial.aevalTower b.hom z p) := hp B b z
  have hSc (v : B) : g * rootPoint x B v * g⁻¹ =
      rootPoint x B (c * v) := (P.pin α).property B t v
  change rootPoint x B (Polynomial.aevalTower b.hom (c * z) p) =
    rootPoint x B (c * Polynomial.aevalTower b.hom z p)
  rw [← he, ← hSc z, map_mul, map_mul, map_inv, hg, he, hSc]

private theorem aevalTower_laurent_constants {R : TestAlgebra k} (p : Polynomial R)
    (z : Polynomial (LaurentPolynomial R)) :
    Polynomial.aevalTower ((laurentConstants R ≫ polynomialConstants (laurentAlgebra R)).hom) z p =
      (p.map LaurentPolynomial.C).comp z := by
  change Polynomial.eval₂ (Polynomial.C.comp LaurentPolynomial.C) z p =
    Polynomial.eval₂ Polynomial.C z (p.map LaurentPolynomial.C)
  rw [Polynomial.eval₂_map]

/-- A torus-fixing automorphism acts on a pinned simple root coordinate by a
unit of the scalar test algebra. This applies to nonreduced algebras as well. -/
theorem fixesTorus_simpleRootScales {A : AdditiveLine k} {P : PinnedGroup A}
    (D : AttachedDatum P.pair) {R : TestAlgebra k}
    {f : RelativeAut P.pair.G.val ((testSpec k).obj (op R))} (a : Aligned P f)
    (h : a.torus = 1) (α : SimpleRoot P.pair) :
    let x := (P.pin α).val.hom ≫ (P.roots α.val).val.inclusion
    ∃ u : Rˣ, ∀ (B : TestAlgebra k) (b : R ⟶ B) (z : B),
      relativeEvaluate f.asIso.hom (Over.mk ((testSpec k).map b.op)) (rootPoint x B z) =
        rootPoint x B (b.hom u.val * z) := by
  let x := (P.pin α).val.hom ≫ (P.roots α.val).val.inclusion
  obtain ⟨p, hp⟩ := relative_pin_polynomial D a h α
  let := D.comm
  obtain ⟨_, c, _, hc, _⟩ := D.datum.attached α.val
  let n := pairing P.pair.T.group α.val.val c
  let L := laurentAlgebra R
  let B := polynomialAlgebra L
  let l := polynomialConstants L
  let b : R ⟶ B := laurentConstants R ≫ l
  let s : Bˣ := Units.map l.hom.toMonoidHom (laurentParameter R)
  let t : GroupPoints P.pair.T.group B := cocharacterPoint c B s
  have hvalue : characterValue α.val.val B t = Polynomial.C (LaurentPolynomial.T n : LaurentPolynomial R) := by
    change characterValue α.val.val B (cocharacterPoint c B s) = _
    rw [(RootData.CharacterPairing.characterPairingComposition P.pair.T.group α.val.val c).2 B s]
    change (↑((Units.map l.hom.toMonoidHom (laurentParameter R)) ^ n) : B) = _
    rw [← map_zpow]
    change Polynomial.C (↑(laurentParameter R ^ n) : LaurentPolynomial R) = _
    rw [laurentParameter_zpow]
  have eq := pin_coordinate_commutes_with_weight a h α p hp B b t Polynomial.X
  dsimp only at eq
  change Polynomial.aevalTower b.hom (characterValue α.val.val B t * Polynomial.X) p =
    characterValue α.val.val B t * Polynomial.aevalTower b.hom Polynomial.X p at eq
  rw [hvalue, aevalTower_laurent_constants, aevalTower_laurent_constants, Polynomial.comp_X] at eq
  have heq := equivariantPolynomial_eq_linear p (ne_of_gt hc) eq
  have heval (B : TestAlgebra k) (b : R ⟶ B) (z : B) :
      relativeEvaluate f.asIso.hom (Over.mk ((testSpec k).map b.op)) (rootPoint x B z) =
        rootPoint x B (b.hom (p.coeff 1) * z) := by
    rw [hp B b z]
    conv_lhs => rw [heq]
    rw [map_mul, Polynomial.aevalTower_C, Polynomial.aevalTower_X]
  let U : Over ((testSpec k).obj (op R)) := Over.mk (𝟙 _)
  let aI := Aligned.inv a
  have hInv : aI.torus = 1 := by change a.torus⁻¹ = 1; rw [h, inv_one]
  obtain ⟨v, hv⟩ := relative_preserves_pin_coordinates D aI hInv R (𝟙 _) α 1
  have hcomp := (f.asIso.app (op U)).groupIsoToMulEquiv.apply_symm_apply (rootPoint x R 1)
  change relativeEvaluate f.asIso.hom U (relativeEvaluate f.asIso.inv U (rootPoint x R 1)) =
    rootPoint x R 1 at hcomp
  change relativeEvaluate f.asIso.inv U (rootPoint x R 1) = rootPoint x R v at hv
  rw [hv] at hcomp
  have hEval := heval R (𝟙 R) v
  rw [op_id] at hEval
  rw [(testSpec k).map_id] at hEval
  change relativeEvaluate f.asIso.hom U (rootPoint x R v) = rootPoint x R (p.coeff 1 * v) at hEval
  have hmono := (P.roots α.val).val.isClosedImmersion
  let : Mono (P.roots α.val).val.inclusion.hom.hom := Over.mono_of_mono_left _
  let : Mono x.hom.hom := mono_comp _ _
  have hmul : p.coeff 1 * v = 1 := rootPoint_injective_of_mono x R (hEval.symm.trans hcomp)
  exact ⟨⟨p.coeff 1, v, hmul, (mul_comm _ _).trans hmul⟩, heval⟩


open PinnedUniqueness (scalarGroupPoints)

private theorem relative_rigidity {A : AdditiveLine k} {P : PinnedGroup A}
    (f : relativePoints P.pair.G.val S ⟶ relativePoints P.pair.G.val S)
    (hT : ∀ (R : TestAlgebra k) (b : (testSpec k).obj (op R) ⟶ S)
      (t : GroupPoints P.pair.T.group R),
        relativeEvaluate f (Over.mk b) (t ≫ P.pair.T.inclusion.hom.hom) =
          t ≫ P.pair.T.inclusion.hom.hom)
    (hP : ∀ (R : TestAlgebra k) (b : (testSpec k).obj (op R) ⟶ S)
      (α : SimpleRoot P.pair) (z : R),
        let x := (P.pin α).val.hom ≫ (P.roots α.val).val.inclusion
        relativeEvaluate f (Over.mk b) (rootPoint x R z) = rootPoint x R z) : f = 𝟙 _ := by
  apply relativeHom_ext_affine
  intro R b x
  let F : scalarGroupPoints R P.pair.G.val ⟶ scalarGroupPoints R P.pair.G.val :=
    Functor.whiskerLeft ((affineSlice R).rightOp ⋙ (Over.map b).op) f
  have hor := Classification.PinnedUniqueness.scalarRigidity P R F
    (fun U t => hT U.right ((testSpec k).map U.hom.op ≫ b) t)
    (fun U α z => hP U.right ((testSpec k).map U.hom.op ≫ b) α z)
  have he := congrArg (fun h : scalarGroupPoints R P.pair.G.val ⟶ _ =>
    (h.app (Under.mk (𝟙 R))).hom x) hor
  change relativeEvaluate f (Over.mk ((testSpec k).map (𝟙 R).op ≫ b)) x = x at he
  rw [op_id] at he
  rw [(testSpec k).map_id, Category.id_comp] at he
  exact he

private theorem relativeAut_ext_torus_and_pins {A : AdditiveLine k} {P : PinnedGroup A}
    (f g : RelativeAut P.pair.G.val S)
    (hT : ∀ (R : TestAlgebra k) (b : (testSpec k).obj (op R) ⟶ S)
      (t : GroupPoints P.pair.T.group R),
        relativeEvaluate f.asIso.hom (Over.mk b) (t ≫ P.pair.T.inclusion.hom.hom) =
          relativeEvaluate g.asIso.hom (Over.mk b) (t ≫ P.pair.T.inclusion.hom.hom))
    (hP : ∀ (R : TestAlgebra k) (b : (testSpec k).obj (op R) ⟶ S)
      (α : SimpleRoot P.pair) (z : R),
        let x := (P.pin α).val.hom ≫ (P.roots α.val).val.inclusion
        relativeEvaluate f.asIso.hom (Over.mk b) (rootPoint x R z) =
          relativeEvaluate g.asIso.hom (Over.mk b) (rootPoint x R z)) : f = g := by
  have h (U : Over S) (x : U.left ⟶ P.pair.G.val.X)
      (eq : relativeEvaluate f.asIso.hom U x = relativeEvaluate g.asIso.hom U x) :
      relativeEvaluate (f.asIso.hom ≫ g.asIso.inv) U x = x := by
    change relativeEvaluate g.asIso.inv U (relativeEvaluate f.asIso.hom U x) = x
    rw [eq]
    exact ((g.asIso.app (op U)).groupIsoToMulEquiv).symm_apply_apply x
  have e := relative_rigidity (f.asIso.hom ≫ g.asIso.inv)
    (fun R b t => h (Over.mk b) _ (hT R b t))
    (fun R b α z => h (Over.mk b) _ (hP R b α z))
  apply Aut.ext
  apply Iso.ext
  apply (cancel_mono g.asIso.inv).mp
  exact e.trans g.asIso.hom_inv_id.symm


open DiagonalizableGroups (groupAlgebra IntegerCharacters integerGenerator)
open LinearAlgebraicGroups.CocharacterDynamics (mapPoints_unitPoint unitPoint unitCoordinates)
open private splitTorus_sectionsCommute from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.NormalizerLatticeAction

private theorem characterValue_of_unitPoint {T : GroupScheme k} (χ : CharacterDescent.Character T)
    (R : TestAlgebra k) (t : GroupPoints T R) (s : Rˣ)
    (h : t ≫ χ.hom.hom = unitPoint R s) : characterValue χ R t = s.val := by
  unfold characterValue
  rw [h]
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let v := CommAlgCat.ofHom (unitCoordinates (k := k) R s)
  have hv : ff.preimage ((testSpec k).map v.op) = v.op := ff.preimage_map v.op
  change (ff.preimage ((testSpec k).map v.op)).unop.hom
    (MonoidAlgebra.single integerGenerator 1 : MonoidAlgebra k IntegerCharacters) = _
  rw [hv]
  change unitCoordinates (k := k) R s (MonoidAlgebra.single integerGenerator 1) = _
  rw [← show MonoidAlgebra.of k IntegerCharacters integerGenerator =
    MonoidAlgebra.single integerGenerator 1 from rfl, unitCoordinates, MonoidAlgebra.lift_of]
  exact congrArg Units.val (zpow_one s)

/-- Over an affine scalar base, an aligned automorphism fixing the torus
comes from the adjoint torus. The unique point with the required simple
root characters is constructed from the unit scales. -/
theorem inner_of_fixed_torus {A : AdditiveLine k} {P : PinnedGroup A}
    (D : AttachedDatum P.pair) {Q : AdjointQuotient P.pair.G}
    {O : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{u+1}} (E : ExactSequence P.pair.G Q O)
    (T : AdjointTorus P Q) {R : TestAlgebra k}
    {f : RelativeAut P.pair.G.val ((testSpec k).obj (op R))}
    (a : Aligned P f) (hf : a.torus = 1) :
    ∃ t : (testSpec k).obj (op R) ⟶ T.subgroup.group.X,
      f = E.inner.app (op ((testSpec k).obj (op R))) ⟨t ≫ T.subgroup.inclusion.hom.hom⟩ := by
  classical
  let S := (testSpec k).obj (op R)
  let U := P.pair.T
  choose scales hscales using fun α => fixesTorus_simpleRootScales D a hf α
  obtain ⟨t, ht⟩ := (T.simpleBasis S).2 (fun α => unitPoint R (scales α))
  refine ⟨t, ?_⟩
  let J := schemeTopology k
  let p := groupSectionsMap T.projection
  let : Presheaf.IsLocallySurjective J p := groupSectionsMap_locallySurjective T.projection T.fppf
  apply groupSheaf_separated E.autSheaf (Presheaf.imageSieve_mem J p ⟨t⟩)
  rintro V b ⟨⟨v⟩, hv⟩
  let g : V ⟶ P.pair.G.val.X := v ≫ U.inclusion.hom.hom
  have hv' : v ≫ T.projection.hom.hom = b ≫ t := congrArg ULift.down hv
  have comm := congrArg (fun p => p.hom.hom) T.comm
  change T.projection.hom.hom ≫ T.subgroup.inclusion.hom.hom =
    U.inclusion.hom.hom ≫ Q.projection.hom.hom at comm
  have liftEq : b ≫ t ≫ T.subgroup.inclusion.hom.hom = g ≫ Q.projection.hom.hom := by
    rw [← Category.assoc, ← hv', Category.assoc, comm, ← Category.assoc]
  change restrictAut b f = (automorphisms P.pair.G.val).map b.op (E.inner.app (op S) ⟨_⟩)
  rw [← NatTrans.naturality_apply E.inner]
  change restrictAut b f = E.inner.app (op V) ⟨b ≫ t ≫ T.subgroup.inclusion.hom.hom⟩
  rw [liftEq, E.onLift]
  apply relativeAut_ext_torus_and_pins
  · intro B d z
    have htor := fixes_torus_of_aligned a hf (Over.mk (d ≫ b)) z
    change relativeEvaluate f.asIso.hom (Over.mk (d ≫ b)) (z ≫ U.inclusion.hom.hom) = _
    rw [htor]
    let m := IsMonHom.monoidHom U.inclusion.hom.hom ((testSpec k).obj (op B))
    let : IsMulCommutative (((testSpec k).obj (op B)) ⟶ U.group.X) :=
      splitTorus_sectionsCommute P.pair.split _
    change m z = m (d ≫ v) * m z * (m (d ≫ v))⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    rw [mul_comm' (d ≫ v), mul_assoc, mul_inv_cancel, mul_one]
  · intro B d α z
    let x := (P.pin α).val.hom ≫ (P.roots α.val).val.inclusion
    let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
    let φ : R ⟶ B := (ff.preimage (d ≫ b)).unop
    have hφ : (testSpec k).map φ.op = d ≫ b := ff.map_preimage (d ≫ b)
    have heval : characterValue α.val.val B (d ≫ v) = φ.hom (scales α).val := by
      have hc := congrArg (fun e => e.hom.hom) (T.pullsBack α)
      change T.projection.hom.hom ≫ (T.character α).hom.hom = α.val.val.hom.hom at hc
      have hu : (d ≫ v) ≫ α.val.val.hom.hom = unitPoint B (Units.map φ.hom.toMonoidHom (scales α)) := by
        have hα : t ≫ (T.character α).hom.hom = unitPoint R (scales α) := congrFun ht α
        calc
          (d ≫ v) ≫ α.val.val.hom.hom = (d ≫ b) ≫ (t ≫ (T.character α).hom.hom) := by
            rw [Category.assoc, ← hc, ← Category.assoc v, hv']
            simp only [Category.assoc]
          _ = unitPoint B (Units.map φ.hom.toMonoidHom (scales α)) := by
            rw [← hφ, hα]
            exact mapPoints_unitPoint φ (scales α)
      exact characterValue_of_unitPoint α.val.val B (d ≫ v) _ hu
    let gd : GroupPoints P.pair.G.val B := (d ≫ v) ≫ U.inclusion.hom.hom
    have hact : gd * rootPoint x B z * gd⁻¹ =
      rootPoint x B (characterValue α.val.val B (d ≫ v) * z) := (P.pin α).property B (d ≫ v) z
    let ge : GroupPoints P.pair.G.val B := d ≫ g
    have hge : ge = gd := (Category.assoc ..).symm
    change relativeEvaluate f.asIso.hom (Over.mk (d ≫ b)) (rootPoint x B z) = ge * rootPoint x B z * ge⁻¹
    rw [hge, hact, ← hφ, hscales α B φ z, heval]

end RootSubgroupsOverTests


section BasedAction

open Pinning (transportCharacter)
open CharacterDescent (Character)
open private splitPresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private hom_ext_of_points from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes

variable {k : Type u} [Field k]

private theorem torusIso_eq_of_characterAction {T : GroupScheme k} (hT : GeometricRadicals.IsSplitTorus T)
    (f g : T ≅ T) (h : ∀ χ : Character T, transportCharacter f χ = transportCharacter g χ) : f = g := by
  have hInv : f.symm = g.symm := by
    apply Iso.ext
    apply Grp.hom_ext
    apply hom_ext_of_points
    · obtain ⟨r, ⟨e⟩⟩ := splitPresentation hT
      let j := (Grp.forget _ ⋙ Over.forget _).mapIso e
      let := j.isIso_inv
      let : IsAffine ((Grp.forget (SchemeOver k) ⋙ Over.forget _).obj
          (specGroup (DiagonalizableGroups.groupAlgebra k (CharacterDescent.StandardLattice r)))) :=
        inferInstanceAs (IsAffine (Spec (CommRingCat.of (MonoidAlgebra k (CharacterDescent.StandardLattice r)))))
      exact IsAffine.of_isIso j.inv
    intro R t
    apply Classification.PinnedUniqueness.charactersSeparatePoints hT R
    intro χ
    change (t ≫ f.inv.hom.hom) ≫ χ.hom.hom = (t ≫ g.inv.hom.hom) ≫ χ.hom.hom
    rw [Category.assoc, Category.assoc]
    exact congrArg (fun a : Character T => t ≫ a.hom.hom) (h χ)
  exact congrArg Iso.symm hInv

end BasedAction


section AssembleSplitSequence

open Pinning (PinnedGroup AttachedDatum)
open RootGroups (AdditiveLine)

variable {k : Type u} [Field k] {A : AdditiveLine k} {P : PinnedGroup A}
variable {D : AttachedDatum P.pair} {Q : AdjointQuotient P.pair.G}
variable {O : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{u+1}}

private abbrev simultaneousLatticeActions (D : AttachedDatum P.pair)
    (l : Aut D.toBased ≃* Aut P) : Prop :=
  ∀ d : Aut D.toBased,
    let f := (l d).asIso.hom
    (∀ χ : CharacterDescent.Character P.pair.T.group,
      d.asIso.hom.val.weightEquiv (Additive.ofMul χ) =
        Additive.ofMul (Pinning.transportCharacter f.torus χ)) ∧
    (∀ c : CharacterDescent.Cocharacter P.pair.T.group,
      d.asIso.hom.val.coweightEquiv (Additive.ofMul c) = Additive.ofMul (c ≫ f.torus.inv))

/-- Which ground-field torus actions of aligned automorphisms come from
based automorphisms under the pinned lifting equivalence. It suffices to
recognize them over nonempty affine tests. -/
def RecognizesBasedAction (D : AttachedDatum P.pair) (l : Aut D.toBased ≃* Aut P) : Prop :=
  ∀ (R : TestAlgebra k), let S := (testSpec k).obj (op R)
    Nonempty S.left →
      ∀ (f : RelativeAut P.pair.G.val S) (a : Aligned P f) (t : Aut P.pair.T.group),
        a.torus = scalarAut t S →
          ∃ d : Aut D.toBased, a.torus = scalarAut (Aut.of (l d).asIso.hom.torus) S

private def decompositionSieve (E : ExactSequence P.pair.G Q O)
    (s : constantGroup (Aut D.toBased) ⟶ automorphisms P.pair.G.val)
    {S : SchemeOver k} (f : RelativeAut P.pair.G.val S) : Sieve S where
  arrows V b := ∃ (q : (groupSections Q.quotient.val).obj (op V))
      (d : (constantGroup (Aut D.toBased)).obj (op V)),
    restrictAut b f = E.inner.app (op V) q * s.app (op V) d
  downward_closed := by
    rintro V W b ⟨q, d, h⟩ a
    refine ⟨(groupSections Q.quotient.val).map a.op q, (constantGroup _).map a.op d, ?_⟩
    rw [← restrictAut_comp b a, h, map_mul]
    change (automorphisms P.pair.G.val).map a.op (E.inner.app (op V) q) *
      (automorphisms P.pair.G.val).map a.op (s.app (op V) d) = _
    rw [← NatTrans.naturality_apply E.inner, ← NatTrans.naturality_apply s]

private theorem factoring_sieve_of_aligned (l : Aut D.toBased ≃* Aut P)
    (E : ExactSequence P.pair.G Q O) (T : AdjointTorus P Q)
    (s : constantGroup (Aut D.toBased) ⟶ automorphisms P.pair.G.val)
    (hs : ∀ (S : SchemeOver k) (d : Aut D.toBased),
      s.app (op S) ⟨LocallyConstant.const _ d⟩ =
        scalarAut (Functor.mapAut P (forgetPinning (A := A)) (l d)) S)
    (recognition : RecognizesBasedAction D l)
    {S : SchemeOver k} (f : RelativeAut P.pair.G.val S) (a : Aligned P f) :
    decompositionSieve E s f ∈ schemeTopology k S := by
  let J := schemeTopology k
  let P₀ := decompositionSieve E s f
  refine J.transitive (scalarTorus_cover P.pair.split a.torus) P₀ ?_
  rintro V b ⟨t, ht⟩
  apply covering_of_affine_tests
  intro R c
  let U := (testSpec k).obj (op R)
  let b' := c ≫ b
  let f' := restrictAut b' f
  let a' := a.restrict b'
  have ha : a'.torus = scalarAut t U := by
    change restrictAut (c ≫ b) a.torus = _
    rw [← restrictAut_comp, ht]
    rfl
  rcases isEmpty_or_nonempty U.left with hEmpty | hNonempty
  · exact fppf_empty_cover U |> J.superset_covering bot_le
  obtain ⟨d, hd⟩ := recognition R hNonempty f' a' t ha
  let g := scalarAut (Functor.mapAut P (forgetPinning (A := A)) (l d)) U
  let h := Aligned.mul a' (Aligned.inv (pinnedScalarAligned (l d) U))
  have htor : h.torus = 1 := by
    change a'.torus * (scalarAut (Aut.of (l d).asIso.hom.torus) U)⁻¹ = 1
    rw [hd, mul_inv_cancel]
  obtain ⟨t₀, ht₀⟩ := inner_of_fixed_torus D E T h htor
  apply J.arrow_max
  refine ⟨⟨t₀ ≫ T.subgroup.inclusion.hom.hom⟩, ⟨LocallyConstant.const _ d⟩, ?_⟩
  change f' = E.inner.app (op U) _ * s.app (op U) ⟨LocallyConstant.const _ d⟩
  rw [hs, ← ht₀]
  exact (mul_inv_cancel_right _ _).symm

private theorem restrict_innerAut {G : GroupScheme k} {X Y : SchemeOver k} (a : Y ⟶ X)
    (g : X ⟶ G.X) : restrictAut a (innerAut g) = innerAut (a ≫ g) := by
  apply Aut.ext
  apply Iso.ext
  apply NatTrans.ext
  funext U
  apply GrpCat.ext
  intro x
  change U.unop.left ⟶ G.X at x
  change ((U.unop.hom ≫ a) ≫ g) * x * ((U.unop.hom ≫ a) ≫ g)⁻¹ =
    (U.unop.hom ≫ (a ≫ g)) * x * (U.unop.hom ≫ (a ≫ g))⁻¹
  simp only [Category.assoc]

private theorem factoring_sieve_of_alignment (l : Aut D.toBased ≃* Aut P)
    (E : ExactSequence P.pair.G Q O) (T : AdjointTorus P Q)
    (s : constantGroup (Aut D.toBased) ⟶ automorphisms P.pair.G.val)
    (hs : ∀ (S : SchemeOver k) (d : Aut D.toBased),
      s.app (op S) ⟨LocallyConstant.const _ d⟩ =
        scalarAut (Functor.mapAut P (forgetPinning (A := A)) (l d)) S)
    (recognition : RecognizesBasedAction D l)
    (alignment : ∀ (S : SchemeOver k) (f : RelativeAut P.pair.G.val S),
      alignmentSieve P f ∈ schemeTopology k S)
    (S : SchemeOver k) (f : RelativeAut P.pair.G.val S) :
    decompositionSieve E s f ∈ schemeTopology k S := by
  let J := schemeTopology k
  refine J.transitive (alignment S f) (decompositionSieve E s f) ?_
  intro V b hb
  change ∃ g : V ⟶ P.pair.G.val.X, Nonempty (Aligned P (innerAut g * restrictAut b f)) at hb
  obtain ⟨g, ⟨a⟩⟩ := hb
  let y := innerAut g * restrictAut b f
  have hy : decompositionSieve E s y ∈ J V := factoring_sieve_of_aligned l E T s hs recognition y a
  refine J.superset_covering ?_ hy
  intro W c hc
  change ∃ (q : (groupSections Q.quotient.val).obj (op W))
      (d : (constantGroup (Aut D.toBased)).obj (op W)),
    restrictAut c y = E.inner.app (op W) q * s.app (op W) d at hc
  obtain ⟨q, d, h⟩ := hc
  change ∃ (q : (groupSections Q.quotient.val).obj (op W))
      (d : (constantGroup (Aut D.toBased)).obj (op W)),
    restrictAut (c ≫ b) f = E.inner.app (op W) q * s.app (op W) d
  let q₀ : (groupSections Q.quotient.val).obj (op W) := ⟨(c ≫ g) ≫ Q.projection.hom.hom⟩
  refine ⟨q₀⁻¹ * q, d, ?_⟩
  have hres : restrictAut c (innerAut g) = innerAut (c ≫ g) := restrict_innerAut c g
  have hLift : E.inner.app (op W) q₀ = innerAut (c ≫ g) := E.onLift W (c ≫ g)
  change restrictAut c (innerAut g * restrictAut b f) = _ at h
  rw [map_mul, hres, ← hLift, restrictAut_comp b c] at h
  let i : (groupSections Q.quotient.val).obj (op W) →* RelativeAut P.pair.G.val W :=
    (E.inner.app (op W)).hom
  let e : RelativeAut P.pair.G.val W := s.app (op W) d
  have h' : i q₀ * restrictAut (c ≫ b) f = i q * e := h
  change restrictAut (c ≫ b) f = i (q₀⁻¹ * q) * e
  rw [i.map_mul, i.map_inv, mul_assoc, ← h', ← mul_assoc, inv_mul_cancel, one_mul]

private theorem latticeAction_of_pinned_restriction (l : Aut D.toBased ≃* Aut P)
    (lattices : simultaneousLatticeActions D l) {S : SchemeOver k}
    (f : RelativeAut P.pair.G.val S) (a : Aligned P f) (d : Aut D.toBased)
    (h : a.torus = scalarAut (Aut.of (l d).asIso.hom.torus) S) : HasLatticeAction D a d := by
  let e := (l d).asIso.hom.torus
  have hι : a.torus.asIso.inv = (scalarAut (Aut.of e) S).asIso.inv :=
    congrArg (fun a => a.asIso.inv) h
  constructor
  · intro χ U t
    dsimp only
    rw [hι]
    change (t ≫ e.inv.hom.hom) ≫ χ.hom.hom =
      t ≫ (Additive.toMul (d.asIso.hom.val.weightEquiv (Additive.ofMul χ))).hom.hom
    rw [(lattices d).1 χ]
    rfl
  · intro c U t
    dsimp only
    rw [hι]
    change (t ≫ c.hom.hom) ≫ e.inv.hom.hom =
      t ≫ (Additive.toMul (d.asIso.hom.val.coweightEquiv (Additive.ofMul c))).hom.hom
    rw [(lattices d).2 c]
    exact Category.assoc ..

/-- Assemble the split sequence from local alignment and recognition of the
based action. All remaining checks use the section, the scheme normalizer,
and the construction of the adjoint torus. -/
theorem splitSequence_of_geometry (l : Aut D.toBased ≃* Aut P)
    (lattices : simultaneousLatticeActions D l)
    (E : ExactSequence P.pair.G Q O) (T : AdjointTorus P Q)
    (recognition : RecognizesBasedAction D l)
    (alignment : ∀ (S : SchemeOver k) (f : RelativeAut P.pair.G.val S),
      alignmentSieve P f ∈ schemeTopology k S) : Nonempty (SplitSequence P D l Q) := by
  let p := (Functor.mapAut P (forgetPinning (A := A))).comp l.toMonoidHom
  obtain ⟨s, hs⟩ := extendConstantAutomorphisms P.pair.G.val p E.autSheaf
  have lifting_eq (S : SchemeOver k) (d : Aut D.toBased) :
      s.app (op S) ⟨LocallyConstant.const _ d⟩ =
        scalarAut (Functor.mapAut P (forgetPinning (A := A)) (l d)) S := hs S d
  obtain ⟨F, -, right_inv⟩ := split_of_local_decomposition E s (fun S f =>
    ⟨decompositionSieve E s f, factoring_sieve_of_alignment l E T s lifting_eq recognition alignment S f,
      fun _ _ h => h⟩) (pinnedSection_intersection_trivial l (fun d => (lattices d).1) E s lifting_eq)
  refine ⟨{
    toExactSequence := F
    outerRepresentation := constantGroup_represented _
    sectionMap := s
    rightInverse := right_inv
    sectionOnConstants := lifting_eq
    localAlignment := alignment
    adjointTorus := T
    latticeAction := ?_
    correctsSimpleCoordinates := ?_ }⟩
  · intro S f a d hd
    let g : RelativeAut P.pair.G.val S := scalarAut (Functor.mapAut P (forgetPinning (A := A)) (l d)) S
    let w : (constantGroup (k := k) (Aut D.toBased)).obj (op S) := ⟨LocallyConstant.const _ d⟩
    have hg : F.outer.app (op S) g = w := by
      change F.outer.app (op S) (scalarAut (Functor.mapAut P (forgetPinning (A := A)) (l d)) S) = w
      rw [← lifting_eq S d]
      exact ConcreteCategory.congr_hom (congrArg (fun m => m.app (op S)) right_inv) w
    have hkernel : F.outer.app (op S) (f * g⁻¹) = 1 := by
      rw [map_mul, map_inv, hd, hg, mul_inv_cancel]
    obtain ⟨q, hq⟩ := (F.exact (op S) _).mp hkernel
    let b := Aligned.mul a (Aligned.inv (pinnedScalarAligned (l d) S))
    have eq : f * g⁻¹ = F.inner.app (op S) q := hq.symm
    have hTor := adjointInner_aligned_torus F q b eq
    change a.torus * (scalarAut (Aut.of (l d).asIso.hom.torus) S)⁻¹ = 1 at hTor
    exact latticeAction_of_pinned_restriction l lattices f a d (mul_inv_eq_one.mp hTor)
  · intro S f ha hf
    obtain ⟨a⟩ := ha
    obtain ⟨q, hq⟩ := (F.exact (op S) f).mp hf
    obtain ⟨t, ht⟩ := adjointInner_aligned_factors F T q a hq.symm
    let i := T.subgroup.inclusion.hom.hom
    let qOf (t' : S ⟶ T.subgroup.group.X) :
        (groupSections Q.quotient.val).obj (op S) := ⟨t' ≫ i⟩
    have hq' : qOf t = q := ULift.ext ht
    have hCorrect : f = F.inner.app (op S) (qOf t) :=
      hq.symm.trans (congrArg (F.inner.app (op S)).hom hq').symm
    refine ⟨t, hCorrect, ?_⟩
    intro t' ht'
    have he : qOf t' = qOf t :=
      F.innerInjective (op S) (ht'.symm.trans hCorrect)
    let : IsClosedImmersion i.left := T.subgroup.isClosedImmersion
    let : Mono i := Over.mono_of_mono_left i
    exact (cancel_mono i).mp (congrArg ULift.down he)


/-- Recognition on the lattices identifies the torus map of the pinned field
lift, since the full character lattice separates split-torus morphisms. -/
private theorem recognizesBasedAction_of_lattices (l : Aut D.toBased ≃* Aut P)
    (lattices : simultaneousLatticeActions D l) : RecognizesBasedAction D l := by
  intro R S hS f a t ht
  obtain ⟨d, hd, _⟩ :=
    LinearAlgebraicGroups.Descent.RelativeBasedAction.relativeBasedAction
      P.pair D R hS f a.borel t.asIso (by simpa only [ht] using a.torus_comm) a.borel_comm
  have he := torusIso_eq_of_characterAction P.pair.split t.asIso (l d).asIso.hom.torus
    (fun χ => Additive.ofMul.injective ((hd χ).symm.trans ((lattices d).1 χ)))
  refine ⟨d, ht.trans ?_⟩
  exact congrArg (fun e : P.pair.T.group ≅ P.pair.T.group => scalarAut (Aut.of e) S) he

end AssembleSplitSequence

section RelativeGeometry

open Pinning (AttachedDatum PinnedGroup)
open RootGroups (AdditiveLine)

variable {k : Type u} [Field k]

private theorem innerAut_intertwines {H G : GroupScheme k} {S : SchemeOver k}
    (i : H ⟶ G) (s : S ⟶ H.X) :
    relativeInclusion i S ≫ (innerAut (s ≫ i.hom.hom)).asIso.hom =
      (innerAut s).asIso.hom ≫ relativeInclusion i S := by
  ext U x
  change U.unop.left ⟶ H.X at x
  let m := IsMonHom.monoidHom i.hom.hom U.unop.left
  change m (U.unop.hom ≫ s) * m x * (m (U.unop.hom ≫ s))⁻¹ =
    m ((U.unop.hom ≫ s) * x * (U.unop.hom ≫ s)⁻¹)
  rw [m.map_mul, m.map_mul, m.map_inv]

private theorem localPairAlignment {A : AdditiveLine k} (P : PinnedGroup A)
    (S : SchemeOver k) (f : RelativeAut P.pair.G.val S) :
    alignmentSieve P f ∈ schemeTopology k S := by
  obtain ⟨i, hi⟩ := P.pair.containsTorus
  obtain ⟨C, hC, hB⟩ :=
    LinearAlgebraicGroups.Descent.RelativeBorelAlignment.localBorelAlignment P.pair S f.asIso
  let J := schemeTopology k
  refine J.transitive hC (alignmentSieve P f) ?_
  intro V b hb
  obtain ⟨g, e, he⟩ := hB b hb
  let a := innerAut g * restrictAut b f
  have ha : relativeInclusion P.pair.B.inclusion V ≫ a.asIso.hom =
      e.hom ≫ relativeInclusion P.pair.B.inclusion V := he
  have hCover :=
    LinearAlgebraicGroups.Descent.RelativeTorusAlignment.relativeTorusAlignment
      P.pair i hi V e
  refine J.superset_covering ?_ hCover
  intro W c hc
  obtain ⟨s, t, ht⟩ := hc
  let a' := innerAut (s ≫ P.pair.B.inclusion.hom.hom) * restrictAut c a
  let e' := innerAut s * restrictAut c (Aut.of e)
  have hres : relativeInclusion P.pair.B.inclusion W ≫ (restrictAut c a).asIso.hom =
      (restrictIso c e).hom ≫ relativeInclusion P.pair.B.inclusion W := by
    ext U x
    exact ConcreteCategory.congr_hom
      (congrArg (fun n => n.app ((Over.map c).op.obj U)) ha) x
  have hb' : relativeInclusion P.pair.B.inclusion W ≫ a'.asIso.hom =
      e'.asIso.hom ≫ relativeInclusion P.pair.B.inclusion W := by
    change relativeInclusion P.pair.B.inclusion W ≫
        ((restrictAut c a).asIso.hom ≫
          (innerAut (s ≫ P.pair.B.inclusion.hom.hom)).asIso.hom) =
      ((restrictIso c e).hom ≫ (innerAut s).asIso.hom) ≫
        relativeInclusion P.pair.B.inclusion W
    rw [← Category.assoc, hres, Category.assoc, innerAut_intertwines, Category.assoc]
  have ht' : relativeInclusion i W ≫ e'.asIso.hom = t.hom ≫ relativeInclusion i W := by
    ext U x
    exact ht U.unop x
  let F := yonedaGrp ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.forget W).op
  have hi' : relativeInclusion i W ≫ relativeInclusion P.pair.B.inclusion W =
      relativeInclusion P.pair.T.inclusion W :=
    (F.map_comp i P.pair.B.inclusion).symm.trans (F.congr_map hi)
  have aligned : Aligned P a' :=
    { torus := Aut.of t
      borel := e'
      borel_comm := hb'
      torus_comm := by
        change relativeInclusion P.pair.T.inclusion W ≫ a'.asIso.hom =
          t.hom ≫ relativeInclusion P.pair.T.inclusion W
        rw [← hi', Category.assoc, hb', ← Category.assoc, ht', Category.assoc] }
  have hcomp : a' = innerAut ((s ≫ P.pair.B.inclusion.hom.hom) * (c ≫ g)) *
      restrictAut (c ≫ b) f := by
    dsimp only [a', a]
    rw [map_mul, restrict_innerAut, restrictAut_comp, innerAut_mul, mul_assoc]
  exact ⟨_, ⟨hcomp ▸ aligned⟩⟩

/-- The pinned fppf automorphism sequence and its comparisons for separable forms. -/
theorem automorphismSequence : Statement.{u} := by
  intro k _ A P
  obtain ⟨D, l, hl⟩ := pinnedLifts (k := k) P
  obtain ⟨Q, O, ⟨E⟩⟩ := exactSequence_exists P.pair.G
  obtain ⟨T⟩ := adjointTorus_exists P D Q
  obtain ⟨F⟩ := splitSequence_of_geometry l hl E T
    (recognizesBasedAction_of_lattices l hl) (localPairAlignment P)
  exact ⟨D, l, Q, F, hl, twists_of_exactSequence F.toExactSequence⟩

end RelativeGeometry


end

end LinearAlgebraicGroups.Descent.AutomorphismSequence
