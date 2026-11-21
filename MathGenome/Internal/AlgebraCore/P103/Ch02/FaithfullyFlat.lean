import MathGenome.Internal.AlgebraCore.Specs.P103.Ch02.FaithfullyFlat
import MathGenome.Internal.AlgebraCore.P103.Ch02.FlatnessTests
import Mathlib.RingTheory.Finiteness.Basic
import Batteries.Tactic.OpenPrivate

noncomputable section
set_option linter.style.haveILetI false
universe u v w
namespace P103.Ch02.FaithfullyFlat
open P103.BalancedTensor P103.Specs.Ch02.FlatnessTests
open P103.Specs.Ch02.FaithfullyFlat
open private oppositeFlip oppositeFlip_tmul from MathGenome.Internal.AlgebraCore.P103.Ch02.FlatnessTests

section Right
variable {R : Type u} [Ring R] {P : Type v} [AddCommGroup P] [Module Rᵐᵒᵖ P]

/-- Detection also tests the ring-sized quotients, by lifting the universe. -/
theorem detects_small (h : Detects.{u,v,w} R P) (A : Type u)
    [AddCommGroup A] [Module R A] [Nontrivial A] : Nontrivial (Tensor R P A) := by
  let e : ULift.{max v w} A ≃ₗ[R] A := ULift.moduleEquiv
  have hN := h (ULift.{max v w} A) inferInstance
  letI := hN
  exact Function.Injective.nontrivial
    (P103.Ch02.FlatnessTests.tensor_retract_injective (A := P)
      e.toLinearMap e.symm.toLinearMap e.symm_comp)

theorem detects_maximalTest (h : Detects.{u,v,w} R P) : MaximalTest R P := by
  intro I hI
  letI : Nontrivial (R ⧸ I) := Submodule.Quotient.nontrivial_iff.mpr hI.ne_top
  exact detects_small h (R ⧸ I)

/-- A nonzero element gives a cyclic module, whose annihilator lies in a
maximal left ideal. Flatness and right exactness then give the detection. -/
theorem maximalTest_detects (hf : RightFlat.{u,v,w} R P) (h : MaximalTest R P) :
    Detects.{u,v,w} R P := by
  intro A _ _ hA
  letI := hA
  obtain ⟨x, hx⟩ := exists_ne (0 : A)
  let f : R →ₗ[R] A :=
    { toFun := fun r => r • x
      map_add' := fun r s => add_smul r s x
      map_smul' := fun r s => mul_smul r s x }
  have hk : LinearMap.ker f ≠ ⊤ := by
    intro hk
    have h1 : (1 : R) ∈ LinearMap.ker f := hk ▸ Submodule.mem_top
    exact hx (by simpa [f] using h1)
  obtain ⟨I, hI, hle⟩ := (eq_top_or_exists_le_coatom (LinearMap.ker f)).resolve_left hk
  have hsur := LinearMap.surjective_rangeRestrict f
  have hker : LinearMap.ker f.rangeRestrict ≤ LinearMap.ker I.mkQ := by
    simpa only [LinearMap.ker_rangeRestrict, Submodule.ker_mkQ] using hle
  let q : LinearMap.range f →ₗ[R] R ⧸ I :=
    f.rangeRestrict.liftOfSurjective hsur ⟨I.mkQ, hker⟩
  have hq (r : R) : q (f.rangeRestrict r) = I.mkQ r :=
    LinearMap.equivOfSurjective_apply hsur hker
  have hqs : Function.Surjective q := by
    intro z
    obtain ⟨r, rfl⟩ := I.mkQ_surjective z
    exact ⟨f.rangeRestrict r, hq r⟩
  have hts := P103.HomTensorExactness.tensorSecond_surjective (A := P) q hqs
    (map LinearMap.id q) (by intros; rfl)
  letI := h I hI
  have hN : Nontrivial (Tensor R P (LinearMap.range f)) := Function.Surjective.nontrivial hts
  letI := hN
  exact Function.Injective.nontrivial
    (hf _ _ (LinearMap.range f).subtype Subtype.val_injective
      (map LinearMap.id (LinearMap.range f).subtype) (by intros; rfl))

/-- Factor through the image to reflect a zero map. -/
theorem map_eq_zero (hf : RightFlat.{u,v,w} R P) (hd : Detects.{u,v,w} R P)
    {A B : Type (max u v w)} [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B] (f : A →ₗ[R] B)
    (hz : map (LinearMap.id : P →ₗ[Rᵐᵒᵖ] P) f = 0) : f = 0 := by
  let i := (LinearMap.range f).subtype
  have hi := hf _ _ i Subtype.val_injective (map LinearMap.id i) (by intros; rfl)
  have hs := P103.HomTensorExactness.tensorSecond_surjective (A := P) f.rangeRestrict
    (LinearMap.surjective_rangeRestrict f) (map LinearMap.id f.rangeRestrict) (by intros; rfl)
  have hzero (z : Tensor R P (LinearMap.range f)) : z = 0 := by
    obtain ⟨y, rfl⟩ := hs z
    apply hi
    have hc : (map (LinearMap.id : P →ₗ[Rᵐᵒᵖ] P) i).comp
        (map LinearMap.id f.rangeRestrict) = map LinearMap.id f := hom_ext (by intros; rfl)
    rw [map_zero]
    exact (DFunLike.congr_fun hc y).trans (DFunLike.congr_fun hz y)
  have hsub : Subsingleton (LinearMap.range f) := by
    by_contra hn
    letI : Nontrivial (LinearMap.range f) := not_subsingleton_iff_nontrivial.mp hn
    letI := hd (LinearMap.range f) inferInstance
    obtain ⟨z, hz⟩ := exists_ne (0 : Tensor R P (LinearMap.range f))
    exact hz (hzero z)
  ext a
  exact congrArg Subtype.val (hsub.elim (f.rangeRestrict a) 0)

theorem detects_faithful (hf : RightFlat.{u,v,w} R P) (hd : Detects.{u,v,w} R P) :
    Faithful.{u,v,w} R P := by
  intro A B _ _ _ _ f g F G hF hG hFG
  have heF : F = map LinearMap.id f := hom_ext hF
  have heG : G = map LinearMap.id g := hom_ext hG
  have hh : map (LinearMap.id : P →ₗ[Rᵐᵒᵖ] P) (f - g) = 0 := by
    have ha := map_add_right (LinearMap.id : P →ₗ[Rᵐᵒᵖ] P) (f - g) g
    rw [sub_add_cancel] at ha
    rw [← heF, ← heG, hFG] at ha
    exact add_eq_right.mp ha.symm
  exact sub_eq_zero.mp (map_eq_zero hf hd (f - g) hh)

/-- Reflect exactness without presupposing that g ∘ f vanishes. First
reflect the vanishing composite; then test the quotient by the image of f. -/
theorem detects_reflectsExact (hf : RightFlat.{u,v,w} R P) (hd : Detects.{u,v,w} R P) :
    ReflectsExact.{u,v,w} R P := by
  intro A B C _ _ _ _ _ _ f g F G hF hG he
  have hgf : g.comp f = 0 := by
    apply map_eq_zero hf hd
    apply hom_ext
    intro p a
    simpa only [map_tmul, LinearMap.id_apply, LinearMap.comp_apply, hF, hG,
      AddMonoidHom.zero_apply] using he.apply_apply_eq_zero (tmul R p a)
  let j := (LinearMap.ker g).subtype
  let q := (LinearMap.range f).mkQ
  have hGj : G.comp (map (LinearMap.id : P →ₗ[Rᵐᵒᵖ] P) j) = 0 := by
    apply hom_ext
    intro p b
    change G (tmul R p (j b)) = 0
    rw [hG]
    simp [j]
  have hqF : (map (LinearMap.id : P →ₗ[Rᵐᵒᵖ] P) q).comp F = 0 := by
    apply hom_ext
    intro p a
    change map LinearMap.id q (F (tmul R p a)) = 0
    rw [hF, map_tmul]
    have hq : q (f a) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr ⟨a, rfl⟩
    simp [hq]
  have hqj : q.comp j = 0 := by
    apply map_eq_zero hf hd
    apply AddMonoidHom.ext
    intro z
    have hz : G (map (LinearMap.id : P →ₗ[Rᵐᵒᵖ] P) j z) = 0 :=
      DFunLike.congr_fun hGj z
    obtain ⟨y, hy⟩ := (he _).mp hz
    have hc : map (LinearMap.id : P →ₗ[Rᵐᵒᵖ] P) (q.comp j) =
        (map LinearMap.id q).comp (map LinearMap.id j) := hom_ext (by intros; rfl)
    rw [hc]
    change map LinearMap.id q (map LinearMap.id j z) = 0
    rw [← hy]
    exact DFunLike.congr_fun hqF y
  intro b
  constructor
  · intro hb
    have hqb : q b = 0 := DFunLike.congr_fun hqj ⟨b, hb⟩
    exact (Submodule.Quotient.mk_eq_zero _).mp hqb
  · rintro ⟨a, rfl⟩
    exact DFunLike.congr_fun hgf a

theorem reflectsExact_detects (hr : ReflectsExact.{u,v,w} R P) : Detects.{u,v,w} R P := by
  intro A _ _ hA
  by_contra hn
  letI : Subsingleton (Tensor R P A) := not_nontrivial_iff_subsingleton.mp hn
  have he : Function.Exact (0 : Tensor R P A →+ Tensor R P A) (0 : Tensor R P A →+ Tensor R P A) := by
    intro z
    exact ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => rfl⟩
  have heA := hr A A A 0 0 0 0 (by intros; simp) (by intros; simp) he
  letI := hA
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  obtain ⟨b, hb⟩ := (heA a).mp rfl
  exact ha hb.symm

/-- Flatness preserves exactness at the middle even without endpoint conditions. -/
theorem right_preserves_exact (hf : RightFlat.{u,v,w} R P)
    {A B C : Type (max u v w)} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module R A] [Module R B] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (he : Function.Exact f g)
    (F : Tensor R P A →+ Tensor R P B) (G : Tensor R P B →+ Tensor R P C)
    (hF : ∀ p a, F (tmul R p a) = tmul R p (f a))
    (hG : ∀ p b, G (tmul R p b) = tmul R p (g b)) : Function.Exact F G := by
  let g' := g.rangeRestrict
  let j := (LinearMap.range g).subtype
  have he' : Function.Exact f g' := by
    apply LinearMap.exact_iff.mpr
    simpa only [g', LinearMap.ker_rangeRestrict] using LinearMap.exact_iff.mp he
  have hex := (P103.HomTensorExactness.tensorSecond_rightExact (A := P) f g' he'
    (LinearMap.surjective_rangeRestrict g) F (map LinearMap.id g') hF (by intros; rfl)).1
  have hj := hf _ _ j Subtype.val_injective (map LinearMap.id j) (by intros; rfl)
  have hc : (map (LinearMap.id : P →ₗ[Rᵐᵒᵖ] P) j).comp (map LinearMap.id g') = G := by
    apply hom_ext
    intro p b
    exact (hG p b).symm
  intro z
  constructor
  · intro hz
    apply (hex z).mp
    apply hj
    exact (DFunLike.congr_fun hc z).trans hz |>.trans (map_zero _).symm
  · intro hz
    have hpz := (hex z).mpr hz
    rw [← DFunLike.congr_fun hc z]
    change map LinearMap.id j (map LinearMap.id g' z) = 0
    rw [hpz, map_zero]

end Right

theorem right_characterizations : P103.Specs.Ch02.FaithfullyFlat.right_characterizationsType.{u,v,w} := by
  intro R _ P _ _ hf
  refine ⟨⟨detects_reflectsExact hf, reflectsExact_detects⟩,
    ⟨detects_maximalTest, maximalTest_detects hf⟩, ?_⟩
  intro hd
  refine ⟨detects_faithful hf hd, ?_⟩
  intro A B C _ _ _ _ _ _ f g F G hF hG
  exact ⟨fun he => right_preserves_exact hf f g he F G hF hG,
    detects_reflectsExact hf hd A B C f g F G hF hG⟩

theorem left_orientation : left_orientationType.{u,v,w} := by
  intro R _ M _ _ A _ _
  letI := doubleOppositeModule R M
  exact ⟨oppositeFlip, fun _ _ => rfl⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem opposite_characterizations : opposite_characterizationsType.{u,v,w} := by
  intro R _ M _ _
  letI := doubleOppositeModule R M
  intro hf
  have hfop : Flat.{u,v,w} Rᵐᵒᵖᵐᵒᵖ M := by
    apply (P103.Ch02.FlatnessTests.flat_iff_finiteRelations Rᵐᵒᵖᵐᵒᵖ M).mpr
    intro n k x r hr
    have hrel := (P103.Ch02.FlatnessTests.flat_iff_finiteRelations R M).mp hf
    obtain ⟨l, y, s, hs, hrs⟩ := hrel n k x
      (fun j i => (r j i).unop.unop) hr
    refine ⟨l, y, (fun i a => MulOpposite.op (MulOpposite.op (s i a))), hs, ?_⟩
    intro j a
    apply (RingEquiv.opOp R).symm.injective
    simpa using hrs j a
  exact right_characterizations Rᵐᵒᵖ M
    ((P103.Ch02.FlatnessTests.rightFlat_iff_opposite Rᵐᵒᵖ M).mpr hfop)

section Left
variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ B] [Module Rᵐᵒᵖ C]
local instance : Module Rᵐᵒᵖᵐᵒᵖ M := doubleOppositeModule R M

/-- Conjugate an additive tensor arrow by the balanced opposite-ring flip. -/
private def flipMap (F : Tensor R A M →+ Tensor R B M) :
    Tensor Rᵐᵒᵖ M A →+ Tensor Rᵐᵒᵖ M B :=
  oppositeFlip.toAddMonoidHom.comp (F.comp oppositeFlip.symm.toAddMonoidHom)

private theorem flipMap_tmul (f : A →ₗ[Rᵐᵒᵖ] B) (F : Tensor R A M →+ Tensor R B M)
    (hF : ∀ a m, F (tmul R a m) = tmul R (f a) m) (m : M) (a : A) :
    flipMap F (tmul Rᵐᵒᵖ m a) = tmul Rᵐᵒᵖ m (f a) := by
  change oppositeFlip (F (tmul R a m)) = _
  rw [hF]
  rfl

private theorem flipMap_exact_iff (F : Tensor R A M →+ Tensor R B M)
    (G : Tensor R B M →+ Tensor R C M) :
    Function.Exact F G ↔ Function.Exact (flipMap F) (flipMap G) := by
  apply AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective F G
    (flipMap F) (flipMap G) oppositeFlip.toAddMonoidHom
    oppositeFlip.toAddMonoidHom oppositeFlip.toAddMonoidHom
  · apply hom_ext
    intro a m
    rfl
  · apply hom_ext
    intro a m
    rfl
  · exact oppositeFlip.surjective
  · exact oppositeFlip.bijective
  · exact oppositeFlip.injective

private theorem leftDetects_iff_opposite :
    LeftDetects.{u,v,w} R M ↔ Detects.{u,v,w} Rᵐᵒᵖ M := by
  constructor
  · intro h A _ _ hA
    letI := h A hA
    exact oppositeFlip.injective.nontrivial
  · intro h A _ _ hA
    letI := h A hA
    exact oppositeFlip.symm.injective.nontrivial

private theorem leftMaximalTest_iff_opposite :
    LeftMaximalTest R M ↔ MaximalTest Rᵐᵒᵖ M := by
  constructor
  · intro h I hI
    letI := h I hI
    exact oppositeFlip.injective.nontrivial
  · intro h I hI
    letI := h I hI
    exact oppositeFlip.symm.injective.nontrivial

end Left

/-- The complete left-module criterion, with maximal right ideals and the
right module placed first in every tensor over R. -/
theorem left_characterizations : left_characterizationsType.{u,v,w} := by
  intro R _ M _ _ hf
  letI := doubleOppositeModule R M
  obtain ⟨hDR, hDT, hFE⟩ := opposite_characterizations R M hf
  have hDL := leftDetects_iff_opposite.{u,v,w} (R := R) (M := M)
  have hTL := leftMaximalTest_iff_opposite (R := R) (M := M)
  have hLR (hd : LeftDetects.{u,v,w} R M) : LeftReflectsExact.{u,v,w} R M := by
    intro A B C _ _ _ _ _ _ f g F G hF hG he
    apply hDR.mp (hDL.mp hd) A B C f g (flipMap F) (flipMap G)
      (flipMap_tmul f F hF) (flipMap_tmul g G hG)
    exact (flipMap_exact_iff F G).mp he
  refine ⟨⟨hLR, ?_⟩, hDL.trans (hDT.trans hTL.symm), ?_⟩
  · intro hr A _ _ hA
    by_contra hn
    letI : Subsingleton (Tensor R A M) := not_nontrivial_iff_subsingleton.mp hn
    have he : Function.Exact (0 : Tensor R A M →+ Tensor R A M)
        (0 : Tensor R A M →+ Tensor R A M) := by
      intro z
      exact ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => rfl⟩
    have heA := hr A A A 0 0 0 0 (by intros; simp) (by intros; simp) he
    letI := hA
    obtain ⟨a, ha⟩ := exists_ne (0 : A)
    obtain ⟨b, hb⟩ := (heA a).mp rfl
    exact ha hb.symm
  · intro hd
    obtain ⟨hF, hE⟩ := hFE (hDL.mp hd)
    constructor
    · intro A B _ _ _ _ f g F G hF' hG' hFG
      exact hF A B f g (flipMap F) (flipMap G)
        (flipMap_tmul f F hF') (flipMap_tmul g G hG') (congrArg flipMap hFG)
    · intro A B C _ _ _ _ _ _ f g F G hF' hG'
      exact (hE A B C f g (flipMap F) (flipMap G)
        (flipMap_tmul f F hF') (flipMap_tmul g G hG')).trans (flipMap_exact_iff F G).symm

end P103.Ch02.FaithfullyFlat
