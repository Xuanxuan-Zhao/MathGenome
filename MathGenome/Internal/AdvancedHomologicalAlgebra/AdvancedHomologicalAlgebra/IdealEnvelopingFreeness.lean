import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.IdealEnvelopingFreeness
import MathGenome.Internal.FourVolumeAlgebra.Shared.Lie.PBWOrdered
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Basis.MulOpposite

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace AdvancedHomologicalAlgebra.IdealEnveloping
open Shared.Lie Shared.Lie.PBW
universe u v w w'
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k : Type u} {g : Type v} [Field k] [LieRing g] [LieAlgebra k g]

@[simp] theorem inducedMap_inclusion (h : LieIdeal k g) (x : h) :
    inducedMap k g h (inclusion k h x) = inclusion k g (x : g) :=
  UniversalEnvelopingAlgebra.lift_ι_apply k _ x

@[simp] theorem adaptedBasis_inl (h : LieIdeal k g) (c : Submodule k g)
    (hc : IsCompl c h.toSubmodule) {ι : Type w} {κ : Type w'}
    (bc : Module.Basis ι k c) (bh : Module.Basis κ k h) (i : ι) :
    adaptedBasis k g h c hc bc bh (toLex (Sum.inl i)) = (bc i : g) := by
  change ((bc.prod bh).map (c.prodEquivOfIsCompl h.toSubmodule hc)) (Sum.inl i) = _
  rw [Module.Basis.map_apply, Module.Basis.prod_apply]
  change (bc i : g) + (0 : h) = (bc i : g)
  simp

@[simp] theorem adaptedBasis_inr (h : LieIdeal k g) (c : Submodule k g)
    (hc : IsCompl c h.toSubmodule) {ι : Type w} {κ : Type w'}
    (bc : Module.Basis ι k c) (bh : Module.Basis κ k h) (i : κ) :
    adaptedBasis k g h c hc bc bh (toLex (Sum.inr i)) = (bh i : g) := by
  change ((bc.prod bh).map (c.prodEquivOfIsCompl h.toSubmodule hc)) (Sum.inr i) = _
  rw [Module.Basis.map_apply, Module.Basis.prod_apply]
  change (0 : c) + (bh i : g) = (bh i : g)
  simp

/-- Map an ordered word along an order-preserving alphabet injection. -/
def mapOrderedWord {α β : Type*} [Preorder α] [Preorder β] (f : α → β) (hf : Monotone f)
    (l : OrderedWord α) : OrderedWord β :=
  ⟨l.val.map f, l.property.map f (fun _ _ h => hf h)⟩

theorem mapOrderedWord_injective {α β : Type*} [Preorder α] [Preorder β] (f : α → β)
    (hf : Monotone f) (hi : Function.Injective f) :
    Function.Injective (mapOrderedWord f hf) := by
  intro l m he
  apply Subtype.ext
  exact (List.map_injective_iff.mpr hi) (congrArg Subtype.val he)

/-- The map sends ideal PBW products to the corresponding ambient products. -/
theorem inducedMap_orderedMonomial (h : LieIdeal k g) (c : Submodule k g)
    (hc : IsCompl c h.toSubmodule) {ι : Type w} {κ : Type w'}
    [LinearOrder ι] [LinearOrder κ]
    (bc : Module.Basis ι k c) (bh : Module.Basis κ k h) (l : OrderedWord κ) :
    inducedMap k g h (orderedMonomial bh l) =
      orderedMonomial (adaptedBasis k g h c hc bc bh)
        (mapOrderedWord (toLex ∘ Sum.inr) Sum.Lex.inr_mono l) := by
  change inducedMap k g h (monomial bh l.val) =
    monomial (adaptedBasis k g h c hc bc bh) (l.val.map (toLex ∘ Sum.inr))
  induction l.val with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, monomial_cons, map_mul, inducedMap_inclusion, ih,
      Function.comp_apply, adaptedBasis_inr]

/-- A field supplies a complement, but injectivity is proved from PBW. -/
theorem inducedMap_injective (h : LieIdeal k g) :
    Function.Injective (inducedMap k g h) := by
  classical
  obtain ⟨c, hc⟩ := h.toSubmodule.exists_isCompl
  let ι := Module.Free.ChooseBasisIndex k c
  let κ := Module.Free.ChooseBasisIndex k h
  letI : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  letI : LinearOrder κ := linearOrderOfSTO WellOrderingRel
  let bc := Module.Free.chooseBasis k c
  let bh := Module.Free.chooseBasis k h
  have hind := (orderedBasis (adaptedBasis k g h c hc.symm bc bh)).linearIndependent.comp
    (mapOrderedWord (toLex ∘ Sum.inr) Sum.Lex.inr_mono)
    (mapOrderedWord_injective _ _ ((show Function.Injective (@toLex (ι ⊕ κ)) from fun _ _ h => h).comp Sum.inr_injective))
  apply LinearMap.injective_of_linearIndependent (f := (inducedMap k g h).toLinearMap)
    (orderedBasis bh).span_eq
  simpa only [Function.comp_def, orderedBasis_apply, AlgHom.toLinearMap_apply,
    inducedMap_orderedMonomial h c hc.symm bc bh] using hind

theorem inclusion_spec : Specs.AdvancedHomologicalAlgebra.IdealEnveloping.inclusionExpected.{u,v} :=
  fun _ _ _ _ _ h => inducedMap_injective h

/-- Concatenation of complementary and ideal words is already sorted. -/
def joinOrderedWords {α β : Type*} [LinearOrder α] [LinearOrder β]
    (l : OrderedWord α) (r : OrderedWord β) : OrderedWord (α ⊕ₗ β) :=
  ⟨l.val.map (toLex ∘ Sum.inl) ++ r.val.map (toLex ∘ Sum.inr), by
    apply List.pairwise_append.mpr
    refine ⟨(mapOrderedWord _ Sum.Lex.inl_mono l).property,
      (mapOrderedWord _ Sum.Lex.inr_mono r).property, ?_⟩
    intro a ha b hb
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hb
    exact Sum.Lex.inl_le_inr a b⟩

private theorem filterMap_left_join {α β : Type*} (l : List α) (r : List β) :
    ((l.map Sum.inl ++ r.map Sum.inr).filterMap Sum.getLeft?) = l := by
  induction l with
  | nil => induction r <;> simp_all
  | cons a l ih => simp [ih]

private theorem filterMap_right_join {α β : Type*} (l : List α) (r : List β) :
    ((l.map Sum.inl ++ r.map Sum.inr).filterMap Sum.getRight?) = r := by
  induction l with
  | nil => induction r <;> simp_all
  | cons a l ih => simpa only [List.map_cons, List.cons_append, List.filterMap_cons, Sum.getRight?] using ih

theorem joinOrderedWords_injective {α β : Type*} [LinearOrder α] [LinearOrder β] :
    Function.Injective (fun p : OrderedWord α × OrderedWord β => joinOrderedWords p.1 p.2) := by
  rintro ⟨l,r⟩ ⟨l',r'⟩ he
  have he' : l.val.map Sum.inl ++ r.val.map Sum.inr =
      l'.val.map Sum.inl ++ r'.val.map Sum.inr := congrArg Subtype.val he
  apply Prod.ext <;> apply Subtype.ext
  · simpa only [filterMap_left_join] using congrArg (List.filterMap Sum.getLeft?) he'
  · simpa only [filterMap_right_join] using congrArg (List.filterMap Sum.getRight?) he'

/-- Every sorted word has one complementary prefix and one ideal suffix. -/
theorem joinOrderedWords_surjective {α β : Type*} [LinearOrder α] [LinearOrder β] :
    Function.Surjective (fun p : OrderedWord α × OrderedWord β => joinOrderedWords p.1 p.2) := by
  intro w
  obtain ⟨l, hw⟩ := w
  induction l with
  | nil => exact ⟨(emptyWord α, emptyWord β), rfl⟩
  | cons a l ih =>
    obtain ⟨⟨p,q⟩, he⟩ := ih hw.of_cons
    have he' := congrArg Subtype.val he
    change p.val.map (toLex ∘ Sum.inl) ++ q.val.map (toLex ∘ Sum.inr) = l at he'
    induction a using Lex.rec with
    | h a => cases a with
      | inl a =>
        have hp : (a :: p.val).Pairwise (· ≤ ·) := by
          apply List.pairwise_cons.mpr
          refine ⟨?_, p.property⟩
          intro i hi
          have hm : toLex (Sum.inl i : α ⊕ β) ∈ l := by
            rw [← he']; exact List.mem_append_left _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
          exact Sum.Lex.inl_le_inl_iff.mp ((List.pairwise_cons.mp hw).1 _ hm)
        refine ⟨(⟨a :: p.val, hp⟩, q), ?_⟩
        apply Subtype.ext
        simpa only [joinOrderedWords, List.map_cons, List.cons_append, Function.comp_apply] using congrArg (List.cons (toLex (Sum.inl a))) he'
      | inr a =>
        have hp : p.val = [] := by
          cases hpv : p.val with
          | nil => rfl
          | cons i t =>
            exfalso
            have hm : toLex (Sum.inl i : α ⊕ β) ∈ l := by
              rw [← he', hpv]; simp
            exact Sum.Lex.not_inr_le_inl ((List.pairwise_cons.mp hw).1 _ hm)
        have hq : (a :: q.val).Pairwise (· ≤ ·) := by
          apply List.pairwise_cons.mpr
          refine ⟨?_, q.property⟩
          intro i hi
          have hm : toLex (Sum.inr i : α ⊕ β) ∈ l := by
            rw [← he']; exact List.mem_append_right _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
          exact Sum.Lex.inr_le_inr_iff.mp ((List.pairwise_cons.mp hw).1 _ hm)
        refine ⟨(emptyWord α, ⟨a :: q.val, hq⟩), ?_⟩
        apply Subtype.ext
        simpa only [joinOrderedWords, emptyWord, List.map_cons, List.map_nil, List.nil_append, hp, Function.comp_apply] using
          congrArg (List.cons (toLex (Sum.inr a))) he'

noncomputable def orderedWordsEquiv {α β : Type*} [LinearOrder α] [LinearOrder β] :
    OrderedWord α × OrderedWord β ≃ OrderedWord (α ⊕ₗ β) :=
  Equiv.ofBijective _ ⟨joinOrderedWords_injective, joinOrderedWords_surjective⟩

section RightBasis
variable {R S : Type*} [Ring R] [Ring S] [Algebra k R] [Algebra k S]

/-- The right action attached to any algebra homomorphism. -/
abbrev algebraRightModule (f : R →ₐ[k] S) : Module Rᵐᵒᵖ S :=
  Module.compHom S f.op.toRingHom

/-- Scalar compatibility for restriction of the right multiplication action. -/
theorem algebraRightModule_tower (f : R →ₐ[k] S) :
    letI := algebraRightModule f
    IsScalarTower k Rᵐᵒᵖ S := by
  letI := algebraRightModule f
  apply IsScalarTower.of_algebraMap_smul
  intro r s
  change s * f (algebraMap k R r) = r • s
  rw [f.commutes, ← Algebra.commutes]
  exact (Algebra.smul_def r s).symm

/-- A product k-basis with these values gives a right R-basis. -/
noncomputable def rightBasisOfProductBasis (f : R →ₐ[k] S)
    {I J : Type*} (b : Module.Basis J k R) (v : I → S)
    (B : Module.Basis (I × J) k S) (hB : ∀ i j, B (i,j) = v i * f (b j)) :
    letI := algebraRightModule f
    Module.Basis I Rᵐᵒᵖ S := by
  letI := algebraRightModule f
  letI := algebraRightModule_tower f
  let F := Finsupp.linearCombination Rᵐᵒᵖ v
  let C := Finsupp.basis (fun _ : I => b.mulOpposite)
  let D := B.reindex (Equiv.sigmaEquivProd I J).symm
  have hval : ∀ a, (F.restrictScalars k) (C a) = D a := by
    intro ⟨i,j⟩
    simp only [C, Finsupp.coe_basis, Module.Basis.mulOpposite_apply,
      LinearMap.restrictScalars_apply, F, Finsupp.linearCombination_single]
    change v i * f (b j) = D ⟨i,j⟩
    dsimp only [D]
    rw [Module.Basis.reindex_apply]
    exact (hB i j).symm
  have he : (F.restrictScalars k) ∘ C = D := funext hval
  have hbij : Function.Bijective F :=
    (F.restrictScalars k).bijective_of_linearIndependent_of_span_eq_top C.span_eq
      (he ▸ D.linearIndependent) (he ▸ D.span_eq)
  exact Module.Basis.ofRepr (LinearEquiv.ofBijective F hbij).symm

@[simp] theorem rightBasisOfProductBasis_apply (f : R →ₐ[k] S)
    {I J : Type*} (b : Module.Basis J k R) (v : I → S)
    (B : Module.Basis (I × J) k S) (hB : ∀ i j, B (i,j) = v i * f (b j)) (i : I) :
    letI := algebraRightModule f
    rightBasisOfProductBasis f b v B hB i = v i := by
  letI := algebraRightModule f
  change (Finsupp.linearCombination Rᵐᵒᵖ v) (Finsupp.single i 1) = v i
  simp
end RightBasis

/-- Multiplication of the two PBW factors is exactly concatenation, with no
commutation or lower-order correction terms. -/
theorem orderedMonomial_join (h : LieIdeal k g) (c : Submodule k g)
    (hc : IsCompl c h.toSubmodule) {ι : Type w} {κ : Type w'}
    [LinearOrder ι] [LinearOrder κ]
    (bc : Module.Basis ι k c) (bh : Module.Basis κ k h)
    (l : OrderedWord ι) (r : OrderedWord κ) :
    orderedMonomial (adaptedBasis k g h c hc bc bh) (joinOrderedWords l r) =
      complementaryMonomial k g bc l * inducedMap k g h (orderedMonomial bh r) := by
  rw [inducedMap_orderedMonomial h c hc bc bh]
  change monomial (adaptedBasis k g h c hc bc bh)
    (l.val.map (toLex ∘ Sum.inl) ++ r.val.map (toLex ∘ Sum.inr)) = _
  rw [monomial_append]
  congr 1
  change word k g _ = word k g _
  congr 1
  simp only [List.map_map, Function.comp_def, adaptedBasis_inl]

/-- The explicitly specified right PBW basis, for any adapted bases. -/
noncomputable def orderedRightBasis (h : LieIdeal k g) (c : Submodule k g)
    (hc : IsCompl c h.toSubmodule) {ι : Type w} {κ : Type w'}
    [LinearOrder ι] [LinearOrder κ]
    (bc : Module.Basis ι k c) (bh : Module.Basis κ k h) :
    letI := rightModule k g h
    Module.Basis (OrderedWord ι) (U k h)ᵐᵒᵖ (U k g) := by
  let B := (orderedBasis (adaptedBasis k g h c hc bc bh)).reindex orderedWordsEquiv.symm
  apply rightBasisOfProductBasis (inducedMap k g h) (orderedBasis bh)
    (complementaryMonomial k g bc) B
  intro l r
  dsimp only [B]
  rw [Module.Basis.reindex_apply]
  rw [Equiv.symm_symm, orderedBasis_apply, orderedBasis_apply]
  exact orderedMonomial_join h c hc bc bh l r

@[simp] theorem orderedRightBasis_apply (h : LieIdeal k g) (c : Submodule k g)
    (hc : IsCompl c h.toSubmodule) {ι : Type w} {κ : Type w'}
    [LinearOrder ι] [LinearOrder κ]
    (bc : Module.Basis ι k c) (bh : Module.Basis κ k h) (l : OrderedWord ι) :
    letI := rightModule k g h
    orderedRightBasis h c hc bc bh l = complementaryMonomial k g bc l := by
  unfold orderedRightBasis
  apply rightBasisOfProductBasis_apply

theorem orderedRightBasis_spec :
    Specs.AdvancedHomologicalAlgebra.IdealEnveloping.orderedRightBasisExpected.{u,v,w,w'} := by
  intro k g _ _ _ h c hc ι κ _ _ bc bh
  exact ⟨orderedRightBasis h c hc bc bh, orderedRightBasis_apply h c hc bc bh⟩

theorem rightFree_spec : Specs.AdvancedHomologicalAlgebra.IdealEnveloping.rightFreeExpected.{u,v} := by
  intro k g _ _ _ h
  classical
  obtain ⟨c, hc⟩ := h.toSubmodule.exists_isCompl
  let ι := Module.Free.ChooseBasisIndex k c
  let κ := Module.Free.ChooseBasisIndex k h
  letI : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  letI : LinearOrder κ := linearOrderOfSTO WellOrderingRel
  letI := rightModule k g h
  exact Module.Free.of_basis (orderedRightBasis h c hc.symm
    (Module.Free.chooseBasis k c) (Module.Free.chooseBasis k h))

section Restriction
universe a b z
variable {R : Type a} {S : Type b} [Ring R] [Ring S] [Algebra k R] [Algebra k S]

/-- Baer's criterion gives the restriction theorem directly from a right
basis. The argument uses only left ideals; neither algebra is commutative. -/
theorem restriction_injective_of_right_free (f : R →ₐ[k] S)
    (hfree : letI := algebraRightModule f; Module.Free Rᵐᵒᵖ S)
    (M : Type z) [AddCommGroup M] [Module S M] [Small.{z} S]
    [Module.Injective S M] :
    letI := Module.compHom M f.toRingHom
    Module.Injective R M := by
  classical
  letI := algebraRightModule f
  letI := algebraRightModule_tower f
  letI := hfree
  let b := Module.Free.chooseBasis Rᵐᵒᵖ S
  letI : Module k M := Module.compHom M (algebraMap k S)
  letI : IsScalarTower k S M := IsScalarTower.of_compHom k S M
  letI : Module R M := Module.compHom M f.toRingHom
  letI : IsScalarTower k R M := by
    apply IsScalarTower.of_algebraMap_smul
    intro r m
    change f (algebraMap k R r) • m = (algebraMap k S r) • m
    rw [f.commutes]
  apply Module.Baer.injective
  intro J g
  obtain ⟨G, hG⟩ := LinearMap.exists_extend (p := J.restrictScalars k)
    (g.restrictScalars k : J.restrictScalars k →ₗ[k] M)
  have hG' (r : R) (hr : r ∈ J) : G r = g ⟨r,hr⟩ :=
    LinearMap.congr_fun hG ⟨r,hr⟩
  let F : S →ₗ[k] M :=
    (Finsupp.lsum k (fun i => (DistribSMul.toLinearMap k M (b i)).comp
      (G.comp (MulOpposite.opLinearEquiv k).symm.toLinearMap))).comp
      (b.repr.toLinearMap.restrictScalars k)
  have hF (s : S) (r : R) (hr : r ∈ J) : F (s * f r) = s • g ⟨r,hr⟩ := by
    change (b.repr (s * f r)).sum (fun i a => b i • G (MulOpposite.unop a)) = _
    change (b.repr (MulOpposite.op r • s)).sum _ = _
    rw [map_smul, Finsupp.sum_smul_index']
    · calc
        _ = (b.repr s).sum (fun i a => (a • b i) • g ⟨r,hr⟩) := by
          apply Finsupp.sum_congr
          intro i hi
          let a := b.repr s i
          change b i • G (MulOpposite.unop a * r) =
            (b i * f (MulOpposite.unop a)) • g ⟨r,hr⟩
          rw [hG' _ (J.mul_mem_left _ hr)]
          have he : (⟨MulOpposite.unop a * r, J.mul_mem_left _ hr⟩ : J) =
              MulOpposite.unop a • (⟨r,hr⟩ : J) := rfl
          rw [he, map_smul]
          exact (mul_smul (b i) (f (MulOpposite.unop a)) (g ⟨r,hr⟩)).symm
        _ = ((b.repr s).sum (fun i a => a • b i)) • g ⟨r,hr⟩ := by
          simp only [Finsupp.sum, Finset.sum_smul]
        _ = s • g ⟨r,hr⟩ := by
          rw [← Finsupp.linearCombination_apply, b.linearCombination_repr]
    · intro i
      simp
  let L : Submodule S S := Submodule.span S (Set.range (fun r : J => f r))
  have hlin (x : S) (hx : x ∈ L) : ∀ a : S, F (a * x) = a • F x := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, rfl⟩ := hx
      intro a
      change F (a * f r) = a • F (f r)
      rw [hF a r r.property]
      congr 1
      symm
      simpa only [one_mul, one_smul] using hF 1 r r.property
    | zero => intro a; simp
    | add x y hx hy ihx ihy =>
      intro a
      simp only [mul_add, map_add, smul_add, ihx, ihy]
    | smul c x hx ih =>
      intro a
      change F (a * (c * x)) = a • F (c * x)
      rw [← mul_assoc, ih, ih, mul_smul]
  let H : L →ₗ[S] M :=
    { toFun := fun x => F x
      map_add' := fun x y => F.map_add x y
      map_smul' := fun a x => hlin x x.property a }
  obtain ⟨H', hH'⟩ := Module.Injective.extension_property S M L S L.subtype
    Subtype.val_injective H
  refine ⟨{ toFun := fun r => H' (f r)
            map_add' := fun r s => by rw [map_add, map_add]
            map_smul' := fun r s => by
              change H' (f (r * s)) = f r • H' (f s)
              rw [map_mul]
              exact H'.map_smul (f r) (f s) }, ?_⟩
  intro r hr
  have hm : f r ∈ L := Submodule.subset_span ⟨⟨r,hr⟩,rfl⟩
  have he := LinearMap.congr_fun hH' ⟨f r,hm⟩
  change H' (f r) = F (f r) at he
  change H' (f r) = g ⟨r,hr⟩
  rw [he]
  simpa only [one_mul, one_smul] using hF 1 r hr

end Restriction

theorem restriction_spec :
    Specs.AdvancedHomologicalAlgebra.IdealEnveloping.restrictionExpected.{u,v,w} := by
  intro k g _ _ _ h M _ _ _
  apply restriction_injective_of_right_free (inducedMap k g h)
    (rightFree_spec k g h) M

end AdvancedHomologicalAlgebra.IdealEnveloping
