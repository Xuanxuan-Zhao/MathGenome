import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ArtinSurjectionsAndGluing
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.SchlessingerTangentVectorSpace
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SchlessingerConditionsFromHull

/-! The converse of Schlessinger's hull criterion. -/

universe u w

namespace CommutativeAlgebraNotes

open CategoryTheory LocalArtinAlgebra

variable {k : Type u} [Field k]

namespace LocalArtinAlgebra

private theorem smallExtension_pullbackFst
    {A B C : LocalArtinAlgebra.{u,u} k} (f : Hom A C) (g : Hom B C)
    (hg : SmallExtension g) : SmallExtension (pullbackFst f g) := by
  let p := pullbackFst f g
  let q := pullbackSnd f g
  have hker (x : RingHom.ker p.val.toRingHom) : q.val x.val ∈ RingHom.ker g.val.toRingHom := by
    have hx : p.val x.val = 0 := x.property
    change g (q.val x.val) = 0
    rw [← show f (p.val x.val) = g (q.val x.val) from x.val.property, hx]
    exact f.val.map_zero
  let K := (RingHom.ker p.val.toRingHom).restrictScalars k
  let L := (RingHom.ker g.val.toRingHom).restrictScalars k
  let l : K →ₗ[k] L := (q.val.toLinearMap.comp K.subtype).codRestrict L hker
  have hl : Function.Bijective l := by
    constructor
    · intro x y hxy
      have hx : p.val x.val = 0 := x.property
      have hy : p.val y.val = 0 := y.property
      exact Subtype.ext (Subtype.ext (Prod.ext (hx.trans hy.symm)
        (congrArg Subtype.val hxy)))
    · intro b
      have hb : g b.val = 0 := b.property
      refine ⟨⟨⟨(0, b.val), f.val.map_zero.trans hb.symm⟩, rfl⟩, rfl⟩
  refine ⟨?_, (LinearEquiv.ofBijective l hl).finrank_eq.trans hg.2.1, ?_⟩
  · intro a
    obtain ⟨b, hb⟩ := hg.1 (f a)
    exact ⟨⟨(a, b), hb.symm⟩, rfl⟩
  · intro a ha b hb
    have hqa : q.val a ∈ IsLocalRing.maximalIdeal B := by
      rw [← ker_residue B, RingHom.mem_ker]
      rw [show B.residue (q.val a) = (pullback f g).residue a from Hom.residue_apply q a]
      rwa [← ker_residue (pullback f g)] at ha
    have hb' : p.val b = 0 := hb
    exact Subtype.ext (Prod.ext
      (show p.val a * p.val b = 0 by rw [hb', mul_zero])
      (hg.2.2 (q.val a) hqa (q.val b) (hker ⟨b, hb⟩)))

private theorem smallExtension_dual_residue (k : Type u) [Field k] :
    SmallExtension (residueHom (dualNumbers k)) := by
  let D := dualNumbers k
  let g := residueHom D
  let l : k ≃ₗ[k] RingHom.ker g.val.toRingHom :=
    { toFun := fun b => ⟨TrivSqZeroExt.inr b, rfl⟩
      invFun := fun b => (show DualNumber k from b.val).snd
      left_inv := fun _ => rfl
      right_inv := fun b => Subtype.ext (TrivSqZeroExt.ext
        (show 0 = (show DualNumber k from b.val).fst from b.property.symm) rfl)
      map_add' := fun a b => Subtype.ext (TrivSqZeroExt.inr_add k a b)
      map_smul' := fun a b => Subtype.ext (TrivSqZeroExt.inr_smul k a b) }
  refine ⟨residue_surjective D, l.finrank_eq.symm.trans (CommSemiring.finrank_self k), ?_⟩
  intro a ha b hb
  have ha' : (show DualNumber k from a).fst = 0 := by
    rw [← ker_residue D] at ha
    exact ha
  have hb' : (show DualNumber k from b).fst = 0 := hb
  apply TrivSqZeroExt.ext
  · change (show DualNumber k from a).fst * (show DualNumber k from b).fst = 0
    rw [ha', zero_mul]
  · change (show DualNumber k from a).fst * (show DualNumber k from b).snd +
      (show DualNumber k from a).snd * (show DualNumber k from b).fst = 0
    rw [ha', hb', zero_mul, mul_zero, add_zero]

end LocalArtinAlgebra

namespace ArtinFunctor

variable {F : ArtinFunctor.{u,w} k} {R : CompleteLocalAlgebra k}
variable {A B C : LocalArtinAlgebra.{u,u} k}

private theorem naturality_apply (τ : R.representable.toFunctor ⟶ F.toFunctor)
    (g : Hom B A) (b : R.representable.toFunctor.obj B) :
    τ.app A (R.representable.toFunctor.map g b) = F.toFunctor.map g (τ.app B b) :=
  ConcreteCategory.congr_hom (τ.naturality g) b

private theorem Smooth.lift {τ : R.representable.toFunctor ⟶ F.toFunctor}
    (hτ : Smooth τ) (g : Hom B A) (hg : SmallExtension g)
    (a : R.representable.toFunctor.obj A) (y : F.toFunctor.obj B)
    (hy : τ.app A a = F.toFunctor.map g y) :
    ∃ b : R.representable.toFunctor.obj B,
      R.representable.toFunctor.map g b = a ∧ τ.app B b = y := by
  obtain ⟨b, hb⟩ := hτ g hg ⟨(a, y), hy⟩
  exact ⟨b, congrArg (fun p => p.val.1) hb, congrArg (fun p => p.val.2) hb⟩

private theorem surjective_of_small {τ : R.representable.toFunctor ⟶ F.toFunctor}
    (hτ : Smooth τ) (g : Hom B A) (hg : SmallExtension g)
    (hA : Function.Surjective (τ.app A)) : Function.Surjective (τ.app B) := by
  intro y
  obtain ⟨a, ha⟩ := hA (F.toFunctor.map g y)
  obtain ⟨b, _, hb⟩ := Smooth.lift hτ g hg a y ha
  exact ⟨b, hb⟩

private theorem surjective_of_chain {τ : R.representable.toFunctor ⟶ F.toFunctor}
    (hτ : Smooth τ) {g : Hom B A} {n : ℕ} (hg : SmallExtensionChain g n) :
    Function.Surjective (τ.app A) → Function.Surjective (τ.app B) := by
  induction hg with
  | @zero B A g hg =>
    intro hA y
    let e := AlgEquiv.ofBijective g.val hg
    let s : Hom A B := ⟨e.symm.toAlgHom,
      ⟨(IsLocalHom.of_surjective e.symm.toRingHom e.symm.surjective).map_nonunit⟩⟩
    have hs : s.comp g = Hom.id _ := LocalArtinAlgebra.Hom.ext e.symm_apply_apply
    obtain ⟨a, ha⟩ := hA (F.toFunctor.map g y)
    refine ⟨R.representable.toFunctor.map s a, ?_⟩
    rw [naturality_apply τ, ha]
    have hs' : (g : B ⟶ A) ≫ (s : A ⟶ B) = 𝟙 B := hs
    have heq := (F.toFunctor.map_comp g s).symm
    rw [hs', F.toFunctor.map_id] at heq
    exact ConcreteCategory.congr_hom heq y
  | single g hg => exact surjective_of_small hτ g hg
  | cons q g hq _ ih => exact fun hA => surjective_of_small hτ q hq (ih hA)

/-- Each element over an Artin algebra is in the image of the hull. -/
theorem hull_component_surjective (h : F.Hull) (A : LocalArtinAlgebra.{u,u} k) :
    Function.Surjective (h.transformation.app A) := by
  let g := residueHom A
  obtain ⟨_, hg⟩ := surjection_factors_smallExtensions g (residue_surjective A)
  apply surjective_of_chain h.smooth hg
  exact fun y => ⟨default, Subsingleton.elim _ y⟩

private theorem representable_comparison_bijective (R : CompleteLocalAlgebra k)
    (f : Hom B A) (g : Hom C A) :
    Function.Bijective ((R.representable : ArtinFunctor.{u,w} k).comparison f g) := by
  constructor
  · intro p q hpq
    have hfst := congrArg (fun p => p.val.1) hpq
    have hsnd := congrArg (fun p => p.val.2) hpq
    apply ULift.ext
    apply CompleteLocalAlgebra.Hom.ext
    intro r
    exact Subtype.ext (Prod.ext
      (congrArg (fun x : ULift (CompleteLocalAlgebra.Hom R B) => x.down r) hfst)
      (congrArg (fun x : ULift (CompleteLocalAlgebra.Hom R C) => x.down r) hsnd))
  · rintro ⟨⟨a, b⟩, hab⟩
    let p := a.down.val.prod b.down.val
    let q : R →ₐ[k] pullback f g :=
      p.codRestrict (AlgHom.pullback f.val g.val)
        (fun r => congrArg (fun x : ULift (CompleteLocalAlgebra.Hom R A) => x.down r) hab)
    refine ⟨ULift.up ⟨q, ⟨fun r hr => ?_⟩⟩, rfl⟩
    let : IsLocalHom a.down.val := a.down.property
    exact IsUnit.of_map a.down.val r (hr.map (pullbackFst f g).val)

private theorem h1_of_hull (h : F.Hull) : F.H1 := by
  intro A₁ A A₂ f g hg p
  obtain ⟨a, ha⟩ := hull_component_surjective h A₁ p.val.1
  have he := (naturality_apply h.transformation f a).trans
    ((congrArg (fun x => F.toFunctor.map f x) ha).trans p.property)
  obtain ⟨b, hb₁, hb₂⟩ := Smooth.lift h.smooth g hg _ p.val.2 he
  obtain ⟨c, hc⟩ := (representable_comparison_bijective h.ring f g).surjective
    ⟨(a, b), hb₁.symm⟩
  have hc₁ : (CompleteLocalAlgebra.representable h.ring).toFunctor.map (pullbackFst f g) c = a :=
    congrArg (fun x => x.val.1) hc
  have hc₂ : (CompleteLocalAlgebra.representable h.ring).toFunctor.map (pullbackSnd f g) c = b :=
    congrArg (fun x => x.val.2) hc
  refine ⟨h.transformation.app _ c, Subtype.ext (Prod.ext ?_ ?_)⟩
  · change F.toFunctor.map _ (h.transformation.app _ c) = p.val.1
    rw [← naturality_apply, hc₁, ha]
  · change F.toFunctor.map _ (h.transformation.app _ c) = p.val.2
    rw [← naturality_apply, hc₂, hb₂]

private theorem h2_of_hull (h : F.Hull) : F.H2 := by
  intro A
  let f := residueHom A
  let g := residueHom (dualNumbers k)
  let p := pullbackFst f g
  let q := pullbackSnd f g
  have hg := smallExtension_dual_residue k
  refine ⟨?_, h1_of_hull h f g hg⟩
  intro x y hxy
  have hpx : F.toFunctor.map p x = F.toFunctor.map p y :=
    congrArg (fun t => t.val.1) hxy
  have hqx : F.toFunctor.map q x = F.toFunctor.map q y :=
    congrArg (fun t => t.val.2) hxy
  obtain ⟨a, ha⟩ := hull_component_surjective h A (F.toFunctor.map p x)
  have hp := smallExtension_pullbackFst f g hg
  -- Lift both elements with the same map to A.
  obtain ⟨b, hb₁, hb₂⟩ := Smooth.lift h.smooth p hp a x ha
  obtain ⟨c, hc₁, hc₂⟩ := Smooth.lift h.smooth p hp a y (ha.trans hpx)
  have hq : (CompleteLocalAlgebra.representable h.ring).toFunctor.map q b =
      (CompleteLocalAlgebra.representable h.ring).toFunctor.map q c := by
    apply h.tangent_bijective.injective
    rw [naturality_apply, naturality_apply, hb₂, hc₂, hqx]
  have hbc := (representable_comparison_bijective h.ring f g).injective
    (Subtype.ext (Prod.ext (hb₁.trans hc₁.symm) hq))
  exact hb₂.symm.trans (hbc ▸ hc₂)

open SchlessingerTangentVectorSpaceSpec

private theorem truncation_maximalIdeal_sq (R : CompleteLocalAlgebra k) :
    IsLocalRing.maximalIdeal (R.truncation 1) ^ 2 = ⊥ := by
  let q := R.toTruncation 1
  have hq : Function.Surjective q.val.toRingHom := R.toTruncation_surjective 1
  rw [← IsLocalRing.map_maximalIdeal_of_surjective q.val.toRingHom hq,
    ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker]
  exact (R.ker_toTruncation 1).ge

private theorem split_maximalIdeal_mul_zero {I : Type u} [AddCommGroup I] [Module k I]
    [Module.Finite k I] {a b : split k I}
    (ha : a ∈ IsLocalRing.maximalIdeal (split k I))
    (hb : b ∈ IsLocalRing.maximalIdeal (split k I)) : a * b = 0 := by
  rw [← ker_residue (split k I)] at ha hb
  have ha' : (show TrivSqZeroExt k I from a).fst = 0 := ha
  have hb' : (show TrivSqZeroExt k I from b).fst = 0 := hb
  apply TrivSqZeroExt.ext
  · change (show TrivSqZeroExt k I from a).fst * (show TrivSqZeroExt k I from b).fst = 0
    rw [ha', zero_mul]
  · change (show TrivSqZeroExt k I from a).fst • (show TrivSqZeroExt k I from b).snd +
      (show TrivSqZeroExt k I from b).fst • (show TrivSqZeroExt k I from a).snd = 0
    rw [ha', hb', zero_smul, zero_smul, add_zero]

private def descend_to_truncation (R : CompleteLocalAlgebra k)
    {I : Type u} [AddCommGroup I] [Module k I] [Module.Finite k I]
    (f : CompleteLocalAlgebra.Hom R (split k I)) : Hom (R.truncation 1) (split k I) := by
  have hf : IsLocalRing.maximalIdeal R ^ 2 ≤ RingHom.ker f.val.toRingHom := by
    rw [pow_two, Ideal.mul_le]
    intro a ha b hb
    change f.val (a * b) = 0
    rw [map_mul]
    apply split_maximalIdeal_mul_zero
    · exact (IsLocalRing.mem_maximalIdeal _).mpr fun h =>
        (IsLocalRing.mem_maximalIdeal _).mp ha (f.property.map_nonunit _ h)
    · exact (IsLocalRing.mem_maximalIdeal _).mpr fun h =>
        (IsLocalRing.mem_maximalIdeal _).mp hb (f.property.map_nonunit _ h)
  refine ⟨Ideal.Quotient.liftₐ _ f.val hf, ⟨?_⟩⟩
  intro a ha
  obtain ⟨r, rfl⟩ := R.toTruncation_surjective 1 a
  exact (f.property.map_nonunit r ha).map (R.toTruncation 1).val

private def centered (A : LocalArtinAlgebra.{u,u} k) :
    A →ₗ[k] IsLocalRing.maximalIdeal A :=
  (LinearMap.id - (Algebra.linearMap k A).comp A.residue.toLinearMap).codRestrict
    ((IsLocalRing.maximalIdeal A).restrictScalars k) (fun a => by
      rw [← ker_residue A]
      change A.residue (a - algebraMap k A (A.residue a)) = 0
      simp)

private theorem centered_apply (A : LocalArtinAlgebra.{u,u} k) (a : A) :
    (centered A a : A) = a - algebraMap k A (A.residue a) := rfl

/-- Split a square-zero local algebra using the section supplied by its k-algebra structure. -/
private def toSplit (A : LocalArtinAlgebra.{u,u} k)
    [Module.Finite k (IsLocalRing.maximalIdeal A)] (hA : IsLocalRing.maximalIdeal A ^ 2 = ⊥) :
    Hom A (split k (IsLocalRing.maximalIdeal A)) := by
  let S := split k (IsLocalRing.maximalIdeal A)
  let toPair (a : A) : S := (A.residue a, centered A a)
  have hc (a b : A) : (centered A a : A) * (centered A b : A) = 0 := by
    have hm := Ideal.mul_mem_mul (centered A a).property (centered A b).property
    rw [← pow_two, hA] at hm
    exact hm
  let φ : A →ₐ[k] S :=
    { toFun := toPair
      map_zero' := by
        apply TrivSqZeroExt.ext (R := k) (M := ↥(IsLocalRing.maximalIdeal A))
        · exact map_zero A.residue
        · exact map_zero (centered A)
      map_one' := by
        apply TrivSqZeroExt.ext (R := k) (M := ↥(IsLocalRing.maximalIdeal A))
        · exact map_one A.residue
        · apply Subtype.ext
          change (centered A 1 : A) = 0
          simp [centered_apply]
      map_add' := fun a b => by
        apply TrivSqZeroExt.ext (R := k) (M := ↥(IsLocalRing.maximalIdeal A))
        · exact map_add A.residue a b
        · exact map_add (centered A) a b
      map_mul' := fun a b => by
        apply TrivSqZeroExt.ext (R := k) (M := ↥(IsLocalRing.maximalIdeal A))
        · exact map_mul A.residue a b
        · apply Subtype.ext
          change (centered A (a * b) : A) =
            ↑(A.residue a • centered A b + A.residue b • centered A a)
          have hmul := hc a b
          simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, Algebra.smul_def,
            centered_apply, map_mul] at hmul ⊢
          linear_combination hmul
      commutes' := fun c => by
        apply TrivSqZeroExt.ext (R := k) (M := ↥(IsLocalRing.maximalIdeal A))
        · exact A.residue_algebraMap c
        · apply Subtype.ext
          change (centered A (algebraMap k A c) : A) = 0
          simp [centered_apply] }
  exact ⟨φ, ⟨fun a ha => IsUnit.of_map A.residue a (ha.map S.residue)⟩⟩

private theorem splitMap_toSplit (A : LocalArtinAlgebra.{u,u} k)
    [Module.Finite k (IsLocalRing.maximalIdeal A)] (hA : IsLocalRing.maximalIdeal A ^ 2 = ⊥)
    (b : Hom A (split k k)) :
    ∃ l : Module.Dual k (IsLocalRing.maximalIdeal A), (splitMap l).comp (toSplit A hA) = b := by
  let d : A →ₗ[k] k := (TrivSqZeroExt.sndHom k k).comp b.val.toLinearMap
  let l : Module.Dual k (IsLocalRing.maximalIdeal A) :=
    d.comp ((IsLocalRing.maximalIdeal A).restrictScalars k).subtype
  refine ⟨l, LocalArtinAlgebra.Hom.ext fun a => TrivSqZeroExt.ext ?_ ?_⟩
  · change (splitMap l ((toSplit A hA).val a) : TrivSqZeroExt k k).fst = (b.val a).fst
    rw [splitMap_fst]
    exact (LocalArtinAlgebra.Hom.residue_apply b a).symm
  · change (splitMap l ((toSplit A hA).val a) : TrivSqZeroExt k k).snd = (b.val a).snd
    rw [splitMap_snd]
    change l (centered A a) = d a
    change d (a - algebraMap k A (A.residue a)) = d a
    rw [map_sub, show d (algebraMap k A (A.residue a)) = 0 from ?_, sub_zero]
    change (show TrivSqZeroExt k k from b.val (algebraMap k A (A.residue a))).snd = 0
    rw [b.val.commutes]
    rfl

private theorem h3_of_hull (h : F.Hull) (h₂ : F.H2) : F.H3 := by
  let R : CompleteLocalAlgebra k := h.ring
  let A := R.truncation 1
  -- The maximal ideal of R / m² is the cotangent space m / m².
  let I : Ideal A := IsLocalRing.maximalIdeal A
  let : Module.Finite k A := moduleFinite A
  let : Module.Finite k I :=
    Module.Finite.of_injective (I.restrictScalars k).subtype Subtype.val_injective
  let ρ := toSplit A (truncation_maximalIdeal_sq R)
  let q := R.toTruncation 1
  let c : (CompleteLocalAlgebra.representable R).toFunctor.obj (split k I) :=
    ULift.up (q.postcomp ρ)
  let x : SplitValue F I := h.transformation.app _ c
  let := F.tangentAddCommGroup h₂
  let := F.tangentModule h₂
  let e := F.splitTensorComparison h₂ (↥I)
  let g : Module.Dual k I →ₗ[k] F.Tangent := tensorContraction (e.equiv x)
  refine ⟨F.tangentVectorLaws h₂, Module.Finite.of_surjective g ?_⟩
  intro t
  let y := (tangentIdentification F).symm t
  obtain ⟨b, hb⟩ := hull_component_surjective h (split k k) y
  obtain ⟨l, hl⟩ := splitMap_toSplit A (truncation_maximalIdeal_sq R) (descend_to_truncation R b.down)
  refine ⟨l, ?_⟩
  change tensorContraction (e.equiv x) l = t
  have hl' : (CompleteLocalAlgebra.representable R).toFunctor.map (splitMap l) c = b := by
    apply ULift.ext
    apply CompleteLocalAlgebra.Hom.ext
    intro r
    exact congrArg (fun f : Hom A (split k k) => f.val (q.val r)) hl
  rw [e.contract, show onLinear F l x = y from
    (naturality_apply h.transformation (splitMap l) c).symm.trans (hl' ▸ hb)]
  exact (tangentIdentification F).apply_symm_apply t

/-- The existence of a hull implies Schlessinger's conditions H1, H2, and H3. -/
theorem conditions_of_hull (F : ArtinFunctor.{u,w} k) (h : Nonempty F.Hull) :
    F.H1 ∧ F.H2 ∧ F.H3 := by
  obtain ⟨h⟩ := h
  have h₂ := h2_of_hull h
  exact ⟨h1_of_hull h, h₂, h3_of_hull h h₂⟩

end ArtinFunctor
end CommutativeAlgebraNotes
