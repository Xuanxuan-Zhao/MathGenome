import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.MaximalUnramifiedTorusTorsors
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.MaximalUnramifiedBrauer
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.NonabelianCohomology
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.SmoothTorsors
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.RelativeIsomorphism
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ULift
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

namespace LinearAlgebraicGroups.Arithmetic.MaximalUnramifiedTorusTorsors

open MaximalUnramifiedBrauer CategoryTheory groupCohomology

universe u

/-- Scalar degree-two cocycles correspond to classes in the relative Brauer group. -/
private theorem scalarCoboundary
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (E L : Type u) [Field E] [Algebra (maximalUnramified F) E]
    [FiniteDimensional (maximalUnramified F) E] [Algebra.IsSeparable (maximalUnramified F) E]
    [Field L] [Algebra E L] [FiniteDimensional E L] [IsGalois E L]
    (c : Gal(L/E) × Gal(L/E) → Lˣ) (hc : IsMulCocycle₂ c) :
    IsMulCoboundary₂ c := by
  obtain ⟨z, hz⟩ := brauerGroup_trivial.{u,u,u} F E
  have hB : Subsingleton (BrauerGroup.{u,u} E) :=
    ⟨fun a b => (hz a).trans (hz b).symm⟩
  open RM03.Brauer.ScalarObstruction in
  have hEq : cocycleClass E L ⟨c, hc⟩ = 1 := by
    let e := RM03.Brauer.RelativeIsomorphism.relativeBrauerEquiv.{u,u,u} (k := E) (K := L)
    exact e.symm.injective (Subtype.ext (Subsingleton.elim _ _))
  open RM03.Brauer.ScalarObstruction in
  obtain ⟨a, ha⟩ := (QuotientGroup.eq_one_iff _).mp hEq
  refine ⟨a, fun g j => ?_⟩
  exact congrArg (fun z : ScalarCocycle E L => z.val (g, j)) ha

private abbrev Z := ULift.{u} ℤ

local instance unitsDistribAction (E L : Type u) [Field E] [Field L] [Algebra E L] :
    DistribMulAction Gal(L/E) (Additive Lˣ) :=
  { smul := fun g a => Additive.ofMul (g • a.toMul)
    one_smul := fun a => one_smul Gal(L/E) a.toMul
    mul_smul := fun g h a => mul_smul g h a.toMul
    smul_zero := fun g => congrArg Additive.ofMul ((show g • (1 : Lˣ) = 1 from smul_one g))
    smul_add := fun g a b => smul_mul' g a.toMul b.toMul }

local instance unitsSmulComm (E L : Type u) [Field E] [Field L] [Algebra E L] :
    SMulCommClass Gal(L/E) Z.{u} (Additive Lˣ) :=
  ⟨fun g n x => (DistribSMul.toAddMonoidHom (Additive Lˣ) g).map_zsmul n.down x⟩

private noncomputable def unitRep (E L : Type u) [Field E] [Field L] [Algebra E L] :
    Rep Z.{u} Gal(L/E) := Rep.ofDistribMulAction Z.{u} Gal(L/E) (Additive Lˣ)

private theorem scalarCohomology
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {K : Type u} [Field K] [Algebra (maximalUnramified F) K]
    [FiniteDimensional (maximalUnramified F) K] [Algebra.IsSeparable (maximalUnramified F) K]
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (J : Subgroup Gal(L/K)) (n : ℕ) (hn : n = 1 ∨ n = 2) :
    Limits.IsZero (groupCohomology (Rep.res J.subtype (unitRep K L)) n) := by
  let E := IntermediateField.fixedField J
  letI : Algebra (maximalUnramified F) E := RingHom.toAlgebra
    ((algebraMap K E).comp (algebraMap (maximalUnramified F) K))
  letI : IsScalarTower (maximalUnramified F) K E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional (maximalUnramified F) E := FiniteDimensional.trans _ K _
  haveI : Algebra.IsSeparable (maximalUnramified F) E := Algebra.IsSeparable.trans _ K _
  let e := IntermediateField.subgroupEquivAlgEquiv J
  have he : ∀ (g : J) (z : Additive Lˣ),
      (unitRep E L).ρ (e g) z =
        (unitRep K L).ρ g.val z := by
    intro g z
    exact Units.ext ((congrFun (IntermediateField.coe_subgroupEquivAlgEquiv_apply (H := J) g) z.toMul.val))
  let iso := groupCohomology.mapIso
    (A := unitRep E L)
    (B := Rep.res J.subtype (unitRep K L)) e
    (LinearEquiv.refl Z.{u} (Additive Lˣ))
    (fun g => LinearMap.ext fun z => (he g z).symm) n
  apply Limits.IsZero.of_iso _ iso
  apply ModuleCat.isZero_iff_subsingleton.2
  constructor
  intro x y
  suffices ∀ z : groupCohomology (unitRep E L) n, z = 0 by
    exact (this x).trans (this y).symm
  intro z
  rcases hn with rfl | rfl
  · induction z using H1_induction_on with
    | _ c =>
      apply (H1π_eq_zero_iff c).2
      change c.val ∈ coboundaries₁ (Rep.ofDistribMulAction Z.{u} Gal(L/E) (Additive Lˣ))
      let f : Gal(L/E) → Additive Lˣ := c.val
      have hc : IsMulCocycle₁ (Additive.toMul ∘ f) :=
        fun g h => congrArg Additive.toMul
          (isCocycle₁_of_mem_cocycles₁ (k := Z.{u}) f c.property g h)
      obtain ⟨b, hb⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units _ hc
      exact (coboundariesOfIsCoboundary₁ (k := Z.{u}) (f := f) ⟨Additive.ofMul b, fun g => congrArg Additive.ofMul (hb g)⟩).property
  · induction z using H2_induction_on with
    | _ c =>
      apply (H2π_eq_zero_iff c).2
      change c.val ∈ coboundaries₂ (Rep.ofDistribMulAction Z.{u} Gal(L/E) (Additive Lˣ))
      let f : Gal(L/E) × Gal(L/E) → Additive Lˣ := c.val
      have hc : IsMulCocycle₂ (Additive.toMul ∘ f) :=
        fun g h j => congrArg Additive.toMul
          (isCocycle₂_of_mem_cocycles₂ (k := Z.{u}) f c.property g h j)
      obtain ⟨b, hb⟩ := scalarCoboundary F E L _ hc
      exact (coboundariesOfIsCoboundary₂ (k := Z.{u}) (f := f) ⟨Additive.ofMul ∘ b, fun g j => congrArg Additive.ofMul (hb g j)⟩).property

section Transfer

open Rep

variable {R G : Type u} [CommRing R] [Group G] [Finite G]

private noncomputable def cosetComponent (D : Rep R G) (J : Subgroup G) :
    G ⧸ J → (coind J.subtype (res J.subtype D) →ₗ[R] D) :=
  Quotient.lift
    (fun g : G => D.ρ g ∘ₗ LinearMap.proj g⁻¹ ∘ₗ
      (Representation.coindV J.subtype (res J.subtype D).ρ).subtype)
    (by
      intro a b hab
      have hmem : a⁻¹ * b ∈ J := QuotientGroup.leftRel_apply.mp hab
      let h : J := ⟨a⁻¹ * b, hmem⟩
      have hba : b = a * h.val := by simp [h]
      apply LinearMap.ext
      intro f
      change D.ρ a (f.val a⁻¹) = D.ρ b (f.val b⁻¹)
      rw [hba, mul_inv_rev]
      have hf := f.property h⁻¹ a⁻¹
      change f.val (h.val⁻¹ * a⁻¹) = D.ρ h.val⁻¹ (f.val a⁻¹) at hf
      rw [hf, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_right])

private noncomputable def cosetTrace (D : Rep R G) (J : Subgroup G) :
    coind J.subtype (res J.subtype D) ⟶ D := by
  classical
  letI : Fintype (G ⧸ J) := Fintype.ofFinite _
  refine Rep.ofHom ⟨∑ q : G ⧸ J, cosetComponent D J q, fun g => ?_⟩
  apply LinearMap.ext
  intro f
  change (∑ q : G ⧸ J, cosetComponent D J q) ((coind J.subtype (res J.subtype D)).ρ g f) =
    D.ρ g ((∑ q : G ⧸ J, cosetComponent D J q) f)
  simp only [LinearMap.sum_apply, map_sum]
  apply Fintype.sum_equiv (MulAction.toPerm g⁻¹)
  intro q
  refine Quotient.inductionOn' q ?_
  intro a
  change D.ρ a (f.val (a⁻¹ * g)) =
    D.ρ g (D.ρ (g⁻¹ * a) (f.val (g⁻¹ * a)⁻¹))
  simp only [mul_inv_rev, inv_inv, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

private theorem index_annihilates (D : Rep R G) (J : Subgroup G) (n : ℕ)
    (h : Limits.IsZero (groupCohomology (res J.subtype D) n)) :
    ∀ x : groupCohomology D n, J.index • x = 0 := by
  classical
  letI : Fintype (G ⧸ J) := Fintype.ofFinite _
  let i := resCoindToHom J.subtype D (res J.subtype D) (𝟙 _)
  have hi : i ≫ cosetTrace D J = J.index • (𝟙 D) := by
    apply Rep.hom_ext
    apply DFunLike.ext
    intro x
    change (∑ q : G ⧸ J, cosetComponent D J q) (i.hom x) = J.index • x
    simp only [LinearMap.sum_apply]
    have hterm (q : G ⧸ J) : cosetComponent D J q (i.hom x) = x := by
      refine Quotient.inductionOn' q ?_
      intro a
      change D.ρ a (D.ρ a⁻¹ x) = x
      simp [← Module.End.mul_apply, ← map_mul]
    simp [hterm, ← Nat.card_eq_fintype_card, J.index_eq_card]
  let f := groupCohomology.functor R G n
  haveI : f.Additive := inferInstanceAs
    ((cochainsFunctor R G ⋙ HomologicalComplex.homologyFunctor _ _ n).Additive)
  have hzero := h.of_iso (coindIso (res J.subtype D) n)
  have hz : f.map i = 0 := hzero.eq_of_tgt ..
  have hx : J.index • (𝟙 (f.obj D)) = 0 := by
    have hm := congrArg f.map hi
    rw [Functor.map_comp, hz, Limits.zero_comp, Functor.map_nsmul, f.map_id] at hm
    exact hm.symm
  intro x
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hx) x

private theorem card_annihilates (D : Rep R G) (n : ℕ) :
    ∀ x : groupCohomology D (n + 1), Nat.card G • x = 0 :=
  Subgroup.index_bot (G := G) ▸ index_annihilates D ⊥ _ (isZero_groupCohomology_succ_of_subsingleton _ n)

end Transfer

section ExactSequences

open Rep Limits

variable {R G : Type u} [CommRing R] [Group G]

private theorem repShortExact {C : ShortComplex (Rep.{u} R G)} (hf : Function.Injective C.f)
    (hg : Function.Surjective C.g) (hfg : Function.Exact (C.f.hom.toLinearMap)
      (C.g.hom.toLinearMap)) : C.ShortExact :=
  ShortComplex.ShortExact.mk'
    ((C.exact_map_iff_of_faithful (forget₂ (Rep R G) (ModuleCat R))).1
      ((C.map (forget₂ (Rep R G) (ModuleCat R))).moduleCat_exact_iff.2
        (fun x hx => (hfg x).mp hx)))
    ((Rep.mono_iff_injective _).2 hf) ((Rep.epi_iff_surjective _).2 hg)

private instance (M : Rep.{u} R G) : (Rep.ihom M).PreservesZeroMorphisms where
  map_zero _ _ := by ext x y; rfl

private theorem ihom_shortExact {C : ShortComplex (Rep.{u} R G)} (hC : C.ShortExact)
    (M : Rep.{u} R G) [Module.Projective R M.V] :
    (C.map (Rep.ihom M)).ShortExact := by
  have hE := (C.map (forget₂ (Rep R G) (ModuleCat R))).moduleCat_exact_iff.mp
    ((C.exact_map_iff_of_faithful (forget₂ (Rep R G) (ModuleCat R))).2 hC.exact)
  have hf := (Rep.mono_iff_injective C.f).1 hC.mono_f
  have hg := (Rep.epi_iff_surjective C.g).1 hC.epi_g
  apply repShortExact
  · intro f g h
    change (f : M.V →ₗ[R] C.X₁.V) = g
    apply LinearMap.ext
    intro m
    change C.f.hom.toLinearMap.comp (f : M.V →ₗ[R] C.X₁.V) =
      C.f.hom.toLinearMap.comp (g : M.V →ₗ[R] C.X₁.V) at h
    exact hf (DFunLike.congr_fun h m)
  · intro f
    change M.V →ₗ[R] C.X₃.V at f
    obtain ⟨g, hg⟩ := Module.projective_lifting_property C.g.hom.toLinearMap f hg
    exact ⟨g, hg⟩
  · intro f
    change M.V →ₗ[R] C.X₂.V at f
    change C.g.hom.toLinearMap.comp f = 0 ↔
      ∃ g : M.V →ₗ[R] C.X₁.V, C.f.hom.toLinearMap.comp g = f
    constructor
    · intro h
      change ∀ x : C.X₂, C.g.hom x = 0 → ∃ y : C.X₁, C.f.hom y = x at hE
      choose lift hlift using fun m : M.V => hE (f m) (DFunLike.congr_fun h m)
      refine ⟨{toFun := lift, map_add' := ?_, map_smul' := ?_}, LinearMap.ext hlift⟩
      · intro x y
        apply hf
        simp only [map_add, hlift]
      · intro r x
        apply hf
        simp only [map_smul, hlift, RingHom.id_apply]
    · rintro ⟨g, rfl⟩
      ext m
      exact DFunLike.congr_fun (congrArg Rep.Hom.hom C.zero) (g m)

end ExactSequences


section FreePresentation

open Rep Limits

variable {R G : Type u} [CommRing R] [Group G] [Finite G]

private noncomputable abbrev cofree (V : Type u) [AddCommGroup V] [Module R V] : Rep R G :=
  coind (⊥ : Subgroup G).subtype (trivial R (⊥ : Subgroup G) V)

private def cofreeValue (V : Type u) [AddCommGroup V] [Module R V] (f : G → V) :
    cofree (R := R) (G := G) V :=
  ⟨f, fun g h => by
    have hg : g.val = (1 : G) := Subgroup.mem_bot.1 g.property
    change f (g.val * h) = f h
    rw [hg, one_mul]⟩

private theorem cofree_isZero (V : Type u) [AddCommGroup V] [Module R V] (n : ℕ) :
    IsZero (groupCohomology (cofree (R := R) (G := G) V) (n + 1)) :=
  (isZero_groupCohomology_succ_of_subsingleton _ n).of_iso (coindIso _ (n + 1))

private noncomputable def cofreeTo (A : Rep.{u} R G)
    {V : Type u} [AddCommGroup V] [Module R V] (f : V →ₗ[R] A.V) :
    cofree (G := G) V ⟶ A := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  refine Rep.ofHom ⟨∑ g : G, A.ρ g⁻¹ ∘ₗ f ∘ₗ
    LinearMap.proj g ∘ₗ (Representation.coindV (⊥ : Subgroup G).subtype
      (Representation.trivial R (⊥ : Subgroup G) V)).subtype, ?_⟩
  intro s
  ext x
  simp only [LinearMap.comp_apply, LinearMap.sum_apply]
  change (∑ g : G, A.ρ g⁻¹ (f (x.val (g * s)))) =
    A.ρ s (∑ g : G, A.ρ g⁻¹ (f (x.val g)))
  rw [map_sum]
  apply Fintype.sum_equiv (Equiv.mulRight s)
  intro g
  simp only [← Module.End.mul_apply, ← map_mul]
  change A.ρ g⁻¹ (f (x.val (g * s))) = A.ρ (s * (g * s)⁻¹) (f (x.val (g * s)))
  simp [mul_inv_rev]

private theorem cofreeTo_surjective (A : Rep.{u} R G)
    {V : Type u} [AddCommGroup V] [Module R V] (f : V →ₗ[R] A.V)
    (hf : Function.Surjective f) : Function.Surjective (cofreeTo A f) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  intro a
  obtain ⟨v, hv⟩ := hf a
  refine ⟨cofreeValue V (fun g => if g = 1 then v else 0), ?_⟩
  simp only [cofreeTo, Rep.hom_ofHom, Representation.IntertwiningMap.coe_mk,
    LinearMap.sum_apply, LinearMap.comp_apply]
  change (∑ g : G, A.ρ g⁻¹ (f (if g = 1 then v else 0))) = a
  rw [Finset.sum_eq_single (1 : G)]
  · simp [hv]
  · intro g _ hg
    simp [hg]
  · simp

private noncomputable def kerRep {X Y : Rep.{u} R G} (f : X ⟶ Y) :
    Subrepresentation X.ρ where
  toSubmodule := LinearMap.ker f.hom.toLinearMap
  apply_mem_toSubmodule g := by
    intro x hx
    change f.hom (X.ρ g x) = 0
    rw [hom_comm_apply, show f.hom x = 0 from hx, map_zero]

private noncomputable def kerSequence {X Y : Rep.{u} R G} (f : X ⟶ Y) :
    ShortComplex (Rep R G) :=
  ShortComplex.mk (Rep.ofHom
    (⟨(kerRep f).toSubmodule.subtype, fun _ => rfl⟩ :
      (kerRep f).toRepresentation.IntertwiningMap X.ρ)) f (by
        ext x
        exact x.property)

private theorem kerSequence_exact {X Y : Rep.{u} R G} (f : X ⟶ Y)
    (hf : Function.Surjective f) : (kerSequence f).ShortExact := by
  apply repShortExact Subtype.val_injective hf
  intro x
  exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.property⟩

private theorem ihom_cofree_H1 (M : Rep.{u} R G)
    (V : Type u) [AddCommGroup V] [Module R V] :
    IsZero (H1 ((Rep.ihom M).obj (cofree (R := R) (G := G) V))) := by
  let Q := cofree (R := R) (G := G) V
  let D := (Rep.ihom M).obj Q
  apply ModuleCat.isZero_iff_subsingleton.2
  constructor
  intro x y
  suffices ∀ z : H1 D, z = 0 by exact (this x).trans (this y).symm
  intro z
  induction z using H1_induction_on with
  | _ c =>
    have hc := (mem_cocycles₁_iff c.val).mp c.property
    let a : G → (M.V →ₗ[R] Q.V) := c.val
    let b : M.V →ₗ[R] Q.V :=
      (LinearMap.pi fun g : G =>
        LinearMap.proj (1 : G) ∘ₗ
          (Representation.coindV (⊥ : Subgroup G).subtype
            (Representation.trivial R (⊥ : Subgroup G) V)).subtype ∘ₗ
          a g ∘ₗ M.ρ g).codRestrict _ fun m => (cofreeValue V _).property
    apply (H1π_eq_zero_iff c).2
    refine ⟨b, ?_⟩
    funext s
    change (Q.ρ s ∘ₗ b ∘ₗ M.ρ s⁻¹) - b = a s
    apply LinearMap.ext
    intro m
    apply Subtype.ext
    funext g
    have h := congrArg (fun h : M.V →ₗ[R] Q.V => (h (M.ρ g m)).val 1) (hc g s)
    change (a (g * s) (M.ρ g m)).val 1 =
      (a s (M.ρ g⁻¹ (M.ρ g m))).val (1 * g) +
        (a g (M.ρ g m)).val 1 at h
    simp only [one_mul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at h
    change (a (g * s) (M.ρ (g * s) (M.ρ s⁻¹ m))).val 1 -
      (a g (M.ρ g m)).val 1 = (a s m).val g
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_right] using
      sub_eq_iff_eq_add.mpr h

end FreePresentation


section Reduction

open Rep Limits

variable {G : Type u} [Group G]

variable {R : Type u} [CommRing R]

private noncomputable def rangeRep {X Y : Rep.{u} R G} (f : X ⟶ Y) :
    Subrepresentation Y.ρ where
  toSubmodule := LinearMap.range f.hom.toLinearMap
  apply_mem_toSubmodule g := by
    rintro y ⟨x, rfl⟩
    exact ⟨X.ρ g x, hom_comm_apply f g x⟩

private noncomputable def cokerSequence {X Y : Rep.{u} R G} (f : X ⟶ Y) :
    ShortComplex (Rep R G) :=
  ShortComplex.mk f (Rep.ofHom
    (⟨(rangeRep f).toSubmodule.mkQ, fun _ => rfl⟩ :
      Y.ρ.IntertwiningMap (rangeRep f).quotient)) (by
        ext x
        exact Submodule.Quotient.mk_eq_zero _ |>.2 ⟨x, rfl⟩)

private theorem cokerSequence_exact {X Y : Rep.{u} R G} (f : X ⟶ Y)
    (hf : Function.Injective f) : (cokerSequence f).ShortExact := by
  exact repShortExact hf (Submodule.mkQ_surjective _) (fun x =>
    (Submodule.Quotient.mk_eq_zero (rangeRep f).toSubmodule : Submodule.Quotient.mk x = 0 ↔ _))

private noncomputable def modSequence (p : ℕ) (B : Rep.{u} R G) :
    ShortComplex (Rep R G) :=
  cokerSequence (p • 𝟙 B)

private theorem modSequence_torsion (p : ℕ) (B : Rep.{u} R G)
    (x : (modSequence p B).X₃) : p • x = 0 := by
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective (rangeRep (p • 𝟙 B)).toSubmodule x
  change p • (rangeRep (p • 𝟙 B)).toSubmodule.mkQ b =
    (0 : B.V ⧸ (rangeRep (p • 𝟙 B)).toSubmodule)
  rw [← map_nsmul]
  exact (Submodule.Quotient.mk_eq_zero _).2 ⟨b, rfl⟩

private noncomputable def homPrecompose {X Y : Rep.{u} R G} (f : X ⟶ Y) (D : Rep.{u} R G) :
    (Rep.ihom Y).obj D ⟶ (Rep.ihom X).obj D :=
  Rep.ofHom ⟨LinearMap.llcomp R _ _ _ |>.flip f.hom.toLinearMap, fun g => by
    ext b x
    change D.ρ g (b (Y.ρ g⁻¹ (f.hom x))) = D.ρ g (b (f.hom (X.ρ g⁻¹ x)))
    rw [hom_comm_apply]⟩

private noncomputable def homSequence (D : Rep.{u} R G) (C : ShortComplex (Rep.{u} R G)) :
    ShortComplex (Rep R G) :=
  ShortComplex.mk (homPrecompose C.g D) (homPrecompose C.f D) (by
    apply Rep.hom_ext
    apply DFunLike.ext
    intro b
    change C.X₃.V →ₗ[R] D.V at b
    apply LinearMap.ext
    intro x
    change (b : C.X₃.V →ₗ[R] D.V) (C.g.hom (C.f.hom x)) = 0
    have hx : C.g.hom (C.f.hom x) = 0 :=
      DFunLike.congr_fun (congrArg Rep.Hom.hom C.zero) x
    rw [hx, map_zero])

private theorem homSequence_exact (D : Rep.{u} R G) (C : ShortComplex (Rep.{u} R G))
    (hC : C.ShortExact) (r : C.X₂.V →ₗ[R] C.X₁.V)
    (hr : Function.LeftInverse r C.f.hom) :
    (homSequence D C).ShortExact := by
  have hg := (Rep.epi_iff_surjective C.g).1 hC.epi_g
  apply repShortExact
  · intro a b hab
    change (a : C.X₃.V →ₗ[R] D.V) = b
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := hg x
    exact DFunLike.congr_fun
      (show (a : C.X₃.V →ₗ[R] D.V).comp C.g.hom.toLinearMap =
        (b : C.X₃.V →ₗ[R] D.V).comp C.g.hom.toLinearMap from hab) y
  · intro a
    change C.X₁.V →ₗ[R] D.V at a
    exact ⟨a.comp r, LinearMap.ext fun x => congrArg a (hr x)⟩
  · intro a
    change C.X₂.V →ₗ[R] D.V at a
    change a.comp C.f.hom.toLinearMap = 0 ↔
      ∃ b : C.X₃.V →ₗ[R] D.V, b.comp C.g.hom.toLinearMap = a
    constructor
    · intro ha
      have hC' := ((C.map (forget₂ (Rep R G) (ModuleCat R))).moduleCat_exact_iff).1
        (hC.exact.map _)
      have hker : LinearMap.ker C.g.hom.toLinearMap ≤ LinearMap.ker a := by
        intro x hx
        obtain ⟨y, rfl⟩ : ∃ y : C.X₁, C.f.hom y = x := hC' x hx
        exact DFunLike.congr_fun ha y
      exact ⟨((LinearMap.ker C.g.hom.toLinearMap).liftQ a hker).comp
        ((C.g.hom.toLinearMap.quotKerEquivOfSurjective hg).symm.toLinearMap), by
          ext x
          exact congrArg _ (LinearMap.quotKerEquivOfSurjective_symm_apply C.g.hom.toLinearMap hg x)⟩
    · rintro ⟨b, rfl⟩
      ext x
      change b (C.g.hom (C.f.hom x)) = 0
      have hx : C.g.hom (C.f.hom x) = 0 :=
        DFunLike.congr_fun (congrArg Rep.Hom.hom C.zero) x
      rw [hx, map_zero]

private noncomputable def modHomIso (p : ℕ) (M D : Rep.{u} R G)
    (hD : ∀ d : D, p • d = 0) :
    (Rep.ihom (modSequence p M).X₃).obj D ≅ (Rep.ihom M).obj D := by
  let g := (modSequence p M).g
  let f := homPrecompose g D
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      change (a : (modSequence p M).X₃.V →ₗ[R] D.V) = b
      apply LinearMap.ext
      intro x
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (rangeRep (p • 𝟙 M)).toSubmodule x
      exact DFunLike.congr_fun
        (show (a : (modSequence p M).X₃.V →ₗ[R] D.V).comp g.hom.toLinearMap =
          (b : (modSequence p M).X₃.V →ₗ[R] D.V).comp g.hom.toLinearMap from hab) y
    · intro a
      change M.V →ₗ[R] D.V at a
      refine ⟨(rangeRep (p • 𝟙 M)).toSubmodule.liftQ a ?_, ?_⟩
      · rintro _ ⟨x, rfl⟩
        change a (p • x) = 0
        rw [map_nsmul, hD]
      · apply LinearMap.ext
        intro x
        rfl
  exact Rep.mkIso (Representation.Equiv.mk (LinearEquiv.ofBijective f.hom.toLinearMap hf) f.hom.2)

end Reduction


section PrimeGroup

open Rep Limits

variable {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

private def zModuleMap {U V : Type u} [AddCommGroup U] [AddCommGroup V]
    [Module Z.{u} U] [Module Z.{u} V] (f : U →+ V) : U →ₗ[Z.{u}] V where
  __ := f
  map_smul' n x := by
    have hn : (n.down : Z.{u}) = n := rfl
    rw [← hn, Int.cast_smul_eq_zsmul, RingHom.id_apply, Int.cast_smul_eq_zsmul]
    exact f.map_zsmul n.down x

private theorem mulPrime_surjective_H2_yields_zero (hG : IsPGroup p G)
    (B : Rep.{u} Z.{u} G)
    (hs : Function.Surjective (fun x : H2 B => p • x)) :
    IsZero (H2 B) := by
  obtain ⟨k, hk⟩ := hG.exists_card_eq
  have hp (m : ℕ) : Function.Surjective (fun x : H2 B => p ^ m • x) := by
    induction m with
    | zero => exact fun x => ⟨x, by simp⟩
    | succ m ih =>
      simpa only [Function.comp_def, pow_succ, mul_nsmul] using hs.comp ih
  apply ModuleCat.isZero_iff_subsingleton.2
  constructor
  intro x y
  suffices ∀ t : H2 B, t = 0 by exact (this x).trans (this y).symm
  intro t
  obtain ⟨s, rfl⟩ := hp k t
  exact hk ▸ card_annihilates B 1 s

/-- Shift to the kernel of a coinduced cover and reduce it modulo `p`. -/
private theorem primeGroupH1 (hG : IsPGroup p G)
    (A M : Rep.{u} Z.{u} G) [Module.Projective Z.{u} M.V]
    (hOne : IsZero (H1 A)) (hTwo : IsZero (H2 A))
    (devissage : ∀ D : Rep.{u} Z.{u} G, (∀ d : D, p • d = 0) → IsZero (H2 D) →
      IsZero (H2 ((Rep.ihom M).obj D))) :
    IsZero (H1 ((Rep.ihom M).obj A)) := by
  classical
  let V := A.V →₀ Z.{u}
  let π : V →ₗ[Z.{u}] A.V := Finsupp.linearCombination _ id
  let f := cofreeTo A π
  let C := kerSequence f
  have hC : C.ShortExact :=
    kerSequence_exact f (cofreeTo_surjective A π (Finsupp.linearCombination_surjective _ Function.surjective_id))
  let B := C.X₁
  have hB₂ : IsZero (H2 B) :=
    (mapShortComplex₁_exact hC (i := 1) (j := 2) rfl).isZero_of_both_isZero hOne (cofree_isZero V 1)
  have hB₃ : IsZero (groupCohomology B 3) :=
    (mapShortComplex₁_exact hC (i := 2) (j := 3) rfl).isZero_of_both_isZero hTwo (cofree_isZero V 2)
  let C' := modSequence p B
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hC' : C'.ShortExact := by
    apply cokerSequence_exact
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    funext g
    apply Finsupp.ext
    intro a
    apply ULift.ext
    have h' := congrArg (fun z : B => ((z.val.val g) a).down) h
    change p • ((x.val.val g) a).down = p • ((y.val.val g) a).down at h'
    exact nsmul_right_injective hp h'
  have hmod : IsZero (H2 C'.X₃) :=
    (mapShortComplex₃_exact hC' (i := 2) (j := 3) rfl).isZero_of_both_isZero hB₂ hB₃
  have hred := devissage C'.X₃ (modSequence_torsion p B) hmod
  have hC'M := ihom_shortExact hC' M
  let functorH := groupCohomology.functor Z.{u} G 2
  let B' := (Rep.ihom M).obj B
  let i : B' ⟶ B' := (Rep.ihom M).map (p • 𝟙 B)
  have hsurj : Function.Surjective (functorH.map i) := by
    let X := mapShortComplex₂ (C'.map (Rep.ihom M)) 2
    have he : X.Exact := mapShortComplex₂_exact hC'M 2
    intro x
    exact X.moduleCat_exact_iff.mp he x
      ((ModuleCat.isZero_iff_subsingleton.1 hred).elim _ _)
  have hsMul : Function.Surjective (fun x : H2 B' => p • x) := by
    haveI : functorH.Additive := inferInstanceAs
      ((cochainsFunctor Z.{u} G ⋙ HomologicalComplex.homologyFunctor _ _ 2).Additive)
    have hi : i = p • 𝟙 B' := by
      apply Rep.hom_ext
      apply DFunLike.ext
      intro f
      apply LinearMap.ext
      intro x
      rfl
    have hmap : functorH.map i = p • 𝟙 (functorH.obj B') :=
      (congrArg (fun f : B' ⟶ B' => functorH.map f) hi).trans
        ((Functor.map_nsmul functorH).trans (congrArg (p • ·) (functorH.map_id _)))
    intro x
    obtain ⟨y, hy⟩ := hsurj x
    refine ⟨y, ?_⟩
    exact (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hmap) y).symm.trans hy
  exact (mapShortComplex₃_exact (ihom_shortExact hC M) (i := 1) (j := 2) rfl).isZero_of_both_isZero
    (ihom_cofree_H1 M V) (mulPrime_surjective_H2_yields_zero hG _ hsMul)

end PrimeGroup


section PrimeFiltration

open Rep Limits

variable {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

private def downAddHom (A : Type) [AddCommGroup A] : ULift.{u} A →+ A where
  toFun := ULift.down
  map_zero' := rfl
  map_add' _ _ := rfl

private noncomputable abbrev trivialLine : Rep.{u} Z.{u} G :=
  Rep.trivial Z.{u} G (ULift.{u} (ZMod p))

private noncomputable def evalAtFixed {R : Type u} [CommRing R] (W D : Rep.{u} R G)
    (w : W.V) (hw : ∀ g : G, W.ρ g w = w) : (Rep.ihom W).obj D ⟶ D :=
  Rep.ofHom ⟨{ toFun := fun f => f w, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl },
    fun g => by
      ext f
      change D.ρ g (f (W.ρ g⁻¹ w)) = D.ρ g (f w)
      rw [hw]⟩

private noncomputable def repIsoOfBijective {R : Type u} [CommRing R] {W D : Rep.{u} R G}
    (f : W ⟶ D) (hf : Function.Bijective f) : W ≅ D :=
  Rep.mkIso (Representation.Equiv.mk (LinearEquiv.ofBijective f.hom.toLinearMap hf) f.hom.2)

private noncomputable def trivialLineHomIso (D : Rep.{u} Z.{u} G)
    (hD : ∀ d : D, p • d = 0) :
    ((Rep.ihom (trivialLine (G := G) (p := p))).obj D) ≅ D := by
  let W := trivialLine (G := G) (p := p)
  letI : Module (ZMod p) D.V := AddCommGroup.zmodModule hD
  let f := evalAtFixed W D (1 : W.V) (by intro g; rfl)
  apply repIsoOfBijective f
  constructor
  · intro a b h
    change W.V →ₗ[Z.{u}] D.V at a b
    apply LinearMap.ext
    intro x
    change a 1 = b 1 at h
    have hx : x.down • (1 : W.V) = x := by apply ULift.ext; exact mul_one _
    rw [← hx, ZMod.map_smul, ZMod.map_smul, h]
  · intro d
    let v : W.V →ₗ[Z.{u}] D.V :=
      zModuleMap ((((LinearMap.id : ZMod p →ₗ[ZMod p] ZMod p).smulRight d).toAddMonoidHom).comp
        (downAddHom (ZMod p)))
    refine ⟨v, ?_⟩
    change (1 : ZMod p) • d = d
    exact one_smul _ _

private theorem exists_scalarFunctional {k W : Type*} [Field k] [AddCommGroup W] [Module k W]
    (x : W) (hx : x ≠ 0) : ∃ f : W →ₗ[k] k, f x = 1 := by
  let j : k →ₗ[k] W := (LinearMap.id : k →ₗ[k] k).smulRight x
  have hj : Function.Injective j := smul_left_injective k hx
  obtain ⟨r, hr⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hj)
  exact ⟨r, by simpa [j] using DFunLike.congr_fun hr (1 : k)⟩

/-- Successive quotients by fixed lines transfer vanishing to the internal Hom. -/
private theorem primeFiltrationH2 (hG : IsPGroup p G)
    (D : Rep.{u} Z.{u} G) (hD : ∀ d : D, p • d = 0) (h₂ : IsZero (H2 D))
    (W : Rep.{u} Z.{u} G) [Finite W.V] (hW : ∀ w : W, p • w = 0) :
    IsZero (H2 ((Rep.ihom W).obj D)) := by
  classical
  by_cases hw : Subsingleton W.V
  · apply (groupCohomology.functor Z.{u} G 2).map_isZero
    apply (IsZero.iff_id_eq_zero _).2
    apply Rep.hom_ext
    apply DFunLike.ext
    intro f
    change W.V →ₗ[Z.{u}] D.V at f
    apply LinearMap.ext
    intro w
    rw [Subsingleton.elim w 0]
    change f 0 = 0
    exact map_zero _
  letI : Nontrivial W.V := not_subsingleton_iff_nontrivial.mp hw
  letI : MulAction G W.V :=
    { smul := fun g w => W.ρ g w
      one_smul := by intro w; change W.ρ 1 w = w; simp
      mul_smul := by intro g h w; change W.ρ (g * h) w = W.ρ g (W.ρ h w); simp }
  obtain ⟨w, hw0⟩ := exists_ne (0 : W.V)
  have hcard : p ∣ Nat.card W.V := by
    have ho : addOrderOf w = p :=
      ((Nat.dvd_prime (Fact.out : p.Prime)).mp ((addOrderOf_dvd_iff_nsmul_eq_zero).2 (hW w))).resolve_left
        (fun h => hw0 (AddMonoid.addOrderOf_eq_one_iff.mp h))
    rw [← ho, ← Nat.card_zmultiples]
    rw [(AddSubgroup.zmultiples w).card_eq_card_quotient_mul_card_addSubgroup]
    exact dvd_mul_left _ _
  obtain ⟨x, hx, hx0⟩ := hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := W.V)
    hcard (a := 0) (fun g => map_zero (W.ρ g))
  let L := trivialLine (G := G) (p := p)
  letI : Module (ZMod p) W.V := AddCommGroup.zmodModule hW
  let f : L.V →ₗ[Z.{u}] W.V :=
    zModuleMap (((LinearMap.id : ZMod p →ₗ[ZMod p] ZMod p).smulRight x).toAddMonoidHom.comp
      (downAddHom (ZMod p)))
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro a ha
    change a.down • x = 0 at ha
    apply ULift.ext
    change a.down = 0
    by_contra hn
    apply Ne.symm hx0
    calc
      x = a.down⁻¹ • (a.down • x) := by rw [smul_smul, inv_mul_cancel₀ hn, one_smul]
      _ = 0 := by rw [ha, smul_zero]
  let j : L ⟶ W := Rep.ofHom ⟨f, fun g => by
    apply LinearMap.ext
    intro a
    change a.down • x = W.ρ g (a.down • x)
    rw [ZMod.map_smul, show W.ρ g x = x from hx g]⟩
  let C := cokerSequence j
  have hC : C.ShortExact := cokerSequence_exact j hf
  let Q := C.X₃
  have hq : Function.Surjective C.g.hom := (Rep.epi_iff_surjective _).1 hC.epi_g
  haveI : Finite C.X₂.V := ‹Finite W.V›
  haveI : Finite Q.V := Finite.of_surjective _ hq
  have hQ (q : Q.V) : p • q = 0 := by
    obtain ⟨w, rfl⟩ := hq q
    exact (map_nsmul C.g.hom.toLinearMap p w).symm.trans
      (by rw [show p • w = 0 from hW w, map_zero])
  have hsmaller : Nat.card Q.V < Nat.card W.V := by
    haveI : Finite (W.V ⧸ (rangeRep j).toSubmodule) := ‹Finite Q.V›
    change Nat.card (W.V ⧸ (rangeRep j).toSubmodule) < Nat.card W.V
    rw [(rangeRep j).toSubmodule.card_eq_card_quotient_mul_card]
    apply lt_mul_of_one_lt_left Nat.card_pos
    rw [Finite.one_lt_card_iff_nontrivial]
    let z : (rangeRep j).toSubmodule := ⟨x, ⟨1, one_smul (ZMod p) x⟩⟩
    refine ⟨⟨0, z, ?_⟩⟩
    intro he
    exact hx0 (congrArg Subtype.val he)
  obtain ⟨r, hr⟩ := exists_scalarFunctional (k := ZMod p) x (Ne.symm hx0)
  let up : ZMod p →+ L.V :=
    { toFun := ULift.up, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hrep := homSequence_exact D C hC (zModuleMap (up.comp r.toAddMonoidHom)) (by
    intro a
    apply ULift.ext
    change r.toFun (a.down • x) = a.down
    exact (r.map_smul a.down x).trans (by rw [hr, smul_eq_mul, mul_one]))
  have hLeft := primeFiltrationH2 hG D hD h₂ Q hQ
  have hRight := h₂.of_iso ((groupCohomology.functor Z.{u} G 2).mapIso (trivialLineHomIso D hD))
  exact (mapShortComplex₂_exact hrep 2).isZero_of_both_isZero hLeft hRight
termination_by Nat.card W.V

end PrimeFiltration


section FiniteGroup

open Rep Limits

variable {G : Type u} [Group G] [Finite G]

private theorem mod_finite {p : ℕ} [NeZero p] (M : Rep.{u} Z.{u} G)
    {r : ℕ} (e : M.V ≃ₗ[Z.{u}] (Fin r → Z.{u})) :
    Finite (modSequence p M).X₃.V := by
  let f : (Fin r → ZMod p) → (modSequence p M).X₃.V := fun a =>
    (modSequence p M).g.hom (e.symm fun i => ULift.up (a i).val)
  apply Finite.of_surjective f
  intro q
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (rangeRep (p • 𝟙 M)).toSubmodule q
  let a : Fin r → ZMod p := fun i => (e m i).down
  refine ⟨a, ?_⟩
  change Submodule.Quotient.mk (p := (rangeRep (p • 𝟙 M)).toSubmodule)
    (e.symm fun i => ULift.up (a i).val) = Submodule.Quotient.mk m
  apply (Submodule.Quotient.eq (p := (rangeRep (p • 𝟙 M)).toSubmodule)).mpr
  have hd (i : Fin r) : (p : ℤ) ∣ (a i).val - (e m i).down := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
    rw [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val, sub_eq_zero]
  choose b hb using hd
  refine ⟨e.symm (fun i => ULift.up (b i)), ?_⟩
  apply e.injective
  change e (p • e.symm (fun i => ULift.up (b i))) =
    e (e.symm (fun i => ULift.up (a i).val) - m)
  rw [map_nsmul, map_sub, e.apply_symm_apply, e.apply_symm_apply]
  funext i
  exact ULift.ext (hb i).symm

private theorem finiteGroupH1 (A M : Rep.{u} Z.{u} G)
    {r : ℕ} (e : M.V ≃ₗ[Z.{u}] (Fin r → Z.{u}))
    (hA : ∀ J : Subgroup G, IsZero (H1 (res J.subtype A)) ∧ IsZero (H2 (res J.subtype A))) :
    IsZero (H1 ((Rep.ihom M).obj A)) := by
  classical
  let D := (Rep.ihom M).obj A
  apply ModuleCat.isZero_iff_subsingleton.2
  constructor
  intro x y
  suffices ∀ z : H1 D, z = 0 by exact (this x).trans (this y).symm
  intro z
  apply AddMonoid.addOrderOf_eq_one_iff.mp
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp hdiv
  letI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p G := Classical.choice inferInstance
  let J : Subgroup G := P
  let M' := res J.subtype M
  haveI : Module.Projective Z.{u} M'.V := Module.Projective.of_equiv' e.symm
  have hD : IsZero (H1 (res J.subtype D)) := by
    have hw : Finite (modSequence p M').X₃.V := mod_finite M' e
    refine primeGroupH1 P.isPGroup' (res J.subtype A) M' (hA J).1 (hA J).2 ?_
    intro B hB h₂
    exact (primeFiltrationH2 P.isPGroup' B hB h₂ _ (modSequence_torsion p M')).of_iso
      ((groupCohomology.functor Z.{u} J 2).mapIso (modHomIso p M' B hB)).symm
  exact P.not_dvd_index (hdiv.trans ((addOrderOf_dvd_iff_nsmul_eq_zero).2
    (index_annihilates D J 1 hD z)))

end FiniteGroup


section TorusPoints

open AlgebraicGeometry Opposite WithConv Coalgebra
open LinearAlgebraicGroups.Descent LinearAlgebraicGroups.Descent.NonabelianCohomology
open LinearAlgebraicGroups.DiagonalizableGroups
open LinearAlgebraicGroups.Specs.CharacterDescent
open scoped TensorProduct CategoryTheory.MonObj CategoryTheory.GrpObj

open private groupLikeSpanOfSplit groupAlgebraOfCharacters groupAlgebraOfCharacters_hom_single
  groupLikeIso splitBaseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  (A : HopfAlgebraCategory K)

private abbrev extendPoint (a : A →ₐ[K] L) : extendedHopf L A →ₐ[L] L :=
  Algebra.TensorProduct.liftEquivRight K L A L a

private theorem extendPoint_tmul (a : A →ₐ[K] L) (x : L) (y : A) :
    extendPoint A a (x ⊗ₜ[K] y) = x * a y :=
  Algebra.TensorProduct.lift_tmul (Algebra.ofId L L) a (fun _ _ => Commute.all _ _) x y

private noncomputable def extendConv : (convolutionPoints A).obj (CommAlgCat.of K L) ≃*
    (convolutionPoints (extendedHopf L A)).obj (CommAlgCat.of L L) where
  toFun f := toConv (extendPoint A f.ofConv)
  invFun f := toConv ((Algebra.TensorProduct.liftEquivRight K L A L).symm f.ofConv)
  left_inv f := WithConv.ofConv_injective ((Algebra.TensorProduct.liftEquivRight K L A L).left_inv _)
  right_inv f := WithConv.ofConv_injective ((Algebra.TensorProduct.liftEquivRight K L A L).right_inv _)
  map_mul' f g := by
    apply WithConv.ofConv_injective
    apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro a
    change extendPoint A (f * g).ofConv (1 ⊗ₜ[K] a) =
      (toConv (extendPoint A f.ofConv) * toConv (extendPoint A g.ofConv)) (1 ⊗ₜ[K] a)
    rw [extendPoint_tmul, one_mul]
    let f' : WithConv (A →ₐ[K] L) := f
    let g' : WithConv (A →ₐ[K] L) := g
    change (f' * g') a = _
    rw [AlgHom.convMul_apply, AlgHom.convMul_apply, TensorProduct.comul_tmul]
    generalize comul (R := K) a = t
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      simp [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, f', g']
    | add a b ha hb =>
      simp only [TensorProduct.tmul_add, map_add, ha, hb]

private noncomputable def convolutionIsoOfHopfIso {k : Type u} [Field k]
    {B C : HopfAlgebraCategory k} (e : B ≅ C) :
    (convolutionPoints C).obj (CommAlgCat.of k k) ≃*
      (convolutionPoints B).obj (CommAlgCat.of k k) where
  toFun f := toConv (f.ofConv.comp e.hom.hom.toAlgHom)
  invFun f := toConv (f.ofConv.comp e.inv.hom.toAlgHom)
  left_inv f := by
    apply WithConv.ofConv_injective
    ext x
    exact congrArg f.ofConv (congrArg (fun g : C ⟶ C => g.hom x) e.inv_hom_id)
  right_inv f := by
    apply WithConv.ofConv_injective
    ext x
    exact congrArg f.ofConv (congrArg (fun g : B ⟶ B => g.hom x) e.hom_inv_id)
  map_mul' f g := WithConv.ofConv_injective (AlgHom.convMul_comp_bialgHom_distrib f g e.hom.hom)

private noncomputable def pointCharacters (h : IsDiagonalizable (extendedHopf L A)) :
    NonabelianCohomology.Points K L (specGroup A).X ≃* (GeometricCharacters L A →* Lˣ) :=
  let j := groupAlgebraOfCharacters _ (groupLikeSpanOfSplit _ h)
  (((hopfSpecPointIso A).app (CommAlgCat.of K L)).groupIsoToMulEquiv.symm.trans
    (extendConv A)).trans ((convolutionIsoOfHopfIso j).trans
      (((convolutionCharacterIso _).app (CommAlgCat.of L L)).groupIsoToMulEquiv))

private theorem pointCharacters_apply (h : IsDiagonalizable (extendedHopf L A))
    (a : NonabelianCohomology.Points K L (specGroup A).X) (m : GeometricCharacters L A) :
    (pointCharacters A h a m).val =
      extendPoint A ((((hopfSpecPointIso A).app (CommAlgCat.of K L)).groupIsoToMulEquiv.symm a).ofConv)
        m.val := by
  change extendPoint A _
    ((groupAlgebraOfCharacters (extendedHopf L A) (groupLikeSpanOfSplit _ h)).hom.hom
      (MonoidAlgebra.single m 1)) = _
  rw [groupAlgebraOfCharacters_hom_single]
  rfl

private noncomputable def latticeRep : Rep Z.{u} Gal(L/K) where
  V := Additive (GeometricCharacters L A)
  ρ :=
    { toFun := fun σ => zModuleMap ((CharacterDescent.geometricAction L A σ).asHom.hom.toAdditive)
      map_one' := by
        apply LinearMap.ext
        intro x
        exact congrArg (fun f => Additive.ofMul (f.asHom x.toMul))
          (map_one (CharacterDescent.geometricAction L A))
      map_mul' := by
        intro σ τ
        apply LinearMap.ext
        intro x
        exact congrArg (fun f => Additive.ofMul (f.asHom x.toMul))
          (map_mul (CharacterDescent.geometricAction L A) σ τ) }


private theorem pointCharacters_action (h : IsDiagonalizable (extendedHopf L A))
    (g : Gal(L/K)) (a : NonabelianCohomology.Points K L (specGroup A).X) (m : GeometricCharacters L A) :
    pointCharacters A h (pointAction K L (specGroup A).X g a) m =
      Units.map g.toRingEquiv.toMonoidHom
        (pointCharacters A h a ((CharacterDescent.geometricAction L A g⁻¹).asHom m)) := by
  apply Units.ext
  rw [pointCharacters_apply]
  change _ = g ((pointCharacters A h a ((CharacterDescent.geometricAction L A g⁻¹).asHom m)).val)
  rw [pointCharacters_apply]
  let e := hopfSpecPointIso A
  let R := CommAlgCat.of K L
  let f : R ⟶ R := CommAlgCat.ofHom g.toAlgHom
  have he := e.inv.naturality_apply f a
  change e.inv.app R (pointAction K L (specGroup A).X g a) =
    toConv (g.toAlgHom.comp (e.inv.app R a).ofConv) at he
  change extendPoint A (e.inv.app R (pointAction K L (specGroup A).X g a)).ofConv m.val =
    g (extendPoint A (e.inv.app R a).ofConv
      ((SemilinearAction.scalarExtension (K := L) A).act g⁻¹ m.val))
  rw [he]
  generalize m.val = x
  induction x using TensorProduct.inductionOn with
  | tmul r b =>
    change extendPoint A (g.toAlgHom.comp (e.inv.app R a).ofConv) (r ⊗ₜ[K] b) =
      g (extendPoint A (e.inv.app R a).ofConv (g⁻¹ r ⊗ₜ[K] b))
    rw [extendPoint_tmul, extendPoint_tmul, map_mul, AlgHom.comp_apply]
    congr 1
    exact (g.apply_symm_apply r).symm
  | add a b ha hb => simp only [map_add, ha, hb]

private noncomputable def pointModuleIso (h : IsDiagonalizable (extendedHopf L A)) :
    NonabelianCohomology.Points K L (specGroup A).X ≃* Multiplicative ((Rep.ihom (latticeRep A)).obj (unitRep K L)) :=
  (pointCharacters A h).trans
    { toFun := fun f => Multiplicative.ofAdd (zModuleMap f.toAdditive)
      invFun := fun f => f.toAdd.toAddMonoidHom.toMultiplicative
      left_inv := fun f => MonoidHom.ext fun x => rfl
      right_inv := fun f => by
        apply Multiplicative.toAdd.injective
        apply LinearMap.ext
        intro x
        rfl
      map_mul' := fun f g => by
        apply Multiplicative.toAdd.injective
        apply LinearMap.ext
        intro x
        rfl }

private theorem pointModuleIso_action (h : IsDiagonalizable (extendedHopf L A))
    (g : Gal(L/K)) (a : NonabelianCohomology.Points K L (specGroup A).X) :
    (pointModuleIso A h (pointAction K L (specGroup A).X g a)).toAdd =
      ((Rep.ihom (latticeRep A)).obj (unitRep K L)).ρ g (pointModuleIso A h a).toAdd := by
  apply LinearMap.ext
  intro x
  exact congrArg Additive.ofMul (pointCharacters_action A h g a x.toMul)

private noncomputable def latticeBasis {r : ℕ}
    (e : GeometricCharacters L A ≃* StandardLattice.{u} r) :
    (latticeRep (L := L) A).V ≃ₗ[Z.{u}] (Fin r → Z.{u}) := by
  let t : Additive (StandardLattice.{u} r) ≃+ (Fin r → Z.{u}) :=
    { toFun := fun x i => ULift.up ((x.toMul i).down.toAdd)
      invFun := fun f => Additive.ofMul fun i => ULift.up (Multiplicative.ofAdd (f i).down)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  let a := e.toAdditive.trans t
  exact LinearEquiv.ofBijective (zModuleMap a.toAddMonoidHom) a.bijective

private theorem solveFinite
    {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (L : FiniteGaloisIntermediateField k S)
    (B : HopfAlgebraCategory k) (hT : IsTorus B)
    (hL : IsDiagonalizable (extendedHopf L B))
    (hA : ∀ J : Subgroup Gal(L/k), Limits.IsZero (H1 (Rep.res J.subtype (unitRep k L))) ∧
      Limits.IsZero (H2 (Rep.res J.subtype (unitRep k L))))
    (c : Gal(L/k) → NonabelianCohomology.Points k L (specGroup B).X)
    (hc : ∀ g h, c (g * h) = c g * pointAction _ _ _ g (c h)) :
    ∃ b : NonabelianCohomology.Points k L (specGroup B).X,
      ∀ g, c g = b⁻¹ * pointAction _ _ _ g b := by
  obtain ⟨r, ⟨basisS⟩⟩ := ((CharacterDescent.torusAndSplitCriteria B
    (CharacterDescent.torusIsMultiplicativeType B hT)).1.mp hT :
      ∃ r, Nonempty (GeometricCharacters S B ≃* StandardLattice.{u} r))
  let e := (MulEquiv.ofBijective (CharacterDescent.baseChangeCharacterMap S (extendedHopf L B))
      (CharacterDescent.baseChangeCharacterMap_bijective S _ hL)).trans
    ((groupLikeIso (CharacterDescent.extendedHopfTower S B)).trans basisS)
  let M := latticeRep (L := L) B
  let U := unitRep k L
  let D := (Rep.ihom M).obj U
  have hH : Limits.IsZero (H1 D) :=
    finiteGroupH1 U M (latticeBasis B e) hA
  let v := pointModuleIso B hL
  let a (g : Gal(L/k)) : D.V := (v (c g)).toAdd
  have ha : a ∈ cocycles₁ D := (mem_cocycles₁_iff a).2 fun g h => by
    change (v (c (g * h))).toAdd = D.ρ g (v (c h)).toAdd + (v (c g)).toAdd
    rw [hc, map_mul, ← pointModuleIso_action]
    exact add_comm _ _
  have hz : H1π D ⟨a, ha⟩ = 0 := (ModuleCat.isZero_iff_subsingleton.1 hH).elim _ _
  obtain ⟨b, hb⟩ := (H1π_eq_zero_iff ⟨a, ha⟩).1 hz
  refine ⟨v.symm (Multiplicative.ofAdd b), fun g => v.injective ?_⟩
  apply Multiplicative.toAdd.injective
  rw [map_mul, map_inv]
  change a g = -((v (v.symm (Multiplicative.ofAdd b))).toAdd) +
    (v (pointAction k L (specGroup B).X g (v.symm (Multiplicative.ofAdd b)))).toAdd
  rw [pointModuleIso_action, v.apply_symm_apply]
  exact (congrFun hb g).symm.trans (sub_eq_add_neg _ _ |>.trans (add_comm _ _))

private theorem torusH1OfScalar {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (B : HopfAlgebraCategory k) (hT : IsTorus B)
    (hA : ∀ (L : FiniteGaloisIntermediateField k S) (J : Subgroup Gal(L/k)),
      Limits.IsZero (H1 (Rep.res J.subtype (unitRep k L))) ∧
      Limits.IsZero (H2 (Rep.res J.subtype (unitRep k L))))
    (x : groupH1 k (specGroup B).X S) : x = groupBasepoint k (specGroup B).X S := by
  let T := specGroup B
  let : TopologicalSpace (NonabelianCohomology.Points k S T.X) := ⊥
  let : DiscreteTopology (NonabelianCohomology.Points k S T.X) := ⟨rfl⟩
  change x = basepoint (pointAction k S T.X)
  refine Quotient.inductionOn x fun a => ?_
  change NonabelianCohomology.classOf a = NonabelianCohomology.classOf (trivial _)
  obtain ⟨E, hfd, hgal, hE⟩ := (CharacterDescent.finiteGaloisSplitting B
    (CharacterDescent.torusIsMultiplicativeType B hT) :
      ∃ (E : IntermediateField k S) (_ : FiniteDimensional k E) (_ : IsGalois k E),
        IsDiagonalizable (extendedHopf E B))
  let L₀ : FiniteGaloisIntermediateField k S :=
    { toIntermediateField := E, finiteDimensional := hfd, isGalois := hgal }
  obtain ⟨L, c, hL, hc⟩ := finiteLevel L₀ a
  obtain ⟨e, _, hequiv⟩ := finitePointsIdentification (H := T.X) L
  have hlaw (σ τ : Gal(L/k)) :
      e.symm (c (σ * τ)) = e.symm (c σ) * pointAction k L T.X σ (e.symm (c τ)) := by
    apply e.injective
    rw [e.apply_symm_apply, map_mul, e.apply_symm_apply, hequiv, e.apply_symm_apply]
    exact c.property.2 σ τ
  let f : E →ₐ[k] L :=
    IntermediateField.inclusion ((FiniteGaloisIntermediateField.le_iff L₀ L).mp hL)
  let : Algebra E L := f.toAlgebra
  let : IsScalarTower k E L := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  obtain ⟨M, ⟨j⟩⟩ := splitBaseChange (K := L) _ hE
  have hs : IsDiagonalizable (extendedHopf L B) :=
    ⟨M, ⟨j ≪≫ CharacterDescent.extendedHopfTower L B⟩⟩
  obtain ⟨b, hb⟩ := solveFinite L B hT hs (hA L) (fun σ => e.symm (c σ)) hlaw
  apply classOf_eq_iff.mpr
  refine ⟨(e b).val⁻¹, fun σ => ?_⟩
  have h := congrArg Subtype.val (congrArg e (hb (restriction L σ)))
  rw [e.apply_symm_apply, map_mul, map_inv, hequiv] at h
  change (c (restriction L σ)).val = (e b).val⁻¹ *
    (levelAction (pointAction k S T.X) L (restriction L σ) (e b)).val at h
  rw [quotientAction_apply, hc σ] at h
  change (1 : NonabelianCohomology.Points k S T.X) = ((e b).val⁻¹)⁻¹ * a σ *
    pointAction k S T.X σ (e b).val⁻¹
  rw [h, map_inv]
  simp

end TorusPoints

/-- Every torus over the maximal unramified extension of a nonarchimedean local
field has trivial first Galois cohomology. -/
theorem torus_vanishing : TorusVanishing.{u} := by
  intro F _ _ _ _ K S _ _ _ A hT x
  refine torusH1OfScalar (k := K) (S := S) A hT ?_ x
  intro L J
  let : Algebra K L := L.toIntermediateField.toSubalgebra.algebra
  exact ⟨scalarCohomology F (K := K) L J 1 (Or.inl rfl),
    scalarCohomology F (K := K) L J 2 (Or.inr rfl)⟩

section Torsors

open AlgebraicGeometry Opposite WithConv
open Specs.Fppf Specs.StandardGroups Specs.CharacterDescent

/-- The unit coordinates of the split torus lift across square-zero ideals. -/
private theorem smoothSplitTorus (k J : Type u) [Field k] [Fintype J] :
    Smooth (multiplicativePowerGroup k J).val.X.hom := by
  classical
  let A := LaurentPowerCoordinates k J
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (algebraMap k A).Smooth
  rw [RingHom.smooth_algebraMap]
  have hfinite : Algebra.FinitePresentation k A :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  refine ⟨Algebra.FormallySmooth.iff_comp_surjective.mpr ?_, hfinite⟩
  intro R _ _ I hI f
  obtain ⟨e, _, c, _⟩ := (StandardGroups.multiplicativePowerSpecification k J).2.2.2
  let α := e ≪≫ c
  let q := Ideal.Quotient.mkₐ k I
  let a : J → (R ⧸ I)ˣ :=
    (α.app (CommAlgCat.of k (R ⧸ I))).hom (toConv f)
  have hLift (i : J) : ∃ b : Rˣ, Units.map q.toMonoidHom b = a i := by
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (a i).val
    have hu : IsUnit x :=
      (IsNilpotent.isUnit_quotient_mk_iff ⟨2, hI⟩).mp (hx.symm ▸ (a i).isUnit)
    refine ⟨hu.unit, Units.ext ?_⟩
    change Ideal.Quotient.mk I hu.unit.val = (a i).val
    rwa [hu.unit_spec]
  choose b hb using hLift
  let φ := (α.app (CommAlgCat.of k R)).groupIsoToMulEquiv
  let ψ := (α.app (CommAlgCat.of k (R ⧸ I))).groupIsoToMulEquiv
  let g : A →ₐ[k] R := (φ.symm b).ofConv
  refine ⟨g, WithConv.toConv_injective (ψ.injective ?_)⟩
  have h := α.hom.naturality_apply (CommAlgCat.ofHom q) (toConv g)
  change ψ (toConv (q.comp g)) = fun i => Units.map q.toMonoidHom (φ (toConv g) i) at h
  rw [h, show φ (toConv g) = b from φ.apply_symm_apply b]
  exact funext hb

private theorem torus_smooth {k : Type u} [Field k] (A : HopfAlgebraCategory k)
    (hT : IsTorus A) : Smooth (specGroup A).X.hom := by
  obtain ⟨E, _, _, _, r, ⟨i⟩⟩ := (CharacterDescent.torusOnSchemes A).mp hT
  apply MorphismProperty.of_pullback_snd_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (g := fieldSpecMap k E)
  · exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  · change Smooth ((groupBaseChange k E).obj (specGroup A)).X.hom
    rw [← i.hom.hom.hom.w]
    have : IsIso i.hom.hom.hom.left :=
      ((Grp.forget (SchemeOver E) ⋙ Over.forget _).mapIso i).isIso_hom
    have := smoothSplitTorus E (ULift.{u} (Fin r))
    infer_instance

/-- Every right fppf torsor under a torus over the maximal unramified
extension has a rational point. -/
theorem torus_torsors_have_points : TorusTorsorsHavePoints.{u} := by
  intro F _ _ _ _ K A hT P
  let hA := (CharacterDescent.multiplicativeTypeProperties A
    (CharacterDescent.torusIsMultiplicativeType A hT)).1
  let H : Specs.AffineAlgebraicGroup K := (finiteTypeHopfSpec K).obj (op ⟨A, hA⟩)
  let S : IntermediateField K (AlgebraicClosure K) := separableClosure K (AlgebraicClosure K)
  let : Algebra K S := S.toSubalgebra.algebra
  let : IsSepClosure K S := separableClosure.isSepClosure K (AlgebraicClosure K)
  obtain ⟨e, _, he⟩ := LinearAlgebraicGroups.Descent.SmoothTorsors.classification
    (S := S) H (torus_smooth A hT)
  exact (he P).1.mp (torus_vanishing F S A hT (e (Quotient.mk _ P)))

end Torsors

end LinearAlgebraicGroups.Arithmetic.MaximalUnramifiedTorusTorsors
