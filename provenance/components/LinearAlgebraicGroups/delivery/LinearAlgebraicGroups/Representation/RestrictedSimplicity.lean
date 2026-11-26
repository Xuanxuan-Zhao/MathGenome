import Specs.LinearAlgebraicGroups.Representation.RestrictedSimplicity
import LinearAlgebraicGroups.Representation.RestrictedCyclicity
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.SimpleModule.Basic
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory WithConv
open scoped TensorProduct CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Representation.RestrictedSimplicity

noncomputable section

open _root_.LinearAlgebraicGroups.Specs

section Endomorphisms

variable {k V H X : Type*} [Field k] [AddCommGroup V] [Module k V]
  [Monoid H] [CommGroup X]

private def HasWeight (a : H → V ≃ₗ[k] V) (c : X →* (H →* k)) (mu : X) (w : V) :
    Prop := ∀ t, a t w = c mu t • w

/-- Every weight component of a vector in an invariant subspace belongs to
that subspace. Here it suffices that the characters be distinct on points. -/
private theorem weight_components_mem
    (a : H → V ≃ₗ[k] V) (c : X →* (H →* k)) (hc : Function.Injective c)
    (W : Submodule k V) (hW : ∀ t z, z ∈ W → a t z ∈ W)
    (s : Finset X) (w : X → V) (hw : ∀ mu ∈ s, HasWeight a c mu (w mu))
    (hs : ∑ mu ∈ s, w mu ∈ W) (mu : X) (hmu : mu ∈ s) : w mu ∈ W := by
  classical
  by_contra hn
  obtain ⟨ℓ, hne, hℓ⟩ := Submodule.exists_le_ker_of_notMem hn
  have hzero (t : H) : (∑ i ∈ s, ℓ (w i) • (c i : H → k)) t = 0 := by
    have he := hℓ (hW t _ hs)
    change ℓ (a t (∑ i ∈ s, w i)) = 0 at he
    rw [map_sum, map_sum] at he
    rw [Finset.sum_apply]
    refine (Finset.sum_congr rfl (fun i hi ↦ ?_)).trans he
    simp only [Pi.smul_apply, hw i hi t, map_smul, smul_eq_mul, mul_comm]
  have hli : LinearIndependent k (fun i : X ↦ (c i : H → k)) :=
    (linearIndependent_monoidHom H k).comp c hc
  exact hne (linearIndependent_iff'.mp hli s (fun i ↦ ℓ (w i)) (funext hzero) mu hmu)

/-- An endomorphism algebra with inner inverses is scalar when it is
normalized by a diagonal action and evaluation at the highest vector is
injective. The highest vector must span the unique weight space of greatest
height. -/
private theorem scalar_of_highest [DecidableEq X]
    (a : H → V ≃ₗ[k] V) (c : X →* (H →* k)) (hc : Function.Injective c)
    (height : Additive X →+ ℝ) (χ : X) (v : V)
    (E : Subalgebra k (Module.End k V))
    (hnorm : ∀ t (f : Module.End k V), f ∈ E →
      (a t).toLinearMap ∘ₗ f ∘ₗ (a t).symm.toLinearMap ∈ E)
    (hinj : ∀ f g : E, f.val v = g.val v → f = g)
    (hreg : ∀ f : E, ∃ g : E, (f.val * g.val * f.val : Module.End k V) = f.val)
    (hv : HasWeight a c χ v)
    (hline : ∀ z, HasWeight a c χ z → ∃ b : k, z = b • v)
    (hbound : ∀ mu z, HasWeight a c mu z → z ≠ 0 → mu ≠ χ →
      height (Additive.ofMul mu) < height (Additive.ofMul χ))
    (hdecomp : ∀ z : V, ∃ (s : Finset X) (w : X → V),
      (∑ mu ∈ s, w mu) = z ∧ ∀ mu ∈ s, HasWeight a c mu (w mu))
    (projection : X → V →ₗ[k] V)
    (hprojection : ∀ α mu z, HasWeight a c mu z →
      projection α z = if mu = α then z else 0) :
    ∀ f : E, ∃ b : k, f.val = b • (1 : Module.End k V) := by
  classical
  have c_ne (mu : X) (t : H) : c mu t ≠ 0 := by
    have h : c mu t * c mu⁻¹ t = 1 := by
      rw [← MonoidHom.mul_apply, ← map_mul, mul_inv_cancel, map_one, MonoidHom.one_apply]
    intro hh
    rw [hh, zero_mul] at h
    exact zero_ne_one h
  let ev : E →ₗ[k] V := (LinearMap.applyₗ (R := k) v).comp E.val.toLinearMap
  have ev_apply (f : E) : ev f = f.val v := rfl
  let conjugate (t : H) (f : E) : E :=
    ⟨(a t).toLinearMap ∘ₗ f.val ∘ₗ (a t).symm.toLinearMap, hnorm t f.val f.property⟩
  have conjugate_eval (t : H) (f : E) :
      ev (conjugate t f) = (c χ t)⁻¹ • a t (ev f) := by
    have h : (a t).symm v = (c χ t)⁻¹ • v := by
      apply (a t).injective
      rw [LinearEquiv.apply_symm_apply, map_smul, hv t, smul_smul,
        inv_mul_cancel₀ (c_ne χ t), one_smul]
    change a t (f.val ((a t).symm v)) = _
    rw [h, map_smul, map_smul, ev_apply]
  have hstable : ∀ t z, z ∈ LinearMap.range ev → a t z ∈ LinearMap.range ev := by
    rintro t _ ⟨f, rfl⟩
    refine ⟨c χ t • conjugate t f, ?_⟩
    rw [map_smul, conjugate_eval, smul_smul, mul_inv_cancel₀ (c_ne χ t), one_smul]
  have end_decomp (f : E) : ∃ (s : Finset X) (b : X → E),
      (∑ mu ∈ s, b mu) = f ∧ ∀ mu ∈ s, HasWeight a c mu (ev (b mu)) := by
    obtain ⟨s, w, he, hw⟩ := hdecomp (ev f)
    have hm (mu : X) (hmu : mu ∈ s) : w mu ∈ LinearMap.range ev :=
      weight_components_mem a c hc _ hstable s w hw
        (he.symm ▸ LinearMap.mem_range_self ev f) mu hmu
    let b (mu : X) : E := if h : mu ∈ s then (hm mu h).choose else 0
    have hb (mu) (hmu : mu ∈ s) : ev (b mu) = w mu := by
      change ev (if h : mu ∈ s then (hm mu h).choose else 0) = w mu
      rw [dite_eq_left hmu]
      exact (hm mu hmu).choose_spec
    refine ⟨s, b, hinj _ _ ?_, fun mu hmu ↦ (hb mu hmu).symm ▸ hw mu hmu⟩
    change ev (∑ mu ∈ s, b mu) = ev f
    rw [map_sum, ← he]
    exact Finset.sum_congr rfl hb
  have shift (f : E) {mu ν : X} (hf : HasWeight a c mu (ev f))
      {z : V} (hz : HasWeight a c ν z) :
      HasWeight a c (mu * χ⁻¹ * ν) (f.val z) := by
    intro t
    have hc' : c χ⁻¹ t = (c χ t)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← MonoidHom.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        MonoidHom.one_apply]
    have hcon : conjugate t f = (c (mu * χ⁻¹) t) • f := by
      apply hinj
      change ev (conjugate t f) = ev (c (mu * χ⁻¹) t • f)
      rw [conjugate_eval, hf t, map_smul, smul_smul, map_mul, MonoidHom.mul_apply, hc',
        mul_comm]
    have he := congrArg (fun e : E ↦ e.val (a t z)) hcon
    change a t (f.val ((a t).symm (a t z))) =
      c (mu * χ⁻¹) t • f.val (a t z) at he
    rw [LinearEquiv.symm_apply_apply, hz t, map_smul, smul_smul] at he
    rw [map_mul, MonoidHom.mul_apply]
    exact he
  have hheight (mu) (g : E) (hg : HasWeight a c mu (ev g)) (hne : g ≠ 0) :
      height (Additive.ofMul mu) ≤ height (Additive.ofMul χ) := by
    by_cases he : mu = χ
    · exact he ▸ le_rfl
    · apply (hbound mu _ hg _ he).le
      intro hz
      exact hne (hinj _ 0 hz)
  -- A nonzero homogeneous endomorphism cannot lower height. If it did,
  -- every homogeneous term of its inner inverse would have to lower or
  -- preserve height, so the component of f * g * f in the degree of f would vanish.
  have elim_lower (f : E) (mu : X) (hf : HasWeight a c mu (ev f)) (hne : mu ≠ χ) :
      f = 0 := by
    by_contra h0
    have fv0 : ev f ≠ 0 := fun h ↦ h0 (hinj _ 0 h)
    have hl := hbound mu _ hf fv0 hne
    obtain ⟨g, hg⟩ := hreg f
    obtain ⟨s, d, hd, hdw⟩ := end_decomp g
    have hp (i) (hi : i ∈ s) : projection mu (f.val ((d i).val (ev f))) = 0 := by
      by_cases hz : d i = 0
      · simp [hz]
      have hw := shift f hf (shift (d i) (hdw i hi) hf)
      rw [hprojection _ _ _ hw, ite_eq_right]
      intro h
      have he := congrArg (fun x : X ↦ height (Additive.ofMul x)) h
      change height ((Additive.ofMul mu + -Additive.ofMul χ) +
        ((Additive.ofMul i + -Additive.ofMul χ) + Additive.ofMul mu)) =
        height (Additive.ofMul mu) at he
      simp only [map_add, map_neg] at he
      have hb := hheight i (d i) (hdw i hi) hz
      linarith
    have hg' : f.val (g.val (ev f)) = ev f := LinearMap.congr_fun hg v
    apply fv0
    have he := congrArg (projection mu) hg'
    rw [hprojection _ _ _ hf, ite_eq_left rfl] at he
    rw [← he, ← hd]
    change projection mu (f.val (E.val (∑ i ∈ s, d i) (ev f))) = 0
    rw [map_sum, LinearMap.sum_apply, map_sum, map_sum]
    exact Finset.sum_eq_zero hp
  intro f
  obtain ⟨s, d, hd, hdw⟩ := end_decomp f
  by_cases hχ : χ ∈ s
  · obtain ⟨b, hb⟩ := hline _ (hdw χ hχ)
    refine ⟨b, ?_⟩
    have he : d χ = b • (1 : E) := by
      apply hinj
      exact hb
    have hs : ∑ i ∈ s, d i = d χ := Finset.sum_eq_single_of_mem χ hχ
      (fun i hi hn ↦ elim_lower _ _ (hdw i hi) hn)
    rw [← hd, hs, he]
    rfl
  · refine ⟨0, ?_⟩
    rw [← hd, Finset.sum_eq_zero (fun i hi ↦ elim_lower _ _ (hdw i hi)
      (fun he ↦ hχ (he ▸ hi)))]
    simp

end Endomorphisms

section Modules

variable {k D V : Type*} [Field k] [Ring D] [Algebra k D]
  [AddCommGroup V] [Module k V] [Module D V] [IsScalarTower k D V]

private def endomorphismAlgebra : Subalgebra k (Module.End k V) where
  carrier := {f | ∀ (d : D) (x : V), f (d • x) = d • f x}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg d x
    change f (d • x) + g (d • x) = d • (f x + g x)
    rw [hf d x, hg d x, smul_add]
  one_mem' := fun _ _ ↦ rfl
  mul_mem' := by
    intro f g hf hg d x
    change f (g (d • x)) = d • f (g x)
    rw [hg d x, hf d (g x)]
  algebraMap_mem' r := by
    intro d x
    change r • (d • x) = d • (r • x)
    rw [← smul_assoc, Algebra.smul_def, Algebra.commutes,
      mul_smul, algebraMap_smul]

private def transportSubmodule (e : V ≃ₗ[k] V)
    (he : ∀ d : D, ∃ d' : D, ∀ x : V, e.symm (d • x) = d' • e.symm x)
    (W : Submodule D V) : Submodule D V where
  __ := (W.restrictScalars k).comap e.symm.toLinearMap
  smul_mem' d x hx := by
    obtain ⟨d', hd⟩ := he d
    change e.symm (d • x) ∈ W
    rw [hd]
    exact W.smul_mem d' hx

private def normalizerOrderIso (e : V ≃ₗ[k] V)
    (he : ∀ d : D, ∃ d' : D, ∀ x : V, e (d • x) = d' • e x)
    (hi : ∀ d : D, ∃ d' : D, ∀ x : V, e.symm (d • x) = d' • e.symm x) :
    Submodule D V ≃o Submodule D V where
  toFun := transportSubmodule e hi
  invFun := transportSubmodule e.symm he
  left_inv W := by
    ext x
    change e.symm (e x) ∈ W ↔ x ∈ W
    rw [LinearEquiv.symm_apply_apply]
  right_inv W := by
    ext x
    change e (e.symm x) ∈ W ↔ x ∈ W
    rw [LinearEquiv.apply_symm_apply]
  map_rel_iff' {W Z} := by
    change (∀ x, e.symm x ∈ W → e.symm x ∈ Z) ↔ W ≤ Z
    exact ⟨fun h x hx ↦ by simpa using h (e x) (by simpa using hx), fun h _ hx ↦ h hx⟩

private theorem endomorphismAlgebra_normalized (e : V ≃ₗ[k] V)
    (he : ∀ d : D, ∃ d' : D, ∀ x : V, e (d • x) = d' • e x)
    (hi : ∀ d : D, ∃ d' : D, ∀ x : V, e.symm (d • x) = d' • e.symm x)
    (f : Module.End k V) (hf : f ∈ endomorphismAlgebra (D := D) (k := k) (V := V)) :
    e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap ∈
      endomorphismAlgebra (D := D) (k := k) (V := V) := by
  intro d x
  obtain ⟨d', hd⟩ := hi d
  obtain ⟨d'', hd'⟩ := he d'
  have h : ∀ y : V, d'' • y = d • y := by
    intro y
    calc
      d'' • y = e (d' • e.symm y) := by rw [hd', e.apply_symm_apply]
      _ = d • y := by rw [← hd, e.apply_symm_apply]
  change e (f (e.symm (d • x))) = d • e (f (e.symm x))
  rw [hd, hf d', hd', h]

/-- The distribution socle is invariant under every normalizer and therefore
fills an irreducible representation of the normalizing group. -/
private theorem semisimple_of_normalizers {H : Type*} (a : H → V ≃ₗ[k] V)
    (ha : ∀ t (d : D), ∃ d' : D, ∀ x : V, a t (d • x) = d' • a t x)
    (hi : ∀ t (d : D), ∃ d' : D, ∀ x : V, (a t).symm (d • x) = d' • (a t).symm x)
    [Nontrivial V] [IsArtinian D V]
    (hirr : ∀ W : Submodule k V, (∀ t, ∀ x ∈ W, a t x ∈ W) → W = ⊥ ∨ W = ⊤) :
    IsSemisimpleModule D V := by
  let W : Submodule D V := sSup {N | IsSimpleModule D N}
  have hW : W ≠ ⊥ := by
    obtain ⟨N, hN⟩ := IsAtomic.exists_atom (Submodule D V)
    have hle : N ≤ W := le_sSup (isSimpleModule_iff_isAtom.mpr hN)
    exact fun h ↦ hN.ne_bot (le_bot_iff.mp (h ▸ hle))
  have hstable : ∀ t, ∀ x ∈ W.restrictScalars k, a t x ∈ W.restrictScalars k := by
    intro t x hx
    let e := normalizerOrderIso (D := D) (a t) (ha t) (hi t)
    have he : e W ≤ W := by
      rw [show W = _ from rfl, map_sSup]
      apply sSup_le
      rintro _ ⟨N, hN, rfl⟩
      exact le_sSup (isSimpleModule_iff_isAtom.mpr
        ((e.isAtom_iff N).mpr (isSimpleModule_iff_isAtom.mp hN)))
    apply he
    change (a t).symm (a t x) ∈ W
    simpa using hx
  apply IsSemisimpleModule.of_sSup_simples_eq_top
  rcases hirr (W.restrictScalars k) hstable with hb | ht
  · exact False.elim (hW ((Submodule.restrictScalars_eq_bot_iff k D V).mp hb))
  · exact (Submodule.restrictScalars_eq_top_iff k D V).mp ht

private def liftEndomorphism
    (f : endomorphismAlgebra (D := D) (k := k) (V := V)) : Module.End D V :=
  { (f.val : V →ₗ[k] V).toAddHom with
    map_smul' := f.property }

private theorem endomorphismAlgebra_regular [IsSemisimpleModule D V]
    (f : endomorphismAlgebra (D := D) (k := k) (V := V)) :
    ∃ g : endomorphismAlgebra (D := D) (k := k) (V := V),
      (f.val * g.val * f.val : Module.End k V) = f.val := by
  let F := liftEndomorphism f
  obtain ⟨s, hs⟩ := IsSemisimpleModule.lifting_property F.rangeRestrict
    F.surjective_rangeRestrict LinearMap.id
  obtain ⟨g, hg⟩ := IsSemisimpleModule.extension_property (LinearMap.range F).subtype
    (Submodule.subtype_injective _) s
  refine ⟨⟨g.restrictScalars k, g.map_smul⟩, LinearMap.ext fun x ↦ ?_⟩
  change F (g (F x)) = F x
  have e := LinearMap.congr_fun hg (F.rangeRestrict x)
  change g (F x) = s (F.rangeRestrict x) at e
  rw [e]
  exact congrArg Subtype.val (LinearMap.congr_fun hs (F.rangeRestrict x))

private theorem simple_of_scalar_endomorphisms [IsSemisimpleModule D V] [Nontrivial V]
    (h : ∀ f : endomorphismAlgebra (D := D) (k := k) (V := V),
      ∃ b : k, f.val = b • (1 : Module.End k V)) : IsSimpleModule D V := by
  refine (isSimpleModule_iff D V).mpr (IsSimpleOrder.mk fun W ↦ ?_)
  by_cases hW : W = ⊥
  · exact Or.inl hW
  obtain ⟨W', hW'⟩ := exists_isCompl W
  let f := W.projection W' hW'
  obtain ⟨b, hb⟩ := h ⟨f.restrictScalars k, f.map_smul⟩
  obtain ⟨x, hx, hx0⟩ := W.ne_bot_iff.mp hW
  have hfix (y : V) : f y = b • y := LinearMap.congr_fun hb y
  have h1 : b = 1 := by
    have he := hfix x
    rw [show f x = x from W.projection_apply_of_mem_left hW' hx] at he
    have hz : (b - 1) • x = 0 := by rw [sub_smul, one_smul, ← he, sub_self]
    have hn := (smul_eq_zero.mp hz).resolve_right hx0
    exact sub_eq_zero.mp hn
  refine Or.inr (top_unique (fun y _ ↦ ?_))
  have hy := hfix y
  rw [h1, one_smul] at hy
  exact hy ▸ (W.projectionOnto W' hW' y).property

end Modules

open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Character StandardLattice)
open Specs.CharacterPairing (characterValue)
open Specs.RootWeightAction (Representation act extendVector weightSpace mem_weightSpace
  DominanceLE SimpleRoot)
open Specs.FlagLineBundle (OppositeBorelPair)
open Specs.SimpleClassification (SocleModel)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open FiniteDistributions

open private pointDistribution pointDistribution_mul conjugate_distribution basis_act_point
  stable_of_rational_points pair_lTensor
  from LinearAlgebraicGroups.Representation.RestrictedCyclicity
open private affinePoint affinePointEquiv
  from LinearAlgebraicGroups.Representation.FlagLineBundle
open private pointIso from LinearAlgebraicGroups.Representation.InducedSocle
open private generates_of_simple from LinearAlgebraicGroups.Representation.PrimitiveLine
open private characterUnitOnPoints characterEvaluation characterValue_eq_unit characterUnit characterUnit_point
  from LinearAlgebraicGroups.RootData.RootGroups
open private act_extend_natural characterValue_natural torusPoint_weights charactersOfIso
  from LinearAlgebraicGroups.Representation.RootWeightAction
open private coordinateReduced eq_zero_of_algHom_eq_zero
  from LinearAlgebraicGroups.Affine.RationalRepresentations
open private weightProjection sum_projections projection_mem
  from LinearAlgebraicGroups.Multiplicative.WeightDecomposition
open private splitTorusSmooth from LinearAlgebraicGroups.Reductive.WeylScheme
open private weightProjection dominanceLE_iff positiveCone
  from LinearAlgebraicGroups.Representation.CyclicHighestWeight

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {k : Type u} [Field k]
variable {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
variable {U : ClosedSubgroup P.positive.group} {χ : Character P.torus.group}

local notation "K" => CommAlgCat.of k k

private def pointCoordinates {H : GroupScheme k} {A : HopfAlgebraCategory k}
    (e : specGroup A ≅ H) (R : TestAlgebra k) : (A →ₐ[k] R) ≃ GroupPoints H R :=
  (affinePointEquiv A R).trans
    (((CategoryTheory.forget GrpCat).mapIso (((groupPointsFunctor k).mapIso e).app R)).toEquiv)

private theorem pointCoordinates_apply {H : GroupScheme k} {A : HopfAlgebraCategory k}
    (e : specGroup A ≅ H) (R : TestAlgebra k) (b : A →ₐ[k] R) :
    pointCoordinates e R b = affinePoint R b ≫ e.hom.hom.hom := rfl

private theorem map_universalPoint {H : GroupScheme k} {A : HopfAlgebraCategory k}
    (e : specGroup A ≅ H) (R : TestAlgebra k) (b : A →ₐ[k] R) :
    mapPoints (CommAlgCat.ofHom b) e.hom.hom.hom = pointCoordinates e R b := rfl

private def rationalAction {A : HopfAlgebraCategory k} {V : Type u}
    [AddCommGroup V] [Module k V] (δ : RightComodule k A V) :
    letI := convolutionGroup A K
    WithConv (A →ₐ[k] k) → V ≃ₗ[k] V := by
  letI := convolutionGroup A K
  intro g
  refine
    { toFun := toAction δ (pointDistribution g)
      invFun := toAction δ (pointDistribution g⁻¹)
      map_add' := map_add _
      map_smul' := map_smul _
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    change (toAction δ (pointDistribution g⁻¹) * toAction δ (pointDistribution g)) x = x
    rw [← map_mul, ← pointDistribution_mul, inv_mul_cancel]
    change toAction δ 1 x = x
    rw [map_one]
    rfl
  · intro x
    change (toAction δ (pointDistribution g) * toAction δ (pointDistribution g⁻¹)) x = x
    rw [← map_mul, ← pointDistribution_mul, mul_inv_cancel]
    change toAction δ 1 x = x
    rw [map_one]
    rfl

private theorem rationalAction_normalizes (S : SocleModel P U χ)
    {Q : HopfAlgebraCategory k} (q : S.A ⟶ Q)
    (hn : Specs.IsNormalSubgroup (specGroupMap q)) :
    letI := convolutionGroup S.A K
    let m := (toAction S.socleCoaction).comp (distributionMap q.hom.toCoalgHom)
    ∀ (g : WithConv (S.A →ₐ[k] k)) (d : Dist k Q),
      ∃ d' : Dist k Q, ∀ x : S.socle,
        rationalAction S.socleCoaction g (m d x) =
          m d' (rationalAction S.socleCoaction g x) := by
  letI := convolutionGroup S.A K
  intro m g d
  let a := toAction S.socleCoaction
  let j := distributionMap q.hom.toCoalgHom
  obtain ⟨d', hd⟩ := conjugate_distribution q hn g d
  have he : pointDistribution g * j d = j d' * pointDistribution g := by
    rw [← hd, mul_assoc (pointDistribution g * j d), ← pointDistribution_mul,
      inv_mul_cancel, show pointDistribution (1 : WithConv (S.A →ₐ[k] k)) = 1 from rfl,
      mul_one]
  refine ⟨d', fun x ↦ ?_⟩
  change (a (pointDistribution g) * a (j d)) x = (a (j d') * a (pointDistribution g)) x
  rw [← map_mul, ← map_mul, he]

private theorem rationalAction_irreducible [IsAlgClosed k] (S : SocleModel P U χ)
    (W : Submodule k S.socle)
    (hW : ∀ g : WithConv (S.A →ₐ[k] k), ∀ x ∈ W,
      rationalAction S.socleCoaction g x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  let e := S.socleBasis.equivFun
  have hStable := stable_of_rational_points S W
    (fun g w hw ↦ by
      obtain ⟨b, rfl⟩ := (pointCoordinates S.groupIso K).surjective g
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hw
      rw [pointCoordinates_apply]
      have hact := basis_act_point S (toConv b) x
      have hm := Submodule.mem_map_of_mem (f := S.socleBasis.equivFun.toLinearMap)
        (hW (toConv b) x hx)
      simpa only [WithConv.ofConv_toConv] using hact.symm ▸ hm)
  rcases S.simple.2 _ hStable with hbot | htop
  · left
    apply (Submodule.map_injective_of_injective e.injective)
    simpa only [Submodule.map_bot] using hbot
  · right
    apply (Submodule.map_injective_of_injective e.injective)
    simpa only [Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective] using htop

private theorem algHom_points_ext [IsAlgClosed k] {A : HopfAlgebraCategory k}
    [Algebra.FiniteType k A] [_root_.IsReduced A] {v w : A}
    (h : ∀ f : A →ₐ[k] k, f v = f w) : v = w :=
  sub_eq_zero.mp (eq_zero_of_algHom_eq_zero (F := k) (B := A) (v - w) fun f ↦ by rw [map_sub, h f, sub_self])

private def pointCharacters (T : GroupScheme k) :
    Character T →* (GroupPoints T K →* k) where
  toFun χ := (Units.coeHom k).comp (characterUnitOnPoints χ K)
  map_one' := by
    ext t
    exact congrArg Units.val ((characterEvaluation K t).map_one)
  map_mul' χ ψ := by
    ext t
    exact congrArg Units.val ((characterEvaluation K t).map_mul χ ψ)

private theorem pointCharacters_apply (T : GroupScheme k) (mu : Character T)
    (t : GroupPoints T K) :
    pointCharacters T mu t = characterValue mu K t :=
  (characterValue_eq_unit mu K t).symm

private theorem pointCharacters_injective [IsAlgClosed k]
    {T : GroupScheme k} {A : HopfAlgebraCategory k} (e : specGroup A ≅ T)
    [Algebra.FiniteType k A] [_root_.IsReduced A] :
    Function.Injective (pointCharacters T) := by
  intro mu ν h
  let R := CommAlgCat.of k A
  let t : GroupPoints T R := e.hom.hom.hom
  have he : characterValue mu R t = characterValue ν R t := by
    apply algHom_points_ext
    intro b
    have hb := DFunLike.congr_fun h (pointCoordinates e K b)
    rw [pointCharacters_apply, pointCharacters_apply, ← map_universalPoint,
      characterValue_natural, characterValue_natural] at hb
    exact hb
  apply (cancel_epi e.hom).mp
  apply (Grp.forget (SchemeOver k)).map_injective
  change t ≫ mu.hom.hom = t ≫ ν.hom.hom
  rw [← characterUnit_point mu, ← characterUnit_point ν]
  congr 1
  exact Units.ext (by rwa [characterValue_eq_unit, characterValue_eq_unit] at he)

private theorem rational_weight_iff [IsAlgClosed k] {I : Type u} [Fintype I] [DecidableEq I]
    (ρ : Representation G.val I) (T : ClosedSubgroup G.val)
    {A : HopfAlgebraCategory k} (e : specGroup A ≅ T.group)
    [Algebra.FiniteType k A] [_root_.IsReduced A] (mu : Character T.group) (w : I → k) :
    (∀ t : GroupPoints T.group K,
      act ρ K (t ≫ T.inclusion.hom.hom) w = characterValue mu K t • w) ↔
      w ∈ weightSpace ρ T mu := by
  refine ⟨?_, fun h t ↦ mem_weightSpace.mp h K t⟩
  intro h
  let R := CommAlgCat.of k A
  let z : GroupPoints T.group R := e.hom.hom.hom
  have compare {B : TestAlgebra k} (b : A →ₐ[k] B) (i : I) :
      (act ρ B (pointCoordinates e B b ≫ T.inclusion.hom.hom) (extendVector B w)) i =
        b (act ρ R (z ≫ T.inclusion.hom.hom) (extendVector R w) i) := by
    rw [← map_universalPoint]
    exact congrFun (act_extend_natural ρ (CommAlgCat.ofHom b) (z ≫ T.inclusion.hom.hom) w) i
  have compareScalar {B : TestAlgebra k} (b : A →ₐ[k] B) (i : I) :
      (characterValue mu B (pointCoordinates e B b) • extendVector B w) i =
        b ((characterValue mu R z • extendVector R w) i) := by
    rw [← map_universalPoint, characterValue_natural]
    change b (characterValue mu R z) * algebraMap k B (w i) =
      b (characterValue mu R z * algebraMap k A (w i))
    rw [map_mul, b.commutes]
  have hz : act ρ R (z ≫ T.inclusion.hom.hom) (extendVector R w) =
      characterValue mu R z • extendVector R w := by
    funext i
    apply algHom_points_ext
    intro b
    rw [← compare (B := K) b i, ← compareScalar (B := K) b i]
    exact congrFun (h (pointCoordinates e K b)) i
  apply mem_weightSpace.mpr
  intro B t
  obtain ⟨b, rfl⟩ := (pointCoordinates e B).surjective t
  funext i
  rw [compare (B := B) b i, compareScalar (B := B) b i, hz]

private theorem split_weight_sum {I : Type u} [Fintype I] [DecidableEq I]
    (ρ : Representation G.val I) (T : ClosedSubgroup G.val)
    (hT : Specs.GeometricRadicals.IsSplitTorus T.group) (x : I → k) :
    ∃ (s : Finset (Character T.group)) (w : Character T.group → I → k),
      (∑ mu ∈ s, w mu) = x ∧ ∀ mu ∈ s, w mu ∈ weightSpace ρ T mu := by
  classical
  obtain ⟨n, ⟨iT⟩⟩ := hT
  obtain ⟨iA⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := k) n
  let i := iA ≪≫ iT.symm
  obtain ⟨c, _, hc, _, _⟩ := LinearAlgebraicGroups.CharacterDescent.splitCompositionPairing
    (k := k) n
  obtain ⟨δ, hδ⟩ := torusPoint_weights ρ i c hc
  let E := c.toEquiv.trans (charactersOfIso i)
  obtain ⟨s, hs⟩ := sum_projections δ x
  let w (mu : Character T.group) := weightProjection δ (E.symm mu) x
  refine ⟨s.map E.toEmbedding, w, ?_, fun mu _ ↦ ?_⟩
  · simpa only [Finset.sum_map, Equiv.toEmbedding_apply, w, Equiv.symm_apply_apply] using hs
  · rw [← E.apply_symm_apply mu]
    rw [show weightSpace ρ T (E (E.symm mu)) = _ from hδ (E.symm mu)]
    simpa only [w, Equiv.symm_apply_apply] using projection_mem δ (E.symm mu) x

private theorem strict_height (T B : ClosedSubgroup G.val)
    (f : Additive (Character T.group) →ₗ[ℤ] ℝ)
    (hf : ∀ α : SimpleRoot T B, 0 < f (Additive.ofMul α.val.val))
    {mu lam : Character T.group} (hne : mu ≠ lam) (h : DominanceLE T B mu lam) :
    f (Additive.ofMul mu) < f (Additive.ofMul lam) := by
  have hm := (dominanceLE_iff T B mu lam).mp h
  have hpos : ∀ x ∈ positiveCone T B, x = 0 ∨ 0 < f x := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ ↦ x = 0 ∨ 0 < f x) ?_ (Or.inl rfl)
      ?_ ?_ hx
    · rintro _ ⟨α, rfl⟩
      exact Or.inr (hf α)
    · intro a b _ _ ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · simp
      · simpa using Or.inr hb
      · simpa using Or.inr ha
      · exact Or.inr (by rw [map_add]; exact add_pos ha hb)
    · intro n a _ ha
      rcases ha with rfl | ha
      · simp
      · cases n with
        | zero => simp
        | succ n => exact Or.inr (by rw [map_nsmul]; exact nsmul_pos ha n.succ_ne_zero)
  have hne' : Additive.ofMul lam - Additive.ofMul mu ≠ 0 :=
    sub_ne_zero.mpr (fun he ↦ hne (congrArg Additive.toMul he.symm))
  have hh := (hpos _ hm).resolve_left hne'
  rwa [map_sub, sub_pos] at hh

open private finite_kernel_of_formula from LinearAlgebraicGroups.Representation.FiniteDistributions

set_option maxHeartbeats 1500000 in
/-- The rational simple module of restricted highest weight remains simple
over the iterated relative Frobenius kernel. -/
theorem simplicity : Specs.RestrictedSimplicity.Simplicity.{u} := by
  classical
  intro k _ _ p r _ _ hr G P U hU χ hdom hrestricted S F hF hHopf
  letI := hHopf
  let K₀ := CommAlgCat.of k k
  let V := S.socle
  let Q := hopfQuotient S.A (kernelIdeal F)
  let q := hopfQuotientMap S.A (kernelIdeal F)
  let D := Dist k Q
  let δ := restrict q.hom.toCoalgHom S.socleCoaction
  let m := (toAction S.socleCoaction).comp (distributionMap q.hom.toCoalgHom)
  let M := moduleStructure m
  letI : Module D V := M.module
  letI : IsScalarTower k D V := M.tower
  let v := S.highestVector
  let b := S.socleBasis.equivFun
  have hv : v ≠ 0 := fun he ↦ S.primitive.1 (by simpa using congrArg b he)
  letI : Nontrivial V := ⟨⟨v, 0, hv⟩⟩
  letI : IsArtinian D V := isArtinian_of_tower k (inferInstance : IsArtinian k V)
  have hn : Specs.IsNormalSubgroup (specGroupMap q) := (LinearAlgebraicGroups.schemeKernel k F).2
  letI := convolutionGroup S.A K₀
  let a := rationalAction S.socleCoaction
  have ha (t : WithConv (S.A →ₐ[k] k)) (d : D) :
      ∃ d' : D, ∀ x : V, a t (d • x) = d' • a t x :=
    rationalAction_normalizes S q hn t d
  have hi (t : WithConv (S.A →ₐ[k] k)) (d : D) :
      ∃ d' : D, ∀ x : V, (a t).symm (d • x) = d' • (a t).symm x :=
    ha t⁻¹ d
  letI : IsSemisimpleModule D V :=
    semisimple_of_normalizers a ha hi (rationalAction_irreducible S)
  have hcyc : ∀ w : V, ∃ d : D, d • v = w := by
    intro w
    obtain ⟨d, hd⟩ := RestrictedCyclicity.cyclicity p r hr P U hU χ hdom hrestricted S F hF hHopf w
    refine ⟨d, ?_⟩
    change toAction S.socleCoaction (distributionMap q.hom.toCoalgHom d) v = w
    rw [toAction_pairs]
    exact (pair_lTensor q.hom.toAlgHom.toLinearMap d.ofConv
      (S.socleCoaction.coaction v)).symm.trans hd
  let E := endomorphismAlgebra (k := k) (D := D) (V := V)
  have hinj (f g : E) (h : f.val v = g.val v) : f = g := by
    apply Subtype.ext
    apply LinearMap.ext
    intro w
    obtain ⟨d, rfl⟩ := hcyc w
    exact (f.property d v).trans ((congrArg (d • ·) h).trans (g.property d v).symm)
  let T := P.torus
  let H := closedSubgroupAlgebraicGroup T
  let AT := coordinateHopf (⟨T.group, H.property.1⟩ : AffineGroupCategory k)
  let eT : specGroup AT ≅ T.group :=
    (affineGroupInclusion k).mapIso (coordinateHopfSpecIso ⟨T.group, H.property.1⟩)
  obtain ⟨hAT, hred⟩ := coordinateReduced H AT eT (splitTorusSmooth P.split)
  letI : Algebra.FiniteType k AT := hAT
  letI : _root_.IsReduced (AlgebraicClosure k ⊗[k] AT) := hred
  letI : _root_.IsReduced AT :=
    isReduced_of_injective (Algebra.TensorProduct.includeRight :
      AT →ₐ[k] AlgebraicClosure k ⊗[k] AT)
      (Algebra.TensorProduct.includeRight_injective (algebraMap k (AlgebraicClosure k)).injective)
  let liftPoint (t : GroupPoints T.group K₀) : WithConv (S.A →ₐ[k] k) :=
    toConv ((pointCoordinates S.groupIso K₀).symm (t ≫ T.inclusion.hom.hom))
  let aT (t : GroupPoints T.group K₀) := a (liftPoint t)
  let c := pointCharacters T.group
  have hc : Function.Injective c := pointCharacters_injective eT
  have hact (t : GroupPoints T.group K₀) (x : V) :
      b (aT t x) = act S.socleAction K₀ (t ≫ T.inclusion.hom.hom) (b x) := by
    have he := (pointCoordinates S.groupIso K₀).apply_symm_apply (t ≫ T.inclusion.hom.hom)
    rw [pointCoordinates_apply] at he
    exact ((basis_act_point S (liftPoint t) x).symm.trans
      (congrArg (fun g ↦ act S.socleAction K₀ g (b x)) he))
  have hw (mu : Character T.group) (x : V) :
      HasWeight aT c mu x ↔ b x ∈ weightSpace S.socleAction T mu := by
    rw [← rational_weight_iff S.socleAction T eT]
    constructor
    · intro h t
      rw [← hact, h t, map_smul, pointCharacters_apply]
    · intro h t
      apply b.injective
      rw [hact, h t, map_smul, pointCharacters_apply]
  have hC := CyclicHighestWeight.cyclicHighestWeight.{u}
  have hgen := generates_of_simple hC.1 S.socleAction S.A (pointIso S.groupIso) S.simple S.primitive.1
  obtain ⟨inst, datum, hhighest⟩ :=
    hC.2 G P.reductive T P.positive P.split P.maximal P.positiveBorel P.inPositive
  letI := inst
  obtain ⟨_, hweights⟩ := hhighest U hU S.socleAction χ (b v) S.primitive
  have hlower := (hweights hgen).2.1
  obtain ⟨_, _, _, hB, _⟩ := RootData.BorelPositivity.borelPositivity G P.reductive T P.split P.maximal
  obtain ⟨height, _, hheight⟩ := hB.1 P.positive P.positiveBorel P.inPositive
  have hpos (α : SimpleRoot T P.positive) : 0 < height (Additive.ofMul α.val.val) := by
    have h (root : Specs.AbstractPairing.Root T) :
        root ∈ Specs.BorelsAndChambers.subgroupRoots T P.positive ↔
          0 < height (Additive.ofMul root.val) := by
      rw [hheight]
      rfl
    exact (h α.val).mp α.property.1
  have hbound (mu : Character T.group) (x : V) (hx : HasWeight aT c mu x)
      (h0 : x ≠ 0) (hmu : mu ≠ χ) :
      height (Additive.ofMul mu) < height (Additive.ofMul χ) := by
    apply strict_height T P.positive height hpos hmu
    apply hlower mu hmu
    intro he
    have hmem := (hw mu x).mp hx
    rw [he, Submodule.mem_bot] at hmem
    exact h0 (b.map_eq_zero_iff.mp hmem)
  have hline (x : V) (hx : HasWeight aT c χ x) : ∃ z : k, x = z • v := by
    have hmem := (hw χ x).mp hx
    rw [S.highestLine, Submodule.mem_span_singleton] at hmem
    obtain ⟨z, hz⟩ := hmem
    exact ⟨z, b.injective (by rw [map_smul, hz])⟩
  have hdecomp (x : V) : ∃ (s : Finset (Character T.group)) (w : Character T.group → V),
      (∑ mu ∈ s, w mu) = x ∧ ∀ mu ∈ s, HasWeight aT c mu (w mu) := by
    obtain ⟨s, w, hs, hmem⟩ := split_weight_sum S.socleAction T P.split (b x)
    exact ⟨s, fun mu ↦ b.symm (w mu), by rw [← map_sum, hs, b.symm_apply_apply],
      fun mu hi ↦ (hw mu _).mpr (by rw [b.apply_symm_apply]; exact hmem mu hi)⟩
  have hproject (α : Character T.group) : ∃ L : V →ₗ[k] V, ∀ mu x,
      HasWeight aT c mu x → L x = if mu = α then x else 0 := by
    obtain ⟨L, hL⟩ := weightProjection S.socleAction T α
    refine ⟨b.symm.toLinearMap ∘ₗ L ∘ₗ b.toLinearMap, fun mu x hx ↦ ?_⟩
    change b.symm (L (b x)) = _
    rw [hL mu _ ((hw mu x).mp hx)]
    split <;> simp
  choose proj hproj using hproject
  have hscalar := scalar_of_highest aT c hc height.toAddMonoidHom χ v E
    (fun t f hf ↦ endomorphismAlgebra_normalized (aT t) (ha _) (hi _) f hf)
    hinj endomorphismAlgebra_regular ((hw χ v).mpr S.primitive.2.2) hline hbound hdecomp proj hproj
  letI : IsSimpleModule D V := simple_of_scalar_endomorphisms hscalar
  obtain ⟨hft, _⟩ := coordinateReduced G S.A S.groupIso P.reductive.1
  letI : Module.Finite k Q := finite_kernel_of_formula p r S.A F hF hft
  have hpair : PairsWith δ m := by
    intro d x
    change toAction S.socleCoaction (distributionMap q.hom.toCoalgHom d) x =
      pair d (q.hom.toAlgHom.toLinearMap.lTensor V (S.socleCoaction.coaction x))
    rw [toAction_pairs]
    exact (pair_lTensor _ _ _).symm
  refine ⟨δ, rfl, bot_ne_top.symm, fun W hW ↦ ?_⟩
  have hu := (subobjectComparison δ m hpair W).mp hW
  let W' : Submodule D V :=
    { W with smul_mem' := fun d x hx ↦ hu d ⟨x, hx⟩ }
  have he : W'.restrictScalars k = W := rfl
  rcases eq_bot_or_eq_top W' with hb | ht
  · left
    rw [← he, hb, Submodule.restrictScalars_bot]
  · right
    rw [← he, ht, Submodule.restrictScalars_top]

end

end LinearAlgebraicGroups.Representation.RestrictedSimplicity
