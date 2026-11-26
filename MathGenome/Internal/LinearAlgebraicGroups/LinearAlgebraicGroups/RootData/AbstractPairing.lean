import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.AbstractPairing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.WeylScheme
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Group
import Mathlib.Tactic.Module

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.RootData.AbstractPairing

open _root_.LinearAlgebraicGroups.Specs
open Specs.AbstractPairing (Root)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (absoluteRoots adjointWeightVectors characterValue pairing)
open Specs.AdjointRepresentation (GroupPoints constants dualMap scale)
open Specs.NormalizerLatticeAction (SplitImage)

noncomputable section

section Lattices

variable {X Y I W : Type*} [AddCommGroup X] [AddCommGroup Y]
  [Module.IsTorsionFree ℤ X] [Group W] [Finite W]
  (ρ : W →* (X ≃ₗ[ℤ] X)) (B : X →ₗ[ℤ] Y →ₗ[ℤ] ℤ)

/-- A finite-order operator on a torsion-free lattice equals the identity
if its difference from the identity is square-zero. -/
private theorem finite_shear (w : W) (d : X →ₗ[ℤ] X)
    (hw : ∀ x, ρ w x = x + d x) (hd : ∀ x, d (d x) = 0) : d = 0 := by
  have hpow (x : X) (n : ℕ) : ρ (w ^ n) x = x + n • d x := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', map_mul]
      change ρ w (ρ (w ^ n) x) = _
      rw [ih, hw, map_add, map_nsmul, hd, nsmul_zero, add_zero, succ_nsmul, add_assoc]
  ext x
  have h := hpow x (orderOf w)
  rw [pow_orderOf_eq_one, map_one] at h
  have hz : orderOf w • d x = 0 := by simpa using h.symm
  exact (smul_eq_zero.mp (show (orderOf w : ℤ) • d x = 0 by simpa using hz)).resolve_left
    (by exact_mod_cast (orderOf_pos w).ne')

/-- Reflections with the same coroot have a square-zero shear as their product. -/
private theorem coroot_determines_root {s t : W} {r q : X} {c : Y}
    (hr : B r c = 2) (hq : B q c = 2)
    (hs : ∀ x, ρ s x = x - B x c • r) (ht : ∀ x, ρ t x = x - B x c • q) :
    r = q := by
  let d := (B.flip c).smulRight (r - q)
  have hh (x : X) : d x = B x c • (r - q) := rfl
  have hz : d = 0 := finite_shear ρ (s * t) d (fun x => by
    rw [map_mul]
    change ρ s (ρ t x) = _
    rw [ht, hs, hh, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, hq]
    module) (fun x => by
    rw [hh, hh, map_smul, LinearMap.smul_apply, map_sub, LinearMap.sub_apply, hr, hq,
      sub_self, smul_zero, zero_smul])
  have h := LinearMap.congr_fun hz r
  rw [hh, hr, LinearMap.zero_apply] at h
  exact sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_left (by decide))

/-- Within a finite group of lattice automorphisms, a reflection with a
specified root determines its coroot. -/
private theorem root_determines_coroot [B.IsPerfPair] {s t : W} {r : X} {c d : Y}
    (hc : B r c = 2) (hd : B r d = 2)
    (hs : ∀ x, ρ s x = x - B x c • r) (ht : ∀ x, ρ t x = x - B x d • r) :
    c = d := by
  have hr : r ≠ 0 := by
    intro h
    simp [h] at hc
  let D := (B.flip (d - c)).smulRight r
  have hD (x : X) : D x = (B x d - B x c) • r := by simp [D, LinearMap.smulRight_apply]
  have hz : D = 0 := finite_shear ρ (s * t) D (fun x => by
    rw [map_mul]
    change ρ s (ρ t x) = _
    rw [ht, hs, hD, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, hc]
    module) (fun x => by
    simp only [hD, map_smul, LinearMap.smul_apply, hc, hd, sub_self, zero_smul])
  apply B.flip.toPerfPair.injective
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun hz x
  rw [hD, LinearMap.zero_apply] at h
  exact (sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_right hr)).symm

variable [B.IsPerfPair]

private def dualEquiv (f : X ≃ₗ[ℤ] X) : Y ≃ₗ[ℤ] Y :=
  B.flip.toPerfPair.trans (f.symm.dualMap.trans B.flip.toPerfPair.symm)

omit [Module.IsTorsionFree ℤ X] in
private theorem dualEquiv_pair (f : X ≃ₗ[ℤ] X) (x : X) (y : Y) :
    B (f x) (dualEquiv B f y) = B x y := by
  change B.flip.toPerfPair (B.flip.toPerfPair.symm (f.symm.dualMap (B.flip.toPerfPair y))) (f x) = _
  simp

omit [Module.IsTorsionFree ℤ X] in
private theorem dualEquiv_reflection {f : X ≃ₗ[ℤ] X} {r : X} {c : Y}
    (h2 : B r c = 2) (hf : ∀ x, f x = x - B x c • r) (y : Y) :
    dualEquiv B f y = y - B r y • c := by
  have hinv (x : X) : f.symm x = f x := by
    apply f.injective
    rw [f.apply_symm_apply, hf (f x), hf x, map_sub, LinearMap.sub_apply,
      map_smul, LinearMap.smul_apply, h2]
    module
  apply B.flip.toPerfPair.injective
  apply LinearMap.ext
  intro x
  change B.flip.toPerfPair (B.flip.toPerfPair.symm (f.symm.dualMap (B.flip.toPerfPair y))) x =
    B x (y - B r y • c)
  rw [LinearEquiv.apply_symm_apply]
  change B (f.symm x) y = _
  simp only [hinv, hf, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

variable (root : I ↪ X) (coroot : I → Y) (reflection : I → W)
  (action : W → I ≃ I) (hroot : ∀ w i, ρ w (root i) = root (action w i))
  (hpair : ∀ i, B (root i) (coroot i) = 2)
  (href : ∀ i x, ρ (reflection i) x = x - B x (coroot i) • root i)

include reflection hroot hpair href in
private theorem coroot_equivariant (w : W) (i : I) :
    dualEquiv B (ρ w) (coroot i) = coroot (action w i) := by
  have hmul (x : X) : ρ (w * reflection i * w⁻¹) x = ρ w (ρ (reflection i) ((ρ w).symm x)) := by
    simp only [map_mul, map_inv]
    rfl
  apply root_determines_coroot ρ B (s := w * reflection i * w⁻¹) (t := reflection (action w i)) (r := root (action w i))
  · rw [← hroot, dualEquiv_pair, hpair]
  · exact hpair _
  · intro x
    rw [hmul, href, map_sub, map_smul, hroot, LinearEquiv.apply_symm_apply]
    rw [← dualEquiv_pair B (ρ w) ((ρ w).symm x) (coroot i), LinearEquiv.apply_symm_apply]
  · exact href _

private def rootDatum : RootDatum I X Y where
  toLinearMap := B
  root := root
  coroot := ⟨coroot, fun i j hij => root.injective
    (coroot_determines_root ρ B (hpair i) (hij ▸ hpair j) (href i) (hij ▸ href j))⟩
  root_coroot_two := hpair
  reflectionPerm i := action (reflection i)
  reflectionPerm_root i j := (href i (root j)).symm.trans (hroot _ _)
  reflectionPerm_coroot i _j :=
    (dualEquiv_reflection B (hpair i) (href i) _).symm.trans
      (coroot_equivariant ρ B root coroot reflection action hroot hpair href _ _)

private def datumAutomorphism (P : RootDatum I X Y) (f : X ≃ₗ[ℤ] X) (π : I ≃ I)
    (hroot : ∀ i, f (P.root i) = P.root (π i))
    (hc : ∀ i, dualEquiv P.toLinearMap f (P.coroot i) = P.coroot (π i)) : P.Aut where
  weightMap := f
  coweightMap := (dualEquiv P.toLinearMap f).symm
  indexEquiv := π
  weight_coweight_transpose := by
    ext y x
    change P.toLinearMap (f x) y = P.toLinearMap x ((dualEquiv P.toLinearMap f).symm y)
    simpa only [LinearEquiv.apply_symm_apply] using
      dualEquiv_pair P.toLinearMap f x ((dualEquiv P.toLinearMap f).symm y)
  root_weightMap := funext hroot
  coroot_coweightMap := by
    funext i
    change (dualEquiv P.toLinearMap f).symm (P.coroot i) = P.coroot (π.symm i)
    apply (dualEquiv P.toLinearMap f).injective
    rw [LinearEquiv.apply_symm_apply, hc, Equiv.apply_symm_apply]
  bijective_weightMap := f.bijective
  bijective_coweightMap := (dualEquiv P.toLinearMap f).symm.bijective

omit [Module.IsTorsionFree ℤ X] in
private theorem weightHom_datumAutomorphism (P : RootDatum I X Y) (f : X ≃ₗ[ℤ] X)
    (π : I ≃ I) (hroot : ∀ i, f (P.root i) = P.root (π i))
    (hc : ∀ i, dualEquiv P.toLinearMap f (P.coroot i) = P.coroot (π i)) :
    RootPairing.Equiv.weightHom P (datumAutomorphism P f π hroot hc) = f :=
  LinearEquiv.ext fun _ => rfl

end Lattices

end

noncomputable section

variable {k : Type u} [Field k] {G : GroupScheme k}

set_option backward.isDefEq.respectTransparency false

private def constantPoint (g : 𝟙_ (SchemeOver k) ⟶ G.X) (S : SchemeOver k) : S ⟶ G.X :=
  toUnit S ≫ g

private theorem comp_constantPoint (g : 𝟙_ (SchemeOver k) ⟶ G.X)
    {S U : SchemeOver k} (f : S ⟶ U) : f ≫ constantPoint g U = constantPoint g S := by
  unfold constantPoint
  rw [← Category.assoc]
  congr 1
  subsingleton

private def pointConj (g : 𝟙_ (SchemeOver k) ⟶ G.X) {S : SchemeOver k} (p : S ⟶ G.X) :
    S ⟶ G.X :=
  constantPoint g S * p * (constantPoint g S)⁻¹

private theorem comp_pointConj (g : 𝟙_ (SchemeOver k) ⟶ G.X)
    {S U : SchemeOver k} (f : S ⟶ U) (p : U ⟶ G.X) :
    f ≫ pointConj g p = pointConj g (f ≫ p) := by
  simp only [pointConj, MonObj.comp_mul, GrpObj.comp_inv, comp_constantPoint]

private theorem mapPoints_pointConj (g : 𝟙_ (SchemeOver k) ⟶ G.X)
    {R S : TestAlgebra k} (b : R ⟶ S) (p : GroupPoints G R) :
    mapPoints b (pointConj g p) = pointConj g (mapPoints b p) :=
  comp_pointConj g _ p

/-- Conjugation transports a nonzero weight vector by conjugating its
dual-number point. This works over every test algebra. -/
private theorem conjugation_maps_roots {T : ClosedSubgroup G} (e : T.group ≅ T.group)
    (g : 𝟙_ (SchemeOver k) ⟶ G.X)
    (h : (e.hom ≫ T.inclusion).hom.hom = pointConj g T.inclusion.hom.hom)
    {χ : Character T.group} (hχ : χ ∈ absoluteRoots T) :
    (e.inv ≫ χ) ∈ absoluteRoots T := by
  obtain ⟨hne, v, hv, hvne⟩ := hχ
  refine ⟨?_, ?_⟩
  · intro he
    apply hne
    have hh := congrArg (fun f : Character T.group => e.hom ≫ f) he
    have hone : e.hom ≫ (1 : Character T.group) = 1 := by
      apply Grp.hom_ext
      exact MonObj.comp_one _
    simpa only [CategoryTheory.Iso.hom_inv_id_assoc, hone] using hh
  let v' : Lie k G := Additive.ofMul ⟨pointConj g v.toMul.val, by
    change mapPoints (dualReduction k) (pointConj g v.toMul.val) = 1
    have hv0 : mapPoints (dualReduction k) v.toMul.val = 1 := v.toMul.property
    rw [mapPoints_pointConj, hv0]
    simp [pointConj]⟩
  refine ⟨v', ?_, ?_⟩
  · intro R t
    let D := CommAlgCat.of k (DualNumber R)
    let extend := dualMap (CommAlgCat.ofHom (Algebra.ofId k R))
    let p : GroupPoints G D := mapPoints extend v.toMul.val
    let t' : GroupPoints T.group R := t ≫ e.inv.hom.hom
    let a : GroupPoints G D := mapPoints (constants R) (t' ≫ T.inclusion.hom.hom)
    let b : GroupPoints G D := mapPoints (constants R) (t ≫ T.inclusion.hom.hom)
    let z := characterValue χ R t'
    have hb : b = pointConj g a := by
      have heq := congrArg (fun f => t' ≫ f) h
      simp only [comp_pointConj] at heq
      have ht : t' ≫ (e.hom ≫ T.inclusion).hom.hom = t ≫ T.inclusion.hom.hom := by
        have hcomp : e.inv ≫ e.hom ≫ T.inclusion = T.inclusion := e.inv_hom_id_assoc _
        exact congrArg (fun f : T.group ⟶ G => t ≫ f.hom.hom) hcomp
      rw [ht] at heq
      exact (congrArg (mapPoints (constants R)) heq).trans
        (mapPoints_pointConj g (constants R) _)
    have hz : characterValue (e.inv ≫ χ) R t = z := by
      unfold characterValue z t'
      congr 2
    let p' : GroupPoints G D := mapPoints extend (pointConj g v.toMul.val)
    let cp : GroupPoints G D := pointConj g p
    have hcp : p' = cp := mapPoints_pointConj g extend v.toMul.val
    change b * p' * b⁻¹ = mapPoints (scale R (characterValue (e.inv ≫ χ) R t)) p'
    have hweight : a * p * a⁻¹ = mapPoints (scale R z) p := hv R t'
    rw [hz, hcp]
    change b * cp * b⁻¹ = mapPoints (scale R z) (pointConj g p)
    rw [mapPoints_pointConj, ← hweight, hb]
    change pointConj g a * pointConj g p * (pointConj g a)⁻¹ = pointConj g (a * p * a⁻¹)
    unfold pointConj
    group
  · intro hzero
    have he := congrArg (fun v : Lie k G => v.toMul.val) hzero
    change pointConj g v.toMul.val = 1 at he
    have hv1 : v.toMul.val = 1 := by
      have he' := mul_inv_eq_one.mp he
      exact (mul_left_cancel (he'.trans (mul_one _).symm))
    exact hvne (Subtype.ext hv1)

private def quotientLabel {T N Q : GroupScheme k} {i : T ⟶ G} {v : N ⟶ G} {q : N ⟶ Q}
    (D : SplitImage i v q) : (𝟙_ (SchemeOver k) ⟶ N.X) →* D.labels :=
  (LocallyConstant.evalMonoidHom (IsLocalRing.closedPoint k)).comp
    ((D.constantGroup.families _).toMonoidHom.comp
      { toFun := fun n => n ≫ q.hom.hom
        map_one' := MonObj.one_comp _
        map_mul' := fun _ _ => MonObj.mul_comp _ _ _ })

private theorem quotientLabel_spec {T N Q : GroupScheme k} {i : T ⟶ G} {v : N ⟶ G}
    {q : N ⟶ Q} (D : SplitImage i v q) (n : 𝟙_ (SchemeOver k) ⟶ N.X) :
    n ≫ q.hom.hom = toUnit _ ≫ D.constantGroup.sectionPoint (quotientLabel D n) := by
  apply (D.constantGroup.families _).injective
  rw [D.constantGroup.constant]
  apply LocallyConstant.ext
  intro x
  change (D.constantGroup.families _ (n ≫ q.hom.hom)) x =
    (D.constantGroup.families _ (n ≫ q.hom.hom)) (IsLocalRing.closedPoint k)
  rw [Subsingleton.elim (α := PrimeSpectrum k) x (IsLocalRing.closedPoint k)]

private theorem quotientLabel_conjugates {T N Q : GroupScheme k} {i : T ⟶ G} {v : N ⟶ G}
    {q : N ⟶ Q} (D : SplitImage i v q) (n : 𝟙_ (SchemeOver k) ⟶ N.X) :
    ((D.conjugation (quotientLabel D n)).hom ≫ i).hom.hom =
      pointConj (n ≫ v.hom.hom) i.hom.hom := by
  have he := congrArg (fun f => lift (𝟙 T.X) (toUnit T.X) ≫ f)
    (D.conjugates _ n _ (quotientLabel_spec D n))
  simpa only [conjugateFamily, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc,
    lift_fst_assoc, lift_snd_assoc, Category.id_comp, pointConj, constantPoint] using he.symm

private theorem quotientLabel_surjective {T N Q : GroupScheme k} {i : T ⟶ G} {v : N ⟶ G}
    {q : N ⟶ Q} (D : SplitImage i v q)
    (h : ∀ w : 𝟙_ (SchemeOver k) ⟶ Q.X, ∃ n : 𝟙_ (SchemeOver k) ⟶ N.X,
      n ≫ q.hom.hom = w) :
    Function.Surjective (quotientLabel D) := by
  intro w
  obtain ⟨n, hn⟩ := h (D.constantGroup.sectionPoint w)
  refine ⟨n, ?_⟩
  change (D.constantGroup.families _ (n ≫ q.hom.hom)) (IsLocalRing.closedPoint k) = w
  have he : toUnit (𝟙_ (SchemeOver k)) = 𝟙 _ := Subsingleton.elim _ _
  rw [hn, ← Category.id_comp (D.constantGroup.sectionPoint w), ← he,
    D.constantGroup.constant]
  rfl

private def latticeAction {T N Q : GroupScheme k} {i : T ⟶ G} {v : N ⟶ G} {q : N ⟶ Q}
    (D : SplitImage i v q) :
    D.labels →* (Additive (Character T) ≃ₗ[ℤ] Additive (Character T)) where
  toFun w := AddEquiv.toIntLinearEquiv w.val.toAdditive
  map_one' := rfl
  map_mul' w z := by
    ext x
    rfl

private def actionOnRoots {H : AffineAlgebraicGroup k} {T : ClosedSubgroup H.val} {N Q : GroupScheme k}
    {v : N ⟶ H.val} {q : N ⟶ Q} (D : SplitImage T.inclusion v q)
    (hlift : Function.Surjective (quotientLabel D)) (w : D.labels) : Root T ≃ Root T := by
  have hstable (a : D.labels) (α : Root T) : a.val α.val ∈ absoluteRoots T := by
    obtain ⟨n, hn⟩ := hlift a
    rw [D.characterAction]
    exact conjugation_maps_roots _ _ (hn ▸ quotientLabel_conjugates D n) α.property
  exact {
    toFun := fun α => ⟨w.val α.val, hstable w α⟩
    invFun := fun α => ⟨(w⁻¹).val α.val, hstable w⁻¹ α⟩
    left_inv := fun α => Subtype.ext (w.val.symm_apply_apply α.val)
    right_inv := fun α => Subtype.ext (w.val.apply_symm_apply α.val)
  }

end

open Specs.AbstractPairing (Datum IsAttachedCoroot NormalizerAction Statement)
open Specs.CharacterDescent (compositionPairing)
open Specs.RootGroups (RankOneRootGroups RootDimension RootSubgroups Proportional)
open Specs.GeometricRadicals (IsSplitTorus)

open private isTorus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

private theorem conjugation_unique {G : GroupScheme k} (T : ClosedSubgroup G)
    {e e' : T.group ≅ T.group}
    (h : (e.hom ≫ T.inclusion).hom.hom = (e'.hom ≫ T.inclusion).hom.hom) : e = e' := by
  have : IsClosedImmersion T.inclusion.hom.hom.left := T.isClosedImmersion
  have : Mono T.inclusion.hom.hom :=
    (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono T.inclusion.hom.hom.left))
  apply Iso.ext
  apply Grp.hom_ext
  exact (cancel_mono T.inclusion.hom.hom).mp h

private theorem reduced_of_proportional {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    [IsCommMonObj T.group.X] [Module.IsTorsionFree ℤ (Additive (Character T.group))]
    (P : RootDatum (Root T) (Additive (Character T.group)) (Additive (Cocharacter T.group)))
    (hroot : ∀ α, P.root α = Additive.ofMul α.val)
    (hprop : ∀ α : Root T, ∀ β : Character T.group,
      β ∈ absoluteRoots T ∧ Proportional α.val β ↔ β = α.val ∨ β = α.val⁻¹) : P.IsReduced := by
  constructor
  intro i j h
  rw [LinearIndependent.pair_iff] at h
  push Not at h
  obtain ⟨a, b, hab, hne⟩ := h
  have ha : a ≠ 0 := by
    intro ha
    have hb : b • P.root j = 0 := by simpa [ha] using hab
    exact hne ha ((smul_eq_zero.mp hb).resolve_right (P.ne_zero j))
  have hb : b ≠ 0 := by
    intro hb
    have hz : a • P.root i = 0 := by simpa [hb] using hab
    exact hne ((smul_eq_zero.mp hz).resolve_right (P.ne_zero i)) hb
  have hp : Proportional i.val j.val := by
    refine ⟨a, -b, ha, neg_ne_zero.mpr hb, ?_⟩
    have hh : a • P.root i = (-b) • P.root j := by
      rw [neg_smul, eq_neg_iff_add_eq_zero]
      exact hab
    rw [hroot, hroot] at hh
    exact congrArg Additive.toMul hh
  rcases (hprop i j.val).mp ⟨j.property, hp⟩ with h' | h'
  · left
    rw [hroot, hroot, h']
  · right
    rw [hroot, hroot, h']
    change Additive.ofMul i.val = -(-Additive.ofMul i.val)
    rw [neg_neg]

/-- The absolute root datum and rational normalizer action, conditional on the
three root-group theorems. -/
theorem abstractPairing_conditional
    (rankOne : RankOneRootGroups.{u})
    (dimension : RootDimension.{u})
    (rootGroups : RootSubgroups.{u}) :
    Statement.{u} := by
  classical
  intro k _ G hG T hT hmax
  obtain ⟨hcomm, hfreeX, hfinX, hfreeY, hfinY, B, hperf, hB⟩ :=
    LinearAlgebraicGroups.RootData.CharacterPairing.perfectCharacterPairing T.group hT
  have := hcomm
  have := hfreeX
  have := hfreeY
  have := hperf
  have : Finite (Root T) := (dimension G hG T hT hmax).1
  obtain ⟨N, _, _, Q, q, hN, _, _, _, _, _, hsplit⟩ :=
    LinearAlgebraicGroups.Reductive.WeylScheme.weylScheme G hG T (isTorus_of_split hT) hmax
  obtain ⟨⟨D⟩, hlift⟩ := hsplit hT
  have := D.finite
  let ρ := latticeAction D
  let action := actionOnRoots D (quotientLabel_surjective D (fun w => (hlift w).2))
  let root : Root T ↪ Additive (Character T.group) :=
    ⟨fun α => Additive.ofMul α.val, fun _ _ h => Subtype.ext (congrArg Additive.toMul h)⟩
  have hroot (w : D.labels) (i : Root T) : ρ w (root i) = root (action w i) := rfl
  have hRank (α : Root T) :
      ∃ c : Cocharacter T.group, IsAttachedCoroot T α c ∧ B (root α) (Additive.ofMul c) = 2 ∧
      ∃ w : D.labels, ∀ x, ρ w x = x - B x (Additive.ofMul c) • root α := by
    obtain ⟨C, cochar₀, hC, hpositive, Dpos, Dneg, hDyn, Q₀, F, A₀, A, p, n, hp, hn, hs, hs', ⟨s⟩⟩ :=
      rankOne G hG T hT hmax α.val α.property
    obtain ⟨m, hm⟩ := (hN _ _).mp s.normalizes
    let w := quotientLabel D m
    have hconj : s.conjugation = D.conjugation w := by
      apply conjugation_unique T
      exact s.conjugates.trans (by simpa only [w, hm, pointConj, constantPoint] using
        (quotientLabel_conjugates D m).symm)
    refine ⟨s.coroot, ⟨C, cochar₀, hC, hpositive, Dpos, Dneg, hDyn, Q₀, F, A₀, A, p, n, hp, hn, hs, hs', s, rfl⟩,
      (hB α.val s.coroot).trans s.root_pairing, w, fun x => ?_⟩
    let χ : Character T.group := Additive.toMul x
    change Additive.ofMul (w.val χ) =
      Additive.ofMul χ - B (Additive.ofMul χ) (Additive.ofMul s.coroot) • Additive.ofMul α.val
    rw [D.characterAction, ← hconj, s.reflection, hB, sub_eq_add_neg, ← neg_smul]
    rfl
  choose c hc hpair σ href using hRank
  let coroot (i : Root T) := Additive.ofMul (c i)
  let P := rootDatum ρ B root coroot σ action hroot hpair href
  have : P.IsReduced := reduced_of_proportional P (fun _ => rfl)
    (fun i j => (rootGroups G hG T hT hmax).2 i.val i.property |>.2.1 j)
  have hcoroot (w : D.labels) (i : Root T) :
      dualEquiv B (ρ w) (P.coroot i) = P.coroot (action w i) :=
    coroot_equivariant ρ B root coroot σ action hroot hpair href w i
  let aut : D.labels →* P.Aut :=
    { toFun := fun w => datumAutomorphism P (ρ w) (action w) (hroot w) (hcoroot w)
      map_one' := by
        apply (RootPairing.Equiv.weightHom_injective P)
        rw [weightHom_datumAutomorphism]
        exact (ρ.map_one).trans ((RootPairing.Equiv.weightHom P).map_one).symm
      map_mul' := fun w z => by
        apply (RootPairing.Equiv.weightHom_injective P)
        simpa only [map_mul (RootPairing.Equiv.weightHom P), weightHom_datumAutomorphism] using
          ρ.map_mul w z }
  have hnormalizer : NormalizerAction T P := by
    refine ⟨N, hN, aut.comp (quotientLabel D), fun n => ?_⟩
    let w := quotientLabel D n
    let e := D.conjugation w
    refine ⟨e, quotientLabel_conjugates D n, ?_, ?_⟩
    · intro χ
      change Additive.ofMul (w.val χ) = _
      rw [D.characterAction]
    · intro cochar
      change (aut w).coweightEquiv.symm (Additive.ofMul cochar) = _
      apply (aut w).coweightEquiv.injective
      rw [LinearEquiv.apply_symm_apply]
      change Additive.ofMul cochar = (dualEquiv B (ρ w)).symm (Additive.ofMul (cochar ≫ e.hom))
      apply (dualEquiv B (ρ w)).injective
      rw [LinearEquiv.apply_symm_apply]
      apply B.flip.toPerfPair.injective
      apply LinearMap.ext
      intro x
      change B x (dualEquiv B (ρ w) (Additive.ofMul cochar)) = B x (Additive.ofMul (cochar ≫ e.hom))
      rw [← (ρ w).apply_symm_apply x, dualEquiv_pair]
      let χ : Character T.group := Additive.toMul ((ρ w).symm x)
      change B (Additive.ofMul χ) (Additive.ofMul cochar) =
        B (Additive.ofMul (w.val χ)) (Additive.ofMul (cochar ≫ e.hom))
      rw [D.characterAction, hB, hB]
      unfold pairing compositionPairing
      simp [e, Category.assoc]
  exact ⟨hcomm, ⟨{
    finiteRoots := inferInstance
    freeCharacters := hfreeX
    finiteCharacters := hfinX
    freeCocharacters := hfreeY
    finiteCocharacters := hfinY
    rootDatum := P
    root_eq := fun _ => rfl
    pairing_eq := hB
    attached := hc
    reduced := inferInstance
    reducedCoroots := inferInstance
    opposite := fun _ _ => P.root_eq_neg_iff.trans P.coroot_eq_neg_iff.symm
    normalizerAction := hnormalizer }⟩⟩

end

end LinearAlgebraicGroups.RootData.AbstractPairing

universe v8_closure_f2b4fcfdeec101cf_u0
theorem _root_.«LinearAlgebraicGroups».«RootData».«AbstractPairing».«abstractPairing» : _root_.«LinearAlgebraicGroups».«Specs».«AbstractPairing».«Statement».{v8_closure_f2b4fcfdeec101cf_u0} :=
  @_root_.«LinearAlgebraicGroups».«RootData».«AbstractPairing».«abstractPairing_conditional».{v8_closure_f2b4fcfdeec101cf_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rankOneRootGroups».{v8_closure_f2b4fcfdeec101cf_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rootDimension».{v8_closure_f2b4fcfdeec101cf_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«RootGroups».«rootSubgroups».{v8_closure_f2b4fcfdeec101cf_u0})
