import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalInnerIndexParabolic
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct nonZeroDivisors

universe u

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalInnerIndexParabolic

open Specs.ExceptionalAffineRootSystems (ApartmentRoots)
open Specs.ExceptionalInnerIndexParabolic (AdaptedIndexParabolic)
open Specs.ExceptionalInnerStandardTorusDescent (markedCocharacterMap)
open Specs.CharacterDescent (StandardLattice)
open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.Pinning (BasedRootDatum)
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Specs.SchemeDerivedGroup (IsSubgroupOf)

open private splitGroupHomEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private latticeCoordinates from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing

set_option backward.isDefEq.respectTransparency false in
/-- A closed immersion of split tori is an isomorphism if the target has
rank at most that of the source. -/
private theorem isIso_of_splitTorusClosedImmersion {k : Type u} [Field k]
    {S R : GroupScheme k} {r s : ℕ}
    (hS : Nonempty (S ≅ (StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin r))).val))
    (hR : Nonempty (R ≅ (StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin s))).val))
    (hsr : s ≤ r) (j : S ⟶ R) (hj : IsClosedImmersion j.hom.hom.left) : IsIso j := by
  obtain ⟨iS⟩ := hS
  obtain ⟨iR⟩ := hR
  obtain ⟨eS⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := k) r
  obtain ⟨eR⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := k) s
  let S₀ := eS ≪≫ iS.symm
  let R₀ := eR ≪≫ iR.symm
  let latticeHom := splitGroupHomEquiv (k := k) (StandardLattice.{u} s) (StandardLattice.{u} r)
  obtain ⟨h, hh⟩ := latticeHom.surjective (S₀.hom ≫ j ≫ R₀.inv)
  change specGroupMap (groupAlgebraMap k h) = _ at hh
  have hclosed : IsClosedImmersion (specGroupMap (groupAlgebraMap k h)).hom.hom.left := by
    rw [hh]
    change IsClosedImmersion (S₀.hom.hom.hom.left ≫ j.hom.hom.left ≫ R₀.inv.hom.hom.left)
    let _ : IsIso S₀.hom.hom.hom.left := inferInstanceAs
      (IsIso ((Grp.forget (SchemeOver k) ⋙ Over.forget _).map S₀.hom))
    let _ : IsIso R₀.inv.hom.hom.left := inferInstanceAs
      (IsIso ((Grp.forget (SchemeOver k) ⋙ Over.forget _).map R₀.inv))
    let _ := hj
    infer_instance
  -- A monomial in the target Hopf algebra needs a preimage with a term
  -- indexed by a character mapping to its exponent.
  have hsurj : Function.Surjective h := by
    classical
    have hf := (LinearAlgebraicGroups.hopfMapClosedImmersion k (groupAlgebraMap k h)).mp hclosed
    intro a
    obtain ⟨b, hb⟩ := hf (MonoidAlgebra.single a (1 : k))
    have he : b.coeff.mapDomain h = Finsupp.single a (1 : k) := congrArg MonoidAlgebra.coeff hb
    have ha : a ∈ (b.coeff.mapDomain h).support := by simp [he]
    obtain ⟨z, _, hz⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ha)
    exact ⟨z, hz⟩
  let hZ := (latticeCoordinates.{u} r).toLinearMap.comp
    (h.toAdditive.toIntLinearMap.comp (latticeCoordinates.{u} s).symm.toLinearMap)
  have hZsurj : Function.Surjective hZ := (latticeCoordinates r).surjective.comp
    (hsurj.comp (latticeCoordinates s).symm.surjective)
  have hdim : Module.finrank ℤ (Fin s → ℤ) ≤ Module.finrank ℤ (Fin r → ℤ) := by
    simpa using hsr
  have hZinj := (OrzechProperty.bijective_of_surjective_of_finrank_le hZ hZsurj hdim).1
  have hinj : Function.Injective h := by
    intro a b hab
    let i := latticeCoordinates.{u} s
    have ht : hZ (i (Additive.ofMul a)) = hZ (i (Additive.ofMul b)) := by
      simp [hZ, i, hab]
    exact Additive.ofMul.injective (i.injective (hZinj ht))
  let iso := (hopfSpec (CommRingCat.of k)).mapIso
    (CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv k k
      (MulEquiv.ofBijective h ⟨hinj, hsurj⟩))).op
  have he : iso.hom = specGroupMap (groupAlgebraMap k h) := rfl
  have hj' : j = (S₀.symm ≪≫ iso ≪≫ R₀).hom := by
    change j = S₀.inv ≫ iso.hom ≫ R₀.hom
    rw [he, hh]
    simp
  rw [hj']
  infer_instance

private theorem maximalSplitTorus_of_rank_bound {k : Type u} [Field k]
    {H : GroupScheme k} {S : ClosedSubgroup H} {r : ℕ}
    (hS : Nonempty (S.group ≅ (StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin r))).val))
    (hbound : ∀ (R : ClosedSubgroup H) (s : ℕ),
      Nonempty (R.group ≅ (StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin s))).val) →
        s ≤ r) :
    IsMaximalSplitTorus S := by
  refine ⟨⟨r, hS⟩, ?_⟩
  intro R hR hSR
  obtain ⟨s, hr⟩ := hR
  obtain ⟨j, hj⟩ := hSR
  let _ := R.isClosedImmersion
  have hcomp : IsClosedImmersion (j.hom.hom.left ≫ R.inclusion.hom.hom.left) := by
    change IsClosedImmersion (j ≫ R.inclusion).hom.hom.left
    rw [hj]
    exact S.isClosedImmersion
  let _ := hcomp
  let _ := isIso_of_splitTorusClosedImmersion hS hr (hbound R s hr) j
    (IsClosedImmersion.of_comp_isClosedImmersion j.hom.hom.left R.inclusion.hom.hom.left)
  exact ⟨inv j, by rw [← hj, IsIso.inv_hom_id_assoc]⟩

private def rationalRootFunctional (D : BasedRootDatum.{u}) :
    D.X →+ ((ℚ ⊗[ℤ] D.Y) →ₗ[ℚ] ℚ) where
  toFun a := RootData.extendFunctional ℚ (D.datum.toLinearMap a)
  map_zero' := by simp [RootData.extendFunctional, LinearMap.baseChange_zero]
  map_add' a b := by
    simp [RootData.extendFunctional, LinearMap.baseChange_add, LinearMap.comp_add]

/-- Nonnegativity on simple roots gives dominance. If a positive root vanishes,
every simple summand vanishes. The opposite-root identity handles negative roots. -/
private theorem dominant_generic_of_simple {D : BasedRootDatum.{u}} {n : ℕ}
    (b : Fin n ≃ D.base.support) (x : ℚ ⊗[ℤ] D.Y)
    (W : Submodule ℚ (ℚ ⊗[ℤ] D.Y)) :
    let A := ApartmentRoots.split D.datum ℚ
    (∀ j, 0 ≤ A.root (b j) x ∧ (A.root (b j) x = 0 → ∀ y ∈ W, A.root (b j) y = 0)) →
    (∀ i, D.base.IsPos i → 0 ≤ A.root i x) ∧
      (∀ i, A.root i x = 0 → ∀ y ∈ W, A.root i y = 0) := by
  intro A hsimple
  let _ := D.finiteRoots
  let _ := D.datum.indexNeg
  let good (i : D.I) : Prop :=
    0 ≤ A.root i x ∧ (A.root i x = 0 → ∀ y ∈ W, A.root i y = 0)
  have hs (i : D.I) (hi : i ∈ D.base.support) : good i := by
    obtain ⟨j, hj⟩ := b.surjective ⟨i, hi⟩
    have he : (b j : D.I) = i := congrArg Subtype.val hj
    rw [← he]
    exact hsimple j
  have hp {i : D.I} (hi : D.base.IsPos i) : good i := by
    refine hi.induction_on_add hs (fun j k i he hj hk => ?_)
    have ha : A.root i = A.root j + A.root k := by
      change rationalRootFunctional D (D.datum.root i) = _
      rw [he, map_add]
      rfl
    have h₀ := hs k hk
    change 0 ≤ A.root i x ∧ (A.root i x = 0 → ∀ y ∈ W, A.root i y = 0)
    rw [ha]
    refine ⟨add_nonneg hj.1 h₀.1, fun hz y hy => ?_⟩
    obtain ⟨hjz, hkz⟩ := (add_eq_zero_iff_of_nonneg hj.1 h₀.1).mp hz
    change A.root j y + A.root k y = 0
    rw [hj.2 hjz y hy, h₀.2 hkz y hy, add_zero]
  refine ⟨fun i hi => (hp hi).1, fun i hi y hy => ?_⟩
  rcases RootPairing.Base.IsPos.or_neg D.base i with h | h
  · exact (hp h).2 hi y hy
  · change D.base.IsPos (D.datum.reflectionPerm i i) at h
    have hn : A.root (D.datum.reflectionPerm i i) = -A.root i := by
      change rationalRootFunctional D (D.datum.root (D.datum.reflectionPerm i i)) = _
      rw [D.datum.root_reflectionPerm, D.datum.reflection_apply_self, map_neg]
      rfl
    have hx : A.root (D.datum.reflectionPerm i i) x = 0 := by
      simp only [hn, LinearMap.neg_apply, hi, neg_zero]
    simpa only [hn, LinearMap.neg_apply, neg_eq_zero] using (hp h).2 hx y hy

/-- Clear a denominator in the localized lattice, squaring it to preserve signs. -/
private theorem exists_integral_multiple {Y : Type u} [AddCommGroup Y] (v : ℚ ⊗[ℤ] Y) :
    ∃ (d : ℚ) (z : Y), 0 < d ∧ d • v = (1 : ℚ) ⊗ₜ[ℤ] z := by
  obtain ⟨⟨z, d⟩, h⟩ := IsLocalizedModule.surj ℤ⁰ (TensorProduct.mk ℤ ℚ Y 1) v
  change (d : ℤ) • v = (1 : ℚ) ⊗ₜ[ℤ] z at h
  have hne : (d : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d.property
  have hd : ((d : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hne
  refine ⟨_, (d : ℤ) • z, mul_self_pos.mpr hd, ?_⟩
  rw [mul_smul]
  change (d : ℤ) • ((d : ℤ) • v) = _
  rw [h, TensorProduct.tmul_smul]

set_option backward.isDefEq.respectTransparency false in
/-- A dominant direction in the conjugated cocharacter image gives a minimal
parabolic and identifies the trivial simple-character restrictions. -/
theorem adaptedIndexParabolic : AdaptedIndexParabolic.{u} := by
  unfold AdaptedIndexParabolic
  intro F K _ _ _ D E M M' c C H f N L hStandard r hBound
  dsimp only
  intro hRank n b I g hg hTest
  obtain ⟨U, S, uK, hU, hu, _, hRankS, e, hComm, _, hBase, _, hRange, hParabolic⟩ := hStandard
  let _ := hComm
  let P := C.realization.pinned.pair
  let A := ApartmentRoots.split D.datum ℚ
  let s := (groupBaseChange F K).map S.inclusion ≫ uK.hom
  obtain ⟨a, ha, hCharacter, hParabolic⟩ := hParabolic g hg
  let sK := s ≫ a.hom
  let m := markedCocharacterMap C sK
  let W := LinearMap.range (m.baseChange ℚ)
  obtain ⟨hZero, y, hy, hPositive⟩ := hTest _ s hRange a ha
  obtain ⟨v, hv⟩ := (show y ∈ W from hy)
  obtain ⟨d, z, hd, hz⟩ := exists_integral_multiple v
  obtain ⟨cochar, hcochar⟩ := hBase.surjective z.toMul
  dsimp only at hcochar
  let x := (1 : ℚ) ⊗ₜ[ℤ] m (Additive.ofMul (e.hom ≫ (groupBaseChange F K).map cochar))
  have hx : x = d • y := by
    change (1 : ℚ) ⊗ₜ[ℤ] m (Additive.ofMul _) = _
    rw [hcochar]
    change (1 : ℚ) ⊗ₜ[ℤ] m z = _
    rw [← LinearMap.baseChange_tmul, ← hz, map_smul, hv]
  have hSimple (i : Fin n) : 0 ≤ A.root (b i) x ∧
      (A.root (b i) x = 0 → ∀ z ∈ W, A.root (b i) z = 0) := by
    by_cases hi : i ∈ I
    · have h := hZero i hi
      refine ⟨?_, fun _ => h⟩
      rw [hx, map_smul, h y hy, smul_zero]
    · have h : 0 < A.root (b i) x := by
        rw [hx, map_smul, smul_eq_mul]
        exact mul_pos hd (hPositive i hi)
      exact ⟨h.le, fun hz => (h.ne' hz).elim⟩
  obtain ⟨hDominant, hGeneric⟩ := dominant_generic_of_simple b x W hSimple
  obtain ⟨J, _, hSJ, hMinimal, jK, hjK⟩ := hParabolic cochar hDominant hGeneric
  let S₀ := subgroupOfSubgroup U S
  have hS : Nonempty (S₀.group ≅
      (StandardGroups.multiplicativePowerGroup F (ULift.{u} (Fin r))).val) := by
    change Nonempty (S.group ≅ _)
    rw [← hRank]
    exact hRankS
  have hMax := maximalSplitTorus_of_rank_bound hS hBound
  refine ⟨U, S₀, uK, hU, hMax, hS, ⟨S.inclusion, rfl⟩, hu,
    J.parabolic, sK, jK, hMinimal hMax, hSJ, ?_, hjK, ?_⟩
  · have hs : s ≫ P.T.inclusion = (groupBaseChange F K).map S₀.inclusion ≫ f.inv := by
      change ((groupBaseChange F K).map S.inclusion ≫ uK.hom) ≫ P.T.inclusion =
        (groupBaseChange F K).map (S.inclusion ≫ U.inclusion) ≫ f.inv
      apply (cancel_mono f.hom).mp
      simp only [Category.assoc, Functor.map_comp]
      rw [f.inv_hom_id, Category.comp_id]
      exact congrArg ((groupBaseChange F K).map S.inclusion ≫ ·) hu
    have hsScheme := congrArg
      (fun (h : (groupBaseChange F K).obj S.group ⟶ P.G.val) => h.hom.hom) hs
    change s.hom.hom ≫ P.T.inclusion.hom.hom =
      ((groupBaseChange F K).map S₀.inclusion ≫ f.inv).hom.hom at hsScheme
    change s.hom.hom ≫ (a.hom ≫ P.T.inclusion).hom.hom = _
    rw [ha]
    simp only [MonObj.comp_mul, GrpObj.comp_inv, comp_toUnit_assoc]
    let gs : ((groupBaseChange F K).obj S.group).X ⟶ P.G.val.X := toUnit _ ≫ g
    exact congrArg
      (fun (p : ((groupBaseChange F K).obj S.group).X ⟶ P.G.val.X) => gs * p * gs⁻¹)
      hsScheme
  · intro i
    rw [hCharacter (b i)]
    exact ⟨hZero i, fun h => by
      by_contra hi
      exact (hPositive i hi).ne' (h y hy)⟩

end LinearAlgebraicGroups.Arithmetic.ExceptionalInnerIndexParabolic
