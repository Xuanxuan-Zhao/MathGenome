import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagEulerCharacteristic
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.WeylDenominator
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagFixedPoints
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagLineBundle
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj BigOperators

universe u

namespace LinearAlgebraicGroups.Representation.FlagEulerCharacteristic

open _root_.LinearAlgebraicGroups.Specs
open Specs.AbstractPairing (Datum Root)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.BruhatOrbitParametrization (IsRepresentative)
open Specs.CharacterDescent (Character)
open Specs.DatumAndWeyl (Identification)
open Specs.EquivariantAffineModules (CharacterRing eChar)
open Specs.FlagEulerCharacteristic
open Specs.FlagFixedPoints
open Specs.FlagLocalizationGeometry (PositiveRoot cotangentWeight)
open Specs.FlagLineBundle (OppositeBorelPair)
open Specs.QuotientEmbedding (Presentation)
open Specs.WeylDenominator (GroupRing monomial positiveRoots rho denominator alternant onGroupRing weylSign)

open private rationalSectionsEquiv labelConjugation inducedConjugation_unique
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.DatumAndWeyl
open private representativeExists
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.BruhatOrbitParametrization
open private isReduced_of_smooth_over_field from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria

noncomputable section

set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

private theorem includeCharacters_eChar {T : GroupScheme k} (χ : Character T) :
    includeCharacters T (eChar χ) = monomial (2 • Additive.ofMul χ) := by
  simp [includeCharacters, eChar, MonoidAlgebra.of, AddMonoidAlgebra.mapDomainRingHom]

private theorem includeCharacters_injective (T : GroupScheme k)
    [Module.Free ℤ (Additive (Character T))] : Function.Injective (includeCharacters T) := by
  letI := HasUniqueDiv.of_isTorsionFree ℤ (Additive (Character T))
  have htwo : Function.Injective (fun x : Additive (Character T) => (2 : ℕ) • x) :=
    nsmul_right_injective (by decide)
  exact (AddMonoidAlgebra.mapDomain_injective (R := ℤ) htwo).comp
    (MonoidAlgebra.toAdditive ℤ (Character T)).injective

private theorem eChar_factor_ne_zero {T : GroupScheme k}
    [Module.Free ℤ (Additive (Character T))] (χ : Character T) (hχ : χ ≠ 1) :
    includeCharacters T (1 - eChar χ) ≠ 0 := by
  intro h
  have he := includeCharacters_injective T (h.trans (map_zero _).symm)
  have hcoeff := congrArg (fun c : CharacterRing T => c.coeff 1) (sub_eq_zero.mp he)
  simp [eChar, MonoidAlgebra.of, MonoidAlgebra.one_def, hχ] at hcoeff

private theorem root_ne_one {T : ClosedSubgroup G.val} (α : Root T) :
    α.val ≠ 1 :=
  α.property.1

/-- Compare the label actions through the common scheme normalizer. The comparison
also moves a given representative across presentations without changing its point in G. -/
private theorem transferRepresentative {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D E : Datum T} (J : Identification D) (K : Identification E)
    {w : D.rootDatum.weylGroup} {n : 𝟙_ (SchemeOver k) ⟶ J.normalizer.group.X}
    (hn : IsRepresentative J w n) :
    ∃ (v : E.rootDatum.weylGroup) (m : 𝟙_ (SchemeOver k) ⟶ K.normalizer.group.X),
      IsRepresentative K v m ∧
      m ≫ K.normalizer.inclusion.hom.hom = n ≫ J.normalizer.inclusion.hom.hom ∧
      (K.labelEquiv v).val = (J.labelEquiv w).val := by
  let g := n ≫ J.normalizer.inclusion.hom.hom
  have hg : Normalizes T.inclusion g :=
    (J.representsNormalizer _ g).mpr ⟨n, rfl⟩
  obtain ⟨m, hm⟩ := (K.representsNormalizer _ g).mp hg
  obtain ⟨e, he⟩ := rationalSectionsEquiv K.image.constantGroup
  let v := K.labelEquiv.symm (e.symm (m ≫ K.quotient.hom.hom))
  have hv : IsRepresentative K v m := by
    change m ≫ K.quotient.hom.hom = K.image.constantGroup.sectionPoint (K.labelEquiv v)
    simp only [v, MulEquiv.apply_symm_apply, ← he]
  have hj := labelConjugation J.image (J.labelEquiv w) n hn
  have hk := labelConjugation K.image (K.labelEquiv v) m hv
  rw [hm] at hk
  have hc := inducedConjugation_unique hk hj
  refine ⟨v, m, hv, hm, ?_⟩
  apply MulEquiv.ext
  intro χ
  rw [K.image.characterAction, J.image.characterAction, hc]

private theorem labelSubgroups_eq {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D E : Datum T} (J : Identification D) (K : Identification E)
    (hT : GeometricRadicals.IsSplitTorus T.group) :
    J.image.labels = K.image.labels := by
  have le {D E : Datum T} (J : Identification D) (K : Identification E) :
      J.image.labels ≤ K.image.labels := by
    intro x hx
    let w := J.labelEquiv.symm ⟨x, hx⟩
    obtain ⟨n, hn⟩ := representativeExists J hT w
    obtain ⟨v, _, _, _, hv⟩ := transferRepresentative J K hn
    have h : (K.labelEquiv v).val = x := by
      simpa only [w, MulEquiv.apply_symm_apply] using hv
    rw [← h]
    exact (K.labelEquiv v).property
  exact le_antisymm (le J K) (le K J)

private def weylLabelEquiv {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D E : Datum T} (J : Identification D) (K : Identification E)
    (hT : GeometricRadicals.IsSplitTorus T.group) :
    D.rootDatum.weylGroup ≃ E.rootDatum.weylGroup :=
  J.labelEquiv.toEquiv.trans <|
    (Equiv.subtypeEquivRight (fun x => Iff.of_eq
      (congrArg (fun H : Subgroup (MulAut (Character T.group)) => x ∈ H)
        (labelSubgroups_eq J K hT)))).trans K.labelEquiv.symm.toEquiv

private theorem weylLabelEquiv_label {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D E : Datum T} (J : Identification D) (K : Identification E)
    (hT : GeometricRadicals.IsSplitTorus T.group) (w : D.rootDatum.weylGroup) :
    (K.labelEquiv (weylLabelEquiv J K hT w)).val = (J.labelEquiv w).val := by
  simp [weylLabelEquiv, Equiv.subtypeEquivRight]

private theorem rootlessFlag {P : OppositeBorelPair G} (Q : Presentation P.negative)
    (hroot : IsEmpty (Root P.torus)) : Nonempty (Q.scheme ≅ 𝟙_ (SchemeOver k)) := by
  classical
  obtain ⟨hc, D, J, U, B, Rpos, Rneg, cochar, b, _, _, _, _, _, _, _, _, hreps, _, hcells⟩ :=
    Flag.BruhatCells.bruhatCells G P.reductive P.torus P.negative P.split P.maximal
      P.negativeBorel P.inNegative
  letI := hc
  choose n hn using hreps
  obtain ⟨a, _, ha⟩ := hcells Q
  obtain ⟨A, C, hC, _, _, hcover⟩ := ha n hn
  have hw (w : D.rootDatum.weylGroup) : w = 1 := by
    apply Subtype.ext
    have hempty : Set.range (RootPairing.Equiv.reflection D.rootDatum) = ∅ := by
      ext _
      exact ⟨fun ⟨i, _⟩ => hroot.false i, False.elim⟩
    have h := w.property
    change w.val ∈ Subgroup.closure (Set.range (RootPairing.Equiv.reflection D.rootDatum)) at h
    rw [hempty, Subgroup.closure_empty, Subgroup.mem_bot] at h
    exact h
  have hlen : SimpleRoots.wordLength D.rootDatum b 1 = 0 :=
    Nat.eq_zero_of_le_zero (Nat.sInf_le ⟨[], rfl, rfl⟩)
  obtain ⟨e⟩ := (hC 1).2.2
  rw [hlen] at e
  have he : (C 1).orbit ≅ 𝟙_ (SchemeOver k) := e
  let f := (C 1).orbitInclusion
  have hsurj : Set.range f.left = Set.univ := by
    rw [← hcover]
    ext x
    simp only [Set.mem_iUnion]
    refine ⟨fun hx => ⟨1, hx⟩, ?_⟩
    rintro ⟨w, hx⟩
    have h := hw w
    subst w
    exact hx
  haveI : Surjective f.left := ⟨Set.range_eq_univ.mp hsurj⟩
  haveI : IsImmersion f.left := (C 1).orbitImmersion
  haveI : IsClosedImmersion f.left :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [hsurj]; exact isClosed_univ)
  haveI : Smooth Q.scheme.hom :=
    ((FlagLineBundle.oppositeFlagGeometry k G P).2.2 Q).1
  haveI : IsReduced Q.scheme.left := isReduced_of_smooth_over_field Q.scheme.hom
  haveI : IsIso f.left := isIso_of_isClosedImmersion_of_surjective _
  exact ⟨(Over.isoMk (asIso f.left) (Over.w f)).symm ≪≫ he⟩

private theorem includeCharacters_cotangentProduct {P : OppositeBorelPair G}
    [IsCommMonObj P.torus.group.X] {D E : Datum P.torus}
    (J : Identification D) (K : Identification E)
    [Fintype (PositiveRoot P)] [Finite (Root P.torus)]
    (w : D.rootDatum.weylGroup) (v : E.rootDatum.weylGroup)
    (h : (J.labelEquiv w).val = (K.labelEquiv v).val) :
    includeCharacters P.torus.group (cotangentProduct J w) =
      onGroupRing E.rootDatum v (denominator E.rootDatum (subgroupRoots P.torus P.positive)) := by
  classical
  let S := subgroupRoots P.torus P.positive
  have hmem (i : Root P.torus) : i ∈ positiveRoots S ↔ i ∈ S := by
    simp [positiveRoots]
  rw [cotangentProduct, denominator, map_prod, map_prod]
  change (∏ α : PositiveRoot P, includeCharacters P.torus.group
    (1 - eChar ((J.labelEquiv w).val α.val.val⁻¹))) = _
  rw [← Finset.prod_subtype (positiveRoots S) hmem (fun α =>
    includeCharacters P.torus.group (1 - eChar ((J.labelEquiv w).val α.val⁻¹)))]
  apply Finset.prod_congr rfl
  intro α _
  have ha : v.val.weightEquiv (Additive.ofMul α.val) =
      Additive.ofMul ((J.labelEquiv w).val α.val) := by
    rw [K.characterAction, h]
  have hm (x : Additive (Character P.torus.group)) :
      onGroupRing E.rootDatum v (monomial x) = monomial (v.val.weightEquiv x) := by
    simp [onGroupRing]
  let e := v.val.weightEquiv.toAddEquiv.toAddMonoidHom
  rw [map_sub, map_one, map_sub, map_one, includeCharacters_eChar, hm, E.root_eq]
  change 1 - monomial ((2 : ℕ) • Additive.ofMul ((J.labelEquiv w).val α.val⁻¹)) =
    1 - monomial (e (-((2 : ℕ) • Additive.ofMul α.val)))
  rw [e.map_neg, map_nsmul e]
  change _ = 1 - monomial (-((2 : ℕ) • v.val.weightEquiv (Additive.ofMul α.val)))
  rw [ha]
  simp only [map_inv, ofMul_inv, smul_neg]

private theorem halfWeightMap {P : OppositeBorelPair G}
    [Module.Free ℤ (Additive (Character P.torus.group))]
    [IsDomain (GroupRing (Additive (Character P.torus.group)))] :
    ∃ f : LocalCharacterRing P.torus →+* FractionRing (GroupRing (Additive (Character P.torus.group))),
      ∀ c, f (localScalar P.torus c) =
        algebraMap _ _ (includeCharacters P.torus.group c) := by
  let A := GroupRing (Additive (Character P.torus.group))
  let g : CharacterRing P.torus.group →+* FractionRing A :=
    (algebraMap A _).comp (includeCharacters P.torus.group)
  have hg : ∀ x : rootFactors P.torus, IsUnit (g x) := by
    rintro ⟨x, hx⟩
    induction hx using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨α, rfl⟩ := hx
      apply isUnit_iff_ne_zero.mpr
      intro h
      apply eChar_factor_ne_zero α.val (root_ne_one α)
      apply IsFractionRing.injective A (FractionRing A)
      exact h.trans (map_zero _).symm
    | one => rw [map_one]; exact isUnit_one
    | mul x y hx hy ix iy => rw [map_mul]; exact ix.mul iy
  exact ⟨IsLocalization.lift hg, IsLocalization.lift_eq hg⟩

section Alternants

variable {I X Y F : Type*} [AddCommGroup X] [AddCommGroup Y] [Field F]
    (P : RootPairing I ℤ X Y) [Finite I] [Finite P.weylGroup] (S : Set I) (b : P.Base)

private theorem sum_to_alternant [Fintype P.weylGroup]
    (f : GroupRing X →+* F) (laws : WeylDenominator.Laws P S b) (x : X)
    (hdenom : f (alternant P b (rho P S)) ≠ 0)
    (hunit : ∀ w, f (onGroupRing P w (denominator P S)) ≠ 0) :
    (∑ w, f (monomial (w.val.weightEquiv x)) /
        f (onGroupRing P w (denominator P S))) =
      f (alternant P b (x + rho P S)) / f (alternant P b (rho P S)) := by
  classical
  let δ := fun w => f (onGroupRing P w (denominator P S))
  let A := f (alternant P b (rho P S))
  have hterm (w : P.weylGroup) :
      f (monomial (w.val.weightEquiv x)) / δ w =
      f (weylSign P b w • monomial (w.val.weightEquiv (x + rho P S))) / A := by
    rw [div_eq_div_iff (hunit w) hdenom, ← map_mul, ← map_mul]
    congr 1
    have hs : weylSign P b w * weylSign P b w = 1 := by
      rw [weylSign, ← mul_pow]
      norm_num
    have h := laws.shiftedDenominatorAction w
    have hm : onGroupRing P w (monomial (rho P S)) =
        monomial (w.val.weightEquiv (rho P S)) := by simp [onGroupRing]
    rw [map_mul, hm] at h
    rw [← laws.identity] at h
    have hmon (y z : X) : monomial y * monomial z = monomial (y + z) := by simp
    rw [map_add, ← hmon]
    calc
      monomial (w.val.weightEquiv x) * alternant P b (rho P S) =
          monomial (w.val.weightEquiv x) *
            (weylSign P b w • (weylSign P b w • alternant P b (rho P S))) := by
        rw [smul_smul, hs, one_smul]
      _ = _ := by rw [← h, mul_smul_comm, ← mul_assoc, smul_mul_assoc]
  have hAlt : ∑ w : P.weylGroup, weylSign P b w •
      monomial (w.val.weightEquiv (x + rho P S)) = alternant P b (x + rho P S) := by
    rw [alternant]
    congr 2
    exact Subsingleton.elim _ _
  simp_rw [show (fun w => f (monomial (w.val.weightEquiv x)) /
    f (onGroupRing P w (denominator P S))) =
    (fun w => f (weylSign P b w • monomial (w.val.weightEquiv (x + rho P S))) / A) from funext hterm]
  rw [← Finset.sum_div, ← map_sum, hAlt]

end Alternants

/-- The Weyl Euler characteristic formula for the associated line bundles on the
negative-Borel flag over the ground field. -/
theorem flagEulerCharacteristic : Statement.{u} := by
  classical
  intro k _ G P Q a ha
  let T := P.torus
  let S := subgroupRoots T P.positive
  obtain ⟨hc, D, J, hFin, hPos, hRep, hLoc⟩ :=
    FlagFixedPoints.flagLocalization P Q a ha
  letI := hc
  letI := hFin
  letI := hPos
  obtain ⟨_, E, ⟨K⟩, hW, hDen⟩ :=
    WeylDenominator.weylDenominator G P.reductive T P.split P.maximal
  letI := hW
  letI := E.finiteRoots
  letI := E.freeCharacters
  letI := halfWeightDomain T.group
  obtain ⟨_, _, _, hBorel, _, _, _⟩ :=
    RootData.BorelPositivity.borelPositivity G P.reductive T P.split P.maximal
  obtain ⟨⟨b, hb⟩, hLaws⟩ := hDen S (hBorel.1 P.positive P.positiveBorel P.inPositive)
  have laws := hLaws b hb
  let equiv := weylLabelEquiv J K P.split
  letI := Fintype.ofFinite E.rootDatum.weylGroup
  choose n hn using hRep
  obtain ⟨_, _, _, _, _, _, _, hPoints, _, _, _, _, hFixed⟩ := hLoc n hn
  refine ⟨hc, E, K, hW, E.finiteRoots, b, hb, representativeExists K P.split, rootlessFlag Q,
    ?_, (FlagLineBundle.oppositeFlagGeometry k G P).1, HomogeneousQuotient.quotientPullback Q, ?_⟩
  · intro w m hm
    dsimp only
    refine ⟨?_, ?_⟩
    · obtain ⟨v, l, hl, hpoint, hlabel⟩ := transferRepresentative K J hm
      let n' := Function.update n v l
      have hn' (q) : IsRepresentative J q (n' q) := by
        by_cases hq : q = v
        · subst q
          simpa [n'] using hl
        · simpa [n', Function.update_of_ne hq] using hn q
      have hcot := (hLoc n' hn').2.1 v
      have heq : cotangentWeight J v = cotangentWeight K w := by
        funext α
        change (J.labelEquiv v).val α.val.val⁻¹ = (K.labelEquiv w).val α.val.val⁻¹
        exact congrArg (fun e : MulAut (Character T.group) => e α.val.val⁻¹) hlabel
      simpa only [n', Function.update_self, Category.assoc, reassoc_of% hpoint, heq] using hcot
    · intro p χ L
      simpa only [HasAssociatedFiberWeight, Category.assoc] using
        FlagEquivariantEulerMap.weylFiberTransport K w m hm L
  · intro p χ h
    refine ⟨?_, ?_⟩
    · choose basis r hr using FlagCohomology.flagCohomologyRepresentation Q p χ h a ha
      obtain ⟨N, hN⟩ := (FlagCohomology.flagCohomologyFinite Q p χ h).2
      exact ⟨r, basis, N, hr, hN⟩
    · intro r basis hr N hN
      dsimp only
      let A := GroupRing (Additive (Character T.group))
      let j := algebraMap A (FractionRing A)
      have hDenom : j (alternant E.rootDatum b (rho E.rootDatum S)) ≠ 0 := by
        intro hz
        have hzero := IsFractionRing.injective A (FractionRing A) (hz.trans j.map_zero.symm)
        have hw := laws.leadingCoefficient
        rw [hzero] at hw
        simp at hw
      refine ⟨hDenom, ?_⟩
      obtain ⟨f, hf⟩ := halfWeightMap (P := P)
      let δ := fun q => localScalar T (cotangentProduct J q)
      have hu (q : D.rootDatum.weylGroup) : IsUnit (δ q) := (hPoints q).2.2.1
      have hδ (q : D.rootDatum.weylGroup) :
          f (δ q) = j (onGroupRing E.rootDatum (equiv q) (denominator E.rootDatum S)) := by
        rw [show f (δ q) = _ from hf _,
          includeCharacters_cotangentProduct J K q (equiv q) (weylLabelEquiv_label J K P.split q).symm]
      have hw (q : D.rootDatum.weylGroup) :
          f (localScalar T (eChar ((J.labelEquiv q).val χ))) =
            j (monomial ((equiv q).val.weightEquiv (2 • Additive.ofMul χ))) := by
        let g := (equiv q).val.weightEquiv.toAddEquiv.toAddMonoidHom
        rw [hf, includeCharacters_eChar]
        change _ = j (monomial (g ((2 : ℕ) • Additive.ofMul χ)))
        rw [map_nsmul g]
        change _ = j (monomial ((2 : ℕ) •
          (equiv q).val.weightEquiv (Additive.ofMul χ)))
        rw [K.characterAction, weylLabelEquiv_label J K P.split q]
      have hnonzero (v : E.rootDatum.weylGroup) :
          j (onGroupRing E.rootDatum v (denominator E.rootDatum S)) ≠ 0 := by
        let q := equiv.symm v
        have hq := hδ q
        rw [Equiv.apply_symm_apply] at hq
        exact hq ▸ ((hu q).map f).ne_zero
      have hsum := congrArg f (hFixed p χ h r basis hr N hN)
      change f (localScalar T (FlagCohomology.equivariantEulerCharacteristic h r N)) =
        f (∑ q, localScalar T (eChar ((J.labelEquiv q).val χ)) * Ring.inverse (δ q)) at hsum
      rw [hf, map_sum] at hsum
      calc
        _ = ∑ q : D.rootDatum.weylGroup,
            j (monomial ((equiv q).val.weightEquiv (2 • Additive.ofMul χ))) /
              j (onGroupRing E.rootDatum (equiv q) (denominator E.rootDatum S)) := by
          rw [hsum]
          apply Finset.sum_congr rfl
          intro q _
          rw [map_mul, (hu q).map_ringInverse f, Ring.inverse_eq_inv, hw, hδ, div_eq_mul_inv]
        _ = ∑ v : E.rootDatum.weylGroup,
            j (monomial (v.val.weightEquiv (2 • Additive.ofMul χ))) /
              j (onGroupRing E.rootDatum v (denominator E.rootDatum S)) :=
          Equiv.sum_comp equiv (fun v =>
            j (monomial (v.val.weightEquiv (2 • Additive.ofMul χ))) /
              j (onGroupRing E.rootDatum v (denominator E.rootDatum S)))
        _ = _ := sum_to_alternant E.rootDatum S b j laws (2 • Additive.ofMul χ) hDenom hnonzero

end

end LinearAlgebraicGroups.Representation.FlagEulerCharacteristic
