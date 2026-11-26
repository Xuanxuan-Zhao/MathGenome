import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalSingletonRootSL2
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RelativeReflections
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalRootGroupDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalRankOneNormalization
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalRankOneEmbeddingDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalRankOneMatrixWitnesses
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Matrix

universe u

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalSingletonRootSL2

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup GroupScheme)
open Specs.AbstractPairing (Root)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Character Cocharacter compositionPairing)
open Specs.CharacterPairing (absoluteRoots characterValue pairing)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open Specs.ExceptionalSingletonRootSL2
open Specs.GeometricRadicals (GeometricGroup IsReductive IsSemisimple IsSplitTorus
  geometricSolvableRadical)
open Specs.RootGroups (AdditiveLine HasScalarAction IsRootSubgroup
  rootPoint)
open Specs.SchemeDerivedGroup (IsSolvable)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected corootLattice)
open Specs.Unipotent (Index baseChangedAlgebraicGroup)
open private precomposeCharacter splitEndomorphism_ext
  powerMorphism_eq_zpow
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RelativeReflections
open private splitTorus_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private groupBaseChangeTower radical_transport solvable_of_iso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private centralIsogeny_baseChange centralIsogeny_postIso isIso_of_scalarExtension
  torusIso_of_isIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice

noncomputable section

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F}

local notation "Fsep" => SeparableClosure F
local notation "Gm[" K "]" => specGroup (groupAlgebra K IntegerCharacters)

private abbrev MultiplicativeComparison (F : Type u) [Field F] :=
  Gm[SeparableClosure F] ≅ (groupBaseChange F (SeparableClosure F)).obj Gm[F]

private abbrev extendCocharacter (e : MultiplicativeComparison F) {T : GroupScheme F}
    (c : Cocharacter T) : Cocharacter ((groupBaseChange F Fsep).obj T) :=
  e.hom ≫ (groupBaseChange F Fsep).map c

open private factor_of_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private factor_group_through_subgroup
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private cocharacterFactorsThroughMaximalSplit
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.MaximalSplitTori
open private inclusion_mono from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate

set_option maxHeartbeats 900000 in
/-- A rational diagonal whose scalar extension is the absolute coroot
factors first through the rational maximal torus and then through the
specified maximal split torus. -/
private theorem diagonalFactorsThroughSplitTorus (A : MarkedTori G) (α : Root A.P.T)
    (e : MultiplicativeComparison F) (c : Cocharacter G.val)
    (hc : extendCocharacter e c =
      Additive.toMul (A.datum.toBased.datum.coroot α) ≫ A.P.T.inclusion ≫ A.ambient.hom) :
    ∃ d : Cocharacter A.S.group, d ≫ A.S.inclusion = c ∧
      extendCocharacter e d ≫ A.splitInAbsolute =
        Additive.toMul (A.datum.toBased.datum.coroot α) := by
  let E := groupBaseChange F Fsep
  let q := Additive.toMul (A.datum.toBased.datum.coroot α)
  let p := e.inv ≫ q ≫ A.torus.inv
  have hp : p ≫ E.map A.T.inclusion = E.map c := by
    change (e.inv ≫ q ≫ A.torus.inv) ≫ E.map A.T.inclusion = _
    rw [← A.torus_eq]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    have he := congrArg (e.inv ≫ ·) hc
    change e.inv ≫ e.hom ≫ E.map c = e.inv ≫ q ≫ A.P.T.inclusion ≫ A.ambient.hom at he
    rw [e.inv_hom_id_assoc] at he
    exact he.symm
  letI := A.T.isClosedImmersion
  obtain ⟨s, hs⟩ := factor_of_baseChange Fsep c.hom.hom A.T.inclusion.hom.hom
    p.hom.hom (congrArg (Grp.forget (SchemeOver Fsep)).map hp)
  obtain ⟨t, ht⟩ := factor_group_through_subgroup A.T c s hs
  obtain ⟨d, hd⟩ := cocharacterFactorsThroughMaximalSplit G A.S A.T A.maximalSplit
    A.maximalTorus.1 A.intoTorus A.intoTorus_eq t
  have hdi : d ≫ A.S.inclusion = c := by
    rw [← A.intoTorus_eq, ← Category.assoc, hd, ht]
  refine ⟨d, hdi, ?_⟩
  letI := inclusion_mono A.P.T
  apply (cancel_mono (A.P.T.inclusion ≫ A.ambient.hom)).mp
  calc
    (extendCocharacter e d ≫ A.splitInAbsolute) ≫ A.P.T.inclusion ≫ A.ambient.hom =
        e.hom ≫ E.map d ≫ E.map A.intoTorus ≫ E.map A.T.inclusion := by
      unfold extendCocharacter MarkedTori.splitInAbsolute
      simp only [Category.assoc, A.torus_eq]
      rfl
    _ = extendCocharacter e c := by
      rw [← E.map_comp, A.intoTorus_eq, ← E.map_comp, hdi]
    _ = q ≫ A.P.T.inclusion ≫ A.ambient.hom := hc

private theorem semisimpleOfIso {P Q : AffineAlgebraicGroup F} (e : P.val ≅ Q.val)
    (hP : IsReductive P) (hQ : IsSemisimple Q) : IsSemisimple P := by
  let f : (GeometricGroup P).val ≅ (GeometricGroup Q).val :=
    (groupBaseChange F (AlgebraicClosure F)).mapIso e
  let N := geometricSolvableRadical P
  have hN := GeometricRadicals.geometricSolvableRadicalLargest P
  have hM := GeometricRadicals.geometricSolvableRadicalLargest Q
  have ht := radical_transport f (fun J ↦ IsSolvable J.val)
    (fun d hx hy ↦ solvable_of_iso d hx.1 hx.2.1 hy.1 hy.2.1) N hN
  obtain ⟨i, _, _⟩ := GeometricRadicals.radicalUnique (GeometricGroup Q) _ ht hM
  obtain ⟨j⟩ := hQ.2.2
  exact ⟨hP.1, hP.2.1, ⟨i ≪≫ j⟩⟩

set_option maxHeartbeats 1100000 in
/-- Applying geometric simple connectedness to the scalar extension of the
split coroot cover gives the full lattice on the marked torus. -/
private theorem fullCorootLattice (A : MarkedTori G) (hG : IsSemisimple G)
    (hsc : GeometricallySimplyConnected G) : corootLattice A.datum = ⊤ := by
  let K := AlgebraicClosure F
  have hGsep := (Reductive.RadicalBaseChange.semisimpleFieldExtension
    (K := Fsep) G hG.1 hG.2.1).mpr hG
  have hP : IsSemisimple A.P.G :=
    semisimpleOfIso (Q := baseChangedAlgebraicGroup Fsep G) A.ambient A.P.reductive hGsep
  let D := A.datum
  letI := D.comm
  obtain ⟨P, E, f, τ, hP', _, hf, hτ, _, e, he⟩ :=
    Classification.SimplyConnectedLattice.splitCover A.P.G hP A.P.T A.P.split A.P.maximal D.datum
  letI := E.comm
  let B := groupBaseChange Fsep K
  let i : B.obj A.P.G.val ≅ (GeometricGroup G).val :=
    B.mapIso A.ambient ≪≫ ((groupBaseChangeTower (k := F) (K := Fsep) K).app G.val).symm
  have hPK : IsSemisimple (baseChangedAlgebraicGroup K P.G) :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := K) P.G hP'.1 hP'.2.1).mpr hP'
  have hh : IsIso (B.map f ≫ i.hom) :=
    hsc (baseChangedAlgebraicGroup K P.G) hPK _
      (centralIsogeny_postIso i (centralIsogeny_baseChange K P f hf))
  letI := hh
  have hi : IsIso f :=
    isIso_of_scalarExtension K f (IsIso.of_isIso_comp_right (B.map f) i.hom)
  letI := hi
  haveI : IsIso τ := torusIso_of_isIso P A.P f τ hτ
  apply eq_top_iff.mpr
  intro y _
  have hy := (e (Additive.ofMul (Additive.toMul y ≫ inv τ))).property
  rwa [he, Category.assoc, IsIso.inv_hom_id, Category.comp_id] at hy

/-- In a full coroot lattice, primitivity is witnessed by a character with
composition exponent one. -/
private theorem primitiveAttachedCoroot (A : MarkedTori G) (α : Root A.P.T)
    (h : corootLattice A.datum = ⊤) :
    ∃ χ : Character A.P.T.group,
      pairing A.P.T.group χ (Additive.toMul (A.datum.toBased.datum.coroot α)) = 1 := by
  let D := A.datum
  letI := D.comm
  obtain ⟨x, hx⟩ := IntegralFibreReductivity.primitiveCoroots D.toBased h α
  refine ⟨Additive.toMul x, ?_⟩
  rw [← D.datum.pairing_eq]
  exact hx

/-- The reflection as an actual morphism of the torus, using multiplication
by the inverse of the character followed by the coroot. -/
private def torusReflectionMap {k : Type u} [Field k] {T : GroupScheme k}
    [IsCommMonObj T.X] (a : Character T) (c : Cocharacter T) : T ⟶ T :=
  (𝟙 T) * (a ≫ c)⁻¹

private theorem torusReflectionMap_character {k : Type u} [Field k] {T : GroupScheme k}
    [IsCommMonObj T.X] (a χ : Character T) (c : Cocharacter T) :
    torusReflectionMap a c ≫ χ = χ * a ^ (-pairing T χ c) := by
  let n := pairing T χ c
  have h : c ≫ χ = (𝟙 Gm[k] : Character Gm[k]) ^ n := by
    rw [← powerMorphism_eq_zpow]
    exact ((RootData.CharacterPairing.characterPairingComposition T χ c).1 n).mpr rfl
  have h' : (a ≫ c) ≫ χ = a ^ n := by
    rw [Category.assoc, h]
    exact ((precomposeCharacter a).map_zpow (𝟙 Gm[k]) n).trans (by
      change ((a ≫ 𝟙 Gm[k]) ^ n) = _
      rw [Category.comp_id])
  have h'' : torusReflectionMap a c ≫ χ = χ * ((a ≫ c) ≫ χ)⁻¹ := by
    apply Grp.hom_ext
    change ((𝟙 T.X) * ((a ≫ c).hom.hom)⁻¹) ≫ χ.hom.hom =
      χ.hom.hom * (((a ≫ c) ≫ χ).hom.hom)⁻¹
    simp only [MonObj.mul_comp, Category.id_comp, GrpObj.inv_comp, Grp.comp_hom_hom]
  rw [h'', h', zpow_neg]

/-- The pairing value two makes the scheme morphism an involution. -/
private theorem torusReflectionMap_involutive {k : Type u} [Field k] {T : GroupScheme k}
    [IsCommMonObj T.X] (hT : IsSplitTorus T) (a : Character T) (c : Cocharacter T)
    (hc : pairing T a c = 2) :
    torusReflectionMap a c ≫ torusReflectionMap a c = 𝟙 T := by
  let r := torusReflectionMap a c
  have h : r ≫ a = a⁻¹ := by
    rw [torusReflectionMap_character, hc]
    change a * a ^ (-2 : ℤ) = a⁻¹
    calc
      _ = a ^ ((1 : ℤ) + -2) := by rw [zpow_add, zpow_one]
      _ = _ := by norm_num
  apply splitEndomorphism_ext hT
  intro χ
  let n := -pairing T χ c
  calc
    (r ≫ r) ≫ χ = r ≫ (χ * a ^ n) := by
      rw [Category.assoc]
      exact congrArg (r ≫ ·) (torusReflectionMap_character a χ c)
    _ = (r ≫ χ) * (r ≫ a) ^ n := by
      exact ((precomposeCharacter r).map_mul χ (a ^ n)).trans (by
        rw [(precomposeCharacter r).map_zpow]
        rfl)
    _ = 𝟙 T ≫ χ := by
      rw [Category.id_comp, torusReflectionMap_character, h, inv_zpow]
      exact mul_inv_cancel_right χ (a ^ n)

/-- An actual torus conjugation realizing the character reflection also
realizes its dual on cocharacters. -/
private theorem cocharacterReflectionOfCharacterReflection (A : MarkedTori G)
    (α : Root A.P.T) (c : A.P.T.group ≅ A.P.T.group)
    (hc : ∀ χ : Character A.P.T.group,
      Additive.ofMul (c.inv ≫ χ) = A.datum.toBased.datum.reflection α (Additive.ofMul χ))
    (cochar : Cocharacter A.P.T.group) :
    Additive.ofMul (cochar ≫ c.hom) =
      A.datum.toBased.datum.coreflection α (Additive.ofMul cochar) := by
  let D := A.datum
  letI := D.comm
  let P := D.datum.rootDatum
  let q := P.toLinearMap
  change Additive.ofMul (cochar ≫ c.hom) = P.coreflection α (Additive.ofMul cochar)
  apply q.flip.toPerfPair.injective
  ext x
  let χ : Character A.P.T.group := Additive.toMul x
  change q (Additive.ofMul χ) (Additive.ofMul (cochar ≫ c.hom)) =
    q (Additive.ofMul χ) (P.coreflection α (Additive.ofMul cochar))
  have hχ : Additive.ofMul (c.hom ≫ χ) = P.reflection α (Additive.ofMul χ) := by
    have he := hc (c.hom ≫ χ)
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at he
    exact ((congrArg (P.reflection α) he).trans (P.reflection_same α _)).symm
  have hq : q (Additive.ofMul χ) (Additive.ofMul (cochar ≫ c.hom)) =
      q (Additive.ofMul (c.hom ≫ χ)) (Additive.ofMul cochar) := by
    dsimp only [q, P]
    rw [D.datum.pairing_eq, D.datum.pairing_eq]
    unfold pairing compositionPairing
    rw [Category.assoc]
  rw [hq, hχ]
  rw [RootPairing.reflection_apply, RootPairing.coreflection_apply]
  change q (Additive.ofMul χ - q (Additive.ofMul χ) (P.coroot α) • P.root α)
      (Additive.ofMul cochar) =
    q (Additive.ofMul χ) (Additive.ofMul cochar - q (P.root α) (Additive.ofMul cochar) • P.coroot α)
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

section AbsoluteRankOne

open Specs.IntegralSemisimpleModel (IntegralMarking Model TorusValues cocharacter fibre
  forgetFibrePoint integerAlgebra torusPoint)
open Specs.IntegralRootRelations (diagonal lower upper)
open Specs.Pinning (BasedIso PinnedGroup RootCoordinate SplitBorelPair)
open CocharacterDynamics (cocharacterPoint)
open private pinnedLift pushScalarAction from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence
open private fibrePointsEquiv forgetFibrePoint_comp rankOneFibre rankOneFibre_apply restrictToIntegers
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private transportSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private normalizes_of_scalarAction from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedUniqueness
open private rootPoint_comp hom_ext_on_affine_tests tangent_weight_of_scalarAction characterValue_eq_unit characterUnit
  characterUnit_point characterUnit_inv
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private unitEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

open private exists_rankOne_pivots_after_injective_extension rankOne_pivot_factorization
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRankOneExtension
open private mapPoints_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RankOneRelations

/-- Compare the standard size-two group scheme with the rank-one point
functor indexed by `Fin 2` in the integral model. -/
private def rankOnePointsIso (k : Type u) [Field k] :
    (groupPointsFunctor k).obj (StandardGroups.specialLinearGroup k (Index.{u} 2)).val ≅
      Specs.IntegralFibreReductivity.rankOnePoints k :=
  ExceptionalRankOneMatrixWitnesses.standardMatrix k ≪≫
    NatIso.ofComponents
      (fun R ↦ (Specs.ExceptionalRankOneMatrixWitnesses.liftMatrix (R := R)).symm.toGrpIso)
      (by
        intro R S f
        apply GrpCat.ext
        intro m
        apply Subtype.ext
        ext i j
        rfl)

/-- The rank-one map of the integral fibre and any transport of it by a
marked isomorphism are represented by scheme morphisms. -/
private theorem representedRankOneHomomorphism {k : Type u} [Field k] {J : GroupScheme k}
    (ρ : Specs.IntegralFibreReductivity.rankOnePoints k ⟶ (groupPointsFunctor k).obj J) :
    ∃ f : (StandardGroups.specialLinearGroup k (Index.{u} 2)).val ⟶ J,
      (groupPointsFunctor k).map f = (rankOnePointsIso k).hom ≫ ρ :=
  (groupHomComparison k _ J (StandardGroups.specialLinearGroup k (Index.{u} 2)).property.1).surjective
    ((rankOnePointsIso k).hom ≫ ρ)

/-- It suffices to check injectivity on the top-left pivot chart. Two
test-algebra matrices enter that chart after a common injective extension and
a common upper transvection. -/
private theorem rankOneInjectiveOfPivot {k : Type u} [Field k] {J : GroupScheme k}
    (ρ : Specs.IntegralFibreReductivity.rankOnePoints k ⟶ (groupPointsFunctor k).obj J)
    (hρ : ∀ (S : TestAlgebra k) (m n : Matrix.SpecialLinearGroup (Fin 2) S),
      IsUnit (m.val 0 0) → IsUnit (n.val 0 0) →
        ρ.app S m = ρ.app S n → m = n) :
    ∀ R, Function.Injective (ρ.app R) := by
  intro R m n h
  obtain ⟨B, _, f, t, hfinj, hpivot⟩ :=
    exists_rankOne_pivots_after_injective_extension ([m, n] :
      List (Matrix.SpecialLinearGroup (Fin 2) R))
  letI : Algebra k B := (f.comp (algebraMap k R)).toAlgebra
  let S : TestAlgebra k := CommAlgCat.of k B
  let a : R ⟶ S := CommAlgCat.ofHom
    ({ toRingHom := f, commutes' := fun _ ↦ rfl } : R →ₐ[k] B)
  let M := Matrix.SpecialLinearGroup.map f m
  let N := Matrix.SpecialLinearGroup.map f n
  have hm : ρ.app S M = mapPoints a (ρ.app R m) :=
    ConcreteCategory.congr_hom (ρ.naturality a) m
  have hn : ρ.app S N = mapPoints a (ρ.app R n) :=
    ConcreteCategory.congr_hom (ρ.naturality a) n
  have hMN : ρ.app S (upper t * M) = ρ.app S (upper t * N) := by
    simp only [map_mul, hm, hn, h]
  have hm' : IsUnit ((upper t * M).val 0 0) := hpivot m (by simp)
  have hn' : IsUnit ((upper t * N).val 0 0) := hpivot n (by simp)
  have eq : M = N := mul_left_cancel (hρ S _ _ hm' hn' hMN)
  apply Subtype.ext
  ext i j
  exact hfinj (congrArg (fun x => x.val i j) eq)

/-- A group homomorphism injective on all affine test points is a closed
immersion, by its faithfully flat factorization through its scheme image. -/
private theorem closedImmersionOfInjectivePoints {k : Type u} [Field k]
    {P Q : AffineAlgebraicGroup k} (f : P.val ⟶ Q.val)
    (h : ∀ R : TestAlgebra k, Function.Injective (fun x : Points P.val.X R ↦ x ≫ f.hom.hom)) :
    IsClosedImmersion f.hom.hom.left := by
  obtain ⟨I, p, i, ⟨hp, hflat, hsurj, _, ha, hi⟩, _, _⟩ := schemeImageFactorization P Q f
  haveI : Mono p.hom.hom := ⟨fun a b hab ↦ by
    apply hom_ext_on_affine_tests
    intro R x
    apply h R
    rw [← hp, Grp.comp_hom_hom]
    exact congrArg (· ≫ i.hom.hom)
      (by simpa only [Category.assoc] using congrArg (x ≫ ·) hab)⟩
  letI : Flat p.hom.hom.left := hflat
  letI : Surjective p.hom.hom.left := hsurj
  letI : IsAffineHom p.hom.hom.left := ha
  letI : IsIso p.hom.hom.left := Flat.isIso_of_surjective_of_mono _
  letI : IsClosedImmersion i.hom.hom.left := hi
  rw [← hp]
  change IsClosedImmersion (p.hom.hom.left ≫ i.hom.hom.left)
  infer_instance

open private elementaryWord rankOneWord_reflection
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization

set_option maxHeartbeats 800000 in
/-- Evaluating the normalized anti-diagonal conjugation on the marked torus
gives the reflection morphism on every test algebra. -/
private theorem rankOneWordConjugates {k : Type u} [Field k] {J : GroupScheme k}
    (T : ClosedSubgroup J) [IsCommMonObj T.group.X]
    (a : Character T.group) (c : Cocharacter T.group)
    {L : AdditiveLine k} {x y : L.group ⟶ J}
    (ρ : Specs.IntegralFibreReductivity.rankOnePoints k ⟶ (groupPointsFunctor k).obj J)
    (hx : HasScalarAction T a x) (hy : HasScalarAction T a⁻¹ y)
    (hp : ∀ (R : TestAlgebra k) (z : R), ρ.app R (upper z) = rootPoint x R z)
    (hn : ∀ (R : TestAlgebra k) (z : R), ρ.app R (lower z) = rootPoint y R z)
    (hc : ∀ (R : TestAlgebra k) (b : Rˣ),
      ρ.app R (diagonal b) = cocharacterPoint c R b ≫ T.inclusion.hom.hom)
    (R : TestAlgebra k) (t : GroupPoints T.group R) :
    let w : GroupPoints J R := ρ.app R (elementaryWord (1 : Rˣ))
    let g : GroupPoints J R := t ≫ T.inclusion.hom.hom
    w * g * w⁻¹ = t ≫ (torusReflectionMap a c ≫ T.inclusion).hom.hom := by
  let g : GroupPoints J R := t ≫ T.inclusion.hom.hom
  let b := characterUnit a R t
  have hpos (z : R) : g * ρ.app R (upper z) * g⁻¹ =
      ρ.app R (upper ((b : R) * z)) := by
    simp only [hp]
    simpa only [g, b, characterValue_eq_unit] using hx R t z
  have hneg (z : R) : g * ρ.app R (lower z) * g⁻¹ =
      ρ.app R (lower ((↑b⁻¹ : R) * z)) := by
    simp only [hn]
    simpa only [g, b, characterValue_eq_unit, characterUnit_inv] using hy R t z
  have hcom : Commute g (ρ.app R (diagonal b)) := by
    rw [hc]
    let V := (testSpec k).obj (op R)
    let p : V ⟶ T.group.X := t
    let q : V ⟶ T.group.X := cocharacterPoint c R b
    exact (Commute.all p q).map (IsMonHom.monoidHom T.inclusion.hom.hom V)
  have he := rankOneWord_reflection ((ρ.app R).hom) g b hpos hneg hcom
  refine he.trans ?_
  change g * (ρ.app R (diagonal b))⁻¹ = _
  rw [hc R b]
  have hcochar : cocharacterPoint c R b = t ≫ (a ≫ c).hom.hom := by
    change CocharacterDynamics.unitPoint R b ≫ c.hom.hom = _
    rw [characterUnit_point, Grp.comp_hom_hom, Category.assoc]
  rw [hcochar]
  change (t ≫ T.inclusion.hom.hom) * ((t ≫ (a ≫ c).hom.hom) ≫ T.inclusion.hom.hom)⁻¹ =
    (t ≫ ((𝟙 T.group.X) * ((a ≫ c).hom.hom)⁻¹)) ≫ T.inclusion.hom.hom
  rw [MonObj.comp_mul, Category.comp_id, GrpObj.comp_inv, MonObj.mul_comp,
    GrpObj.inv_comp]

/-- Transporting a root coordinate along a marked isomorphism gives a root
coordinate on the transported closed subgroup for the inverse pullback character. -/
private theorem transportedRootCoordinate {k : Type u} [Field k] {P Q : SplitBorelPair k}
    {L : AdditiveLine k} {U : ClosedSubgroup P.G.val} {χ : Character P.T.group}
    (hU : IsRootSubgroup P.T U χ) (x : RootCoordinate L P.T U χ)
    (f : P.G.val ≅ Q.G.val) (t : P.T.group ≅ Q.T.group)
    (ht : P.T.inclusion ≫ f.hom = t.hom ≫ Q.T.inclusion) :
    IsRootSubgroup Q.T (transportSubgroup f U) (t.inv ≫ χ) ∧
      HasScalarAction Q.T (t.inv ≫ χ) (x.val.hom ≫ U.inclusion ≫ f.hom) := by
  have hs := pushScalarAction (A := L) (P := P) (Q := Q) f t ht _ _ x.property
  refine ⟨⟨hU.1, hU.2.1, ?_, ?_⟩, hs⟩
  · exact normalizes_of_scalarAction Q.G.property.1 x.val hs
  · exact tangent_weight_of_scalarAction Q.T (transportSubgroup f U) _ L x.val hs

section IntegralGaussCell

open Specs.IntegralSemisimpleModel (Integers IntegralAlgebra IntegralPoints
  additivePoint cellMap integralSpec)
open Specs.OrderedRootProducts (Enumerates)
open Specs.Pinning (BasedRootDatum)
open private orderedFactorPoint orderedFactorPoint_eq integralRootFactorsIso
  integralRootProduct_evaluation additivePoint_zero lift_mul_three_factors
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

private def integralRootSection {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (i : D.I) (R : IntegralAlgebra.{u}) (x : R) : IntegralPoints M.group R :=
  M.line.point R x ≫ (M.root i).hom.hom

private theorem integralRootSection_zero {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (i : D.I) (R : IntegralAlgebra.{u}) : integralRootSection M i R 0 = 1 := by
  letI := M.line.operations
  calc
    integralRootSection M i R 0 = (1 : IntegralPoints M.line.group R) ≫ (M.root i).hom.hom :=
      congrArg (· ≫ (M.root i).hom.hom) (additivePoint_zero M.line R)
    _ = _ := (IsMonHom.monoidHom (M.root i).hom.hom _).map_one

private theorem integralAdditivePoint_injective (R : IntegralAlgebra.{u}) :
    Function.Injective (additivePoint R) := by
  intro x y h
  have e := (algSpec.fullyFaithful (R := CommRingCat.of Integers.{u})).map_injective h
  let P := CommAlgCat.of Integers.{u} (Polynomial Integers.{u})
  have ee : CommAlgCat.ofHom (Y := R) (Polynomial.aeval x : Polynomial Integers.{u} →ₐ[_] R) =
      CommAlgCat.ofHom (Y := R) (Polynomial.aeval y : Polynomial Integers.{u} →ₐ[_] R) :=
    Quiver.Hom.op_inj e
  have hxy := congrArg (fun f : P ⟶ R ↦ f.hom Polynomial.X) ee
  exact (Polynomial.aeval_X (R := Integers.{u}) x).symm.trans
    (hxy.trans (Polynomial.aeval_X (R := Integers.{u}) y))

/-- A coordinate character with pairing one detects the diagonal parameter
on the entire marked torus, including all test rings. -/
private theorem integralCorootPoint_injective (D : BasedRootDatum.{u}) (d : D.Y)
    (χ : D.X) (hχ : D.datum.toLinearMap χ d = 1) (R : IntegralAlgebra.{u}) :
    Function.Injective (fun t : Rˣ ↦ torusPoint D R (cocharacter D d R t)) := by
  intro a b h
  have e := (algSpec.fullyFaithful (R := CommRingCat.of Integers.{u})).map_injective h
  let A := CommAlgCat.of Integers.{u} (MonoidAlgebra Integers.{u} (Multiplicative D.X))
  let evaluation (t : Rˣ) : A ⟶ R := CommAlgCat.ofHom
    (MonoidAlgebra.lift Integers.{u} R (Multiplicative D.X)
      ((Units.coeHom R).comp (cocharacter D d R t)))
  let m : A := MonoidAlgebra.single (Multiplicative.ofAdd χ) 1
  have he := congrArg (fun f : A ⟶ R ↦ f.hom m)
    (show evaluation a = evaluation b from Quiver.Hom.op_inj e)
  have ev (t : Rˣ) : (evaluation t).hom m = (t : R) := by
    change (MonoidAlgebra.lift Integers.{u} R (Multiplicative D.X)
      ((Units.coeHom R).comp (cocharacter D d R t)))
      (MonoidAlgebra.single (Multiplicative.ofAdd χ) 1) = _
    rw [MonoidAlgebra.lift_single, Algebra.smul_def, map_one, one_mul]
    change ((t ^ D.datum.toLinearMap χ d : Rˣ) : R) = _
    rw [hχ, zpow_one]
  exact Units.ext ((ev a).symm.trans (he.trans (ev b)))

set_option maxHeartbeats 1000000 in
/-- The marked multiplication cell separates the two opposite root
parameters and the diagonal parameter. -/
private theorem integralGaussParameters {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (i j : D.I) (hi : ¬ D.base.IsPos i) (hj : D.base.IsPos j)
    (d : D.Y) (χ : D.X) (hχ : D.datum.toLinearMap χ d = 1)
    (R : IntegralAlgebra.{u}) {l₁ l₂ r₁ r₂ : R} {b₁ b₂ : Rˣ}
    (h : integralRootSection M i R l₁ *
        (torusPoint D R (cocharacter D d R b₁) ≫ M.torus.hom.hom) *
        integralRootSection M j R r₁ =
      integralRootSection M i R l₂ *
        (torusPoint D R (cocharacter D d R b₂) ≫ M.torus.hom.hom) *
        integralRootSection M j R r₂) :
    l₁ = l₂ ∧ b₁ = b₂ ∧ r₁ = r₂ := by
  classical
  letI := D.finiteRoots
  letI := Fintype.ofFinite D.I
  let neg : List D.I := ({a | ¬ D.base.IsPos a} : Finset D.I).toList
  let pos : List D.I := ({a | D.base.IsPos a} : Finset D.I).toList
  have hneg : Enumerates neg {a | ¬ D.base.IsPos a} := ⟨Finset.nodup_toList _, by simp [neg]⟩
  have hpos : Enumerates pos {a | D.base.IsPos a} := ⟨Finset.nodup_toList _, by simp [pos]⟩
  have him : i ∈ neg := (hneg.2 i).mpr hi
  have hjm : j ∈ pos := (hpos.2 j).mpr hj
  let a (k : D.I) (x : R) (l : List D.I) := orderedFactorPoint
    (fun z ↦ additivePoint R (if z = k then x else 0)) l
  let q (l r : R) (b : Rˣ) :=
    lift (a i l neg ≫ (integralRootFactorsIso M.line neg).hom)
      (lift (torusPoint D R (cocharacter D d R b))
        (a j r pos ≫ (integralRootFactorsIso M.line pos).hom))
  let f := cellMap M.line M.torus M.root neg pos
  haveI : IsOpenImmersion f.left := M.openCell neg pos hneg hpos
  haveI : Mono f := Over.mono_of_mono_left _
  have hprod (k : D.I) (x : R) (s : List D.I) (hs : s.Nodup) (hk : k ∈ s) :
      (s.map (fun z ↦ integralRootSection M z R (if z = k then x else 0))).prod =
        integralRootSection M k R x := by
    rw [List.prod_map_eq_pow_single k _ (fun z hne _ ↦ by
      simp only [ite_eq_right hne, integralRootSection_zero]), List.count_eq_one_of_mem hs hk,
      pow_one, ite_eq_left rfl]
  have heval (l r : R) (b : Rˣ) : q l r b ≫ f =
      integralRootSection M i R l * (torusPoint D R (cocharacter D d R b) ≫ M.torus.hom.hom) *
        integralRootSection M j R r := by
    dsimp only [q, f, a]
    rw [cellMap, lift_mul_three_factors, Category.assoc, Category.assoc,
      integralRootProduct_evaluation, integralRootProduct_evaluation]
    exact congrArg₂ (fun x y ↦ x * (torusPoint D R (cocharacter D d R b) ≫ M.torus.hom.hom) * y)
      (hprod i l neg hneg.1 him) (hprod j r pos hpos.1 hjm)
  have heq : q l₁ r₁ b₁ = q l₂ r₂ b₂ := (cancel_mono f).mp
    ((heval l₁ r₁ b₁).trans (h.trans (heval l₂ r₂ b₂).symm))
  have hl : a i l₁ neg = a i l₂ neg :=
    (cancel_mono (integralRootFactorsIso M.line neg).hom).mp (by
      simpa only [q, lift_fst] using congrArg (· ≫ fst _ _) heq)
  have hr₀ : lift (torusPoint D R (cocharacter D d R b₁))
      (a j r₁ pos ≫ (integralRootFactorsIso M.line pos).hom) =
      lift (torusPoint D R (cocharacter D d R b₂))
      (a j r₂ pos ≫ (integralRootFactorsIso M.line pos).hom) := by
    simpa only [q, lift_snd] using congrArg (· ≫ snd _ _) heq
  have hb : torusPoint D R (cocharacter D d R b₁) = torusPoint D R (cocharacter D d R b₂) := by
    simpa only [lift_fst] using congrArg (· ≫ fst _ _) hr₀
  have hr : a j r₁ pos = a j r₂ pos :=
    (cancel_mono (integralRootFactorsIso M.line pos).hom).mp (by
      simpa only [lift_snd] using congrArg (· ≫ snd _ _) hr₀)
  refine ⟨integralAdditivePoint_injective R ?_, integralCorootPoint_injective D d χ hχ R hb,
    integralAdditivePoint_injective R ?_⟩
  · simpa using (orderedFactorPoint_eq _ _ neg).mp hl i him
  · simpa using (orderedFactorPoint_eq _ _ pos).mp hr j hjm

private theorem upper_inverse {R : Type u} [CommRing R] (x : R) :
    (upper x)⁻¹ = upper (-x) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) R) * !![1, -x; 0, 1] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem lower_inverse {R : Type u} [CommRing R] (x : R) :
    (lower x)⁻¹ = lower (-x) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change (!![1, 0; x, 1] : Matrix (Fin 2) (Fin 2) R) * !![1, 0; -x, 1] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem diagonal_inverse {R : Type u} [CommRing R] (b : Rˣ) :
    (diagonal b)⁻¹ = diagonal b⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change (!![(b : R), 0; 0, (↑b⁻¹ : R)] : Matrix (Fin 2) (Fin 2) R) *
    !![(↑b⁻¹ : R), 0; 0, (↑b : R)] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

set_option maxHeartbeats 1100000 in
/-- On the rank-one pivot chart the homomorphism is injective when the
marked coroot is primitive. For a negative root invert both words and
use the positive marking on the opposite root. -/
private theorem integralRankOne_pivot_injective {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (i : D.I) (χ : D.X) (hχ : D.datum.coroot' i χ = 1) (R : IntegralAlgebra.{u})
    (m n : Matrix.SpecialLinearGroup (Fin 2) R)
    (hm : IsUnit (m.val 0 0)) (hn : IsUnit (n.val 0 0))
    (h : (M.rankOne i).app R m = (M.rankOne i).app R n) : m = n := by
  let j := D.datum.reflectionPerm i i
  let f : Matrix.SpecialLinearGroup (Fin 2) R →* IntegralPoints M.group R :=
    ((M.rankOne i).app R).hom
  obtain ⟨b₁, hb₁⟩ := hm
  obtain ⟨b₂, hb₂⟩ := hn
  let l₁ := m.val 1 0 * (↑b₁⁻¹ : R)
  let l₂ := n.val 1 0 * (↑b₂⁻¹ : R)
  let r₁ := m.val 0 1 * (↑b₁⁻¹ : R)
  let r₂ := n.val 0 1 * (↑b₂⁻¹ : R)
  have h₁ : m = lower l₁ * diagonal b₁ * upper r₁ := rankOne_pivot_factorization m b₁ hb₁
  have h₂ : n = lower l₂ * diagonal b₂ * upper r₂ := rankOne_pivot_factorization n b₂ hb₂
  have hdiag : D.datum.toLinearMap χ (D.datum.coroot i) = 1 := hχ
  have hp : D.base.IsPos j ↔ ¬ D.base.IsPos i := RootPairing.Base.IsPos.neg_iff_not D.base i
  have hU (z : R) : f (upper z) = integralRootSection M i R z := M.rankOneUpper i R z
  have hL (z : R) : f (lower z) = integralRootSection M j R z := M.rankOneLower i R z
  have hD (b : Rˣ) : f (diagonal b) =
      torusPoint D R (cocharacter D (D.datum.coroot i) R b) ≫ M.torus.hom.hom :=
    M.rankOneDiagonal i R b
  change f m = f n at h
  have hparams : l₁ = l₂ ∧ b₁ = b₂ ∧ r₁ = r₂ := by
    by_cases hi : D.base.IsPos i
    · have hj : ¬ D.base.IsPos j := fun hj ↦ (hp.mp hj) hi
      have hprod := h
      rw [h₁, h₂] at hprod
      simp only [map_mul, hU, hL, hD] at hprod
      exact integralGaussParameters M j i hj hi (D.datum.coroot i) χ hdiag R hprod
    · have hj : D.base.IsPos j := hp.mpr hi
      have hprod : f m⁻¹ = f n⁻¹ := by rw [map_inv, map_inv, h]
      simp only [h₁, h₂, mul_inv_rev, upper_inverse, diagonal_inverse, lower_inverse,
        ← mul_assoc, map_mul, hU, hL, hD] at hprod
      obtain ⟨hr, hb, hl⟩ :=
        integralGaussParameters M i j hi hj (D.datum.coroot i) χ hdiag R hprod
      exact ⟨neg_injective hl, inv_injective hb, neg_injective hr⟩
  obtain ⟨hl, hb, hr⟩ := hparams
  calc
    m = lower l₁ * diagonal b₁ * upper r₁ := h₁
    _ = lower l₂ * diagonal b₂ * upper r₂ := by rw [hl, hb, hr]
    _ = n := h₂.symm

end IntegralGaussCell

attribute [local instance] integerAlgebra

set_option maxHeartbeats 1400000 in
/-- The integral model gives an absolute rank-one homomorphism with both
root coordinates on the marked ambient group. The diagonal is the attached
coroot. -/
private theorem absoluteRankOneHomomorphism (A : MarkedTori G) (α : Root A.P.T)
    (hspan : corootLattice A.datum = ⊤) :
    ∃ (L : AdditiveLine Fsep) (U V : ClosedSubgroup A.P.G.val)
      (x : L.group ≅ U.group) (y : L.group ≅ V.group)
      (ρ : Specs.IntegralFibreReductivity.rankOnePoints Fsep ⟶
        (groupPointsFunctor Fsep).obj A.P.G.val),
      (∀ R, Function.Injective (ρ.app R)) ∧
      IsRootSubgroup A.P.T U α.val ∧ IsRootSubgroup A.P.T V α.val⁻¹ ∧
      HasScalarAction A.P.T α.val (x.hom ≫ U.inclusion) ∧
      HasScalarAction A.P.T α.val⁻¹ (y.hom ≫ V.inclusion) ∧
      (∀ (R : TestAlgebra Fsep) (z : R),
        ρ.app R (upper z) = rootPoint (x.hom ≫ U.inclusion) R z) ∧
      (∀ (R : TestAlgebra Fsep) (z : R),
        ρ.app R (lower z) = rootPoint (y.hom ≫ V.inclusion) R z) ∧
      ∀ (R : TestAlgebra Fsep) (s : Rˣ),
        ρ.app R (diagonal s) =
          cocharacterPoint (Additive.toMul (A.datum.toBased.datum.coroot α)) R s ≫
            A.P.T.inclusion.hom.hom := by
  classical
  letI := A.datum.comm
  let D := A.datum.toBased
  let a : D.I := α
  obtain ⟨M⟩ := Classification.IntegralRealization.integralRealization D
  obtain ⟨L, B, e, t, z, ht, _, hchar, hz⟩ := M.fieldFibre Fsep
  letI := B.attached.comm
  obtain ⟨W, ⟨pin⟩⟩ := Classification.Pinning.pinningsExist L A.P
  let Q : PinnedGroup L := ⟨A.P, W, pin⟩
  let d : BasedIso B.attached.toBased D := Groupoid.inv (show D ⟶ _ from B.datumIso)
  obtain ⟨f, hf⟩ := pinnedLift B.pinned Q B.attached A.datum d
  let i (a : D.I) := B.datumIso.val.indexEquiv a
  let W' (a : D.I) : ClosedSubgroup A.P.G.val :=
    transportSubgroup f.group (B.pinned.roots (i a)).val
  have hweight (χ : Character A.P.T.group) :
      Additive.ofMul (f.torus.hom ≫ χ) = B.datumIso.val.weightEquiv (Additive.ofMul χ) := by
    let b := B.datumIso.val.weightEquiv (Additive.ofMul χ)
    have h := congrArg (fun q : BasedIso B.attached.toBased D => q.val.weightEquiv b) hf
    change Additive.ofMul (f.torus.inv ≫ Additive.toMul b) =
      B.datumIso.val.weightEquiv.symm b at h
    rw [LinearEquiv.symm_apply_apply] at h
    have h' : f.torus.inv ≫ Additive.toMul b = χ := congrArg Additive.toMul h
    nth_rw 1 [← h']
    rw [Iso.hom_inv_id_assoc]
    rfl
  have hχ (a : D.I) : f.torus.inv ≫ (i a).val = a.val := by
    have hi := B.datumIso.val.toHom.root_weightMap_apply D.datum B.attached.toBased.datum a
    rw [show D.datum.root a = Additive.ofMul a.val from A.datum.datum.root_eq a,
      show B.attached.toBased.datum.root (i a) = Additive.ofMul (i a).val from
        B.attached.datum.root_eq (i a)] at hi
    apply (cancel_epi f.torus.hom).mp
    rw [f.torus.hom_inv_id_assoc]
    exact congrArg Additive.toMul (hi.symm.trans (hweight a.val).symm)
  have hr (a : D.I) :
      IsRootSubgroup A.P.T (W' a) a.val ∧
        HasScalarAction A.P.T a.val ((z a).val.hom ≫ (W' a).inclusion) := by
    have h := transportedRootCoordinate
      (B.pinned.roots (i a)).property (z a) f.group f.torus f.torus_comm
    rw [hχ a] at h
    simpa only [W', transportSubgroup] using h
  let a' := D.datum.reflectionPerm a a
  have hOpp : a'.val = α.val⁻¹ := by
    have h := D.datum.root_reflectionPerm a a
    rw [D.datum.reflection_apply_self] at h
    change A.datum.datum.rootDatum.root a' = -A.datum.datum.rootDatum.root α at h
    rw [A.datum.datum.root_eq, A.datum.datum.root_eq] at h
    exact congrArg Additive.toMul h
  let ρ := rankOneFibre (k := Fsep) M.toIntegralMarking a ≫
    (groupPointsFunctor Fsep).map (e.hom ≫ f.group.hom)
  refine ⟨L, W' a, W' a', (z a).val, (z a').val, ρ, ?_,
    (hr a).1, hOpp ▸ (hr a').1, (hr a).2, hOpp ▸ (hr a').2, ?_, ?_, ?_⟩
  · obtain ⟨χ, hχ⟩ := IntegralFibreReductivity.primitiveCoroots D hspan a
    apply rankOneInjectiveOfPivot
    intro R m n hm hn he
    let E := Grp.forget (SchemeOver Fsep)
    letI : IsIso (e.hom ≫ f.group.hom).hom.hom := E.map_isIso (e.hom ≫ f.group.hom)
    have h : (rankOneFibre (k := Fsep) M.toIntegralMarking a).app R m =
        (rankOneFibre (k := Fsep) M.toIntegralMarking a).app R n :=
      (cancel_mono (e.hom ≫ f.group.hom).hom.hom).mp he
    have h' := congrArg (forgetFibrePoint M.group R) h
    rw [rankOneFibre_apply, rankOneFibre_apply] at h'
    exact integralRankOne_pivot_injective M.toIntegralMarking a χ hχ
      ((restrictToIntegers Fsep).obj R) m n hm hn h' 
  · intro R r
    have h : (rankOneFibre (k := Fsep) M.toIntegralMarking a).app R (upper r) =
        rootPoint ((z a).val.hom ≫ (B.pinned.roots (i a)).val.inclusion ≫ e.inv) R r := by
      apply (Classification.IntegralSemisimpleModel.forgetFibrePoint_bijective M.group R).injective
      rw [rankOneFibre_apply, hz, M.rankOneUpper]
    change (rankOneFibre (k := Fsep) M.toIntegralMarking a).app R (upper r) ≫
      (e.hom ≫ f.group.hom).hom.hom = _
    rw [h, ← rootPoint_comp]
    simp only [W', transportSubgroup, Category.assoc, e.inv_hom_id_assoc]
  · intro R r
    have h : (rankOneFibre (k := Fsep) M.toIntegralMarking a).app R (lower r) =
        rootPoint ((z a').val.hom ≫ (B.pinned.roots (i a')).val.inclusion ≫ e.inv) R r := by
      apply (Classification.IntegralSemisimpleModel.forgetFibrePoint_bijective M.group R).injective
      rw [rankOneFibre_apply, hz, M.rankOneLower]
    change (rankOneFibre (k := Fsep) M.toIntegralMarking a).app R (lower r) ≫
      (e.hom ≫ f.group.hom).hom.hom = _
    rw [h, ← rootPoint_comp]
    simp only [W', transportSubgroup, Category.assoc, e.inv_hom_id_assoc]
  · intro R b
    let R₀ := (restrictToIntegers Fsep).obj R
    let value : TorusValues D R₀ := cocharacter D (D.datum.coroot a) R₀ b
    let s := (fibrePointsEquiv (Specs.IntegralSemisimpleModel.splitTorus D) R).symm
      (torusPoint D R₀ value)
    have hs : forgetFibrePoint (Specs.IntegralSemisimpleModel.splitTorus D) R s =
        torusPoint D R₀ value := (fibrePointsEquiv _ R).apply_symm_apply _
    have hRank : (rankOneFibre (k := Fsep) M.toIntegralMarking a).app R (diagonal b) =
        s ≫ ((fibre Fsep).map M.torus).hom.hom := by
      apply (Classification.IntegralSemisimpleModel.forgetFibrePoint_bijective M.group R).injective
      rw [rankOneFibre_apply, M.rankOneDiagonal, forgetFibrePoint_comp]
      exact (congrArg (· ≫ M.torus.hom.hom) hs).symm
    have hT : s ≫ (t.hom ≫ f.torus.hom).hom.hom =
        cocharacterPoint (Additive.toMul (D.datum.coroot a)) R b := by
      apply Classification.PinnedUniqueness.charactersSeparatePoints A.P.split R
      intro χ
      apply (unitEquiv R).injective
      apply Units.ext
      change (characterUnit (f.torus.hom ≫ χ) R (s ≫ t.hom.hom.hom) : R) =
        (characterUnit χ R (cocharacterPoint (Additive.toMul (D.datum.coroot a)) R b) : R)
      rw [← characterValue_eq_unit, ← characterValue_eq_unit]
      let x : D.X := Additive.ofMul χ
      calc
        _ = characterValue (Additive.toMul (B.datumIso.val.weightEquiv x)) R
            (s ≫ t.hom.hom.hom) := by
          rw [show f.torus.hom ≫ χ =
            Additive.toMul (B.datumIso.val.weightEquiv x) from
              congrArg Additive.toMul (hweight χ)]
          rfl
        _ = ((value (Multiplicative.ofAdd x)).val : R) := hchar R s value hs x
        _ = _ := by
          rw [(RootData.CharacterPairing.characterPairingComposition _ _ _).2]
          change (↑(b ^ D.datum.toLinearMap x (D.datum.coroot a)) : R) =
            ↑(b ^ pairing A.P.T.group χ (Additive.toMul (D.datum.coroot a)))
          exact congrArg (fun n : ℤ => ((b ^ n : Rˣ) : R))
            (A.datum.datum.pairing_eq χ (Additive.toMul (D.datum.coroot a)))
    change (rankOneFibre (k := Fsep) M.toIntegralMarking a).app R (diagonal b) ≫
      (e.hom ≫ f.group.hom).hom.hom = _
    rw [hRank]
    have hsq : (fibre Fsep).map M.torus ≫ e.hom ≫ f.group.hom =
        (t.hom ≫ f.torus.hom) ≫ A.P.T.inclusion := by
      rw [← Category.assoc, ht, Category.assoc, f.torus_comm, Category.assoc]
    calc
      _ = s ≫ ((fibre Fsep).map M.torus ≫ e.hom ≫ f.group.hom).hom.hom := by
        simp only [Grp.comp_hom_hom, Category.assoc]
      _ = s ≫ ((t.hom ≫ f.torus.hom) ≫ A.P.T.inclusion).hom.hom :=
        congrArg (fun j => s ≫ j.hom.hom) hsq
      _ = _ := by rw [Grp.comp_hom_hom, ← Category.assoc, hT]

/-- The injective absolute point map is represented by a closed embedding. -/
private theorem absoluteRankOneClosedEmbedding (A : MarkedTori G) (α : Root A.P.T)
    (hG : IsSemisimple G) (hsc : GeometricallySimplyConnected G) :
    ∃ (L : AdditiveLine Fsep) (U V : ClosedSubgroup A.P.G.val)
      (x : L.group ≅ U.group) (y : L.group ≅ V.group)
      (ρ : Specs.IntegralFibreReductivity.rankOnePoints Fsep ⟶
        (groupPointsFunctor Fsep).obj A.P.G.val)
      (i : (StandardGroups.specialLinearGroup Fsep (Index.{u} 2)).val ⟶ A.P.G.val),
      IsClosedImmersion i.hom.hom.left ∧
      (groupPointsFunctor Fsep).map i = (rankOnePointsIso Fsep).hom ≫ ρ ∧
      IsRootSubgroup A.P.T U α.val ∧ IsRootSubgroup A.P.T V α.val⁻¹ ∧
      HasScalarAction A.P.T α.val (x.hom ≫ U.inclusion) ∧
      HasScalarAction A.P.T α.val⁻¹ (y.hom ≫ V.inclusion) ∧
      (∀ (R : TestAlgebra Fsep) (r : R),
        ρ.app R (upper r) = rootPoint (x.hom ≫ U.inclusion) R r) ∧
      (∀ (R : TestAlgebra Fsep) (r : R),
        ρ.app R (lower r) = rootPoint (y.hom ≫ V.inclusion) R r) ∧
      ∀ (R : TestAlgebra Fsep) (t : Rˣ),
        ρ.app R (diagonal t) =
          cocharacterPoint (Additive.toMul (A.datum.toBased.datum.coroot α)) R t ≫
            A.P.T.inclusion.hom.hom := by
  obtain ⟨L, U, V, x, y, ρ, hρ, hU, hV, hx, hy, hp, hn, hD⟩ :=
    absoluteRankOneHomomorphism A α (fullCorootLattice A hG hsc)
  obtain ⟨i, hi⟩ := representedRankOneHomomorphism ρ
  refine ⟨L, U, V, x, y, ρ, i, ?_, hi, hU, hV, hx, hy, hp, hn, hD⟩
  apply closedImmersionOfInjectivePoints i
  intro R p q hpq
  have eq (m : GroupPoints (StandardGroups.specialLinearGroup Fsep (Index.{u} 2)).val R) :
      m ≫ i.hom.hom = ρ.app R ((rankOnePointsIso Fsep).hom.app R m) :=
    ConcreteCategory.congr_hom (congrArg (fun τ => τ.app R) hi) m
  have hinj := ConcreteCategory.bijective_of_isIso ((rankOnePointsIso Fsep).hom.app R)
  exact hinj.1 ((hρ R) ((eq p).symm.trans (hpq.trans (eq q))))

end AbsoluteRankOne


section Assembly

open Specs.IntegralFibreReductivity (rankOnePoints)
open Specs.IntegralRootRelations (upper lower diagonal)
open Specs.ExceptionalRankOneMatrixWitnesses (Witnesses liftMatrix)
open Specs.ExceptionalRankOneNormalization (antiDiagonal diagonalConjugate matrixMap)
open Specs.ExceptionalRankOneEmbeddingDescent (MatrixComparison)
open ExceptionalRankOneMatrixWitnesses (standardGroup standardMatrix)
open Specs.GeometricBorelConjugacy (ConjugatesSubgroups)
open CocharacterDynamics (cocharacterPoint)
open private reductive_of_semisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies
open private scaleIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.Pinning
open private rootPoint_eq rootPoint_comp hom_ext_on_affine_tests from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private unitEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private elementaryWord from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization
open private diagonalConjugate_antiDiagonal from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalRankOneNormalization
open private conjugates_descend extendSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer
open private scalarExtendedPoint_natural from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag

private def descentMarking (A : MarkedTori G) : Specs.ExceptionalRootGroupDescent.MarkedTori G :=
  ⟨A.S, A.maximalSplit, A.T, A.maximalTorus, A.intoTorus, A.intoTorus_eq,
    A.P, A.ambient, A.torus, A.torus_eq⟩

private theorem oppositeSingleton (A : MarkedTori G) (α β : Root A.P.T)
    (hα : HasSingletonRootLine A α) (hβ : β.val = α.val⁻¹) :
    HasSingletonRootLine A β := by
  have hr : A.restrict β.val = (A.restrict α.val)⁻¹ := by
    rw [hβ]
    exact (precomposeCharacter A.splitInAbsolute).map_inv α.val
  refine ⟨fun h ↦ hα.1 (inv_eq_one.mp (hr ▸ h)), ?_⟩
  intro δ hδ ⟨m, n, hm, hn, hmn⟩
  have h : (A.restrict α.val) ^ (-m) = (A.restrict δ.val) ^ n := by
    rw [zpow_neg, ← inv_zpow, ← hr]
    exact hmn
  rcases hα.2 δ hδ ⟨-m, n, neg_ne_zero.mpr hm, hn, h⟩ with hδ' | hδ'
  · exact Or.inr (by rw [hβ, inv_inv, hδ'])
  · exact Or.inl (hδ'.trans hβ.symm)

private abbrev markedCoroot (A : MarkedTori G) (α : Root A.P.T) : Cocharacter A.P.T.group :=
  Additive.toMul (A.datum.toBased.datum.coroot α)

private theorem coroot_pairing_eq_two (A : MarkedTori G) (α : Root A.P.T) :
    pairing A.P.T.group α.val (markedCoroot A α) = 2 := by
  let D := A.datum
  letI := D.comm
  change pairing A.P.T.group α.val (Additive.toMul (D.datum.rootDatum.coroot α)) = 2
  rw [← D.datum.pairing_eq, ← D.datum.root_eq]
  exact D.datum.rootDatum.root_coroot_two α

private def reflectionIso {k : Type u} [Field k] {T : GroupScheme k}
    [IsCommMonObj T.X] (hT : IsSplitTorus T)
    (a : Character T) (c : Cocharacter T) (h : pairing T a c = 2) : T ≅ T :=
  ⟨torusReflectionMap a c, torusReflectionMap a c,
    torusReflectionMap_involutive hT a c h, torusReflectionMap_involutive hT a c h⟩

private abbrev markedReflection (A : MarkedTori G) (α : Root A.P.T) : A.P.T.group ≅ A.P.T.group :=
  letI := A.datum.comm
  reflectionIso A.P.split α.val (markedCoroot A α) (coroot_pairing_eq_two A α)

private theorem markedCharacterReflection (A : MarkedTori G) (α : Root A.P.T)
    (χ : Character A.P.T.group) :
    Additive.ofMul ((markedReflection A α).inv ≫ χ) =
      A.datum.toBased.datum.reflection α (Additive.ofMul χ) := by
  let D := A.datum
  letI := D.comm
  let c := markedCoroot A α
  change Additive.ofMul (torusReflectionMap α.val c ≫ χ) =
    D.datum.rootDatum.reflection α (Additive.ofMul χ)
  rw [torusReflectionMap_character, RootPairing.reflection_apply, D.datum.root_eq]
  change Additive.ofMul (χ * α.val ^ (-pairing A.P.T.group χ c)) =
    Additive.ofMul χ - D.datum.rootDatum.toLinearMap (Additive.ofMul χ)
      (Additive.ofMul c) • Additive.ofMul α.val
  rw [D.datum.pairing_eq, sub_eq_add_neg, ← neg_smul]
  rfl

private theorem rankOnePointsIso_matrix {k : Type u} [Field k] (R : TestAlgebra k)
    (p : GroupPoints (standardGroup k).val R) :
    liftMatrix ((rankOnePointsIso k).hom.app R p) = (standardMatrix k).hom.app R p :=
  liftMatrix.apply_symm_apply _

private theorem rankOnePointsIso_inv_matrix {k : Type u} [Field k] (R : TestAlgebra k)
    (p : Matrix.SpecialLinearGroup (Fin 2) R) :
    (standardMatrix k).hom.app R ((rankOnePointsIso k).inv.app R p) = liftMatrix p := by
  rw [← rankOnePointsIso_matrix R, Iso.inv_hom_id_app_apply]

private theorem rankOnePoint_map {k : Type u} [Field k] {J : GroupScheme k}
    {g : (standardGroup k).val ⟶ J}
    {ρ : rankOnePoints k ⟶ (groupPointsFunctor k).obj J}
    (hg : (groupPointsFunctor k).map g = (rankOnePointsIso k).hom ≫ ρ)
    (R : TestAlgebra k) (m : Matrix.SpecialLinearGroup (Fin 2) R) :
    (rankOnePointsIso k).inv.app R m ≫ g.hom.hom = ρ.app R m := by
  have h := ConcreteCategory.congr_hom (congrArg (fun τ => τ.app R) hg)
    ((rankOnePointsIso k).inv.app R m)
  change _ = ρ.app R ((rankOnePointsIso k).hom.app R ((rankOnePointsIso k).inv.app R m)) at h
  rw [Iso.inv_hom_id_app_apply] at h
  exact h

private theorem antiDiagonal_eq_word (R : Type u) [CommRing R] :
    antiDiagonal R = elementaryWord (1 : Rˣ) := by
  apply Subtype.ext
  change (!![(0 : R), 1; -1, 0] : Matrix (Fin 2) (Fin 2) R) =
    !![1, 1; 0, 1] * !![1, 0; -1, 1] * !![1, 1; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem mem_normalizer_of_conjugation {X Y : Type*} [Group X] [Group Y]
    (i : X →* Y) (w : Y) (f : X → X) (hf : Function.Surjective f)
    (h : ∀ t, MulAut.conj w (i t) = i (f t)) : w ∈ Subgroup.normalizer i.range := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  ext g
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨f t, (h t).symm⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨p, rfl⟩ := hf t
    exact ⟨i p, ⟨p, rfl⟩, h p⟩

private theorem markedTorusIncl (A : MarkedTori G) :
    A.torus.inv ≫ (groupBaseChange F Fsep).map A.T.inclusion =
      A.P.T.inclusion ≫ A.ambient.hom := by
  rw [← A.torus_eq, A.torus.inv_hom_id_assoc]

private theorem markedSplitIncl (A : MarkedTori G) :
    A.splitInAbsolute ≫ A.P.T.inclusion ≫ A.ambient.hom =
      (groupBaseChange F Fsep).map A.S.inclusion := by
  change ((groupBaseChange F Fsep).map A.intoTorus ≫ A.torus.hom) ≫ _ ≫ _ = _
  rw [Category.assoc, A.torus_eq, ← Functor.map_comp, A.intoTorus_eq]

/-- The coroot and Weyl word in the split model give the diagonal and
normalizer hypotheses for rational normalization. -/
private theorem weyl_mem_normalizer (A : MarkedTori G) (α : Root A.P.T)
    {L : AdditiveLine Fsep} {x y : L.group ⟶ A.P.G.val}
    (ρ : rankOnePoints Fsep ⟶ (groupPointsFunctor Fsep).obj A.P.G.val)
    (hx : HasScalarAction A.P.T α.val x) (hy : HasScalarAction A.P.T α.val⁻¹ y)
    (hp : ∀ (R : TestAlgebra Fsep) (z : R), ρ.app R (upper z) = rootPoint x R z)
    (hn : ∀ (R : TestAlgebra Fsep) (z : R), ρ.app R (lower z) = rootPoint y R z)
    (hc : ∀ (R : TestAlgebra Fsep) (b : Rˣ), ρ.app R (diagonal b) =
      cocharacterPoint (markedCoroot A α) R b ≫ A.P.T.inclusion.hom.hom) :
    let R := CommAlgCat.of Fsep Fsep
    let w : GroupPoints ((groupBaseChange F Fsep).obj G.val) R :=
      ρ.app R (antiDiagonal Fsep) ≫ A.ambient.hom.hom.hom
    w ∈ Subgroup.normalizer (((groupPointsFunctor Fsep).map ((groupBaseChange F Fsep).map A.T.inclusion)).app R).hom.range := by
  letI := A.datum.comm
  let R := CommAlgCat.of Fsep Fsep
  let w : GroupPoints ((groupBaseChange F Fsep).obj G.val) R :=
    ρ.app R (antiDiagonal Fsep) ≫ A.ambient.hom.hom.hom
  let c := A.torus ≪≫ markedReflection A α ≪≫ A.torus.symm
  let f := ((groupPointsFunctor Fsep).map c.hom).app R
  apply mem_normalizer_of_conjugation _ w f (ConcreteCategory.bijective_of_isIso f).surjective
  intro t
  let tP : GroupPoints A.P.T.group R := t ≫ A.torus.hom.hom.hom
  let gP : GroupPoints A.P.G.val R := tP ≫ A.P.T.inclusion.hom.hom
  let wP := ρ.app R (antiDiagonal Fsep)
  have ht : wP * gP * wP⁻¹ = tP ≫ (torusReflectionMap α.val (markedCoroot A α) ≫
      A.P.T.inclusion).hom.hom := by
    rw [show wP = ρ.app R (elementaryWord (1 : Fsepˣ)) from
      congrArg (ρ.app R) (antiDiagonal_eq_word Fsep)]
    exact rankOneWordConjugates A.P.T α.val (markedCoroot A α) ρ hx hy hp hn hc R tP
  let m := IsMonHom.monoidHom A.ambient.hom.hom.hom ((testSpec Fsep).obj (op R))
  have h := congrArg m ht
  rw [map_mul, map_mul, map_inv] at h
  have hcomm : A.torus.hom ≫ A.P.T.inclusion ≫ A.ambient.hom =
      (groupBaseChange F Fsep).map A.T.inclusion := A.torus_eq
  have hcomm' : A.torus.hom.hom.hom ≫ A.P.T.inclusion.hom.hom ≫ A.ambient.hom.hom.hom =
      ((groupBaseChange F Fsep).map A.T.inclusion).hom.hom :=
    congrArg (Grp.forget (SchemeOver Fsep)).map hcomm
  have hreverse : A.torus.inv.hom.hom ≫ ((groupBaseChange F Fsep).map A.T.inclusion).hom.hom =
      A.P.T.inclusion.hom.hom ≫ A.ambient.hom.hom.hom :=
    congrArg (Grp.forget (SchemeOver Fsep)).map (markedTorusIncl A)
  let tG : GroupPoints ((groupBaseChange F Fsep).obj G.val) R :=
    t ≫ ((groupBaseChange F Fsep).map A.T.inclusion).hom.hom
  let tG' : GroupPoints ((groupBaseChange F Fsep).obj G.val) R :=
    (t ≫ c.hom.hom.hom) ≫ ((groupBaseChange F Fsep).map A.T.inclusion).hom.hom
  change w * tG * w⁻¹ = tG'
  have hW : m wP = w := rfl
  have hG : m gP = tG := by
    change ((t ≫ A.torus.hom.hom.hom) ≫ A.P.T.inclusion.hom.hom) ≫
        A.ambient.hom.hom.hom = _
    simp only [Category.assoc, hcomm', tG]
  have hG' : m (tP ≫ (torusReflectionMap α.val (markedCoroot A α) ≫
      A.P.T.inclusion).hom.hom) = tG' := by
    change (tP ≫ (torusReflectionMap α.val (markedCoroot A α) ≫ A.P.T.inclusion).hom.hom) ≫
      A.ambient.hom.hom.hom = tG'
    simp only [tP, tG', c, Iso.trans_hom, Iso.symm_hom, Grp.comp_hom_hom, Category.assoc, hreverse]
    rfl
  rw [hW, hG, hG'] at h
  exact h

private theorem cocharacterPoint_comp {k : Type u} [Field k] {X Y : GroupScheme k}
    (c : Cocharacter X) (f : X ⟶ Y) (R : TestAlgebra k) (t : Rˣ) :
    cocharacterPoint (c ≫ f) R t = cocharacterPoint c R t ≫ f.hom.hom := by
  unfold cocharacterPoint
  rw [Functor.map_comp, NatTrans.comp_app]
  rfl

private theorem cocharacter_ext {k : Type u} [Field k] {J : GroupScheme k}
    {a b : Cocharacter J}
    (h : ∀ (R : TestAlgebra k) (t : Rˣ), cocharacterPoint a R t = cocharacterPoint b R t) :
    a = b := by
  apply Grp.hom_ext
  apply hom_ext_on_affine_tests
  intro R p
  obtain ⟨t, rfl⟩ := (unitEquiv R).symm.surjective p
  exact h R t

private theorem rootCoordinate_ext {k : Type u} [Field k] {J : GroupScheme k} {L : AdditiveLine k}
    {a b : L.group ⟶ J}
    (h : ∀ (R : TestAlgebra k) (t : R), rootPoint a R t = rootPoint b R t) : a = b := by
  apply Grp.hom_ext
  apply hom_ext_on_affine_tests
  intro R p
  obtain ⟨t, rfl⟩ := (RootData.RootGroups.additivePoints L R).surjective p
  simpa only [rootPoint_eq] using h R t

private theorem elementaryInclusion_eq {k : Type u} [Field k] {J : GroupScheme k}
    {L : AdditiveLine k} (c : L.group ⟶ (standardGroup k).val) (i : (standardGroup k).val ⟶ J)
    (x : L.group ⟶ J)
    (m : ∀ R : TestAlgebra k, R → Matrix.SpecialLinearGroup (Fin 2) R)
    (hc : ∀ (R : TestAlgebra k) (t : R),
      (standardMatrix k).hom.app R (rootPoint c R t) = liftMatrix (m R t))
    (hi : ∀ (R : TestAlgebra k) (t : R),
      (rankOnePointsIso k).inv.app R (m R t) ≫ i.hom.hom = rootPoint x R t) :
    c ≫ i = x := by
  apply rootCoordinate_ext
  intro R t
  have he : rootPoint c R t = (rankOnePointsIso k).inv.app R (m R t) := by
    apply (ConcreteCategory.bijective_of_isIso ((standardMatrix k).hom.app R)).injective
    exact (hc R t).trans (rankOnePointsIso_inv_matrix R (m R t)).symm
  rw [rootPoint_comp, he, hi]

private def matrixComparison (e : (standardGroup Fsep).val ≅
    (groupBaseChange F Fsep).obj (standardGroup F).val)
    (he : ∀ (R : TestAlgebra Fsep) (p : GroupPoints (standardGroup Fsep).val R),
      (standardMatrix F).hom.app ((restrictTestAlgebra F Fsep).obj R)
        (baseChangePoint F Fsep (standardGroup F).val.X R (p ≫ e.hom.hom.hom)) =
          (standardMatrix Fsep).hom.app R p) : MatrixComparison F Fsep where
  ground := standardGroup F
  extended := standardGroup Fsep
  groundMatrices := rankOnePointsIso F
  extendedMatrices := rankOnePointsIso Fsep
  scalarIso := e
  scalarMatrices R m := by
    apply liftMatrix.injective
    rw [rankOnePointsIso_matrix, he, rankOnePointsIso_inv_matrix]

private theorem baseChangePoint_constant {K : Type u} [Field K] [Algebra F K]
    {X : SchemeOver F} (w : 𝟙_ (SchemeOver F) ⟶ X) (R : TestAlgebra K) :
    baseChangePoint F K X R (toUnit _ ≫ scalarExtendedRationalPoint K w) = toUnit _ ≫ w := by
  unfold scalarExtendedRationalPoint
  rw [← Category.assoc, baseChangePointsSchemeNaturality]
  exact congrArg (· ≫ w) (toUnit_unique _ _)

private theorem standardWeyl_matrix {L : AdditiveLine F}
    (W : Witnesses L (standardMatrix F)) (R : TestAlgebra F) :
    (standardMatrix F).hom.app R (toUnit _ ≫ W.weyl) = liftMatrix (antiDiagonal R) := by
  let R₀ := CommAlgCat.of F F
  let a : R₀ ⟶ R := CommAlgCat.ofHom (Algebra.ofId F R)
  let p : GroupPoints (standardGroup F).val R₀ := toUnit _ ≫ W.weyl
  have h₀ : (standardMatrix F).hom.app R₀ p = liftMatrix (antiDiagonal F) := by
    apply Subtype.ext
    exact W.weyl_matrix
  have h := ConcreteCategory.congr_hom ((standardMatrix F).hom.naturality a) p
  change (standardMatrix F).hom.app R (mapPoints a p) =
    Matrix.SpecialLinearGroup.map a.hom.toRingHom ((standardMatrix F).hom.app R₀ p) at h
  have hp : mapPoints a p = toUnit _ ≫ W.weyl :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ W.weyl) (toUnit_unique _ _))
  rw [hp, h₀] at h
  refine h.trans (Subtype.ext ?_)
  ext i j
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  fin_cases i <;> fin_cases j <;>
    simp [liftMatrix, antiDiagonal, Matrix.reindex]

private theorem standardWeyl_extends {L : AdditiveLine F} (W : Witnesses L (standardMatrix F))
    (e : (standardGroup Fsep).val ≅ (groupBaseChange F Fsep).obj (standardGroup F).val)
    (he : ∀ (R : TestAlgebra Fsep) (p : GroupPoints (standardGroup Fsep).val R),
      (standardMatrix F).hom.app ((restrictTestAlgebra F Fsep).obj R)
        (baseChangePoint F Fsep (standardGroup F).val.X R (p ≫ e.hom.hom.hom)) =
          (standardMatrix Fsep).hom.app R p)
    (R : TestAlgebra Fsep) :
    toUnit _ ≫ scalarExtendedRationalPoint Fsep W.weyl =
      (rankOnePointsIso Fsep).inv.app R (antiDiagonal R) ≫ e.hom.hom.hom := by
  apply (baseChangePointsEquiv Fsep (standardGroup F).val.X R).injective
  change baseChangePoint F Fsep (standardGroup F).val.X R (toUnit _ ≫ scalarExtendedRationalPoint Fsep W.weyl) = _
  rw [baseChangePoint_constant]
  apply (ConcreteCategory.bijective_of_isIso ((standardMatrix F).hom.app
    ((restrictTestAlgebra F Fsep).obj R))).injective
  exact (standardWeyl_matrix W _).trans
    (((he R ((rankOnePointsIso Fsep).inv.app R (antiDiagonal R))).trans
      (rankOnePointsIso_inv_matrix R _)).symm)

private theorem rescaledWeyl_conjugation {k : Type u} [Field k] {J : GroupScheme k}
    (T : ClosedSubgroup J) [IsCommMonObj T.group.X] (a : Character T.group) (c : Cocharacter T.group)
    {L : AdditiveLine k} {x y : L.group ⟶ J}
    (ρ : rankOnePoints k ⟶ (groupPointsFunctor k).obj J)
    (hx : HasScalarAction T a x) (hy : HasScalarAction T a⁻¹ y)
    (hp : ∀ (R : TestAlgebra k) (z : R), ρ.app R (upper z) = rootPoint x R z)
    (hn : ∀ (R : TestAlgebra k) (z : R), ρ.app R (lower z) = rootPoint y R z)
    (hc : ∀ (R : TestAlgebra k) (b : Rˣ),
      ρ.app R (diagonal b) = cocharacterPoint c R b ≫ T.inclusion.hom.hom)
    (R : TestAlgebra k) (s : Rˣ) (t : GroupPoints T.group R) :
    let w := ρ.app R (diagonalConjugate s (antiDiagonal R))
    let g : GroupPoints J R := t ≫ T.inclusion.hom.hom
    w * g * w⁻¹ = t ≫ (torusReflectionMap a c ≫ T.inclusion).hom.hom := by
  dsimp only
  rw [diagonalConjugate_antiDiagonal]
  let g : GroupPoints J R := t ≫ T.inclusion.hom.hom
  change ρ.app R (diagonal s * antiDiagonal R) * g *
    (ρ.app R (diagonal s * antiDiagonal R))⁻¹ = _
  rw [map_mul, antiDiagonal_eq_word R]
  let d := ρ.app R (diagonal s)
  let w := ρ.app R (elementaryWord (1 : Rˣ))
  let g' : GroupPoints J R := t ≫ (torusReflectionMap a c ≫ T.inclusion).hom.hom
  change (d * w) * g * (d * w)⁻¹ = g'
  have h : w * g * w⁻¹ = g' := rankOneWordConjugates T a c ρ hx hy hp hn hc R t
  have hd : Commute d g' := by
    change Commute (ρ.app R (diagonal s)) (t ≫ (torusReflectionMap a c ≫ T.inclusion).hom.hom)
    rw [hc]
    change Commute (cocharacterPoint c R s ≫ T.inclusion.hom.hom)
      (t ≫ (torusReflectionMap a c).hom.hom ≫ T.inclusion.hom.hom)
    rw [← Category.assoc t]
    let X := (testSpec k).obj (op R)
    let p : X ⟶ T.group.X := cocharacterPoint c R s
    let q : X ⟶ T.group.X := t ≫ (torusReflectionMap a c).hom.hom
    exact (Commute.all p q).map (IsMonHom.monoidHom T.inclusion.hom.hom X)
  calc
    _ = d * (w * g * w⁻¹) * d⁻¹ := by rw [mul_inv_rev]; simp only [mul_assoc]
    _ = d * g' * d⁻¹ := by rw [h]
    _ = _ := by rw [hd.eq, mul_inv_cancel_right]

private theorem descendedInclusion {L : AdditiveLine F}
    {U₀ : ClosedSubgroup G.val} {U : GroupScheme Fsep}
    {J : GroupScheme F} (i : J ⟶ G.val) (B : ClosedSubgroup J)
    (b : L.group ≅ B.group) (x : L.group ≅ U₀.group)
    (iu : U ⟶ (groupBaseChange F Fsep).obj G.val)
    (s : (groupBaseChange F Fsep).obj U₀.group ≅ U)
    (hs : s.hom ≫ iu = (groupBaseChange F Fsep).map U₀.inclusion)
    (hb : (b.hom ≫ B.inclusion) ≫ i = x.hom ≫ U₀.inclusion) :
    let E := groupBaseChange F Fsep
    ((E.mapIso b).symm ≪≫ E.mapIso x ≪≫ s).hom ≫ iu =
      E.map (B.inclusion ≫ i) := by
  let E := groupBaseChange F Fsep
  change (E.map b.inv ≫ E.map x.hom ≫ s.hom) ≫ iu = _
  rw [Category.assoc, Category.assoc, hs]
  rw [← E.map_comp x.hom, ← E.map_comp b.inv, ← hb, ← Category.assoc, b.inv_hom_id_assoc]

set_option maxHeartbeats 1800000 in
/-- Assemble the rational embedding and identify the absolute action of
its anti-diagonal section. -/
private theorem splitRankOneWithAbsoluteReflection (A : MarkedTori G) (α : Root A.P.T)
    (hG : IsSemisimple G) (hsc : GeometricallySimplyConnected G) (hα : HasSingletonRootLine A α) :
    ∃ (H : SplitRootSL2 A α) (w : 𝟙_ (SchemeOver F) ⟶ H.subgroup.group.X),
      (H.matrix.hom.app (CommAlgCat.of F F) (toUnit _ ≫ w)).val =
        (fun i j : Index.{u} 2 => if i.down = j.down then 0 else if i.down = 0 then 1 else -1) ∧
      let p := toUnit A.P.T.group.X ≫ A.absolutePoint (w ≫ H.subgroup.inclusion.hom.hom)
      ((markedReflection A α).hom ≫ A.P.T.inclusion).hom.hom =
        p * A.P.T.inclusion.hom.hom * p⁻¹ := by
  letI := A.datum.comm
  let E := groupBaseChange F Fsep
  let c := markedCoroot A α
  let rd := descentMarking A
  obtain ⟨L, U, V, x, y, ρ, i, hi, hiρ, hU, hV, hx, hy, hp, hn, hd⟩ :=
    absoluteRankOneClosedEmbedding A α hG hsc
  have hβr : α.val⁻¹ ∈ absoluteRoots A.P.T :=
    (((RootData.RootGroups.rootSubgroups A.P.G A.P.reductive A.P.T A.P.split A.P.maximal).2
      α.val α.property).2.1 α.val⁻¹).mpr (Or.inr rfl) |>.1
  let β : Root A.P.T := ⟨α.val⁻¹, hβr⟩
  have hβ := oppositeSingleton A α β hα rfl
  have hRed := reductive_of_semisimple G hG
  obtain ⟨U₀, L₀, x₀, su, hsu⟩ := ExceptionalRootGroupDescent.rootGroupDescent G hRed rd α hα U hU L x hx
  obtain ⟨V₀, L₁, y₁, sv, hsv⟩ := ExceptionalRootGroupDescent.rootGroupDescent G hRed rd β hβ V hV L y hy
  change su.hom ≫ U.inclusion ≫ A.ambient.hom = E.map U₀.inclusion at hsu
  change sv.hom ≫ V.inclusion ≫ A.ambient.hom = E.map V₀.inclusion at hsv
  let y₀ := scaleIso L₀ L₁ 1 ≪≫ y₁
  let xK := x ≪≫ su.symm
  let yK := y ≪≫ sv.symm
  let g := i ≫ A.ambient.hom
  have hg : IsClosedImmersion g.hom.hom.left := by
    letI := hi
    haveI : IsIso A.ambient.hom.hom.hom.left :=
      (Grp.forget (SchemeOver Fsep) ⋙ Over.forget _).map_isIso A.ambient.hom
    change IsClosedImmersion (i.hom.hom.left ≫ A.ambient.hom.hom.hom.left)
    infer_instance
  let M := rankOnePointsIso Fsep
  have hpoint (R : TestAlgebra Fsep) (p : Matrix.SpecialLinearGroup (Fin 2) R) :
      matrixMap M g R p = ρ.app R p ≫ A.ambient.hom.hom.hom := by
    change M.inv.app R p ≫ i.hom.hom ≫ A.ambient.hom.hom.hom = _
    rw [← Category.assoc, rankOnePoint_map hiρ]
  have hxp (R : TestAlgebra Fsep) (z : R) :
      matrixMap M g R (upper z) = rootPoint (xK.hom ≫ E.map U₀.inclusion) R z := by
    rw [hpoint, hp, ← rootPoint_comp]
    change rootPoint ((x.hom ≫ U.inclusion) ≫ A.ambient.hom) R z =
      rootPoint ((x.hom ≫ su.inv) ≫ E.map U₀.inclusion) R z
    rw [← hsu, Category.assoc, Category.assoc, su.inv_hom_id_assoc]
  have hyn (R : TestAlgebra Fsep) (z : R) :
      matrixMap M g R (lower z) = rootPoint (yK.hom ≫ E.map V₀.inclusion) R z := by
    rw [hpoint, hn, ← rootPoint_comp]
    change rootPoint ((y.hom ≫ V.inclusion) ≫ A.ambient.hom) R z =
      rootPoint ((y.hom ≫ sv.inv) ≫ E.map V₀.inclusion) R z
    rw [← hsv, Category.assoc, Category.assoc, sv.inv_hom_id_assoc]
  have hdiag : ∃ q : Cocharacter (E.obj A.T.group), ∀ (R : TestAlgebra Fsep) (t : Rˣ),
      matrixMap M g R (diagonal t) = cocharacterPoint q R t ≫ (E.map A.T.inclusion).hom.hom := by
    refine ⟨c ≫ A.torus.inv, fun R t => ?_⟩
    rw [hpoint, hd, cocharacterPoint_comp, Category.assoc, Category.assoc]
    exact congrArg (fun f : A.P.T.group ⟶ E.obj G.val => cocharacterPoint c R t ≫ f.hom.hom)
      (markedTorusIncl A).symm
  have hw := weyl_mem_normalizer A α ρ hx hy hp hn hd
  have hw' : matrixMap M g (CommAlgCat.of Fsep Fsep) (antiDiagonal Fsep) ∈
        Subgroup.normalizer (((groupPointsFunctor Fsep).map (E.map A.T.inclusion)).app
          (CommAlgCat.of Fsep Fsep)).hom.range := by
    rw [hpoint]
    exact hw
  obtain ⟨scale, g', x', y', hg', hg'rescale, hg'diag, hg'upper, hg'lower⟩ :=
    ExceptionalRankOneNormalization.normalizeRootCoordinates G A.T U₀ V₀ A.maximalTorus.1
      L₀ L x₀ y₀ xK yK (standardGroup Fsep) M g hg hxp hyn hdiag hw'
  let W := ExceptionalRankOneMatrixWitnesses.standardWitnesses F L₀
  obtain ⟨e, _, m, he, _, hm, _, _, hediag⟩ :=
    ExceptionalRankOneMatrixWitnesses.standardMatrixScalarExtension F Fsep L₀ L
  let C := matrixComparison e he
  obtain ⟨j, hj, hjK, hjupper, hjlower⟩ :=
    ExceptionalRankOneEmbeddingDescent.descendMatrixEmbedding F G C g' hg'
      L₀ L₀ (x'.hom ≫ U₀.inclusion) (y'.hom ≫ V₀.inclusion) hg'upper hg'lower
  dsimp only [C, matrixComparison] at j hj hjK hjupper hjlower
  change e.hom ≫ E.map j = g' at hjK
  have hpos := elementaryInclusion_eq (W.posCoord.hom ≫ W.pos.inclusion) j
    (x'.hom ≫ U₀.inclusion) (fun _ r ↦ upper r) W.pos_matrix hjupper
  have hneg := elementaryInclusion_eq (W.negCoord.hom ≫ W.neg.inclusion) j
    (y'.hom ≫ V₀.inclusion) (fun _ r ↦ lower r) W.neg_matrix hjlower
  have hdiagAmbient : extendCocharacter m (W.diag ≫ j) =
      c ≫ A.P.T.inclusion ≫ A.ambient.hom := by
    apply cocharacter_ext
    intro R t
    have hmat : (rankOnePointsIso Fsep).inv.app R (diagonal t) =
        cocharacterPoint (m.hom ≫ E.map W.diag ≫ e.inv) R t := by
      apply (ConcreteCategory.bijective_of_isIso ((standardMatrix Fsep).hom.app R)).injective
      exact (rankOnePointsIso_inv_matrix R _).trans (hediag R t).symm
    have hCancel : (m.hom ≫ E.map W.diag ≫ e.inv) ≫ e.hom = m.hom ≫ E.map W.diag := by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hEval : (rankOnePointsIso Fsep).inv.app R (diagonal t) ≫ e.hom.hom.hom =
        cocharacterPoint (m.hom ≫ E.map W.diag) R t := by
      rw [hmat, ← cocharacterPoint_comp, hCancel]
    calc
      cocharacterPoint (extendCocharacter m (W.diag ≫ j)) R t =
          cocharacterPoint (m.hom ≫ E.map W.diag) R t ≫ (E.map j).hom.hom := by
        change cocharacterPoint (m.hom ≫ E.map (W.diag ≫ j)) R t = _
        rw [E.map_comp, ← Category.assoc, cocharacterPoint_comp]
      _ = matrixMap M g' R (diagonal t) := by
        change _ = (rankOnePointsIso Fsep).inv.app R (diagonal t) ≫ g'.hom.hom
        rw [← hEval, Category.assoc, ← Grp.comp_hom_hom, hjK]
      _ = matrixMap M g R (diagonal t) := hg'diag R t
      _ = ρ.app R (diagonal t) ≫ A.ambient.hom.hom.hom := hpoint R (diagonal t)
      _ = cocharacterPoint (c ≫ A.P.T.inclusion ≫ A.ambient.hom) R t := by
        rw [hd, cocharacterPoint_comp, Grp.comp_hom_hom, Category.assoc]
  obtain ⟨d, hdj, hdc⟩ := diagonalFactorsThroughSplitTorus A α m (W.diag ≫ j) hdiagAmbient
  let H : SplitRootSL2 A α :=
    { subgroup := ⟨(standardGroup F).val, j, hj⟩
      matrix := standardMatrix F
      positive := W.pos
      negative := W.neg
      positive_eq := W.pos_membership
      negative_eq := W.neg_membership
      generated := W.generates G j hj
      positiveAbsolute := U
      negativeAbsolute := V
      positiveIso := (E.mapIso W.posCoord).symm ≪≫ E.mapIso x' ≪≫ su
      negativeIso := (E.mapIso W.negCoord).symm ≪≫ E.mapIso y' ≪≫ sv
      positiveInclusion := descendedInclusion j W.pos W.posCoord x'
        (U.inclusion ≫ A.ambient.hom) su hsu hpos
      negativeInclusion := descendedInclusion j W.neg W.negCoord y'
        (V.inclusion ≫ A.ambient.hom) sv hsv hneg
      positiveRoot := hU
      negativeRoot := hV
      diagonal := W.diag
      diagonal_eq := by
        intro R t
        apply (congrArg Subtype.val (W.diag_matrix R t)).trans
        ext i j
        rcases i with ⟨i⟩
        rcases j with ⟨j⟩
        fin_cases i <;> fin_cases j <;> rfl
      coroot := d
      diagonalInAmbient := hdj.symm
      multiplicative := m
      multiplicative_eq := hm
      coroot_eq := hdc
      coroot_primitive := primitiveAttachedCoroot A α (fullCorootLattice A hG hsc) }
  refine ⟨H, W.weyl, ?_, ?_⟩
  · change ((standardMatrix F).hom.app _ (toUnit _ ≫ W.weyl)).val = _
    rw [W.weyl_matrix]
    ext i j
    rcases i with ⟨i⟩
    rcases j with ⟨j⟩
    fin_cases i <;> fin_cases j <;> rfl
  · apply hom_ext_on_affine_tests
    intro R t
    let w := A.absolutePoint (W.weyl ≫ j.hom.hom)
    have hwpoint : (toUnit ((testSpec Fsep).obj (op R)) ≫ w) =
        ρ.app R (diagonalConjugate (Units.map (algebraMap Fsep R) scale) (antiDiagonal R)) := by
      have hLift : toUnit ((testSpec Fsep).obj (op R)) ≫ scalarExtendedRationalPoint Fsep W.weyl =
          (rankOnePointsIso Fsep).inv.app R (antiDiagonal R) ≫ e.hom.hom.hom :=
        standardWeyl_extends W e he R
      have hSection : toUnit ((testSpec Fsep).obj (op R)) ≫
          scalarExtendedRationalPoint Fsep (W.weyl ≫ j.hom.hom) =
            (rankOnePointsIso Fsep).inv.app R (antiDiagonal R) ≫ g'.hom.hom := by
        rw [scalarExtendedPoint_natural, ← Category.assoc, hLift]
        change (((rankOnePointsIso Fsep).inv.app R (antiDiagonal R)) ≫ e.hom.hom.hom) ≫
          (E.map j).hom.hom = _
        rw [Category.assoc, ← Grp.comp_hom_hom, hjK]
      change (toUnit ((testSpec Fsep).obj (op R)) ≫
        scalarExtendedRationalPoint Fsep (W.weyl ≫ j.hom.hom)) ≫ A.ambient.inv.hom.hom = _
      rw [hSection]
      change matrixMap M g' R (antiDiagonal R) ≫ A.ambient.inv.hom.hom = _
      rw [hg'rescale R (antiDiagonal R), hpoint, Category.assoc, ← Grp.comp_hom_hom,
        A.ambient.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
    have hW : t ≫ (toUnit A.P.T.group.X ≫ w) = toUnit _ ≫ w :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ w) (toUnit_unique _ _))
    change t ≫ (torusReflectionMap α.val c ≫ A.P.T.inclusion).hom.hom =
      t ≫ ((toUnit A.P.T.group.X ≫ w) * A.P.T.inclusion.hom.hom *
        (toUnit A.P.T.group.X ≫ w)⁻¹)
    rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, hW, hwpoint]
    exact (rescaledWeyl_conjugation A.P.T α.val c ρ hx hy hp hn hd R _ t).symm


private theorem reflection_comp_inclusion {k : Type u} [Field k] {S T : GroupScheme k}
    [IsCommMonObj S.X] [IsCommMonObj T.X] (i : S ⟶ T) (χ : Character T)
    (d : Cocharacter S) (c : Cocharacter T) (h : d ≫ i = c) :
    torusReflectionMap (i ≫ χ) d ≫ i = i ≫ torusReflectionMap χ c := by
  have h' : ((i ≫ χ) ≫ d) ≫ i = i ≫ (χ ≫ c) := by
    simp only [Category.assoc, h]
  apply Grp.hom_ext
  change (𝟙 S.X * (((i ≫ χ) ≫ d).hom.hom)⁻¹) ≫ i.hom.hom =
    i.hom.hom ≫ (𝟙 T.X * (χ ≫ c).hom.hom⁻¹)
  rw [MonObj.mul_comp, MonObj.comp_mul, Category.id_comp, Category.comp_id,
    GrpObj.inv_comp, GrpObj.comp_inv, ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, h']

set_option maxHeartbeats 750000 in
/-- The marked geometric reflection preserves the scalar extension of the split
torus because its coroot factors through that torus. Conjugation descends. -/
private theorem rationalSplitConjugation (A : MarkedTori G) (α : Root A.P.T)
    (H : SplitRootSL2 A α) (w : 𝟙_ (SchemeOver F) ⟶ H.subgroup.group.X)
    (hw : let p := toUnit A.P.T.group.X ≫ A.absolutePoint (w ≫ H.subgroup.inclusion.hom.hom)
      ((markedReflection A α).hom ≫ A.P.T.inclusion).hom.hom =
        p * A.P.T.inclusion.hom.hom * p⁻¹) :
    ConjugatesSubgroups (w ≫ H.subgroup.inclusion.hom.hom) A.S A.S := by
  letI := A.datum.comm
  let E := groupBaseChange F Fsep
  let S := extendSubgroup Fsep A.S
  let i := A.splitInAbsolute
  let q := extendCocharacter H.multiplicative H.coroot
  let n := w ≫ H.subgroup.inclusion.hom.hom
  let nK : 𝟙_ (SchemeOver Fsep) ⟶ (E.obj G.val).X := scalarExtendedRationalPoint Fsep n
  have hS : IsSplitTorus S.group := splitTorus_baseChange A.maximalSplit.1
  obtain ⟨hc, _⟩ := RootData.CharacterPairing.perfectCharacterPairing S.group hS
  letI : IsCommMonObj (E.obj A.S.group).X := hc
  have hq : q ≫ i = markedCoroot A α := H.coroot_eq
  have hp : pairing S.group (i ≫ α.val) q = 2 := by
    calc
      _ = pairing A.P.T.group α.val (q ≫ i) := by
        unfold pairing compositionPairing
        exact congrArg _ (Category.assoc q i α.val).symm
      _ = 2 := by rw [hq, coroot_pairing_eq_two]
  let r := reflectionIso hS (i ≫ α.val) q hp
  have hr : r.hom ≫ i = i ≫ (markedReflection A α).hom :=
    reflection_comp_inclusion i α.val q (markedCoroot A α) hq
  have hi : i ≫ A.P.T.inclusion ≫ A.ambient.hom = S.inclusion := markedSplitIncl A
  have he : r.hom ≫ S.inclusion = i ≫ (markedReflection A α).hom ≫
      A.P.T.inclusion ≫ A.ambient.hom := by
    rw [← hi, ← Category.assoc r.hom, hr, Category.assoc]
  apply conjugates_descend Fsep
  refine ⟨r, ?_⟩
  let aK : S.group.X ⟶ (E.obj G.val).X := toUnit S.group.X ≫ nK
  change (r.hom ≫ S.inclusion).hom.hom = aK * S.inclusion.hom.hom * aK⁻¹
  have hInc : i.hom.hom ≫ A.P.T.inclusion.hom.hom ≫ A.ambient.hom.hom.hom = S.inclusion.hom.hom :=
    congrArg (Grp.forget (SchemeOver Fsep)).map hi
  have hpoint : A.absolutePoint n ≫ A.ambient.hom.hom.hom = nK := by
    change (nK ≫ A.ambient.inv.hom.hom) ≫ A.ambient.hom.hom.hom = nK
    rw [Category.assoc, ← Grp.comp_hom_hom, A.ambient.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  let p := toUnit A.P.T.group.X ≫ A.absolutePoint n
  have hConj : ((markedReflection A α).hom ≫ A.P.T.inclusion).hom.hom =
      p * A.P.T.inclusion.hom.hom * p⁻¹ := hw
  have hMap : i.hom.hom ≫ p ≫ A.ambient.hom.hom.hom = aK := by
    change i.hom.hom ≫ (toUnit A.P.T.group.X ≫ A.absolutePoint n) ≫
      A.ambient.hom.hom.hom = toUnit S.group.X ≫ nK
    rw [Category.assoc (toUnit A.P.T.group.X), hpoint, ← Category.assoc i.hom.hom,
      toUnit_unique (i.hom.hom ≫ toUnit A.P.T.group.X)]
  calc
    _ = i.hom.hom ≫ ((markedReflection A α).hom ≫ A.P.T.inclusion).hom.hom ≫
        A.ambient.hom.hom.hom := by
      rw [he]
      simp only [Grp.comp_hom_hom, Category.assoc]
    _ = _ := by
      rw [hConj]
      simp only [MonObj.mul_comp, MonObj.comp_mul, GrpObj.inv_comp, GrpObj.comp_inv, hMap, hInc]

/-- A singleton absolute root line gives an actual rational split SL₂
and a rational representative of its marked reflection. -/
theorem singletonRootSL2 : SingletonRootSL2.{u} := by
  intro F _ _ _ _ G hG hsc A α hα
  obtain ⟨H, w, hw, ha⟩ := splitRankOneWithAbsoluteReflection A α hG hsc hα
  obtain ⟨s, hs⟩ := rationalSplitConjugation A α H w ha
  refine ⟨H, ⟨{
    representative := w
    representative_eq := hw
    splitConjugation := s
    splitConjugates := hs
    absoluteConjugation := markedReflection A α
    absoluteConjugates := ha
    characterReflection := markedCharacterReflection A α
    cocharacterReflection := cocharacterReflectionOfCharacterReflection A α
      (markedReflection A α) (markedCharacterReflection A α) }⟩⟩


end Assembly


end

end LinearAlgebraicGroups.Arithmetic.ExceptionalSingletonRootSL2
