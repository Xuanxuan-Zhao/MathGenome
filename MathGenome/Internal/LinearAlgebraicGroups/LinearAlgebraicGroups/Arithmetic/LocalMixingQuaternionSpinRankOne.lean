import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalMixingQuaternionSpinRankOne
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuaternionSpinOddCharacteristic
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuaternionSpinCharacteristicTwo
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.MaximalSplitTori
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RelativeChambers
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory ValuativeRel Matrix
open scoped CategoryTheory.MonObj Matrix TensorProduct

universe u v

namespace LinearAlgebraicGroups.Arithmetic.LocalMixingQuaternionSpinRankOne

open LinearAlgebraicGroups.Specs
open _root_.Specs.RM03.CSA (degree isCentralSimple)
open _root_.RM03.Brauer.SemilinearDescent (AlgebraAction)
open LocalAlgebraicTransport (RationalPoints pointTopology)
open CocharacterDynamics
open CharacterDescent (Cocharacter)
open Specs.Arithmetic.NontrialitarianSpinModels (DescendedQuadraticPair SpinModel)
open Specs.Arithmetic.QuaternionSpinScaleCover
  (QuaternionHyperbolicPresentation QuaternionPairIndex spinVectorProjection)
open Specs.Arithmetic.QuaternionScalarCliffordLift (LiftsScalarPair scalarDiagonal scalarPairMatrix)
open Specs.Arithmetic.QuaternionSpinCharacteristicTwo (oppositeWords)
open Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open SymplecticDatumRankOneAndPinning (determinantOnePoints)
open AdjointRepresentation (GroupPoints)
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus)
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

open private scalarSpecialLinearEquiv rationalRadicals radicals_eq_top
  nonarchimedean_local_infinite from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuaternionSpinOddCharacteristic
open private quaternion_generation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuaternionSpinCharacteristicTwo
open private unitEquiv unitEquiv_unitPoint evalLaurent evalLaurent_parameter evalLaurent_constants
  opposite_point centralizes_onAlgebras centralizes_hasLimit orbit_eval
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private cocharacterPoint_comp hasLimit_iso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.BruhatOrbitParametrization
open private cocharacter_in_maximal_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
open private reductive_of_semisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
open private innerIso comp_innerMap from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.BorelProper
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private rationalSourceIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalDensity
open private tensorLaurent tensorLaurent_symm_single
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuaternionHermitianCocharacters
open private cocharacter_at_one vectorMatrix_map from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuaternionSpinOddCharacteristic
open private splitTorus_commutative from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeneralLinearStructure
open private map_transvection from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuaternionScalarCliffordLift

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K] [Fintype I] [DecidableEq I]
  [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ}
  {hB : isCentralSimple F B} {d : ℕ}

private def reindexPoints :
    Specs.StandardGroups.specialLinearPoints F (ULift.{u} (Fin 2)) ≅ determinantOnePoints F :=
  NatIso.ofComponents (fun R => (scalarSpecialLinearEquiv R).toGrpIso)
    (by
      intro R S a
      apply GrpCat.ext
      intro g
      exact Subtype.ext rfl)

private theorem cocharacter_ext {H : GroupScheme F} {a b : Cocharacter H}
    (h : ∀ (R : TestAlgebra F) (s : Rˣ), cocharacterPoint a R s = cocharacterPoint b R s) :
    a = b := by
  apply Grp.hom_ext
  let M := Specs.DiagonalizableGroups.groupAlgebra F
    Specs.DiagonalizableGroups.IntegerCharacters.{u}
  let R := CommAlgCat.of F M
  have hp : unitPoint R (unitEquiv R (𝟙 _)) = 𝟙 _ :=
    (unitEquiv R).injective (unitEquiv_unitPoint R _)
  have he := h R (unitEquiv R (𝟙 _))
  change (unitPoint R _ ≫ a.hom.hom) = (unitPoint R _ ≫ b.hom.hom) at he
  rw [hp] at he
  change (𝟙 _ ≫ a.hom.hom) = 𝟙 _ ≫ b.hom.hom at he
  simpa only [Category.id_comp] using he

private theorem cocharacter_ext_laurent {H : GroupScheme F} {a b : Cocharacter H}
    (h : cocharacterPoint a (laurentAlgebra (CommAlgCat.of F F))
      (laurentParameter (CommAlgCat.of F F)) =
      cocharacterPoint b (laurentAlgebra (CommAlgCat.of F F))
      (laurentParameter (CommAlgCat.of F F))) : a = b := by
  apply cocharacter_ext
  intro R s
  let f := evalLaurent (CommAlgCat.ofHom (Algebra.ofId F R)) s
  have h' := congrArg (mapPoints f) h
  rw [mapPoints_cocharacterPoint, mapPoints_cocharacterPoint, evalLaurent_parameter] at h'
  exact h'

private theorem oppositeWords_eq_top_of_sections {a : Cocharacter G.val}
    (U : LimitDecomposition a) (V : LimitDecomposition (oppositeCocharacter a))
    (h : rationalRadicals U V = ⊤) : oppositeWords a = ⊤ := by
  have hle : rationalRadicals U V ≤ oppositeWords a := by
    apply sup_le
    · rintro p ⟨q, rfl⟩
      exact Subgroup.subset_closure (Or.inl ((U.contracting_points ..).mpr ⟨q, rfl⟩))
    · rintro p ⟨q, rfl⟩
      exact Subgroup.subset_closure (Or.inr ((V.contracting_points ..).mpr ⟨q, rfl⟩))
  exact top_unique (h ▸ hle)

/-- The marked scalar subgroup and its diagonal before rational conjugation. -/
private theorem scalarRankOne [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [FiniteDimensional F K] [IsGalois F K] (M : SpinModel G D) (Q : QuaternionHyperbolicPresentation D hB d)
    (hG : IsAbsolutelyAlmostSimple G) (hrank : 4 ≤ Fintype.card I)
    (hd : degree F B = 2) (hpos : (2 : F) ≠ 0 → 0 < d) :
    ∃ (A : AffineAlgebraicGroup F) (e : (groupPointsFunctor F).obj A.val ≅ determinantOnePoints F)
      (j : A.val ⟶ G.val) (b : Cocharacter A.val),
      IsClosedImmersion j.hom.hom.left ∧ LiftsScalarPair M Q e j ∧
      (∀ (R : TestAlgebra F) (s : Rˣ), e.hom.app R (cocharacterPoint b R s) = scalarDiagonal s) ∧
      oppositeWords (b ≫ j) = ⊤ := by
  classical
  by_cases htwo : (2 : F) = 0
  · let : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr htwo
    obtain ⟨A, e, j, _, _, hj, hlift, _, ⟨b, hb, hdiag, _, _⟩, _⟩ :=
      QuaternionScalarCliffordLift.scalarCliffordLift M hrank hB hd Q
    obtain ⟨_, a, ha, _, _, _, hgen, _⟩ := quaternion_generation M hrank hd Q
    have heq : b ≫ j = a := by
      apply cocharacter_ext_laurent
      let R := laurentAlgebra (CommAlgCat.of F F)
      let s := laurentParameter (CommAlgCat.of F F)
      apply QuaternionScalarCliffordLift.spinVectorProjection_injective_of_reduced M R
      apply Units.ext
      apply (Q.matrixAt R).injective
      exact (hdiag R s).trans (ha R s).symm
    exact ⟨A, e, j, b, hj, hlift, hb, heq.symm ▸ hgen⟩
  · let := nonarchimedean_local_infinite F
    obtain ⟨a, L, _, ⟨A, e', j, hj, hjmat, ha, _⟩, _,
        ⟨N, v, _, hv, _, _, hn, _, hvwords⟩, ⟨⟨U⟩, ⟨V⟩⟩, _⟩ :=
      QuaternionSpinOddCharacteristic.localGeneration.1 M hG hrank htwo hB hd d (hpos htwo) Q
    let e := e' ≪≫ reindexPoints (F := F)
    obtain ⟨b, hb⟩ := QuaternionScalarCliffordLift.determinantOne_diagonal e
    have hjformula : LiftsScalarPair M Q e j := by
      intro R p
      exact hjmat R p
    have heq : b ≫ j = a := by
      apply cocharacter_ext
      intro R s
      obtain ⟨_, p, hp, hjp⟩ := ha R s
      have hp' : e.hom.app R p = scalarDiagonal s := Subtype.ext hp
      have he : cocharacterPoint b R s = p := by
        apply (e.app R).groupIsoToMulEquiv.injective
        exact (hb R s).trans hp'.symm
      change (cocharacterPoint b R s ≫ j.hom.hom) = cocharacterPoint a R s
      rw [he, hjp]
    have htop := radicals_eq_top Q M hG htwo hd (hpos htwo) L
      (fun R s => (ha R s).1) N v hv hn hvwords U V
    exact ⟨A, e, j, b, hj, hjformula, hb, heq.symm ▸ oppositeWords_eq_top_of_sections U V htop⟩

private abbrev scalarPoint {A : AffineAlgebraicGroup F}
    (e : (groupPointsFunctor F).obj A.val ≅ determinantOnePoints F) (j : A.val ⟶ G.val)
    (R : TestAlgebra F) (z : Matrix.SpecialLinearGroup (Fin 2) R) : Points G.val.X R :=
  e.inv.app R z ≫ j.hom.hom

private abbrev upper {R : Type u} [CommRing R] (x : R) : Matrix.SpecialLinearGroup (Fin 2) R :=
  Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) x

private abbrev lower {R : Type u} [CommRing R] (x : R) : Matrix.SpecialLinearGroup (Fin 2) R :=
  Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) x

private theorem inverse_point_eval {A : AffineAlgebraicGroup F}
    (e : (groupPointsFunctor F).obj A.val ≅ determinantOnePoints F)
    (R : TestAlgebra F) (z : Matrix.SpecialLinearGroup (Fin 2) R) :
    e.hom.app R (e.inv.app R z) = z :=
  (e.app R).groupIsoToMulEquiv.apply_symm_apply z

private theorem diagonal_limits {A : AffineAlgebraicGroup F}
    (e : (groupPointsFunctor F).obj A.val ≅ determinantOnePoints F)
    (j : A.val ⟶ G.val) (b : Cocharacter A.val)
    (hb : ∀ (R : TestAlgebra F) (s : Rˣ), e.hom.app R (cocharacterPoint b R s) = scalarDiagonal s)
    (R : TestAlgebra F) (x : R) :
    HasLimit (b ≫ j) (scalarPoint e j R (upper x)) 1 ∧
      HasLimit (oppositeCocharacter (b ≫ j)) (scalarPoint e j R (lower x)) 1 := by
  refine ⟨?_, ?_⟩
  · exact (QuaternionScalarCliffordLift.determinantOne_contracts e b hb j R
      (e.inv.app R (upper x)) x).1 (inverse_point_eval e R (upper x))
  · exact (QuaternionScalarCliffordLift.determinantOne_contracts e b hb j R
      (e.inv.app R (lower x)) x).2 (inverse_point_eval e R (lower x))

private theorem centralizes_comp_of_centralizes {L H : GroupScheme F} (i : L ⟶ H)
    (j : H ⟶ G.val) (p : RationalPoints G.val.X) (h : Centralizes j p) :
    Centralizes (i ≫ j) p := by
  apply (centralizes_iff (i ≫ j) p).mpr
  intro T a x
  have hh := (centralizes_iff j p).mp h T a (x ≫ i.hom.hom)
  change Commute (a ≫ p) (x ≫ i.hom.hom ≫ j.hom.hom)
  simpa only [Category.assoc] using hh

private theorem centralizes_transport (E : G.val ≅ G.val) (a : Cocharacter G.val)
    (p : RationalPoints G.val.X) :
    Centralizes (a ≫ E.hom) (p ≫ E.hom.hom.hom) ↔ Centralizes a p := by
  let R := CommAlgCat.of F F
  let f (S : TestAlgebra F) := (((groupPointsFunctor F).mapIso E).app S).groupIsoToMulEquiv
  rw [centralizes_onAlgebras (a ≫ E.hom)
    (R := R) (show GroupPoints G.val R from p ≫ E.hom.hom.hom),
    centralizes_onAlgebras a (R := R) (show GroupPoints G.val R from p)]
  have hc (S : TestAlgebra F) (m : R ⟶ S) (s : Sˣ) :
      Commute (mapPoints m (show GroupPoints G.val R from p ≫ E.hom.hom.hom))
        (cocharacterPoint (a ≫ E.hom) S s) ↔
      Commute (mapPoints m p : GroupPoints G.val S) (cocharacterPoint a S s) := by
    have hm : f S (mapPoints m p) = mapPoints m (p ≫ E.hom.hom.hom) :=
      by
        change (((testSpec F).map m.op ≫ p) ≫ E.hom.hom.hom) =
          (testSpec F).map m.op ≫ p ≫ E.hom.hom.hom
        exact Category.assoc _ _ _
    have ha : f S (cocharacterPoint a S s) = cocharacterPoint (a ≫ E.hom) S s :=
      (cocharacterPoint_comp a E.hom S s).symm
    rw [← hm, ← ha]
    constructor
    · intro h
      let p' : ↑(GroupPoints G.val S) := mapPoints m p
      let a' : ↑(GroupPoints G.val S) := cocharacterPoint a S s
      change p' * a' = a' * p'
      apply (f S).injective
      exact ((f S).map_mul p' a').trans (h.eq.trans ((f S).map_mul a' p').symm)
    · intro h
      exact h.map (f S).toMonoidHom
  exact ⟨fun h S m s => (hc S m s).mp (h S m s),
    fun h S m s => (hc S m s).mpr (h S m s)⟩

private theorem opposite_comp (a : Cocharacter G.val) (f : G.val ⟶ G.val) :
    oppositeCocharacter (a ≫ f) = oppositeCocharacter a ≫ f :=
  (Category.assoc _ _ _).symm

private theorem generation_transport (E : G.val ≅ G.val) {a : Cocharacter G.val}
    (h : oppositeWords a = ⊤) : oppositeWords (a ≫ E.hom) = ⊤ := by
  let R := CommAlgCat.of F F
  let e := (((groupPointsFunctor F).mapIso E).app R).groupIsoToMulEquiv
  have hmap : (oppositeWords a).map e.toMonoidHom ≤ oppositeWords (a ≫ E.hom) := by
    unfold oppositeWords
    rw [MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨p, hp, rfl⟩
    rcases hp with hp | hp
    · exact Or.inl ((hasLimit_iso E a p).mpr hp)
    · rw [opposite_comp]
      exact Or.inr ((hasLimit_iso E (oppositeCocharacter a) p).mpr hp)
  have ht := Subgroup.map_top_of_surjective (e.toMonoidHom) e.surjective
  rw [h, ht] at hmap
  exact top_unique hmap

private theorem reindex_upper {R : Type u} [CommRing R] (x : R) :
    scalarSpecialLinearEquiv R (Matrix.SpecialLinearGroup.transvection
      (show (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)) ≠ ULift.up 1 by decide) x) = upper x := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change (Matrix.transvection (ULift.up (0 : Fin 2)) (ULift.up (1 : Fin 2)) x)
    (ULift.up i) (ULift.up j) = Matrix.transvection (0 : Fin 2) 1 x i j
  simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply]

private theorem reindex_lower {R : Type u} [CommRing R] (x : R) :
    scalarSpecialLinearEquiv R (Matrix.SpecialLinearGroup.transvection
      (show (ULift.up (1 : Fin 2) : ULift.{u} (Fin 2)) ≠ ULift.up 0 by decide) x) = lower x := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change (Matrix.transvection (ULift.up (1 : Fin 2)) (ULift.up (0 : Fin 2)) x)
    (ULift.up i) (ULift.up j) = Matrix.transvection (1 : Fin 2) 0 x i j
  simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply]

open AddMonoidAlgebra
open Specs.SymplecticDivisionForms (tensorMap)

private theorem coeff_mul_at_pair {B : Type u} [DivisionRing B]
    (x y : AddMonoidAlgebra B ℤ) (i j : ℤ)
    (h : ∀ a ∈ x.coeff.support, ∀ b ∈ y.coeff.support, a + b = i + j → a = i) :
    (x * y).coeff (i + j) = x.coeff i * y.coeff j := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  classical
  unfold Finsupp.sum
  rw [Finset.sum_eq_single i]
  · dsimp only
    rw [show -i + (i + j) = j by omega]
  · intro a ha hai
    have hy : y.coeff (-a + (i + j)) = 0 := by
      by_contra hne
      exact hai (h a ha _ (Finsupp.mem_support_iff.mpr hne) (by omega))
    simp only [hy, mul_zero]
  · intro hi
    simp only [Finsupp.notMem_support_iff.mp hi, zero_mul]

/-- The extreme support degrees add under multiplication over a division ring. -/
private theorem unit_monomial {B : Type u} [DivisionRing B] (z : (AddMonoidAlgebra B ℤ)ˣ) :
    ∃ (n : ℤ) (b : B), (z : AddMonoidAlgebra B ℤ) = single n b := by
  let x : AddMonoidAlgebra B ℤ := z
  let y : AddMonoidAlgebra B ℤ := ↑z⁻¹
  have hxy : x * y = 1 := z.val_inv
  have hx : x.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr (by
    intro h; apply z.ne_zero; exact AddMonoidAlgebra.coeff_injective h)
  have hy : y.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr (by
    intro h; apply (z⁻¹).ne_zero; exact AddMonoidAlgebra.coeff_injective h)
  let a := x.coeff.support.min' hx
  let b := y.coeff.support.min' hy
  let A := x.coeff.support.max' hx
  let B' := y.coeff.support.max' hy
  have ha : a ∈ x.coeff.support := Finset.min'_mem _ _
  have hb : b ∈ y.coeff.support := Finset.min'_mem _ _
  have hA : A ∈ x.coeff.support := Finset.max'_mem _ _
  have hB : B' ∈ y.coeff.support := Finset.max'_mem _ _
  have eqlo := coeff_mul_at_pair x y a b (fun i hi j hj h => by
    have hi' : a ≤ i := Finset.min'_le _ _ hi
    have hj' : b ≤ j := Finset.min'_le _ _ hj
    omega)
  have eqhi := coeff_mul_at_pair x y A B' (fun i hi j hj h => by
    have hi' : i ≤ A := Finset.le_max' _ _ hi
    have hj' : j ≤ B' := Finset.le_max' _ _ hj
    omega)
  have hzero {i j : ℤ} (hi : i ∈ x.coeff.support) (hj : j ∈ y.coeff.support)
      (he : (x * y).coeff (i + j) = x.coeff i * y.coeff j) : i + j = 0 := by
    have hp := mul_ne_zero (Finsupp.mem_support_iff.mp hi) (Finsupp.mem_support_iff.mp hj)
    by_contra h
    apply hp
    rw [← he, hxy, AddMonoidAlgebra.one_def, coeff_single, Finsupp.single_apply]
    simp [Ne.symm h]
  have hal := Finset.le_max' _ _ ha
  have hbl := Finset.le_max' _ _ hb
  change a ≤ A at hal
  change b ≤ B' at hbl
  have hsame : a = A := by
    have h₁ := hzero ha hb eqlo
    have h₂ := hzero hA hB eqhi
    omega
  refine ⟨a, x.coeff a, ?_⟩
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro i
  by_cases hi : i = a
  · subst i
    rw [coeff_single, Finsupp.single_eq_same]
  · have hx' : x.coeff i = 0 := by
      by_contra hn
      have hm := Finsupp.mem_support_iff.mpr hn
      have hm₁ : a ≤ i := Finset.min'_le _ _ hm
      have hm₂ : i ≤ A := Finset.le_max' _ _ hm
      omega
    simpa only [coeff_single, Finsupp.single_apply, ite_eq_right (Ne.symm hi)] using hx'

private abbrev ground (F : Type u) [Field F] := CommAlgCat.of F F

private def laurentAtOne : laurentAlgebra (ground F) ⟶ ground F :=
  evalLaurent (𝟙 (ground F)) 1

private theorem laurentAtOne_T (n : ℤ) :
    (laurentAtOne (F := F)).hom (LaurentPolynomial.T n) = 1 := by
  change LaurentPolynomial.eval₂ (RingHom.id F) (1 : Fˣ) (LaurentPolynomial.T n) = 1
  simp [LaurentPolynomial.eval₂_T]

private theorem normalizedLaurentUnit
    (z : (laurentAlgebra (ground F) ⊗[F] B)ˣ)
    (hz : tensorMap B (laurentAtOne (F := F)).hom z.val = 1) :
    ∃ n : ℤ, z.val = algebraMap (laurentAlgebra (ground F))
      (laurentAlgebra (ground F) ⊗[F] B) (LaurentPolynomial.T n) := by
  let f := tensorLaurent (F := F) (B := B)
  obtain ⟨n, v, hv⟩ := unit_monomial (Units.map f.toMonoidHom z)
  have h := congrArg f.symm hv
  change f.symm (f z.val) = f.symm (AddMonoidAlgebra.single n v) at h
  rw [AlgEquiv.symm_apply_apply] at h
  change z.val = _ at h
  have hh : z.val = (LaurentPolynomial.T n : laurentAlgebra (ground F)) ⊗ₜ[F] v :=
    h.trans (tensorLaurent_symm_single n v)
  rw [hh] at hz
  change (laurentAtOne (F := F)).hom (LaurentPolynomial.T n) ⊗ₜ[F] v = _ at hz
  rw [laurentAtOne_T] at hz
  have hv₁ : v = 1 := by
    simpa using congrArg (Algebra.TensorProduct.lid F B) hz
  subst v
  exact ⟨n, hh⟩

private theorem row_col_zero_of_commute {C : Type u} [Ring C] [Algebra F C]
    {J : Type v} [Fintype J] [DecidableEq J] (X : Matrix J J C)
    (w : J → F) (hw : Commute (Matrix.diagonal fun i => algebraMap F C (w i)) X)
    (i j : J) (h : w i ≠ w j) : X i j = 0 := by
  have he := congrArg (fun M : Matrix J J C => M i j) hw.eq
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, ← (Algebra.commutes (w j) (X i j)),
    ← Algebra.smul_def, ← Algebra.smul_def] at he
  have hz : (w i - w j) • X i j = 0 := by rw [sub_smul, he, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr h)

private def matrixEntryUnit {C : Type u} {J : Type v} [Ring C] [Fintype J] [DecidableEq J]
    (X : (Matrix J J C)ˣ) (i : J)
    (hrow : ∀ j ≠ i, X.val i j = 0) (hcol : ∀ j ≠ i, X.val j i = 0) : Cˣ where
  val := X.val i i
  inv := X.inv i i
  val_inv := by
    have h := congrArg (fun M : Matrix J J C => M i i) X.val_inv
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at h
    · simpa only [Matrix.one_apply_eq] using h
    · intro j _ hj
      rw [hrow j hj, zero_mul]
    · intro hi
      exact (hi (Finset.mem_univ _)).elim
  inv_val := by
    have h := congrArg (fun M : Matrix J J C => M i i) X.inv_val
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at h
    · simpa only [Matrix.one_apply_eq] using h
    · intro j _ hj
      rw [hcol j hj, mul_zero]
    · intro hi
      exact (hi (Finset.mem_univ _)).elim

private theorem conjugate_single {C : Type u} {J : Type v} [Ring C] [Fintype J] [DecidableEq J]
    (X : (Matrix J J C)ˣ) (i j : J) (x : C)
    (hcol : ∀ k ≠ i, X.val k i = 0) (hrow : ∀ k ≠ j, (↑X⁻¹ : Matrix J J C) j k = 0) :
    X.val * (1 + Matrix.single i j x) * (↑X⁻¹ : Matrix J J C) =
      1 + Matrix.single i j (X.val i i * x * (↑X⁻¹ : Matrix J J C) j j) := by
  have h₁ : X.val * Matrix.single i j x = Matrix.single i j (X.val i i * x) := by
    ext a b
    by_cases hb : b = j
    · subst b
      rw [Matrix.mul_single_apply_same]
      by_cases ha : a = i
      · subst a
        exact (Matrix.single_apply_same _ _ _).symm
      · rw [hcol a ha, zero_mul, Matrix.single_apply_of_row_ne (Ne.symm ha) _ _ _]
    · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hb,
        Matrix.single_apply_of_col_ne _ _ (Ne.symm hb) _]
  have h₂ : Matrix.single i j (X.val i i * x) * (↑X⁻¹ : Matrix J J C) =
      Matrix.single i j (X.val i i * x * (↑X⁻¹ : Matrix J J C) j j) := by
    ext a b
    by_cases ha : a = i
    · subst a
      rw [Matrix.single_mul_apply_same]
      by_cases hb : b = j
      · subst b
        exact (Matrix.single_apply_same _ _ _).symm
      · rw [hrow b hb, mul_zero, Matrix.single_apply_of_col_ne _ _ (Ne.symm hb) _]
    · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ ha,
        Matrix.single_apply_of_row_ne (Ne.symm ha) _ _ _]
  rw [mul_add, mul_one, add_mul, show X.val * (↑X⁻¹ : Matrix J J C) = 1 from X.val_inv, h₁, h₂]

/-- Equality in the vector image and at one specialization determines a lift over a domain. -/
private theorem spin_eq_of_eval {R : TestAlgebra F} [IsDomain R]
    (M : SpinModel G D) (f : R ⟶ ground F) {p q : GroupPoints G.val R}
    (h : spinVectorProjection M R p = spinVectorProjection M R q)
    (he : mapPoints f p = mapPoints f q) : p = q := by
  let π := (((groupPointsFunctor F).map M.projection).app R).hom
  have hπ : π p = π q := by
    let : IsOpenImmersion M.inclusion.hom.hom.left := M.openImmersion
    let : Mono M.inclusion.hom.hom := Over.mono_of_mono_left _
    apply (cancel_mono M.inclusion.hom.hom).mp
    apply M.fullFaithful R
    change M.fullPoints R ((p ≫ M.projection.hom.hom) ≫ M.inclusion.hom.hom) =
      M.fullPoints R ((q ≫ M.projection.hom.hom) ≫ M.inclusion.hom.hom)
    rw [Category.assoc, Category.assoc]
    exact h
  have hk : π (p * q⁻¹) = 1 := by rw [map_mul, map_inv, hπ, mul_inv_cancel]
  let z : Points M.kernel.group.X R := M.isKernel.lift (p * q⁻¹) (toUnit _) hk
  have hz : z ≫ M.kernel.inclusion.hom.hom = p * q⁻¹ := M.isKernel.lift_fst _ _ _
  have hs : mapPoints f z = 1 := by
    let := M.kernel.isClosedImmersion
    let : Mono M.kernel.inclusion.hom.hom := Over.mono_of_mono_left _
    apply (cancel_mono M.kernel.inclusion.hom.hom).mp
    change mapPoints f (z ≫ M.kernel.inclusion.hom.hom) = _
    rw [hz, MonObj.one_comp]
    let m := (((groupPointsFunctor F).obj G.val).map f).hom
    change m (p * q⁻¹) = 1
    rw [map_mul, map_inv, show m p = m q from he, mul_inv_cancel]
  let w : Rˣ := (M.kernelPoints R z).val
  have hw : (w : R) ^ 2 = 1 := (mem_rootsOfUnity' 2 w).mp (M.kernelPoints R z).property
  have hf : f.hom w.val = 1 := by
    rw [← M.kernelNatural R (ground F) f z, hs, map_one]
    rfl
  have h' : w.val = 1 := by
    rcases sq_eq_one_iff.mp hw with h' | h'
    · exact h'
    · rw [h', map_neg, map_one] at hf
      have hF : -(1 : F) = 1 := hf
      rw [h']
      simpa using congrArg (algebraMap F R) hF
  have hz₁ : z = 1 := (M.kernelPoints R).injective
    (by rw [map_one]; exact Subtype.ext (Units.ext h'))
  apply mul_inv_eq_one.mp
  rw [← hz, hz₁, MonObj.one_comp]

private def vectorUnits (M : SpinModel G D) (Q : QuaternionHyperbolicPresentation D hB d)
    (R : TestAlgebra F) :
    Points G.val.X R →* (Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) (R ⊗[F] B))ˣ :=
  (Units.map (Q.matrixAt R).toMonoidHom).comp (spinVectorProjection M R)

private theorem scalarPoint_natural {A : AffineAlgebraicGroup F}
    (e : (groupPointsFunctor F).obj A.val ≅ determinantOnePoints F)
    (j : A.val ⟶ G.val) {R S : TestAlgebra F} (f : R ⟶ S)
    (m : Matrix.SpecialLinearGroup (Fin 2) R) :
    mapPoints f (scalarPoint e j R m) =
      scalarPoint e j S (Matrix.SpecialLinearGroup.map f.hom.toRingHom m) := by
  have h := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (e.inv.naturality f)) m
  change e.inv.app S (Matrix.SpecialLinearGroup.map f.hom.toRingHom m) =
    mapPoints f (e.inv.app R m) at h
  change (testSpec F).map f.op ≫ e.inv.app R m ≫ j.hom.hom = _
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun p : Points A.val.X S => p ≫ j.hom.hom) h.symm)

private theorem scalarPair_transvection (R : TestAlgebra F) {i j : Fin 2}
    (hij : i ≠ j) (x : R) :
    scalarPairMatrix (B := B) (d := d) R (Matrix.SpecialLinearGroup.transvection hij x) =
      1 + Matrix.single (Sum.inl i) (Sum.inl j) (algebraMap R (R ⊗[F] B) x) := by
  ext (a | a) (b | b)
  · change algebraMap R (R ⊗[F] B) ((1 : Matrix (Fin 2) (Fin 2) R) a b +
      Matrix.single i j x a b) =
      (1 : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) (R ⊗[F] B))
        (Sum.inl a) (Sum.inl b) + Matrix.single (Sum.inl i) (Sum.inl j)
        (algebraMap R (R ⊗[F] B) x) (Sum.inl a) (Sum.inl b)
    simp only [map_add, Matrix.one_apply, Matrix.single_apply, Sum.inl.injEq]
    split <;> split <;> simp only [map_one, map_zero]
  · simp [scalarPairMatrix]
  · simp [scalarPairMatrix]
  · simp [scalarPairMatrix, Matrix.one_apply]

private theorem vectorUnits_scalarPoint (M : SpinModel G D)
    (Q : QuaternionHyperbolicPresentation D hB d) {A : AffineAlgebraicGroup F}
    (e : (groupPointsFunctor F).obj A.val ≅ determinantOnePoints F)
    (j : A.val ⟶ G.val) (hj : LiftsScalarPair M Q e j)
    (R : TestAlgebra F) (m : Matrix.SpecialLinearGroup (Fin 2) R) :
    (vectorUnits M Q R (scalarPoint e j R m)).val = scalarPairMatrix R m := by
  change Q.matrixAt R (spinVectorProjection M R (e.inv.app R m ≫ j.hom.hom)).val = _
  rw [hj R (e.inv.app R m), inverse_point_eval]

private theorem scalarPair_diagonal {R : TestAlgebra F} (t : Rˣ) :
    scalarPairMatrix (B := B) (d := d) R (scalarDiagonal t) =
      Matrix.diagonal (Sum.elim ![algebraMap R (R ⊗[F] B) (t : R),
        algebraMap R (R ⊗[F] B) (↑t⁻¹ : R)] (fun _ => 1)) := by
  ext (a | a) (b | b)
  · fin_cases a <;> fin_cases b <;> simp [scalarPairMatrix, scalarDiagonal]
  · simp [scalarPairMatrix]
  · simp [scalarPairMatrix]
  · simp [scalarPairMatrix, Matrix.one_apply, Matrix.diagonal_apply]

private theorem exists_separating_unit [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : ∃ t : Fˣ,
    (t : F) ≠ 1 ∧ (↑t⁻¹ : F) ≠ 1 ∧ (t : F) ≠ (↑t⁻¹ : F) := by
  classical
  let := nonarchimedean_local_infinite F
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset F)
  have hx₀ : x ≠ 0 := fun h => hx (by simp [h])
  have hx₁ : x ≠ 1 := fun h => hx (by simp [h])
  have hx₂ : x ≠ -1 := fun h => hx (by simp [h])
  let t := Units.mk0 x hx₀
  refine ⟨t, hx₁, ?_, ?_⟩
  · intro h
    have he : t⁻¹ = 1 := Units.ext h
    exact hx₁ (Units.ext_iff.mp (inv_eq_one.mp he))
  · intro h
    have he : x ^ 2 = 1 := calc
      x ^ 2 = (t : F) * (t : F) := by rw [pow_two]; rfl
      _ = (t : F) * (↑t⁻¹ : F) := congrArg ((t : F) * ·) h
      _ = 1 := t.val_inv
    exact (sq_eq_one_iff.mp he).elim hx₁ hx₂

private theorem pairWeights_separate {t : Fˣ}
    (h₀ : (t : F) ≠ 1) (h₁ : (↑t⁻¹ : F) ≠ 1) (h₂ : (t : F) ≠ (↑t⁻¹ : F))
    (i : Fin 2) (j : QuaternionPairIndex d) (hij : j ≠ Sum.inl i) :
    Sum.elim ![(t : F), (↑t⁻¹ : F)] (fun _ => (1 : F)) j ≠
      Sum.elim ![(t : F), (↑t⁻¹ : F)] (fun _ : Fin d => (1 : F)) (Sum.inl i) := by
  rcases j with j | j
  · fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact h₂.symm
    · exact h₂
    · exact (hij rfl).elim
  · fin_cases i
    · exact Ne.symm h₀
    · exact Ne.symm h₁

/-- On each isolated quaternionic line, the universal torus element acts by a scalar monomial. -/
private theorem matrix_of_commuting_cochars [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (M : SpinModel G D) (Q : QuaternionHyperbolicPresentation D hB d)
    {A : AffineAlgebraicGroup F}
    (e : (groupPointsFunctor F).obj A.val ≅ determinantOnePoints F)
    (j : A.val ⟶ G.val) (hlift : LiftsScalarPair M Q e j)
    (b : Cocharacter A.val)
    (hb : ∀ (R : TestAlgebra F) (t : Rˣ), e.hom.app R (cocharacterPoint b R t) = scalarDiagonal t)
    (T : ClosedSubgroup G.val) (hT : IsMaximalSplitTorus T)
    (a c : Cocharacter T.group) (ha : a ≫ T.inclusion = b ≫ j) :
    let R := laurentAlgebra (ground F)
    let δ := oppositeCocharacter (c ≫ T.inclusion)
    let X := vectorUnits M Q R (cocharacterPoint δ R (laurentParameter (ground F)))
    ∃ w : Fin 2 → ℤ,
      (∀ i, X.val (Sum.inl i) (Sum.inl i) =
        algebraMap R (R ⊗[F] B) (LaurentPolynomial.T (w i))) ∧
      (∀ i, (↑X⁻¹ : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) (R ⊗[F] B))
        (Sum.inl i) (Sum.inl i) =
        algebraMap R (R ⊗[F] B) (LaurentPolynomial.T (-w i))) ∧
      (∀ (i : Fin 2) k, k ≠ Sum.inl i → X.val k (Sum.inl i) = 0) ∧
      (∀ (i : Fin 2) k, k ≠ Sum.inl i →
        (↑X⁻¹ : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) (R ⊗[F] B))
          (Sum.inl i) k = 0) := by
  classical
  intro R δ X
  obtain ⟨t, ht₀, ht₁, ht₂⟩ := exists_separating_unit (F := F)
  let u := Units.map (algebraMap F R).toMonoidHom t
  let wt : QuaternionPairIndex d → F := Sum.elim ![(t : F), (↑t⁻¹ : F)] (fun _ => 1)
  let W := Matrix.diagonal (fun i => algebraMap F (R ⊗[F] B) (wt i))
  have haM : (vectorUnits M Q R (cocharacterPoint (a ≫ T.inclusion) R u)).val = W := by
    rw [ha, cocharacterPoint_comp]
    change Q.matrixAt R (spinVectorProjection M R (cocharacterPoint b R u ≫ j.hom.hom)).val = _
    rw [hlift R _, hb, scalarPair_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    rcases i with i | i
    · fin_cases i
      · exact (IsScalarTower.algebraMap_apply F R _ _).symm
      · change algebraMap R (R ⊗[F] B) (↑u⁻¹ : R) = algebraMap F (R ⊗[F] B) (↑t⁻¹ : F)
        rw [← map_inv]
        exact (IsScalarTower.algebraMap_apply F R _ _).symm
    · exact (map_one (algebraMap F (R ⊗[F] B))).symm
  have hcomm : Commute W X.val := by
    rw [← haM]
    apply Commute.map (f := (Units.coeHom _).comp (vectorUnits M Q R))
    dsimp only [δ]
    rw [opposite_point, cocharacterPoint_comp, cocharacterPoint_comp]
    let f := (((groupPointsFunctor F).map T.inclusion).app R).hom
    change Commute (f (cocharacterPoint a R u))
      (f (cocharacterPoint c R ((laurentParameter (ground F))⁻¹)))
    apply Commute.map
    exact splitTorus_commutative hT.1 _ _ _
  have hcomm' : Commute W (↑X⁻¹ : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) (R ⊗[F] B)) := by
    exact hcomm.units_inv_right
  have hrow (i : Fin 2) (k : QuaternionPairIndex d) (hk : k ≠ Sum.inl i) :
      X.val (Sum.inl i) k = 0 :=
    row_col_zero_of_commute X.val wt hcomm (Sum.inl i) k (pairWeights_separate ht₀ ht₁ ht₂ i k hk).symm
  have hcol (i : Fin 2) (k : QuaternionPairIndex d) (hk : k ≠ Sum.inl i) :
      X.val k (Sum.inl i) = 0 :=
    row_col_zero_of_commute X.val wt hcomm _ _ (pairWeights_separate ht₀ ht₁ ht₂ i k hk)
  have hrow' (i : Fin 2) (k : QuaternionPairIndex d) (hk : k ≠ Sum.inl i) :
      (↑X⁻¹ : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) (R ⊗[F] B)) (Sum.inl i) k = 0 :=
    row_col_zero_of_commute
      (↑X⁻¹ : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) (R ⊗[F] B))
      wt hcomm' (Sum.inl i) k (pairWeights_separate ht₀ ht₁ ht₂ i k hk).symm
  let z (i : Fin 2) := matrixEntryUnit X (Sum.inl i) (hrow i) (hcol i)
  have hspec : X.val.map (tensorMap B (laurentAtOne (F := F)).hom) = 1 := by
    have hm := (vectorMatrix_map Q M (laurentAtOne (F := F))
      (cocharacterPoint δ R (laurentParameter (ground F)))).symm
    have ht : Units.map (laurentAtOne (F := F)).hom.toMonoidHom
        (laurentParameter (ground F)) = 1 :=
      evalLaurent_parameter (𝟙 (ground F)) 1
    have hs : mapPoints (laurentAtOne (F := F))
        (cocharacterPoint δ R (laurentParameter (ground F))) = (1 : Points G.val.X (ground F)) :=
      (mapPoints_cocharacterPoint (laurentAtOne (F := F)) δ _).trans
        ((congrArg (cocharacterPoint δ (ground F)) ht).trans (cocharacter_at_one (ground F)))
    rw [hs] at hm
    exact hm.trans (congrArg Units.val ((vectorUnits M Q (ground F)).map_one))
  have hz (i : Fin 2) : tensorMap B (laurentAtOne (F := F)).hom (z i).val = 1 := by
    have he := congrFun (congrFun hspec (Sum.inl i)) (Sum.inl i)
    change tensorMap B (laurentAtOne (F := F)).hom (z i).val =
      (1 : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) (ground F ⊗[F] B))
        (Sum.inl i) (Sum.inl i) at he
    exact he.trans (Matrix.one_apply_eq _)
  choose w hw using fun i => normalizedLaurentUnit (z i) (hz i)
  refine ⟨w, hw, ?_, hcol, hrow'⟩
  intro i
  have hui : (z i).val * algebraMap R (R ⊗[F] B) (LaurentPolynomial.T (-w i)) = 1 := by
    rw [hw i, ← map_mul, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero, map_one]
  exact left_inv_eq_right_inv (z i).inv_val hui

private theorem signed_contraction [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (M : SpinModel G D) (Q : QuaternionHyperbolicPresentation D hB d)
    {A : AffineAlgebraicGroup F}
    (e : (groupPointsFunctor F).obj A.val ≅ determinantOnePoints F)
    (j : A.val ⟶ G.val) (hlift : LiftsScalarPair M Q e j)
    (b : Cocharacter A.val)
    (hb : ∀ (R : TestAlgebra F) (t : Rˣ), e.hom.app R (cocharacterPoint b R t) = scalarDiagonal t)
    (T : ClosedSubgroup G.val) (hT : IsMaximalSplitTorus T)
    (a c : Cocharacter T.group) (ha : a ≫ T.inclusion = b ≫ j)
    (hreg : ∀ p : RationalPoints G.val.X, Centralizes (c ≫ T.inclusion) p →
      Centralizes (b ≫ j) p) :
    (∀ x : F, HasLimit (oppositeCocharacter (c ≫ T.inclusion))
      (scalarPoint e j (CommAlgCat.of F F) (upper x)) 1) ∨
    (∀ x : F, HasLimit (oppositeCocharacter (c ≫ T.inclusion))
      (scalarPoint e j (CommAlgCat.of F F) (lower x)) 1) := by
  classical
  let R := ground F
  let L := laurentAlgebra R
  let δ := oppositeCocharacter (c ≫ T.inclusion)
  obtain ⟨w, hw, hw', hcol, hrow'⟩ := matrix_of_commuting_cochars M Q e j hlift b hb T hT a c ha
  let trans {S : Type u} [CommRing S] {i k : Fin 2} (hik : i ≠ k) (x : S) :=
    Matrix.SpecialLinearGroup.transvection hik x
  have hLaurent {i k : Fin 2} (hik : i ≠ k) (x : F) :
      orbit δ (scalarPoint e j R (trans hik x)) =
        scalarPoint e j L (trans hik (LaurentPolynomial.T (w i - w k) * LaurentPolynomial.C x)) := by
    let p := scalarPoint e j R (trans hik x)
    let y : L := LaurentPolynomial.T (w i - w k) * LaurentPolynomial.C x
    let q := scalarPoint e j L (trans hik y)
    change orbit δ p = q
    apply spin_eq_of_eval M (laurentAtOne (F := F))
    · apply Units.ext
      apply (Q.matrixAt L).injective
      let τ : Points G.val.X L := cocharacterPoint δ L (laurentParameter R)
      let X := vectorUnits M Q L τ
      let v := vectorUnits M Q L
      have hP : (v (mapPoints (laurentConstants R) p)).val =
          1 + Matrix.single (Sum.inl i) (Sum.inl k)
            (algebraMap L (L ⊗[F] B) (LaurentPolynomial.C x)) := by
        rw [scalarPoint_natural, map_transvection, vectorUnits_scalarPoint M Q e j hlift,
          scalarPair_transvection]
        rfl
      have hQ : (v q).val = 1 + Matrix.single (Sum.inl i) (Sum.inl k)
          (algebraMap L (L ⊗[F] B) y) :=
        (vectorUnits_scalarPoint M Q e j hlift L _).trans (scalarPair_transvection L hik y)
      change (v (τ * mapPoints (laurentConstants R) p * τ⁻¹)).val = (v q).val
      rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, hP, hQ]
      change X.val * _ * (↑X⁻¹ : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d)
        (L ⊗[F] B)) = _
      rw [conjugate_single X _ _ _ (hcol i) (hrow' k), hw i, hw' k]
      congr 2
      let m := algebraMap L (L ⊗[F] B)
      change m (LaurentPolynomial.T (w i)) * m (LaurentPolynomial.C x) *
        m (LaurentPolynomial.T (-w k)) = m y
      rw [← map_mul, ← map_mul]
      congr 1
      dsimp only [y]
      rw [mul_assoc, mul_comm (LaurentPolynomial.C x), ← mul_assoc, ← LaurentPolynomial.T_add]
      rfl
    · have hy : (laurentAtOne (F := F)).hom y = x := by
        dsimp only [y]
        rw [map_mul, laurentAtOne_T, one_mul]
        exact LaurentPolynomial.eval₂_C (RingHom.id F) 1 x
      calc
        mapPoints (laurentAtOne (F := F)) (orbit δ p) = p := by
          change mapPoints (evalLaurent (𝟙 R) 1) (orbit δ p) = p
          rw [orbit_eval, cocharacter_at_one, inv_one, one_mul, mul_one]
          change (testSpec F).map ((𝟙 R).op) ≫ p = p
          rw [show (𝟙 R).op = 𝟙 (Opposite.op R) from rfl,
            CategoryTheory.Functor.map_id, Category.id_comp]
        _ = mapPoints (laurentAtOne (F := F)) q := by
          symm
          change mapPoints (laurentAtOne (F := F)) (scalarPoint e j L (trans hik y)) = p
          rw [scalarPoint_natural, map_transvection]
          change scalarPoint e j R (trans hik ((laurentAtOne (F := F)).hom y)) = p
          rw [hy]

  have hneq : w 0 ≠ w 1 := by
    intro hzero
    let p := scalarPoint e j R (upper (1 : F))
    have ho : orbit δ p = mapPoints (laurentConstants R) p := by
      rw [hLaurent (show (0 : Fin 2) ≠ 1 by decide), scalarPoint_natural, map_transvection]
      simp only [hzero, sub_self, LaurentPolynomial.T_zero, one_mul]
      rfl
    have hcent : Centralizes (c ≫ T.inclusion) p := by
      apply (centralizes_onAlgebras (c ≫ T.inclusion) (R := R) p).mpr
      intro S f t
      have hh := congrArg (mapPoints (evalLaurent f t⁻¹)) ho
      rw [orbit_eval, ← mapPoints_comp, evalLaurent_constants] at hh
      have ht : cocharacterPoint δ S t⁻¹ = cocharacterPoint (c ≫ T.inclusion) S t := by
        dsimp only [δ]
        rw [opposite_point, inv_inv]
      rw [ht] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hp := centralizes_hasLimit (b ≫ j) (hreg p hcent)
    have h₁ := (diagonal_limits e j b hb R (1 : F)).1
    let := G.property.1
    have hp1 : p = 1 := limitIsUnique (b ≫ j) hp h₁
    have hpM := vectorUnits_scalarPoint M Q e j hlift R (upper (1 : F))
    rw [show scalarPoint e j R (upper (1 : F)) = 1 from hp1, map_one,
      scalarPair_transvection] at hpM
    have hm := congrFun (congrFun hpM (Sum.inl (0 : Fin 2))) (Sum.inl (1 : Fin 2))
    have hne : (Sum.inl (0 : Fin 2) : QuaternionPairIndex d) ≠ Sum.inl 1 :=
      fun h => (by decide : (0 : Fin 2) ≠ 1) (Sum.inl.inj h)
    have hz : (0 : R ⊗[F] B) = 1 := by
      simpa only [Units.val_one, Matrix.add_apply, Matrix.one_apply_ne hne, Matrix.single_apply_same,
        map_one, zero_add] using hm
    exact (zero_ne_one : (0 : B) ≠ 1)
      (by simpa only [map_zero, map_one] using congrArg (Algebra.TensorProduct.lid F B) hz)
  have hcontract {i k : Fin 2} (hik : i ≠ k) (hpos : 0 < w i - w k) (x : F) :
      HasLimit δ (scalarPoint e j R (trans hik x)) 1 := by
    let n := (w i - w k).toNat
    have hn : (n : ℤ) = w i - w k := Int.toNat_of_nonneg hpos.le
    have hn₀ : n ≠ 0 := by omega
    let z : polynomialAlgebra R := Polynomial.X ^ n * Polynomial.C x
    refine ⟨scalarPoint e j _ (trans hik z), ?_, ?_⟩
    · rw [scalarPoint_natural, map_transvection, hLaurent hik x]
      congr 2
      change Polynomial.toLaurent (Polynomial.X ^ n * Polynomial.C x) = _
      rw [map_mul, Polynomial.toLaurent_X_pow, Polynomial.toLaurent_C, hn]
    · rw [scalarPoint_natural, map_transvection]
      have hz : (polynomialEvaluate R 0).hom z = 0 := by
        change Polynomial.eval 0 (Polynomial.X ^ n * Polynomial.C x) = 0
        simp [hn₀]
      change scalarPoint e j R (trans hik ((polynomialEvaluate R 0).hom z)) =
        (1 : Points G.val.X R)
      rw [hz]
      dsimp only [trans]
      rw [Matrix.SpecialLinearGroup.transvection_coeff_zero]
      let f := (e.app R).groupIsoToMulEquiv.symm
      change f 1 ≫ j.hom.hom = 1
      rw [map_one, MonObj.one_comp]
  rcases lt_or_gt_of_ne hneq with h | h
  · exact Or.inr (fun x => hcontract (show (1 : Fin 2) ≠ 0 by decide) (by omega) x)
  · exact Or.inl (fun x => hcontract (show (0 : Fin 2) ≠ 1 by decide) (by omega) x)

/-- The quaternionic scalar rank-one witness for the local mixing argument. -/
theorem quaternionSpinRankOne :
    Specs.Arithmetic.LocalMixingQuaternionSpinRankOne.QuaternionSpinRankOne.{u} := by
  classical
  intro F K I B _ _ _ _ _ _ _ _ _ _ _ _ ρ G D M hG hrank hB hd d hdpos Q S hS c hc
  obtain ⟨A, e, j, b, hj, hlift, hb, hgen⟩ := scalarRankOne M Q hG hrank hd hdpos
  obtain ⟨T, a, hT, ha⟩ := cocharacter_in_maximal_split (b ≫ j)
  have hred := reductive_of_semisimple G hG.1
  obtain ⟨q, qiso, hq⟩ := Relative.MaximalSplitTori.maximalSplitToriConjugate G hred T S hT hS
  let E := innerIso q
  have hinc : T.inclusion ≫ E.hom = qiso.hom ≫ S.inclusion := by
    apply Grp.hom_ext
    exact (comp_innerMap q T.inclusion.hom.hom).trans hq.symm
  let c' := c ≫ qiso.inv
  have hc' : (c' ≫ T.inclusion) ≫ E.hom = c ≫ S.inclusion := by
    simp [c', Category.assoc, hinc]
  have ha' : (b ≫ j) ≫ E.hom = (a ≫ qiso.hom) ≫ S.inclusion := by
    rw [← ha, Category.assoc, hinc, Category.assoc]
  obtain ⟨C⟩ := existsLimitDecomposition G (c ≫ S.inclusion)
  have hreg (p : RationalPoints G.val.X) (hp : Centralizes (c' ≫ T.inclusion) p) :
      Centralizes (b ≫ j) p := by
    apply (centralizes_transport E (b ≫ j) p).mp
    rw [ha']
    have hcp := (centralizes_transport E (c' ≫ T.inclusion) p).mpr hp
    rw [hc'] at hcp
    have hs := (Relative.RelativeChambers.regularLevi G hred S hS.1 c C hc _ _).mpr
      ((C.centralizer_points _ _).mp hcp)
    exact centralizes_comp_of_centralizes _ _ _ hs
  have hsign := signed_contraction M Q e j hlift b hb T hT a c' ha hreg
  let g : RationalPoints G.val.X := (rationalSourceIso F).inv ≫ q
  let e' := e ≪≫ (reindexPoints (F := F)).symm
  let j' := j ≫ E.hom
  have hj' : IsClosedImmersion j'.hom.hom.left := by
    let := hj
    let : IsIso E.hom.hom.hom.left := ((Grp.forget (SchemeOver F)) ⋙ Over.forget _).map_isIso E.hom
    change IsClosedImmersion (j.hom.hom.left ≫ E.hom.hom.hom.left)
    infer_instance
  refine ⟨A, e', j', b, g, hj', ?_, ?_, ?_, ?_, ?_⟩
  · intro R p
    let m : CommAlgCat.of F F ⟶ R := CommAlgCat.ofHom (Algebra.ofId F R)
    have hg : mapPoints m g = toUnit ((testSpec F).obj (Opposite.op R)) ≫ q := by
      change _ ≫ (rationalSourceIso F).inv ≫ q = _
      rw [← Category.assoc]
      congr 1
      change (testSpec F).map m.op ≫ (rationalSourceIso F).inv =
        toUnit ((testSpec F).obj (Opposite.op R))
      exact (Over.mkIdTerminal (X := Spec (CommRingCat.of F))).hom_ext _ _
    have hconj : p ≫ j'.hom.hom =
        mapPoints m g * (p ≫ j.hom.hom) * (mapPoints m g)⁻¹ := by
      rw [hg]
      change p ≫ j.hom.hom ≫ E.hom.hom.hom = _
      rw [← Category.assoc]
      exact comp_innerMap q _
    change Q.matrixAt R (spinVectorProjection M R
      ((mapPoints m g)⁻¹ * (p ≫ j'.hom.hom) * (mapPoints m g))).val = _
    rw [hconj, show (mapPoints m g)⁻¹ *
      (mapPoints m g * (p ≫ j.hom.hom) * (mapPoints m g)⁻¹) * mapPoints m g =
      p ≫ j.hom.hom by group]
    exact hlift R p
  · intro R t
    exact congrArg Subtype.val (hb R t)
  · intro R x
    obtain ⟨hu, hv⟩ := diagonal_limits e j b hb R x
    constructor
    · change HasLimit (b ≫ j ≫ E.hom)
        (scalarPoint e j R (scalarSpecialLinearEquiv R _) ≫ E.hom.hom.hom) 1
      rw [reindex_upper, ← Category.assoc b]
      exact (hasLimit_iso E (b ≫ j) _).mpr hu
    · change HasLimit (oppositeCocharacter (b ≫ j ≫ E.hom))
        (scalarPoint e j R (scalarSpecialLinearEquiv R _) ≫ E.hom.hom.hom) 1
      rw [reindex_lower, ← Category.assoc b, opposite_comp]
      exact (hasLimit_iso E (oppositeCocharacter (b ≫ j)) _).mpr hv
  · rcases hsign with hu | hv
    · left
      intro x
      change HasLimit (oppositeCocharacter (c ≫ S.inclusion))
        (scalarPoint e j (CommAlgCat.of F F) (scalarSpecialLinearEquiv F _) ≫ E.hom.hom.hom) 1
      rw [reindex_upper, ← hc', opposite_comp]
      exact (hasLimit_iso E (oppositeCocharacter (c' ≫ T.inclusion)) _).mpr (hu x)
    · right
      intro x
      change HasLimit (oppositeCocharacter (c ≫ S.inclusion))
        (scalarPoint e j (CommAlgCat.of F F) (scalarSpecialLinearEquiv F _) ≫ E.hom.hom.hom) 1
      rw [reindex_lower, ← hc', opposite_comp]
      exact (hasLimit_iso E (oppositeCocharacter (c' ≫ T.inclusion)) _).mpr (hv x)
  · -- Generation holds on the underlying point group, so it gives density in the specified topology.
    have htop := generation_transport E hgen
    change @Dense (RationalPoints G.val.X) (pointTopology G.val.X)
      {p | p ∈ oppositeWords (b ≫ j ≫ E.hom)}
    rw [← Category.assoc b, htop]
    have he : {p : RationalPoints G.val.X | p ∈ (⊤ : Subgroup
        (GroupPoints G.val (CommAlgCat.of F F)))} = Set.univ :=
      Set.eq_univ_of_forall fun p => Subgroup.mem_top (show GroupPoints G.val _ from p)
    rw [he]
    exact @dense_univ _ (pointTopology G.val.X)

end

end LinearAlgebraicGroups.Arithmetic.LocalMixingQuaternionSpinRankOne
