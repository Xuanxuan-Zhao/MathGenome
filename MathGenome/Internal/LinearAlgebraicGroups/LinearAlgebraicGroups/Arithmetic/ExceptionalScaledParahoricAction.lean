import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalScaledParahoricAction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.HopfAlgebras
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalResidueCentralizerAction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalResidueBorelTransport
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.SemilinearHopfFromPoints
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalScaledParahoricAction

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Pointwise TensorProduct WithZero
open _root_.LinearAlgebraicGroups.Specs
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel
open Specs.IntegralRootRelations (upper lower diagonal)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots)
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalAffineBuilding
open Specs.ExceptionalIwahoriCongruence
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation residueMap)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover MarkedLocalNormalizer integralPointHom)
open Specs.ExceptionalMarkedRootDescent (markedWeylWord markedWall wallMatrix rankOneMatrixWord)
open Specs.ExceptionalScaledParahoricAction
open ValuativeRel

open private affineTorusPointEquiv torusPoint_natural
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private elementaryWord elementaryWord_diagonal rankOneWord_reflection
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization

universe u v w

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000

private def markedTorusHom {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) : TorusValues D R →* IntegralPoints M.group R :=
  (integralPointHom M.torus R).comp
    (affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X) R).toMonoidHom

private theorem markedTorusHom_apply {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (t : TorusValues D R) :
    markedTorusHom M R t = torusPoint D R t ≫ M.torus.hom.hom := rfl

private theorem torus_changeRing {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (t : TorusValues D R) :
    changeRingHom M.group f (markedTorusHom M R t) =
      markedTorusHom M S ((Units.map f.hom.toMonoidHom).comp t) := by
  simp only [markedTorusHom_apply]
  change integralSpec.map f.op ≫ torusPoint D R t ≫ M.torus.hom.hom = _
  rw [← Category.assoc, torusPoint_natural]

private theorem markedWall_changeRing {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (i : D.I) :
    changeRingHom M.group f (markedWall M R i 1) = markedWall M S i 1 := by
  have h := DFunLike.congr_fun (congrArg GrpCat.Hom.hom ((M.rankOne i).naturality f).symm)
    (wallMatrix (1 : Rˣ))
  change _ = (M.rankOne i).app S (Matrix.SpecialLinearGroup.map f.hom.toRingHom (wallMatrix 1))
    at h
  have hm : Matrix.SpecialLinearGroup.map f.hom.toRingHom (wallMatrix (1 : Rˣ)) =
      wallMatrix (1 : Sˣ) := by
    apply Subtype.ext
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [wallMatrix, rankOneMatrixWord, upper, lower, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hm] at h
  exact h

private theorem markedWeylWord_changeRing {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (l : List D.I) :
    changeRingHom M.group f (markedWeylWord M R l) = markedWeylWord M S l := by
  induction l with
  | nil => exact map_one _
  | cons i l ih =>
    change changeRingHom M.group f (markedWall M R i 1 * markedWeylWord M R l) =
      markedWall M S i 1 * markedWeylWord M S l
    rw [map_mul, markedWall_changeRing, ih]

private def liftIntegralTorusValues {D : BasedRootDatum.{u}} {L : Type u}
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    (t : TorusValues D (integralRing L))
    (ht : ∀ χ, normalizedValuation L (t χ : L) = 1) :
    TorusValues D (localIntegers L) :=
  let v := valuation L
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L
  (v.valuationSubring.unitGroupMulEquiv.toMonoidHom).comp
    (t.codRestrict v.valuationSubring.unitGroup fun χ => by
      apply (Valuation.mem_unitGroup_iff L v (t χ)).2
      apply e.injective
      change normalizedValuation L (t χ : L) = e 1
      rw [map_one e]
      exact ht χ)

private theorem liftIntegralTorusValues_eq {D : BasedRootDatum.{u}} {L : Type u}
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    (t : TorusValues D (integralRing L)) (ht : ∀ χ, normalizedValuation L (t χ : L) = 1) :
    (Units.map (localIntegersInclusion L).hom.toMonoidHom).comp
      (liftIntegralTorusValues t ht) = t := by
  apply MonoidHom.ext
  intro χ
  apply Units.ext
  unfold liftIntegralTorusValues
  exact (valuation L).valuationSubring.coe_unitGroupMulEquiv_apply _

private theorem cocharacter_transport {D : BasedRootDatum.{u}} (g : D.datum.Equiv D.datum)
    (R : IntegralAlgebra.{u}) (v : D.Y) (s : Rˣ) :
    (cocharacter D v R s).comp g.weightEquiv.symm.toLinearMap.toAddMonoidHom.toMultiplicative =
      cocharacter D (g.coweightEquiv.symm v) R s := by
  apply MonoidHom.ext
  intro χ
  change s ^ D.datum.toLinearMap (g.weightEquiv.symm χ.toAdd) v =
    s ^ D.datum.toLinearMap χ.toAdd (g.coweightEquiv.symm v)
  have he := g.toLinearMap_weightEquiv (g.weightEquiv.symm χ.toAdd) (g.coweightEquiv.symm v)
  simpa only [LinearEquiv.apply_symm_apply] using congrArg (fun j : ℤ => s ^ j) he.symm

set_option maxHeartbeats 600000 in
private theorem markedWall_conjugates_torus {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (i : D.I) (t : TorusValues D R) :
    let n := markedWall M R i 1
    n * markedTorusHom M R t * n⁻¹ =
      markedTorusHom M R
        (t.comp (D.datum.reflection i).toLinearMap.toAddMonoidHom.toMultiplicative) := by
  let r : Matrix.SpecialLinearGroup (Fin 2) R →* IntegralPoints M.group R :=
    ((M.rankOne i).app R).hom
  let h := markedTorusHom M R
  let a := t (Multiplicative.ofAdd (D.datum.root i))
  have hu (z : R) : r (upper z) = M.line.point R z ≫ (M.root i).hom.hom :=
    M.rankOneUpper i R z
  have hl (z : R) :
      r (lower z) = M.line.point R z ≫ (M.root (D.datum.reflectionPerm i i)).hom.hom :=
    M.rankOneLower i R z
  have hUpper (z : R) : h t * r (upper z) * (h t)⁻¹ = r (upper ((a : R) * z)) := by
    rw [hu, hu]
    exact M.conjugation R t i z
  have hLower (z : R) :
      h t * r (lower z) * (h t)⁻¹ = r (lower ((↑a⁻¹ : R) * z)) := by
    have hr : D.datum.root (D.datum.reflectionPerm i i) = -D.datum.root i := by
      rw [D.datum.root_reflectionPerm, D.datum.reflection_apply_self]
    rw [hl, hl]
    have hv : t (Multiplicative.ofAdd (D.datum.root (D.datum.reflectionPerm i i))) = a⁻¹ := by
      rw [hr]
      exact map_inv t (Multiplicative.ofAdd (D.datum.root i))
    have hc := M.conjugation R t (D.datum.reflectionPerm i i) z
    dsimp only at hc
    rw [hv] at hc
    exact hc
  have hDiag (b : Rˣ) : r (diagonal b) = h (cocharacter D (D.datum.coroot i) R b) :=
    M.rankOneDiagonal i R b
  have hComm (t' : TorusValues D R) (b : Rˣ) :
      Commute (h t') (r (diagonal b)) := by
    rw [hDiag]
    show h t' * h (cocharacter D (D.datum.coroot i) R b) =
         h (cocharacter D (D.datum.coroot i) R b) * h t'
    rw [← map_mul h, ← map_mul h, mul_comm t']
  have hPositive := rankOneWord_reflection r (h t) a hUpper hLower (hComm t a)
  have hSign : markedWall M R i 1 =
      r (diagonal (-1)) * r (elementaryWord (1 : Rˣ)) := by
    change r (elementaryWord (-(1 : Rˣ))) = _
    rw [elementaryWord_diagonal, map_mul]
  have hConj : markedWall M R i 1 * h t * (markedWall M R i 1)⁻¹ =
      h t * (r (diagonal a))⁻¹ := by
    rw [hSign]
    calc
      _ = r (diagonal (-1)) *
          (r (elementaryWord (1 : Rˣ)) * h t * (r (elementaryWord (1 : Rˣ)))⁻¹) *
            (r (diagonal (-1)))⁻¹ := by group
      _ = _ := by
        rw [hPositive]
        apply Commute.mul_inv_cancel
        apply Commute.mul_right (hComm t (-1)).symm
        rw [hDiag a]
        exact (hComm _ (-1)).symm.inv_right
  change markedWall M R i 1 * h t * (markedWall M R i 1)⁻¹ =
    h (t.comp (D.datum.reflection i).toLinearMap.toAddMonoidHom.toMultiplicative)
  rw [hConj, hDiag, ← map_inv, ← map_mul]
  congr 1
  apply MonoidHom.ext
  intro χ
  change t χ * (a ^ D.datum.toLinearMap χ.toAdd (D.datum.coroot i))⁻¹ =
    t (Multiplicative.ofAdd (D.datum.reflection i χ.toAdd))
  rw [D.datum.reflection_apply]
  change t χ * (a ^ D.datum.toLinearMap χ.toAdd (D.datum.coroot i))⁻¹ =
    t (χ / (Multiplicative.ofAdd (D.datum.root i)) ^ D.datum.coroot' i χ.toAdd)
  rw [map_div, map_zpow, div_eq_mul_inv]
  rfl

private theorem markedWall_conjugates_cocharacter {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (i : D.I) (v : D.Y) (s : Rˣ) :
    let n := markedWall M R i 1
    n * markedCocharacter M R v s * n⁻¹ = markedCocharacter M R (D.datum.coreflection i v) s := by
  let n := markedWall M R i 1
  let h := markedTorusHom M R
  let t := cocharacter D v R s
  change n * h t * n⁻¹ = h (cocharacter D (D.datum.coreflection i v) R s)
  rw [markedWall_conjugates_torus]
  congr 1
  apply MonoidHom.ext
  intro χ
  change s ^ D.datum.toLinearMap (D.datum.reflection i χ.toAdd) v =
    s ^ D.datum.toLinearMap χ.toAdd (D.datum.coreflection i v)
  rw [D.datum.reflection_apply, D.datum.coreflection_apply]
  simp [mul_comm]

private theorem markedWord_conjugates_cocharacter {D : BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (l : List D.I) (v : D.Y) (s : Rˣ) :
    let w := ((l.map (RootPairing.weylGroup.ofIdx D.datum)).prod).val.coweightEquiv.symm
    let n := markedWeylWord M R l
    n * markedCocharacter M R v s * n⁻¹ = markedCocharacter M R (w v) s := by
  induction l with
  | nil =>
    have h : (RootPairing.Equiv.coweightEquiv (1 : D.datum.Equiv D.datum)).symm v = v := by
      apply (LinearEquiv.symm_apply_eq _).2
      change v = ((RootPairing.Equiv.coweightEquiv (1 : D.datum.Equiv D.datum)).toLinearMap) v
      rw [RootPairing.Equiv.coweightEquiv_one]
      rfl
    simpa only [markedWeylWord, List.map_nil, List.prod_nil, Subgroup.coe_one, one_mul,
      inv_one, mul_one] using congrArg (fun y => markedCocharacter M R y s) h.symm
  | cons i l ih =>
    dsimp only at ih
    let n := markedWall M R i 1
    let q := markedWeylWord M R l
    let w := ((l.map (RootPairing.weylGroup.ofIdx D.datum)).prod).val
    dsimp only [List.map_cons, List.prod_cons, Subgroup.coe_mul]
    change (n * q) * markedCocharacter M R v s * (n * q)⁻¹ =
      markedCocharacter M R ((RootPairing.Equiv.reflection D.datum i * w).coweightEquiv.symm v) s
    calc
      _ = n * (q * markedCocharacter M R v s * q⁻¹) * n⁻¹ := by group
      _ = markedCocharacter M R (D.datum.coreflection i (w.coweightEquiv.symm v)) s := by
        rw [show q * markedCocharacter M R v s * q⁻¹ =
          markedCocharacter M R (w.coweightEquiv.symm v) s from ih]
        exact markedWall_conjugates_cocharacter M R i _ s
      _ = _ := by
        congr 1
        rw [RootPairing.Equiv.mul_eq_comp, RootPairing.Equiv.coweightEquiv_comp_toLin]
        simp only [LinearEquiv.trans_symm, LinearEquiv.trans_apply,
          RootPairing.Equiv.reflection_coweightEquiv]
        symm
        exact (LinearEquiv.symm_apply_eq (D.datum.coreflection i)).2
          (D.datum.coreflection_same i _).symm

private theorem pinned_cocharacter {F K : Type u} [Field F] [Field K] [Algebra F K]
    {E : BasedRootDatum.{u}} {M : Model E} {ρ : Gal(K/F) →* MulAut (FieldPoints M K)}
    {h : Gal(K/F) → (ℚ ⊗[ℤ] E.Y) ≃ᵃ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    (δ : PinnedOperators ρ h) (σ : Gal(K/F))
    (R : IntegralAlgebra.{u}) (y : E.Y) (ξ : Rˣ) :
    integralPointHom (δ.pinned σ).asIso.hom R (markedCocharacter M.toIntegralMarking R y ξ) =
      markedCocharacter M.toIntegralMarking R ((δ.diagram σ).coweightEquiv.symm y) ξ := by
  exact (δ.torus_formula σ R (cocharacter E y R ξ)).trans
    (congrArg (markedTorusHom M.toIntegralMarking R) (cocharacter_transport (δ.diagram σ) R y ξ))

private theorem lift_normalizer : IntegralNormalizerCorrection.{u} := by
  intro F K L _ _ _ _ _ _ _ _ _ _ _ D E M M' c p p' e Y ρ h δ a σ y ξ
  dsimp only
  intro v hv hvaluation
  let O := localIntegers L
  let U := integralRing L
  let j := localIntegersInclusion L
  let f := integralRingMap (algebraMap K L)
  let N := Y.ad.localIwahori.normalizer
  let n := typeLift (Y := Y) a σ
  let w := (N.label n).val.coweightEquiv.symm
  let l := N.word (N.label n)
  let y' := (δ.diagram σ).coweightEquiv.symm y
  let t := markedTorusHom M'.toIntegralMarking U
  let nU := markedWeylWord M'.toIntegralMarking U l
  let vU := (Units.map f.hom.toMonoidHom).comp v
  let vq := cocharacter E y U ξ * vU * (cocharacter E (w y') U ξ)⁻¹
  have hq (χ : Multiplicative E.X) : normalizedValuation L (vq χ : L) = 1 := by
    have h' := hvaluation χ.toAdd
    change normalizedValuation L
      ((ξ : L) ^ (E.datum.toLinearMap χ.toAdd y - E.datum.toLinearMap χ.toAdd (w y')) *
        algebraMap K L (v χ : K)) = 1 at h'
    rw [zpow_sub₀ ξ.ne_zero, div_eq_mul_inv, mul_right_comm] at h'
    change normalizedValuation L
      (((ξ ^ E.datum.toLinearMap χ.toAdd y : Lˣ) : L) * algebraMap K L (v χ : K) *
          (((ξ ^ E.datum.toLinearMap χ.toAdd (w y') : Lˣ)⁻¹ : Lˣ) : L)) = 1
    simpa only [Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val] using h'
  refine ⟨liftIntegralTorusValues vq hq, ?_⟩
  change changeRingHom M'.group j
    (markedTorusHom M'.toIntegralMarking O (liftIntegralTorusValues vq hq) *
      markedWeylWord M'.toIntegralMarking O l) = _
  rw [map_mul, torus_changeRing, liftIntegralTorusValues_eq, markedWeylWord_changeRing,
    pinned_cocharacter]
  have hn : (n : FieldPoints M' K) =
      (N.torusPart n : FieldPoints M' K) * markedWeylWord M'.toIntegralMarking (integralRing K) l := by
    rw [← N.lift_point (N.label n)]
    change (n : FieldPoints M' K) = (N.torusPart n : FieldPoints M' K) * (N.lift (N.label n) : _)
    simp [MarkedLocalNormalizer.torusPart]
  have hs : scalarPoints M' (algebraMap K L) (n : FieldPoints M' K) = t vU * nU := by
    rw [hn, hv, map_mul]
    change changeRingHom M'.group f (markedTorusHom M'.toIntegralMarking (integralRing K) v) *
      changeRingHom M'.group f (markedWeylWord M'.toIntegralMarking (integralRing K) l) = _
    rw [torus_changeRing, markedWeylWord_changeRing]
  have hword : ((l.map (RootPairing.weylGroup.ofIdx E.datum)).prod) = N.label n := by
    obtain ⟨_, _, _, hw⟩ := Y.ad_points.2.1
    exact hw _
  have hConj := markedWord_conjugates_cocharacter M'.toIntegralMarking U l y' ξ
  dsimp only at hConj
  rw [hword] at hConj
  change nU * t (cocharacter E y' U ξ) * nU⁻¹ = t (cocharacter E (w y') U ξ) at hConj
  rw [hs]
  change t vq * nU = t (cocharacter E y U ξ) * (t vU * nU) * (t (cocharacter E y' U ξ))⁻¹
  rw [show t vq = t (cocharacter E y U ξ) * t vU * (t (cocharacter E (w y') U ξ))⁻¹ by
    dsimp only [vq]
    rw [map_mul t, map_mul t, map_inv t], ← hConj]
  group

/-- The scaled length-zero representative lifts to the marked integral model. -/
theorem integralNormalizerCorrection : IntegralNormalizerCorrection.{u} :=
  lift_normalizer

/-- The corrected length-zero lift is integral when the marked character
valuation cancellation holds. -/
theorem integralNormalizerCorrection_conditional
    (_coxeter : Specs.ExceptionalAffineBruhat.CoxeterDoubleCosets.{u,v,w})
    (_coweight : Specs.ExceptionalAffineBruhat.E6CoweightClass)
    (_lattices : Specs.ExceptionalAffineBruhat.E6ProjectedLattices)
    (_index : Specs.ExceptionalAffineBruhat.LeftCosetIndex.{u})
    (_ramified : Specs.ExceptionalAffineBruhat.RamifiedAffineBruhatComparison.{u})
    (_product : Specs.ExceptionalAffineBruhat.RankOneDoubleCosetProduct.{u})
    (_conjugation : Specs.ExceptionalAffineBruhat.RankOneWallConjugation.{u})
    (_multiplication : Specs.ExceptionalAffineBruhat.RankOneWallMultiplication.{u})
    (_layers : Specs.ExceptionalAffineBruhat.ResidueLayerCounts.{u})
    (_power : Specs.ExceptionalAffineBruhat.ResiduePowerCounts.{u})
    (_split : Specs.ExceptionalAffineBruhat.SplitAffineBruhatComparison.{u})
    (_ramifiedBuilding : Specs.ExceptionalAffineBuilding.RamifiedAffineBuildings.{u})
    (_splitBuilding : Specs.ExceptionalAffineBuilding.SplitAffineBuildings.{u}) :
    IntegralNormalizerCorrection.{u} :=
  lift_normalizer

section IntegralCocycle

open CategoryTheory.Limits

private theorem integral_points_injective {G : IntegralGroup.{u}} (ha : IsAffine G.X.left)
    {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (hf : Function.Injective f.hom) :
    Function.Injective (changeRingHom G f) := by
  intro p q h
  apply Over.OverMorphism.ext
  letI : IsAffine G.X.left := ha
  let i := G.X.left.isoSpec.hom
  have hpq : Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫ (p.left ≫ i) =
      Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫ (q.left ≫ i) := by
    change (integralSpec.map f.op).left ≫ (p.left ≫ i) =
      (integralSpec.map f.op).left ≫ (q.left ≫ i)
    change integralSpec.map f.op ≫ p = integralSpec.map f.op ≫ q at h
    simpa only [Over.comp_left, Category.assoc] using
      congrArg (fun z : IntegralPoints G S => z.left ≫ i) h
  have hring := congrArg Spec.preimage hpq
  simp only [Spec.preimage_comp, Spec.preimage_map] at hring
  have hr : Spec.preimage (p.left ≫ i) = Spec.preimage (q.left ≫ i) := by
    ext z
    exact hf (ConcreteCategory.congr_hom hring z)
  apply (cancel_mono i).mp
  simpa using congrArg Spec.map hr

section CoefficientActions

attribute [local instance] integerAlgebra

private theorem coefficientPoint_natural {G : IntegralGroup.{u}}
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (α : R ≃+* R) (β : S ≃+* S) (δ : Aut G)
    (h : ∀ z, f (α z) = β (f z)) (g : IntegralPoints G (integralRing R)) :
    changeRingHom G (integralRingMap f) (coefficientPoint α δ g) =
      coefficientPoint β δ (changeRingHom G (integralRingMap f) g) := by
  change integralSpec.map (integralRingMap f).op ≫
      integralSpec.map (integralRingMap α.toRingHom).op ≫ g ≫ δ.asIso.hom.hom.hom =
    (integralSpec.map (integralRingMap β.toRingHom).op ≫
      integralSpec.map (integralRingMap f).op ≫ g) ≫ δ.asIso.hom.hom.hom
  have hf : integralRingMap α.toRingHom ≫ integralRingMap f =
      integralRingMap f ≫ integralRingMap β.toRingHom :=
    CommAlgCat.hom_ext (AlgHom.ext h)
  simp only [Category.assoc, ← Functor.map_comp_assoc, ← op_comp, hf]

private theorem coefficientPoint_mul_apply {Γ : Type*} [Group Γ] {G : IntegralGroup.{u}}
    {R : Type u} [CommRing R] (α : Γ →* (R ≃+* R)) (δ : Γ →* Aut G)
    (σ τ : Γ) (g : IntegralPoints G (integralRing R)) :
    coefficientPoint (α (σ * τ)) (δ (σ * τ)) g =
      coefficientPoint (α σ) (δ σ) (coefficientPoint (α τ) (δ τ) g) := by
  change integralSpec.map (integralRingMap (α (σ * τ)).toRingHom).op ≫
      g ≫ (δ (σ * τ)).asIso.hom.hom.hom =
    (integralSpec.map (integralRingMap (α σ).toRingHom).op ≫
      integralSpec.map (integralRingMap (α τ).toRingHom).op ≫
        g ≫ (δ τ).asIso.hom.hom.hom) ≫ (δ σ).asIso.hom.hom.hom
  have he : integralRingMap (α (σ * τ)).toRingHom =
      integralRingMap (α τ).toRingHom ≫ integralRingMap (α σ).toRingHom := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    change α (σ * τ) z = α σ (α τ z)
    rw [map_mul]
    rfl
  rw [he, op_comp, Functor.map_comp, map_mul]
  rfl_cat

end CoefficientActions

private theorem coefficientPoint_fixes_parameter
    {D : BasedRootDatum.{u}} (M : IntegralMarking D) {L : Type u} [Field L]
    (α : L ≃+* L) (δ : Aut M.group) (y : D.Y) (ξ : Lˣ) (hξ : α (ξ : L) = ξ) :
    coefficientPoint α δ (markedCocharacter M (integralRing L) y ξ) =
      integralPointHom δ.asIso.hom (integralRing L) (markedCocharacter M (integralRing L) y ξ) := by
  change integralPointHom δ.asIso.hom (integralRing L)
    (changeRingHom M.group (integralRingMap α.toRingHom)
      (markedTorusHom M (integralRing L) (cocharacter D y (integralRing L) ξ))) = _
  rw [torus_changeRing]
  congr 1
  apply congrArg (markedTorusHom M (integralRing L))
  apply MonoidHom.ext
  intro χ
  have hu : Units.map α.toRingHom.toMonoidHom ξ = ξ := Units.ext hξ
  change Units.map α.toRingHom.toMonoidHom (ξ ^ D.datum.toLinearMap χ.toAdd y) =
    ξ ^ D.datum.toLinearMap χ.toAdd y
  rw [map_zpow, hu]

section Local

variable {F K L : Type u} [Field F] [Field K] [Field L]
  [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
  [ValuativeRel F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension F L] [ValuativeExtension K L]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e} {B : SplitBuildingLevel Y}
  {t : Weights ((ApartmentRoots.split E.datum ℚ).SimpleWall p')}
  {x : ℚ ⊗[ℤ] E.Y} {d : ℕ} {y : E.Y} {ξ : Lˣ}
  {R : FaceReduction B t x d y ξ} (S : ScaledInput (F := F) R)

private theorem twisted_mem (σ : Gal(K/F)) (g : parahoric Y.ad (cotype t)) :
    S.a σ * S.ρ σ (g : FieldPoints M' K) * (S.a σ)⁻¹ ∈ parahoric Y.ad (cotype t) := by
  let z := B.ad.realization.place 1 t
  let ad := B.adjoint
  have gfix : ad.action (g : FieldPoints M' K) z = z := by
    let k : Y.ad.G₀ := ⟨g, B.ad.realization.face_mem _ g.property⟩
    rw [show (g : FieldPoints M' K) = (k : FieldPoints M' K) from rfl, ad.restrict]
    exact (B.ad.stabilizer _ t rfl k).2 g.property
  have hconj : ad.action (S.a σ * S.ρ σ (g : FieldPoints M' K) * (S.a σ)⁻¹) z = z := by
    rw [map_mul, map_mul, map_inv]
    change ad.action (S.a σ) (ad.action (S.ρ σ (g : FieldPoints M' K))
      ((ad.action (S.a σ)).symm z)) = z
    have he : (ad.action (S.a σ)).symm z = S.onBuilding.action σ z :=
      ((ad.action (S.a σ)).symm_apply_eq).2 (S.fixed σ).symm
    rw [he, ← S.equivariant, gfix, S.fixed]
  letI := Y.typeQuotient.normal
  have hmem : S.ρ σ (g : FieldPoints M' K) ∈ Y.ad.G₀ := by
    rw [← (S.coefficient_comparison σ).2.2.2.1]
    exact ⟨g, B.ad.realization.face_mem _ g.property, rfl⟩
  have hnormal : S.a σ * S.ρ σ (g : FieldPoints M' K) * (S.a σ)⁻¹ ∈ Y.ad.G₀ :=
    Subgroup.Normal.conj_mem inferInstance _ hmem _
  let k : Y.ad.G₀ := ⟨_, hnormal⟩
  exact (B.ad.stabilizer _ t rfl k).1 (by simpa only [← ad.restrict] using hconj)

private theorem scaled_cocycle (S : ScaledInput (F := F) R) :
    Nonempty (ScaledIntegralAction S) := by
  let O := localIntegers L
  let U := integralRing L
  let φ := changeRingHom M'.group (localIntegersInclusion L)
  let f := scalarPoints M' (algebraMap K L)
  let s := markedCocharacter M'.toIntegralMarking U y ξ
  let δO := fun σ => coefficientPoint (S.coefficients.integerAction σ) (S.δ.pinned σ)
  let δU := fun σ => coefficientPoint (S.coefficients.fieldAction σ).toRingEquiv (S.δ.pinned σ)
  have hδ (σ) (z : IntegralPoints M'.group O) : φ (δO σ z) = δU σ (φ z) :=
    coefficientPoint_natural _ _ _ _ (S.coefficients.integer_eq σ) z
  have hf (σ) (z : FieldPoints M' K) : δU σ (f z) = f (S.ρ σ z) := by
    rw [← S.δ.generic_eq]
    exact (coefficientPoint_natural _ _ _ _ (fun z => (S.coefficients.restrict σ z).symm) z).symm
  have hs (σ) : δU σ s = integralPointHom (S.δ.pinned σ).asIso.hom U s :=
    coefficientPoint_fixes_parameter _ _ _ _ _ (S.coefficients.fixes_root σ)
  let φ_inj := integral_points_injective M'.affine (localIntegersInclusion L)
    (fun _ _ eq => Subtype.ext eq)
  have hq (σ) := lift_normalizer Y S.ρ S.h S.δ S.a σ y ξ
    (S.torusValues σ) (S.torusValues_eq σ) (S.valuation_cancel σ)
  choose vq hvq using hq
  let N := Y.ad.localIwahori.normalizer
  let l := fun σ => N.word (N.label (typeLift (Y := Y) S.a σ))
  let q := fun σ => markedTorusHom M'.toIntegralMarking O (vq σ) *
    markedWeylWord M'.toIntegralMarking O (l σ)
  have hq (σ) : φ (q σ) =
      s * f (typeLift (Y := Y) S.a σ : FieldPoints M' K) *
        (integralPointHom (S.δ.pinned σ).asIso.hom U s)⁻¹ := hvq σ
  let p := fun σ => R.integral (S.b σ) * q σ
  have hp (σ) : φ (p σ) = s * f (S.a σ) * (δU σ s)⁻¹ := by
    change φ (R.integral (S.b σ) * q σ) = _
    rw [map_mul, R.scale, hq, hs, S.factor, map_mul]
    dsimp only [s, f, U]
    group
  have hδ_mul (σ τ) (z : FieldPoints M' L) : δU (σ * τ) z = δU σ (δU τ z) := by
    let f := S.coefficients.fieldAction
    let f' : Gal(K/F) →* (L ≃+* L) :=
      { toFun := fun σ => (f σ).toRingEquiv
        map_one' := by rw [map_one]; rfl
        map_mul' σ τ := by rw [map_mul]; rfl }
    exact coefficientPoint_mul_apply f' S.δ.pinned σ τ z
  constructor
  refine ⟨q, hq, ?_, ?_, twisted_mem S, ?_⟩
  · intro σ τ
    change p (σ * τ) = p σ * δO σ (p τ)
    apply φ_inj
    change φ (p (σ * τ)) = φ (p σ * δO σ (p τ))
    rw [map_mul φ (p σ) (δO σ (p τ)), hδ, hp, hp, hp, S.cocycle]
    simp only [map_mul, map_inv, hf, hδ_mul]
    group
  · intro σ T f r hr
    let m := markedTorusHom M'.toIntegralMarking T
    let v := (Units.map f.hom.toMonoidHom).comp (vq σ)
    let n := markedWeylWord M'.toIntegralMarking T (l σ)
    let w := (N.label (typeLift (Y := Y) S.a σ)).val.coweightEquiv.symm
    let y' := (S.δ.diagram σ).coweightEquiv.symm y
    have hword : ((l σ).map (RootPairing.weylGroup.ofIdx E.datum)).prod =
        N.label (typeLift (Y := Y) S.a σ) := by
      obtain ⟨_, _, _, hw⟩ := Y.ad_points.2.1
      exact hw _
    have hw := markedWord_conjugates_cocharacter M'.toIntegralMarking T (l σ) y' r
    dsimp only at hw
    rw [hword] at hw
    change n * m (cocharacter E y' T r) * n⁻¹ = m (cocharacter E (w y') T r) at hw
    change changeRingHom M'.group f (q σ) *
      integralPointHom (S.δ.pinned σ).asIso.hom T
        (markedCocharacter M'.toIntegralMarking T y r) *
      (changeRingHom M'.group f (q σ))⁻¹ =
        markedCocharacter M'.toIntegralMarking T y r
    have hred : changeRingHom M'.group f (q σ) = m v * n := by
      dsimp only [q]
      rw [map_mul, torus_changeRing, markedWeylWord_changeRing]
    rw [hred, pinned_cocharacter]
    change m v * n * m (cocharacter E y' T r) * (m v * n)⁻¹ =
      m (cocharacter E y T r)
    calc
      _ = m v * (n * m (cocharacter E y' T r) * n⁻¹) * (m v)⁻¹ := by group
      _ = _ := by
        rw [hw, S.cocharacter_eq σ T r hr]
        apply Commute.mul_inv_cancel
        show m v * m (cocharacter E y T r) = m (cocharacter E y T r) * m v
        rw [← map_mul m, ← map_mul m, mul_comm v]
  · intro σ g
    change R.integral ⟨_, twisted_mem S σ g⟩ = p σ * δO σ (R.integral g) * (p σ)⁻¹
    apply φ_inj
    change φ (R.integral ⟨_, twisted_mem S σ g⟩) =
      φ (p σ * δO σ (R.integral g) * (p σ)⁻¹)
    rw [map_mul φ (p σ * δO σ (R.integral g)) ((p σ)⁻¹),
      map_mul φ (p σ) (δO σ (R.integral g)), map_inv φ, hp, hδ, R.scale, R.scale]
    change s * f (S.a σ * S.ρ σ (g : FieldPoints M' K) * (S.a σ)⁻¹) * s⁻¹ =
      (s * f (S.a σ) * (δU σ s)⁻¹) *
        δU σ (s * f (g : FieldPoints M' K) * s⁻¹) *
        (s * f (S.a σ) * (δU σ s)⁻¹)⁻¹
    simp only [map_mul, map_inv, hf]
    group

end Local
end IntegralCocycle

section ResidueComparison

open Specs.ExceptionalAffineRootSystems (diagramCocharacters alcoveStabilizer)

private theorem root_diagram_covariance {E : BasedRootDatum.{u}} (σ : E.datum.Equiv E.datum)
    (i : E.I) (z : ℚ ⊗[ℤ] E.Y) :
    (ApartmentRoots.split E.datum ℚ).root (σ.indexEquiv i) (diagramCocharacters σ z) =
      (ApartmentRoots.split E.datum ℚ).root i z := by
  induction z using TensorProduct.inductionOn with
  | tmul r z =>
    rw [show r ⊗ₜ[ℤ] z = r • ((1 : ℚ) ⊗ₜ[ℤ] z) by simp [TensorProduct.smul_tmul']]
    simp [diagramCocharacters, ApartmentRoots.split, σ.root'_coweightEquiv]
  | add x y hx hy => simp only [map_add, hx, hy]

variable {F K L : Type u} [Field F] [Field K] [Field L]
  [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
  [ValuativeRel F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension F L] [ValuativeExtension K L]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e} {B : SplitBuildingLevel Y}
  {t : Weights ((ApartmentRoots.split E.datum ℚ).SimpleWall p')}
  {x : ℚ ⊗[ℤ] E.Y} {d : ℕ} {y : E.Y} {ξ : Lˣ}
  {R : FaceReduction B t x d y ξ} {S : ScaledInput (F := F) R}

local notation "A" => ApartmentRoots.split E.datum ℚ

/-- Root transport of the combined action, including the sign on the given
alcove for each integral level through the face. -/
theorem positive_roots_transport (S : ScaledInput (F := F) R)
    (σ : Gal(K/F)) (i : E.I) (j : ℤ) (hj : (A).root i x = j) :
    let n := typeLift (Y := Y) S.a σ
    let N := Y.ad.localIwahori.normalizer
    let b := (N.label n).val.indexEquiv ((S.δ.diagram σ).indexEquiv i)
    let j' := j + E.datum.root' b (N.translation (N.torusPart n)).toAdd
    (A).root b x = j' ∧ ((A).positive p' (b, -j') ↔ (A).positive p' (i, -j)) := by
  let Phi := ApartmentRoots.split E.datum ℚ
  let n := typeLift (Y := Y) S.a σ
  let N := Y.ad.localIwahori.normalizer
  let w := (N.label n).val
  let δ := S.δ.diagram σ
  let b := w.indexEquiv (δ.indexEquiv i)
  let l := (N.translation (N.torusPart n)).toAdd
  let j' := j + E.datum.root' b l
  let f := fun z => Y.ad.affine n (S.h σ z)
  have hf (z) : Phi.root b (f z) = Phi.root i z + (E.datum.root' b l : ℚ) := by
    dsimp only [f]
    rw [Y.ad_points.2.2.2.2.2.2.1 n, S.δ.h_eq σ, map_add]
    change Phi.root b (diagramCocharacters w (diagramCocharacters δ z)) +
      RootData.extendFunctional ℚ (E.datum.root' b) ((1 : ℚ) ⊗ₜ[ℤ] l) = _
    rw [show b = w.indexEquiv (δ.indexEquiv i) from rfl,
      root_diagram_covariance, root_diagram_covariance, RootData.extendFunctional_one_tmul]
  have hfx : f x = x := S.affine_fixed σ
  have hroot : Phi.root b x = (j' : ℚ) := by
    rw [← hfx, hf, hj]
    simp [j']
  refine ⟨hroot, ?_⟩
  have hsign (z) : Phi.positive (f z) (b, -j') ↔ Phi.positive z (i, -j) := by
    change 0 < Phi.root b (f z) + ((-j' : ℤ) : ℚ) ↔
      0 < Phi.root i z + ((-j : ℤ) : ℚ)
    rw [hf]
    simp only [j', Int.cast_neg, Int.cast_add]
    abel_nf
  have hn : (fun z => Y.ad.affine n z) '' Phi.alcove p' = Phi.alcove p' := by
    change (Y.ad.affine n) '' Phi.alcove p' = Phi.alcove p'
    rw [Y.typeQuotient.affine_lift]
    exact (typeChange Y.typeQuotient (S.a σ)).property
  have honto : f '' Phi.alcove p' = Phi.alcove p' := by
    change ((fun z => Y.ad.affine n z) ∘ S.h σ) '' Phi.alcove p' = Phi.alcove p'
    rw [Set.image_comp _ _ (Phi.alcove p')]
    have hc : (S.h σ) '' Phi.alcove p' = Phi.alcove p' :=
      (S.coefficient_comparison σ).2.2.2.2.2.1
    rw [hc, hn]
  have hp : p' ∈ Phi.alcove p' := fun _ h => h
  constructor
  · intro hb
    have hm : f p' ∈ Phi.alcove p' := by
      rw [← honto]
      exact ⟨p', hp, rfl⟩
    exact (hsign p').mp (hm _ hb)
  · intro hi
    obtain ⟨z, hz, hfz⟩ := (show p' ∈ f '' Phi.alcove p' from honto.symm ▸ hp)
    exact (congrArg (fun q => Phi.positive q (b, -j')) hfz).mp ((hsign z).mpr (hz _ hi))

private theorem residue_coefficient_compatibility (σ : Gal(K/F))
    (z : IntegralPoints M'.group (localIntegers L)) :
    letI := (residueMap F L).toAlgebra
    let red := changeRingHom M'.group (residueHom (localIntegers L))
    red (coefficientPoint (S.coefficients.integerAction σ) (S.δ.pinned σ) z) =
      coefficientPoint (S.coefficients.residueAction σ).toRingEquiv (S.δ.pinned σ) (red z) := by
  letI := (residueMap F L).toAlgebra
  let O := localIntegers L
  let red := changeRingHom M'.group (residueHom O)
  have hr : residueHom O = integralRingMap (residueHom O).hom.toRingHom := by
    apply CommAlgCat.hom_ext
    rfl
  have h := coefficientPoint_natural (residueHom O).hom.toRingHom
    (S.coefficients.integerAction σ) (S.coefficients.residueAction σ).toRingEquiv
    (S.δ.pinned σ) (S.coefficients.residue_eq σ) z
  rw [← hr] at h
  exact h

/-- The special-fibre correcting points satisfy the same cocycle law as
their scaled integral lifts. -/
theorem residue_cocycle (J : ScaledIntegralAction S) (σ τ : Gal(K/F)) :
    letI := (residueMap F L).toAlgebra
    J.correctingResidue (σ * τ) =
      J.correctingResidue σ *
        coefficientPoint (S.coefficients.residueAction σ).toRingEquiv (S.δ.pinned σ)
          (J.correctingResidue τ) := by
  letI := (residueMap F L).toAlgebra
  dsimp only [ScaledIntegralAction.correctingResidue]
  rw [J.cocycle, map_mul, residue_coefficient_compatibility]

/-- Reduction of the integral operator gives the prescribed twisted
operation after inclusion into the marked affine special fibre. -/
theorem ambient_residue_equivariance (J : ScaledIntegralAction S)
    (σ : Gal(K/F)) (g : parahoric Y.ad (cotype t)) :
    letI := (residueMap F L).toAlgebra
    let C := J.correctingResidue σ
    let red := changeRingHom M'.group (residueHom (localIntegers L))
    red (R.integral ⟨_, J.invariant σ g⟩) =
      C * coefficientPoint (S.coefficients.residueAction σ).toRingEquiv
          (S.δ.pinned σ) (red (R.integral g)) * C⁻¹ := by
  letI := (residueMap F L).toAlgebra
  let O := localIntegers L
  let red := changeRingHom M'.group (residueHom O)
  let C := J.correctingResidue σ
  change red (R.integral ⟨_, J.invariant σ g⟩) = _
  rw [J.equivariant, map_mul red, map_mul red, map_inv red, residue_coefficient_compatibility]
  rfl

end ResidueComparison

section PointAction

attribute [local instance] integerAlgebra

open Specs.AdjointRepresentation (GroupPoints)
open Specs.AdjointCocharacters (coordinateHopfIso)
open _root_.LinearAlgebraicGroups.Descent (TwistedPointAction inverseTwistAlgebra inverseTwistHom)
open private fibrePointsEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private forgetFibrePoint_natural from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates

private theorem changeRing_comp {G : IntegralGroup.{u}} {R S T : IntegralAlgebra.{u}}
    (f : R ⟶ S) (g : S ⟶ T) (z : IntegralPoints G R) :
    changeRingHom G (f ≫ g) z = changeRingHom G g (changeRingHom G f z) := by
  change integralSpec.map (f ≫ g).op ≫ z = integralSpec.map g.op ≫ integralSpec.map f.op ≫ z
  rw [op_comp, Functor.map_comp, Category.assoc]

private theorem integralRingMap_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) :
    integralRingMap (g.comp f) = integralRingMap f ≫ integralRingMap g := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro z
  rfl

private theorem integralRingMap_id (T : Type u) [CommRing T] :
    integralRingMap (RingHom.id T) = 𝟙 (integralRing T) := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro z
  rfl

private theorem pinned_changeRing {G : IntegralGroup.{u}} {R T : IntegralAlgebra.{u}}
    (δ : Aut G) (f : R ⟶ T) (z : IntegralPoints G R) :
    changeRingHom G f (integralPointHom δ.asIso.hom R z) =
      integralPointHom δ.asIso.hom T (changeRingHom G f z) := by
  change integralSpec.map f.op ≫ z ≫ δ.asIso.hom.hom.hom =
    (integralSpec.map f.op ≫ z) ≫ δ.asIso.hom.hom.hom
  exact (Category.assoc _ _ _).symm

private theorem pinned_mul {Γ : Type*} [Group Γ] {G : IntegralGroup.{u}}
    (δ : Γ →* Aut G) (T : IntegralAlgebra.{u}) (σ τ : Γ) (z : IntegralPoints G T) :
    integralPointHom (δ (σ * τ)).asIso.hom T z =
      integralPointHom (δ σ).asIso.hom T (integralPointHom (δ τ).asIso.hom T z) := by
  rw [map_mul]
  rfl_cat

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']
  {G : IntegralGroup.{u}} {H : AffineAlgebraicGroup k'}

private def includedPoint (i : H.val ⟶ (fibre k').obj G) (T : TestAlgebra k') :
    GroupPoints H.val T →* IntegralPoints G (integralRing T) :=
  (fibrePointsEquiv G T).toMonoidHom.comp
    (IsMonHom.monoidHom i.hom.hom ((testSpec k').obj (op T)))

private theorem includedPoint_injective (i : H.val ⟶ (fibre k').obj G)
    (hi : IsClosedImmersion i.hom.hom.left) (T : TestAlgebra k') :
    Function.Injective (includedPoint i T) := by
  letI : Mono i.hom.hom.left := inferInstance
  letI : Mono i.hom.hom := Over.mono_of_mono_left _
  intro p q h
  apply (cancel_mono i.hom.hom).mp
  exact (fibrePointsEquiv G T).injective h

private theorem includedPoint_map (i : H.val ⟶ (fibre k').obj G) {T U : TestAlgebra k'}
    (m : T ⟶ U) (p : GroupPoints H.val T) :
    includedPoint i U (mapPoints m p) =
      changeRingHom G (integralRingMap m.hom.toRingHom) (includedPoint i T p) := by
  change forgetFibrePoint G U ((mapPoints m p) ≫ i.hom.hom) = _
  rw [Category.assoc]
  exact forgetFibrePoint_natural G m (p ≫ i.hom.hom)

private abbrev coordinateIso (H : AffineAlgebraicGroup k') :
    convolutionPoints (AdjointCocharacters.coordinateHopf H) ≅ (groupPointsFunctor k').obj H.val :=
  _root_.LinearAlgebraicGroups.hopfSpecPointIso (AdjointCocharacters.coordinateHopf H) ≪≫
    (groupPointsFunctor k').mapIso (coordinateHopfIso H)

private abbrev coordinateEquiv (H : AffineAlgebraicGroup k') (T : TestAlgebra k') :
    (convolutionPoints (AdjointCocharacters.coordinateHopf H)).obj T ≃* GroupPoints H.val T :=
  ((coordinateIso H).app T).groupIsoToMulEquiv

private theorem coordinateEquiv_apply (H : AffineAlgebraicGroup k') (T : TestAlgebra k')
    (f : (convolutionPoints (AdjointCocharacters.coordinateHopf H)).obj T) :
    coordinateEquiv H T f = coordinatePoint H T (CommAlgCat.ofHom f.ofConv) := rfl

private theorem coordinateEquiv_map (H : AffineAlgebraicGroup k') {T U : TestAlgebra k'}
    (m : T ⟶ U) (f : (convolutionPoints (AdjointCocharacters.coordinateHopf H)).obj T) :
    coordinateEquiv H U ((convolutionPoints (AdjointCocharacters.coordinateHopf H)).map m f) =
      mapPoints m (coordinateEquiv H T f) :=
  ConcreteCategory.congr_hom ((coordinateIso H).hom.naturality m) f

private def ambientOperator {T : Type u} [CommRing T] (δ : Aut G)
    (q : IntegralPoints G (integralRing k')) (a : k' →+* T) :
    IntegralPoints G (integralRing T) →* IntegralPoints G (integralRing T) :=
  (MulAut.conj (changeRingHom G (integralRingMap a) q)).toMonoidHom.comp
    (integralPointHom δ.asIso.hom (integralRing T))

private theorem ambientOperator_apply {T : Type u} [CommRing T] (δ : Aut G)
    (q : IntegralPoints G (integralRing k')) (a : k' →+* T)
    (z : IntegralPoints G (integralRing T)) :
    ambientOperator δ q a z =
      changeRingHom G (integralRingMap a) q *
        integralPointHom δ.asIso.hom (integralRing T) z *
          (changeRingHom G (integralRingMap a) q)⁻¹ := rfl

private theorem changeRing_coefficient {T : Type u} [CommRing T]
    (δ : Aut G) (galois : k' ≃+* k') (a : k' →+* T)
    (z : IntegralPoints G (integralRing k')) :
    changeRingHom G (integralRingMap a) (coefficientPoint galois δ z) =
      integralPointHom δ.asIso.hom (integralRing T)
        (changeRingHom G (integralRingMap (a.comp galois.toRingHom)) z) := by
  change changeRingHom G (integralRingMap a)
    (integralPointHom δ.asIso.hom _ (changeRingHom G (integralRingMap galois.toRingHom) z)) = _
  rw [pinned_changeRing, integralRingMap_comp, changeRing_comp]

private theorem ambientOperator_changeRing {T U : Type u} [CommRing T] [CommRing U]
    (δ : Aut G) (q : IntegralPoints G (integralRing k')) (a : k' →+* T)
    (f : T →+* U) (z : IntegralPoints G (integralRing T)) :
    changeRingHom G (integralRingMap f) (ambientOperator δ q a z) =
      ambientOperator δ q (f.comp a) (changeRingHom G (integralRingMap f) z) := by
  simp only [ambientOperator_apply, map_mul, map_inv, pinned_changeRing, integralRingMap_comp,
    changeRing_comp]

private theorem ambientOperator_comp {Γ : Type*} [Group Γ]
    (δ : Γ →* Aut G) (galois : Γ →* (k' ≃+* k'))
    (q : Γ → IntegralPoints G (integralRing k'))
    (hq : ∀ σ τ, q (σ * τ) = q σ * coefficientPoint (galois σ) (δ σ) (q τ))
    {T : Type u} [CommRing T] (a : k' →+* T) (σ τ : Γ)
    (z : IntegralPoints G (integralRing T)) :
    ambientOperator (δ (σ * τ)) (q (σ * τ)) a z =
      ambientOperator (δ σ) (q σ) a
        (ambientOperator (δ τ) (q τ) (a.comp (galois σ).toRingHom) z) := by
  simp only [ambientOperator_apply]
  rw [pinned_mul δ, hq σ τ]
  simp only [map_mul, changeRing_coefficient, map_inv]
  group

private theorem changeRing_id {G : IntegralGroup.{u}} {R : IntegralAlgebra.{u}}
    (z : IntegralPoints G R) : changeRingHom G (𝟙 R) z = z := by
  change integralSpec.map (𝟙 R).op ≫ z = z
  simp

private theorem pinned_one (T : IntegralAlgebra.{u}) (z : IntegralPoints G T) :
    integralPointHom (1 : Aut G).asIso.hom T z = z := by
  change z ≫ (1 : Aut G).asIso.hom.hom.hom = z
  rfl_cat

private theorem corrector_one {Γ : Type*} [Group Γ]
    (δ : Γ →* Aut G) (galois : Γ →* (k' ≃+* k'))
    (q : Γ → IntegralPoints G (integralRing k'))
    (hq : ∀ σ τ, q (σ * τ) = q σ * coefficientPoint (galois σ) (δ σ) (q τ)) :
    q 1 = 1 := by
  have h := hq 1 1
  have he : coefficientPoint (galois 1) (δ 1) (q 1) = q 1 := by
    change integralPointHom (δ 1).asIso.hom _
      (changeRingHom G (integralRingMap (galois 1).toRingHom) (q 1)) = q 1
    rw [map_one galois, map_one δ, pinned_one]
    rw [show (1 : k' ≃+* k').toRingHom = RingHom.id k' from rfl, integralRingMap_id, changeRing_id]
  rw [one_mul, he] at h
  apply mul_left_cancel (a := q 1)
  simpa only [mul_one] using h.symm

private def coefficientRingAction : Gal(k'/k) →* (k' ≃+* k') where
  toFun := fun σ => σ.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

private def identityTwistHom (T : TestAlgebra k') : inverseTwistAlgebra (1 : Gal(k'/k)) T ⟶ T := by
  refine ConcreteCategory.ofHom (C := CommAlgCat k') { (RingHom.id T) with commutes' := ?_ }
  intro x
  change algebraMap k' T ((1 : Gal(k'/k))⁻¹ x) = algebraMap k' T x
  rw [inv_one]
  rfl

private def compositeTwistHom (σ τ : Gal(k'/k)) (T : TestAlgebra k') :
    inverseTwistAlgebra (σ * τ) T ⟶ inverseTwistAlgebra σ (inverseTwistAlgebra τ T) := by
  refine ConcreteCategory.ofHom (C := CommAlgCat k') { (RingHom.id T) with commutes' := ?_ }
  intro x
  change algebraMap k' T ((σ * τ)⁻¹ x) = algebraMap k' T (τ⁻¹ (σ⁻¹ x))
  rw [mul_inv_rev]
  rfl

private theorem compositeTwist_scalar (σ τ : Gal(k'/k)) (T : TestAlgebra k') :
    algebraMap k' (inverseTwistAlgebra (σ * τ) T) =
      algebraMap k' (inverseTwistAlgebra σ (inverseTwistAlgebra τ T)) :=
  RingHom.ext (compositeTwistHom σ τ T).hom.commutes

private theorem twistedScalar_cancel (σ τ : Gal(k'/k)) (T : TestAlgebra k') :
    (algebraMap k' (inverseTwistAlgebra (σ * τ) T)).comp σ.toRingHom =
      algebraMap k' (inverseTwistAlgebra τ T) := by
  apply RingHom.ext
  intro x
  change algebraMap k' T ((σ * τ)⁻¹ (σ x)) = algebraMap k' T (τ⁻¹ x)
  rw [mul_inv_rev]
  change algebraMap k' T (τ⁻¹ (σ⁻¹ (σ x))) = algebraMap k' T (τ⁻¹ x)
  rw [show σ⁻¹ (σ x) = x from σ.symm_apply_apply x]

variable (op : ∀ (σ : Gal(k'/k)) (T : TestAlgebra k'),
  GroupPoints H.val T →* GroupPoints H.val (inverseTwistAlgebra σ T))

private def convolutionOperator (σ : Gal(k'/k)) (T : TestAlgebra k') :
    (convolutionPoints (AdjointCocharacters.coordinateHopf H)).obj T ⟶
      (convolutionPoints (AdjointCocharacters.coordinateHopf H)).obj (inverseTwistAlgebra σ T) :=
  ConcreteCategory.ofHom (C := GrpCat)
    (X := (convolutionPoints (AdjointCocharacters.coordinateHopf H)).obj T)
    (Y := (convolutionPoints (AdjointCocharacters.coordinateHopf H)).obj (inverseTwistAlgebra σ T))
    ((coordinateEquiv H (inverseTwistAlgebra σ T)).symm.toMonoidHom.comp
      ((op σ T).comp (coordinateEquiv H T).toMonoidHom))

private theorem convolutionOperator_apply (σ : Gal(k'/k)) (T : TestAlgebra k')
    (f : (convolutionPoints (AdjointCocharacters.coordinateHopf H)).obj T) :
    coordinateEquiv H (inverseTwistAlgebra σ T) (convolutionOperator op σ T f) =
      op σ T (coordinateEquiv H T f) :=
  (coordinateEquiv H (inverseTwistAlgebra σ T)).apply_symm_apply _

variable (i : H.val ⟶ (fibre k').obj G) (hi : IsClosedImmersion i.hom.hom.left)
  (δ : Gal(k'/k) →* Aut G) (q : Gal(k'/k) → IntegralPoints G (integralRing k'))
  (hq : ∀ σ τ, q (σ * τ) = q σ * coefficientPoint (σ.toRingEquiv) (δ σ) (q τ))
  (formula : ∀ σ T p, includedPoint i (inverseTwistAlgebra σ T) (op σ T p) =
    ambientOperator (δ σ) (q σ) (algebraMap k' (inverseTwistAlgebra σ T)) (includedPoint i T p))

include hi hq formula in
private theorem pointOperator_identity (T : TestAlgebra k') (p : GroupPoints H.val T) :
    mapPoints (identityTwistHom (k := k) T) (op 1 T p) = p := by
  apply includedPoint_injective i hi T
  rw [includedPoint_map, formula]
  change changeRingHom G (integralRingMap (RingHom.id T))
      (ambientOperator (δ 1) (q 1) (algebraMap k' (inverseTwistAlgebra 1 T))
        (includedPoint i T p)) = includedPoint i T p
  rw [integralRingMap_id, changeRing_id]
  rw [corrector_one δ coefficientRingAction q hq, map_one δ, ambientOperator_apply]
  simp only [map_one, pinned_one, inv_one, one_mul, mul_one]

include hi hq formula in
private theorem pointOperator_composition (σ τ : Gal(k'/k)) (T : TestAlgebra k')
    (p : GroupPoints H.val T) :
    mapPoints (compositeTwistHom σ τ T) (op (σ * τ) T p) =
      op σ (inverseTwistAlgebra τ T) (op τ T p) := by
  apply includedPoint_injective i hi
  rw [includedPoint_map, formula]
  change changeRingHom G (integralRingMap (RingHom.id T))
      (ambientOperator (δ (σ * τ)) (q (σ * τ)) (algebraMap k' (inverseTwistAlgebra (σ * τ) T))
        (includedPoint i T p)) = _
  rw [integralRingMap_id, changeRing_id, formula, formula]
  rw [ambientOperator_comp δ coefficientRingAction q hq _ σ τ]
  have h (a : k' →+* T) : a.comp (coefficientRingAction (k := k) σ).toRingHom =
      a.comp σ.toRingHom := rfl
  rw [h, twistedScalar_cancel σ τ T, compositeTwist_scalar σ τ T]
  rfl

private def pointAction
    (naturality : ∀ (σ : Gal(k'/k)) {T U : TestAlgebra k'} (f : T ⟶ U)
      (p : GroupPoints H.val T),
      mapPoints (inverseTwistHom σ f) (op σ T p) = op σ U (mapPoints f p)) :
    TwistedPointAction k (AdjointCocharacters.coordinateHopf H) where
  operator := convolutionOperator op
  natural := by
    intro σ T U m
    apply GrpCat.ext
    intro f
    apply (coordinateEquiv H (inverseTwistAlgebra σ U)).injective
    change coordinateEquiv H _ (convolutionOperator op σ U ((convolutionPoints _).map m f)) =
      coordinateEquiv H _ ((convolutionPoints _).map (inverseTwistHom σ m)
        (convolutionOperator op σ T f))
    rw [convolutionOperator_apply, coordinateEquiv_map, coordinateEquiv_map,
      convolutionOperator_apply, naturality]
  identity := by
    intro T f x
    let m := identityTwistHom (k := k) T
    have h : (convolutionPoints _).map m (convolutionOperator op 1 T f) = f := by
      apply (coordinateEquiv H T).injective
      rw [coordinateEquiv_map, convolutionOperator_apply]
      exact pointOperator_identity op i hi δ q hq formula T (coordinateEquiv H T f)
    have he := congrArg (fun g : (convolutionPoints (AdjointCocharacters.coordinateHopf H)).obj T =>
      g.ofConv x) h
    change (convolutionOperator op 1 T f).ofConv x = f.ofConv x at he
    exact he
  composition := by
    intro σ τ T f x
    let m := compositeTwistHom σ τ T
    let U := inverseTwistAlgebra σ (inverseTwistAlgebra τ T)
    have h : (convolutionPoints _).map m (convolutionOperator op (σ * τ) T f) =
        convolutionOperator op σ (inverseTwistAlgebra τ T) (convolutionOperator op τ T f) := by
      apply (coordinateEquiv H U).injective
      rw [coordinateEquiv_map, convolutionOperator_apply, convolutionOperator_apply,
        convolutionOperator_apply]
      exact pointOperator_composition op i hi δ q hq formula σ τ T (coordinateEquiv H T f)
    have he := congrArg (fun g : (convolutionPoints (AdjointCocharacters.coordinateHopf H)).obj U =>
      g.ofConv x) h
    change (convolutionOperator op (σ * τ) T f).ofConv x =
      (convolutionOperator op σ (inverseTwistAlgebra τ T) (convolutionOperator op τ T f)).ofConv x
      at he
    exact he

end PointAction

section ScaledPointAction

open Specs.AdjointRepresentation (GroupPoints)
open _root_.LinearAlgebraicGroups.Descent
  (HopfDescentDatum inverseTwistAlgebra inverseTwistHom semilinearHopfFromPoints)
open private fibrePointsEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

variable {F K L : Type u} [Field F] [Field K] [Field L]
  [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
  [ValuativeRel F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension F L] [ValuativeExtension K L]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e} {B : SplitBuildingLevel Y}
  {t : Weights ((ApartmentRoots.split E.datum ℚ).SimpleWall p')}
  {x : ℚ ⊗[ℤ] E.Y} {d : ℕ} {y : E.Y} {ξ : Lˣ}
  {R : FaceReduction B t x d y ξ} {S : ScaledInput (F := F) R}

local notation "k₀" => residue F
local notation "k₁" => residue L
local notation "ground" => CommAlgCat.of k₁ k₁
local notation "red" => changeRingHom M'.group (residueHom (localIntegers L))

private abbrev residueInclusion (R : FaceReduction B t x d y ξ) :
    R.group.val ⟶ (fibre k₁).obj M'.group :=
  R.identityComponent.inclusion ≫ R.centralizer.inclusion

private theorem residueInclusion_closed (R : FaceReduction B t x d y ξ) :
    IsClosedImmersion (residueInclusion R).hom.hom.left := by
  change IsClosedImmersion
    (R.identityComponent.inclusion.hom.hom.left ≫ R.centralizer.inclusion.hom.hom.left)
  letI := R.identityComponent.isClosedImmersion
  letI := R.centralizer.isClosedImmersion
  infer_instance

open Specs.ExceptionalResidueCentralizerAction (MarkedCentralizer FixesMarkedImage)

private def residueCentralizer (R : FaceReduction B t x d y ξ) :
    MarkedCentralizer M'.toIntegralMarking k₁ d y :=
  ⟨R.muGroup, R.unitPoints, R.μImage, R.μImage_cocharacter, R.centralizer, R.centralizes,
    R.identityComponent, R.group_is_affine, R.component_open, R.component_eq⟩

private def reducedNormalizer (J : ScaledIntegralAction S) (σ : Gal(K/F)) :
    GroupPoints ((fibre k₁).obj M'.group) ground :=
  (fibrePointsEquiv M'.group ground).symm (red (J.normalizer σ))

private theorem reducedNormalizer_forget (J : ScaledIntegralAction S) (σ : Gal(K/F)) :
    forgetFibrePoint M'.group ground (reducedNormalizer J σ) = red (J.normalizer σ) :=
  (fibrePointsEquiv M'.group ground).apply_symm_apply _

private theorem reducedNormalizer_fixes (J : ScaledIntegralAction S) (σ : Gal(K/F)) :
    FixesMarkedImage (residueCentralizer R) (S.δ.pinned σ) (reducedNormalizer J σ) := by
  intro T r
  let f := integralRingMap (algebraMap k₁ T)
  let q₀ := changeRingHom M'.group f (forgetFibrePoint M'.group ground (reducedNormalizer J σ))
  let q := changeRingHom M'.group (residueHom (localIntegers L) ≫ f) (J.normalizer σ)
  let z := forgetFibrePoint M'.group T (r ≫ R.μImage.hom.hom)
  let s : rootsOfUnity d T := R.unitPoints.hom.app T r
  let δ := integralPointHom (S.δ.pinned σ).asIso.hom (integralRing T)
  have hq : q₀ = q :=
    (congrArg (changeRingHom M'.group f) (reducedNormalizer_forget J σ)).trans
      (changeRing_comp (residueHom (localIntegers L)) f (J.normalizer σ)).symm
  have hz : z = markedCocharacter M'.toIntegralMarking (integralRing T) y s.val :=
    R.μImage_cocharacter T r
  change q₀ * δ z * q₀⁻¹ = z
  rw [hq, hz]
  exact J.fixed_cocharacter σ (integralRing T) (residueHom (localIntegers L) ≫ f) s.val s.property

private theorem correctingResidue_product (J : ScaledIntegralAction S) (σ : Gal(K/F)) :
    J.correctingResidue σ =
      includedPoint (residueInclusion R) ground (R.reduction (S.b σ)) * red (J.normalizer σ) := by
  dsimp only [ScaledIntegralAction.correctingResidue]
  rw [map_mul]
  exact congrArg (· * red (J.normalizer σ)) (R.reduction_eq (S.b σ)).symm

private theorem scaledPointOperator (J : ScaledIntegralAction S) :
    letI := (residueMap F L).toAlgebra
    ∀ galois : Gal(k₁/k₀),
      ∃ action : ∀ T : TestAlgebra k₁,
          GroupPoints R.group.val T →* GroupPoints R.group.val (inverseTwistAlgebra galois T),
        (∀ T z, includedPoint (residueInclusion R) (inverseTwistAlgebra galois T) (action T z) =
          ambientOperator (S.δ.pinned (S.coefficients.residueAction.symm galois))
            (J.correctingResidue (S.coefficients.residueAction.symm galois))
            (algebraMap k₁ (inverseTwistAlgebra galois T))
            (includedPoint (residueInclusion R) T z)) ∧
        (∀ {T U : TestAlgebra k₁} (f : T ⟶ U) (z : GroupPoints R.group.val T),
          mapPoints (inverseTwistHom galois f) (action T z) = action U (mapPoints f z)) := by
  letI := (residueMap F L).toAlgebra
  intro galois
  let σ := S.coefficients.residueAction.symm galois
  let C := residueCentralizer R
  obtain ⟨action, hAction, hNatural⟩ :=
    ExceptionalResidueCentralizerAction.connectedCentralizerAction k₁ E M'.toIntegralMarking
      d y C galois.toRingEquiv (S.δ.pinned σ) (reducedNormalizer J σ)
      (R.reduction (S.b σ)) (reducedNormalizer_fixes J σ)
  refine ⟨action, ?_, ?_⟩
  · intro T z
    let U := inverseTwistAlgebra galois T
    let b := R.reduction (S.b σ)
    let n := reducedNormalizer J σ
    let bu : GroupPoints ((fibre k₁).obj M'.group) ground := b ≫ (residueInclusion R).hom.hom
    have hq : forgetFibrePoint M'.group ground (bu * n) = J.correctingResidue σ := by
      change (fibrePointsEquiv M'.group ground) (bu * n) = _
      rw [map_mul, correctingResidue_product J σ]
      change forgetFibrePoint M'.group ground bu * forgetFibrePoint M'.group ground n = _
      rw [reducedNormalizer_forget]
      rfl
    have h := (hAction T z (action T z)).2 rfl
    change includedPoint (residueInclusion R) U (action T z) =
      ambientOperator (S.δ.pinned σ) (forgetFibrePoint M'.group ground (bu * n))
        (algebraMap k₁ U) (includedPoint (residueInclusion R) T z) at h
    rw [hq] at h
    exact h
  · intro T U f z
    have hf : inverseTwistHom galois f =
        Specs.ExceptionalResidueCentralizerAction.twistHom galois.toRingEquiv f := by
      apply CommAlgCat.hom_ext
      ext a
      rfl
    rw [hf]
    exact hNatural f z

private def AmbientComparison (J : ScaledIntegralAction S)
    (hopf : letI := (residueMap F L).toAlgebra
      HopfDescentDatum k₀ (AdjointCocharacters.coordinateHopf R.group)) : Prop :=
  letI := (residueMap F L).toAlgebra
  ∀ (σ : Gal(K/F)) (T : TestAlgebra k₁)
      (f : CommAlgCat.of k₁ (AdjointCocharacters.coordinateHopf R.group) ⟶ T),
    let galois := S.coefficients.residueAction σ
    let U := transportAlgebra galois T
    includedPoint (residueInclusion R) U
        (coordinatePoint R.group U (transportPoint hopf galois f)) =
      ambientOperator (S.δ.pinned σ) (J.correctingResidue σ) (algebraMap k₁ U)
        (includedPoint (residueInclusion R) T (coordinatePoint R.group T f))

private theorem scaledHopfAction (J : ScaledIntegralAction S) :
    letI := (residueMap F L).toAlgebra
    ∃ hopf : HopfDescentDatum k₀ (AdjointCocharacters.coordinateHopf R.group),
      AmbientComparison J hopf := by
  letI := (residueMap F L).toAlgebra
  let coeff := S.coefficients.residueAction
  let δ := S.δ.pinned.comp coeff.symm.toMonoidHom
  let q := fun galois : Gal(k₁/k₀) => J.correctingResidue (coeff.symm galois)
  have hq (g h : Gal(k₁/k₀)) : q (g * h) = q g * coefficientPoint g.toRingEquiv (δ g) (q h) := by
    change J.correctingResidue (coeff.symm (g * h)) =
      J.correctingResidue (coeff.symm g) *
        coefficientPoint g.toRingEquiv (S.δ.pinned (coeff.symm g)) (J.correctingResidue (coeff.symm h))
    rw [map_mul]
    have he := residue_cocycle J (coeff.symm g) (coeff.symm h)
    change J.correctingResidue (coeff.symm g * coeff.symm h) =
      J.correctingResidue (coeff.symm g) *
        coefficientPoint (coeff (coeff.symm g)).toRingEquiv (S.δ.pinned (coeff.symm g))
          (J.correctingResidue (coeff.symm h)) at he
    rw [coeff.apply_symm_apply] at he
    exact he
  have hop galois := scaledPointOperator J galois
  choose op hop using hop
  let action := pointAction op (residueInclusion R) (residueInclusion_closed R) δ q hq
    (fun galois => (hop galois).1) (fun galois => (hop galois).2)
  obtain ⟨hopf, hHopf⟩ := semilinearHopfFromPoints k₀ k₁ (AdjointCocharacters.coordinateHopf R.group) action
  refine ⟨hopf, ?_⟩
  intro σ T f
  let galois := coeff σ
  let U := inverseTwistAlgebra galois T
  let conv := convolutionPoints (AdjointCocharacters.coordinateHopf R.group)
  let ft : conv.obj T := WithConv.toConv f.hom
  let fu : conv.obj U := WithConv.toConv (transportPoint hopf galois f).hom
  have hEvaluation : action.operator galois T ft = fu := by
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro a
    exact hHopf galois T ft a
  have hOperator := convolutionOperator_apply op galois T ft
  change coordinateEquiv R.group U (action.operator galois T ft) =
    op galois T (coordinateEquiv R.group T ft) at hOperator
  rw [hEvaluation, coordinateEquiv_apply, coordinateEquiv_apply] at hOperator
  change coordinatePoint R.group U (transportPoint hopf galois f) =
    op galois T (coordinatePoint R.group T f) at hOperator
  have hAmbient := (hop galois).1 T (coordinatePoint R.group T f)
  change includedPoint (residueInclusion R) U (op galois T _) =
    ambientOperator (δ galois) (q galois) (algebraMap k₁ U)
      (includedPoint (residueInclusion R) T (coordinatePoint R.group T f)) at hAmbient
  rw [← hOperator] at hAmbient
  have hs : coeff.symm galois = σ := coeff.symm_apply_apply σ
  change includedPoint (residueInclusion R) U
      (coordinatePoint R.group U (transportPoint hopf galois f)) =
    ambientOperator (S.δ.pinned σ) (J.correctingResidue σ) (algebraMap k₁ U)
      (includedPoint (residueInclusion R) T (coordinatePoint R.group T f))
  simpa only [δ, q, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hs] using hAmbient

open Specs.ExceptionalMarkedRootDescent (weylWordPerm)
open Specs.ExceptionalResidueCentralizerAction (scalarHom)
open Specs.ExceptionalResidueBorelTransport (borelPoint correction)
private theorem weylWord_index {D : BasedRootDatum.{u}} (l : List D.I) :
    weylWordPerm l = ((l.map (RootPairing.weylGroup.ofIdx D.datum)).prod).val.indexEquiv := by
  change weylWordPerm l = D.datum.weylGroupToPerm ((l.map (RootPairing.weylGroup.ofIdx D.datum)).prod)
  rw [map_list_prod, List.map_map]
  simp only [weylWordPerm, List.prod_eq_foldr, List.foldr_map]
  rfl

private abbrev normalizerWord (S : ScaledInput (F := F) R) (σ : Gal(K/F)) : List E.I :=
  let N := Y.ad.localIwahori.normalizer
  N.word (N.label (typeLift (Y := Y) S.a σ))

private def faceRoots (E : BasedRootDatum.{u}) (x : ℚ ⊗[ℤ] E.Y) : Set E.I :=
  {i | ∃ m : ℤ, (ApartmentRoots.split E.datum ℚ).root i x = m}

private def positiveFaceRoots (E : BasedRootDatum.{u}) (p x : ℚ ⊗[ℤ] E.Y) : Set E.I :=
  {i | ∃ m : ℤ, (ApartmentRoots.split E.datum ℚ).root i x = m ∧
    (ApartmentRoots.split E.datum ℚ).positive p (i, -m)}

private theorem normalizerWord_positive (S : ScaledInput (F := F) R) (σ : Gal(K/F)) :
    (S.δ.diagram σ).indexEquiv.trans (weylWordPerm (normalizerWord S σ)) ''
      positiveFaceRoots E p' x = positiveFaceRoots E p' x := by
  let N := Y.ad.localIwahori.normalizer
  let n := typeLift (Y := Y) S.a σ
  obtain ⟨_, _, _, hword⟩ := Y.ad_points.2.1
  have h : weylWordPerm (normalizerWord S σ) = (N.label n).val.indexEquiv := by
    rw [weylWord_index]
    exact congrArg (fun w : E.datum.weylGroup => w.val.indexEquiv) (hword (N.label n))
  rw [h]
  let perm := (S.δ.diagram σ).indexEquiv.trans (N.label n).val.indexEquiv
  letI := E.finiteRoots
  apply Set.map_eq_of_subset (f := perm.toEmbedding) ?_ (Set.toFinite _)
  rintro _ ⟨i, ⟨m, hm, hp⟩, rfl⟩
  obtain ⟨he, hpos⟩ := positive_roots_transport S σ i m hm
  exact ⟨_, he, hpos.mpr hp⟩

private theorem normalizerResidue_eq (J : ScaledIntegralAction S) (σ : Gal(K/F)) :
    ∃ v : TorusValues E (integralRing k₁),
      red (J.normalizer σ) = correction M' (normalizerWord S σ) v := by
  obtain ⟨v, hv⟩ := integralNormalizerCorrection Y S.ρ S.h S.δ S.a σ y ξ
    (S.torusValues σ) (S.torusValues_eq σ) (S.valuation_cancel σ)
  let f := residueHom (localIntegers L)
  let v' := (Units.map f.hom.toMonoidHom).comp v
  let l := normalizerWord S σ
  let q := markedTorusHom M'.toIntegralMarking (localIntegers L) v *
    markedWeylWord M'.toIntegralMarking (localIntegers L) l
  have h : J.normalizer σ = q :=
    (integral_points_injective M'.affine (localIntegersInclusion L) (fun _ _ he => Subtype.ext he))
      ((J.normalizer_eq σ).trans hv.symm)
  refine ⟨v', ?_⟩
  change changeRingHom M'.group f (J.normalizer σ) = _
  rw [h]
  change changeRingHom M'.group f
    (markedTorusHom M'.toIntegralMarking _ v * markedWeylWord M'.toIntegralMarking _ l) = _
  rw [map_mul, torus_changeRing, markedWeylWord_changeRing]
  rfl

private theorem residueBorelTransport (J : ScaledIntegralAction S) (σ : Gal(K/F))
    (T : TestAlgebra k₁) (z : IntegralPoints M'.group (integralRing T)) :
    letI := (residueMap F L).toAlgebra
    let galois := S.coefficients.residueAction σ
    let U := transportAlgebra galois T
    z ∈ Set.range (borelPoint (residueInclusion R) R.borel T) ↔
      ambientOperator (S.δ.pinned σ) (red (J.normalizer σ)) (algebraMap k₁ U) z ∈
        Set.range (borelPoint (residueInclusion R) R.borel U) := by
  letI := (residueMap F L).toAlgebra
  let galois := S.coefficients.residueAction σ
  let U := transportAlgebra galois T
  change z ∈ Set.range (borelPoint (residueInclusion R) R.borel T) ↔
    ambientOperator (S.δ.pinned σ) (red (J.normalizer σ)) (algebraMap k₁ U) z ∈
      Set.range (borelPoint (residueInclusion R) R.borel U)
  obtain ⟨v, hv⟩ := normalizerResidue_eq J σ
  rw [hv, ambientOperator_apply]
  exact ExceptionalResidueBorelTransport.markedBorelTransport M' R.ambientMarking
    R.group R.reductive (residueInclusion R) (residueInclusion_closed R) R.torus R.borel
    R.torus_split R.torus_maximal R.borel_is_borel R.borel_torus R.torusComparison
    R.torus_marked (faceRoots E x) (positiveFaceRoots E p' x)
    R.root_characters R.roots R.borel_roots (S.δ.pinned σ) (S.δ.diagram σ)
    (S.δ.torus_formula σ) (S.δ.root_formula σ) (normalizerWord S σ) v
    (normalizerWord_positive S σ) T galois.toRingEquiv z

private theorem borelPoint_included (T : TestAlgebra k₁) (b : GroupPoints R.borel.group T) :
    borelPoint (residueInclusion R) R.borel T b =
      includedPoint (residueInclusion R) T (b ≫ R.borel.inclusion.hom.hom) := by
  change forgetFibrePoint M'.group T
      (b ≫ (R.borel.inclusion ≫ residueInclusion R).hom.hom) =
    forgetFibrePoint M'.group T ((b ≫ R.borel.inclusion.hom.hom) ≫ (residueInclusion R).hom.hom)
  rw [Grp.comp_hom_hom, Category.assoc]

private theorem ambientOperator_product {k A : Type u} [Field k] [CommRing A]
    {G : IntegralGroup.{u}} (δ : Aut G) (q n : IntegralPoints G (integralRing k))
    (a : k →+* A) (z : IntegralPoints G (integralRing A)) :
    let u := changeRingHom G (integralRingMap a) q
    ambientOperator δ (q * n) a z = u * ambientOperator δ n a z * u⁻¹ := by
  simp only [ambientOperator_apply, map_mul]
  group

private theorem scaledBorelComparison (J : ScaledIntegralAction S) :
    letI := (residueMap F L).toAlgebra
    ∀ (σ : Gal(K/F)) (T : TestAlgebra k₁),
      let galois := S.coefficients.residueAction σ
      let U := transportAlgebra galois T
      ∀ (p : GroupPoints R.group.val T) (p' : GroupPoints R.group.val U),
        includedPoint (residueInclusion R) U p' =
          ambientOperator (S.δ.pinned σ) (J.correctingResidue σ) (algebraMap k₁ U)
            (includedPoint (residueInclusion R) T p) →
        let u : GroupPoints R.group.val U := mapPoints (scalarHom U) (R.reduction (S.b σ))
        (∃ b : GroupPoints R.borel.group T, b ≫ R.borel.inclusion.hom.hom = p) ↔
          ∃ b' : GroupPoints R.borel.group U,
            let v : GroupPoints R.group.val U := b' ≫ R.borel.inclusion.hom.hom
            u * v * u⁻¹ = p' := by
  letI := (residueMap F L).toAlgebra
  dsimp only
  intro σ T p p' hp
  let galois := S.coefficients.residueAction σ
  let U := transportAlgebra galois T
  let i := residueInclusion R
  let b := R.reduction (S.b σ)
  let u : GroupPoints R.group.val U := mapPoints (scalarHom U) b
  let z := includedPoint i T p
  let w := ambientOperator (S.δ.pinned σ) (red (J.normalizer σ)) (algebraMap k₁ U) z
  have himage : z ∈ Set.range (borelPoint i R.borel T) ↔ w ∈ Set.range (borelPoint i R.borel U) :=
    residueBorelTransport J σ T z
  have hu : includedPoint i U u =
      changeRingHom M'.group (integralRingMap (algebraMap k₁ U)) (includedPoint i ground b) :=
    includedPoint_map i (scalarHom U) b
  have hp' : includedPoint i U p' = includedPoint i U u * w * (includedPoint i U u)⁻¹ := by
    rw [hp, correctingResidue_product J σ, ambientOperator_product, hu]
  change (∃ a : GroupPoints R.borel.group T, a ≫ R.borel.inclusion.hom.hom = p) ↔
    ∃ a : GroupPoints R.borel.group U,
      let v : GroupPoints R.group.val U := a ≫ R.borel.inclusion.hom.hom
      u * v * u⁻¹ = p'
  constructor
  · rintro ⟨a, ha⟩
    have hs : z ∈ Set.range (borelPoint i R.borel T) :=
      ⟨a, (borelPoint_included T a).trans (congrArg (includedPoint i T) ha)⟩
    obtain ⟨v, hv⟩ := himage.mp hs
    refine ⟨v, ?_⟩
    apply includedPoint_injective i (residueInclusion_closed R) U
    simp only [map_mul, map_inv]
    rw [← borelPoint_included U v, hv]
    exact hp'.symm
  · rintro ⟨a, ha⟩
    have h := congrArg (includedPoint i U) ha
    simp only [map_mul, map_inv] at h
    rw [← borelPoint_included U a, hp'] at h
    have hs : w ∈ Set.range (borelPoint i R.borel U) :=
      ⟨a, mul_left_cancel (mul_right_cancel h)⟩
    obtain ⟨v, hv⟩ := himage.mpr hs
    refine ⟨v, includedPoint_injective i (residueInclusion_closed R) T ?_⟩
    exact (borelPoint_included T v).symm.trans hv

private theorem ambientOperator_base {k : Type u} [Field k] {G : IntegralGroup.{u}}
    (δ : Aut G) (galois : k ≃+* k) (q z : IntegralPoints G (integralRing k)) :
    changeRingHom G (integralRingMap galois.toRingHom) (ambientOperator δ q galois.symm.toRingHom z) =
      q * coefficientPoint galois δ z * q⁻¹ := by
  rw [ambientOperator_changeRing]
  have h : galois.toRingHom.comp galois.symm.toRingHom = RingHom.id k :=
    RingHom.ext galois.apply_symm_apply
  rw [h, ambientOperator_apply, integralRingMap_id, changeRing_id]
  rfl

/-- The scaled operators restrict to the given connected centralizer and
induce the Hopf descent datum with the marked Borel and reduction comparisons. -/
theorem scaledParahoricDescent : ScaledParahoricDescent.{u} := by
  intro F K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D E M M' c p p' e Y B t x d y ξ R S
  obtain ⟨J⟩ := scaled_cocycle S
  obtain ⟨hopf, hAmbient⟩ := scaledHopfAction J
  refine ⟨J, ⟨{ hopf := hopf, ambient := ?_, borel := ?_, rational := ?_ }⟩⟩
  · exact hAmbient
  · letI := (residueMap F L).toAlgebra
    intro σ T f
    let galois := S.coefficients.residueAction σ
    let U := transportAlgebra galois T
    exact scaledBorelComparison J σ T (coordinatePoint R.group T f)
      (coordinatePoint R.group U (transportPoint hopf galois f)) (hAmbient σ T f)
  · letI := (residueMap F L).toAlgebra
    dsimp only
    intro σ g f hf
    let galois := S.coefficients.residueAction σ
    let T := CommAlgCat.of (residue L) (residue L)
    let U := transportAlgebra galois T
    let m : U ⟶ T := ConcreteCategory.ofHom (C := CommAlgCat (residue L))
      { galois.toRingHom with commutes' := galois.apply_symm_apply }
    let j := residueInclusion R
    change mapPoints m (coordinatePoint R.group U (transportPoint hopf galois f)) =
      R.reduction ⟨_, J.invariant σ g⟩
    apply includedPoint_injective j (residueInclusion_closed R) T
    rw [includedPoint_map]
    have h := hAmbient σ T f
    change includedPoint j U (coordinatePoint R.group U (transportPoint hopf galois f)) =
      ambientOperator (S.δ.pinned σ) (J.correctingResidue σ) (algebraMap (residue L) U)
        (includedPoint j T (coordinatePoint R.group T f)) at h
    rw [h]
    have hr (g : parahoric Y.ad (cotype t)) :
        includedPoint j T (R.reduction g) =
          changeRingHom M'.group (residueHom (localIntegers L)) (R.integral g) := R.reduction_eq g
    change coordinatePoint R.group T f = R.reduction g at hf
    rw [hf, hr, hr]
    exact (ambientOperator_base (S.δ.pinned σ) galois.toRingEquiv
      (J.correctingResidue σ) _).trans (ambient_residue_equivariance J σ g).symm

end ScaledPointAction

end
end LinearAlgebraicGroups.Arithmetic.ExceptionalScaledParahoricAction
