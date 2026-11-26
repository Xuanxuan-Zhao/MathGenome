import Specs.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalRationalUnitTorus
import LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.RamifiedExceptionalRationalUnitTorus

open CategoryTheory ValuativeRel IsLocalRing
open scoped CategoryTheory.MonObj
open Specs.AdjointRepresentation (GroupPoints)
open Specs.ExceptionalAffineBruhat (DiagramCompositum FieldPoints FoldedApartment FoldedLevel
  RamifiedReference RootSlots pinnedCoefficientPoint residue scalarPoints)
open Specs.ExceptionalIwahoriCongruence (CellValues cellValue changeRing integralRing integralRingMap)
open Specs.ExceptionalIwahoriImageComparison (integralUnitTorus)
open Specs.ExceptionalLocalRootCoordinates (residueMap)
open Specs.ExceptionalMarkedRootDescent (markedFibrePoint)
open Specs.ExceptionalValuedTorusNormalizer (simplePermutation valuationRingInclusion)
open Specs.IntegralSemisimpleModel (IntegralAlgebra IntegralPoints Model TorusValues
  integralSpec splitTorus torusPoint)
open Specs.Pinning (BasedIso BasedRootDatum)
open Specs.RamifiedExceptionalRationalUnitTorus
open Arithmetic.ExceptionalAffineBruhat (markedCoefficientAction markedPinnedAction markedPinnedAction_torus)

open private torusPoint_bijective torusPoint_natural cellValue_torus
  from LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
open private markedPinnedAction_apply markedCoefficientAction_apply
  from LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
open private fibrePointEquiv quadraticGalois
  from LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent

universe u

attribute [local instance] Specs.ExceptionalLocalRootCoordinates.canonicalExtension

noncomputable section

local notation "Oᵥ[" K "]" => Valuation.valuationSubring (valuation K)

private theorem markedTorusPoint_natural {D : BasedRootDatum.{u}} (M : Model D)
    {S T : IntegralAlgebra.{u}} (f : S ⟶ T) (q : TorusValues D S) :
    changeRing f (markedTorusPoint M q) =
      markedTorusPoint M ((Units.map f.hom.toRingHom).comp q) := by
  change integralSpec.map f.op ≫ (torusPoint D S q ≫ M.torus.hom.hom) = _
  rw [← Category.assoc]
  exact congrArg (· ≫ M.torus.hom.hom) (torusPoint_natural f q)

private theorem markedTorusPoint_injective {D : BasedRootDatum.{u}} (M : Model D)
    (S : IntegralAlgebra.{u}) :
    Function.Injective (markedTorusPoint (S := S) M) := by
  have := M.torusClosed
  have : Mono M.torus.hom.hom := Over.mono_of_mono_left _
  exact fun _ _ h => (torusPoint_bijective D S).injective ((cancel_mono M.torus.hom.hom).mp h)

/-- The generic fibre of the marked valuation-ring torus gives the unit subgroup. -/
theorem integralUnitTorusCoordinates : IntegralUnitTorusCoordinates.{u} := by
  intro K _ _ D M
  refine ⟨fun q => markedTorusPoint_natural M (valuationRingInclusion K) q, fun p => ?_⟩
  change
    (∃ t : IntegralPoints (splitTorus D) (integralRing Oᵥ[K]),
      changeRing (valuationRingInclusion K) t ≫ M.torus.hom.hom = p) ↔ _
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨q, rfl⟩ := (torusPoint_bijective D (integralRing Oᵥ[K])).surjective t
    exact ⟨q, ht.symm.trans (congrArg (· ≫ M.torus.hom.hom)
      (torusPoint_natural (valuationRingInclusion K) q))⟩
  · rintro ⟨q, rfl⟩
    exact ⟨torusPoint D _ q, congrArg (· ≫ M.torus.hom.hom)
      (torusPoint_natural (valuationRingInclusion K) q)⟩

private theorem torusValues_ext_basis {D : BasedRootDatum.{u}} {S : IntegralAlgebra.{u}}
    {I : Type u} (b : Module.Basis I ℤ D.X) {f g : TorusValues D S}
    (h : ∀ i, f (Multiplicative.ofAdd (b i)) = g (Multiplicative.ofAdd (b i))) :
    f = g := by
  let asLinear (t : TorusValues D S) : D.X →ₗ[ℤ] Additive Sˣ :=
    t.toAdditiveRight.toIntLinearMap
  have he : asLinear f = asLinear g := b.ext h
  exact MonoidHom.ext fun x => DFunLike.congr_fun he x.toAdd

/-- Lift the values as a function of each residue unit, so equal basis values have equal lifts. -/
private theorem liftInvariantValues {D : BasedRootDatum.{u}} (τ : BasedIso D D)
    (had : D.datum.rootSpan ℤ = ⊤) {S U : IntegralAlgebra.{u}} (ρ : Sˣ →* Uˣ)
    (hρ : Function.Surjective ρ) (t : TorusValues D U) (ht : IsInvariant τ t) :
    ∃ q : TorusValues D S, IsInvariant τ q ∧ ρ.comp q = t := by
  classical
  let b : Module.Basis D.base.support ℤ D.X :=
    Module.Basis.mk D.base.linearIndepOn_root (by
      change ⊤ ≤ Submodule.span ℤ (Set.range (D.datum.root ∘ ((↑) : D.base.support → D.I)))
      rw [Set.range_comp, Subtype.range_coe, D.base.span_int_root_support]
      exact had.ge)
  have hb (i : D.base.support) : b i = D.datum.root i := Module.Basis.mk_apply _ _ _
  let lift (z : Uˣ) : Sˣ := (hρ z).choose
  have hlift (z : Uˣ) : ρ (lift z) = z := (hρ z).choose_spec
  let v (i : D.base.support) := lift (t (Multiplicative.ofAdd (b i)))
  let q₀ : D.X →ₗ[ℤ] Additive Sˣ := b.constr ℤ (fun i => Additive.ofMul (v i))
  let q : TorusValues D S :=
    { toFun := fun x => (q₀ x.toAdd).toMul
      map_one' := q₀.map_zero
      map_mul' := fun x y => q₀.map_add x.toAdd y.toAdd }
  have hq (i : D.base.support) : q (Multiplicative.ofAdd (b i)) = v i :=
    b.constr_basis ℤ (fun i => Additive.ofMul (v i)) i
  let perm := τ.val.weightEquiv.toLinearMap.toAddMonoidHom.toMultiplicative
  have hinv : q.comp perm = q := by
    apply torusValues_ext_basis b
    intro i
    let j := simplePermutation D τ i
    have hperm : τ.val.weightEquiv (b i) = b j := by
      rw [hb, hb]
      exact RootPairing.Hom.root_weightMap_apply D.datum D.datum i.val τ.val.toHom
    change q (Multiplicative.ofAdd (τ.val.weightEquiv (b i))) = _
    rw [hperm, hq, hq]
    exact congrArg lift ((congrArg (fun x => t (Multiplicative.ofAdd x)) hperm).symm.trans
      (ht (b i)))
  refine ⟨q, fun χ => DFunLike.congr_fun hinv (Multiplicative.ofAdd χ), ?_⟩
  apply torusValues_ext_basis b
  intro i
  change ρ (q (Multiplicative.ofAdd (b i))) = _
  rw [hq]
  exact hlift _

section FiniteLevel

variable {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
  {σ : Gal(L/F)} {A : FoldedApartment (R.diagram σ)}
  (T : DiagramCompositum F L k σ)
  (X : FoldedLevel R σ T.diagram (IsScalarTower.toAlgHom F L T.field) A)

set_option maxHeartbeats 800000 in
private theorem markedTorus_rational_iff (q : TorusValues D (integralRing T.field)) :
    markedTorusPoint M q ∈ X.points.range ↔
      ∀ χ : D.X, q (Multiplicative.ofAdd ((R.diagram σ).val.weightEquiv χ)) =
        Units.map T.diagram.toRingHom (q (Multiplicative.ofAdd χ)) := by
  let K := T.field
  let f : Gal(K/F) := T.diagram.restrictScalars F
  let δ := R.pin (R.outer σ)
  let e := fibrePointEquiv R.fibre (CommAlgCat.of F K)
  let p : FieldPoints M K := markedTorusPoint M q
  let v := e.symm p
  have hv : markedFibrePoint R.fibre (CommAlgCat.of F K) v = p := e.apply_symm_apply p
  let q₁ : TorusValues D (integralRing K) := (Units.map T.diagram.toRingHom).comp q
  obtain ⟨q', hq', hval⟩ := markedPinnedAction_torus R.fibre R.sequence (R.outer σ) q₁
  let vσ : GroupPoints R.fibre.realization.pinned.pair.G.val (CommAlgCat.of F K) :=
    (testSpec F).map (CommAlgCat.ofHom f.toAlgHom).op ≫ v
  have hσ : markedFibrePoint R.fibre (CommAlgCat.of F K) vσ = markedTorusPoint M q₁ := by
    calc
      _ = markedCoefficientAction M f (markedFibrePoint R.fibre (CommAlgCat.of F K) v) :=
        (markedCoefficientAction_apply R.fibre f v).symm
      _ = scalarPoints M T.diagram.toRingHom p := by rw [hv]; rfl
      _ = _ := markedTorusPoint_natural M (integralRingMap T.diagram.toRingHom) q
  have hpinned : pinnedCoefficientPoint R.fibre δ f v = markedTorusPoint M q' := by
    calc
      _ = markedPinnedAction (K := K) R.fibre δ
          (markedFibrePoint R.fibre (CommAlgCat.of F K) vσ) :=
        (markedPinnedAction_apply R.fibre δ vσ).symm
      _ = _ := (congrArg (markedPinnedAction (K := K) R.fibre δ) hσ).trans hq'
  change ∀ χ : D.X, q' (Multiplicative.ofAdd ((R.diagram σ).val.weightEquiv χ)) =
    Units.map T.diagram.toRingHom (q (Multiplicative.ofAdd χ)) at hval
  have hfixed := X.fixed_points v
  rw [hv, hpinned] at hfixed
  change p ∈ X.points.range ↔ _
  rw [hfixed]
  constructor
  · intro h χ
    have hqq : q' = q := markedTorusPoint_injective M (integralRing K) h
    rw [hqq] at hval
    exact hval χ
  · intro h
    have hqq : q' = q := by
      apply MonoidHom.ext
      intro χ
      obtain ⟨a, ha⟩ := (R.diagram σ).val.weightEquiv.surjective χ.toAdd
      rw [← show Multiplicative.ofAdd ((R.diagram σ).val.weightEquiv a) = χ from congrArg _ ha]
      exact (hval a).trans (h a).symm
    rw [hqq]

private theorem chartTorus_iff (q : TorusValues D (integralRing T.field)) :
    q ∈ X.comparison.chart.chart.torus ↔ markedTorusPoint M q ∈ X.points.range := by
  let C := X.comparison.chart
  let z : CellValues D (integralRing T.field) C.negative C.positive := (0, q, 0)
  have hz : cellValue M.toIntegralMarking _ _ _ z = markedTorusPoint M q :=
    cellValue_torus M.toIntegralMarking _ _ _ q
  rw [← hz, C.rational]
  constructor
  · intro h
    refine ⟨⟨q, h⟩, fun _ => 0, Prod.ext (funext fun l => ?_) (Prod.ext rfl (funext fun l => ?_))⟩
    · change _ * C.chart.negMap l 0 = 0
      simp
    · change _ * C.chart.posMap l 0 = 0
      simp
  · rintro ⟨t, x, h⟩
    have hcoord : t.val = q := congrArg (fun w : CellValues D _ _ _ => w.2.1) h
    exact hcoord ▸ t.property

include X in
private theorem coefficientResidue_surjective :
    Function.Surjective (residueMap k T.field) := by
  let _ : Finite (residue k) := inferInstanceAs (Finite 𝓀[k])
  let _ : Finite (residue T.field) := inferInstanceAs (Finite 𝓀[T.field])
  let f := residueMap k T.field
  exact ((Nat.bijective_iff_injective_and_card f).mpr ⟨f.injective, X.same_residue.symm⟩).surjective

private theorem diagramPreservesValuation (x : T.field) :
    valuation T.field (T.diagram x) = valuation T.field x := by
  have hs := (quadraticGalois T.degree T.diagram T.diagram_ne).2
  have hι : Function.Involutive T.diagram := fun y =>
    congrArg (fun a : Gal(T.field/k) => a y) hs
  have h := Arithmetic.ExceptionalLocalRootCoordinates.involutionPreservesValuation T.diagram hι x
  exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt T.field).injective h

private def diagramOnIntegers : Oᵥ[T.field] ≃+* Oᵥ[T.field] where
  toFun x := ⟨T.diagram x, by
    change valuation T.field (T.diagram (x : T.field)) ≤ 1
    rw [diagramPreservesValuation]
    exact x.property⟩
  invFun x := ⟨T.diagram.symm x, by
    change valuation T.field (T.diagram.symm (x : T.field)) ≤ 1
    rw [← diagramPreservesValuation T (T.diagram.symm (x : T.field)), AlgEquiv.apply_symm_apply]
    exact x.property⟩
  left_inv x := Subtype.ext (T.diagram.symm_apply_apply x)
  right_inv x := Subtype.ext (T.diagram.apply_symm_apply x)
  map_mul' x y := Subtype.ext (map_mul T.diagram (x : T.field) y)
  map_add' x y := Subtype.ext (map_add T.diagram (x : T.field) y)

include X in
private theorem diagramOnIntegers_residue (b : Oᵥ[T.field]) :
    IsLocalRing.residue Oᵥ[T.field] (diagramOnIntegers T b) = IsLocalRing.residue Oᵥ[T.field] b := by
  let a := algebraMap Oᵥ[k] Oᵥ[T.field]
  let d := diagramOnIntegers T
  obtain ⟨z, hz⟩ := coefficientResidue_surjective T X (IsLocalRing.residue Oᵥ[T.field] b)
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
  change IsLocalRing.residue Oᵥ[T.field] (a c) = IsLocalRing.residue Oᵥ[T.field] b at hz
  have hd : d (a c) = a c := Subtype.ext (T.diagram.commutes (c : k))
  let _ : IsLocalHom d.toRingHom := IsLocalHom.of_surjective _ d.surjective
  have h := congrArg (ResidueField.map d.toRingHom) hz
  change IsLocalRing.residue Oᵥ[T.field] (d (a c)) = IsLocalRing.residue Oᵥ[T.field] (d b) at h
  rw [hd] at h
  exact h.symm.trans hz

private theorem rationalTorus_reduction (q : TorusValues D (integralRing Oᵥ[T.field]))
    (hq : markedTorusPoint M (genericTorusValues q) ∈ X.points.range) :
    IsInvariant (R.diagram σ) (reduceTorusValues q) := by
  intro χ
  have hχ := (markedTorus_rational_iff T X (genericTorusValues q)).mp hq χ
  have h :
      (q (Multiplicative.ofAdd ((R.diagram σ).val.weightEquiv χ)) : Oᵥ[T.field]) =
        diagramOnIntegers T (q (Multiplicative.ofAdd χ) : Oᵥ[T.field]) :=
    Subtype.ext (congrArg Units.val hχ)
  apply Units.ext
  change IsLocalRing.residue Oᵥ[T.field] (q (Multiplicative.ofAdd ((R.diagram σ).val.weightEquiv χ))) =
    IsLocalRing.residue Oᵥ[T.field] (q (Multiplicative.ofAdd χ))
  rw [h, diagramOnIntegers_residue T X]

include X in
private theorem coefficientUnits_surjective :
    Function.Surjective
      (Units.map ((IsLocalRing.residue Oᵥ[T.field]).comp
        (algebraMap Oᵥ[k] Oᵥ[T.field])).toMonoidHom) := by
  intro z
  let f := residueMap k T.field
  obtain ⟨a, ha⟩ := coefficientResidue_surjective T X (z : residue T.field)
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective a
  change f (IsLocalRing.residue Oᵥ[k] c) = (z : residue T.field) at ha
  have hc : IsLocalRing.residue Oᵥ[k] c ≠ 0 := by
    intro h
    rw [h, map_zero] at ha
    exact z.ne_zero ha.symm
  obtain ⟨v, rfl⟩ := (residue_ne_zero_iff_isUnit c).mp hc
  exact ⟨v, Units.ext ha⟩

private theorem rationalTorus_lift (had : D.datum.rootSpan ℤ = ⊤)
    (t : TorusValues D (integralRing (residue T.field))) (ht : IsInvariant (R.diagram σ) t) :
    ∃ q : TorusValues D (integralRing Oᵥ[T.field]), reduceTorusValues q = t ∧
      markedTorusPoint M (genericTorusValues q) ∈ X.points.range := by
  let a : Oᵥ[k] →+* Oᵥ[T.field] := algebraMap _ _
  let ρ : (integralRing Oᵥ[k])ˣ →* (integralRing (residue T.field))ˣ :=
    Units.map ((IsLocalRing.residue Oᵥ[T.field]).comp a).toMonoidHom
  obtain ⟨q₀, hinv, hred⟩ :=
    liftInvariantValues (R.diagram σ) had ρ (coefficientUnits_surjective T X) t ht
  let q : TorusValues D (integralRing Oᵥ[T.field]) := (Units.map a).comp q₀
  refine ⟨q, ?_, (markedTorus_rational_iff T X _).mpr ?_⟩
  · apply MonoidHom.ext
    intro χ
    apply Units.ext
    exact congrArg Units.val (DFunLike.congr_fun hred χ)
  · intro χ
    apply Units.ext
    change algebraMap k T.field (q₀ (Multiplicative.ofAdd ((R.diagram σ).val.weightEquiv χ)) : Oᵥ[k]) =
      T.diagram (algebraMap k T.field (q₀ (Multiplicative.ofAdd χ) : Oᵥ[k]))
    rw [hinv χ, AlgEquiv.commutes]

end FiniteLevel

/-- The marked rational torus and its exact invariant residue image at each given level. -/
theorem rationalUnitTorusComparison : RationalUnitTorusComparison.{u} := by
  intro F L k _ _ _ _ _ _ _ _ _ _ _ D M R σ A T X
  refine ⟨markedTorus_rational_iff T X, chartTorus_iff T X, ?_,
    rationalTorus_reduction T X, rationalTorus_lift T X⟩
  intro g
  exact (integralUnitTorusCoordinates M).2 (X.points g)

end
end LinearAlgebraicGroups.RamifiedExceptionalRationalUnitTorus
