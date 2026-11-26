import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RamifiedCongruenceTorusCoordinates

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory WithZero

universe u

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace LinearAlgebraicGroups.Arithmetic.RamifiedCongruenceTorusCoordinates

open _root_.LinearAlgebraicGroups.Specs
open RamifiedCongruenceTorusCoordinates
open IntegralSemisimpleModel
open ExceptionalAffineBruhat
open ExceptionalAffineRootSystems (e6Partner)
open ExceptionalIwahoriCongruence (integralRing cellValue cellValuePoint rootValuePoint)
open ExceptionalMarkedRootDescent (MarkedFibre markedFibrePoint)
open ExceptionalLocalRootCoordinates (normalizedValuation)
open ExceptionalValuedTorusNormalizer (markedDiagramEquiv)
open Pinning (BasedRootDatum)
open AdjointRepresentation (GroupPoints)
open CharacterPairing (characterValue)
open AutomorphismSequence (scalarAut Aligned HasLatticeAction forgetPinning)

attribute [local instance] integerAlgebra

noncomputable section

private def simpleBasis (D : BasedRootDatum.{u}) (b : Fin 6 ≃ D.base.support)
    (h : D.datum.rootSpan ℤ = ⊤) : Module.Basis (Fin 6) ℤ D.X :=
  let e : D.datum.rootSpan ℤ ≃ₗ[ℤ] D.X :=
    (LinearEquiv.ofEq _ _ h).trans (Submodule.topEquiv : (⊤ : Submodule ℤ D.X) ≃ₗ[ℤ] D.X)
  (D.base.toWeightBasisInt.map e).reindex b.symm

private theorem simpleBasis_apply (D : BasedRootDatum.{u}) (b : Fin 6 ≃ D.base.support)
    (h : D.datum.rootSpan ℤ = ⊤) (i : Fin 6) :
    simpleBasis D b h i = simpleCharacter b i := by
  simp [simpleBasis, simpleCharacter]

private theorem torusValues_ext {D : BasedRootDatum.{u}} {index : Type*}
    (B : Module.Basis index ℤ D.X) {S : IntegralAlgebra.{u}} {s t : TorusValues D S}
    (h : ∀ i, s (Multiplicative.ofAdd (B i)) = t (Multiplicative.ofAdd (B i))) : s = t := by
  apply AddMonoidHom.toMultiplicativeLeft.symm.injective
  let x := (AddMonoidHom.toMultiplicativeLeft.symm s).toIntLinearMap
  let y := (AddMonoidHom.toMultiplicativeLeft.symm t).toIntLinearMap
  have hxy : x = y := B.ext fun i => congrArg Additive.ofMul (h i)
  exact congrArg LinearMap.toAddMonoidHom hxy

private theorem torusValuesOfBasis {D : BasedRootDatum.{u}} {index : Type*}
    (B : Module.Basis index ℤ D.X) (S : IntegralAlgebra.{u}) (v : index → Sˣ) :
    ∃! t : TorusValues D S, ∀ i, t (Multiplicative.ofAdd (B i)) = v i := by
  let x : D.X →ₗ[ℤ] Additive Sˣ := B.constr ℤ (fun i => Additive.ofMul (v i))
  let t : TorusValues D S := x.toAddMonoidHom.toMultiplicativeLeft
  have ht (i : index) : t (Multiplicative.ofAdd (B i)) = v i :=
    congrArg Additive.toMul (B.constr_basis ℤ (fun j => Additive.ofMul (v j)) i)
  exact ⟨t, ht, fun s hs => torusValues_ext B (fun i => (hs i).trans (ht i).symm)⟩

private theorem torusCongruence {D : BasedRootDatum.{u}} {index : Type*}
    (B : Module.Basis index ℤ D.X) {S : IntegralAlgebra.{u}} (I : Ideal S) (t : TorusValues D S)
    (h : ∀ i, (t (Multiplicative.ofAdd (B i)) : S) - 1 ∈ I) (χ : D.X) :
    (t (Multiplicative.ofAdd χ) : S) - 1 ∈ I := by
  let Q : IntegralAlgebra.{u} := CommAlgCat.of Integers.{u} (S ⧸ I)
  let red : TorusValues D Q := (Units.map (Ideal.Quotient.mk I).toMonoidHom).comp t
  have hr : red = 1 := torusValues_ext B (fun i => by
    apply Units.ext
    exact (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr (h i))
  exact (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mp
    (congrArg (fun f : TorusValues D Q => (f (Multiplicative.ofAdd χ) : Q)) hr)

section Fibre

variable {D : BasedRootDatum.{u}} {F : Type u} [Field F]

private theorem forgetFibrePoint_injective (G : IntegralGroup.{u}) (S : TestAlgebra F) :
    Function.Injective (forgetFibrePoint G S) := by
  intro p q h
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact congrArg (fun f : IntegralPoints G (CommAlgCat.of Integers.{u} S) => f.left) h
  · exact (Over.w p).trans (Over.w q).symm

private theorem forgetFibrePoint_surjective (G : IntegralGroup.{u}) (S : TestAlgebra F) :
    Function.Surjective (forgetFibrePoint G S) := by
  intro p
  let U := (testSpec F).obj (op S)
  have hw : p.left ≫ G.X.hom =
      U.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} F)) := by
    rw [Over.w p]
    change Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} S)) =
      Spec.map (CommRingCat.ofHom (algebraMap F S)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} F))
    rw [← Spec.map_comp]
    congr 2
    ext x
    exact (map_intCast (algebraMap F S) x.down).symm
  refine ⟨Over.homMk (pullback.lift p.left U.hom hw) (pullback.lift_snd _ _ _), ?_⟩
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

private theorem forgetFibrePoint_comp {G H : IntegralGroup.{u}} (f : G ⟶ H)
    (S : TestAlgebra F) (p : GroupPoints ((fibre F).obj G) S) :
    forgetFibrePoint H S (p ≫ ((fibre F).map f).hom.hom) =
      forgetFibrePoint G S p ≫ f.hom.hom := by
  apply Over.OverMorphism.ext
  let g := Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} F))
  change (p.left ≫ ((Over.pullback g).map f.hom.hom).left) ≫ pullback.fst H.X.hom g =
    (p.left ≫ pullback.fst G.X.hom g) ≫ f.hom.hom.left
  simp only [Over.pullback_map_left, Category.assoc, pullback.lift_fst]

private theorem torusPoint_surjective (D : BasedRootDatum.{u}) (S : IntegralAlgebra.{u}) :
    Function.Surjective (torusPoint D S) := by
  intro p
  let A := MonoidAlgebra Integers.{u} (Multiplicative D.X)
  let C : IntegralAlgebra.{u} := @CommAlgCat.of Integers.{u} _ A _ MonoidAlgebra.algebra
  let FF := algSpec.fullyFaithful (R := CommRingCat.of Integers.{u})
  let f : C ⟶ S := (FF.preimage p).unop
  letI : Algebra Integers.{u} A := MonoidAlgebra.algebra
  letI : Algebra Integers.{u} S := S.algebra
  let m : Multiplicative D.X →* S :=
    f.hom.toMonoidHom.comp (MonoidAlgebra.of Integers.{u} (Multiplicative D.X))
  refine ⟨m.toHomUnits, ?_⟩
  have h : CommAlgCat.ofHom (MonoidAlgebra.lift Integers.{u} S _
        ((Units.coeHom S).comp m.toHomUnits)) = f := by
    apply CommAlgCat.hom_ext
    exact (MonoidAlgebra.lift_unique' f.hom).symm
  unfold torusPoint
  rw [h]
  exact FF.map_preimage p

private theorem characterValue_map {G : GroupScheme F} (χ : CharacterDescent.Character G)
    {S S' : TestAlgebra F} (f : S ⟶ S') (p : GroupPoints G S) :
    characterValue χ S' ((testSpec F).map f.op ≫ p) =
      f.hom (characterValue χ S p) := by
  let FF := algSpec.fullyFaithful (R := CommRingCat.of F)
  let x := p ≫ χ.hom.hom
  have h := FF.preimage_comp ((testSpec F).map f.op) x
  rw [FF.preimage_map] at h
  have hh : (((testSpec F).map f.op ≫ p) ≫ χ.hom.hom) =
      (testSpec F).map f.op ≫ x := Category.assoc _ _ _
  unfold characterValue
  dsimp only
  rw [hh]
  exact congrArg (fun f => f.unop.hom (MonoidAlgebra.single DiagonalizableGroups.integerGenerator 1)) h

private theorem characterValue_comp {G H : GroupScheme F} (χ : CharacterDescent.Character H)
    (f : G ⟶ H) (S : TestAlgebra F) (p : GroupPoints G S) :
    characterValue χ S (p ≫ f.hom.hom) = characterValue (f ≫ χ) S p := by
  have h : (p ≫ f.hom.hom) ≫ χ.hom.hom = p ≫ (f ≫ χ).hom.hom := Category.assoc _ _ _
  unfold characterValue
  dsimp only
  rw [h]

private def simpleFibreCharacter {M : Model D} (C : MarkedFibre M F)
    (b : Fin 6 ≃ D.base.support) (i : Fin 6) :
    CharacterDescent.Character C.realization.pinned.pair.T.group :=
  Additive.toMul (C.realization.datumIso.val.weightEquiv (simpleCharacter b i))

end Fibre

section PinnedAction

variable {D : BasedRootDatum.{u}} {M : Model D}
  {F L : Type u} [Field F] [Field L] [Algebra F L] (R : RamifiedReference F L M)
  (σ : Gal(L/F))

private theorem markedDiagram_index (i : D.I) :
    R.fibre.realization.datumIso.val.indexEquiv ((R.diagram σ).val.indexEquiv i) =
      (R.outer σ).asIso.hom.val.indexEquiv (R.fibre.realization.datumIso.val.indexEquiv i) := by
  let e := R.fibre.realization.datumIso.val.indexEquiv
  change e (e.symm ((R.outer σ).asIso.hom.val.indexEquiv (e i))) = _
  exact e.apply_symm_apply _

private theorem diagramCharacter (b : Fin 6 ≃ D.base.support)
    (hb : ∀ i, (R.diagram σ).val.indexEquiv (b i) = b (e6Partner i)) (i : Fin 6) :
    Additive.toMul ((R.outer σ).asIso.hom.val.weightEquiv
      (Additive.ofMul (simpleFibreCharacter R.fibre b i))) =
      simpleFibreCharacter R.fibre b (e6Partner i) := by
  apply Additive.toMul.injective
  let e := R.fibre.realization.datumIso.val
  let a := (R.outer σ).asIso.hom.val
  change a.weightEquiv (e.weightEquiv (D.datum.root (b i).val)) =
    e.weightEquiv (D.datum.root (b (e6Partner i)).val)
  have he (j : D.I) : e.weightEquiv (D.datum.root j) =
      R.fibre.realization.attached.toBased.datum.root (e.indexEquiv j) :=
    congrFun e.toHom.root_weightMap j
  have ha (j : R.fibre.realization.attached.toBased.I) :
      a.weightEquiv (R.fibre.realization.attached.toBased.datum.root j) =
        R.fibre.realization.attached.toBased.datum.root (a.indexEquiv j) :=
    congrFun a.toHom.root_weightMap j
  rw [he, ha, he]
  exact congrArg R.fibre.realization.attached.toBased.datum.root
    ((markedDiagram_index R σ (b i)).symm.trans (congrArg e.indexEquiv (hb i)))

private theorem pinnedCharacter_transport
    (χ : CharacterDescent.Character R.fibre.realization.pinned.pair.T.group) :
    (R.pin (R.outer σ)).asIso.hom.torus.inv ≫ χ =
      Additive.toMul ((R.outer σ).asIso.hom.val.weightEquiv (Additive.ofMul χ)) := by
  let P := R.fibre.realization.pinned
  let a := R.outer σ
  let δ := (R.pin a).asIso
  let U := P.pair.T.group.X
  let g := scalarAut (Functor.mapAut P (forgetPinning (A := R.fibre.line)) (R.pin a)) U
  let aligned : Aligned P g :=
    { torus := scalarAut (Aut.of δ.hom.torus) U
      borel := scalarAut (Aut.of δ.hom.borel) U
      torus_comm := by
        ext V t
        change (t ≫ P.pair.T.inclusion.hom.hom) ≫ δ.hom.group.hom.hom.hom =
          (t ≫ δ.hom.torus.hom.hom.hom) ≫ P.pair.T.inclusion.hom.hom
        simp only [Category.assoc]
        exact congrArg (fun f : P.pair.T.group ⟶ P.pair.G.val => t ≫ f.hom.hom) δ.hom.torus_comm
      borel_comm := by
        ext V t
        change (t ≫ P.pair.B.inclusion.hom.hom) ≫ δ.hom.group.hom.hom.hom =
          (t ≫ δ.hom.borel.hom.hom.hom) ≫ P.pair.B.inclusion.hom.hom
        simp only [Category.assoc]
        exact congrArg (fun f : P.pair.B.group ⟶ P.pair.G.val => t ≫ f.hom.hom) δ.hom.borel_comm }
  have hout : R.sequence.toExactSequence.outer.app (op U) g =
      ⟨LocallyConstant.const _ a⟩ := by
    let c : (AutomorphismSequence.constantGroup (Aut R.fibre.realization.attached.toBased)).obj
        (op U) := ⟨LocallyConstant.const _ a⟩
    calc
      _ = R.sequence.toExactSequence.outer.app (op U) (R.sequence.sectionMap.app (op U) c) :=
        congrArg (fun t => R.sequence.toExactSequence.outer.app (op U) t)
          (R.sequence.sectionOnConstants U a).symm
      _ = c := ConcreteCategory.congr_hom
        (congrArg (fun n => n.app (op U)) R.sequence.rightInverse) c
  -- This evaluates the same natural transformations on the object with torus as its domain.
  have h := (R.sequence.latticeAction U g aligned a hout).1 χ
    (Over.mk (𝟙 U)) (𝟙 U)
  apply Grp.hom_ext
  change δ.hom.torus.inv.hom.hom ≫ χ.hom.hom = _
  change ((𝟙 U ≫ δ.hom.torus.inv.hom.hom) ≫ χ.hom.hom) = 𝟙 U ≫ _ at h
  simp only [Category.id_comp] at h
  exact h

end PinnedAction

section Chart

variable {D : BasedRootDatum.{u}} {M : Model D}
  {F L k : Type u} [Field F] [Field L] [Field k] [Algebra F L] [Algebra F k]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (R : RamifiedReference F L M) (σ : Gal(L/F)) (T : DiagramCompositum F L k σ)
  {A : FoldedApartment (R.diagram σ)}
  (X : FoldedLevel R σ T.diagram (IsScalarTower.toAlgHom F L T.field) A)

private theorem fibreTorusCoordinates (p : GroupPoints R.fibre.realization.pinned.pair.T.group
    (CommAlgCat.of F T.field)) :
    ∃ t : TorusValues D (integralRing T.field),
      (∀ x : D.X, characterValue
          (Additive.toMul (R.fibre.realization.datumIso.val.weightEquiv x))
          (CommAlgCat.of F T.field) p = (t (Multiplicative.ofAdd x) : T.field)) ∧
      markedFibrePoint R.fibre (CommAlgCat.of F T.field)
        (p ≫ R.fibre.realization.pinned.pair.T.inclusion.hom.hom) = torusPointInModel M t := by
  let S := CommAlgCat.of F T.field
  let C := R.fibre
  let q := p ≫ C.torusIso.inv.hom.hom
  have hq : q ≫ C.torusIso.hom.hom.hom = p := by
    change p ≫ C.torusIso.inv.hom.hom ≫ C.torusIso.hom.hom.hom = p
    exact (congrArg (fun f => p ≫ f)
      (congrArg (fun (f : C.realization.pinned.pair.T.group ⟶ _) => f.hom.hom)
        C.torusIso.inv_hom_id)).trans (Category.comp_id p)
  obtain ⟨t, ht⟩ := torusPoint_surjective D (integralRing T.field) (forgetFibrePoint _ S q)
  refine ⟨t, fun x => ?_, ?_⟩
  · simpa only [hq] using C.torus_eval S q t ht.symm x
  · have hc : C.realization.pinned.pair.T.inclusion ≫ C.groupIso.inv =
        C.torusIso.inv ≫ (fibre F).map M.torus := by
      apply (cancel_epi C.torusIso.hom).mp
      rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← C.torus_comm,
        Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hc' := congrArg
      (fun f : C.realization.pinned.pair.T.group ⟶ (fibre F).obj M.group => f.hom.hom) hc
    change C.realization.pinned.pair.T.inclusion.hom.hom ≫ C.groupIso.inv.hom.hom =
      C.torusIso.inv.hom.hom ≫ ((fibre F).map M.torus).hom.hom at hc'
    change forgetFibrePoint M.group S
        ((p ≫ C.realization.pinned.pair.T.inclusion.hom.hom) ≫ C.groupIso.inv.hom.hom) =
      torusPoint D _ t ≫ M.torus.hom.hom
    simp only [Category.assoc] at hc' ⊢
    rw [hc', ← Category.assoc, forgetFibrePoint_comp]
    exact congrArg (fun f => f ≫ M.torus.hom.hom) ht.symm

private theorem torusPointInModel_range_iff (b : Fin 6 ≃ D.base.support)
    (B : Module.Basis (Fin 6) ℤ D.X) (hB : ∀ i, B i = simpleCharacter b i)
    (hb : ∀ i, (R.diagram σ).val.indexEquiv (b i) = b (e6Partner i))
    (t : TorusValues D (integralRing T.field)) :
    torusPointInModel M t ∈ X.points.range ↔
      ∀ i, simpleUnit b t (e6Partner i) =
        Units.map T.diagram.toRingHom.toMonoidHom (simpleUnit b t i) := by
  let S := CommAlgCat.of F T.field
  let C := R.fibre
  obtain ⟨s, hs⟩ := forgetFibrePoint_surjective (splitTorus D) S (torusPoint D _ t)
  let p := s ≫ C.torusIso.hom.hom.hom
  let j := C.realization.pinned.pair.T.inclusion
  let d := (R.pin (R.outer σ)).asIso.hom
  let f := CommAlgCat.ofHom (T.diagram.restrictScalars F).toAlgHom
  let q : GroupPoints C.realization.pinned.pair.T.group S :=
    (testSpec F).map f.op ≫ p ≫ d.torus.hom.hom.hom
  have hp (i : Fin 6) : characterValue (simpleFibreCharacter C b i) S p =
      (simpleUnit b t i : T.field) :=
    C.torus_eval S s t hs (simpleCharacter b i)
  have hq (i : Fin 6) : characterValue (simpleFibreCharacter C b (e6Partner i)) S q =
      T.diagram (simpleUnit b t i : T.field) := by
    have h := (pinnedCharacter_transport R σ (simpleFibreCharacter C b i)).trans
      (diagramCharacter R σ b hb i)
    have hc : d.torus.hom ≫ simpleFibreCharacter C b (e6Partner i) =
        simpleFibreCharacter C b i := by
      rw [← h, Iso.hom_inv_id_assoc]
    change characterValue _ S (((testSpec F).map f.op ≫ p) ≫ d.torus.hom.hom.hom) = _
    rw [characterValue_comp, hc, characterValue_map, hp]
    rfl
  obtain ⟨t', ht', hm'⟩ := fibreTorusCoordinates R σ T p
  have htt' : t' = t := torusValues_ext B fun i => by
    rw [hB]
    apply Units.ext
    exact (ht' (simpleCharacter b i)).symm.trans (hp i)
  rw [htt'] at hm'
  rw [← hm', X.fixed_points]
  change markedFibrePoint C S (((testSpec F).map f.op ≫ p ≫ j.hom.hom) ≫
    d.group.hom.hom.hom) = _ ↔ _
  have hd : j.hom.hom ≫ d.group.hom.hom.hom =
      d.torus.hom.hom.hom ≫ j.hom.hom :=
    congrArg (fun f : C.realization.pinned.pair.T.group ⟶ C.realization.pinned.pair.G.val =>
      f.hom.hom) d.torus_comm
  simp only [Category.assoc, hd]
  change markedFibrePoint C S (q ≫ j.hom.hom) = markedFibrePoint C S (p ≫ j.hom.hom) ↔ _
  have hj : IsClosedImmersion j.hom.hom.left := C.realization.pinned.pair.T.isClosedImmersion
  haveI : Mono j.hom.hom.left := by letI := hj; infer_instance
  haveI : Mono j.hom.hom := Over.mono_of_mono_left _
  have hEq : markedFibrePoint C S (q ≫ j.hom.hom) = markedFibrePoint C S (p ≫ j.hom.hom)
      ↔ q = p := by
    constructor
    · intro he
      apply (cancel_mono j.hom.hom).mp
      apply (cancel_mono C.groupIso.inv.hom.hom).mp
      exact forgetFibrePoint_injective M.group S he
    · exact fun he => congrArg (fun x => markedFibrePoint C S (x ≫ j.hom.hom)) he
  rw [hEq]
  constructor
  · intro he i
    apply Units.ext
    exact (hp (e6Partner i)).symm.trans ((he ▸ hq i))
  · intro he
    obtain ⟨t'', ht'', hm''⟩ := fibreTorusCoordinates R σ T q
    have hpp : Function.Involutive e6Partner := by
      intro i
      fin_cases i <;> rfl
    have ht : t'' = t := torusValues_ext B fun i => by
      rw [hB]
      apply Units.ext
      have h := hq (e6Partner i)
      rw [hpp i] at h
      refine (ht'' (simpleCharacter b i)).symm.trans (h.trans ?_)
      have hh := congrArg (fun x : T.fieldˣ => (x : T.field)) (he (e6Partner i))
      rw [hpp i] at hh
      exact hh.symm
    rw [ht] at hm''
    exact hEq.mp (hm''.trans hm'.symm)

private theorem rootValuePoint_zero (S : IntegralAlgebra.{u}) (l : List D.I) :
    rootValuePoint M.line S l 0 ≫ rootProduct M.line M.root l = 1 := by
  induction l with
  | nil =>
    rw [rootProduct, MonObj.comp_one]
  | cons i l ih =>
    rw [rootProduct, MonObj.comp_mul, ← Category.assoc, ← Category.assoc]
    simp only [rootValuePoint, lift_fst, lift_snd]
    have hz : Fin.tail (0 : Fin (l.length + 1) → S) = 0 := rfl
    rw [hz, ih, mul_one]
    change M.line.point S (0 : S) ≫ (M.root i).hom.hom = 1
    rw [← M.rankOneUpper]
    have h : IntegralRootRelations.upper (0 : S) = 1 := by
      apply Subtype.ext
      ext x y
      fin_cases x <;> fin_cases y <;> simp [IntegralRootRelations.upper]
    rw [h]
    exact map_one ((M.rankOne i).app S).hom

private theorem cellValue_torus (negative positive : List D.I)
    (t : TorusValues D (integralRing T.field)) :
    cellValue M.toIntegralMarking (integralRing T.field) negative positive (0, t, 0) =
      torusPointInModel M t := by
  rw [cellValue, cellMap, MonObj.comp_mul, ← Category.assoc, ← Category.assoc]
  simp only [cellValuePoint, lift_fst, lift_snd]
  rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, lift_fst, lift_snd,
    rootValuePoint_zero, rootValuePoint_zero, one_mul, mul_one]
  rfl

private theorem chartTorus_iff (t : TorusValues D (integralRing T.field)) :
    t ∈ X.comparison.chart.chart.torus ↔ torusPointInModel M t ∈ X.points.range := by
  let C := X.comparison.chart
  have h := C.rational (0, t, 0)
  rw [cellValue_torus (T := T)] at h
  constructor
  · intro ht
    exact h.mpr ⟨⟨t, ht⟩, fun _ => 0, by simp [RootSlots.coordinates, Pi.zero_def]⟩
  · intro ht
    obtain ⟨s, _, hs⟩ := h.mp ht
    have he : s.val = t := congrArg (fun z => z.2.1) hs
    exact he ▸ s.property

end Chart

section Quadratic

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K] (s : Gal(K/k))
  (hdeg : Module.finrank k K = 2) (hs : s ≠ 1)

include hdeg hs

private theorem quadraticGal_cases (g : Gal(K/k)) : g = 1 ∨ g = s := by
  have hcard : Nat.card (Gal(K/k)) = 2 := (IsGalois.card_aut_eq_finrank k K).trans hdeg
  obtain ⟨_, _, hu⟩ := (Nat.card_eq_two_iff' (1 : Gal(K/k))).mp hcard
  by_cases hg : g = 1
  · exact Or.inl hg
  · exact Or.inr ((hu g hg).trans (hu s hs).symm)

private theorem quadraticGal_square : s * s = 1 := by
  rcases quadraticGal_cases s hdeg hs (s * s) with h | h
  · exact h
  · exact (hs (mul_right_cancel (h.trans (one_mul s).symm))).elim

private theorem quadraticGal_involutive : Function.Involutive s := by
  intro x
  exact congrArg (fun g : Gal(K/k) => g x) (quadraticGal_square s hdeg hs)

private theorem quadratic_fixed (x : K) (hx : s x = x) : ∃ y : k, algebraMap k K y = x :=
  (IsGalois.mem_range_algebraMap_iff_fixed (F := k) x).mpr fun g => by
    rcases quadraticGal_cases s hdeg hs g with h | h
    · rw [h]
      rfl
    · rwa [h]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- In this ramified quadratic extension, logarithmic values from the base
are even. Trace and norm show that every odd value is preserved. Multiplying
by an element of value `exp (-1)` reduces the even values to the odd case. -/
private theorem diagram_preservesValuation
    (hram : ∀ x : k, normalizedValuation K (algebraMap k K x) =
      (normalizedValuation k x) ^ 2) (x : K) :
    normalizedValuation K (s x) = normalizedValuation K x := by
  let v := normalizedValuation K
  let logValue (x : K) := WithZero.log (v x)
  have heven (z : K) (hz : s z = z) : logValue z % 2 = 0 := by
    obtain ⟨a, rfl⟩ := quadratic_fixed s hdeg hs z hz
    change WithZero.log (normalizedValuation K (algebraMap k K a)) % 2 = 0
    rw [hram, WithZero.log_pow, nsmul_eq_mul]
    omega
  have hmul {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
      logValue (a * b) = logValue a + logValue b := by
    change WithZero.log (v (a * b)) = _
    rw [map_mul, WithZero.log_mul (by simpa) (by simpa)]
  have hi := quadraticGal_involutive s hdeg hs
  have hodd (z : K) (hz : z ≠ 0) (ho : logValue z % 2 = 1) : v (s z) = v z := by
    have hN : logValue (z * s z) % 2 = 0 := heven _ (by rw [map_mul, hi, mul_comm])
    have hT : logValue (z + s z) % 2 = 0 := heven _ (by rw [map_add, hi, add_comm])
    have hsz : logValue (s z) % 2 = 1 := by
      rw [hmul hz ((map_ne_zero s).mpr hz)] at hN
      omega
    have hne₁ : ¬v z < v (s z) := by
      intro h
      have he := congrArg WithZero.log (v.map_add_eq_of_lt_right h)
      change logValue (z + s z) = logValue (s z) at he
      omega
    have hne₂ : ¬v (s z) < v z := by
      intro h
      have he := congrArg WithZero.log (v.map_add_eq_of_lt_left h)
      change logValue (z + s z) = logValue z at he
      omega
    exact le_antisymm (le_of_not_gt hne₁) (le_of_not_gt hne₂)
  by_cases hx : x = 0
  · simp [hx]
  by_cases ho : logValue x % 2 = 1
  · exact hodd x hx ho
  have hv : Function.Surjective v :=
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).surjective.comp
      ValuativeRel.valuation_surjective
  obtain ⟨p, hp⟩ := hv (WithZero.exp (-1 : ℤ))
  have hp0 : p ≠ 0 := by
    intro h
    have hz : (0 : ℤᵐ⁰) = WithZero.exp (-1 : ℤ) := (v.map_zero.symm.trans (congrArg v h.symm)).trans hp
    exact WithZero.exp_ne_zero hz.symm
  have hpLog : logValue p = -1 := by
    change WithZero.log (v p) = -1
    rw [hp, WithZero.log_exp]
  have hsp : v (s p) = v p := hodd p hp0 (by omega)
  have hh := hodd (p * x) (mul_ne_zero hp0 hx) (by rw [hmul hp0 hx, hpLog]; omega)
  rw [map_mul, map_mul v, map_mul v, hsp] at hh
  exact mul_left_cancel₀ (by simpa using hp0 : v p ≠ 0) hh

end Quadratic

section UnitLifts

variable {E : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

private theorem normalizedValuation_eq_one_iff {x : E} :
    normalizedValuation E x = 1 ↔ ValuativeRel.valuation E x = 1 := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt E
  change e (ValuativeRel.valuation E x) = 1 ↔ _
  rw [← map_one e]
  exact e.injective.eq_iff

private theorem fieldUnit_value (a : (valuationRing E)ˣ) :
    normalizedValuation E (fieldUnit a : E) = 1 := by
  apply normalizedValuation_eq_one_iff.mpr
  exact (Valuation.valuationSubring.integers (ValuativeRel.valuation E)).valuation_unit a

private theorem fieldUnit_lift (a : Eˣ) (ha : normalizedValuation E (a : E) = 1) :
    ∃! b : (valuationRing E)ˣ, fieldUnit b = a := by
  let O := valuationRing E
  have hval : ValuativeRel.valuation E (a : E) = 1 := normalizedValuation_eq_one_iff.mp ha
  have hinv : ValuativeRel.valuation E (↑a⁻¹ : E) = 1 := by rw [Units.val_inv_eq_inv_val, map_inv₀, hval, inv_one]
  let b : Oˣ := ⟨⟨a, hval.le⟩, ⟨↑a⁻¹, hinv.le⟩,
    Subtype.ext a.val_inv, Subtype.ext a.inv_val⟩
  exact ⟨b, rfl, fun c hc => Units.map_injective O.subtype_injective hc⟩

end UnitLifts

section Orbits

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private theorem orbitValues_equivariant (s : Gal(K/k)) (hs : Function.Involutive s)
    (a c : kˣ) (p q : Kˣ) (i : Fin 6) :
    orbitValues s a c p q (e6Partner i) =
      Units.map s.toRingHom.toMonoidHom (orbitValues s a c p q i) := by
  apply Units.ext
  fin_cases i
  · rfl
  · exact (s.commutes (a : k)).symm
  · rfl
  · exact (s.commutes (c : k)).symm
  · exact (hs (q : K)).symm
  · exact (hs (p : K)).symm

private theorem orbitValues_integral [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (s : Gal(K/k))
    (hram : ∀ x : k, normalizedValuation K (algebraMap k K x) =
      (normalizedValuation k x) ^ 2)
    (hval : ∀ x, normalizedValuation K (s x) = normalizedValuation K x)
    (a c : (valuationRing k)ˣ) (p q : (valuationRing K)ˣ) (i : Fin 6) :
    normalizedValuation K (orbitValues s (fieldUnit a) (fieldUnit c) (fieldUnit p) (fieldUnit q) i
      : K) = 1 := by
  fin_cases i
  · exact fieldUnit_value p
  · change normalizedValuation K (algebraMap k K (fieldUnit a : k)) = 1
    rw [hram, fieldUnit_value, one_pow]
  · exact fieldUnit_value q
  · change normalizedValuation K (algebraMap k K (fieldUnit c : k)) = 1
    rw [hram, fieldUnit_value, one_pow]
  · change normalizedValuation K (s (fieldUnit q : K)) = 1
    exact (hval _).trans (fieldUnit_value q)
  · change normalizedValuation K (s (fieldUnit p : K)) = 1
    exact (hval _).trans (fieldUnit_value p)

private theorem singletonUnit [FiniteDimensional k K] [IsGalois k K]
    (s : Gal(K/k)) (hdeg : Module.finrank k K = 2) (hs : s ≠ 1)
    (x : Kˣ) (hx : s (x : K) = (x : K)) :
    ∃! a : kˣ, Units.map (algebraMap k K).toMonoidHom a = x := by
  obtain ⟨y, hy⟩ := quadratic_fixed s hdeg hs _ hx
  have hyn : y ≠ 0 := by
    intro h
    rw [h, map_zero] at hy
    exact x.ne_zero hy.symm
  exact ⟨Units.mk0 y hyn, Units.ext hy,
    fun a ha => Units.map_injective (algebraMap k K).injective (ha.trans (Units.ext hy).symm)⟩

end Orbits

/-- The ordered conditional derivation of the marked torus coordinate description. -/
theorem pinnedTorusCoordinates_conditional
    (_coxeterDoubleCosets : CoxeterDoubleCosets.{u, u, u})
    (_e6CoweightClass : E6CoweightClass)
    (_e6ProjectedLattices : E6ProjectedLattices)
    (_leftCosetIndex : LeftCosetIndex.{u})
    (_ramifiedAffineBruhat : RamifiedAffineBruhatComparison.{u})
    (_rankOneDoubleCosetProduct : RankOneDoubleCosetProduct.{u})
    (_rankOneWallConjugation : RankOneWallConjugation.{u})
    (_rankOneWallMultiplication : RankOneWallMultiplication.{u})
    (_residueLayerCounts : ResidueLayerCounts.{u})
    (_residuePowerCounts : ResiduePowerCounts.{u})
    (_splitAffineBruhat : SplitAffineBruhatComparison.{u})
    : PinnedTorusCoordinates.{u} := by
  intro D b h
  let B := simpleBasis D b h
  have hB (i : Fin 6) : B i = simpleCharacter b i := simpleBasis_apply D b h i
  have hex (S : IntegralAlgebra.{u}) (v : Fin 6 → Sˣ) :
      ∃! t : TorusValues D S, ∀ i, simpleUnit b t i = v i := by
    simpa only [hB, simpleUnit] using torusValuesOfBasis B S v
  refine ⟨⟨B, hB⟩, hex, ?_, ?_⟩
  · intro E _ _ _ _ n _ t I ht χ
    exact torusCongruence B I t (fun i => by simpa only [hB, simpleUnit] using ht i) χ
  · intro F L k _ _ _ _ _ _ _ _ _ _ _ M R σ T A X hb
    dsimp only
    have htor := torusPointInModel_range_iff R σ T X b B hB hb
    have hchart (t : TorusValues D (integralRing T.field)) :=
      (chartTorus_iff R σ T X t).trans (htor t)
    have hi := quadraticGal_involutive T.diagram T.degree T.diagram_ne
    refine ⟨htor, hchart, ?_, ?_, ?_⟩
    · intro t i hi'
      have hh := (hchart t.val).mp t.property i
      rw [hi'] at hh
      exact singletonUnit T.diagram T.degree T.diagram_ne _
        (congrArg (fun z : T.fieldˣ => (z : T.field)) hh.symm)
    · intro a c p q
      let v := orbitValues T.diagram a c p q
      obtain ⟨t, ht, hu⟩ := hex (integralRing T.field) v
      refine ⟨⟨t, (hchart t).mpr (fun i => ?_)⟩, ht, fun t' ht' => Subtype.ext (hu t'.val ht')⟩
      simpa only [ht] using orbitValues_equivariant T.diagram hi a c p q i
    · intro a c p q
      let v := orbitValues T.diagram (fieldUnit a) (fieldUnit c) (fieldUnit p) (fieldUnit q)
      obtain ⟨t, ht, hu⟩ := hex (integralRing T.field) v
      have hval := diagram_preservesValuation T.diagram T.degree T.diagram_ne X.ramification
      have hunit (i : Fin 6) : normalizedValuation T.field (v i : T.field) = 1 :=
        orbitValues_integral T.diagram X.ramification hval a c p q i
      choose w hw using fun i => (fieldUnit_lift (v i) (hunit i)).exists
      obtain ⟨s, hs, _⟩ := hex (integralRing (valuationRing T.field)) w
      have hst : fieldUnit.comp s = t := hu _ (fun i => by
        change fieldUnit (simpleUnit b s i) = v i
        rw [hs, hw])
      refine ⟨⟨t, (hchart t).mpr (fun i => ?_)⟩, ⟨ht, s, hst⟩,
        fun t' ht' => Subtype.ext (hu t'.val ht'.1)⟩
      simpa only [ht] using orbitValues_equivariant T.diagram hi (fieldUnit a) (fieldUnit c)
        (fieldUnit p) (fieldUnit q) i

end
end LinearAlgebraicGroups.Arithmetic.RamifiedCongruenceTorusCoordinates

universe v8_closure_d2d81186b7bd1798_u0
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«RamifiedCongruenceTorusCoordinates».«pinnedTorusCoordinates» : _root_.«LinearAlgebraicGroups».«Specs».«RamifiedCongruenceTorusCoordinates».«PinnedTorusCoordinates».{v8_closure_d2d81186b7bd1798_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«RamifiedCongruenceTorusCoordinates».«pinnedTorusCoordinates_conditional».{v8_closure_d2d81186b7bd1798_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«coxeterDoubleCosets».{v8_closure_d2d81186b7bd1798_u0, v8_closure_d2d81186b7bd1798_u0, v8_closure_d2d81186b7bd1798_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«e6CoweightQuotient») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«e6ProjectedLattices») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«leftCosetIndex».{v8_closure_d2d81186b7bd1798_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«ramifiedAffineBruhatComparison».{v8_closure_d2d81186b7bd1798_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneDoubleCosetProduct».{v8_closure_d2d81186b7bd1798_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneWallConjugation».{v8_closure_d2d81186b7bd1798_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneWallMultiplication».{v8_closure_d2d81186b7bd1798_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«residueLayerCounts».{v8_closure_d2d81186b7bd1798_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«residuePowerCounts».{v8_closure_d2d81186b7bd1798_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«splitAffineBruhatComparison».{v8_closure_d2d81186b7bd1798_u0})
