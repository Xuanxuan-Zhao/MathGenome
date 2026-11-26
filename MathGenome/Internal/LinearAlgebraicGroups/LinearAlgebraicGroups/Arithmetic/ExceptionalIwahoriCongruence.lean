import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.OpenCell
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

open AlgebraicGeometry CategoryTheory Opposite Topology
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj WithZero

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence

open Specs.ExceptionalIwahoriCongruence Specs.IntegralSemisimpleModel

universe u

theorem localChartLifting : LocalChartLifting := by
  intro R hR X Y c _ p
  constructor
  · rintro ⟨z, rfl, _⟩
    exact ⟨changeRing (residueHom R) z, Category.assoc _ _ _⟩
  · rintro ⟨z, hz⟩
    have hp : p.left (IsLocalRing.closedPoint R) ∈ Set.range c.left := by
      let k := IsLocalRing.ResidueField R
      let x := IsLocalRing.closedPoint k
      refine ⟨z.left x, ?_⟩
      have he := congrArg (fun f : Spec (CommRingCat.of k) ⟶ Y.left => f x)
        (congrArg Over.Hom.left hz)
      change c.left (z.left x) = p.left (PrimeSpectrum.comap (IsLocalRing.residue R) x) at he
      have hx := @IsLocalRing.PrimeSpectrum.comap_residue (↑R) _ hR x
      exact he.trans (congrArg (fun y : PrimeSpectrum R => p.left y) hx)
    have hs : Set.range p.left ⊆ Set.range c.left := by
      rintro _ ⟨x, rfl⟩
      exact ((@IsLocalRing.specializes_closedPoint (↑R) _ hR x).map p.left.continuous).mem_open
        c.left.isOpenEmbedding.isOpen_range hp
    let l := IsOpenImmersion.lift c.left p.left hs
    have hl : l ≫ c.left = p.left := IsOpenImmersion.lift_fac _ _ _
    let lOver : integralSpec.obj (op R) ⟶ X :=
      Over.homMk l (by rw [← Over.w c, ← Category.assoc, hl, Over.w p])
    have hlOver : lOver ≫ c = p := Over.OverMorphism.ext hl
    refine ⟨lOver, hlOver, fun w hw => ?_⟩
    apply Over.OverMorphism.ext
    apply (cancel_mono c.left).mp
    exact (congrArg Over.Hom.left hw).trans hl.symm

theorem chartCongruence : ChartCongruence := by
  intro R S f X Y c _ a b
  simp only [changeRing, ← Category.assoc]
  constructor
  · intro h
    apply Over.OverMorphism.ext
    apply (cancel_mono c.left).mp
    exact congrArg Over.Hom.left h
  · exact fun h => congrArg (fun p => p ≫ c) h

private theorem residuePowerCardinality (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)] (n : ℕ) :
    Nat.card (R ⧸ (IsLocalRing.maximalIdeal R) ^ n) =
      Nat.card (IsLocalRing.ResidueField R) ^ n := by
  let P := IsLocalRing.maximalIdeal R
  have hP : P ≠ ⊥ := by
    intro h
    exact IsDiscreteValuationRing.not_isField R
      (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)
  change Nat.card (R ⧸ P ^ n) = Nat.card (R ⧸ P) ^ n
  simpa only [Submodule.cardQuot_apply] using (cardQuot_pow_of_prime hP (i := n))

theorem truncatedLayerCardinality : TruncatedLayerCardinality := by
  intro R _ _ _ _ a b hab
  let P := IsLocalRing.maximalIdeal R
  let q := Nat.card (IsLocalRing.ResidueField R)
  change Nat.card (Submodule.map (P ^ b).mkQ (P ^ a)) = q ^ (b - a)
  have hle : P ^ b ≤ P ^ a := Ideal.pow_le_pow_right hab
  have h := Submodule.card_quotient_mul_card_quotient
    (P ^ a : Ideal R) (P ^ b : Ideal R) hle
  rw [residuePowerCardinality R a, residuePowerCardinality R b] at h
  change Nat.card (Submodule.map (P ^ b).mkQ (P ^ a)) * q ^ a = q ^ b at h
  apply Nat.eq_of_mul_eq_mul_right (show 0 < q ^ a from pow_pos Nat.card_pos a)
  rw [h, ← pow_add, Nat.sub_add_cancel hab]

theorem indexFromTruncatedChart : IndexFromTruncatedChart := by
  classical
  intro G J _ _ H N _ hNH R _ _ _ _ a b m hab hbm q hq hres T _ _ eG eH
  obtain ⟨eG⟩ := eG
  obtain ⟨eH⟩ := eH
  have cardLayers (c : J → ℕ) (hcm : c ≤ m) :
      Nat.card (∀ j, truncatedLayer (R j) (c j) (m j)) =
        q ^ ∑ j, (m j - c j) := by
    have hcount j : Nat.card (truncatedLayer (R j) (c j) (m j)) = q ^ (m j - c j) := by
      rw [truncatedLayerCardinality (R j) (c j) (m j) (hcm j), hres j]
    rw [Nat.card_pi, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro j _
    exact hcount j
  have cardG : N.index = Nat.card T * q ^ ∑ j, (m j - a j) := by
    rw [Subgroup.index_eq_card, Nat.card_congr eG, Nat.card_prod,
      cardLayers a (le_trans hab hbm)]
  have cardH : N.relIndex H = Nat.card T * q ^ ∑ j, (m j - b j) := by
    change Nat.card (H ⧸ N.comap H.subtype) = _
    rw [Nat.card_congr eH, Nat.card_prod, cardLayers b hbm]
  have hsum : (∑ j, (m j - a j)) = (∑ j, (m j - b j)) + ∑ j, (b j - a j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact (Nat.sub_add_sub_cancel (hbm j) (hab j)).symm
  apply Nat.eq_of_mul_eq_mul_left (show 0 < N.relIndex H by rw [cardH]; exact Nat.mul_pos Nat.card_pos (pow_pos hq _))
  rw [Subgroup.relIndex_mul_index hNH, cardG, cardH, hsum, pow_add, mul_assoc]

private theorem additivePoint_bijective (R : IntegralAlgebra.{u}) :
    Function.Bijective (additivePoint R) := by
  let e := (algSpec.fullyFaithful (R := CommRingCat.of Integers)).homEquiv
    (X := op R) (Y := op (CommAlgCat.of Integers (Polynomial Integers)))
  let f : R ≃ (op R ⟶ op (CommAlgCat.of Integers (Polynomial Integers))) :=
    (Polynomial.aevalEquiv Integers R).trans
      ((ConcreteCategory.homEquiv (X := CommAlgCat.of Integers (Polynomial Integers))
        (Y := R)).symm.trans Quiver.Hom.opEquiv)
  exact (f.trans e).bijective

private theorem torusPoint_bijective (D : Specs.Pinning.BasedRootDatum) (R : IntegralAlgebra) :
    Function.Bijective (torusPoint D R) := by
  let e := (algSpec.fullyFaithful (R := CommRingCat.of Integers)).homEquiv
    (X := op R) (Y := op (CommAlgCat.of Integers (MonoidAlgebra Integers (Multiplicative D.X))))
  let f : TorusValues D R ≃ (op R ⟶ op (CommAlgCat.of Integers
      (MonoidAlgebra Integers (Multiplicative D.X)))) :=
    MonoidHom.toHomUnitsMulEquiv.symm.toEquiv.trans
      ((MonoidAlgebra.lift Integers R (Multiplicative D.X)).trans
        ((ConcreteCategory.homEquiv (X := CommAlgCat.of Integers
          (MonoidAlgebra Integers (Multiplicative D.X))) (Y := R)).symm.trans Quiver.Hom.opEquiv))
  exact (f.trans e).bijective

private theorem rootValuePoint_bijective {I : Type u} (L : AdditiveLine.{u})
    (R : IntegralAlgebra.{u}) (l : List I) :
    Function.Bijective (rootValuePoint L R l) := by
  induction l with
  | nil =>
      exact ⟨fun _ _ _ => funext fun i => Fin.elim0 i, fun z =>
        ⟨Fin.elim0, isTerminalTensorUnit.hom_ext _ z⟩⟩
  | cons i l ih =>
      let e := (Fin.consEquiv (fun _ : Fin (l.length + 1) => R)).symm.trans
        (((Equiv.ofBijective (additivePoint R) (additivePoint_bijective R)).prodCongr
          (Equiv.ofBijective _ ih)).trans liftEquiv)
      exact e.bijective

private theorem cellValuePoint_bijective {D : Specs.Pinning.BasedRootDatum} (L : AdditiveLine)
    (R : IntegralAlgebra) (negative positive : List D.I) :
    Function.Bijective (cellValuePoint L R negative positive) := by
  let neg := Equiv.ofBijective _ (rootValuePoint_bijective L R negative)
  let pos := Equiv.ofBijective _ (rootValuePoint_bijective L R positive)
  let tor := Equiv.ofBijective _ (torusPoint_bijective D R)
  exact ((neg.prodCongr ((tor.prodCongr pos).trans liftEquiv)).trans liftEquiv).bijective


private theorem additivePoint_natural {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (x : R) :
    changeRing f (additivePoint R x) = additivePoint S (f.hom x) := by
  simp only [changeRing, additivePoint, ← Functor.map_comp, ← op_comp]
  congr 2
  apply CommAlgCat.hom_ext
  exact Polynomial.algHom_ext (by simp)

private theorem torusPoint_natural {D : Specs.Pinning.BasedRootDatum.{u}}
    {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (t : TorusValues D R) :
    changeRing f (torusPoint D R t) = torusPoint D S ((Units.map f.hom.toRingHom).comp t) := by
  let A := CommAlgCat.of Integers.{u} (MonoidAlgebra Integers.{u} (Multiplicative D.X))
  let gR : A ⟶ R := CommAlgCat.ofHom
    (MonoidAlgebra.lift Integers R (Multiplicative D.X) ((Units.coeHom R).comp t))
  let gS : A ⟶ S := CommAlgCat.ofHom
    (MonoidAlgebra.lift Integers S (Multiplicative D.X)
      ((Units.coeHom S).comp ((Units.map f.hom.toRingHom).comp t)))
  change integralSpec.map f.op ≫ integralSpec.map gR.op = integralSpec.map gS.op
  calc
    _ = integralSpec.map (gR ≫ f).op := (integralSpec.map_comp f.op gR.op).symm
    _ = _ := by
      congr 2
      apply CommAlgCat.hom_ext
      apply MonoidAlgebra.algHom_ext
      · intro a
        change f.hom ((MonoidAlgebra.lift _ _ _ _) (MonoidAlgebra.of _ _ a)) =
          (MonoidAlgebra.lift _ _ _ _) (MonoidAlgebra.of _ _ a)
        rw [MonoidAlgebra.lift_of, MonoidAlgebra.lift_of]
        rfl
      · exact Subsingleton.elim _ _

private theorem rootValuePoint_natural {I : Type u} (L : AdditiveLine.{u})
    {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (l : List I) (r : Fin l.length → R) :
    changeRing f (rootValuePoint L R l r) = rootValuePoint L S l (fun i => f.hom (r i)) := by
  induction l with
  | nil => exact isTerminalTensorUnit.hom_ext _ _
  | cons i l ih =>
      rw [rootValuePoint, rootValuePoint]
      change integralSpec.map f.op ≫ lift (additivePoint R (r 0))
        (rootValuePoint L R l (Fin.tail r)) = _
      rw [comp_lift]
      change lift (changeRing f (additivePoint R (r 0)))
        (changeRing f (rootValuePoint L R l (Fin.tail r))) = _
      rw [additivePoint_natural, ih]
      rfl

theorem markedChart : MarkedChart := by
  intro D M negative positive hn hp
  constructor
  · intro R a b h
    have := M.openCell negative positive hn hp
    apply (cellValuePoint_bijective M.line R negative positive).injective
    apply Over.OverMorphism.ext
    apply (cancel_mono (cellMap M.line M.torus M.root negative positive).left).mp
    exact congrArg Over.Hom.left h
  · intro R S f z
    simp only [cellValue, cellValuePoint, changeRing, ← Category.assoc, comp_lift]
    rw [← changeRing, rootValuePoint_natural, ← changeRing, torusPoint_natural,
      ← changeRing, rootValuePoint_natural]
    rfl

private theorem markedChart_of_reduction {D : Specs.Pinning.BasedRootDatum.{u}}
    (M : IntegralMarking D) (R : IntegralAlgebra.{u}) [IsLocalRing R]
    (negative positive : List D.I)
    (hn : Specs.OrderedRootProducts.Enumerates negative {i | ¬ D.base.IsPos i})
    (hp : Specs.OrderedRootProducts.Enumerates positive {i | D.base.IsPos i})
    (g : IntegralPoints M.group R) (w : CellValues D _ negative positive)
    (hw : changeRing (residueHom R) g = cellValue M _ negative positive w) :
    ∃ z : CellValues D R negative positive,
      cellValue M R negative positive z = g ∧ mapCellValues (residueHom R) z = w := by
  have := M.openCell negative positive hn hp
  obtain ⟨v, hv, _⟩ :=
    (localChartLifting R (cellMap M.line M.torus M.root negative positive) g).mpr
      ⟨cellValuePoint M.line _ negative positive w, hw.symm⟩
  obtain ⟨z, rfl⟩ := (cellValuePoint_bijective M.line R negative positive).surjective v
  change cellValue M R negative positive z = g at hv
  refine ⟨z, hv, (markedChart M negative positive hn hp).1 _ ?_⟩
  rw [← (markedChart M negative positive hn hp).2, hv, hw]

theorem markedBorelReductionChart : MarkedBorelReductionChart := by
  intro D M R hR negative positive hn hp g
  constructor
  · rintro ⟨t, y, hy⟩
    obtain ⟨z, hz, hred⟩ := markedChart_of_reduction M R negative positive hn hp g _ hy
    refine ⟨z, ⟨hz, fun i => ?_⟩, fun z' hz' => (markedChart M negative positive hn hp).1 R
      (hz'.1.trans hz.symm)⟩
    exact Ideal.Quotient.eq_zero_iff_mem.mp (congrArg (fun z => z.1 i) hred)
  · rintro ⟨z, ⟨hz, hneg⟩, _⟩
    refine ⟨(mapCellValues (residueHom R) z).2.1, (mapCellValues (residueHom R) z).2.2, ?_⟩
    rw [← hz, (markedChart M negative positive hn hp).2]
    congr 1
    exact Prod.ext (funext fun i => Ideal.Quotient.eq_zero_iff_mem.mpr (hneg i)) rfl

theorem markedTorusReductionChart : MarkedTorusReductionChart := by
  intro D M R hR negative positive hn hp g
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨z, hz, hred⟩ := markedChart_of_reduction M R negative positive hn hp g _ ht
    refine ⟨z, ⟨hz, fun i => ?_, fun i => ?_⟩, fun z' hz' =>
      (markedChart M negative positive hn hp).1 R (hz'.1.trans hz.symm)⟩
    · exact Ideal.Quotient.eq_zero_iff_mem.mp (congrArg (fun z => z.1 i) hred)
    · exact Ideal.Quotient.eq_zero_iff_mem.mp (congrArg (fun z => z.2.2 i) hred)
  · rintro ⟨z, ⟨hz, hneg, hpos⟩, _⟩
    refine ⟨(mapCellValues (residueHom R) z).2.1, ?_⟩
    rw [← hz, (markedChart M negative positive hn hp).2]
    congr 1
    exact Prod.ext (funext fun i => Ideal.Quotient.eq_zero_iff_mem.mpr (hneg i))
      (Prod.ext rfl (funext fun i => Ideal.Quotient.eq_zero_iff_mem.mpr (hpos i)))


private theorem rootWord_cons {D : Specs.Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (a : D.I) (l : List D.I) (z : Fin (a :: l).length → R) :
    rootValuePoint M.line R (a :: l) z ≫ rootProduct M.line M.root (a :: l) =
      (M.line.point R (z 0) ≫ (M.root a).hom.hom) *
        (rootValuePoint M.line R l (Fin.tail z) ≫ rootProduct M.line M.root l) := by
  rw [rootValuePoint, rootProduct]
  let P := product (fun _ : D.I => M.line.group.X) l
  change lift (M.line.point R (z 0)) (rootValuePoint M.line R l (Fin.tail z)) ≫
    ((fst M.line.group.X P ≫ (M.root a).hom.hom) *
      (snd M.line.group.X P ≫ rootProduct M.line M.root l)) = _
  rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc]
  exact congrArg₂ (· * ·)
    (congrArg (· ≫ (M.root a).hom.hom) (lift_fst (M.line.point R (z 0))
      (rootValuePoint M.line R l (Fin.tail z))))
    (congrArg (· ≫ rootProduct M.line M.root l) (lift_snd (M.line.point R (z 0))
      (rootValuePoint M.line R l (Fin.tail z))))

private theorem cellValue_eq_mul {D : Specs.Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (negative positive : List D.I)
    (z : CellValues D R negative positive) :
    cellValue M R negative positive z =
      (rootValuePoint M.line R negative z.1 ≫ rootProduct M.line M.root negative) *
        ((torusPoint D R z.2.1 ≫ M.torus.hom.hom) *
          (rootValuePoint M.line R positive z.2.2 ≫ rootProduct M.line M.root positive)) := by
  simp only [cellValue, cellValuePoint, cellMap, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]

private theorem scaleRootWord {D : Specs.Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (t : TorusValues D R)
    (l : List D.I) (z : Fin l.length → R) :
    MulAut.conj (torusPoint D R t ≫ M.torus.hom.hom)
      (rootValuePoint M.line R l z ≫ rootProduct M.line M.root l) =
    rootValuePoint M.line R l
      (fun j => (t (Multiplicative.ofAdd (D.datum.root l[j])) : R) * z j) ≫
        rootProduct M.line M.root l := by
  induction l with
  | nil => simp [rootProduct]
  | cons a l ih =>
      rw [rootWord_cons, rootWord_cons, map_mul]
      congr 1
      · exact M.conjugation R t a (z 0)
      · exact ih (Fin.tail z)

private theorem torus_commutes {D : Specs.Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (t s : TorusValues D R) :
    Commute (torusPoint D R t ≫ M.torus.hom.hom) (torusPoint D R s ≫ M.torus.hom.hom) := by
  let A := MonoidAlgebra Integers.{u} (Multiplicative D.X)
  let _ : Coalgebra.IsCocomm Integers.{u} A := by
    constructor
    ext x
    simp [A]
  have h : IsCommMonObj (splitTorus D).X :=
    isCommMonObj_spec_asOver_spec (R := CommRingCat.of Integers.{u}) (A := CommRingCat.of A)
  have hc := (isCommMonObj_iff_isMulCommutative (splitTorus D).X).mp h (integralSpec.obj (op R))
  let _ := hc
  show _ * _ = _ * _
  rw [← MonObj.mul_comp, ← MonObj.mul_comp]
  exact congrArg (fun p => p ≫ M.torus.hom.hom) (mul_comm' (torusPoint D R t) (torusPoint D R s))

theorem scaleMarkedChart : ScaleMarkedChart := by
  intro D M R negative positive t z
  rw [cellValue_eq_mul, cellValue_eq_mul, map_mul, map_mul,
    scaleRootWord, scaleRootWord]
  congr 2
  rw [MulAut.conj_apply, (torus_commutes M R t z.2.1).eq, mul_assoc, mul_inv_cancel, mul_one]
  rfl

private theorem chart_of_surjective_spec {R S : IntegralAlgebra.{u}} (f : R ⟶ S)
    (hf : Function.Surjective (integralSpec.map f.op).left)
    {X Y : IntegralScheme.{u}} (c : X ⟶ Y) [IsOpenImmersion c.left]
    (p : integralSpec.obj (op R) ⟶ Y)
    (v : integralSpec.obj (op S) ⟶ X) (hv : v ≫ c = changeRing f p) :
    ∃ w : integralSpec.obj (op R) ⟶ X, w ≫ c = p := by
  have hs : Set.range p.left ⊆ Set.range c.left := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := hf x
    exact ⟨v.left y, congrArg (fun g : Spec (CommRingCat.of S) ⟶ Y.left => g y)
      (congrArg Over.Hom.left hv)⟩
  let w := IsOpenImmersion.lift c.left p.left hs
  have hw : w ≫ c.left = p.left := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Over.homMk w (by rw [← Over.w c, ← Category.assoc, hw, Over.w p]), ?_⟩
  exact Over.OverMorphism.ext hw

theorem scaledTorusReduction : ScaledTorusReduction := by
  intro D M K E O hO f i hf negative positive hn hp t g
  have hchart := markedChart M negative positive hn hp
  have hred := markedTorusReductionChart M O negative positive hn hp
  have := M.openCell negative positive hn hp
  let T := torusPoint D E t ≫ M.torus.hom.hom
  constructor
  · rintro ⟨p, hp', hr⟩
    obtain ⟨w, ⟨hw, hn', hp''⟩, _⟩ := (hred p).mp hr
    have hs₁ : MulAut.conj T (changeRing f g) =
        cellValue M E negative positive (mapCellValues i w) := by
      rw [← hp', ← hw, hchart.2]
    obtain ⟨s, hs⟩ := (torusPoint_bijective D E).surjective ((torusPoint D E t)⁻¹)
    have hst : torusPoint D E s ≫ M.torus.hom.hom = T⁻¹ := by
      rw [hs]
      exact GrpObj.inv_comp _ _
    have hg : cellValue M E negative positive (scaleCellValues s (mapCellValues i w)) =
        changeRing f g := by
      rw [← scaleMarkedChart, hst, ← hs₁]
      simp [MulAut.conj_apply, mul_assoc]
    obtain ⟨v, hv⟩ :=
      chart_of_surjective_spec f hf (cellMap M.line M.torus M.root negative positive) g
        (cellValuePoint M.line E negative positive _) hg
    obtain ⟨z, rfl⟩ := (cellValuePoint_bijective M.line K negative positive).surjective v
    change cellValue M K negative positive z = g at hv
    refine ⟨z, ⟨hv, w, hchart.1 E ?_, hn', hp''⟩, ?_⟩
    · calc
        cellValue M E negative positive (mapCellValues i w) = MulAut.conj T (changeRing f g) :=
          hs₁.symm
        _ = MulAut.conj T (cellValue M E negative positive (mapCellValues f z)) :=
          congrArg (MulAut.conj T) ((congrArg (changeRing f) hv).symm.trans (hchart.2 f z))
        _ = _ := scaleMarkedChart M E negative positive t _
    · intro z' hz'
      exact hchart.1 K (hz'.1.trans hv.symm)
  · rintro ⟨z, ⟨hz, w, hw, hn', hp'⟩, _⟩
    refine ⟨cellValue M O negative positive w, ?_, (hred _).mpr ⟨w, ⟨rfl, hn', hp'⟩, ?_⟩⟩
    · calc
        changeRing i (cellValue M O negative positive w) =
            cellValue M E negative positive (mapCellValues i w) := hchart.2 i w
        _ = _ := by rw [hw, ← scaleMarkedChart, ← hchart.2 f z, hz]
    · intro w' hw'
      exact hchart.1 O hw'.1


theorem scaledReductionCovariance : ScaledReductionCovariance := by
  intro G E O k _ _ _ _ extend integral reduce T sx sy n r hr he
  have ht : ∀ z : O, z ∈ T.comap reduce ↔ MulAut.conj r z ∈ T.comap reduce := by
    intro z
    simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.mp hr (reduce z))
  have hs (z : E) : z ∈ (T.comap reduce).map integral ↔
      MulAut.conj (integral r) z ∈ (T.comap reduce).map integral := by
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨MulAut.conj r v, (ht v).mp hv, by simp [MulAut.conj_apply]⟩
    · rintro ⟨v, hv, heq⟩
      refine ⟨(MulAut.conj r).symm v, (ht _).mpr ?_, ?_⟩
      · rwa [MulEquiv.apply_symm_apply]
      · rw [MulAut.conj_symm_apply]
        simp only [map_mul, map_inv]
        rw [heq, MulAut.conj_apply]
        simp [mul_assoc]
  have hconj (g : G) :
      MulAut.conj sy (extend (MulAut.conj n g)) =
        MulAut.conj (integral r) (MulAut.conj sx (extend g)) := by
    rw [← he]
    simp [MulAut.conj_apply, mul_assoc]
  ext g
  constructor
  · rintro ⟨v, hv, rfl⟩
    change MulAut.conj sy (extend (MulAut.conj n v)) ∈ (T.comap reduce).map integral
    exact hconj v ▸ (hs _).mp hv
  · intro hg
    let v := (MulAut.conj n).symm g
    have hv : MulAut.conj n v = g := MulEquiv.apply_symm_apply _ _
    refine ⟨v, (hs _).mpr ?_, hv⟩
    change MulAut.conj (integral r) (MulAut.conj sx (extend v)) ∈ (T.comap reduce).map integral
    rw [← hconj, hv]
    exact hg

theorem thresholdIntersection : ThresholdIntersection := by
  intro G J T K Γ encode _ depth a b hinj
  ext g
  constructor
  · rintro ⟨⟨z, hz, hz'⟩, ⟨w, hw, hw'⟩⟩
    have hzw := hinj (hz'.trans hw'.symm)
    subst w
    exact ⟨z, fun j => max_le (hz j) (hw j), hz'⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, fun j => le_trans (le_max_left _ _) (hz j), rfl⟩,
      ⟨z, fun j => le_trans (le_max_right _ _) (hz j), rfl⟩⟩

theorem quotientFromTruncatedCoordinates : QuotientFromTruncatedCoordinates := by
  classical
  intro G Q T T' J _ _ K K' reduce chart truncT trunc hChart hTruncT hTrunc hEq
  let out (z : T × (∀ j, K j)) : T' × (∀ j, K' j) := (truncT z.1, fun j => trunc j (z.2 j))
  have hOut (z w) : reduce (chart z) = reduce (chart w) ↔ out z = out w := by
    rw [hEq, Prod.ext_iff]
    exact and_congr_right' funext_iff.symm
  let lift (g : G) := (hChart g).choose
  have hlift (g : G) : chart (lift g) = g := (hChart g).choose_spec
  let ψ (q : reduce.range) := out (lift q.property.choose)
  have hψ (g : G) (q : reduce.range) (h : reduce g = q.val) : ψ q = out (lift g) := by
    apply (hOut _ _).mp
    rw [hlift, hlift, q.property.choose_spec, h]
  refine ⟨(QuotientGroup.quotientKerEquivRange reduce).toEquiv.trans
    (Equiv.ofBijective ψ ⟨?_, ?_⟩)⟩
  · intro q q' h
    apply Subtype.ext
    have hq := (hOut _ _).mpr h
    rwa [hlift, hlift, q.property.choose_spec, q'.property.choose_spec] at hq
  · rintro ⟨t, x⟩
    obtain ⟨t₀, ht⟩ := hTruncT t
    choose x₀ hx using fun j => hTrunc j (x j)
    let z : T × (∀ j, K j) := (t₀, x₀)
    let q := reduce.rangeRestrict (chart z)
    refine ⟨q, (hψ (chart z) q rfl).trans ?_⟩
    have hLift : out (lift (chart z)) = out z := (hOut _ _).mp (by rw [hlift])
    exact hLift.trans (Prod.ext ht (funext hx))


private theorem maximalIdeal_pow_le_pow {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (a b : ℕ) :
    (IsLocalRing.maximalIdeal R) ^ a ≤ (IsLocalRing.maximalIdeal R) ^ b ↔ b ≤ a := by
  let e := IsDiscreteValuationRing.idealOrderIsoENat R
  rw [← IsDiscreteValuationRing.idealOrderIsoENat_symm_apply_coe R a,
    ← IsDiscreteValuationRing.idealOrderIsoENat_symm_apply_coe R b, e.symm.le_iff_le]
  exact ENat.natCast_le_natCast

theorem ramifiedTruncation : RamifiedTruncation := by
  intro R S _ _ _ _ _ _ f e n he hr
  ext x
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨j, u, hj⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  have hxR : Ideal.span {x} = (IsLocalRing.maximalIdeal R) ^ j := by
    rw [hj, Ideal.span_singleton_mul_left_unit u.isUnit, hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hxS : Ideal.span {f x} = (IsLocalRing.maximalIdeal S) ^ (e * j) := by
    rw [← Set.image_singleton, ← Ideal.map_span, hxR, Ideal.map_pow, hr, ← pow_mul]
  rw [Ideal.mem_comap, ← Ideal.span_singleton_le_iff_mem, hxS, maximalIdeal_pow_le_pow,
    ← Ideal.span_singleton_le_iff_mem, hxR, maximalIdeal_pow_le_pow,
    Nat.div_le_iff_le_mul he, Nat.mul_comm j e]
  omega


private theorem isClosedEmbedding_affinePoints {B A R : Type*} [CommRing B] [CommRing A]
    [CommRing R] [Algebra B A] [Algebra B R] [TopologicalSpace R] [T2Space R]
    [IsTopologicalRing R] :
    let := affinePointTopology B A R
    IsClosedEmbedding (fun f : A →ₐ[B] R => (f : A → R)) := by
  let := affinePointTopology B A R
  refine ⟨⟨⟨rfl⟩, DFunLike.coe_injective⟩, ?_⟩
  rw [show Set.range (fun f : A →ₐ[B] R => (f : A → R)) =
    (⋂ a : A, ⋂ b : A, {f : A → R | f (a + b) = f a + f b}) ∩
    (⋂ a : A, ⋂ b : A, {f : A → R | f (a * b) = f a * f b}) ∩
    (⋂ b : B, {f : A → R | f (algebraMap B A b) = algebraMap B R b}) by
    ext f
    simp only [Set.mem_range, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨⟨p.map_add, p.map_mul⟩, p.commutes⟩
    · rintro ⟨⟨ha, hm⟩, hB⟩
      exact ⟨{ toFun := f
               map_zero' := by simpa using hB 0
               map_one' := by simpa using hB 1
               map_add' := ha
               map_mul' := hm
               commutes' := hB }, rfl⟩]
  exact ((isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_eq (continuous_apply (a + b)) ((continuous_apply a).add (continuous_apply b))).inter
    (isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_eq (continuous_apply (a * b)) ((continuous_apply a).mul (continuous_apply b)))).inter
    (isClosed_iInter fun b => isClosed_eq (continuous_apply (algebraMap B A b)) continuous_const)

theorem compactOpenAffineReduction : CompactOpenAffineReduction := by
  classical
  intro B A K k _ _ _ _ _ _ _ hA _ _ _ _ _ R hRc hRo red hred C
  let := affinePointTopology B A K
  let := affinePointTopology B A R
  let addIntegral (p : A →ₐ[B] R) := R.val.comp p
  have hEvalR (a : A) : Continuous (fun f : A →ₐ[B] R => f a) :=
    (continuous_apply a).comp continuous_induced_dom
  have hEvalK (a : A) : Continuous (fun f : A →ₐ[B] K => f a) :=
    (continuous_apply a).comp continuous_induced_dom
  have hRcont : Continuous addIntegral :=
    continuous_induced_rng.mpr (continuous_pi fun a => continuous_subtype_val.comp (hEvalR a))
  let _ : T2Space (A →ₐ[B] K) :=
    (show IsEmbedding (fun f : A →ₐ[B] K => (f : A → K)) from
      ⟨⟨rfl⟩, DFunLike.coe_injective⟩).t2Space
  let _ : CompactSpace R := isCompact_iff_compactSpace.mp hRc
  let _ : IsTopologicalRing R := inferInstanceAs (IsTopologicalRing R.toSubring)
  let _ : CompactSpace (A →ₐ[B] R) := (isClosedEmbedding_affinePoints (B := B) (A := A)).compactSpace
  obtain ⟨gens, hgens⟩ := hA.out
  have hRange : Set.range addIntegral = ⋂ a ∈ gens, {p : A →ₐ[B] K | p a ∈ R} := by
    ext p
    simp only [Set.mem_range, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨p, rfl⟩ a _
      exact (p a).prop
    · intro hp
      have hp' : ∀ a, p a ∈ R := fun a => by
        have hsub : Algebra.adjoin B (↑gens : Set A) ≤ R.comap p :=
          Algebra.adjoin_le (fun a ha => hp a ha)
        exact hsub (by rw [hgens]; trivial)
      exact ⟨p.codRestrict R hp', rfl⟩
  have hOpenRange : IsOpen (Set.range addIntegral) := by
    rw [hRange]
    exact isOpen_biInter_finset fun a _ => hRo.preimage (hEvalK a)
  have hInj : Function.Injective addIntegral := by
    intro p q h
    ext a
    exact congrArg (fun f : A →ₐ[B] K => f a) h
  let hEmb : IsOpenEmbedding addIntegral := ⟨(hRcont.isClosedEmbedding hInj).isEmbedding, hOpenRange⟩
  have hFiber (q : A →ₐ[B] k) : IsOpen {p : A →ₐ[B] R | red.comp p = q} := by
    rw [show {p : A →ₐ[B] R | red.comp p = q} =
        ⋂ a ∈ gens, (fun p : A →ₐ[B] R => red (p a)) ⁻¹' {q a} by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h a _ => congrArg (fun f : A →ₐ[B] k => f a) h,
        fun h => AlgHom.ext_of_adjoin_eq_top hgens (fun a ha => h a ha)⟩]
    exact isOpen_biInter_finset fun a _ => (isOpen_discrete _).preimage (hred.comp (hEvalR a))
  have hOpen (U : Set (A →ₐ[B] k)) : IsOpen {p : A →ₐ[B] R | red.comp p ∈ U} := by
    rw [show {p : A →ₐ[B] R | red.comp p ∈ U} =
        ⋃ q ∈ U, {p : A →ₐ[B] R | red.comp p = q} by ext; simp]
    exact isOpen_biUnion fun q _ => hFiber q
  let I := addIntegral '' {p | red.comp p ∈ C}
  have hIcompact : IsCompact I :=
    ((show IsClosed {p : A →ₐ[B] R | red.comp p ∈ C} from isOpen_compl_iff.mp (hOpen Cᶜ)).isCompact).image hRcont
  have hIopen : IsOpen I := hEmb.isOpenMap _ (hOpen C)
  refine ⟨hIcompact, hIopen, fun σ hσ => ?_⟩
  have hF := isClosed_eq hσ continuous_id
  exact ⟨hF.isClosedEmbedding_subtypeVal.isCompact_preimage hIcompact,
    hIopen.preimage continuous_subtype_val⟩


theorem finiteScalingExtension : FiniteScalingExtension := by
  intro K _ _ _ _ π d hd
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) (π : K)) hd
  let E := IntermediateField.adjoin K {z}
  let _ : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
  obtain ⟨v, τ, h⟩ := finiteExtension_localField (K := K) (L := E)
  let zE : E := ⟨z, IntermediateField.subset_adjoin K {z} rfl⟩
  have hzE : zE ^ d = algebraMap K E (π : K) := Subtype.ext hz
  have hn : zE ≠ 0 := by
    intro hz0
    rw [hz0, zero_pow hd.ne'] at hzE
    exact Units.ne_zero π ((algebraMap K E).injective (by simpa using hzE.symm))
  exact ⟨E, inferInstance, v, τ, h.1, h.2.1, Units.mk0 zE hn, hzE⟩

theorem valuedScaledChart : ValuedScaledChart := by
  intro D M K E Γ _ _ _ f v negative positive hn hp y ξ g
  let O := v.valuationSubring
  let R := integralRing O
  let i := integralRingMap O.subtype
  let t := cocharacter D y (integralRing E) ξ
  let e := integralRingMap f
  have he : Function.Surjective (integralSpec.map e.op).left := by
    intro x
    change PrimeSpectrum (integralRing K) at x
    exact ⟨(default : PrimeSpectrum E), Subsingleton.elim _ x⟩
  have hc := markedChart M negative positive hn hp
  have hs := scaledTorusReduction M (integralRing K) (integralRing E) R e i he
    negative positive hn hp t g
  refine hs.trans ?_
  constructor
  · rintro ⟨z, ⟨hz, w, hw, hn', hp'⟩, _⟩
    refine ⟨z, ⟨hz, ?_, ?_, ?_⟩, fun z' hz' => hc.1 _ (hz'.1.trans hz.symm)⟩
    · intro χ
      have hχ := congrArg (fun s : CellValues D (integralRing E) negative positive =>
        s.2.1 χ) hw
      change Units.map O.subtype (w.2.1 χ) = Units.map f.toMonoidHom (z.2.1 χ) at hχ
      rw [← show ((Units.map f.toMonoidHom (z.2.1 χ) : Eˣ) : E) = f (z.2.1 χ : K) from rfl, ← hχ]
      exact (Valuation.mem_unitGroup_iff (v := v) (x := _)).mp (O.unitGroupMulEquiv.symm (w.2.1 χ)).property
    · intro j
      have h := congrArg (fun s : CellValues D (integralRing E) negative positive => s.1 j) hw
      change ((w.1 j : O) : E) =
        (↑(ξ ^ D.datum.toLinearMap (D.datum.root negative[j]) y) : E) * f (z.1 j) at h
      rw [← h]
      exact v.mem_maximalIdeal_iff.mp (hn' j)
    · intro j
      have h := congrArg (fun s : CellValues D (integralRing E) negative positive => s.2.2 j) hw
      change ((w.2.2 j : O) : E) =
        (↑(ξ ^ D.datum.toLinearMap (D.datum.root positive[j]) y) : E) * f (z.2.2 j) at h
      rw [← h]
      exact v.mem_maximalIdeal_iff.mp (hp' j)
  · rintro ⟨z, ⟨hz, ht, hn', hp'⟩, _⟩
    let s := scaleCellValues t (mapCellValues e z)
    let hUnit : Multiplicative D.X →* O.unitGroup :=
      s.2.1.codRestrict O.unitGroup (fun χ => (Valuation.mem_unitGroup_iff (v := v) (x := _)).mpr (ht χ))
    let w : CellValues D R negative positive :=
      (fun j => ⟨s.1 j, (hn' j).le⟩, O.unitGroupMulEquiv.toMonoidHom.comp hUnit,
        fun j => ⟨s.2.2 j, (hp' j).le⟩)
    refine ⟨z, ⟨hz, w, ?_, fun j => v.mem_maximalIdeal_iff.mpr (hn' j),
      fun j => v.mem_maximalIdeal_iff.mpr (hp' j)⟩, fun z' hz' => hc.1 _ (hz'.1.trans hz.symm)⟩
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    exact MonoidHom.ext fun χ => Units.ext (O.coe_unitGroupMulEquiv_apply (hUnit χ))


private theorem mapCellValues_injective {D : Specs.Pinning.BasedRootDatum.{u}}
    {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (hf : Function.Injective f.hom)
    (negative positive : List D.I) :
    Function.Injective (mapCellValues (D := D) (negative := negative) (positive := positive) f) := by
  intro z w h
  refine Prod.ext (funext fun j => hf (congrArg (fun c => c.1 j) h))
    (Prod.ext ?_ (funext fun j => hf (congrArg (fun c => c.2.2 j) h)))
  exact MonoidHom.ext fun χ => Units.ext (hf (congrArg (fun c => (c.2.1 χ : S)) h))

theorem iwahoriChart : IwahoriChart := by
  intro D M R K hR i hi B H negative positive hn hp hB g
  have hchart := markedChart M negative positive hn hp
  have hinj : Function.Injective (fun z : CellValues D R negative positive =>
      changeRing i (cellValue M R negative positive z)) := by
    intro z w h
    change changeRing i (cellValue M R negative positive z) =
      changeRing i (cellValue M R negative positive w) at h
    rw [hchart.2, hchart.2] at h
    exact mapCellValues_injective i hi _ _ (hchart.1 K h)
  have hcriteria (g : H) :
      g ∈ iwahoriSubgroup i B H ↔
        ∃! z : CellValues D R negative positive,
          changeRing i (cellValue M R negative positive z) = (g : IntegralPoints M.group K) ∧
          ∀ j, z.1 j ∈ IsLocalRing.maximalIdeal R := by
    constructor
    · rintro ⟨p, hmem, heq⟩
      change changeRing (residueHom R) p ∈ (B : Set _) at hmem
      rw [hB] at hmem
      obtain ⟨⟨t, x⟩, htx⟩ := hmem
      obtain ⟨z, ⟨hz, hneg⟩, _⟩ :=
        (markedBorelReductionChart M R negative positive hn hp p).mp ⟨t, x, htx.symm⟩
      have hg : changeRing i (cellValue M R negative positive z) = (g : IntegralPoints M.group K) :=
        (congrArg (changeRing i) hz).trans heq
      exact ⟨z, ⟨hg, hneg⟩, fun z' hz' => hinj (hz'.1.trans hg.symm)⟩
    · rintro ⟨z, ⟨hz, hneg⟩, _⟩
      refine ⟨cellValue M R negative positive z, ?_, hz⟩
      change changeRing (residueHom R) (cellValue M R negative positive z) ∈ (B : Set _)
      rw [hB]
      obtain ⟨t, x, htx⟩ :=
        (markedBorelReductionChart M R negative positive hn hp _).mpr
          ⟨z, ⟨rfl, hneg⟩, fun z' hz' => hchart.1 R hz'.1⟩
      exact ⟨(t, x), htx.symm⟩
  refine ⟨hcriteria g, ?_⟩
  rw [← (iwahoriSubgroup i B H).inv_mem_iff, hcriteria g⁻¹]
  apply existsUnique_congr
  intro z
  exact and_congr_left' inv_eq_iff_eq_inv.symm

theorem positiveFirstWord : PositiveFirstWord := by
  intro D M R negative positive z
  rw [cellValue_eq_mul, mul_inv_rev, mul_inv_rev, mul_assoc]


private theorem truncateLayer_surjective (R : Type*) [CommRing R] [IsLocalRing R] (a m : ℕ) :
    Function.Surjective (truncateLayer R a m) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

theorem indexByIndependentCongruence : IndexByIndependentCongruence := by
  intro G Q T T' J _ _ _ _ _ reduce I H hHI R _ _ _ _ a b m hab hbm q hq hres
    chart truncateT ht₁ hOne hI hH hEq
  let f := reduce.comp I.subtype
  let N := f.ker
  let H' := H.subgroupOf I
  have hNH' : N ≤ H' := by
    rintro ⟨g, hg⟩ hgf
    obtain ⟨t, x, hx⟩ := (hI g).mp hg
    obtain ⟨t₀, ht₀⟩ := hOne
    have h0 : reduce (chart (t, fun j => (x j : R j))) = reduce (chart (t₀, 0)) := by
      rw [hx, ht₀, map_one]
      exact hgf
    have hdepth j : (x j : R j) ∈ (IsLocalRing.maximalIdeal (R j)) ^ m j := by
      have heq := ((hEq _ _).mp h0).2 j
      change Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (R j)) ^ m j) (x j : R j) =
        Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (R j)) ^ m j) 0 at heq
      rw [map_zero] at heq
      exact Ideal.Quotient.eq_zero_iff_mem.mp heq
    exact (hH g).mpr ⟨t, fun j => ⟨x j, Ideal.pow_le_pow_right (hbm j) (hdepth j)⟩, hx⟩
  let encodeI (z : T × (∀ j, integralLayer (R j) (a j))) : I :=
    ⟨chart (z.1, fun j => z.2 j), (hI _).mpr ⟨z.1, z.2, rfl⟩⟩
  let encodeH (z : T × (∀ j, integralLayer (R j) (b j))) : H' :=
    ⟨⟨chart (z.1, fun j => z.2 j), hHI ((hH _).mpr ⟨z.1, z.2, rfl⟩)⟩,
      (hH _).mpr ⟨z.1, z.2, rfl⟩⟩
  have hEqI (z w : T × (∀ j, integralLayer (R j) (a j))) :
      f (encodeI z) = f (encodeI w) ↔ truncateT z.1 = truncateT w.1 ∧
        ∀ j, truncateLayer (R j) (a j) (m j) (z.2 j) =
          truncateLayer (R j) (a j) (m j) (w.2 j) := by
    exact (hEq _ _).trans (and_congr_right'
      (forall_congr' fun _ => ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩))
  have hEqH (z w : T × (∀ j, integralLayer (R j) (b j))) :
      (f.comp H'.subtype) (encodeH z) = (f.comp H'.subtype) (encodeH w) ↔
        truncateT z.1 = truncateT w.1 ∧
          ∀ j, truncateLayer (R j) (b j) (m j) (z.2 j) =
            truncateLayer (R j) (b j) (m j) (w.2 j) := by
    exact (hEq _ _).trans (and_congr_right'
      (forall_congr' fun _ => ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩))
  have eqI := quotientFromTruncatedCoordinates f encodeI truncateT
    (fun j => truncateLayer (R j) (a j) (m j))
    (fun g => by
      obtain ⟨t, x, hx⟩ := (hI g).mp g.prop
      exact ⟨(t, x), Subtype.ext hx⟩) ht₁ (fun j => truncateLayer_surjective (R j) (a j) (m j)) hEqI
  have eqH := quotientFromTruncatedCoordinates (f.comp H'.subtype) encodeH truncateT
    (fun j => truncateLayer (R j) (b j) (m j))
    (fun g => by
      obtain ⟨t, x, hx⟩ := (hH g.val).mp g.prop
      exact ⟨(t, x), Subtype.ext (Subtype.ext hx)⟩) ht₁
    (fun j => truncateLayer_surjective (R j) (b j) (m j)) hEqH
  exact ⟨hNH', indexFromTruncatedChart H' N hNH' R a b m hab hbm q hq hres T' eqI eqH⟩


private theorem finite_monoidHom_of_fg {A B : Type*} [Group A] [Monoid B]
    [Group.FG A] [Finite B] : Finite (A →* B) := by
  obtain ⟨s, hs, hf⟩ := Group.fg_iff.mp (inferInstance : Group.FG A)
  let _ : Finite s := hf
  exact Finite.of_injective (fun f : A →* B => fun x : s => f x) fun f g h =>
    MonoidHom.eq_of_eqOn_dense hs (fun x hx => congrFun h ⟨x, hx⟩)

private theorem quotient_eq_of_ramification {A R : Type*} [CommRing A] [CommRing R]
    [IsLocalRing A] [IsLocalRing R] (f : A →+* R) (n m : ℕ)
    (hf : Ideal.comap f (IsLocalRing.maximalIdeal R ^ n) = IsLocalRing.maximalIdeal A ^ m)
    (x y : A) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ n) (f x) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ n) (f y) ↔
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ m) x =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ m) y := by
  rw [← sub_eq_zero, ← map_sub, ← map_sub, Ideal.Quotient.eq_zero_iff_mem,
    ← Ideal.mem_comap, hf, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]

theorem markedCongruenceIndex : MarkedCongruenceIndex := by
  classical
  intro D M R _ _ _ negative positive hn hp J _ P _ _ _ _ neg pos embedNeg embedPos
    hOrbits e he hNeg hPos T _ chart I H hHI a b hab q hq hres hOne hI hH
  let n := 1 + ∑ j, b j * e j
  let m (j : J) := (n + e j - 1) / e j
  have hbm : b ≤ m := by
    intro j
    have hsum : b j * e j ≤ ∑ l, b l * e l :=
      Finset.single_le_sum (f := fun j => b j * e j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    apply (Nat.le_div_iff_mul_le (he j)).mpr
    dsimp [m, n]
    omega
  let S := congruenceRing R n
  let f := congruenceHom R n
  let red := changeRingHom M.group f
  let truncateT (t : T) : TorusValues D S := (Units.map f.hom.toRingHom).comp t.val
  let tr (t : T) : Set.range truncateT := ⟨truncateT t, t, rfl⟩
  have hTr : Function.Surjective tr := fun ⟨_, ⟨t, ht⟩⟩ => ⟨t, Subtype.ext ht⟩
  let _ : Finite S := Nat.finite_of_card_ne_zero (by
    change Nat.card (R ⧸ (IsLocalRing.maximalIdeal R) ^ n) ≠ 0
    rw [residuePowerCardinality]
    exact pow_ne_zero _ (Nat.ne_of_gt Nat.card_pos))
  let _ : Group.FG (Multiplicative D.X) :=
    GroupFG.iff_add_fg.mpr (Module.Finite.iff_addGroup_fg.mp D.finiteX)
  let _ : Finite (TorusValues D S) := finite_monoidHom_of_fg
  let _ : Nonempty (Set.range truncateT) := ⟨tr (Classical.arbitrary T)⟩
  have hchart := markedChart M negative positive hn hp
  have hEq (z w : T × (∀ j, P j)) :
      red (chart z) = red (chart w) ↔ tr z.1 = tr w.1 ∧
        ∀ j, Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (P j)) ^ m j) (z.2 j) =
          Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (P j)) ^ m j) (w.2 j) := by
    let coords (v : T × (∀ j, P j)) : CellValues D R negative positive :=
      (fun i => embedNeg i (v.2 (neg i)), v.1.val, fun i => embedPos i (v.2 (pos i)))
    change changeRing f (cellValue M R negative positive (coords z)) =
      changeRing f (cellValue M R negative positive (coords w)) ↔ _
    rw [hchart.2, hchart.2, (hchart.1 S).eq_iff]
    have hneg (i) := quotient_eq_of_ramification (embedNeg i) n (m (neg i))
      (ramifiedTruncation (embedNeg i) (e (neg i)) n (he (neg i)) (hNeg i)) (z.2 _) (w.2 _)
    have hpos (i) := quotient_eq_of_ramification (embedPos i) n (m (pos i))
      (ramifiedTruncation (embedPos i) (e (pos i)) n (he (pos i)) (hPos i)) (z.2 _) (w.2 _)
    constructor
    · intro h
      refine ⟨Subtype.ext (congrArg (fun v => v.2.1) h), fun j => ?_⟩
      rcases hOrbits j with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · exact (hneg i).mp (congrArg (fun v => v.1 i) h)
      · exact (hpos i).mp (congrArg (fun v => v.2.2 i) h)
    · rintro ⟨ht, hr⟩
      exact Prod.ext (funext fun i => (hneg i).mpr (hr (neg i)))
        (Prod.ext (congrArg Subtype.val ht) (funext fun i => (hpos i).mpr (hr (pos i))))
  obtain ⟨hKernel, hIndex⟩ :=
    indexByIndependentCongruence red I H hHI P a b m hab hbm q hq hres chart tr
      hTr hOne hI hH hEq
  exact ⟨n, by dsimp [n]; omega, hKernel, hIndex⟩


theorem integralAffinePresentation : IntegralAffinePresentation.{u} := by
  intro D M
  have := M.affine
  have := M.locallyOfFinitePresentation
  let X := M.group.X.left
  let e : X ≅ Spec (Scheme.Γ.obj (op X)) := X.isoSpec
  let φ := Spec.preimage (e.inv ≫ M.group.X.hom)
  let : Algebra Integers.{u} (Scheme.Γ.obj (op X)) := φ.hom.toAlgebra
  let A := CommAlgCat.of Integers.{u} (Scheme.Γ.obj (op X))
  have hφ : Spec.map φ = e.inv ≫ M.group.X.hom := Spec.map_preimage _
  have hfp : LocallyOfFinitePresentation (Spec.map φ) := hφ ▸
    (inferInstance : LocallyOfFinitePresentation (e.inv ≫ M.group.X.hom))
  have hft : Algebra.FiniteType Integers.{u} A :=
    RingHom.FiniteType.of_finitePresentation ((LocallyOfFinitePresentation.SpecMap_iff φ).mp hfp)
  exact ⟨A, hft, ⟨Over.isoMk e.symm hφ.symm⟩⟩

private theorem pointAlgebraEquiv_natural (A : IntegralAlgebra.{u}) {X : IntegralScheme.{u}}
    (iso : integralSpec.obj (op A) ≅ X) {R S : IntegralAlgebra.{u}}
    (f : R ⟶ S) (p : A →ₐ[Integers.{u}] R) :
    changeRing f (pointAlgebraEquiv A iso R p) =
      pointAlgebraEquiv A iso S (f.hom.comp p) := by
  change integralSpec.map f.op ≫ integralSpec.map (CommAlgCat.ofHom p).op ≫ iso.hom =
    integralSpec.map (CommAlgCat.ofHom (f.hom.comp p)).op ≫ iso.hom
  rw [← Category.assoc, ← integralSpec.map_comp, ← op_comp]
  rfl

theorem compactOpenLocalModel : CompactOpenLocalModel.{u} := by
  classical
  intro D M A hA iso K _ _ _ _ B
  let := markedPointTopology A iso K
  let := integerAlgebra K
  let O := localIntegers K
  let k : IntegralAlgebra.{u} := CommAlgCat.of Integers.{u} (IsLocalRing.ResidueField O)
  let : TopologicalSpace (IsLocalRing.ResidueField O) := ⊥
  let : DiscreteTopology (IsLocalRing.ResidueField O) := ⟨rfl⟩
  let R := localIntegersAlgebra K
  let _ : IsTopologicalRing R := inferInstanceAs (IsTopologicalRing R.toSubring)
  let f := residueHom O
  let i := localIntegersInclusion K
  have hred : Continuous f.hom := by
    change Continuous (IsLocalRing.residue (↑O))
    apply continuous_of_tendsto_nhds_zero (IsLocalRing.residue (↑O)).toAddMonoidHom
    apply Filter.Tendsto.mono_right _ (pure_le_nhds _)
    apply Filter.tendsto_pure.mpr
    have hball : IsOpen {x : K | ValuativeRel.valuation K x < 1} := by
      let : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
      let : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup (G := K)
      simpa only [Valuation.restrict_lt_one_iff, IsValuativeTopology.v_eq_valuation] using
        (Valued.isOpen_ball K 1 (Γ₀ := ValuativeRel.ValueGroupWithZero K))
    apply Filter.mem_of_superset ((hball.preimage continuous_subtype_val).mem_nhds
      (show ValuativeRel.valuation K (0 : K) < 1 by simp)) ?_
    intro x hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((ValuativeRel.valuation K).mem_maximalIdeal_iff.mpr hx)
  let p := pointAlgebraEquiv A iso (integralRing K)
  let C : Set (A →ₐ[Integers.{u}] k) := {r | pointAlgebraEquiv A iso k r ∈ B}
  let good : Set (A →ₐ[Integers.{u}] (integralRing K)) :=
    (fun r : A →ₐ[Integers.{u}] R => R.val.comp r) '' {r | f.hom.comp r ∈ C}
  let := affinePointTopology Integers.{u} A K
  have hp : IsEmbedding p.symm := ⟨⟨rfl⟩, p.symm.injective⟩
  have hp' := hp.isOpenEmbedding_of_surjective p.symm.surjective
  obtain ⟨hComp, hOpen, _⟩ := compactOpenAffineReduction (R := R)
    (localField_properties K).2.2.1 (localField_properties K).2.2.2 f.hom hred C
  let I := (B.comap (changeRingHom M.group f)).map (changeRingHom M.group i)
  have hI : (I : Set _) = p.symm ⁻¹' good := by
    ext g
    change (∃ r : IntegralPoints M.group O, changeRing f r ∈ B ∧ changeRing i r = g) ↔
      ∃ r : A →ₐ[Integers.{u}] R, f.hom.comp r ∈ C ∧ R.val.comp r = p.symm g
    constructor
    · rintro ⟨r, hr, hg⟩
      obtain ⟨q, rfl⟩ := (pointAlgebraEquiv A iso O).surjective r
      refine ⟨q, ?_, p.injective ?_⟩
      · change pointAlgebraEquiv A iso k (f.hom.comp q) ∈ B
        rwa [← pointAlgebraEquiv_natural]
      · rw [Equiv.apply_symm_apply]
        change pointAlgebraEquiv A iso (integralRing K) (i.hom.comp q) = g
        rw [← pointAlgebraEquiv_natural A iso i q]
        exact hg
    · rintro ⟨r, hr, hg⟩
      refine ⟨pointAlgebraEquiv A iso O r, ?_, ?_⟩
      · rw [pointAlgebraEquiv_natural]
        exact hr
      · rw [pointAlgebraEquiv_natural, show i.hom = R.val from rfl, hg, Equiv.apply_symm_apply]
  have hIcompact : IsCompact (I : Set _) := hp.isInducing.isCompact_iff.mpr (by
    rw [hI, Set.image_preimage_eq_inter_range, p.symm.surjective.range_eq, Set.inter_univ]
    exact hComp)
  have hIopen : IsOpen (I : Set (IntegralPoints M.group (integralRing K))) := by
    rw [hI]
    exact hOpen.preimage hp'.continuous
  let _ : T2Space (A →ₐ[Integers.{u}] (integralRing K)) :=
    (show IsEmbedding (fun f : A →ₐ[Integers.{u}] (integralRing K) => (f : A → K)) from
      ⟨⟨rfl⟩, DFunLike.coe_injective⟩).t2Space
  let _ : T2Space (IntegralPoints M.group (integralRing K)) :=
    hp.t2Space
  refine ⟨hIcompact, hIopen, fun σ hσ => ?_⟩
  have hF := isClosed_eq hσ continuous_id
  exact ⟨hF.isClosedEmbedding_subtypeVal.isCompact_preimage hIcompact,
    hIopen.preimage continuous_subtype_val⟩

theorem stepThresholdCriterion : StepThresholdCriterion := by
  intro step offset a hstep
  unfold stepThreshold
  have h₁ := Int.ediv_lt_iff_lt_mul (a := -offset) (b := a) hstep
  have h₂ := Int.le_ediv_iff_mul_le (a := a - 1) (b := -offset) hstep
  omega

private theorem scaledParameterTest {K E : Type u} [Field K] [Field E]
    (f : K →+* E) (vK : Valuation K ℤᵐ⁰) (vE : Valuation E ℤᵐ⁰)
    (e : ℤ) (he : 0 < e) (hmap : ∀ z, vE (f z) = vK z ^ e)
    (ξ : Eˣ) (s k : ℤ) (hξ : vE (ξ : E) = WithZero.exp (-s)) (z : K) :
    vE ((↑(ξ ^ k) : E) * f z) < 1 ↔ vK z ≤ WithZero.exp (-stepThreshold e (k * s)) := by
  by_cases hz : z = 0
  · simp [hz, WithZero.exp_pos.le]
  have hlog := WithZero.exp_log (show vK z ≠ 0 from by simpa using hz)
  rw [map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hξ, hmap, ← hlog,
    ← WithZero.exp_zsmul, ← WithZero.exp_zsmul, ← WithZero.exp_add,
    WithZero.exp_lt_one_iff, WithZero.exp_le_exp]
  change k * -s + e * WithZero.log (vK z) < 0 ↔ _
  have h := Int.ediv_lt_iff_lt_mul (a := -(k * s)) (b := -WithZero.log (vK z)) he
  rw [mul_comm (-WithZero.log (vK z)), mul_neg] at h
  rw [mul_neg, stepThreshold]
  omega

theorem scaledParameterThreshold : ScaledParameterThreshold.{u} := by
  intro K E _ _ f vK vE e he hmap ξ π d hd hξπ r k hπ z
  let s := -WithZero.log (vE (ξ : E))
  have hξ : vE (ξ : E) = WithZero.exp (-s) := by
    dsimp [s]
    rw [neg_neg, WithZero.exp_log (by simp)]
  have hs : (d : ℤ) * s = r := by
    have h := congrArg (fun a : E => WithZero.log (vE a)) hξπ
    change WithZero.log (vE ((ξ : E) ^ d)) = WithZero.log (vE (π : E)) at h
    rw [map_pow, hξ, hπ, WithZero.log_pow, WithZero.log_exp, WithZero.log_exp] at h
    change (d : ℤ) * -s = -r at h
    rwa [mul_neg, neg_inj] at h
  have hde : 0 < (d : ℤ) * e := mul_pos (by exact_mod_cast hd) he
  rw [scaledParameterTest f vK vE e he hmap ξ s k hξ z]
  suffices stepThreshold e (k * s) = stepThreshold ((d : ℤ) * e) (k * r) by rw [this]
  unfold stepThreshold
  congr 1
  have hcancel (x : ℤ) : - (k * s) < x * e ↔ - (k * r) < x * ((d : ℤ) * e) := by
    have hmul : 0 < (d : ℤ) := by exact_mod_cast hd
    rw [← hs, mul_comm (d : ℤ) s]
    have h1 : - (k * (s * (d : ℤ))) = - (k * s) * (d : ℤ) := by ring
    have h2 : x * ((d : ℤ) * e) = (x * e) * (d : ℤ) := by ring
    rw [h1, h2, mul_lt_mul_iff_left₀ hmul]
  apply le_antisymm <;> apply Int.le_of_lt_add_one
  · apply (Int.ediv_lt_iff_lt_mul he).mpr
    apply (hcancel _).mpr
    exact (Int.ediv_lt_iff_lt_mul hde).mp (by omega) 
  · apply (Int.ediv_lt_iff_lt_mul hde).mpr
    apply (hcancel _).mp
    exact (Int.ediv_lt_iff_lt_mul he).mp (by omega)

private theorem valuationDvd {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰)
    (a x : v.valuationSubring) (ha : v (a : K) ≠ 0) :
    a ∣ x ↔ v (x : K) ≤ v (a : K) := by
  constructor
  · rintro ⟨y, rfl⟩
    change v ((a : K) * (y : K)) ≤ _
    rw [map_mul]
    have hy : v (y : K) ≤ 1 := y.prop
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hy (show 0 ≤ v (a : K) from zero_le)
  · intro hx
    have hy : (x : K) / (a : K) ∈ v.valuationSubring := by
      rw [v.mem_valuationSubring_iff, v.map_div, div_le_iff₀ (pos_iff_ne_zero.mpr ha), one_mul]
      exact hx
    refine ⟨⟨_, hy⟩, Subtype.ext ?_⟩
    change (x : K) = (a : K) * ((x : K) / (a : K))
    have ha' : (a : K) ≠ 0 := fun h => ha (by rw [h, map_zero])
    rw [mul_comm, div_mul_cancel₀ _ ha']

theorem idealLayerValuation : IdealLayerValuation.{u} := by
  intro K _ v π hπ x a
  have hpow (a : ℕ) : v (↑(π ^ a) : K) = WithZero.exp (-(a : ℤ)) := by
    change v ((π : K) ^ a) = _
    rw [map_pow, hπ, ← zpow_natCast, ← WithZero.exp_zsmul]
    congr 1
    simp
  have hdiv (a : ℕ) (x : v.valuationSubring) :
      π ^ a ∣ x ↔ v (x : K) ≤ WithZero.exp (-(a : ℤ)) := by
    rw [← hpow]
    exact valuationDvd v (π ^ a) x ((hpow a).symm ▸ WithZero.exp_pos.ne')
  have hmax : IsLocalRing.maximalIdeal v.valuationSubring = Ideal.span {π} := by
    ext y
    rw [v.mem_maximalIdeal_iff, Ideal.mem_span_singleton, ← pow_one π, hdiv]
    have h := WithZero.lt_mul_exp_iff_le (x := v (y : K))
      (y := WithZero.exp (-1 : ℤ)) WithZero.exp_pos.ne'
    simpa only [← WithZero.exp_add, show (-1 : ℤ) + 1 = 0 by decide, WithZero.exp_zero, Int.natCast_one] using h
  rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hdiv]

theorem valuationExtensionPowers : ValuationExtensionPowers.{u} := by
  intro K E _ _ f vK vE π hπ hunit e he hπE z
  by_cases hz : z = 0
  · simp [hz, zero_zpow _ he.ne']
  let n := -WithZero.log (vK z)
  have hk : vK z = WithZero.exp (-n) := by
    dsimp [n]
    rw [neg_neg, WithZero.exp_log (by simpa)]
  have hπn : vK ((π : K) ^ n) = vK z := by
    rw [map_zpow₀, hk, hπ, ← WithZero.exp_zsmul]
    congr 1
    simp
  have h := hunit (z / (π : K) ^ n) (by
    rw [vK.map_div, hπn, div_self (by simpa)])
  rw [map_div₀, vE.map_div, map_zpow₀, map_zpow₀, hπE,
    div_eq_one_iff_eq WithZero.exp_pos.ne' ] at h
  rw [h, hk, ← WithZero.exp_zsmul, ← WithZero.exp_zsmul]
  congr 1
  change n * -e = e * -n
  ring


private theorem rootWord_zero {D : Specs.Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (roots : List D.I) :
    rootValuePoint M.line R roots 0 ≫ rootProduct M.line M.root roots = 1 := by
  let : GrpObj additiveScheme.{u} := M.line.operations
  have hzero : M.line.point R (0 : R) = 1 := by
    have h := M.line.add R 0 0
    rw [zero_add] at h
    exact mul_left_cancel (h.trans (mul_one _).symm)
  induction roots with
  | nil => exact MonObj.comp_one _
  | cons a l ih =>
    rw [rootWord_cons]
    change (M.line.point R (0 : R) ≫ (M.root a).hom.hom) *
      (rootValuePoint M.line R l 0 ≫ rootProduct M.line M.root l) = 1
    rw [hzero, MonObj.one_comp, ih, one_mul]

private theorem cellValue_torus {D : Specs.Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (negative positive : List D.I) (t : TorusValues D R) :
    cellValue M R negative positive (0, t, 0) = torusPoint D R t ≫ M.torus.hom.hom := by
  rw [cellValue_eq_mul, rootWord_zero, rootWord_zero, one_mul, mul_one]

private theorem mem_markedTorus_iff {D : Specs.Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (negative positive : List D.I) (g : IntegralPoints M.group R) :
    g ∈ markedTorus M R ↔ ∃ t : TorusValues D R, g = cellValue M R negative positive (0, t, 0) := by
  change (∃ p : IntegralPoints (splitTorus D) R, p ≫ M.torus.hom.hom = g) ↔ _
  simp only [cellValue_torus]
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨t, rfl⟩ := (torusPoint_bijective D R).surjective p
    exact ⟨t, hp.symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨torusPoint D R t, rfl⟩

private theorem rationalCoordinates_injective {D : Specs.Pinning.BasedRootDatum.{u}}
    {M : IntegralMarking D} {K : Type u} [Field K]
    {H : Subgroup (IntegralPoints M.group (integralRing K))} {negative positive : List D.I}
    {J : Type u} {P : J → Type u} [∀ j, Field (P j)]
    (C : RationalRootChart M H negative positive J P) :
    Function.Injective (fun z : C.torus × (∀ j, P j) => C.coordinates z.1 z.2) := by
  intro z w h
  refine Prod.ext (Subtype.ext (congrArg (fun c => c.2.1) h)) (funext fun j => ?_)
  rcases C.covers j with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact (C.negMap i).injective (congrArg (fun c => c.1 i) h)
  · exact (C.posMap i).injective (congrArg (fun c => c.2.2 i) h)

theorem rationalScaledChart : RationalScaledChart.{u} := by
  intro D M K E _ _ H f v negative positive hn hp J P _ C vP e he hvn hvp y ξ π d hd hpow r hπ
    k hkn hkp g
  let O := integralRing v.valuationSubring
  have hval := valuedScaledChart M f v negative positive hn hp y ξ g.val
  have hmem : (g ∈ markedScaledReduction M H f v y ξ) ↔
      ∃ p : IntegralPoints M.group O,
        changeRing (integralRingMap v.valuationSubring.subtype) p =
          MulAut.conj (torusPoint D (integralRing E) (cocharacter D y (integralRing E) ξ) ≫
            M.torus.hom.hom) (changeRing (integralRingMap f) g.val) ∧
        ∃ t : TorusValues D _,
          changeRing (residueHom O) p = cellValue M _ negative positive (0, t, 0) := by
    apply exists_congr
    intro p
    exact and_comm.trans (and_congr_right' (mem_markedTorus_iff M _ negative positive _))
  have hdepthN (x : ∀ j, P j) (i : Fin negative.length) :
      v ((↑(ξ ^ D.datum.toLinearMap (D.datum.root negative[i]) y) : E) * f (C.negMap i (x (C.neg i)))) < 1 ↔
        vP (C.neg i) (x (C.neg i)) ≤ WithZero.exp (-stepThreshold ((d : ℤ) * e (C.neg i)) (k (C.neg i) * r)) := by
    rw [hkn]
    exact scaledParameterThreshold (f.comp (C.negMap i)) _ v _ (he _) (hvn i) ξ π d hd hpow r _ hπ _
  have hdepthP (x : ∀ j, P j) (i : Fin positive.length) :
      v ((↑(ξ ^ D.datum.toLinearMap (D.datum.root positive[i]) y) : E) * f (C.posMap i (x (C.pos i)))) < 1 ↔
        vP (C.pos i) (x (C.pos i)) ≤ WithZero.exp (-stepThreshold ((d : ℤ) * e (C.pos i)) (k (C.pos i) * r)) := by
    rw [hkp]
    exact scaledParameterThreshold (f.comp (C.posMap i)) _ v _ (he _) (hvp i) ξ π d hd hpow r _ hπ _
  have hchart := (markedChart M negative positive hn hp).1 (integralRing K)
  have hinj := rationalCoordinates_injective C
  refine (hmem.trans hval).trans ?_
  constructor
  · rintro ⟨z, ⟨hz, ht, hneg, hpos⟩, _⟩
    obtain ⟨t, x, hx⟩ := (C.rational z).mp (hz.symm ▸ g.prop)
    change C.coordinates t x = z at hx
    subst z
    refine ⟨(t, x), ⟨hz, ht, fun j => ?_⟩, fun w hw => hinj (hchart (hw.1.trans hz.symm))⟩
    rcases C.covers j with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact (hdepthN x i).mp (hneg i)
    · exact (hdepthP x i).mp (hpos i)
  · rintro ⟨⟨t, x⟩, ⟨hz, ht, hx⟩, _⟩
    refine ⟨C.coordinates t x, ⟨hz, ht, fun i => (hdepthN x i).mpr (hx _),
      fun i => (hdepthP x i).mpr (hx _)⟩, fun w hw => hchart (hw.1.trans hz.symm)⟩


private theorem changeRing_injective {D : Specs.Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    {R K : IntegralAlgebra.{u}} (i : R ⟶ K) (hi : Function.Injective i.hom) :
    Function.Injective (changeRingHom M.group i) := by
  obtain ⟨A, _, ⟨iso⟩⟩ := integralAffinePresentation M
  intro g h hgh
  obtain ⟨p, rfl⟩ := (pointAlgebraEquiv A iso R).surjective g
  obtain ⟨q, rfl⟩ := (pointAlgebraEquiv A iso R).surjective h
  change changeRing i (pointAlgebraEquiv A iso R p) = changeRing i (pointAlgebraEquiv A iso R q) at hgh
  rw [pointAlgebraEquiv_natural, pointAlgebraEquiv_natural] at hgh
  have he := (pointAlgebraEquiv A iso K).injective hgh
  congr 1
  ext x
  exact hi (congrArg (fun f : A →ₐ[Integers.{u}] K => f x) he)

theorem markedFieldCongruenceIndex : MarkedFieldCongruenceIndex.{u} := by
  intro D M R K i hi _ _ _ negative positive hn hp J _ P _ _ _ _ neg pos embedNeg embedPos
    hOrbits e he hNeg hPos T _ chart lift I I' a b q hq hres hOne hI hI'
  let H := I ⊓ I'
  let c (j : J) := max (a j) (b j)
  have hH (g) : g ∈ H ↔ ∃ (t : T) (x : ∀ j, integralLayer (P j) (c j)),
      lift (chart (t, fun j => x j)) = g := by
    constructor
    · rintro ⟨hg, hg'⟩
      obtain ⟨t, x, hx⟩ := (hI g).mp hg
      have hb : ∀ j, (x j : P j) ∈ IsLocalRing.maximalIdeal (P j) ^ b j :=
        (hI' (t, fun j => x j)).mp (hx ▸ hg' : lift (chart (t, fun j => x j)) ∈ I')
      refine ⟨t, fun j => ⟨x j, ?_⟩, hx⟩
      rcases le_total (a j) (b j) with hab | hba
      · simpa [c, max_eq_right hab] using hb j
      · simp [c, max_eq_left hba]
    · rintro ⟨t, x, rfl⟩
      have hdepth (j : J) {m : ℕ} (hm : m ≤ c j) :
          (x j : P j) ∈ IsLocalRing.maximalIdeal (P j) ^ m := Ideal.pow_le_pow_right hm (x j).prop
      exact ⟨(hI _).mpr ⟨t, fun j => ⟨x j, hdepth j (le_max_left _ _)⟩, rfl⟩,
        (hI' _).mpr (fun j => hdepth j (le_max_right _ _))⟩
  refine ⟨hH, ?_⟩
  have hl : Function.Injective lift := changeRing_injective M i hi
  have hI₀ (g) : g ∈ I.comap lift ↔ ∃ (t : T) (x : ∀ j, integralLayer (P j) (a j)),
      chart (t, fun j => x j) = g := by
    change lift g ∈ I ↔ _
    rw [hI]
    exact exists_congr (fun _ => exists_congr (fun _ => hl.eq_iff))
  have hH₀ (g) : g ∈ H.comap lift ↔ ∃ (t : T) (x : ∀ j, integralLayer (P j) (c j)),
      chart (t, fun j => x j) = g := by
    change lift g ∈ H ↔ _
    rw [hH]
    exact exists_congr (fun _ => exists_congr (fun _ => hl.eq_iff))
  obtain ⟨n, hn', hker, hindex⟩ := markedCongruenceIndex M R negative positive hn hp P neg pos
    embedNeg embedPos hOrbits e he hNeg hPos T (I.comap lift) (H.comap lift)
    (Subgroup.comap_mono (show H ≤ I from inf_le_left)) a c (fun _ => le_max_left _ _) q hq hres
    hOne hI₀ hH₀
  have hImap : (I.comap lift).map lift = I := by
    rw [Subgroup.map_comap_eq, inf_eq_right]
    intro g hg
    obtain ⟨t, x, hx⟩ := (hI g).mp hg
    exact ⟨chart (t, fun j => x j), hx⟩
  rw [Subgroup.relIndex_comap, hImap] at hindex
  exact ⟨n, hn', hker, hindex⟩


private theorem rootWord_eq_prod {D : Specs.Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (roots : List D.I) (x : Fin roots.length → R) :
    rootValuePoint M.line R roots x ≫ rootProduct M.line M.root roots =
      (markedRootFactors M R roots x).prod := by
  induction roots with
  | nil => exact MonObj.comp_one _
  | cons a l ih =>
    rw [rootWord_cons, ih]
    simp only [markedRootFactors, List.length_cons, List.ofFn_succ, List.prod_cons]
    rfl

private theorem rootFactor_neg {D : Specs.Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (a : D.I) (x : R) :
    (M.line.point R x ≫ (M.root a).hom.hom)⁻¹ = M.line.point R (-x) ≫ (M.root a).hom.hom := by
  let : GrpObj additiveScheme.{u} := M.line.operations
  have hzero : M.line.point R (0 : R) = 1 := by
    have h := M.line.add R 0 0
    rw [zero_add] at h
    exact mul_left_cancel (h.trans (mul_one _).symm)
  have h := M.line.add R x (-x)
  change M.line.point R x * M.line.point R (-x) = M.line.point R (x + -x) at h
  rw [add_neg_cancel, hzero] at h
  rw [← GrpObj.inv_comp, inv_eq_of_mul_eq_one_right h]

theorem markedWordFactors : MarkedWordFactors.{u} := by
  intro D M R negative positive z t
  constructor
  · rw [cellValue_eq_mul, rootWord_eq_prod, rootWord_eq_prod, List.prod_append, List.prod_cons]
  · rw [positiveFirstWord, rootWord_eq_prod, rootWord_eq_prod, List.prod_inv_reverse, List.prod_inv_reverse,
      List.prod_append, List.prod_cons]
    have hInv (l : List D.I) (x : Fin l.length → R) :
        (markedRootFactors M R l x).map (fun g => g⁻¹) = markedRootFactors M R l (-x) := by
      simp only [markedRootFactors, List.map_ofFn]
      congr 1
      funext l
      exact rootFactor_neg M R _ _
    rw [hInv, hInv]


open private affineTorusPointEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

private theorem markedTorusPoint_mul {D : Specs.Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (a b : TorusValues D R) :
    torusPoint D R (a * b) ≫ M.torus.hom.hom =
      (torusPoint D R a ≫ M.torus.hom.hom) * (torusPoint D R b ≫ M.torus.hom.hom) := by
  let e := affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X) R
  change e (a * b) ≫ M.torus.hom.hom = (e a ≫ M.torus.hom.hom) * (e b ≫ M.torus.hom.hom)
  rw [map_mul, MonObj.mul_comp]

private theorem markedTorusPoint_inv {D : Specs.Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    (R : IntegralAlgebra.{u}) (a : TorusValues D R) :
    torusPoint D R a⁻¹ ≫ M.torus.hom.hom = (torusPoint D R a ≫ M.torus.hom.hom)⁻¹ := by
  let e := affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X) R
  symm
  apply inv_eq_of_mul_eq_one_right
  rw [← markedTorusPoint_mul]
  change e (a * a⁻¹) ≫ M.torus.hom.hom = 1
  rw [show a * a⁻¹ = (1 : TorusValues D R) from mul_inv_cancel a]
  exact (congrArg (fun p : IntegralPoints (splitTorus D) R => p ≫ M.torus.hom.hom)
    (map_one e)).trans (MonObj.one_comp _)

theorem markedNormalizerCovariance : MarkedNormalizerCovariance := by
  intro D M K E Γ _ _ _ H f v x y ξ n O k i red cx cy point r t wx hr hn hwx hval
  let a := cy * t * wx⁻¹
  have ha (χ) : v (a χ : E) = 1 := by
    change v (↑((cy χ) * (t χ) * (wx χ)⁻¹) : E) = 1
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hval]
    exact mul_inv_cancel₀ (by simp)
  let V := v.valuationSubring
  let au : Multiplicative D.X →* V.unitGroup := a.codRestrict V.unitGroup (fun χ =>
    (Valuation.mem_unitGroup_iff (v := v) (x := _)).mpr (ha χ))
  let aO := V.unitGroupMulEquiv.toMonoidHom.comp au
  let p : IntegralPoints M.group O := torusPoint D O aO ≫ M.torus.hom.hom
  have hp : i p = point a := by
    change changeRing (integralRingMap V.subtype) (torusPoint D O aO ≫ M.torus.hom.hom) = _
    simp only [changeRing, ← Category.assoc]
    rw [← changeRing, torusPoint_natural]
    congr 2
  have hpred : red p ∈ markedTorus M _ := by
    refine ⟨changeRing (residueHom O) (torusPoint D O aO), ?_⟩
    change changeRing (residueHom O) (torusPoint D O aO) ≫ M.torus.hom.hom =
      changeRing (residueHom O) (torusPoint D O aO ≫ M.torus.hom.hom)
    exact Category.assoc _ _ _
  have hpn : red (p * r) ∈ Subgroup.normalizer (markedTorus M k : Set (IntegralPoints M.group k)) := by
    rw [map_mul]
    exact mul_mem (Subgroup.le_normalizer hpred) hr
  have hpw : point a = point cy * point t * (point wx)⁻¹ := by
    change torusPoint D (integralRing E) (cy * t * wx⁻¹) ≫ M.torus.hom.hom = _
    rw [markedTorusPoint_mul, markedTorusPoint_mul, markedTorusPoint_inv]
  let extend := (changeRingHom M.group (integralRingMap f)).comp H.subtype
  have hc : point cy * extend n * (point cx)⁻¹ = i (p * r) := by
    change point cy * changeRing (integralRingMap f) n.val * (point cx)⁻¹ = i (p * r)
    rw [hn, map_mul, hp, hpw, ← hwx, MulAut.conj_apply]
    group
  exact scaledReductionCovariance extend i red (markedTorus M _) (point cx) (point cy) n
    (p * r) hpn hc

theorem affineTwistContinuity : AffineTwistContinuity.{u} := by
  intro A X iso K _ _ σ hσ α e
  let : Algebra Integers.{u} (integralRing K : Type u) := (integralRing K).algebra
  let : TopologicalSpace (integralSpec.obj (op (integralRing K)) ⟶ X) := markedPointTopology A iso K
  let : TopologicalSpace (A →ₐ[Integers.{u}] (integralRing K)) :=
    @affinePointTopology Integers.{u} A K _ _ _ A.algebra (integralRing K).algebra _
  have he : IsEmbedding e.symm := ⟨⟨rfl⟩, e.symm.injective⟩
  apply he.isInducing.continuous_iff.mpr
  change Continuous (fun p => e.symm (e (σ.hom.comp ((e.symm p).comp α.hom))))
  simp only [Equiv.symm_apply_apply]
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro a
  change Continuous (fun p => σ.hom (e.symm p (α.hom a)))
  exact hσ.comp ((continuous_apply (α.hom a)).comp (continuous_induced_dom.comp he.continuous))

private theorem positivePower_le_one {value : ℤᵐ⁰} {e : ℤ} (he : 0 < e) : value ^ e ≤ 1 ↔ value ≤ 1 := by
  by_cases hvalue : value = 0
  · simp [hvalue, zero_zpow _ he.ne']
  rw [← WithZero.exp_log hvalue, ← WithZero.exp_zsmul, WithZero.exp_le_one_iff, WithZero.exp_le_one_iff]
  change e * value.log ≤ 0 ↔ value.log ≤ 0
  simpa only [mul_zero] using (mul_le_mul_iff_right₀ he (b := value.log) (c := 0))

private theorem positivePower_lt_one {value : ℤᵐ⁰} {e : ℤ} (he : 0 < e) :
    value ^ e < 1 ↔ value ≤ WithZero.exp (-1 : ℤ) := by
  have h : value < 1 ↔ value ≤ WithZero.exp (-1 : ℤ) := by
    simpa only [← WithZero.exp_add, show (-1 : ℤ) + 1 = 0 by decide, WithZero.exp_zero] using
      (WithZero.lt_mul_exp_iff_le (x := value) (y := WithZero.exp (-1 : ℤ)) WithZero.exp_pos.ne')
  rw [← h]
  by_cases hvalue : value = 0
  · simp [hvalue, zero_zpow _ he.ne']
  rw [← WithZero.exp_log hvalue, ← WithZero.exp_zsmul, WithZero.exp_lt_one_iff, WithZero.exp_lt_one_iff]
  change e * value.log < 0 ↔ value.log < 0
  simpa only [mul_zero] using (mul_lt_mul_iff_right₀ he (b := value.log) (c := 0))

private theorem iwahoriValuationChart {D : Specs.Pinning.BasedRootDatum.{u}} (M : IntegralMarking D)
    {K : Type u} [Field K] (H : Subgroup (IntegralPoints M.group (integralRing K)))
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (negative positive : List D.I)
    (hn : Specs.OrderedRootProducts.Enumerates negative {i | ¬ D.base.IsPos i})
    (hp : Specs.OrderedRootProducts.Enumerates positive {i | D.base.IsPos i})
    (B : Subgroup (IntegralPoints M.group (residueRing (integralRing v.valuationSubring))))
    (hB : (B : Set (IntegralPoints M.group (residueRing (integralRing v.valuationSubring)))) =
      Set.range (fun z : TorusValues D (residueRing (integralRing v.valuationSubring)) ×
        (Fin positive.length → residueRing (integralRing v.valuationSubring)) =>
        cellValue M _ negative positive (0, z.1, z.2))) (g : H) :
    g ∈ iwahoriSubgroup (integralRingMap v.valuationSubring.subtype) B H ↔
      ∃! z : CellValues D (integralRing K) negative positive,
        cellValue M (integralRing K) negative positive z = g.val ∧
        (∀ χ, v (z.2.1 χ : K) = 1) ∧
        (∀ i, v (z.1 i) < 1) ∧ ∀ i, v (z.2.2 i) ≤ 1 := by
  let V := v.valuationSubring
  let O := integralRing V
  let i := integralRingMap V.subtype
  have hi : Function.Injective i.hom := Subtype.val_injective
  have hc := markedChart M negative positive hn hp
  refine ((iwahoriChart M i hi B H negative positive hn hp hB g).1).trans ?_
  constructor
  · rintro ⟨w, ⟨hw, hneg⟩, _⟩
    refine ⟨mapCellValues i w, ⟨(hc.2 i w).symm.trans hw, fun χ => ?_,
      fun l => v.mem_maximalIdeal_iff.mp (hneg l), fun l => (w.2.2 l).prop⟩, ?_⟩
    · exact (Valuation.mem_unitGroup_iff (v := v) (x := _)).mp
        (V.unitGroupMulEquiv.symm (w.2.1 χ)).prop
    · intro z hz
      exact hc.1 _ (hz.1.trans ((hc.2 i w).symm.trans hw).symm)
  · rintro ⟨z, ⟨hz, ht, hn', hp'⟩, _⟩
    let u : Multiplicative D.X →* V.unitGroup := z.2.1.codRestrict V.unitGroup
      (fun χ => (Valuation.mem_unitGroup_iff (v := v) (x := _)).mpr (ht χ))
    let w : CellValues D O negative positive :=
      (fun l => ⟨z.1 l, (hn' l).le⟩, V.unitGroupMulEquiv.toMonoidHom.comp u,
        fun l => ⟨z.2.2 l, hp' l⟩)
    have hm : mapCellValues i w = z :=
      Prod.ext rfl (Prod.ext (MonoidHom.ext fun χ => Units.ext (V.coe_unitGroupMulEquiv_apply (u χ))) rfl)
    have hw : changeRing i (cellValue M O negative positive w) = g.val := by
      rw [hc.2, hm, hz]
    exact ⟨w, ⟨hw, fun l => v.mem_maximalIdeal_iff.mpr (hn' l)⟩, fun w' hw' =>
      mapCellValues_injective i hi _ _ (hc.1 _ ((hc.2 i w').symm.trans (hw'.1.trans (hw.symm.trans (hc.2 i w)))))⟩

theorem rationalIwahoriChart : RationalIwahoriChart.{u} := by
  intro D M K _ H v negative positive hn hp O k B hB J P _ C vP e he hvn hvp a han hap g
  have hc := (markedChart M negative positive hn hp).1 (integralRing K)
  have hinj := rationalCoordinates_injective C
  have hNeg (x : ∀ j, P j) (l : Fin negative.length) :
      v (C.negMap l (x (C.neg l))) < 1 ↔ vP _ (x (C.neg l)) ≤ WithZero.exp (-(a (C.neg l) : ℤ)) := by
    rw [hvn, han, Int.natCast_one]
    exact positivePower_lt_one (he _)
  have hPos (x : ∀ j, P j) (l : Fin positive.length) :
      v (C.posMap l (x (C.pos l))) ≤ 1 ↔ vP _ (x (C.pos l)) ≤ WithZero.exp (-(a (C.pos l) : ℤ)) := by
    rw [hvp, hap, Int.natCast_zero, neg_zero, WithZero.exp_zero]
    exact positivePower_le_one (he _)
  refine (iwahoriValuationChart M H v negative positive hn hp B hB g).trans ?_
  constructor
  · rintro ⟨z, ⟨hz, ht, hn', hp'⟩, _⟩
    obtain ⟨t, x, hx⟩ := (C.rational z).mp (hz.symm ▸ g.prop)
    change C.coordinates t x = z at hx
    subst z
    refine ⟨(t, x), ⟨hz, ht, fun j => ?_⟩, fun w hw => hinj (hc (hw.1.trans hz.symm))⟩
    rcases C.covers j with ⟨l, rfl⟩ | ⟨l, rfl⟩
    · exact (hNeg x l).mp (hn' l)
    · exact (hPos x l).mp (hp' l)
  · rintro ⟨⟨t, x⟩, ⟨hz, ht, hx⟩, _⟩
    exact ⟨C.coordinates t x, ⟨hz, ht, fun l => (hNeg x l).mpr (hx _),
      fun l => (hPos x l).mpr (hx _)⟩, fun w hw => hc (hw.1.trans hz.symm)⟩

section FieldBorel

open Specs.AdjointRepresentation (GroupPoints)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.RootGroups (rootPoint)
open LinearAlgebraicGroups.CocharacterDynamics (multiplyFactors)
open private rootPoint_surjective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private rootPoint_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private fibrePointsEquiv forgetFibrePoint_comp from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

private abbrev FibreCoordinate {D : Specs.Pinning.BasedRootDatum.{u}} {k : Type u} [Field k]
    {A : Specs.RootGroups.AdditiveLine k} (F : Specs.RationalRealization.Realization D A) (a : D.I) :=
  Specs.Pinning.RootCoordinate A F.pinned.pair.T
    (F.pinned.roots (F.datumIso.val.indexEquiv a)).val (F.datumIso.val.indexEquiv a).val

private theorem pinnedFibrePositive {D : Specs.Pinning.BasedRootDatum.{u}} {k : Type u} [Field k]
    {A : Specs.RootGroups.AdditiveLine k} (F : Specs.RationalRealization.Realization D A)
    (hS : Specs.BorelsAndChambers.IsPositiveSystem F.pinned.pair.T
      (subgroupRoots F.pinned.pair.T F.pinned.pair.B)) (a : D.I) :
    F.datumIso.val.indexEquiv a ∈ subgroupRoots F.pinned.pair.T F.pinned.pair.B ↔ D.base.IsPos a := by
  let := F.attached.comm
  let := D.finiteRoots
  obtain ⟨f, _, hf⟩ := hS
  let L := f.comp F.datumIso.val.weightEquiv.toLinearMap
  have hpos (i : D.I) : F.datumIso.val.indexEquiv i ∈ subgroupRoots F.pinned.pair.T F.pinned.pair.B ↔
      0 < L (D.datum.root i) := by
    rw [hf]
    change 0 < f (Additive.ofMul (F.datumIso.val.indexEquiv i).val) ↔
      0 < f (F.datumIso.val.weightEquiv (D.datum.root i))
    rw [show F.datumIso.val.weightEquiv (D.datum.root i) =
      Additive.ofMul (F.datumIso.val.indexEquiv i).val from
      (congrFun F.datumIso.val.root_weightMap i).trans (F.attached.datum.root_eq _)]
  have hs (i : D.I) (hi : i ∈ D.base.support) : 0 < L (D.datum.root i) :=
    (hpos i).mp (F.simpleRoot ⟨i, hi⟩).property.1
  have hfwd {i : D.I} (hi : D.base.IsPos i) : 0 < L (D.datum.root i) := by
    apply hi.induction_on_add hs
    intro j l m hl hj hs'
    rw [hl, map_add]
    exact add_pos hj (hs l hs')
  refine (hpos a).trans ⟨?_, hfwd⟩
  intro ha
  by_contra hn
  let := D.datum.indexNeg
  have hm := hfwd ((RootPairing.Base.IsPos.neg_iff_not D.base a).mpr hn)
  have hr : D.datum.root (-a) = -D.datum.root a := by
    rw [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  rw [hr, map_neg] at hm
  exact (not_lt_of_ge (neg_nonpos.mpr ha.le)) hm

private noncomputable def fibreRootValuePoint {D : Specs.Pinning.BasedRootDatum.{u}} {k : Type u}
    [Field k] {A : Specs.RootGroups.AdditiveLine k} (F : Specs.RationalRealization.Realization D A)
    (z : ∀ a, FibreCoordinate F a) (R : TestAlgebra k) :
    (roots : List D.I) → (Fin roots.length → R) →
      Points (Specs.OrderedRootProducts.product
        (fun a => (F.pinned.roots a).val.group.X) (roots.map F.datumIso.val.indexEquiv)) R
  | [], _ => toUnit _
  | a :: l, x => lift (rootPoint (z a).val.hom R (x 0)) (fibreRootValuePoint F z R l (Fin.tail x))

set_option maxHeartbeats 650000 in
set_option backward.isDefEq.respectTransparency false in
private theorem fibreRootValuePoint_surjective {D : Specs.Pinning.BasedRootDatum.{u}} {k : Type u}
    [Field k] {A : Specs.RootGroups.AdditiveLine k} (F : Specs.RationalRealization.Realization D A)
    (z : ∀ a, FibreCoordinate F a) (R : TestAlgebra k) (roots : List D.I) :
    Function.Surjective (fibreRootValuePoint F z R roots) := by
  induction roots with
  | nil => exact fun p => ⟨Fin.elim0, isTerminalTensorUnit.hom_ext _ _⟩
  | cons a l ih =>
    intro p
    obtain ⟨x, hx⟩ := rootPoint_surjective (z a).val R (p ≫ fst _ _)
    obtain ⟨y, hy⟩ := ih (p ≫ snd _ _)
    refine ⟨Fin.cons x y, ?_⟩
    simp only [fibreRootValuePoint, Fin.cons_zero, Fin.tail_cons, hx, hy]
    apply CartesianMonoidalCategory.hom_ext
    · exact lift_fst _ _
    · exact lift_snd _ _

set_option backward.isDefEq.respectTransparency false in
private theorem fibreRootWord_comparison {D : Specs.Pinning.BasedRootDatum.{u}}
    (M : IntegralMarking D) {k : Type u} [Field k] {A : Specs.RootGroups.AdditiveLine k}
    (F : Specs.RationalRealization.Realization D A) (z : ∀ a, FibreCoordinate F a)
    (φ : Points F.pinned.pair.G.val.X (CommAlgCat.of k k) →* IntegralPoints M.group (integralRing k))
    (hφ : ∀ a (r : k),
      φ (rootPoint ((z a).val.hom ≫ (F.pinned.roots (F.datumIso.val.indexEquiv a)).val.inclusion)
        (CommAlgCat.of k k) r) = M.line.point (integralRing k) r ≫ (M.root a).hom.hom)
    (roots : List D.I) (x : Fin roots.length → k) :
    φ (fibreRootValuePoint F z (CommAlgCat.of k k) roots x ≫ Specs.OrderedRootProducts.rootProduct
      F.pinned.roots (roots.map F.datumIso.val.indexEquiv)) =
      rootValuePoint M.line (integralRing k) roots x ≫ rootProduct M.line M.root roots := by
  induction roots with
  | nil =>
    change φ (toUnit _ ≫ 1) = rootValuePoint M.line (integralRing k) [] x ≫ 1
    rw [MonObj.comp_one, MonObj.comp_one]
    exact map_one φ
  | cons a l ih =>
    rw [rootWord_cons]
    let R := CommAlgCat.of k k
    let root := (F.pinned.roots (F.datumIso.val.indexEquiv a)).val.inclusion
    let p := rootPoint (z a).val.hom R (x 0)
    let q := fibreRootValuePoint F z R l (Fin.tail x)
    let word := Specs.OrderedRootProducts.rootProduct F.pinned.roots (l.map F.datumIso.val.indexEquiv)
    change φ (lift p q ≫ ((fst _ _ ≫ root.hom.hom) * (snd _ _ ≫ word))) = _
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, map_mul]
    exact congrArg₂ (· * ·) (hφ a (x 0)) (ih (Fin.tail x))

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Identify the residue Borel in the actual pinned field fibre. -/
theorem markedFibreBorel : MarkedFibreBorel.{u} := by
  intro D M k _ A F e t z ht hz negative positive hpositive
  let P := F.pinned.pair
  let R := CommAlgCat.of k k
  let φ : GroupPoints P.G.val R →* IntegralPoints M.group (integralRing k) :=
    (fibrePointsEquiv M.group R).toMonoidHom.comp (((groupPointsFunctor k).map e.inv).app R).hom
  let inclB : GroupPoints P.B.group R →* GroupPoints P.G.val R :=
    (((groupPointsFunctor k).map P.B.inclusion).app R).hom
  let B := (φ.comp inclB).range
  refine ⟨B, ?_, ?_⟩
  · ext g
    change (∃ b, forgetFibrePoint M.group R ((b ≫ P.B.inclusion.hom.hom) ≫ e.inv.hom.hom) = g) ↔ _
    simp only [Category.assoc, Set.mem_range]
    rfl
  obtain ⟨_, _, _, hCorr, _, _, hBorel⟩ :=
    LinearAlgebraicGroups.RootData.BorelPositivity.borelPositivity P.G P.reductive P.T P.split P.maximal
  have hpos := pinnedFibrePositive F (hCorr.1 P.B P.borel P.containsTorus)
  let l := positive.map F.datumIso.val.indexEquiv
  have hl : Specs.OrderedRootProducts.Enumerates l (subgroupRoots P.T P.B) := by
    refine ⟨hpositive.1.map F.datumIso.val.indexEquiv.injective, ?_⟩
    intro a
    obtain ⟨i, rfl⟩ := F.datumIso.val.indexEquiv.surjective a
    change F.datumIso.val.indexEquiv i ∈ l ↔
      F.datumIso.val.indexEquiv i ∈ subgroupRoots F.pinned.pair.T F.pinned.pair.B
    simpa only [l, List.mem_map, Equiv.apply_eq_iff_eq, exists_eq_right] using
      (hpositive.2 i).trans (hpos i).symm
  obtain ⟨U, j, _, _, _, hj, _, _, hMul, hParams⟩ := hBorel P.B P.borel P.containsTorus
  obtain ⟨d, hd⟩ := hParams F.pinned.roots l hl
  let m := multiplyFactors j U.inclusion
  let : IsIso m := hMul
  have hm (s : Points P.T.group.X R)
      (q : Points (Specs.OrderedRootProducts.product (fun a => (F.pinned.roots a).val.group.X) l) R) :
      inclB (lift s (q ≫ d.hom) ≫ m) =
        (s ≫ P.T.inclusion.hom.hom) * (q ≫ Specs.OrderedRootProducts.rootProduct F.pinned.roots l) := by
    change (lift s (q ≫ d.hom) ≫ m) ≫ P.B.inclusion.hom.hom = _
    simp only [m, multiplyFactors, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, MonObj.mul_comp,
      Category.assoc]
    rw [← hd]
    congr 2
    exact congrArg (fun g : P.T.group ⟶ P.G.val => g.hom.hom) hj
  have hTor (s : GroupPoints ((fibre k).obj (splitTorus D)) R) :
      φ ((s ≫ t.hom.hom.hom) ≫ P.T.inclusion.hom.hom) =
        forgetFibrePoint (splitTorus D) R s ≫ M.torus.hom.hom := by
    have h : (t.hom ≫ P.T.inclusion) ≫ e.inv = (fibre k).map M.torus := by
      calc
        _ = ((fibre k).map M.torus ≫ e.hom) ≫ e.inv := congrArg (· ≫ e.inv) ht.symm
        _ = _ := by simp only [Category.assoc, e.hom_inv_id, Category.comp_id]
    change forgetFibrePoint M.group R (((s ≫ t.hom.hom.hom) ≫ P.T.inclusion.hom.hom) ≫
      e.inv.hom.hom) = _
    simp only [Category.assoc]
    exact (congrArg (fun f : (fibre k).obj (splitTorus D) ⟶ (fibre k).obj M.group =>
      forgetFibrePoint M.group R (s ≫ f.hom.hom)) h).trans (forgetFibrePoint_comp M.torus R s)
  have hRoot (a : D.I) (r : k) : φ (rootPoint ((z a).val.hom ≫
      (F.pinned.roots (F.datumIso.val.indexEquiv a)).val.inclusion) R r) =
      M.line.point (integralRing k) r ≫ (M.root a).hom.hom := by
    change forgetFibrePoint M.group R ((rootPoint _ R r) ≫ e.inv.hom.hom) = _
    rw [← rootPoint_comp]
    exact hz a r
  have hword := fibreRootWord_comparison M F z φ hRoot positive
  ext g
  constructor
  · rintro ⟨b, rfl⟩
    let w := b ≫ inv m
    let s := w ≫ fst _ _
    let q := (w ≫ snd _ _) ≫ d.inv
    have hw : lift s (q ≫ d.hom) ≫ m = b := by
      rw [show lift s (q ≫ d.hom) = w by
        apply CartesianMonoidalCategory.hom_ext
        · exact lift_fst _ _
        · simp [q], show w ≫ m = b by
          change (b ≫ inv m) ≫ m = b
          rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]]
    obtain ⟨x, hx⟩ := fibreRootValuePoint_surjective F z R positive q
    let s₀ : GroupPoints ((fibre k).obj (splitTorus D)) R := s ≫ t.inv.hom.hom
    have hs : s₀ ≫ t.hom.hom.hom = s := by
      change (s ≫ t.inv.hom.hom) ≫ t.hom.hom.hom = s
      rw [Category.assoc, show t.inv.hom.hom ≫ t.hom.hom.hom = 𝟙 _ from
        congrArg (fun a => a.hom.hom) t.inv_hom_id, Category.comp_id]
    obtain ⟨v, hv⟩ := (torusPoint_bijective D (integralRing k)).surjective
      (forgetFibrePoint (splitTorus D) R s₀)
    refine ⟨(v, x), ?_⟩
    change cellValue M (integralRing k) negative positive (0, v, x) = φ (inclB b)
    rw [cellValue_eq_mul, rootWord_zero, one_mul, ← hw, hm, map_mul]
    refine congrArg₂ (· * ·) ?_ ?_
    · exact (congrArg (· ≫ M.torus.hom.hom) hv).trans ((hTor s₀).symm.trans
        (congrArg (fun p : Points P.T.group.X R => φ (p ≫ P.T.inclusion.hom.hom)) hs))
    · exact (hword x).symm.trans (congrArg (fun p : Points _ R =>
        φ (p ≫ Specs.OrderedRootProducts.rootProduct F.pinned.roots l)) hx)
  · rintro ⟨⟨v, x⟩, rfl⟩
    obtain ⟨s₀, hs⟩ := (fibrePointsEquiv (splitTorus D) R).surjective (torusPoint D (integralRing k) v)
    change forgetFibrePoint (splitTorus D) R s₀ = torusPoint D (integralRing k) v at hs
    let s : GroupPoints P.T.group R := s₀ ≫ t.hom.hom.hom
    let q := fibreRootValuePoint F z R positive x
    refine ⟨lift s (q ≫ d.hom) ≫ m, ?_⟩
    change φ (inclB (lift s (q ≫ d.hom) ≫ m)) = cellValue M (integralRing k) negative positive (0, v, x)
    rw [hm, map_mul, show φ (q ≫ Specs.OrderedRootProducts.rootProduct F.pinned.roots l) = _ from hword x,
      cellValue_eq_mul, rootWord_zero, one_mul, show φ (s ≫ P.T.inclusion.hom.hom) = _ from hTor s₀, hs]

end FieldBorel

set_option maxHeartbeats 600000 in
theorem standardAlcoveReduction : StandardAlcoveReduction.{u} := by
  intro D M K E _ _ H f vK vE hunit negative positive hn hp residue B hB J P _ C vP eK eE
    heK heE hvnK hvpK hvnE hvpE y ξ π d hd hpow r hπ k hkn hkp hoffn hoffp
  let level (j : J) := stepThreshold ((d : ℤ) * eE j) (k j * r)
  let a (j : J) := (level j).toNat
  have hstep (j : J) : 0 < (d : ℤ) * eE j := mul_pos (by exact_mod_cast hd) (heE j)
  have hneg (i : Fin negative.length) : level (C.neg i) = 1 := by
    apply (stepThresholdCriterion _ _ _ (hstep _)).mpr
    obtain ⟨hl, hh⟩ := hoffn i
    rw [neg_mul] at hl
    simp only [one_mul, sub_self, zero_mul, add_zero]
    exact ⟨by omega, hh.le⟩
  have hpos (i : Fin positive.length) : level (C.pos i) = 0 := by
    apply (stepThresholdCriterion _ _ _ (hstep _)).mpr
    obtain ⟨hl, hh⟩ := hoffp i
    simp only [zero_mul, add_zero, zero_sub, neg_mul, one_mul]
    exact ⟨hl, by omega⟩
  have ha (j : J) : (a j : ℤ) = level j := by
    rcases C.covers j with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · simp [a, hneg i]
    · simp [a, hpos i]
  ext g
  rw [rationalScaledChart M H f vE negative positive hn hp P C vP eE heE hvnE hvpE y ξ π d hd hpow r hπ k hkn hkp g,
    rationalIwahoriChart M H vK negative positive hn hp B hB P C vP eK heK hvnK hvpK a
      (fun i => by simp [a, hneg i]) (fun i => by simp [a, hpos i]) g]
  apply existsUnique_congr
  intro z
  simp only [hunit, ha, level]

open ValuativeRel in
private theorem normalizedLocalValuation_le_iff (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x y : K) :
    normalizedLocalValuation K x ≤ normalizedLocalValuation K y ↔ x ≤ᵥ y :=
  (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toOrderIso.le_iff_le.trans
    (Valuation.Compatible.vle_iff_le (v := valuation K) x y).symm

open ValuativeRel in
theorem localValuationNormalization : LocalValuationNormalization.{u} := by
  intro K _ _ _ _
  have hsurj : Function.Surjective (normalizedLocalValuation K) :=
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).surjective.comp (valuation_surjective (K := K))
  refine ⟨hsurj, ?_, ?_⟩
  · ext x
    rw [Valuation.mem_valuationSubring_iff, Valuation.mem_valuationSubring_iff,
      ← (normalizedLocalValuation K).map_one, normalizedLocalValuation_le_iff,
      Valuation.Compatible.vle_iff_le (v := valuation K), map_one]
  intro E _ _ _ _ _ _
  let vK := normalizedLocalValuation K
  let vE := normalizedLocalValuation E
  have hle (x y : K) : vE (algebraMap K E x) ≤ vE (algebraMap K E y) ↔ vK x ≤ vK y := by
    dsimp only [vK, vE]
    rw [normalizedLocalValuation_le_iff, normalizedLocalValuation_le_iff, ValuativeExtension.vle_iff_vle]
  have hunit (x : K) (hx : vK x = 1) : vE (algebraMap K E x) = 1 := by
    rw [← map_one (vE : Valuation E _), ← map_one (algebraMap K E), le_antisymm_iff, hle, hle, hx, map_one]
    exact ⟨le_rfl, le_rfl⟩
  obtain ⟨p, hp⟩ := hsurj (WithZero.exp (-1 : ℤ))
  have hp0 : p ≠ 0 := fun h => WithZero.exp_pos.ne' (hp.symm.trans (by rw [h, map_zero]))
  let π := Units.mk0 p hp0
  have hπ : vK (π : K) = WithZero.exp (-1 : ℤ) := hp
  have hlt : vE (algebraMap K E (π : K)) < 1 := by
    rw [← not_le, ← map_one (vE : Valuation E _), ← map_one (algebraMap K E), hle, hπ, map_one]
    simp
  have hne : vE (algebraMap K E (π : K)) ≠ 0 := by simp
  let e := -WithZero.log (vE (algebraMap K E (π : K)))
  have he : 0 < e := by
    apply neg_pos.mpr
    apply (WithZero.log_lt_iff_lt_exp hne).mpr
    simpa only [WithZero.exp_zero] using hlt
  have hπE : vE (algebraMap K E (π : K)) = WithZero.exp (-e) := by
    dsimp only [e]
    rw [neg_neg, WithZero.exp_log hne]
  let n := e.toNat
  have hn : (n : ℤ) = e := Int.toNat_of_nonneg he.le
  refine ⟨n, by exact_mod_cast (hn.symm ▸ he : 0 < (n : ℤ)), fun z => ?_⟩
  simpa only [← zpow_natCast, hn] using
    valuationExtensionPowers (algebraMap K E) vK vE π hπ hunit e he hπE z


theorem integralThresholdValuation : IntegralThresholdValuation.{u} := by
  intro K _ v π hπ x a
  rw [idealLayerValuation v π hπ]
  rcases le_total 0 a with ha | ha
  · rw [Int.toNat_of_nonneg ha]
  · rw [Int.toNat_eq_zero.mpr ha]
    simp only [Int.natCast_zero, neg_zero, WithZero.exp_zero]
    exact iff_of_true (x.prop.trans (WithZero.one_le_exp_iff.mpr (neg_nonneg.mpr ha))) x.prop

theorem canonicalIntegralAlgebra : CanonicalIntegralAlgebra.{u} := by
  intro R
  have h : integerAlgebra R = R.algebra := by
    apply Algebra.algebra_ext
    intro x
    let e : ℤ ≃+* Integers.{u} := ULift.ringEquiv.symm
    exact DFunLike.congr_fun (RingHom.ext_int ((integerAlgebra R).algebraMap.comp e.toRingHom)
      (R.algebra.algebraMap.comp e.toRingHom)) x.down
  exact congrArg (fun a : Algebra Integers.{u} R => @CommAlgCat.of Integers.{u} _ R _ a) h

open scoped TensorProduct in
theorem affineFibreTwistContinuity : AffineFibreTwistContinuity := by
  intro B A K _ _ _ _ _ _ _ σ hσ α
  let : TopologicalSpace (A →ₐ[B] K) := affinePointTopology B A K
  let extend (p : A →ₐ[B] K) := Algebra.TensorProduct.lift p (AlgHom.id B K) (fun _ _ => Commute.all _ _)
  have he (x : A ⊗[B] K) : Continuous (fun p : A →ₐ[B] K => extend p x) := by
    induction x using TensorProduct.inductionOn with
    | tmul a k =>
      have h : Continuous (fun p : A →ₐ[B] K => p a) := (continuous_apply a).comp continuous_induced_dom
      simp only [extend, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply]
      exact continuous_mul.comp (h.prodMk continuous_const)
    | add u v hu hv =>
      simp only [map_add]
      exact continuous_add.comp (hu.prodMk hv)
  exact continuous_induced_rng.mpr (continuous_pi fun a => hσ.comp (he (α a)))

theorem affineScalarPointEmbedding : AffineScalarPointEmbedding := by
  intro B A K L _ _ _ _ _ _ _ _ _ f hf
  let : TopologicalSpace (A →ₐ[B] K) := affinePointTopology B A K
  let : TopologicalSpace (A →ₐ[B] L) := affinePointTopology B A L
  have hK : IsEmbedding (fun p : A →ₐ[B] K => (p : A → K)) := ⟨⟨rfl⟩, DFunLike.coe_injective⟩
  have hL : IsEmbedding (fun p : A →ₐ[B] L => (p : A → L)) := ⟨⟨rfl⟩, DFunLike.coe_injective⟩
  have hMap : IsEmbedding (fun p : A → K => fun a => f (p a)) := IsEmbedding.piMap (fun _ => hf)
  exact (hL.of_comp_iff).mp (hMap.comp hK)

theorem localFieldExtensionTopology : LocalFieldExtensionTopology := by
  intro K L _ _ _ _ _ _ J _ b hb hb'
  have hcoords (x : K) : b.equivFun (algebraMap K L x) = x • b.equivFun 1 := by
    rw [← map_smul]
    exact congrArg b.equivFun ((Algebra.smul_def x (1 : L)).trans (mul_one _)).symm
  have hc (i : J) : Continuous (fun x : K => x * b.equivFun 1 i) :=
    continuous_mul.comp (continuous_id.prodMk continuous_const)
  have hcont : Continuous (algebraMap K L) := by
    have hf : (fun x : K => b.equivFun.symm (fun i => x * b.equivFun 1 i)) = algebraMap K L := by
      funext x
      apply b.equivFun.injective
      rw [LinearEquiv.apply_symm_apply, hcoords]
      rfl
    rw [← hf]
    exact hb'.comp (continuous_pi hc)
  have hOne : b.equivFun (1 : L) ≠ 0 := by simp
  obtain ⟨i, hi⟩ : ∃ i, b.equivFun (1 : L) i ≠ 0 := by
    by_contra! hn
    exact hOne (funext hn)
  let pr (x : L) := b.equivFun x i * (b.equivFun 1 i)⁻¹
  have hpr : Continuous pr :=
    continuous_mul.comp (((continuous_apply i).comp hb).prodMk continuous_const)
  have hl : Function.LeftInverse pr (algebraMap K L) := by
    intro x
    change b.equivFun (algebraMap K L x) i * (b.equivFun 1 i)⁻¹ = x
    rw [hcoords]
    change (x * b.equivFun 1 i) * (b.equivFun 1 i)⁻¹ = x
    rw [mul_assoc, mul_inv_cancel₀ hi, mul_one]
  refine ⟨hl.isEmbedding hpr hcont, fun σ => ?_⟩
  let u := σ.toLinearMap
  have hs (x : L) (j : J) : b.equivFun (σ x) j =
      ∑ i, b.equivFun x i * b.equivFun (σ (b i)) j := by
    change b.equivFun (u x) j = _
    calc
      _ = b.equivFun (u (∑ i, b.repr x i • b i)) j := congrArg (fun y => b.equivFun (u y) j) (b.sum_repr x).symm
      _ = _ := by
        simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rfl
  have hσ : (fun x : L => b.equivFun.symm (fun j => ∑ i, b.equivFun x i * b.equivFun (σ (b i)) j)) = σ := by
    funext x
    apply b.equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    exact funext (fun j => (hs x j).symm)
  rw [← hσ]
  refine hb'.comp (continuous_pi fun j => ?_)
  exact continuous_finsetSum _ (fun i _ =>
    continuous_mul.comp (((continuous_apply i).comp hb).prodMk continuous_const))

theorem ramificationIdealMap : RamificationIdealMap.{u} := by
  intro K L _ _ vK vL πK πL hπK hπL f e hf
  have hmax : IsLocalRing.maximalIdeal vK.valuationSubring = Ideal.span {πK} := by
    ext x
    rw [Ideal.mem_span_singleton, valuationDvd vK πK x (hπK.symm ▸ WithZero.exp_pos.ne'), hπK]
    simpa only [pow_one, Int.natCast_one] using idealLayerValuation vK πK hπK x 1
  rw [hmax, Ideal.map_span, Set.image_singleton]
  ext x
  rw [Ideal.mem_span_singleton, valuationDvd vL (f πK) x (hf.symm ▸ WithZero.exp_pos.ne'), hf]
  exact (idealLayerValuation vL πL hπL x e).symm

end LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
