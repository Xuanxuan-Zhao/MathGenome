import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.SquareZeroLiftGraph
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.SquareZeroLiftTorsor
import Mathlib.LinearAlgebra.TensorProduct.Lift

noncomputable section

namespace CommutativeAlgebraNotes.SquareZeroLift.Presentation

open Algebra.Extension
open scoped TensorProduct

universe u v w t n l m

variable {A' : Type u} {A : Type v} {B : Type w} {σ : Type t}
  [CommRing A'] [CommRing A] [CommRing B] [Algebra A B] {e : BaseExtension A' A}
  (p : Presentation e B σ)

open Specs.CommutativeAlgebraNotes.SquareZeroLiftTorsor (liftClass)

/-- The linear map on Hom spaces given by precomposition with the conormal differential. -/
abbrev conormalRestriction (N : Type n) [AddCommGroup N] [Module B N] :=
  Specs.CommutativeAlgebraNotes.SquareZeroLiftTorsor.conormalRestriction p N

/-- The first tangent module for the reduced presentation and coefficients N. -/
abbrev T1 (N : Type n) [AddCommGroup N] [Module B N] :=
  Specs.CommutativeAlgebraNotes.SquareZeroLiftTorsor.T1 p N

variable {N : Type n} [AddCommGroup N] [Module B N] {c : e.CoefficientMap (B := B) N}

private abbrev reduceToExtension : p.extension.Ring →+* p.barExtension.Ring := p.reduce

/-- The map of the reduced polynomial ring to the coefficient module given by a
linear form on its differentials after base change. -/
private def differentialValue (h : p.barExtension.CotangentSpace →ₗ[B] N) (x : p.barExtension.Ring) : N :=
  h (1 ⊗ₜ KaehlerDifferential.D A p.barExtension.Ring x)

private theorem differentialValue_add (h : p.barExtension.CotangentSpace →ₗ[B] N)
    (x y : p.barExtension.Ring) :
    p.differentialValue h (x + y) = p.differentialValue h x + p.differentialValue h y := by
  simp only [differentialValue, map_add, TensorProduct.tmul_add]

private theorem differentialValue_algebraMap (h : p.barExtension.CotangentSpace →ₗ[B] N)
    (a : A) : p.differentialValue h (algebraMap A p.barExtension.Ring a) = 0 := by
  unfold differentialValue
  rw [Derivation.map_algebraMap, TensorProduct.tmul_zero, map_zero]

private theorem differentialValue_mul (h : p.barExtension.CotangentSpace →ₗ[B] N)
    (x y : p.barExtension.Ring) :
    p.differentialValue h (x * y) =
      algebraMap p.barExtension.Ring B x • p.differentialValue h y +
        algebraMap p.barExtension.Ring B y • p.differentialValue h x := by
  have balance (r : p.barExtension.Ring) (z : Ω[p.barExtension.Ring⁄A]) :
      h (1 ⊗ₜ (r • z)) = algebraMap p.barExtension.Ring B r • h (1 ⊗ₜ z) := by
    have hr : r • (1 : B) = algebraMap p.barExtension.Ring B r :=
      (Algebra.algebraMap_eq_smul_one r).symm
    calc
      _ = h ((r • (1 : B)) ⊗ₜ z) :=
        congrArg h (TensorProduct.smul_tmul r (1 : B) z).symm
      _ = h (algebraMap p.barExtension.Ring B r ⊗ₜ z) :=
        congrArg (fun b : B => h (b ⊗ₜ z)) hr
      _ = h (algebraMap p.barExtension.Ring B r • (1 ⊗ₜ z)) :=
        congrArg h (TensorProduct.tmul_eq_smul_one_tmul (R := p.barExtension.Ring) _ z)
      _ = _ := h.map_smul _ _
  simp only [differentialValue, Derivation.leibniz, TensorProduct.tmul_add, map_add, balance]

/-- Every assignment of values on the reduced variables comes from a linear form
on the base-changed polynomial differentials. -/
private theorem exists_differentialValue (a : σ → N) :
    ∃ h : p.barExtension.CotangentSpace →ₗ[B] N,
      ∀ i, p.differentialValue h (p.reduceToExtension (p.polynomialEquiv (MvPolynomial.X i))) = a i := by
  let P := MvPolynomial σ A
  let E : p.barExtension.Ring ≃ₐ[A] P := p.barPolynomialEquiv
  let b : P →ₐ[A] B := p.barMap.comp E.symm.toAlgHom
  let : Module A N := Module.compHom N (algebraMap A B)
  let : Module P N := Module.compHom N b.toRingHom
  let : Module p.barExtension.Ring N :=
    Module.compHom N (algebraMap p.barExtension.Ring B)
  let : IsScalarTower p.barExtension.Ring B N :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : Algebra p.barExtension.Ring P := E.toAlgHom.toAlgebra
  let : IsScalarTower A p.barExtension.Ring P :=
    IsScalarTower.of_algebraMap_eq' E.toAlgHom.comp_algebraMap.symm
  let : IsScalarTower p.barExtension.Ring P N :=
    IsScalarTower.of_algebraMap_smul fun r x => by
      change p.barMap (E.symm (E r)) • x = p.barMap r • x
      rw [E.symm_apply_apply]
  let : IsScalarTower A P N :=
    IsScalarTower.of_algebraMap_smul fun r x => by
      change b (algebraMap A P r) • x = algebraMap A B r • x
      rw [b.commutes]
  let : IsScalarTower A p.barExtension.Ring N :=
    IsScalarTower.of_algebraMap_smul fun r x => by
      change p.barMap (algebraMap A p.Bar r) • x = algebraMap A B r • x
      rw [p.barMap.commutes]
  let d := (MvPolynomial.mkDerivation A a).compAlgebraMap p.barExtension.Ring
  refine ⟨d.liftKaehlerDifferential.liftBaseChange B, fun i => ?_⟩
  rw [differentialValue, LinearMap.liftBaseChange_one_tmul, Derivation.liftKaehlerDifferential_comp_D]
  change MvPolynomial.mkDerivation A a (p.barPolynomialEquiv (p.reduce (p.polynomialEquiv (MvPolynomial.X i)))) = a i
  rw [p.barPolynomialEquiv_reduce]
  change MvPolynomial.mkDerivation A a (MvPolynomial.map e.hom (MvPolynomial.X i)) = a i
  rw [MvPolynomial.map_X, MvPolynomial.mkDerivation_X]

namespace ChosenLift

variable {p} (L : p.ChosenLift.{u,v,w,t,n,l} c)

private def kernelInclusion : N →+ L.lift.Ring :=
  L.lift.ker.subtype.toAddMonoidHom.comp L.lift.marking.symm.toAddMonoidHom

private theorem kernelInclusion_mul (x : L.lift.Ring) (a : N) :
    L.kernelInclusion (L.lift.map x • a) = x * L.kernelInclusion a :=
  congrArg Subtype.val
    ((L.lift.marking.symm.map_smul (L.lift.map x) a).trans
      (L.lift.map_smul x (L.lift.marking.symm a)))

@[simp] private theorem map_kernelInclusion (a : N) :
    L.lift.map (L.kernelInclusion a) = 0 := (L.lift.marking.symm a).property

private theorem kernelInclusion_mul_kernelInclusion (a b : N) :
    L.kernelInclusion a * L.kernelInclusion b = 0 := by
  rw [← L.kernelInclusion_mul, L.map_kernelInclusion, zero_smul, map_zero]

/-- Change the chosen generators using a linear form on the polynomial differentials. -/
abbrev shiftVariables (h : p.barExtension.CotangentSpace →ₗ[B] N) :
    p.ChosenLift.{u,v,w,t,n,l} c where
  lift := L.lift
  variableLifts i := L.variableLifts i +
    L.kernelInclusion (p.differentialValue h (p.reduceToExtension (p.polynomialEquiv (MvPolynomial.X i))))
  overVariable i := by rw [map_add, L.map_kernelInclusion, add_zero, L.overVariable]

private def shiftedEvaluation (h : p.barExtension.CotangentSpace →ₗ[B] N) :
    p.extension.Ring →+* L.lift.Ring where
  toFun x := L.evaluate x + L.kernelInclusion (p.differentialValue h (p.reduceToExtension x))
  map_zero' := by
    rw [map_zero, map_zero, show (0 : p.barExtension.Ring) = algebraMap A p.barExtension.Ring 0 from (map_zero _).symm,
      p.differentialValue_algebraMap, map_zero, add_zero]
  map_one' := by
    rw [map_one, map_one, show (1 : p.barExtension.Ring) = algebraMap A p.barExtension.Ring 1 from (map_one _).symm,
      p.differentialValue_algebraMap, map_zero, add_zero]
  map_add' x y := by
    rw [map_add L.evaluate, map_add p.reduceToExtension, p.differentialValue_add, map_add]
    abel
  map_mul' x y := by
    rw [map_mul L.evaluate, map_mul p.reduceToExtension, p.differentialValue_mul, map_add]
    change L.evaluate x * L.evaluate y +
      (L.kernelInclusion (p.ringHom x • p.differentialValue h (p.reduceToExtension y)) +
       L.kernelInclusion (p.ringHom y • p.differentialValue h (p.reduceToExtension x))) = _
    rw [← L.map_evaluate x, ← L.map_evaluate y,
      L.kernelInclusion_mul, L.kernelInclusion_mul, add_mul, mul_add, mul_add,
      L.kernelInclusion_mul_kernelInclusion, add_zero]
    ring

private theorem evaluate_shiftVariables (h : p.barExtension.CotangentSpace →ₗ[B] N) :
    (L.shiftVariables h).evaluate = L.shiftedEvaluation h := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a) =
      MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a) +
        L.kernelInclusion (p.differentialValue h (p.reduceToExtension (p.polynomialEquiv (MvPolynomial.C a))))
    have hc : p.reduceToExtension (p.polynomialEquiv (MvPolynomial.C a)) =
      algebraMap A p.barExtension.Ring (e.hom a) := (p.algebraMap_bar_hom a).symm
    rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, hc,
      p.differentialValue_algebraMap, map_zero, add_zero]
  · intro i
    change MvPolynomial.eval₂Hom _ _ (MvPolynomial.X i) =
      MvPolynomial.eval₂Hom _ _ (MvPolynomial.X i) +
        L.kernelInclusion (p.differentialValue h (p.reduceToExtension (p.polynomialEquiv (MvPolynomial.X i))))
    rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']

theorem relationMap_shiftVariables (h : p.barExtension.CotangentSpace →ₗ[B] N) :
    (L.shiftVariables h).relationMap = L.relationMap +
      (p.conormalRestriction N h).comp p.conormalReduction := by
  ext x
  obtain ⟨q, rfl⟩ := Cotangent.mk_surjective (P := p.extension) x
  have heval : (L.shiftVariables h).evaluateKer q =
      L.evaluateKer q + L.lift.marking.symm (p.differentialValue h (p.reduceToExtension q.val)) := by
    apply Subtype.ext
    change (L.shiftVariables h).evaluate q.val =
      L.evaluate q.val + L.kernelInclusion (p.differentialValue h (p.reduceToExtension q.val))
    rw [evaluate_shiftVariables]
    rfl
  change (L.shiftVariables h).relationMap (Cotangent.mk q) =
    L.relationMap (Cotangent.mk q) +
      h (p.barExtension.cotangentComplex (p.conormalReduction (Cotangent.mk q)))
  rw [relationMap_mk, relationMap_mk, heval, map_add, LinearEquiv.apply_symm_apply,
    p.conormalReduction_mk, cotangentComplex_mk]
  rfl

/-- Two lists of generators of the same marked lift differ by a change of this form. -/
private theorem exists_shiftVariables (M : p.ChosenLift.{u,v,w,t,n,m} c)
    (f : L.lift.Iso M.lift) :
    ∃ h : p.barExtension.CotangentSpace →ₗ[B] N, Nonempty ((L.shiftVariables h).Iso M) := by
  let z : σ → M.lift.ker := fun i =>
    ⟨M.variableLifts i - f.equiv (L.variableLifts i), by
      change M.lift.map (M.variableLifts i - f.equiv (L.variableLifts i)) = 0
      rw [map_sub, f.over, M.overVariable, L.overVariable, sub_self]⟩
  obtain ⟨h, hh⟩ := p.exists_differentialValue (fun i => M.lift.marking (z i))
  refine ⟨h, ⟨⟨f, fun i => ?_⟩⟩⟩
  change f.equiv (L.variableLifts i +
    L.kernelInclusion (p.differentialValue h (p.reduceToExtension (p.polynomialEquiv (MvPolynomial.X i))))) =
    M.variableLifts i
  rw [hh, map_add]
  have hz := congrArg Subtype.val (M.lift.marking.injective
    ((f.marked (L.lift.marking.symm (M.lift.marking (z i)))).trans
      (L.lift.marking.apply_symm_apply _)))
  change f.equiv (L.kernelInclusion (M.lift.marking (z i))) =
    M.variableLifts i - f.equiv (L.variableLifts i) at hz
  rw [hz]
  abel

end ChosenLift

variable {p}

theorem liftIso_iff (L : p.ChosenLift.{u,v,w,t,n,l} c) (M : p.ChosenLift.{u,v,w,t,n,m} c) :
    Nonempty (L.lift.Iso M.lift) ↔
      ∃ h : p.barExtension.CotangentSpace →ₗ[B] N,
        M.relationMap - L.relationMap = (p.conormalRestriction N h).comp p.conormalReduction := by
  constructor
  · rintro ⟨f⟩
    obtain ⟨h, ⟨F⟩⟩ := L.exists_shiftVariables M f
    refine ⟨h, ?_⟩
    have hF := congrArg Subtype.val F.toRelationMaps_eq
    change (L.shiftVariables h).relationMap = M.relationMap at hF
    rw [← hF, L.relationMap_shiftVariables, add_sub_cancel_left]
  · rintro ⟨h, hh⟩
    have H : (L.shiftVariables h).toRelationMaps = M.toRelationMaps := by
      apply Subtype.ext
      change (L.shiftVariables h).relationMap = M.relationMap
      rw [L.relationMap_shiftVariables, ← hh, add_sub_cancel]
    have F := (L.shiftVariables h).fromGraph.symm
    rw [H] at F
    exact ⟨(F.trans M.fromGraph).toIso⟩

open Specs.CommutativeAlgebraNotes.SquareZeroLiftTorsor (ActsByReduction torsorType liftIsoType classRepresentativeType)

theorem liftIso : liftIsoType.{u,v,w,t,n,l,m} := by
  intro A' A B σ N _ _ _ _ _ _ e p c L M ρ τ hρ hτ
  rw [L.relationMaps_unique ρ hρ, M.relationMaps_unique τ hτ]
  exact liftIso_iff L M

variable (p)

private theorem conormalReduction_toConormal (i : p.IP) :
    p.conormalReduction (p.toConormal i) = 0 := by
  apply LinearMap.mem_ker.mp
  rw [p.conormalReduction_ker]
  exact (p.mem_K _).2 ⟨i, rfl⟩

/-- Adding a map from the reduced conormal preserves the coefficient constraint. -/
def addRelationMap (ρ : p.RelationMaps c) (g : p.BarConormal →ₗ[B] N) :
    p.RelationMaps c :=
  ⟨ρ.val + g.comp p.conormalReduction, fun i => by
    simp only [LinearMap.add_apply, LinearMap.comp_apply, p.conormalReduction_toConormal,
      map_zero, add_zero, ρ.property]⟩

private theorem ker_le_ker_relationSub (ρ τ : p.RelationMaps c) :
    LinearMap.ker p.conormalReduction ≤ LinearMap.ker (ρ.val - τ.val) := by
  rw [p.conormalReduction_ker]
  intro x hx
  obtain ⟨i, rfl⟩ := (p.mem_K x).1 hx
  exact LinearMap.mem_ker.mpr (sub_eq_zero.mpr ((ρ.property i).trans (τ.property i).symm))

/-- The unique reduced conormal map that pulls back to the difference of two solutions. -/
def relationDifference (ρ τ : p.RelationMaps c) : p.BarConormal →ₗ[B] N :=
  (p.conormalReduction.liftOfSurjective p.conormalReduction_surjective)
    ⟨ρ.val - τ.val, p.ker_le_ker_relationSub ρ τ⟩

theorem relationDifference_apply (ρ τ : p.RelationMaps c) (x : p.Conormal) :
    p.relationDifference ρ τ (p.conormalReduction x) = ρ.val x - τ.val x :=
  LinearMap.equivOfSurjective_apply p.conormalReduction_surjective
    (p.ker_le_ker_relationSub ρ τ)

theorem relationDifference_eq_iff (ρ τ : p.RelationMaps c) (g : p.BarConormal →ₗ[B] N) :
    p.relationDifference ρ τ = g ↔ ρ.val - τ.val = g.comp p.conormalReduction := by
  constructor
  · intro h
    ext x
    exact (p.relationDifference_apply ρ τ x).symm.trans
      (congrArg (fun f : p.BarConormal →ₗ[B] N => f (p.conormalReduction x)) h)
  · intro h
    ext x
    obtain ⟨q, rfl⟩ := p.conormalReduction_surjective x
    exact (p.relationDifference_apply ρ τ q).trans (DFunLike.congr_fun h q)

private def relationDifferenceClass (ρ τ : p.RelationMaps c) : p.T1 N :=
  (p.conormalRestriction N).range.mkQ (p.relationDifference ρ τ)

private theorem relationDifferenceClass_add (ρ τ υ : p.RelationMaps c) :
    p.relationDifferenceClass ρ τ + p.relationDifferenceClass τ υ =
      p.relationDifferenceClass ρ υ := by
  unfold relationDifferenceClass
  rw [← map_add]
  congr 1
  ext x
  obtain ⟨q, rfl⟩ := p.conormalReduction_surjective x
  simp only [LinearMap.add_apply, p.relationDifference_apply]
  abel

private theorem relationDifferenceClass_eq_zero (L : p.ChosenLift.{u,v,w,t,n,l} c)
    (M : p.ChosenLift.{u,v,w,t,n,m} c) :
    p.relationDifferenceClass L.toRelationMaps M.toRelationMaps = 0 ↔
      Nonempty (L.lift.Iso M.lift) := by
  change Submodule.Quotient.mk (p := (p.conormalRestriction N).range)
    (p.relationDifference L.toRelationMaps M.toRelationMaps) = 0 ↔ _
  have hswap : Nonempty (L.lift.Iso M.lift) ↔ Nonempty (M.lift.Iso L.lift) :=
    ⟨fun ⟨f⟩ => ⟨f.symm⟩, fun ⟨f⟩ => ⟨f.symm⟩⟩
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range, hswap, liftIso_iff M L]
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨h, (p.relationDifference_eq_iff _ _ _).1 hh.symm⟩
  · rintro ⟨h, hh⟩
    exact ⟨h, ((p.relationDifference_eq_iff _ _ _).2 hh).symm⟩

private theorem relationDifferenceClass_congr
    (L M L' M' : p.ChosenLift.{u,v,w,t,n,max u t n} c)
    (hL : Nonempty (L.lift.Iso L'.lift)) (hM : Nonempty (M.lift.Iso M'.lift)) :
    p.relationDifferenceClass L.toRelationMaps M.toRelationMaps =
      p.relationDifferenceClass L'.toRelationMaps M'.toRelationMaps := by
  have h₁ := p.relationDifferenceClass_add L.toRelationMaps L'.toRelationMaps M.toRelationMaps
  have h₂ := p.relationDifferenceClass_add L'.toRelationMaps M.toRelationMaps M'.toRelationMaps
  rw [(p.relationDifferenceClass_eq_zero L L').2 hL, zero_add] at h₁
  rw [(p.relationDifferenceClass_eq_zero M M').2 hM, add_zero] at h₂
  exact h₁.symm.trans h₂

/-- The difference of two marked lift classes in the first tangent module. -/
def classDifference (Y X : Lift.Classes.{u,v,w,n,max u t n} c) : p.T1 N :=
  Quotient.liftOn₂ Y X
    (fun L M => p.relationDifferenceClass (p.chooseVariables L).toRelationMaps
      (p.chooseVariables M).toRelationMaps)
    (fun _ _ _ _ hL hM => p.relationDifferenceClass_congr _ _ _ _ hL hM)

private theorem classDifference_liftClass (L M : p.ChosenLift.{u,v,w,t,n,max u t n} c) :
    p.classDifference (liftClass L.lift) (liftClass M.lift) =
      p.relationDifferenceClass L.toRelationMaps M.toRelationMaps :=
  p.relationDifferenceClass_congr _ _ _ _
    ⟨Lift.Iso.refl L.lift⟩ ⟨Lift.Iso.refl M.lift⟩

theorem classDifference_add (Z Y X : Lift.Classes.{u,v,w,n,max u t n} c) :
    p.classDifference Z Y + p.classDifference Y X = p.classDifference Z X := by
  obtain ⟨L, rfl⟩ := Quotient.exists_rep Z
  obtain ⟨M, rfl⟩ := Quotient.exists_rep Y
  obtain ⟨W, rfl⟩ := Quotient.exists_rep X
  exact p.relationDifferenceClass_add (p.chooseVariables L).toRelationMaps
    (p.chooseVariables M).toRelationMaps (p.chooseVariables W).toRelationMaps

theorem classDifference_eq_zero (Y X : Lift.Classes.{u,v,w,n,max u t n} c) :
    p.classDifference Y X = 0 ↔ Y = X := by
  obtain ⟨L, rfl⟩ := Quotient.exists_rep Y
  obtain ⟨M, rfl⟩ := Quotient.exists_rep X
  exact (p.relationDifferenceClass_eq_zero (p.chooseVariables L) (p.chooseVariables M)).trans
    ⟨fun h => Quotient.sound h, fun h => Quotient.exact h⟩

theorem classDifference_bijective (X : Lift.Classes.{u,v,w,n,max u t n} c) :
    Function.Bijective (fun Y => p.classDifference Y X) := by
  constructor
  · intro Y Z h
    change p.classDifference Y X = p.classDifference Z X at h
    have hh := p.classDifference_add Y Z X
    rw [h, add_eq_right] at hh
    exact (p.classDifference_eq_zero Y Z).mp hh
  · intro g
    obtain ⟨L, rfl⟩ := Quotient.exists_rep X
    obtain ⟨a, rfl⟩ := (p.conormalRestriction N).range.mkQ_surjective g
    let W := p.chooseVariables L
    let ρ := p.addRelationMap W.toRelationMaps a
    let M := p.ofRelationMaps ρ
    refine ⟨liftClass M.lift, ?_⟩
    change p.classDifference (liftClass M.lift) (liftClass W.lift) = _
    rw [p.classDifference_liftClass]
    change (p.conormalRestriction N).range.mkQ
      (p.relationDifference (p.ofRelationMaps ρ).toRelationMaps W.toRelationMaps) = _
    rw [p.toRelationMaps_ofRelationMaps ρ]
    congr 1
    apply (p.relationDifference_eq_iff _ _ _).2
    change W.toRelationMaps.val + a.comp p.conormalReduction - W.toRelationMaps.val = _
    exact add_sub_cancel_left _ _

/-- Translation on marked lift classes, characterized by its reduced conormal difference. -/
def translate (g : p.T1 N) (X : Lift.Classes.{u,v,w,n,max u t n} c) :
    Lift.Classes.{u,v,w,n,max u t n} c :=
  (Equiv.ofBijective _ (p.classDifference_bijective X)).symm g

@[simp] theorem classDifference_translate (g : p.T1 N)
    (X : Lift.Classes.{u,v,w,n,max u t n} c) :
    p.classDifference (p.translate g X) X = g :=
  (Equiv.ofBijective _ (p.classDifference_bijective X)).apply_symm_apply g

/-- The canonical additive action of the tangent module on the set of marked lifts. -/
@[instance_reducible]
def liftAddAction : AddAction (p.T1 N) (Lift.Classes.{u,v,w,n,max u t n} c) where
  vadd := p.translate
  zero_vadd X := by
    apply (p.classDifference_bijective X).1
    change p.classDifference (p.translate 0 X) X = p.classDifference X X
    rw [p.classDifference_translate]
    exact ((p.classDifference_eq_zero X X).2 rfl).symm
  add_vadd g h X := by
    apply (p.classDifference_bijective X).1
    change p.classDifference (p.translate (g + h) X) X =
      p.classDifference (p.translate g (p.translate h X)) X
    rw [p.classDifference_translate,
      ← p.classDifference_add (p.translate g (p.translate h X)) (p.translate h X) X,
      p.classDifference_translate, p.classDifference_translate]

/-- Every lift, in any universe, has a representative in the graph universe. -/
def representative (L : Lift.{u,v,w,n,l} e c) : Lift.{u,v,w,n,max u t n} e c :=
  (p.ofRelationMaps (p.chooseVariables L).toRelationMaps).lift

def representativeIso (L : Lift.{u,v,w,n,l} e c) : (p.representative L).Iso L :=
  (p.chooseVariables L).fromGraph.toIso

theorem classRepresentative : classRepresentativeType.{u,v,w,t,n,l} := by
  intro A' A B σ N _ _ _ _ _ _ e p c L
  refine ⟨liftClass (p.representative L), fun M => ?_⟩
  constructor
  · intro h
    have hM : Nonempty ((p.representative L).Iso M) := Quotient.exact h
    exact hM.map (p.representativeIso L).symm.trans
  · rintro ⟨f⟩
    exact Quotient.sound ⟨(p.representativeIso L).trans f⟩

/-- The torsor structure given any marked lift. -/
@[instance_reducible]
def liftTorsor (h : Nonempty (Lift.{u,v,w,n,l} e c)) :
    AddTorsor (p.T1 N) (Lift.Classes.{u,v,w,n,max u t n} c) where
  toAddAction := p.liftAddAction
  nonempty := h.map fun L => liftClass (p.representative L)
  vsub := p.classDifference
  vsub_vadd' Y X := (Equiv.ofBijective _ (p.classDifference_bijective X)).symm_apply_apply Y
  vadd_vsub' g X := p.classDifference_translate g X

theorem liftAddAction_actsByReduction :
    ActsByReduction p (p.liftAddAction (c := c)).toVAdd := by
  intro g L M ρ τ hρ hτ hg
  change p.translate ((p.conormalRestriction N).range.mkQ g) (liftClass L.lift) =
    liftClass M.lift
  apply (p.classDifference_bijective (liftClass L.lift)).1
  change p.classDifference (p.translate ((p.conormalRestriction N).range.mkQ g)
    (liftClass L.lift)) (liftClass L.lift) = p.classDifference (liftClass M.lift) (liftClass L.lift)
  rw [p.classDifference_translate, p.classDifference_liftClass,
    ← L.relationMaps_unique ρ hρ, ← M.relationMaps_unique τ hτ]
  unfold relationDifferenceClass
  congr 1
  symm
  apply (p.relationDifference_eq_iff τ ρ g).2
  rw [hg, add_sub_cancel_left]

/-- Proposition 6.2, the torsor of marked square-zero lifts. -/
theorem torsor : torsorType.{u,v,w,t,n,l} := by
  intro A' A B σ N _ _ _ _ _ _ e p c h
  exact ⟨p.liftTorsor h, p.liftAddAction_actsByReduction⟩

end CommutativeAlgebraNotes.SquareZeroLift.Presentation
