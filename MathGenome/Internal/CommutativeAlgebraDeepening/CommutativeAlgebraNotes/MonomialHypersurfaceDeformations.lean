import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.MonomialHypersurfaceDeformations
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.KoszulFlatDeformationModels
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Ring

noncomputable section

open scoped TensorProduct Pointwise
open Specs.CommutativeAlgebraNotes.MonomialHypersurfaceDeformations
open Specs.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace
  (dual reduction presentation TangentModule EvaluatesRelations reducedRelation c epsilon Coeff)
open Specs.CommutativeAlgebraNotes.SquareZeroLiftTorsor (liftClass)
open Algebra.Extension (Cotangent)
open CommutativeAlgebraNotes.SquareZeroLift

namespace CommutativeAlgebraNotes.MonomialHypersurfaceDeformations

universe u z

variable {k : Type u} [Field k]

private theorem list_equation (k : Type u) [Field k] (m : ℕ) :
    List.ofFn (equation k m) = [X k ^ m] := by
  simp [List.ofFn_succ]

private theorem relationIdeal_eq (k : Type u) [Field k] (m : ℕ) :
    Specs.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace.J (equation k m) =
      Ideal.ofList [X k ^ m] := by
  rw [Ideal.ofList_singleton]
  change Ideal.span (Set.range (fun _ : Fin 1 => X k ^ m)) = _
  rw [Set.range_const]

theorem regular : Regular.{u} := by
  intro k _ m hm
  rw [list_equation, RingTheory.Sequence.isRegular_iff,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff, Ideal.ofList_singleton,
    Submodule.ideal_span_singleton_smul]
  constructor
  · intro a b hab
    change X k ^ m * a = X k ^ m * b at hab
    exact mul_left_cancel₀ (pow_ne_zero m (MvPolynomial.X_ne_zero (R := k) (0 : Fin 1))) hab
  · intro h
    have hmem : (1 : P k) ∈ X k ^ m • (⊤ : Submodule (P k) (P k)) :=
      h ▸ Submodule.mem_top
    obtain ⟨a, _, ha⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mp hmem
    have he := congrArg (MvPolynomial.constantCoeff : P k →+* k) ha
    simp [zero_pow (by omega : m ≠ 0)] at he

private theorem reduce_extend (q : P k) : reduce k (extend k q) = q := by
  have h : (reduce k).comp (extend k) = RingHom.id (P k) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      simp
  exact DFunLike.congr_fun h q

private theorem reduce_equation (m : ℕ) (q : P k) :
    reduce k (perturbedEquation m q) = X k ^ m := by
  simp only [perturbedEquation, map_add, map_pow, map_mul, reduce, MvPolynomial.map_X,
    MvPolynomial.map_C]
  rw [show (dual k).residue.toRingHom (ε k) = 0 from rfl, map_zero, zero_mul, add_zero]

theorem models : Models.{u,z} := by
  intro k _ m hm q
  let g := [perturbedEquation m q]
  let f := [X k ^ m]
  have hg : g.map (MvPolynomial.map (dual k).residue.toRingHom) = f := by
    simpa only [g, f, List.map_cons, List.map_nil, List.cons.injEq, and_true] using
      reduce_equation m q
  have hf : RingTheory.Sequence.IsRegular (P k) f := by
    change RingTheory.Sequence.IsRegular (P k) [X k ^ m]
    rw [← list_equation]
    exact regular hm
  let : Module.Flat (dual k) (Model m q) :=
    KoszulFlatDeformationModels.flatModel (dual k) g f hg hf
  obtain ⟨e, he⟩ := KoszulFlatDeformationModels.canonicalSpecialFibre (dual k) g f hg
  let b : KoszulFlatDeformationModelsSpec.Model f ≃ₐ[k] B k m :=
    Ideal.quotientEquivAlgOfEq _ (relationIdeal_eq k m).symm
  let j : ULift.{z} (Model m q) ≃ₐ[dual k] Model m q := ULift.algEquiv
  let D : Deformation.{u,z} k m := {
    carrier := ULift.{z} (Model m q)
    marking := (Algebra.TensorProduct.congr (AlgEquiv.refl : k ≃ₐ[k] k) j).trans (e.trans b) }
  refine ⟨D, AlgEquiv.refl, fun p => ?_⟩
  change b (e ((1 : k) ⊗ₜ[dual k] Ideal.Quotient.mk _ p)) = _
  rw [he]
  simp [b, reduce]

private theorem jacobian_apply (m : ℕ) (v : Fin 1 → B k m) :
    Specs.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace.jacobian (equation k m) v 0 =
      residue m (slope k m) * v 0 := by
  simp [Specs.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace.jacobian,
    slope]

theorem jacobianIdentification : JacobianIdentification.{u} := by
  intro k _ m
  let d := Specs.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace.jacobian (equation k m)
  let e := LinearEquiv.funUnique (Fin 1) (B k m) (B k m)
  have he (v : Fin 1 → B k m) : e v = v 0 := rfl
  have h : d.range.map e.toLinearMap = (jacobianIdeal k m : Submodule (B k m) (B k m)) := by
    ext x
    constructor
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      rw [LinearEquiv.coe_coe, he, jacobian_apply]
      exact Ideal.mem_span_singleton'.mpr ⟨v 0, mul_comm _ _⟩
    · intro hx
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      refine ⟨d (fun _ => a), ⟨_, rfl⟩, ?_⟩
      rw [LinearEquiv.coe_coe, he, jacobian_apply, mul_comm]
  exact ⟨Submodule.Quotient.equiv _ _ e h, fun _ => rfl⟩

private theorem uniqueEquiv_extend (q : P k) :
    MvPolynomial.uniqueAlgEquiv (dual k) (Fin 1) (extend k q) =
      Polynomial.map (algebraMap k (dual k)) (MvPolynomial.uniqueAlgEquiv k (Fin 1) q) := by
  let e := (MvPolynomial.uniqueAlgEquiv (dual k) (Fin 1)).toRingEquiv.toRingHom
  let e₀ := (MvPolynomial.uniqueAlgEquiv k (Fin 1)).toRingEquiv.toRingHom
  have h : e.comp (extend k) = (Polynomial.mapRingHom (algebraMap k (dual k))).comp e₀ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [e, e₀, MvPolynomial.uniqueAlgEquiv_apply]
    · intro i
      simp [e, e₀, MvPolynomial.uniqueAlgEquiv_apply]
  exact DFunLike.congr_fun h q

theorem polynomialPresentations : PolynomialPresentations.{u} := by
  intro k _ m
  let e := MvPolynomial.uniqueAlgEquiv k (Fin 1)
  have h : Ideal.span {(Polynomial.X : Polynomial k) ^ m} =
      (Specs.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace.J (equation k m)).map
        e.toRingEquiv.toRingHom := by
    rw [relationIdeal_eq, Ideal.ofList_singleton, Ideal.map_span, Set.image_singleton, map_pow]
    simp [e, MvPolynomial.uniqueAlgEquiv_apply]
  let b : B k m ≃ₐ[k] PolynomialFibre k m := Ideal.quotientEquivAlg _ _ e h
  have hb (p : P k) : b (residue m p) = Ideal.Quotient.mk _ (e p) := rfl
  refine ⟨b, hb, ?_, fun q => ?_⟩
  · have ht : polynomialJacobianIdeal k m = (jacobianIdeal k m).map b.toRingEquiv.toRingHom := by
      rw [polynomialJacobianIdeal, jacobianIdeal, Ideal.map_span, Set.image_singleton]
      congr 2
      change _ = b (residue m (slope k m))
      rw [hb]
      simp [slope, e, MvPolynomial.uniqueAlgEquiv_apply]
    exact ⟨Ideal.quotientEquivAlg _ _ b ht, fun _ => rfl⟩
  · let e' := MvPolynomial.uniqueAlgEquiv (dual k) (Fin 1)
    have h' : Ideal.span {(Polynomial.X ^ m + Polynomial.C (ε k) *
        Polynomial.map (algebraMap k (dual k)) (e q))} =
        (Ideal.ofList [perturbedEquation m q]).map e'.toRingEquiv.toRingHom := by
      rw [Ideal.ofList_singleton, Ideal.map_span, Set.image_singleton]
      congr 2
      change _ = e' (perturbedEquation m q)
      rw [perturbedEquation, map_add, map_pow, map_mul]
      have hq := uniqueEquiv_extend q
      change e' (extend k q) = _ at hq
      rw [hq]
      simp [e, e', MvPolynomial.uniqueAlgEquiv_apply]
    exact ⟨Ideal.quotientEquivAlg _ _ e' h', fun _ => rfl⟩


section Coordinates

open private hasSmallLift
  from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace

variable {m : ℕ}

private abbrev pres (k : Type u) [Field k] (m : ℕ) := presentation (equation k m)

private abbrev Chosen (k : Type u) [Field k] (m : ℕ) :=
  (pres k m).ChosenLift.{u,u,u,0,u,u} (c (k := k) (B k m))

private theorem power_residue_zero : residue m (X k ^ m) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [relationIdeal_eq, Ideal.ofList_singleton]
  exact Ideal.subset_span (Set.mem_singleton _)

private def powerRelation (k : Type u) [Field k] (m : ℕ) : (pres k m).Q :=
  ⟨X (dual k) ^ m, by
    change residue m (reduce k (X (dual k) ^ m)) = 0
    simpa only [reduce, map_pow, MvPolynomial.map_X] using power_residue_zero (k := k) (m := m)⟩

private theorem reduced_powerRelation :
    (pres k m).conormalReduction (Cotangent.mk (powerRelation k m)) =
      reducedRelation (equation k m) 0 := by
  rw [Presentation.conormalReduction, Cotangent.map_mk, reducedRelation]
  apply congrArg Cotangent.mk
  apply Subtype.ext
  change (pres k m).reduce ((pres k m).polynomialEquiv (X (dual k) ^ m)) =
    (pres k m).barPolynomialEquiv.symm (X k ^ m)
  apply (pres k m).barPolynomialEquiv.injective
  rw [Presentation.barPolynomialEquiv_reduce, AlgEquiv.apply_symm_apply]
  change reduce k (X (dual k) ^ m) = _
  simp [reduce]

private theorem realizes_power
    (D : Deformation.{u,z} k m) (x y : D)
    (hx : reduction D x = residue m (X k)) (q : P k)
    (hy : reduction D y = residue m q)
    (hpow : x ^ m = -(algebraMap (dual k) D (ε k) * y)) :
    ∃ (L : Chosen k m) (ρ : (pres k m).RelationMaps (c (k := k) (B k m))),
      Specs.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace.Corresponds D L.lift ∧
      L.Realizes ρ ∧
      ρ.val (Cotangent.mk (powerRelation k m)) =
        -(residue m q • c (k := k) (B k m) (epsilon k)) := by
  obtain ⟨L, j, hj⟩ := hasSmallLift (equation k m) D
  let L' : Chosen k m :=
    ⟨L, fun _ => j x, fun i => (hj x).trans (hx.trans (by
      change residue m (X k) = residue m (reduce k (MvPolynomial.X i))
      simp only [reduce, MvPolynomial.map_X, Subsingleton.elim i (0 : Fin 1)]))⟩
  obtain ⟨ρ, hρ, _⟩ := Presentation.evaluation L'
  refine ⟨L', ρ, ⟨j, hj⟩, hρ, (hρ (powerRelation k m)).trans ?_⟩
  have hker : L'.evaluateKer (powerRelation k m) =
      -(L.map (j y) • FlatSquareZeroLifts.coefficientInKernel
        _ L.map L.over (epsilon k)) := by
    rw [L.map_smul]
    apply Subtype.ext
    change MvPolynomial.eval₂Hom (algebraMap (dual k) L.Ring) (fun _ : Fin 1 => j x)
      (X (dual k) ^ m) = -(j y * algebraMap (dual k) L.Ring (ε k))
    rw [map_pow]
    rw [MvPolynomial.eval₂Hom_X']
    change j x ^ m = _
    rw [← map_pow, hpow, map_neg, map_mul, j.commutes, mul_comm]
  change L.marking (L'.evaluateKer (powerRelation k m)) = _
  rw [hker, map_neg, map_smul]
  rw [show L.marking (FlatSquareZeroLifts.coefficientInKernel _ L.map L.over (epsilon k)) =
    c (k := k) (B k m) (epsilon k) from L.induces _]
  rw [hj, hy]

private theorem represents_realizes
    (D : Deformation.{u,z} k m) (q : P k) (h : Represents q D) :
    ∃ (L : Chosen k m) (ρ : (pres k m).RelationMaps (c (k := k) (B k m))),
      Specs.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace.Corresponds D L.lift ∧
      L.Realizes ρ ∧
      ρ.val (Cotangent.mk (powerRelation k m)) =
        -(residue m q • c (k := k) (B k m) (epsilon k)) := by
  obtain ⟨j, hj⟩ := h
  let π : P (dual k) →ₐ[dual k] D :=
    j.toAlgHom.comp (ULift.algEquiv.symm.toAlgHom.comp (Ideal.Quotient.mkₐ _ _))
  have hπ (p : P (dual k)) : reduction D (π p) = residue m (reduce k p) := hj p
  refine realizes_power D (π (X (dual k))) (π (extend k q)) ?_ q ?_ ?_
  · rw [hπ]
    simp [reduce]
  · rw [hπ, reduce_extend]
  · have hrel : π (perturbedEquation m q) = 0 := by
      change j (ULift.up (Ideal.Quotient.mk _ (perturbedEquation m q))) = 0
      have hz : Ideal.Quotient.mk (Ideal.ofList [perturbedEquation m q])
          (perturbedEquation m q) = 0 := by
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        rw [Ideal.ofList_singleton]
        exact Ideal.subset_span (Set.mem_singleton _)
      rw [hz]
      exact map_zero j
    have hε : π (εP k) = algebraMap (dual k) D (ε k) := π.commutes _
    apply eq_neg_of_add_eq_zero_left
    simpa only [perturbedEquation, map_add, map_pow, map_mul, hε] using hrel

private theorem trivial_reduction_tmul (C : Type u) [CommRing C] [Algebra k C] (b : C) :
    let D := Specs.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace.trivial.{u,z} k C
    reduction D (ULift.up ((1 : dual k) ⊗ₜ[k] b)) = b := by
  let R := dual k
  let j : ULift.{z} (R ⊗[k] C) ≃ₐ[R] R ⊗[k] C := ULift.algEquiv
  let e₁ := Algebra.TensorProduct.congr (AlgEquiv.refl : k ≃ₐ[k] k) j
  let e₂ := (Algebra.TensorProduct.assoc k R k k R C).symm
  let h : k ⊗[R] R ≃ₐ[k] k := Algebra.TensorProduct.rid R k k
  let e₃ := Algebra.TensorProduct.congr h (AlgEquiv.refl : C ≃ₐ[k] C)
  let e₄ := Algebra.TensorProduct.lid k C
  change e₄ (e₃ (e₂ (e₁ ((1 : k) ⊗ₜ[R] ULift.up ((1 : R) ⊗ₜ[k] b))))) = b
  have h₁ : e₁ ((1 : k) ⊗ₜ[R] ULift.up ((1 : R) ⊗ₜ[k] b)) =
      (1 : k) ⊗ₜ[R] ((1 : R) ⊗ₜ[k] b) := rfl
  have h₂ : e₂ ((1 : k) ⊗ₜ[R] ((1 : R) ⊗ₜ[k] b)) =
      ((1 : k) ⊗ₜ[R] (1 : R)) ⊗ₜ[k] b := rfl
  have h₃ : e₃ (((1 : k) ⊗ₜ[R] (1 : R)) ⊗ₜ[k] b) = (1 : k) ⊗ₜ[k] b := by
    change (1 : R) • (1 : k) ⊗ₜ[k] b = (1 : k) ⊗ₜ[k] b
    rw [one_smul]
  rw [h₁, h₂, h₃]
  exact one_smul k b

private theorem trivial_realizes :
    ∃ (L : Chosen k m) (ρ : (pres k m).RelationMaps (c (k := k) (B k m))),
      Specs.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace.Corresponds
        (Specs.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace.trivial.{u,z} k (B k m)) L.lift ∧ L.Realizes ρ ∧
      ρ.val (Cotangent.mk (powerRelation k m)) = 0 := by
  let D := Specs.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace.trivial.{u,z} k (B k m)
  let j : ((dual k) ⊗[k] B k m) ≃ₐ[dual k] D := ULift.algEquiv.symm
  let π : B k m →+* D :=
    j.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight : B k m →ₐ[k] (dual k) ⊗[k] B k m).toRingHom
  have hx : reduction D (π (residue m (X k))) = residue m (X k) :=
    trivial_reduction_tmul (B k m) (residue m (X k))
  have hp : (π (residue m (X k))) ^ m = -(algebraMap (dual k) D (ε k) * 0) := by
    rw [← map_pow, ← map_pow, power_residue_zero, map_zero, mul_zero, neg_zero]
  obtain ⟨L, ρ, hL, hρ, hr⟩ :=
    realizes_power D (π (residue m (X k))) 0 hx 0 (by simp) hp
  refine ⟨L, ρ, hL, hρ, hr.trans ?_⟩
  rw [map_zero, zero_smul (B k m) (c (k := k) (B k m) (epsilon k)), neg_zero]

private theorem difference_factors
    (ρ τ : (pres k m).RelationMaps (c (k := k) (B k m))) :
    ∃ g : (pres k m).BarConormal →ₗ[B k m] Coeff (k := k) (B k m),
      τ.val = ρ.val + g.comp (pres k m).conormalReduction := by
  let p := pres k m
  obtain ⟨_, _, E, hE⟩ := Presentation.conormalCokernel p
  have hK : p.K ≤ LinearMap.ker (τ.val - ρ.val) := by
    rintro x ⟨i, hi⟩
    change p.toConormal i = x at hi
    rw [← hi, LinearMap.mem_ker, LinearMap.sub_apply, τ.property, ρ.property, sub_self]
  let d := p.K.liftQ (τ.val - ρ.val) hK
  refine ⟨d.comp E.symm.toLinearMap, ?_⟩
  ext x
  change τ.val x = ρ.val x + d (E.symm (p.conormalReduction x))
  rw [← hE, LinearEquiv.symm_apply_apply]
  change τ.val x = ρ.val x + (τ.val x - ρ.val x)
  abel

set_option maxHeartbeats 1400000 in
theorem coordinates : Coordinates.{u,z} := by
  intro k _ m hm
  let f := equation k m
  obtain ⟨F, a, U, E, G, hF, ha, hE, hG, H, hH, hzero⟩ :=
    CompleteIntersectionTangentSpace.tangentSpace.{u,z} f (regular hm)
  obtain ⟨J, hJ⟩ := jacobianIdentification (k := k) m
  refine ⟨F, a, E.trans J, G.trans J.toEquiv, hF, ha, ?_, ?_, ?_, ?_⟩
  · intro Y
    exact congrArg J (hG Y)
  · change J (G _) = 0
    rw [hG]
    let := a
    rw [vsub_self, map_zero, map_zero]
  · intro q D hD
    obtain ⟨L₀, ρ, hL₀, hρ, hp₀⟩ := trivial_realizes.{u,z} (k := k) (m := m)
    obtain ⟨L, τ, hL, hτ, hp⟩ := represents_realizes D q hD
    obtain ⟨g, hg⟩ := difference_factors ρ τ
    have hgq : U (g (reducedRelation f 0)) = -residue m q := by
      have h := DFunLike.congr_fun hg (Cotangent.mk (powerRelation k m))
      change τ.val _ = ρ.val _ + g ((pres k m).conormalReduction _) at h
      rw [hp, hp₀, zero_add, reduced_powerRelation] at h
      change _ = g (reducedRelation f 0) at h
      rw [← h, map_neg, map_smul, hE.1, smul_eq_mul, mul_one]
    have ht := ha g L₀ L ρ τ hρ hτ hg
    have hv : a.vsub (F (MarkedDeformation.classModel D))
        (F (MarkedDeformation.classModel (Specs.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace.trivial.{u,z} k (B k m)))) =
        (Specs.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace.restriction f).range.mkQ g := by
      rw [hF D _ hL, hF _ _ hL₀, ← ht]
      exact a.vadd_vsub' _ _
    change J (G _) = _
    rw [hG, hv]
    calc
      _ = J ((Specs.CommutativeAlgebraNotes.CompleteIntersectionTangentSpace.jacobian f).range.mkQ
          (fun i => U (g (reducedRelation f i)))) := congrArg J (hE.2 g)
      _ = Ideal.Quotient.mk (jacobianIdeal k m) (U (g (reducedRelation f 0))) :=
        hJ (fun i => U (g (reducedRelation f i)))
      _ = _ := by rw [hgq, map_neg]
  · let Q := G.trans J.toEquiv
    let := Q.addCommGroup
    let := Q.addEquiv.module k
    exact ⟨Q.addEquiv.linearEquiv k, rfl⟩

theorem classification : Classification.{u,z} := by
  intro k _ m hm
  obtain ⟨F, a, E, G, _, _, _, _, hG, _⟩ := coordinates.{u,z} (k := k) hm
  constructor
  · intro D
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (-G (MarkedDeformation.classModel D))
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨D', hD'⟩ := models.{u,z} hm q
    refine ⟨q, D', hD', Quotient.exact (G.injective ?_)⟩
    change G (MarkedDeformation.classModel D) = G (MarkedDeformation.classModel D')
    rw [hG q D' hD']
    change _ = -(Ideal.Quotient.mk (jacobianIdeal k m) (Ideal.Quotient.mk _ q))
    rw [hb, neg_neg]
  · intro q r D D' hD hD'
    have he : D.Isomorphic D' ↔
        MarkedDeformation.classModel D = MarkedDeformation.classModel D' :=
      by
        change (D ≈ D') ↔ (⟦D⟧ : Classes.{u,z} k m) = ⟦D'⟧
        exact ⟨Quotient.sound, Quotient.exact⟩
    rw [he, ← G.injective.eq_iff, hG q D hD, hG r D' hD', neg_inj]
    change (tangentClass m q = tangentClass m r) ↔
      Ideal.Quotient.mk (jacobianIdeal k m) (residue m (q - r)) = 0
    rw [map_sub, map_sub, sub_eq_zero]

end Coordinates


section EquationChanges

private theorem epsilon_mul_self (k : Type u) [Field k] : εP k * εP k = 0 := by
  change MvPolynomial.C (ε k) * MvPolynomial.C (ε k) = 0
  rw [← map_mul]
  exact (congrArg MvPolynomial.C (TrivSqZeroExt.inr_mul_inr k (1 : k) 1)).trans (map_zero _)

private theorem pow_add_squareZero {R : Type*} [CommRing R] (a b : R) (hb : b * b = 0)
    (n : ℕ) : (a + b) ^ n = a ^ n + (n : R) * a ^ (n - 1) * b := by
  cases n with
  | zero => simp
  | succ n =>
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ (a + b), ih, Nat.cast_succ]
      simp only [Nat.add_one_sub_one, pow_succ a]
      calc
        _ = a ^ n * a * a + ((n : R) + 1 + 1) * (a ^ n * a) * b +
            (((n : R) + 1) * a ^ n) * (b * b) := by ring
        _ = _ := by simp only [hb, mul_zero, add_zero, Nat.cast_add, Nat.cast_one]

private theorem epsilon_mul_substitution (u : P k) (p : P (dual k)) :
    εP k * MvPolynomial.aeval (fun _ : Fin 1 => X (dual k) + εP k * extend k u) p =
      εP k * p := by
  let s := MvPolynomial.aeval (R := dual k) (fun _ : Fin 1 => X (dual k) + εP k * extend k u)
  change εP k * s p = εP k * p
  induction p using MvPolynomial.induction_on with
  | C a => exact congrArg (εP k * ·) (s.commutes a)
  | add p q hp hq => rw [map_add, mul_add, hp, hq, mul_add]
  | mul_X p i hp =>
    have hi : s (MvPolynomial.X i) = MvPolynomial.X i + εP k * extend k u := by
      rw [show i = (0 : Fin 1) from Subsingleton.elim _ _, MvPolynomial.aeval_X]
    rw [map_mul, ← mul_assoc, hp, hi]
    calc
      _ = εP k * (p * MvPolynomial.X i) + (p * extend k u) * (εP k * εP k) := by ring
      _ = _ := by rw [epsilon_mul_self, mul_zero, add_zero]

theorem equationChanges : EquationChanges.{u} := by
  intro k _ m q u v
  let s := MvPolynomial.aeval (R := dual k) (fun _ : Fin 1 => X (dual k) + εP k * extend k u)
  have hs : s (εP k) = εP k := s.commutes _
  have hX : s (X (dual k)) = X (dual k) + εP k * extend k u :=
    MvPolynomial.aeval_X _ _
  have sq (p : P (dual k)) : (εP k * p) * (εP k * p) = 0 := by
    rw [mul_mul_mul_comm, epsilon_mul_self, zero_mul]
  have hX' : extend k (X k) = X (dual k) := MvPolynomial.map_X _ _
  have hslope : extend k (slope k m) = (m : P (dual k)) * X (dual k) ^ (m - 1) := by
    rw [slope, map_mul, map_pow, map_natCast, hX']
  have hclass (p : P k) :
      tangentClass m (q + p) = tangentClass m q + tangentClass m p := by
    change Ideal.Quotient.mk (jacobianIdeal k m) (residue m (q + p)) = _
    rw [map_add, map_add]
  refine ⟨?_, ⟨(show IsNilpotent (εP k * extend k v) from ⟨2, by rw [pow_two, sq]⟩).isUnit_one_add,
    ?_⟩, ?_, ?_⟩
  · change s (perturbedEquation m q) = _
    rw [perturbedEquation, map_add, map_pow, map_mul, hX, hs, epsilon_mul_substitution,
      pow_add_squareZero _ _ (sq _) m]
    rw [perturbedEquation, map_add, map_mul, hslope]
    ring
  · rw [perturbedEquation, perturbedEquation, map_add, map_mul, map_pow]
    rw [hX']
    calc
      _ = X (dual k) ^ m + εP k * (extend k q + X (dual k) ^ m * extend k v) +
          (extend k v * extend k q) * (εP k * εP k) := by ring
      _ = _ := by rw [epsilon_mul_self, mul_zero, add_zero]
  · have hz : tangentClass m (slope k m * u) = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [map_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
    rw [hclass, hz, add_zero]
  · have hz : tangentClass m (X k ^ m * v) = 0 := by
      change Ideal.Quotient.mk _ (residue m (X k ^ m * v)) = 0
      rw [map_mul, power_residue_zero, zero_mul, map_zero]
    rw [hclass, hz, add_zero]

theorem boundaryCases : BoundaryCases.{u} := by
  intro k _
  constructor
  · apply Ideal.Quotient.subsingleton_iff.mpr
    simp [jacobianIdeal, slope]
  · intro m hm
    have hcast : (m : P k) = 0 := by
      rw [← map_natCast (MvPolynomial.C : k →+* P k), hm, map_zero]
    have h : jacobianIdeal k m = ⊥ := by
      simp [jacobianIdeal, slope, hcast]
    refine ⟨(Ideal.quotientEquivAlgOfEq _ h).trans (AlgEquiv.quotientBot _ _), fun q => ?_⟩
    simp

end EquationChanges

end CommutativeAlgebraNotes.MonomialHypersurfaceDeformations
