import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.SteinbergFrobeniusPushforward
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagLineBundle
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagRelativeFrobeniusAtlas
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.AssociatedFlagLineSheaves
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.LinePushforwardProjection
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.RestrictedSimplicity
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.SteinbergDimension
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Nullstellensatz
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Coalgebra WithConv
open scoped CategoryTheory.MonObj TensorProduct

universe u

noncomputable section

namespace LinearAlgebraicGroups.SteinbergFrobeniusPushforward

open _root_.LinearAlgebraicGroups.Specs
open Specs.SteinbergFrobeniusPushforward
open Specs.CharacterDescent (Character)
open Specs.FlagLineBundle
open Specs.SimpleClassification (SocleModel)

open private tensorPoint leftCoactionHom leftEval constructAssociatedBundle coversWithSections_of_local
  linePointEquiv linePointEquiv_apply linePoint_comp restrictToChart restrictToChart_eval
  flagCover_and_polynomialChart
  coordinateFunction torsorDifference torsorDifference_value
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagLineBundle

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
  {P : OppositeBorelPair G} {U : ClosedSubgroup P.positive.group}
  {χ : Character P.torus.group}

set_option backward.isDefEq.respectTransparency false in
private theorem socleFunction_coaction (S : SocleModel P U χ) (s : S.socle) :
    (socleFunction S).rTensor S.A (S.socleCoaction.coaction s) =
      leftCoactionHom S.A (socleFunction S s) := by
  unfold socleFunction
  let i := S.inducedBasis.equivFun.symm.toLinearMap.comp S.socle.subtype
  let j := (covariantFunctions S.restriction S.coordinate).subtype
  change (j.comp i).rTensor S.A (S.socleCoaction.coaction s) =
    leftCoactionHom S.A (j (i s))
  have h₁ := DFunLike.congr_fun S.socleCoaction_spec s
  have h₂ := DFunLike.congr_fun S.leftTranslation (i s)
  rw [LinearMap.rTensor_comp, LinearMap.comp_apply]
  change j.rTensor S.A (i.rTensor S.A (S.socleCoaction.coaction s)) = _
  change i.rTensor S.A (S.socleCoaction.coaction s) = S.inducedCoaction.coaction (i s) at h₁
  rw [h₁]
  exact h₂

/-- The nonzero socle has nonzero evaluation at every point of the group
over every extension field. -/
theorem evaluationOnGroup : EvaluationOnGroup.{u} := by
  intro k _ G P U χ S K _ _ g
  classical
  by_contra! h
  let R : TestAlgebra k := CommAlgCat.of k (K ⊗[k] S.A)
  let e : S.A →ₐ[k] R := Algebra.TensorProduct.includeLeft.comp g
  let i : S.A →ₐ[k] R := Algebra.TensorProduct.includeRight
  let := convolutionGroup S.A R
  let t : WithConv (S.A →ₐ[k] R) := toConv e * (toConv i)⁻¹
  have ht : t⁻¹ * toConv e = toConv i := by simp [t]
  have he : e.toLinearMap.comp (socleFunction S) = 0 := by
    ext s
    change (Algebra.TensorProduct.includeLeft : K →ₐ[k] R) (g (socleFunction S s)) = 0
    rw [h s, map_zero]
  have htensor (v : S.socle ⊗[k] S.A) :
      tensorPoint e t.ofConv ((socleFunction S).rTensor S.A v) = 0 := by
    have hf : (tensorPoint e t.ofConv).toLinearMap.comp ((socleFunction S).rTensor S.A) = 0 := by
      apply TensorProduct.ext'
      intro s a
      rw [LinearMap.comp_apply, LinearMap.rTensor_tmul]
      change e (socleFunction S s) * t.ofConv a = 0
      have hz := DFunLike.congr_fun he s
      change e (socleFunction S s) = 0 at hz
      rw [hz, zero_mul]
    exact DFunLike.congr_fun hf v
  let s := S.highestVector
  have hz : i (socleFunction S s) = 0 := by
    have hEval := leftEval (R := R) e t.ofConv (socleFunction S s)
    change _ = (t⁻¹ * toConv e) (socleFunction S s) at hEval
    rw [ht, ← socleFunction_coaction, htensor] at hEval
    exact hEval.symm
  have hi : Function.Injective i :=
    Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective
  have hs : Function.Injective (socleFunction S) :=
    Subtype.val_injective.comp (S.inducedBasis.equivFun.symm.injective.comp Subtype.val_injective)
  have hz' : s = 0 := hs (hi (by simpa only [map_zero] using hz))
  exact S.highest_primitive.1 (congrArg Subtype.val hz')

set_option backward.isDefEq.respectTransparency false in
/-- No geometric point of the flag is a common zero of the socle sections. -/
theorem bundleEvaluationNonvanishing : BundleEvaluationNonvanishing.{u} := by
  intro k _ G P U χ S Q a L E hE K _ _ y
  let R := CommAlgCat.of k K
  let x₀ : ((testSpec k).obj (op R)).left := (default : PrimeSpectrum K)
  obtain ⟨V, b, hb, hcover⟩ :=
    (flagCover_and_polynomialChart Q).1 (y.left x₀)
  have : IsOpenImmersion (b ≫ Q.projection).left := hb
  have hrange : Set.range y.left ⊆ Set.range (b ≫ Q.projection).left := by
    rintro _ ⟨x, rfl⟩
    have hx : x = x₀ := Subsingleton.elim (α := PrimeSpectrum K) x x₀
    rwa [hx]
  let v : (testSpec k).obj (op R) ⟶ V :=
    Over.homMk (IsOpenImmersion.lift (b ≫ Q.projection).left y.left hrange) (by
      rw [← Over.w (b ≫ Q.projection), ← Category.assoc, IsOpenImmersion.lift_fac, Over.w])
  let g := v ≫ b
  have hg : g ≫ Q.projection = y := by
    apply Over.OverMorphism.ext
    exact IsOpenImmersion.lift_fac (b ≫ Q.projection).left y.left hrange
  let f := restrictToChart S.groupIso g
  obtain ⟨s, hs⟩ := evaluationOnGroup S K f
  refine ⟨g, s, hg, ?_⟩
  let sectionOfS := E.symm (S.inducedBasis.equivFun.symm (s : S.I → k))
  have hsection : y ≫ sectionOfS.val =
      prod.lift g (linePoint R (f (socleFunction S s))) ≫ L.trivialization := by
    rw [← hg, Category.assoc, hE, ← Category.assoc]
    have he : (E sectionOfS : S.A) = socleFunction S s := by
      change (↑(E (E.symm _)) : S.A) = _
      rw [Equiv.apply_symm_apply]
      rfl
    rw [he]
    congr 1
    apply prod.hom_ext
    · simp
    · simpa only [Category.assoc, prod.lift_snd, coordinateFunction] using
        restrictToChart_eval S.groupIso g (socleFunction S s)
  change y ≫ sectionOfS.val ≠ _
  rw [hsection]
  intro hz
  have hl : prod.lift g (linePoint R (f (socleFunction S s))) =
      prod.lift g (linePoint R 0) :=
    L.trivializes.hom_ext (by simp) hz
  apply hs
  apply (linePointEquiv R).injective
  simpa only [linePointEquiv_apply, prod.lift_snd] using
    congrArg (· ≫ prod.snd) hl

section Coefficients

variable {C V : Type u} [AddCommGroup C] [Module k C] [Coalgebra k C]
  [AddCommGroup V] [Module k V]

private theorem comul_coefficient (δ : RightComodule k C V) (ℓ : V →ₗ[k] k) (x : V) :
    comul (R := k) (coefficientMap δ ℓ x) =
      (coefficientMap δ ℓ).rTensor C (δ.coaction x) := by
  -- Apply the functional to the first factor of the coassociativity identity.
  let contract : V ⊗[k] (C ⊗[k] C) →ₗ[k] C ⊗[k] C :=
    (TensorProduct.lid k (C ⊗[k] C)).toLinearMap.comp (ℓ.rTensor _)
  have hleft : contract.comp ((TensorProduct.assoc k V C C).toLinearMap.comp
      (δ.coaction.rTensor C)) = (coefficientMap δ ℓ).rTensor C := by
    apply TensorProduct.ext'
    intro v c
    simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul]
    unfold coefficientMap
    simp only [LinearMap.comp_apply]
    generalize δ.coaction v = w
    refine w.inductionOn (fun v' c' ↦ ?_) (fun x y hx hy ↦ ?_)
    · simp [contract, TensorProduct.assoc_tmul, TensorProduct.smul_tmul']
    · rw [TensorProduct.add_tmul, map_add, map_add, hx, hy, map_add, map_add, TensorProduct.add_tmul]
  have hright : contract.comp ((comul (R := k) (A := C)).lTensor V) =
      (comul (R := k) (A := C)).comp
        ((TensorProduct.lid k C).toLinearMap.comp (ℓ.rTensor C)) := by
    apply TensorProduct.ext'
    intro v c
    simp [contract]
  have h := congrArg contract (δ.coassoc x)
  exact (DFunLike.congr_fun hright (δ.coaction x)).symm.trans
    (h.symm.trans (DFunLike.congr_fun hleft (δ.coaction x)))

private theorem counit_coefficient (δ : RightComodule k C V) (ℓ : V →ₗ[k] k) (x : V) :
    counit (R := k) (coefficientMap δ ℓ x) = ℓ x := by
  have h :
      (counit (R := k) (A := C)).comp
          ((TensorProduct.lid k C).toLinearMap.comp (ℓ.rTensor C)) =
        ℓ.comp ((TensorProduct.rid k V).toLinearMap.comp
          ((counit (R := k) (A := C)).lTensor V)) := by
    apply TensorProduct.ext'
    intro v c
    simp [mul_comm]
  exact (DFunLike.congr_fun h (δ.coaction x)).trans (congrArg ℓ (δ.counit x))

/-- Simplicity forces a nonzero orbit coefficient map to have zero kernel. -/
theorem simpleCoefficientInjection : SimpleCoefficientInjection.{u} := by
  intro k C V _ _ _ _ _ _ δ ℓ hSimple hℓ
  let f := coefficientMap δ ℓ
  have hk : δ.IsSubcomodule (LinearMap.ker f) := by
    intro x
    have hExact : Function.Exact (LinearMap.ker f).subtype f :=
      LinearMap.exact_subtype_ker_map f
    rw [← (Module.Flat.rTensor_exact C hExact).linearMap_ker_eq]
    rw [LinearMap.mem_ker, ← comul_coefficient]
    exact (congrArg (comul (R := k) (A := C)) x.property).trans (map_zero _)
  apply LinearMap.ker_eq_bot.mp
  rcases hSimple _ hk with h | h
  · exact h
  · exfalso
    apply hℓ
    ext x
    have hx : x ∈ LinearMap.ker f := h.symm ▸ Submodule.mem_top
    rw [LinearMap.zero_apply, ← counit_coefficient δ ℓ x]
    exact (congrArg (counit (R := k) (A := C)) hx).trans (map_zero _)

end Coefficients

private theorem tensorEvaluation_eq {A C V : Type u} [CommRing A] [CommRing C]
    [Algebra k A] [Algebra k C] [AddCommGroup V] [Module k V]
    (i : V →ₗ[k] A) (g : A →ₐ[k] k) (f : A →ₐ[k] C) :
    (tensorPoint ((Algebra.ofId k C).comp g) f).toLinearMap.comp (i.rTensor A) =
      (TensorProduct.lid k C).toLinearMap.comp
        (((g.toLinearMap.comp i).rTensor C).comp (f.toLinearMap.lTensor V)) := by
  apply TensorProduct.ext'
  intro v a
  rw [LinearMap.comp_apply, LinearMap.rTensor_tmul]
  change (algebraMap k C (g (i v))) * f a =
    TensorProduct.lid k C (((g.toLinearMap.comp i).rTensor C) (v ⊗ₜ[k] f a))
  rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
  exact (Algebra.smul_def (g (i v)) (f a)).symm

set_option maxHeartbeats 900000 in
set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- Evaluation on the scheme kernel orbit detects every nonzero socle vector. -/
theorem kernelOrbitInjection : KernelOrbitInjection.{u} := by
  intro k _ _ p r _ _ hr G P _ U hU ρ hρ S F hF h g
  let χ := Additive.toMul ((p ^ r - 1) • Additive.ofMul ρ)
  have hpair α c hc : Specs.CharacterPairing.pairing P.torus.group χ c =
      ((p ^ r - 1 : ℕ) : ℤ) :=
    LinearAlgebraicGroups.Representation.SteinbergDimension.steinbergWeight_pairing P ρ hρ _ α c hc
  have hdom : Specs.InducedNonvanishing.Dominant P χ := by
    intro α c hc
    rw [hpair α c hc]
    exact Int.natCast_nonneg _
  have hres (α : Specs.RootWeightAction.SimpleRoot P.torus P.positive)
      (c : Specs.CharacterDescent.Cocharacter P.torus.group)
      (hc : Specs.AbstractPairing.IsAttachedCoroot P.torus α.val c) :
      Specs.CharacterPairing.pairing P.torus.group χ c < (↑(p ^ r) : ℤ) := by
    rw [hpair α c hc]
    have hp : 0 < p ^ r := Nat.pow_pos (Fact.out : p.Prime).pos
    omega
  letI := h
  let C := hopfQuotient S.A (kernelIdeal F)
  let q := hopfQuotientMap S.A (kernelIdeal F)
  obtain ⟨δ, hδ, _, hsimple⟩ :=
    LinearAlgebraicGroups.Representation.RestrictedSimplicity.simplicity p r hr P U hU χ hdom hres S F hF h
  let ℓ := g.toLinearMap.comp (socleFunction S)
  obtain ⟨s, hs⟩ := evaluationOnGroup S k g
  have hℓ : ℓ ≠ 0 := fun hz ↦ hs (DFunLike.congr_fun hz s)
  have hinj := simpleCoefficientInjection δ ℓ hsimple hℓ
  let R : TestAlgebra k := CommAlgCat.of k C
  let e : S.A →ₐ[k] R := (Algebra.ofId k C).comp g
  let f : S.A →ₐ[k] R := q.hom.toAlgHom
  let := convolutionGroup S.A R
  have hcomp : (tensorPoint e f).toLinearMap.comp ((socleFunction S).rTensor S.A) =
      (TensorProduct.lid k C).toLinearMap.comp
        ((ℓ.rTensor C).comp (f.toLinearMap.lTensor S.socle)) := by
    exact tensorEvaluation_eq (socleFunction S) g f
  have heq (s : S.socle) :
      ((toConv f)⁻¹ * toConv e : WithConv (S.A →ₐ[k] R)) (socleFunction S s) =
        coefficientMap δ ℓ s := by
    rw [← leftEval (R := R) e f, ← socleFunction_coaction]
    have h := DFunLike.congr_fun hcomp (S.socleCoaction.coaction s)
    unfold coefficientMap
    rw [hδ, LinearMap.comp_apply]
    exact h
  change Function.Injective fun s : S.socle ↦
    ((toConv f)⁻¹ * toConv e : WithConv (S.A →ₐ[k] R)) (socleFunction S s)
  simpa only [heq] using hinj

section PolynomialPower

open MvPolynomial
open scoped BigOperators

private theorem expandedExponent_eq {n q : ℕ} (hq : 0 < q) {i j : Fin n → Fin q}
    {d e : Fin n →₀ ℕ}
    (h : q • d + boundedExponents i = q • e + boundedExponents j) :
    d = e ∧ i = j := by
  have he (v : Fin n) : q * d v + (i v).val = q * e v + (j v).val := by
    simpa [boundedExponents] using congrArg (fun m : Fin n →₀ ℕ ↦ m v) h
  have hij : i = j := by
    ext v
    simpa [Nat.add_mod, Nat.mod_eq_of_lt (i v).isLt, Nat.mod_eq_of_lt (j v).isLt]
      using congrArg (· % q) (he v)
  refine ⟨?_, hij⟩
  subst j
  ext v
  exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_right_cancel (he v))

private theorem coeff_expandedMonomial {n q : ℕ} (hq : 0 < q)
    (f : MvPolynomial (Fin n) k) (i j : Fin n → Fin q) (d : Fin n →₀ ℕ) :
    (expand q f * monomial (boundedExponents i) 1).coeff (q • d + boundedExponents j) =
      if i = j then f.coeff d else 0 := by
  classical
  by_cases h : i = j
  · subst j
    simp [hq.ne']
  · rw [ite_eq_right h]
    induction f using MvPolynomial.induction_on' with
    | monomial e a =>
      rw [expand_monomial, monomial_mul_monomial, mul_one, coeff_monomial]
      split
      · rename_i he
        exact (h (expandedExponent_eq hq he).2).elim
      · rfl
    | add f g hf hg =>
      have hfg : expand q (f + g) = expand q f + expand q g :=
        map_add (expand q) f g
      rw [hfg, add_mul, AddMonoidAlgebra.coeff_add]
      change (expand q f * monomial (boundedExponents i) 1).coeff
          (q • d + boundedExponents j) +
        (expand q g * monomial (boundedExponents i) 1).coeff
          (q • d + boundedExponents j) = 0
      rw [hf, hg, add_zero]

set_option maxHeartbeats 650000 in
set_option linter.style.haveILetI false in
/-- The finitely many residue monomials give the affine power map its
free-module rank. -/
theorem polynomialPowerBasis : PolynomialPowerBasis.{u} := by
  intro k _ n q hq
  classical
  let M := MvPolynomial (Fin n) k
  let T := ULift.{0} M
  let alg : Algebra M T := (polynomialPowerMap k n q).toAlgebra
  letI : Algebra M T := alg
  letI : Module M T := alg.toModule
  letI : SMul M T := alg.toSMul
  let v : (Fin n → Fin q) → T := fun i ↦ ULift.up (monomial (boundedExponents i) 1)
  have hv (f : M) (i : Fin n → Fin q) : (f • v i).down =
      expand q f * monomial (boundedExponents i) 1 := by
    change ((polynomialPowerMap k n q f) * v i).down = _
    rfl
  have hli : LinearIndependent M v := by
    rw [Fintype.linearIndependent_iff]
    intro f hf j
    ext d
    let e : T ≃+* M := ULift.ringEquiv
    have he (x : T) : e x = x.down := rfl
    have h := congrArg (fun x : T ↦ (e x).coeff (q • d + boundedExponents j)) hf
    change (e (∑ i, f i • v i)).coeff (q • d + boundedExponents j) =
      (e 0).coeff (q • d + boundedExponents j) at h
    simp only [map_sum, ← MvPolynomial.coeffAddMonoidHom_apply, map_sum, map_zero] at h
    change (f j).coeff d = 0
    simpa only [MvPolynomial.coeffAddMonoidHom_apply, he, hv, coeff_expandedMonomial hq,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h
  have hsp : (⊤ : Submodule M T) ≤ Submodule.span M (Set.range v) := by
    intro ⟨f⟩ hf
    clear hf
    change (ULift.up f : T) ∈ Submodule.span M (Set.range v)
    induction f using MvPolynomial.induction_on' with
    | monomial d a =>
      let j : Fin n → Fin q := fun i ↦ ⟨d i % q, Nat.mod_lt _ hq⟩
      let e : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i ↦ d i / q)
      have hd : q • e + boundedExponents j = d := by
        ext i
        simpa [e, j, boundedExponents, add_comm] using Nat.mod_add_div (d i) q
      have h : (monomial e a : M) • v j = ULift.up (monomial d a) := by
        apply ULift.ext
        rw [hv, expand_monomial, monomial_mul_monomial, mul_one, hd]
      rw [← h]
      exact Submodule.smul_mem _ (monomial e a) (Submodule.subset_span ⟨j, rfl⟩)
    | add f g hf hg => exact Submodule.add_mem _ hf hg
  refine ⟨Module.Basis.mk hli hsp, ?_, by simp⟩
  intro i
  rw [Module.Basis.mk_apply]

set_option linter.style.haveILetI false in
/-- The basis of residue monomials computes the scheme-theoretic degree
of the affine power map at every point. -/
theorem polynomialPowerDegree : PolynomialPowerDegree.{u} := by
  intro k _ n q hq
  classical
  let R := MvPolynomial (Fin n) k
  let T := ULift.{0} R
  letI : Algebra R T := (polynomialPowerMap k n q).toAlgebra
  letI : Module R T := (polynomialPowerMap k n q).toAlgebra.toModule
  obtain ⟨b, _, hcard⟩ := polynomialPowerBasis k n q hq
  letI : Module.Finite R T := Module.Finite.of_basis b
  letI : Module.Free R T := Module.Free.of_basis b
  letI : Module.Flat R T := Module.Flat.of_free
  have hFinite : (polynomialPowerMap k n q).Finite :=
    (RingHom.finite_algebraMap (A := R) (B := T)).mpr inferInstance
  have hFlat : (polynomialPowerMap k n q).Flat :=
    RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat R T)
  refine ⟨(IsFinite.SpecMap_iff _).mpr hFinite, Flat.SpecMap_iff.mpr hFlat, ?_⟩
  intro x
  change (Spec.map (CommRingCat.ofHom (algebraMap R T))).finrank x = _
  refine (Scheme.Hom.finrank_SpecMap_algebraMap R T x).trans ?_
  let z : PrimeSpectrum R := x
  have hRank := Module.rankAtStalk_eq_finrank_tensorProduct (M := T) z
  exact hRank.trans
    ((Module.finrank_eq_card_basis (b.baseChange (Localization.AtPrime z.asIdeal))).trans hcard)

/-- The determinant is a unit if it is nonzero at every closed point. -/
theorem polynomialMatrixCriterion : PolynomialMatrixCriterion.{u} := by
  intro k I _ _ _ _ n A hA
  apply (Matrix.isUnit_iff_isUnit_det A).mpr
  by_contra h
  obtain ⟨m, hm, hle⟩ :=
    Ideal.exists_le_maximal (Ideal.span {A.det}) (mt Ideal.span_singleton_eq_top.mp h)
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal k hm
  have hdet : MvPolynomial.aeval x A.det = (0 : k) := by
    apply (MvPolynomial.mem_vanishingIdeal_singleton_iff x A.det).mp
    rw [← hx]
    exact hle (Ideal.subset_span (Set.mem_singleton A.det))
  have hUnit := Matrix.mulVec_injective_iff_isUnit.mp (hA x)
  have hNe := ((Matrix.isUnit_iff_isUnit_det _).mp hUnit).ne_zero
  apply hNe
  exact ((MvPolynomial.aeval x).toRingHom.map_det A).symm.trans hdet

end PolynomialPower

section FlagFrobenius

open Specs.FlagRelativeFrobeniusAtlas
open LinearAlgebraicGroups.FlagRelativeFrobeniusAtlas
  (flagFrobeniusCellCover relativeFrobenius_unique)
open QuotientEmbedding (Presentation)
open CategoryTheory.MonoidalCategory

set_option backward.isDefEq.respectTransparency false in
private theorem powerMorphism_degree (k : Type u) [Field k] (n q : ℕ) (hq : 0 < q) :
    let m := (powerMorphism (k := k) q n).left
    IsFinite m ∧ Flat m ∧ ∀ y, m.finrank y = q ^ n := by
  let R := MvPolynomial (Fin n) k
  let e := Scheme.Spec.mapIso (ULift.ringEquiv : ULift.{0} R ≃+* R).symm.toCommRingCatIso.op
  have : IsIso e.hom := e.isIso_hom
  let m := (powerMorphism (k := k) q n).left
  have he : e.hom ≫ m = Spec.map (CommRingCat.ofHom (polynomialPowerMap k n q)) := by
    change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (powerMap q n).toRingHom) = _
    rw [← Spec.map_comp]
    rfl
  obtain ⟨hFinite, hFlat, hRank⟩ := polynomialPowerDegree k n q hq
  have hmFinite : IsFinite m := by
    rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) e.hom, he]
    exact hFinite
  have hmFlat : Flat m := by
    rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Flat) e.hom, he]
    exact hFlat
  refine ⟨hmFinite, hmFlat, fun y ↦ ?_⟩
  change m.finrank y = _
  rw [← Scheme.Hom.finrank_comp_left_of_isIso e.hom m, he]
  exact hRank y

private theorem property_on_pullback_chart (B : MorphismProperty Scheme.{u}) [B.RespectsIso]
    {A X Y T : Scheme.{u}} {m : A ⟶ T} {i : A ⟶ X} {j : T ⟶ Y} {f : X ⟶ Y}
    (h : IsPullback m i j f) (hm : B m) : B (pullback.snd f j) :=
  (MorphismProperty.cancel_left_of_respectsIso (P := B) h.flip.isoPullback.hom _).mp
    (h.flip.isoPullback_hom_snd.symm ▸ hm)

set_option backward.isDefEq.respectTransparency false in
theorem flagFrobeniusDegree : FlagFrobeniusDegree.{u} := by
  intro k _ _ p r _ _ hr G P Q F hF
  obtain ⟨F', C, e, hF', hn, hdim, hcharts, hcover⟩ := flagFrobeniusCellCover p r Q hr
  have h : F = F' := (relativeFrobenius_unique p r Q.scheme F hF).trans
    (relativeFrobenius_unique p r Q.scheme F' hF').symm
  subst F'
  let j (a : 𝟙_ (SchemeOver k) ⟶ G.val.X) :=
    (e.hom ≫ (twist p r).map (translatedChart Q C a)).left
  let m := (powerMorphism (k := k) (p ^ r) C.order.length).left
  have sq (a) : IsPullback m (translatedChart Q C a).left (j a) F.left :=
    (hcharts a).2.2.2
  let cover : ((twist p r).obj Q.scheme).left.OpenCover :=
    Scheme.Cover.mkOfCovers _ (fun _ ↦ (affineChart k C.order.length).left) j hcover
      (fun a ↦ (hcharts a).2.1)
  obtain ⟨hmFinite, hmFlat, hmRank⟩ :=
    powerMorphism_degree k C.order.length (p ^ r) (Nat.pow_pos (Fact.out : p.Prime).pos)
  have hfFinite : IsFinite F.left := by
    apply (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite) cover).mpr
    intro a
    exact property_on_pullback_chart (@IsFinite) (sq a) hmFinite
  have hfFlat : Flat F.left := by
    apply (IsZariskiLocalAtTarget.iff_of_openCover (P := @Flat) cover).mpr
    intro a
    exact property_on_pullback_chart (@Flat) (sq a) hmFlat
  refine ⟨hdim.trans (congrArg _ hn), hfFinite, hfFlat, fun y ↦ ?_⟩
  obtain ⟨a, z, rfl⟩ := hcover y
  exact (Scheme.Hom.finrank_of_isPullback _ _ _ _ (sq a).flip z).symm.trans
    ((hmRank z).trans (congrArg ((p ^ r) ^ ·) hn))

end FlagFrobenius

section LinePullback

open Specs.AssociatedFlagLineSheaves
open LinearAlgebraicGroups.FlagRelativeFrobeniusAtlas
  (relativeFrobenius relativeFrobenius_formula relativeFrobenius_unique absoluteFrobenius)
open LinearAlgebraicGroups.AssociatedFlagLineSheaves (chartCover chartIso)
open QuotientEmbedding (Presentation)
open Scheme.Modules

open private characterFunction_projected_product characterFunction_characterComp
  characterFunction_one functionsOver_smul chartValue_eq lift_in_open isIso_of_open_restrictions
  restrict_adjoint_isIso local_adjoint_isIso restrictTopSections
  restrictDirectImageHom restrictDirectImageHom_top chartIso_top
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.AssociatedFlagLineSheaves
open private wholeGroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.AssociatedFlagLineSheaves

variable (p r : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
  {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme} {b : BorelProjection P}
  {L : AssociatedBundle Q a b χ} {Lq : AssociatedBundle Q a b (χ ^ (p ^ r))}
  (M : SectionRealization L) (Mq : SectionRealization Lq)

/-- In the model with unchanged underlying scheme, the pullback on an open
is the iterated power map on sections of its structure sheaf. -/
private theorem frobenius_app (X : SchemeOver k) (U : X.left.Opens) (x : Γ(X.left, U)) :
    (absoluteFrobenius p r X).app U x = x ^ (p ^ r) := by
  have h := (relativeFrobenius_formula p r X).2 U (le_refl U) x
  exact (congrArg (fun f : Γ(X.left, U) ⟶ Γ(X.left, U) ↦ f x)
    (Scheme.Hom.appLE_eq_app (absoluteFrobenius p r X))).symm.trans h

omit [IsAlgClosed k] in
private theorem projectedCharacter_pow {T : SchemeOver k} (t : T ⟶ P.negative.group.X)
    (n : ℕ) :
    characterFunction (b.projection ≫ χ ^ n) t =
      characterFunction (b.projection ≫ χ) t ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, characterFunction_characterComp]
    change characterFunction (H := specGroup _) (𝟙 _)
      ((t ≫ b.projection.hom.hom) ≫ (1 : Character P.torus.group).hom.hom) = 1
    rw [Grp.Hom.hom_one, Mon.Hom.hom_one, MonObj.comp_one]
    exact characterFunction_one (H := wholeGroup _) (𝟙 _) T
  | succ n ih =>
    rw [pow_succ, characterFunction_projected_product, ih, pow_succ]

omit [Fact p.Prime] [CharP k p] [IsAlgClosed k] in
private theorem power_covariant {U : Q.scheme.left.Opens}
    {f : Γ(G.val.X.left, Q.projection.left ⁻¹ᵁ U)}
    (hf : IsCovariantOn Q b χ U f) :
    IsCovariantOn Q b (χ ^ (p ^ r)) U (f ^ (p ^ r)) := by
  intro T g t hg ht
  simp only [evalOn, map_pow]
  have he := hf T g t hg ht
  unfold evalOn at he
  rw [he, mul_pow, projectedCharacter_pow]

private def powerSection (U : Q.scheme.left.Opens) (s : Γ(M.sheaf, U)) :
    Γ(Mq.sheaf, U) :=
  ((Mq.functions_range U _).mpr
    (power_covariant p r ((M.functions_range U _).mp ⟨s, rfl⟩))).choose

omit [Fact p.Prime] [CharP k p] [IsAlgClosed k] in
private theorem powerSection_function (U : Q.scheme.left.Opens) (s : Γ(M.sheaf, U)) :
    Mq.functionVal U (powerSection p r M Mq U s) = (M.functionVal U s) ^ (p ^ r) :=
  ((Mq.functions_range U _).mpr
    (power_covariant p r ((M.functions_range U _).mp ⟨s, rfl⟩))).choose_spec

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private def frobeniusPullSections :
    M.sheaf ⟶ (pushforward (absoluteFrobenius p r Q.scheme)).obj Mq.sheaf :=
  ⟨PresheafOfModules.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := powerSection p r M Mq U.unop
          map_zero' := by
            apply Mq.functions_injective
            change Mq.functionVal U.unop (powerSection p r M Mq U.unop 0) =
              Mq.functionVal U.unop 0
            rw [powerSection_function]
            simp [SectionRealization.functionVal, (Fact.out : p.Prime).ne_zero]
          map_add' := by
            intro x y
            change Γ(M.sheaf, U.unop) at x y
            apply Mq.functions_injective
            change Mq.functionVal U.unop (powerSection p r M Mq U.unop (x + y)) =
              Mq.functionVal U.unop (powerSection p r M Mq U.unop x + powerSection p r M Mq U.unop y)
            rw [powerSection_function]
            have h₁ : M.functionVal U.unop (x + y) =
                M.functionVal U.unop x + M.functionVal U.unop y := by
              simp only [SectionRealization.functionVal, map_add]
            have h₂ : Mq.functionVal U.unop
                (powerSection p r M Mq U.unop x + powerSection p r M Mq U.unop y) =
                Mq.functionVal U.unop (powerSection p r M Mq U.unop x) +
                  Mq.functionVal U.unop (powerSection p r M Mq U.unop y) := by
              simp only [SectionRealization.functionVal, map_add]
            rw [h₁, h₂, powerSection_function, powerSection_function]
            simp only [← frobenius_app p r G.val.X, map_add] }
      naturality := by
        intro U V i
        ext : 1
        apply DFunLike.ext
        intro x
        change powerSection p r M Mq V.unop (M.sheaf.presheaf.map i x) =
          Mq.sheaf.presheaf.map i (powerSection p r M Mq U.unop x)
        apply Mq.functions_injective
        have hM := PresheafOfModules.naturality_apply M.functions.val i x
        have hMq := PresheafOfModules.naturality_apply Mq.functions.val i
          (powerSection p r M Mq U.unop x)
        change M.functionVal V.unop (M.sheaf.presheaf.map i x) =
          G.val.X.left.presheaf.map ((Opens.map Q.projection.left.base).map i.unop).op
            (M.functionVal U.unop x) at hM
        change Mq.functionVal V.unop (Mq.sheaf.presheaf.map i _) =
          G.val.X.left.presheaf.map ((Opens.map Q.projection.left.base).map i.unop).op
            (Mq.functionVal U.unop _) at hMq
        change Mq.functionVal V.unop _ = Mq.functionVal V.unop _
        rw [powerSection_function, hM, hMq, powerSection_function, map_pow] }
    (by
      intro U t s
      let t' : Γ(Q.scheme.left, U.unop) := t
      let t'' : Γ(Q.scheme.left, U.unop) := (absoluteFrobenius p r Q.scheme).app U.unop t'
      change Γ(M.sheaf, U.unop) at s
      change powerSection p r M Mq U.unop (t' • s) =
        t'' • powerSection p r M Mq U.unop s
      apply Mq.functions_injective
      have hs : M.functionVal U.unop (t' • s) =
          Q.projection.left.app U.unop t' * M.functionVal U.unop s :=
        (Scheme.Modules.Hom.app_smul M.functions t' s).trans
          (functionsOver_smul _ _ _ _)
      have ht (z : Γ(Mq.sheaf, U.unop)) : Mq.functionVal U.unop (t'' • z) =
          Q.projection.left.app U.unop t'' * Mq.functionVal U.unop z :=
        (Scheme.Modules.Hom.app_smul Mq.functions t'' z).trans
          (functionsOver_smul _ _ _ _)
      change Mq.functionVal _ _ = Mq.functionVal _ _
      rw [powerSection_function, hs, ht, powerSection_function, mul_pow]
      dsimp only [t'']
      rw [frobenius_app, map_pow])⟩

omit [Fact p.Prime] [CharP k p] [IsAlgClosed k] in
set_option backward.isDefEq.respectTransparency false in
private theorem chartValue_power {U : Q.scheme.left.Opens} (t : TorsorLift Q U)
    (s : Γ(M.sheaf, U)) :
    chartValue Mq t (powerSection p r M Mq U s) = chartValue M t s ^ (p ^ r) := by
  change U.topIso.hom (evalOn t.lift.left _ (lift_in_open t)
    (Mq.functionVal U (powerSection p r M Mq U s))) =
    U.topIso.hom (evalOn t.lift.left _ (lift_in_open t) (M.functionVal U s)) ^ (p ^ r)
  rw [powerSection_function p r M Mq U s]
  unfold evalOn
  rw [map_pow, map_pow]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 850000 in
/-- On the Frobenius twist, a line of weight `χ` pulls back to the associated
line of weight `χ ^ (p ^ r)`. -/
theorem flagFrobeniusLinePullback : FlagFrobeniusLinePullback.{u} := by
  intro k _ _ p r _ _ G P Q a b χ L Lq M Mq F hF
  have hEq := relativeFrobenius_unique p r Q.scheme F hF
  subst F
  let f := absoluteFrobenius p r Q.scheme
  let h := frobeniusPullSections p r M Mq
  let adj := pullbackPushforwardAdjunction f
  let v := (adj.homEquiv M.sheaf Mq.sheaf).symm h
  have : IsIso v := by
    apply isIso_of_open_restrictions
    intro y
    obtain ⟨U, hy, ⟨t⟩⟩ := chartCover Q y
    have hU : U ≤ f ⁻¹ᵁ U := le_refl U
    refine ⟨U, hy, restrict_adjoint_isIso f hU h ?_⟩
    let e := chartIso M t
    apply local_adjoint_isIso _ e (chartIso Mq t)
    let s₀ := e.inv.app ⊤ (1 : Γ(U.toScheme, ⊤))
    let s := (restrictTopSections M.sheaf U).hom s₀
    have hs₀ : e.hom.app ⊤ s₀ = (1 : Γ(U.toScheme, ⊤)) := by
      change (e.inv ≫ e.hom).app ⊤ (1 : Γ(U.toScheme, ⊤)) = _
      rw [Iso.inv_hom_id]
      rfl
    have hs : chartValue M t s = 1 := by
      have he := (chartIso_top M t s₀).symm.trans hs₀
      exact (ConcreteCategory.bijective_of_isIso U.topIso.inv).1
        (he.trans (map_one U.topIso.inv.hom).symm)
    change IsUnit (show Γ(U.toScheme, ⊤) from
      (chartIso Mq t).hom.app ⊤ ((restrictDirectImageHom f hU h).app ⊤ s₀))
    rw [chartIso_top, restrictDirectImageHom_top]
    have ht : Mq.sheaf.presheaf.map (homOfLE hU).op (h.app U s) = powerSection p r M Mq U s := by
      rw [show homOfLE hU = 𝟙 U from Subsingleton.elim _ _, op_id]
      exact congrArg (fun f : Γ(Mq.sheaf, U) ⟶ Γ(Mq.sheaf, U) ↦
        f (powerSection p r M Mq U s)) (Mq.sheaf.presheaf.map_id (op U))
    rw [ht, chartValue_power, hs, one_pow, map_one]
    exact isUnit_one
  refine ⟨asIso v, fun U s ↦ ?_⟩
  let heq : f ⁻¹ᵁ U = U := rfl
  change Mq.functionVal U ((adj.homEquiv _ _ v).app U s) =
    G.val.X.left.presheaf.map (eqToHom (congrArg (fun V ↦ Q.projection.left ⁻¹ᵁ V) heq)).op _
  rw [Equiv.apply_symm_apply]
  change Mq.functionVal U (powerSection p r M Mq U s) =
    G.val.X.left.presheaf.map (𝟙 _) _
  rw [powerSection_function, (G.val.X.left.presheaf).map_id]
  rfl

end LinePullback

section KernelOrbit

open Specs.FlagRelativeFrobeniusAtlas
open QuotientEmbedding (Presentation)
open LinearAlgebraicGroups.FiniteDistributions
  (frobeniusKernelHopf frobeniusKernelInclusion frobeniusPullback frobeniusPullback_formula)
open LinearAlgebraicGroups.FlagRelativeFrobeniusAtlas
  (relativeGroupFrobenius relativeGroupFrobenius_hom relativeFrobenius
    affineFrobeniusKernel_toUnit uniqueGeometricFiberPoint relativeFrobenius_formula)

private abbrev affinePoint {A R : TestAlgebra k} (f : A →ₐ[k] R) :
    Points ((testSpec k).obj (op A)) R :=
  (testSpec k).map (CommAlgCat.ofHom f).op

private theorem affinePoint_comp {A B R : TestAlgebra k} (g : B →ₐ[k] R) (f : A →ₐ[k] B) :
    affinePoint (g.comp f) = affinePoint g ≫ affinePoint f :=
  (testSpec k).map_comp (CommAlgCat.ofHom g).op (CommAlgCat.ofHom f).op

private def pointAlgHom {A R : TestAlgebra k} (x : Points ((testSpec k).obj (op A)) R) :
    A →ₐ[k] R :=
  ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage x).unop.hom

private theorem affinePoint_pointAlgHom {A R : TestAlgebra k}
    (x : Points ((testSpec k).obj (op A)) R) : affinePoint (pointAlgHom x) = x :=
  (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage x

private theorem affinePoint_injective {A R : TestAlgebra k} :
    Function.Injective (affinePoint (A := A) (R := R)) := by
  intro f g h
  have e := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective h
  exact congrArg (fun a ↦ a.unop.hom) e

set_option backward.isDefEq.respectTransparency false in
private theorem affinePoint_restrictToChart {R : TestAlgebra k} (S : SocleModel P U χ)
    (g : Points G.val.X R) :
    affinePoint (A := CommAlgCat.of k S.A) (R := R) (restrictToChart S.groupIso g) ≫
      S.groupIso.hom.hom.hom = g := by
  have h : affinePoint (A := CommAlgCat.of k S.A) (R := R) (restrictToChart S.groupIso g) =
      g ≫ S.groupIso.inv.hom.hom :=
    affinePoint_pointAlgHom (A := CommAlgCat.of k S.A) (R := R) (g ≫ S.groupIso.inv.hom.hom)
  rw [h, Category.assoc]
  exact congrArg (fun f : G.val ⟶ G.val ↦ g ≫ f.hom.hom) S.groupIso.inv_hom_id

variable (p r : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]

private abbrev kernelAlgebra (A : HopfAlgebraCategory k) :=
  CommAlgCat.of k (frobeniusKernelHopf p r A)

set_option linter.style.haveILetI false in
private def kernelOrbitAlgHom (S : SocleModel P U χ) (g : S.A →ₐ[k] k) :
    S.A →ₐ[k] kernelAlgebra p r S.A :=
  let R := kernelAlgebra p r S.A
  letI := convolutionGroup S.A R
  letI := hopfKernelIdeal k (frobeniusPullback p r S.A)
  let h : WithConv (S.A →ₐ[k] R) :=
    toConv (hopfQuotientMap S.A (kernelIdeal (frobeniusPullback p r S.A))).hom.toAlgHom
  let gC : WithConv (S.A →ₐ[k] R) :=
    toConv ((Algebra.ofId k (frobeniusKernelHopf p r S.A)).comp g)
  (h⁻¹ * gC).ofConv

private abbrev kernelOrbitPoint (S : SocleModel P U χ) (g : S.A →ₐ[k] k) :
    Points G.val.X (kernelAlgebra p r S.A) :=
  affinePoint (A := CommAlgCat.of k S.A) (kernelOrbitAlgHom p r S g) ≫
    S.groupIso.hom.hom.hom

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
private theorem orbitPoint_frobenius (Q : Presentation P.negative)
    (S : SocleModel P U χ) (g : S.A →ₐ[k] k) :
    let z : Points Q.scheme (CommAlgCat.of k k) :=
      affinePoint (A := CommAlgCat.of k S.A) g ≫ S.groupIso.hom.hom.hom ≫ Q.projection
    (kernelOrbitPoint p r S g ≫ Q.projection) ≫ (relativeFrobenius p r).app Q.scheme =
      affinePoint (A := CommAlgCat.of k k) (Algebra.ofId k (kernelAlgebra p r S.A)) ≫
        z ≫ (relativeFrobenius p r).app Q.scheme := by
  classical
  let C := frobeniusKernelHopf p r S.A
  let R := kernelAlgebra p r S.A
  let F := relativeFrobenius (k := k) p r
  let Gf := relativeGroupFrobenius (k := k) p r
  letI := convolutionGroup S.A R
  letI := hopfKernelIdeal k (frobeniusPullback p r S.A)
  let h : WithConv (S.A →ₐ[k] R) :=
    toConv (hopfQuotientMap S.A (kernelIdeal (frobeniusPullback p r S.A))).hom.toAlgHom
  let gC : WithConv (S.A →ₐ[k] R) := toConv ((Algebra.ofId k C).comp g)
  let i := S.groupIso.hom.hom.hom ≫ Q.projection
  let liftScalar := (testSpec k).map (CommAlgCat.ofHom (Algebra.ofId k C)).op
  let gk := (testSpec k).map (CommAlgCat.ofHom g).op
  obtain ⟨e, he, _⟩ := hopfSpecPoints k
  let E := (e S.A).hom.app R
  have point (x : WithConv (S.A →ₐ[k] R)) :
      (E x : Points (specGroup S.A).X R) =
        (testSpec k).map (CommAlgCat.ofHom x.ofConv).op :=
    Over.OverMorphism.ext (he S.A R x)
  let m := ((groupPointsFunctor k).map (Gf.app (specGroup S.A))).app R
  have hm (x : Points (specGroup S.A).X R) :
      m x = x ≫ (Gf.app (specGroup S.A)).hom.hom := rfl
  have hker : m (E h) = 1 := by
    rw [hm, point]
    change ((frobeniusKernelInclusion p r S.A) ≫ Gf.app (specGroup S.A)).hom.hom = _
    exact affineFrobeniusKernel_toUnit p r S.A
  have hmul :
      (E (h⁻¹ * gC) : Points (specGroup S.A).X R) ≫ F.app (specGroup S.A).X =
        (E gC : Points (specGroup S.A).X R) ≫ F.app (specGroup S.A).X := by
    change (E ≫ m) (h⁻¹ * gC) = (E ≫ m) gC
    have eq : (E ≫ m) h = 1 := hker
    rw [map_mul, map_inv, eq, inv_one, one_mul]
  have hgC : (E gC : Points (specGroup S.A).X R) = liftScalar ≫ gk := by
    rw [point]
    exact (testSpec k).map_comp (CommAlgCat.ofHom (Algebra.ofId k C)).op
      (CommAlgCat.ofHom g).op
  change ((affinePoint (A := CommAlgCat.of k S.A) (R := R) (h⁻¹ * gC).ofConv ≫
    S.groupIso.hom.hom.hom) ≫ Q.projection) ≫ F.app Q.scheme =
      liftScalar ≫ (gk ≫ i) ≫ F.app Q.scheme
  simp only [Category.assoc]
  change (testSpec k).map (CommAlgCat.ofHom (h⁻¹ * gC).ofConv).op ≫ i ≫
    F.app Q.scheme = _
  have hnat : i ≫ F.app Q.scheme = F.app (specGroup S.A).X ≫ (twist p r).map i :=
    F.naturality i
  rw [← point, hnat, ← Category.assoc (E (h⁻¹ * gC)), hmul, hgC]
  simp only [Category.assoc, ← hnat]

omit [IsAlgClosed k] in
set_option backward.isDefEq.respectTransparency false in
private theorem coordinateFunction_affinePoint {R : TestAlgebra k} (S : SocleModel P U χ)
    (g : S.A →ₐ[k] R) (z : S.A) :
    (affinePoint (A := CommAlgCat.of k S.A) g ≫ S.groupIso.hom.hom.hom) ≫
      coordinateFunction S.groupIso z = linePoint R (g z) := by
  change (_ ≫ S.groupIso.hom.hom.hom) ≫ S.groupIso.inv.hom.hom ≫
      linePoint (CommAlgCat.of k S.A) z = _
  have h := congrArg (fun f : specGroup S.A ⟶ specGroup S.A ↦ f.hom.hom)
    S.groupIso.hom_inv_id
  change S.groupIso.hom.hom.hom ≫ S.groupIso.inv.hom.hom = 𝟙 _ at h
  simp only [Category.assoc, ← Category.assoc S.groupIso.hom.hom.hom, h, Category.id_comp]
  exact linePoint_comp (R := CommAlgCat.of k S.A) (S := R) g z

private def chartFiberLift {A B X Y T : SchemeOver k}
    {m : A ⟶ B} {i : A ⟶ X} {j : B ⟶ Y} {f : X ⟶ Y}
    (h : IsPullback m.left i.left j.left f.left)
    (a : T ⟶ B) (b : T ⟶ X) (w : a ≫ j = b ≫ f) : T ⟶ A :=
  let w' : a.left ≫ j.left = b.left ≫ f.left := congrArg Over.Hom.left w
  Over.homMk (h.lift a.left b.left w') (by
    rw [← Over.w m, ← Category.assoc, h.lift_fst, Over.w])

omit [IsAlgClosed k] in
private theorem chartFiberLift_fst {A B X Y T : SchemeOver k}
    {m : A ⟶ B} {i : A ⟶ X} {j : B ⟶ Y} {f : X ⟶ Y}
    (h : IsPullback m.left i.left j.left f.left)
    (a : T ⟶ B) (b : T ⟶ X) (w : a ≫ j = b ≫ f) :
    chartFiberLift h a b w ≫ m = a :=
  Over.OverMorphism.ext (h.lift_fst _ _ _)

omit [IsAlgClosed k] in
private theorem chartFiberLift_snd {A B X Y T : SchemeOver k}
    {m : A ⟶ B} {i : A ⟶ X} {j : B ⟶ Y} {f : X ⟶ Y}
    (h : IsPullback m.left i.left j.left f.left)
    (a : T ⟶ B) (b : T ⟶ X) (w : a ≫ j = b ≫ f) :
    chartFiberLift h a b w ≫ i = b :=
  Over.OverMorphism.ext (h.lift_snd _ _ _)

open Specs.SteinbergDimension (IsHalfPositiveRootSum)
open Specs.GeometricRadicals (IsUnipotentRadical)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
private theorem polynomialChartFibers [IsCommMonObj P.torus.group.X]
    (hr : 1 ≤ r) (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U)
    (ρ : Character P.torus.group) (hρ : IsHalfPositiveRootSum P ρ)
    (S : SocleModel P U (Additive.toMul ((p ^ r - 1) • Additive.ofMul ρ)))
    (Q : Presentation P.negative) {n : ℕ}
    (l : affineChart k n ⟶ G.val.X)
    (j : affineChart k n ⟶ (twist p r).obj Q.scheme)
    (sq : IsPullback (powerMorphism (p ^ r) n).left (l ≫ Q.projection).left j.left
      ((relativeFrobenius p r).app Q.scheme).left)
    (x : Fin n → k) :
    ∃ v : MvPolynomial (Fin n) k →ₐ[k] kernelAlgebra p r S.A,
      (∀ a, v (powerMap (p ^ r) n a) = algebraMap k _ (MvPolynomial.aeval x a)) ∧
      Function.Injective (fun s : S.socle ↦ v (restrictToChart S.groupIso l (socleFunction S s))) := by
  let B := CommAlgCat.of k (MvPolynomial (Fin n) k)
  let C := kernelAlgebra p r S.A
  let K := CommAlgCat.of k k
  let F := (relativeFrobenius p r).app Q.scheme
  let s : Points (affineChart k n) K := affinePoint (A := B) (R := K) (MvPolynomial.aeval x)
  obtain ⟨z, hz, _⟩ := uniqueGeometricFiberPoint p r Q.scheme F
    (relativeFrobenius_formula p r Q.scheme) k (s ≫ j)
  let zA := chartFiberLift sq s z hz.symm
  let g := restrictToChart S.groupIso (zA ≫ l)
  have hg : affinePoint (A := CommAlgCat.of k S.A) (R := K) g ≫ S.groupIso.hom.hom.hom ≫
      Q.projection = z := by
    rw [← Category.assoc, affinePoint_restrictToChart, Category.assoc]
    exact chartFiberLift_snd sq s z hz.symm
  let o := kernelOrbitPoint p r S g
  let v₀ : MvPolynomial (Fin n) k →ₐ[k] C := (Algebra.ofId k C).comp (MvPolynomial.aeval x)
  let yC : Points (affineChart k n) C := affinePoint (A := B) v₀
  have hyC : yC = affinePoint (A := K) (R := C) (Algebra.ofId k C) ≫ s :=
    affinePoint_comp (A := B) (B := K) (R := C) (Algebra.ofId k C) (MvPolynomial.aeval x)
  have hfiber : yC ≫ j = (o ≫ Q.projection) ≫ F := by
    have h := orbitPoint_frobenius p r Q S g
    change (o ≫ Q.projection) ≫ F =
      affinePoint (A := K) (Algebra.ofId k C) ≫
        (affinePoint (A := CommAlgCat.of k S.A) (R := K) g ≫ S.groupIso.hom.hom.hom ≫
          Q.projection) ≫ F at h
    rw [hg, hz] at h
    rw [h, hyC, Category.assoc]
  let u := chartFiberLift sq yC (o ≫ Q.projection) hfiber
  let v := pointAlgHom (A := B) u
  have hv : affinePoint (A := B) v = u := affinePoint_pointAlgHom u
  have hv₁ : v.comp (powerMap (p ^ r) n) = v₀ := by
    apply affinePoint_injective (A := B) (R := C)
    rw [affinePoint_comp, hv]
    exact chartFiberLift_fst sq yC (o ≫ Q.projection) hfiber
  refine ⟨v, fun a ↦ DFunLike.congr_fun hv₁ a, ?_⟩
  have he : (u ≫ l) ≫ Q.projection = o ≫ Q.projection := by
    rw [Category.assoc]
    exact chartFiberLift_snd sq yC (o ≫ Q.projection) hfiber
  let d := torsorDifference Q (u ≫ l) o he
  have hd : o = (u ≫ l) * (d ≫ P.negative.inclusion.hom.hom) := by
    rw [torsorDifference_value, mul_inv_cancel_left]
  obtain ⟨e, he', hcov⟩ :=
    LinearAlgebraicGroups.FlagLineBundle.schemeCovarianceComparison
      S.projection _ S.groupIso S.borelIso S.restriction S.character
      S.restriction_spec S.character_spec S.coordinate S.coordinate_spec
  have hval (t : S.socle) :
      kernelOrbitAlgHom p r S g (socleFunction S t) =
        CharacterPairing.characterValue
          (S.projection.projection ≫ Additive.toMul ((p ^ r - 1) • Additive.ofMul ρ)) C d⁻¹ *
          v (restrictToChart S.groupIso l (socleFunction S t)) := by
    let f := socleFunction S t
    let σ : Character P.torus.group := Additive.toMul ((p ^ r - 1) • Additive.ofMul ρ)
    have hc : SchemeCovariant S.projection σ (coordinateFunction S.groupIso f) := by
      change SchemeCovariant S.projection σ (S.groupIso.inv.hom.hom ≫
        linePoint (CommAlgCat.of k S.A) f)
      rw [← he']
      exact (hcov f).mp ((S.inducedBasis.equivFun.symm (t : S.I → k))).property
    have h1 : (u ≫ l) ≫ coordinateFunction S.groupIso f =
        linePoint C (v (restrictToChart S.groupIso l f)) := by
      rw [Category.assoc, restrictToChart_eval, ← hv]
      exact linePoint_comp (R := B) (S := C) v _
    have h2 := hc C (u ≫ l) d _ h1
    rw [← hd] at h2
    have h3 := (coordinateFunction_affinePoint (R := C) S
      (kernelOrbitAlgHom p r S g) f).symm.trans h2
    apply (linePointEquiv C).injective
    simpa only [linePointEquiv_apply] using h3
  have hinj := kernelOrbitInjection p r hr P U hU ρ hρ S (frobeniusPullback p r S.A)
    (frobeniusPullback_formula p r S.A) (hopfKernelIdeal k _) g
  change Function.Injective (fun t : S.socle ↦ kernelOrbitAlgHom p r S g (socleFunction S t))
    at hinj
  intro t t' h
  exact hinj ((hval t).trans ((congrArg (_ * ·) h).trans (hval t').symm))

end KernelOrbit

section PolynomialSections

open Specs.FlagRelativeFrobeniusAtlas (powerMap)
open scoped BigOperators

/-- Scalars on the source chart act through the coordinate-power map. -/
private abbrev powerModule (k : Type u) [Field k] (n q : ℕ) :=
  (ModuleCat.restrictScalars (powerMap (k := k) q n).toRingHom).obj
    (ModuleCat.of (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k))

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
private theorem powerModule_basis {I : Type u} [Fintype I] [DecidableEq I]
    (n q : ℕ) (hq : 0 < q) (hcard : Fintype.card I = q ^ n) :
    Nonempty (Module.Basis I (MvPolynomial (Fin n) k) (powerModule k n q)) := by
  let R := MvPolynomial (Fin n) k
  letI : Module R (ULift.{0} R) := (polynomialPowerMap k n q).toAlgebra.toModule
  obtain ⟨b, _, hb⟩ := polynomialPowerBasis k n q hq
  let e : ULift.{0} R ≃ₗ[R] powerModule k n q :=
    { toAddEquiv := ULift.ringEquiv.toAddEquiv
      map_smul' := fun _ _ ↦ rfl }
  exact ⟨(b.map e).reindex (Fintype.equivOfCardEq (hb.trans hcard.symm))⟩

set_option backward.isDefEq.respectTransparency false in
private theorem polynomialSectionBasis {I C : Type u} [Fintype I] [DecidableEq I]
    [IsAlgClosed k] [CommRing C] [Algebra k C] (n q : ℕ) (hq : 0 < q)
    (hcard : Fintype.card I = q ^ n) (v : I → MvPolynomial (Fin n) k)
    (hfiber : ∀ x : Fin n → k, ∃ f : MvPolynomial (Fin n) k →ₐ[k] C,
      (∀ a, f (powerMap q n a) = algebraMap k C (MvPolynomial.aeval x a)) ∧
      LinearIndependent k (fun j ↦ f (v j))) :
    ∃ b : Module.Basis I (MvPolynomial (Fin n) k) (powerModule k n q),
      ∀ j, (b j : MvPolynomial (Fin n) k) = v j := by
  let R := MvPolynomial (Fin n) k
  let T := powerModule k n q
  let down : T → R := fun t ↦ t
  obtain ⟨b⟩ := powerModule_basis (k := k) n q hq hcard
  let A : Matrix I I R := fun i j ↦ b.repr (v j : T) i
  have col (j : I) : ∑ i, powerMap q n (A i j) * down (b i) = v j :=
    b.sum_repr (v j : T)
  have hA : IsUnit A := by
    apply polynomialMatrixCriterion
    intro x
    obtain ⟨f, hf, hind⟩ := hfiber x
    let M := A.map (MvPolynomial.aeval x)
    change Function.Injective M.mulVec
    change Function.Injective M.mulVecLin
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro w hw
    change M.mulVec w = 0 at hw
    have col' (j : I) : f (v j) = ∑ i, M i j • f (down (b i)) := by
      conv_lhs => rw [← col j]
      simp only [map_sum, map_mul, hf, Algebra.smul_def]
      rfl
    have hs : ∑ j, w j • f (v j) = 0 := calc
      _ = ∑ j, ∑ i, (M i j * w j) • f (down (b i)) := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [col', Finset.smul_sum, smul_smul, mul_comm (w j)]
      _ = ∑ i, ∑ j, (M i j * w j) • f (down (b i)) := Finset.sum_comm
      _ = ∑ i, (M.mulVec w i) • f (down (b i)) := by
        simp only [Matrix.mulVec, dotProduct, Finset.sum_smul]
      _ = 0 := by simp [hw]
    exact funext (fun j ↦ (Fintype.linearIndependent_iff.mp hind) w hs j)
  let m : Module.End R T := Matrix.toLinAlgEquiv b A
  have hm : IsUnit m := hA.map (Matrix.toLinAlgEquiv b).toMonoidHom
  let e := LinearEquiv.ofBijective m ((Module.End.isUnit_iff m).mp hm)
  refine ⟨b.map e, fun j ↦ ?_⟩
  change down (m (b j)) = v j
  exact (congrArg down (Matrix.toLinAlgEquiv_self b A j)).trans (col j)

end PolynomialSections

section FreeModules

open Scheme.Modules
open Specs.LinePushforwardProjection (chartSections structureModule)

private def sectionFromTop {X : Scheme.{u}} (M : X.Modules) (s : Γ(M, ⊤)) :
    M.val.sections :=
  M.val.sectionsMk (fun V ↦ M.presheaf.map V.unop.leTop.op s) (by
    intro U V f
    change M.presheaf.map f (M.presheaf.map U.unop.leTop.op s) =
      M.presheaf.map V.unop.leTop.op s
    rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
    congr 1)

private theorem sectionFromTop_top {X : Scheme.{u}} (M : X.Modules) (s : Γ(M, ⊤)) :
    (sectionFromTop M s).val (op (⊤ : X.Opens)) = s := by
  change M.presheaf.map ((⊤ : X.Opens).leTop).op s = s
  rw [show (⊤ : X.Opens).leTop = 𝟙 _ from Subsingleton.elim _ _, op_id]
  exact congrArg (fun f : Γ(M, ⊤) ⟶ Γ(M, ⊤) ↦ f s) (M.presheaf.map_id (op ⊤))

private def evaluationMap {X : Scheme.{u}} {I : Type u} {M : X.Modules}
    (s : I → Γ(M, ⊤)) : freeModule X I ⟶ M :=
  (SheafOfModules.freeHomEquiv (M : SheafOfModules X.ringCatSheaf)).symm
    (fun i ↦ sectionFromTop M (s i))

private theorem evaluationMap_generator {X : Scheme.{u}} {I : Type u} {M : X.Modules}
    (s : I → Γ(M, ⊤)) (i : I) :
    (evaluationMap s).app ⊤ (freeGenerator X i) = s i := by
  let e := SheafOfModules.freeHomEquiv (M : SheafOfModules X.ringCatSheaf) (I := I)
  have h := congrArg (fun f ↦ (f i).val (op (⊤ : X.Opens)))
    (e.apply_symm_apply (fun i ↦ sectionFromTop M (s i)))
  exact h.trans (sectionFromTop_top M (s i))

private theorem chartSections_natural {A X : Scheme.{u}} (j : A ⟶ X) [IsOpenImmersion j]
    {M N : X.Modules} (a : M ⟶ N) (s : Γ(M, ⊤)) :
    ((restrictFunctor j).map a).app ⊤ (chartSections j M s) =
      chartSections j N (a.app ⊤ s) :=
  PresheafOfModules.naturality_apply a.val (j ''ᵁ (⊤ : A.Opens)).leTop.op s

set_option backward.isDefEq.respectTransparency false in
private theorem chartSections_one {A X : Scheme.{u}} (j : A ⟶ X) [IsOpenImmersion j] :
    (restrictUnitIso j).hom.app ⊤ (chartSections j (structureModule X) (1 : Γ(X, ⊤))) =
      (1 : Γ(A, ⊤)) := by
  change (j.appIso ⊤).hom (X.presheaf.map (j ''ᵁ (⊤ : A.Opens)).leTop.op (1 : Γ(X, ⊤))) = 1
  rw [map_one, map_one]

set_option backward.isDefEq.respectTransparency false in
private def restrictFreeIso {A X : Scheme.{u}} (j : A ⟶ X) [IsOpenImmersion j] (I : Type u) :
    freeModule A I ≅ (freeModule X I).restrict j :=
  have : PreservesColimitsOfSize.{u, u} (restrictFunctor j) := inferInstance
  SheafOfModules.mapFreeIso (restrictFunctor j) I (restrictUnitIso j).symm

set_option backward.isDefEq.respectTransparency false in
private theorem restrictFreeIso_generator {A X : Scheme.{u}} (j : A ⟶ X) [IsOpenImmersion j]
    {I : Type u} (i : I) :
    (restrictFreeIso j I).hom.app ⊤ (freeGenerator A i) =
      chartSections j (freeModule X I) (freeGenerator X i) := by
  have : PreservesColimitsOfSize.{u, u} (restrictFunctor j) := inferInstance
  have h := SheafOfModules.ιFree_mapFreeIso_hom (restrictFunctor j) (I := I)
    (restrictUnitIso j).symm i
  have h' := congrArg (fun a : structureModule A ⟶ (freeModule X I).restrict j ↦
    a.app ⊤ (1 : Γ(A, ⊤))) h
  change (restrictFreeIso j I).hom.app ⊤ (freeGenerator A i) =
    ((restrictFunctor j).map (SheafOfModules.ιFree i)).app ⊤
      ((restrictUnitIso j).inv.app ⊤ (1 : Γ(A, ⊤))) at h'
  have hcancel (x : Γ((structureModule X).restrict j, ⊤)) :
      (restrictUnitIso j).inv.app ⊤ ((restrictUnitIso j).hom.app ⊤ x) = x := by
    change ((restrictUnitIso j).hom ≫ (restrictUnitIso j).inv).app ⊤ x = x
    rw [Iso.hom_inv_id]
    rfl
  rw [h', ← chartSections_one j, hcancel]
  exact chartSections_natural j (SheafOfModules.ιFree i) (1 : Γ(X, ⊤))

private def coconeIsColimitOfBasis {R I : Type u} [CommRing R]
    {F : Discrete I ⥤ ModuleCat.{u} R} (D : Cocone F)
    (b : Module.Basis I R D.pt) (one : ∀ i, F.obj i)
    (hgen : ∀ i (x : F.obj i), ∃ c : R, x = c • one i)
    (hb : ∀ i, D.ι.app i (one i) = b i.as) : IsColimit D := by
  let desc (s : Cocone F) : D.pt ⟶ s.pt :=
    ModuleCat.ofHom (b.constr R (fun i ↦ s.ι.app ⟨i⟩ (one ⟨i⟩)))
  have desc_basis (s : Cocone F) (i : I) : desc s (b i) = s.ι.app ⟨i⟩ (one ⟨i⟩) :=
    b.constr_basis R _ i
  refine ⟨desc, ?_, ?_⟩
  · intro s i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨c, rfl⟩ := hgen i x
    change desc s (D.ι.app i (c • one i)) = s.ι.app i (c • one i)
    rw [(D.ι.app i).hom.map_smul, (s.ι.app i).hom.map_smul, (desc s).hom.map_smul, hb, desc_basis]
  · intro s a ha
    apply ModuleCat.hom_ext
    apply b.ext
    intro i
    have h := congrArg (fun f : F.obj ⟨i⟩ ⟶ s.pt ↦ f (one ⟨i⟩)) (ha ⟨i⟩)
    change a (D.ι.app ⟨i⟩ (one ⟨i⟩)) = s.ι.app ⟨i⟩ (one ⟨i⟩) at h
    rw [hb] at h
    exact h.trans (desc_basis s i).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 700000 in
private theorem affineFreeMap_isIso {R : CommRingCat.{u}} {I : Type u} [Fintype I]
    {M : (Spec R).Modules} (a : freeModule (Spec R) I ⟶ M)
    (hM : M.IsQuasicoherent) (b : Module.Basis I R (moduleSpecΓFunctor.obj M))
    (hb : ∀ i, a.app ⊤ (freeGenerator (Spec R) i) = b i) : IsIso a := by
  classical
  let H := moduleSpecΓFunctor (R := R)
  have : H.Additive := ⟨fun {_ _} _ _ ↦ rfl⟩
  let C := H.mapCocone (SheafOfModules.freeCofan (R := (Spec R).ringCatSheaf) I)
  let D : Cocone _ := ⟨H.obj M, C.ι ≫ (Functor.const _).map (H.map a)⟩
  let one : H.obj (structureModule (Spec R)) := (1 : Γ(Spec R, ⊤))
  have hscalar (x : H.obj (structureModule (Spec R))) : ∃ c : R, x = c • one := by
    refine ⟨(Scheme.ΓSpecIso R).hom (show Γ(Spec R, ⊤) from x), ?_⟩
    change (show Γ(Spec R, ⊤) from x) =
      (Scheme.ΓSpecIso R).inv ((Scheme.ΓSpecIso R).hom x) * (1 : Γ(Spec R, ⊤))
    rw [Iso.hom_inv_id_apply, mul_one]
  let hD := coconeIsColimitOfBasis D b (fun _ ↦ one) (fun _ ↦ hscalar) (fun i ↦ hb i.as)
  have hC : IsColimit C :=
    isColimitOfPreserves H (SheafOfModules.isColimitFreeCofan (R := (Spec R).ringCatSheaf) I)
  let e := hC.coconePointUniqueUpToIso hD
  have h : H.map a = e.hom := hC.hom_ext fun i ↦ (hC.fac D i).symm
  have ha : IsIso (H.map a) := h ▸ e.isIso_hom
  exact LinearAlgebraicGroups.LinePushforwardProjection.isIsoOfAffineSections a
    ((isQuasicoherent_iff_isIso_fromTildeΓ _).mpr inferInstance) hM ha

end FreeModules

section ChartSections

open Specs.AssociatedFlagLineSheaves
open Specs.LinePushforwardProjection (chartSections)
open Scheme.Modules
open QuotientEmbedding (Presentation)
open LinearAlgebraicGroups.AssociatedFlagLineSheaves (chartEquiv)
open private evalOn_comp evalOn_congr evalOn_open evalOn_restrict evalOn_top
  lineCoordinate_linePoint coordinate_unique chartValue_eq lift_in_open
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.AssociatedFlagLineSheaves

variable {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
  {b : BorelProjection P} {L : AssociatedBundle Q a b χ}
  (M : SectionRealization L)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 700000 in
private theorem affineSectionCoordinates {R : TestAlgebra k}
    (l : (testSpec k).obj (op R) ⟶ G.val.X) [IsOpenImmersion (l ≫ Q.projection).left] :
    let i := (l ≫ Q.projection).left
    ∃ e : moduleSpecΓFunctor.obj (M.sheaf.restrict i) ≃ₗ[R] R,
      ∀ s : Γ(M.sheaf, ⊤),
        e (chartSections i M.sheaf s) =
          (Scheme.ΓSpecIso (CommRingCat.of R)).hom (l.left.appTop (M.functionVal ⊤ s)) := by
  let i := (l ≫ Q.projection).left
  let A := (testSpec k).obj (op R)
  let W := i ''ᵁ (⊤ : A.left.Opens)
  have hW : Set.range i = Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    exact Set.image_univ.symm
  let e := IsOpenImmersion.isoOfRangeEq i W.ι hW
  have he : e.hom ≫ W.ι = i := IsOpenImmersion.isoOfRangeEq_hom_fac i W.ι hW
  have he' : e.inv ≫ i = W.ι := IsOpenImmersion.isoOfRangeEq_inv_fac i W.ι hW
  let t : TorsorLift Q W :=
    ⟨Over.homMk (e.inv ≫ l.left) (by
      rw [Category.assoc, Over.w l, ← Over.w (l ≫ Q.projection), ← Category.assoc, he']
      rfl), he'⟩
  have htl : e.hom ≫ t.lift.left = l.left := by
    change e.hom ≫ e.inv ≫ l.left = l.left
    rw [Iso.hom_inv_id_assoc]
  let E₁ := M.sheaf.restrictAppIso i ⊤
  let E₂ := chartEquiv M t
  let E₃ := i.appIso ⊤ ≪≫ Scheme.ΓSpecIso (CommRingCat.of R)
  let E : moduleSpecΓFunctor.obj (M.sheaf.restrict i) ≃ₗ[R] R :=
    { toFun := fun x ↦ E₃.hom (E₂ (E₁.hom x))
      invFun := fun z ↦ E₁.inv (E₂.symm (E₃.inv z))
      left_inv := fun x ↦ by
        change E₁.inv (E₂.symm (E₃.inv (E₃.hom (E₂ (E₁.hom x))))) = x
        rw [Iso.hom_inv_id_apply E₃, LinearEquiv.symm_apply_apply, Iso.hom_inv_id_apply E₁]
      right_inv := fun z ↦ by
        change E₃.hom (E₂ (E₁.hom (E₁.inv (E₂.symm (E₃.inv z))))) = z
        rw [Iso.inv_hom_id_apply E₁, LinearEquiv.apply_symm_apply, Iso.inv_hom_id_apply E₃]
      map_add' := fun x y ↦ by
        change E₃.hom (E₂ (E₁.hom (x + y))) = E₃.hom (E₂ (E₁.hom x)) + E₃.hom (E₂ (E₁.hom y))
        rw [map_add, map_add, map_add]
      map_smul' := fun c x ↦ by
        let c' : Γ(A.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv c
        let x' : Γ(M.sheaf.restrict i, ⊤) := x
        change E₃.hom (E₂ (E₁.hom (c' • x'))) = c * E₃.hom (E₂ (E₁.hom x'))
        rw [Scheme.Modules.smul_restrictAppIso_hom_apply, E₂.map_smul]
        change E₃.hom ((i.appIso ⊤).inv c' * E₂ (E₁.hom x')) = _
        rw [map_mul]
        have h : E₃.hom ((i.appIso ⊤).inv c') = c := by
          change (Scheme.ΓSpecIso (CommRingCat.of R)).hom
            ((i.appIso ⊤).hom ((i.appIso ⊤).inv c')) = c
          rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
        rw [h] }
  refine ⟨E, fun s ↦ ?_⟩
  let x := M.sheaf.presheaf.map W.leTop.op s
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom ((i.appIso ⊤).hom (chartValue M t x)) =
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom (l.left.appTop (M.functionVal ⊤ s))
  congr 1
  have hδ (z : Γ(Q.scheme.left, W)) :
      (i.appIso ⊤).hom z = e.hom.appTop (W.topIso.inv z) := by
    have hwa : (⊤ : A.left.Opens) ≤ i ⁻¹ᵁ W := (i.preimage_image_eq ⊤).ge
    have hwb : (⊤ : A.left.Opens) ≤ (e.hom ≫ W.ι) ⁻¹ᵁ W := he ▸ hwa
    calc
      _ = evalOn i W hwa z := congrArg (fun f : Γ(Q.scheme.left, W) ⟶ Γ(A.left, ⊤) ↦ f z)
        (i.appIso_hom' ⊤)
      _ = evalOn (e.hom ≫ W.ι) W hwb z := evalOn_congr he.symm W hwa hwb z
      _ = e.hom.appTop (W.topIso.inv z) := by
        rw [← evalOn_top, ← evalOn_open]
        exact (evalOn_comp e.hom W.ι W ⊤ (by simp) (by simp) hwb z).symm
  have hl : (⊤ : A.left.Opens) ≤ l.left ⁻¹ᵁ (Q.projection.left ⁻¹ᵁ W) :=
    (i.preimage_image_eq ⊤).ge
  have hl' : (⊤ : A.left.Opens) ≤ (e.hom ≫ t.lift.left) ⁻¹ᵁ (Q.projection.left ⁻¹ᵁ W) :=
    htl ▸ hl
  have hc := evalOn_comp e.hom t.lift.left _ ⊤ (lift_in_open t) (by simp) hl'
    (M.functionVal W x)
  rw [hδ, chartValue_eq, ← evalOn_top]
  refine hc.trans ((evalOn_congr htl _ hl' hl _).trans ?_)
  have hn := PresheafOfModules.naturality_apply M.functions.val W.leTop.op s
  change M.functionVal W x = G.val.X.left.presheaf.map
    (homOfLE (show Q.projection.left ⁻¹ᵁ W ≤ (⊤ : G.val.X.left.Opens) from le_top)).op
      (M.functionVal ⊤ s) at hn
  exact (congrArg (evalOn l.left _ hl) hn).trans (evalOn_restrict l.left _ hl (M.functionVal ⊤ s))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 650000 in
private theorem sectionFunction_atLift (S : SocleModel P U χ)
    {L : AssociatedBundle Q a S.projection χ} (M : SectionRealization L)
    (x : Γ(M.sheaf, ⊤)) (f : S.A)
    (h : Q.projection.left ≫ Q.scheme.left.topIso.inv ≫ (M.sections ⊤ x).val =
      (prod.lift (𝟙 G.val.X) (coordinateFunction S.groupIso f) ≫ L.trivialization).left)
    {R : TestAlgebra k} (l : Points G.val.X R) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom (l.left.appTop (M.functionVal ⊤ x)) =
      restrictToChart S.groupIso l f := by
  let T := (testSpec k).obj (op R)
  let i := l.left ≫ Q.projection.left ≫ Q.scheme.left.topIso.inv
  have hi : i ≫ (⊤ : Q.scheme.left.Opens).ι = l.left ≫ Q.projection.left := by
    simp only [i, Category.assoc, Scheme.toIso_inv_ι, Category.comp_id]
  obtain ⟨z, hz, hz'⟩ := M.evaluation ⊤ x T l i hi (by simp)
  have h' : i ≫ (M.sections ⊤ x).val =
      (prod.lift l (l ≫ coordinateFunction S.groupIso f) ≫ L.trivialization).left := by
    have hw := congrArg (l.left ≫ ·) h
    change l.left ≫ Q.projection.left ≫ Q.scheme.left.topIso.inv ≫ (M.sections ⊤ x).val =
      (l ≫ prod.lift (𝟙 G.val.X) (coordinateFunction S.groupIso f) ≫ L.trivialization).left at hw
    rw [← Category.assoc l, prod.comp_lift, Category.comp_id] at hw
    simpa only [i, Category.assoc] using hw
  have eq : z = l ≫ coordinateFunction S.groupIso f :=
    coordinate_unique L l z _ (Over.OverMorphism.ext (hz'.symm.trans h'))
  rw [restrictToChart_eval] at eq
  change lineCoordinate z = evalOn l.left ⊤ (by simp) (M.functionVal ⊤ x) at hz
  rw [eq, evalOn_top] at hz
  rw [← hz]
  exact lineCoordinate_linePoint R _

end ChartSections

section SteinbergEvaluation

open Specs.AssociatedFlagLineSheaves (SectionRealization groundScalars)
open Specs.LinePushforwardProjection (chartSections IsLine)
open Specs.FlagRelativeFrobeniusAtlas
open Specs.SteinbergDimension (IsHalfPositiveRootSum)
open Specs.GeometricRadicals (IsUnipotentRadical)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open QuotientEmbedding (Presentation)
open Scheme.Modules
open LinearAlgebraicGroups.FlagRelativeFrobeniusAtlas
  (relativeFrobenius relativeFrobenius_unique flagFrobeniusCellCover relativeFrobenius_formula)
open LinearAlgebraicGroups.LinePushforwardProjection
  (restrictPushforward affineSectionsIso affinePushforward quasicoherentOfLine)
open LinearAlgebraicGroups.AssociatedFlagLineSheaves
  (globalCovariantSections invertibleSectionSheaf)
open private isIso_of_open_restrictions
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.AssociatedFlagLineSheaves

variable (p r : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]
  {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
  {b : BorelProjection P} {L : AssociatedBundle Q a b χ}

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
private theorem evaluationIsoOnChart {I : Type u} [Fintype I] [DecidableEq I] {n : ℕ}
    (M : SectionRealization L) (s : I → Γ(M.sheaf, ⊤))
    (l : affineChart k n ⟶ G.val.X) [IsOpenImmersion (l ≫ Q.projection).left]
    (j : affineChart k n ⟶ (twist p r).obj Q.scheme) [IsOpenImmersion j.left]
    (sq : IsPullback (powerMorphism (p ^ r) n).left (l ≫ Q.projection).left j.left
      ((relativeFrobenius p r).app Q.scheme).left)
    (v : I → MvPolynomial (Fin n) k)
    (hv : ∀ i, (Scheme.ΓSpecIso _).hom (l.left.appTop (M.functionVal ⊤ (s i))) = v i)
    (B : Module.Basis I (MvPolynomial (Fin n) k) (powerModule k n (p ^ r)))
    (hB : ∀ i, (B i : MvPolynomial (Fin n) k) = v i) :
    let F := ((relativeFrobenius p r).app Q.scheme).left
    let N := (pushforward F).obj M.sheaf
    IsIso ((restrictFunctor j.left).map (evaluationMap (M := N) s)) := by
  let F := ((relativeFrobenius p r).app Q.scheme).left
  let N := (pushforward F).obj M.sheaf
  let R := MvPolynomial (Fin n) k
  let RC := CommRingCat.of R
  let φ : RC ⟶ RC := CommRingCat.ofHom (powerMap (p ^ r) n).toRingHom
  let i := (l ≫ Q.projection).left
  let T := M.sheaf.restrict i
  let P' := (pushforward (Spec.map φ)).obj T
  obtain ⟨e, he⟩ := restrictPushforward i j.left sq M.sheaf
  obtain ⟨d, hd⟩ := affineSectionCoordinates M
    (R := CommAlgCat.of k R) l
  let sectionIso : moduleSpecΓFunctor.obj P' ≅ powerModule k n (p ^ r) :=
    affineSectionsIso φ T ≪≫ (ModuleCat.restrictScalars φ.hom).mapIso d.toModuleIso
  have hSectionIso (s₀ : Γ(T, ⊤)) : sectionIso.hom s₀ = d s₀ := rfl
  let ev : freeModule _ I ⟶ N := evaluationMap s
  let u := (restrictFreeIso j.left I).hom ≫ (restrictFunctor j.left).map ev ≫ e.hom
  let B' := B.map sectionIso.symm.toLinearEquiv
  have hb (t : I) : u.app ⊤ (freeGenerator (Spec RC) t) = B' t := by
    apply (ConcreteCategory.bijective_of_isIso sectionIso.hom).injective
    change sectionIso.hom (u.app ⊤ (freeGenerator (Spec RC) t)) =
      sectionIso.hom (sectionIso.inv (B t))
    have hs := congrArg (fun f ↦ f (s t)) he
    change e.hom.app ⊤ (chartSections j.left N (s t)) = chartSections i M.sheaf (s t) at hs
    have hu : u.app ⊤ (freeGenerator (Spec RC) t) = chartSections i M.sheaf (s t) := by
      have hRestrict :
          (restrictFreeIso j.left I).hom.app ⊤ (freeGenerator (Spec RC) t) =
            chartSections j.left (freeModule _ I) (freeGenerator _ t) :=
        restrictFreeIso_generator j.left t
      change e.hom.app ⊤ (((restrictFunctor j.left).map ev).app ⊤
        ((restrictFreeIso j.left I).hom.app ⊤ (freeGenerator (Spec RC) t))) = _
      rw [hRestrict, chartSections_natural,
        show ev.app ⊤ (freeGenerator _ t) = s t from evaluationMap_generator (M := N) s t]
      exact hs
    rw [hu, Iso.inv_hom_id_apply, hSectionIso, hd]
    exact (hv t).trans (hB t).symm
  have hline : IsLine M.sheaf := fun x ↦ by
    obtain ⟨V, hx, _, e⟩ := invertibleSectionSheaf M x
    exact ⟨V, hx, e⟩
  have hM : M.sheaf.IsQuasicoherent := quasicoherentOfLine hline
  have ht : T.IsQuasicoherent := inferInstance
  have hp : P'.IsQuasicoherent := (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr
    (affinePushforward φ T ((isQuasicoherent_iff_isIso_fromTildeΓ _).mp ht))
  have hu : IsIso u := affineFreeMap_isIso u hp B' hb
  have hu' : IsIso ((restrictFunctor j.left).map ev ≫ e.hom) :=
    IsIso.of_isIso_comp_left (f := (restrictFreeIso j.left I).hom) _
  exact IsIso.of_isIso_comp_right ((restrictFunctor j.left).map ev) e.hom

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1700000 in
set_option linter.style.haveILetI false in
/-- Relative Frobenius sends the Steinberg line to the free sheaf on the
Steinberg module through adjoint evaluation. -/
theorem steinbergEvaluationIso : SteinbergEvaluationIso.{u} := by
  intro k _ _ p r _ _ hr G hG hsc P _ U hU ρ hρ S Q a L M F hF
  classical
  have eq := relativeFrobenius_unique p r Q.scheme F hF
  subst F
  let F := (relativeFrobenius p r).app Q.scheme
  let Y := ((twist p r).obj Q.scheme).left
  let N := (pushforward F.left).obj M.sheaf
  letI : Module k Γ(M.sheaf, ⊤) := Module.compHom _ (groundScalars Q.scheme).hom
  obtain ⟨E, hE⟩ := globalCovariantSections M S.groupIso S.borelIso S.restriction S.character
    S.restriction_spec S.character_spec S.coordinate S.coordinate_spec
  let s (i : S.J) : Γ(M.sheaf, ⊤) :=
    E.symm (S.inducedBasis.equivFun.symm (S.socleBasis i : S.I → k))
  have hs (i : S.J) : Q.projection.left ≫ Q.scheme.left.topIso.inv ≫ (M.sections ⊤ (s i)).val =
      (prod.lift (𝟙 G.val.X) (coordinateFunction S.groupIso (socleFunction S (S.socleBasis i))) ≫
        L.trivialization).left := by
    have h := hE (s i)
    have h' : (E (s i) : S.A) = socleFunction S (S.socleBasis i) := by
      simp only [s, LinearEquiv.apply_symm_apply]
      rfl
    rw [h'] at h
    exact h
  let ev : freeModule Y S.J ⟶ N := evaluationMap s
  obtain ⟨F', C, e, hF', hn, _, hcharts, hcover⟩ := flagFrobeniusCellCover p r Q hr
  have heq : F' = (relativeFrobenius p r).app Q.scheme :=
    relativeFrobenius_unique p r Q.scheme F' hF'
  subst F'
  have hdim := LinearAlgebraicGroups.Representation.SteinbergDimension.dimension
    p r hr hG hsc P ρ hρ U hU S
  have hcard : Fintype.card S.J = (p ^ r) ^ C.order.length :=
    (Module.finrank_eq_card_basis S.socleBasis).symm.trans (hdim.trans (by rw [hn]))
  have hev : IsIso ev := by
    apply isIso_of_open_restrictions
    intro y
    obtain ⟨g, hy⟩ := hcover y
    let j := e.hom ≫ (twist p r).map (translatedChart Q C g)
    let l := translatedLift C g
    haveI : IsOpenImmersion (l ≫ Q.projection).left := (hcharts g).1
    haveI : IsOpenImmersion j.left := (hcharts g).2.1
    have sq := (hcharts g).2.2.2
    let v (i : S.J) : MvPolynomial (Fin C.order.length) k :=
      restrictToChart S.groupIso l (socleFunction S (S.socleBasis i))
    obtain ⟨B, hB⟩ := polynomialSectionBasis C.order.length (p ^ r)
      (Nat.pow_pos (Fact.out : p.Prime).pos) hcard v (C := kernelAlgebra p r S.A) (by
        intro x
        obtain ⟨f, hf, hi⟩ := polynomialChartFibers p r hr hU ρ hρ S Q l j sq x
        refine ⟨f, hf, ?_⟩
        let m := f.toLinearMap.comp ((restrictToChart S.groupIso l).toLinearMap.comp (socleFunction S))
        exact S.socleBasis.linearIndependent.map' m (LinearMap.ker_eq_bot.mpr hi))
    have hj : IsIso ((restrictFunctor j.left).map ev) :=
      evaluationIsoOnChart p r M s l j sq v
        (fun i ↦ sectionFunction_atLift S M (s i) _ (hs i) l) B hB
    let V := j.left.opensRange
    refine ⟨V, hy, ?_⟩
    let i := j.left.isoOpensRange.inv
    have h : i ≫ j.left = V.ι := j.left.isoOpensRange_inv_comp
    have hiso : IsIso (((restrictFunctor j.left) ⋙ (restrictFunctor i)).map ev) :=
      Functor.map_isIso (restrictFunctor i) ((restrictFunctor j.left).map ev)
    exact (NatIso.isIso_map_iff ((restrictFunctorCongr h).symm ≪≫ restrictFunctorComp i j.left)
      ev).mpr hiso
  refine ⟨asIso ev, fun i ↦ ?_⟩
  change Q.projection.left ≫ Q.scheme.left.topIso.inv ≫
    (M.sections ⊤ (ev.app ⊤ (freeGenerator Y i))).val = _
  rw [show ev.app ⊤ (freeGenerator Y i) = s i from evaluationMap_generator (M := N) s i]
  exact hs i

end SteinbergEvaluation

section MarkedTarget

open Specs.AssociatedFlagLineSheaves (SectionRealization)
open Specs.LinePushforwardProjection (chartSections)
open Specs.FlagRelativeFrobeniusAtlas (MarkedFlagTwist)
open Scheme.Modules
open LinearAlgebraicGroups.LinePushforwardProjection (restrictPushforward)
open private comp_character_pow from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.AssociatedFlagLineSheaves

set_option backward.isDefEq.respectTransparency false in
/-- The transported Borel character gives the canonical line pullback on the
marked presentation of the scalar twist. -/
theorem markedFlagFrobeniusLinePullback : MarkedFlagFrobeniusLinePullback.{u} := by
  intro k _ _ p r _ _ G P Q b t ν a a' Lq L' Mq M'
  apply LinearAlgebraicGroups.AssociatedFlagLineSheaves.associatedSheafPullback
    Mq M' (markedQuotientMap t)
  exact (comp_character_pow b.projection ν _).trans (t.character_pullback ν).symm

set_option backward.isDefEq.respectTransparency false in
private theorem chartSections_id {X : Scheme.{u}} (M : X.Modules) (s : Γ(M, ⊤)) :
    (restrictFunctorId.hom.app M).app ⊤ (chartSections (𝟙 X) M s) = s := by
  have h : 𝟙 X ''ᵁ (⊤ : X.Opens) = ⊤ := by simp
  rw [restrictFunctorId_hom_app_app]
  change M.presheaf.map (eqToHom h.symm).op
    (M.presheaf.map (𝟙 X ''ᵁ (⊤ : X.Opens)).leTop.op s) = s
  rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
  rw [show (𝟙 X ''ᵁ (⊤ : X.Opens)).leTop.op ≫ (eqToHom h.symm).op = 𝟙 _ from
    Subsingleton.elim _ _, M.presheaf.map_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 850000 in
/-- Evaluation on the marked target uses the same global socle sections. -/
theorem markedSteinbergEvaluationIso : MarkedSteinbergEvaluationIso.{u} := by
  intro k _ _ p r _ _ hr G hG hsc P _ U hU ρ hρ σ S Q a Lσ Mσ t
  let F := t.flagFrobenius ≫ t.comparison.hom
  obtain ⟨e, he⟩ := steinbergEvaluationIso p r hr hG hsc P U hU ρ hρ S Mσ F t.flag_formula
  let j := t.comparison.hom.left
  let f := t.flagFrobenius.left
  let X := Q.scheme.left
  let M := Mσ.sheaf
  let N := (pushforward F.left).obj M
  have : IsIso j := (Over.forget _).map_isIso t.comparison.hom
  have sq : IsPullback f (𝟙 X) j F.left := IsPullback.of_vert_isIso ⟨(Category.id_comp _).symm⟩
  obtain ⟨d, hd⟩ := restrictPushforward (𝟙 X) j sq M
  let iM := restrictFunctorId.app M
  let e' := restrictFreeIso j S.J ≪≫ (restrictFunctor j).mapIso e ≪≫ d ≪≫
    (pushforward f).mapIso iM
  refine ⟨e', fun i ↦ ?_⟩
  have h : e'.hom.app ⊤ (freeGenerator _ i) = e.hom.app ⊤ (freeGenerator _ i) := by
    change iM.hom.app ⊤ (d.hom.app ⊤ (((restrictFunctor j).map e.hom).app ⊤
      ((restrictFreeIso j S.J).hom.app ⊤ (freeGenerator _ i)))) = _
    rw [restrictFreeIso_generator, chartSections_natural]
    let s := e.hom.app ⊤ (freeGenerator _ i)
    have hs : d.hom.app ⊤ (chartSections j N s) = chartSections (𝟙 X) M s :=
      congrArg (fun m ↦ m s) hd
    rw [hs]
    exact chartSections_id M s
  change Q.projection.left ≫ Q.scheme.left.topIso.inv ≫
    (Mσ.sections ⊤ (e'.hom.app ⊤ (freeGenerator _ i))).val = _
  rw [h]
  exact he i

end MarkedTarget

section ProjectionFormula

open CategoryTheory.MonoidalCategory
open Scheme.Modules
open Specs.LinePushforwardProjection (tensorPresheaf tensorModule tensorToSheaf tensorSection IsLine)
open Specs.AssociatedFlagLineSheaves (SectionPairing IsTensorProduct SectionRealization)

set_option backward.isDefEq.respectTransparency false in
private def tensorModuleCongr {X : Scheme.{u}} {M M' N N' : X.Modules}
    (e : M ≅ M') (f : N ≅ N') : tensorModule M N ≅ tensorModule M' N' :=
  let e' : (M.val : PresheafOfModulesOfCommRing X.presheaf) ≅ M'.val :=
    (SheafOfModules.forget X.ringCatSheaf).mapIso e
  let f' : (N.val : PresheafOfModulesOfCommRing X.presheaf) ≅ N'.val :=
    (SheafOfModules.forget X.ringCatSheaf).mapIso f
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (tensorIso (C := PresheafOfModulesOfCommRing X.presheaf) e' f')

set_option backward.isDefEq.respectTransparency false in
private def tensorPresheafLift {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
    {M N K : PresheafOfModulesOfCommRing.{u} R}
    (b : ∀ U, M.obj U →ₗ[R.obj U] N.obj U →ₗ[R.obj U] K.obj U)
    (h : ∀ {U V} (i : U ⟶ V) x y, K.map i (b U x y) = b V (M.map i x) (N.map i y)) :
    M ⊗ N ⟶ K :=
  PresheafOfModulesOfCommRing.homMk
    (fun U ↦ ModuleCat.ofHom (TensorProduct.lift (b U))) (by
      intro U V i
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro x y
      change TensorProduct.lift (b V) ((M ⊗ N : PresheafOfModulesOfCommRing R).map i
          (x ⊗ₜ[R.obj U] y)) = K.map i (TensorProduct.lift (b U) (x ⊗ₜ[R.obj U] y))
      erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul (M₁ := M) (M₂ := N) i x y]
      rw [TensorProduct.lift.tmul, TensorProduct.lift.tmul]
      exact (h i x y).symm)

set_option backward.isDefEq.respectTransparency false in
private def pairingToPresheaf {X : Scheme.{u}} {M N K : X.Modules}
    (b : SectionPairing M N K) : tensorPresheaf M N ⟶ K.val :=
  tensorPresheafLift (R := X.presheaf) (M := M.val) (N := N.val) (K := K.val)
    (fun U ↦ b.app U.unop) (fun i x y ↦ b.naturality i.unop x y)

set_option backward.isDefEq.respectTransparency false in
private theorem pairingToPresheaf_tmul {X : Scheme.{u}} {M N K : X.Modules}
    (b : SectionPairing M N K) (U : X.Opens) (x : Γ(M, U)) (y : Γ(N, U)) :
    ((pairingToPresheaf b).app (op U)).hom (x ⊗ₜ[Γ(X, U)] y) = b.app U x y :=
  TensorProduct.lift.tmul x y

set_option backward.isDefEq.respectTransparency false in
private def tensorSheafPairing {X : Scheme.{u}} (M N : X.Modules) :
    SectionPairing M N (tensorModule M N) where
  app U := TensorProduct.curry ((tensorToSheaf M N).app (op U)).hom
  naturality := by
    intro U V i x y
    have h := PresheafOfModules.naturality_apply (tensorToSheaf M N) i.op (x ⊗ₜ y)
    erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul
      (M₁ := M.val) (M₂ := N.val)] at h
    exact h.symm

set_option backward.isDefEq.respectTransparency false in
private theorem tensorSheaf_universal {X : Scheme.{u}} (M N : X.Modules) :
    IsTensorProduct (tensorSheafPairing M N) := by
  intro K b
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let e := adj.homEquiv (tensorPresheaf M N) K
  let a : tensorModule M N ⟶ K := e.symm (pairingToPresheaf b)
  have compare (f : tensorModule M N ⟶ K) (U : X.Opens) (x : Γ(M, U)) (y : Γ(N, U)) :
      (e f).app (op U) (x ⊗ₜ y) = f.app U (tensorSection M N U x y) := by
    have h := adj.homEquiv_naturality_right (𝟙 (tensorModule M N)) f
    exact congrArg (fun g : tensorPresheaf M N ⟶ K.val ↦ g.app (op U) (x ⊗ₜ y)) h
  refine ⟨a, fun U x y ↦ ?_, fun f hf ↦ ?_⟩
  · change a.app U (tensorSection M N U x y) = _
    rw [← compare a, e.apply_symm_apply]
    exact pairingToPresheaf_tmul b U x y
  · apply e.injective
    rw [e.apply_symm_apply]
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    exact (compare f U.unop x y).trans
      ((hf U.unop x y).trans (pairingToPresheaf_tmul b U.unop x y).symm)

private theorem sectionPairing_tensorIso {X : Scheme.{u}} {M N K : X.Modules}
    (m : SectionPairing M N K) (hm : IsTensorProduct m) : Nonempty (tensorModule M N ≅ K) := by
  obtain ⟨f, hf, hfu⟩ := tensorSheaf_universal M N K m
  obtain ⟨g, hg, hgu⟩ := hm _ (tensorSheafPairing M N)
  refine ⟨⟨f, g, ?_, ?_⟩⟩
  · have h (U : X.Opens) (x : Γ(M, U)) (y : Γ(N, U)) :
        (f ≫ g).app U ((tensorSheafPairing M N).app U x y) =
          (tensorSheafPairing M N).app U x y := by
      rw [Hom.comp_app, ConcreteCategory.comp_apply, hf, hg]
    obtain ⟨j, _, hj⟩ := tensorSheaf_universal M N _ (tensorSheafPairing M N)
    exact (hj (f ≫ g) h).trans (hj (𝟙 _) (fun _ _ _ ↦ rfl)).symm
  · have h (U : X.Opens) (x : Γ(M, U)) (y : Γ(N, U)) :
        (g ≫ f).app U (m.app U x y) = m.app U x y := by
      rw [Hom.comp_app, ConcreteCategory.comp_apply, hg, hf]
    obtain ⟨j, _, hj⟩ := hm K m
    exact (hj (g ≫ f) h).trans (hj (𝟙 _) (fun _ _ _ ↦ rfl)).symm

open QuotientEmbedding (Presentation)

private theorem associatedIsLine {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
    {b : BorelProjection P} {L : AssociatedBundle Q a b χ} (M : SectionRealization L) :
    IsLine M.sheaf := fun y ↦ by
  obtain ⟨V, hy, _, e⟩ := LinearAlgebraicGroups.AssociatedFlagLineSheaves.invertibleSectionSheaf M y
  exact ⟨V, hy, e⟩

set_option backward.isDefEq.respectTransparency false in
private theorem projectionFormulaForLines {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
    {b : BorelProjection P} {ψ : Character P.torus.group}
    {L₁ : AssociatedBundle Q a b χ} {L₂ : AssociatedBundle Q a b ψ}
    {L₃ : AssociatedBundle Q a b (χ * ψ)}
    (M₁ : SectionRealization L₁) (M₂ : SectionRealization L₂) (M₃ : SectionRealization L₃)
    {Y : Scheme.{u}} (f : Q.scheme.left ⟶ Y) {N : Y.Modules} (hN : IsLine N)
    {I : Type u} (e : freeModule Y I ≅ (pushforward f).obj M₁.sheaf)
    (w : (Scheme.Modules.pullback f).obj N ≅ M₂.sheaf) :
    Nonempty ((pushforward f).obj M₃.sheaf ≅ tensorModule (freeModule Y I) N) := by
  obtain ⟨m, _, _, hm⟩ :=
    LinearAlgebraicGroups.AssociatedFlagLineSheaves.characterMultiplication M₁ M₂ M₃
  obtain ⟨d⟩ := sectionPairing_tensorIso m hm
  obtain ⟨proj, _⟩ := LinearAlgebraicGroups.LinePushforwardProjection.projectionFormula f M₁.sheaf N hN
  exact ⟨(tensorModuleCongr e (Iso.refl _) ≪≫ proj ≪≫
    (pushforward f).mapIso (tensorModuleCongr (Iso.refl _) w ≪≫ d)).symm⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 850000 in
/-- The Steinberg evaluation and the projection formula give the twisted
pushforward for every character of the marked torus. -/
theorem steinbergFrobeniusFormula : SteinbergFrobeniusFormula.{u} := by
  intro k _ _ p r _ _ hr G hG hsc P _ U hU ρ hρ σ S ν Q a Lσ Lν Lsum Mσ Mν Msum ha F hF
  obtain ⟨e, _⟩ := steinbergEvaluationIso p r hr hG hsc P U hU ρ hρ S Mσ F hF
  obtain ⟨Lq⟩ := constructAssociatedBundle S.projection (ν ^ (p ^ r)) a ha
    (coversWithSections_of_local Q.projection (flagCover_and_polynomialChart Q).1)
  obtain ⟨Mq⟩ := LinearAlgebraicGroups.AssociatedFlagLineSheaves.associatedSectionSheaf Lq
  obtain ⟨w, _⟩ := flagFrobeniusLinePullback p r Mν Mq F hF
  exact projectionFormulaForLines Mσ Mq Msum F.left (associatedIsLine Mν) e w

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 850000 in
/-- The pushforward is the Steinberg module tensored with the associated line
of the transported character on the marked target. -/
theorem markedSteinbergFrobeniusFormula : MarkedSteinbergFrobeniusFormula.{u} := by
  intro k _ _ p r _ _ hr G hG hsc P _ U hU ρ hρ σ S ν Q a t a' Lσ Lsum Lν' Mσ Msum Mν' ha
  obtain ⟨e, _⟩ := markedSteinbergEvaluationIso p r hr hG hsc P U hU ρ hρ S Mσ t
  obtain ⟨Lq⟩ := constructAssociatedBundle S.projection (ν ^ (p ^ r)) a ha
    (coversWithSections_of_local Q.projection (flagCover_and_polynomialChart Q).1)
  obtain ⟨Mq⟩ := LinearAlgebraicGroups.AssociatedFlagLineSheaves.associatedSectionSheaf Lq
  obtain ⟨w, _⟩ := markedFlagFrobeniusLinePullback p r t ν Mq Mν'
  exact projectionFormulaForLines Mσ Mq Msum t.flagFrobenius.left (associatedIsLine Mν') e w

end ProjectionFormula

end LinearAlgebraicGroups.SteinbergFrobeniusPushforward
