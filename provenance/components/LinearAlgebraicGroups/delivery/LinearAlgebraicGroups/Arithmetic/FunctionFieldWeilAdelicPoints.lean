import Specs.LinearAlgebraicGroups.Arithmetic.FunctionFieldWeilAdelicPoints
import LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction
import LinearAlgebraicGroups.Arithmetic.AdelicLatticeBounds
import LinearAlgebraicGroups.Arithmetic.AdelicGroups
import Batteries.Tactic.OpenPrivate
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular

open CategoryTheory Topology Filter
open scoped RatFunc TensorProduct

universe u

noncomputable section

namespace LinearAlgebraicGroups.Arithmetic.FunctionFieldWeilAdelicPoints

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.FunctionFieldWeilAdelicPoints
open Specs.IntegralModels (MatrixRealization)
open AdelicGroups
open LatticeCompletionDecompositionSpec (IntrinsicComparison)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 120000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-- Restriction of a nontrivial place along a finite extension remains nontrivial. -/
def restrictFunctionPlace {k K : Type*} [Field k] [Field K] [Algebra k K]
    [Algebra.IsIntegral k K] (w : FunctionPlace K) : FunctionPlace k := by
  refine ⟨w.val.comap (algebraMap k K), ?_⟩
  intro he
  have h (x : k) : algebraMap k K x ∈ w.val := by
    change x ∈ w.val.comap (algebraMap k K)
    rw [he]
    exact ValuationSubring.mem_top x
  let f : k →+* w.val := (algebraMap k K).codRestrict w.val h
  let : Algebra k w.val := f.toAlgebra
  let : IsScalarTower k w.val K := IsScalarTower.of_algebraMap_eq' rfl
  apply w.property
  apply top_unique
  intro x _
  have hx := (Algebra.IsIntegral.isIntegral (R := k) x).tower_top (A := w.val)
  let : IsIntegrallyClosed w.val := by
    rw [← w.val.valuationSubring_valuation]
    exact (Valuation.integer.integers w.val.valuation).isIntegrallyClosed
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
  exact ha ▸ a.property
section Completions

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Polynomial
open LatticeCompletionDecompositionSpec (IntrinsicComparison)
open private LinearAlgebraicGroups.Arithmetic.exists_adic_of_contains from
  LinearAlgebraicGroups.Arithmetic.GlobalPlaces
open private adicPlace adicPlaceEquiv placeCompletionEquiv placeCompletionEquiv_embedding
  placeProductComparison from LinearAlgebraicGroups.Arithmetic.LatticeCompletionDecomposition

/-- Compare the intrinsic base completion with the adic completion on a chart
whose ring lies in the valuation ring. -/
private theorem intrinsicComparison_of_chart
    {R k K : Type u} [CommRing R] [IsDedekindDomain R] [Field k] [Field K]
    [Algebra R k] [IsFractionRing R k] [Algebra k K] [FiniteDimensional k K]
    [Algebra.IsSeparable k K] (v : FunctionPlace k)
    (hR : ∀ r : R, algebraMap R k r ∈ v.val) :
    letI : Algebra k v.Completion := v.embedding.toAlgebra
    IntrinsicComparison (k := k) (K := K) (B := v.Completion) {w : FunctionPlace K |
      w.val.comap (algebraMap k K) = v.val} := by
  classical
  let : Algebra k v.Completion := v.embedding.toAlgebra
  let : Algebra R K := Algebra.compHom K (algebraMap R k)
  let : IsScalarTower R k K := IsScalarTower.of_algebraMap_eq' rfl
  let A := integralClosure R K
  let : IsDedekindDomain A := integralClosure.isDedekindDomain R k K
  let : Module.IsTorsionFree R K :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      ((algebraMap k K).injective.comp (IsFractionRing.injective R k))
  let : Module.IsTorsionFree R A := IsIntegralClosure.isTorsionFree R K
  let : IsFractionRing A K := IsIntegralClosure.isFractionRing_of_finite_extension R k K A
  let : Algebra.IsIntegral R A := IsIntegralClosure.isIntegral_algebra R K
  obtain ⟨p, hp⟩ := LinearAlgebraicGroups.Arithmetic.exists_adic_of_contains v hR
  have he : adicPlace p = v := Subtype.ext hp
  let c := placeCompletionEquiv p v he
  let hval := (Valuation.isEquiv_iff_valuationSubring (p.valuation k) v.val.valuation).mpr
    (hp.trans v.val.valuationSubring_valuation.symm)
  have hc : Continuous c.symm :=
    (adicCompletion.uniformEquiv k p).symm.continuous.comp
      (UniformSpace.Completion.mapEquiv hval.uniformEquiv).symm.continuous
  let b : v.Completion ≃ₐ[k] p.adicCompletion k :=
    { c.symm with
      commutes' := fun x => c.symm_apply_eq.mpr (placeCompletionEquiv_embedding p v he x).symm }
  let i := adicPlaceEquiv (k := k) (A := A) (K := K) p
  let j : {w : FunctionPlace K // w.val.comap (algebraMap k K) =
      (p.valuation k).valuationSubring} ≃
      {w : FunctionPlace K // w.val.comap (algebraMap k K) = v.val} :=
    Equiv.subtypeEquivRight fun _ => by rw [hp]
  let e := i.trans j
  refine ⟨Fintype.ofEquiv _ e, ?_⟩
  exact placeProductComparison p b hc e Subtype.val (fun _ => rfl)

private theorem rationalParameter_rationalMap (F : Type u) [Field F] :
    (rationalParameter F).rationalMap = AlgHom.id F F⟮X⟯ := by
  ext x : 1
  change (RatFunc.algEquivOfTranscendental RatFunc.X RatFunc.transcendental_X x).val = x
  rw [RatFunc.algEquivOfTranscendental_apply]
  simp only [RatFunc.aeval_X_left_eq_algebraMap]
  exact RatFunc.num_div_denom x

/-- The local scalar extension is the product of the actual extension
completions. The inverse-parameter chart provides the base pole case. -/
theorem functionCompletionComparison
    {F K : Type u} [Field F] [Finite F] [Field K] [Algebra F K]
    (t : SeparatingParameter F K) (v : FunctionPlace F⟮X⟯) :
    letI := t.rationalAlgebra
    letI : Algebra F⟮X⟯ v.Completion := v.embedding.toAlgebra
    IntrinsicComparison (k := F⟮X⟯) (K := K) (B := v.Completion) {w : FunctionPlace K |
      w.val.comap t.rationalMap.toRingHom = v.val} := by
  classical
  let := t.rationalAlgebra
  by_cases hv : RatFunc.X ∈ v.val
  · apply intrinsicComparison_of_chart (R := F[X]) v
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add] using add_mem hp hq
    | monomial n c =>
      have hc : algebraMap F F⟮X⟯ c ∈ v.val := by
        rw [← v.val.valuationSubring_valuation]
        exact FiniteField.valuation_algebraMap_le_one v.val.valuation c
      rw [RatFunc.algebraMap_monomial]
      exact mul_mem hc (pow_mem hv n)
  · let R := (RatFunc.inftyValuation F).valuationSubring
    let : IsDiscreteValuationRing R :=
      (RatFunc.inftyValuation F).valuationSubring_isDiscreteValuationRing
    apply intrinsicComparison_of_chart (R := R) v
    have he := ((rationalParameter F).comap_eq_infty_iff v).mpr hv
    rw [rationalParameter_rationalMap F] at he
    have hvR : v.val = R := he
    intro r
    rw [hvR]
    exact r.property

end Completions

section ProductPoints

open AlgebraicGeometry Opposite

private theorem groupFunctor_productEquiv {k I : Type u} [Field k]
    (V : TestAlgebra k ⥤ GrpCat.{u}) (A : TestAlgebra k)
    (E : coyoneda.obj (op A) ≅ V ⋙ forget GrpCat)
    (C : I → Type u) [∀ i, CommRing (C i)] [∀ i, Algebra k (C i)] :
    ∃ e : V.obj (CommAlgCat.of k (∀ i, C i)) ≃* (∀ i, V.obj (CommAlgCat.of k (C i))),
      ∀ g i, e g i = (V.map (CommAlgCat.ofHom (Pi.evalAlgHom k C i))).hom g := by
  let P := CommAlgCat.of k (∀ i, C i)
  let T (i : I) := CommAlgCat.of k (C i)
  let π (i : I) : P ⟶ T i := CommAlgCat.ofHom (Pi.evalAlgHom k C i)
  let φ : V.obj P →* (∀ i, V.obj (T i)) := MonoidHom.pi fun i => (V.map (π i)).hom
  suffices hφ : Function.Bijective φ from ⟨MulEquiv.ofBijective φ hφ, fun _ _ => rfl⟩
  let e (R : TestAlgebra k) : (A ⟶ R) ≃ V.obj R := (E.app R).toEquiv
  have he (i : I) (a : A ⟶ P) :
      e (T i) (a ≫ π i) = (V.map (π i)).hom (e P a) :=
    ConcreteCategory.congr_hom (E.hom.naturality (π i)) a
  constructor
  · intro a b hab
    apply (e P).symm.injective
    apply CommAlgCat.hom_ext
    ext x i
    have hh : e (T i) ((e P).symm a ≫ π i) = e (T i) ((e P).symm b ≫ π i) := by
      rw [he, he, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact congrFun hab i
    exact DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom ((e (T i)).injective hh)) x
  · intro b
    let a : A ⟶ P := CommAlgCat.ofHom (AlgHom.pi fun i => ((e (T i)).symm (b i)).hom)
    refine ⟨e P a, funext fun i => ?_⟩
    change (V.map (π i)).hom (e P a) = b i
    rw [← he, ← (e (T i)).apply_symm_apply (b i)]
    congr 1

/-- Affine group points on a product of test algebras are the product of
the point groups with the coordinate maps induced by evaluation. -/
theorem exists_groupPoints_productEquiv {k I : Type u} [Field k] (G : Specs.AffineAlgebraicGroup k)
    (C : I → Type u) [∀ i, CommRing (C i)] [∀ i, Algebra k (C i)] :
    let V := (groupPointsFunctor k).obj G.val
    ∃ e : V.obj (CommAlgCat.of k (∀ i, C i)) ≃* (∀ i, V.obj (CommAlgCat.of k (C i))),
      ∀ g i, e g i = (V.map (CommAlgCat.ofHom (Pi.evalAlgHom k C i))).hom g := by
  obtain ⟨A, ⟨j⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr G.property.1
  exact groupFunctor_productEquiv ((groupPointsFunctor k).obj G.val) A.unop
    (WeilRestriction.spectrumPoints A.unop G.val.X j) C

end ProductPoints

section LocalPoints

variable {k K R I : Type u} [Field k] [Field K] [Algebra k K]
    [CommRing R] [Algebra k R]
    {C : I → Type u} [∀ i, CommRing (C i)] [∀ i, Algebra K (C i)]

private theorem tmul_algebraMap (x : k) :
    algebraMap k R x ⊗ₜ[k] (1 : K) = (1 : R) ⊗ₜ[k] algebraMap k K x := by
  simpa only [Algebra.smul_def, mul_one] using TensorProduct.smul_tmul x (1 : R) (1 : K)

/-- A scalar extension comparison on rings gives the corresponding local
point comparison for the represented Weil restriction. -/
theorem exists_restrictedPoints_productEquiv
    {G : Specs.AffineAlgebraicGroup K} {W : Specs.AffineAlgebraicGroup k}
    (ρ : (groupPointsFunctor k).obj W.val ≅
      WeilRestriction.extendScalars k K ⋙ (groupPointsFunctor K).obj G.val)
    (e : R ⊗[k] K ≃+* (∀ i, C i))
    (f : ∀ i, R →+* C i)
    (ht : ∀ r x i, e (r ⊗ₜ[k] x) i = f i r * algebraMap K (C i) x) :
    let U := (groupPointsFunctor k).obj W.val
    let V := (groupPointsFunctor K).obj G.val
    ∃ (hf : ∀ i, (f i).comp (algebraMap k R) =
      (algebraMap K (C i)).comp (algebraMap k K))
      (E : U.obj (CommAlgCat.of k R) ≃* (∀ i, V.obj (CommAlgCat.of K (C i)))),
      ∀ g i, E g i = specializedPoint (G := G) (W := W) ρ (tensorSpecialization (f i) (hf i)) g := by
  let V := (groupPointsFunctor K).obj G.val
  have hf (i : I) : (f i).comp (algebraMap k R) =
      (algebraMap K (C i)).comp (algebraMap k K) := by
    apply RingHom.ext
    intro x
    have h := congrFun (congrArg e (tmul_algebraMap (R := R) (K := K) x)) i
    simpa only [ht, map_one, one_mul, mul_one, RingHom.comp_apply] using h
  let E : R ⊗[k] K ≃ₐ[K] (∀ i, C i) :=
    { e with
      commutes' := fun x => funext fun i => by
        change e ((1 : R) ⊗ₜ[k] x) i = algebraMap K (C i) x
        rw [ht, map_one, one_mul] }
  let j := CommAlgCat.isoMk E
  obtain ⟨p, hp⟩ := exists_groupPoints_productEquiv G C
  let g := ((ρ.app (CommAlgCat.of k R)) ≪≫ V.mapIso j).groupIsoToMulEquiv
  refine ⟨hf, g.trans p, ?_⟩
  intro u i
  have hmaps : (Pi.evalAlgHom K C i).comp E.toAlgHom = tensorSpecialization (f i) (hf i) := by
    ext z : 1
    induction z using TensorProduct.inductionOn with
    | tmul r x => exact (ht r x i).trans (tensorSpecialization_tmul _ _ _ _).symm
    | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  rw [MulEquiv.trans_apply, hp]
  have hh : j.hom ≫ CommAlgCat.ofHom (Pi.evalAlgHom K C i) =
      CommAlgCat.ofHom (tensorSpecialization (f i) (hf i)) := CommAlgCat.hom_ext hmaps
  have hmap := congrArg V.map hh
  rw [Functor.map_comp] at hmap
  exact ConcreteCategory.congr_hom hmap ((ρ.hom.app (CommAlgCat.of k R)).hom u)

end LocalPoints

section RestrictedProducts

open Filter
open scoped RestrictedProduct

variable {I J : Type*} {A : I → Type*} {B : J → Type*}
  [∀ i, Group (A i)] [∀ j, Group (B j)]
  [∀ i, TopologicalSpace (A i)] [∀ j, TopologicalSpace (B j)]
  (p : J → I) (U : ∀ i, Subgroup (A i)) (V : ∀ j, Subgroup (B j))

/-- Join local comparisons over the fibers of the restriction of places.
Finite fibers and almost-everywhere agreement of integral subgroups suffice. -/
theorem exists_restrictedProduct_mulHomeomorph
    (hfinite : ∀ i : I, (p ⁻¹' {i}).Finite)
    (e : ∀ i : I, A i ≃ₜ* (∀ j : {j : J // p j = i}, B j.val))
    (he : ∀ᶠ i in cofinite, ∀ a : A i,
      a ∈ U i ↔ ∀ j : {j : J // p j = i}, e i a j ∈ V j.val) :
    ∃ E : (Πʳ i, [A i, U i]) ≃ₜ* (Πʳ j, [B j, V j]),
      ∀ a j, E a j = e (p j) (a (p j)) ⟨j, rfl⟩ := by
  have hp : Tendsto p cofinite cofinite := by
    intro S hS
    change (p ⁻¹' S)ᶜ.Finite
    exact (show Sᶜ.Finite from hS).preimage' (fun i _ => hfinite i)
  have havoid (S : Set J) (hS : cofinite ≤ 𝓟 S) :
      ∀ᶠ i : I in cofinite, ∀ j : {j : J // p j = i}, j.val ∈ S := by
    have hF : Sᶜ.Finite := le_principal_iff.mp hS
    filter_upwards [(hF.image p).eventually_cofinite_notMem] with i hi j
    by_contra hj
    exact hi ⟨j.val, hj, j.property⟩
  let φ (j : J) : A (p j) →* B j :=
    (Pi.evalMonoidHom (f := fun r : {j' : J // p j' = p j} => B r.val) ⟨j, rfl⟩).comp
      (e (p j)).toMonoidHom
  have hφ : ∀ᶠ j in cofinite, Set.MapsTo (φ j) (U (p j)) (V j) := by
    filter_upwards [hp.eventually he] with j hj a ha
    exact (hj a).mp ha ⟨j, rfl⟩
  let E := RestrictedProduct.mapAlongMonoidHom A B p hp φ hφ
  let d (b : ∀ j, B j) (i : I) : A i :=
    (e i).symm fun j => b j.val
  have hd {S : Set J} (hS : cofinite ≤ 𝓟 S) :
      ∀ᶠ i in cofinite, ∀ b : Πʳ j, [B j, V j]_[𝓟 S], d b i ∈ U i := by
    filter_upwards [he, havoid S hS] with i hi hS' b
    apply (hi _).mpr
    intro j
    rw [show e i (d b i) = (fun j : {j : J // p j = i} => b j.val) from (e i).apply_symm_apply _]
    exact (eventually_principal.mp b.property) _ (hS' j)
  let inv (b : Πʳ j, [B j, V j]) : Πʳ i, [A i, U i] :=
    let S : Set J := {j | b j ∈ V j}
    ⟨d b, (hd (S := S) (le_principal_iff.mpr b.property)).mono
      fun i hi => hi ⟨b, eventually_principal.mpr (fun _ h => h)⟩⟩
  have hleft (a : Πʳ i, [A i, U i]) : inv (E a) = a := by
    ext i
    change d (E a) i = a i
    apply (e i).injective
    rw [show e i (d (E a) i) = (fun j : {j : J // p j = i} => E a j.val) from (e i).apply_symm_apply _]
    funext j
    obtain ⟨j, rfl⟩ := j
    rfl
  have hright (b : Πʳ j, [B j, V j]) : E (inv b) = b := by
    ext j
    change e (p j) (d b (p j)) ⟨j, rfl⟩ = b j
    rw [(e (p j)).apply_symm_apply]
  let equiv := MulEquiv.ofBijective E ⟨Function.LeftInverse.injective hleft,
    Function.RightInverse.surjective hright⟩
  have hforward : Continuous equiv :=
    RestrictedProduct.mapAlong_continuous A B p hp _ hφ fun j =>
      (continuous_apply _).comp (e (p j)).continuous
  have hinv : Continuous inv := by
    rw [RestrictedProduct.continuous_dom]
    intro S hS
    let T : Set I := {i | ∀ b : Πʳ j, [B j, V j]_[𝓟 S], d b i ∈ U i}
    have hT : cofinite ≤ 𝓟 T := le_principal_iff.mpr (hd hS)
    let g (b : Πʳ j, [B j, V j]_[𝓟 S]) : Πʳ i, [A i, U i]_[𝓟 T] :=
      ⟨d b, eventually_principal.mpr fun i hi => hi b⟩
    have hfact : inv ∘ RestrictedProduct.inclusion B (fun j => (V j : Set (B j))) hS =
        RestrictedProduct.inclusion A (fun i => (U i : Set (A i))) hT ∘ g := by ext; rfl
    rw [hfact]
    apply (RestrictedProduct.continuous_inclusion hT).comp
    apply RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr
    intro i
    exact (e i).symm.continuous.comp (continuous_pi fun j => RestrictedProduct.continuous_eval j.val)
  have hsymm : (equiv.symm : _ → _) = inv :=
    funext fun b => equiv.injective (by rw [MulEquiv.apply_symm_apply]; exact (hright b).symm)
  have hinverse : Continuous equiv.invFun := by
    change Continuous (equiv.symm : _ → _)
    rw [hsymm]
    exact hinv
  exact ⟨{ equiv with continuous_toFun := hforward, continuous_invFun := hinverse },
    fun _ _ => rfl⟩

end RestrictedProducts

section IntegralCompletions

/-- A continuous extension map that respects the restricted place identifies
the integral elements of the base completion by inverse image. -/
theorem completionMap_mem_integers_iff {k K : Type*} [Field k] [Field K]
    (g : k →+* K) (v : FunctionPlace k) (w : FunctionPlace K)
    (hplace : w.val.comap g = v.val)
    (f : v.Completion →+* w.Completion) (hf : Continuous f)
    (hcompat : f.comp v.embedding = w.embedding.comp g) (r : v.Completion) :
    f r ∈ w.integers ↔ r ∈ v.integers := by
  have hv : IsClopen (v.integers : Set v.Completion) :=
    Valued.isClopen_valuationSubring _
  have hw : IsClopen (w.integers : Set w.Completion) :=
    Valued.isClopen_valuationSubring _
  refine UniformSpace.Completion.induction_on
    (p := fun x : v.Completion => f x ∈ w.integers ↔ x ∈ v.integers) r ?_ ?_
  · exact (Homeomorph.refl v.Completion).isClosed_setOfPred_iff (hw.preimage hf) hv
  · intro x
    let y : k := WithVal.ofVal x
    have hh : (x : v.Completion) = v.embedding y := rfl
    have he : f (v.embedding y) = w.embedding (g y) := DFunLike.congr_fun hcompat y
    rw [hh, he]
    change w.embedding (g y) ∈ w.integers ↔ v.embedding y ∈ v.integers
    rw [w.embedding_mem_integers, v.embedding_mem_integers, ← hplace]
    rfl

end IntegralCompletions
section LocalTopology

open ValuativeRel

private theorem sigmaCompactSpace_localField (B : Type*) [Field B] [ValuativeRel B]
    [TopologicalSpace B] [IsNonarchimedeanLocalField B] : SigmaCompactSpace B := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt B
  let : Countable (WithZero (Multiplicative ℤ)) := inferInstanceAs (Countable (Option ℤ))
  let : Countable (ValueGroupWithZero B) := e.injective.countable
  let C (γ : ValueGroupWithZero B) := {x : B | ValuativeRel.valuation B x ≤ γ}
  have hC : (⋃ γ, C γ) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    exact Set.mem_iUnion.mpr ⟨ValuativeRel.valuation B x, show ValuativeRel.valuation B x ≤ _ from le_rfl⟩
  exact ⟨hC ▸ isSigmaCompact_iUnion_of_isCompact C
    (fun γ => IsNonarchimedeanLocalField.isCompact_closedBall B γ)⟩

private theorem sigmaCompactSpace_units {M : Type*} [Monoid M] [TopologicalSpace M]
    [T1Space M] [ContinuousMul M] [SigmaCompactSpace M] : SigmaCompactSpace Mˣ := by
  let : SigmaCompactSpace Mᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.sigmaCompactSpace
  exact Units.isClosedEmbedding_embedProduct.sigmaCompactSpace

private def mulHomeomorphOfContinuous {A B : Type*} [Group A] [Group B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalGroup A] [ContinuousMul B]
    [SigmaCompactSpace A] [BaireSpace B] [T2Space B]
    (e : A ≃* B) (he : Continuous e) : A ≃ₜ* B :=
  let h := e.toEquiv.toHomeomorphOfContinuousOpen he
    (e.toMonoidHom.isOpenMap_of_sigmaCompact e.surjective he)
  { e with continuous_toFun := h.continuous, continuous_invFun := h.symm.continuous }

end LocalTopology


section Coordinates

open AlgebraicGeometry Opposite
open Specs.Unipotent (Index)
open Specs.StandardGroups (GLCoordinates universalMatrix)
open private matrixPresentation glIntegral_iff glEvaluation_eventually continuous_glEvaluation
  from LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private glEvaluation glEvaluation_entry from LinearAlgebraicGroups.Affine.StandardGroups
open private coordinateMap coordinateMap_spec from LinearAlgebraicGroups.Arithmetic.IntegralModels
open private quotientPoints homQuotient polynomialHomEquiv equations map_coefficient
  from LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {G : AffineAlgebraicGroup K} {W : AffineAlgebraicGroup k}
variable (i : MatrixRealization G) (j : MatrixRealization W)

private abbrev pointChart {k : Type u} [Field k] (H : AffineAlgebraicGroup k)
    (A : TestAlgebra k) (e : (testSpec k).obj (op A) ≅ H.val.X) :
    coyoneda.obj (op A) ≅ (groupPointsFunctor k).obj H.val ⋙ forget GrpCat :=
  WeilRestriction.spectrumPoints A H.val.X e

private theorem pointChart_inv {k : Type u} [Field k] {H : AffineAlgebraicGroup k}
    (A : TestAlgebra k) (e : (testSpec k).obj (op A) ≅ H.val.X)
    (R : TestAlgebra k) (g : ((groupPointsFunctor k).obj H.val).obj R) :
    (pointChart H A e).inv.app R g = coordinateMap (g ≫ e.inv) := by
  apply Quiver.Hom.op_inj
  apply (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective
  rw [coordinateMap_spec]
  change (algSpec (CommRingCat.of k)).map
    (((algSpec.fullyFaithful (R := CommRingCat.of k)).homEquiv).symm (g ≫ e.inv)) =
      g ≫ e.inv
  exact (algSpec.fullyFaithful (R := CommRingCat.of k)).homEquiv.apply_symm_apply _

private def coordinateComparison (A : TestAlgebra k) (B : TestAlgebra K)
    (eA : (testSpec k).obj (op A) ≅ W.val.X)
    (eB : (testSpec K).obj (op B) ≅ G.val.X)
    (ρ : (groupPointsFunctor k).obj W.val ≅
      WeilRestriction.extendScalars k K ⋙ (groupPointsFunctor K).obj G.val) :
    coyoneda.obj (op A) ≅ WeilRestriction.restrictionFunctor k K B :=
  pointChart W A eA ≪≫ Functor.isoWhiskerRight ρ (forget GrpCat) ≪≫
    (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft (WeilRestriction.extendScalars k K) (pointChart G B eB).symm

private theorem natural_on_generic {k : Type u} [Field k] {A : TestAlgebra k}
    {V : TestAlgebra k ⥤ Type u} (η : coyoneda.obj (op A) ⟶ V)
    {R : TestAlgebra k} (g : A ⟶ R) :
    η.app R g = V.map g (η.app A (𝟙 A)) := by
  have h := ConcreteCategory.congr_hom (η.naturality g) (𝟙 A)
  exact (by simpa [coyoneda] using h)

private theorem matrixPresentation_chart {k : Type u} [Field k] {H : AffineAlgebraicGroup k}
    (l : MatrixRealization H) (A : TestAlgebra k) (e : (testSpec k).obj (op A) ≅ H.val.X) :
    ∃ a : CommAlgCat.of k (GLCoordinates k (Index.{u} l.size)) ⟶ A,
      Function.Surjective a.hom ∧
      ∀ (R : Type u) [CommRing R] [Algebra k R] (g : PointsIn l R),
        glEvaluation (asMatrix l R g) =
          (a ≫ (pointChart H A e).inv.app (CommAlgCat.of k R) g).hom := by
  obtain ⟨a, ha, h⟩ := matrixPresentation A e l
  exact ⟨a, ha, fun R _ _ g => by rw [pointChart_inv]; exact h R g⟩

private theorem inverse_coordinate_polynomial {A : TestAlgebra k} {B : TestAlgebra K}
    (η : coyoneda.obj (op A) ≅ WeilRestriction.restrictionFunctor k K B)
    {ι σ : Type u} [Fintype ι] [Finite σ] (b : Module.Basis ι k K)
    (f : MvPolynomial σ K →ₐ[K] B) (hf : Function.Surjective f) (x : A) :
    ∃ p : MvPolynomial (σ × ι) k,
      ∀ (R : TestAlgebra k) (h : B ⟶ (WeilRestriction.extendScalars k K).obj R),
      (η.inv.app R h).hom x =
        MvPolynomial.aeval (fun q : σ × ι =>
          (b.baseChange R).repr (h.hom (f (MvPolynomial.X q.1))) q.2) p := by
  let P := WeilRestriction.ofPresentation b B f hf
  let τ := P.points.hom ≫ η.inv
  let a : A ⟶ P.coordinate := τ.app P.coordinate (𝟙 _)
  obtain ⟨p, hp⟩ := Ideal.Quotient.mkₐ_surjective k
    (equations b (RingHom.ker f.toRingHom)) (a.hom x)
  refine ⟨p, fun R h => ?_⟩
  let g := P.points.inv.app R h
  have hh : η.inv.app R h = a ≫ g := by
    have ht := natural_on_generic τ g
    change η.inv.app R (P.points.hom.app R g) = a ≫ g at ht
    simpa only [g, Iso.inv_hom_id_app_apply] using ht
  rw [hh]
  change g.hom (a.hom x) = _
  rw [← hp]
  rfl


private theorem coordinateComparison_hom (A : TestAlgebra k) (B : TestAlgebra K)
    (eA : (testSpec k).obj (op A) ≅ W.val.X)
    (eB : (testSpec K).obj (op B) ≅ G.val.X)
    (ρ : (groupPointsFunctor k).obj W.val ≅
      WeilRestriction.extendScalars k K ⋙ (groupPointsFunctor K).obj G.val)
    (R : TestAlgebra k) (g : ((groupPointsFunctor k).obj W.val).obj R) :
    (coordinateComparison A B eA eB ρ).hom.app R ((pointChart W A eA).inv.app R g) =
      (pointChart G B eB).inv.app ((WeilRestriction.extendScalars k K).obj R) (ρ.hom.app R g) := by
  let h := (pointChart W A eA).inv.app R g
  have hh : (pointChart W A eA).hom.app R h = g := Iso.inv_hom_id_app_apply _ _ _
  change (pointChart G B eB).inv.app ((WeilRestriction.extendScalars k K).obj R)
    (ρ.hom.app R ((pointChart W A eA).hom.app R h)) = _
  rw [hh]

private theorem specialized_matrix_coordinate
    (A : TestAlgebra k) (B : TestAlgebra K)
    (eA : (testSpec k).obj (op A) ≅ W.val.X)
    (eB : (testSpec K).obj (op B) ≅ G.val.X)
    (ρ : (groupPointsFunctor k).obj W.val ≅
      WeilRestriction.extendScalars k K ⋙ (groupPointsFunctor K).obj G.val)
    (a : CommAlgCat.of K (GLCoordinates K (Index.{u} i.size)) ⟶ B)
    (ha : ∀ (L : Type u) [CommRing L] [Algebra K L] (g : PointsIn i L),
      glEvaluation (asMatrix i L g) =
        (a ≫ (pointChart G B eB).inv.app (CommAlgCat.of K L) g).hom)
    (R : Type u) [CommRing R] [Algebra k R] (L : Type u) [CommRing L] [Algebra K L]
    (f : R ⊗[k] K →ₐ[K] L) (g : PointsIn j R) (x : GLCoordinates K (Index.{u} i.size)) :
    glEvaluation (asMatrix i L (specializedPoint (G := G) (W := W) ρ f g)) x =
      f (WeilRestriction.tensorMap k K ((pointChart W A eA).inv.app (CommAlgCat.of k R) g).hom
        (((coordinateComparison A B eA eB ρ).hom.app A (𝟙 A)).hom (a.hom x))) := by
  let T := CommAlgCat.of K L
  let U := CommAlgCat.of k R
  let E := pointChart G B eB
  let p := ρ.hom.app U g
  let q := (pointChart W A eA).inv.app U g
  let η := coordinateComparison A B eA eB ρ
  have hnat := ConcreteCategory.congr_hom (E.inv.naturality (CommAlgCat.ofHom f)) p
  have h := natural_on_generic η.hom q
  have hq := coordinateComparison_hom A B eA eB ρ U g
  change η.hom.app U q = E.inv.app _ p at hq
  rw [hq] at h
  rw [ha]
  change ((E.inv.app T (specializedPoint (G := G) (W := W) ρ f g)).hom (a.hom x)) = _
  change E.inv.app T (specializedPoint (G := G) (W := W) ρ f g) =
    E.inv.app _ p ≫ CommAlgCat.ofHom f at hnat
  rw [hnat, h]
  rfl

private theorem continuous_specializedPoint
    (ρ : (groupPointsFunctor k).obj W.val ≅
      WeilRestriction.extendScalars k K ⋙ (groupPointsFunctor K).obj G.val)
    (R : Type u) [CommRing R] [Algebra k R] [TopologicalSpace R] [IsTopologicalRing R]
    (L : Type u) [CommRing L] [Algebra K L] [TopologicalSpace L] [IsTopologicalRing L]
    (f : R →+* L) (hf : f.comp (algebraMap k R) = (algebraMap K L).comp (algebraMap k K))
    (hc : Continuous f) :
    @Continuous (PointsIn j R) (PointsIn i L) _ _
      (fun g => specializedPoint (G := G) (W := W) ρ (tensorSpecialization f hf) g) := by
  obtain ⟨A, ⟨eA⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr W.prop.1
  obtain ⟨B, ⟨eB⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr G.prop.1
  obtain ⟨a, ha, ha'⟩ := matrixPresentation_chart j A.unop eA
  obtain ⟨c, _, hc'⟩ := matrixPresentation_chart i B.unop eB
  let ψ : PointsIn j R →* PointsIn i L := specializedPoint (G := G) (W := W) ρ (tensorSpecialization f hf)
  refine (IsInducing.induced (asMatrix i L)).continuous_iff.mpr ?_
  have hentry (s t : Index.{u} i.size) :
      Continuous (fun g : PointsIn j R => (asMatrix i L (ψ g)).val s t) := by
    let z := ((coordinateComparison A.unop B.unop eA eB ρ).hom.app A.unop (𝟙 _)).hom
      (c.hom (universalMatrix K _ s t))
    have h : (fun g : PointsIn j R => (asMatrix i L (ψ g)).val s t) =
        fun g => tensorSpecialization f hf
          (WeilRestriction.tensorMap k K ((pointChart W A.unop eA).inv.app (CommAlgCat.of k R) g).hom z) := by
      funext g
      rw [← glEvaluation_entry (k := K)]
      exact specialized_matrix_coordinate i j A.unop B.unop eA eB ρ c hc' R L _ g _
    rw [h]
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      obtain ⟨d, hd⟩ := ha x
      have he (g : PointsIn j R) :
          ((pointChart W A.unop eA).inv.app (CommAlgCat.of k R) g).hom x =
            glEvaluation (asMatrix j R g) d := by
        rw [ha', ← hd]
        rfl
      change Continuous (fun g : PointsIn j R => tensorSpecialization f hf
        ((((pointChart W A.unop eA).inv.app (CommAlgCat.of k R) g).hom x) ⊗ₜ[k] y))
      simp only [tensorSpecialization_tmul, he]
      exact (hc.comp ((continuous_glEvaluation d).comp continuous_induced_dom)).mul continuous_const
    | add x y hx hy =>
      convert hx.add hy using 1
      funext g
      simp only [map_add, Pi.add_apply]
  have hp : Continuous (fun g : PointsIn j R => (asMatrix i L (ψ g)).val) :=
    continuous_matrix hentry
  refine Units.continuous_iff.mpr ⟨hp, ?_⟩
  change Continuous (fun g : PointsIn j R => (asMatrix i L (ψ g))⁻¹.val)
  simp only [← map_inv]
  exact hp.comp continuous_inv
end Coordinates

section LocalComparison

variable {F K : Type u} [Field F] [Finite F] [Field K] [Algebra F K]

private abbrev below (t : SeparatingParameter F K) :
    FunctionPlace K → FunctionPlace F⟮X⟯ :=
  letI := t.rationalAlgebra
  restrictFunctionPlace

private abbrev Fiber (t : SeparatingParameter F K) (v : FunctionPlace F⟮X⟯) :=
  {w : FunctionPlace K // below t w = v}

private theorem fiber_comap (t : SeparatingParameter F K) (v : FunctionPlace F⟮X⟯)
    (w : FunctionPlace K) :
    below t w = v ↔ w.val.comap t.rationalMap.toRingHom = v.val :=
  Subtype.ext_iff

private abbrev baseAlgebra {k : Type u} [Field k] (v : FunctionPlace k) : Algebra k v.Completion :=
  v.embedding.toAlgebra

private theorem fiber_scalar_comparison (t : SeparatingParameter F K) (v : FunctionPlace F⟮X⟯) :
    letI := t.rationalAlgebra
    letI := baseAlgebra v
    IntrinsicComparison (k := F⟮X⟯) (K := K) (B := v.Completion)
      {w : FunctionPlace K | below t w = v} := by
  letI := t.rationalAlgebra
  letI := baseAlgebra v
  have h := functionCompletionComparison t v
  have he : {w : FunctionPlace K | below t w = v} =
      {w : FunctionPlace K | w.val.comap t.rationalMap.toRingHom = v.val} :=
    Set.ext (fiber_comap t v)
  rw [he]
  exact h

private theorem scalar_map_compat {k K R L : Type u} [Field k] [Field K] [Algebra k K]
    [CommRing R] [Algebra k R] [CommRing L] [Algebra K L]
    (f : R →+* L) (E : R ⊗[k] K →+* L)
    (h : ∀ r x, E (r ⊗ₜ[k] x) = f r * algebraMap K L x) :
    f.comp (algebraMap k R) = (algebraMap K L).comp (algebraMap k K) := by
  ext x
  simpa only [h, map_one, one_mul, mul_one, RingHom.comp_apply] using
    congrArg E (tmul_algebraMap (R := R) (K := K) x)

private theorem local_topological_equiv
    {k K I : Type u} [Field k] [Field K] [Finite I]
    (D : GlobalFieldData.{u, u} k) (E : GlobalFieldData.{u, u} K)
    (v : D.FinitePlace) (w : I → E.FinitePlace)
    {G : AffineAlgebraicGroup K} {W : AffineAlgebraicGroup k}
    (i : MatrixRealization G) (j : MatrixRealization W)
    (e : LocalPoints D j (.inl v) ≃* (∀ q : I, LocalPoints E i (.inl (w q))))
    (he : Continuous (e : LocalPoints D j (.inl v) → (∀ q : I, LocalPoints E i (.inl (w q))))) :
    ∃ H : LocalPoints D j (.inl v) ≃ₜ* (∀ q : I, LocalPoints E i (.inl (w q))), ∀ g, H g = e g := by
  letI : SigmaCompactSpace (D.Completion (.inl v)) :=
    sigmaCompactSpace_localField (D.FiniteCompletion v)
  letI : SigmaCompactSpace (Matrix (Specs.Unipotent.Index.{u} j.size)
      (Specs.Unipotent.Index.{u} j.size) (D.Completion (.inl v))) :=
    inferInstanceAs (SigmaCompactSpace
      (Specs.Unipotent.Index.{u} j.size → Specs.Unipotent.Index.{u} j.size → D.Completion (.inl v)))
  letI : SigmaCompactSpace (Matrix.GeneralLinearGroup (Specs.Unipotent.Index.{u} j.size)
      (D.Completion (.inl v))) := sigmaCompactSpace_units
  letI : SigmaCompactSpace (LocalPoints D j (.inl v)) :=
    (localMatrixEmbedding D j (.inl v)).sigmaCompactSpace
  letI (q : I) : T2Space (LocalPoints E i (.inl (w q))) :=
    (localMatrixEmbedding E i (.inl (w q))).isEmbedding.t2Space
  letI (q : I) : LocallyCompactSpace (LocalPoints E i (.inl (w q))) := by
    letI : LocallyCompactSpace (E.Completion (.inl (w q))) :=
      inferInstanceAs (LocallyCompactSpace (E.FiniteCompletion (w q)))
    let M := Matrix (Specs.Unipotent.Index.{u} i.size) (Specs.Unipotent.Index.{u} i.size)
      (E.Completion (.inl (w q)))
    letI : LocallyCompactSpace M := inferInstanceAs
      (LocallyCompactSpace (Specs.Unipotent.Index.{u} i.size → Specs.Unipotent.Index.{u} i.size →
        E.Completion (.inl (w q))))
    letI : LocallyCompactSpace Mᵐᵒᵖ :=
      MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
    letI : LocallyCompactSpace (M × Mᵐᵒᵖ) := inferInstance
    letI : LocallyCompactSpace (Matrix.GeneralLinearGroup (Specs.Unipotent.Index.{u} i.size)
        (E.Completion (.inl (w q)))) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
    exact (localMatrixEmbedding E i (.inl (w q))).locallyCompactSpace
  letI := Fintype.ofFinite I
  exact ⟨mulHomeomorphOfContinuous e he, fun _ => rfl⟩

end LocalComparison

section IntegralScalars

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Polynomial
open private LinearAlgebraicGroups.Arithmetic.denseFiniteIntegers from
  LinearAlgebraicGroups.Arithmetic.LocalLatticeIntersection

variable {F K : Type u} [Field F] [Finite F] [Field K] [Algebra F K]

private def integerChart (t : SeparatingParameter F K) (p : HeightOneSpectrum t.integerRing)
    (w : FunctionPlace K) (h : t.placeOfPrime p = w) : w.Completion ≃ₜ p.adicCompletion K := by
  subst w
  exact (t.completionEquiv p).toEquiv.toHomeomorphOfIsInducing
    (t.completionEquiv_isUniformInducing p).isInducing

private theorem integerChart_integral (t : SeparatingParameter F K)
    (p : HeightOneSpectrum t.integerRing) (w : FunctionPlace K) (h : t.placeOfPrime p = w)
    (x : w.Completion) :
    integerChart t p w h x ∈ p.adicCompletionIntegers K ↔ x ∈ w.integers := by
  subst w
  exact t.completionEquiv_mem_integers p x

private theorem integerChart_embedding (t : SeparatingParameter F K)
    (p : HeightOneSpectrum t.integerRing) (w : FunctionPlace K) (h : t.placeOfPrime p = w)
    (x : K) :
    integerChart t p w h (w.embedding x) = algebraMap K (p.adicCompletion K) x := by
  subst w
  exact t.completionEquiv_embedding p x

private theorem integral_tuple_in_closure (t : SeparatingParameter F K)
    (v : FunctionPlace F⟮X⟯) (hv : RatFunc.X ∈ v.val) [Fintype (Fiber t v)]
    (y : ∀ w : Fiber t v, w.val.Completion) (hy : ∀ w, y w ∈ w.val.integers) :
    y ∈ closure (Set.range fun x : t.integerRing =>
      fun w : Fiber t v => w.val.embedding (algebraMap t.integerRing K x)) := by
  classical
  have hchart (w : Fiber t v) : w.val ∈ Set.range t.placeOfPrime := by
    rw [t.range_placeOfPrime]
    change t.element ∈ w.val.val
    have hw := (fiber_comap t v w.val).mp w.property
    have hx : RatFunc.X ∈ w.val.val.comap t.rationalMap.toRingHom := hw.symm ▸ hv
    change t.rationalMap RatFunc.X ∈ w.val.val at hx
    have he : t.rationalMap RatFunc.X = t.element :=
      RatFunc.algEquivOfTranscendental_X t.element t.transcendental
    exact he ▸ hx
  choose d hd using hchart
  have hinj : Function.Injective d := fun w z he => Subtype.ext ((hd w).symm.trans
    ((congrArg t.placeOfPrime he).trans (hd z)))
  let S : Finset (HeightOneSpectrum t.integerRing) := Finset.univ.map ⟨d, hinj⟩
  let τ : Fiber t v ≃ S := Equiv.ofBijective
    (fun w => ⟨d w, Finset.mem_map.mpr ⟨w, Finset.mem_univ _, rfl⟩⟩)
    ⟨fun _ _ h => hinj (congrArg Subtype.val h), fun s => by
      obtain ⟨w, _, hw⟩ := Finset.mem_map.mp s.property
      exact ⟨w, Subtype.ext hw⟩⟩
  let c (w : Fiber t v) := integerChart t (d w) w.val (hd w)
  let Y (s : S) := s.val.adicCompletionIntegers K
  let f (a : ∀ s : S, Y s) (w : Fiber t v) : w.val.Completion := (c w).symm (a (τ w)).val
  have hf : Continuous f := continuous_pi fun w =>
    (c w).symm.continuous.comp (continuous_subtype_val.comp (continuous_apply (τ w)))
  let z (w : Fiber t v) : Y (τ w) :=
    ⟨c w (y w), (integerChart_integral t _ _ _ _).mpr (hy w)⟩
  let x := Equiv.piCongrLeft (fun s => (Y s : Type u)) τ z
  have hx (w : Fiber t v) : (x (τ w)).val = c w (y w) := by
    simp [x, z]
  have hxy : f x = y := by
    funext w
    exact (congrArg (c w).symm (hx w)).trans ((c w).symm_apply_apply _)
  have hD := LinearAlgebraicGroups.Arithmetic.denseFiniteIntegers (K := K) S x
  have hmem := mem_closure_image hf.continuousAt hD
  rw [hxy] at hmem
  refine closure_mono ?_ hmem
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  refine ⟨a, funext fun w => ?_⟩
  apply (c w).injective
  rw [(c w).apply_symm_apply, integerChart_embedding]
  exact IsScalarTower.algebraMap_apply t.integerRing K ((d w).adicCompletion K) a

private theorem integral_basis_coefficients_eventually
    (t : SeparatingParameter F K) {ι : Type u} [Finite ι] :
    letI := t.rationalAlgebra
    ∀ (b : Module.Basis ι F⟮X⟯ K), ∀ᶠ v : FunctionPlace F⟮X⟯ in cofinite,
      RatFunc.X ∈ v.val ∧
      ∀ a : t.integerRing, ∀ l, v.embedding (b.repr (algebraMap t.integerRing K a) l) ∈ v.integers := by
  classical
  letI := t.rationalAlgebra
  letI := t.polynomialAlgebra
  letI : Module.Finite F[X] t.integerRing :=
    (IsIntegralClosure.finite F[X] F⟮X⟯ K (FunctionField.ringOfIntegers F K) :
      Module.Finite F[X] (FunctionField.ringOfIntegers F K))
  intro b
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top (R := F[X]) (M := t.integerRing))
  have hX : ∀ᶠ v : FunctionPlace F⟮X⟯ in cofinite, RatFunc.X ∈ v.val := by
    filter_upwards [eventually_cofinite.mpr ((baseData F).finite_nonintegral RatFunc.X)] with v hv
    exact (v.embedding_mem_integers _).mp hv
  have hgen (a : (↑s : Set t.integerRing)) (l : ι) :
      ∀ᶠ v : FunctionPlace F⟮X⟯ in cofinite,
        v.embedding (b.repr (algebraMap t.integerRing K a) l) ∈ v.integers :=
    eventually_cofinite.mpr ((baseData F).finite_nonintegral _)
  filter_upwards [hX, eventually_all.mpr fun a => eventually_all.mpr (hgen a)] with v hv h
  refine ⟨hv, ?_⟩
  intro a l
  have hpoly (r : F[X]) : algebraMap F[X] F⟮X⟯ r ∈ v.val := by
    induction r using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add] using add_mem hp hq
    | monomial n c =>
      have hc : algebraMap F F⟮X⟯ c ∈ v.val := by
        rw [← v.val.valuationSubring_valuation]
        exact FiniteField.valuation_algebraMap_le_one v.val.valuation c
      rw [RatFunc.algebraMap_monomial]
      exact mul_mem hc (pow_mem hv n)
  have ha : a ∈ Submodule.span F[X] (↑s : Set t.integerRing) := hs ▸ Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem a ha => exact h ⟨a, ha⟩ l
  | zero => simp
  | add a c _ _ ha hc =>
    simpa only [map_add, Finsupp.add_apply] using add_mem ha hc
  | smul r a _ ha =>
    have hr := (v.embedding_mem_integers _).mpr (hpoly r)
    change v.embedding (b.repr (algebraMap t.integerRing K (r • a)) l) ∈ v.integers
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply F[X] t.integerRing K,
      IsScalarTower.algebraMap_apply F[X] F⟮X⟯ K, ← Algebra.smul_def, map_smul, Finsupp.smul_apply,
      Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply, map_mul]
    exact mul_mem hr ha


private theorem isClosed_integral_coefficients
    {k K R I ι : Type u} [Field k] [Field K] [Algebra k K]
    [Field R] [Algebra k R] [TopologicalSpace R] [Fintype ι]
    {C : I → Type u} [∀ w, Field (C w)] [∀ w, Algebra K (C w)]
    [∀ w, TopologicalSpace (C w)] [∀ w, IsTopologicalRing (C w)] [∀ w, T2Space (C w)]
    (O : ValuationSubring R) (hO : IsCompact (O : Set R))
    (b : Module.Basis ι k K) (E : R ⊗[k] K ≃+* (∀ w, C w))
    (f : ∀ w, R →+* C w) (hc : ∀ w, Continuous (f w))
    (ht : ∀ r x w, E (r ⊗ₜ[k] x) w = f w r * algebraMap K (C w) x) :
    IsClosed {y | ∀ l, (b.baseChange R).repr (E.symm y) l ∈ O} := by
  let β := (b.baseChange R).equivFun
  let φ (a : ι → R) : ∀ w, C w := E (β.symm a)
  let S : Set (ι → R) := Set.pi Set.univ (fun _ => (O : Set R))
  have hφ : Continuous φ := by
    have he (a : ι → R) (w : I) : φ a w = ∑ l, f w (a l) * algebraMap K (C w) (b l) := by
      change E ((b.baseChange R).equivFun.symm a) w = _
      simp only [Module.Basis.equivFun_symm_apply, Module.Basis.baseChange_apply,
        TensorProduct.smul_tmul', smul_eq_mul, mul_one, map_sum, Finset.sum_apply, ht]
    apply continuous_pi
    intro w
    simp only [he]
    exact continuous_finsetSum _ fun l _ => ((hc w).comp (continuous_apply l)).mul continuous_const
  have himage : φ '' S = {y | ∀ l, (b.baseChange R).repr (E.symm y) l ∈ O} := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩ l
      change (b.baseChange R).repr (E.symm (E (β.symm a))) l ∈ O
      rw [E.symm_apply_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
      exact ha l (Set.mem_univ _)
    · intro hy
      exact ⟨β (E.symm y), fun l _ => hy l, by simp [φ]⟩
  rw [← himage]
  have hS : IsCompact S := isCompact_univ_pi (fun _ => hO)
  exact (hS.image hφ).isClosed

private theorem tensor_integral_coefficients
    (t : SeparatingParameter F K) (v : FunctionPlace F⟮X⟯)
    [Fintype (Fiber t v)] {ι : Type u} [Fintype ι] :
    letI := t.rationalAlgebra
    letI := baseAlgebra v
    letI (w : Fiber t v) := baseAlgebra w.val
    ∀ (b : Module.Basis ι F⟮X⟯ K)
      (E : v.Completion ⊗[F⟮X⟯] K ≃+* (∀ w : Fiber t v, w.val.Completion))
      (f : ∀ w : Fiber t v, v.Completion →+* w.val.Completion),
      (∀ w, Continuous (f w)) →
      (∀ r x w, E (r ⊗ₜ[F⟮X⟯] x) w = f w r * w.val.embedding x) →
      RatFunc.X ∈ v.val →
      (∀ a : t.integerRing, ∀ l, v.embedding (b.repr (algebraMap t.integerRing K a) l) ∈ v.integers) →
      ∀ z : v.Completion ⊗[F⟮X⟯] K,
        (∀ w, E z w ∈ w.val.integers) →
        ∀ l, (b.baseChange v.Completion).repr z l ∈ v.integers := by
  letI := t.rationalAlgebra
  letI := baseAlgebra v
  letI (w : Fiber t v) := baseAlgebra w.val
  intro b E f hc ht hv hcoeff z hz
  have hO : IsCompact (v.integers : Set v.Completion) :=
    ((baseData F).integers_properties v).1
  have hclosed := isClosed_integral_coefficients v.integers hO b E f hc ht
  have hcl := integral_tuple_in_closure t v hv (E z) hz
  have hsub : (Set.range fun x : t.integerRing =>
      fun w : Fiber t v => w.val.embedding (algebraMap t.integerRing K x)) ⊆
      {y | ∀ l, (b.baseChange v.Completion).repr (E.symm y) l ∈ v.integers} := by
    rintro _ ⟨x, rfl⟩
    have he : E ((1 : v.Completion) ⊗ₜ[F⟮X⟯] algebraMap t.integerRing K x) =
        fun w => w.val.embedding (algebraMap t.integerRing K x) := by
      funext w
      rw [ht, map_one, one_mul]
    change ∀ l, (b.baseChange v.Completion).repr (E.symm
      (fun w => w.val.embedding (algebraMap t.integerRing K x))) l ∈ v.integers
    rw [← he, E.symm_apply_apply]
    intro l
    rw [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
    exact hcoeff x l
  have hmem := closure_minimal hsub hclosed hcl
  change ∀ l, (b.baseChange v.Completion).repr (E.symm (E z)) l ∈ v.integers at hmem
  rwa [E.symm_apply_apply] at hmem
end IntegralScalars

section ComparisonData

variable {F K : Type u} [Field F] [Finite F] [Field K] [Algebra F K]

private structure ScalarComparison (t : SeparatingParameter F K) (v : FunctionPlace F⟮X⟯) where
  index : Fintype (Fiber t v)
  compare :
    letI := t.rationalAlgebra
    letI := baseAlgebra v
    v.Completion ⊗[F⟮X⟯] K ≃+* (∀ w : Fiber t v, w.val.Completion)
  factor : ∀ w : Fiber t v, v.Completion →+* w.val.Completion
  continuous_factor : ∀ w, Continuous (factor w)
  pure_tensor :
    letI := t.rationalAlgebra
    letI := baseAlgebra v
    ∀ (r : v.Completion) (x : K) (w : Fiber t v),
      compare (r ⊗ₜ[F⟮X⟯] x) w = factor w r * w.val.embedding x

private theorem exists_scalar_comparison (t : SeparatingParameter F K) (v : FunctionPlace F⟮X⟯) :
    Nonempty (ScalarComparison t v) := by
  letI := t.rationalAlgebra
  letI := baseAlgebra v
  obtain ⟨idx, a, E, _, hc, ht⟩ := fiber_scalar_comparison t v
  letI := a
  exact ⟨⟨idx, E.toRingEquiv, fun w => algebraMap v.Completion w.val.Completion, hc, ht⟩⟩

private theorem ScalarComparison.factor_comp (t : SeparatingParameter F K) (v : FunctionPlace F⟮X⟯)
    (s : ScalarComparison t v) (w : Fiber t v) :
    (s.factor w).comp v.embedding = w.val.embedding.comp t.rationalMap.toRingHom := by
  letI := t.rationalAlgebra
  letI := baseAlgebra v
  letI := baseAlgebra w.val
  exact scalar_map_compat (s.factor w) ((Pi.evalRingHom _ w).comp s.compare.toRingHom)
    (fun r x => s.pure_tensor r x w)

private theorem ScalarComparison.apply_factor (t : SeparatingParameter F K)
    (v : FunctionPlace F⟮X⟯) (s : ScalarComparison t v) (w : Fiber t v) :
    letI := t.rationalAlgebra
    letI := baseAlgebra v
    letI := baseAlgebra w.val
    ∀ z : v.Completion ⊗[F⟮X⟯] K,
      s.compare z w = tensorSpecialization (s.factor w) (s.factor_comp t v w) z := by
  letI := t.rationalAlgebra
  letI := baseAlgebra v
  letI := baseAlgebra w.val
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul r x => rw [s.pure_tensor, tensorSpecialization_tmul]; rfl
  | add x y hx hy =>
    have h := congrFun (s.compare.toAddEquiv.map_add x y) w
    change s.compare (x + y) w = s.compare x w + s.compare y w at h
    rw [h, hx, hy, map_add]

private theorem exists_local_topological_comparison
    (t : SeparatingParameter F K) (v : FunctionPlace F⟮X⟯) (s : ScalarComparison t v)
    {G : AffineAlgebraicGroup K} {W : AffineAlgebraicGroup F⟮X⟯}
    (i : MatrixRealization G) (j : MatrixRealization W) :
    letI := t.rationalAlgebra
    letI := localPointsTopology (baseData F) j (.inl v)
    letI (w : Fiber t v) := localPointsTopology (extensionData t) i (.inl w.val)
    ∀ (ρ : (groupPointsFunctor F⟮X⟯).obj W.val ≅
        WeilRestriction.extendScalars F⟮X⟯ K ⋙ (groupPointsFunctor K).obj G.val),
    letI := baseAlgebra v
    letI (w : Fiber t v) := baseAlgebra w.val
    ∃ H : LocalPoints (baseData F) j (.inl v) ≃ₜ*
      (∀ w : Fiber t v, LocalPoints (extensionData t) i (.inl w.val)),
      ∀ g w, H g w = specializedPoint (G := G) (W := W) ρ
        (tensorSpecialization (s.factor w) (s.factor_comp t v w)) g := by
  letI := t.rationalAlgebra
  letI := localPointsTopology (baseData F) j (.inl v)
  letI (w : Fiber t v) := localPointsTopology (extensionData t) i (.inl w.val)
  letI := baseAlgebra v
  letI (w : Fiber t v) := baseAlgebra w.val
  letI := s.index
  intro ρ
  obtain ⟨hf, e, he⟩ := exists_restrictedPoints_productEquiv
    (C := fun w : Fiber t v => w.val.Completion) (G := G) (W := W)
    ρ s.compare s.factor s.pure_tensor
  let e' : LocalPoints (baseData F) j (.inl v) ≃*
      (∀ w : Fiber t v, LocalPoints (extensionData t) i (.inl w.val)) := e
  have hcont : Continuous (e' : LocalPoints (baseData F) j (.inl v) →
      ∀ w : Fiber t v, LocalPoints (extensionData t) i (.inl w.val)) := by
    apply continuous_pi
    intro w
    change @Continuous (LocalPoints (baseData F) j (.inl v))
      (LocalPoints (extensionData t) i (.inl w.val)) _ _ (fun g => e g w)
    simp only [he]
    exact continuous_specializedPoint i j ρ v.Completion w.val.Completion
      (s.factor w) (hf w) (s.continuous_factor w)
  obtain ⟨H, hH⟩ := local_topological_equiv (baseData F) (extensionData t) v Subtype.val i j e' hcont
  exact ⟨H, fun g w => (congrFun (hH g) w).trans (he g w)⟩

end ComparisonData

section IntegralPoints

open AlgebraicGeometry Opposite
open Specs.Unipotent (Index)
open Specs.StandardGroups (GLCoordinates universalMatrix)
open private matrixPresentation glIntegral_iff glEvaluation_eventually
  from LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private glEvaluation glEvaluation_entry from LinearAlgebraicGroups.Affine.StandardGroups

variable {F K : Type u} [Field F] [Finite F] [Field K] [Algebra F K]
variable (t : SeparatingParameter F K)
variable {G : AffineAlgebraicGroup K} {W : AffineAlgebraicGroup F⟮X⟯}
variable (i : MatrixRealization G) (j : MatrixRealization W)

private theorem eventually_on_fibers {I J : Type*} (p : J → I) {P : J → Prop}
    (h : ∀ᶠ w in cofinite, P w) : ∀ᶠ v in cofinite, ∀ w : {w // p w = v}, P w.val := by
  classical
  have hfin : {w | ¬ P w}.Finite := h
  filter_upwards [(hfin.image p).eventually_cofinite_notMem] with v hv w
  by_contra hw
  exact hv ⟨w.val, hw, w.property⟩

private abbrev local_specialization (v : FunctionPlace F⟮X⟯) (s : ScalarComparison t v)
    (w : Fiber t v) :
    letI := t.rationalAlgebra
    letI := baseAlgebra v
    letI := baseAlgebra w.val
    v.Completion ⊗[F⟮X⟯] K →ₐ[K] w.val.Completion := by
  letI := t.rationalAlgebra
  letI := baseAlgebra v
  letI := baseAlgebra w.val
  exact tensorSpecialization (s.factor w) (s.factor_comp t v w)

private theorem specialized_integral_forward :
    letI := t.rationalAlgebra
    ∀ (ρ : (groupPointsFunctor F⟮X⟯).obj W.val ≅
      WeilRestriction.extendScalars F⟮X⟯ K ⋙ (groupPointsFunctor K).obj G.val),
    ∀ᶠ v : FunctionPlace F⟮X⟯ in cofinite,
      letI := baseAlgebra v
      ∀ (s : ScalarComparison t v) (g : LocalPoints (baseData F) j (.inl v)),
        g ∈ integralPoints (baseData F) j v →
        ∀ w : Fiber t v, letI := baseAlgebra w.val
          specializedPoint (G := G) (W := W) ρ (local_specialization t v s w) g ∈
            integralPoints (extensionData t) i w.val := by
  classical
  letI := t.rationalAlgebra
  intro ρ
  obtain ⟨A, ⟨eA⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr W.prop.1
  obtain ⟨B, ⟨eB⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr G.prop.1
  obtain ⟨a, ha, ha'⟩ := matrixPresentation_chart j A.unop eA
  obtain ⟨c, _, hc'⟩ := matrixPresentation_chart i B.unop eB
  let η := coordinateComparison A.unop B.unop eA eB ρ
  have h_generic (z : A.unop ⊗[F⟮X⟯] K) :
      ∀ᶠ v : FunctionPlace F⟮X⟯ in cofinite,
        letI := baseAlgebra v
        ∀ (s : ScalarComparison t v) (g : LocalPoints (baseData F) j (.inl v)),
          g ∈ integralPoints (baseData F) j v →
          ∀ w : Fiber t v, letI := baseAlgebra w.val
            local_specialization t v s w
              (WeilRestriction.tensorMap F⟮X⟯ K
                ((pointChart W A.unop eA).inv.app (CommAlgCat.of F⟮X⟯ v.Completion) g).hom z) ∈
                  w.val.integers := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      obtain ⟨d, hd⟩ := ha x
      have he := eventually_on_fibers (below t)
        (eventually_cofinite.mpr ((extensionData t).finite_nonintegral y))
      filter_upwards [glEvaluation_eventually (baseData F) d, he] with v hv hw s g hg w
      letI := baseAlgebra v
      letI := baseAlgebra w.val
      let q := (pointChart W A.unop eA).inv.app (CommAlgCat.of F⟮X⟯ v.Completion) g
      have hq : q.hom x = glEvaluation (asMatrix j v.Completion g) d := by
        rw [ha', ← hd]
        rfl
      change tensorSpecialization (s.factor w) (s.factor_comp t v w)
        (q.hom x ⊗ₜ[F⟮X⟯] y) ∈ w.val.integers
      rw [tensorSpecialization_tmul, hq]
      exact mul_mem ((completionMap_mem_integers_iff _ _ _ ((fiber_comap t v w.val).mp w.property)
        (s.factor w) (s.continuous_factor w) (s.factor_comp t v w) _).mpr (hv _ hg)) (hw w)
    | add x y hx hy =>
      filter_upwards [hx, hy] with v hv hw s g hg w
      letI := baseAlgebra v
      letI := baseAlgebra w.val
      rw [map_add, map_add]
      exact add_mem (hv s g hg w) (hw s g hg w)
  have hentries := eventually_all.mpr fun (l : Index.{u} i.size) =>
    eventually_all.mpr fun (m : Index.{u} i.size) =>
      h_generic ((η.hom.app A.unop (𝟙 _)).hom (c.hom (universalMatrix K _ l m)))
  filter_upwards [hentries] with v hv s g hg w
  letI := baseAlgebra v
  letI := baseAlgebra w.val
  let ψ : PointsIn j v.Completion →* PointsIn i w.val.Completion :=
    specializedPoint (G := G) (W := W) ρ (local_specialization t v s w)
  have h (g' : LocalPoints (baseData F) j (.inl v)) (hg' : g' ∈ integralPoints (baseData F) j v)
      (l m : Index.{u} i.size) : (asMatrix i w.val.Completion (ψ g')).val l m ∈ w.val.integers := by
    rw [← glEvaluation_entry (k := K)]
    have he := specialized_matrix_coordinate i j A.unop B.unop eA eB ρ c hc'
      v.Completion w.val.Completion (local_specialization t v s w) g' (universalMatrix K _ l m)
    exact he.symm ▸ (hv l m s g' hg' w)
  change asMatrix i w.val.Completion (ψ g) ∈
    (Matrix.GeneralLinearGroup.map w.val.integers.subtype).range
  refine (glIntegral_iff _ _).mpr ⟨h g hg, fun l m => ?_⟩
  rw [← map_inv, ← map_inv]
  exact h g⁻¹ ((integralPoints (baseData F) j v).inv_mem hg) l m

private theorem polynomial_integral_eventually {k : Type u} [Field k]
    (D : GlobalFieldData.{u, u} k) {σ : Type u} (p : MvPolynomial σ k) :
    ∀ᶠ v : D.FinitePlace in cofinite, ∀ x : σ → D.Completion (.inl v),
      (∀ l, x l ∈ D.integers v) → MvPolynomial.aeval x p ∈ D.integers v := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    filter_upwards [eventually_cofinite.mpr (D.finite_nonintegral r)] with v hr x _
    rw [MvPolynomial.aeval_C]
    exact hr
  | add p q hp hq =>
    filter_upwards [hp, hq] with v hv hw x hx
    rw [map_add]
    exact add_mem (hv x hx) (hw x hx)
  | mul_X p l hp =>
    filter_upwards [hp] with v hv x hx
    rw [map_mul, MvPolynomial.aeval_X]
    exact mul_mem (hv x hx) (hx l)


private theorem specialized_integral_reverse :
    letI := t.rationalAlgebra
    ∀ (ρ : (groupPointsFunctor F⟮X⟯).obj W.val ≅
      WeilRestriction.extendScalars F⟮X⟯ K ⋙ (groupPointsFunctor K).obj G.val),
    ∀ᶠ v : FunctionPlace F⟮X⟯ in cofinite,
      letI := baseAlgebra v
      ∀ (s : ScalarComparison t v) (g : LocalPoints (baseData F) j (.inl v)),
        (∀ w : Fiber t v, letI := baseAlgebra w.val
          specializedPoint (G := G) (W := W) ρ (local_specialization t v s w) g ∈
            integralPoints (extensionData t) i w.val) →
        g ∈ integralPoints (baseData F) j v := by
  classical
  letI := t.rationalAlgebra
  intro ρ
  obtain ⟨A, ⟨eA⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr W.prop.1
  obtain ⟨B, ⟨eB⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr G.prop.1
  obtain ⟨a, _, ha⟩ := matrixPresentation_chart j A.unop eA
  obtain ⟨c, hc, hc'⟩ := matrixPresentation_chart i B.unop eB
  letI : Algebra.FiniteType K B.unop := Algebra.FiniteType.of_surjective c.hom hc
  obtain ⟨σ, hσ, p, hp⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial').mp
    (inferInstance : Algebra.FiniteType K B.unop)
  letI := hσ
  let ι := ULift.{u} (Fin (Module.finrank F⟮X⟯ K))
  let b : Module.Basis ι F⟮X⟯ K :=
    (Module.finBasis F⟮X⟯ K).reindex Equiv.ulift.symm
  let η := coordinateComparison A.unop B.unop eA eB ρ
  have hentry (l m : Index.{u} j.size) :
      ∀ᶠ v : FunctionPlace F⟮X⟯ in cofinite,
        letI := baseAlgebra v
        ∀ (s : ScalarComparison t v) (g : LocalPoints (baseData F) j (.inl v)),
          (∀ w : Fiber t v, letI := baseAlgebra w.val
            specializedPoint (G := G) (W := W) ρ (local_specialization t v s w) g ∈
              integralPoints (extensionData t) i w.val) →
          (asMatrix j v.Completion g).val l m ∈ v.integers := by
    let a₀ := a.hom (universalMatrix F⟮X⟯ _ l m)
    obtain ⟨P, hP⟩ := inverse_coordinate_polynomial η b p hp a₀
    choose d hd using fun x : σ => hc (p (MvPolynomial.X x))
    have hd_int := eventually_all.mpr fun x =>
      eventually_on_fibers (below t) (glEvaluation_eventually (extensionData t) (d x))
    filter_upwards [integral_basis_coefficients_eventually t b,
      polynomial_integral_eventually (baseData F) P, hd_int] with v hcoeff hP_int hd_int s g hg
    letI := baseAlgebra v
    letI (w : Fiber t v) := baseAlgebra w.val
    letI := s.index
    let R := CommAlgCat.of F⟮X⟯ v.Completion
    let q := (pointChart W A.unop eA).inv.app R g
    let h := η.hom.app R q
    have hnat (x : B.unop) :
        h.hom x = WeilRestriction.tensorMap F⟮X⟯ K q.hom ((η.hom.app A.unop (𝟙 _)).hom x) :=
      DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (natural_on_generic η.hom q)) x
    have hvar (x : σ) (w : Fiber t v) :
        s.compare (h.hom (p (MvPolynomial.X x))) w ∈ w.val.integers := by
      have h_eval := specialized_matrix_coordinate i j A.unop B.unop eA eB ρ c hc'
        v.Completion w.val.Completion (local_specialization t v s w) g (d x)
      have he :
          tensorSpecialization (s.factor w) (s.factor_comp t v w)
            (WeilRestriction.tensorMap F⟮X⟯ K q.hom
              ((η.hom.app A.unop (𝟙 _)).hom (c.hom (d x)))) =
            glEvaluation (asMatrix i w.val.Completion
              (specializedPoint (G := G) (W := W) ρ (local_specialization t v s w) g)) (d x) :=
        h_eval.symm
      rw [s.apply_factor t v, hnat, ← hd x, he]
      exact hd_int x w _ (hg w)
    have hintegral (x : σ × ι) : (b.baseChange v.Completion).repr
        (h.hom (p (MvPolynomial.X x.1))) x.2 ∈ v.integers :=
      tensor_integral_coefficients t v b s.compare s.factor s.continuous_factor s.pure_tensor
        hcoeff.1 hcoeff.2 _ (hvar x.1) x.2
    have hq : η.inv.app R h = q := Iso.hom_inv_id_app_apply _ _ _
    rw [← glEvaluation_entry (k := F⟮X⟯), ha]
    change q.hom a₀ ∈ v.integers
    rw [← hq, hP R h]
    exact hP_int _ hintegral
  have hentries := eventually_all.mpr fun l => eventually_all.mpr (hentry l)
  filter_upwards [hentries] with v hv s g hg
  letI := baseAlgebra v
  change asMatrix j v.Completion g ∈ (Matrix.GeneralLinearGroup.map v.integers.subtype).range
  refine (glIntegral_iff _ _).mpr ⟨fun l m => hv l m s g hg, fun l m => ?_⟩
  rw [← map_inv]
  apply hv l m s g⁻¹
  intro w
  letI := baseAlgebra w.val
  let ψ : PointsIn j v.Completion →* PointsIn i w.val.Completion :=
    specializedPoint (G := G) (W := W) ρ (local_specialization t v s w)
  change ψ g⁻¹ ∈ integralPoints (extensionData t) i w.val
  rw [map_inv]
  exact (integralPoints (extensionData t) i w.val).inv_mem (hg w)
end IntegralPoints
section Reindex

open Filter
open scoped RestrictedProduct

variable {I J : Type*} {A : I → Type*} {B : J → Type*}
    [∀ i, Group (A i)] [∀ j, Group (B j)]
    [∀ i, TopologicalSpace (A i)] [∀ j, TopologicalSpace (B j)]
    (p : J ≃ I) (U : ∀ i, Subgroup (A i)) (V : ∀ j, Subgroup (B j))
    (e : ∀ i j, p j = i → A i ≃ₜ* B j)

/-- Reindexing the local points preserves the topology of a restricted product
when the integral subgroups are carried to one another. -/
private theorem exists_reindexRestrictedProduct
    (he : ∀ i j (h : p j = i) (a : A i), e i j h a ∈ V j ↔ a ∈ U i) :
    ∃ E : (Πʳ i, [A i, U i]) ≃ₜ* (Πʳ j, [B j, V j]),
      ∀ a j, E a j = e (p j) j rfl (a (p j)) := by
  let φ (j : J) : A (p j) →* B j := (e (p j) j rfl).toMonoidHom
  let ψ (i : I) : B (p.symm i) →* A i := (e i _ (p.apply_symm_apply i)).symm.toMonoidHom
  have hφ : ∀ᶠ j in cofinite, Set.MapsTo (φ j) (U (p j)) (V j) :=
    Eventually.of_forall fun j a ha => (he (p j) j rfl a).mpr ha
  have hψ : ∀ᶠ i in cofinite, Set.MapsTo (ψ i) (V (p.symm i)) (U i) :=
    Eventually.of_forall fun i b hb => (he i _ (p.apply_symm_apply i) _).mp (by
      change e i (p.symm i) _ ((e i (p.symm i) _).symm b) ∈ V _
      rwa [ContinuousMulEquiv.apply_symm_apply])
  let E := RestrictedProduct.mapAlongMonoidHom A B p p.injective.tendsto_cofinite φ hφ
  let E' := RestrictedProduct.mapAlongMonoidHom B A p.symm p.symm.injective.tendsto_cofinite ψ hψ
  have hleft (a : Πʳ i, [A i, U i]) : E' (E a) = a := by
    ext i
    change (e i (p.symm i) (p.apply_symm_apply i)).symm
      (e (p (p.symm i)) (p.symm i) rfl (a (p (p.symm i)))) = a i
    have h (j : J) (i' : I) (hj : p j = i') :
        (e i' j hj).symm (e (p j) j rfl (a (p j))) = a i' := by
      subst i'
      exact ContinuousMulEquiv.symm_apply_apply _ _
    exact h (p.symm i) i (p.apply_symm_apply i)
  have hright (b : Πʳ j, [B j, V j]) : E (E' b) = b := by
    ext j
    change e (p j) j rfl ((e (p j) (p.symm (p j)) _).symm (b (p.symm (p j)))) = b j
    have h (j' : J) (heq : p j' = p j) (hj : j' = j) :
        e (p j) j rfl ((e (p j) j' heq).symm (b j')) = b j := by
      subst j'
      exact ContinuousMulEquiv.apply_symm_apply _ _
    exact h (p.symm (p j)) (p.apply_symm_apply (p j)) (p.symm_apply_apply j)
  let f := MulEquiv.ofBijective E ⟨Function.LeftInverse.injective hleft,
    Function.RightInverse.surjective hright⟩
  have h' : (f.symm : _ → _) = E' := funext fun b =>
    f.injective (by rw [MulEquiv.apply_symm_apply]; exact (hright b).symm)
  refine ⟨{ f with continuous_toFun := ?_, continuous_invFun := ?_ }, fun _ _ => rfl⟩
  · exact RestrictedProduct.mapAlong_continuous A B p p.injective.tendsto_cofinite _ hφ
      (fun j => (e (p j) j rfl).continuous)
  · change Continuous (f.symm : _ → _)
    rw [h']
    exact RestrictedProduct.mapAlong_continuous B A p.symm p.symm.injective.tendsto_cofinite _ hψ
      (fun i => (e i (p.symm i) (p.apply_symm_apply i)).symm.continuous)

end Reindex

section AdelicComparison

open scoped RestrictedProduct

variable {F K : Type u} [Field F] [Finite F] [Field K] [Algebra F K]

private def outsideEquiv (t : SeparatingParameter F K) :
    FunctionPlace K ≃ Outside (extensionData t) ∅ where
  toFun := adelicIndex (extensionData t)
  invFun w := w.val.elim id PEmpty.elim
  left_inv _ := rfl
  right_inv := by
    rintro ⟨w|w, hw⟩
    · rfl
    · exact w.elim

private theorem exists_adeles_reindex (t : SeparatingParameter F K)
    {G : AffineAlgebraicGroup K} (i : MatrixRealization G) :
    let D := extensionData t
    letI := fullAdelesTopology D i
    letI (v : FunctionPlace K) := localPointsTopology D i (.inl v)
    ∃ e : (Πʳ v : FunctionPlace K, [LocalPoints D i (.inl v), integralPoints D i v]) ≃ₜ*
        Adeles D i ∅,
      ∀ a v, e a (adelicIndex D v) = a v := by
  let D := extensionData t
  letI := fullAdelesTopology D i
  letI (v : FunctionPlace K) := localPointsTopology D i (.inl v)
  letI (x : Outside D ∅) := localPointsTopology D i x.val
  let p := (outsideEquiv t).symm
  let A (v : FunctionPlace K) := LocalPoints D i (.inl v)
  let B (x : Outside D ∅) := LocalPoints D i x.val
  let e (v : FunctionPlace K) (x : Outside D ∅) (h : p x = v) : A v ≃ₜ* B x := by
    subst v
    rcases x with ⟨v|v, hv⟩
    · exact ContinuousMulEquiv.refl _
    · exact v.elim
  have he (v : FunctionPlace K) (x : Outside D ∅) (h : p x = v) (a : A v) :
      e v x h a ∈ localSubgroup D i x.val ↔ a ∈ integralPoints D i v := by
    subst v
    rcases x with ⟨v|v, hv⟩
    · rfl
    · exact v.elim
  obtain ⟨E, hE⟩ := exists_reindexRestrictedProduct (A := A) (B := B)
    p (integralPoints D i) (fun x => localSubgroup D i x.val) e he
  exact ⟨E, fun a v => hE a (outsideEquiv t v)⟩

private theorem exists_full_adelic_comparison (t : SeparatingParameter F K)
    {G : AffineAlgebraicGroup K} {W : AffineAlgebraicGroup F⟮X⟯}
    (i : MatrixRealization G) (j : MatrixRealization W)
    (hfinite : ∀ v, Finite (Fiber t v)) :
    letI (v : FunctionPlace F⟮X⟯) := localPointsTopology (baseData F) j (.inl v)
    letI (w : FunctionPlace K) := localPointsTopology (extensionData t) i (.inl w)
    letI := fullAdelesTopology (baseData F) j
    letI := fullAdelesTopology (extensionData t) i
    ∀ (H : ∀ v, LocalPoints (baseData F) j (.inl v) ≃ₜ*
        (∀ w : Fiber t v, LocalPoints (extensionData t) i (.inl w.val))),
      (∀ᶠ v in cofinite, ∀ g, g ∈ integralPoints (baseData F) j v ↔
        ∀ w : Fiber t v, H v g w ∈ integralPoints (extensionData t) i w.val) →
      ∃ E : Adeles (baseData F) j ∅ ≃ₜ* Adeles (extensionData t) i ∅,
        ∀ g w, E g (adelicIndex (extensionData t) w) =
          H (below t w) (g (adelicIndex (baseData F) (below t w))) ⟨w, rfl⟩ := by
  letI (v : FunctionPlace F⟮X⟯) := localPointsTopology (baseData F) j (.inl v)
  letI (w : FunctionPlace K) := localPointsTopology (extensionData t) i (.inl w)
  letI := fullAdelesTopology (baseData F) j
  letI := fullAdelesTopology (extensionData t) i
  intro H hH
  have hF (v : FunctionPlace F⟮X⟯) : (below t ⁻¹' {v}).Finite := by
    letI : Finite ↑(below t ⁻¹' {v}) := hfinite v
    exact Set.toFinite _
  obtain ⟨C, hC⟩ := exists_restrictedProduct_mulHomeomorph (below t)
    (integralPoints (baseData F) j) (integralPoints (extensionData t) i) hF H hH
  obtain ⟨D, hD⟩ := exists_adeles_reindex (rationalParameter F) j
  obtain ⟨E, hE⟩ := exists_adeles_reindex t i
  refine ⟨(D.symm.trans C).trans E, fun g w => ?_⟩
  rw [ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.trans_apply, hE, hC]
  have h := hD (D.symm g) (below t w)
  rw [ContinuousMulEquiv.apply_symm_apply] at h
  rw [← h]

end AdelicComparison

/-- The natural Weil point comparison respects the prescribed adelic groups,
including the local factors above the pole. -/
theorem weilAdelicComparison : WeilAdelicComparison.{u} := by
  classical
  intro F K _ _ _ _ t G W i j
  letI := t.rationalAlgebra
  intro ρ
  let s (v : FunctionPlace F⟮X⟯) := Classical.choice (exists_scalar_comparison t v)
  have hfinite (v : FunctionPlace F⟮X⟯) : Finite (Fiber t v) := by
    letI := (s v).index
    infer_instance
  have hp (v : FunctionPlace F⟮X⟯) := exists_local_topological_comparison t v (s v) i j ρ
  choose H hH using hp
  have hI : ∀ᶠ v in cofinite, ∀ g, g ∈ integralPoints (baseData F) j v ↔
      ∀ w : Fiber t v, H v g w ∈ integralPoints (extensionData t) i w.val := by
    filter_upwards [specialized_integral_forward t i j ρ, specialized_integral_reverse t i j ρ] with v hf hr g
    simp only [hH]
    exact ⟨hf (s v) g, hr (s v) g⟩
  obtain ⟨E, hE⟩ := exists_full_adelic_comparison t i j hfinite H hI
  exact ⟨{
    below := below t
    below_val := fun _ => rfl
    finite_fiber := hfinite
    completionMap := fun v => (s v).factor
    completionMap_continuous := fun v => (s v).continuous_factor
    completionMap_comp := fun v => (s v).factor_comp t v
    localEquiv := H
    localEquiv_apply := hH
    integral_iff := hI
    adelicEquiv := E
    adelicEquiv_apply := hE }⟩

end LinearAlgebraicGroups.Arithmetic.FunctionFieldWeilAdelicPoints
