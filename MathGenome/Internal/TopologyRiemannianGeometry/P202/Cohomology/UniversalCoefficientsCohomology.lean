import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Cohomology.UniversalCoefficientsCohomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Cohomology.Pairs
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.RelativeSingularChains
import MathGenome.Internal.AlgebraCore.P103.Ch11.UniversalCoefficientsCohomology
import MathGenome.Internal.AlgebraCore.P103.Ch11.UniversalCoefficientsSplitting
import MathGenome.Internal.AlgebraCore.P103.Ch11.VanishingAndFlatness

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
namespace P202.UniversalCoefficientsCohomology
open P202Specs.UniversalCoefficientsCohomology P202Specs.SingularChains
  P202Specs.RelativeSingularChains
universe u v w t
variable (R : Type u) [CommRing R]



namespace Q
export P103.Specs.Ch11.UniversalCoefficientsCohomology
  (ProjectiveTermsAndBoundaries IsRestriction IsExtCoker CokerSequence BoundaryCoker
   cohomologyModule)
end Q
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch10.Comparison

variable (A : Type v) [AddCommGroup A] [Module R A]

theorem evaluation_formula (C : ChainComplex (ModuleCat.{t} R) ℤ) (n : ℤ)
    (a : Algebraic.cycles (dualChain R A C) n) (z : Algebraic.cycles C n) :
    P202Specs.UniversalCoefficientsCohomology.evaluation R A C n
      (cycleClass R (dualChain R A C) n a) (cycleClass R C n z) =
        (show C.X n →ₗ[R] A from a.val) z.val := by
  simp only [P202Specs.UniversalCoefficientsCohomology.evaluation, cycleClass,
    LinearMap.comp_apply, LinearMap.lcomp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  rfl

/-- Evaluation is unchanged by both grading and scalar adapters. -/
theorem evaluation_adapter (C : ChainComplex (ModuleCat.{t} R) ℤ)
    (h0 : C.d 0 (-1) = 0) (n : ℕ)
    (β : Algebraic.Homology (homComplex (trunc R C) A) n →ₗ[ℤ]
      (Algebraic.Homology (trunc R C) n →ₗ[R] A))
    (hβ : Q.IsRestriction (trunc R C) (ModuleCat.of R A) n β) :
    letI := Q.cohomologyModule (trunc R C) (ModuleCat.of R A) n
    ∀ x y, P202Specs.UniversalCoefficientsCohomology.evaluation R A C n
      (cohomologyEquiv R A C h0 n x) (chainHomologyEquiv R C h0 n y) = β x y := by
  letI := Q.cohomologyModule (trunc R C) (ModuleCat.of R A) n
  intro x y
  obtain ⟨a, rfl⟩ := (Algebraic.cycleBoundaries (homComplex (trunc R C) A) n).mkQ_surjective x
  obtain ⟨z, rfl⟩ := (Algebraic.cycleBoundaries (trunc R C) n).mkQ_surjective y
  change P202Specs.UniversalCoefficientsCohomology.evaluation R A C n
    (cycleClass R (dualChain R A C) n (dualTruncCyclesEquiv R A C n a))
    (cycleClass R C n (truncCyclesEquiv R C h0 n z)) = _
  rw [evaluation_formula]
  exact (hβ a z).symm


theorem generic_split [IsDomain R] [IsPrincipalIdealRing R] :
    Expected.genericSplit.{u,v,t} R A := by
  intro C h0 hfree n E N hN
  have hf : ∀ k, Module.Free R ((trunc R C).X k) := hfree
  have hC := (P103.Ch11.UniversalCoefficientsSplitting.pid_cohomology (trunc R C) hf).1
  obtain ⟨S⟩ := (P103.Ch11.UniversalCoefficientsSplitting.pid_cohomology (trunc R C) hf).2
  obtain ⟨e,a₀,b₀,he,hseq,hi,hx,hs⟩ :=
    P103.Ch11.UniversalCoefficientsCohomology.universal_coefficients
      (trunc R C) hC (ModuleCat.of R A) n N hN
  letI := extModule E (A := ModuleCat.of R (Algebraic.Homology (trunc R C) n)) ⟨N,hN⟩ (ModuleCat.of R A)
  letI := Q.cohomologyModule (trunc R C) (ModuleCat.of R A) (n+1)
  obtain ⟨a,b,ha,hb⟩ :=
    (P103.Ch11.UniversalCoefficientsCohomology.scalar_compatibility
      (trunc R C) hC (ModuleCat.of R A) n E N hN).1 e a₀ b₀ he hseq
  have ha' : ∀ x, a x = a₀ (e x) := fun x =>
    congrArg (fun f : ExtWith N A 1 →+ _ => f x) ha
  have hb' : ∀ x, b x = b₀ x := fun x =>
    congrArg (fun f : Algebraic.Homology (homComplex (trunc R C) A) (n+1) →+ _ => f x) hb
  obtain ⟨s,hsplit⟩ :=
    P103.Ch11.UniversalCoefficientsSplitting.cohomology_scalar_splitting
      (trunc R C) S (ModuleCat.of R A) (n+1) b₀ hseq.2.1
  let T := cohomologyEquiv R A C h0 (n+1)
  let H := chainHomologyEquiv R C h0 (n+1)
  let D : (Algebraic.Homology (trunc R C) (n+1) →ₗ[R] A) ≃ₗ[R]
      (C.homology ((n+1 : ℕ) : ℤ) →ₗ[R] A) :=
    LinearEquiv.arrowCongr H (LinearEquiv.refl R A)
  have hv : ∀ x, P202Specs.UniversalCoefficientsCohomology.evaluation R A C ((n+1 : ℕ) : ℤ)
      (T x) = D (b₀ x) := by
    intro x
    apply LinearMap.ext
    intro y
    change P202Specs.UniversalCoefficientsCohomology.evaluation R A C ((n+1 : ℕ) : ℤ)
      (T x) y = b₀ x (H.symm y)
    have h := evaluation_adapter R A C h0 (n+1) b₀ hseq.2.1 x (H.symm y)
    change P202Specs.UniversalCoefficientsCohomology.evaluation R A C ((n+1 : ℕ) : ℤ)
      (T x) (H (H.symm y)) = b₀ x (H.symm y) at h
    simpa only [H.apply_symm_apply] using h
  refine ⟨T.toLinearMap.comp a, T.toLinearMap.comp (s.comp D.symm.toLinearMap), ?_, ?_, ?_, ?_,
    e,a₀,b₀,he,hseq,?_⟩
  · intro x y hxy
    apply hi
    change a₀ (e x) = a₀ (e y)
    rw [← ha', ← ha']
    exact T.injective hxy
  · intro y
    obtain ⟨x, rfl⟩ := T.surjective y
    rw [hv]
    change D (b₀ x) = 0 ↔ ∃ z, T (a z) = T x
    rw [D.map_eq_zero_iff, hx x]
    constructor
    · rintro ⟨z,hz⟩
      exact ⟨z, congrArg T ((ha' z).trans hz)⟩
    · rintro ⟨z,hz⟩
      exact ⟨z,(ha' z).symm.trans (T.injective hz)⟩
  · intro y
    obtain ⟨x,hx⟩ := hs (D.symm y)
    exact ⟨T x, (hv x).trans ((congrArg D hx).trans (D.apply_symm_apply y))⟩
  · apply LinearMap.ext
    intro y
    change P202Specs.UniversalCoefficientsCohomology.evaluation R A C ((n+1 : ℕ) : ℤ)
      (T (s (D.symm y))) = y
    rw [hv]
    have h := LinearMap.congr_fun hsplit (D.symm y)
    change b₀ (s (D.symm y)) = D.symm y at h
    rw [h, D.apply_symm_apply]
  · intro x
    change T (a x) = T (a₀ (e x))
    rw [ha']


/-- At the endpoint evaluation is an isomorphism without any projectivity
or PID hypothesis. The previous ordinary homology is zero. -/
theorem degree_zero : Expected.degreeZero.{u,v,t} R A := by
  intro C h0
  obtain ⟨e,he⟩ := P103.Ch11.UniversalCoefficientsCohomology.degree_zero
    (trunc R C) (ModuleCat.of R A)
  letI := Q.cohomologyModule (trunc R C) (ModuleCat.of R A) 0
  let T := cohomologyEquiv R A C h0 0
  let H := chainHomologyEquiv R C h0 0
  let D : (Algebraic.Homology (trunc R C) 0 →ₗ[R] A) ≃ₗ[R]
      (C.homology 0 →ₗ[R] A) :=
    LinearEquiv.arrowCongr H (LinearEquiv.refl R A)
  have hv : ∀ x, P202Specs.UniversalCoefficientsCohomology.evaluation R A C 0
      (T x) = D (e x) := by
    intro x
    apply LinearMap.ext
    intro y
    change P202Specs.UniversalCoefficientsCohomology.evaluation R A C 0
      (T x) y = e x (H.symm y)
    have h := evaluation_adapter R A C h0 0 e.toLinearMap he x (H.symm y)
    change P202Specs.UniversalCoefficientsCohomology.evaluation R A C 0
      (T x) (H (H.symm y)) = e x (H.symm y) at h
    simpa only [H.apply_symm_apply] using h
  constructor
  · intro x y hxy
    obtain ⟨x,rfl⟩ := T.surjective x
    obtain ⟨y,rfl⟩ := T.surjective y
    apply congrArg T
    apply e.injective
    apply D.injective
    rw [← hv, ← hv]
    exact hxy
  · intro y
    refine ⟨T (e.symm (D.symm y)), ?_⟩
    rw [hv, e.apply_symm_apply, D.apply_symm_apply]

theorem ordinary_free : Expected.ordinaryFree.{u,w} R := by
  intro X n
  haveI : Module.Free R ((complex R R X).X n) := by
    change Module.Free R (Simplex X n →₀ R)
    infer_instance
  exact Module.Free.of_equiv (ordinaryNonnegativeIso R R X n).toLinearEquiv.symm

theorem relative_free : Expected.relativeFree.{u,w} R := by
  intro P n
  obtain ⟨b, _⟩ := P202.RelativeSingularChains.quotient_basis R P n
  haveI := Module.Free.of_basis b
  exact Module.Free.of_equiv (ordinaryDegreeIso R R P n).toLinearEquiv.symm

theorem ordinary_zero : Expected.ordinaryZero.{u,w} R := by
  intro X
  exact (P202.SingularChains.ordinary_negative_chains R R X (-1) (by omega)).eq_of_tgt _ _

theorem relative_zero : Expected.relativeZero.{u,w} R := by
  intro P
  exact (P202.RelativeSingularChains.ordinary_negative R R P (-1) (by omega)).1.eq_of_tgt _ _


theorem topological_split : topological_split_type.{u,v,w} := by
  intro R _ _ _ A _ _
  constructor
  · intro X
    exact ⟨ordinary_zero R X, fun n E N hN =>
      generic_split R A (ordinaryComplex R R X) (ordinary_zero R X)
        (ordinary_free R X) n E N hN⟩
  · intro P
    exact ⟨relative_zero R P, fun n E N hN =>
      generic_split R A (ordinary R R P) (relative_zero R P)
        (relative_free R P) n E N hN⟩

theorem topological_zero : topological_zero_type.{u,v,w} := by
  intro R _ A _ _
  exact ⟨fun X => degree_zero R A (ordinaryComplex R R X) (ordinary_zero R X),
    fun P => degree_zero R A (ordinary R R P) (relative_zero R P)⟩


/-- The representative interface agrees with the categorical homology projection. -/
theorem cycleClass_eq {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{t} R) c) (n : ι)
    (z : Algebraic.cycles K n) :
    cycleClass R K n z = K.homologyπ n ((K.sc n).moduleCatCyclesIso.inv z) := by
  change (K.sc n).moduleCatHomologyIso.inv ((K.sc n).moduleCatLeftHomologyData.π z) = _
  exact (congrArg (fun f => f z) (K.sc n).moduleCatCyclesIso_inv_π).symm

/-- Categorical homology maps send a represented cycle to its represented image. -/
theorem cycleClass_map {ι : Type*} {c : ComplexShape ι}
    {C D : HomologicalComplex (ModuleCat.{t} R) c} (f : C ⟶ D) (n : ι)
    (z : Algebraic.cycles C n) :
    HomologicalComplex.homologyMap f n (cycleClass R C n z) =
      cycleClass R D n (Algebraic.cyclesMap f n z) := by
  rw [cycleClass_eq, cycleClass_eq]
  have hc : HomologicalComplex.cyclesMap f n ((C.sc n).moduleCatCyclesIso.inv z) =
      (D.sc n).moduleCatCyclesIso.inv (Algebraic.cyclesMap f n z) := by
    apply (ModuleCat.mono_iff_injective (D.iCycles n)).mp inferInstance
    have h := congrArg (fun f => f ((C.sc n).moduleCatCyclesIso.inv z))
      (HomologicalComplex.cyclesMap_i f n)
    change D.iCycles n (HomologicalComplex.cyclesMap f n ((C.sc n).moduleCatCyclesIso.inv z)) =
      (f.f n) (C.iCycles n ((C.sc n).moduleCatCyclesIso.inv z)) at h
    rw [h]
    have hC := congrArg (fun f => f z) (C.sc n).moduleCatCyclesIso_inv_iCycles
    have hD := congrArg (fun k => k (Algebraic.cyclesMap f n z))
      (D.sc n).moduleCatCyclesIso_inv_iCycles
    change C.iCycles n ((C.sc n).moduleCatCyclesIso.inv z) = z.val at hC
    change D.iCycles n ((D.sc n).moduleCatCyclesIso.inv (Algebraic.cyclesMap f n z)) =
      (Algebraic.cyclesMap f n z).val at hD
    rw [hC, hD]
    rfl
  have h := congrArg (fun f => f ((C.sc n).moduleCatCyclesIso.inv z))
    (HomologicalComplex.homologyπ_naturality f n)
  change HomologicalComplex.homologyMap f n
      (C.homologyπ n ((C.sc n).moduleCatCyclesIso.inv z)) =
    D.homologyπ n (HomologicalComplex.cyclesMap f n ((C.sc n).moduleCatCyclesIso.inv z)) at h
  rw [hc] at h
  exact h


theorem cycleClass_surjective {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{t} R) c) (n : ι) :
    Function.Surjective (cycleClass R C n) := by
  intro x
  obtain ⟨z,hz⟩ := (Algebraic.cycleBoundaries C n).mkQ_surjective
    (quotientHomologyEquiv R C n x)
  refine ⟨z, ?_⟩
  unfold cycleClass
  rw [show Algebraic.homologyClass C n z = quotientHomologyEquiv R C n x from hz]
  exact (quotientHomologyEquiv R C n).symm_apply_apply x

/-- The canonical evaluation square commutes for arbitrary simultaneous
chain and coefficient maps, hence for continuous maps and maps of pairs. -/
theorem evaluation_natural : evaluation_natural_type.{u,v,t} := by
  intro R _ A B _ _ _ _ C D f g n a z
  obtain ⟨a,rfl⟩ := cycleClass_surjective R (dualChain R A C) n a
  obtain ⟨z,rfl⟩ := cycleClass_surjective R D n z
  rw [cycleClass_map, cycleClass_map, evaluation_formula, evaluation_formula]
  rfl

/-- Pullback with unchanged coefficients is exactly the accepted dual functor. -/
theorem dualMap_id {C D : ChainComplex (ModuleCat.{t} R) ℤ} (f : D ⟶ C) :
    dualMap R A f A LinearMap.id =
      (P202Specs.CohomologyPairs.dualComplexFunctor R A (ComplexShape.down ℤ)).map f.op := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro x
  rfl


/-- Naturality of the chain-homology grading adapter. -/
theorem chainHomologyEquiv_natural {C D : ChainComplex (ModuleCat.{t} R) ℤ}
    (hC : C.d 0 (-1) = 0) (hD : D.d 0 (-1) = 0) (f : D ⟶ C) (n : ℕ)
    (x : Algebraic.Homology (trunc R D) n) :
    chainHomologyEquiv R C hC n
      (Algebraic.homologyMap (HomologicalComplex.restrictionMap f nonnegativeEmbedding) n x) =
    HomologicalComplex.homologyMap f n (chainHomologyEquiv R D hD n x) := by
  obtain ⟨z,rfl⟩ := (Algebraic.cycleBoundaries (trunc R D) n).mkQ_surjective x
  change cycleClass R C n (truncCyclesEquiv R C hC n
      (Algebraic.cyclesMap (HomologicalComplex.restrictionMap f nonnegativeEmbedding) n z)) =
    HomologicalComplex.homologyMap f n
      (cycleClass R D n (truncCyclesEquiv R D hD n z))
  rw [cycleClass_map]
  rfl

/-- The Hom comparison preserves all pullbacks and coefficient maps. -/
theorem cohomologyEquiv_natural (B : Type v) [AddCommGroup B] [Module R B]
    {C D : ChainComplex (ModuleCat.{t} R) ℤ}
    (hC : C.d 0 (-1) = 0) (hD : D.d 0 (-1) = 0) (f : D ⟶ C)
    (g : A →ₗ[R] B) (n : ℕ) :
    letI := Q.cohomologyModule (trunc R C) (ModuleCat.of R A) n
    letI := Q.cohomologyModule (trunc R D) (ModuleCat.of R B) n
    ∀ x, cohomologyEquiv R B D hD n
      (Algebraic.homologyMap
        (homPreMap (HomologicalComplex.restrictionMap f nonnegativeEmbedding) A ≫
          homPostMap (trunc R D) g) n x) =
    HomologicalComplex.homologyMap (dualMap R A f B g) n
      (cohomologyEquiv R A C hC n x) := by
  letI := Q.cohomologyModule (trunc R C) (ModuleCat.of R A) n
  letI := Q.cohomologyModule (trunc R D) (ModuleCat.of R B) n
  intro x
  obtain ⟨a,rfl⟩ := (Algebraic.cycleBoundaries (homComplex (trunc R C) A) n).mkQ_surjective x
  change cycleClass R (dualChain R B D) n (dualTruncCyclesEquiv R B D n
      (Algebraic.cyclesMap
        (homPreMap (HomologicalComplex.restrictionMap f nonnegativeEmbedding) A ≫
          homPostMap (trunc R D) g) n a)) =
    HomologicalComplex.homologyMap (dualMap R A f B g) n
      (cycleClass R (dualChain R A C) n (dualTruncCyclesEquiv R A C n a))
  rw [cycleClass_map]
  rfl

theorem edge_natural : edge_natural_type.{u,v,t} := by
  intro R _ _ _ A B _ _ _ _ C D hC hD hfC hfD f g n E N N' hN hN' e e' a b a' b'
    he he' hs hs'
  letI := Q.cohomologyModule (trunc R C) (ModuleCat.of R A) (n+1)
  letI := Q.cohomologyModule (trunc R D) (ModuleCat.of R B) (n+1)
  intro x
  have hPC := (P103.Ch11.UniversalCoefficientsSplitting.pid_cohomology (trunc R C) hfC).1
  have hPD := (P103.Ch11.UniversalCoefficientsSplitting.pid_cohomology (trunc R D) hfD).1
  have hn := (P103.Ch11.UniversalCoefficientsCohomology.naturality
    (trunc R C) (trunc R D) hPC hPD
    (HomologicalComplex.restrictionMap f nonnegativeEmbedding)
    (ModuleCat.of R A) (ModuleCat.of R B) (ModuleCat.ofHom g) n E N N' hN hN'
    e e' a b a' b' he he' hs hs').1 x
  rw [← cohomologyEquiv_natural R A B hC hD f g (n+1)]
  exact congrArg (cohomologyEquiv R B D hD (n+1)) hn


theorem zero_tail : zero_tail_type.{u,v,w} := by
  intro R _ A _ _
  constructor
  · intro X
    have h0 := P202.SingularChains.ordinary_negative_homology R R X (-1) (by omega)
    haveI := ModuleCat.subsingleton_of_isZero h0
    haveI : Module.Free R ((ordinaryComplex R R X).homology (-1)) :=
      Module.Free.of_subsingleton R _
    refine ⟨h0, ?_⟩
    exact P103.Ch11.VanishingAndFlatness.ext_projective R _ A Module.Projective.of_free
      (AlgebraicExt.resolutionFamily R ((ordinaryComplex R R X).homology (-1))).val
      (AlgebraicExt.resolutionFamily R ((ordinaryComplex R R X).homology (-1))).property 0
  · intro P
    have h0 := (P202.RelativeSingularChains.ordinary_negative R R P (-1) (by omega)).2
    haveI := ModuleCat.subsingleton_of_isZero h0
    haveI : Module.Free R ((ordinary R R P).homology (-1)) :=
      Module.Free.of_subsingleton R _
    refine ⟨h0, ?_⟩
    exact P103.Ch11.VanishingAndFlatness.ext_projective R _ A Module.Projective.of_free
      (AlgebraicExt.resolutionFamily R ((ordinary R R P).homology (-1))).val
      (AlgebraicExt.resolutionFamily R ((ordinary R R P).homology (-1))).property 0


theorem actual_split : actual_split_type.{u,v,t} := by
  intro R _ _ _ A _ _ C h0 hf n
  let N := AlgebraicExt.resolutionFamily R
    (ModuleCat.of R (Algebraic.Homology (trunc R C) n))
  obtain ⟨a,s,hi,hx,hs,hsect,hnorm⟩ :=
    generic_split R A C h0 hf n (AlgebraicExt.extMaps 1) N.val N.property
  let I := extComparison R A C h0 n
  refine ⟨a.comp I.toLinearMap, s, hi.comp I.injective, ?_, hs, hsect, ?_⟩
  · intro y
    rw [hx y]
    constructor
    · rintro ⟨x,hx⟩
      refine ⟨I.symm x, ?_⟩
      change a (I (I.symm x)) = y
      rw [I.apply_symm_apply]
      exact hx
    · rintro ⟨x,hx⟩
      exact ⟨I x,hx⟩
  · obtain ⟨e,a₀,b₀,he,hseq,hformula⟩ := hnorm
    exact ⟨e,a₀,b₀,he,hseq,fun x => hformula (I x)⟩


/-- Comparison of Ext models commutes with the genuine bifunctorial Ext maps. -/
theorem extComparison_natural (B : Type v) [AddCommGroup B] [Module R B]
    {C D : ChainComplex (ModuleCat.{t} R) ℤ}
    (hC : C.d 0 (-1) = 0) (hD : D.d 0 (-1) = 0) (f : D ⟶ C)
    (g : A →ₗ[R] B) (n : ℕ) (x : actualExt R A C n) :
    extComparison R B D hD n
      (AlgebraicExt.extMapLinear R 1 (HomologicalComplex.homologyMap f n) (ModuleCat.ofHom g) x) =
    (AlgebraicExt.extMaps (R := R) 1).map
      (AlgebraicExt.resolutionFamily R (ModuleCat.of R (Algebraic.Homology (trunc R C) n)))
      (AlgebraicExt.resolutionFamily R (ModuleCat.of R (Algebraic.Homology (trunc R D) n)))
      (ModuleCat.ofHom (Algebraic.homologyMap
        (HomologicalComplex.restrictionMap f nonnegativeEmbedding) n)) (ModuleCat.ofHom g)
      (extComparison R A C hC n x) := by
  let E := AlgebraicExt.extMaps (R := R) 1
  let HC := chainHomologyEquiv R C hC n
  let HD := chainHomologyEquiv R D hD n
  let m := Algebraic.homologyMap (HomologicalComplex.restrictionMap f nonnegativeEmbedding) n
  have hsq : ModuleCat.ofHom HD.toLinearMap ≫ HomologicalComplex.homologyMap f n =
      ModuleCat.ofHom m ≫ ModuleCat.ofHom HC.toLinearMap := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    exact (chainHomologyEquiv_natural R hC hD f n y).symm
  have hl := E.comp
    (AlgebraicExt.resolutionFamily R (C.homology n))
    (AlgebraicExt.resolutionFamily R (D.homology n))
    (AlgebraicExt.resolutionFamily R (ModuleCat.of R (Algebraic.Homology (trunc R D) n)))
    (HomologicalComplex.homologyMap f n) (ModuleCat.ofHom HD.toLinearMap)
    (ModuleCat.ofHom g) (𝟙 (ModuleCat.of R B))
  have hr := E.comp
    (AlgebraicExt.resolutionFamily R (C.homology n))
    (AlgebraicExt.resolutionFamily R (ModuleCat.of R (Algebraic.Homology (trunc R C) n)))
    (AlgebraicExt.resolutionFamily R (ModuleCat.of R (Algebraic.Homology (trunc R D) n)))
    (ModuleCat.ofHom HC.toLinearMap) (ModuleCat.ofHom m)
    (𝟙 (ModuleCat.of R A)) (ModuleCat.ofHom g)
  rw [Category.comp_id, hsq] at hl
  rw [Category.id_comp] at hr
  exact LinearMap.congr_fun (hl.symm.trans hr) x

theorem actual_natural : actual_natural_type.{u,v,t} := by
  intro R _ _ _ A B _ _ _ _ C D hC hD hfC hfD f g n α α' hα hα' x
  obtain ⟨e,a,b,he,hs,hformula⟩ := hα
  obtain ⟨e',a',b',he',hs',hformula'⟩ := hα'
  rw [hformula, hformula']
  letI := Q.cohomologyModule (trunc R C) (ModuleCat.of R A) (n+1)
  letI := Q.cohomologyModule (trunc R D) (ModuleCat.of R B) (n+1)
  have hn := edge_natural R A B C D hC hD hfC hfD f g n
    (AlgebraicExt.extMaps 1) _ _
    (AlgebraicExt.resolutionFamily R (ModuleCat.of R (Algebraic.Homology (trunc R C) n))).property
    (AlgebraicExt.resolutionFamily R (ModuleCat.of R (Algebraic.Homology (trunc R D) n))).property
    e e' a b a' b' he he' hs hs' (extComparison R A C hC n x)
  rw [← extComparison_natural R A B hC hD f g n x] at hn
  exact hn


/-- Singular and relative cohomological UCT, with no finite-type assumption. -/
theorem singular_uct : singular_uct_type.{u,v,w} := by
  intro R _ _ _ A _ _
  exact ⟨fun X => ⟨ordinary_zero R X, actual_split R A (ordinaryComplex R R X)
      (ordinary_zero R X) (ordinary_free R X)⟩,
    fun P => ⟨relative_zero R P, actual_split R A (ordinary R R P)
      (relative_zero R P) (relative_free R P)⟩⟩

/-- The endpoint sequence has zero left arrow and the inverse of evaluation
as its R-linear section. -/
theorem split_exact_zero (C : ChainComplex (ModuleCat.{t} R) ℤ)
    (h0 : C.d 0 (-1) = 0) [Subsingleton (actualExt R A C (-1))] :
    SplitExactAt R A C 0 := by
  let e := LinearEquiv.ofBijective (evaluation R A C 0) (degree_zero R A C h0)
  refine ⟨0, e.symm.toLinearMap, ?_, ?_, e.surjective, ?_⟩
  · intro x y _
    exact Subsingleton.elim (α := actualExt R A C (-1)) x y
  · intro y
    constructor
    · intro hy
      refine ⟨0, ?_⟩
      exact (e.injective (hy.trans e.map_zero.symm)).symm
    · rintro ⟨x, hx⟩
      rw [← hx]
      exact map_zero _
  · apply LinearMap.ext
    intro y
    exact e.apply_symm_apply y

theorem split_exact_positive [IsDomain R] [IsPrincipalIdealRing R]
    (C : ChainComplex (ModuleCat.{t} R) ℤ) (h0 : C.d 0 (-1) = 0)
    (hf : ∀ k : ℕ, Module.Free R (C.X (k : ℤ))) (n : ℕ) :
    SplitExactAt R A C (n+1) := by
  obtain ⟨a, s, hi, hx, hs, hsect, _⟩ := actual_split R A C h0 hf n
  exact ⟨a, s, hi, hx, hs, hsect⟩

/-- Both singular cohomological sequences, now uniformly including degree zero. -/
theorem all_degrees : all_degrees_type.{u,v,w} := by
  intro R _ _ _ A _ _
  constructor
  · intro X n
    cases n with
    | zero =>
      haveI := ((zero_tail R A).1 X).2
      exact split_exact_zero R A (ordinaryComplex R R X) (ordinary_zero R X)
    | succ n =>
      exact split_exact_positive R A (ordinaryComplex R R X) (ordinary_zero R X)
        (ordinary_free R X) n
  · intro P n
    cases n with
    | zero =>
      haveI := ((zero_tail R A).2 P).2
      exact split_exact_zero R A (ordinary R R P) (relative_zero R P)
    | succ n =>
      exact split_exact_positive R A (ordinary R R P) (relative_zero R P)
        (relative_free R P) n

end P202.UniversalCoefficientsCohomology
