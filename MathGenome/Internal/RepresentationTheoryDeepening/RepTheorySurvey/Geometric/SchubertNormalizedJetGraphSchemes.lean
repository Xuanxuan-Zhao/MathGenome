import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SchubertNormalizedJetGraphSchemes
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.LatticeModels
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

namespace RepTheorySurvey.Geometric.SchubertNormalizedJetGraphSchemes

open SchubertNormalizedJetGraphSpecs

open LatticeModelSpecs
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open LinearAlgebraicGroups (Points SchemeOver testSpec)
open LinearAlgebraicGroups.Specs.GrassmannianCharts
open LinearAlgebraicGroups.GrassmannianCharts (chartMatrixEquiv)
open scoped Matrix Topology

noncomputable section

private theorem rev_ne (i : Fin 2) : i.rev ≠ i := by
  fin_cases i <;> decide

private theorem eq_or_eq_rev (j i : Fin 2) : j = i ∨ j = i.rev := by
  fin_cases j <;> fin_cases i <;> decide

variable {b : ℤ} {m : ℕ} {d : WindowDimension 2 b m} (hd : d.val = m)

private theorem mem_jetPivot (i : Fin 2) (p : Fin 2 × Fin m) :
    p ∈ (jetPivot hd i).val ↔ p.1 = i.rev := by
  constructor
  · intro h
    obtain ⟨k, _, hk⟩ := Finset.mem_map.mp h
    exact (congrArg Prod.fst hk).symm
  · rintro h
    exact Finset.mem_map.mpr ⟨p.2, Finset.mem_univ _, Prod.ext h.symm rfl⟩

private def pivotCoefficients (i : Fin 2) : Fin m ≃ Inside (jetPivot hd i) where
  toFun k := ⟨(i.rev, k), (mem_jetPivot hd i _).2 rfl⟩
  invFun k := k.val.2
  left_inv _ := rfl
  right_inv k := Subtype.ext (Prod.ext ((mem_jetPivot hd i _).1 k.property).symm rfl)

private def outsideCoefficients (i : Fin 2) : Fin m ≃ Outside (jetPivot hd i) where
  toFun k := ⟨(i, k), fun h ↦ (rev_ne i).symm ((mem_jetPivot hd i _).1 h)⟩
  invFun k := k.val.2
  left_inv _ := rfl
  right_inv k := Subtype.ext (Prod.ext
    (((eq_or_eq_rev k.val.1 i).resolve_right fun h ↦
      k.property ((mem_jetPivot hd i _).2 h)).symm) rfl)

private def insideJet (i : Fin 2) : JetRing m ≃ₗ[ℂ] (Inside (jetPivot hd i) → ℂ) :=
  jetCoefficients m ≪≫ₗ LinearEquiv.piCongrLeft' ℂ (fun _ ↦ ℂ) (pivotCoefficients hd i)

private def outsideJet (i : Fin 2) : JetRing m ≃ₗ[ℂ] (Outside (jetPivot hd i) → ℂ) :=
  jetCoefficients m ≪≫ₗ LinearEquiv.piCongrLeft' ℂ (fun _ ↦ ℂ) (outsideCoefficients hd i)

private def graphAction (i : Fin 2) (A : Matrix (Outside (jetPivot hd i)) (Inside (jetPivot hd i)) ℂ) :
    JetRing m →ₗ[ℂ] JetRing m :=
  (outsideJet hd i).symm.toLinearMap.comp ((Matrix.toLin' A).comp (insideJet hd i).toLinearMap)

private theorem outsideJet_graphAction (i : Fin 2)
    (A : Matrix (Outside (jetPivot hd i)) (Inside (jetPivot hd i)) ℂ) (u : JetRing m) :
    outsideJet hd i (graphAction hd i A u) = A *ᵥ insideJet hd i u := by
  exact (outsideJet hd i).apply_symm_apply _

private theorem windowBasis_coeff (x : Window 2 b m) (j : Fin 2) (k : Fin m) :
    (windowBasis 2 b m).equivFun x (j, k) = jetCoefficients m (windowJets 2 b m x j) k := by
  rw [windowBasis, Module.Basis.equivFun_ofEquivFun]
  rfl

private theorem windowJets_operator (x : Window 2 b m) (j : Fin 2) :
    windowJets 2 b m (windowOperator 2 b m x) j = jetReduction m t * windowJets 2 b m x j := by
  change windowJets 2 b m (t • x) j = _
  rw [map_smul]
  rfl

private theorem graphPlane_mem (i : Fin 2)
    (A : Matrix (Outside (jetPivot hd i)) (Inside (jetPivot hd i)) ℂ) (x : Window 2 b m) :
    x ∈ grassmannianSubspace (windowBasis 2 b m) (windowDimension_le d)
      (grassmannianChartPoint (windowBasis 2 b m) (windowDimension_le d) (jetPivot hd i) A) ↔
    windowJets 2 b m x i = graphAction hd i A (windowJets 2 b m x i.rev) := by
  let basis := windowBasis 2 b m
  let P := grassmannianSubspace basis (windowDimension_le d)
    (grassmannianChartPoint basis (windowDimension_le d) (jetPivot hd i) A)
  let e := basis.equivFun
  change x ∈ P ↔ _
  have hmap : e x ∈ P.map e.toLinearMap ↔ x ∈ P := by
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
  rw [← hmap]
  dsimp only [P, e, basis]
  rw [grassmannianChartSubspace, LinearMap.mem_range]
  have hi (j : Inside (jetPivot hd i)) :
      e x j.val = insideJet hd i (windowJets 2 b m x i.rev) j := by
    rcases j with ⟨⟨j, k⟩, h⟩
    obtain rfl : j = i.rev := (mem_jetPivot hd i _).1 h
    exact windowBasis_coeff x i.rev k
  have ho (j : Outside (jetPivot hd i)) :
      e x j.val = outsideJet hd i (windowJets 2 b m x i) j := by
    rcases j with ⟨⟨j, k⟩, h⟩
    have hj : j = i := (eq_or_eq_rev j i).resolve_right fun hj ↦
      h ((mem_jetPivot hd i _).2 hj)
    subst j
    exact windowBasis_coeff x i k
  constructor
  · rintro ⟨u, hu⟩
    change graphMatrix (jetPivot hd i) A *ᵥ u = e x at hu
    have hu' : u = insideJet hd i (windowJets 2 b m x i.rev) := by
      funext j
      rw [← hi j, ← hu, graphMatrix_inside]
    apply (outsideJet hd i).injective
    rw [outsideJet_graphAction, ← hu']
    funext j
    rw [← ho j, ← hu, graphMatrix_outside]
  · intro h
    let u := insideJet hd i (windowJets 2 b m x i.rev)
    refine ⟨u, ?_⟩
    change graphMatrix (jetPivot hd i) A *ᵥ u = e x
    funext j
    by_cases hj : j ∈ (jetPivot hd i).val
    · rw [graphMatrix_inside _ _ _ ⟨j, hj⟩, hi ⟨j, hj⟩]
    · rw [graphMatrix_outside _ _ _ ⟨j, hj⟩, ho ⟨j, hj⟩, h, outsideJet_graphAction]

private theorem stable_iff_commutes (i : Fin 2)
    (A : Matrix (Outside (jetPivot hd i)) (Inside (jetPivot hd i)) ℂ) :
    StablePlane (windowBasis 2 b m) (windowDimension_le d) (windowOperator 2 b m)
      (grassmannianChartPoint (windowBasis 2 b m) (windowDimension_le d) (jetPivot hd i) A) ↔
    ∀ u : JetRing m, graphAction hd i A (jetReduction m t * u) =
      jetReduction m t * graphAction hd i A u := by
  rw [StablePlane, Submodule.map_le_iff_le_comap]
  constructor
  · intro h u
    let xs : Fin 2 → JetRing m := fun j ↦ if j = i then graphAction hd i A u else u
    let x : Window 2 b m := (windowJets 2 b m).symm xs
    have hx : windowJets 2 b m x = xs := (windowJets 2 b m).apply_symm_apply xs
    have hxi : windowJets 2 b m x i = graphAction hd i A u := by simp [hx, xs]
    have hxj : windowJets 2 b m x i.rev = u := by simp [hx, xs, rev_ne i]
    have hp := (graphPlane_mem hd i A x).2 (by rw [hxi, hxj])
    have hT := (graphPlane_mem hd i A (windowOperator 2 b m x)).1 (h hp)
    rw [windowJets_operator, windowJets_operator, hxi, hxj] at hT
    exact hT.symm
  · intro h x hx
    apply (graphPlane_mem hd i A _).2
    rw [windowJets_operator, windowJets_operator, h, (graphPlane_mem hd i A x).1 hx]

private theorem jetCoefficients_mul_pow (z : JetRing m) (k : ℕ) (r : Fin m) :
    jetCoefficients m (z * jetReduction m t ^ k) r =
      if k ≤ r.val then jetCoefficients m z
        ⟨r.val - k, lt_of_le_of_lt (Nat.sub_le _ _) r.isLt⟩ else 0 := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
  change jetCoefficients m (jetReduction m f * jetReduction m t ^ k) r = _
  rw [← map_pow, ← map_mul, jetCoefficients_reduce, PowerSeries.coeff_mul_X_pow']
  rfl

private theorem jetCoefficients_pow (k r : Fin m) :
    jetCoefficients m (jetReduction m t ^ k.val) r = (Pi.single k 1 : Fin m → ℂ) r := by
  rw [← map_pow, jetCoefficients_reduce, PowerSeries.coeff_X_pow]
  simp [Pi.single_apply, Fin.ext_iff, eq_comm]

private theorem graphAction_pow (i : Fin 2)
    (A : Matrix (Outside (jetPivot hd i)) (Inside (jetPivot hd i)) ℂ) (k r : Fin m) :
    jetCoefficients m (graphAction hd i A (jetReduction m t ^ k.val)) r =
      A (outsideCoefficients hd i r) (pivotCoefficients hd i k) := by
  have h := congrFun (outsideJet_graphAction hd i A (jetReduction m t ^ k.val))
    (outsideCoefficients hd i r)
  have hins : insideJet hd i (jetReduction m t ^ k.val) =
      Pi.single (pivotCoefficients hd i k) (1 : ℂ) := by
    funext j
    change jetCoefficients m (jetReduction m t ^ k.val) ((pivotCoefficients hd i).symm j) = _
    rw [jetCoefficients_pow]
    simp [Pi.single_apply, Equiv.symm_apply_eq]
  rw [hins, Matrix.mulVec_single_one] at h
  exact h

private theorem graphAction_injective (i : Fin 2) :
    Function.Injective (graphAction hd i) := by
  intro A B h
  ext r k
  obtain ⟨r, rfl⟩ := (outsideCoefficients hd i).surjective r
  obtain ⟨k, rfl⟩ := (pivotCoefficients hd i).surjective k
  simpa only [graphAction_pow] using congrArg
    (fun f : JetRing m →ₗ[ℂ] JetRing m ↦
      jetCoefficients m (f (jetReduction m t ^ k.val)) r) h

private def jetMul (z : JetRing m) : JetRing m →ₗ[ℂ] JetRing m :=
  DistribSMul.toLinearMap ℂ (JetRing m) z

private theorem jetBasis_pow (k : Fin m) :
    Module.Basis.ofEquivFun (jetCoefficients m) k = jetReduction m t ^ k.val := by
  apply (jetCoefficients m).injective
  rw [Module.Basis.coe_ofEquivFun, LinearEquiv.apply_symm_apply]
  funext r
  rw [jetCoefficients_pow]

private theorem graphAction_polynomial (i : Fin 2) (z : Fin m → ℂ) :
    graphAction hd i ((polynomialGraph hd i).map (MvPolynomial.aeval z)) =
      jetMul (- (jetCoefficients m).symm z) := by
  apply (Module.Basis.ofEquivFun (jetCoefficients m)).ext
  intro k
  rw [jetBasis_pow]
  apply (jetCoefficients m).injective
  funext r
  rw [graphAction_pow]
  change MvPolynomial.aeval z (polynomialGraph hd i _ _) =
    jetCoefficients m ((- (jetCoefficients m).symm z) * jetReduction m t ^ k.val) r
  rw [jetCoefficients_mul_pow]
  simp only [polynomialGraph, Matrix.of_apply, outsideCoefficients, pivotCoefficients]
  split <;> simp_all

/-- A stable graph acts on the cyclic jet module by multiplication by one jet. -/
private theorem stableGraph_iff (i : Fin 2)
    (A : Matrix (Outside (jetPivot hd i)) (Inside (jetPivot hd i)) ℂ) :
    StablePlane (windowBasis 2 b m) (windowDimension_le d) (windowOperator 2 b m)
      (grassmannianChartPoint (windowBasis 2 b m) (windowDimension_le d) (jetPivot hd i) A) ↔
    ∃ z : Fin m → ℂ, A = (polynomialGraph hd i).map (MvPolynomial.aeval z) := by
  rw [stable_iff_commutes]
  constructor
  · intro h
    let u := graphAction hd i A 1
    refine ⟨jetCoefficients m (-u), ?_⟩
    apply graphAction_injective hd i
    rw [graphAction_polynomial, LinearEquiv.symm_apply_apply, neg_neg]
    apply (Module.Basis.ofEquivFun (jetCoefficients m)).ext
    intro k
    rw [jetBasis_pow]
    have hpow (n : ℕ) :
        graphAction hd i A (jetReduction m t ^ n) = u * jetReduction m t ^ n := by
      induction n with
      | zero => simp [u]
      | succ n ih => rw [pow_succ', h, ih]; ring
    exact hpow k.val
  · rintro ⟨z, rfl⟩ u
    rw [graphAction_polynomial]
    change _ * (_ * u) = _ * (_ * u)
    ring

private abbrev graphRingHom (i : Fin 2) :
    chartAlgebra (k := ℂ) (jetPivot hd i) →ₐ[ℂ] AffineCoordinateRing m :=
  MvPolynomial.aeval (R := ℂ) fun rc ↦ polynomialGraph hd i rc.1 rc.2

private theorem polynomialGraph_firstColumn (hm : 0 < m) (i : Fin 2) (r : Fin m) :
    polynomialGraph hd i (outsideCoefficients hd i r) (pivotCoefficients hd i ⟨0, hm⟩) =
      -MvPolynomial.X r := by
  simp only [polynomialGraph, Matrix.of_apply]
  rw [ite_eq_left (show (pivotCoefficients hd i ⟨0, hm⟩).val.2.val ≤
    (outsideCoefficients hd i r).val.2.val from Nat.zero_le r.val)]
  rfl

private theorem graphRingHom_surjective (hm : 0 < m) (i : Fin 2) :
    Function.Surjective (graphRingHom hd i) := by
  let g : AffineCoordinateRing m →ₐ[ℂ] chartAlgebra (k := ℂ) (jetPivot hd i) :=
    MvPolynomial.aeval (R := ℂ) fun r ↦
      -MvPolynomial.X (outsideCoefficients hd i r, pivotCoefficients hd i ⟨0, hm⟩)
  have h : (graphRingHom hd i).comp g = AlgHom.id ℂ (AffineCoordinateRing m) := by
    apply MvPolynomial.algHom_ext
    intro r
    simp [g, polynomialGraph_firstColumn hd hm i]
  intro p
  exact ⟨g p, DFunLike.congr_fun h p⟩

private theorem aeval_graph (i : Fin 2) (z : Fin m → ℂ) :
    (MvPolynomial.aeval z).comp (graphRingHom hd i) =
      MvPolynomial.aeval (chartVariables (jetPivot hd i)
        ((polynomialGraph hd i).map (MvPolynomial.aeval z))) := by
  apply MvPolynomial.algHom_ext
  intro rc
  simp [chartVariables, Matrix.map_apply]

/-- The polynomial graphs exhaust the complex solutions of the stability equations.
The Nullstellensatz identifies the resulting kernel with the reduced chart ideal. -/
private theorem graphRingHom_ker (i : Fin 2) :
    RingHom.ker (graphRingHom hd i).toRingHom = reducedStabilityIdeal (jetPivot hd i)
      (operatorInCoordinates (windowBasis 2 b m) (windowOperator 2 b m)) := by
  let I := jetPivot hd i
  let D := operatorInCoordinates (windowBasis 2 b m) (windowOperator 2 b m)
  let S := stabilityIdeal I D
  have hzero (x : Outside I × Inside I → ℂ) :
      x ∈ MvPolynomial.zeroLocus ℂ S ↔
        ∃ z : Fin m → ℂ, x = chartVariables I ((polynomialGraph hd i).map (MvPolynomial.aeval z)) := by
    let A : Matrix (Outside I) (Inside I) ℂ := Matrix.of fun r c ↦ x (r, c)
    have hA : chartVariables I A = x := by funext rc; cases rc; rfl
    rw [← hA, chartVariables_mem_zeroLocus I D A,
      ← stablePlane_chart_iff (windowBasis 2 b m) (windowDimension_le d) (windowOperator 2 b m),
      stableGraph_iff hd i]
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z, congrArg (chartVariables I) hz⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, Matrix.ext fun r c ↦ congrFun hz (r, c)⟩
  change RingHom.ker _ = S.radical
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ)]
  ext p
  rw [RingHom.mem_ker, MvPolynomial.mem_vanishingIdeal_iff]
  constructor
  · intro hp x hx
    obtain ⟨z, rfl⟩ := (hzero x).1 hx
    change graphRingHom hd i p = 0 at hp
    rw [← aeval_graph, AlgHom.comp_apply, hp, map_zero]
  · intro hp
    change graphRingHom hd i p = 0
    apply MvPolynomial.funext
    intro z
    have hz := hp _ ((hzero _).2 ⟨z, rfl⟩)
    rw [← aeval_graph, AlgHom.comp_apply] at hz
    simpa only [map_zero, MvPolynomial.aeval_eq_eval] using hz

set_option backward.isDefEq.respectTransparency false in
private theorem stableChart_exists (hm : 0 < m) (i : Fin 2) :
    ∃ f : Affine m ⟶ windowStableScheme 2 b m d,
      IsOpenImmersion f.left ∧
      Set.range f.left = (stablePivotOpen hd i : Set _) ∧
      f ≫ stableInclusion d = polynomialGraphMap hd i ≫ jetPivotChart hd i := by
  let basis := windowBasis 2 b m
  let T := windowOperator 2 b m
  let I := jetPivot hd i
  let p := (jetPivotChart hd i).left
  let j := (stableInclusion d).left
  let R := reducedStabilityIdeal I (operatorInCoordinates basis T)
  let q : Spec (CommRingCat.of (chartAlgebra (k := ℂ) I ⧸ R)) ⟶
      (chartScheme (k := ℂ) I).left :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk R))
  have : IsOpenImmersion p :=
    (grassmannianCharts basis (windowDimension_le d)).openChart I
  obtain ⟨a, ha⟩ := LatticeModels.stableAffinePresentation basis (windowDimension_le d) T I
  change pullback p j ≅ Spec (CommRingCat.of (chartAlgebra (k := ℂ) I ⧸ R)) at a
  change a.hom ≫ q = pullback.fst p j at ha
  let g := graphRingHom hd i
  let e : (chartAlgebra (k := ℂ) I ⧸ R) ≃+* AffineCoordinateRing m :=
    (Ideal.quotEquivOfEq (graphRingHom_ker hd i).symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (graphRingHom_surjective hd hm i)).toRingEquiv
  let E : (Affine m).left ≅ Spec (CommRingCat.of (chartAlgebra (k := ℂ) I ⧸ R)) :=
    Scheme.Spec.mapIso e.toCommRingCatIso.op
  have hE : E.hom ≫ q = (polynomialGraphMap hd i).left := by
    change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk R)) =
      Spec.map (CommRingCat.ofHom g.toRingHom)
    rw [← Spec.map_comp]
    congr 1
  let B := E ≪≫ a.symm
  let f' : (Affine m).left ⟶ (windowStableScheme 2 b m d).left := B.hom ≫ pullback.snd p j
  have hfac : f' ≫ j = (polynomialGraphMap hd i).left ≫ p := by
    calc
      f' ≫ j = E.hom ≫ a.inv ≫ pullback.fst p j ≫ p := by
        simp only [f', B, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullback.condition]
      _ = _ := by
        rw [← ha]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        rw [← Category.assoc, hE]
  let f : Affine m ⟶ windowStableScheme 2 b m d :=
    Over.homMk f' (by
      rw [← Over.w (stableInclusion d), ← Category.assoc, hfac, Category.assoc,
        Over.w (jetPivotChart hd i), Over.w (polynomialGraphMap hd i)])
  refine ⟨f, ?_, ?_, Over.OverMorphism.ext hfac⟩
  · change IsOpenImmersion (B.hom ≫ pullback.snd p j)
    infer_instance
  · change Set.range (pullback.snd p j ∘ B.hom) = _
    have hB : Function.Surjective B.hom := B.hom.homeomorph.surjective
    rw [Set.range_comp, hB.range_eq, Set.image_univ]
    exact IsOpenImmersion.range_pullbackSnd p j

private structure JetCharts where
  chart : Fin 2 → (Affine m ⟶ normalizedJetScheme hd)
  isOpen : ∀ i, IsOpenImmersion (chart i).left
  range_eq : ∀ i,
    Set.range ((chart i ≫ normalizedJetInclusion hd).left) = (stablePivotOpen hd i : Set _)
  graph_eq : ∀ i,
    chart i ≫ normalizedJetInclusion hd ≫ stableInclusion d =
      polynomialGraphMap hd i ≫ jetPivotChart hd i

set_option backward.isDefEq.respectTransparency false in
private def jetCharts (hm : 0 < m) : JetCharts hd := by
  let f i := (stableChart_exists hd hm i).choose
  have ho i : IsOpenImmersion (f i).left := (stableChart_exists hd hm i).choose_spec.1
  have hr i : Set.range (f i).left = (stablePivotOpen hd i : Set _) :=
    (stableChart_exists hd hm i).choose_spec.2.1
  have hg i : f i ≫ stableInclusion d = polynomialGraphMap hd i ≫ jetPivotChart hd i :=
    (stableChart_exists hd hm i).choose_spec.2.2
  let j := normalizedJetInclusion hd
  have hj : IsOpenImmersion j.left := by
    change IsOpenImmersion (normalizedJetOpen hd).ι
    infer_instance
  have hsub i : Set.range (f i).left ⊆ Set.range j.left := by
    rw [hr]
    change _ ⊆ Set.range (normalizedJetOpen hd).ι
    rw [Scheme.Opens.range_ι]
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  let g i : Affine m ⟶ normalizedJetScheme hd :=
    Over.homMk (IsOpenImmersion.lift j.left (f i).left (hsub i)) (by
      rw [← Over.w j, IsOpenImmersion.lift_fac_assoc, Over.w])
  have hfac i : g i ≫ j = f i := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
  refine ⟨g, ?_, fun i ↦ by rw [hfac]; exact hr i, fun i ↦ by rw [← Category.assoc, hfac]; exact hg i⟩
  intro i
  have : IsOpenImmersion ((g i).left ≫ j.left) := by
    rw [← Over.comp_left, hfac]
    exact ho i
  exact IsOpenImmersion.of_comp (g i).left j.left

private theorem chartsCover (C : JetCharts hd) (p : (normalizedJetScheme hd).left) :
    ∃ i, p ∈ Set.range (C.chart i).left := by
  let j := normalizedJetInclusion hd
  have hj : IsOpenImmersion j.left := by
    change IsOpenImmersion (normalizedJetOpen hd).ι
    infer_instance
  have hp : j.left p ∈ (normalizedJetOpen hd : Set (windowStableScheme 2 b m d).left) := by
    exact p.property
  have h := show j.left p ∈ (stablePivotOpen hd 0 : Set _) ∪ (stablePivotOpen hd 1 : Set _) from hp
  obtain ⟨i, hi⟩ : ∃ i, j.left p ∈ (stablePivotOpen hd i : Set _) := h.elim
    (fun h₀ ↦ ⟨0, h₀⟩) (fun h₁ ↦ ⟨1, h₁⟩)
  rw [← C.range_eq i] at hi
  obtain ⟨x, hx⟩ := hi
  exact ⟨i, x, j.left.isOpenEmbedding.injective hx⟩

private theorem matrix_affinePoint_graphMap (i : Fin 2) (z : Fin m → ℂ) :
    affinePoint z ≫ polynomialGraphMap hd i =
      (chartMatrixEquiv (jetPivot hd i) complexAlgebra).symm
        ((polynomialGraph hd i).map (MvPolynomial.aeval z)) := by
  change (testSpec ℂ).map (CommAlgCat.ofHom (MvPolynomial.aeval z)).op ≫
      (testSpec ℂ).map (CommAlgCat.ofHom (graphRingHom hd i)).op =
    (testSpec ℂ).map (CommAlgCat.ofHom
      (MvPolynomial.aeval (chartVariables (jetPivot hd i)
        ((polynomialGraph hd i).map (MvPolynomial.aeval z))))).op
  rw [← Functor.map_comp, ← op_comp]
  congr 2
  apply CommAlgCat.hom_ext
  exact aeval_graph hd i z

private theorem chartKernel (C : JetCharts hd) (i : Fin 2) (z : Fin m → ℂ) (x : Window 2 b m) :
    x ∈ normalizedJetSubspace (affinePoint z ≫ C.chart i) ↔
      windowJets 2 b m x i + (jetCoefficients m).symm z * windowJets 2 b m x i.rev = 0 := by
  unfold normalizedJetSubspace
  rw [Category.assoc, C.graph_eq i, ← Category.assoc, matrix_affinePoint_graphMap]
  change (x ∈ grassmannianSubspace (windowBasis 2 b m) (windowDimension_le d)
    (grassmannianChartPoint (windowBasis 2 b m) (windowDimension_le d) (jetPivot hd i)
      ((polynomialGraph hd i).map (MvPolynomial.aeval z)))) ↔ _
  rw [graphPlane_mem, graphAction_polynomial]
  let a : JetRing m := windowJets 2 b m x i
  let u : JetRing m := (jetCoefficients m).symm z
  let v : JetRing m := windowJets 2 b m x i.rev
  change a = (-u) * v ↔ a + u * v = 0
  calc
    (a = (-u) * v) ↔ a = -(u * v) := (congrArg (fun k : JetRing m ↦ a = k) (neg_mul u v)).to_iff
    _ ↔ a + u * v = 0 := eq_neg_iff_add_eq_zero

private theorem recoverCoefficients (hm : 0 < m) (i : Fin 2) (z : Fin m → ℂ) :
    zerothColumnCoefficients hd hm i ((polynomialGraph hd i).map (MvPolynomial.aeval z)) = z := by
  funext r
  change -MvPolynomial.aeval z
    (polynomialGraph hd i (outsideCoefficients hd i r) (pivotCoefficients hd i ⟨0, hm⟩)) = _
  simp [polynomialGraph_firstColumn]

private theorem normalizedJetSubspace_injective :
    Function.Injective (normalizedJetSubspace (hd := hd)) := by
  have : IsOpenImmersion (normalizedJetInclusion hd).left := by
    change IsOpenImmersion (normalizedJetOpen hd).ι
    infer_instance
  have : IsClosedImmersion (stableInclusion d).left := by
    change IsClosedImmersion (reducedClosureIdeal (WindowGrassmannian d)
      {p | StablePlane (windowBasis 2 b m) (windowDimension_le d) (windowOperator 2 b m) p}).subschemeι
    infer_instance
  have : Mono (normalizedJetInclusion hd) := Over.mono_of_mono_left _
  have : Mono (stableInclusion d) := Over.mono_of_mono_left _
  intro p q h
  apply (cancel_mono (normalizedJetInclusion hd ≫ stableInclusion d)).1
  exact grassmannianSubspace_injective _ _ h

set_option backward.isDefEq.respectTransparency false in
private theorem inversionOnPoints (C : JetCharts hd) (i : Fin 2) (z w : Fin m → ℂ) :
    affinePoint z ≫ C.chart i = affinePoint w ≫ C.chart i.rev ↔
    ∃ v : (JetRing m)ˣ, (jetCoefficients m).symm z = v.val ∧
      (jetCoefficients m).symm w = (v⁻¹).val := by
  let a := (jetCoefficients m).symm z
  let c := (jetCoefficients m).symm w
  have hrow (x : Window 2 b m) :
      x ∈ normalizedJetSubspace (affinePoint w ≫ C.chart i.rev) ↔
        windowJets 2 b m x i.rev + c * windowJets 2 b m x i = 0 := by
    rw [chartKernel hd C, Fin.rev_rev]
  constructor
  · intro h
    let xs : Fin 2 → JetRing m := fun j ↦ if j = i then -a else 1
    let x := (windowJets 2 b m).symm xs
    have he : windowJets 2 b m x = xs := (windowJets 2 b m).apply_symm_apply _
    have hx : x ∈ normalizedJetSubspace (affinePoint z ≫ C.chart i) := by
      rw [chartKernel hd C, he]
      simp [xs, a, rev_ne i]
    have hh := (hrow x).1 (h ▸ hx)
    have ha : a * c = 1 := by
      have h' : (1 : JetRing m) + c * (-a) = 0 := by simpa [he, xs, rev_ne i] using hh
      have k : 1 - a * c = 0 := by
        calc
          1 - a * c = 1 + c * (-a) := by ring
          _ = 0 := h'
      exact (sub_eq_zero.mp k).symm
    exact ⟨Units.mkOfMulEqOne a c ha, rfl, rfl⟩
  · rintro ⟨v, ha, hc⟩
    apply normalizedJetSubspace_injective hd
    ext x
    rw [chartKernel hd C, hrow x]
    change windowJets 2 b m x i + a * windowJets 2 b m x i.rev = 0 ↔ _
    have hmul : a * c = 1 := by change a = v.val at ha; change c = (v⁻¹).val at hc; rw [ha, hc]; simp
    have hmul' : c * a = 1 := by simpa only [mul_comm] using hmul
    constructor
    · intro hx
      have hx' := congrArg (fun k : JetRing m ↦ c * k) hx
      simpa only [mul_add, ← mul_assoc, hmul', one_mul, mul_zero, add_comm] using hx'
    · intro hx
      have hx' := congrArg (fun k : JetRing m ↦ a * k) hx
      simpa only [mul_add, ← mul_assoc, hmul, one_mul, mul_zero, add_comm] using hx'

private def lineVariable (i : Fin 2) : Outside (linePivot i) × Inside (linePivot i) :=
  (⟨i.rev, by simp [linePivot, rev_ne i]⟩, ⟨i, by simp [linePivot]⟩)

private theorem lineVariable_eq (i : Fin 2) (rc : Outside (linePivot i) × Inside (linePivot i)) :
    rc = lineVariable i := by
  apply Prod.ext <;> apply Subtype.ext
  · have h := rc.1.property
    simp only [linePivot, Finset.mem_singleton] at h
    exact (eq_or_eq_rev rc.1.val i).resolve_left h
  · exact Finset.mem_singleton.mp rc.2.property

private def lineVariablesEquiv (i : Fin 2) : Outside (linePivot i) × Inside (linePivot i) ≃ Fin 1 where
  toFun _ := 0
  invFun _ := lineVariable i
  left_inv rc := (lineVariable_eq i rc).symm
  right_inv _ := Subsingleton.elim _ _

private abbrev lineRingEquiv (i : Fin 2) := MvPolynomial.renameEquiv ℂ (lineVariablesEquiv i)

private theorem lineRingEquiv_eq (i : Fin 2) :
    (lineRingEquiv i).toAlgHom = MvPolynomial.aeval (R := ℂ)
      (fun _ : Outside (linePivot i) × Inside (linePivot i) ↦
        (MvPolynomial.X 0 : AffineCoordinateRing 1)) := by
  apply MvPolynomial.algHom_ext
  intro rc
  simp [lineVariablesEquiv]

private theorem lineChart_left (i : Fin 2) :
    (lineChart i).left = Spec.map (CommRingCat.ofHom (lineRingEquiv i).toAlgHom.toRingHom) ≫
      ((grassmannianCharts (Pi.basisFun ℂ (Fin 2)) projectiveLineDimension).chart (linePivot i)).left := by
  rw [lineRingEquiv_eq]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem lineChart_open (i : Fin 2) : IsOpenImmersion (lineChart i).left := by
  let b := Pi.basisFun ℂ (Fin 2)
  let G := grassmannianCharts b projectiveLineDimension
  let e := lineRingEquiv i
  let f := CommRingCat.ofHom e.toAlgHom.toRingHom
  have h : IsIso f := e.toRingEquiv.toCommRingCatIso.isIso_hom
  have ho : IsOpenImmersion (G.chart (linePivot i)).left := G.openChart _
  have hf : IsIso (Spec.map f) := by
    change IsIso (Scheme.Spec.map f.op)
    infer_instance
  rw [lineChart_left]
  change IsOpenImmersion (Spec.map f ≫ (G.chart (linePivot i)).left)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem lineChart_cover (p : ProjectiveLine.left) :
    ∃ i, p ∈ Set.range (lineChart i).left := by
  let b := Pi.basisFun ℂ (Fin 2)
  let G := grassmannianCharts b projectiveLineDimension
  obtain ⟨I, q, rfl⟩ := G.cover p
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp I.property
  have hI : I = linePivot i := Subtype.ext hi
  subst I
  let e := lineRingEquiv i
  let f := CommRingCat.ofHom e.toAlgHom.toRingHom
  have h : IsIso f := e.toRingEquiv.toCommRingCatIso.isIso_hom
  have hf : IsIso (Spec.map f) := by
    change IsIso (Scheme.Spec.map f.op)
    infer_instance
  have hsurj : Function.Surjective (Spec.map f) := (Spec.map f).homeomorph.surjective
  obtain ⟨q', hq'⟩ := hsurj q
  refine ⟨i, q', ?_⟩
  rw [lineChart_left, Scheme.Hom.comp_apply]
  exact congrArg (fun v ↦ (G.chart (linePivot i)).left v) hq'

private theorem lineChart_point (i : Fin 2) (x : Fin 1 → ℂ) :
    grassmannianSubspace (Pi.basisFun ℂ (Fin 2)) projectiveLineDimension
      (affinePoint x ≫ lineChart i) = normalizedLine i (x 0) := by
  let I := linePivot i
  let G := grassmannianCharts (Pi.basisFun ℂ (Fin 2)) projectiveLineDimension
  let A : Matrix (Outside I) (Inside I) ℂ := Matrix.of fun _ _ ↦ x 0
  have hp : affinePoint x ≫ lineChart i =
      grassmannianChartPoint (Pi.basisFun ℂ (Fin 2)) projectiveLineDimension I A := by
    change (testSpec ℂ).map (CommAlgCat.ofHom (MvPolynomial.aeval x)).op ≫
        (testSpec ℂ).map (CommAlgCat.ofHom (MvPolynomial.aeval (R := ℂ)
          (fun _ : Outside I × Inside I ↦ (MvPolynomial.X 0 : AffineCoordinateRing 1)))).op ≫
        G.chart I =
      (testSpec ℂ).map (CommAlgCat.ofHom (MvPolynomial.aeval (chartVariables I A))).op ≫ G.chart I
    rw [← Category.assoc, ← Functor.map_comp, ← op_comp]
    congr 3
    apply CommAlgCat.hom_ext
    apply MvPolynomial.algHom_ext
    intro rc
    simp [chartVariables, A]
  rw [hp]
  have hG := grassmannianChartSubspace (Pi.basisFun ℂ (Fin 2)) projectiveLineDimension I A
  have hE : (Pi.basisFun ℂ (Fin 2)).equivFun = LinearEquiv.refl ℂ (Fin 2 → ℂ) := by
    ext v j
    simp
  rw [hE] at hG
  change (grassmannianSubspace _ _ _).map LinearMap.id = _ at hG
  rw [Submodule.map_id] at hG
  rw [hG, normalizedLine]
  ext v
  rw [LinearMap.mem_range, Submodule.mem_span_singleton]
  have h (u : Inside I → ℂ) :
      Matrix.toLin' (graphMatrix I A) u =
        u (lineVariable i).2 • (fun j : Fin 2 ↦ if j = i then (1 : ℂ) else x 0) := by
    funext j
    by_cases hj : j = i
    · subst j
      have hg := graphMatrix_inside I A u (lineVariable i).2
      change (graphMatrix I A *ᵥ u) i = _ at hg
      rw [Matrix.toLin'_apply, hg]
      simp
    · have hji : j = i.rev := (eq_or_eq_rev j i).resolve_left hj
      subst j
      have hg := graphMatrix_outside I A u (lineVariable i).1
      change (graphMatrix I A *ᵥ u) i.rev = _ at hg
      rw [Matrix.toLin'_apply, hg]
      let : Unique (Inside I) := ⟨⟨(lineVariable i).2⟩, fun c ↦
        Subtype.ext (Finset.mem_singleton.mp c.property)⟩
      simp [Matrix.mulVec, dotProduct, Finset.univ_unique, A, rev_ne i, mul_comm,
        show (default : Inside I) = (lineVariable i).2 from rfl]
  exact ⟨fun ⟨u, hu⟩ ↦ ⟨u (lineVariable i).2, (h u).symm.trans hu⟩,
    fun ⟨z, hz⟩ ↦ ⟨fun _ ↦ z, (h _).trans hz⟩⟩

private def jetOpenCover (C : JetCharts hd) : (normalizedJetScheme hd).left.OpenCover :=
  Scheme.Cover.mkOfCovers (Fin 2) (fun _ : Fin 2 ↦ (Affine m).left)
    (fun i ↦ (C.chart i).left) (chartsCover hd C)
    (fun i ↦ C.isOpen i)

private theorem affineSmooth (n : ℕ) : SmoothOfRelativeDimension n (Affine n).hom := by
  change SmoothOfRelativeDimension n
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ (AffineCoordinateRing n))))
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  change (algebraMap ℂ (AffineCoordinateRing n)).IsStandardSmoothOfRelativeDimension n
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  infer_instance

private theorem jetSmooth (C : JetCharts hd) :
    SmoothOfRelativeDimension m (normalizedJetScheme hd).hom := by
  let cover := jetOpenCover hd C
  have : ∀ i, IsAffine (cover.X i) := fun _ ↦ inferInstanceAs (IsAffine (Spec (CommRingCat.of (AffineCoordinateRing m))))
  refine HasRingHomProperty.of_source_openCover (P := @SmoothOfRelativeDimension m) cover ?_
  intro i
  have h : cover.f i ≫ (normalizedJetScheme hd).hom = (Affine m).hom := Over.w (C.chart i)
  rw [h]
  exact HasRingHomProperty.appTop (@SmoothOfRelativeDimension m) _ (affineSmooth m)

private theorem affineFiniteType (n : ℕ) : LocallyOfFiniteType (Affine n).hom := by
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℂ (AffineCoordinateRing n))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact (RingHom.finiteType_algebraMap).2 inferInstance

private theorem point_factors_iff {X Y : SchemeOver ℂ} (f : X ⟶ Y) [IsOpenImmersion f.left]
    (p : Points Y complexAlgebra) :
    pointLocation p ∈ Set.range f.left ↔ ∃ q : Points X complexAlgebra, q ≫ f = p := by
  constructor
  · intro h
    have hp : Set.range p.left ⊆ Set.range f.left := by
      rw [pointLocation_range]
      exact Set.singleton_subset_iff.mpr h
    refine ⟨Over.homMk (IsOpenImmersion.lift f.left p.left hp) ?_, ?_⟩
    · rw [← Over.w f, IsOpenImmersion.lift_fac_assoc, Over.w]
    · exact Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
  · rintro ⟨q, rfl⟩
    exact ⟨pointLocation q, rfl⟩

private theorem evalPoint {A : Type} [CommRing A] [Algebra ℂ A]
    (q : Points ((testSpec ℂ).obj (op (CommAlgCat.of ℂ A))) complexAlgebra) :
    ∃ f : A →ₐ[ℂ] ℂ, q = (testSpec ℂ).map (CommAlgCat.ofHom f).op := by
  obtain ⟨f, rfl⟩ := (algSpec.fullyFaithful (R := CommRingCat.of ℂ)).map_surjective q
  exact ⟨f.unop.hom, rfl⟩

private theorem affinePoint_surjective (n : ℕ) :
    Function.Surjective (affinePoint (n := n)) := by
  intro q
  obtain ⟨f, rfl⟩ := evalPoint q
  use fun j ↦ f (MvPolynomial.X j)
  unfold affinePoint
  congr 2
  apply CommAlgCat.hom_ext
  apply MvPolynomial.algHom_ext
  intro j
  exact MvPolynomial.aeval_X _ _

private theorem complexPoint_at_closed (X : SchemeOver ℂ) [LocallyOfFiniteType X.hom]
    (x : X.left) (hx : IsClosed ({x} : Set X.left)) :
    ∃ q : Points X complexAlgebra, pointLocation q = x := by
  let q := pointOfClosedPoint X.hom x hx
  have hq : q ≫ X.hom = ((testSpec ℂ).obj (op complexAlgebra)).hom := by
    change q ≫ X.hom = Spec.map (𝟙 (CommRingCat.of ℂ))
    rw [Spec.map_id]
    exact pointOfClosedPoint_comp _ _ _
  exact ⟨Over.homMk q hq, pointOfClosedPoint_apply X.hom x hx _⟩

private theorem opens_eq_of_complexPoints (X : SchemeOver ℂ) [LocallyOfFiniteType X.hom]
    {U V : X.left.Opens} (h : ∀ q : Points X complexAlgebra,
      pointLocation q ∈ U ↔ pointLocation q ∈ V) : U = V := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have aux (A B : X.left.Opens) (hAB : ∀ q : Points X complexAlgebra,
      pointLocation q ∈ A → pointLocation q ∈ B) : A ≤ B := by
    intro x hx
    by_contra hx'
    have hne : ((A : Set X.left) ∩ (B : Set X.left)ᶜ).Nonempty := ⟨x, hx, hx'⟩
    have hlc : IsLocallyClosed ((A : Set X.left) ∩ (B : Set X.left)ᶜ) :=
      ⟨A, (B : Set X.left)ᶜ, A.isOpen, B.isOpen.isClosed_compl, rfl⟩
    obtain ⟨y, hy, hy'⟩ := nonempty_inter_closedPoints hne hlc
    obtain ⟨q, rfl⟩ := complexPoint_at_closed X y hy'
    exact hy.2 (hAB q hy.1)
  exact le_antisymm (aux U V fun q ↦ (h q).1) (aux V U fun q ↦ (h q).2)

private theorem overlapOpen (hm : 0 < m) : IsOpenImmersion (overlapInclusion hm).left := by
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (algebraMap (AffineCoordinateRing m) (OverlapRing hm))))
  exact IsOpenImmersion.of_isLocalization (headVariable hm)

private theorem overlapRange (hm : 0 < m) :
    letI : IsOpenImmersion (overlapInclusion hm).left := overlapOpen hm
    (overlapInclusion hm).left.opensRange = PrimeSpectrum.basicOpen (headVariable hm) := by
  let := overlapOpen hm
  exact Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of (AffineCoordinateRing m))
    (headVariable hm)

private theorem affinePoint_mem_overlap (hm : 0 < m) (z : Fin m → ℂ) :
    pointLocation (affinePoint z) ∈ Set.range (overlapInclusion hm).left ↔ z ⟨0, hm⟩ ≠ 0 := by
  have := overlapOpen hm
  change pointLocation (affinePoint z) ∈ (overlapInclusion hm).left.opensRange ↔ _
  rw [overlapRange]
  change headVariable hm ∉
    (PrimeSpectrum.comap (MvPolynomial.aeval z).toRingHom (default : PrimeSpectrum ℂ)).asIdeal ↔ _
  rw [show (default : PrimeSpectrum ℂ) = ⊥ from Subsingleton.elim _ _]
  change (MvPolynomial.aeval z) (headVariable hm) ∉ (⊥ : Ideal ℂ) ↔ _
  simp [headVariable]

private def jetHead {m : ℕ} (hm : 0 < m) : JetRing m →+* ℂ :=
  Ideal.Quotient.lift (jetIdeal m) PowerSeries.constantCoeff (by
    change jetIdeal m ≤ RingHom.ker PowerSeries.constantCoeff
    rw [jetIdeal, Ideal.span_le]
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    subst f
    simp [Nat.ne_of_gt hm])

private theorem jetHead_apply {m : ℕ} (hm : 0 < m) (u : JetRing m) :
    jetHead hm u = jetCoefficients m u ⟨0, hm⟩ := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective u
  exact (PowerSeries.coeff_zero_eq_constantCoeff_apply f).symm

private theorem jetUnit_iff {m : ℕ} (hm : 0 < m) (u : JetRing m) :
    IsUnit u ↔ jetCoefficients m u ⟨0, hm⟩ ≠ 0 := by
  rw [← jetHead_apply]
  constructor
  · exact fun hu ↦ (hu.map (jetHead hm)).ne_zero
  · obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective u
    intro hf
    have hu : IsUnit f := PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hf)
    exact hu.map (jetReduction m).toMonoidHom

/-- The Jacobson property of affine space promotes the unit condition on complex
points to an equality of scheme opens. -/
private theorem chartOverlapRange (hm : 0 < m) (C : JetCharts hd) (i : Fin 2) :
    letI : IsOpenImmersion (C.chart i.rev).left := C.isOpen i.rev
    letI : IsOpenImmersion (overlapInclusion hm).left := overlapOpen hm
    (C.chart i).left ⁻¹ᵁ (C.chart i.rev).left.opensRange = (overlapInclusion hm).left.opensRange := by
  have := affineFiniteType m
  have := C.isOpen i.rev
  have := overlapOpen hm
  apply opens_eq_of_complexPoints
  intro p
  obtain ⟨z, rfl⟩ := affinePoint_surjective m p
  change pointLocation (affinePoint z ≫ C.chart i) ∈ Set.range (C.chart i.rev).left ↔
    pointLocation (affinePoint z) ∈ Set.range (overlapInclusion hm).left
  rw [point_factors_iff, affinePoint_mem_overlap]
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨w, rfl⟩ := affinePoint_surjective m q
    obtain ⟨v, hv, _⟩ := (inversionOnPoints hd C i z w).1 hq.symm
    have hunit : IsUnit ((jetCoefficients m).symm z) := hv ▸ v.isUnit
    simpa only [LinearEquiv.apply_symm_apply] using (jetUnit_iff hm _).1 hunit
  · intro hz
    have hu : IsUnit ((jetCoefficients m).symm z) :=
      (jetUnit_iff hm _).2 (by simpa using hz)
    obtain ⟨v, hv⟩ := hu
    refine ⟨affinePoint (jetCoefficients m (v⁻¹).val), ?_⟩
    symm
    exact (inversionOnPoints hd C i z _).2 ⟨v, hv.symm, (jetCoefficients m).symm_apply_apply _⟩

private def polynomialJet {A : Type} [CommRing A] (f : A →+* ℂ) (m : ℕ) :
    Polynomial A →+* JetRing m :=
  (jetReduction m).toRingHom.comp
    (Polynomial.coeToPowerSeries.ringHom.comp (Polynomial.mapRingHom f))

private theorem polynomialJet_coeff {A : Type} [CommRing A] (f : A →+* ℂ)
    (P : Polynomial A) (k : Fin m) :
    jetCoefficients m (polynomialJet f m P) k = f (P.coeff k.val) := by
  change jetCoefficients m (jetReduction m (P.map f : Polynomial ℂ)) k = _
  rw [jetCoefficients_reduce, Polynomial.coeff_coe, Polynomial.coeff_map]

private theorem polynomialJet_X_pow {A : Type} [CommRing A] (f : A →+* ℂ) :
    (polynomialJet f m) (Polynomial.X ^ m) = 0 := by
  have hX : (polynomialJet f m) Polynomial.X = jetReduction m t := by
    change jetReduction m ((Polynomial.X.map f : Polynomial ℂ) : O) = jetReduction m t
    rw [Polynomial.map_X, Polynomial.coe_X]
  rw [map_pow, hX, ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

private theorem positivePolynomial_coeff {A : Type} [CommRing A] (a : Fin m → A) (k : Fin m) :
    (∑ j ∈ (Finset.univ : Finset (Fin m)).filter (fun j ↦ j.val ≠ 0),
      Polynomial.monomial j.val (a j)).coeff k.val = if k.val = 0 then 0 else a k := by
  rw [Polynomial.finsetSum_coeff]
  by_cases hk : k.val = 0
  · rw [ite_eq_left hk, Finset.sum_eq_zero]
    intro j hj
    have h := (Finset.mem_filter.mp hj).2
    simp [Polynomial.coeff_monomial, hk, h]
  · rw [ite_eq_right hk, Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      simp [Polynomial.coeff_monomial, show j.val ≠ k.val from fun h ↦ hj (Fin.ext h)]
    · simp [hk]

private theorem inverseJetPolynomial_eval (hm : 0 < m) (f : OverlapRing hm →ₐ[ℂ] ℂ) :
    let a := fun k : Fin m ↦ algebraMap (AffineCoordinateRing m) (OverlapRing hm) (MvPolynomial.X k)
    let z := fun k ↦ f (a k)
    let w := fun k : Fin m ↦ f ((inverseJetPolynomial hm).coeff k.val)
    (jetCoefficients m).symm z * (jetCoefficients m).symm w = 1 := by
  let k₀ : Fin m := ⟨0, hm⟩
  let a := fun k : Fin m ↦ algebraMap (AffineCoordinateRing m) (OverlapRing hm) (MvPolynomial.X k)
  let p := ∑ k ∈ (Finset.univ : Finset (Fin m)).filter (fun k ↦ k.val ≠ 0),
    Polynomial.monomial k.val (a k)
  let u : OverlapRing hm := IsLocalization.Away.invSelf (headVariable hm)
  let P := Polynomial.C (a k₀) + p
  let Q := inverseJetPolynomial hm
  let e := polynomialJet f.toRingHom m
  have hP : e P = (jetCoefficients m).symm (fun k ↦ f (a k)) := by
    apply (jetCoefficients m).injective
    funext k
    rw [LinearEquiv.apply_symm_apply]
    change jetCoefficients m (polynomialJet f.toRingHom m P) k = f (a k)
    rw [polynomialJet_coeff, show P.coeff k.val = (Polynomial.C (a k₀)).coeff k.val + p.coeff k.val from
        Polynomial.coeff_add _ _ _, Polynomial.coeff_C, positivePolynomial_coeff]
    by_cases hk : k.val = 0
    · have : k = k₀ := Fin.ext hk
      subst k
      simp [k₀]
    · simp [hk]
  have hQ : e Q = (jetCoefficients m).symm (fun k : Fin m ↦ f (Q.coeff k.val)) := by
    apply (jetCoefficients m).injective
    funext k
    rw [LinearEquiv.apply_symm_apply]
    exact polynomialJet_coeff f.toRingHom Q k
  have hp₀ : p.coeff 0 = 0 := by
    change p.coeff k₀.val = 0
    rw [positivePolynomial_coeff]
    rfl
  have hn : (e p) ^ m = 0 := by
    obtain ⟨g, hg⟩ := Polynomial.X_dvd_iff.mpr hp₀
    rw [← map_pow, hg, mul_pow, map_mul, polynomialJet_X_pow, zero_mul]
  have hu : e (Polynomial.C (a k₀)) * e (Polynomial.C u) = 1 := by
    rw [← map_mul, ← map_mul, show a k₀ * u = 1 from
      IsLocalization.Away.mul_invSelf (S := OverlapRing hm) (headVariable hm), map_one, map_one]
  let y := -(e (Polynomial.C u) * e p)
  have hy : y ^ m = 0 := by
    change (-(e (Polynomial.C u) * e p)) ^ m = 0
    calc
      (-(e (Polynomial.C u) * e p)) ^ m = ((-1 : JetRing m) * e (Polynomial.C u) * e p) ^ m := by
        congr 1
        ring
      _ = 0 := by rw [mul_pow, hn, mul_zero]
  have hQ' : e Q = e (Polynomial.C u) * ∑ k ∈ Finset.range m, y ^ k := by
    change e (Polynomial.C u * ∑ k ∈ Finset.range m, (-(Polynomial.C u * p)) ^ k) = _
    simp only [map_mul, map_sum, map_pow, map_neg, y]
  have hPu : e P * e (Polynomial.C u) = 1 - y := by
    change e (Polynomial.C (a k₀) + p) * e (Polynomial.C u) = 1 - y
    rw [map_add, add_mul, hu]
    dsimp [y]
    ring
  change (jetCoefficients m).symm (fun k ↦ f (a k)) *
    (jetCoefficients m).symm (fun k : Fin m ↦ f (Q.coeff k.val)) = 1
  rw [← hP, ← hQ, hQ', ← mul_assoc, hPu]
  have hg := geom_sum_mul y m
  rw [hy] at hg
  linear_combination -hg

set_option maxHeartbeats 600000 in
private theorem overlapPoints (hm : 0 < m) (q : Points (Overlap hm) complexAlgebra) :
    ∃ (z w : Fin m → ℂ),
      q ≫ SchubertNormalizedJetGraphSpecs.overlapInclusion hm = affinePoint z ∧
      q ≫ overlapInversion hm = affinePoint w ∧
      (jetCoefficients m).symm z * (jetCoefficients m).symm w = 1 := by
  obtain ⟨f, rfl⟩ := evalPoint q
  let z := fun k : Fin m ↦ f (algebraMap (AffineCoordinateRing m) (OverlapRing hm) (MvPolynomial.X k))
  let w := fun k : Fin m ↦ f ((inverseJetPolynomial hm).coeff k.val)
  refine ⟨z, w, ?_, ?_, inverseJetPolynomial_eval hm f⟩
  · unfold SchubertNormalizedJetGraphSpecs.overlapInclusion affinePoint
    rw [← Functor.map_comp, ← op_comp]
    congr 2
    apply CommAlgCat.hom_ext
    apply MvPolynomial.algHom_ext
    intro k
    change z k = (MvPolynomial.aeval z) (MvPolynomial.X k)
    rw [MvPolynomial.aeval_X]
  · unfold overlapInversion affinePoint
    rw [← Functor.map_comp, ← op_comp]
    congr 2
    apply CommAlgCat.hom_ext
    apply MvPolynomial.algHom_ext
    intro k
    simp [w]

private theorem overlapFiniteType (hm : 0 < m) : LocallyOfFiniteType (Overlap hm).hom := by
  have := affineFiniteType m
  have := overlapOpen hm
  rw [← Over.w (overlapInclusion hm)]
  infer_instance

private theorem overlapReduced (hm : 0 < m) : IsReduced (Overlap hm).left := by
  have := overlapOpen hm
  have : IsReduced (Affine m).left := by
    change IsReduced (Spec (CommRingCat.of (AffineCoordinateRing m)))
    infer_instance
  exact isReduced_of_isOpenImmersion (overlapInclusion hm).left

private def liftOver {X Y U : SchemeOver ℂ} (j : U ⟶ Y) (f : X ⟶ Y)
    [IsOpenImmersion j.left] (h : Set.range f.left ⊆ Set.range j.left) : X ⟶ U :=
  Over.homMk (IsOpenImmersion.lift j.left f.left h) (by
    rw [← Over.w j, IsOpenImmersion.lift_fac_assoc, Over.w])

@[reassoc]
private theorem liftOver_fac {X Y U : SchemeOver ℂ} (j : U ⟶ Y) (f : X ⟶ Y)
    [IsOpenImmersion j.left] (h : Set.range f.left ⊆ Set.range j.left) :
    liftOver j f h ≫ j = f := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)

set_option backward.isDefEq.respectTransparency false in
private theorem affineMap_ext_complex {X : SchemeOver ℂ} {n : ℕ} [IsReduced X.left]
    [LocallyOfFiniteType X.hom] {f g : X ⟶ Affine n}
    (h : ∀ q : Points X complexAlgebra, q ≫ f = q ≫ g) : f = g := by
  have := affineFiniteType n
  have : IsSeparated (Affine n).hom := by
    change IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap ℂ (AffineCoordinateRing n))))
    infer_instance
  have : LocallyOfFiniteType (f.left ≫ (Affine n).hom) := Over.w f ▸ inferInstance
  apply Over.OverMorphism.ext
  refine AlgebraicGeometry.ext_of_apply_eq (Affine n).hom Set.univ
    isOpen_univ.isLocallyClosed dense_univ ?_ ((Over.w f).trans (Over.w g).symm)
  intro x _ hx
  obtain ⟨q, rfl⟩ := complexPoint_at_closed X x hx
  exact congrArg pointLocation (h q)

private theorem overPullback_of_opens {U V X Y : SchemeOver ℂ} (f : U ⟶ X) (g : U ⟶ V)
    (h : X ⟶ Y) (j : V ⟶ Y) [IsOpenImmersion f.left] [IsOpenImmersion j.left]
    (H : f ≫ h = g ≫ j)
    (H' : h.left ⁻¹ᵁ j.left.opensRange = f.left.opensRange) : IsPullback f g h j := by
  apply IsPullback.of_map (Over.forget _) H
  exact (IsOpenImmersion.isPullback g.left f.left j.left h.left
    (congrArg (fun k : U ⟶ Y ↦ k.left) H) H').flip

private theorem inversionPullback (hm : 0 < m) (C : JetCharts hd) (i : Fin 2) :
    IsPullback (SchubertNormalizedJetGraphSpecs.overlapInclusion hm) (overlapInversion hm)
      (C.chart i) (C.chart i.rev) := by
  have := C.isOpen i.rev
  have := overlapOpen hm
  have := overlapReduced hm
  have := overlapFiniteType hm
  let f := SchubertNormalizedJetGraphSpecs.overlapInclusion hm ≫ C.chart i
  have hR : Set.range f.left ⊆ Set.range (C.chart i.rev).left := by
    rintro _ ⟨x, rfl⟩
    change (C.chart i).left ((SchubertNormalizedJetGraphSpecs.overlapInclusion hm).left x) ∈
      (C.chart i.rev).left.opensRange
    have h₁ : (SchubertNormalizedJetGraphSpecs.overlapInclusion hm).left x ∈
        (SchubertNormalizedJetGraphSpecs.overlapInclusion hm).left.opensRange :=
      Set.mem_range_self x
    rw [← chartOverlapRange hd hm C i] at h₁
    exact h₁
  let g := liftOver (C.chart i.rev) f hR
  have hfac : g ≫ C.chart i.rev = f := liftOver_fac _ _ _
  have hg : g = overlapInversion hm := by
    apply affineMap_ext_complex
    intro q
    have : Mono (C.chart i.rev) := Over.mono_of_mono_left _
    apply (cancel_mono (C.chart i.rev)).1
    simp only [Category.assoc, hfac, f]
    obtain ⟨z, w, hz, hw, hzw⟩ := overlapPoints hm q
    rw [← Category.assoc, hz, ← Category.assoc, hw]
    exact (inversionOnPoints hd C i z w).2 ⟨Units.mkOfMulEqOne _ _ hzw, rfl, rfl⟩
  exact overPullback_of_opens _ _ _ _ (hfac.symm.trans (congrArg (fun h ↦ h ≫ C.chart i.rev) hg))
    (chartOverlapRange hd hm C i)

private theorem normalizedLine_eq_iff (i : Fin 2) (x y : ℂ) :
    normalizedLine i x = normalizedLine i.rev y ↔ x * y = 1 := by
  let u : Fin 2 → ℂ := fun j ↦ if j = i then 1 else x
  let v : Fin 2 → ℂ := fun j ↦ if j = i.rev then 1 else y
  change Submodule.span ℂ {u} = Submodule.span ℂ {v} ↔ _
  constructor
  · intro h
    have hu : u ∈ Submodule.span ℂ {v} := h ▸ Submodule.mem_span_singleton_self u
    obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp hu
    have hz' : z = x := by simpa [u, v, rev_ne i] using congrFun hz i.rev
    simpa [u, v, (rev_ne i).symm, hz'] using congrFun hz i
  · intro h
    have hu : x • v = u := by
      funext j
      rcases eq_or_eq_rev j i with hj | hj <;> rw [hj]
      · simp [u, v, (rev_ne i).symm, h]
      · simp [u, v, rev_ne i]
    have hv : y • u = v := by
      funext j
      rcases eq_or_eq_rev j i with hj | hj <;> rw [hj]
      · simp [u, v, (rev_ne i).symm]
      · simpa [u, v, rev_ne i, mul_comm] using h
    exact le_antisymm ((Submodule.span_singleton_le_iff_mem _ _).mpr (Submodule.mem_span_singleton.mpr ⟨x, hu⟩))
      ((Submodule.span_singleton_le_iff_mem _ _).mpr (Submodule.mem_span_singleton.mpr ⟨y, hv⟩))

private theorem affinePoint_head (hm : 0 < m) (z : Fin m → ℂ) :
    affinePoint z ≫ affineHead hm = affinePoint (fun _ : Fin 1 ↦ z ⟨0, hm⟩) := by
  unfold affinePoint affineHead
  rw [← Functor.map_comp, ← op_comp]
  congr 2
  apply CommAlgCat.hom_ext
  apply MvPolynomial.algHom_ext
  intro k
  simp

private theorem lineChart_intersection_iff (i : Fin 2) (x : Fin 1 → ℂ) :
    pointLocation (affinePoint x ≫ lineChart i) ∈ Set.range (lineChart i.rev).left ↔ x 0 ≠ 0 := by
  have := lineChart_open i.rev
  rw [point_factors_iff]
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨y, rfl⟩ := affinePoint_surjective 1 q
    have h := congrArg (grassmannianSubspace (Pi.basisFun ℂ (Fin 2)) projectiveLineDimension) hq.symm
    rw [lineChart_point, lineChart_point, normalizedLine_eq_iff] at h
    exact left_ne_zero_of_mul_eq_one h
  · intro hx
    refine ⟨affinePoint (fun _ : Fin 1 ↦ (x 0)⁻¹), ?_⟩
    apply grassmannianSubspace_injective (Pi.basisFun ℂ (Fin 2)) projectiveLineDimension
    symm
    rw [lineChart_point, lineChart_point, normalizedLine_eq_iff]
    exact mul_inv_cancel₀ hx

private theorem eq_of_points_of_affine_factor {X Y : SchemeOver ℂ} {n : ℕ} [IsReduced X.left]
    [LocallyOfFiniteType X.hom] (f : X ⟶ Y) (g : X ⟶ Affine n)
    (j : Affine n ⟶ Y) [IsOpenImmersion j.left]
    (h : ∀ q : Points X complexAlgebra, q ≫ f = q ≫ g ≫ j) : f = g ≫ j := by
  have hOpen : f.left ⁻¹ᵁ j.left.opensRange = ⊤ := by
    apply opens_eq_of_complexPoints X
    intro q
    constructor
    · intro _
      trivial
    · intro _
      change pointLocation (q ≫ f) ∈ Set.range j.left
      rw [h q]
      exact (point_factors_iff j _).2 ⟨q ≫ g, Category.assoc _ _ _⟩
  have hR : Set.range f.left ⊆ Set.range j.left := by
    rintro _ ⟨x, rfl⟩
    change x ∈ f.left ⁻¹ᵁ j.left.opensRange
    rw [hOpen]
    trivial
  let k := liftOver j f hR
  have hk : k ≫ j = f := liftOver_fac _ _ _
  suffices k = g by rw [← hk, this]
  apply affineMap_ext_complex
  intro q
  have : Mono j := Over.mono_of_mono_left _
  exact (cancel_mono j).1 (by rw [Category.assoc, hk, Category.assoc, h q])

private theorem projection_agrees (hm : 0 < m) (i : Fin 2) :
    SchubertNormalizedJetGraphSpecs.overlapInclusion hm ≫ affineHead hm ≫ lineChart i =
      overlapInversion hm ≫ affineHead hm ≫ lineChart i.rev := by
  have := overlapReduced hm
  have := overlapFiniteType hm
  have := lineChart_open i.rev
  rw [← Category.assoc (overlapInversion hm)]
  refine eq_of_points_of_affine_factor _ _ (lineChart i.rev) ?_
  intro q
  obtain ⟨z, w, hz, hw, hzw⟩ := overlapPoints hm q
  simp only [← Category.assoc, hz, hw, affinePoint_head]
  apply grassmannianSubspace_injective (Pi.basisFun ℂ (Fin 2)) projectiveLineDimension
  rw [lineChart_point, lineChart_point, normalizedLine_eq_iff]
  have h := congrArg (jetHead hm) hzw
  rw [map_mul, map_one, jetHead_apply, jetHead_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
private theorem projection_exists (hm : 0 < m) (C : JetCharts hd) :
    ∃ π : normalizedJetScheme hd ⟶ ProjectiveLine,
      ∀ i, C.chart i ≫ π = affineHead hm ≫ lineChart i := by
  let cover := jetOpenCover hd C
  let φ i := affineHead hm ≫ lineChart i
  have hcompat : ∀ i j, pullback.fst (cover.f i) (cover.f j) ≫ (φ i).left =
      pullback.snd (cover.f i) (cover.f j) ≫ (φ j).left := by
    intro i j
    rcases eq_or_eq_rev j i with hj | hj
    · subst j
      have := C.isOpen i
      have hf : Mono (cover.f i) := inferInstanceAs (Mono (C.chart i).left)
      rw [show pullback.fst (cover.f i) (cover.f i) = pullback.snd (cover.f i) (cover.f i) from
        (cancel_mono (cover.f i)).1 pullback.condition]
    · subst j
      have H := (inversionPullback hd hm C i).map (Over.forget (Spec (CommRingCat.of ℂ)))
      change IsPullback (SchubertNormalizedJetGraphSpecs.overlapInclusion hm).left
        (overlapInversion hm).left (cover.f i) (cover.f i.rev) at H
      rw [← cancel_epi H.isoPullback.hom, ← Category.assoc, ← Category.assoc,
        H.isoPullback_hom_fst, H.isoPullback_hom_snd]
      exact congrArg (fun k : Overlap hm ⟶ ProjectiveLine ↦ k.left) (projection_agrees hm i)
  let π' : (normalizedJetScheme hd).left ⟶ ProjectiveLine.left :=
    cover.glueMorphisms (fun i ↦ (φ i).left) hcompat
  have hπ i : cover.f i ≫ π' = (φ i).left := cover.ι_glueMorphisms _ _ i
  let π : normalizedJetScheme hd ⟶ ProjectiveLine := Over.homMk π' (by
    apply cover.hom_ext
    intro i
    rw [← Category.assoc, hπ i, Over.w (φ i)]
    exact (Over.w (C.chart i)).symm)
  exact ⟨π, fun i ↦ Over.OverMorphism.ext (hπ i)⟩

private theorem lineOverlap_preimage (hm : 0 < m) (i : Fin 2) :
    letI : IsOpenImmersion (lineChart i.rev).left := lineChart_open i.rev
    letI : IsOpenImmersion (SchubertNormalizedJetGraphSpecs.overlapInclusion hm).left := overlapOpen hm
    (affineHead hm ≫ lineChart i).left ⁻¹ᵁ (lineChart i.rev).left.opensRange =
      (SchubertNormalizedJetGraphSpecs.overlapInclusion hm).left.opensRange := by
  have := affineFiniteType m
  have := lineChart_open i.rev
  have := overlapOpen hm
  apply opens_eq_of_complexPoints
  intro p
  obtain ⟨z, rfl⟩ := affinePoint_surjective m p
  change pointLocation (affinePoint z ≫ affineHead hm ≫ lineChart i) ∈ Set.range (lineChart i.rev).left ↔
    pointLocation (affinePoint z) ∈ Set.range (SchubertNormalizedJetGraphSpecs.overlapInclusion hm).left
  rw [← Category.assoc, affinePoint_head, lineChart_intersection_iff, affinePoint_mem_overlap]

private theorem projectionPullback (hm : 0 < m) (C : JetCharts hd)
    (π : normalizedJetScheme hd ⟶ ProjectiveLine)
    (hπ : ∀ i, C.chart i ≫ π = affineHead hm ≫ lineChart i) (i : Fin 2) :
    IsPullback (C.chart i) (affineHead hm) π (lineChart i) := by
  have := C.isOpen i
  have := lineChart_open i
  have := overlapOpen hm
  apply overPullback_of_opens (C.chart i) (affineHead hm) π (lineChart i) (hπ i)
  apply SetLike.coe_injective
  ext x
  obtain ⟨j, y, rfl⟩ := chartsCover hd C x
  rcases eq_or_eq_rev j i with hj | hj
  · subst j
    change (π.left ((C.chart i).left y) ∈ Set.range (lineChart i).left) ↔
      (C.chart i).left y ∈ Set.range (C.chart i).left
    have he : π.left ((C.chart i).left y) = (lineChart i).left ((affineHead hm).left y) :=
      congrArg (fun f : Affine m ⟶ ProjectiveLine ↦ f.left y) (hπ i)
    rw [he]
    exact ⟨fun _ ↦ Set.mem_range_self _, fun _ ↦ Set.mem_range_self _⟩
  · subst j
    have hL := lineOverlap_preimage hm i.rev
    have hC := chartOverlapRange hd hm C i.rev
    rw [Fin.rev_rev] at hL hC
    have he : (C.chart i.rev ≫ π).left = (affineHead hm ≫ lineChart i.rev).left :=
      congrArg (fun f : Affine m ⟶ ProjectiveLine ↦ f.left) (hπ i.rev)
    change (y ∈ (C.chart i.rev ≫ π).left ⁻¹ᵁ (lineChart i).left.opensRange) ↔
      y ∈ (C.chart i.rev).left ⁻¹ᵁ (C.chart i).left.opensRange
    rw [he, hL, hC]

section AnalyticCharts

variable {ι V : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℂ V]
  {n : ℕ} (basis : Module.Basis ι ℂ V) (hn : n ≤ Module.finrank ℂ V)
  (I J : Pivot ι n)

private abbrev pivotReindex : Inside I ≃ Inside J :=
  (pivotOrder I).trans (pivotOrder J).symm

private def newPivot (A : Matrix (Outside I) (Inside I) ℂ) :
    Matrix (Inside I) (Inside I) ℂ :=
  (graphMatrix I A).submatrix (fun j ↦ (pivotReindex I J j).val) id

private def newGraph (A : Matrix (Outside I) (Inside I) ℂ) :
    Matrix (Outside J) (Inside J) ℂ :=
  (graphMatrix I A * (newPivot I J A)⁻¹).submatrix Subtype.val (pivotReindex I J).symm

private theorem graphChart_injective :
    Function.Injective (grassmannianChartPoint basis hn I) := by
  have := (grassmannianCharts basis hn).openChart I
  have : Mono ((grassmannianCharts basis hn).chart I) := Over.mono_of_mono_left _
  intro A B h
  apply (chartMatrixEquiv I complexAlgebra).symm.injective
  exact (cancel_mono ((grassmannianCharts basis hn).chart I)).1 h

private theorem graphChart_eq_iff (A : Matrix (Outside I) (Inside I) ℂ)
    (B : Matrix (Outside J) (Inside J) ℂ) :
    grassmannianChartPoint basis hn I A = grassmannianChartPoint basis hn J B ↔
      (Matrix.toLin' (graphMatrix I A)).range = (Matrix.toLin' (graphMatrix J B)).range := by
  rw [← grassmannianChartSubspace basis hn I, ← grassmannianChartSubspace basis hn J]
  constructor
  · intro h
    rw [h]
  · intro h
    exact grassmannianSubspace_injective basis hn
      (Submodule.map_injective_of_injective basis.equivFun.injective h)

private theorem newPivot_det_ne (A : Matrix (Outside I) (Inside I) ℂ)
    (B : Matrix (Outside J) (Inside J) ℂ)
    (h : grassmannianChartPoint basis hn I A = grassmannianChartPoint basis hn J B) :
    (newPivot I J A).det ≠ 0 := by
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro u v huv
  have hr := (graphChart_eq_iff basis hn I J A B).mp h
  have mem (u : Inside I → ℂ) :
      graphMatrix I A *ᵥ u ∈ (Matrix.toLin' (graphMatrix J B)).range := by
    rw [← hr]
    exact ⟨u, rfl⟩
  obtain ⟨u', hu'⟩ := mem u
  obtain ⟨v', hv'⟩ := mem v
  change graphMatrix J B *ᵥ u' = graphMatrix I A *ᵥ u at hu'
  change graphMatrix J B *ᵥ v' = graphMatrix I A *ᵥ v at hv'
  have h' : u' = v' := by
    funext j
    let k := (pivotReindex I J).symm j
    have hk : pivotReindex I J k = j := (pivotReindex I J).apply_symm_apply j
    have he := congrFun huv k
    change (graphMatrix I A *ᵥ u) (pivotReindex I J k).val =
      (graphMatrix I A *ᵥ v) (pivotReindex I J k).val at he
    rw [hk, ← hu', ← hv', graphMatrix_inside J B u' j, graphMatrix_inside J B v' j] at he
    exact he
  have heq : graphMatrix I A *ᵥ u = graphMatrix I A *ᵥ v := hu'.symm.trans (h' ▸ hv')
  funext j
  have hk := congrFun heq j.val
  rwa [graphMatrix_inside I A u j, graphMatrix_inside I A v j] at hk

private theorem newGraph_eq (A : Matrix (Outside I) (Inside I) ℂ)
    (h : (newPivot I J A).det ≠ 0) :
    grassmannianChartPoint basis hn I A = grassmannianChartPoint basis hn J (newGraph I J A) := by
  let e := pivotReindex I J
  let G := graphMatrix I A
  let D := newPivot I J A
  let H := G * D⁻¹
  have hu : IsUnit D.det := isUnit_iff_ne_zero.mpr h
  have hv : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv D hu
  have hg : graphMatrix J (newGraph I J A) = H.submatrix id e.symm := by
    ext r c
    by_cases hr : r ∈ J.val
    · let j : Inside J := ⟨r, hr⟩
      have hj : e (e.symm j) = j := e.apply_symm_apply j
      have he : H r (e.symm c) = (D * D⁻¹) (e.symm j) (e.symm c) := by
        change H j.val (e.symm c) = _
        simp only [H, Matrix.mul_apply, D, newPivot, Matrix.submatrix_apply, id_eq, e] at *
        rw [hj]
      change graphMatrix J (newGraph I J A) r c = H r (e.symm c)
      rw [he, hv, Matrix.one_apply]
      have hc : (e.symm j = e.symm c) ↔ r = c.val :=
        e.symm.injective.eq_iff.trans Subtype.ext_iff
      simp [graphMatrix, hr, hc]
    · simp [graphMatrix, hr, newGraph, H, G, D, e]
  apply (graphChart_eq_iff basis hn I J A _).mpr
  change G.toLin'.range = (graphMatrix J (newGraph I J A)).toLin'.range
  have hid : (LinearMap.funLeft ℂ ℂ (id : ι → ι)) = LinearMap.id := by
    apply LinearMap.ext
    exact LinearMap.funLeft_id ℂ ℂ
  rw [hg, Matrix.toLin'_submatrix id e.symm, hid, LinearMap.id_comp]
  have hE : (LinearMap.funLeft ℂ ℂ (e.symm.symm : Inside I → Inside J)).range = ⊤ :=
    LinearMap.range_eq_top.mpr (LinearMap.funLeft_surjective_of_injective ℂ ℂ e e.injective)
  rw [LinearMap.range_comp_of_range_eq_top _ hE, Matrix.toLin'_mul]
  have hD : (Matrix.toLin' D⁻¹).range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro u
    refine ⟨D *ᵥ u, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul D hu, Matrix.one_mulVec]
  rw [LinearMap.range_comp_of_range_eq_top _ hD]

omit [Fintype ι] in
private theorem continuous_graphMatrix :
    Continuous (graphMatrix I : Matrix (Outside I) (Inside I) ℂ → Matrix ι (Inside I) ℂ) := by
  apply continuous_matrix
  intro r c
  by_cases hr : r ∈ I.val
  · simp only [graphMatrix, Matrix.of_apply, dite_eq_left hr]
    exact continuous_const
  · simp only [graphMatrix, Matrix.of_apply, dite_eq_right hr]
    exact continuous_id.matrix_elem _ _

omit [Fintype ι] in
private theorem continuous_newPivot :
    Continuous (newPivot I J : Matrix (Outside I) (Inside I) ℂ → Matrix (Inside I) (Inside I) ℂ) :=
  continuous_matrix fun r c ↦ (continuous_graphMatrix I).matrix_elem (pivotReindex I J r).val c

omit [Fintype ι] in
private theorem continuousOn_newGraph :
    ContinuousOn (newGraph I J) {A | (newPivot I J A).det ≠ 0} := by
  intro A hA
  have hD : ContinuousAt (fun A ↦ (newPivot I J A)⁻¹) A := by
    apply (continuousAt_matrix_inv (newPivot I J A) ?_).comp (continuous_newPivot I J).continuousAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hA
  have hMul : Continuous (fun p : Matrix ι (Inside I) ℂ × Matrix (Inside I) (Inside I) ℂ ↦ p.1 * p.2) :=
    continuous_fst.matrix_mul continuous_snd
  have hsub : Continuous (fun M : Matrix ι (Inside I) ℂ ↦
      M.submatrix (Subtype.val : Outside J → ι) (pivotReindex I J).symm) :=
    continuous_matrix fun r c ↦ continuous_id.matrix_elem r.val ((pivotReindex I J).symm c)
  have hmul := hMul.continuousAt.comp
    (((continuous_graphMatrix I).continuousAt (x := A)).prodMk hD)
  exact (hsub.continuousAt.comp hmul).continuousWithinAt

private theorem graphChart_openEmbedding :
    Topology.IsOpenEmbedding (grassmannianChartPoint basis hn J) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · apply continuous_iff_coinduced_le.mpr
    exact le_iSup (fun K ↦ TopologicalSpace.coinduced (grassmannianChartPoint basis hn K) inferInstance) J
  · exact graphChart_injective basis hn J
  · intro s hs
    change IsOpen[⨆ K : Pivot ι n,
      TopologicalSpace.coinduced (grassmannianChartPoint basis hn K) inferInstance]
        (grassmannianChartPoint basis hn J '' s)
    apply isOpen_iSup_iff.mpr
    intro K
    rw [isOpen_coinduced]
    have he : (grassmannianChartPoint basis hn K) ⁻¹' (grassmannianChartPoint basis hn J '' s) =
        {A | (newPivot K J A).det ≠ 0} ∩ (newGraph K J) ⁻¹' s := by
      ext A
      constructor
      · rintro ⟨B, hB, hb⟩
        have h := newPivot_det_ne basis hn K J A B hb.symm
        have hnew := newGraph_eq basis hn K J A h
        have hAB := graphChart_injective basis hn J (hb.trans hnew)
        refine ⟨h, ?_⟩
        change newGraph K J A ∈ s
        rwa [← hAB]
      · rintro ⟨h, hA⟩
        exact ⟨newGraph K J A, hA, (newGraph_eq basis hn K J A h).symm⟩
    rw [he]
    exact (continuousOn_newGraph K J).isOpen_inter_preimage
      (isOpen_compl_singleton.preimage (continuous_newPivot K J).matrix_det) hs

end AnalyticCharts

private theorem polynomialGraph_eval_continuous (i : Fin 2) :
    Continuous (fun z : Fin m → ℂ ↦ (polynomialGraph hd i).map (MvPolynomial.aeval z)) := by
  apply continuous_matrix
  intro r c
  simp only [Matrix.map_apply, polynomialGraph, Matrix.of_apply]
  split
  · simp only [map_neg, MvPolynomial.aeval_X]
    exact (continuous_apply _).neg
  · simp only [map_zero]
    exact continuous_const

private theorem zerothColumn_continuous (hm : 0 < m) (i : Fin 2) :
    Continuous (zerothColumnCoefficients hd hm i) := by
  apply continuous_pi
  intro k
  unfold zerothColumnCoefficients
  exact (continuous_id.matrix_elem _ _).neg

private theorem jetChart_analytic_open (hm : 0 < m) (C : JetCharts hd) (i : Fin 2) :
    Topology.IsOpenEmbedding
      (fun z : Fin m → ℂ ↦ (affinePoint z ≫ C.chart i : NormalizedJetPoints hd)) := by
  let f := fun z : Fin m → ℂ ↦ (affinePoint z ≫ C.chart i : NormalizedJetPoints hd)
  let j := normalizedJetInclusion hd
  let g : NormalizedJetPoints hd → WindowPoints 2 b m d := fun q ↦ q ≫ j ≫ stableInclusion d
  let A := fun z : Fin m → ℂ ↦ (polynomialGraph hd i).map (MvPolynomial.aeval z)
  let G := grassmannianChartPoint (windowBasis 2 b m) (windowDimension_le d) (jetPivot hd i)
  have hG : Topology.IsOpenEmbedding G := graphChart_openEmbedding _ _ _
  have hg : Topology.IsInducing g := ⟨rfl⟩
  have hcomp : g ∘ f = G ∘ A := by
    funext z
    change (affinePoint z ≫ C.chart i) ≫ j ≫ stableInclusion d = G (A z)
    rw [Category.assoc, C.graph_eq i, ← Category.assoc, matrix_affinePoint_graphMap]
    rfl
  have hA : Topology.IsEmbedding A := Function.LeftInverse.isEmbedding
    (recoverCoefficients hd hm i) (zerothColumn_continuous hd hm i) (polynomialGraph_eval_continuous hd i)
  have hgf : Topology.IsEmbedding (g ∘ f) := hcomp.symm ▸ (hG.isEmbedding.comp hA)
  have hf : Continuous f := hg.continuous_iff.mpr hgf.continuous
  have hEmb : Topology.IsEmbedding f := Topology.IsEmbedding.of_comp hf hg.continuous hgf
  have hr : Set.range f = g ⁻¹' Set.range G := by
    ext q
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨A z, (congrFun hcomp z).symm⟩
    · rintro ⟨B, hB⟩
      have hpoint : pointLocation (g q) ∈ Set.range (jetPivotChart hd i).left := by
        rw [← hB]
        exact ⟨pointLocation ((chartMatrixEquiv (jetPivot hd i) complexAlgebra).symm B), rfl⟩
      have hstable : pointLocation (q ≫ j) ∈ (stablePivotOpen hd i : Set _) := hpoint
      rw [← C.range_eq i] at hstable
      obtain ⟨x, hx⟩ := hstable
      have : IsOpenImmersion j.left := by
        change IsOpenImmersion (normalizedJetOpen hd).ι
        infer_instance
      have := C.isOpen i
      have hl : pointLocation q ∈ Set.range (C.chart i).left :=
        ⟨x, j.left.isOpenEmbedding.injective hx⟩
      obtain ⟨p, rfl⟩ := (point_factors_iff (C.chart i) q).1 hl
      obtain ⟨z, rfl⟩ := affinePoint_surjective m p
      exact ⟨z, rfl⟩
  refine ⟨hEmb, ?_⟩
  rw [hr]
  exact hG.isOpen_range.preimage hg.continuous

/-- The two normalized row charts on the reduced minimal rank-two jet window. -/
theorem normalizedJetGraphSchemeCharts : NormalizedJetGraphSchemeCharts := by
  intro b m d hd hm
  let C := jetCharts hd hm
  obtain ⟨π, hπ⟩ := projection_exists hd hm C
  exact ⟨{
    chart := C.chart
    projection := π
    chart_open := C.isOpen
    chart_range := C.range_eq
    chart_cover := chartsCover hd C
    polynomial_graph := C.graph_eq
    kernel := chartKernel hd C
    line_chart_open := lineChart_open
    line_chart_cover := lineChart_cover
    line_chart_point := lineChart_point
    projection_pullback := projectionPullback hd hm C π hπ
    inversion_pullback := inversionPullback hd hm C
    inversion_on_points := inversionOnPoints hd C
    smooth := jetSmooth hd C
    analytic_open := jetChart_analytic_open hd hm C
    recover_coefficients := recoverCoefficients hd hm
  }⟩

end

end RepTheorySurvey.Geometric.SchubertNormalizedJetGraphSchemes
