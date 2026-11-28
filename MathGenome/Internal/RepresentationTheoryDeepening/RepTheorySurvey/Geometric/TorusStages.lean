import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.TorusStages

import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.BoundedLattices
namespace RepTheorySurvey.Geometric.TorusStages

open LatticeModelSpecs BoundedLatticeSpecs TorusStageSpecs
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LinearAlgebraicGroups (Points SchemeOver)
open Scheme.IdealSheafData

noncomputable section

private theorem laurentFactorization (f : K) (hf : f ≠ 0) :
    ∃ u : Oˣ, f = monomial f.order * inclusion (u : O) := by
  have h0 : PowerSeries.constantCoeff f.powerSeriesPart ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, LaurentSeries.powerSeriesPart_coeff]
    simpa using HahnSeries.coeff_order_eq_zero.not.mpr hf
  obtain ⟨u, hu⟩ := PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr h0)
  refine ⟨u, ?_⟩
  rw [hu]
  exact f.single_order_mul_powerSeriesPart.symm

private theorem positiveTorusFixesLattices (ht : TorusTransitive) (hs : TorusStabilizer)
    (r : ℕ) (u : PositiveTorus r) (L : TorusLattice r) :
    (u : Fin r → Kˣ) • L = L := by
  obtain ⟨g, rfl⟩ := ht r L
  have hu : (u : Fin r → Kˣ) ∈
      MulAction.stabilizer (Fin r → Kˣ) (fun _ : Fin r ↦ standardLattice 1) := by
    rw [hs r]
    exact u.property
  rw [MulAction.mem_stabilizer_iff] at hu
  rw [← mul_smul, mul_comm (u : Fin r → Kˣ) g, mul_smul, hu]


set_option backward.isDefEq.respectTransparency false in
private theorem scalarLattice_le_iff (a b : ℤ) :
    (scalarLattice 1 a).val ≤ (scalarLattice 1 b).val ↔ b ≤ a := by
  constructor
  · intro h
    have hx : shiftedInclusion 1 a (fun _ ↦ 1) ∈ (scalarLattice 1 a).val := by
      rw [scalarLattice_val]
      exact LinearMap.mem_range_self _ _
    have hy := h hx
    rw [scalarLattice_val, LinearMap.mem_range] at hy
    obtain ⟨y, hy⟩ := hy
    have heq : monomial b * inclusion (y 0) = monomial a := by
      have h0 := congrFun hy (0 : Fin 1)
      change monomial b * inclusion (y 0) = monomial a * inclusion 1 at h0
      simpa using h0
    by_contra! hab
    have hcoeff := congrArg (fun f : K ↦ f.coeff a) heq
    rw [monomial, HahnSeries.coeff_single_mul, one_mul, monomial, HahnSeries.coeff_single_same]
      at hcoeff
    have hzero : (inclusion (y 0)).coeff (a - b) = 0 := by
      change (HahnSeries.ofPowerSeries ℤ ℂ (y 0)).coeff (a - b) = 0
      rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_of_notMem_range]
      rintro ⟨n, hn⟩
      change (n : ℤ) = a - b at hn
      omega
    rw [hzero] at hcoeff
    exact zero_ne_one hcoeff
  · intro h
    exact diagonalLattice_le (fun _ ↦ h)

private theorem torusLabels_bijective (ht : TorusTransitive) (hs : TorusStabilizer)
    (r : ℕ) : Function.Bijective (torusLatticeAt r) := by
  constructor
  · intro v w hvw
    funext i
    have heq : scalarLattice 1 (v i) = scalarLattice 1 (w i) := congrFun hvw i
    have hle : (scalarLattice 1 (v i)).val ≤ (scalarLattice 1 (w i)).val := heq.le
    have hge : (scalarLattice 1 (w i)).val ≤ (scalarLattice 1 (v i)).val := heq.ge
    exact le_antisymm ((scalarLattice_le_iff _ _).mp hge) ((scalarLattice_le_iff _ _).mp hle)
  · intro L
    obtain ⟨g, hg⟩ := ht r L
    let w : Coweight r := fun i ↦ (g i : K).order
    choose u hu using fun i ↦ laurentFactorization (g i : K) (g i).ne_zero
    have heq : g = torusMonomial r w * positiveTorusMap r u := by
      funext i
      apply Units.ext
      exact hu i
    refine ⟨w, ?_⟩
    rw [← torusMonomial_smul_standard, ← hg, heq, mul_smul]
    have hfix := positiveTorusFixesLattices ht hs r
      ⟨positiveTorusMap r u, ⟨u, rfl⟩⟩ (fun _ ↦ standardLattice 1)
    exact congrArg (fun L : TorusLattice r ↦ torusMonomial r w • L) hfix.symm

private theorem scalarLattice_surjective (ht : TorusTransitive) (hs : TorusStabilizer) :
    Function.Surjective (scalarLattice 1) := by
  intro L
  obtain ⟨w, hw⟩ := (torusLabels_bijective ht hs 1).surjective (fun _ ↦ L)
  exact ⟨w 0, congrFun hw 0⟩

private def polynomialToJet (m : ℕ) : Polynomial ℂ →ₐ[ℂ] JetRing m :=
  (jetReduction m).comp (Polynomial.coeToPowerSeries.algHom ℂ)

private theorem polynomialToJet_apply (m : ℕ) (f : Polynomial ℂ) :
    polynomialToJet m f = jetReduction m (f : O) := by
  simp [polynomialToJet]

private theorem polynomialToJet_eq_zero (m : ℕ) (f : Polynomial ℂ) :
    polynomialToJet m f = 0 ↔ f ∈ Ideal.span {(Polynomial.X : Polynomial ℂ) ^ m} := by
  rw [polynomialToJet_apply]
  change Ideal.Quotient.mk (jetIdeal m) (f : O) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, jetIdeal, Ideal.mem_span_singleton, Ideal.mem_span_singleton,
    PowerSeries.X_pow_dvd_iff, Polynomial.X_pow_dvd_iff]
  simp only [Polynomial.coeff_coe]

private theorem polynomialToJet_surjective (m : ℕ) : Function.Surjective (polynomialToJet m) := by
  intro j
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective j
  refine ⟨PowerSeries.trunc m f, ?_⟩
  rw [polynomialToJet_apply]
  change jetReduction m (PowerSeries.trunc m f : O) = jetReduction m f
  apply (jetCoefficients m).injective
  funext i
  simp [Polynomial.coeff_coe, PowerSeries.coeff_trunc, i.isLt]

private def polynomialJetEquiv (m : ℕ) : PolynomialTruncation m ≃ₐ[ℂ] JetRing m := by
  let g := Ideal.Quotient.liftₐ _ (polynomialToJet m)
    (fun f hf ↦ (polynomialToJet_eq_zero m f).mpr hf)
  refine AlgEquiv.ofBijective g ⟨?_, ?_⟩
  · apply (injective_iff_map_eq_zero g.toLinearMap).mpr
    intro y hy
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((polynomialToJet_eq_zero m f).mp hy)
  · intro y
    obtain ⟨f, rfl⟩ := polynomialToJet_surjective m y
    exact ⟨truncatedPolynomial f, rfl⟩

private def windowJetOne (a : ℤ) (m : ℕ) : Window 1 a m ≃ₗ[O] JetRing m :=
  windowJets 1 a m ≪≫ₗ LinearEquiv.funUnique (Fin 1) O (JetRing m)

private def rankOneWindowQuotient (a : ℤ) (m : ℕ) :
    ((scalarLattice 1 a).val : Type) →ₗ[O] Window 1 a m :=
  @Submodule.mkQ O ((scalarLattice 1 a).val : Type) inferInstance inferInstance inferInstance
    (windowLower 1 a m)

private theorem windowJetOne_mk (a : ℤ) (m : ℕ) (x : Fin 1 → O) :
    windowJetOne a m (rankOneWindowQuotient a m (shiftedCoordinates 1 a x)) =
      jetReduction m (x 0) := by
  change (windowReduction 1 a m (shiftedCoordinates 1 a x)) 0 = _
  change jetReduction m ((shiftedCoordinates 1 a).symm (shiftedCoordinates 1 a x) 0) = _
  rw [LinearEquiv.symm_apply_apply]

private theorem windowJetOne_operator (a : ℤ) (m : ℕ) (x : Window 1 a m) :
    windowJetOne a m (windowOperator 1 a m x) = jetReduction m t * windowJetOne a m x :=
  (windowJetOne a m).map_smul t x

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem rankOneCyclicWindowProof : RankOneCyclicWindow := by
  intro a m
  let E := polynomialJetEquiv m
  let W := (windowJetOne a m).restrictScalars ℂ
  refine ⟨E.toLinearEquiv ≪≫ₗ W.symm, ?_, ?_⟩
  · apply W.injective
    change W (W.symm (E 1)) = _
    rw [LinearEquiv.apply_symm_apply, map_one]
    change 1 = windowJetOne a m (rankOneWindowQuotient a m (shiftedCoordinates 1 a (fun _ ↦ 1)))
    rw [windowJetOne_mk, map_one]
  · intro x
    apply W.injective
    change W (W.symm (E (truncatedPolynomial Polynomial.X * x))) =
      windowJetOne a m (windowOperator 1 a m (W.symm (E x)))
    rw [LinearEquiv.apply_symm_apply, windowJetOne_operator, map_mul]
    change E (truncatedPolynomial Polynomial.X) * E x =
      jetReduction m t * W (W.symm (E x))
    rw [LinearEquiv.apply_symm_apply]
    exact congrArg (· * E x) (by
      change polynomialToJet m Polynomial.X = _
      rw [polynomialToJet_apply, Polynomial.coe_X])


private theorem windowFinrank (a : ℤ) (m : ℕ) :
    Module.finrank ℂ (Window 1 a m) = m := by
  rw [(windowCoordinates 1 a m).finrank_eq, Module.finrank_pi_fintype]
  simp

set_option backward.isDefEq.respectTransparency false in
private def windowToSmaller (a : ℤ) {d m : ℕ} (h : d ≤ m) :
    Window 1 a m →ₗ[O] Window 1 a d :=
  @Submodule.liftQ O ((scalarLattice 1 a).val : Type) inferInstance inferInstance
    inferInstance (windowLower 1 a m) O (Window 1 a d) inferInstance inferInstance
    inferInstance (RingHom.id O) (rankOneWindowQuotient a d) (by
      rw [rankOneWindowQuotient, Submodule.ker_mkQ]
      exact Submodule.comap_mono ((scalarLattice_le_iff (a + (m : ℤ)) (a + (d : ℤ))).mpr
        (by omega)))

set_option backward.isDefEq.respectTransparency false in
private theorem latticeSubspace_finrank (a : ℤ) {d m : ℕ} (h : d ≤ m) :
    Module.finrank ℂ (latticeSubspace a m (scalarLattice 1 (a + (d : ℤ)))) = m - d := by
  let f := (windowToSmaller a h).restrictScalars ℂ
  have hker : f.ker = latticeSubspace a m (scalarLattice 1 (a + (d : ℤ))) := by
    change (LinearMap.ker (windowToSmaller a h)).restrictScalars ℂ = _
    unfold windowToSmaller
    rw [Submodule.ker_liftQ, rankOneWindowQuotient, Submodule.ker_mkQ]
    rfl
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := (@Submodule.mkQ_surjective O ((scalarLattice 1 a).val : Type)
      inferInstance inferInstance inferInstance (windowLower 1 a d)) y
    exact ⟨rankOneWindowQuotient a m x, rfl⟩
  have hq := (f.quotKerEquivOfSurjective hsurj).finrank_eq
  rw [windowFinrank] at hq
  have hsum := f.ker.finrank_quotient_add_finrank
  rw [windowFinrank, hq, hker] at hsum
  omega

private theorem rankOneStableSubspacesProof (ht : TorusTransitive) (hs : TorusStabilizer)
    (hc : WindowLatticeComparison) : RankOneStableSubspaces := by
  intro a m
  refine ⟨?_, fun d ↦ latticeSubspace_finrank a (Nat.lt_succ_iff.mp d.isLt)⟩
  intro P
  obtain ⟨e, he, _⟩ := hc 1 a m
  let L := e.symm P
  obtain ⟨b, hb⟩ := scalarLattice_surjective ht hs L.val
  have hab : a ≤ b := (scalarLattice_le_iff _ _).mp (hb ▸ L.property.2)
  have hba : b ≤ a + (m : ℤ) := (scalarLattice_le_iff _ _).mp (hb ▸ L.property.1)
  let d := (b - a).toNat
  have hd : d ≤ m := by omega
  have hbd : a + (d : ℤ) = b := by omega
  have hp : P.val = latticeSubspace a m (scalarLattice 1 (a + (d : ℤ))) := by
    rw [hbd, hb, ← he L, Equiv.apply_symm_apply]
  refine ⟨⟨d, Nat.lt_succ_of_le hd⟩, hp, ?_⟩
  intro j hj
  apply Fin.ext
  have hjm := Nat.lt_succ_iff.mp j.isLt
  have hdim := congrArg (fun Q : Submodule ℂ (Window 1 a m) ↦ Module.finrank ℂ Q)
    (hj.symm.trans hp)
  rw [latticeSubspace_finrank a hjm, latticeSubspace_finrank a hd] at hdim
  change m - j.val = m - d at hdim
  change j.val = d
  omega



private theorem stableSubspace_eq_of_finrank (h : RankOneStableSubspaces)
    {a : ℤ} {m : ℕ} (P Q : StableSubspaces 1 a m)
    (hr : Module.finrank ℂ P.val = Module.finrank ℂ Q.val) : P.val = Q.val := by
  obtain ⟨d, hd, _⟩ := (h a m).1 P
  obtain ⟨e, he, _⟩ := (h a m).1 Q
  rw [hd, he, (h a m).2 d, (h a m).2 e] at hr
  have hde : d = e := Fin.ext (by have := d.isLt; have := e.isLt; omega)
  rw [hd, he, hde]

private theorem rankOneStablePoints_subsingleton (h : RankOneStableSubspaces)
    (a : ℤ) (m : ℕ) (d : WindowDimension 1 a m) :
    Subsingleton (StablePoints (windowBasis 1 a m) (windowDimension_le d) (windowOperator 1 a m)) := by
  constructor
  intro p q
  apply Subtype.ext
  apply grassmannianSubspace_injective
  exact stableSubspace_eq_of_finrank h ⟨_, p.property⟩ ⟨_, q.property⟩
    ((grassmannianSubspace_finrank _ _ p.val).trans
      (grassmannianSubspace_finrank _ _ q.val).symm)

private theorem rankOneBounded_discrete (h : RankOneStableSubspaces)
    (hc : BoundedStageComparison) (N : ℕ) : DiscreteTopology (BoundedLattice 1 N) := by
  have hstage : DiscreteTopology (BoundedStage 1 N) := by
    apply discreteTopology_iff_forall_isOpen.mpr
    intro S
    apply (@isOpen_sigma_iff _ _ (fun d ↦
      stablePointsTopology (windowBasis 1 (-(N : ℤ)) (2 * N))
        (windowDimension_le d) (windowOperator 1 (-(N : ℤ)) (2 * N))) S).mpr
    intro d
    let := rankOneStablePoints_subsingleton h (-(N : ℤ)) (2 * N) d
    exact isOpen_discrete _
  apply discreteTopology_iff_forall_isOpen.mpr
  intro S
  apply isOpen_induced_iff.mpr
  exact ⟨boundedPoint '' S, (discreteTopology_iff_forall_isOpen.mp hstage) _,
    Set.preimage_image_eq _ (hc 1 N).1.injective⟩

private def boundedLabel {r N : ℕ} (w : BoundedCoweight r N) : BoundedTorus r N :=
  fun i ↦ ⟨scalarLattice 1 (w.val i),
    (scalarLattice_le_iff _ _).mpr (w.property i).2,
    (scalarLattice_le_iff _ _).mpr (w.property i).1⟩

private theorem forgetTorusBound_injective (r N : ℕ) :
    Function.Injective (forgetTorusBound (r := r) (N := N)) := by
  intro L L' h
  funext i
  exact Subtype.ext (congrFun h i)

private theorem boundedLabel_bijective (ht : TorusTransitive) (hs : TorusStabilizer)
    (r N : ℕ) : Function.Bijective (boundedLabel (r := r) (N := N)) := by
  constructor
  · intro w v h
    exact Subtype.ext ((torusLabels_bijective ht hs r).injective
      (congrArg (forgetTorusBound (r := r) (N := N)) h))
  · intro L
    obtain ⟨w, hw⟩ := (torusLabels_bijective ht hs r).surjective (forgetTorusBound L)
    have hb : ∀ i, -(N : ℤ) ≤ w i ∧ w i ≤ N := by
      intro i
      have hi : scalarLattice 1 (w i) = (L i).val := congrFun hw i
      exact ⟨(scalarLattice_le_iff _ _).mp (hi ▸ (L i).property.2),
        (scalarLattice_le_iff _ _).mp (hi ▸ (L i).property.1)⟩
    exact ⟨⟨w, hb⟩, forgetTorusBound_injective _ _ hw⟩

private theorem finiteBoundedCoweight (r N : ℕ) : Finite (BoundedCoweight r N) := by
  have : Finite (Set.Icc (-(N : ℤ)) (N : ℤ)) :=
    Set.finite_coe_iff.mpr (Set.finite_Icc _ _)
  let f (w : BoundedCoweight r N) : Fin r → Set.Icc (-(N : ℤ)) (N : ℤ) :=
    fun i ↦ ⟨w.val i, w.property i⟩
  apply Finite.of_injective f
  intro w v heq
  exact Subtype.ext (funext fun i ↦ congrArg Subtype.val (congrFun heq i))

private theorem boundedTorusPointsProof (ht : TorusTransitive) (hs : TorusStabilizer)
    (h : RankOneStableSubspaces) (hc : BoundedStageComparison) : BoundedTorusPoints := by
  intro r
  refine ⟨fun N ↦ Equiv.ofBijective _ (boundedLabel_bijective ht hs r N), ?_, ?_, ?_⟩
  · intros
    rfl
  · intro N
    let := rankOneBounded_discrete h hc N
    exact ⟨finiteBoundedCoweight r N, Pi.discreteTopology⟩
  · intro N M hNM w
    apply forgetTorusBound_injective r M
    rfl

private theorem torusPointsProof (ht : TorusTransitive) (hs : TorusStabilizer)
    (hq : TorusCosets) (hex : LatticeExhaustion) (hb : BoundedTorusPoints) : TorusPoints := by
  intro r
  obtain ⟨q, hq⟩ := hq r
  obtain ⟨_, _, hd, _⟩ := hb r
  refine ⟨Equiv.ofBijective _ (torusLabels_bijective ht hs r), q, fun _ ↦ rfl, hq, ?_,
    ?_, ?_, ?_, positiveTorusFixesLattices ht hs r⟩
  · intro w
    rw [hq, torusMonomial_smul_standard]
    rfl
  · intro L
    obtain ⟨N, B, hB⟩ := hex.2 r L
    exact ⟨N, B, funext hB⟩
  · let := torusAnalyticTopology r
    apply discreteTopology_iff_forall_isOpen.mpr
    intro S
    change @IsOpen _ (⨆ N : ℕ, TopologicalSpace.coinduced
      (forgetTorusBound (r := r) (N := N)) inferInstance) S
    rw [isOpen_iSup_iff]
    intro N
    exact isOpen_coinduced.mpr ((discreteTopology_iff_forall_isOpen.mp (hd N).2) _)
  · intro u x
    induction x using Quotient.inductionOn with
    | h g =>
      change coset (PositiveTorus r) ((u : Fin r → Kˣ) * g) = coset (PositiveTorus r) g
      apply QuotientGroup.eq.mpr
      rw [mul_comm (u : Fin r → Kˣ) g, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
      exact (PositiveTorus r).inv_mem u.property



private theorem complexPointStructure :
    complexPointScheme.hom = 𝟙 (Spec (CommRingCat.of ℂ)) := by
  change Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ)) = _
  simp

private def complexPointTerminal : IsTerminal complexPointScheme :=
  IsTerminal.ofUniqueHom
    (fun X ↦ Over.homMk X.hom (by
      rw [complexPointStructure]
      exact Category.comp_id X.hom))
    (fun X p ↦ Over.OverMorphism.ext (by
      change p.left = X.hom
      have h := Over.w p
      rw [complexPointStructure] at h
      exact (Category.comp_id p.left).symm.trans h))

private theorem complexPointClosed {X : SchemeOver ℂ} (p : Points X complexAlgebra) :
    IsClosedImmersion p.left :=
  isClosedImmersion_of_comp_eq_id X.hom p.left ((Over.w p).trans complexPointStructure)

private theorem reducedSingletonIso
    (X : SchemeOver ℂ) (S : Set (Points X complexAlgebra))
    (p : Points (reducedClosureScheme X S) complexAlgebra)
    (hS : S = {p ≫ reducedClosureInclusion X S})
    (hr : IsReduced (reducedClosureScheme X S).left) : IsIso p := by
  let j := reducedClosureInclusion X S
  have hj : IsClosedImmersion j.left := by
    change IsClosedImmersion (reducedClosureIdeal X S).subschemeι
    infer_instance
  have hp : IsClosedImmersion p.left := complexPointClosed p
  have hpj : IsClosedImmersion (p ≫ j).left := complexPointClosed (p ≫ j)
  have hjrange : Set.range j.left = closure (pointLocation '' S) := by
    change Set.range (reducedClosureIdeal X S).subschemeι = _
    rw [range_subschemeι, reducedClosureIdeal, coe_support_vanishingIdeal]
    rfl
  have hclosure := congrArg (fun P : Set (Points X complexAlgebra) ↦
    closure (pointLocation '' P)) hS
  have hrange : Set.range j.left = Set.range (p ≫ j).left := by
    rw [hjrange, hclosure, Set.image_singleton, ← pointLocation_range]
    exact hpj.isClosedEmbedding.isClosed_range.closure_eq
  have : Surjective p.left := by
    constructor
    intro y
    obtain ⟨x, hx⟩ := (Set.ext_iff.mp hrange (j.left y)).mp (Set.mem_range_self y)
    exact ⟨x, hj.isClosedEmbedding.injective hx⟩
  have : IsIso p.left := isIso_of_isClosedImmersion_of_surjective _
  have : IsIso ((Over.forget (Spec (CommRingCat.of ℂ))).map p) :=
    inferInstanceAs (IsIso p.left)
  exact isIso_of_reflects_iso p (Over.forget _)

private theorem rankOneSchemePoint (hs : WindowSchemeComparison) (a : ℤ) (m : ℕ)
    (d : WindowDimension 1 a m) :
    ∃ q : Points (windowStableScheme 1 a m d) complexAlgebra,
      IsReduced (windowStableScheme 1 a m d).left ∧
      windowSchemeSubspace q =
        latticeSubspace a m (scalarLattice 1 (a + ((m - d.val : ℕ) : ℤ))) := by
  obtain ⟨hr, _, e, he⟩ := hs 1 a m d
  have hd : d.val ≤ m := by
    exact (windowDimension_le d).trans_eq (windowFinrank a m)
  let j := m - d.val
  have hj : j ≤ m := Nat.sub_le _ _
  let L : WindowLattice 1 a m := ⟨scalarLattice 1 (a + (j : ℤ)),
    (scalarLattice_le_iff _ _).mpr (by omega), scalarLattice_add_nat_le 1 a j⟩
  have hdim : Module.finrank ℂ (latticeSubspace a m L.val) = d.val :=
    (latticeSubspace_finrank a hj).trans (by dsimp [j]; omega)
  let q := e.symm ⟨L, hdim⟩
  refine ⟨q, hr, ?_⟩
  rw [he q]
  change latticeSubspace a m (e (e.symm ⟨L, hdim⟩)).val.val = _
  rw [Equiv.apply_symm_apply]

private theorem rankOneSchemeIso (hs : WindowSchemeComparison) (h : RankOneStableSubspaces)
    (a : ℤ) (m : ℕ) (d : WindowDimension 1 a m) :
    ∃ e : complexPointScheme ≅ windowStableScheme 1 a m d,
      windowSchemeSubspace e.hom =
        latticeSubspace a m (scalarLattice 1 (a + ((m - d.val : ℕ) : ℤ))) := by
  obtain ⟨q, hr, hq⟩ := rankOneSchemePoint hs a m d
  let b := windowBasis 1 a m
  let hd := windowDimension_le d
  let T := windowOperator 1 a m
  let X := (grassmannianCharts b hd).scheme
  let S : Set (Points X complexAlgebra) := {p | StablePlane b hd T p}
  let j := reducedClosureInclusion X S
  have hqS : q ≫ j ∈ S := by
    change (windowSchemeSubspace q).map T ≤ windowSchemeSubspace q
    rw [hq]
    exact latticeSubspace_stable a m _
  have hS : S = {q ≫ j} := by
    have hsub : Subsingleton (StablePoints b hd T) := rankOneStablePoints_subsingleton h a m d
    ext p
    constructor
    · intro hp
      exact Set.mem_singleton_iff.mpr (congrArg (fun z : StablePoints b hd T ↦ z.val)
        (@Subsingleton.elim (StablePoints b hd T) hsub ⟨p, hp⟩ ⟨q ≫ j, hqS⟩))
    · rintro rfl
      exact hqS
  have : IsIso q := reducedSingletonIso X S q hS hr
  exact ⟨asIso q, hq⟩



private def boundedDimensionEquiv (r N : ℕ) : BoundedCoweight r N ≃ TorusStageDimensions r N where
  toFun w i := ⟨((N : ℤ) - w.val i).toNat, by
    have h := w.property i
    rw [windowFinrank]
    omega⟩
  invFun d := ⟨fun i ↦ (N : ℤ) - ((d i).val : ℤ), fun i ↦ by
    have h := (windowDimension_le (d i)).trans_eq (windowFinrank (-(N : ℤ)) (2 * N))
    change -(N : ℤ) ≤ (N : ℤ) - (d i).val ∧ (N : ℤ) - (d i).val ≤ N
    exact ⟨by omega, by omega⟩⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    change (N : ℤ) - ((((N : ℤ) - w.val i).toNat : ℕ) : ℤ) = w.val i
    have h := w.property i
    omega
  right_inv d := by
    funext i
    apply Fin.ext
    change ((N : ℤ) - ((N : ℤ) - ((d i).val : ℤ))).toNat = (d i).val
    omega

private theorem boundedDimensionEquiv_exponent {r N : ℕ}
    (w : BoundedCoweight r N) (i : Fin r) :
    -(N : ℤ) + ((2 * N - (boundedDimensionEquiv r N w i).val : ℕ) : ℤ) = w.val i := by
  change -(N : ℤ) + ((2 * N - ((N : ℤ) - w.val i).toNat : ℕ) : ℤ) = w.val i
  have h := w.property i
  omega

private def torusProductIso (r N : ℕ) (d : TorusStageDimensions r N)
    (e : ∀ i, complexPointScheme ≅ windowStableScheme 1 (-(N : ℤ)) (2 * N) (d i)) :
    complexPointScheme ≅ torusStageScheme r N d where
  hom := Pi.lift (fun i ↦ (e i).hom)
  inv := complexPointTerminal.from _
  hom_inv_id := complexPointTerminal.hom_ext _ _
  inv_hom_id := by
    unfold torusStageScheme
    apply Pi.hom_ext
    intro i
    rw [Category.assoc, Pi.lift_comp_π, Category.id_comp]
    apply (cancel_mono (e i).inv).mp
    apply complexPointTerminal.hom_ext

private def torusStageIso (r N : ℕ)
    (e : ∀ d : TorusStageDimensions r N, complexPointScheme ≅ torusStageScheme r N d) :
    labelledPointScheme r N ≅ boundedTorusScheme r N :=
  Sigma.whiskerEquiv (boundedDimensionEquiv r N) (fun w ↦ (e (boundedDimensionEquiv r N w)).symm)

private theorem torusStageIso_apply (r N : ℕ)
    (e : ∀ d : TorusStageDimensions r N, complexPointScheme ≅ torusStageScheme r N d)
    (w : BoundedCoweight r N) :
    labelledPoint w ≫ (torusStageIso r N e).hom =
      (e (boundedDimensionEquiv r N w)).hom ≫ Sigma.ι _ (boundedDimensionEquiv r N w) := by
  exact Sigma.ι_comp_map' (boundedDimensionEquiv r N)
    (fun w ↦ (e (boundedDimensionEquiv r N w)).hom) w

private theorem labelledPoint_inclusion {r N M : ℕ} (h : N ≤ M) (w : BoundedCoweight r N) :
    labelledPoint w ≫ labelledInclusion h = labelledPoint (enlargeCoweight h w) := by
  exact Sigma.ι_comp_desc (fun v : BoundedCoweight r N ↦ labelledPoint (enlargeCoweight h v)) w



private theorem pointCoproductInclusion_closed {I J : Type} [Finite I]
    (f : I → J) (hf : Function.Injective f) :
    IsClosedImmersion (Sigma.desc (fun i : I ↦
      Sigma.ι (fun _ : J ↦ complexPointScheme) (f i)) :
        (∐ fun _ : I ↦ complexPointScheme) ⟶ (∐ fun _ : J ↦ complexPointScheme)).left := by
  let F := Over.forget (Spec (CommRingCat.of ℂ))
  let A : I → SchemeOver ℂ := fun _ ↦ complexPointScheme
  let B : J → SchemeOver ℂ := fun _ ↦ complexPointScheme
  let h : ∐ A ⟶ ∐ B := Sigma.desc fun i ↦ Sigma.ι B (f i)
  let α (i : I) : (A i).left ⟶ (∐ B).left := (Sigma.ι B (f i)).left
  let c := sigmaComparison F B
  have hα (i : I) : Sigma.ι (fun j ↦ (B j).left) (f i) ≫ c = α i := by
    exact ι_comp_sigmaComparison F B (f i)
  have hαopen (i : I) : IsOpenImmersion (α i) := by
    rw [← hα]
    infer_instance
  have hdisjoint : Pairwise (fun i j ↦ Disjoint (Set.range (α i)) (Set.range (α j))) := by
    intro i j hij
    rw [← hα, ← hα]
    apply Set.disjoint_left.mpr
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    have hy' : c (Sigma.ι (fun j ↦ (B j).left) (f j) y) =
        c (Sigma.ι (fun j ↦ (B j).left) (f i) x) := hy
    have heq := c.homeomorph.injective hy'
    have hidx := congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).mp heq)
    exact hij (hf hidx.symm)
  have hh : sigmaComparison F A ≫ h.left = Sigma.desc α := by
    apply Sigma.hom_ext
    intro i
    have hι : Sigma.ι A i ≫ h = Sigma.ι B (f i) := Sigma.ι_comp_desc _ _
    rw [← Category.assoc, ι_comp_sigmaComparison, Sigma.ι_comp_desc]
    exact (F.map_comp _ _).symm.trans (congrArg (fun k ↦ F.map k) hι)
  let : ∀ i, IsOpenImmersion (α i) := hαopen
  have hop : IsOpenImmersion (Sigma.desc α) :=
    isOpenImmersion_sigmaDesc (fun i ↦ (A i).left) α hdisjoint
  have hclosed : IsClosed (Set.range (Sigma.desc α)) := by
    suffices hRange : Set.range (Sigma.desc α) = ⋃ i, Set.range (α i) by
      rw [hRange]
      apply isClosed_iUnion_of_finite
      intro i
      exact (complexPointClosed (Sigma.ι B (f i))).isClosedEmbedding.isClosed_range
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨⟨i, z⟩, rfl⟩ := (sigmaMk (fun i ↦ (A i).left)).surjective x
      refine Set.mem_iUnion.mpr ⟨i, z, ?_⟩
      rw [sigmaMk_mk, ← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
    · intro hy
      obtain ⟨i, z, rfl⟩ := Set.mem_iUnion.mp hy
      refine ⟨Sigma.ι (fun i ↦ (A i).left) i z, ?_⟩
      rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
  have hcl : IsClosedImmersion (Sigma.desc α) :=
    IsClosedImmersion.of_isPreimmersion _ hclosed
  change IsClosedImmersion h.left
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion (sigmaComparison F A), hh]
  exact hcl

private theorem labelledInclusion_closed {r N M : ℕ} (h : N ≤ M) :
    IsClosedImmersion (labelledInclusion (r := r) h).left := by
  let := finiteBoundedCoweight r N
  exact pointCoproductInclusion_closed (enlargeCoweight h)
    (fun _ _ hvw ↦ Subtype.ext (congrArg (fun v : BoundedCoweight r M ↦ v.val) hvw))

private theorem labelledInclusion_id (r N : ℕ) :
    labelledInclusion (r := r) (le_refl N) = 𝟙 _ := by
  apply Sigma.hom_ext
  intro w
  change labelledPoint w ≫ _ = labelledPoint w ≫ _
  rw [labelledPoint_inclusion, Category.comp_id]
  rfl

private theorem labelledInclusion_comp (r : ℕ) {N M P : ℕ} (h : N ≤ M) (k : M ≤ P) :
    labelledInclusion (r := r) h ≫ labelledInclusion k = labelledInclusion (h.trans k) := by
  apply Sigma.hom_ext
  intro w
  change labelledPoint w ≫ (_ ≫ _) = labelledPoint w ≫ _
  rw [← Category.assoc, labelledPoint_inclusion, labelledPoint_inclusion, labelledPoint_inclusion]
  rfl

private theorem torusStageIso_hasLattice
    (r N : ℕ)
    (e : ∀ d : WindowDimension 1 (-(N : ℤ)) (2 * N),
      complexPointScheme ≅ windowStableScheme 1 (-(N : ℤ)) (2 * N) d)
    (he : ∀ d, windowSchemeSubspace (e d).hom =
      latticeSubspace (-(N : ℤ)) (2 * N) (scalarLattice 1 (-(N : ℤ) + ↑(2 * N - d.val))))
    (w : BoundedCoweight r N) :
    HasStageLattice (labelledPoint w ≫
      (torusStageIso r N (fun d ↦ torusProductIso r N d (fun i ↦ e (d i)))).hom)
      (torusLatticeAt r w.val) := by
  let d := boundedDimensionEquiv r N w
  let E (s : TorusStageDimensions r N) := torusProductIso r N s (fun i ↦ e (s i))
  refine ⟨d, (E d).hom, torusStageIso_apply r N E w, ?_⟩
  intro i
  change windowSchemeSubspace (Pi.lift (fun i ↦ (e (d i)).hom) ≫ Pi.π _ i) = _
  rw [Pi.lift_comp_π, he (d i), boundedDimensionEquiv_exponent w i]
  rfl

private def transportDiagram {C : Type*} [Category C] {A B : ℕ → C}
    (e : ∀ N, A N ≅ B N) (f : ∀ {N M}, N ≤ M → (A N ⟶ A M))
    {N M : ℕ} (h : N ≤ M) : B N ⟶ B M :=
  (e N).inv ≫ f h ≫ (e M).hom

private abbrev stageInclusion {r : ℕ}
    (e : ∀ N : ℕ, labelledPointScheme r N ≅ boundedTorusScheme r N)
    {N M : ℕ} (h : N ≤ M) : boundedTorusScheme r N ⟶ boundedTorusScheme r M :=
  transportDiagram (C := SchemeOver ℂ) (A := labelledPointScheme r) (B := boundedTorusScheme r)
    e (@labelledInclusion r) h

private theorem stageInclusion_closed {r : ℕ}
    (e : ∀ N : ℕ, labelledPointScheme r N ≅ boundedTorusScheme r N)
    {N M : ℕ} (h : N ≤ M) : IsClosedImmersion (stageInclusion e h).left := by
  have hclosed := labelledInclusion_closed (r := r) h
  change IsClosedImmersion ((e N).inv.left ≫ (labelledInclusion h).left ≫ (e M).hom.left)
  have : IsIso (e N).inv.left := inferInstanceAs (IsIso ((Over.forget _).map (e N).inv))
  have : IsIso (e M).hom.left := inferInstanceAs (IsIso ((Over.forget _).map (e M).hom))
  infer_instance

private theorem stageInclusion_commutes {r : ℕ}
    (e : ∀ N : ℕ, labelledPointScheme r N ≅ boundedTorusScheme r N)
    {N M : ℕ} (h : N ≤ M) :
    (e N).hom ≫ stageInclusion e h = labelledInclusion h ≫ (e M).hom := by
  simp [stageInclusion, transportDiagram]

private theorem stageInclusion_id {r : ℕ}
    (e : ∀ N : ℕ, labelledPointScheme r N ≅ boundedTorusScheme r N) (N : ℕ) :
    stageInclusion e (le_refl N) = 𝟙 (boundedTorusScheme r N) := by
  simp [stageInclusion, transportDiagram, labelledInclusion_id]

private theorem composeCommutativeSquares {C : Type*} [Category C]
    {A B D A' B' D' : C} (eA : A ⟶ A') (eB : B ⟶ B') (eD : D ⟶ D') [Epi eA]
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ D)
    (f' : A' ⟶ B') (g' : B' ⟶ D') (h' : A' ⟶ D')
    (hf : eA ≫ f' = f ≫ eB) (hg : eB ≫ g' = g ≫ eD)
    (hh : eA ≫ h' = h ≫ eD) (hfg : f ≫ g = h) :
    f' ≫ g' = h' := by
  apply (cancel_epi eA).mp
  rw [← Category.assoc, hf, Category.assoc, hg, hh, ← Category.assoc, hfg]

private theorem stageInclusions_comp {r : ℕ}
    (E : ∀ N : ℕ, labelledPointScheme r N ≅ boundedTorusScheme r N)
    (j : ∀ {N M : ℕ}, N ≤ M → (boundedTorusScheme r N ⟶ boundedTorusScheme r M))
    (hj : ∀ {N M : ℕ} (h : N ≤ M), (E N).hom ≫ j h = labelledInclusion h ≫ (E M).hom)
    {N M P : ℕ} (h : N ≤ M) (k : M ≤ P) :
    j h ≫ j k = j (h.trans k) :=
  @composeCommutativeSquares (SchemeOver ℂ) _
    (labelledPointScheme r N) (labelledPointScheme r M) (labelledPointScheme r P)
    (boundedTorusScheme r N) (boundedTorusScheme r M) (boundedTorusScheme r P)
    (E N).hom (E M).hom (E P).hom _ (labelledInclusion h) (labelledInclusion k)
    (labelledInclusion (h.trans k)) (j h) (j k) (j (h.trans k))
    (hj h) (hj k) (hj (h.trans k)) (labelledInclusion_comp r h k)

private theorem canonicalStageInclusionsComp (r : ℕ)
    (E : ∀ N : ℕ, labelledPointScheme r N ≅ boundedTorusScheme r N) :
    ∀ {N M P : ℕ} (h : N ≤ M) (k : M ≤ P),
      @stageInclusion r E N M h ≫ @stageInclusion r E M P k =
        @stageInclusion r E N P (h.trans k) :=
  @stageInclusions_comp r E (@stageInclusion r E) (@stageInclusion_commutes r E)

private theorem assembleReducedTorusStages (r : ℕ)
    (E : ∀ N : ℕ, labelledPointScheme r N ≅ boundedTorusScheme r N)
    (hE : ∀ (N : ℕ) (w : BoundedCoweight r N),
      HasStageLattice (labelledPoint w ≫ (E N).hom) (torusLatticeAt r w.val)) :
    ∃ (e : ∀ N : ℕ, labelledPointScheme r N ≅ boundedTorusScheme r N)
      (j : ∀ {N M : ℕ}, N ≤ M → (boundedTorusScheme r N ⟶ boundedTorusScheme r M)),
      (∀ (N : ℕ) (w : BoundedCoweight r N),
        HasStageLattice (labelledPoint w ≫ (e N).hom) (torusLatticeAt r w.val)) ∧
      (∀ {N M : ℕ} (h : N ≤ M),
        IsClosedImmersion (j h).left ∧
          (e N).hom ≫ j h = labelledInclusion h ≫ (e M).hom) ∧
      (∀ N : ℕ, j (le_refl N) = 𝟙 (boundedTorusScheme r N)) ∧
      (∀ {N M P : ℕ} (h : N ≤ M) (k : M ≤ P), j h ≫ j k = j (h.trans k)) := by
  refine ⟨E, @stageInclusion r E, hE, ?_, stageInclusion_id E, ?_⟩
  · intro N M h
    exact ⟨stageInclusion_closed E h, stageInclusion_commutes E h⟩
  · exact canonicalStageInclusionsComp r E

private theorem reducedTorusStagesProof (hS : WindowSchemeComparison) (h : RankOneStableSubspaces) :
    ReducedTorusStages := by
  intro r
  choose e he using fun (N : ℕ) (d : WindowDimension 1 (-(N : ℤ)) (2 * N)) ↦
    rankOneSchemeIso hS h (-(N : ℤ)) (2 * N) d
  let E (N : ℕ) := torusStageIso r N (fun d ↦ torusProductIso r N d (fun i ↦ e N (d i)))
  exact assembleReducedTorusStages r E (fun N ↦ torusStageIso_hasLattice r N (e N) (he N))

theorem rankOneCyclicWindow_conditional
  (_ : BoundedInclusionTopology) (_ : BoundedStageComparison) (_ : GLCosets) (_ : GLJetAction)
    (_ : GLJetChartAnalytic) (_ : GLStabilizer) (_ : GLTransitive) (_ : LatticeExhaustion)
    (_ : TorusCosets) (_ : TorusJetAction) (_ : TorusStabilizer) (_ : TorusTransitive)
    (_ : WindowInclusions) (_ : WindowLatticeComparison) (_ : WindowPositiveStable)
    (_ : WindowSchemeComparison) (_ : WindowStageComparison) :
    RankOneCyclicWindow :=
  rankOneCyclicWindowProof

theorem rankOneStableSubspaces_conditional
  (_ : BoundedInclusionTopology) (_ : BoundedStageComparison) (_ : GLCosets) (_ : GLJetAction)
    (_ : GLJetChartAnalytic) (_ : GLStabilizer) (_ : GLTransitive) (_ : LatticeExhaustion)
    (_ : TorusCosets) (_ : TorusJetAction) (hs : TorusStabilizer) (ht : TorusTransitive)
    (_ : WindowInclusions) (hw : WindowLatticeComparison) (_ : WindowPositiveStable)
    (_ : WindowSchemeComparison) (_ : WindowStageComparison) :
    RankOneStableSubspaces :=
  rankOneStableSubspacesProof ht hs hw

theorem boundedTorusPoints_conditional
  (_ : BoundedInclusionTopology) (hb : BoundedStageComparison) (_ : GLCosets) (_ : GLJetAction)
    (_ : GLJetChartAnalytic) (_ : GLStabilizer) (_ : GLTransitive) (_ : LatticeExhaustion)
    (_ : TorusCosets) (_ : TorusJetAction) (hs : TorusStabilizer) (ht : TorusTransitive)
    (_ : WindowInclusions) (hw : WindowLatticeComparison) (_ : WindowPositiveStable)
    (_ : WindowSchemeComparison) (_ : WindowStageComparison) :
    BoundedTorusPoints :=
  boundedTorusPointsProof ht hs (rankOneStableSubspacesProof ht hs hw) hb

theorem torusPoints_conditional
  (_ : BoundedInclusionTopology) (hb : BoundedStageComparison) (_ : GLCosets) (_ : GLJetAction)
    (_ : GLJetChartAnalytic) (_ : GLStabilizer) (_ : GLTransitive) (hex : LatticeExhaustion)
    (hq : TorusCosets) (_ : TorusJetAction) (hs : TorusStabilizer) (ht : TorusTransitive)
    (_ : WindowInclusions) (hw : WindowLatticeComparison) (_ : WindowPositiveStable)
    (_ : WindowSchemeComparison) (_ : WindowStageComparison) :
    TorusPoints :=
  torusPointsProof ht hs hq hex
    (boundedTorusPointsProof ht hs (rankOneStableSubspacesProof ht hs hw) hb)

theorem reducedTorusStages_conditional
  (_ : BoundedInclusionTopology) (_ : BoundedStageComparison) (_ : GLCosets) (_ : GLJetAction)
    (_ : GLJetChartAnalytic) (_ : GLStabilizer) (_ : GLTransitive) (_ : LatticeExhaustion)
    (_ : TorusCosets) (_ : TorusJetAction) (hs : TorusStabilizer) (ht : TorusTransitive)
    (_ : WindowInclusions) (hw : WindowLatticeComparison) (_ : WindowPositiveStable)
    (hS : WindowSchemeComparison) (_ : WindowStageComparison) :
    ReducedTorusStages :=
  reducedTorusStagesProof hS (rankOneStableSubspacesProof ht hs hw)

end

end RepTheorySurvey.Geometric.TorusStages

theorem _root_.«RepTheorySurvey».«Geometric».«TorusStages».«boundedTorusPoints» : _root_.«RepTheorySurvey».«Geometric».«TorusStageSpecs».«BoundedTorusPoints» :=
  @_root_.«RepTheorySurvey».«Geometric».«TorusStages».«boundedTorusPoints_conditional» (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«boundedInclusionTopology») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«boundedStageComparison») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«glCosets») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«glJetAction») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«glJetChartAnalytic») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«glStabilizer») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«glTransitive») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«latticeExhaustion») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«torusCosets») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«torusJetAction») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«torusStabilizer») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«torusTransitive») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«windowInclusions») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«windowLatticeComparison») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«windowPositiveStable») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«windowSchemeComparison») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«windowStageComparison»)
theorem _root_.«RepTheorySurvey».«Geometric».«TorusStages».«rankOneCyclicWindow» : _root_.«RepTheorySurvey».«Geometric».«TorusStageSpecs».«RankOneCyclicWindow» :=
  @_root_.«RepTheorySurvey».«Geometric».«TorusStages».«rankOneCyclicWindow_conditional» (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«boundedInclusionTopology») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«boundedStageComparison») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«glCosets») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«glJetAction») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«glJetChartAnalytic») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«glStabilizer») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«glTransitive») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«latticeExhaustion») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«torusCosets») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«torusJetAction») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«torusStabilizer») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«torusTransitive») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«windowInclusions») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«windowLatticeComparison») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«windowPositiveStable») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«windowSchemeComparison») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«windowStageComparison»)
theorem _root_.«RepTheorySurvey».«Geometric».«TorusStages».«rankOneStableSubspaces» : _root_.«RepTheorySurvey».«Geometric».«TorusStageSpecs».«RankOneStableSubspaces» :=
  @_root_.«RepTheorySurvey».«Geometric».«TorusStages».«rankOneStableSubspaces_conditional» (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«boundedInclusionTopology») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«boundedStageComparison») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«glCosets») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«glJetAction») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«glJetChartAnalytic») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«glStabilizer») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«glTransitive») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«latticeExhaustion») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«torusCosets») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«torusJetAction») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«torusStabilizer») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«torusTransitive») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«windowInclusions») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«windowLatticeComparison») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«windowPositiveStable») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«windowSchemeComparison») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«windowStageComparison»)
theorem _root_.«RepTheorySurvey».«Geometric».«TorusStages».«reducedTorusStages» : _root_.«RepTheorySurvey».«Geometric».«TorusStageSpecs».«ReducedTorusStages» :=
  @_root_.«RepTheorySurvey».«Geometric».«TorusStages».«reducedTorusStages_conditional» (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«boundedInclusionTopology») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«boundedStageComparison») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«glCosets») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«glJetAction») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«glJetChartAnalytic») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«glStabilizer») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«glTransitive») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«latticeExhaustion») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«torusCosets») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«torusJetAction») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«torusStabilizer») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«torusTransitive») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«windowInclusions») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«windowLatticeComparison») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«windowPositiveStable») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«windowSchemeComparison») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«windowStageComparison»)
theorem _root_.«RepTheorySurvey».«Geometric».«TorusStages».«torusPoints» : _root_.«RepTheorySurvey».«Geometric».«TorusStageSpecs».«TorusPoints» :=
  @_root_.«RepTheorySurvey».«Geometric».«TorusStages».«torusPoints_conditional» (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«boundedInclusionTopology») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«boundedStageComparison») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«glCosets») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«glJetAction») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«glJetChartAnalytic») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«glStabilizer») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«glTransitive») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«latticeExhaustion») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«torusCosets») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«torusJetAction») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«torusStabilizer») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«torusTransitive») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«windowInclusions») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«windowLatticeComparison») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«windowPositiveStable») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«windowSchemeComparison») (@_root_.«RepTheorySurvey».«Geometric».«BoundedLattices».«windowStageComparison»)
