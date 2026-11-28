import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.LatticeModels

namespace RepTheorySurvey.Geometric.LatticeModels

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped MatrixGroups TensorProduct Matrix
open LinearAlgebraicGroups (Points SchemeOver TestAlgebra testSpec)
open LinearAlgebraicGroups.Specs.GrassmannianCharts
open LinearAlgebraicGroups.GrassmannianCharts (chartMatrixEquiv)
open Scheme.IdealSheafData
open LatticeModelSpecs

theorem cosetRelation {Γ : Type*} [Group Γ] (H : Subgroup Γ) : CosetRelation H := by
  intro g g'
  change Quotient.mk (QuotientGroup.leftRel H) g = Quotient.mk (QuotientGroup.leftRel H) g' ↔ _
  rw [Quotient.eq, QuotientGroup.leftRel_apply]
  refine ⟨fun h ↦ ⟨h, ⟨g⁻¹ * g', h⟩, by simp⟩, And.left⟩

theorem cosetAction : CosetAction := by
  intro Γ _ H g k
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem stable_chart_support {V ι : Type} [AddCommGroup V] [Module ℂ V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ V) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ V) (T : V →ₗ[ℂ] V) (I : Pivot ι d) :
    (chartInclusion b hd I) ⁻¹'
        ((reducedClosureIdeal (grassmannianCharts b hd).scheme
          {p | StablePlane b hd T p}).support : Set (grassmannianCharts b hd).scheme.left) =
      PrimeSpectrum.zeroLocus (stabilityIdeal I (operatorInCoordinates b T) : Set _) := by
  let C := grassmannianCharts b hd
  let j := C.chart I
  let S : Set (GrassmannianPoints b hd) := {p | StablePlane b hd T p}
  let J := stabilityIdeal I (operatorInCoordinates b T)
  have : IsOpenImmersion j.left := C.openChart I
  change j.left ⁻¹' ((reducedClosureIdeal C.scheme S).support : Set C.scheme.left) =
    PrimeSpectrum.zeroLocus (J : Set (chartAlgebra (k := ℂ) I))
  rw [reducedClosureIdeal, coe_support_vanishingIdeal]
  change j.left ⁻¹' closure (pointLocation '' S) = _
  rw [j.left.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage j.left.continuous,
    openChart_preimage_points, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  have hpts : pointLocation '' {q : Points (chartScheme (k := ℂ) I) complexAlgebra | q ≫ j ∈ S} =
      MvPolynomial.pointToPoint (k := ℂ) '' MvPolynomial.zeroLocus ℂ J := by
    ext x
    constructor
    · rintro ⟨q, hq, hqx⟩
      let A := chartMatrixEquiv I complexAlgebra q
      have hq' : (chartMatrixEquiv I complexAlgebra).symm A = q :=
        Equiv.symm_apply_apply _ q
      refine ⟨chartVariables I A, (chartVariables_mem_zeroLocus _ _ _).mpr
        ((stablePlane_chart_iff b hd T I A).mp ?_), ?_⟩
      · change (chartMatrixEquiv I complexAlgebra).symm A ≫ j ∈ S
        change q ≫ j ∈ S at hq
        simpa only [hq'] using hq
      · rw [← chart_location I A, hq', hqx]
    · rintro ⟨v, hv, rfl⟩
      let A : Matrix (Outside I) (Inside I) ℂ := Matrix.of fun j i ↦ v (j,i)
      have hA : chartVariables I A = v := by funext x; cases x; rfl
      refine ⟨(chartMatrixEquiv I complexAlgebra).symm A, ?_, by rw [chart_location, hA]⟩
      change StablePlane b hd T (grassmannianChartPoint b hd I A)
      apply (stablePlane_chart_iff b hd T I A).mpr
      apply (chartVariables_mem_zeroLocus I _ A).mp
      simpa only [hA] using hv
  rw [hpts, MvPolynomial.vanishingIdeal_pointToPoint,
    MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, PrimeSpectrum.zeroLocus_radical]

set_option backward.isDefEq.respectTransparency false in
theorem stable_chart_radical {V ι : Type} [AddCommGroup V] [Module ℂ V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ V) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ V) (T : V →ₗ[ℂ] V) (I : Pivot ι d) :
    PrimeSpectrum.vanishingIdeal ((chartInclusion b hd I) ⁻¹'
        ((reducedClosureIdeal (grassmannianCharts b hd).scheme
          {p | StablePlane b hd T p}).support : Set (grassmannianCharts b hd).scheme.left)) =
      reducedStabilityIdeal I (operatorInCoordinates b T) := by
  rw [stable_chart_support, PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
  rfl
section ReducedClosure

set_option backward.isDefEq.respectTransparency false in
theorem reducedClosure_reduced (X : SchemeOver ℂ) (S : Set (Points X complexAlgebra)) :
    IsReduced (reducedClosureScheme X S).left := by
  let Z : Closeds X.left := Closeds.closure (pointLocation '' S)
  let J := reducedClosureIdeal X S
  change IsReduced J.subscheme
  apply (IsReduced.iff_of_openCover J.subscheme J.subschemeCover.openCover).mpr
  intro U
  change IsReduced (Spec (CommRingCat.of (Γ(X.left, U.val) ⧸ J.ideal U)))
  rw [affine_isReduced_iff, ← Ideal.isRadical_iff_quotient_reduced]
  change ((vanishingIdeal Z).ideal U).IsRadical
  rw [vanishingIdeal_ideal]
  exact PrimeSpectrum.isRadical_vanishingIdeal _

theorem pointLocation_in_closure_iff {X : SchemeOver ℂ} (S : Set (Points X complexAlgebra))
    (p : Points X complexAlgebra) :
    pointLocation p ∈ closure (pointLocation '' S) ↔
      ∃ q : Points (reducedClosureScheme X S) complexAlgebra,
        q ≫ reducedClosureInclusion X S = p := by
  let J := reducedClosureIdeal X S
  let f := reducedClosureInclusion X S
  have hf : IsClosedImmersion f.left := by change IsClosedImmersion J.subschemeι; infer_instance
  have hS : (J.support : Set X.left) = closure (pointLocation '' S) :=
    coe_support_vanishingIdeal _
  constructor
  · intro hp
    have hker : f.left.ker ≤ p.left.ker := by
      change J.subschemeι.ker ≤ p.left.ker
      rw [ker_subschemeι]
      have he : p.left.ker = vanishingIdeal (Closeds.closure {pointLocation p}) := by
        have : IsReduced ((testSpec ℂ).obj (op complexAlgebra)).left := by
          change IsReduced (Spec (CommRingCat.of ℂ))
          infer_instance
        rw [← map_bot p.left, ← Scheme.nilradical_eq_bot, ← vanishingIdeal_top,
          map_vanishingIdeal]
        congr 2
        rw [Closeds.coe_top, Set.image_univ, pointLocation_range]
      rw [he]
      apply vanishingIdeal_antimono
      apply Closeds.closure_le.mpr
      exact Set.singleton_subset_iff.mpr hp
    let q : Points (reducedClosureScheme X S) complexAlgebra :=
      Over.homMk (IsClosedImmersion.lift f.left p.left hker) (by
        rw [← Over.w f, ← Category.assoc, IsClosedImmersion.lift_fac, Over.w])
    exact ⟨q, Over.OverMorphism.ext (IsClosedImmersion.lift_fac f.left p.left hker)⟩
  · rintro ⟨q, rfl⟩
    rw [pointLocation_comp, ← hS, ← range_subschemeι]
    exact Set.mem_range_self (pointLocation q)

end ReducedClosure

section Stability

variable {V ι : Type} [AddCommGroup V] [Module ℂ V] [Fintype ι] [DecidableEq ι]

set_option backward.isDefEq.respectTransparency false in
theorem stable_iff_mem_support (b : Module.Basis ι ℂ V) {d : ℕ} (hd : d ≤ Module.finrank ℂ V)
    (T : V →ₗ[ℂ] V) (p : GrassmannianPoints b hd) :
    StablePlane b hd T p ↔
      pointLocation p ∈ closure (pointLocation '' {q | StablePlane b hd T q}) := by
  obtain ⟨I, A, rfl⟩ := grassmannianChartPoint_cover b hd p
  let C := grassmannianCharts b hd
  let J := reducedClosureIdeal C.scheme {q | StablePlane b hd T q}
  have hS : (J.support : Set C.scheme.left) = closure (pointLocation '' {q | StablePlane b hd T q}) :=
    coe_support_vanishingIdeal _
  rw [← hS, grassmannianChartPoint, pointLocation_comp]
  change StablePlane b hd T (grassmannianChartPoint b hd I A) ↔
    pointLocation ((chartMatrixEquiv I complexAlgebra).symm A) ∈
    (chartInclusion b hd I) ⁻¹' (J.support : Set C.scheme.left)
  rw [stable_chart_support b hd T I, chart_location,
    stablePlane_chart_iff b hd T I A, ← chartVariables_mem_zeroLocus]
  change _ ↔ ∀ f ∈ stabilityIdeal I (operatorInCoordinates b T),
    f ∈ MvPolynomial.vanishingIdeal ℂ {chartVariables I A}
  simp only [MvPolynomial.mem_vanishingIdeal_singleton_iff]
  rfl

/-- The stable-complex-point topology is the subspace topology in the Grassmannian.
The underlying points agree with morphisms to the reduced scheme. -/
def stableSchemePoints (b : Module.Basis ι ℂ V) {d : ℕ} (hd : d ≤ Module.finrank ℂ V)
    (T : V →ₗ[ℂ] V) :
    Points (stableScheme b hd T) complexAlgebra ≃ StablePoints b hd T := by
  let X := (grassmannianCharts b hd).scheme
  let S : Set (Points X complexAlgebra) := {p | StablePlane b hd T p}
  let f := reducedClosureInclusion X S
  have hf : IsClosedImmersion f.left := by
    change IsClosedImmersion (reducedClosureIdeal X S).subschemeι
    infer_instance
  refine Equiv.ofBijective (fun q ↦ ⟨q ≫ f, (stable_iff_mem_support b hd T _).mpr
    ((pointLocation_in_closure_iff S _).mpr ⟨q, rfl⟩)⟩) ⟨?_, ?_⟩
  · intro q q' h
    apply Over.OverMorphism.ext
    apply (cancel_mono f.left).mp
    exact congrArg (fun p : Points X complexAlgebra ↦ p.left) (congrArg Subtype.val h)
  · intro p
    obtain ⟨q, hq⟩ := (pointLocation_in_closure_iff S p.val).mp
      ((stable_iff_mem_support b hd T p.val).mp p.property)
    exact ⟨q, Subtype.ext hq⟩

theorem isClosed_stablePlanes (b : Module.Basis ι ℂ V) {d : ℕ} (hd : d ≤ Module.finrank ℂ V)
    (T : V →ₗ[ℂ] V) : IsClosed {p | StablePlane b hd T p} := by
  change @IsClosed (GrassmannianPoints b hd)
    (⨆ I : Pivot ι d, TopologicalSpace.coinduced
      (grassmannianChartPoint b hd I) inferInstance) {p | StablePlane b hd T p}
  rw [isClosed_iSup_iff]
  intro I
  rw [isClosed_coinduced]
  have hset : (grassmannianChartPoint b hd I) ⁻¹' {p | StablePlane b hd T p} =
      ⋂ ji : Outside I × Inside I, {A | MvPolynomial.eval (chartVariables I A)
        (graphPolynomial I (operatorInCoordinates b T) ji.1 ji.2) = 0} := by
    ext A
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, stablePlane_chart_iff, Set.mem_iInter,
      ← MvPolynomial.aeval_eq_eval, graphPolynomial_eval]
    constructor
    · intro h ji
      simp [h]
    · intro h
      ext j i
      exact h (j,i)
  rw [hset]
  apply isClosed_iInter
  intro ji
  apply isClosed_eq _ continuous_const
  exact (MvPolynomial.continuous_eval _).comp (continuous_pi fun x ↦
    (continuous_apply x.2).comp (continuous_apply x.1))

end Stability

section Schubert

theorem schubertOrbit_stable (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (d : WindowDimension 2 (-(N : ℤ)) (2*N)) :
    schubertOrbitPoints ab N hN d ⊆
      {p | StablePlane (windowBasis 2 (-(N : ℤ)) (2*N)) (windowDimension_le d)
        (windowOperator 2 (-(N : ℤ)) (2*N)) p} := by
  rintro p ⟨L, hL, h⟩
  change StablePlane _ _ _ p
  unfold StablePlane
  rw [h]
  exact latticeSubspace_stable _ _ L

/-- The orbit closure is a closed subscheme of the reduced stability locus. -/
def schubertInclusion (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (d : WindowDimension 2 (-(N : ℤ)) (2*N)) :
    schubertScheme ab N hN d ⟶ windowStableScheme 2 (-(N : ℤ)) (2*N) d := by
  let b := windowBasis 2 (-(N : ℤ)) (2*N)
  let X := (grassmannianCharts b (windowDimension_le d)).scheme
  let S : Set (Points X complexAlgebra) :=
    {p | StablePlane b (windowDimension_le d) (windowOperator 2 (-(N : ℤ)) (2*N)) p}
  let J := reducedClosureIdeal X S
  let I := reducedClosureIdeal X (schubertOrbitPoints ab N hN d)
  have h : J ≤ I := vanishingIdeal_antimono
    (closure_mono (Set.image_mono (schubertOrbit_stable ab N hN d)))
  refine Over.homMk (Scheme.IdealSheafData.inclusion h) ?_
  change _ ≫ (J.subschemeι ≫ X.hom) = I.subschemeι ≫ X.hom
  rw [← Category.assoc, inclusion_subschemeι]

private theorem inclusion_closed {X : Scheme} {I J : X.IdealSheafData} (h : I ≤ J) :
    IsClosedImmersion (Scheme.IdealSheafData.inclusion h) := by
  have : IsClosedImmersion (Scheme.IdealSheafData.inclusion h ≫ I.subschemeι) := by
    rw [inclusion_subschemeι]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ I.subschemeι

theorem schubertScheme_closed (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (d : WindowDimension 2 (-(N : ℤ)) (2*N)) :
    IsClosedImmersion (schubertInclusion ab N hN d).left := by
  dsimp [schubertInclusion]
  exact inclusion_closed _

def schubertSchemePoints (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (d : WindowDimension 2 (-(N : ℤ)) (2*N)) :
    Points (schubertScheme ab N hN d) complexAlgebra ≃ SchubertPoints ab N hN d := by
  let X := (grassmannianCharts (windowBasis 2 (-(N : ℤ)) (2*N)) (windowDimension_le d)).scheme
  let S := schubertOrbitPoints ab N hN d
  let f := reducedClosureInclusion X S
  have hf : IsClosedImmersion f.left := by
    change IsClosedImmersion (reducedClosureIdeal X S).subschemeι
    infer_instance
  refine Equiv.ofBijective
    (fun q ↦ ⟨q ≫ f, (pointLocation_in_closure_iff S _).mpr ⟨q, rfl⟩⟩) ⟨?_, ?_⟩
  · intro q q' h
    apply Over.OverMorphism.ext
    apply (cancel_mono f.left).mp
    exact congrArg (fun p : Points X complexAlgebra ↦ p.left) (congrArg Subtype.val h)
  · intro p
    obtain ⟨q, hq⟩ := (pointLocation_in_closure_iff S p.val).mp p.property
    exact ⟨q, Subtype.ext hq⟩

end Schubert

theorem twistedProduct_eq {Γ X : Type*} [Group Γ] [MulAction Γ X] (H : Subgroup Γ)
    {A : Set (Grassmannian H)} {S : Set X} (hS : StableStage H S)
    (p q : Representatives H A S) :
    (Quotient.mk (twistRel H A S) p : TwistedProduct H A S hS) =
      Quotient.mk (twistRel H A S) q ↔
        ∃ h : H, q.val.1 = p.val.1 * (h : Γ) ∧ p.val.2 = (h : Γ) • q.val.2 := by
  rw [Quotient.eq]
  change (∃ h : H, q.val.1 = p.val.1 * (h : Γ) ∧
    q.val.2 = ((h⁻¹ : H) : Γ) • p.val.2) ↔ _
  constructor
  · rintro ⟨h, h₁, h₂⟩
    exact ⟨h, h₁, by rw [h₂]; simp [smul_smul]⟩
  · rintro ⟨h, h₁, h₂⟩
    exact ⟨h, h₁, by rw [h₂]; simp [smul_smul]⟩

section AffineComparison

open CategoryTheory.Limits

private theorem reduced_ker_eq {X Y : Scheme} [IsReduced X] (f : X ⟶ Y) :
    f.ker = vanishingIdeal (Closeds.closure (Set.range f)) := by
  rw [← map_bot f, ← Scheme.nilradical_eq_bot, ← vanishingIdeal_top,
    map_vanishingIdeal, Closeds.coe_top, Set.image_univ]

set_option backward.isDefEq.respectTransparency false in
theorem stableAffinePresentation {V ι : Type} [AddCommGroup V] [Module ℂ V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ V) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ V) (T : V →ₗ[ℂ] V) (I : Pivot ι d) :
    StableAffineChart b hd T I := by
  let X := (grassmannianCharts b hd).scheme
  let S : Set (Points X complexAlgebra) := {p | StablePlane b hd T p}
  let J := reducedClosureIdeal X S
  let f := chartInclusion b hd I
  let A := chartAlgebra (k := ℂ) I
  let R := reducedStabilityIdeal I (operatorInCoordinates b T)
  let q : Spec (CommRingCat.of (A ⧸ R)) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk R))
  let P := pullback f J.subschemeι
  let g : P ⟶ Spec (CommRingCat.of A) := pullback.fst f J.subschemeι
  have : IsOpenImmersion f := (grassmannianCharts b hd).openChart I
  have : IsClosedImmersion g := by dsimp [g, P]; infer_instance
  have : IsClosedImmersion q := by
    dsimp [q]
    apply IsClosedImmersion.spec_of_surjective
    exact Ideal.Quotient.mk_surjective
  have : IsReduced J.subscheme := reducedClosure_reduced X S
  have : IsReduced P := isReduced_of_isOpenImmersion (pullback.snd f J.subschemeι)
  have : _root_.IsReduced (A ⧸ R) :=
    (Ideal.isRadical_iff_quotient_reduced R).mp (Ideal.radical_isRadical _)
  have : IsReduced (Spec (CommRingCat.of (A ⧸ R))) := inferInstance
  have hg : (g.ker.support : Set (Spec (CommRingCat.of A))) = PrimeSpectrum.zeroLocus (R : Set A) := by
    change ((J.comap f).support : Set (Spec (CommRingCat.of A))) = _
    rw [support_comap]
    change (chartInclusion b hd I) ⁻¹' (J.support : Set X.left) = _
    rw [stable_chart_support b hd T I]
    exact (PrimeSpectrum.zeroLocus_radical _).symm
  have hq : (q.ker.support : Set (Spec (CommRingCat.of A))) = PrimeSpectrum.zeroLocus (R : Set A) := by
    rw [Scheme.Hom.support_ker]
    change closure (Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk R))) = _
    rw [PrimeSpectrum.closure_range_comap, Ideal.mk_ker]
  have h : g.ker = q.ker := by
    rw [reduced_ker_eq g, reduced_ker_eq q]
    congr 1
    apply SetLike.coe_injective
    change closure (Set.range g) = closure (Set.range q)
    rw [← Scheme.Hom.support_ker g, ← Scheme.Hom.support_ker q]
    exact hg.trans hq.symm
  let u := IsClosedImmersion.lift q g h.ge
  have hu : u ≫ q = g := IsClosedImmersion.lift_fac q g h.ge
  have : IsIso u := IsClosedImmersion.isIso_of_ker_eq g q u hu h
  exact ⟨asIso u, hu⟩

end AffineComparison


theorem stableSchemePointComparison : StableSchemePointComparison := by
  intro V ι _ _ _ _ b d hd T
  exact ⟨stableSchemePoints b hd T, fun _ ↦ rfl⟩

theorem schubertClosureComparison : SchubertClosureComparison := by
  intro ab N hN d
  exact ⟨⟨schubertInclusion ab N hN d, schubertScheme_closed ab N hN d⟩,
    ⟨schubertSchemePoints ab N hN d, fun _ ↦ rfl⟩⟩

-- The shared definitions are imported from the independent specification.
abbrev O := @LatticeModelSpecs.O
abbrev K := @LatticeModelSpecs.K
abbrev t := @LatticeModelSpecs.t
abbrev inclusion := @LatticeModelSpecs.inclusion
abbrev monomial := @LatticeModelSpecs.monomial
abbrev Coordinates := @LatticeModelSpecs.Coordinates
abbrev Lattice := @LatticeModelSpecs.Lattice
abbrev GL2Lattice := @LatticeModelSpecs.GL2Lattice
abbrev TorusLattice := @LatticeModelSpecs.TorusLattice
abbrev Coweight := @LatticeModelSpecs.Coweight
abbrev coordinateInclusion := @LatticeModelSpecs.coordinateInclusion
abbrev standardLattice := @LatticeModelSpecs.standardLattice
abbrev loopLinearEquiv := @LatticeModelSpecs.loopLinearEquiv
abbrev latticeAction := @LatticeModelSpecs.latticeAction
abbrev torusAction := @LatticeModelSpecs.torusAction
abbrev diagonalLoop := @LatticeModelSpecs.diagonalLoop
abbrev diagonalLattice := @LatticeModelSpecs.diagonalLattice
abbrev torusMonomial := @LatticeModelSpecs.torusMonomial
abbrev torusLatticeAt := @LatticeModelSpecs.torusLatticeAt
abbrev scalarLattice := @LatticeModelSpecs.scalarLattice
abbrev positiveGLMap := @LatticeModelSpecs.positiveGLMap
abbrev positiveTorusMap := @LatticeModelSpecs.positiveTorusMap
abbrev PositiveGL := @LatticeModelSpecs.PositiveGL
abbrev PositiveTorus := @LatticeModelSpecs.PositiveTorus
abbrev Grassmannian := @LatticeModelSpecs.Grassmannian
abbrev coset := @LatticeModelSpecs.coset
abbrev StableStage := @LatticeModelSpecs.StableStage
abbrev Representatives := @LatticeModelSpecs.Representatives
abbrev twistRel := @LatticeModelSpecs.twistRel
abbrev TwistedProduct := @LatticeModelSpecs.TwistedProduct
abbrev firstProjection := @LatticeModelSpecs.firstProjection
abbrev terminalMap := @LatticeModelSpecs.terminalMap
abbrev BoundedLattice := @LatticeModelSpecs.BoundedLattice
abbrev BoundedTorus := @LatticeModelSpecs.BoundedTorus
abbrev Window := @LatticeModelSpecs.Window
abbrev BoundedWindow := @LatticeModelSpecs.BoundedWindow
abbrev windowOperator := @LatticeModelSpecs.windowOperator
abbrev latticeSubspace := @LatticeModelSpecs.latticeSubspace
abbrev boundedSubspace := @LatticeModelSpecs.boundedSubspace
abbrev windowCoordinates := @LatticeModelSpecs.windowCoordinates
abbrev windowBasis := @LatticeModelSpecs.windowBasis
abbrev JetRing := @LatticeModelSpecs.JetRing
abbrev jetReduction := @LatticeModelSpecs.jetReduction
abbrev jetCoefficients := @LatticeModelSpecs.jetCoefficients
abbrev jetTopology := @LatticeModelSpecs.jetTopology
abbrev GLJets := @LatticeModelSpecs.GLJets
abbrev TorusJets := @LatticeModelSpecs.TorusJets
abbrev reduceGL := @LatticeModelSpecs.reduceGL
abbrev reduceTorus := @LatticeModelSpecs.reduceTorus
abbrev glJetTopology := @LatticeModelSpecs.glJetTopology
abbrev torusJetTopology := @LatticeModelSpecs.torusJetTopology
abbrev grassmannianCharts := @LatticeModelSpecs.grassmannianCharts
abbrev grassmannianFamilies := @LatticeModelSpecs.grassmannianFamilies
abbrev GrassmannianPoints := @LatticeModelSpecs.GrassmannianPoints
abbrev grassmannianChartPoint := @LatticeModelSpecs.grassmannianChartPoint
abbrev grassmannianAnalyticTopology := @LatticeModelSpecs.grassmannianAnalyticTopology
abbrev grassmannianSubspace := @LatticeModelSpecs.grassmannianSubspace
abbrev graphMatrix := @LatticeModelSpecs.graphMatrix
abbrev graphResidual := @LatticeModelSpecs.graphResidual
abbrev stabilityIdeal := @LatticeModelSpecs.stabilityIdeal
abbrev reducedStabilityIdeal := @LatticeModelSpecs.reducedStabilityIdeal
abbrev StablePlane := @LatticeModelSpecs.StablePlane
abbrev StablePoints := @LatticeModelSpecs.StablePoints
abbrev stableScheme := @LatticeModelSpecs.stableScheme
abbrev windowStableScheme := @LatticeModelSpecs.windowStableScheme
abbrev WindowStage := @LatticeModelSpecs.WindowStage
abbrev boundedPoint := @LatticeModelSpecs.boundedPoint
abbrev boundedAnalyticTopology := @LatticeModelSpecs.boundedAnalyticTopology
abbrev boundedInclusion := @LatticeModelSpecs.boundedInclusion
abbrev latticeAnalyticTopology := @LatticeModelSpecs.latticeAnalyticTopology
abbrev torusAnalyticTopology := @LatticeModelSpecs.torusAnalyticTopology
abbrev torusStageScheme := @LatticeModelSpecs.torusStageScheme
abbrev DominantPair := @LatticeModelSpecs.DominantPair
abbrev pairCoweight := @LatticeModelSpecs.pairCoweight
abbrev gl2Orbit := @LatticeModelSpecs.gl2Orbit
abbrev OrbitBound := @LatticeModelSpecs.OrbitBound
abbrev schubertOrbitPoints := @LatticeModelSpecs.schubertOrbitPoints
abbrev schubertScheme := @LatticeModelSpecs.schubertScheme
abbrev SchubertPoints := @LatticeModelSpecs.SchubertPoints

end
end RepTheorySurvey.Geometric.LatticeModels
