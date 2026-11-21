import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.TopologicalKunneth
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SingularChains
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.EilenbergZilber
import MathGenome.Internal.AlgebraCore.P103.Ch11.KunnethFreeSplitting
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! The natural split topological Künneth sequence over a PID.
The algebraic sequence is transported through the actual singular-chain and
oriented-shuffle comparisons. The final theorem closes the auxiliary derivation
using the upstream Eilenberg--Zilber proofs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000
open CategoryTheory
open scoped TensorProduct DirectSum
namespace P202.TopologicalKunneth
open P202Specs.SingularChains P202Specs.AlexanderWhitney
open P103.Specs.Ch11.TorBalance P103.Specs.Ch11.KunnethSequence
open P103.Specs.Ch11.ExtTorDefinitions
universe u w
variable (R : Type u) [CommRing R]

/-- The first singular complex, with the canonical commutative right action. -/
abbrev rightSingular (X : TopCat.{w}) := commRightOrdinaryComplex (complex R R X)

/-- Finite support, rather than finite rank, supplies the free singular basis. -/
theorem singular_terms_free (X : TopCat.{w}) (n : ℕ) :
    Module.Free R ((complex R R X).X n) := by
  change Module.Free R (Chains R X n)
  infer_instance

/-- Scalar transport along R ≃ Rᵐᵒᵖ preserves freeness in arbitrary rank. -/
theorem right_singular_terms_free (X : TopCat.{w}) (n : ℕ) :
    Module.Free Rᵐᵒᵖ ((rightSingular R X).X n) := by
  letI := singular_terms_free R X n
  letI : Module Rᵐᵒᵖ ((complex R R X).X n) :=
    P103.BalancedTensor.commRightModule R ((complex R R X).X n)
  let σ : R →+* Rᵐᵒᵖ := (RingEquiv.toOpposite R).toRingHom
  let σ' : Rᵐᵒᵖ →+* R := (RingEquiv.toOpposite R).symm.toRingHom
  letI : RingHomInvPair σ σ' := RingHomInvPair.of_ringEquiv (RingEquiv.toOpposite R)
  letI : RingHomInvPair σ' σ := RingHomInvPair.of_ringEquiv (RingEquiv.toOpposite R).symm
  let e : LinearEquiv σ (σ' := σ') ((complex R R X).X n)
      ((rightSingular R X).X n) :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun (r : R) (x : (complex R R X).X n) => by
        change r • x = MulOpposite.op r • (x : (rightSingular R X).X n)
        rfl }
  exact Module.Free.of_equiv e

/-- Lemma 11.7 of P103 applies to the actual singular boundary submodule. -/
theorem singular_boundaries_free [IsDomain R] [IsPrincipalIdealRing R]
    (X : TopCat.{w}) (n : ℕ) :
    Module.Free R (P103.Specs.Ch10.Complexes.boundaries (complex R R X) n) := by
  letI := singular_terms_free R X n
  exact P103.Ch11.ArbitraryRankPIDSubmodules.free_submodule R _ _

/-- The exact right-flatness tests required by P103, at the full simplex universe. -/
theorem right_singular_flat [IsDomain R] [IsPrincipalIdealRing R]
    (X : TopCat.{w}) :
    P103.Specs.Ch11.UniversalCoefficientsHomology.FlatTermsAndBoundaries.{u,max u w,max u w} (rightSingular R X) :=
  P103.Ch11.KunnethFreeSplitting.free_flat_terms_boundaries
    (rightSingular R X) (right_singular_terms_free R X)

/-- The normalized algebraic sequence exists for the actual two singular
complexes. Its first arrow has P103's elementary cycle-class formula. -/
theorem algebraic_sequence [IsDomain R] [IsPrincipalIdealRing R]
    (X Y : TopCat.{w}) (P : HomologyModels (rightSingular R X)) (n : ℕ) :
    Nonempty (NormalizedDegreeSequence (rightSingular R X) (complex R R Y) P n) :=
  P103.Ch11.KunnethSequence.right_sequence R (rightSingular R X)
    (right_singular_flat R X) (complex R R Y) P n

/-- The actual normalized surjection admits an R-linear section, using the
coefficient actions supplied by P103, with no claim of a natural section. -/
theorem algebraic_scalar_splitting [IsDomain R] [IsPrincipalIdealRing R]
    (X Y : TopCat.{w}) (P : HomologyModels (rightSingular R X)) (n : ℕ)
    (T : TorMaps.{u,max u w,max u w} R 1)
    (S : NormalizedDegreeSequence (rightSingular R X) (complex R R Y) P n) :
    P103.Specs.Ch11.KunnethFreeSplitting.ScalarSplits S.toDegreeSequence T :=
  (P103.Ch11.KunnethFreeSplitting.scalar_splitting R
    (rightSingular R X) (complex R R Y)
    (right_singular_terms_free R X) (singular_terms_free R Y) P n T).2 S

/-- The algebraic Tor tail has no negative-index artefact at n=0. -/
theorem algebraic_tor_zero (X Y : TopCat.{w})
    (P : HomologyModels (rightSingular R X)) :
    Subsingleton (TorDiagonal (rightSingular R X) (complex R R Y) P 0) :=
  P103.Ch11.KunnethSequence.tor_diagonal_zero R (rightSingular R X) (complex R R Y) P

/-- The original Tor tail is also zero at n=0, independently of any sequence. -/
theorem tor_zero (P : P202Specs.TopologicalKunneth.Models.{u,w} R)
    (T : TorMaps.{u,max u w,max u w} R 1) (X Y : TopCat.{w}) :
    Subsingleton (P202Specs.TopologicalKunneth.TorSum R P T X Y 0) := by
  letI : IsEmpty (P202Specs.TopologicalKunneth.TailDiagonal 0) :=
    ⟨fun i => by have := i.property; omega⟩
  unfold P202Specs.TopologicalKunneth.TorSum
  infer_instance

section TotalCoordinates
open P103.Ch11.FlatResolutions P103.Ch11.KunnethFlatColumns

/-- P103's balanced quotient is canonically the ordinary R-tensor product. -/
def balancedChainEquiv (X Y : TopCat.{w}) (p q : ℕ) :
    P103.BalancedTensor.Tensor R ((rightSingular R X).X p) ((complex R R Y).X q)
      ≃ₗ[ℤ] Summand R X Y p q := by
  letI opModule : Module Rᵐᵒᵖ (Chains R X p) := P103.BalancedTensor.commRightModule R _
  letI : SMul Rᵐᵒᵖ (Chains R X p) := opModule.toSMul
  letI : IsCentralScalar R (Chains R X p) :=
    ⟨fun (r : R) (a : Chains R X p) => rfl⟩
  exact (P103.BalancedTensor.commAddEquiv
    (K := R) (A := Chains R X p) (B := Chains R Y q)).toIntLinearEquiv

@[simp] theorem balancedChainEquiv_tmul (X Y : TopCat.{w}) (p q : ℕ)
    (a : Chains R X p) (b : Chains R Y q) :
    balancedChainEquiv R X Y p q (P103.BalancedTensor.tmul R a b) = a ⊗ₜ[R] b := rfl

/-- Coordinates on the actual algebraic total, including inverse reconstruction.
The indexing diagonal is finite; the modules can have arbitrary rank. -/
def algebraicTotalCoordinates (X Y : TopCat.{w}) (n : ℕ) :
    (ordinaryTotal (rightSingular R X) (complex R R Y)).X n ≃ₗ[ℤ] Total R X Y n where
  toFun z i := balancedChainEquiv R X Y i.val.1 i.val.2
    (ordinaryProjection (rightSingular R X) (complex R R Y) i.val.1 i.val.2 n i.property z)
  invFun z := ∑ i : P202Specs.AlexanderWhitney.Diagonal n,
    ordinaryInclusion (rightSingular R X) (complex R R Y) i.val.1 i.val.2 n i.property
      ((balancedChainEquiv R X Y i.val.1 i.val.2).symm (z i))
  left_inv z := by
    simpa only [LinearEquiv.symm_apply_apply] using
      ordinary_reconstruction (rightSingular R X) (complex R R Y) n z
  right_inv z := by
    classical
    funext i
    simp only [map_sum]
    rw [Finset.sum_eq_single i]
    · rw [ordinaryProjection_inclusion, LinearEquiv.apply_symm_apply]
    · intro j _ hji
      have hne : j.val.1 ≠ i.val.1 ∨ j.val.2 ≠ i.val.2 := by
        by_contra! h
        exact hji (Subtype.ext (Prod.ext h.1 h.2))
      rw [ordinaryProjection_inclusion_ne _ _ _ _ _ _ _ _ _ hne, map_zero]
    · simp
  map_add' a b := by funext i; rw [map_add, map_add]; rfl
  map_smul' r a := by
    funext i
    exact ((balancedChainEquiv R X Y i.val.1 i.val.2).toLinearMap.comp
      (ordinaryProjection (rightSingular R X) (complex R R Y) i.val.1 i.val.2 n i.property)).map_smul r a

theorem balancedChainEquiv_leftBoundary (X Y : TopCat.{w}) (p q : ℕ)
    (t : P103.BalancedTensor.Tensor R ((rightSingular R X).X (p+1)) ((complex R R Y).X q)) :
    balancedChainEquiv R X Y p q
      (tensorMap ((rightSingular R X).d (p+1) p).hom LinearMap.id t) =
      leftBoundary R X Y p q (balancedChainEquiv R X Y (p+1) q t) := by
  induction t using P103.BalancedTensor.induction_on with
  | h0 => simp only [map_zero]
  | ht a b => rfl
  | ha a b ha hb => simp only [map_add, ha, hb]

theorem balancedChainEquiv_rightBoundary (X Y : TopCat.{w}) (p q : ℕ)
    (t : P103.BalancedTensor.Tensor R ((rightSingular R X).X p) ((complex R R Y).X (q+1))) :
    balancedChainEquiv R X Y p q
      (tensorMap LinearMap.id ((complex R R Y).d (q+1) q).hom t) =
      rightBoundary R X Y p q (balancedChainEquiv R X Y p (q+1) t) := by
  induction t using P103.BalancedTensor.induction_on with
  | h0 => simp only [map_zero]
  | ht a b => rfl
  | ha a b ha hb => simp only [map_add, ha, hb]

/-- The coordinates commute with the signed boundary, including the degree-zero
endpoint. This identifies the actual complexes, not only their graded terms. -/
theorem algebraicTotalCoordinates_boundary (X Y : TopCat.{w}) (n : ℕ)
    (z : (ordinaryTotal (rightSingular R X) (complex R R Y)).X (n+1)) :
    algebraicTotalCoordinates R X Y n
        (((ordinaryTotal (rightSingular R X) (complex R R Y)).d (n+1) n).hom z) =
      totalBoundary R X Y n (algebraicTotalCoordinates R X Y (n+1) z) := by
  funext i
  have hd := LinearMap.congr_fun
    (ordinaryProjection_d (rightSingular R X) (complex R R Y)
      i.val.1 i.val.2 n i.property) z
  dsimp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply] at hd
  change balancedChainEquiv R X Y i.val.1 i.val.2 _ = _
  rw [hd, map_add, Units.smul_def, map_zsmul, Int.coe_negOnePow_natCast]
  change _ = leftBoundary R X Y i.val.1 i.val.2
      (balancedChainEquiv R X Y (i.val.1+1) i.val.2 _) +
    (-1 : ℤ)^i.val.1 • rightBoundary R X Y i.val.1 i.val.2
      (balancedChainEquiv R X Y i.val.1 (i.val.2+1) _)
  rw [balancedChainEquiv_leftBoundary, balancedChainEquiv_rightBoundary]

/-- Coordinate comparison is natural before passing to homology. -/
theorem algebraicTotalCoordinates_natural
    {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ)
    (z : (ordinaryTotal (rightSingular R X) (complex R R Y)).X n) :
    algebraicTotalCoordinates R X' Y' n
        (((ordinaryTotalMap (commRightOrdinaryMap (chainMap R R f))
          (chainMap R R g)).f n).hom z) =
      totalMap R f g n (algebraicTotalCoordinates R X Y n z) := by
  funext i
  change balancedChainEquiv R X' Y' i.val.1 i.val.2 _ = _
  rw [P103.Ch11.KunnethTotalConnector.projection_totalMap]
  change balancedChainEquiv R X' Y' i.val.1 i.val.2
      (tensorMap _ _ (ordinaryProjection _ _ _ _ _ _ z)) =
    TensorProduct.map _ _ (balancedChainEquiv R X Y i.val.1 i.val.2
      (ordinaryProjection _ _ _ _ _ _ z))
  generalize ordinaryProjection (rightSingular R X) (complex R R Y)
    i.val.1 i.val.2 n i.property z = t
  induction t using P103.BalancedTensor.induction_on with
  | h0 => simp only [map_zero]
  | ht a b => rfl
  | ha a b ha hb => simp only [map_add, ha, hb]

/-- The shared tensor differential, forgetting scalars to integers. -/
def integerTensorComplex (X Y : TopCat.{w}) : ChainComplex (ModuleCat.{max u w} ℤ) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of ℤ (Total R X Y n))
    (fun n => ModuleCat.ofHom ((totalBoundary R X Y n).restrictScalars ℤ)) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact LinearMap.congr_fun (totalBoundary_square R X Y n) z)

/-- A genuine natural chain isomorphism from P103's signed total to the shared
finite-diagonal tensor complex, after forgetting coefficients to integers. -/
def algebraicTotalIso (X Y : TopCat.{w}) :
    ordinaryTotal (rightSingular R X) (complex R R Y) ≅ integerTensorComplex R X Y :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (algebraicTotalCoordinates R X Y n).toModuleIso) (by
      intro n m h
      change m + 1 = n at h
      subst n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      simpa [integerTensorComplex] using
        (algebraicTotalCoordinates_boundary R X Y m z).symm)

/-- The coefficient endomorphism on P103's total becomes the actual R action
in tensor coordinates, in every degree and at arbitrary rank. -/
theorem algebraicTotalCoordinates_scalar (X Y : TopCat.{w}) (n : ℕ) (r : R)
    (z : (ordinaryTotal (rightSingular R X) (complex R R Y)).X n) :
    algebraicTotalCoordinates R X Y n
      (((ordinaryTotalMap (𝟙 (rightSingular R X))
        (P103.Specs.Ch11.KunnethFreeSplitting.scalarChainMap (complex R R Y) r)).f n).hom z) =
      r • algebraicTotalCoordinates R X Y n z := by
  funext i
  change balancedChainEquiv R X Y i.val.1 i.val.2 _ = _
  rw [P103.Ch11.KunnethTotalConnector.projection_totalMap]
  change balancedChainEquiv R X Y i.val.1 i.val.2
    (tensorMap LinearMap.id (scalarMap ((complex R R Y).X i.val.2) r).hom
      (ordinaryProjection _ _ _ _ _ _ z)) =
      r • balancedChainEquiv R X Y i.val.1 i.val.2
        (ordinaryProjection _ _ _ _ _ _ z)
  generalize ordinaryProjection (rightSingular R X) (complex R R Y)
    i.val.1 i.val.2 n i.property z = t
  induction t using P103.BalancedTensor.induction_on with
  | h0 => simp only [map_zero, smul_zero]
  | ht a b =>
    let a' : Chains R X i.val.1 := a
    let b' : Chains R Y i.val.2 := b
    exact TensorProduct.tmul_smul r a' b'
  | ha a b ha hb => simp only [map_add, ha, hb, smul_add]


/-- The algebraic total's elementary inclusion is the same single bidegree
in the shared tensor coordinates, with the original chain coefficients. -/
theorem algebraicTotalCoordinates_inclusion (X Y : TopCat.{w}) (p q : ℕ)
    (a : Chains R X p) (b : Chains R Y q) :
    algebraicTotalCoordinates R X Y (p+q)
      (ordinaryInclusion (rightSingular R X) (complex R R Y) p q (p+q) rfl
        (P103.BalancedTensor.tmul R a b)) =
      LinearMap.single R
        (fun i : P202Specs.AlexanderWhitney.Diagonal (p+q) => Summand R X Y i.val.1 i.val.2)
        ⟨(p,q),rfl⟩ (a ⊗ₜ[R] b) := by
  classical
  funext i
  by_cases hi : i = (⟨(p,q),rfl⟩ : P202Specs.AlexanderWhitney.Diagonal (p+q))
  · subst i
    change balancedChainEquiv R X Y p q _ = _
    rw [P103.Ch11.FlatResolutions.ordinaryProjection_inclusion]
    simp only [balancedChainEquiv_tmul, LinearMap.single_apply, Pi.single_eq_same]
  · have hne : p ≠ i.val.1 ∨ q ≠ i.val.2 := by
      by_contra! h
      exact hi (Subtype.ext (Prod.ext h.1.symm h.2.symm))
    change balancedChainEquiv R X Y i.val.1 i.val.2 _ = _
    rw [P103.Ch11.FlatResolutions.ordinaryProjection_inclusion_ne _ _ _ _ _ _ _ _ _ hne]
    simp only [map_zero, LinearMap.single_apply, Pi.single_eq_of_ne hi]

end TotalCoordinates

section QuotientHomology
universe v
variable (C : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)

/-- Concrete and categorical cycles of the same complex agree canonically. -/
def quotientCyclesEquiv :
    P103.Specs.Ch10.Complexes.cycles C n ≃ₗ[R] C.cycles n :=
  (C.sc n).moduleCatCyclesIso.toLinearEquiv.symm

private theorem range_toCycles_eq :
    LinearMap.range (C.sc n).moduleCatToCycles =
      P103.Specs.Ch10.Complexes.cycleBoundaries C n := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩

/-- Explicit bridge from P103's quotient homology to the categorical homology
used by singular chains and the prescribed shuffle external product. -/
def quotientHomologyEquiv :
    P103.Specs.Ch10.Complexes.Homology C n ≃ₗ[R] C.homology n :=
  (Submodule.quotEquivOfEq _ _ (range_toCycles_eq R C n).symm).trans
    (C.sc n).moduleCatHomologyIso.toLinearEquiv.symm

/-- The bridge sends a quotient cycle class to the class of the same cycle. -/
theorem quotientHomologyEquiv_class (z : P103.Specs.Ch10.Complexes.cycles C n) :
    quotientHomologyEquiv R C n (P103.Specs.Ch10.Complexes.homologyClass C n z) =
      C.homologyπ n (quotientCyclesEquiv R C n z) := by
  exact (congrArg (fun f => f.hom z) (C.sc n).moduleCatCyclesIso_inv_π).symm

/-- Under the cycle bridge the actual chain representative is unchanged. -/
theorem quotientCyclesEquiv_val (z : P103.Specs.Ch10.Complexes.cycles C n) :
    C.iCycles n (quotientCyclesEquiv R C n z) = z.val :=
  congrArg (fun f => f.hom z) (C.sc n).moduleCatCyclesIso_inv_iCycles

/-- The concrete quotient bridge is natural for actual chain maps. -/
theorem quotientHomologyEquiv_natural
    {D : ChainComplex (ModuleCat.{v} R) ℕ} (f : C ⟶ D)
    (x : P103.Specs.Ch10.Complexes.Homology C n) :
    quotientHomologyEquiv R D n (P103.Specs.Ch10.Complexes.homologyMap f n x) =
      HomologicalComplex.homologyMap f n (quotientHomologyEquiv R C n x) := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    change quotientHomologyEquiv R D n
      (P103.Specs.Ch10.Complexes.homologyClass D n
        (P103.Specs.Ch10.Complexes.cyclesMap f n z)) =
      HomologicalComplex.homologyMap f n (quotientHomologyEquiv R C n
        (P103.Specs.Ch10.Complexes.homologyClass C n z))
    rw [quotientHomologyEquiv_class, quotientHomologyEquiv_class]
    have hc : quotientCyclesEquiv R D n (P103.Specs.Ch10.Complexes.cyclesMap f n z) =
        HomologicalComplex.cyclesMap f n (quotientCyclesEquiv R C n z) := by
      apply (ModuleCat.mono_iff_injective (D.iCycles n)).mp inferInstance
      rw [quotientCyclesEquiv_val]
      have hi := congrArg (fun t => t.hom (quotientCyclesEquiv R C n z))
        (HomologicalComplex.cyclesMap_i f n)
      simpa only [ModuleCat.comp_apply, quotientCyclesEquiv_val,
        P103.Specs.Ch10.Complexes.cyclesMap, LinearMap.codRestrict_apply,
        LinearMap.comp_apply, Submodule.coe_subtype] using hi.symm
    rw [hc]
    exact (congrArg (fun t => t.hom (quotientCyclesEquiv R C n z))
      (HomologicalComplex.homologyπ_naturality f n)).symm

end QuotientHomology

/-- Both squares of the algebraic sequence commute for arbitrary maps of
spaces and arbitrary projective models; no finite-type assumption appears. -/
theorem algebraic_naturality [IsDomain R] [IsPrincipalIdealRing R]
    {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y')
    (P : HomologyModels (rightSingular R X))
    (P' : HomologyModels (rightSingular R X'))
    (T : TorMaps.{u,max u w,max u w} R 1) (n : ℕ)
    (S : NormalizedDegreeSequence (rightSingular R X) (complex R R Y) P n)
    (S' : NormalizedDegreeSequence (rightSingular R X') (complex R R Y') P' n) :
    let F := commRightOrdinaryMap (chainMap R R f)
    let G := chainMap R R g
    ((P103.Specs.Ch10.Complexes.homologyMap (ordinaryTotalMap F G) n).toAddMonoidHom.toIntLinearMap).comp S.α =
      S'.α.comp (tensorDiagonalMap F G n) ∧
    (torDiagonalMap F G P P' T n).comp S.β =
      S'.β.comp (P103.Specs.Ch10.Complexes.homologyMap
        (ordinaryTotalMap F G) n).toAddMonoidHom.toIntLinearMap :=
  P103.Ch11.KunnethSequence.normalized_natural R _ _ _ _
    (commRightOrdinaryMap (chainMap R R f)) (chainMap R R g) P P' T n S S'

/-- The stipulated shuffle map induces an isomorphism on tensor homology.
All seven complete provisional statements occur in the contract order. This
auxiliary result isolates the pointwise shuffle consequence. -/
theorem shuffleHomologyIso_conditional :
    P202Specs.EilenbergZilber.comparison_type.{u,w} →
    P202Specs.EilenbergZilber.equivalence_type.{u,w} →
    P202Specs.EilenbergZilber.externalProduct_type.{u,w} →
    P202Specs.EilenbergZilber.naturalComparison_type.{u,w} →
    P202Specs.EilenbergZilber.naturalHomotopies_type.{u,w} →
    P202Specs.EilenbergZilber.relativeCompatibility_type.{u,w} →
    P202Specs.EilenbergZilber.smoothAW_type.{u,w} →
    ∀ (R : Type u) [CommRing R] (X Y : TopCat.{w}) (n : ℕ),
      ∃ (e : (tensorComplex R X Y).homology n ≅
          (complex R R (productSpace X Y)).homology n)
        (F : tensorComplex R X Y ⟶ complex R R (productSpace X Y)),
        (∀ k, F.f k = ModuleCat.ofHom (P202Specs.ShuffleModel.shuffle R X Y k)) ∧
          e.hom = HomologicalComplex.homologyMap F n := by
  intro _hcomparison hequivalence _hexternal _hnatural _hhomotopies _hrelative _hsmooth
  intro R _ X Y n
  obtain ⟨e, _hehom, heinv⟩ := hequivalence R X Y
  exact ⟨(e.toHomologyIso n).symm, e.inv, heinv, rfl⟩


/-- Tensor coordinates turn the actual total functor into its R-linear chain map. -/
theorem totalMap_boundary_from_coordinates
    {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ)
    (z : Total R X Y (n+1)) :
    totalBoundary R X' Y' n (totalMap R f g (n+1) z) =
      totalMap R f g n (totalBoundary R X Y n z) := by
  let A := ordinaryTotal (rightSingular R X) (complex R R Y)
  let B := ordinaryTotal (rightSingular R X') (complex R R Y')
  let F : A ⟶ B := ordinaryTotalMap (commRightOrdinaryMap (chainMap R R f))
    (chainMap R R g)
  obtain ⟨x, rfl⟩ := (algebraicTotalCoordinates R X Y (n+1)).surjective z
  rw [← algebraicTotalCoordinates_natural,
    ← algebraicTotalCoordinates_boundary]
  have hd := congrArg (fun t => t.hom x) (F.comm (n+1) n)
  change (B.d (n+1) n).hom ((F.f (n+1)).hom x) =
    (F.f n).hom ((A.d (n+1) n).hom x) at hd
  change algebraicTotalCoordinates R X' Y' n
      ((B.d (n+1) n).hom ((F.f (n+1)).hom x)) = _
  calc
    _ = algebraicTotalCoordinates R X' Y' n
        ((F.f n).hom ((A.d (n+1) n).hom x)) := congrArg _ hd
    _ = _ := (algebraicTotalCoordinates_natural R f g n
      ((A.d (n+1) n).hom x)).trans
        (congrArg (totalMap R f g n) (algebraicTotalCoordinates_boundary R X Y n x))

/-- The shared tensor complex is functorial under maps of both spaces. -/
def tensorChainMap {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorComplex R X Y ⟶ tensorComplex R X' Y' where
  f n := ModuleCat.ofHom (totalMap R f g n)
  comm' n m h := by
    change m + 1 = n at h
    subst n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    simp only [P202Specs.AlexanderWhitney.tensorComplex, ChainComplex.of_d,
      ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
    change totalBoundary R X' Y' m (totalMap R f g (m+1) z) =
      totalMap R f g m (totalBoundary R X Y m z)
    exact totalMap_boundary_from_coordinates R f g m z

/-- Naturality of the prescribed shuffle holds as equality of chain maps. -/
theorem shuffleChain_natural
    (c : ∀ X Y : TopCat.{w}, P202Specs.EilenbergZilber.Comparison R X Y)
    (hc : ∀ {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ),
      ((chainMap R R (productMap f g)).f n).hom.comp ((c X Y).fromTensor.f n).hom =
        ((c X' Y').fromTensor.f n).hom.comp (totalMap R f g n))
    {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') :
    (c X Y).fromTensor ≫ chainMap R R (productMap f g) =
      tensorChainMap R f g ≫ (c X' Y').fromTensor := by
  ext n z
  exact LinearMap.congr_fun (hc f g n) z

/-- A comparison with the stipulated graded map induces an isomorphism on homology. -/
def shuffleComparisonHomologyIso
    (hequivalence : P202Specs.EilenbergZilber.equivalence_type.{u,w})
    (X Y : TopCat.{w}) (c : P202Specs.EilenbergZilber.Comparison R X Y) (n : ℕ) :
    (tensorComplex R X Y).homology n ≅
      (complex R R (productSpace X Y)).homology n := by
  let e := Classical.choose (hequivalence R X Y)
  have heinv := (Classical.choose_spec (hequivalence R X Y)).2
  have hF : c.fromTensor = e.inv := by
    ext k
    rw [c.fromTensor_f, heinv]
  exact { (e.toHomologyIso n).symm with
    hom := HomologicalComplex.homologyMap c.fromTensor n
    hom_inv_id := by rw [hF]; exact (e.toHomologyIso n).inv_hom_id
    inv_hom_id := by rw [hF]; exact (e.toHomologyIso n).hom_inv_id }

@[simp] theorem shuffleComparisonHomologyIso_hom
    (hequivalence : P202Specs.EilenbergZilber.equivalence_type.{u,w})
    (X Y : TopCat.{w}) (c : P202Specs.EilenbergZilber.Comparison R X Y) (n : ℕ) :
    (shuffleComparisonHomologyIso R hequivalence X Y c n).hom =
      HomologicalComplex.homologyMap c.fromTensor n := by
  rfl

/-- The shuffle homology isomorphism is natural in both spaces. -/
theorem shuffleComparisonHomologyIso_natural
    (hequivalence : P202Specs.EilenbergZilber.equivalence_type.{u,w})
    (c : ∀ X Y : TopCat.{w}, P202Specs.EilenbergZilber.Comparison R X Y)
    (hc : ∀ {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ),
      ((chainMap R R (productMap f g)).f n).hom.comp ((c X Y).fromTensor.f n).hom =
        ((c X' Y').fromTensor.f n).hom.comp (totalMap R f g n))
    {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) :
    (shuffleComparisonHomologyIso R hequivalence X Y (c X Y) n).hom ≫
        HomologicalComplex.homologyMap (chainMap R R (productMap f g)) n =
      HomologicalComplex.homologyMap (tensorChainMap R f g) n ≫
        (shuffleComparisonHomologyIso R hequivalence X' Y' (c X' Y') n).hom := by
  simp only [shuffleComparisonHomologyIso_hom, ← HomologicalComplex.homologyMap_comp]
  rw [shuffleChain_natural R c hc f g]

section ScalarHomology
universe v
open P103.Specs.Ch10.Complexes

/-- Changing to the canonical right action commutes with singular homology. -/
def rightHomologyIso (X : TopCat.{w}) (n : ℕ) :
    ModuleCat.of Rᵐᵒᵖ (Homology (rightSingular R X) n) ≅
      (commRightFunctor R).obj ((complex R R X).homology n) :=
  (quotientHomologyEquiv Rᵐᵒᵖ (rightSingular R X) n).toModuleIso ≪≫
    ((complex R R X).sc n).mapHomologyIso (commRightFunctor R)

/-- The right-action bridge reaches the original integer-indexed singular
homology, rather than introducing a replacement homology module. -/
def rightOrdinaryHomologyIso (X : TopCat.{w}) (n : ℕ) :
    ModuleCat.of Rᵐᵒᵖ (Homology (rightSingular R X) n) ≅
      (commRightFunctor R).obj
        (ModuleCat.of R (P202Specs.TopologicalKunneth.H R X n)) :=
  rightHomologyIso R X n ≪≫
    (commRightFunctor R).mapIso (P202Specs.EilenbergZilber.ordinaryHomologyIso R X n).symm

/-- The left quotient homology reaches the same original ordinary homology. -/
def ordinaryQuotientHomologyEquiv (X : TopCat.{w}) (n : ℕ) :
    Homology (complex R R X) n ≃ₗ[R] P202Specs.TopologicalKunneth.H R X n :=
  (quotientHomologyEquiv R (complex R R X) n).trans
    (P202Specs.EilenbergZilber.ordinaryHomologyIso R X n).toLinearEquiv.symm

/-- The two integer scalar presentations have the same chains and boundary. -/
def integerTensorRestrictionIso (X Y : TopCat.{w}) :
    integerTensorComplex R X Y ≅
      ((ModuleCat.restrictScalars (Int.castRingHom R)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (tensorComplex R X Y) :=
  HomologicalComplex.Hom.isoOfComponents (fun n =>
    ((AddEquiv.refl (Total R X Y n)).toIntLinearEquiv
      (modM := (integerTensorComplex R X Y).X n |>.isModule)
      (modM₂ := ((ModuleCat.restrictScalars (Int.castRingHom R)).obj
        ((tensorComplex R X Y).X n)).isModule)).toModuleIso) (by
    intro n m h
    change m + 1 = n at h
    subst n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    simp only [integerTensorComplex, P202Specs.AlexanderWhitney.tensorComplex,
      ChainComplex.of_d, Functor.mapHomologicalComplex_obj_d]
    rfl)

/-- Forgetting coefficients commutes with homology of the shared tensor complex. -/
def tensorIntegerHomologyIso (X Y : TopCat.{w}) (n : ℕ) :
    (integerTensorComplex R X Y).homology n ≅
      (ModuleCat.restrictScalars (Int.castRingHom R)).obj
        ((tensorComplex R X Y).homology n) :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (integerTensorRestrictionIso R X Y) ≪≫
    ((tensorComplex R X Y).sc n).mapHomologyIso
      (ModuleCat.restrictScalars (Int.castRingHom R))

/-- P103's total maps to the actual scalar restriction of the R-tensor total. -/
def algebraicTotalRestrictionIso (X Y : TopCat.{w}) :
    ordinaryTotal (rightSingular R X) (complex R R Y) ≅
      ((ModuleCat.restrictScalars (Int.castRingHom R)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (tensorComplex R X Y) :=
  algebraicTotalIso R X Y ≪≫ integerTensorRestrictionIso R X Y

/-- The chain comparison intertwines the coefficient endomorphisms. -/
theorem algebraicTotalRestrictionIso_scalar (X Y : TopCat.{w}) (r : R) :
    ordinaryTotalMap (𝟙 (rightSingular R X))
        (P103.Specs.Ch11.KunnethFreeSplitting.scalarChainMap (complex R R Y) r) ≫
      (algebraicTotalRestrictionIso R X Y).hom =
    (algebraicTotalRestrictionIso R X Y).hom ≫
      ((ModuleCat.restrictScalars (Int.castRingHom R)).mapHomologicalComplex
        (ComplexShape.down ℕ)).map
          (P103.Specs.Ch11.KunnethFreeSplitting.scalarChainMap (tensorComplex R X Y) r) := by
  ext n z
  change algebraicTotalCoordinates R X Y n
      (((ordinaryTotalMap (𝟙 (rightSingular R X))
        (P103.Specs.Ch11.KunnethFreeSplitting.scalarChainMap (complex R R Y) r)).f n).hom z) =
    r • algebraicTotalCoordinates R X Y n z
  exact algebraicTotalCoordinates_scalar R X Y n r z

/-- P103's actual quotient total homology is the shared tensor homology.
This is an integer-linear equivalence; compatibility with R is proved below. -/
def algebraicTensorHomologyEquiv (X Y : TopCat.{w}) (n : ℕ) :
    Homology (ordinaryTotal (rightSingular R X) (complex R R Y)) n ≃ₗ[ℤ]
      (tensorComplex R X Y).homology n :=
 by
  let e := (HomologicalComplex.homologyFunctor _ _ n).mapIso
      (algebraicTotalRestrictionIso R X Y) ≪≫
    ((tensorComplex R X Y).sc n).mapHomologyIso
      (ModuleCat.restrictScalars (Int.castRingHom R))
  let a : Homology (ordinaryTotal (rightSingular R X) (complex R R Y)) n ≃+
      (ordinaryTotal (rightSingular R X) (complex R R Y)).homology n := by
    let C := ordinaryTotal (rightSingular R X) (complex R R Y)
    letI : Module ℤ (cycles C n) := (cycles C n).module
    letI : Module ℤ (Homology C n) := Submodule.Quotient.module _
    exact (quotientHomologyEquiv ℤ C n).toAddEquiv
  let b := e.toLinearEquiv.toAddEquiv
  let c := a.trans b
  exact c.toIntLinearEquiv (modM := AddCommGroup.toIntModule _)
    (modM₂ := AddCommGroup.toIntModule _)

/-- Formula for the total-homology bridge using the actual quotient class
and the actual chain comparison. -/
theorem algebraicTensorHomologyEquiv_apply (X Y : TopCat.{w}) (n : ℕ)
    (x : Homology (ordinaryTotal (rightSingular R X) (complex R R Y)) n) :
    algebraicTensorHomologyEquiv R X Y n x =
      (((tensorComplex R X Y).sc n).mapHomologyIso
        (ModuleCat.restrictScalars (Int.castRingHom R))).hom
        (HomologicalComplex.homologyMap (algebraicTotalRestrictionIso R X Y).hom n
          (quotientHomologyEquiv ℤ _ n x)) := rfl

/-- Scalar multiplication on a module complex induces the same scalar
multiplication on its categorical homology. -/
theorem scalarChainMap_homology (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (n : ℕ) (r : R) (x : C.homology n) :
    HomologicalComplex.homologyMap
      (P103.Specs.Ch11.KunnethFreeSplitting.scalarChainMap C r) n x = r • x := by
  let σ := P103.Specs.Ch11.KunnethFreeSplitting.scalarChainMap C r
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (C.homologyπ n)).mp inferInstance x
  have hz : HomologicalComplex.cyclesMap σ n z = r • z := by
    apply (ModuleCat.mono_iff_injective (C.iCycles n)).mp inferInstance
    have hi := congrArg (fun t => t.hom z) (HomologicalComplex.cyclesMap_i σ n)
    change C.iCycles n (HomologicalComplex.cyclesMap σ n z) = _ at hi
    rw [hi, map_smul]
    rfl
  have hπ := congrArg (fun t => t.hom z) (HomologicalComplex.homologyπ_naturality σ n)
  change HomologicalComplex.homologyMap σ n (C.homologyπ n z) = _ at hπ
  rw [hπ, ModuleCat.comp_apply, hz, map_smul]

set_option maxHeartbeats 1200000 in
/-- The bridge carries P103's genuine coefficient action to the R action on
shared tensor homology; this scalar condition is proved, not assumed. -/
theorem algebraicTensorHomologyEquiv_scalar (X Y : TopCat.{w}) (n : ℕ) (r : R)
    (x : Homology (ordinaryTotal (rightSingular R X) (complex R R Y)) n) :
    algebraicTensorHomologyEquiv R X Y n
      (P103.Specs.Ch11.KunnethFreeSplitting.totalScalar
        (rightSingular R X) (complex R R Y) n r x) =
      r • algebraicTensorHomologyEquiv R X Y n x := by
  let C := ordinaryTotal (rightSingular R X) (complex R R Y)
  let D := tensorComplex R X Y
  let F := ModuleCat.restrictScalars (Int.castRingHom R)
  let σ := P103.Specs.Ch11.KunnethFreeSplitting.scalarChainMap D r
  have hh := congrArg (fun (f : C ⟶
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj D) =>
    (HomologicalComplex.homologyMap f n).hom (quotientHomologyEquiv ℤ C n x)) (algebraicTotalRestrictionIso_scalar R X Y r)
  simp only [HomologicalComplex.homologyMap_comp, ModuleCat.comp_apply] at hh
  rw [algebraicTensorHomologyEquiv_apply, algebraicTensorHomologyEquiv_apply]
  change ((D.sc n).mapHomologyIso F).hom
      (HomologicalComplex.homologyMap (algebraicTotalRestrictionIso R X Y).hom n
        (quotientHomologyEquiv ℤ C n (homologyMap _ n x))) = _
  rw [quotientHomologyEquiv_natural]
  erw [hh]
  have hn := congrArg (fun (f :
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj D).homology n ⟶
        F.obj (D.homology n)) => f.hom
    (HomologicalComplex.homologyMap (algebraicTotalRestrictionIso R X Y).hom n
      (quotientHomologyEquiv ℤ C n x)))
    (ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor _ _ n).map σ) F)
  change ((D.sc n).mapHomologyIso F).hom
      (HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map σ) n
        (HomologicalComplex.homologyMap (algebraicTotalRestrictionIso R X Y).hom n
          (quotientHomologyEquiv ℤ C n x))) = _ at hn
  rw [hn]
  exact scalarChainMap_homology R D n r _

theorem ordinaryHomologyIso_natural {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ) :
    HomologicalComplex.homologyMap ((ordinaryFunctor R R).map f) (n : ℤ) ≫
      (P202Specs.EilenbergZilber.ordinaryHomologyIso R Y n).hom =
    (P202Specs.EilenbergZilber.ordinaryHomologyIso R X n).hom ≫
      HomologicalComplex.homologyMap (chainMap R R f) n := by
  exact HomologicalComplex.extendHomologyIso_hom_naturality (chainMap R R f)
    (degreeEmbedding 0) (by change (0 : ℤ) + (n : ℤ) = n; omega)

theorem ordinaryQuotientHomologyEquiv_natural {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ)
    (x : Homology (complex R R X) n) :
    ordinaryQuotientHomologyEquiv R Y n (homologyMap (chainMap R R f) n x) =
      P202Specs.TopologicalKunneth.hMap R f n (ordinaryQuotientHomologyEquiv R X n x) := by
  apply (P202Specs.EilenbergZilber.ordinaryHomologyIso R Y n).toLinearEquiv.injective
  simp only [ordinaryQuotientHomologyEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [quotientHomologyEquiv_natural]
  have h := congrArg (fun f => f.hom (ordinaryQuotientHomologyEquiv R X n x))
    (ordinaryHomologyIso_natural R f n)
  have hx : (P202Specs.EilenbergZilber.ordinaryHomologyIso R X n).hom
      (ordinaryQuotientHomologyEquiv R X n x) =
        quotientHomologyEquiv R (complex R R X) n x :=
    (P202Specs.EilenbergZilber.ordinaryHomologyIso R X n).toLinearEquiv.apply_symm_apply _
  change (P202Specs.EilenbergZilber.ordinaryHomologyIso R Y n).hom
      (P202Specs.TopologicalKunneth.hMap R f n (ordinaryQuotientHomologyEquiv R X n x)) =
    HomologicalComplex.homologyMap (chainMap R R f) n
      ((P202Specs.EilenbergZilber.ordinaryHomologyIso R X n).hom
        (ordinaryQuotientHomologyEquiv R X n x)) at h
  rw [hx] at h
  exact h.symm

theorem rightHomologyIso_natural {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ)
    (x : Homology (rightSingular R X) n) :
    (rightHomologyIso R Y n).hom
      (homologyMap (commRightOrdinaryMap (chainMap R R f)) n x) =
    ((commRightFunctor R).map (HomologicalComplex.homologyMap (chainMap R R f) n))
      ((rightHomologyIso R X n).hom x) := by
  change (((complex R R Y).sc n).mapHomologyIso (commRightFunctor R)).hom
      (quotientHomologyEquiv Rᵐᵒᵖ (rightSingular R Y) n
        (homologyMap (commRightOrdinaryMap (chainMap R R f)) n x)) = _
  rw [quotientHomologyEquiv_natural]
  exact congrArg (fun t => t.hom (quotientHomologyEquiv Rᵐᵒᵖ (rightSingular R X) n x))
    (ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor _ _ n).map (chainMap R R f))
      (commRightFunctor R))

theorem rightOrdinaryHomologyIso_natural {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ)
    (x : Homology (rightSingular R X) n) :
    (rightOrdinaryHomologyIso R Y n).hom
      (homologyMap (commRightOrdinaryMap (chainMap R R f)) n x) =
    P202Specs.TopologicalKunneth.hMap R f n
      ((rightOrdinaryHomologyIso R X n).hom x) := by
  apply (P202Specs.EilenbergZilber.ordinaryHomologyIso R Y n).toLinearEquiv.injective
  have hY (y : Homology (rightSingular R Y) n) :
      (P202Specs.EilenbergZilber.ordinaryHomologyIso R Y n).hom
        ((rightOrdinaryHomologyIso R Y n).hom y) = (rightHomologyIso R Y n).hom y :=
    (P202Specs.EilenbergZilber.ordinaryHomologyIso R Y n).toLinearEquiv.apply_symm_apply _
  have hX : (P202Specs.EilenbergZilber.ordinaryHomologyIso R X n).hom
      ((rightOrdinaryHomologyIso R X n).hom x) = (rightHomologyIso R X n).hom x :=
    (P202Specs.EilenbergZilber.ordinaryHomologyIso R X n).toLinearEquiv.apply_symm_apply _
  change (P202Specs.EilenbergZilber.ordinaryHomologyIso R Y n).hom _ =
    (P202Specs.EilenbergZilber.ordinaryHomologyIso R Y n).hom _
  rw [hY, rightHomologyIso_natural]
  have h := congrArg (fun f => f.hom ((rightOrdinaryHomologyIso R X n).hom x))
    (ordinaryHomologyIso_natural R f n)
  change (P202Specs.EilenbergZilber.ordinaryHomologyIso R Y n).hom
      (P202Specs.TopologicalKunneth.hMap R f n ((rightOrdinaryHomologyIso R X n).hom x)) =
    HomologicalComplex.homologyMap (chainMap R R f) n
      ((P202Specs.EilenbergZilber.ordinaryHomologyIso R X n).hom
        ((rightOrdinaryHomologyIso R X n).hom x)) at h
  rw [hX] at h
  exact h.symm

theorem algebraicTotalRestrictionIso_natural
    {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') :
    ordinaryTotalMap (commRightOrdinaryMap (chainMap R R f)) (chainMap R R g) ≫
      (algebraicTotalRestrictionIso R X' Y').hom =
    (algebraicTotalRestrictionIso R X Y).hom ≫
      ((ModuleCat.restrictScalars (Int.castRingHom R)).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (tensorChainMap R f g) := by
  ext n z
  exact algebraicTotalCoordinates_natural R f g n z

set_option maxHeartbeats 1200000 in
theorem algebraicTensorHomologyEquiv_natural
    {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ)
    (x : Homology (ordinaryTotal (rightSingular R X) (complex R R Y)) n) :
    algebraicTensorHomologyEquiv R X' Y' n
      (homologyMap (ordinaryTotalMap (commRightOrdinaryMap (chainMap R R f))
        (chainMap R R g)) n x) =
    HomologicalComplex.homologyMap (tensorChainMap R f g) n
      (algebraicTensorHomologyEquiv R X Y n x) := by
  let C := ordinaryTotal (rightSingular R X) (complex R R Y)
  let D := tensorComplex R X Y
  let D' := tensorComplex R X' Y'
  let F := ModuleCat.restrictScalars (Int.castRingHom R)
  have hh := congrArg (fun (h : C ⟶
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj D') =>
    (HomologicalComplex.homologyMap h n).hom (quotientHomologyEquiv ℤ C n x))
      (algebraicTotalRestrictionIso_natural R f g)
  simp only [HomologicalComplex.homologyMap_comp, ModuleCat.comp_apply] at hh
  rw [algebraicTensorHomologyEquiv_apply, algebraicTensorHomologyEquiv_apply]
  erw [quotientHomologyEquiv_natural]
  erw [hh]
  exact congrArg (fun h => h.hom
    (HomologicalComplex.homologyMap (algebraicTotalRestrictionIso R X Y).hom n
      (quotientHomologyEquiv ℤ C n x)))
    (ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor _ _ n).map (tensorChainMap R f g)) F)

theorem restriction_homologyπ (C : ChainComplex (ModuleCat.{max u v} R) ℕ) (n : ℕ) :
    ((C.sc n).map (ModuleCat.restrictScalars (Int.castRingHom R))).homologyπ ≫
      ((C.sc n).mapHomologyIso (ModuleCat.restrictScalars (Int.castRingHom R))).hom =
    ((C.sc n).mapCyclesIso (ModuleCat.restrictScalars (Int.castRingHom R))).hom ≫
      (ModuleCat.restrictScalars (Int.castRingHom R)).map (C.homologyπ n) := by
  let S := C.sc n
  let F := ModuleCat.restrictScalars (Int.castRingHom R)
  let h := S.homologyData.left
  change (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
    (S.mapCyclesIso F).hom ≫ F.map S.homologyπ
  rw [h.mapHomologyIso_eq F, h.mapCyclesIso_eq F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, (h.map F).homologyπ_comp_homologyIso_hom]
  simp only [Category.assoc, ShortComplex.LeftHomologyData.map_π]
  rw [← F.map_comp, h.π_comp_homologyIso_inv, F.map_comp]

/-- A total cycle in P103 coordinates determines the same cycle in tensor coordinates. -/
def algebraicTensorCycles (X Y : TopCat.{w}) (n : ℕ)
    (z : cycles (ordinaryTotal (rightSingular R X) (complex R R Y)) n) :
    (tensorComplex R X Y).cycles n :=
  (((tensorComplex R X Y).sc n).mapCyclesIso
      (ModuleCat.restrictScalars (Int.castRingHom R))).hom
    (HomologicalComplex.cyclesMap (algebraicTotalRestrictionIso R X Y).hom n
      (quotientCyclesEquiv ℤ _ n z))

theorem algebraicTensorCycles_val (X Y : TopCat.{w}) (n : ℕ)
    (z : cycles (ordinaryTotal (rightSingular R X) (complex R R Y)) n) :
    (tensorComplex R X Y).iCycles n (algebraicTensorCycles R X Y n z) =
      algebraicTotalCoordinates R X Y n z.val := by
  let C := ordinaryTotal (rightSingular R X) (complex R R Y)
  let D := tensorComplex R X Y
  let F : ModuleCat.{max u w} R ⥤ ModuleCat.{max u w} ℤ :=
    ModuleCat.restrictScalars (Int.castRingHom R)
  let w := HomologicalComplex.cyclesMap (algebraicTotalRestrictionIso R X Y).hom n
    (quotientCyclesEquiv ℤ C n z)
  have hi := congrArg (fun f => f.hom w) ((D.sc n).mapCyclesIso_hom_iCycles F)
  change D.iCycles n (algebraicTensorCycles R X Y n z) = _ at hi
  rw [hi]
  have hc := congrArg (fun f => f.hom (quotientCyclesEquiv ℤ C n z))
    (HomologicalComplex.cyclesMap_i (algebraicTotalRestrictionIso R X Y).hom n)
  change _ = ((algebraicTotalRestrictionIso R X Y).hom.f n).hom
    (C.iCycles n (quotientCyclesEquiv ℤ C n z)) at hc
  rw [quotientCyclesEquiv_val] at hc
  exact hc

set_option maxHeartbeats 1200000 in
theorem algebraicTensorHomologyEquiv_class (X Y : TopCat.{w}) (n : ℕ)
    (z : cycles (ordinaryTotal (rightSingular R X) (complex R R Y)) n) :
    algebraicTensorHomologyEquiv R X Y n (homologyClass _ n z) =
      (tensorComplex R X Y).homologyπ n (algebraicTensorCycles R X Y n z) := by
  let C := ordinaryTotal (rightSingular R X) (complex R R Y)
  let D := tensorComplex R X Y
  let F : ModuleCat.{max u w} R ⥤ ModuleCat.{max u w} ℤ :=
    ModuleCat.restrictScalars (Int.castRingHom R)
  let w := HomologicalComplex.cyclesMap (algebraicTotalRestrictionIso R X Y).hom n
    (quotientCyclesEquiv ℤ C n z)
  rw [algebraicTensorHomologyEquiv_apply, quotientHomologyEquiv_class]
  have hn := congrArg (fun f => f.hom (quotientCyclesEquiv ℤ C n z))
    (HomologicalComplex.homologyπ_naturality (algebraicTotalRestrictionIso R X Y).hom n)
  change HomologicalComplex.homologyMap (algebraicTotalRestrictionIso R X Y).hom n
      (C.homologyπ n (quotientCyclesEquiv ℤ C n z)) = _ at hn
  erw [hn]
  exact congrArg (fun f => f.hom w) (restriction_homologyπ R D n)

end ScalarHomology

section ShuffleOnOrdinaryHomology

open P202Specs.EilenbergZilber P202Specs.ShuffleModel

/-- The homology isomorphism lands in the original ordinary singular homology. -/
def shuffleOrdinaryHomologyIso
    (hequivalence : P202Specs.EilenbergZilber.equivalence_type.{u,w})
    (X Y : TopCat.{w}) (c : Comparison R X Y) (n : ℕ) :
    (tensorComplex R X Y).homology n ≅
      ModuleCat.of R (P202Specs.TopologicalKunneth.H R (productSpace X Y) n) :=
  shuffleComparisonHomologyIso R hequivalence X Y c n ≪≫
    (ordinaryHomologyIso R (productSpace X Y) n).symm

/-- The same shuffle isomorphisms commute with ordinary homology maps. -/
theorem shuffleOrdinaryHomologyIso_natural
    (hequivalence : P202Specs.EilenbergZilber.equivalence_type.{u,w})
    (c : ∀ X Y : TopCat.{w}, Comparison R X Y)
    (hc : ∀ {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ),
      ((chainMap R R (productMap f g)).f n).hom.comp ((c X Y).fromTensor.f n).hom =
        ((c X' Y').fromTensor.f n).hom.comp (totalMap R f g n))
    {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) :
    (shuffleOrdinaryHomologyIso R hequivalence X Y (c X Y) n).hom ≫
        HomologicalComplex.homologyMap ((ordinaryFunctor R R).map (productMap f g)) (n : ℤ) =
      HomologicalComplex.homologyMap (tensorChainMap R f g) n ≫
        (shuffleOrdinaryHomologyIso R hequivalence X' Y' (c X' Y') n).hom := by
  apply (cancel_mono (ordinaryHomologyIso R (productSpace X' Y') n).hom).mp
  simp only [shuffleOrdinaryHomologyIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    ordinaryHomologyIso_natural, Iso.inv_hom_id, Category.comp_id,
    Iso.inv_hom_id_assoc]
  exact shuffleComparisonHomologyIso_natural R hequivalence c hc f g n

/-- On a single bidegree, the finite-diagonal shuffle is its specified component. -/
theorem shuffle_single (X Y : TopCat.{w}) (p q : ℕ)
    (t : Summand R X Y p q) :
    shuffle R X Y (p+q)
      (LinearMap.single R (fun i : P202Specs.AlexanderWhitney.Diagonal (p+q) => Summand R X Y i.val.1 i.val.2)
        ⟨(p,q),rfl⟩ t) = shuffleComponent R X Y p q t := by
  classical
  simp only [shuffle, LinearMap.sum_apply]
  rw [Finset.sum_eq_single (⟨(p,q),rfl⟩ : P202Specs.AlexanderWhitney.Diagonal (p+q))]
  · simp [LinearMap.single_apply, castChains]
  · intro i _ hi
    simp [LinearMap.single_apply, Pi.single_eq_of_ne hi]
  · simp

/-- Any tensor cycle with the elementary shuffle representative gives the
prescribed external product, independently of all choices of comparison data. -/
theorem shuffleComparisonHomologyIso_external
    (hequivalence : P202Specs.EilenbergZilber.equivalence_type.{u,w})
    (e : ExternalProduct.{u,w} R) (X Y : TopCat.{w}) (c : Comparison R X Y)
    (p q : ℕ) (a : (complex R R X).cycles p) (b : (complex R R Y).cycles q)
    (z : (tensorComplex R X Y).cycles (p+q))
    (hz : shuffle R X Y (p+q) ((tensorComplex R X Y).iCycles (p+q) z) =
      shuffleComponent R X Y p q
        ((complex R R X).iCycles p a ⊗ₜ[R] (complex R R Y).iCycles q b)) :
    (shuffleComparisonHomologyIso R hequivalence X Y c (p+q)).hom
        ((tensorComplex R X Y).homologyπ (p+q) z) =
      e.map X Y p q ((complex R R X).homologyπ p a ⊗ₜ[R]
        (complex R R Y).homologyπ q b) := by
  obtain ⟨v, hv, hπ⟩ := e.represents X Y p q a b
  have hcv : HomologicalComplex.cyclesMap c.fromTensor (p+q) z = v := by
    apply (ModuleCat.mono_iff_injective ((complex R R (productSpace X Y)).iCycles (p+q))).mp inferInstance
    have hi := congrArg (fun t => t.hom z)
      (HomologicalComplex.cyclesMap_i c.fromTensor (p+q))
    change (complex R R (productSpace X Y)).iCycles (p+q)
      (HomologicalComplex.cyclesMap c.fromTensor (p+q) z) = _ at hi
    rw [hi, c.fromTensor_f]
    exact hz.trans hv.symm
  rw [shuffleComparisonHomologyIso_hom]
  have hn := congrArg (fun t => t.hom z)
    (HomologicalComplex.homologyπ_naturality c.fromTensor (p+q))
  change HomologicalComplex.homologyMap c.fromTensor (p+q)
    ((tensorComplex R X Y).homologyπ (p+q) z) = _ at hn
  rw [hn, ModuleCat.comp_apply, hcv, hπ]

/-- Elementary tensor-cycle classes map to the specified external product. -/
theorem shuffle_homology_external
    (hequivalence : P202Specs.EilenbergZilber.equivalence_type.{u,w})
    (e : ExternalProduct.{u,w} R) (X Y : TopCat.{w}) (c : Comparison R X Y)
    (p q : ℕ) (a : (complex R R X).cycles p) (b : (complex R R Y).cycles q)
    (z : (tensorComplex R X Y).cycles (p+q))
    (hz : (tensorComplex R X Y).iCycles (p+q) z =
      LinearMap.single R
        (fun i : P202Specs.AlexanderWhitney.Diagonal (p+q) => Summand R X Y i.val.1 i.val.2)
        ⟨(p,q),rfl⟩ ((complex R R X).iCycles p a ⊗ₜ[R] (complex R R Y).iCycles q b)) :
    (shuffleComparisonHomologyIso R hequivalence X Y c (p+q)).hom
        ((tensorComplex R X Y).homologyπ (p+q) z) =
      e.map X Y p q ((complex R R X).homologyπ p a ⊗ₜ[R]
        (complex R R Y).homologyπ q b) := by
  apply shuffleComparisonHomologyIso_external R hequivalence e X Y c p q a b z
  rw [hz, shuffle_single]

/-- The elementary tensor-cycle formula also holds in the original ordinary
singular homology, using exactly the external product fixed in the Specs. -/
theorem shuffle_ordinary_homology_external
    (hequivalence : P202Specs.EilenbergZilber.equivalence_type.{u,w})
    (e : ExternalProduct.{u,w} R) (X Y : TopCat.{w}) (c : Comparison R X Y)
    (p q : ℕ) (a : (complex R R X).cycles p) (b : (complex R R Y).cycles q)
    (z : (tensorComplex R X Y).cycles (p+q))
    (hz : (tensorComplex R X Y).iCycles (p+q) z =
      LinearMap.single R
        (fun i : P202Specs.AlexanderWhitney.Diagonal (p+q) => Summand R X Y i.val.1 i.val.2)
        ⟨(p,q),rfl⟩ ((complex R R X).iCycles p a ⊗ₜ[R] (complex R R Y).iCycles q b)) :
    (shuffleOrdinaryHomologyIso R hequivalence X Y c (p+q)).hom
        ((tensorComplex R X Y).homologyπ (p+q) z) =
      P202Specs.TopologicalKunneth.ordinaryExternal R e X Y p q
        ((ordinaryHomologyIso R X p).inv ((complex R R X).homologyπ p a) ⊗ₜ[R]
          (ordinaryHomologyIso R Y q).inv ((complex R R Y).homologyπ q b)) := by
  have h := shuffle_homology_external R hequivalence e X Y c p q a b z hz
  change (ordinaryHomologyIso R (productSpace X Y) (p+q)).inv
    ((shuffleComparisonHomologyIso R hequivalence X Y c (p+q)).hom
      ((tensorComplex R X Y).homologyπ (p+q) z)) = _
  rw [h]
  simp only [P202Specs.TopologicalKunneth.ordinaryExternal, LinearMap.comp_apply,
    TensorProduct.map_tmul]
  congr 2
  apply congrArg₂ (fun aa bb => aa ⊗ₜ[R] bb)
  · exact (congrArg (fun t => t.hom ((complex R R X).homologyπ p a))
      (ordinaryHomologyIso R X p).inv_hom_id).symm
  · exact (congrArg (fun t => t.hom ((complex R R Y).homologyπ q b))
      (ordinaryHomologyIso R Y q).inv_hom_id).symm


section ProductHomologyTransport
open P103.Specs.Ch10.Complexes P202Specs.EilenbergZilber

/-- The actual algebraic total homology is the original ordinary homology of
X × Y, via the prescribed shuffle and the scalar-forgetting comparison. -/
def productHomologyEquiv
    (hequivalence : P202Specs.EilenbergZilber.equivalence_type.{u,w})
    (X Y : TopCat.{w}) (c : Comparison R X Y) (n : ℕ) :
    Homology (ordinaryTotal (rightSingular R X) (complex R R Y)) n ≃ₗ[ℤ]
      P202Specs.TopologicalKunneth.H R (productSpace X Y) n :=
  (algebraicTensorHomologyEquiv R X Y n).trans
    ((shuffleOrdinaryHomologyIso R hequivalence X Y c n).toLinearEquiv.restrictScalars ℤ)

/-- This bridge uses the actual scalar action on the algebraic total. -/
theorem productHomologyEquiv_scalar
    (hequivalence : P202Specs.EilenbergZilber.equivalence_type.{u,w})
    (X Y : TopCat.{w}) (c : Comparison R X Y) (n : ℕ) (r : R)
    (x : Homology (ordinaryTotal (rightSingular R X) (complex R R Y)) n) :
    productHomologyEquiv R hequivalence X Y c n
      (P103.Specs.Ch11.KunnethFreeSplitting.totalScalar
        (rightSingular R X) (complex R R Y) n r x) =
      r • productHomologyEquiv R hequivalence X Y c n x := by
  change (shuffleOrdinaryHomologyIso R hequivalence X Y c n).hom
      (algebraicTensorHomologyEquiv R X Y n
        (P103.Specs.Ch11.KunnethFreeSplitting.totalScalar
          (rightSingular R X) (complex R R Y) n r x)) = _
  rw [algebraicTensorHomologyEquiv_scalar]
  exact (shuffleOrdinaryHomologyIso R hequivalence X Y c n).hom.hom.map_smul r _

/-- The comparison with ordinary product homology is natural in both spaces. -/
theorem productHomologyEquiv_natural
    (hequivalence : P202Specs.EilenbergZilber.equivalence_type.{u,w})
    (c : ∀ X Y : TopCat.{w}, Comparison R X Y)
    (hc : ∀ {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ),
      ((chainMap R R (productMap f g)).f n).hom.comp ((c X Y).fromTensor.f n).hom =
        ((c X' Y').fromTensor.f n).hom.comp (totalMap R f g n))
    {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ)
    (x : Homology (ordinaryTotal (rightSingular R X) (complex R R Y)) n) :
    productHomologyEquiv R hequivalence X' Y' (c X' Y') n
      (homologyMap (ordinaryTotalMap (commRightOrdinaryMap (chainMap R R f))
        (chainMap R R g)) n x) =
      P202Specs.TopologicalKunneth.hMap R (productMap f g) n
        (productHomologyEquiv R hequivalence X Y (c X Y) n x) := by
  change (shuffleOrdinaryHomologyIso R hequivalence X' Y' (c X' Y') n).hom
      (algebraicTensorHomologyEquiv R X' Y' n
        (homologyMap (ordinaryTotalMap (commRightOrdinaryMap (chainMap R R f))
          (chainMap R R g)) n x)) = _
  rw [algebraicTensorHomologyEquiv_natural]
  exact (congrArg (fun h => h.hom (algebraicTensorHomologyEquiv R X Y n x))
    (shuffleOrdinaryHomologyIso_natural R hequivalence c hc f g n)).symm

end ProductHomologyTransport

end ShuffleOnOrdinaryHomology


section TensorHomologyTransport
open P103.Specs.Ch10.Complexes
/-- Both variables of the balanced quotient can be transported along actual
module equivalences, without choosing a new tensor product. -/
def balancedTensorCongr {A A' B B' : Type*}
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup A'] [Module Rᵐᵒᵖ A']
    [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
    (e : A ≃ₗ[Rᵐᵒᵖ] A') (f : B ≃ₗ[R] B') :
    P103.BalancedTensor.Tensor R A B ≃+ P103.BalancedTensor.Tensor R A' B' where
  toFun := P103.BalancedTensor.map e.toLinearMap f.toLinearMap
  invFun := P103.BalancedTensor.map e.symm.toLinearMap f.symm.toLinearMap
  map_add' := map_add _
  left_inv z := by
    induction z using P103.BalancedTensor.induction_on with
    | h0 => simp only [map_zero]
    | ht a b => simp only [P103.BalancedTensor.map_tmul, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply]
    | ha a b ha hb => simp only [map_add, ha, hb]
  right_inv z := by
    induction z using P103.BalancedTensor.induction_on with
    | h0 => simp only [map_zero]
    | ht a b => simp only [P103.BalancedTensor.map_tmul, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply]
    | ha a b ha hb => simp only [map_add, ha, hb]

/-- Tensor products of algebraic quotient homology are the actual tensor
products of the original singular homology modules. -/
def balancedHomologyEquiv (X Y : TopCat.{w}) (p q : ℕ) :
    P103.BalancedTensor.Tensor R (Homology (rightSingular R X) p)
      (Homology (complex R R Y) q) ≃+ P202Specs.TopologicalKunneth.TensorSummand R X Y (p,q) := by
  let A := P202Specs.TopologicalKunneth.H R X p
  letI opModule : Module Rᵐᵒᵖ A := ((commRightFunctor R).obj (ModuleCat.of R A)).isModule
  letI : SMul Rᵐᵒᵖ A := opModule.toSMul
  letI : IsCentralScalar R A := ⟨fun _ _ => rfl⟩
  exact (balancedTensorCongr R (rightOrdinaryHomologyIso R X p).toLinearEquiv
    (ordinaryQuotientHomologyEquiv R Y q)).trans
      (P103.BalancedTensor.commAddEquiv (K := R) (A := A))

@[simp] theorem balancedHomologyEquiv_tmul (X Y : TopCat.{w}) (p q : ℕ)
    (a : Homology (rightSingular R X) p) (b : Homology (complex R R Y) q) :
    balancedHomologyEquiv R X Y p q (P103.BalancedTensor.tmul R a b) =
      (rightOrdinaryHomologyIso R X p).hom a ⊗ₜ[R]
        ordinaryQuotientHomologyEquiv R Y q b := rfl

/-- The finite homology diagonal agrees with the source's direct sum. -/
def tensorHomologyDiagonalEquiv (X Y : TopCat.{w}) (n : ℕ) :
    TensorDiagonal (rightSingular R X) (complex R R Y) n ≃ₗ[ℤ]
      P202Specs.TopologicalKunneth.TensorSum R X Y n :=
  DirectSum.congrLinearEquiv (fun i : P202Specs.AlexanderWhitney.Diagonal n =>
    (balancedHomologyEquiv R X Y i.val.1 i.val.2).toIntLinearEquiv)

@[simp] theorem tensorHomologyDiagonalEquiv_lof (X Y : TopCat.{w}) (n : ℕ)
    (i : P202Specs.AlexanderWhitney.Diagonal n)
    (z : P103.BalancedTensor.Tensor R (Homology (rightSingular R X) i.val.1)
      (Homology (complex R R Y) i.val.2)) :
    tensorHomologyDiagonalEquiv R X Y n (DirectSum.lof ℤ _ _ i z) =
      DirectSum.lof R _ _ i (balancedHomologyEquiv R X Y i.val.1 i.val.2 z) := by
  dsimp only [tensorHomologyDiagonalEquiv]
  simp only [DirectSum.lof_eq_of]
  erw [DirectSum.map_of]
  rfl


/-- The homology-diagonal comparison preserves the actual coefficient action. -/
theorem tensorHomologyDiagonalEquiv_scalar (X Y : TopCat.{w}) (n : ℕ) (r : R)
    (z : TensorDiagonal (rightSingular R X) (complex R R Y) n) :
    tensorHomologyDiagonalEquiv R X Y n
      (tensorDiagonalMap (𝟙 (rightSingular R X))
        (P103.Specs.Ch11.KunnethFreeSplitting.scalarChainMap (complex R R Y) r) n z) =
      r • tensorHomologyDiagonalEquiv R X Y n z := by
  induction z using DirectSum.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add a b ha hb => simp only [map_add, ha, hb, smul_add]
  | of i z =>
    change tensorHomologyDiagonalEquiv R X Y n
      (tensorDiagonalMap (𝟙 (rightSingular R X))
        (P103.Specs.Ch11.KunnethFreeSplitting.scalarChainMap (complex R R Y) r) n
        (DirectSum.lof ℤ _ _ i z)) =
      r • tensorHomologyDiagonalEquiv R X Y n (DirectSum.lof ℤ _ _ i z)
    rw [tensorDiagonalMap, DirectSum.lmap_lof,
      tensorHomologyDiagonalEquiv_lof, tensorHomologyDiagonalEquiv_lof]
    induction z using P103.BalancedTensor.induction_on with
    | h0 => simp only [map_zero, smul_zero]
    | ha a b ha hb => simp only [map_add, ha, hb, smul_add]
    | ht a b =>
      have hid : homologyMap (𝟙 (rightSingular R X)) i.val.1 = LinearMap.id :=
        P103.Ch10.Complexes.homologyMap_id (rightSingular R X) i.val.1
      have hsc : homologyMap
          (P103.Specs.Ch11.KunnethFreeSplitting.scalarChainMap (complex R R Y) r) i.val.2 =
          r • LinearMap.id :=
        P103.Ch11.KunnethFreeSplitting.homologyMap_scalar (complex R R Y) i.val.2 r
      rw [hid, hsc]
      change DirectSum.lof R (P202Specs.AlexanderWhitney.Diagonal n)
        (fun j : P202Specs.AlexanderWhitney.Diagonal n =>
          P202Specs.TopologicalKunneth.TensorSummand R X Y j.val) i
        (balancedHomologyEquiv R X Y i.val.1 i.val.2
          (P103.BalancedTensor.tmul R a (r • b))) = _
      rw [balancedHomologyEquiv_tmul, balancedHomologyEquiv_tmul,
        map_smul, TensorProduct.tmul_smul, map_smul]



/-- The comparison of the tensor homology diagonal is natural in both factors. -/
theorem tensorHomologyDiagonalEquiv_natural
    {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ)
    (z : TensorDiagonal (rightSingular R X) (complex R R Y) n) :
    tensorHomologyDiagonalEquiv R X' Y' n
      (tensorDiagonalMap (commRightOrdinaryMap (chainMap R R f)) (chainMap R R g) n z) =
      P202Specs.TopologicalKunneth.tensorSumMap R f g n
        (tensorHomologyDiagonalEquiv R X Y n z) := by
  induction z using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | of i z =>
    change tensorHomologyDiagonalEquiv R X' Y' n
      (tensorDiagonalMap (commRightOrdinaryMap (chainMap R R f)) (chainMap R R g) n
        (DirectSum.lof ℤ _ _ i z)) =
      P202Specs.TopologicalKunneth.tensorSumMap R f g n
        (tensorHomologyDiagonalEquiv R X Y n (DirectSum.lof ℤ _ _ i z))
    rw [tensorDiagonalMap, DirectSum.lmap_lof, tensorHomologyDiagonalEquiv_lof,
      tensorHomologyDiagonalEquiv_lof, P202Specs.TopologicalKunneth.tensorSumMap,
      DirectSum.lmap_lof]
    induction z using P103.BalancedTensor.induction_on with
    | h0 => simp only [map_zero]
    | ha a b ha hb => simp only [map_add, ha, hb]
    | ht a b =>
      change DirectSum.lof R (P202Specs.AlexanderWhitney.Diagonal n)
        (fun j : P202Specs.AlexanderWhitney.Diagonal n =>
          P202Specs.TopologicalKunneth.TensorSummand R X' Y' j.val) i
        (balancedHomologyEquiv R X' Y' i.val.1 i.val.2
          (P103.BalancedTensor.tmul R
            (homologyMap (commRightOrdinaryMap (chainMap R R f)) i.val.1 a)
            (homologyMap (chainMap R R g) i.val.2 b))) = _
      rw [balancedHomologyEquiv_tmul, balancedHomologyEquiv_tmul,
        rightOrdinaryHomologyIso_natural, ordinaryQuotientHomologyEquiv_natural]
      rfl

end TensorHomologyTransport

section SequenceTransport
universe v₁ v₂ v₃ w₁ w₂ w₃
variable (R : Type u) [CommRing R]
variable {A : Type v₁} {B : Type v₂} {C : Type v₃}
  {A' : Type w₁} {B' : Type w₂} {C' : Type w₃}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
  [Module ℤ A] [Module ℤ B] [Module ℤ C]
  [Module R A'] [Module R B'] [Module R C']

/-- Transport an integer-linear map to coefficient modules when the actual
scalar endomorphisms are intertwined by the established equivalences. -/
def transportLinearMap (f : A →ₗ[ℤ] B) (a : A ≃ₗ[ℤ] A') (b : B ≃ₗ[ℤ] B')
    (σ : R → A →ₗ[ℤ] A) (τ : R → B →ₗ[ℤ] B)
    (ha : ∀ r x, a (σ r x) = r • a x)
    (hb : ∀ r x, b (τ r x) = r • b x)
    (hf : ∀ r x, f (σ r x) = τ r (f x)) : A' →ₗ[R] B' where
  toFun x := b (f (a.symm x))
  map_add' x y := by simp only [map_add]
  map_smul' r x := by
    have hx : a.symm (r • x) = σ r (a.symm x) := by
      apply a.injective
      rw [a.apply_symm_apply, ha, a.apply_symm_apply]
    simpa only [RingHom.id_apply] using (congrArg b (congrArg f hx)).trans
      ((congrArg b (hf r (a.symm x))).trans (hb r (f (a.symm x))))

@[simp] theorem transportLinearMap_apply
    (f : A →ₗ[ℤ] B) (a : A ≃ₗ[ℤ] A') (b : B ≃ₗ[ℤ] B')
    (σ : R → A →ₗ[ℤ] A) (τ : R → B →ₗ[ℤ] B)
    (ha : ∀ r x, a (σ r x) = r • a x)
    (hb : ∀ r x, b (τ r x) = r • b x)
    (hf : ∀ r x, f (σ r x) = τ r (f x)) (x : A') :
    transportLinearMap R f a b σ τ ha hb hf x = b (f (a.symm x)) := rfl

/-- Exactness is preserved by the three actual additive equivalences. -/
theorem transportExact (f : A →ₗ[ℤ] B) (g : B →ₗ[ℤ] C)
    (a : A ≃ₗ[ℤ] A') (b : B ≃ₗ[ℤ] B') (c : C ≃ₗ[ℤ] C')
    (h : Function.Exact f g) :
    Function.Exact (fun x => b (f (a.symm x))) (fun y => c (g (b.symm y))) := by
  intro y
  constructor
  · intro hy
    have hg : g (b.symm y) = 0 := c.injective (hy.trans c.map_zero.symm)
    obtain ⟨x, hx⟩ := (h (b.symm y)).mp hg
    exact ⟨a x, by simpa only [a.symm_apply_apply, hx, b.apply_symm_apply]⟩
  · rintro ⟨x, rfl⟩
    change c (g (b.symm (b (f (a.symm x)))) ) = 0
    rw [b.symm_apply_apply, h.apply_apply_eq_zero, map_zero]

/-- A transported injection remains injective. -/
theorem transportInjective (f : A →ₗ[ℤ] B) (a : A ≃ₗ[ℤ] A') (b : B ≃ₗ[ℤ] B')
    (h : Function.Injective f) : Function.Injective (fun x => b (f (a.symm x))) :=
  b.injective.comp (h.comp a.symm.injective)

/-- A transported surjection remains surjective. -/
theorem transportSurjective (g : B →ₗ[ℤ] C) (b : B ≃ₗ[ℤ] B') (c : C ≃ₗ[ℤ] C')
    (h : Function.Surjective g) : Function.Surjective (fun y => c (g (b.symm y))) :=
  c.surjective.comp (h.comp b.symm.surjective)

/-- Scalar-compatible splitting of the algebraic last arrow gives an actual
R-linear section of its transported last arrow. -/
theorem transportSplitting (g : B →ₗ[ℤ] C) (b : B ≃ₗ[ℤ] B') (c : C ≃ₗ[ℤ] C')
    (τ : R → B →ₗ[ℤ] B) (υ : R → C →ₗ[ℤ] C)
    (hb : ∀ r x, b (τ r x) = r • b x)
    (hc : ∀ r x, c (υ r x) = r • c x)
    (hg : ∀ r x, g (τ r x) = υ r (g x))
    (s : C →ₗ[ℤ] B) (hs : g.comp s = LinearMap.id)
    (hs_scalar : ∀ r x, s (υ r x) = τ r (s x)) :
    ∃ t : C' →ₗ[R] B',
      (transportLinearMap R g b c τ υ hb hc hg).comp t = LinearMap.id := by
  refine ⟨transportLinearMap R s c b υ τ hc hb hs_scalar, ?_⟩
  ext x
  change c (g (b.symm (b (s (c.symm x))))) = x
  rw [b.symm_apply_apply]
  have hx := LinearMap.congr_fun hs (c.symm x)
  change g (s (c.symm x)) = c.symm x at hx
  rw [hx, c.apply_symm_apply]


/-- Conjugating a commuting square by compatible equivalences preserves it. -/
theorem transportNatural
    {A B A₁ B₁ A' B' A₁' B₁' : Type*}
    (a : A ≃ A') (b : B ≃ B') (a₁ : A₁ ≃ A₁') (b₁ : B₁ ≃ B₁')
    (f : A → B) (f₁ : A₁ → B₁)
    (p : A → A₁) (q : B → B₁) (p' : A' → A₁') (q' : B' → B₁')
    (ha : ∀ x, a₁ (p x) = p' (a x))
    (hb : ∀ y, b₁ (q y) = q' (b y))
    (hf : ∀ x, q (f x) = f₁ (p x)) (x : A') :
    q' (b (f (a.symm x))) = b₁ (f₁ (a₁.symm (p' x))) := by
  obtain ⟨z, rfl⟩ := a.surjective x
  rw [a.symm_apply_apply, ← hb, hf, ← ha, a₁.symm_apply_apply]

end SequenceTransport

section TorTransport
universe v t
open P103.Specs.Ch10.Comparison P103.Specs.Ch10.Complexes
/-- Global choices of actual projective resolutions of original singular homology. -/
def topologicalModels : P202Specs.TopologicalKunneth.Models.{u,w} R := fun X p =>
  P103.Ch11.ExtTorDefinitions.resolutionFamily Rᵐᵒᵖ
    ((commRightFunctor R).obj (ModuleCat.of R (P202Specs.TopologicalKunneth.H R X p)))

/-- Actual projective resolutions of the algebraic quotient homology. -/
def singularHomologyModels (X : TopCat.{w}) : HomologyModels (rightSingular R X) := fun p =>
  P103.Ch11.ExtTorDefinitions.resolutionFamily Rᵐᵒᵖ
    (ModuleCat.of Rᵐᵒᵖ (Homology (rightSingular R X) p))

/-- The all-model Tor maps transport genuine isomorphisms in both arguments. -/
def torCongr (T : TorMaps.{u,v,t} R 1)
    {A A' : ModuleCat.{v} Rᵐᵒᵖ} (P : ProjectiveChoice Rᵐᵒᵖ A)
    (Q : ProjectiveChoice Rᵐᵒᵖ A') {B B' : ModuleCat.{t} R}
    (e : A ≅ A') (f : B ≅ B') : TorWith P.val B 1 ≃ₗ[ℤ] TorWith Q.val B' 1 where
  toLinearMap := T.map P Q e.hom f.hom
  invFun := T.map Q P e.inv f.inv
  left_inv x := by
    have h := T.comp P Q P e.hom e.inv f.hom f.inv
    rw [e.hom_inv_id, f.hom_inv_id, T.id] at h
    exact (LinearMap.congr_fun h x).symm
  right_inv x := by
    have h := T.comp Q P Q e.inv e.hom f.inv f.hom
    rw [e.inv_hom_id, f.inv_hom_id, T.id] at h
    exact (LinearMap.congr_fun h x).symm

/-- Tor transport commutes with every commuting square in both arguments. -/
theorem torCongr_natural (T : TorMaps.{u,v,t} R 1)
    {A A' A₁ A₁' : ModuleCat.{v} Rᵐᵒᵖ}
    (P : ProjectiveChoice Rᵐᵒᵖ A) (P' : ProjectiveChoice Rᵐᵒᵖ A')
    (Q : ProjectiveChoice Rᵐᵒᵖ A₁) (Q' : ProjectiveChoice Rᵐᵒᵖ A₁')
    {B B' B₁ B₁' : ModuleCat.{t} R}
    (e : A ≅ A₁) (e' : A' ≅ A₁') (f : B ≅ B₁) (f' : B' ≅ B₁')
    (a : A ⟶ A') (a' : A₁ ⟶ A₁') (b : B ⟶ B') (b' : B₁ ⟶ B₁')
    (ha : a ≫ e'.hom = e.hom ≫ a') (hb : b ≫ f'.hom = f.hom ≫ b')
    (x : TorWith P.val B 1) :
    torCongr R T P' Q' e' f' (T.map P P' a b x) =
      T.map Q Q' a' b' (torCongr R T P Q e f x) := by
  change T.map P' Q' e'.hom f'.hom (T.map P P' a b x) =
    T.map Q Q' a' b' (T.map P Q e.hom f.hom x)
  have h₁ := T.comp P P' Q' a e'.hom b f'.hom
  have h₂ := T.comp P Q Q' e.hom a' f.hom b'
  rw [ha, hb] at h₁
  exact (LinearMap.congr_fun h₁ x).symm.trans (LinearMap.congr_fun h₂ x)

/-- Tor is linear for P103's actual coefficient action on every chosen model. -/
theorem torCongr_scalar (T : TorMaps.{u,v,t} R 1)
    {A A' : ModuleCat.{v} Rᵐᵒᵖ} (P : ProjectiveChoice Rᵐᵒᵖ A)
    (Q : ProjectiveChoice Rᵐᵒᵖ A') {B B' : ModuleCat.{t} R}
    (e : A ≅ A') (f : B ≅ B') (r : R) (x : TorWith P.val B 1) :
    letI := torModule T P B
    letI := torModule T Q B'
    torCongr R T P Q e f (r • x) = r • torCongr R T P Q e f x :=
  P103.Ch11.ExtTorDefinitions.tor_linear R 1 T P Q e.hom f.hom r x

/-- The genuine Tor summands are identified using the established homology bridges. -/
def torSummandEquiv (P : P202Specs.TopologicalKunneth.Models.{u,w} R)
    (T : TorMaps.{u,max u w,max u w} R 1) (X Y : TopCat.{w}) (i : ℕ × ℕ) :
    TorTerm (rightSingular R X) (complex R R Y) (singularHomologyModels R X) i ≃ₗ[ℤ]
      P202Specs.TopologicalKunneth.TorSummand R P X Y i :=
  torCongr R T
    (B := ModuleCat.of R (Homology (complex R R Y) i.2))
    (B' := ModuleCat.of R (P202Specs.TopologicalKunneth.H R Y i.2))
    (singularHomologyModels R X i.1) (P X i.1)
    (rightOrdinaryHomologyIso R X i.1)
    (ordinaryQuotientHomologyEquiv R Y i.2).toModuleIso

/-- Direct sums of the actual Tor identifications, with the empty tail preserved. -/
def torDiagonalEquiv (P : P202Specs.TopologicalKunneth.Models.{u,w} R)
    (T : TorMaps.{u,max u w,max u w} R 1) (X Y : TopCat.{w}) (n : ℕ) :
    TorDiagonal (rightSingular R X) (complex R R Y) (singularHomologyModels R X) n ≃ₗ[ℤ]
      P202Specs.TopologicalKunneth.TorSum R P T X Y n :=
  DirectSum.congrLinearEquiv (fun i : P103.Specs.Ch11.KunnethSequence.TailDiagonal n =>
    torSummandEquiv R P T X Y i.val)


@[simp] theorem torDiagonalEquiv_apply
    (P : P202Specs.TopologicalKunneth.Models.{u,w} R)
    (T : TorMaps.{u,max u w,max u w} R 1) (X Y : TopCat.{w}) (n : ℕ)
    (x : TorDiagonal (rightSingular R X) (complex R R Y) (singularHomologyModels R X) n)
    (i : P103.Specs.Ch11.KunnethSequence.TailDiagonal n) :
    (show ⨁ j : P202Specs.TopologicalKunneth.TailDiagonal n,
      P202Specs.TopologicalKunneth.TorSummand R P X Y j.val from
      torDiagonalEquiv R P T X Y n x) i = torSummandEquiv R P T X Y i.val (x i) := rfl

/-- Both-variable naturality follows from the two actual homology bridge squares. -/
theorem torDiagonalEquiv_natural
    (P : P202Specs.TopologicalKunneth.Models.{u,w} R)
    (T : TorMaps.{u,max u w,max u w} R 1)
    {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ)
    (hright : ∀ p,
      ModuleCat.ofHom (homologyMap (commRightOrdinaryMap (chainMap R R f)) p) ≫
        (rightOrdinaryHomologyIso R X' p).hom =
      (rightOrdinaryHomologyIso R X p).hom ≫
        (commRightFunctor R).map (ModuleCat.ofHom (P202Specs.TopologicalKunneth.hMap R f p)))
    (hleft : ∀ q,
      ModuleCat.ofHom (homologyMap (chainMap R R g) q) ≫
        (ordinaryQuotientHomologyEquiv R Y' q).toModuleIso.hom =
      (ordinaryQuotientHomologyEquiv R Y q).toModuleIso.hom ≫
        ModuleCat.ofHom (P202Specs.TopologicalKunneth.hMap R g q))
    (x : TorDiagonal (rightSingular R X) (complex R R Y) (singularHomologyModels R X) n) :
    torDiagonalEquiv R P T X' Y' n
      (torDiagonalMap (commRightOrdinaryMap (chainMap R R f)) (chainMap R R g)
        (singularHomologyModels R X) (singularHomologyModels R X') T n x) =
      P202Specs.TopologicalKunneth.torSumMap R P T f g n
        (torDiagonalEquiv R P T X Y n x) := by
  unfold P202Specs.TopologicalKunneth.TorSum
  ext i
  exact torCongr_natural R T
    (singularHomologyModels R X i.val.1) (singularHomologyModels R X' i.val.1)
    (P X i.val.1) (P X' i.val.1)
    (rightOrdinaryHomologyIso R X i.val.1) (rightOrdinaryHomologyIso R X' i.val.1)
    (ordinaryQuotientHomologyEquiv R Y i.val.2).toModuleIso
    (ordinaryQuotientHomologyEquiv R Y' i.val.2).toModuleIso
    _ _ _ _ (hright i.val.1) (hleft i.val.2) (x i)

/-- The established coefficient action on the algebraic Tor tail becomes the
coefficient module action on the original topological Tor tail. -/
theorem torDiagonalEquiv_scalar
    (P : P202Specs.TopologicalKunneth.Models.{u,w} R)
    (T : TorMaps.{u,max u w,max u w} R 1) (X Y : TopCat.{w}) (n : ℕ) (r : R)
    (x : TorDiagonal (rightSingular R X) (complex R R Y) (singularHomologyModels R X) n) :
    torDiagonalEquiv R P T X Y n
      (P103.Specs.Ch11.KunnethFreeSplitting.torScalar
        (rightSingular R X) (complex R R Y) (singularHomologyModels R X) T n r x) =
      r • torDiagonalEquiv R P T X Y n x := by
  letI (i : P202Specs.TopologicalKunneth.TailDiagonal n) :
      Module R (P202Specs.TopologicalKunneth.TorSummand R P X Y i.val) :=
    torModule T (P X i.val.1) (ModuleCat.of R (P202Specs.TopologicalKunneth.H R Y i.val.2))
  unfold P202Specs.TopologicalKunneth.TorSum
  ext i
  change torSummandEquiv R P T X Y i.val
    (T.map (singularHomologyModels R X i.val.1) (singularHomologyModels R X i.val.1)
      (ModuleCat.ofHom (homologyMap (𝟙 (rightSingular R X)) i.val.1))
      (ModuleCat.ofHom (homologyMap
        (P103.Specs.Ch11.KunnethFreeSplitting.scalarChainMap (complex R R Y) r) i.val.2))
      (x i)) = r • torSummandEquiv R P T X Y i.val (x i)
  have hid : homologyMap (𝟙 (rightSingular R X)) i.val.1 = LinearMap.id :=
    P103.Ch10.Complexes.homologyMap_id (rightSingular R X) i.val.1
  have hsc : homologyMap
      (P103.Specs.Ch11.KunnethFreeSplitting.scalarChainMap (complex R R Y) r) i.val.2 =
      r • LinearMap.id :=
    P103.Ch11.KunnethFreeSplitting.homologyMap_scalar (complex R R Y) i.val.2 r
  rw [hid, hsc]
  exact torCongr_scalar R T
    (singularHomologyModels R X i.val.1) (P X i.val.1)
    (rightOrdinaryHomologyIso R X i.val.1)
    (ordinaryQuotientHomologyEquiv R Y i.val.2).toModuleIso r (x i)


end TorTransport

section ExternalProductIdentification
open P103.Specs.Ch10.Complexes P202Specs.EilenbergZilber

section AlphaExternal
open P103.Specs.Ch10.Complexes
theorem rightFunctor_homologyπ (C : ChainComplex (ModuleCat.{max u v} R) ℕ) (n : ℕ) :
    ((C.sc n).map (commRightFunctor R)).homologyπ ≫
      ((C.sc n).mapHomologyIso (commRightFunctor R)).hom =
    ((C.sc n).mapCyclesIso (commRightFunctor R)).hom ≫
      (commRightFunctor R).map (C.homologyπ n) := by
  let S := C.sc n
  let F := commRightFunctor R
  let h := S.homologyData.left
  change (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
    (S.mapCyclesIso F).hom ≫ F.map S.homologyπ
  rw [h.mapHomologyIso_eq F, h.mapCyclesIso_eq F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, (h.map F).homologyπ_comp_homologyIso_hom]
  simp only [Category.assoc, ShortComplex.LeftHomologyData.map_π]
  rw [← F.map_comp, h.π_comp_homologyIso_inv, F.map_comp]

def rightSingularCycles (X : TopCat.{w}) (n : ℕ)
    (z : cycles (rightSingular R X) n) : (complex R R X).cycles n :=
  (((complex R R X).sc n).mapCyclesIso (commRightFunctor R)).hom
    (quotientCyclesEquiv Rᵐᵒᵖ _ n z)

theorem rightSingularCycles_val (X : TopCat.{w}) (n : ℕ)
    (z : cycles (rightSingular R X) n) :
    (complex R R X).iCycles n (rightSingularCycles R X n z) = z.val := by
  have hi := congrArg (fun f => f.hom (quotientCyclesEquiv Rᵐᵒᵖ _ n z))
    (((complex R R X).sc n).mapCyclesIso_hom_iCycles (commRightFunctor R))
  change (complex R R X).iCycles n (rightSingularCycles R X n z) = _ at hi
  exact hi.trans (quotientCyclesEquiv_val Rᵐᵒᵖ _ n z)

theorem rightOrdinaryHomologyIso_class (X : TopCat.{w}) (n : ℕ)
    (z : cycles (rightSingular R X) n) :
    (rightOrdinaryHomologyIso R X n).hom (homologyClass _ n z) =
      (P202Specs.EilenbergZilber.ordinaryHomologyIso R X n).inv
        ((complex R R X).homologyπ n (rightSingularCycles R X n z)) := by
  change (P202Specs.EilenbergZilber.ordinaryHomologyIso R X n).inv
      ((((complex R R X).sc n).mapHomologyIso (commRightFunctor R)).hom
        (quotientHomologyEquiv Rᵐᵒᵖ _ n (homologyClass _ n z))) = _
  rw [quotientHomologyEquiv_class]
  apply congrArg (P202Specs.EilenbergZilber.ordinaryHomologyIso R X n).inv
  exact congrArg (fun f => f.hom (quotientCyclesEquiv Rᵐᵒᵖ _ n z))
    (rightFunctor_homologyπ R (complex R R X) n)

theorem ordinaryQuotientHomologyEquiv_class (X : TopCat.{w}) (n : ℕ)
    (z : cycles (complex R R X) n) :
    ordinaryQuotientHomologyEquiv R X n (homologyClass _ n z) =
      (P202Specs.EilenbergZilber.ordinaryHomologyIso R X n).inv
        ((complex R R X).homologyπ n (quotientCyclesEquiv R _ n z)) := by
  change (P202Specs.EilenbergZilber.ordinaryHomologyIso R X n).inv
      (quotientHomologyEquiv R _ n (homologyClass _ n z)) = _
  rw [quotientHomologyEquiv_class]

set_option maxHeartbeats 2000000 in
theorem transported_alpha_external
    (hequivalence : P202Specs.EilenbergZilber.equivalence_type.{u,w})
    (e : P202Specs.EilenbergZilber.ExternalProduct.{u,w} R)
    (X Y : TopCat.{w}) (c : P202Specs.EilenbergZilber.Comparison R X Y)
    (P : HomologyModels (rightSingular R X)) (p q : ℕ)
    (S : NormalizedDegreeSequence (rightSingular R X) (complex R R Y) P (p+q))
    (a : P202Specs.TopologicalKunneth.H R X p)
    (b : P202Specs.TopologicalKunneth.H R Y q) :
    productHomologyEquiv R hequivalence X Y c (p+q)
      (S.α ((tensorHomologyDiagonalEquiv R X Y (p+q)).symm
        (DirectSum.lof R _ _ (⟨(p,q),rfl⟩ : P202Specs.AlexanderWhitney.Diagonal (p+q))
          (a ⊗ₜ[R] b)))) =
      P202Specs.TopologicalKunneth.ordinaryExternal R e X Y p q (a ⊗ₜ[R] b) := by
  obtain ⟨a, rfl⟩ := (rightOrdinaryHomologyIso R X p).toLinearEquiv.surjective a
  obtain ⟨b, rfl⟩ := (ordinaryQuotientHomologyEquiv R Y q).surjective b
  obtain ⟨a, rfl⟩ := (cycleBoundaries (rightSingular R X) p).mkQ_surjective a
  obtain ⟨b, rfl⟩ := (cycleBoundaries (complex R R Y) q).mkQ_surjective b
  let z : cycles (ordinaryTotal (rightSingular R X) (complex R R Y)) (p+q) :=
    ⟨ordinaryInclusion (rightSingular R X) (complex R R Y) p q (p+q) rfl
      (P103.BalancedTensor.tmul R a.val b.val),
      P103.Ch11.KunnethSequence.pure_tensor_cycle R _ _ p q (p+q) rfl a b⟩
  have hA : (tensorHomologyDiagonalEquiv R X Y (p+q)).symm
      (DirectSum.lof R _ _ (⟨(p,q),rfl⟩ : P202Specs.AlexanderWhitney.Diagonal (p+q))
        ((rightOrdinaryHomologyIso R X p).hom (homologyClass _ p a) ⊗ₜ[R]
          ordinaryQuotientHomologyEquiv R Y q (homologyClass _ q b))) =
      DirectSum.lof ℤ _ _ (⟨(p,q),rfl⟩ : P202Specs.AlexanderWhitney.Diagonal (p+q))
        (P103.BalancedTensor.tmul R (homologyClass _ p a) (homologyClass _ q b)) := by
    apply (tensorHomologyDiagonalEquiv R X Y (p+q)).injective
    rw [LinearEquiv.apply_symm_apply, tensorHomologyDiagonalEquiv_lof,
      balancedHomologyEquiv_tmul]
  change productHomologyEquiv R hequivalence X Y c (p+q) (S.α
    ((tensorHomologyDiagonalEquiv R X Y (p+q)).symm _)) = _
  erw [hA]
  rw [S.α_formula ⟨(p,q),rfl⟩ a b z rfl]
  change (shuffleOrdinaryHomologyIso R hequivalence X Y c (p+q)).hom
    (algebraicTensorHomologyEquiv R X Y (p+q) (homologyClass _ (p+q) z)) = _
  rw [algebraicTensorHomologyEquiv_class]
  have hz : (tensorComplex R X Y).iCycles (p+q)
      (algebraicTensorCycles R X Y (p+q) z) =
    LinearMap.single R
      (fun i : P202Specs.AlexanderWhitney.Diagonal (p+q) => Summand R X Y i.val.1 i.val.2)
      ⟨(p,q),rfl⟩
      ((complex R R X).iCycles p (rightSingularCycles R X p a) ⊗ₜ[R]
        (complex R R Y).iCycles q (quotientCyclesEquiv R _ q b)) := by
    rw [algebraicTensorCycles_val, rightSingularCycles_val, quotientCyclesEquiv_val]
    exact algebraicTotalCoordinates_inclusion R X Y p q a.val b.val
  rw [shuffle_ordinary_homology_external R hequivalence e X Y c p q
    (rightSingularCycles R X p a) (quotientCyclesEquiv R _ q b)
    (algebraicTensorCycles R X Y (p+q) z) hz]
  erw [rightOrdinaryHomologyIso_class, ordinaryQuotientHomologyEquiv_class]

end AlphaExternal

end ExternalProductIdentification

section AdditiveSequenceTransport
universe v₁ v₂ v₃ w₁ w₂ w₃
variable (R : Type u) [CommRing R]
variable {A : Type v₁} {B : Type v₂} {C : Type v₃}
  {A' : Type w₁} {B' : Type w₂} {C' : Type w₃}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
  [Module R A'] [Module R B'] [Module R C']

/-- Transport an integer-linear map to coefficient modules when the actual
scalar endomorphisms are intertwined by the established equivalences. -/
def transportAdditiveMap (f : A →+ B) (a : A ≃+ A') (b : B ≃+ B')
    (σ : R → A →+ A) (τ : R → B →+ B)
    (ha : ∀ r x, a (σ r x) = r • a x)
    (hb : ∀ r x, b (τ r x) = r • b x)
    (hf : ∀ r x, f (σ r x) = τ r (f x)) : A' →ₗ[R] B' where
  toFun x := b (f (a.symm x))
  map_add' x y := by simp only [map_add]
  map_smul' r x := by
    have hx : a.symm (r • x) = σ r (a.symm x) := by
      apply a.injective
      rw [a.apply_symm_apply, ha, a.apply_symm_apply]
    simpa only [RingHom.id_apply] using (congrArg b (congrArg f hx)).trans
      ((congrArg b (hf r (a.symm x))).trans (hb r (f (a.symm x))))

@[simp] theorem transportAdditiveMap_apply
    (f : A →+ B) (a : A ≃+ A') (b : B ≃+ B')
    (σ : R → A →+ A) (τ : R → B →+ B)
    (ha : ∀ r x, a (σ r x) = r • a x)
    (hb : ∀ r x, b (τ r x) = r • b x)
    (hf : ∀ r x, f (σ r x) = τ r (f x)) (x : A') :
    transportAdditiveMap R f a b σ τ ha hb hf x = b (f (a.symm x)) := rfl

/-- Exactness is preserved by the three actual additive equivalences. -/
theorem transportAdditiveExact (f : A →+ B) (g : B →+ C)
    (a : A ≃+ A') (b : B ≃+ B') (c : C ≃+ C')
    (h : Function.Exact f g) :
    Function.Exact (fun x => b (f (a.symm x))) (fun y => c (g (b.symm y))) := by
  intro y
  constructor
  · intro hy
    have hg : g (b.symm y) = 0 := c.injective (hy.trans c.map_zero.symm)
    obtain ⟨x, hx⟩ := (h (b.symm y)).mp hg
    exact ⟨a x, by simpa only [a.symm_apply_apply, hx, b.apply_symm_apply]⟩
  · rintro ⟨x, rfl⟩
    change c (g (b.symm (b (f (a.symm x)))) ) = 0
    rw [b.symm_apply_apply, h.apply_apply_eq_zero, map_zero]

/-- A transported injection remains injective. -/
theorem transportAdditiveInjective (f : A →+ B) (a : A ≃+ A') (b : B ≃+ B')
    (h : Function.Injective f) : Function.Injective (fun x => b (f (a.symm x))) :=
  b.injective.comp (h.comp a.symm.injective)

/-- A transported surjection remains surjective. -/
theorem transportAdditiveSurjective (g : B →+ C) (b : B ≃+ B') (c : C ≃+ C')
    (h : Function.Surjective g) : Function.Surjective (fun y => c (g (b.symm y))) :=
  c.surjective.comp (h.comp b.symm.surjective)

/-- Scalar-compatible splitting of the algebraic last arrow gives an actual
R-linear section of its transported last arrow. -/
theorem transportAdditiveSplitting (g : B →+ C) (b : B ≃+ B') (c : C ≃+ C')
    (τ : R → B →+ B) (υ : R → C →+ C)
    (hb : ∀ r x, b (τ r x) = r • b x)
    (hc : ∀ r x, c (υ r x) = r • c x)
    (hg : ∀ r x, g (τ r x) = υ r (g x))
    (s : C →+ B) (hs : ∀ x, g (s x) = x)
    (hs_scalar : ∀ r x, s (υ r x) = τ r (s x)) :
    ∃ t : C' →ₗ[R] B',
      (transportAdditiveMap R g b c τ υ hb hc hg).comp t = LinearMap.id := by
  refine ⟨transportAdditiveMap R s c b υ τ hc hb hs_scalar, ?_⟩
  ext x
  change c (g (b.symm (b (s (c.symm x))))) = x
  rw [b.symm_apply_apply]
  have hx := hs (c.symm x)
  rw [hx, c.apply_symm_apply]


end AdditiveSequenceTransport

section ActualTopologicalSequence
open P103.Specs.Ch10.Complexes P202Specs.EilenbergZilber
/-- The normalized algebraic injection intertwines the genuine scalar
endomorphisms of its source and target. -/
theorem algebraicAlphaScalar
    (T : TorMaps.{u,max u w,max u w} R 1) (X Y : TopCat.{w}) (n : ℕ)
    (S : NormalizedDegreeSequence (rightSingular R X) (complex R R Y)
      (singularHomologyModels R X) n)
    (r : R) (a : TensorDiagonal (rightSingular R X) (complex R R Y) n) :
    S.α (tensorDiagonalMap (𝟙 (rightSingular R X))
      (P103.Specs.Ch11.KunnethFreeSplitting.scalarChainMap (complex R R Y) r) n a) =
    P103.Specs.Ch11.KunnethFreeSplitting.totalScalar
      (rightSingular R X) (complex R R Y) n r (S.α a) := by
  have h := (P103.Ch11.KunnethSequence.normalized_natural R
    (rightSingular R X) (rightSingular R X) (complex R R Y) (complex R R Y)
    (𝟙 (rightSingular R X))
    (P103.Specs.Ch11.KunnethFreeSplitting.scalarChainMap (complex R R Y) r)
    (singularHomologyModels R X) (singularHomologyModels R X) T n S S).1
  exact (LinearMap.congr_fun h a).symm

/-- The normalized last arrow intertwines the genuine scalar action on total
homology and P103's coefficient action on Tor. -/
theorem algebraicBetaScalar
    (T : TorMaps.{u,max u w,max u w} R 1) (X Y : TopCat.{w}) (n : ℕ)
    (S : NormalizedDegreeSequence (rightSingular R X) (complex R R Y)
      (singularHomologyModels R X) n)
    (r : R) (x : Homology (ordinaryTotal (rightSingular R X) (complex R R Y)) n) :
    S.β (P103.Specs.Ch11.KunnethFreeSplitting.totalScalar
      (rightSingular R X) (complex R R Y) n r x) =
      P103.Specs.Ch11.KunnethFreeSplitting.torScalar
      (rightSingular R X) (complex R R Y) (singularHomologyModels R X) T n r (S.β x) := by
  have h := (P103.Ch11.KunnethSequence.normalized_natural R
    (rightSingular R X) (rightSingular R X) (complex R R Y) (complex R R Y)
    (𝟙 (rightSingular R X))
    (P103.Specs.Ch11.KunnethFreeSplitting.scalarChainMap (complex R R Y) r)
    (singularHomologyModels R X) (singularHomologyModels R X) T n S S).2
  exact (LinearMap.congr_fun h x).symm

/-- The first topological arrow, obtained from the actual algebraic injection
and the specified shuffle comparison. -/
def transportedAlpha
    (hequivalence : P202Specs.EilenbergZilber.equivalence_type.{u,w})
    (T : TorMaps.{u,max u w,max u w} R 1) (X Y : TopCat.{w})
    (c : Comparison R X Y) (n : ℕ)
    (S : NormalizedDegreeSequence (rightSingular R X) (complex R R Y)
      (singularHomologyModels R X) n) :
    P202Specs.TopologicalKunneth.TensorSum R X Y n →ₗ[R]
      P202Specs.TopologicalKunneth.H R (productSpace X Y) n :=
  transportAdditiveMap R
    (A := TensorDiagonal (rightSingular R X) (complex R R Y) n)
    (B := Homology (ordinaryTotal (rightSingular R X) (complex R R Y)) n)
    S.α.toAddMonoidHom (tensorHomologyDiagonalEquiv R X Y n).toAddEquiv
    (productHomologyEquiv R hequivalence X Y c n).toAddEquiv
    (fun r => (tensorDiagonalMap (𝟙 (rightSingular R X))
      (P103.Specs.Ch11.KunnethFreeSplitting.scalarChainMap (complex R R Y) r) n).toAddMonoidHom)
    (fun r => (P103.Specs.Ch11.KunnethFreeSplitting.totalScalar
      (rightSingular R X) (complex R R Y) n r).toAddMonoidHom)
    (tensorHomologyDiagonalEquiv_scalar R X Y n)
    (productHomologyEquiv_scalar R hequivalence X Y c n)
    (algebraicAlphaScalar R T X Y n S)

/-- The last topological arrow uses the actual Tor maps and module actions. -/
def transportedBeta
    (hequivalence : P202Specs.EilenbergZilber.equivalence_type.{u,w})
    (P : P202Specs.TopologicalKunneth.Models.{u,w} R)
    (T : TorMaps.{u,max u w,max u w} R 1) (X Y : TopCat.{w})
    (c : Comparison R X Y) (n : ℕ)
    (S : NormalizedDegreeSequence (rightSingular R X) (complex R R Y)
      (singularHomologyModels R X) n) :
    P202Specs.TopologicalKunneth.H R (productSpace X Y) n →ₗ[R]
      P202Specs.TopologicalKunneth.TorSum R P T X Y n :=
  transportAdditiveMap R
    (A := Homology (ordinaryTotal (rightSingular R X) (complex R R Y)) n)
    (B := TorDiagonal (rightSingular R X) (complex R R Y) (singularHomologyModels R X) n)
    S.β.toAddMonoidHom (productHomologyEquiv R hequivalence X Y c n).toAddEquiv
    (torDiagonalEquiv R P T X Y n).toAddEquiv
    (fun r => (P103.Specs.Ch11.KunnethFreeSplitting.totalScalar
      (rightSingular R X) (complex R R Y) n r).toAddMonoidHom)
    (fun r => (P103.Specs.Ch11.KunnethFreeSplitting.torScalar
      (rightSingular R X) (complex R R Y) (singularHomologyModels R X) T n r).toAddMonoidHom)
    (productHomologyEquiv_scalar R hequivalence X Y c n)
    (torDiagonalEquiv_scalar R P T X Y n)
    (algebraicBetaScalar R T X Y n S)

/-- The transported first arrow is injective. -/
theorem transportedAlpha_injective
    (hequivalence : P202Specs.EilenbergZilber.equivalence_type.{u,w})
    (T : TorMaps.{u,max u w,max u w} R 1) (X Y : TopCat.{w})
    (c : Comparison R X Y) (n : ℕ)
    (S : NormalizedDegreeSequence (rightSingular R X) (complex R R Y)
      (singularHomologyModels R X) n) :
    Function.Injective (transportedAlpha R hequivalence T X Y c n S) :=
  (productHomologyEquiv R hequivalence X Y c n).injective.comp
    (S.injective_α.comp (tensorHomologyDiagonalEquiv R X Y n).symm.injective)

/-- Exactness is transported through the three actual module presentations. -/
theorem transported_exact
    (hequivalence : P202Specs.EilenbergZilber.equivalence_type.{u,w})
    (P : P202Specs.TopologicalKunneth.Models.{u,w} R)
    (T : TorMaps.{u,max u w,max u w} R 1) (X Y : TopCat.{w})
    (c : Comparison R X Y) (n : ℕ)
    (S : NormalizedDegreeSequence (rightSingular R X) (complex R R Y)
      (singularHomologyModels R X) n) :
    Function.Exact (transportedAlpha R hequivalence T X Y c n S)
      (transportedBeta R hequivalence P T X Y c n S) :=
  by
  intro y
  change torDiagonalEquiv R P T X Y n
      (S.β ((productHomologyEquiv R hequivalence X Y c n).symm y)) = 0 ↔
    ∃ a, productHomologyEquiv R hequivalence X Y c n
      (S.α ((tensorHomologyDiagonalEquiv R X Y n).symm a)) = y
  constructor
  · intro hy
    have hg : S.β ((productHomologyEquiv R hequivalence X Y c n).symm y) = 0 :=
      (torDiagonalEquiv R P T X Y n).injective
        (hy.trans (torDiagonalEquiv R P T X Y n).map_zero.symm)
    obtain ⟨a, ha⟩ := (S.exact _).mp hg
    refine ⟨tensorHomologyDiagonalEquiv R X Y n a, ?_⟩
    rw [LinearEquiv.symm_apply_apply, ha, LinearEquiv.apply_symm_apply]
  · rintro ⟨a, rfl⟩
    rw [LinearEquiv.symm_apply_apply, S.exact.apply_apply_eq_zero, map_zero]

/-- The transported last arrow is surjective. -/
theorem transportedBeta_surjective
    (hequivalence : P202Specs.EilenbergZilber.equivalence_type.{u,w})
    (P : P202Specs.TopologicalKunneth.Models.{u,w} R)
    (T : TorMaps.{u,max u w,max u w} R 1) (X Y : TopCat.{w})
    (c : Comparison R X Y) (n : ℕ)
    (S : NormalizedDegreeSequence (rightSingular R X) (complex R R Y)
      (singularHomologyModels R X) n) :
    Function.Surjective (transportedBeta R hequivalence P T X Y c n S) :=
  (torDiagonalEquiv R P T X Y n).surjective.comp
    (S.surjective_β.comp (productHomologyEquiv R hequivalence X Y c n).symm.surjective)

/-- The R-linear section belongs to this actual last arrow; no natural choice
of a section is asserted. -/
theorem transported_splits [IsDomain R] [IsPrincipalIdealRing R]
    (hequivalence : P202Specs.EilenbergZilber.equivalence_type.{u,w})
    (P : P202Specs.TopologicalKunneth.Models.{u,w} R)
    (T : TorMaps.{u,max u w,max u w} R 1) (X Y : TopCat.{w})
    (c : Comparison R X Y) (n : ℕ)
    (S : NormalizedDegreeSequence (rightSingular R X) (complex R R Y)
      (singularHomologyModels R X) n) :
    ∃ s : P202Specs.TopologicalKunneth.TorSum R P T X Y n →ₗ[R]
        P202Specs.TopologicalKunneth.H R (productSpace X Y) n,
      (transportedBeta R hequivalence P T X Y c n S).comp s = LinearMap.id := by
  obtain ⟨s, hs, hscalar⟩ := algebraic_scalar_splitting R X Y
    (singularHomologyModels R X) n T S
  exact transportAdditiveSplitting R S.β.toAddMonoidHom (productHomologyEquiv R hequivalence X Y c n).toAddEquiv
    (torDiagonalEquiv R P T X Y n).toAddEquiv
    (fun r => (P103.Specs.Ch11.KunnethFreeSplitting.totalScalar
      (rightSingular R X) (complex R R Y) n r).toAddMonoidHom)
    (fun r => (P103.Specs.Ch11.KunnethFreeSplitting.torScalar
      (rightSingular R X) (complex R R Y) (singularHomologyModels R X) T n r).toAddMonoidHom)
    (productHomologyEquiv_scalar R hequivalence X Y c n)
    (torDiagonalEquiv_scalar R P T X Y n)
    (algebraicBetaScalar R T X Y n S) s.toAddMonoidHom
      (fun x => LinearMap.congr_fun hs x) (fun r x => (LinearMap.congr_fun (hscalar r) x).symm)


end ActualTopologicalSequence


section SequenceNaturality
open P103.Specs.Ch10.Complexes P202Specs.EilenbergZilber

/-- Naturality of the Tor-diagonal comparison for arbitrary maps of spaces. -/
theorem torDiagonalEquiv_natural_spaces
    (P : P202Specs.TopologicalKunneth.Models.{u,w} R)
    (T : TorMaps.{u,max u w,max u w} R 1)
    {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ)
    (x : TorDiagonal (rightSingular R X) (complex R R Y) (singularHomologyModels R X) n) :
    torDiagonalEquiv R P T X' Y' n
      (torDiagonalMap (commRightOrdinaryMap (chainMap R R f)) (chainMap R R g)
        (singularHomologyModels R X) (singularHomologyModels R X') T n x) =
      P202Specs.TopologicalKunneth.torSumMap R P T f g n
        (torDiagonalEquiv R P T X Y n x) := by
  apply torDiagonalEquiv_natural R P T f g n
  · intro p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact rightOrdinaryHomologyIso_natural R f p z
  · intro q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact ordinaryQuotientHomologyEquiv_natural R g q z

end SequenceNaturality

section ActualSequenceNaturality
open P103.Specs.Ch10.Complexes P202Specs.EilenbergZilber

/-- The actual transported injection is natural in both arbitrary spaces. -/
theorem transportedAlpha_natural
    (hequivalence : P202Specs.EilenbergZilber.equivalence_type.{u,w})
    (T : TorMaps.{u,max u w,max u w} R 1)
    (c : ∀ X Y : TopCat.{w}, Comparison R X Y)
    (hc : ∀ {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ),
      ((chainMap R R (productMap f g)).f n).hom.comp ((c X Y).fromTensor.f n).hom =
        ((c X' Y').fromTensor.f n).hom.comp (totalMap R f g n))
    {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ)
    (S : NormalizedDegreeSequence (rightSingular R X) (complex R R Y)
      (singularHomologyModels R X) n)
    (S' : NormalizedDegreeSequence (rightSingular R X') (complex R R Y')
      (singularHomologyModels R X') n) :
    (P202Specs.TopologicalKunneth.hMap R (productMap f g) n).comp
        (transportedAlpha R hequivalence T X Y (c X Y) n S) =
      (transportedAlpha R hequivalence T X' Y' (c X' Y') n S').comp
        (P202Specs.TopologicalKunneth.tensorSumMap R f g n) := by
  apply LinearMap.ext
  intro x
  exact transportNatural
    (tensorHomologyDiagonalEquiv R X Y n).toEquiv
    (productHomologyEquiv R hequivalence X Y (c X Y) n).toEquiv
    (tensorHomologyDiagonalEquiv R X' Y' n).toEquiv
    (productHomologyEquiv R hequivalence X' Y' (c X' Y') n).toEquiv
    S.α S'.α
    (tensorDiagonalMap (commRightOrdinaryMap (chainMap R R f)) (chainMap R R g) n)
    (homologyMap (ordinaryTotalMap (commRightOrdinaryMap (chainMap R R f))
      (chainMap R R g)) n)
    (P202Specs.TopologicalKunneth.tensorSumMap R f g n)
    (P202Specs.TopologicalKunneth.hMap R (productMap f g) n)
    (tensorHomologyDiagonalEquiv_natural R f g n)
    (productHomologyEquiv_natural R hequivalence c hc f g n)
    (fun z => LinearMap.congr_fun (P103.Ch11.KunnethSequence.normalized_natural R
      (rightSingular R X) (rightSingular R X') (complex R R Y) (complex R R Y')
      (commRightOrdinaryMap (chainMap R R f)) (chainMap R R g)
      (singularHomologyModels R X) (singularHomologyModels R X') T n S S').1 z) x

/-- The actual transported surjection is natural, with the genuine functorial
Tor maps in both ordinary homology variables. -/
theorem transportedBeta_natural
    (hequivalence : P202Specs.EilenbergZilber.equivalence_type.{u,w})
    (P : P202Specs.TopologicalKunneth.Models.{u,w} R)
    (T : TorMaps.{u,max u w,max u w} R 1)
    (c : ∀ X Y : TopCat.{w}, Comparison R X Y)
    (hc : ∀ {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ),
      ((chainMap R R (productMap f g)).f n).hom.comp ((c X Y).fromTensor.f n).hom =
        ((c X' Y').fromTensor.f n).hom.comp (totalMap R f g n))
    {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ)
    (S : NormalizedDegreeSequence (rightSingular R X) (complex R R Y)
      (singularHomologyModels R X) n)
    (S' : NormalizedDegreeSequence (rightSingular R X') (complex R R Y')
      (singularHomologyModels R X') n)
    (x : P202Specs.TopologicalKunneth.H R (productSpace X Y) n) :
    P202Specs.TopologicalKunneth.torSumMap R P T f g n
        (transportedBeta R hequivalence P T X Y (c X Y) n S x) =
      transportedBeta R hequivalence P T X' Y' (c X' Y') n S'
        (P202Specs.TopologicalKunneth.hMap R (productMap f g) n x) := by
  exact transportNatural
    (productHomologyEquiv R hequivalence X Y (c X Y) n).toEquiv
    (torDiagonalEquiv R P T X Y n).toEquiv
    (productHomologyEquiv R hequivalence X' Y' (c X' Y') n).toEquiv
    (torDiagonalEquiv R P T X' Y' n).toEquiv
    S.β S'.β
    (homologyMap (ordinaryTotalMap (commRightOrdinaryMap (chainMap R R f))
      (chainMap R R g)) n)
    (torDiagonalMap (commRightOrdinaryMap (chainMap R R f)) (chainMap R R g)
      (singularHomologyModels R X) (singularHomologyModels R X') T n)
    (P202Specs.TopologicalKunneth.hMap R (productMap f g) n)
    (P202Specs.TopologicalKunneth.torSumMap R P T f g n)
    (productHomologyEquiv_natural R hequivalence c hc f g n)
    (torDiagonalEquiv_natural_spaces R P T f g n)
    (fun z => LinearMap.congr_fun (P103.Ch11.KunnethSequence.normalized_natural R
      (rightSingular R X) (rightSingular R X') (complex R R Y) (complex R R Y')
      (commRightOrdinaryMap (chainMap R R f)) (chainMap R R g)
      (singularHomologyModels R X) (singularHomologyModels R X') T n S S').2 z) x

end ActualSequenceNaturality


/-- Auxiliary derivation of the full Künneth conclusion from the
Eilenberg--Zilber interfaces. The closed theorem below supplies these proofs. -/
theorem kunneth_conditional :
    P202Specs.EilenbergZilber.comparison_type.{u,w} →
    P202Specs.EilenbergZilber.equivalence_type.{u,w} →
    P202Specs.EilenbergZilber.externalProduct_type.{u,w} →
    P202Specs.EilenbergZilber.naturalComparison_type.{u,w} →
    P202Specs.EilenbergZilber.naturalHomotopies_type.{u,w} →
    P202Specs.EilenbergZilber.relativeCompatibility_type.{u,w} →
    P202Specs.EilenbergZilber.smoothAW_type.{u,w} →
    P202Specs.TopologicalKunneth.kunneth_type.{u,w} := by
  intro _hcomparison hequivalence hexternal hnatural _hhomotopies _hrelative _hsmooth
  intro R _ _ _
  let P : P202Specs.TopologicalKunneth.Models.{u,w} R := topologicalModels R
  let T : TorMaps.{u,max u w,max u w} R 1 := P103.Ch11.ExtTorDefinitions.torMaps (R := R) 1
  obtain ⟨c, _hAW, hshuffle⟩ := hnatural R
  let e : P202Specs.EilenbergZilber.ExternalProduct.{u,w} R := Classical.choice (hexternal R)
  let S : ∀ (X Y : TopCat.{w}) (n : ℕ),
      NormalizedDegreeSequence (rightSingular R X) (complex R R Y)
        (singularHomologyModels R X) n :=
    fun X Y n => Classical.choice (algebraic_sequence R X Y (singularHomologyModels R X) n)
  refine ⟨P, T, ?_, fun X Y => tor_zero R P T X Y⟩
  refine ⟨{
    external := e
    α := fun X Y n => transportedAlpha R hequivalence T X Y (c X Y) n (S X Y n)
    β := fun X Y n => transportedBeta R hequivalence P T X Y (c X Y) n (S X Y n)
    injective_α := fun X Y n =>
      transportedAlpha_injective R hequivalence T X Y (c X Y) n (S X Y n)
    exact := fun X Y n =>
      transported_exact R hequivalence P T X Y (c X Y) n (S X Y n)
    surjective_β := fun X Y n =>
      transportedBeta_surjective R hequivalence P T X Y (c X Y) n (S X Y n)
    α_external := ?_
    naturality_α := fun f g n =>
      transportedAlpha_natural R hequivalence T c hshuffle f g n (S _ _ n) (S _ _ n)
    naturality_β := fun f g n x =>
      transportedBeta_natural R hequivalence P T c hshuffle f g n (S _ _ n) (S _ _ n) x
    splits := fun X Y n =>
      transported_splits R hequivalence P T X Y (c X Y) n (S X Y n)
  }⟩
  intro X Y p q a b
  change productHomologyEquiv R hequivalence X Y (c X Y) (p+q)
    ((S X Y (p+q)).α ((tensorHomologyDiagonalEquiv R X Y (p+q)).symm
      (DirectSum.lof R _ _ (⟨(p,q),rfl⟩ : P202Specs.AlexanderWhitney.Diagonal (p+q))
        (a ⊗ₜ[R] b)))) = _
  exact transported_alpha_external R hequivalence e X Y (c X Y)
    (singularHomologyModels R X) p q (S X Y (p+q)) a b

/-- Homological Künneth over a PID for arbitrary spaces: the natural short
exact sequence has the shuffle external product as its first map, admits an
R-linear section, and has zero Tor term in degree zero. -/
theorem kunneth : P202Specs.TopologicalKunneth.kunneth_type.{u,w} :=
  kunneth_conditional
    P202.EilenbergZilber.comparison_exists
    P202.EilenbergZilber.equivalence
    P202.EilenbergZilber.externalProduct
    P202.EilenbergZilber.naturalComparison
    P202.EilenbergZilber.naturalHomotopies
    P202.EilenbergZilber.relativeCompatibility
    P202.EilenbergZilber.smoothAW

end P202.TopologicalKunneth
