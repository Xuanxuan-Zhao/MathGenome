import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.RankTwoSchubertStrata
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.BoundedLattices
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SchubertAnalyticFlagTransport
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SchubertNormalizedJetGraphSchemes
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Order.Interval.Finset.Fin
import Batteries.Tactic.OpenPrivate

namespace RepTheorySurvey.Geometric.RankTwoSchubertStrata

noncomputable section

open LatticeModelSpecs BoundedLatticeSpecs RankTwoSchubertStrataSpecs

open scoped Matrix MatrixGroups

theorem below_iff (cd ab : DominantPair) :
    Below cd ab ↔ cd.val.1 + cd.val.2 = ab.val.1 + ab.val.2 ∧
      cd.val.1 ≤ ab.val.1 ∧ ab.val.2 ≤ cd.val.2 := by
  unfold Below
  have hcd : cd.val.2 ≤ cd.val.1 := cd.property
  constructor
  · rintro ⟨j, _, h₁, h₂⟩
    exact ⟨by omega, by omega, by omega⟩
  · rintro ⟨hsum, h₁, h₂⟩
    let j := (ab.val.1 - cd.val.1).toNat
    have hj : (j : ℤ) = ab.val.1 - cd.val.1 :=
      Int.toNat_of_nonneg (sub_nonneg.mpr h₁)
    exact ⟨j, by omega, by omega, by omega⟩

theorem orbitBound_of_below {ab cd : DominantPair} {N : ℕ} (h : Below cd ab)
    (hN : OrbitBound ab N) : OrbitBound cd N := by
  obtain ⟨_, h₁, h₂⟩ := (below_iff cd ab).mp h
  have hcd : cd.val.2 ≤ cd.val.1 := cd.property
  have hU : ab.val.1 ≤ (N : ℤ) := by
    simpa [pairCoweight] using (hN 0).2
  have hL : -(N : ℤ) ≤ ab.val.2 := by
    simpa [pairCoweight] using (hN 1).1
  intro i
  fin_cases i <;> simp [pairCoweight] <;> omega

theorem closureLattices_bounded {ab : DominantPair} {N : ℕ} (hN : OrbitBound ab N)
    {L : GL2Lattice} (hL : L ∈ closureLattices ab) :
    ∃ B : BoundedLattice 2 N, B.val = L := by
  obtain ⟨cd, hcd, hL⟩ := hL
  exact ⟨⟨L, gl2Orbit_bounded cd (orbitBound_of_below hcd hN) hL⟩, rfl⟩

theorem smul_mem_gl2Orbit (ab : DominantPair) (g : PositiveGL 2)
    {L : GL2Lattice} (hL : L ∈ gl2Orbit ab) : g • L ∈ gl2Orbit ab := by
  obtain ⟨k, rfl⟩ := hL
  exact ⟨g * k, mul_smul g k _⟩

theorem smul_mem_closureLattices (ab : DominantPair) (g : PositiveGL 2)
    {L : GL2Lattice} (hL : L ∈ closureLattices ab) : g • L ∈ closureLattices ab := by
  obtain ⟨cd, hcd, hL⟩ := hL
  exact ⟨cd, hcd, smul_mem_gl2Orbit cd g hL⟩

private def jetConstantCoeff (n : ℕ) (hn : 1 ≤ n) : JetRing n →+* ℂ :=
  Ideal.Quotient.lift (jetIdeal n) PowerSeries.constantCoeff (by
    intro x hx
    obtain ⟨y, rfl⟩ := (Ideal.mem_span_singleton.mp hx : t ^ n ∣ x)
    rw [map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), zero_mul])

theorem reduceGL_surjective (r n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective (reduceGL r n hn) := by
  classical
  intro g
  choose a ha using fun i j : Fin r ↦ Ideal.Quotient.mk_surjective (g.val i j)
  let A : Matrix (Fin r) (Fin r) O := a
  have hA : A.map (jetReduction n) = g.val := Matrix.ext ha
  have hdet : (jetReduction n) A.det = g.val.det := by
    rw [← hA]
    exact (jetReduction n).toRingHom.map_det A
  have hu : IsUnit (PowerSeries.constantCoeff A.det) := by
    have h := (Matrix.isUnits_det_units g).map (jetConstantCoeff n hn)
    rw [← hdet] at h
    exact h
  refine ⟨Matrix.GeneralLinearGroup.mk'' A (PowerSeries.isUnit_iff_constantCoeff.mpr hu), ?_⟩
  exact Units.ext hA

private theorem jetActionOn_of_stable (hAction : GLJetAction) (hAnalytic : GLJetChartAnalytic)
    (a : ℤ) (m n : ℕ) (hn : 1 ≤ n) (hmn : m ≤ n) (S : Set GL2Lattice)
    (hS : ∀ (g : PositiveGL 2) {L : GL2Lattice}, L ∈ S → g • L ∈ S) :
    JetActionOn a m n hn hmn S := by
  obtain ⟨ρ, hmap, hreduce, hcont⟩ := hAction 2 a m n hn hmn
  have hmem (g : GLJets 2 n hn) (p : stageImage a m S) :
      ρ.smul g p.val ∈ stageImage a m S := by
    obtain ⟨g₀, rfl⟩ := reduceGL_surjective 2 n hn g
    obtain ⟨p, ⟨L, hL, rfl⟩⟩ := p
    refine ⟨positiveGLMap 2 g₀ • L, hS ⟨positiveGLMap 2 g₀, ⟨g₀, rfl⟩⟩ hL, ?_⟩
    exact (hreduce g₀ L).symm
  let ρS : MulAction (GLJets 2 n hn) (stageImage a m S) :=
    { smul := fun g p ↦ ⟨ρ.smul g p.val, hmem g p⟩
      one_smul := fun p ↦ Subtype.ext (ρ.one_smul p.val)
      mul_smul := fun g k p ↦ Subtype.ext (ρ.mul_smul g k p.val) }
  refine ⟨ρS, fun g p ↦ hmap g p.val, fun g L _ ↦ hreduce g L, ?_, ?_⟩
  · exact (hcont.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  · intro d I g A
    obtain ⟨J, U, F, hpt, hU, hF, hchart⟩ := hAnalytic 2 a m n hn hmn d I g A
    refine ⟨J, U, F, hpt, hU, hF, ?_⟩
    intro g' C p hmem' hp
    exact (hmap g' p.val).trans (hp ▸ hchart g' C hmem')

theorem schubertJetActions : SchubertJetActions := by
  intro ab a m n hn hmn _ _
  let hAction := BoundedLattices.glJetAction
  let hAnalytic := BoundedLattices.glJetChartAnalytic
  exact ⟨jetActionOn_of_stable hAction hAnalytic a m n hn hmn _ (smul_mem_gl2Orbit ab),
    jetActionOn_of_stable hAction hAnalytic a m n hn hmn _ (smul_mem_closureLattices ab)⟩

private theorem mem_diagonalLattice_iff {r : ℕ} (a : Coweight r) (v : Coordinates r) :
    v ∈ (diagonalLattice a).val ↔ ∃ x : Fin r → O, ∀ i, v i = monomial (a i) * inclusion (x i) := by
  change (∃ w ∈ (coordinateInclusion r).range, diagonalEquiv a w = v) ↔ _
  constructor
  · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, fun _ ↦ rfl⟩
  · rintro ⟨x, hx⟩
    exact ⟨coordinateInclusion r x, ⟨x, rfl⟩, funext fun i ↦ (hx i).symm⟩

private theorem exponent_le_of_monomial_eq {u v : ℤ} {q : O}
    (h : monomial u = monomial v * inclusion q) : v ≤ u := by
  have he : monomial (u - v) = inclusion q := by
    apply mul_left_cancel₀ (monomial_ne_zero v)
    rw [← monomial_add, show v + (u - v) = u by omega, h]
  by_contra! hu
  have hc := congrArg (fun z : K ↦ z.coeff (u - v)) he
  change (monomial (u - v)).coeff (u - v) = (q : K).coeff (u - v) at hc
  rw [PowerSeries.coeff_coe, ite_eq_left (sub_neg.mpr hu)] at hc
  simp [monomial] at hc

theorem diagonalLattice_le_iff {r : ℕ} (a b : Coweight r) :
    (diagonalLattice a).val ≤ (diagonalLattice b).val ↔ ∀ i, b i ≤ a i := by
  classical
  refine ⟨?_, diagonalLattice_le⟩
  intro h i
  let x : Fin r → O := Pi.single i 1
  let v := diagonalEquiv a (coordinateInclusion r x)
  have hv : v ∈ (diagonalLattice a).val := (mem_diagonalLattice_iff a v).mpr ⟨x, fun _ ↦ rfl⟩
  obtain ⟨y, hy⟩ := (mem_diagonalLattice_iff b v).mp (h hv)
  apply exponent_le_of_monomial_eq (q := y i)
  have hi := hy i
  change monomial (a i) * inclusion (x i) = _ at hi
  simpa [x] using hi

theorem orbit_endpoints {ab : DominantPair} {L : GL2Lattice} (hL : L ∈ gl2Orbit ab) :
    (∀ c : ℤ, (scalarLattice 2 c).val ≤ L.val ↔ ab.val.1 ≤ c) ∧
    (∀ c : ℤ, L.val ≤ (scalarLattice 2 c).val ↔ c ≤ ab.val.2) := by
  obtain ⟨⟨_, ⟨g, rfl⟩⟩, rfl⟩ := hL
  let e := (loopLinearEquiv 2 (positiveGLMap 2 g)).restrictScalars O
  have hmap (c : ℤ) : (scalarLattice 2 c).val.map e.toLinearMap = (scalarLattice 2 c).val :=
    congrArg Subtype.val (positiveGL_preserves_scalar g c)
  have hab : ab.val.2 ≤ ab.val.1 := ab.property
  constructor
  · intro c
    change (scalarLattice 2 c).val ≤ (diagonalLattice (pairCoweight ab)).val.map e.toLinearMap ↔ _
    rw [← hmap c, Submodule.map_le_map_iff_of_injective e.injective,
      scalarLattice, diagonalLattice_le_iff, Fin.forall_fin_two]
    simp [pairCoweight]
    omega
  · intro c
    change (diagonalLattice (pairCoweight ab)).val.map e.toLinearMap ≤ (scalarLattice 2 c).val ↔ _
    rw [← hmap c, Submodule.map_le_map_iff_of_injective e.injective,
      scalarLattice, diagonalLattice_le_iff, Fin.forall_fin_two]
    simp [pairCoweight]
    omega

theorem orbit_label_unique {ab cd : DominantPair} {L : GL2Lattice}
    (hL : L ∈ gl2Orbit ab) (hL' : L ∈ gl2Orbit cd) : ab = cd := by
  obtain ⟨h₁, h₂⟩ := orbit_endpoints hL
  obtain ⟨h₁', h₂'⟩ := orbit_endpoints hL'
  apply Subtype.ext
  exact Prod.ext
    (le_antisymm ((h₁ _).mp ((h₁' _).mpr le_rfl)) ((h₁' _).mp ((h₁ _).mpr le_rfl)))
    (le_antisymm ((h₂' _).mp ((h₂ _).mpr le_rfl)) ((h₂ _).mp ((h₂' _).mpr le_rfl)))

private def diagonalInclusion {r : ℕ} (a : Coweight r) : (Fin r → O) →ₗ[O] Coordinates r :=
  (diagonalEquiv a).restrictScalars O |>.toLinearMap.comp (coordinateInclusion r)

private theorem diagonalLattice_eq_span {r : ℕ} (a : Coweight r) :
    (diagonalLattice a).val =
      Submodule.span O (Set.range fun i : Fin r ↦ diagonalInclusion a (Pi.basisFun O (Fin r) i)) := by
  change (coordinateInclusion r).range.map _ = _
  rw [Set.range_comp', ← Submodule.map_span, (Pi.basisFun O (Fin r)).span_eq,
    Submodule.map_top, diagonalInclusion, LinearMap.range_comp]

private theorem diagonalInclusion_eq_shifted {r : ℕ} (c : ℤ) (k : Fin r → ℕ) (i : Fin r) :
    diagonalInclusion (fun j ↦ c + (k j : ℤ)) (Pi.basisFun O (Fin r) i) =
      shiftedInclusion r c ((t ^ k i) • Pi.basisFun O (Fin r) i) := by
  classical
  funext j
  change monomial (c + (k j : ℤ)) * inclusion ((Pi.basisFun O (Fin r) i) j) =
    monomial c * inclusion ((t ^ k i) * (Pi.basisFun O (Fin r) i) j)
  by_cases h : j = i
  · subst j
    rw [monomial_add, monomial_nat, map_mul, mul_assoc]
  · simp [Pi.basisFun_apply, h]

private def positiveMatrix {r : ℕ} (e : (Fin r → O) ≃ₗ[O] (Fin r → O)) :
    GL (Fin r) O :=
  (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv O (Fin r → O))).symm e

private theorem positiveMatrix_linear {r : ℕ} (e : (Fin r → O) ≃ₗ[O] (Fin r → O))
    (c : ℤ) (x : Fin r → O) :
    loopLinearEquiv r (positiveGLMap r (positiveMatrix e)) (shiftedInclusion r c x) =
      shiftedInclusion r c (e x) := by
  let g := positiveMatrix e
  have h : LinearMap.GeneralLinearGroup.generalLinearEquiv O _
      (Matrix.GeneralLinearGroup.toLin g) = e :=
    (Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv O (Fin r → O))).apply_symm_apply e
  have hx : g.val *ᵥ x = e x := by
    rw [← h, LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv]
    rfl
  change loopLinearEquiv r (positiveGLMap r g) (monomial c • coordinateInclusion r x) =
    monomial c • coordinateInclusion r (e x)
  rw [map_smul, positiveGLMap_linear, hx]

private theorem exists_power_basis (P : Submodule O (Fin 2 → O))
    (hP : Module.finrank O P = Module.finrank O (Fin 2 → O)) :
    ∃ (k : Fin 2 → ℕ) (b : Module.Basis (Fin 2) O (Fin 2 → O))
      (bP : Module.Basis (Fin 2) O P),
      k 1 ≤ k 0 ∧ ∀ i, (bP i : Fin 2 → O) = t ^ k i • b i := by
  classical
  obtain ⟨b, a, bP, ha⟩ := P.exists_smith_normal_form_of_rank_eq (Pi.basisFun O (Fin 2)) hP
  have ha₀ (i : Fin 2) : a i ≠ 0 := by
    intro h
    apply bP.ne_zero i
    apply Subtype.ext
    simp [ha i, h]
  let k (i : Fin 2) := (a i).order.toNat
  let u (i : Fin 2) := PowerSeries.Unit_of_divided_by_X_pow_order (a i)
  have hf (i : Fin 2) : a i = t ^ k i * (u i : O) := by
    dsimp [u]
    rw [PowerSeries.Unit_of_divided_by_X_pow_order_nonzero (ha₀ i)]
    exact PowerSeries.X_pow_order_mul_divXPowOrder.symm
  let p : Fin 2 ≃ Fin 2 := if k 1 ≤ k 0 then Equiv.refl _ else Equiv.swap 0 1
  have hp : k (p 1) ≤ k (p 0) := by
    dsimp [p]
    split
    · assumption
    · simpa using (Nat.le_of_lt (Nat.lt_of_not_ge ‹¬ k 1 ≤ k 0›))
  refine ⟨k ∘ p, (b.unitsSMul u).reindex p.symm, bP.reindex p.symm, hp, ?_⟩
  intro i
  simp only [Module.Basis.reindex_apply, Equiv.symm_symm, Module.Basis.unitsSMul_apply,
    Function.comp_apply]
  rw [ha, hf]
  exact mul_smul (t ^ k (p i)) (u (p i) : O) (b (p i))

theorem orbit_exists (hExhaustion : LatticeExhaustion) (L : GL2Lattice) :
    ∃ ab : DominantPair, L ∈ gl2Orbit ab := by
  classical
  obtain ⟨N, B, rfl⟩ := hExhaustion.1 2 L
  let c : ℤ := -(N : ℤ)
  let f := shiftedInclusion 2 c
  let P := B.val.val.comap f
  have hPmap : P.map f = B.val.val := by
    rw [Submodule.map_comap_eq, inf_eq_right]
    simpa only [f, ← scalarLattice_val] using B.property.2
  let eP : P ≃ₗ[O] B.val.val :=
    P.equivMapOfInjective f (shiftedInclusion_injective 2 c) ≪≫ₗ LinearEquiv.ofEq _ _ hPmap
  obtain ⟨b₀⟩ := B.val.property.1
  have hP : Module.finrank O P = Module.finrank O (Fin 2 → O) := by
    rw [eP.finrank_eq, Module.finrank_eq_card_basis b₀,
      Module.finrank_eq_card_basis (Pi.basisFun O (Fin 2))]
  obtain ⟨k, b, bP, hsort, hbP⟩ := exists_power_basis P hP
  let ab : DominantPair :=
    ⟨(c + (k 0 : ℤ), c + (k 1 : ℤ)), by exact add_le_add_right (Int.ofNat_le.mpr hsort) c⟩
  have hab : pairCoweight ab = fun j ↦ c + (k j : ℤ) := by
    funext j
    fin_cases j <;> simp [pairCoweight, ab]
  let e := b.equivFun.symm
  let g := positiveMatrix e
  refine ⟨ab, ⟨⟨positiveGLMap 2 g, ⟨g, rfl⟩⟩, Subtype.ext ?_⟩⟩
  change (diagonalLattice (pairCoweight ab)).val.map
    ((loopLinearEquiv 2 (positiveGLMap 2 g)).restrictScalars O).toLinearMap = B.val.val
  rw [hab, diagonalLattice_eq_span, Submodule.map_span, ← hPmap]
  have hbSpan : P = Submodule.span O (Set.range fun i ↦ (bP i : Fin 2 → O)) := by
    change P = Submodule.span O (Set.range (fun i ↦ P.subtype (bP i)))
    rw [Set.range_comp', ← Submodule.map_span, bP.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  rw [hbSpan, Submodule.map_span, ← Set.range_comp', ← Set.range_comp']
  congr 1
  apply congrArg Set.range
  funext i
  change loopLinearEquiv 2 (positiveGLMap 2 g) (diagonalInclusion _ _) = f (bP i)
  have he : e (Pi.basisFun O (Fin 2) i) = b i := by
    apply b.equivFun.injective
    funext j
    rw [show b.equivFun (e (Pi.basisFun O (Fin 2) i)) = Pi.basisFun O (Fin 2) i from
      b.equivFun.apply_symm_apply _, Module.Basis.equivFun_self]
    simp [Pi.basisFun_apply, Pi.single_apply, eq_comm]
  rw [diagonalInclusion_eq_shifted, positiveMatrix_linear, hbP, map_smul, he]

open private LatticeModelSpecs.quotientEquivOfKernel
  from MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.LatticeModels

private def windowProjection (r : ℕ) (c : ℤ) (m : ℕ) :
    ((scalarLattice r c).val : Type) →ₗ[O] Window r c m :=
  @Submodule.mkQ O ((scalarLattice r c).val : Type) inferInstance inferInstance inferInstance
    (windowLower r c m)

set_option maxHeartbeats 600000 in
private theorem windowCoordinates_mkQ {r : ℕ} {c : ℤ} {m : ℕ}
    (x : Fin r → O) (i : Fin r) (j : Fin m) :
    windowCoordinates r c m (windowProjection r c m (shiftedCoordinates r c x)) (i, j) =
      PowerSeries.coeff j.val (x i) := by
  have h : windowJets r c m (windowProjection r c m (shiftedCoordinates r c x)) =
      windowReduction r c m (shiftedCoordinates r c x) := by
    simp only [windowProjection, windowJets, LatticeModelSpecs.quotientEquivOfKernel, LinearEquiv.trans_apply, Submodule.mkQ_apply,
      Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  change jetCoefficients m (windowJets r c m
    (windowProjection r c m (shiftedCoordinates r c x)) i) j = _
  rw [h]
  change jetCoefficients m (jetReduction m ((shiftedCoordinates r c).symm
    (shiftedCoordinates r c x) i)) j = _
  rw [LinearEquiv.symm_apply_apply, jetCoefficients_reduce]

private theorem shiftedInclusion_mem_diagonal_iff {r : ℕ} {c : ℤ} (k : Fin r → ℕ) (x : Fin r → O) :
    shiftedInclusion r c x ∈ (diagonalLattice (fun i ↦ c + (k i : ℤ))).val ↔
      ∀ i, t ^ k i ∣ x i := by
  rw [mem_diagonalLattice_iff]
  constructor
  · rintro ⟨y, hy⟩ i
    refine ⟨y i, HahnSeries.ofPowerSeries_injective (show inclusion (x i) =
      inclusion (t ^ k i * y i) from ?_)⟩
    apply mul_left_cancel₀ (monomial_ne_zero c)
    have hi := hy i
    change monomial c * inclusion (x i) = monomial (c + (k i : ℤ)) * inclusion (y i) at hi
    simpa only [monomial_add, monomial_nat, map_mul, mul_assoc] using hi
  · intro h
    choose y hy using h
    refine ⟨y, fun i ↦ ?_⟩
    change monomial c * inclusion (x i) = monomial (c + (k i : ℤ)) * inclusion (y i)
    rw [hy i, monomial_add, monomial_nat, map_mul, mul_assoc]

private def lowerCoefficients {r m : ℕ} (k : Fin r → ℕ) (hkm : ∀ i, k i ≤ m) :
    (Fin r × Fin m → ℂ) →ₗ[ℂ] (∀ i : Fin r, Fin (k i) → ℂ) :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦ LinearMap.proj (i, Fin.castLE (hkm i) j)

private theorem lowerCoefficients_surjective {r m : ℕ} (k : Fin r → ℕ) (hkm : ∀ i, k i ≤ m) :
    Function.Surjective (lowerCoefficients k hkm) := by
  intro y
  refine ⟨fun ij ↦ if h : ij.2.val < k ij.1 then y ij.1 ⟨ij.2.val, h⟩ else 0, ?_⟩
  funext i j
  change (if h : j.val < k i then y i ⟨j.val, h⟩ else 0) = y i j
  rw [dite_eq_left j.isLt]

private theorem coordinate_image_of_diagonal {r m : ℕ} (c : ℤ)
    (k : Fin r → ℕ) (hkm : ∀ i, k i ≤ m) :
    (latticeSubspace c m (diagonalLattice (fun i ↦ c + (k i : ℤ)))).map
      (windowCoordinates r c m).toLinearMap = (lowerCoefficients k hkm).ker := by
  classical
  let L := diagonalLattice (fun i ↦ c + (k i : ℤ))
  let q := windowProjection r c m
  have hmem (w : Window r c m) :
      w ∈ latticeSubspace c m L ↔
        ∃ x : Fin r → O, (∀ i, t ^ k i ∣ x i) ∧ q (shiftedCoordinates r c x) = w := by
    change (∃ v : (scalarLattice r c).val, v.val ∈ L.val ∧ q v = w) ↔ _
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨x, rfl⟩ := (shiftedCoordinates r c).surjective v
      exact ⟨x, (shiftedInclusion_mem_diagonal_iff k x).mp hv, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨shiftedCoordinates r c x, (shiftedInclusion_mem_diagonal_iff k x).mpr hx, rfl⟩
  ext v
  change v ∈ (latticeSubspace c m L).map (windowCoordinates r c m).toLinearMap ↔ _
  rw [Submodule.mem_map, LinearMap.mem_ker]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (hmem w).mp hw
    funext i j
    change windowCoordinates r c m (q (shiftedCoordinates r c x)) (i, Fin.castLE (hkm i) j) = 0
    rw [windowCoordinates_mkQ]
    exact PowerSeries.X_pow_dvd_iff.mp (hx i) j.val j.isLt
  · intro hv
    let x : Fin r → O := fun i ↦ PowerSeries.mk fun j ↦ if h : j < m then v (i, ⟨j, h⟩) else 0
    have hx (i : Fin r) : t ^ k i ∣ x i := by
      apply PowerSeries.X_pow_dvd_iff.mpr
      intro j hj
      have hjm : j < m := lt_of_lt_of_le hj (hkm i)
      have hv' := congrFun (congrFun hv i) (⟨j, hj⟩ : Fin (k i))
      change v (i, ⟨j, hjm⟩) = 0 at hv'
      simpa [x, hjm] using hv'
    refine ⟨q (shiftedCoordinates r c x), (hmem _).mpr ⟨x, hx, rfl⟩, ?_⟩
    funext ij
    obtain ⟨i, j⟩ := ij
    change windowCoordinates r c m (q (shiftedCoordinates r c x)) (i, j) = v (i, j)
    rw [windowCoordinates_mkQ]
    simp [x, j.isLt]

private theorem diagonal_window_finrank (ab : DominantPair) (c : ℤ) (m : ℕ)
    (hc : c ≤ ab.val.2) (hm : ab.val.1 ≤ c + (m : ℤ)) :
    (Module.finrank ℂ (latticeSubspace c m (diagonalLattice (pairCoweight ab))) : ℤ) =
      2 * (c + (m : ℤ)) - (ab.val.1 + ab.val.2) := by
  let k (i : Fin 2) := (pairCoweight ab i - c).toNat
  have hab : ab.val.2 ≤ ab.val.1 := ab.property
  have hcast (i : Fin 2) : (k i : ℤ) = pairCoweight ab i - c := by
    apply Int.toNat_of_nonneg
    fin_cases i <;> simp [pairCoweight] <;> omega
  have hkm (i : Fin 2) : k i ≤ m := by
    have hi : pairCoweight ab i ≤ ab.val.1 := by
      unfold pairCoweight
      split <;> omega
    have h := hcast i
    omega
  have heq : pairCoweight ab = fun i ↦ c + (k i : ℤ) := by
    funext i
    rw [hcast]
    omega
  rw [heq]
  let P := latticeSubspace c m (diagonalLattice (fun i ↦ c + (k i : ℤ)))
  let e := windowCoordinates 2 c m
  have hP : Module.finrank ℂ P = Module.finrank ℂ (lowerCoefficients k hkm).ker := by
    have he := (P.equivMapOfInjective e.toLinearMap e.injective).finrank_eq
    rw [coordinate_image_of_diagonal] at he
    exact he
  change (Module.finrank ℂ P : ℤ) = _
  rw [hP]
  have hf := LinearMap.finrank_range_add_finrank_ker (lowerCoefficients k hkm)
  rw [LinearMap.range_eq_top.mpr (lowerCoefficients_surjective k hkm), finrank_top,
    Module.finrank_pi_fintype] at hf
  simp only [Module.finrank_pi, Fintype.card_prod, Fintype.card_fin, Fin.sum_univ_two] at hf
  have h0 := hcast 0
  have h1 := hcast 1
  simp [pairCoweight] at h0 h1
  omega

open LinearAlgebraicGroups.Specs.GrassmannianCharts

private theorem windowStagePoint_subspace {r : ℕ} (c : ℤ) (m : ℕ) (L : Lattice r) :
    windowStageSubspace (windowStagePoint c m L) = latticeSubspace c m L := by
  unfold windowStageSubspace windowStagePoint
  exact subspacePoint_subspace _ _ _ rfl

private theorem orbit_window_finrank (hAction : GLJetAction) {ab : DominantPair} {L : GL2Lattice}
    (hL : L ∈ gl2Orbit ab) (c : ℤ) (m : ℕ) (hc : c ≤ ab.val.2)
    (hm : ab.val.1 ≤ c + (m : ℤ)) :
    (Module.finrank ℂ (latticeSubspace c m L) : ℤ) =
      2 * (c + (m : ℤ)) - (ab.val.1 + ab.val.2) := by
  obtain ⟨ρ, hmap, hreduce, _⟩ := hAction 2 c m (m + 1) (by omega) (by omega)
  have hd (g : GLJets 2 (m + 1) (by omega)) (p : WindowStage 2 c m) :
      Module.finrank ℂ (windowStageSubspace (ρ.smul g p)) ≤
        Module.finrank ℂ (windowStageSubspace p) := by
    rw [hmap]
    exact Submodule.finrank_map_le _ _
  have heq (g : GLJets 2 (m + 1) (by omega)) (p : WindowStage 2 c m) :
      Module.finrank ℂ (windowStageSubspace (ρ.smul g p)) =
        Module.finrank ℂ (windowStageSubspace p) := by
    refine le_antisymm (hd g p) ?_
    have hh : ρ.smul g⁻¹ (ρ.smul g p) = p := by
      calc
        _ = ρ.smul (g⁻¹ * g) p := (ρ.mul_smul g⁻¹ g p).symm
        _ = ρ.smul 1 p := congrArg (fun k ↦ ρ.smul k p) (inv_mul_cancel g)
        _ = p := ρ.one_smul p
    calc
      _ = Module.finrank ℂ (windowStageSubspace (ρ.smul g⁻¹ (ρ.smul g p))) :=
        congrArg (fun p ↦ Module.finrank ℂ (windowStageSubspace p)) hh.symm
      _ ≤ _ := hd g⁻¹ (ρ.smul g p)
  obtain ⟨⟨_, ⟨g, rfl⟩⟩, rfl⟩ := hL
  have h := heq (reduceGL 2 (m + 1) (by omega) g) (windowStagePoint c m
    (diagonalLattice (pairCoweight ab)))
  rw [hreduce, windowStagePoint_subspace, windowStagePoint_subspace] at h
  change (Module.finrank ℂ (latticeSubspace c m (positiveGLMap 2 g •
    diagonalLattice (pairCoweight ab))) : ℤ) = _
  rw [h]
  exact diagonal_window_finrank ab c m hc hm

theorem smithClassification : SmithClassification := by
  let hAction := BoundedLattices.glJetAction
  let hExhaustion := BoundedLattices.latticeExhaustion
  constructor
  · intro L
    obtain ⟨ab, hab⟩ := orbit_exists hExhaustion L
    exact ⟨ab, hab, fun _ h ↦ orbit_label_unique h hab⟩
  · intro _ _ hL
    exact ⟨(orbit_endpoints hL).1, (orbit_endpoints hL).2, orbit_window_finrank hAction hL⟩

private theorem isUnit_jetReduction {m : ℕ} (hm : 1 ≤ m) (a : O) :
    IsUnit (jetReduction m a) ↔ IsUnit a := by
  constructor
  · intro ha
    exact PowerSeries.isUnit_iff_constantCoeff.mpr (ha.map (jetConstantCoeff m hm))
  · exact fun ha ↦ ha.map (jetReduction m)

private theorem rowMap_eval {m : ℕ} (v : Row m) (x : Fin 2 → O) :
    rowMap v x = ∑ i : Fin 2, v i * jetReduction m (x i) := by
  simp [rowMap, smul_eq_mul]
  rfl

private theorem rowMap_single {m : ℕ} (v : Row m) (i : Fin 2) (q : O) :
    rowMap v (Pi.single i q) = v i * jetReduction m q := by
  rw [rowMap_eval, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, map_zero, mul_zero]
  · simp

private theorem rowMap_surjective {m : ℕ} (v : PrimitiveRow m) :
    Function.Surjective (rowMap v.val) := by
  obtain ⟨i, u, hu⟩ := v.property
  intro y
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective ((u⁻¹).val * y)
  refine ⟨Pi.single i x, ?_⟩
  have hx' : jetReduction m x = (u⁻¹).val * y := hx
  rw [rowMap_single, hx', ← hu, ← mul_assoc, Units.mul_inv, one_mul]

private def firstJetRow (m : ℕ) (g : GL (Fin 2) O) : Row m :=
  fun i ↦ jetReduction m (g.val 0 i)

private theorem firstJetRow_primitive (m : ℕ) (g : GL (Fin 2) O) :
    IsPrimitive (firstJetRow m g) := by
  unfold IsPrimitive
  by_contra! h
  have hz (i : Fin 2) : PowerSeries.constantCoeff (g.val 0 i) = 0 := by
    by_contra hne
    exact h i ((PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hne)).map
      (jetReduction m))
  have hu := PowerSeries.isUnit_iff_constantCoeff.mp (Matrix.isUnits_det_units g)
  rw [Matrix.det_fin_two, map_sub, map_mul, map_mul, hz 0, hz 1, zero_mul, zero_mul,
    sub_zero] at hu
  exact not_isUnit_zero hu

private theorem jetRow_completion {m : ℕ} (hm : 1 ≤ m) (v : PrimitiveRow m) :
    ∃ g : GL (Fin 2) O, firstJetRow m g = v.val := by
  classical
  choose x hx using fun i ↦ Ideal.Quotient.mk_surjective (v.val i)
  obtain ⟨i, hi⟩ := v.property
  have hxi : IsUnit (x i) :=
    (isUnit_jetReduction hm (x i)).mp (show IsUnit (jetReduction m (x i)) from
      (hx i).symm ▸ hi)
  let A : Matrix (Fin 2) (Fin 2) O :=
    !![x 0, x 1; (if i = 0 then 0 else 1), (if i = 0 then 1 else 0)]
  have hA : IsUnit A.det := by
    fin_cases i
    · simpa [A, Matrix.det_fin_two] using hxi
    · simpa [A, Matrix.det_fin_two] using hxi.neg
  refine ⟨Matrix.GeneralLinearGroup.mk'' A hA, ?_⟩
  funext j
  fin_cases j
  · exact hx 0
  · exact hx 1

private theorem rowMap_firstJetRow (m : ℕ) (g : GL (Fin 2) O) (x : Fin 2 → O) :
    rowMap (firstJetRow m g) x = jetReduction m ((g.val *ᵥ x) 0) := by
  rw [rowMap_eval]
  simp [firstJetRow, Matrix.mulVec, dotProduct, map_mul]

private theorem positiveGL_linear_shifted {r : ℕ} (g : GL (Fin r) O) (c : ℤ)
    (x : Fin r → O) :
    loopLinearEquiv r (positiveGLMap r g) (shiftedInclusion r c x) =
      shiftedInclusion r c (g.val *ᵥ x) := by
  change loopLinearEquiv r (positiveGLMap r g) (monomial c • coordinateInclusion r x) =
    monomial c • coordinateInclusion r (g.val *ᵥ x)
  rw [map_smul, positiveGLMap_linear]

private theorem mulVec_inv_mulVec {r : ℕ} (g : GL (Fin r) O) (x : Fin r → O) :
    (g⁻¹).val *ᵥ (g.val *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

private theorem shifted_diagonal_mem (ab : DominantPair) (x : Fin 2 → O) :
    shiftedInclusion 2 ab.val.2 x ∈ (diagonalLattice (pairCoweight ab)).val ↔
      t ^ difference ab ∣ x 0 := by
  let k : Fin 2 → ℕ := ![difference ab, 0]
  have hk : pairCoweight ab = fun i ↦ ab.val.2 + (k i : ℤ) := by
    have hab : ab.val.2 ≤ ab.val.1 := ab.property
    have hd : (difference ab : ℤ) = ab.val.1 - ab.val.2 :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hab)
    funext i
    fin_cases i
    · simp [k, pairCoweight, hd]
    · simp [k, pairCoweight]
  rw [hk, shiftedInclusion_mem_diagonal_iff k x, Fin.forall_fin_two]
  simp [k]

private theorem shiftedKernel_firstJetRow (ab : DominantPair) (g : GL (Fin 2) O) :
    shiftedKernel ab.val.2 (firstJetRow (difference ab) g) =
      (positiveGLMap 2 g⁻¹ • diagonalLattice (pairCoweight ab)).val := by
  let L := diagonalLattice (pairCoweight ab)
  let f := shiftedInclusion 2 ab.val.2
  let e := loopLinearEquiv 2 (positiveGLMap 2 g⁻¹)
  have hL : L.val ≤ f.range := by
    rw [← scalarLattice_val]
    exact (orbit_endpoints (MulAction.mem_orbit_self _ : L ∈ gl2Orbit ab)).2 _ |>.mpr le_rfl
  have hker (x : Fin 2 → O) :
      x ∈ (rowMap (firstJetRow (difference ab) g)).ker ↔ f (g.val *ᵥ x) ∈ L.val := by
    rw [LinearMap.mem_ker, rowMap_firstJetRow, show f (g.val *ᵥ x) =
      shiftedInclusion 2 ab.val.2 (g.val *ᵥ x) from rfl, shifted_diagonal_mem]
    exact Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton
  ext z
  change (∃ x ∈ (rowMap (firstJetRow (difference ab) g)).ker, f x = z) ↔
    ∃ y ∈ L.val, e y = z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨f (g.val *ᵥ x), (hker x).mp hx, ?_⟩
    change loopLinearEquiv 2 (positiveGLMap 2 g⁻¹) (shiftedInclusion 2 _ (g.val *ᵥ x)) = _
    rw [positiveGL_linear_shifted, mulVec_inv_mulVec]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, rfl⟩ := hL hy
    refine ⟨(g⁻¹).val *ᵥ x, (hker _).mpr ?_, ?_⟩
    · simpa only [inv_inv, mulVec_inv_mulVec] using
        (show f ((g⁻¹⁻¹).val *ᵥ ((g⁻¹).val *ᵥ x)) ∈ L.val from by
          rw [mulVec_inv_mulVec]
          exact hy)
    · exact (positiveGL_linear_shifted g⁻¹ ab.val.2 x).symm

private theorem row_quotient_rel_iff {m : ℕ} (b : ℤ) (v w : PrimitiveRow m) :
    (primitiveRowRel m).r v w ↔ shiftedKernel b v.val = shiftedKernel b w.val := by
  have hinj := shiftedInclusion_injective 2 b
  change (∃ u : (JetRing m)ˣ, ∀ i, w.val i = u.val * v.val i) ↔
    (rowMap v.val).ker.map (shiftedInclusion 2 b) =
      (rowMap w.val).ker.map (shiftedInclusion 2 b)
  rw [(Submodule.map_injective_of_injective hinj).eq_iff]
  constructor
  · rintro ⟨u, hu⟩
    have hfactor (x : Fin 2 → O) : rowMap w.val x = u.val * rowMap v.val x := by
      rw [rowMap_eval, rowMap_eval, Finset.mul_sum]
      simp only [hu, mul_assoc]
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_ker, hfactor]
    exact ⟨fun h ↦ h.symm ▸ mul_zero _, fun h ↦ u.isUnit.mul_left_cancel (h.trans (mul_zero _).symm)⟩
  · intro h
    let e := (rowMap v.val).quotKerEquivOfSurjective (rowMap_surjective v)
    let e' := (rowMap w.val).quotKerEquivOfSurjective (rowMap_surjective w)
    let E := e.symm ≪≫ₗ (Submodule.quotEquivOfEq _ _ h) ≪≫ₗ e'
    have hE (x : JetRing m) : E x = x * E 1 := by
      obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hq (z : JetRing m) : q • z = Ideal.Quotient.mk (jetIdeal m) q * z := by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
        exact (Ideal.Quotient.mk (jetIdeal m)).map_mul q y
      calc
        _ = E (q • 1) := congrArg E ((hq 1).trans (mul_one _)).symm
        _ = q • E 1 := map_smul E q 1
        _ = _ := hq _
    obtain ⟨y, hy⟩ := E.surjective 1
    have hu : IsUnit (E 1) := isUnit_iff_exists_inv'.mpr ⟨y, (hE y).symm.trans hy⟩
    obtain ⟨u, hu⟩ := hu
    refine ⟨u, fun i ↦ ?_⟩
    have hmap (x : Fin 2 → O) : E (rowMap v.val x) = rowMap w.val x := by
      change e' ((Submodule.quotEquivOfEq _ _ h) (e.symm (rowMap v.val x))) = _
      rw [show rowMap v.val x = e (Submodule.Quotient.mk x) from rfl, e.symm_apply_apply,
        Submodule.quotEquivOfEq_mk]
      rfl
    have he := hmap (Pi.single i 1)
    simp only [rowMap_single, map_one, mul_one] at he
    rw [hE, ← hu, mul_comm] at he
    exact he.symm

theorem primitiveRowClassification : PrimitiveRowClassification := by
  intro ab hm
  classical
  have hr (v : PrimitiveRow (difference ab)) :
      ∃ p : gl2Orbit ab, p.val.val = shiftedKernel ab.val.2 v.val := by
    obtain ⟨g, hg⟩ := jetRow_completion hm v
    refine ⟨⟨positiveGLMap 2 g⁻¹ • diagonalLattice (pairCoweight ab),
      ⟨⟨positiveGLMap 2 g⁻¹, ⟨g⁻¹, rfl⟩⟩, rfl⟩⟩, ?_⟩
    exact (shiftedKernel_firstJetRow ab g).symm.trans
      (congrArg (shiftedKernel ab.val.2) hg)
  let f := fun v ↦ (hr v).choose
  have hf (v : PrimitiveRow (difference ab)) : (f v).val.val =
      shiftedKernel ab.val.2 v.val := (hr v).choose_spec
  let fQ : Quotient (primitiveRowRel (difference ab)) → gl2Orbit ab :=
    Quotient.lift f (fun v w h ↦ Subtype.ext (Subtype.ext
      ((hf v).trans (((row_quotient_rel_iff ab.val.2 v w).mp h).trans (hf w).symm))))
  have hQ : Function.Bijective fQ := by
    constructor
    · rintro ⟨v⟩ ⟨w⟩ h
      apply Quotient.sound
      apply (row_quotient_rel_iff ab.val.2 v w).mpr
      exact (hf v).symm.trans ((congrArg (fun p : gl2Orbit ab ↦ p.val.val) h).trans (hf w))
    · rintro ⟨L, ⟨⟨_, ⟨g, rfl⟩⟩, rfl⟩⟩
      let v : PrimitiveRow (difference ab) :=
        ⟨firstJetRow _ g⁻¹, firstJetRow_primitive _ g⁻¹⟩
      refine ⟨Quotient.mk _ v, Subtype.ext (Subtype.ext ?_)⟩
      change (f v).val.val = _
      rw [hf, show v.val = firstJetRow (difference ab) g⁻¹ from rfl, shiftedKernel_firstJetRow, inv_inv]
      rfl
  exact ⟨rowMap_surjective, Equiv.ofBijective fQ hQ, hf⟩

open AlgebraicGeometry CategoryTheory TopologicalSpace
open LinearAlgebraicGroups (Points SchemeOver testSpec)

open private LatticeModels.reduced_ker_eq LatticeModels.inclusion_closed
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.LatticeModels

private theorem equal_pair_orbit_set (ab : DominantPair) (hab : ab.val.1 = ab.val.2) :
    gl2Orbit ab = {scalarLattice 2 ab.val.1} := by
  have hpair : pairCoweight ab = fun _ ↦ ab.val.1 := by
    funext i
    simp [pairCoweight, ← hab]
  unfold gl2Orbit
  rw [hpair]
  ext L
  constructor
  · rintro ⟨⟨_, ⟨g, rfl⟩⟩, rfl⟩
    exact Set.mem_singleton_iff.mpr (positiveGL_preserves_scalar g _)
  · rintro (rfl : L = _)
    exact MulAction.mem_orbit_self _

private theorem equal_pair_closure_set (ab : DominantPair) (hab : ab.val.1 = ab.val.2) :
    closureLattices ab = {scalarLattice 2 ab.val.1} := by
  rw [← equal_pair_orbit_set ab hab]
  ext L
  constructor
  · rintro ⟨cd, hcd, hL⟩
    obtain ⟨j, hj, h₁, h₂⟩ := hcd
    have hcd' : cd = ab := Subtype.ext (Prod.ext (by omega) (by omega))
    exact hcd' ▸ hL
  · intro hL
    exact ⟨ab, ⟨0, by simp [hab]⟩, hL⟩

private theorem reducedClosure_singleton_iso {X : SchemeOver ℂ}
    (p : Points X complexAlgebra) :
    Nonempty (reducedClosureScheme X {p} ≅ (testSpec ℂ).obj (Opposite.op complexAlgebra)) := by
  let T := (testSpec ℂ).obj (Opposite.op complexAlgebra)
  have hT : T.hom = 𝟙 _ := by
    change Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ)) = 𝟙 (Spec (CommRingCat.of ℂ))
    have h : CommRingCat.ofHom (algebraMap ℂ ℂ) = 𝟙 _ := rfl
    rw [h, Spec.map_id]
  let : IsClosedImmersion p.left :=
    isClosedImmersion_of_comp_eq_id X.hom p.left ((Over.w p).trans hT)
  let i := reducedClosureInclusion X ({p} : Set (Points X complexAlgebra))
  let : IsClosedImmersion i.left := by
    change IsClosedImmersion (reducedClosureIdeal X {p}).subschemeι
    infer_instance
  have hTred : IsReduced T.left := by
    change IsReduced (Spec (CommRingCat.of ℂ))
    infer_instance
  have hker : i.left.ker = p.left.ker := by
    have hp := LatticeModels.reduced_ker_eq p.left
    change (reducedClosureIdeal X {p}).subschemeι.ker = p.left.ker
    rw [Scheme.IdealSheafData.ker_subschemeι, hp, reducedClosureIdeal, Set.image_singleton, pointLocation_range]
  let f := IsClosedImmersion.lift p.left i.left hker.ge
  have hf : f ≫ p.left = i.left := IsClosedImmersion.lift_fac p.left i.left _
  have hfIso : IsIso f := IsClosedImmersion.isIso_of_ker_eq i.left p.left f hf hker
  let F : reducedClosureScheme X {p} ⟶ T :=
    Over.homMk f (by rw [← Over.w p, ← Category.assoc, hf, Over.w])
  have : IsIso ((Over.forget _).map F) := hfIso
  have : IsIso F := isIso_of_reflects_iso F (Over.forget _)
  exact ⟨asIso F⟩

private theorem occupied_of_mem_boundedOrbit (hAction : GLJetAction) {ab : DominantPair}
    {N : ℕ} {B : BoundedLattice 2 N} (hB : B ∈ boundedOrbit ab N) :
    Occupied ab N (boundedPoint B).1 := by
  obtain ⟨hl, hu⟩ := orbit_endpoints hB
  have ha := (hl N).mp B.property.1
  have hb := (hu (-(N : ℤ))).mp B.property.2
  have h := orbit_window_finrank hAction hB (-(N : ℤ)) (2 * N) hb
    (by rw [boundedExponent]; exact ha)
  rw [boundedExponent] at h
  change (Module.finrank ℂ (latticeSubspace (-(N : ℤ)) (2 * N) B.val) : ℤ) = _
  omega

theorem diagonalBounded_dimension (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) :
    (boundedPoint (diagonalBounded ab N hN)).1 = occupiedDimension ab N hN := by
  have hDiag := occupied_of_mem_boundedOrbit BoundedLattices.glJetAction
    (B := diagonalBounded ab N hN) (MulAction.mem_orbit_self _)
  have hDim := occupiedDimension_occupied ab N hN
  apply Fin.ext
  unfold Occupied at hDiag hDim
  omega

private theorem diagonalBounded_point (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) :
    ∃ p : WindowPoints 2 (-(N : ℤ)) (2 * N) (occupiedDimension ab N hN),
      grassmannianSubspace (windowBasis 2 (-(N : ℤ)) (2 * N))
        (windowDimension_le (occupiedDimension ab N hN)) p =
          boundedSubspace (diagonalBounded ab N hN) := by
  let d := occupiedDimension ab N hN
  let B := diagonalBounded ab N hN
  let b := windowBasis 2 (-(N : ℤ)) (2 * N)
  have hDim : Module.finrank ℂ (boundedSubspace B) = d.val :=
    congrArg Fin.val (diagonalBounded_dimension ab N hN)
  exact ⟨subspacePoint b (windowDimension_le d) (boundedSubspace B) hDim,
    subspacePoint_subspace _ _ _ _⟩

theorem equalPairOrbit : EqualPairOrbit := by
  intro ab N hN hab
  refine ⟨equal_pair_closure_set ab hab, equal_pair_orbit_set ab hab, ?_⟩
  let d := occupiedDimension ab N hN
  let B := diagonalBounded ab N hN
  obtain ⟨p, hp⟩ := diagonalBounded_point ab N hN
  have hO : gl2Orbit ab = {B.val} := by
    have hpair : pairCoweight ab = fun _ ↦ ab.val.1 := by
      funext i
      simp [pairCoweight, ← hab]
    have hlat : B.val = scalarLattice 2 ab.val.1 := congrArg diagonalLattice hpair
    rw [hlat, equal_pair_orbit_set ab hab]
  have hpoints : schubertOrbitPoints ab N hN d = {p} := by
    ext q
    constructor
    · rintro ⟨L, hL, hq⟩
      have hLB : L = B.val := Set.mem_singleton_iff.mp (hO ▸ hL)
      subst L
      apply Set.mem_singleton_iff.mpr
      exact grassmannianSubspace_injective _ _ (hq.trans hp.symm)
    · rintro (rfl : q = p)
      exact ⟨B.val, MulAction.mem_orbit_self _, hp⟩
  have hSchubert : Nonempty (occupiedSchubert ab N hN ≅
      (testSpec ℂ).obj (Opposite.op complexAlgebra)) := by
    change Nonempty (reducedClosureScheme (BoundedGrassmannian N d)
      (schubertOrbitPoints ab N hN d) ≅ _)
    rw [hpoints]
    exact reducedClosure_singleton_iso p
  have htop : orbitOpen ab N hN = ⊤ := by
    simp [orbitOpen, difference, hab]
  have hι : IsIso (orbitToSchubert ab N hN).left := by
    change IsIso (orbitOpen ab N hN).ι
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    rw [Scheme.Opens.opensRange_ι, htop]
  have : IsIso ((Over.forget _).map (orbitToSchubert ab N hN)) := hι
  have : IsIso (orbitToSchubert ab N hN) :=
    isIso_of_reflects_iso _ (Over.forget _)
  obtain ⟨e⟩ := hSchubert
  exact ⟨asIso (orbitToSchubert ab N hN) ≪≫ e⟩

theorem schubertLatticeSet_iff (hAction : GLJetAction) (hExhaustion : LatticeExhaustion)
    (ab : DominantPair) (N : ℕ) (B : BoundedLattice 2 N) :
    B ∈ schubertLatticeSet ab N ↔
      Between ab.val.1 ab.val.2 B.val ∧ Occupied ab N (boundedPoint B).1 := by
  constructor
  · rintro ⟨cd, hcd, hB⟩
    obtain ⟨hsum, h₁, h₂⟩ := (below_iff cd ab).mp hcd
    obtain ⟨hl, hu⟩ := orbit_endpoints hB
    refine ⟨⟨(hl _).mpr h₁, (hu _).mpr h₂⟩, ?_⟩
    have ho : Occupied cd N (boundedPoint B).1 := occupied_of_mem_boundedOrbit hAction hB
    unfold Occupied at *
    omega
  · rintro ⟨⟨h₁, h₂⟩, ho⟩
    obtain ⟨cd, hB⟩ := orbit_exists hExhaustion B.val
    have hc : Occupied cd N (boundedPoint B).1 := occupied_of_mem_boundedOrbit hAction hB
    unfold Occupied at hc ho
    obtain ⟨hl, hu⟩ := orbit_endpoints hB
    exact ⟨cd, (below_iff cd ab).mpr ⟨by omega, (hl _).mp h₁, (hu _).mp h₂⟩, hB⟩

theorem schubertOrbitPoints_nonempty_iff (hAction : GLJetAction) (ab : DominantPair)
    (N : ℕ) (hN : OrbitBound ab N) (d : WindowDimension 2 (-(N : ℤ)) (2 * N)) :
    (schubertOrbitPoints ab N hN d).Nonempty ↔ Occupied ab N d := by
  let B₀ := diagonalBounded ab N hN
  let d₀ := occupiedDimension ab N hN
  have h₀ : Occupied ab N d₀ := occupiedDimension_occupied ab N hN
  constructor
  · rintro ⟨p, L, hL, hp⟩
    let B : BoundedLattice 2 N := ⟨L, gl2Orbit_bounded ab hN hL⟩
    have hf := grassmannianSubspace_finrank (windowBasis 2 (-(N : ℤ)) (2 * N))
      (windowDimension_le d) p
    rw [hp] at hf
    have hd : (boundedPoint B).1 = d := Fin.ext hf
    exact hd ▸ occupied_of_mem_boundedOrbit hAction (B := B) hL
  · intro hd
    have hdd : d = d₀ := by
      apply Fin.ext
      unfold Occupied at h₀ hd
      omega
    subst d
    obtain ⟨p, hp⟩ := diagonalBounded_point ab N hN
    exact ⟨p, B₀.val, MulAction.mem_orbit_self _, hp⟩

set_option maxHeartbeats 600000 in
theorem schubertLatticeSet_homeomorph (hTopology : BoundedInclusionTopology)
    (ab : DominantPair) (N M : ℕ) (hN : OrbitBound ab N) (hNM : N ≤ M) :
    ∃ e : schubertLatticeSet ab N ≃ₜ schubertLatticeSet ab M,
      ∀ L, (e L).val = boundedInclusion hNM L.val := by
  let f : schubertLatticeSet ab N → schubertLatticeSet ab M :=
    fun L ↦ ⟨boundedInclusion hNM L.val, L.property⟩
  have hEmbed : Topology.IsEmbedding f := by
    apply (Topology.IsEmbedding.subtypeVal.of_comp_iff).mp
    exact (hTopology 2 N M hNM).isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have hSurj : Function.Surjective f := by
    intro L
    obtain ⟨B, hB⟩ := closureLattices_bounded hN L.property
    have hBmem : B.val ∈ closureLattices ab := hB.symm ▸ L.property
    exact ⟨⟨B, hBmem⟩, Subtype.ext (Subtype.ext hB)⟩
  exact ⟨hEmbed.toHomeomorphOfSurjective hSurj, fun _ ↦ rfl⟩

private def adjacentMatrix (ab : DominantPair) (s : ℂ) : Matrix (Fin 2) (Fin 2) K :=
  !![monomial (ab.val.1 - 1), 0; s • monomial ab.val.2, monomial (ab.val.2 + 1)]

private def adjacentLoop (ab : DominantPair) (s : ℂ) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (adjacentMatrix ab s) (by
    rw [adjacentMatrix, Matrix.det_fin_two_of, zero_mul, sub_zero]
    exact mul_ne_zero (monomial_ne_zero _) (monomial_ne_zero _))

private def adjacentLattice (ab : DominantPair) (s : ℂ) : GL2Lattice :=
  adjacentLoop ab s • standardLattice 2

private theorem adjacentLattice_val (ab : DominantPair) (s : ℂ) :
    (adjacentLattice ab s).val = Submodule.span O (Set.range (adjacentColumn ab s)) := by
  let e := (loopLinearEquiv 2 (adjacentLoop ab s)).restrictScalars O
  let f := coordinateInclusion 2
  change f.range.map e.toLinearMap = _
  have hcol (i : Fin 2) :
      e (f (Pi.basisFun O (Fin 2) i)) = adjacentColumn ab s i := by
    change loopLinearEquiv 2 (adjacentLoop ab s) (f (Pi.basisFun O (Fin 2) i)) = _
    rw [loopLinearEquiv_apply]
    funext j
    change (adjacentMatrix ab s *ᵥ f (Pi.basisFun O (Fin 2) i)) j = _
    fin_cases i <;> fin_cases j <;>
      simp [f, coordinateInclusion, adjacentMatrix, adjacentColumn, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, Pi.basisFun_apply]
  rw [← funext hcol]
  change f.range.map e.toLinearMap = Submodule.span O
    (Set.range fun i ↦ e.toLinearMap (f (Pi.basisFun O (Fin 2) i)))
  rw [Set.range_comp', ← Submodule.map_span, Set.range_comp', ← Submodule.map_span,
    (Pi.basisFun O (Fin 2)).span_eq, Submodule.map_top]

private theorem adjacentLattice_zero (ab : DominantPair) (h : 2 ≤ difference ab) :
    adjacentLattice ab 0 = diagonalLattice (pairCoweight (adjacentPair ab h)) := by
  have he : (adjacentLoop ab (0 : ℂ)) = diagonalLoop 2 (pairCoweight (adjacentPair ab h)) := by
    apply (Matrix.GeneralLinearGroup.ext_iff ..).mpr
    intro i j
    change adjacentMatrix ab 0 i j =
      Matrix.diagonal (fun k ↦ monomial (pairCoweight (adjacentPair ab h) k)) i j
    fin_cases i <;> fin_cases j <;>
      simp [adjacentMatrix, adjacentPair, pairCoweight]
    exact zero_smul ℂ (monomial ab.val.2)
  rw [adjacentLattice, he, diagonalLoop_smul_standard]

private theorem shiftedInclusion_adjacent_iff (ab : DominantPair) (s : ℂ) {c : ℤ}
    {p q : ℕ} (hp : c + (p : ℤ) = ab.val.1 - 1) (hq : c + (q : ℤ) = ab.val.2)
    (x : Fin 2 → O) :
    shiftedInclusion 2 c x ∈ (adjacentLattice ab s).val ↔
      ∃ u v : O, x 0 = t ^ p * u ∧ x 1 = PowerSeries.C s * t ^ q * u + t ^ (q + 1) * v := by
  have hpower (n : ℕ) (u : O) :
      monomial (c + (n : ℤ)) * inclusion u = monomial c * inclusion (t ^ n * u) := by
    rw [monomial_add, monomial_nat, map_mul, mul_assoc]
  have hq' : c + ((q + 1 : ℕ) : ℤ) = ab.val.2 + 1 := by push_cast; omega
  have hs : s • monomial ab.val.2 = monomial ab.val.2 * inclusion (PowerSeries.C s) := by
    change s • monomial ab.val.2 = monomial ab.val.2 * ((PowerSeries.C s : O) : K)
    rw [PowerSeries.coe_C, mul_comm]
    exact HahnSeries.single_zero_mul_eq_smul.symm
  have hE (y : Fin 2 → O) :
      loopLinearEquiv 2 (adjacentLoop ab s) (coordinateInclusion 2 y) =
        shiftedInclusion 2 c ![t ^ p * y 0, PowerSeries.C s * t ^ q * y 0 + t ^ (q + 1) * y 1] := by
    rw [loopLinearEquiv_apply]
    funext i
    change (adjacentMatrix ab s *ᵥ coordinateInclusion 2 y) i = _
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    fin_cases i
    · change monomial (ab.val.1 - 1) * inclusion (y 0) + 0 * inclusion (y 1) =
        monomial c * inclusion (t ^ p * y 0)
      rw [zero_mul, add_zero, ← hp, hpower]
    · change (s • monomial ab.val.2) * inclusion (y 0) + monomial (ab.val.2 + 1) * inclusion (y 1) =
        monomial c * inclusion (PowerSeries.C s * t ^ q * y 0 + t ^ (q + 1) * y 1)
      rw [hs, ← hq', hpower, map_add, mul_add]
      congr 1
      rw [← hq, mul_assoc, ← map_mul, hpower]
      congr 2
      ring
  change (∃ y ∈ (coordinateInclusion 2).range,
    loopLinearEquiv 2 (adjacentLoop ab s) y = shiftedInclusion 2 c x) ↔ _
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, hy⟩
    rw [hE] at hy
    have h := shiftedInclusion_injective 2 c hy
    exact ⟨z 0, z 1, (congrFun h 0).symm, (congrFun h 1).symm⟩
  · rintro ⟨u, v, h₀, h₁⟩
    refine ⟨coordinateInclusion 2 ![u, v], ⟨![u, v], rfl⟩, ?_⟩
    rw [hE]
    congr 1
    funext i
    fin_cases i
    · exact h₀.symm
    · exact h₁.symm


open CategoryTheory

private abbrev boundedStability (N : ℕ) (d : WindowDimension 2 (-(N : ℤ)) (2 * N)) :=
  windowStableScheme 2 (-(N : ℤ)) (2 * N) d

private abbrev boundedStabilityInclusion (N : ℕ) (d : WindowDimension 2 (-(N : ℤ)) (2 * N)) :=
  windowSchemeInGrassmannian 2 (-(N : ℤ)) (2 * N) d

private theorem windowSchemeSubspace_injective {r : ℕ} {c : ℤ} {m : ℕ}
    {d : WindowDimension r c m} :
    Function.Injective (windowSchemeSubspace (d := d)) := by
  intro p q h
  have he := grassmannianSubspace_injective (windowBasis r c m) (windowDimension_le d) h
  let w := windowSchemeInGrassmannian r c m d
  have hw : IsClosedImmersion w.left := by
    change IsClosedImmersion (reducedClosureIdeal _ _).subschemeι
    infer_instance
  apply Over.OverMorphism.ext
  apply (cancel_mono w.left).mp
  exact congrArg Over.Hom.left he

private theorem schubertInclusion_comp (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (d : WindowDimension 2 (-(N : ℤ)) (2 * N)) :
    LatticeModels.schubertInclusion ab N hN d ≫ boundedStabilityInclusion N d =
      schubertToGrassmannian ab N hN d := by
  apply Over.OverMorphism.ext
  exact Scheme.IdealSheafData.inclusion_subschemeι _

private def boundedSchemeOrbit (ab : DominantPair) (N : ℕ)
    (d : WindowDimension 2 (-(N : ℤ)) (2 * N)) :
    Set (Points (boundedStability N d) complexAlgebra) :=
  { p | ∃ B : BoundedLattice 2 N, B.val ∈ gl2Orbit ab ∧
    windowSchemeSubspace p = boundedSubspace B }

private theorem boundedSchemeOrbit_image (ab : DominantPair) (N : ℕ)
    (hN : OrbitBound ab N) (d : WindowDimension 2 (-(N : ℤ)) (2 * N)) :
    (fun p ↦ p ≫ boundedStabilityInclusion N d) '' boundedSchemeOrbit ab N d =
      schubertOrbitPoints ab N hN d := by
  ext p
  constructor
  · rintro ⟨q, ⟨B, hB, he⟩, rfl⟩
    exact ⟨B.val, hB, he⟩
  · intro hp
    have hstable := LatticeModels.schubertOrbit_stable ab N hN d hp
    let b := windowBasis 2 (-(N : ℤ)) (2 * N)
    let T := windowOperator 2 (-(N : ℤ)) (2 * N)
    let q := (LatticeModels.stableSchemePoints b (windowDimension_le d) T).symm ⟨p, hstable⟩
    have hq : q ≫ boundedStabilityInclusion N d = p :=
      congrArg Subtype.val ((LatticeModels.stableSchemePoints b (windowDimension_le d) T)
        |>.apply_symm_apply ⟨p, hstable⟩)
    obtain ⟨L, hL, hp⟩ := hp
    refine ⟨q, ⟨⟨L, gl2Orbit_bounded ab hN hL⟩, hL, ?_⟩, hq⟩
    exact (congrArg (grassmannianSubspace b (windowDimension_le d)) hq).trans hp

private theorem range_reducedClosureInclusion {X : SchemeOver ℂ}
    (S : Set (Points X complexAlgebra)) :
    Set.range (reducedClosureInclusion X S).left = closure (pointLocation '' S) := by
  change Set.range (reducedClosureIdeal X S).subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι]
  exact Scheme.IdealSheafData.coe_support_vanishingIdeal _

private theorem range_over_comp {X Y Z : SchemeOver ℂ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Set.range (f ≫ g).left = g.left '' Set.range f.left :=
  Set.range_comp g.left f.left

set_option maxHeartbeats 600000 in
private theorem range_schubertInclusion (ab : DominantPair) (N : ℕ)
    (hN : OrbitBound ab N) (d : WindowDimension 2 (-(N : ℤ)) (2 * N)) :
    Set.range (LatticeModels.schubertInclusion ab N hN d).left =
      closure (pointLocation '' boundedSchemeOrbit ab N d) := by
  let w := boundedStabilityInclusion N d
  let f := LatticeModels.schubertInclusion ab N hN d
  have hw : IsClosedImmersion w.left := by
    change IsClosedImmersion (reducedClosureIdeal _ _).subschemeι
    infer_instance
  apply Set.image_injective.mpr w.left.isClosedEmbedding.injective
  calc
    w.left '' Set.range f.left = Set.range (schubertToGrassmannian ab N hN d).left := by
      have h := range_over_comp f w
      change Set.range (LatticeModels.schubertInclusion ab N hN d ≫
        boundedStabilityInclusion N d).left = _ at h
      rw [schubertInclusion_comp] at h
      exact h.symm
    _ = closure (pointLocation '' schubertOrbitPoints ab N hN d) :=
      range_reducedClosureInclusion (schubertOrbitPoints ab N hN d)
    _ = w.left '' closure (pointLocation '' boundedSchemeOrbit ab N d) := by
      rw [← w.left.isClosedEmbedding.closure_image_eq, Set.image_image,
        ← boundedSchemeOrbit_image ab N hN d, Set.image_image]
      rfl

private theorem point_of_boundedOrbit (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (hAction : GLJetAction) (B : BoundedLattice 2 N) (hB : B ∈ boundedOrbit ab N) :
    ∃ p : Points (boundedStability N (occupiedDimension ab N hN)) complexAlgebra,
      windowSchemeSubspace p = boundedSubspace B := by
  let d := occupiedDimension ab N hN
  have hb : Occupied ab N (boundedPoint B).1 := occupied_of_mem_boundedOrbit hAction hB
  have h₀ : Occupied ab N d := occupiedDimension_occupied ab N hN
  have hd : Module.finrank ℂ (boundedSubspace B) = d.val := by
    change (boundedPoint B).1.val = d.val
    unfold Occupied at hb h₀
    omega
  let b := windowBasis 2 (-(N : ℤ)) (2 * N)
  let T := windowOperator 2 (-(N : ℤ)) (2 * N)
  let q := subspacePoint b (windowDimension_le d) (boundedSubspace B) hd
  have hq : grassmannianSubspace b (windowDimension_le d) q = boundedSubspace B :=
    subspacePoint_subspace _ _ _ _
  have hs : StablePlane b (windowDimension_le d) T q := by
    unfold StablePlane
    rw [hq]
    exact latticeSubspace_stable _ _ B.val
  let e := LatticeModels.stableSchemePoints b (windowDimension_le d) T
  have he : e.symm ⟨q, hs⟩ ≫ boundedStabilityInclusion N d = q :=
    congrArg Subtype.val (e.apply_symm_apply ⟨q, hs⟩)
  exact ⟨e.symm ⟨q, hs⟩, (congrArg (grassmannianSubspace b (windowDimension_le d)) he).trans hq⟩

private theorem boundedStability_inclusion (hInclusions : WindowInclusions)
    (ab : DominantPair) (N M : ℕ) (hN : OrbitBound ab N) (hM : OrbitBound ab M) (hNM : N ≤ M) :
    ∃ j : boundedStability N (occupiedDimension ab N hN) ⟶
        boundedStability M (occupiedDimension ab M hM),
      IsClosedImmersion j.left ∧
      ∀ (B : BoundedLattice 2 N)
        (q : Points (boundedStability N (occupiedDimension ab N hN)) complexAlgebra),
        windowSchemeSubspace q = boundedSubspace B →
        windowSchemeSubspace (q ≫ j) = boundedSubspace (boundedInclusion hNM B) := by
  let dN := occupiedDimension ab N hN
  let dM := occupiedDimension ab M hM
  obtain ⟨d', hd', j, hj, hc⟩ := hInclusions 2 (-(N : ℤ)) (-(M : ℤ)) (2 * N) (2 * M)
    (by omega) (by rw [boundedExponent, boundedExponent]; omega) dN
  repeat rw [boundedExponent] at hd'
  have hNdim : Occupied ab N dN := occupiedDimension_occupied ab N hN
  have hMdim : Occupied ab M dM := occupiedDimension_occupied ab M hM
  have he : d' = dM := by
    apply Fin.ext
    unfold Occupied at hNdim hMdim
    omega
  subst d'
  refine ⟨j, hj, ?_⟩
  intro B p hp
  let L : WindowLattice 2 (-(N : ℤ)) (2 * N) := ⟨B.val, by
    rw [boundedExponent]
    exact B.property⟩
  exact hc L p hp

set_option maxHeartbeats 800000 in
private theorem boundedSchemeOrbit_transport (hAction : GLJetAction)
    (ab : DominantPair) (N M : ℕ) (hN : OrbitBound ab N) (hM : OrbitBound ab M) (hNM : N ≤ M)
    (j : boundedStability N (occupiedDimension ab N hN) ⟶
      boundedStability M (occupiedDimension ab M hM))
    (hc : ∀ (B : BoundedLattice 2 N)
      (q : Points (boundedStability N (occupiedDimension ab N hN)) complexAlgebra),
      windowSchemeSubspace q = boundedSubspace B →
      windowSchemeSubspace (q ≫ j) = boundedSubspace (boundedInclusion hNM B)) :
    (fun p ↦ p ≫ j) '' boundedSchemeOrbit ab N (occupiedDimension ab N hN) =
      boundedSchemeOrbit ab M (occupiedDimension ab M hM) := by
  ext p
  constructor
  · rintro ⟨q, ⟨B, hB, hq⟩, rfl⟩
    exact ⟨boundedInclusion hNM B, hB, hc B q hq⟩
  · rintro ⟨B, hB, hp⟩
    let B' : BoundedLattice 2 N := ⟨B.val, gl2Orbit_bounded ab hN hB⟩
    obtain ⟨q, hq⟩ := point_of_boundedOrbit ab N hN hAction B' hB
    let dM := occupiedDimension ab M hM
    let G : Points (boundedStability M dM) complexAlgebra → Submodule ℂ (BoundedWindow 2 M) :=
      windowSchemeSubspace
    have hstep : G (q ≫ j) = boundedSubspace (boundedInclusion hNM B') := hc B' q hq
    have hsub : boundedSubspace (boundedInclusion hNM B') = boundedSubspace B := rfl
    have hsep : Function.Injective G := windowSchemeSubspace_injective (d := dM)
    have he : q ≫ j = p := hsep (hstep.trans (hsub.trans hp.symm))
    exact ⟨q, ⟨B', hB, hq⟩, he⟩

set_option maxHeartbeats 800000 in
theorem boundedSchubertInvariance : BoundedSchubertInvariance := by
  intro ab N M hN hM hNM
  let hTopology := BoundedLattices.boundedInclusionTopology
  let hAction := BoundedLattices.glJetAction
  let hInclusions := BoundedLattices.windowInclusions
  refine ⟨schubertLatticeSet_homeomorph hTopology ab N M hN hNM, ?_⟩
  let dN := occupiedDimension ab N hN
  let dM := occupiedDimension ab M hM
  let fN := LatticeModels.schubertInclusion ab N hN dN
  let fM := LatticeModels.schubertInclusion ab M hM dM
  obtain ⟨j, hj, hc⟩ := boundedStability_inclusion hInclusions ab N M hN hM hNM
  have hfN : IsClosedImmersion fN.left := LatticeModels.schubertScheme_closed ab N hN dN
  have hfM : IsClosedImmersion fM.left := LatticeModels.schubertScheme_closed ab M hM dM
  have hNred : IsReduced (occupiedSchubert ab N hN).left := LatticeModels.reducedClosure_reduced _ _
  have hMred : IsReduced (occupiedSchubert ab M hM).left := LatticeModels.reducedClosure_reduced _ _
  have hrange : Set.range (fN ≫ j).left = Set.range fM.left := by
    rw [range_over_comp]
    change j.left '' Set.range (LatticeModels.schubertInclusion ab N hN dN).left =
      Set.range (LatticeModels.schubertInclusion ab M hM dM).left
    rw [range_schubertInclusion, range_schubertInclusion,
      ← j.left.isClosedEmbedding.closure_image_eq,
      ← boundedSchemeOrbit_transport hAction ab N M hN hM hNM j hc,
      Set.image_image, Set.image_image]
    rfl
  have hker : (fN ≫ j).left.ker = fM.left.ker := by
    exact (LatticeModels.reduced_ker_eq (fN ≫ j).left).trans
      ((congrArg (fun S : Set (boundedStability M dM).left ↦
        Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure S)) hrange).trans
        (LatticeModels.reduced_ker_eq fM.left).symm)
  let u := IsClosedImmersion.lift fM.left (fN ≫ j).left hker.ge
  have hu : u ≫ fM.left = (fN ≫ j).left := IsClosedImmersion.lift_fac fM.left _ _
  let e : occupiedSchubert ab N hN ⟶ occupiedSchubert ab M hM :=
    Over.homMk u (by rw [← Over.w fM, ← Category.assoc, hu, Over.w])
  have : IsClosedImmersion (fN ≫ j).left := by
    change IsClosedImmersion (fN.left ≫ j.left)
    infer_instance
  have : IsIso ((Over.forget _).map e) :=
    IsClosedImmersion.isIso_of_ker_eq (fN ≫ j).left fM.left u hu hker
  have : IsIso e := isIso_of_reflects_iso e (Over.forget _)
  exact ⟨asIso e, j, fN, fM, hj, hfN, hfM, schubertInclusion_comp ab N hN dN,
    schubertInclusion_comp ab M hM dM, Over.OverMorphism.ext hu, hc⟩

private theorem adjacent_mem_iff_coeff (ab : DominantPair) (s : ℂ) {c : ℤ} {p q : ℕ}
    (hp : c + (p : ℤ) = ab.val.1 - 1) (hq : c + (q : ℤ) = ab.val.2)
    (x : Fin 2 → O) :
    shiftedInclusion 2 c x ∈ (adjacentLattice ab s).val ↔
      (∀ j < p, PowerSeries.coeff j (x 0) = 0) ∧
      (∀ j < q, PowerSeries.coeff j (x 1) = 0) ∧
      PowerSeries.coeff q (x 1) = s * PowerSeries.coeff p (x 0) := by
  rw [shiftedInclusion_adjacent_iff ab s hp hq]
  have hs (u : O) (j : ℕ) :
      PowerSeries.coeff j (PowerSeries.C s * t ^ q * u) =
        s * (if q ≤ j then PowerSeries.coeff (j - q) u else 0) := by
    rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  have htop (u : O) : PowerSeries.coeff p (t ^ p * u) = PowerSeries.coeff 0 u := by
    rw [PowerSeries.coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self]
  constructor
  · rintro ⟨u, v, h₀, h₁⟩
    refine ⟨PowerSeries.X_pow_dvd_iff.mp ⟨u, h₀⟩, ?_, ?_⟩
    · intro j hj
      rw [h₁, map_add, hs, ite_eq_right (by omega), mul_zero, zero_add,
        PowerSeries.coeff_X_pow_mul', ite_eq_right (by omega)]
    · rw [h₀, h₁, map_add, hs, ite_eq_left le_rfl, Nat.sub_self, htop,
        PowerSeries.coeff_X_pow_mul', ite_eq_right (by omega), add_zero]
  · rintro ⟨h₀, h₁, h₂⟩
    obtain ⟨u, hu⟩ := PowerSeries.X_pow_dvd_iff.mpr h₀
    have hd : t ^ (q + 1) ∣ x 1 - PowerSeries.C s * t ^ q * u := by
      apply PowerSeries.X_pow_dvd_iff.mpr
      intro j hj
      rw [map_sub, hs]
      by_cases he : j < q
      · rw [h₁ j he, ite_eq_right (by omega), mul_zero, sub_zero]
      · have hqj : j = q := by omega
        subst j
        rw [ite_eq_left le_rfl, Nat.sub_self, h₂, hu, htop, sub_self]
    obtain ⟨v, hv⟩ := hd
    exact ⟨u, v, hu, (eq_add_of_sub_eq hv).trans (add_comm _ _)⟩

private theorem coordinate_mem_iff {r m : ℕ} (c : ℤ) (L : Lattice r)
    (v : Fin r × Fin m → ℂ) :
    v ∈ (latticeSubspace c m L).map (windowCoordinates r c m).toLinearMap ↔
      ∃ x : Fin r → O, shiftedInclusion r c x ∈ L.val ∧
        ∀ i j, v (i, j) = PowerSeries.coeff j.val (x i) := by
  change (∃ w ∈ latticeSubspace c m L, windowCoordinates r c m w = v) ↔ _
  constructor
  · rintro ⟨w, hw, rfl⟩
    change ∃ u : (scalarLattice r c).val, u.val ∈ L.val ∧ windowProjection r c m u = w at hw
    obtain ⟨u, hu, rfl⟩ := hw
    obtain ⟨x, rfl⟩ := (shiftedCoordinates r c).surjective u
    exact ⟨x, hu, fun i j ↦ windowCoordinates_mkQ x i j⟩
  · rintro ⟨x, hx, h⟩
    refine ⟨windowProjection r c m (shiftedCoordinates r c x), ?_, ?_⟩
    · change ∃ u : (scalarLattice r c).val, u.val ∈ L.val ∧
        windowProjection r c m u = windowProjection r c m (shiftedCoordinates r c x)
      exact ⟨shiftedCoordinates r c x, hx, rfl⟩
    · funext ij
      obtain ⟨i, j⟩ := ij
      exact (windowCoordinates_mkQ x i j).trans (h i j).symm

private theorem adjacent_window_coeffs (ab : DominantPair) (s : ℂ) {c : ℤ} {m p q : ℕ}
    (hp : c + (p : ℤ) = ab.val.1 - 1) (hq : c + (q : ℤ) = ab.val.2)
    (hp' : p < m) (hq' : q < m) (v : Fin 2 × Fin m → ℂ) :
    v ∈ (latticeSubspace c m (adjacentLattice ab s)).map (windowCoordinates 2 c m).toLinearMap ↔
      (∀ j : Fin m, j.val < p → v (0, j) = 0) ∧
      (∀ j : Fin m, j.val < q → v (1, j) = 0) ∧
      v (1, ⟨q, hq'⟩) = s * v (0, ⟨p, hp'⟩) := by
  rw [coordinate_mem_iff]
  constructor
  · rintro ⟨x, hx, h⟩
    obtain ⟨h₀, h₁, h₂⟩ := (adjacent_mem_iff_coeff ab s hp hq x).mp hx
    exact ⟨fun j hj ↦ (h 0 j).trans (h₀ _ hj), fun j hj ↦ (h 1 j).trans (h₁ _ hj),
      by rw [h, h, h₂]⟩
  · rintro ⟨h₀, h₁, h₂⟩
    let x : Fin 2 → O := fun i ↦ PowerSeries.mk fun j ↦ if h : j < m then v (i, ⟨j, h⟩) else 0
    have hx (i : Fin 2) (j : Fin m) : PowerSeries.coeff j.val (x i) = v (i, j) := by
      simp [x, j.isLt]
    refine ⟨x, (adjacent_mem_iff_coeff ab s hp hq x).mpr ⟨?_, ?_, ?_⟩, fun i j ↦ (hx i j).symm⟩
    · intro j hj
      exact (hx 0 ⟨j, hj.trans hp'⟩).trans (h₀ _ hj)
    · intro j hj
      exact (hx 1 ⟨j, hj.trans hq'⟩).trans (h₁ _ hj)
    · rw [show PowerSeries.coeff q (x 1) = _ from hx 1 ⟨q, hq'⟩,
        show PowerSeries.coeff p (x 0) = _ from hx 0 ⟨p, hp'⟩, h₂]

private theorem adjacent_upper (ab : DominantPair) (h : 2 ≤ difference ab) (s : ℂ) :
    (adjacentLattice ab s).val ≤ (scalarLattice 2 ab.val.2).val := by
  have hp : 0 ≤ ab.val.1 - 1 - ab.val.2 := by
    unfold difference at h
    omega
  let p := (ab.val.1 - 1 - ab.val.2).toNat
  have hp' : ab.val.2 + (p : ℤ) = ab.val.1 - 1 := by
    dsimp [p]
    rw [Int.toNat_of_nonneg hp]
    omega
  rw [adjacentLattice_val, Submodule.span_le, scalarLattice_val]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · refine ⟨![t ^ p, PowerSeries.C s], ?_⟩
    funext j
    fin_cases j
    · change monomial ab.val.2 * inclusion (t ^ p) = monomial (ab.val.1 - 1)
      rw [← monomial_nat, ← monomial_add, hp']
    · change monomial ab.val.2 * ((PowerSeries.C s : O) : K) = s • monomial ab.val.2
      rw [PowerSeries.coe_C, mul_comm]
      exact HahnSeries.single_zero_mul_eq_smul
  · refine ⟨![0, t], ?_⟩
    funext j
    fin_cases j
    · change monomial ab.val.2 * inclusion 0 = 0
      rw [map_zero, mul_zero]
    · change monomial ab.val.2 * inclusion t = monomial (ab.val.2 + 1)
      nth_rw 1 [← pow_one t]
      rw [← monomial_nat, ← monomial_add]
      rfl

private theorem adjacent_not_upper (ab : DominantPair) {s : ℂ} (hs : s ≠ 0) :
    ¬ (adjacentLattice ab s).val ≤ (scalarLattice 2 (ab.val.2 + 1)).val := by
  intro h
  have hx : adjacentColumn ab s 0 ∈ (adjacentLattice ab s).val := by
    rw [adjacentLattice_val]
    exact Submodule.subset_span (Set.mem_range_self 0)
  obtain ⟨z, hz⟩ := (mem_diagonalLattice_iff (fun _ : Fin 2 ↦ ab.val.2 + 1) _).mp (h hx)
  have hz' := hz 1
  change s • monomial ab.val.2 = monomial (ab.val.2 + 1) * inclusion (z 1) at hz'
  have hc := congrArg (fun w : K ↦ w.coeff ab.val.2) hz'
  rw [HahnSeries.coeff_smul, monomial, HahnSeries.coeff_single_same, smul_eq_mul, mul_one,
    monomial, HahnSeries.coeff_single_mul, one_mul,
    show ab.val.2 - (ab.val.2 + 1) = (-1 : ℤ) by omega] at hc
  change s = ((z 1 : O) : K).coeff (-1) at hc
  rw [PowerSeries.coeff_coe, ite_eq_left (by omega)] at hc
  exact hs hc

private theorem adjacent_bounded (ab : DominantPair) (h : 2 ≤ difference ab) (s : ℂ)
    (N : ℕ) (hN : OrbitBound ab N) :
    (scalarLattice 2 (N : ℤ)).val ≤ (adjacentLattice ab s).val ∧
      (adjacentLattice ab s).val ≤ (scalarLattice 2 (-(N : ℤ))).val := by
  have hgap : 2 ≤ ab.val.1 - ab.val.2 := by
    unfold difference at h
    omega
  have hU : ab.val.1 ≤ (N : ℤ) := by simpa [pairCoweight] using (hN 0).2
  have hL : -(N : ℤ) ≤ ab.val.2 := by simpa [pairCoweight] using (hN 1).1
  refine ⟨?_, (adjacent_upper ab h s).trans (diagonalLattice_le (fun _ ↦ hL))⟩
  rw [scalarLattice_val]
  rintro _ ⟨x, rfl⟩
  let c : ℤ := -(N : ℤ)
  let p := (ab.val.1 - 1 - c).toNat
  let q := (ab.val.2 - c).toNat
  have hp : c + (p : ℤ) = ab.val.1 - 1 := by dsimp [p, c]; omega
  have hq : c + (q : ℤ) = ab.val.2 := by dsimp [q, c]; omega
  have hp' : p < 2 * N := by dsimp [c] at hp; omega
  have hq' : q < 2 * N := by dsimp [c] at hq; omega
  rw [← boundedExponent N, shiftedInclusion_add_nat]
  apply (adjacent_mem_iff_coeff ab s hp hq _).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    change PowerSeries.coeff j (t ^ (2 * N) * x 0) = 0
    rw [PowerSeries.coeff_X_pow_mul', ite_eq_right (by omega)]
  · intro j hj
    change PowerSeries.coeff j (t ^ (2 * N) * x 1) = 0
    rw [PowerSeries.coeff_X_pow_mul', ite_eq_right (by omega)]
  · change PowerSeries.coeff q (t ^ (2 * N) * x 1) =
      s * PowerSeries.coeff p (t ^ (2 * N) * x 0)
    rw [PowerSeries.coeff_X_pow_mul', ite_eq_right (by omega), PowerSeries.coeff_X_pow_mul',
      ite_eq_right (by omega), mul_zero]

private def entryPolynomial {ι : Type} [DecidableEq ι] {d : ℕ} (I : Pivot ι d)
    (j : Outside I) (i : Inside I) : Matrix (Outside I) (Inside I) (Polynomial ℂ) :=
  Matrix.of fun k l ↦ if k = j ∧ l = i then Polynomial.X else 0

private theorem graph_entry_iff {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ} (I : Pivot ι d)
    (j₀ : Outside I) (i₀ : Inside I) (s : ℂ) (v : ι → ℂ) :
    v ∈ (Matrix.toLin' (graphMatrix I ((entryPolynomial I j₀ i₀).map (Polynomial.eval s)))).range ↔
      ∀ j : Outside I, v j.val = if j = j₀ then s * v i₀.val else 0 := by
  let A := (entryPolynomial I j₀ i₀).map (Polynomial.eval s)
  have hA (u : Inside I → ℂ) (j : Outside I) :
      (A *ᵥ u) j = if j = j₀ then s * u i₀ else 0 := by
    change (∑ i : Inside I, Polynomial.eval s
      (if j = j₀ ∧ i = i₀ then Polynomial.X else 0) * u i) = _
    by_cases h : j = j₀
    · subst j
      rw [ite_eq_left rfl, Finset.sum_eq_single i₀]
      · simp
      · intro i _ hi
        simp [hi]
      · simp
    · simp [h]
  change v ∈ (Matrix.toLin' (graphMatrix I A)).range ↔ _
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨u, rfl⟩ j
    rw [Matrix.toLin'_apply, graphMatrix_outside, hA, graphMatrix_inside]
  · intro hv
    refine ⟨fun i ↦ v i.val, ?_⟩
    rw [Matrix.toLin'_apply]
    funext k
    by_cases hk : k ∈ I.val
    · exact graphMatrix_inside I A (fun i ↦ v i.val) ⟨k, hk⟩
    · exact (graphMatrix_outside I A (fun i ↦ v i.val) ⟨k, hk⟩).trans
        ((hA (fun i ↦ v i.val) ⟨k, hk⟩).trans (hv ⟨k, hk⟩).symm)

set_option maxHeartbeats 600000 in
private theorem adjacent_specialization (hAction : GLJetAction) (hExhaustion : LatticeExhaustion) :
    AdjacentSpecialization := by
  classical
  intro ab h N hN
  let d := occupiedDimension ab N hN
  let c : ℤ := -(N : ℤ)
  let m := 2 * N
  let p := (ab.val.1 - 1 - c).toNat
  let q := (ab.val.2 - c).toNat
  have hgap : 2 ≤ ab.val.1 - ab.val.2 := by unfold difference at h; omega
  have hU : ab.val.1 ≤ (N : ℤ) := by simpa [pairCoweight] using (hN 0).2
  have hL : -(N : ℤ) ≤ ab.val.2 := by simpa [pairCoweight] using (hN 1).1
  have hp : c + (p : ℤ) = ab.val.1 - 1 := by dsimp [p, c]; omega
  have hq : c + (q : ℤ) = ab.val.2 := by dsimp [q, c]; omega
  have hpm : p < m := by dsimp [c] at hp; dsimp [m]; omega
  have hqm : q < m := by dsimp [c] at hq; dsimp [m]; omega
  let pF : Fin m := ⟨p, hpm⟩
  let qF : Fin m := ⟨q, hqm⟩
  let I₀ := ({0} : Finset (Fin 2)) ×ˢ Finset.Ici pF
  let I₁ := ({1} : Finset (Fin 2)) ×ˢ Finset.Ioi qF
  have hDisjoint : Disjoint I₀ I₁ := by
    rw [Finset.disjoint_left]
    rintro ⟨i,j⟩ hi hj
    simp only [I₀, I₁, Finset.mem_product, Finset.mem_singleton] at hi hj
    exact Fin.zero_ne_one (hi.1.symm.trans hj.1)
  have hDim : (I₀ ∪ I₁).card = d.val := by
    have hd : Occupied ab N d := occupiedDimension_occupied ab N hN
    unfold Occupied at hd
    rw [Finset.card_union_of_disjoint hDisjoint]
    simp only [I₀, I₁, Finset.card_product, Finset.card_singleton, one_mul, Fin.card_Ici, Fin.card_Ioi]
    change m - p + (m - 1 - q) = d.val
    dsimp [c] at hp hq
    dsimp [m] at *
    omega
  let I : Pivot (Fin 2 × Fin m) d.val := ⟨I₀ ∪ I₁, hDim⟩
  have hP₀ (j : Fin m) : (0, j) ∈ I.val ↔ p ≤ j.val := by
    simp [I, I₀, I₁, pF, Fin.le_def]
  have hP₁ (j : Fin m) : (1, j) ∈ I.val ↔ q < j.val := by
    simp [I, I₀, I₁, qF, Fin.lt_def]
  let i₀ : Inside I := ⟨(0, pF), (hP₀ pF).mpr le_rfl⟩
  let j₀ : Outside I := ⟨(1, qF), fun hy ↦ (lt_irrefl q) ((hP₁ qF).mp hy)⟩
  let A := entryPolynomial I j₀ i₀
  let B (s : ℂ) : BoundedLattice 2 N := ⟨adjacentLattice ab s, adjacent_bounded ab h s N hN⟩
  have hgraph (s : ℂ) : grassmannianSubspace (windowBasis 2 c m) (windowDimension_le d)
      (grassmannianChartPoint (windowBasis 2 c m) (windowDimension_le d) I
        (A.map (Polynomial.eval s))) = boundedSubspace (B s) := by
    let e := (windowBasis 2 c m).equivFun
    apply Submodule.map_injective_of_injective e.injective
    rw [grassmannianChartSubspace]
    change (Matrix.toLin' (graphMatrix I (A.map (Polynomial.eval s)))).range =
      (latticeSubspace c m (adjacentLattice ab s)).map e.toLinearMap
    have he : e = windowCoordinates 2 c m := Module.Basis.equivFun_ofEquivFun _
    rw [he]
    ext v
    rw [graph_entry_iff, adjacent_window_coeffs ab s hp hq hpm hqm v]
    constructor
    · intro hv
      refine ⟨?_, ?_, ?_⟩
      · intro j hj
        let k : Outside I := ⟨(0,j), fun hg ↦ (not_le.mpr hj) ((hP₀ j).mp hg)⟩
        have hk : k ≠ j₀ := fun eq ↦ Fin.zero_ne_one
          (congrArg (fun w : Outside I ↦ w.val.1) eq)
        exact (hv k).trans (ite_eq_right hk)
      · intro j hj
        let k : Outside I := ⟨(1,j), fun hg ↦ (not_lt.mpr hj.le) ((hP₁ j).mp hg)⟩
        have hk : k ≠ j₀ := fun eq ↦ (ne_of_lt hj)
          (congrArg (fun w : Outside I ↦ w.val.2.val) eq)
        exact (hv k).trans (ite_eq_right hk)
      · exact (hv j₀).trans (ite_eq_left rfl)
    · rintro ⟨h₀, h₁, h₂⟩ k
      obtain ⟨⟨i, j⟩, hj⟩ := k
      fin_cases i
      · change v (0,j) = if (⟨(0,j), hj⟩ : Outside I) = j₀ then s * v i₀.val else 0
        have hj' : j.val < p := not_le.mp (fun hh ↦ hj ((hP₀ j).mpr hh))
        have hn : (⟨(0,j), hj⟩ : Outside I) ≠ j₀ := fun eq ↦ Fin.zero_ne_one
          (congrArg (fun w : Outside I ↦ w.val.1) eq)
        rw [ite_eq_right hn]
        exact h₀ j hj'
      · change v (1,j) = if (⟨(1,j), hj⟩ : Outside I) = j₀ then s * v i₀.val else 0
        have hj' : j.val ≤ q := not_lt.mp (fun hh ↦ hj ((hP₁ j).mpr hh))
        by_cases heq : j = qF
        · subst j
          rw [ite_eq_left (show (⟨(1,qF), hj⟩ : Outside I) = j₀ from rfl)]
          exact h₂
        · have hn : (⟨(1,j), hj⟩ : Outside I) ≠ j₀ := fun eq ↦
            heq (congrArg (fun w : Outside I ↦ w.val.2) eq)
          rw [ite_eq_right hn]
          exact h₁ j (lt_of_le_of_ne hj' (fun eq ↦ heq (Fin.ext eq)))
  refine ⟨I, A, B, adjacentLattice_val ab, hgraph, ?_, adjacentLattice_zero ab h⟩
  intro s hs
  obtain ⟨cd, hc⟩ := orbit_exists hExhaustion (B s).val
  have hf := grassmannianSubspace_finrank (windowBasis 2 c m) (windowDimension_le d)
    (grassmannianChartPoint (windowBasis 2 c m) (windowDimension_le d) I (A.map (Polynomial.eval s)))
  rw [hgraph s] at hf
  have hfd : (boundedPoint (B s)).1 = d := Fin.ext hf
  have hcd : Occupied cd N (boundedPoint (B s)).1 := occupied_of_mem_boundedOrbit hAction hc
  rw [hfd] at hcd
  have hab : Occupied ab N d := occupiedDimension_occupied ab N hN
  obtain ⟨_, hu⟩ := orbit_endpoints hc
  have hc₁ : ab.val.2 ≤ cd.val.2 := (hu _).mp (adjacent_upper ab h s)
  have hc₂ : ¬ ab.val.2 + 1 ≤ cd.val.2 := fun hle ↦ adjacent_not_upper ab hs ((hu _).mpr hle)
  have hEq : cd = ab := by
    apply Subtype.ext
    apply Prod.ext
    · unfold Occupied at hcd hab
      omega
    · omega
  exact hEq ▸ hc

theorem adjacentSpecialization : AdjacentSpecialization := by
  exact adjacent_specialization BoundedLattices.glJetAction BoundedLattices.latticeExhaustion

private theorem continuous_grassmannianChartPoint {V ι : Type} [AddCommGroup V] [Module ℂ V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ V) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ V) (I : Pivot ι d) :
    Continuous (grassmannianChartPoint b hd I) := by
  change @Continuous _ _ _ (⨆ J : Pivot ι d, TopologicalSpace.coinduced
    (grassmannianChartPoint b hd J) inferInstance) _
  exact continuous_iSup_rng (i := I) continuous_coinduced_rng

private theorem continuous_bounded_curve (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (I : Pivot (Fin 2 × Fin (2 * N)) (occupiedDimension ab N hN).val)
    (A : Matrix (Outside I) (Inside I) (Polynomial ℂ)) (B : ℂ → BoundedLattice 2 N)
    (hB : ∀ s, grassmannianSubspace (windowBasis 2 (-(N : ℤ)) (2 * N))
        (windowDimension_le (occupiedDimension ab N hN))
        (grassmannianChartPoint (windowBasis 2 (-(N : ℤ)) (2 * N))
          (windowDimension_le (occupiedDimension ab N hN)) I (A.map (Polynomial.eval s))) =
      boundedSubspace (B s)) :
    Continuous B := by
  let d := occupiedDimension ab N hN
  let b := windowBasis 2 (-(N : ℤ)) (2 * N)
  let D := windowOperator 2 (-(N : ℤ)) (2 * N)
  let F : ℂ → WindowPoints 2 (-(N : ℤ)) (2 * N) d :=
    fun s ↦ grassmannianChartPoint b (windowDimension_le d) I (A.map (Polynomial.eval s))
  have hF : Continuous F := (continuous_grassmannianChartPoint b (windowDimension_le d) I).comp
    (continuous_matrix fun i j ↦ (A i j).continuous)
  have hs (s : ℂ) : StablePlane b (windowDimension_le d) D (F s) := by
    change (grassmannianSubspace b (windowDimension_le d) (F s)).map D ≤ _
    have hEq : grassmannianSubspace b (windowDimension_le d) (F s) = boundedSubspace (B s) := hB s
    rw [hEq]
    exact latticeSubspace_stable _ _ (B s).val
  let H : ℂ → BoundedStage 2 N := fun s ↦ ⟨d, ⟨F s, hs s⟩⟩
  have hmk : Continuous (fun p : StablePoints b (windowDimension_le d) D ↦
      (⟨d, p⟩ : BoundedStage 2 N)) :=
    @continuous_sigmaMk _ _ (fun e ↦ stablePointsTopology b (windowDimension_le e) D) d
  have hH : Continuous H := hmk.comp (hF.subtype_mk hs)
  have hEq : (boundedPoint (r := 2) (N := N)) ∘ B = H := by
    funext s
    have hf := grassmannianSubspace_finrank b (windowDimension_le d) (F s)
    have hFB : grassmannianSubspace b (windowDimension_le d) (F s) = boundedSubspace (B s) := hB s
    rw [hFB] at hf
    have hd : (boundedPoint (B s)).1 = d := Fin.ext hf
    have hmap := windowStagePoint_subspace (-(N : ℤ)) (2 * N) (B s).val
    let P : BoundedStage 2 N := boundedPoint (B s)
    change windowStageSubspace P = boundedSubspace (B s) at hmap
    change P = ⟨d, ⟨F s, hs s⟩⟩
    change P.1 = d at hd
    obtain ⟨d', p⟩ := P
    change d' = d at hd
    subst d'
    congr 1
    apply Subtype.ext
    exact grassmannianSubspace_injective b (windowDimension_le d) (hmap.trans hFB.symm)
  exact continuous_induced_rng.mpr (hEq.symm ▸ hH)

private def boundedSmul (hStable : WindowPositiveStable) (N : ℕ)
    (g : GL (Fin 2) O) (L : BoundedLattice 2 N) : BoundedLattice 2 N := by
  let W : WindowLattice 2 (-(N : ℤ)) (2 * N) :=
    ⟨L.val, by rw [boundedExponent]; exact L.property⟩
  refine ⟨positiveGLMap 2 g • L.val, ?_⟩
  have h := hStable 2 (-(N : ℤ)) (2 * N) g W
  have hl : (scalarLattice 2 (-(N : ℤ) + ((2 * N : ℕ) : ℤ))).val ≤
      (positiveGLMap 2 g • L.val).val := h.1
  rw [boundedExponent] at hl
  exact ⟨hl, h.2⟩

private theorem boundedSmul_continuous (hStable : WindowPositiveStable) (hAction : GLJetAction)
    (N : ℕ) (g : GL (Fin 2) O) : Continuous (boundedSmul hStable N g) := by
  let n := 2 * N + 1
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hmn : 2 * N ≤ n := by dsimp [n]; omega
  obtain ⟨ρ, _, hreduce, hcont⟩ := hAction 2 (-(N : ℤ)) (2 * N) n hn hmn
  have hB : Continuous (boundedPoint (r := 2) (N := N)) := continuous_induced_dom
  have hfun :
      (boundedPoint (r := 2) (N := N)) ∘ boundedSmul hStable N g =
        fun L ↦ ρ.smul (reduceGL 2 n hn g) (boundedPoint L) :=
    funext fun L ↦ by
      change windowStagePoint (-(N : ℤ)) (2 * N) (positiveGLMap 2 g • L.val) = _
      exact (hreduce g L.val).symm
  apply continuous_induced_rng.mpr
  rw [hfun]
  exact hcont.comp (continuous_const.prodMk hB)

private theorem boundedSmul_mapsTo_orbit (hStable : WindowPositiveStable) (ab : DominantPair)
    (N : ℕ) (g : GL (Fin 2) O) :
    Set.MapsTo (boundedSmul hStable N g) (boundedOrbit ab N) (boundedOrbit ab N) := by
  intro L hL
  change (positiveGLMap 2 g • L.val) ∈ gl2Orbit ab
  exact smul_mem_gl2Orbit ab ⟨positiveGLMap 2 g, ⟨g, rfl⟩⟩ hL

private theorem adjacent_subset_analyticClosure (hAdjacent : AdjacentSpecialization)
    (hStable : WindowPositiveStable) (hAction : GLJetAction) (ab : DominantPair)
    (h : 2 ≤ difference ab) (N : ℕ) (hN : OrbitBound ab N) :
    boundedOrbit (adjacentPair ab h) N ⊆ closure (boundedOrbit ab N) := by
  obtain ⟨I, A, B, _, hgraph, hOrbit, hzero⟩ := hAdjacent ab h N hN
  have hcont : Continuous B := continuous_bounded_curve ab N hN I A B hgraph
  have hm : B 0 ∈ closure (boundedOrbit ab N) := by
    have hz : (0 : ℂ) ∈ closure ({0}ᶜ : Set ℂ) :=
      (dense_compl_singleton (0 : ℂ)) 0
    have hB : B 0 ∈ closure (B '' ({0}ᶜ : Set ℂ)) :=
      image_closure_subset_closure_image hcont ⟨0, hz, rfl⟩
    apply closure_mono (t := boundedOrbit ab N) _ hB
    rintro _ ⟨s, hs, rfl⟩
    exact hOrbit s (Set.mem_compl_singleton_iff.mp hs)
  intro L hL
  change L.val ∈ gl2Orbit (adjacentPair ab h) at hL
  obtain ⟨⟨_, ⟨g, rfl⟩⟩, hL⟩ := hL
  let f := boundedSmul hStable N g
  have hEq : f (B 0) = L := by
    apply Subtype.ext
    change positiveGLMap 2 g • (B 0).val = L.val
    exact (congrArg (fun T : GL2Lattice ↦ positiveGLMap 2 g • T) hzero).trans hL
  rw [← hEq]
  apply closure_mono (t := boundedOrbit ab N) (boundedSmul_mapsTo_orbit hStable ab N g).image_subset
  exact image_closure_subset_closure_image (boundedSmul_continuous hStable hAction N g)
    ⟨B 0, hm, rfl⟩

private theorem below_subset_analyticClosure (hAdjacent : AdjacentSpecialization)
    (hStable : WindowPositiveStable) (hAction : GLJetAction)
    {ab cd : DominantPair} {N : ℕ} (hN : OrbitBound ab N) (h : Below cd ab) :
    boundedOrbit cd N ⊆ closure (boundedOrbit ab N) := by
  obtain ⟨j, hj, ha, hb⟩ := h
  induction j generalizing ab with
  | zero =>
    have he : cd = ab := Subtype.ext (Prod.ext (by simpa using ha) (by simpa using hb))
    subst cd
    exact subset_closure
  | succ j ih =>
    have h' : 2 ≤ difference ab := by dsimp [difference]; omega
    let ab' := adjacentPair ab h'
    have hbelow : Below ab' ab := ⟨1, by push_cast; omega, rfl, rfl⟩
    have hN' : OrbitBound ab' N := orbitBound_of_below hbelow hN
    have hc : boundedOrbit cd N ⊆ closure (boundedOrbit ab' N) := by
      apply ih hN'
      · change 2 * (j : ℤ) ≤ (ab.val.1 - 1) - (ab.val.2 + 1)
        omega
      · change cd.val.1 = ab.val.1 - 1 - (j : ℤ)
        omega
      · change cd.val.2 = ab.val.2 + 1 + (j : ℤ)
        omega
    exact hc.trans (closure_minimal (adjacent_subset_analyticClosure hAdjacent hStable hAction
      ab h' N hN) isClosed_closure)


private theorem graph_mem_range_iff {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (I : Pivot ι d) (A : Matrix (Outside I) (Inside I) ℂ) (v : ι → ℂ) :
    v ∈ (Matrix.toLin' (graphMatrix I A)).range ↔
      ∀ j : Outside I, v j.val = (A *ᵥ (fun i : Inside I ↦ v i.val)) j := by
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨u, rfl⟩ j
    simp only [Matrix.toLin'_apply, graphMatrix_outside, graphMatrix_inside]
  · intro hv
    refine ⟨fun i ↦ v i.val, ?_⟩
    rw [Matrix.toLin'_apply]
    funext k
    by_cases hk : k ∈ I.val
    · exact graphMatrix_inside I A (fun i ↦ v i.val) ⟨k, hk⟩
    · exact (graphMatrix_outside I A (fun i ↦ v i.val) ⟨k, hk⟩).trans (hv ⟨k, hk⟩).symm

private theorem isClosed_incidence_affine {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (I : Pivot ι d) (P Q : Submodule ℂ (ι → ℂ)) :
    IsClosed {A : Matrix (Outside I) (Inside I) ℂ |
      P ≤ (Matrix.toLin' (graphMatrix I A)).range ∧
      (Matrix.toLin' (graphMatrix I A)).range ≤ Q} := by
  have hEval (u : Inside I → ℂ) (j : Outside I) :
      Continuous (fun A : Matrix (Outside I) (Inside I) ℂ ↦ (A *ᵥ u) j) := by
    exact continuous_finsetSum _ (fun i _ ↦ (continuous_apply_apply j i).mul continuous_const)
  let C₁ := ⋂ v : P, ⋂ j : Outside I, {A : Matrix (Outside I) (Inside I) ℂ |
    v.val j.val = (A *ᵥ (fun i : Inside I ↦ v.val i.val)) j}
  let C₂ := ⋂ u : Inside I → ℂ, (fun A : Matrix (Outside I) (Inside I) ℂ ↦
    graphMatrix I A *ᵥ u) ⁻¹' (Q : Set (ι → ℂ))
  have hc₁ : IsClosed C₁ := isClosed_iInter fun v ↦ isClosed_iInter fun j ↦
    isClosed_eq continuous_const (hEval (fun i ↦ v.val i.val) j)
  have hc₂ : IsClosed C₂ := by
    apply isClosed_iInter
    intro u
    apply Q.closed_of_finiteDimensional.preimage
    apply continuous_pi
    intro j
    by_cases hj : j ∈ I.val
    · change Continuous (fun A : Matrix (Outside I) (Inside I) ℂ ↦ (graphMatrix I A *ᵥ u) j)
      simp only [show (fun A : Matrix (Outside I) (Inside I) ℂ ↦ (graphMatrix I A *ᵥ u) j) =
        fun _ ↦ u ⟨j, hj⟩ from funext fun A ↦ graphMatrix_inside I A u ⟨j, hj⟩]
      exact continuous_const
    · change Continuous (fun A : Matrix (Outside I) (Inside I) ℂ ↦ (graphMatrix I A *ᵥ u) j)
      simp only [show (fun A : Matrix (Outside I) (Inside I) ℂ ↦ (graphMatrix I A *ᵥ u) j) =
        fun A ↦ (A *ᵥ u) ⟨j, hj⟩ from funext fun A ↦ graphMatrix_outside I A u ⟨j, hj⟩]
      exact hEval u ⟨j, hj⟩
  convert hc₁.inter hc₂ using 1
  ext A
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, C₁, C₂, Set.mem_iInter, Set.mem_preimage,
    SetLike.mem_coe]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun v j ↦ (graph_mem_range_iff I A v.val).mp (h₁ v.property) j, ?_⟩
    intro u
    apply h₂
    exact ⟨u, rfl⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun v hv ↦ (graph_mem_range_iff I A v).mpr (h₁ ⟨v, hv⟩), ?_⟩
    rintro _ ⟨u, rfl⟩
    exact h₂ u

private theorem isClosed_grassmannian_incidence {V ι : Type}
    [AddCommGroup V] [Module ℂ V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ V) {d : ℕ} (hd : d ≤ Module.finrank ℂ V) (P Q : Submodule ℂ V) :
    IsClosed {p : GrassmannianPoints b hd |
      P ≤ grassmannianSubspace b hd p ∧ grassmannianSubspace b hd p ≤ Q} := by
  change @IsClosed _ (⨆ I : Pivot ι d, TopologicalSpace.coinduced
    (grassmannianChartPoint b hd I) inferInstance) _
  rw [isClosed_iSup_iff]
  intro I
  rw [isClosed_coinduced]
  convert isClosed_incidence_affine I (P.map b.equivFun.toLinearMap)
    (Q.map b.equivFun.toLinearMap) using 1
  ext A
  change (P ≤ grassmannianSubspace b hd (grassmannianChartPoint b hd I A) ∧
    grassmannianSubspace b hd (grassmannianChartPoint b hd I A) ≤ Q) ↔ _
  rw [← Submodule.map_le_map_iff_of_injective b.equivFun.injective P
    (grassmannianSubspace b hd (grassmannianChartPoint b hd I A)),
    ← Submodule.map_le_map_iff_of_injective b.equivFun.injective
    (grassmannianSubspace b hd (grassmannianChartPoint b hd I A)) Q,
    grassmannianChartSubspace]
  rfl

set_option maxHeartbeats 700000 in
private theorem latticeSubspace_le_iff {r : ℕ} {c : ℤ} {m : ℕ} {L S : Lattice r}
    (hL : L.val ≤ (scalarLattice r c).val)
    (hS : (scalarLattice r (c + (m : ℤ))).val ≤ S.val) :
    latticeSubspace c m L ≤ latticeSubspace c m S ↔ L.val ≤ S.val := by
  let U := (scalarLattice r c).val
  let f : U →ₗ[O] Coordinates r := U.subtype
  let q : U →ₗ[O] Window r c m := windowProjection r c m
  change (L.val.comap f).map q ≤ (S.val.comap f).map q ↔ _
  rw [Submodule.map_le_iff_le_comap]
  have h : ((S.val.comap f).map q).comap q = S.val.comap f := by
    have hq := @Submodule.comap_map_mkQ O (U : Type) inferInstance inferInstance
      inferInstance (windowLower r c m) (S.val.comap f)
    have hle : windowLower r c m ≤ S.val.comap f := fun x hx ↦ hS hx
    exact hq.trans (sup_eq_right.mpr hle)
  rw [h]
  constructor
  · intro h' x hx
    have hm : (⟨x, hL hx⟩ : U) ∈ L.val.comap f := hx
    exact h' hm
  · intro hle
    exact Submodule.comap_mono hle

private theorem closed_bounded_incidence (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) :
    IsClosed {B : BoundedLattice 2 N | Between ab.val.1 ab.val.2 B.val} := by
  let c : ℤ := -(N : ℤ)
  let m := 2 * N
  let P := latticeSubspace c m (scalarLattice 2 ab.val.1)
  let Q := latticeSubspace c m (scalarLattice 2 ab.val.2)
  let C : Set (BoundedStage 2 N) := {p | P ≤ windowStageSubspace p ∧ windowStageSubspace p ≤ Q}
  have hC : IsClosed C := by
    apply (@isClosed_sigma_iff _ _ (fun e ↦ stablePointsTopology (windowBasis 2 c m)
      (windowDimension_le e) (windowOperator 2 c m)) C).mpr
    intro d
    exact (isClosed_grassmannian_incidence (windowBasis 2 c m) (windowDimension_le d)
      P Q).preimage continuous_subtype_val
  have hU : ab.val.1 ≤ (N : ℤ) := by simpa [pairCoweight] using (hN 0).2
  have hL : -(N : ℤ) ≤ ab.val.2 := by simpa [pairCoweight] using (hN 1).1
  have hab : ab.val.2 ≤ ab.val.1 := ab.property
  have hP : (scalarLattice 2 ab.val.1).val ≤ (scalarLattice 2 c).val :=
    diagonalLattice_le fun _ ↦ le_trans hL hab
  have hQ : (scalarLattice 2 (c + (m : ℤ))).val ≤ (scalarLattice 2 ab.val.2).val := by
    change (scalarLattice 2 (-(N : ℤ) + ((2 * N : ℕ) : ℤ))).val ≤ _
    rw [boundedExponent]
    exact diagonalLattice_le fun _ ↦ le_trans hab hU
  have hEq : {B : BoundedLattice 2 N | Between ab.val.1 ab.val.2 B.val} =
      boundedPoint ⁻¹' C := by
    ext B
    change Between ab.val.1 ab.val.2 B.val ↔
      P ≤ windowStageSubspace (windowStagePoint c m B.val) ∧
        windowStageSubspace (windowStagePoint c m B.val) ≤ Q
    have hB : (scalarLattice 2 (c + (m : ℤ))).val ≤ B.val.val := by
      change (scalarLattice 2 (-(N : ℤ) + ((2 * N : ℕ) : ℤ))).val ≤ B.val.val
      rw [boundedExponent]
      exact B.property.1
    rw [windowStagePoint_subspace, latticeSubspace_le_iff hP hB,
      latticeSubspace_le_iff B.property.2 hQ]
    rfl
  rw [hEq]
  exact hC.preimage continuous_induced_dom

private theorem continuous_pointToPoint {σ : Type} :
    Continuous (MvPolynomial.pointToPoint (k := ℂ) (σ := σ) (K := ℂ)) := by
  rw [continuous_iff_isClosed]
  intro S hS
  obtain ⟨J, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus S).mp hS
  have hEq : MvPolynomial.pointToPoint (k := ℂ) (σ := σ) (K := ℂ) ⁻¹'
      PrimeSpectrum.zeroLocus J =
      ⋂ p : J, {x : σ → ℂ | MvPolynomial.eval x p.val = 0} := by
    ext x
    change J ⊆ ((MvPolynomial.pointToPoint (k := ℂ) x).asIdeal : Set _) ↔ _
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨fun h p ↦ (MvPolynomial.mem_vanishingIdeal_singleton_iff x p.val).mp (h p.property),
      fun h p hp ↦ (MvPolynomial.mem_vanishingIdeal_singleton_iff x p).mpr (h ⟨p, hp⟩)⟩
  rw [hEq]
  exact isClosed_iInter fun p ↦ isClosed_eq (MvPolynomial.continuous_eval p.val) continuous_const

private theorem continuous_pointLocation_grassmannian {V ι : Type} [AddCommGroup V] [Module ℂ V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ V) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ V) :
    Continuous (pointLocation : GrassmannianPoints b hd → (grassmannianCharts b hd).scheme.left) := by
  change @Continuous _ _ (⨆ I : Pivot ι d, TopologicalSpace.coinduced
    (grassmannianChartPoint b hd I) inferInstance) _ _
  rw [continuous_iSup_dom]
  intro I
  rw [continuous_coinduced_dom]
  have hloc (A : Matrix (Outside I) (Inside I) ℂ) :
      pointLocation (grassmannianChartPoint b hd I A) =
        (chartInclusion b hd I) (MvPolynomial.pointToPoint (k := ℂ) (chartVariables I A)) := by
    unfold grassmannianChartPoint
    rw [pointLocation_comp, chart_location]
    rfl
  change Continuous (fun A ↦ pointLocation (grassmannianChartPoint b hd I A))
  simp only [hloc]
  exact (chartInclusion b hd I).continuous.comp
    (continuous_pointToPoint.comp (continuous_pi fun ij ↦ continuous_apply_apply ij.1 ij.2))

private theorem boundedPoint_eq_of_subspace_eq {N : ℕ} {L : BoundedLattice 2 N}
    {d : WindowDimension 2 (-(N : ℤ)) (2 * N)}
    {p : StablePoints (windowBasis 2 (-(N : ℤ)) (2 * N)) (windowDimension_le d)
      (windowOperator 2 (-(N : ℤ)) (2 * N))}
    (hp : windowStageSubspace ⟨d, p⟩ = boundedSubspace L) :
    boundedPoint L = ⟨d, p⟩ := by
  have hf := grassmannianSubspace_finrank (windowBasis 2 (-(N : ℤ)) (2 * N))
    (windowDimension_le d) p.val
  change grassmannianSubspace (windowBasis 2 (-(N : ℤ)) (2 * N))
    (windowDimension_le d) p.val = boundedSubspace L at hp
  rw [hp] at hf
  have hd : (boundedPoint L).1 = d := Fin.ext hf
  have hsub := windowStagePoint_subspace (-(N : ℤ)) (2 * N) L.val
  let P := boundedPoint L
  change windowStageSubspace P = boundedSubspace L at hsub
  change P.1 = d at hd
  change P = ⟨d, p⟩
  obtain ⟨d', q⟩ := P
  change d' = d at hd
  subst d'
  congr 1
  apply Subtype.ext
  exact grassmannianSubspace_injective _ _ (hsub.trans hp.symm)

private theorem mem_zariski_closure_of_mem_analytic {N : ℕ}
    (hAction : GLJetAction) (ab : DominantPair) (hN : OrbitBound ab N)
    (d : WindowDimension 2 (-(N : ℤ)) (2 * N))
    (L : BoundedLattice 2 N) (hL : L ∈ closure (boundedOrbit ab N))
    (p : WindowPoints 2 (-(N : ℤ)) (2 * N) d)
    (hp : grassmannianSubspace (windowBasis 2 (-(N : ℤ)) (2 * N)) (windowDimension_le d) p =
      boundedSubspace L) :
    pointLocation p ∈ closure (pointLocation '' schubertOrbitPoints ab N hN d) := by
  let c : ℤ := -(N : ℤ)
  let m := 2 * N
  let b := windowBasis 2 c m
  let D := windowOperator 2 c m
  let T (e : WindowDimension 2 c m) := StablePoints b (windowDimension_le e) D
  let Mk : T d → BoundedStage 2 N := Sigma.mk d
  let S : Set (T d) := Mk ⁻¹' (boundedPoint '' boundedOrbit ab N)
  have hpst : StablePlane b (windowDimension_le d) D p := by
    unfold StablePlane
    rw [hp]
    exact latticeSubspace_stable _ _ L.val
  let q : T d := ⟨p, hpst⟩
  have hEq : boundedPoint L = Mk q := boundedPoint_eq_of_subspace_eq hp
  have hB : Continuous (boundedPoint (r := 2) (N := N)) := continuous_induced_dom
  have hq : Mk q ∈ closure (boundedPoint '' boundedOrbit ab N) :=
    hEq ▸ image_closure_subset_closure_image hB ⟨L, hL, rfl⟩
  have hDim : ∀ B ∈ boundedOrbit ab N, (boundedPoint B).1 = occupiedDimension ab N hN := by
    intro B hB
    have he := occupied_of_mem_boundedOrbit hAction hB
    have hd := occupiedDimension_occupied ab N hN
    apply Fin.ext
    unfold Occupied at he hd
    omega
  have hMk : Topology.IsClosedEmbedding Mk :=
    @Topology.IsClosedEmbedding.sigmaMk _ T (fun e ↦ stablePointsTopology b (windowDimension_le e) D) d
  have hd : d = occupiedDimension ab N hN := by
    by_contra hneq
    have hs : boundedPoint '' boundedOrbit ab N ⊆
        Set.range (Sigma.mk (β := T) (occupiedDimension ab N hN)) := by
      rintro _ ⟨B, hB', rfl⟩
      have hde := hDim B hB'
      generalize hP : boundedPoint B = P at hde ⊢
      obtain ⟨e, r⟩ := P
      change e = occupiedDimension ab N hN at hde
      subst e
      exact ⟨r, rfl⟩
    have hclosed : IsClosed (Set.range (Sigma.mk (β := T) (occupiedDimension ab N hN))) :=
      (@Topology.IsClosedEmbedding.sigmaMk _ T
        (fun e ↦ stablePointsTopology b (windowDimension_le e) D) _).isClosed_range
    obtain ⟨p', hp'⟩ := closure_minimal hs hclosed hq
    exact hneq (congrArg Sigma.fst hp').symm
  have hs : boundedPoint '' boundedOrbit ab N ⊆ Set.range Mk := by
    rintro _ ⟨B, hB', rfl⟩
    have hde := (hDim B hB').trans hd.symm
    generalize hP : boundedPoint B = P at hde ⊢
    obtain ⟨e, r⟩ := P
    change e = d at hde
    subst e
    exact ⟨r, rfl⟩
  have himage : Mk '' S = boundedPoint '' boundedOrbit ab N :=
    Set.image_preimage_eq_of_subset hs
  have hclosure : q ∈ closure S := by
    have hh : Mk q ∈ Mk '' closure S := by rw [← hMk.closure_image_eq, himage]; exact hq
    obtain ⟨q', hq', he⟩ := hh
    exact (hMk.injective he) ▸ hq'
  let f : T d → (BoundedGrassmannian N d).left := fun x ↦ pointLocation x.val
  have hf : Continuous f := (continuous_pointLocation_grassmannian b (windowDimension_le d)).comp
    continuous_subtype_val
  have hmem : f q ∈ closure (f '' S) := image_closure_subset_closure_image hf ⟨q, hclosure, rfl⟩
  apply closure_mono _ hmem
  rintro _ ⟨q', hq', rfl⟩
  obtain ⟨B, hB', hEq'⟩ := (show Mk q' ∈ boundedPoint '' boundedOrbit ab N from hq')
  have hsub : windowStageSubspace (Mk q') = boundedSubspace B := by
    rw [← hEq']
    exact windowStagePoint_subspace _ _ _
  exact ⟨q'.val, ⟨B.val, hB', hsub⟩, rfl⟩

private theorem difference_cast (ab : DominantPair) :
    (difference ab : ℤ) = ab.val.1 - ab.val.2 :=
  Int.toNat_of_nonneg (sub_nonneg.mpr ab.property)

private theorem pair_window_end (ab : DominantPair) :
    ab.val.2 + (difference ab : ℤ) = ab.val.1 := by
  rw [difference_cast]
  omega

private def minimalDimension (ab : DominantPair) :
    WindowDimension 2 ab.val.2 (difference ab) :=
  ⟨difference ab, by
    rw [Module.finrank_eq_card_basis (windowBasis 2 ab.val.2 (difference ab)),
      Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    omega⟩

private def bounded_of_minimal (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (L : WindowLattice 2 ab.val.2 (difference ab)) : BoundedLattice 2 N :=
  ⟨L.val, by
    have ha : ab.val.1 ≤ (N : ℤ) := by simpa [pairCoweight] using (hN 0).2
    have hb : -(N : ℤ) ≤ ab.val.2 := by simpa [pairCoweight] using (hN 1).1
    let U : GL2Lattice := L.val
    have hl : (scalarLattice 2 (ab.val.2 + (difference ab : ℤ))).val ≤ U.val := L.property.1
    rw [pair_window_end] at hl
    exact ⟨(diagonalLattice_le fun _ ↦ ha).trans hl,
      L.property.2.trans (diagonalLattice_le fun _ ↦ hb)⟩⟩

set_option maxHeartbeats 1000000 in
private theorem minimalStability_inclusion (hInclusions : WindowInclusions)
    (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) :
    ∃ j : windowStableScheme 2 ab.val.2 (difference ab) (minimalDimension ab) ⟶
        boundedStability N (occupiedDimension ab N hN),
      IsClosedImmersion j.left ∧
      ∀ (L : WindowLattice 2 ab.val.2 (difference ab))
        (q : Points (windowStableScheme 2 ab.val.2 (difference ab) (minimalDimension ab)) complexAlgebra),
        windowSchemeSubspace q = latticeSubspace ab.val.2 (difference ab) L.val →
        windowSchemeSubspace (q ≫ j) = boundedSubspace (bounded_of_minimal ab N hN L) := by
  have ha : ab.val.1 ≤ (N : ℤ) := by simpa [pairCoweight] using (hN 0).2
  have hb : -(N : ℤ) ≤ ab.val.2 := by simpa [pairCoweight] using (hN 1).1
  obtain ⟨d', hd', j, hj, hc⟩ := hInclusions 2 ab.val.2 (-(N : ℤ)) (difference ab)
    (2 * N) hb (by rw [boundedExponent, pair_window_end]; exact ha) (minimalDimension ab)
  rw [boundedExponent, pair_window_end] at hd'
  have hD := occupiedDimension_occupied ab N hN
  unfold Occupied at hD
  have he : d' = occupiedDimension ab N hN := by
    apply Fin.ext
    change d'.val = difference ab + 2 * ((N : ℤ) - ab.val.1).toNat at hd'
    have hd := difference_cast ab
    omega
  subst d'
  refine ⟨j, hj, ?_⟩
  intro L q hq
  exact hc L q hq

private theorem point_factors_closed {X Y : SchemeOver ℂ} (j : X ⟶ Y) [IsClosedImmersion j.left]
    (p : Points Y complexAlgebra) (hp : pointLocation p ∈ Set.range j.left) :
    ∃ q : Points X complexAlgebra, q ≫ j = p := by
  have : IsReduced ((testSpec ℂ).obj (Opposite.op complexAlgebra)).left := by
    change IsReduced (Spec (CommRingCat.of ℂ))
    infer_instance
  have hker : j.left.ker ≤ p.left.ker := by
    rw [LatticeModels.reduced_ker_eq p.left, pointLocation_range,
      ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal, TopologicalSpace.Closeds.closure_le]
    exact Set.singleton_subset_iff.mpr (j.left.range_subset_ker_support hp)
  let f := IsClosedImmersion.lift j.left p.left hker
  have hf : f ≫ j.left = p.left := IsClosedImmersion.lift_fac j.left p.left hker
  exact ⟨Over.homMk f (by rw [← Over.w j, ← Category.assoc, hf, Over.w]),
    Over.OverMorphism.ext hf⟩

private theorem orbit_point_of_minimal (hAction : GLJetAction) (hScheme : WindowSchemeComparison)
    (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (j : windowStableScheme 2 ab.val.2 (difference ab) (minimalDimension ab) ⟶
      boundedStability N (occupiedDimension ab N hN))
    (hc : ∀ (L : WindowLattice 2 ab.val.2 (difference ab))
      (q : Points (windowStableScheme 2 ab.val.2 (difference ab) (minimalDimension ab)) complexAlgebra),
      windowSchemeSubspace q = latticeSubspace ab.val.2 (difference ab) L.val →
      windowSchemeSubspace (q ≫ j) = boundedSubspace (bounded_of_minimal ab N hN L))
    (p : WindowPoints 2 (-(N : ℤ)) (2 * N) (occupiedDimension ab N hN))
    (hp : p ∈ schubertOrbitPoints ab N hN (occupiedDimension ab N hN)) :
    ∃ q : Points (windowStableScheme 2 ab.val.2 (difference ab) (minimalDimension ab)) complexAlgebra,
      q ≫ j ≫ boundedStabilityInclusion N (occupiedDimension ab N hN) = p := by
  obtain ⟨L, hL, hpL⟩ := hp
  let d := minimalDimension ab
  let m := difference ab
  obtain ⟨hl, hu⟩ := orbit_endpoints hL
  let B : WindowLattice 2 ab.val.2 m :=
    ⟨L, (hl _).mpr (by rw [pair_window_end]), (hu _).mpr le_rfl⟩
  have hrank := orbit_window_finrank hAction hL ab.val.2 m le_rfl (by rw [pair_window_end])
  rw [pair_window_end] at hrank
  have hdim : Module.finrank ℂ (latticeSubspace ab.val.2 m B.val) = d.val := by
    change Module.finrank ℂ (latticeSubspace ab.val.2 m L) = m
    have hd := difference_cast ab
    dsimp [m] at *
    omega
  obtain ⟨_, _, e, he⟩ := hScheme 2 ab.val.2 m d
  let z : {L : WindowLattice 2 ab.val.2 m // Module.finrank ℂ
      (latticeSubspace ab.val.2 m L.val) = d.val} := ⟨B, hdim⟩
  let q := e.symm z
  have hq : windowSchemeSubspace q = latticeSubspace ab.val.2 m B.val := by
    have h := he q
    rw [show e q = z from e.apply_symm_apply z] at h
    exact h
  refine ⟨q, ?_⟩
  apply grassmannianSubspace_injective (windowBasis 2 (-(N : ℤ)) (2 * N))
    (windowDimension_le (occupiedDimension ab N hN))
  rw [← Category.assoc]
  exact (hc B q hq).trans hpL.symm

set_option maxHeartbeats 800000 in
private theorem zariski_bounded_upper (hInclusions : WindowInclusions)
    (hScheme : WindowSchemeComparison) (hAction : GLJetAction) (hExhaustion : LatticeExhaustion)
    (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (d : WindowDimension 2 (-(N : ℤ)) (2 * N)) (p : WindowPoints 2 (-(N : ℤ)) (2 * N) d)
    (hp : pointLocation p ∈ closure (pointLocation '' schubertOrbitPoints ab N hN d)) :
    ∃ L ∈ schubertLatticeSet ab N,
      grassmannianSubspace (windowBasis 2 (-(N : ℤ)) (2 * N)) (windowDimension_le d) p =
        boundedSubspace L := by
  have hpt : (schubertOrbitPoints ab N hN d).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Set.image_empty, closure_empty] at hp
    exact hp
  have hd := (schubertOrbitPoints_nonempty_iff hAction ab N hN d).mp hpt
  have hOcc := occupiedDimension_occupied ab N hN
  have hEq : d = occupiedDimension ab N hN := by
    apply Fin.ext
    unfold Occupied at hd hOcc
    omega
  subst d
  let d := occupiedDimension ab N hN
  obtain ⟨j, hj, hc⟩ := minimalStability_inclusion hInclusions ab N hN
  let f := j ≫ boundedStabilityInclusion N d
  have : IsClosedImmersion (boundedStabilityInclusion N d).left := by
    change IsClosedImmersion (reducedClosureIdeal _ _).subschemeι
    infer_instance
  have hf : IsClosedImmersion f.left := by
    change IsClosedImmersion (j.left ≫ (boundedStabilityInclusion N d).left)
    infer_instance
  have hsub : pointLocation '' schubertOrbitPoints ab N hN d ⊆ Set.range f.left := by
    rintro _ ⟨p', hp', rfl⟩
    obtain ⟨q, hq⟩ := orbit_point_of_minimal hAction hScheme ab N hN j hc p' hp'
    refine ⟨pointLocation q, ?_⟩
    exact (pointLocation_comp q f).symm.trans (congrArg pointLocation hq)
  have hp' : pointLocation p ∈ Set.range f.left :=
    closure_minimal hsub f.left.isClosedEmbedding.isClosed_range hp
  obtain ⟨q, hq⟩ := point_factors_closed f p hp'
  obtain ⟨_, _, e, he⟩ := hScheme 2 ab.val.2 (difference ab) (minimalDimension ab)
  let L := (e q).val
  let B := bounded_of_minimal ab N hN L
  have hBsub : grassmannianSubspace (windowBasis 2 (-(N : ℤ)) (2 * N))
      (windowDimension_le d) p = boundedSubspace B := by
    have h := hc L q (he q)
    change grassmannianSubspace (windowBasis 2 (-(N : ℤ)) (2 * N))
      (windowDimension_le d) ((q ≫ j) ≫ boundedStabilityInclusion N d) = _ at h
    rw [Category.assoc, hq] at h
    exact h
  refine ⟨B, (schubertLatticeSet_iff hAction hExhaustion ab N B).mpr ⟨?_, ?_⟩, hBsub⟩
  · let U : GL2Lattice := L.val
    have hl : (scalarLattice 2 (ab.val.2 + (difference ab : ℤ))).val ≤ U.val := L.property.1
    rw [pair_window_end] at hl
    exact ⟨hl, L.property.2⟩
  · have hRank := grassmannianSubspace_finrank (windowBasis 2 (-(N : ℤ)) (2 * N))
      (windowDimension_le d) p
    rw [hBsub] at hRank
    have hdim : (boundedPoint B).1 = d := Fin.ext hRank
    exact hdim.symm ▸ hOcc

private theorem closed_occupied (ab : DominantPair) (N : ℕ)
    (hN : OrbitBound ab N) :
    IsClosed {B : BoundedLattice 2 N | Occupied ab N (boundedPoint B).1} := by
  let c : ℤ := -(N : ℤ)
  let m := 2 * N
  let b := windowBasis 2 c m
  let D := windowOperator 2 c m
  let T (e : WindowDimension 2 c m) := StablePoints b (windowDimension_le e) D
  let d := occupiedDimension ab N hN
  let Mk : T d → BoundedStage 2 N := Sigma.mk d
  have hd : Occupied ab N d := occupiedDimension_occupied ab N hN
  have hset : {B : BoundedLattice 2 N | Occupied ab N (boundedPoint B).1} =
      boundedPoint ⁻¹' Set.range Mk := by
    ext B
    change Occupied ab N (boundedPoint B).1 ↔ boundedPoint B ∈ Set.range Mk
    generalize hP : boundedPoint B = P
    obtain ⟨e, p⟩ := P
    change Occupied ab N e ↔ Sigma.mk e p ∈ Set.range Mk
    constructor
    · intro he
      have heq : e = d := by
        apply Fin.ext
        unfold Occupied at he hd
        omega
      subst e
      exact ⟨p, rfl⟩
    · rintro ⟨q, hq⟩
      have heq : d = e := congrArg Sigma.fst hq
      exact heq ▸ hd
  have he : Topology.IsClosedEmbedding Mk :=
    @Topology.IsClosedEmbedding.sigmaMk _ T (fun e ↦ stablePointsTopology b (windowDimension_le e) D) d
  rw [hset]
  exact he.isClosed_range.preimage continuous_induced_dom

private theorem bounded_analytic_closure (hAdjacent : AdjacentSpecialization)
    (hStable : WindowPositiveStable) (hAction : GLJetAction) (hExhaustion : LatticeExhaustion)
    (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) :
    closure (boundedOrbit ab N) = schubertLatticeSet ab N := by
  apply le_antisymm
  · have hClosed : IsClosed (schubertLatticeSet ab N) := by
      have H : schubertLatticeSet ab N =
          {B | Between ab.val.1 ab.val.2 B.val} ∩ {B | Occupied ab N (boundedPoint B).1} :=
        Set.ext fun B ↦ schubertLatticeSet_iff hAction hExhaustion ab N B
      rw [H]
      exact (closed_bounded_incidence ab N hN).inter (closed_occupied ab N hN)
    apply closure_minimal _ hClosed
    intro B hB
    exact ⟨ab, ⟨0, by simpa using ab.property, by simp, by simp⟩, hB⟩
  · rintro B ⟨cd, hcd, hB⟩
    exact below_subset_analyticClosure hAdjacent hStable hAction hN hcd hB

theorem boundedSchubertComparison : BoundedSchubertComparison := by
  intro ab N hN
  let hAction := BoundedLattices.glJetAction
  let hExhaustion := BoundedLattices.latticeExhaustion
  let hInclusions := BoundedLattices.windowInclusions
  let hStable := BoundedLattices.windowPositiveStable
  let hScheme := BoundedLattices.windowSchemeComparison
  have hOcc := occupiedDimension_occupied ab N hN
  have hClosure := bounded_analytic_closure adjacentSpecialization
    hStable hAction hExhaustion ab N hN
  refine ⟨hOcc, schubertOrbitPoints_nonempty_iff hAction ab N hN,
    fun _ h ↦ closureLattices_bounded hN h, schubertLatticeSet_iff hAction hExhaustion ab N,
    closed_bounded_incidence ab N hN, hClosure, ?_⟩
  intro d p
  refine ⟨zariski_bounded_upper hInclusions hScheme hAction hExhaustion ab N hN d p, ?_⟩
  rintro ⟨B, hB, he⟩
  exact mem_zariski_closure_of_mem_analytic hAction ab hN d B (hClosure.symm ▸ hB) p he

private theorem reducedClosure_dense_points {X : SchemeOver ℂ} (S : Set (Points X complexAlgebra)) :
    Dense (Set.range (pointLocation :
      Points (reducedClosureScheme X S) complexAlgebra → (reducedClosureScheme X S).left)) := by
  let i := reducedClosureInclusion X S
  have hi : IsClosedImmersion i.left := by
    change IsClosedImmersion (reducedClosureIdeal X S).subschemeι
    infer_instance
  rw [dense_iff_closure_eq]
  apply Set.image_injective.mpr i.left.isClosedEmbedding.injective
  rw [← i.left.isClosedEmbedding.closure_image_eq, Set.image_univ, range_reducedClosureInclusion]
  apply le_antisymm
  · apply closure_minimal _ isClosed_closure
    rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
    rw [← pointLocation_comp]
    exact (LatticeModels.pointLocation_in_closure_iff S _).mpr ⟨q, rfl⟩
  · apply closure_mono
    rintro _ ⟨p, hp, rfl⟩
    have hp' : pointLocation p ∈ Set.range i.left :=
      (range_reducedClosureInclusion S).symm ▸ subset_closure (Set.mem_image_of_mem pointLocation hp)
    obtain ⟨q, hq⟩ := point_factors_closed i p hp'
    exact ⟨pointLocation q, ⟨q, rfl⟩, (pointLocation_comp q i).symm.trans (congrArg pointLocation hq)⟩

set_option maxHeartbeats 900000 in
private theorem minimalWindowComparison_of_comparison (hComparison : BoundedSchubertComparison)
    (hInclusions : WindowInclusions) (hScheme : WindowSchemeComparison)
    (hAction : GLJetAction) : MinimalWindowComparison := by
  intro ab N hN
  let dm := minimalDimension ab
  let d := occupiedDimension ab N hN
  obtain ⟨j, hj, hc⟩ := minimalStability_inclusion hInclusions ab N hN
  let f := j ≫ boundedStabilityInclusion N d
  let k := schubertToGrassmannian ab N hN d
  have hw : IsClosedImmersion (boundedStabilityInclusion N d).left := by
    change IsClosedImmersion (reducedClosureIdeal _ _).subschemeι
    infer_instance
  have hf : IsClosedImmersion f.left := by
    change IsClosedImmersion (j.left ≫ (boundedStabilityInclusion N d).left)
    infer_instance
  have hk : IsClosedImmersion k.left := by
    change IsClosedImmersion (reducedClosureIdeal _ _).subschemeι
    infer_instance
  have hrK : Set.range k.left = closure (pointLocation '' schubertOrbitPoints ab N hN d) :=
    range_reducedClosureInclusion _
  obtain ⟨hOcc, _, _, hLattice, _, _, hZar⟩ := hComparison ab N hN
  have hfsub : Set.range k.left ⊆ Set.range f.left := by
    rw [hrK]
    apply closure_minimal _ f.left.isClosedEmbedding.isClosed_range
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨q, hq⟩ := orbit_point_of_minimal hAction hScheme ab N hN j hc p hp
    exact ⟨pointLocation q, (pointLocation_comp q f).symm.trans (congrArg pointLocation hq)⟩
  obtain ⟨hRed, _, e, he⟩ := hScheme 2 ab.val.2 (difference ab) dm
  have hfPoints (q : Points (windowStableScheme 2 ab.val.2 (difference ab) dm) complexAlgebra) :
      f.left (pointLocation q) ∈ Set.range k.left := by
    let p := q ≫ f
    let W := (e q).val
    let B := bounded_of_minimal ab N hN W
    have hsub : grassmannianSubspace (windowBasis 2 (-(N : ℤ)) (2 * N))
        (windowDimension_le d) p = boundedSubspace B := by
      change grassmannianSubspace (windowBasis 2 (-(N : ℤ)) (2 * N)) (windowDimension_le d)
        (q ≫ j ≫ boundedStabilityInclusion N d) = _
      rw [← Category.assoc]
      exact hc W q (he q)
    have hBw : Between ab.val.1 ab.val.2 B.val := by
      change Between ab.val.1 ab.val.2 W.val
      let L : GL2Lattice := W.val
      have hl : (scalarLattice 2 (ab.val.2 + (difference ab : ℤ))).val ≤ L.val := W.property.1
      rw [pair_window_end] at hl
      exact ⟨hl, W.property.2⟩
    have hd := grassmannianSubspace_finrank (windowBasis 2 (-(N : ℤ)) (2 * N))
      (windowDimension_le d) p
    rw [hsub] at hd
    have hdim : (boundedPoint B).1 = d := Fin.ext hd
    have hBL : B ∈ schubertLatticeSet ab N := (hLattice B).mpr ⟨hBw, hdim.symm ▸ hOcc⟩
    rw [← pointLocation_comp, hrK]
    exact (hZar d p).mpr ⟨B, hBL, hsub⟩
  have hksub : Set.range f.left ⊆ Set.range k.left := by
    have hdense : Dense (Set.range (pointLocation : Points (windowStableScheme 2 ab.val.2
        (difference ab) dm) complexAlgebra → (windowStableScheme 2 ab.val.2 (difference ab) dm).left)) :=
      reducedClosure_dense_points _
    have hPoints : Set.range (pointLocation : Points (windowStableScheme 2 ab.val.2
        (difference ab) dm) complexAlgebra → (windowStableScheme 2 ab.val.2 (difference ab) dm).left) ⊆
        f.left ⁻¹' Set.range k.left := by
      rintro _ ⟨q, rfl⟩
      exact hfPoints q
    have hc' := closure_minimal hPoints
      (hk.isClosedEmbedding.isClosed_range.preimage f.left.continuous)
    rw [hdense.closure_eq] at hc'
    rintro _ ⟨x, rfl⟩
    exact hc' (Set.mem_univ x)
  have heq : Set.range f.left = Set.range k.left := le_antisymm hksub hfsub
  have hKred : IsReduced (occupiedSchubert ab N hN).left := LatticeModels.reducedClosure_reduced _ _
  have hker : f.left.ker = k.left.ker := by
    rw [LatticeModels.reduced_ker_eq f.left, LatticeModels.reduced_ker_eq k.left, heq]
  let u := IsClosedImmersion.lift k.left f.left hker.ge
  have hu : u ≫ k.left = f.left := IsClosedImmersion.lift_fac k.left f.left _
  let g : windowStableScheme 2 ab.val.2 (difference ab) dm ⟶ occupiedSchubert ab N hN :=
    Over.homMk u (by rw [← Over.w k, ← Category.assoc, hu, Over.w])
  have hg : g ≫ k = f := Over.OverMorphism.ext hu
  have : IsIso ((Over.forget _).map g) :=
    IsClosedImmersion.isIso_of_ker_eq f.left k.left u hu hker
  have : IsIso g := isIso_of_reflects_iso g (Over.forget _)
  refine ⟨dm, rfl, asIso g, ?_⟩
  intro L q hq
  change grassmannianSubspace (windowBasis 2 (-(N : ℤ)) (2 * N))
    (windowDimension_le d) (q ≫ g ≫ k) = _
  rw [hg]
  change grassmannianSubspace (windowBasis 2 (-(N : ℤ)) (2 * N))
    (windowDimension_le d) (q ≫ j ≫ boundedStabilityInclusion N d) = _
  rw [← Category.assoc]
  exact hc L q hq

theorem minimalWindowComparison : MinimalWindowComparison :=
  minimalWindowComparison_of_comparison boundedSchubertComparison BoundedLattices.windowInclusions
    BoundedLattices.windowSchemeComparison BoundedLattices.glJetAction


section PointComparisons

private theorem schubertToGrassmannian_closed (ab : DominantPair) (N : ℕ)
    (hN : OrbitBound ab N) (d : WindowDimension 2 (-(N : ℤ)) (2 * N)) :
    IsClosedImmersion (schubertToGrassmannian ab N hN d).left := by
  change IsClosedImmersion (reducedClosureIdeal _ _).subschemeι
  infer_instance

private theorem orbitToSchubert_open (ab : DominantPair) (N : ℕ)
    (hN : OrbitBound ab N) : IsOpenImmersion (orbitToSchubert ab N hN).left := by
  change IsOpenImmersion (orbitOpen ab N hN).ι
  infer_instance

private theorem point_factors_open {X U : SchemeOver ℂ} (i : U ⟶ X)
    [IsOpenImmersion i.left] (p : Points X complexAlgebra)
    (hp : pointLocation p ∈ Set.range i.left) :
    ∃ q : Points U complexAlgebra, q ≫ i = p := by
  have hs : Set.range p.left ⊆ Set.range i.left := by
    rw [pointLocation_range, Set.singleton_subset_iff]
    exact hp
  let f := IsOpenImmersion.lift i.left p.left hs
  have hf : f ≫ i.left = p.left := IsOpenImmersion.lift_fac i.left p.left hs
  exact ⟨Over.homMk f (by rw [← Over.w i, ← Category.assoc, hf, Over.w]),
    Over.OverMorphism.ext hf⟩

private theorem eq_occupiedDimension {ab : DominantPair} {N : ℕ} (hN : OrbitBound ab N)
    {d : WindowDimension 2 (-(N : ℤ)) (2 * N)} (hd : Occupied ab N d) :
    d = occupiedDimension ab N hN := by
  have hd' := occupiedDimension_occupied ab N hN
  apply Fin.ext
  unfold Occupied at hd hd'
  omega

private theorem schubert_pointRange (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (d : WindowDimension 2 (-(N : ℤ)) (2 * N))
    (p : WindowPoints 2 (-(N : ℤ)) (2 * N) d) :
    (∃ q : Points (schubertScheme ab N hN d) complexAlgebra,
      q ≫ schubertToGrassmannian ab N hN d = p) ↔
      ∃ B ∈ schubertLatticeSet ab N,
        grassmannianSubspace (windowBasis 2 (-(N : ℤ)) (2 * N)) (windowDimension_le d) p =
          boundedSubspace B :=
  (LatticeModels.pointLocation_in_closure_iff (schubertOrbitPoints ab N hN d) p).symm.trans
    ((boundedSchubertComparison ab N hN).2.2.2.2.2.2 d p)

private theorem schubert_point_homeomorph (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) :
    ∃ E : OccupiedSchubertPoints ab N hN ≃ₜ schubertLatticeSet ab N,
      ∀ p, schubertPointSubspace p = boundedSubspace (E p).val := by
  let d := occupiedDimension ab N hN
  let f := schubertToGrassmannian ab N hN d
  have : IsClosedImmersion f.left := schubertToGrassmannian_closed ab N hN d
  refine SchubertAnalyticFlagTransport.boundedPointTransport N d (schubertLatticeSet ab N)
    (occupiedSchubert ab N hN) f inferInstance (BoundedLattices.boundedStageComparison 2 N).1.1
    ?_ ?_
  · intro B hB
    exact eq_occupiedDimension hN (((boundedSchubertComparison ab N hN).2.2.2.1 B).mp hB).2
  · ext p
    exact schubert_pointRange ab N hN d p

private theorem boundedSubspace_injective (N : ℕ) :
    Function.Injective (boundedSubspace (r := 2) (N := N)) := by
  intro B B' hB
  let p := boundedPoint B'
  have hp : windowStageSubspace ⟨p.1, p.2⟩ = boundedSubspace B := by
    change windowStageSubspace (boundedPoint B') = boundedSubspace B
    exact (windowStagePoint_subspace _ _ B'.val).trans hB.symm
  exact (BoundedLattices.boundedStageComparison 2 N).1.1 (boundedPoint_eq_of_subspace_eq hp)

private theorem below_adjacent_of_ne {ab cd : DominantPair} (h : 2 ≤ difference ab)
    (hc : Below cd ab) (hd : cd ≠ ab) :
    Below cd (adjacentPair ab h) := by
  obtain ⟨j, hj, ha, hb⟩ := hc
  have hj₀ : j ≠ 0 := by
    intro h'
    subst j
    exact hd (Subtype.ext (Prod.ext (by simpa using ha) (by simpa using hb)))
  refine ⟨j - 1, ?_, ?_, ?_⟩
  · change 2 * ((j - 1 : ℕ) : ℤ) ≤ (ab.val.1 - 1) - (ab.val.2 + 1)
    omega
  · change cd.val.1 = ab.val.1 - 1 - ((j - 1 : ℕ) : ℤ)
    omega
  · change cd.val.2 = ab.val.2 + 1 + ((j - 1 : ℕ) : ℤ)
    omega

private theorem orbit_iff_not_inner {ab : DominantPair} (h : 2 ≤ difference ab)
    {L : GL2Lattice} (hL : L ∈ closureLattices ab) :
    L ∈ gl2Orbit ab ↔ L ∉ closureLattices (adjacentPair ab h) := by
  constructor
  · rintro hO ⟨cd, hc, hC⟩
    have he := orbit_label_unique hC hO
    subst cd
    have hle := ((below_iff ab (adjacentPair ab h)).mp hc).2.1
    change ab.val.1 ≤ ab.val.1 - 1 at hle
    omega
  · intro hNot
    obtain ⟨cd, hc, hC⟩ := hL
    by_cases he : cd = ab
    · exact he ▸ hC
    · exact False.elim (hNot ⟨cd, below_adjacent_of_ne h hc he, hC⟩)

private theorem orbit_mem_of_small {ab : DominantPair} (h : ¬2 ≤ difference ab)
    {L : GL2Lattice} (hL : L ∈ closureLattices ab) : L ∈ gl2Orbit ab := by
  obtain ⟨cd, ⟨j, hj, ha, hb⟩, hC⟩ := hL
  have hz : j = 0 := by
    have hd := difference_cast ab
    omega
  subst j
  have he : cd = ab := Subtype.ext (Prod.ext (by simpa using ha) (by simpa using hb))
  exact he ▸ hC

private theorem pointLocation_orbitOpen_iff (ab : DominantPair) (N : ℕ)
    (hN : OrbitBound ab N) (B : schubertLatticeSet ab N)
    (q : OccupiedSchubertPoints ab N hN) (hq : schubertPointSubspace q = boundedSubspace B.val) :
    pointLocation q ∈ orbitOpen ab N hN ↔ B.val ∈ boundedOrbit ab N := by
  by_cases h : 2 ≤ difference ab
  · simp only [orbitOpen, dite_eq_left h]
    have hbelow : Below (adjacentPair ab h) ab :=
      ⟨1, by have hh := difference_cast ab; omega, rfl, rfl⟩
    have hBound := orbitBound_of_below hbelow hN
    let d := occupiedDimension ab N hN
    let p := q ≫ schubertToGrassmannian ab N hN d
    change pointLocation p ∉ closure (pointLocation '' schubertOrbitPoints (adjacentPair ab h)
      N hBound d) ↔ _
    have hCmp := (boundedSchubertComparison (adjacentPair ab h) N hBound).2.2.2.2.2.2 d p
    have hClosure : pointLocation p ∈ closure (pointLocation '' schubertOrbitPoints
        (adjacentPair ab h) N hBound d) ↔ B.val ∈ schubertLatticeSet (adjacentPair ab h) N := by
      rw [hCmp]
      constructor
      · rintro ⟨B', hB', hsub⟩
        have he := boundedSubspace_injective N (hq.symm.trans hsub)
        exact he.symm ▸ hB'
      · exact fun hB ↦ ⟨B.val, hB, hq⟩
    exact (not_congr hClosure).trans (orbit_iff_not_inner h B.property).symm
  · simp only [orbitOpen, dite_eq_right h]
    exact ⟨fun _ ↦ orbit_mem_of_small h B.property, fun _ ↦ by trivial⟩

set_option maxHeartbeats 650000 in
theorem orbitPointComparison : OrbitPointComparison := by
  intro ab N hN
  let d := occupiedDimension ab N hN
  let i := orbitToSchubert ab N hN
  let f := schubertToGrassmannian ab N hN d
  have : IsOpenImmersion i.left := orbitToSchubert_open ab N hN
  have : IsClosedImmersion f.left := schubertToGrassmannian_closed ab N hN d
  have hImm : IsImmersion (orbitToGrassmannian ab N hN).left := by
    change IsImmersion (i.left ≫ f.left)
    infer_instance
  obtain ⟨e, he⟩ := schubert_point_homeomorph ab N hN
  refine SchubertAnalyticFlagTransport.boundedPointTransport N d (boundedOrbit ab N)
    (orbitScheme ab N hN) (orbitToGrassmannian ab N hN) hImm
    (BoundedLattices.boundedStageComparison 2 N).1.1 ?_ ?_
  · intro B hB
    exact eq_occupiedDimension hN (occupied_of_mem_boundedOrbit BoundedLattices.glJetAction hB)
  · ext p
    constructor
    · rintro ⟨q, rfl⟩
      let r := q ≫ i
      have hr : pointLocation r ∈ orbitOpen ab N hN := (pointLocation q).property
      have hO := (pointLocation_orbitOpen_iff ab N hN (e r) r (he r)).mp hr
      refine ⟨(e r).val, hO, ?_⟩
      change grassmannianSubspace (windowBasis 2 (-(N : ℤ)) (2 * N))
        (windowDimension_le d) (q ≫ i ≫ f) = _
      rw [← Category.assoc]
      exact he r
    · rintro ⟨B, hB, hsub⟩
      have hBC : B ∈ schubertLatticeSet ab N :=
        ⟨ab, (below_iff ab ab).mpr ⟨rfl, le_rfl, le_rfl⟩, hB⟩
      obtain ⟨q, hq⟩ := (schubert_pointRange ab N hN d p).mpr ⟨B, hBC, hsub⟩
      have hqsub : schubertPointSubspace q = boundedSubspace B := by
        change grassmannianSubspace (windowBasis 2 (-(N : ℤ)) (2 * N))
          (windowDimension_le d) (q ≫ f) = _
        rw [hq]
        exact hsub
      have hloc := (pointLocation_orbitOpen_iff ab N hN ⟨B, hBC⟩ q hqsub).mpr hB
      have hloc' : pointLocation q ∈ Set.range i.left := by
        change pointLocation q ∈ Set.range (orbitOpen ab N hN).ι
        rw [Scheme.Opens.range_ι]
        exact hloc
      obtain ⟨q', hq'⟩ := point_factors_open i q hloc'
      exact ⟨q', by change q' ≫ i ≫ f = p; rw [← Category.assoc, hq', hq]⟩

end PointComparisons

section StratumInclusions

private theorem reducedClosure_inclusion_of_support {X : SchemeOver ℂ}
    (S T : Set (Points X complexAlgebra))
    (h : closure (pointLocation '' S) ⊆ closure (pointLocation '' T)) :
    ∃ j : reducedClosureScheme X S ⟶ reducedClosureScheme X T,
      IsClosedImmersion j.left ∧ j ≫ reducedClosureInclusion X T = reducedClosureInclusion X S := by
  let I := reducedClosureIdeal X T
  let J := reducedClosureIdeal X S
  have hIJ : I ≤ J := Scheme.IdealSheafData.vanishingIdeal_antimono h
  let f := Scheme.IdealSheafData.inclusion hIJ
  have hf : f ≫ I.subschemeι = J.subschemeι :=
    Scheme.IdealSheafData.inclusion_subschemeι hIJ
  let j : reducedClosureScheme X S ⟶ reducedClosureScheme X T :=
    Over.homMk f (by
      change f ≫ (I.subschemeι ≫ X.hom) = J.subschemeι ≫ X.hom
      rw [← Category.assoc, hf])
  exact ⟨j, LatticeModels.inclusion_closed hIJ, Over.OverMorphism.ext hf⟩

private theorem lowerSchubert_support_subset (ab cd : DominantPair) (N : ℕ)
    (hN : OrbitBound ab N) (hN' : OrbitBound cd N) (h : Below cd ab)
    (d : WindowDimension 2 (-(N : ℤ)) (2 * N)) :
    closure (pointLocation '' schubertOrbitPoints cd N hN' d) ⊆
      closure (pointLocation '' schubertOrbitPoints ab N hN d) := by
  apply closure_minimal _ isClosed_closure
  rintro _ ⟨p, ⟨L, hL, hp⟩, rfl⟩
  let B : BoundedLattice 2 N := ⟨L, gl2Orbit_bounded cd hN' hL⟩
  exact ((boundedSchubertComparison ab N hN).2.2.2.2.2.2 d p).mpr ⟨B, ⟨cd, h, hL⟩, hp⟩

private theorem lowerSchubert_inclusionAt (ab cd : DominantPair) (N : ℕ)
    (hN : OrbitBound ab N) (hN' : OrbitBound cd N) (h : Below cd ab)
    (d d' : WindowDimension 2 (-(N : ℤ)) (2 * N)) (hd : d' = d) :
    ∃ j : schubertScheme cd N hN' d' ⟶ schubertScheme ab N hN d,
      IsClosedImmersion j.left ∧
      j ≫ schubertToGrassmannian ab N hN d =
        schubertToGrassmannian cd N hN' d' ≫ eqToHom (congrArg (BoundedGrassmannian N) hd) := by
  subst d'
  simp only [eqToHom_refl, Category.comp_id]
  exact reducedClosure_inclusion_of_support (schubertOrbitPoints cd N hN' d)
    (schubertOrbitPoints ab N hN d) (lowerSchubert_support_subset ab cd N hN hN' h d)

private theorem precompose_comm {C : Type*} [Category C] {U X Y G H : C}
    (i : U ⟶ X) (j : X ⟶ Y) (a : X ⟶ G) (b : Y ⟶ H) (t : G ⟶ H)
    (hc : j ≫ b = a ≫ t) : (i ≫ j) ≫ b = (i ≫ a) ≫ t := by
  rw [Category.assoc, hc, Category.assoc]

set_option maxHeartbeats 450000 in
private theorem lowerOrbit_analytic {ab cd : DominantPair} {N : ℕ}
    {hN : OrbitBound ab N} {hN' : OrbitBound cd N}
    (E : OccupiedSchubertPoints ab N hN ≃ₜ schubertLatticeSet ab N)
    (hE : ∀ p, schubertPointSubspace p = boundedSubspace (E p).val)
    (hd : occupiedDimension cd N hN' = occupiedDimension ab N hN)
    (j : occupiedSchubert cd N hN' ⟶ occupiedSchubert ab N hN)
    (hc : j ≫ schubertToGrassmannian ab N hN _ =
      schubertToGrassmannian cd N hN' _ ≫ eqToHom (congrArg (BoundedGrassmannian N) hd)) :
    Topology.IsEmbedding (fun q : OrbitPoints cd N hN' ↦
      (q ≫ orbitToSchubert cd N hN' ≫ j : OccupiedSchubertPoints ab N hN)) ∧
    Set.range (fun q : OrbitPoints cd N hN' ↦ E (q ≫ orbitToSchubert cd N hN' ≫ j)) =
      {L | L.val ∈ boundedOrbit cd N} := by
  obtain ⟨e, he⟩ := orbitPointComparison cd N hN'
  exact (SchubertAnalyticFlagTransport.boundedPointTransportCompatibility N _ _ hd
    (boundedOrbit cd N) (schubertLatticeSet ab N) (orbitScheme cd N hN')
    (occupiedSchubert ab N hN) (orbitToGrassmannian cd N hN')
    (schubertToGrassmannian ab N hN _) (orbitToSchubert cd N hN' ≫ j)
    (precompose_comm (orbitToSchubert cd N hN') j (schubertToGrassmannian cd N hN' _)
      (schubertToGrassmannian ab N hN _) (eqToHom (congrArg (BoundedGrassmannian N) hd)) hc)
    (BoundedLattices.boundedStageComparison 2 N).1.1
    e E he hE).2.2

private theorem occupiedDimension_of_below (ab cd : DominantPair) (N : ℕ)
    (hN : OrbitBound ab N) (hN' : OrbitBound cd N) (h : Below cd ab) :
    occupiedDimension cd N hN' = occupiedDimension ab N hN := by
  apply Fin.ext
  change (2 * (N : ℤ) - (cd.val.1 + cd.val.2)).toNat =
    (2 * (N : ℤ) - (ab.val.1 + ab.val.2)).toNat
  rw [((below_iff cd ab).mp h).1]

set_option maxHeartbeats 650000 in
private theorem schubert_attachment (ab cd : DominantPair) (N : ℕ)
    (hN : OrbitBound ab N) (hN' : OrbitBound cd N) (h : Below cd ab)
    (E : OccupiedSchubertPoints ab N hN ≃ₜ schubertLatticeSet ab N)
    (hE : ∀ p, schubertPointSubspace p = boundedSubspace (E p).val) :
    ∃ (hd : occupiedDimension cd N hN' = occupiedDimension ab N hN)
      (j : occupiedSchubert cd N hN' ⟶ occupiedSchubert ab N hN),
      IsClosedImmersion j.left ∧
      j ≫ schubertToGrassmannian ab N hN _ =
        schubertToGrassmannian cd N hN' _ ≫ eqToHom (congrArg (BoundedGrassmannian N) hd) ∧
      Topology.IsEmbedding (fun q : OrbitPoints cd N hN' ↦
        (q ≫ orbitToSchubert cd N hN' ≫ j : OccupiedSchubertPoints ab N hN)) ∧
      Set.range (fun q : OrbitPoints cd N hN' ↦ E (q ≫ orbitToSchubert cd N hN' ≫ j)) =
        {L | L.val ∈ boundedOrbit cd N} := by
  let hd := occupiedDimension_of_below ab cd N hN hN' h
  obtain ⟨j, hj, hc⟩ := lowerSchubert_inclusionAt ab cd N hN hN' h _ _ hd
  exact ⟨hd, j, hj, hc, lowerOrbit_analytic E hE hd j hc⟩

set_option maxHeartbeats 1000000 in
theorem schubertStratification : SchubertStratification := by
  unfold SchubertStratification
  intro ab N hN
  obtain ⟨E, hE⟩ := schubert_point_homeomorph ab N hN
  refine ⟨E, hE, ?_⟩
  intro cd hN' h
  exact schubert_attachment ab cd N hN hN' h E hE

end StratumInclusions

section NormalizedRows

open private mem_windowSubspace_iff windowRepresentative
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SchubertAnalyticFlagTransport

private theorem windowJets_representative {r m : ℕ} {b : ℤ} (x : Fin r → O) (i : Fin r) :
    windowJets r b m (windowRepresentative b m x) i = jetReduction m (x i) := by
  have h : windowJets r b m (windowRepresentative b m x) =
      windowReduction r b m (shiftedCoordinates r b x) := by
    simp only [windowRepresentative, windowJets, LatticeModelSpecs.quotientEquivOfKernel,
      LinearEquiv.trans_apply, Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk,
      LinearMap.quotKerEquivOfSurjective_apply_mk]
  rw [h]
  change jetReduction m ((shiftedCoordinates r b).symm (shiftedCoordinates r b x) i) = _
  rw [LinearEquiv.symm_apply_apply]

private theorem normalizedRow_eval {m : ℕ} (i : Fin 2) (z : JetRing m) (x : Fin 2 → O) :
    rowMap (normalizedRow i z) x = jetReduction m (x i) + z * jetReduction m (x i.rev) := by
  rw [rowMap_eval, Fin.sum_univ_two]
  fin_cases i <;> simp [normalizedRow, add_comm]

set_option maxHeartbeats 600000 in
private theorem latticeSubspace_chartKernel {m : ℕ} {b : ℤ} (L : GL2Lattice) (i : Fin 2)
    (z : Fin m → ℂ) (hL : L.val = chartKernel b i z) (w : Window 2 b m) :
    w ∈ latticeSubspace b m L ↔
      windowJets 2 b m w i + (jetCoefficients m).symm z * windowJets 2 b m w i.rev = 0 := by
  rw [mem_windowSubspace_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [hL] at hx
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx
    have he := shiftedInclusion_injective 2 b hyx
    subst y
    rw [LinearMap.mem_ker, normalizedRow_eval] at hy
    rwa [windowJets_representative, windowJets_representative]
  · intro hw
    have hs : Function.Surjective (windowProjection 2 b m) := Submodule.mkQ_surjective _
    obtain ⟨q, hq⟩ := hs w
    obtain ⟨x, hx⟩ := (shiftedCoordinates 2 b).surjective q
    have hxw : windowRepresentative b m x = w := by
      change windowProjection 2 b m (shiftedCoordinates 2 b x) = w
      rw [hx, hq]
    rw [← hxw, windowJets_representative, windowJets_representative] at hw
    refine ⟨x, ?_, hxw⟩
    rw [hL]
    apply Submodule.mem_map_of_mem
    rw [LinearMap.mem_ker, normalizedRow_eval]
    exact hw

private theorem normalizedRow_primitive {m : ℕ} (i : Fin 2) (z : JetRing m) :
    IsPrimitive (normalizedRow i z) := ⟨i, by simp [normalizedRow]⟩

private theorem normalizedRow_lattice (ab : DominantPair) (hm : 0 < difference ab)
    (i : Fin 2) (z : Fin (difference ab) → ℂ) :
    ∃ L : GL2Lattice, L ∈ gl2Orbit ab ∧ L.val = chartKernel ab.val.2 i z := by
  obtain ⟨_, e, he⟩ := primitiveRowClassification ab hm
  let a := (jetCoefficients (difference ab)).symm z
  let v : PrimitiveRow (difference ab) := ⟨normalizedRow i a, normalizedRow_primitive i a⟩
  exact ⟨(e (Quotient.mk _ v)).val, (e (Quotient.mk _ v)).property, he v⟩

private theorem lattice_has_normalizedRow {ab : DominantPair} (hm : 0 < difference ab)
    {L : GL2Lattice} (hL : L ∈ gl2Orbit ab) :
    ∃ (i : Fin 2) (z : Fin (difference ab) → ℂ), L.val = chartKernel ab.val.2 i z := by
  obtain ⟨_, e, he⟩ := primitiveRowClassification ab hm
  obtain ⟨⟨v⟩, hv⟩ := e.surjective ⟨L, hL⟩
  obtain ⟨i, u, hu⟩ := v.property
  let a := (u⁻¹).val * v.val i.rev
  let w : PrimitiveRow (difference ab) := ⟨normalizedRow i a, normalizedRow_primitive i a⟩
  have hrel : (primitiveRowRel (difference ab)).r v w := by
    refine ⟨u⁻¹, ?_⟩
    intro j
    by_cases hji : j = i
    · subst j
      simp [w, normalizedRow, ← hu]
    · have hj : j = i.rev := by
        fin_cases i <;> fin_cases j <;> simp_all
      subst j
      simp [w, normalizedRow, hji, a]
  refine ⟨i, jetCoefficients _ a, ?_⟩
  have hv' : L.val = shiftedKernel ab.val.2 v.val :=
    (congrArg (fun A : gl2Orbit ab ↦ A.val.val) hv).symm.trans (he v)
  rw [hv', chartKernel, LinearEquiv.symm_apply_apply]
  exact (row_quotient_rel_iff ab.val.2 v w).mp hrel

private def orbitWindowLattice {ab : DominantPair} {L : GL2Lattice} (hL : L ∈ gl2Orbit ab) :
    WindowLattice 2 ab.val.2 (difference ab) :=
  ⟨L, ⟨by rw [pair_window_end]; exact (orbit_endpoints hL).1 _ |>.mpr le_rfl,
    (orbit_endpoints hL).2 _ |>.mpr le_rfl⟩⟩

private theorem windowLattice_subspace_injective (r : ℕ) (a : ℤ) (m : ℕ) :
    Function.Injective (fun L : WindowLattice r a m ↦ latticeSubspace a m L.val) := by
  obtain ⟨e, he, _⟩ := BoundedLattices.windowLatticeComparison r a m
  intro L L' h
  apply e.injective
  apply Subtype.ext
  exact (he L).trans (h.trans (he L').symm)

end NormalizedRows

section NormalizedOrbit

open SchubertNormalizedJetGraphSpecs
  (NormalizedJetGraphCharts NormalizedJetPoints normalizedJetOpen normalizedJetScheme
    normalizedJetInclusion normalizedJetSubspace stableInclusion lineChart)
open private affinePoint_surjective opens_eq_of_complexPoints
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SchubertNormalizedJetGraphSchemes

variable {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
  {d : WindowDimension 2 ab.val.2 (difference ab)} {hd : d.val = difference ab}
  {hm : 0 < difference ab}

private theorem normalizedJetInclusion_open {b : ℤ} {m : ℕ} {d : WindowDimension 2 b m}
    (hd : d.val = m) :
    IsOpenImmersion (normalizedJetInclusion hd).left := by
  change IsOpenImmersion (normalizedJetOpen hd).ι
  infer_instance

private theorem normalizedJet_point_has_chart {b : ℤ} {m : ℕ}
    {d : WindowDimension 2 b m} {hd : d.val = m} {hm : 0 < m}
    (C : NormalizedJetGraphCharts hd hm) (q : NormalizedJetPoints hd) :
    ∃ (i : Fin 2) (z : Fin m → ℂ), affinePoint z ≫ C.chart i = q := by
  obtain ⟨i, hi⟩ := C.chart_cover (pointLocation q)
  have := C.chart_open i
  obtain ⟨p, hp⟩ := point_factors_open (C.chart i) q hi
  obtain ⟨z, rfl⟩ := affinePoint_surjective m p
  exact ⟨i, z, hp⟩

private theorem normalizedJet_chart_subspace {b : ℤ} {m : ℕ}
    {d : WindowDimension 2 b m} {hd : d.val = m} {hm : 0 < m}
    (C : NormalizedJetGraphCharts hd hm) (i : Fin 2) (z : Fin m → ℂ)
    {L : GL2Lattice} (hL : L.val = chartKernel b i z) :
    windowSchemeSubspace (affinePoint z ≫ C.chart i ≫ normalizedJetInclusion hd) =
      latticeSubspace b m L := by
  change normalizedJetSubspace (affinePoint z ≫ C.chart i) = _
  -- Both sides are the kernel of the same row on O/(t^m).
  ext x
  exact (C.kernel i z x).trans (latticeSubspace_chartKernel L i z hL x).symm

set_option maxHeartbeats 600000 in
private theorem normalizedJet_range_iff (C : NormalizedJetGraphCharts hd hm)
    (q : Points (windowStableScheme 2 ab.val.2 (difference ab) d) complexAlgebra)
    (L : WindowLattice 2 ab.val.2 (difference ab))
    (hq : windowSchemeSubspace q = latticeSubspace ab.val.2 (difference ab) L.val) :
    pointLocation q ∈ Set.range (normalizedJetInclusion hd).left ↔ L.val ∈ gl2Orbit ab := by
  let k := normalizedJetInclusion hd
  have : IsOpenImmersion k.left := normalizedJetInclusion_open hd
  constructor
  · intro h
    obtain ⟨p, hp⟩ := point_factors_open k q h
    obtain ⟨i, z, hz⟩ := normalizedJet_point_has_chart C p
    obtain ⟨K, hK, hKrow⟩ := normalizedRow_lattice ab hm i z
    have he := normalizedJet_chart_subspace C i z hKrow
    change windowSchemeSubspace (affinePoint z ≫ C.chart i ≫ k) = _ at he
    rw [← Category.assoc, hz, hp, hq] at he
    have hKL : L = orbitWindowLattice hK :=
      windowLattice_subspace_injective 2 ab.val.2 (difference ab) he
    have hLK : L.val = K := congrArg Subtype.val hKL
    exact hLK.symm ▸ hK
  · intro h
    obtain ⟨i, z, hz⟩ := lattice_has_normalizedRow hm h
    have he : (affinePoint z ≫ C.chart i) ≫ k = q := by
      apply windowSchemeSubspace_injective (d := d)
      rw [Category.assoc]
      exact (normalizedJet_chart_subspace C i z hz).trans hq.symm
    exact ⟨pointLocation (affinePoint z ≫ C.chart i),
      (pointLocation_comp _ _).symm.trans (congrArg pointLocation he)⟩

private theorem grassmannian_locallyOfFiniteType {V ι : Type}
    [AddCommGroup V] [Module ℂ V] [Fintype ι] [DecidableEq ι]
    (basis : Module.Basis ι ℂ V) {n : ℕ} (hn : n ≤ Module.finrank ℂ V) :
    LocallyOfFiniteType (grassmannianCharts basis hn).scheme.hom := by
  let G := grassmannianCharts basis hn
  let cover : G.scheme.left.OpenCover :=
    Scheme.Cover.mkOfCovers (Pivot ι n) (fun I ↦ (chartScheme (k := ℂ) I).left)
      (fun I ↦ (G.chart I).left) G.cover G.openChart
  have : ∀ I, IsAffine (cover.X I) := fun I ↦
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (chartAlgebra (k := ℂ) I))))
  refine HasRingHomProperty.of_source_openCover (P := @LocallyOfFiniteType) cover ?_
  intro I
  have h : cover.f I ≫ G.scheme.hom = (chartScheme (k := ℂ) I).hom := Over.w (G.chart I)
  rw [h]
  apply HasRingHomProperty.appTop (@LocallyOfFiniteType)
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℂ (chartAlgebra I))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

private theorem windowStable_locallyOfFiniteType (r : ℕ) (a : ℤ) (m : ℕ)
    (d : WindowDimension r a m) : LocallyOfFiniteType (windowStableScheme r a m d).hom := by
  let j := windowSchemeInGrassmannian r a m d
  have : IsClosedImmersion j.left := by
    change IsClosedImmersion (reducedClosureIdeal _ _).subschemeι
    infer_instance
  have := grassmannian_locallyOfFiniteType (windowBasis r a m) (windowDimension_le d)
  have h : LocallyOfFiniteType
      (j.left ≫ (grassmannianCharts (windowBasis r a m) (windowDimension_le d)).scheme.hom) :=
    inferInstance
  rwa [Over.w j] at h

private abbrev WindowToSchubert (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (d : WindowDimension 2 ab.val.2 (difference ab)) :=
  windowStableScheme 2 ab.val.2 (difference ab) d ⟶ occupiedSchubert ab N hN

private def PreservesLatticeSubspaces (f : WindowToSchubert ab N hN d) : Prop :=
  ∀ (L : WindowLattice 2 ab.val.2 (difference ab))
    (q : Points (windowStableScheme 2 ab.val.2 (difference ab) d) complexAlgebra),
    windowSchemeSubspace q = latticeSubspace ab.val.2 (difference ab) L.val →
    schubertPointSubspace (q ≫ f) = boundedSubspace (bounded_of_minimal ab N hN L)


private theorem schubertLatticeSet_of_subspace (q : OccupiedSchubertPoints ab N hN)
    (B : BoundedLattice 2 N) (hq : schubertPointSubspace q = boundedSubspace B) :
    B ∈ schubertLatticeSet ab N := by
  obtain ⟨E, hE⟩ := schubert_point_homeomorph ab N hN
  have eq : B = (E q).val := boundedSubspace_injective N (hq.symm.trans (hE q))
  exact eq.symm ▸ (E q).property

set_option maxHeartbeats 600000 in
private theorem normalizedJetOpen_matches (C : NormalizedJetGraphCharts hd hm)
    (e : WindowToSchubert ab N hN d) (he : PreservesLatticeSubspaces e)
    (q : Points (windowStableScheme 2 ab.val.2 (difference ab) d) complexAlgebra)
    (L : WindowLattice 2 ab.val.2 (difference ab))
    (hq : windowSchemeSubspace q = latticeSubspace ab.val.2 (difference ab) L.val) :
    pointLocation q ∈ normalizedJetOpen hd ↔ pointLocation (q ≫ e) ∈ orbitOpen ab N hN := by
  let B := bounded_of_minimal ab N hN L
  have hsub : schubertPointSubspace (q ≫ e) = boundedSubspace B := he L q hq
  have hB : B ∈ schubertLatticeSet ab N := schubertLatticeSet_of_subspace (q ≫ e) B hsub
  change pointLocation q ∈ (normalizedJetOpen hd : Set _) ↔ _
  rw [← Scheme.Opens.range_ι (normalizedJetOpen hd)]
  exact (normalizedJet_range_iff C q L hq).trans
    (pointLocation_orbitOpen_iff ab N hN ⟨B, hB⟩ (q ≫ e) hsub).symm

private theorem windowSchemePoint_lattice {r : ℕ} {b : ℤ} {m : ℕ}
    {d : WindowDimension r b m} (q : Points (windowStableScheme r b m d) complexAlgebra) :
    ∃ L : WindowLattice r b m, windowSchemeSubspace q = latticeSubspace b m L.val := by
  obtain ⟨_, _, e, he⟩ := BoundedLattices.windowSchemeComparison r b m d
  exact ⟨(e q).val, he q⟩

set_option maxHeartbeats 550000 in
private theorem normalizedJetOpen_preimage (C : NormalizedJetGraphCharts hd hm)
    (e : WindowToSchubert ab N hN d) (he : PreservesLatticeSubspaces e) :
    normalizedJetOpen hd = e.left ⁻¹ᵁ orbitOpen ab N hN := by
  let X := windowStableScheme 2 ab.val.2 (difference ab) d
  have ht : LocallyOfFiniteType X.hom := windowStable_locallyOfFiniteType _ _ _ _
  refine @opens_eq_of_complexPoints X ht (normalizedJetOpen hd) (e.left ⁻¹ᵁ orbitOpen ab N hN) ?_
  intro q
  change pointLocation q ∈ normalizedJetOpen hd ↔ e.left (pointLocation q) ∈ orbitOpen ab N hN
  rw [← pointLocation_comp q e]
  obtain ⟨L, hL⟩ := windowSchemePoint_lattice q
  exact normalizedJetOpen_matches C e he q L hL

private theorem openImmersions_iso_of_range {A B X : SchemeOver ℂ}
    (f : A ⟶ X) (i : B ⟶ X) [IsOpenImmersion f.left] [IsOpenImmersion i.left]
    (hRange : Set.range f.left = Set.range i.left) :
    ∃ E : A ≅ B, E.hom ≫ i = f := by
  let u := IsOpenImmersion.isoOfRangeEq f.left i.left hRange
  have hu : u.hom ≫ i.left = f.left := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let v : A ⟶ B := Over.homMk u.hom (by rw [← Over.w i, ← Category.assoc, hu, Over.w])
  have : IsIso ((Over.forget _).map v) := inferInstanceAs (IsIso u.hom)
  have : IsIso v := isIso_of_reflects_iso _ (Over.forget _)
  exact ⟨asIso v, Over.OverMorphism.ext hu⟩

private theorem iso_left_surjective {A B : SchemeOver ℂ} (e : A ≅ B) :
    Function.Surjective e.hom.left := by
  intro x
  exact ⟨e.inv.left x, congrArg (fun g : B ⟶ B ↦ g.left x) e.inv_hom_id⟩

private theorem restrict_minimal_isomorphism (C : NormalizedJetGraphCharts hd hm)
    (e : windowStableScheme 2 ab.val.2 (difference ab) d ≅ occupiedSchubert ab N hN)
    (he : PreservesLatticeSubspaces e.hom) :
    ∃ E : normalizedJetScheme hd ≅ orbitScheme ab N hN,
      E.hom ≫ orbitToSchubert ab N hN = normalizedJetInclusion hd ≫ e.hom := by
  let k := normalizedJetInclusion hd
  let i := orbitToSchubert ab N hN
  let f := k ≫ e.hom
  have : IsOpenImmersion k.left := normalizedJetInclusion_open hd
  have : IsOpenImmersion i.left := orbitToSchubert_open ab N hN
  have : IsIso e.hom.left := Functor.map_isIso (Over.forget _) e.hom
  have : IsOpenImmersion f.left := by
    change IsOpenImmersion (k.left ≫ e.hom.left)
    infer_instance
  have hRange : Set.range f.left = Set.range i.left := by
    rw [range_over_comp]
    change e.hom.left '' Set.range (normalizedJetOpen hd).ι = Set.range (orbitOpen ab N hN).ι
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι, normalizedJetOpen_preimage C e.hom he]
    exact Set.image_preimage_eq _ (iso_left_surjective e)
  exact openImmersions_iso_of_range f i hRange

end NormalizedOrbit

section OrbitCharts

open CategoryTheory.Limits
open SchubertNormalizedJetGraphSpecs
  (NormalizedJetGraphCharts NormalizedJetPoints normalizedJetScheme
    normalizedJetInclusion stableInclusion lineChart)

variable {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
  {d : WindowDimension 2 ab.val.2 (difference ab)} {hd : d.val = difference ab}

private theorem complexPoints_injective {X Y : SchemeOver ℂ} (j : X ⟶ Y) [Mono j.left] :
    Function.Injective (fun p : Points X complexAlgebra ↦ p ≫ j) := by
  have : Mono j := Over.mono_of_mono_left j
  exact fun _ _ h ↦ (cancel_mono j).mp h

private abbrev WindowFlagMap (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (d : WindowDimension 2 ab.val.2 (difference ab)) :=
  WindowPoints 2 ab.val.2 (difference ab) d →
    WindowPoints 2 (-(N : ℤ)) (2 * N) (occupiedDimension ab N hN)

private def WindowFlagRespectsLattices (F : WindowFlagMap ab N hN d) : Prop :=
  ∀ (L : WindowLattice 2 ab.val.2 (difference ab))
    (p : WindowPoints 2 ab.val.2 (difference ab) d),
    grassmannianSubspace (windowBasis 2 ab.val.2 (difference ab)) (windowDimension_le d) p =
      latticeSubspace ab.val.2 (difference ab) L.val →
    grassmannianSubspace (windowBasis 2 (-(N : ℤ)) (2 * N))
      (windowDimension_le (occupiedDimension ab N hN)) (F p) =
      boundedSubspace (bounded_of_minimal ab N hN L)

set_option maxHeartbeats 600000 in
private theorem minimalWindow_analytic_inclusion (ab : DominantPair) (N : ℕ)
    (hN : OrbitBound ab N) (d : WindowDimension 2 ab.val.2 (difference ab))
    (hd : d.val = difference ab) :
    ∃ F : WindowFlagMap ab N hN d, Topology.IsClosedEmbedding F ∧ WindowFlagRespectsLattices F := by
  let D₀ := occupiedDimension ab N hN
  have ha : ab.val.1 ≤ (N : ℤ) := by simpa [pairCoweight] using (hN 0).2
  have hb : -(N : ℤ) ≤ ab.val.2 := by simpa [pairCoweight] using (hN 1).1
  have hEnd : ab.val.2 + (difference ab : ℤ) ≤ -(N : ℤ) + ((2 * N : ℕ) : ℤ) := by
    rw [boundedExponent, pair_window_end]
    exact ha
  obtain ⟨_, _, _, _, hFlag⟩ := SchubertAnalyticFlagTransport.windowFlagIncidence
    2 ab.val.2 (-(N : ℤ)) (difference ab) (2 * N) hb hEnd
  obtain ⟨D, F, hD, hF, _, _, hLattice⟩ := hFlag d
  have hDim : D = D₀ := by
    apply eq_occupiedDimension hN
    change D.val = d.val + 2 * ((-(N : ℤ) + ((2 * N : ℕ) : ℤ)) -
      (ab.val.2 + (difference ab : ℤ))).toNat at hD
    rw [boundedExponent, pair_window_end, hd] at hD
    have hdiff := difference_cast ab
    unfold Occupied
    omega
  subst D
  exact ⟨F, hF, fun L p hp ↦ hLattice L.val p L.property.1 L.property.2 hp⟩

private theorem induced_openEmbedding_of_iso {X Y G H : SchemeOver ℂ}
    [TopologicalSpace (Points G complexAlgebra)] [TopologicalSpace (Points H complexAlgebra)]
    (a : X ⟶ G) (b : Y ⟶ H) [Mono a.left] [Mono b.left]
    (E : X ≅ Y) (F : Points G complexAlgebra → Points H complexAlgebra)
    (hF : Topology.IsEmbedding F) (hcomm : ∀ p : Points X complexAlgebra,
      (p ≫ E.hom) ≫ b = F (p ≫ a)) :
    @Topology.IsOpenEmbedding _ _
      (TopologicalSpace.induced (fun p : Points X complexAlgebra ↦ p ≫ a) inferInstance)
      (TopologicalSpace.induced (fun q : Points Y complexAlgebra ↦ q ≫ b) inferInstance)
      (fun p : Points X complexAlgebra ↦ p ≫ E.hom) := by
  let g (p : Points X complexAlgebra) := p ≫ a
  let h (q : Points Y complexAlgebra) := q ≫ b
  let f (p : Points X complexAlgebra) := p ≫ E.hom
  let : TopologicalSpace (Points X complexAlgebra) := TopologicalSpace.induced g inferInstance
  let : TopologicalSpace (Points Y complexAlgebra) := TopologicalSpace.induced h inferInstance
  have hg : Topology.IsEmbedding g := (complexPoints_injective a).isEmbedding_induced
  have hh : Topology.IsEmbedding h := (complexPoints_injective b).isEmbedding_induced
  have hf : Topology.IsEmbedding f := by
    apply hh.of_comp_iff.mp
    have he : h ∘ f = F ∘ g := funext hcomm
    rw [he]
    exact hF.comp hg
  have hSurj : Function.Surjective f := by
    intro q
    exact ⟨q ≫ E.inv, by simp [f]⟩
  exact (hf.toHomeomorphOfSurjective hSurj).isOpenEmbedding

private theorem minimalWindow_point_comp
    (e : WindowToSchubert ab N hN d) (he : PreservesLatticeSubspaces e)
    (F : WindowFlagMap ab N hN d) (hF : WindowFlagRespectsLattices F)
    (q : Points (windowStableScheme 2 ab.val.2 (difference ab) d) complexAlgebra) :
    (q ≫ e) ≫ schubertToGrassmannian ab N hN _ = F (q ≫ stableInclusion d) := by
  obtain ⟨L, hL⟩ := windowSchemePoint_lattice q
  apply grassmannianSubspace_injective (windowBasis 2 (-(N : ℤ)) (2 * N))
    (windowDimension_le (occupiedDimension ab N hN))
  exact (he L q hL).trans (hF L (q ≫ stableInclusion d) hL).symm

private theorem normalizedOrbit_point_comp
    (e : WindowToSchubert ab N hN d) (E : normalizedJetScheme hd ≅ orbitScheme ab N hN)
    (hE : E.hom ≫ orbitToSchubert ab N hN = normalizedJetInclusion hd ≫ e)
    (p : NormalizedJetPoints hd) :
    (p ≫ E.hom) ≫ orbitToGrassmannian ab N hN =
      ((p ≫ normalizedJetInclusion hd) ≫ e) ≫ schubertToGrassmannian ab N hN _ := by
  simpa only [orbitToGrassmannian, Category.assoc] using
    (congrArg (fun g ↦ p ≫ g ≫ schubertToGrassmannian ab N hN _) hE)

set_option maxHeartbeats 600000 in
private theorem normalized_orbit_analytic
    (e : windowStableScheme 2 ab.val.2 (difference ab) d ≅ occupiedSchubert ab N hN)
    (he : PreservesLatticeSubspaces e.hom)
    (E : normalizedJetScheme hd ≅ orbitScheme ab N hN)
    (hE : E.hom ≫ orbitToSchubert ab N hN = normalizedJetInclusion hd ≫ e.hom) :
    Topology.IsOpenEmbedding (fun p : NormalizedJetPoints hd ↦ (p ≫ E.hom : OrbitPoints ab N hN)) := by
  let k := normalizedJetInclusion hd
  let s := stableInclusion d
  let G := orbitToGrassmannian ab N hN
  let j := schubertToGrassmannian ab N hN (occupiedDimension ab N hN)
  have : IsOpenImmersion k.left := normalizedJetInclusion_open hd
  have : IsClosedImmersion s.left := by
    change IsClosedImmersion (reducedClosureIdeal _ _).subschemeι
    infer_instance
  have : IsOpenImmersion (orbitToSchubert ab N hN).left := orbitToSchubert_open ab N hN
  have : IsClosedImmersion j.left :=
    schubertToGrassmannian_closed ab N hN (occupiedDimension ab N hN)
  have : Mono (k ≫ s).left := by
    change Mono (k.left ≫ s.left)
    infer_instance
  have : Mono G.left := by
    change Mono ((orbitToSchubert ab N hN).left ≫ j.left)
    infer_instance
  obtain ⟨F, hF, hLattice⟩ := minimalWindow_analytic_inclusion ab N hN d hd
  refine induced_openEmbedding_of_iso (k ≫ s) G E F hF.isEmbedding ?_
  intro p
  rw [← Category.assoc p k s]
  exact (normalizedOrbit_point_comp e.hom E hE p).trans
    (minimalWindow_point_comp e.hom he F hLattice (p ≫ k))

set_option maxHeartbeats 1100000 in
theorem primitiveRowCharts : PrimitiveRowCharts := by
  intro ab N hN hm
  let m := difference ab
  let Y := orbitScheme ab N hN
  obtain ⟨d, hd, e, hsub⟩ := minimalWindowComparison ab N hN
  have he : PreservesLatticeSubspaces e.hom := by
    intro L p hp
    simpa only [schubertPointSubspace, Category.assoc, boundedSubspace, bounded_of_minimal]
      using hsub L p hp
  obtain ⟨C⟩ := SchubertNormalizedJetGraphSchemes.normalizedJetGraphSchemeCharts ab.val.2 m d hd hm
  obtain ⟨E, hE⟩ := restrict_minimal_isomorphism C e he
  have : IsIso E.hom.left := Functor.map_isIso (Over.forget _) E.hom
  have : IsIso E.inv.left := Functor.map_isIso (Over.forget _) E.inv
  have hSmooth : SmoothOfRelativeDimension m Y.hom := by
    have : SmoothOfRelativeDimension 0 E.inv.left := inferInstance
    have := C.smooth
    have h : SmoothOfRelativeDimension (0 + m) (E.inv.left ≫ (normalizedJetScheme hd).hom) :=
      inferInstance
    simpa only [Over.w E.inv, Nat.zero_add] using h
  let π : Y ⟶ ProjectiveLine := E.inv ≫ C.projection
  let c : Fin 2 → (Affine m ⟶ Y) := fun i ↦ C.chart i ≫ E.hom
  have hp : IsPullback E.hom C.projection π (𝟙 _) := by
    apply IsPullback.of_horiz_isIso
    exact ⟨by simp [π]⟩
  refine ⟨hSmooth, π, c, lineChart, ?_, ?_, C.line_chart_cover, C.line_chart_point, ?_, ?_, ?_⟩
  · intro i
    have := C.chart_open i
    have hc : IsOpenImmersion (c i).left := by
      change IsOpenImmersion ((C.chart i).left ≫ E.hom.left)
      infer_instance
    exact ⟨hc, C.line_chart_open i, by
      simpa only [Category.comp_id] using (C.projection_pullback i).paste_horiz hp⟩
  · intro y
    obtain ⟨p, rfl⟩ := iso_left_surjective E y
    obtain ⟨i, x, hx⟩ := C.chart_cover p
    refine ⟨i, x, ?_⟩
    change E.hom.left ((C.chart i).left x) = E.hom.left p
    rw [hx]
  · intro i z
    obtain ⟨L, hL, hRow⟩ := normalizedRow_lattice ab hm i z
    let W := orbitWindowLattice hL
    let q := affinePoint z ≫ C.chart i ≫ normalizedJetInclusion hd
    refine ⟨bounded_of_minimal ab N hN W, hRow, ?_⟩
    have hq : windowSchemeSubspace q = latticeSubspace ab.val.2 m W.val :=
      normalizedJet_chart_subspace C i z hRow
    have hcomp : ((affinePoint z ≫ c i) ≫ orbitToGrassmannian ab N hN) =
        (q ≫ e.hom) ≫ schubertToGrassmannian ab N hN _ := by
      simpa only [q, c, orbitToGrassmannian, Category.assoc] using
        (congrArg (fun g ↦ affinePoint z ≫ C.chart i ≫ g ≫ schubertToGrassmannian ab N hN _) hE)
    unfold orbitPointSubspace
    rw [hcomp]
    exact he W q hq
  · intro i
    have hEan := normalized_orbit_analytic e he E hE
    simpa only [Function.comp_def, Category.assoc] using hEan.comp (C.analytic_open i)
  · intro z w
    simp only [c, ← Category.assoc, cancel_mono]
    exact C.inversion_on_points 0 z w

end OrbitCharts

end

end RepTheorySurvey.Geometric.RankTwoSchubertStrata
