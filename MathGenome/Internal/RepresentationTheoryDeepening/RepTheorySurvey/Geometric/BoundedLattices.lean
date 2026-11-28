import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.BoundedLattices
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.LatticeModels
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.GrassmannianIncidenceSchemes
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.GrassmannianIncidenceTopology
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.LatticeWindowInclusionCoordinates
import Mathlib.Algebra.Module.Lattice
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

namespace RepTheorySurvey.Geometric.BoundedLattices

noncomputable section

open scoped Matrix MatrixGroups Matrix.Norms.Elementwise
open LatticeModelSpecs BoundedLatticeSpecs
open Module AlgebraicGeometry CategoryTheory
open LinearAlgebraicGroups (Points SchemeOver)
open LinearAlgebraicGroups.Specs.GrassmannianCharts
open LinearAlgebraicGroups.GrassmannianCharts (chartMatrixEquiv)
open scoped Topology
open Filter TopologicalSpace

private theorem inclusion_injective : Function.Injective inclusion :=
  HahnSeries.ofPowerSeries_injective

private theorem isLattice {r : ℕ} (L : Lattice r) : Submodule.IsLattice K L.val := by
  obtain ⟨b⟩ := L.property.1
  let : Module.Finite O L.val := Module.Finite.of_basis b
  exact ⟨Module.Finite.iff_fg.mp inferInstance, L.property.2⟩

theorem glTransitive : GLTransitive := by
  intro r L
  obtain ⟨b⟩ := L.property.1
  let := isLattice L
  let c := b.extendOfIsLattice K
  let e := (Pi.basisFun K (Fin r)).equiv c (Equiv.refl _)
  let g := (loopLinearEquiv r).symm e
  have he : loopLinearEquiv r g = e := (loopLinearEquiv r).apply_symm_apply e
  let eO := (Pi.basisFun O (Fin r)).equiv b (Equiv.refl _)
  have hcomp : ((e.restrictScalars O).toLinearMap.comp (coordinateInclusion r)) =
      L.val.subtype.comp eO.toLinearMap := by
    apply (Pi.basisFun O (Fin r)).ext
    intro i
    have hi : coordinateInclusion r (Pi.basisFun O (Fin r) i) = Pi.basisFun K (Fin r) i := by
      ext j
      by_cases h : j = i <;>
        simp [coordinateInclusion, Pi.basisFun_apply, h]
    change e (coordinateInclusion r (Pi.basisFun O (Fin r) i)) =
      L.val.subtype (eO (Pi.basisFun O (Fin r) i))
    rw [hi, Basis.equiv_apply, Basis.equiv_apply]
    exact b.extendOfIsLattice_apply K i
  refine ⟨g, Subtype.ext ?_⟩
  change (coordinateInclusion r).range.map ((loopLinearEquiv r g).restrictScalars O).toLinearMap =
    L.val
  rw [he, ← LinearMap.range_comp, hcomp, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr eO.surjective, Submodule.map_top, Submodule.range_subtype]

private theorem scalarLattice_zero (r : ℕ) : scalarLattice r 0 = standardLattice r := by
  have h : diagonalEquiv (r := r) (fun _ ↦ 0) = LinearEquiv.refl K (Coordinates r) := by
    apply LinearEquiv.ext
    intro x
    funext i
    change monomial 0 * x i = x i
    simp [monomial_eq_zpow]
  apply Subtype.ext
  change (standardLattice r).val.map ((diagonalEquiv (r := r) (fun _ ↦ 0)).restrictScalars O).toLinearMap = _
  rw [h]
  exact Submodule.map_id _

private theorem integralMatrixOfStabilizer {r : ℕ} (g : GL (Fin r) K)
    (hg : g • standardLattice r = standardLattice r) :
    ∃ M : Matrix (Fin r) (Fin r) O, M.map inclusion = g.val := by
  classical
  have hcols (j : Fin r) : ∃ x : Fin r → O, ∀ i, inclusion (x i) = g.val i j := by
    let y := coordinateInclusion r (Pi.single j (1 : O))
    have hy : loopLinearEquiv r g y ∈ (standardLattice r).val := by
      rw [← hg]
      exact ⟨y, LinearMap.mem_range_self _ _, rfl⟩
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, fun i ↦ ?_⟩
    have hy' : y = Pi.single j 1 := by
      funext i
      by_cases h : i = j <;> simp [y, coordinateInclusion, h]
    rw [hy', loopLinearEquiv_apply, Matrix.mulVec_single_one] at hx
    exact congrFun hx i
  choose x hx using hcols
  exact ⟨Matrix.of fun i j ↦ x j i, funext fun i ↦ funext fun j ↦ hx j i⟩

theorem glStabilizer : GLStabilizer := by
  intro r
  ext g
  change (g • standardLattice r = standardLattice r) ↔
    g ∈ (positiveGLMap r).range
  constructor
  · intro hg
    have hgi : g⁻¹ • standardLattice r = standardLattice r := by
      exact (inv_smul_eq_iff.mpr hg.symm)
    obtain ⟨M, hM⟩ := integralMatrixOfStabilizer g hg
    obtain ⟨N, hN⟩ := integralMatrixOfStabilizer g⁻¹ hgi
    have hinj : Function.Injective (Matrix.map · inclusion :
        Matrix (Fin r) (Fin r) O → Matrix (Fin r) (Fin r) K) := by
      intro A B hab
      apply Matrix.ext
      intro i j
      exact inclusion_injective (congrFun (congrFun hab i) j)
    have hmul : M * N = 1 := hinj (by
      change (M * N).map inclusion = (1 : Matrix (Fin r) (Fin r) O).map inclusion
      rw [Matrix.map_mul, hM, hN, Matrix.map_one _ (map_zero inclusion) (map_one inclusion)]
      exact g.val_inv)
    have hinv : N * M = 1 := hinj (by
      change (N * M).map inclusion = (1 : Matrix (Fin r) (Fin r) O).map inclusion
      rw [Matrix.map_mul, hM, hN, Matrix.map_one _ (map_zero inclusion) (map_one inclusion)]
      exact g.inv_val)
    exact ⟨⟨M, N, hmul, hinv⟩, Units.ext hM⟩
  · rintro ⟨h, rfl⟩
    simpa only [scalarLattice_zero] using positiveGL_preserves_scalar h 0

private theorem orbitCosets {G X : Type} [Group G] [MulAction G X]
    (x : X) (H : Subgroup G) (hH : MulAction.stabilizer G x = H)
    (hx : ∀ y : X, ∃ g : G, g • x = y) :
    ∃ e : Grassmannian H ≃ X, ∀ g : G, e (coset H g) = g • x := by
  subst H
  let p : MulAction.orbit G x ≃ X :=
    Equiv.ofBijective Subtype.val ⟨Subtype.val_injective, fun y ↦
      ⟨⟨y, hx y⟩, rfl⟩⟩
  exact ⟨(MulAction.orbitEquivQuotientStabilizer G x).symm.trans p,
    MulAction.orbitEquivQuotientStabilizer_symm_apply G x⟩

theorem glCosets : GLCosets := by
  intro r
  exact orbitCosets _ _ (glStabilizer r) (glTransitive r)

/-- The singleton diagonal matrix for a unit, valid over the positive, Laurent,
and truncated coefficient rings. -/
private def oneByOne (R : Type) [CommRing R] : Rˣ ≃* GL (Fin 1) R :=
  Units.mapEquiv (Matrix.uniqueRingEquiv (m := Fin 1) (A := R)).symm.toMulEquiv

private theorem oneByOne_val {R : Type} [CommRing R] (u : Rˣ) :
    (oneByOne R u).val = Matrix.diagonal (fun _ : Fin 1 ↦ u.val) := by
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i
  subst j
  change u.val = Matrix.diagonal (fun _ : Fin 1 ↦ u.val) 0 0
  simp

private theorem oneByOne_positive (u : Oˣ) :
    oneByOne K (Units.map inclusion.toMonoidHom u) = positiveGLMap 1 (oneByOne O u) := by
  apply Units.ext
  rw [oneByOne_val]
  change Matrix.diagonal (fun _ : Fin 1 ↦ inclusion u.val) = (oneByOne O u).val.map inclusion
  rw [oneByOne_val, Matrix.diagonal_map (map_zero inclusion)]

private theorem torus_smul_coordinate {r : ℕ} (g : Fin r → Kˣ) (L : TorusLattice r)
    (i : Fin r) : (g • L) i = oneByOne K (g i) • L i := by
  have hm : diagonalUnits 1 (fun _ ↦ g i) = oneByOne K (g i) := by
    apply Units.ext
    exact (oneByOne_val (g i)).symm
  change diagonalUnits 1 (fun _ ↦ g i) • L i = _
  rw [hm]

theorem torusTransitive : TorusTransitive := by
  intro r L
  choose g hg using fun i ↦ glTransitive 1 (L i)
  refine ⟨fun i ↦ (oneByOne K).symm (g i), ?_⟩
  funext i
  rw [torus_smul_coordinate, MulEquiv.apply_symm_apply]
  exact hg i

theorem torusStabilizer : TorusStabilizer := by
  intro r
  ext g
  change (g • (fun _ : Fin r ↦ standardLattice 1) = _) ↔
    g ∈ (positiveTorusMap r).range
  constructor
  · intro h
    have hi (i : Fin r) : oneByOne K (g i) ∈ PositiveGL 1 := by
      rw [← glStabilizer 1, MulAction.mem_stabilizer_iff]
      rw [← torus_smul_coordinate g (fun _ ↦ standardLattice 1) i, h]
    choose u hu using hi
    refine ⟨fun i ↦ (oneByOne O).symm (u i), ?_⟩
    funext i
    apply (oneByOne K).injective
    change oneByOne K (Units.map inclusion.toMonoidHom ((oneByOne O).symm (u i))) = _
    rw [oneByOne_positive, MulEquiv.apply_symm_apply, hu i]
  · rintro ⟨u, rfl⟩
    funext i
    rw [torus_smul_coordinate]
    change oneByOne K (Units.map inclusion.toMonoidHom (u i)) • standardLattice 1 = _
    rw [oneByOne_positive]
    apply MulAction.mem_stabilizer_iff.mp
    rw [glStabilizer 1]
    exact ⟨oneByOne O (u i), rfl⟩

theorem torusCosets : TorusCosets := by
  intro r
  exact orbitCosets _ _ (torusStabilizer r) (torusTransitive r)

theorem windowPositiveStable : WindowPositiveStable := by
  intro r a m g L
  let f := ((loopLinearEquiv r (positiveGLMap r g)).restrictScalars O).toLinearMap
  have hfix (b : ℤ) : (scalarLattice r b).val.map f = (scalarLattice r b).val :=
    congrArg Subtype.val (positiveGL_preserves_scalar g b)
  change (scalarLattice r (a + (m : ℤ))).val ≤ L.val.val.map f ∧
    L.val.val.map f ≤ (scalarLattice r a).val
  exact ⟨by simpa only [hfix] using Submodule.map_mono (f := f) L.property.1,
    by simpa only [hfix] using Submodule.map_mono (f := f) L.property.2⟩

private theorem commonLaurentBound {ι : Type} [Fintype ι] (x : ι → K) :
    ∃ N : ℕ, ∀ i, ∃ f : O, monomial N * x i = inclusion f := by
  let N := Finset.univ.sup (fun i ↦ (x i).order.natAbs)
  refine ⟨N, fun i ↦ ?_⟩
  let a : ℤ := N + (x i).order
  have hbound : (x i).order.natAbs ≤ N :=
    Finset.le_sup (f := fun i ↦ (x i).order.natAbs) (Finset.mem_univ i)
  have ha : 0 ≤ a := by dsimp [a]; omega
  refine ⟨t ^ a.toNat * (x i).powerSeriesPart, ?_⟩
  have hx : monomial (x i).order * inclusion (x i).powerSeriesPart = x i :=
    (x i).single_order_mul_powerSeriesPart
  calc
    monomial N * x i = monomial a * inclusion (x i).powerSeriesPart := by
      conv_lhs => rw [← hx]
      rw [← mul_assoc, ← monomial_add]
    _ = inclusion (t ^ a.toNat * (x i).powerSeriesPart) := by
      rw [map_mul, ← monomial_nat, Int.toNat_of_nonneg ha]

private theorem standardImage_le_scalar {r N : ℕ} (g : GL (Fin r) K)
    (h : ∀ i j, ∃ f : O, monomial N * g.val i j = inclusion f) :
    (g • standardLattice r).val ≤ (scalarLattice r (-(N : ℤ))).val := by
  classical
  choose f hf using h
  intro y hy
  obtain ⟨_, ⟨x, rfl⟩, rfl⟩ := hy
  rw [scalarLattice_val]
  refine ⟨(Matrix.of f) *ᵥ x, ?_⟩
  change _ = loopLinearEquiv r g (coordinateInclusion r x)
  rw [loopLinearEquiv_apply]
  funext i
  have hcancel (z : K) : monomial (-(N : ℤ)) * (monomial N * z) = z := by
    rw [← mul_assoc, ← monomial_add, neg_add_cancel]
    simp [monomial_eq_zpow]
  change monomial (-(N : ℤ)) * inclusion (∑ j, f i j * x j) =
    ∑ j, g.val i j * inclusion (x j)
  simp only [map_sum, map_mul, ← hf, Finset.mul_sum, ← mul_assoc, hcancel]

set_option maxHeartbeats 600000 in
theorem latticeExhaustion : LatticeExhaustion := by
  have hgl (r : ℕ) (L : Lattice r) : ∃ (N : ℕ) (B : BoundedLattice r N), B.val = L := by
    obtain ⟨g, rfl⟩ := glTransitive r L
    let x : Bool × Fin r × Fin r → K :=
      fun ⟨b, i, j⟩ ↦ if b then g.val i j else (g⁻¹).val i j
    obtain ⟨N, hN⟩ := commonLaurentBound x
    have hg := standardImage_le_scalar g (N := N)
      (fun i j ↦ by simpa [x] using hN (true, i, j))
    have hgi := standardImage_le_scalar g⁻¹ (N := N)
      (fun i j ↦ by simpa [x] using hN (false, i, j))
    refine ⟨N, ⟨_, ?_, hg⟩, rfl⟩
    rw [scalarLattice_val]
    rintro _ ⟨u, rfl⟩
    let e := loopLinearEquiv r g
    let y := loopLinearEquiv r g⁻¹ (coordinateInclusion r u)
    have hy : y ∈ (scalarLattice r (-(N : ℤ))).val :=
      hgi ⟨_, LinearMap.mem_range_self _ _, rfl⟩
    rw [scalarLattice_val] at hy
    obtain ⟨v, hv⟩ := hy
    refine ⟨coordinateInclusion r v, LinearMap.mem_range_self _ _, ?_⟩
    have he : loopLinearEquiv r g⁻¹ = e.symm := map_inv (loopLinearEquiv r) g
    change e (coordinateInclusion r v) = monomial N • coordinateInclusion r u
    apply e.symm.injective
    rw [e.symm_apply_apply, map_smul, ← he]
    change coordinateInclusion r v = monomial N • y
    rw [← hv]
    change coordinateInclusion r v = monomial N • (monomial (-(N : ℤ)) • coordinateInclusion r v)
    rw [smul_smul, ← monomial_add, add_neg_cancel]
    simp [monomial_eq_zpow]
  refine ⟨hgl, fun r L ↦ ?_⟩
  choose n B hB using fun i ↦ hgl 1 (L i)
  refine ⟨Finset.univ.sup n, fun i ↦ boundedInclusion (Finset.le_sup (f := n) (Finset.mem_univ i)) (B i),
    hB⟩

private theorem window_smul_eq_of_reduction {r m : ℕ} {a : ℤ} {f g : O}
    (h : jetReduction m f = jetReduction m g) (x : Window r a m) : f • x = g • x := by
  apply (windowJets r a m).injective
  simp only [map_smul]
  funext i
  change jetReduction m f * windowJets r a m x i = jetReduction m g * windowJets r a m x i
  rw [h]

private theorem windowSubspace_smul_mem {r m : ℕ} {a : ℤ} (P : StableSubspaces r a m)
    (f : O) {x : Window r a m} (hx : x ∈ P.val) : f • x ∈ P.val := by
  classical
  let f' : O := ∑ j ∈ Finset.range m, PowerSeries.monomial j (PowerSeries.coeff j f)
  have hred : jetReduction m f = jetReduction m f' := by
    apply (jetCoefficients m).injective
    funext j
    rw [jetCoefficients_reduce, jetCoefficients_reduce]
    change PowerSeries.coeff j.val f = (PowerSeries.coeff j.val) (∑ k ∈ Finset.range m, _)
    rw [map_sum]
    simp only [PowerSeries.coeff_monomial]
    rw [Finset.sum_eq_single j.val]
    · simp
    · intro k _ hne
      simp [Ne.symm hne]
    · simp [j.isLt]
  have hpow (j : ℕ) : t ^ j • x ∈ P.val := by
    induction j with
    | zero => simpa using hx
    | succ j ih =>
      rw [pow_succ', mul_smul]
      exact P.property ⟨t ^ j • x, ih, rfl⟩
  rw [window_smul_eq_of_reduction hred x]
  change f' • x ∈ P.val
  rw [show f' • x = ∑ j ∈ Finset.range m,
      PowerSeries.monomial j (PowerSeries.coeff j f) • x from Finset.sum_smul ..]
  apply Submodule.sum_mem
  intro j _
  rw [PowerSeries.monomial_eq_C_mul_X_pow, mul_smul]
  change (algebraMap ℂ O (PowerSeries.coeff j f)) • (t ^ j • x) ∈ P.val
  rw [IsScalarTower.algebraMap_smul O]
  exact P.val.smul_mem (PowerSeries.coeff j f) (hpow j)

private def liftStableSubspace {r : ℕ} {a : ℤ} {m : ℕ}
    (P : StableSubspaces r a m) : Submodule O (Window r a m) where
  carrier := P.val
  zero_mem' := P.val.zero_mem
  add_mem' := P.val.add_mem
  smul_mem' f _ := windowSubspace_smul_mem P f

private def latticeOfBetween {r : ℕ} {a : ℤ} {m : ℕ}
    (S : Submodule O (Coordinates r)) (hlo : (scalarLattice r (a + (m : ℤ))).val ≤ S)
    (hhi : S ≤ (scalarLattice r a).val) : Lattice r := by
  let b := (scalarLattice r a).property.1.some
  let bS := (Submodule.basisOfPidOfLE hhi b).2
  let : Module.Finite O (S : Type) := Module.Finite.of_basis bS
  have hspan : Submodule.span K (S : Set (Coordinates r)) = ⊤ := by
    exact top_unique ((scalarLattice r (a + (m : ℤ))).property.2 ▸ Submodule.span_mono hlo)
  let : Submodule.IsLattice K S := ⟨Module.Finite.iff_fg.mp inferInstance, hspan⟩
  exact ⟨S, ⟨⟨Module.finBasisOfFinrankEq O S (by
    simpa using Submodule.IsLattice.finrank_of_pi K S)⟩, hspan⟩⟩

set_option backward.isDefEq.respectTransparency false in
private abbrev windowProjection (r : ℕ) (a : ℤ) (m : ℕ) :
    ((scalarLattice r a).val : Type) →ₗ[O] Window r a m :=
  @Submodule.mkQ O ((scalarLattice r a).val : Type) inferInstance inferInstance inferInstance
    (windowLower r a m)

set_option backward.isDefEq.respectTransparency false in
private theorem windowProjection_ker (r : ℕ) (a : ℤ) (m : ℕ) :
    (windowProjection r a m).ker = windowLower r a m :=
  @Submodule.ker_mkQ O ((scalarLattice r a).val : Type) inferInstance inferInstance inferInstance
    (windowLower r a m)

set_option backward.isDefEq.respectTransparency false in
private theorem windowProjection_range (r : ℕ) (a : ℤ) (m : ℕ) :
    (windowProjection r a m).range = ⊤ :=
  @Submodule.range_mkQ O ((scalarLattice r a).val : Type) inferInstance inferInstance inferInstance
    (windowLower r a m)

set_option maxHeartbeats 500000 in
private theorem windowInverseImage_latticeSubspace {r : ℕ} {a : ℤ} {m : ℕ}
    (L : WindowLattice r a m) :
    windowInverseImage (latticeSubspace a m L.val) = L.val.val.restrictScalars ℂ := by
  let f := (scalarLattice r a).val.subtype
  let q := windowProjection r a m
  let Z := L.val.val.comap f
  have hle : windowLower r a m ≤ Z := by
    intro x hx
    exact L.property.1 (show (x : Coordinates r) ∈ (scalarLattice r (a + (m : ℤ))).val from hx)
  have hz : (Z.map q).comap q = Z := by
    calc
      (Z.map q).comap q = windowLower r a m ⊔ Z :=
        @Submodule.comap_map_mkQ O ((scalarLattice r a).val : Type)
          inferInstance inferInstance inferInstance (windowLower r a m) Z
      _ = Z := sup_eq_right.mpr hle
  have hmap : Z.map f = L.val.val := by
    rw [Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.mpr L.property.2]
  change (((Z.map q).comap q).map f).restrictScalars ℂ = _
  rw [hz, hmap]

set_option maxHeartbeats 500000 in
theorem windowLatticeComparison : WindowLatticeComparison := by
  intro r a m
  let toStable (L : WindowLattice r a m) : StableSubspaces r a m :=
    ⟨latticeSubspace a m L.val, latticeSubspace_stable a m L.val⟩
  have hb : Function.Bijective toStable := by
    constructor
    · intro L L' h
      apply Subtype.ext
      apply Subtype.ext
      apply Submodule.restrictScalars_injective ℂ O (Coordinates r)
      rw [← windowInverseImage_latticeSubspace L, ← windowInverseImage_latticeSubspace L']
      exact congrArg (fun p : StableSubspaces r a m ↦ windowInverseImage p.val) h
    · intro P
      let f := (scalarLattice r a).val.subtype
      let q := windowProjection r a m
      let Q := (liftStableSubspace P).comap q
      let S := Q.map f
      have hhi : S ≤ (scalarLattice r a).val := by
        rintro _ ⟨y, _, rfl⟩
        exact y.property
      have hlo : (scalarLattice r (a + (m : ℤ))).val ≤ S := by
        intro y hy
        have hy' : y ∈ (scalarLattice r a).val := scalarLattice_add_nat_le r a m hy
        refine ⟨⟨y, hy'⟩, ?_, rfl⟩
        have hmem : (⟨y, hy'⟩ : (scalarLattice r a).val) ∈ windowLower r a m := hy
        have hker : q.ker = windowLower r a m := windowProjection_ker r a m
        rw [← hker, LinearMap.mem_ker] at hmem
        change q ⟨y, hy'⟩ ∈ liftStableSubspace P
        rw [hmem]
        exact (liftStableSubspace P).zero_mem
      refine ⟨⟨latticeOfBetween S hlo hhi, hlo, hhi⟩, Subtype.ext ?_⟩
      have hq : Q.map q = liftStableSubspace P := by
        have htop : q.range = ⊤ := windowProjection_range r a m
        exact Submodule.map_comap_eq_self (htop ▸ le_top)
      change (((S.comap f).map q).restrictScalars ℂ) = P.val
      have hf : Function.Injective f := (scalarLattice r a).val.injective_subtype
      change ((((Q.map f).comap f).map q).restrictScalars ℂ) = _
      rw [Submodule.comap_map_eq_of_injective hf, hq]
      rfl
  let e := Equiv.ofBijective toStable hb
  refine ⟨e, fun _ ↦ rfl, fun P ↦ ?_⟩
  simp only [← windowInverseImage_latticeSubspace (e.symm P),
    show latticeSubspace a m (e.symm P).val = P.val from
      congrArg Subtype.val (e.apply_symm_apply P)]

private theorem windowStageSubspace_finrank {r : ℕ} {a : ℤ} {m : ℕ}
    (p : WindowStage r a m) : Module.finrank ℂ (windowStageSubspace p) = p.1.val :=
  grassmannianSubspace_finrank (windowBasis r a m) (windowDimension_le p.1) p.2.val

private theorem windowStageSubspace_injective (r : ℕ) (a : ℤ) (m : ℕ) :
    Function.Injective (windowStageSubspace (r := r) (a := a) (m := m)) := by
  rintro ⟨d,p⟩ ⟨d',p'⟩ h
  have hd : d = d' := Fin.ext (calc
    d.val = Module.finrank ℂ (windowStageSubspace (⟨d,p⟩ : WindowStage r a m)) :=
      (windowStageSubspace_finrank ⟨d,p⟩).symm
    _ = Module.finrank ℂ (windowStageSubspace (⟨d',p'⟩ : WindowStage r a m)) :=
      congrArg (fun P : Submodule ℂ (Window r a m) ↦ Module.finrank ℂ P) h
    _ = d'.val := windowStageSubspace_finrank ⟨d',p'⟩)
  subst d'
  have hp := grassmannianSubspace_injective (windowBasis r a m) (windowDimension_le d) h
  have he : p = p' := Subtype.ext hp
  subst p'
  rfl

private theorem windowStagePoint_subspace {r : ℕ} (a : ℤ) (m : ℕ) (L : Lattice r) :
    windowStageSubspace (windowStagePoint a m L) = latticeSubspace a m L :=
  subspacePoint_subspace _ _ _ rfl

theorem windowStageComparison : WindowStageComparison := by
  intro r a m
  obtain ⟨e,he,-⟩ := windowLatticeComparison r a m
  refine ⟨⟨?_,?_⟩, fun L ↦ windowStagePoint_subspace a m L.val⟩
  · intro L L' h
    apply e.injective
    apply Subtype.ext
    change windowStagePoint a m L.val = windowStagePoint a m L'.val at h
    rw [he, he, ← windowStagePoint_subspace, ← windowStagePoint_subspace, h]
  · intro p
    let P : StableSubspaces r a m := ⟨windowStageSubspace p, p.2.property⟩
    refine ⟨e.symm P, windowStageSubspace_injective r a m ?_⟩
    rw [windowStagePoint_subspace, ← he]
    exact congrArg Subtype.val (e.apply_symm_apply P)

set_option maxHeartbeats 450000 in
set_option backward.isDefEq.respectTransparency false in
theorem boundedStageComparison : BoundedStageComparison := by
  intro r N
  have h := windowStageComparison r (-(N : ℤ)) (2*N)
  let i : BoundedLattice r N ≃ WindowLattice r (-(N : ℤ)) (2*N) :=
    (Equiv.refl (Lattice r)).subtypeEquiv (fun L ↦ by
      change _ ↔ (scalarLattice r (-(N : ℤ) + ((2*N : ℕ) : ℤ))).val ≤ L.val ∧ _
      rw [boundedExponent]
      rfl)
  refine ⟨?_, fun L ↦ windowStagePoint_subspace _ _ L.val⟩
  have hg : Function.Bijective (fun L : WindowLattice r (-(N : ℤ)) (2*N) ↦
    windowStagePoint (-(N : ℤ)) (2*N) L.val) := h.1
  constructor
  · intro L L' hL
    exact i.injective (hg.1 hL)
  · intro p
    obtain ⟨L, hL⟩ := hg.2 p
    refine ⟨i.symm L, ?_⟩
    have h' := congrArg (fun L : WindowLattice r (-(N : ℤ)) (2*N) ↦
      windowStagePoint (-(N : ℤ)) (2*N) L.val) (i.apply_symm_apply L)
    exact h'.trans hL

theorem windowSchemeComparison : WindowSchemeComparison := by
  intro r a m d
  let b := windowBasis r a m
  let hd := windowDimension_le d
  let T := windowOperator r a m
  let X := (grassmannianCharts b hd).scheme
  let Y := windowStableScheme r a m d
  let S := {p : GrassmannianPoints b hd | StablePlane b hd T p}
  have hred : IsReduced Y.left := LatticeModels.reducedClosure_reduced X S
  have hcl : IsClosedImmersion (windowSchemeInGrassmannian r a m d).left := by
    change IsClosedImmersion (reducedClosureIdeal X S).subschemeι
    infer_instance
  refine ⟨hred, hcl, ?_⟩
  obtain ⟨el, hel, -⟩ := windowLatticeComparison r a m
  obtain ⟨ep, hep⟩ := LatticeModels.stableSchemePointComparison b hd T
  let el' := el.subtypeEquiv (p := fun L ↦ Module.finrank ℂ (latticeSubspace a m L.val) = d.val)
    (q := fun P ↦ Module.finrank ℂ P.val = d.val) (fun L ↦ by rw [hel])
  let f (p : StablePoints b hd T) : {P : StableSubspaces r a m // Module.finrank ℂ P.val = d.val} :=
    ⟨⟨grassmannianSubspace b hd p.val, p.property⟩, grassmannianSubspace_finrank b hd p.val⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p q h
      apply Subtype.ext
      exact grassmannianSubspace_injective b hd (congrArg (fun P ↦ P.val.val) h)
    · intro P
      let p := subspacePoint b hd P.val.val P.property
      have hp : grassmannianSubspace b hd p = P.val.val := subspacePoint_subspace _ _ _ _
      have hs : StablePlane b hd T p := by
        unfold StablePlane
        rw [hp]
        exact P.val.property
      exact ⟨⟨p, hs⟩, Subtype.ext (Subtype.ext hp)⟩
  let ef := Equiv.ofBijective f hf
  refine ⟨ep.trans (ef.trans el'.symm), fun q ↦ ?_⟩
  have h := el'.apply_symm_apply (ef (ep q))
  change windowSchemeSubspace q = latticeSubspace a m (el'.symm (ef (ep q))).val.val
  rw [← hel]
  change windowSchemeSubspace q = (el' (el'.symm (ef (ep q)))).val.val
  rw [h]
  change grassmannianSubspace b hd (q ≫ windowSchemeInGrassmannian r a m d) =
    grassmannianSubspace b hd (ep q).val
  exact congrArg (grassmannianSubspace b hd) (hep q).symm

private def stageSubspaceEquiv (r : ℕ) (a : ℤ) (m : ℕ) :
    WindowStage r a m ≃ StableSubspaces r a m :=
  Equiv.ofBijective (fun p ↦ ⟨windowStageSubspace p, p.2.property⟩) (by
    constructor
    · intro p q h
      exact windowStageSubspace_injective r a m (congrArg Subtype.val h)
    · obtain ⟨e, he, -⟩ := windowLatticeComparison r a m
      intro P
      refine ⟨windowStagePoint a m (e.symm P).val, Subtype.ext ?_⟩
      change windowStageSubspace (windowStagePoint a m (e.symm P).val) = P.val
      rw [windowStagePoint_subspace, ← he]
      exact congrArg Subtype.val (e.apply_symm_apply P))

private theorem windowJetLinear_coords {r m n : ℕ} (a : ℤ) (hmn : m ≤ n)
    (M : Matrix (Fin r) (Fin r) (JetRing n)) (x : Window r a m) :
    windowJets r a m (windowJetLinear a hmn M x) =
      M.map (truncateJet hmn) *ᵥ (windowJets r a m x) := by
  let e := (windowJets r a m).restrictScalars ℂ
  exact e.apply_symm_apply _

private theorem windowJetLinear_one {r m n : ℕ} (a : ℤ) (hmn : m ≤ n) :
    windowJetLinear a hmn (1 : Matrix (Fin r) (Fin r) (JetRing n)) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply (windowJets r a m).injective
  rw [windowJetLinear_coords, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  rfl

private theorem windowJetLinear_mul {r m n : ℕ} (a : ℤ) (hmn : m ≤ n)
    (A B : Matrix (Fin r) (Fin r) (JetRing n)) :
    windowJetLinear a hmn (A * B) =
      (windowJetLinear a hmn A).comp (windowJetLinear a hmn B) := by
  apply LinearMap.ext
  intro x
  apply (windowJets r a m).injective
  simp only [LinearMap.comp_apply, windowJetLinear_coords, Matrix.map_mul, Matrix.mulVec_mulVec]

private theorem windowJetLinear_comm {r m n : ℕ} (a : ℤ) (hmn : m ≤ n)
    (A : Matrix (Fin r) (Fin r) (JetRing n)) (x : Window r a m) :
    windowOperator r a m (windowJetLinear a hmn A x) =
      windowJetLinear a hmn A (windowOperator r a m x) := by
  apply (windowJets r a m).injective
  change windowJets r a m (t • windowJetLinear a hmn A x) =
    windowJets r a m (windowJetLinear a hmn A (t • x))
  simp only [windowJetLinear_coords, map_smul, Matrix.mulVec_smul]

@[instance_reducible] private def windowJetAct (r : ℕ) (a : ℤ) (m n : ℕ) (hn : 1 ≤ n) (hmn : m ≤ n) :
    MulAction (GLJets r n hn) (WindowStage r a m) := by
  let e := stageSubspaceEquiv r a m
  let f (g : GLJets r n hn) (p : WindowStage r a m) : StableSubspaces r a m :=
    ⟨(windowStageSubspace p).map (windowJetLinear a hmn g.val), by
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rw [windowJetLinear_comm]
      exact ⟨windowOperator r a m x, p.2.property ⟨x, hx, rfl⟩, rfl⟩⟩
  have h (g) (p) : windowStageSubspace (e.symm (f g p)) = (f g p).val :=
    congrArg Subtype.val (e.apply_symm_apply (f g p))
  refine { smul := fun g p ↦ e.symm (f g p), one_smul := ?_, mul_smul := ?_ }
  · intro g k p
    apply windowStageSubspace_injective r a m
    change windowStageSubspace (e.symm (f (g*k) p)) =
      windowStageSubspace (e.symm (f g (e.symm (f k p))))
    rw [h, h]
    change (windowStageSubspace p).map (windowJetLinear a hmn (g.val * k.val)) =
      (windowStageSubspace (e.symm (f k p))).map (windowJetLinear a hmn g.val)
    rw [h, windowJetLinear_mul, Submodule.map_comp]
  · intro p
    apply windowStageSubspace_injective r a m
    change windowStageSubspace (e.symm (f 1 p)) = windowStageSubspace p
    rw [h]
    change (windowStageSubspace p).map (windowJetLinear a hmn 1) = _
    rw [windowJetLinear_one, Submodule.map_id]

private theorem windowJetAct_subspace {r m n : ℕ} (a : ℤ) (hn : 1 ≤ n) (hmn : m ≤ n)
    (g : GLJets r n hn) (p : WindowStage r a m) :
    windowStageSubspace ((windowJetAct r a m n hn hmn).smul g p) =
      (windowStageSubspace p).map (windowJetLinear a hmn g.val) := by
  exact congrArg Subtype.val ((stageSubspaceEquiv r a m).apply_symm_apply _)

private theorem shiftedInclusion_positive {r : ℕ} (a : ℤ) (g : GL (Fin r) O)
    (x : Fin r → O) :
    loopLinearEquiv r (positiveGLMap r g) (shiftedInclusion r a x) =
      shiftedInclusion r a (g.val *ᵥ x) := by
  change loopLinearEquiv r (positiveGLMap r g) (monomial a • coordinateInclusion r x) =
    monomial a • coordinateInclusion r (g.val *ᵥ x)
  rw [map_smul, positiveGLMap_linear]

set_option backward.isDefEq.respectTransparency false in
private theorem windowJets_projection {r m : ℕ} {a : ℤ} (x : (scalarLattice r a).val) :
    windowJets r a m (windowProjection r a m x) = windowReduction r a m x := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem windowJet_reduced_map_projection {r m n : ℕ} (a : ℤ) (hn : 1 ≤ n) (hmn : m ≤ n)
    (g : GL (Fin r) O) (x : Fin r → O) :
    windowJetLinear a hmn (reduceGL r n hn g).val
        (windowProjection r a m (shiftedCoordinates r a x)) =
      windowProjection r a m (shiftedCoordinates r a (g.val *ᵥ x)) := by
  apply (windowJets r a m).injective
  rw [windowJetLinear_coords, windowJets_projection, windowJets_projection]
  have hred (u : Fin r → O) :
      windowReduction r a m (shiftedCoordinates r a u) = fun i ↦ jetReduction m (u i) := by
    funext i
    change jetReduction m ((shiftedCoordinates r a).symm (shiftedCoordinates r a u) i) = _
    rw [LinearEquiv.symm_apply_apply]
  rw [hred, hred]
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
  rfl

set_option maxHeartbeats 550000 in
set_option backward.isDefEq.respectTransparency false in
private theorem latticeSubspace_positive {r m n : ℕ} (a : ℤ) (hn : 1 ≤ n) (hmn : m ≤ n)
    (g : GL (Fin r) O) (L : Lattice r) :
    (latticeSubspace a m L).map (windowJetLinear a hmn (reduceGL r n hn g).val) =
      latticeSubspace a m (positiveGLMap r g • L) := by
  let Q := windowProjection r a m
  let f := (scalarLattice r a).val.subtype
  let F := ((loopLinearEquiv r (positiveGLMap r g)).restrictScalars O).toLinearMap
  let T := windowJetLinear a hmn (reduceGL r n hn g).val
  have happly (x : Fin r → O) :
      T (Q (shiftedCoordinates r a x)) = Q (shiftedCoordinates r a (g.val *ᵥ x)) :=
    windowJet_reduced_map_projection a hn hmn g x
  have hF (x : Fin r → O) :
      F (f (shiftedCoordinates r a x)) = f (shiftedCoordinates r a (g.val *ᵥ x)) :=
    shiftedInclusion_positive a g x
  have hupper {v : Coordinates r} (h : F v ∈ (scalarLattice r a).val) :
      v ∈ (scalarLattice r a).val := by
    have hinv : loopLinearEquiv r (positiveGLMap r g⁻¹) =
      (loopLinearEquiv r (positiveGLMap r g)).symm := by rw [map_inv, map_inv]; rfl
    have h' : v ∈ (positiveGLMap r g⁻¹ • scalarLattice r a).val := by
      refine ⟨F v, h, ?_⟩
      change loopLinearEquiv r (positiveGLMap r g⁻¹)
        (loopLinearEquiv r (positiveGLMap r g) v) = v
      rw [hinv, LinearEquiv.symm_apply_apply]
    rwa [positiveGL_preserves_scalar] at h'
  change (((L.val.comap f).map Q).restrictScalars ℂ).map T = _
  refine le_antisymm ?_ ?_
  · rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    obtain ⟨x, rfl⟩ := (shiftedCoordinates r a).surjective v
    rw [happly]
    refine ⟨shiftedCoordinates r a (g.val *ᵥ x), ?_, rfl⟩
    exact ⟨f (shiftedCoordinates r a x), hv, hF x⟩
  · rintro _ ⟨w, ⟨v, hv, he⟩, rfl⟩
    change F v = f w at he
    have hv' : v ∈ (scalarLattice r a).val := hupper (he.symm ▸ w.property)
    obtain ⟨x, hx⟩ := (shiftedCoordinates r a).surjective ⟨v, hv'⟩
    have hfx : f (shiftedCoordinates r a x) = v := congrArg f hx
    have hw : shiftedCoordinates r a (g.val *ᵥ x) = w := by
      apply Subtype.ext
      change f (shiftedCoordinates r a (g.val *ᵥ x)) = f w
      rw [← hF, hfx, he]
    refine ⟨Q (shiftedCoordinates r a x), ⟨shiftedCoordinates r a x, ?_, rfl⟩, ?_⟩
    · change f (shiftedCoordinates r a x) ∈ L.val
      rwa [hfx]
    · rw [happly, hw]

private theorem windowJetAct_positive {r m n : ℕ} (a : ℤ) (hn : 1 ≤ n) (hmn : m ≤ n)
    (g : GL (Fin r) O) (L : Lattice r) :
    (windowJetAct r a m n hn hmn).smul (reduceGL r n hn g) (windowStagePoint a m L) =
      windowStagePoint a m (positiveGLMap r g • L) := by
  apply windowStageSubspace_injective r a m
  rw [windowJetAct_subspace, windowStagePoint_subspace, windowStagePoint_subspace]
  exact latticeSubspace_positive a hn hmn g L

section GraphCoordinates

variable {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}

private def pivotBlock (J : Pivot ι d) (B : Matrix ι (Inside J) ℂ) :
    Matrix (Inside J) (Inside J) ℂ :=
  B.submatrix Subtype.val id

private def normalizedGraph (J : Pivot ι d) (B : Matrix ι (Inside J) ℂ) :
    Matrix (Outside J) (Inside J) ℂ :=
  B.submatrix Subtype.val id * (pivotBlock J B)⁻¹

omit [Fintype ι] in
private theorem normalizedGraph_range (J : Pivot ι d) (B : Matrix ι (Inside J) ℂ)
    (h : IsUnit (pivotBlock J B).det) :
    (graphMatrix J (normalizedGraph J B)).mulVecLin.range = B.mulVecLin.range := by
  classical
  let C := pivotBlock J B
  have hmul : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv _ h
  have hG : graphMatrix J (normalizedGraph J B) = B * C⁻¹ := by
    apply Matrix.ext
    intro i j
    by_cases hi : i ∈ J.val
    · have hentry := congrFun (congrFun hmul (⟨i,hi⟩ : Inside J)) j
      change (graphMatrix J (normalizedGraph J B)) i j = (C * C⁻¹) ⟨i,hi⟩ j
      rw [hentry]
      simp [graphMatrix, hi, Matrix.one_apply, Subtype.ext_iff]
    · simp only [graphMatrix, Matrix.of_apply, dite_eq_right hi, normalizedGraph, C]
      rfl
  have hs : Function.Surjective C⁻¹.mulVecLin := by
    intro x
    refine ⟨C *ᵥ x, ?_⟩
    change C⁻¹ *ᵥ (C *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec]
  rw [hG, Matrix.mulVecLin_mul, LinearMap.range_comp, LinearMap.range_eq_top.mpr hs,
    Submodule.map_top]

omit [Fintype ι] in
private theorem pivotBlock_unit_of_range (J : Pivot ι d) (B : Matrix ι (Inside J) ℂ)
    (A : Matrix (Outside J) (Inside J) ℂ)
    (h : B.mulVecLin.range = (graphMatrix J A).mulVecLin.range) :
    IsUnit (pivotBlock J B).det := by
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_surjective_iff_isUnit.mp
  intro x
  have hx : (graphMatrix J A) *ᵥ x ∈ B.mulVecLin.range :=
    h.symm ▸ LinearMap.mem_range_self (graphMatrix J A).mulVecLin x
  obtain ⟨y, hy⟩ := hx
  refine ⟨y, funext fun i ↦ ?_⟩
  change (B *ᵥ y) i.val = x i
  change B *ᵥ y = graphMatrix J A *ᵥ x at hy
  rw [hy, graphMatrix_inside]

omit [Fintype ι] [DecidableEq ι] in
private theorem range_reindexColumns {σ τ : Type} [Fintype σ] [Fintype τ]
    (B : Matrix ι σ ℂ) (e : τ ≃ σ) :
    (B.submatrix id e).mulVecLin.range = B.mulVecLin.range := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨x ∘ e.symm, (Matrix.submatrix_mulVec_equiv B x id e).symm⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨x ∘ e, ?_⟩
    change (B.submatrix id e) *ᵥ (x ∘ e) = _
    rw [Matrix.submatrix_mulVec_equiv]
    simp [Function.comp_def]

private def pivotIndexEquiv (I J : Pivot ι d) : Inside J ≃ Inside I :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_coe, Fintype.card_coe, I.property, J.property])

private theorem analyticAt_matrixDet {E σ : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Fintype σ] [DecidableEq σ] {x : E} {B : E → Matrix σ σ ℂ}
    (h : ∀ i j, AnalyticAt ℂ (fun z ↦ B z i j) x) :
    AnalyticAt ℂ (fun z ↦ (B z).det) x := by
  simp only [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro σ _
  refine analyticAt_const.mul (Finset.analyticAt_fun_prod _ ?_)
  intro i _
  exact h _ _

private theorem analyticAt_normalizedGraph {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : Pivot ι d) {x : E} {B : E → Matrix ι (Inside J) ℂ}
    (h : ∀ i j, AnalyticAt ℂ (fun z ↦ B z i j) x)
    (hdet : (pivotBlock J (B x)).det ≠ 0) :
    AnalyticAt ℂ (fun z ↦ normalizedGraph J (B z)) x := by
  classical
  let C (z : E) := pivotBlock J (B z)
  have hc (i j : Inside J) : AnalyticAt ℂ (fun z ↦ C z i j) x := h i.val j
  have hi (i j : Inside J) : AnalyticAt ℂ (fun z ↦ (C z)⁻¹ i j) x := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
      Matrix.adjugate_apply]
    refine ((analyticAt_matrixDet hc).inv hdet).mul (analyticAt_matrixDet ?_)
    intro u v
    by_cases huv : u = j
    · subst u
      simpa using (analyticAt_const (𝕜 := ℂ) (x := x) (v := (Pi.single i (1 : ℂ) : Inside J → ℂ) v))
    · simpa [Matrix.updateRow_ne huv] using hc u v
  change AnalyticAt ℂ (fun z (i : Outside J) (j : Inside J) ↦ normalizedGraph J (B z) i j) x
  refine analyticAt_pi_iff.mpr (fun i ↦ analyticAt_pi_iff.mpr (fun j ↦ ?_))
  simp only [normalizedGraph, Matrix.mul_apply]
  apply Finset.analyticAt_fun_sum
  intro l _
  exact (h i.val l).mul (hi l j)

private theorem analyticAt_graphEntry (I : Pivot ι d) (i : ι) (j : Inside I)
    (x : Matrix (Outside I) (Inside I) ℂ) :
    AnalyticAt ℂ (fun z : Matrix (Outside I) (Inside I) ℂ ↦ graphMatrix I z i j) x := by
  by_cases hi : i ∈ I.val
  · simp only [graphMatrix, Matrix.of_apply, dite_eq_left hi]
    exact analyticAt_const
  · simp only [graphMatrix, Matrix.of_apply, dite_eq_right hi]
    let f : Matrix (Outside I) (Inside I) ℂ →ₗ[ℂ] ℂ :=
      Matrix.entryLinearMap ℂ ℂ ⟨i,hi⟩ j
    exact f.toContinuousLinearMap.analyticAt x

private theorem analyticAt_matrixMulEntry {E σ τ ω : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [Fintype τ] {x : E} {A : E → Matrix σ τ ℂ} {B : E → Matrix τ ω ℂ}
    {i : σ} {j : ω} (hA : ∀ k, AnalyticAt ℂ (fun z ↦ A z i k) x)
    (hB : ∀ k, AnalyticAt ℂ (fun z ↦ B z k j) x) :
    AnalyticAt ℂ (fun z ↦ (A z * B z) i j) x := by
  simp only [Matrix.mul_apply]
  exact Finset.analyticAt_fun_sum _ (fun k _ ↦ (hA k).mul (hB k))

end GraphCoordinates

private def truncateJetAlg {m n : ℕ} (hmn : m ≤ n) : JetRing n →ₐ[ℂ] JetRing m :=
  { truncateJet hmn with commutes' := fun _ ↦ rfl }

private def jetWindowVector {r m n : ℕ} (a : ℤ) (hmn : m ≤ n) (x : Window r a m) :
    JetMatrixCoefficients r n →ₗ[ℂ] Window r a m :=
  let e := (windowJets r a m).restrictScalars ℂ
  let f := (truncateJetAlg hmn).toLinearMap.comp (jetCoefficients n).symm.toLinearMap
  e.symm.toLinearMap.comp
    ((LinearMap.applyₗ (R := ℂ) (e x)).comp ((Matrix.mulVecBilin ℂ ℂ).comp f.mapMatrix))

private def jetWindowEntry {r m n : ℕ} (a : ℤ) (hmn : m ≤ n) (i j : WindowIndex r m) :
    JetMatrixCoefficients r n →ₗ[ℂ] ℂ :=
  let e := (windowBasis r a m).equivFun
  (LinearMap.proj i).comp (e.toLinearMap.comp (jetWindowVector a hmn (e.symm (Pi.single j 1))))

private def jetWindowCoordMatrix {r m n : ℕ} (a : ℤ) (hmn : m ≤ n)
    (B : JetMatrixCoefficients r n) : Matrix (WindowIndex r m) (WindowIndex r m) ℂ :=
  Matrix.of (fun i j ↦ jetWindowEntry a hmn i j B)

private theorem analyticAt_jetWindowEntry {r m n : ℕ} (a : ℤ) (hmn : m ≤ n)
    (B : JetMatrixCoefficients r n) (i j : WindowIndex r m) :
    AnalyticAt ℂ (fun C ↦ jetWindowCoordMatrix a hmn C i j) B :=
  (jetWindowEntry a hmn i j).toContinuousLinearMap.analyticAt B

set_option maxRecDepth 1600 in
private theorem jetWindowEntry_eq {r m n : ℕ} (a : ℤ) (hmn : m ≤ n)
    (C : JetMatrixCoefficients r n) (i j : WindowIndex r m) :
    jetWindowEntry a hmn i j C = operatorInCoordinates (windowBasis r a m)
      (windowJetLinear a hmn (C.map (jetCoefficients n).symm)) i j := rfl

private theorem jetWindowCoordMatrix_coefficients {r m n : ℕ} (a : ℤ) (hmn : m ≤ n)
    (G : Matrix (Fin r) (Fin r) (JetRing n)) :
    jetWindowCoordMatrix a hmn (jetMatrixCoefficients G) =
      operatorInCoordinates (windowBasis r a m) (windowJetLinear a hmn G) := by
  have hG : (jetMatrixCoefficients G).map (jetCoefficients n).symm = G := by
    apply Matrix.ext
    intro i j
    exact (jetCoefficients n).symm_apply_apply (G i j)
  apply Matrix.ext
  intro i j
  change jetWindowEntry a hmn i j (jetMatrixCoefficients G) = _
  rw [jetWindowEntry_eq, hG]

private theorem windowJetLinear_injective {r m n : ℕ} (a : ℤ) (hn : 1 ≤ n) (hmn : m ≤ n)
    (G : GLJets r n hn) : Function.Injective (windowJetLinear a hmn G.val) := by
  have h : (windowJetLinear a hmn (G⁻¹ : GLJets r n hn).val).comp (windowJetLinear a hmn G.val)
      = (LinearMap.id : Window r a m →ₗ[ℂ] _) := by
    rw [← windowJetLinear_mul,
      show (G⁻¹ : GLJets r n hn).val * G.val = 1 from G.inv_val, windowJetLinear_one]
  intro x y hxy
  exact (DFunLike.congr_fun h x).symm.trans
    ((congrArg (windowJetLinear a hmn (G⁻¹ : GLJets r n hn).val) hxy).trans
      (DFunLike.congr_fun h y))

private theorem chartSubspace_map_coordinates {V ι : Type} [AddCommGroup V] [Module ℂ V]
    [Fintype ι] [DecidableEq ι] (b : Basis ι ℂ V) {d : ℕ} (hd : d ≤ Module.finrank ℂ V)
    (I : Pivot ι d) (A : Matrix (Outside I) (Inside I) ℂ) (T : V →ₗ[ℂ] V) :
    ((grassmannianSubspace b hd (grassmannianChartPoint b hd I A)).map T).map
        b.equivFun.toLinearMap = ((operatorInCoordinates b T) * graphMatrix I A).mulVecLin.range := by
  let e := b.equivFun
  let T' := e.toLinearMap.comp (T.comp e.symm.toLinearMap)
  have h : e.toLinearMap.comp T = T'.comp e.toLinearMap := by
    ext x
    exact congrArg (fun y ↦ e (T y) _) (e.symm_apply_apply x).symm
  rw [← Submodule.map_comp, h, Submodule.map_comp]
  rw [show (grassmannianSubspace b hd (grassmannianChartPoint b hd I A)).map e.toLinearMap =
      (graphMatrix I A).mulVecLin.range from grassmannianChartSubspace b hd I A]
  rw [Matrix.mulVecLin_mul, LinearMap.range_comp]
  congr 1
  change T' = Matrix.toLin' (LinearMap.toMatrix' T')
  rw [Matrix.toLin'_toMatrix']

private theorem analyticAt_pivotDet {ι E : Type} [DecidableEq ι] [NormedAddCommGroup E]
    [NormedSpace ℂ E] {d : ℕ} (J : Pivot ι d) {x : E} {B : E → Matrix ι (Inside J) ℂ}
    (h : ∀ i j, AnalyticAt ℂ (fun z ↦ B z i j) x) :
    AnalyticAt ℂ (fun z ↦ (pivotBlock J (B z)).det) x :=
  analyticAt_matrixDet (B := fun z ↦ pivotBlock J (B z)) (fun i j ↦ h i.val j)

section AnalyticGraphAction

variable {V ι G E : Type} [AddCommGroup V] [Module ℂ V] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem analyticGraphAction (b : Basis ι ℂ V) {d : ℕ} (hd : d ≤ Module.finrank ℂ V)
    (D : G → V →ₗ[ℂ] V) (hD : ∀ g, Function.Injective (D g))
    (v : G → E) (M : E → Matrix ι ι ℂ) (hM : ∀ g, M (v g) = operatorInCoordinates b (D g))
    (hentry : ∀ x i j, AnalyticAt ℂ (fun y ↦ M y i j) x)
    (I : Pivot ι d) (g : G) (A : Matrix (Outside I) (Inside I) ℂ) :
    ∃ (J : Pivot ι d) (U : Set (E × Matrix (Outside I) (Inside I) ℂ))
      (F : E × Matrix (Outside I) (Inside I) ℂ → Matrix (Outside J) (Inside J) ℂ),
      (v g, A) ∈ U ∧ IsOpen U ∧ AnalyticOnNhd ℂ F U ∧
      ∀ (h : G) (C : Matrix (Outside I) (Inside I) ℂ), (v h, C) ∈ U →
        (grassmannianSubspace b hd (grassmannianChartPoint b hd I C)).map (D h) =
          grassmannianSubspace b hd (grassmannianChartPoint b hd J (F (v h, C))) := by
  let P := grassmannianSubspace b hd (grassmannianChartPoint b hd I A)
  have hdim : Module.finrank ℂ (P.map (D g)) = d :=
    (P.equivMapOfInjective (D g) (hD g)).finrank_eq.symm.trans
      (grassmannianSubspace_finrank b hd _)
  let p := subspacePoint b hd (P.map (D g)) hdim
  obtain ⟨J, A', hJ⟩ := grassmannianChartPoint_cover b hd p
  let f (z : E × Matrix (Outside I) (Inside I) ℂ) : Matrix ι (Inside J) ℂ :=
    (M z.1 * graphMatrix I z.2).submatrix id (pivotIndexEquiv I J)
  have hf (z : E × Matrix (Outside I) (Inside I) ℂ)
      (i : ι) (j : Inside J) : AnalyticAt ℂ (fun y ↦ f y i j) z :=
    analyticAt_matrixMulEntry (A := fun y : E × Matrix (Outside I) (Inside I) ℂ ↦ M y.1)
      (B := fun y : E × Matrix (Outside I) (Inside I) ℂ ↦ graphMatrix I y.2)
      (i := i) (j := pivotIndexEquiv I J j)
      (fun k ↦ (hentry z.1 i k).comp analyticAt_fst)
      (fun k ↦ (analyticAt_graphEntry I k (pivotIndexEquiv I J j) z.2).comp analyticAt_snd)
  have hmap (h : G) (C : Matrix (Outside I) (Inside I) ℂ) :
      ((grassmannianSubspace b hd (grassmannianChartPoint b hd I C)).map (D h)).map
          b.equivFun.toLinearMap = (f (v h, C)).mulVecLin.range := by
    rw [chartSubspace_map_coordinates]
    dsimp only [f]
    rw [range_reindexColumns, hM]
  let U := {z | (pivotBlock J (f z)).det ≠ 0}
  have hu : IsOpen U := isOpen_ne_fun
    (continuous_iff_continuousAt.mpr (fun z ↦ (analyticAt_pivotDet J (B := f) (hf z)).continuousAt))
    continuous_const
  refine ⟨J, U, fun z ↦ normalizedGraph J (f z), ?_, hu,
    fun z hz ↦ analyticAt_normalizedGraph J (B := f) (hf z) hz, ?_⟩
  · change (pivotBlock J (f (v g, A))).det ≠ 0
    apply IsUnit.ne_zero
    apply pivotBlock_unit_of_range J _ A'
    have hchart : (grassmannianSubspace b hd (grassmannianChartPoint b hd J A')).map
        b.equivFun.toLinearMap = (graphMatrix J A').mulVecLin.range :=
      grassmannianChartSubspace b hd J A'
    rw [← hmap, ← hchart, hJ, subspacePoint_subspace]
  · intro h C hz
    apply Submodule.map_injective_of_injective b.equivFun.injective
    rw [hmap, grassmannianChartSubspace b hd J]
    exact (normalizedGraph_range J _ (isUnit_iff_ne_zero.mpr hz)).symm

end AnalyticGraphAction

set_option maxHeartbeats 1000000 in
theorem glJetChartAnalytic : GLJetChartAnalytic := by
  intro r a m n hn hmn d I g A
  exact analyticGraphAction (E := JetMatrixCoefficients r n) (G := GLJets r n hn)
    (windowBasis r a m) (windowDimension_le d)
    (fun g ↦ windowJetLinear a hmn g.val) (windowJetLinear_injective a hn hmn)
    (fun g ↦ jetMatrixCoefficients g.val) (jetWindowCoordMatrix a hmn)
    (fun g ↦ jetWindowCoordMatrix_coefficients a hmn g.val) (analyticAt_jetWindowEntry a hmn)
    I g A

section AnalyticTopology

variable {V ι : Type} [AddCommGroup V] [Module ℂ V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℂ V) {d : ℕ} (hd : d ≤ Module.finrank ℂ V)

private theorem grassmannianChart_continuous (I : Pivot ι d) :
    Continuous (grassmannianChartPoint b hd I) := by
  change Continuous[_, ⨆ J : Pivot ι d, coinduced (grassmannianChartPoint b hd J) inferInstance] _
  exact continuous_iSup_rng (i := I) continuous_coinduced_rng

private theorem grassmannianChart_injective (I : Pivot ι d) :
    Function.Injective (grassmannianChartPoint b hd I) := by
  intro A B h
  apply (chartMatrixEquiv I complexAlgebra).symm.injective
  apply Over.OverMorphism.ext
  let j := (grassmannianCharts b hd).chart I
  let : IsOpenImmersion j.left := (grassmannianCharts b hd).openChart I
  apply (cancel_mono j.left).mp
  exact congrArg (fun p : GrassmannianPoints b hd ↦ p.left) h

private theorem grassmannianChart_isOpenEmbedding (I : Pivot ι d) :
    Topology.IsOpenEmbedding (grassmannianChartPoint b hd I) := by
  refine .of_continuous_injective_isOpenMap (grassmannianChart_continuous b hd I)
    (grassmannianChart_injective b hd I) ?_
  intro U hU
  change @IsOpen _ (⨆ J : Pivot ι d, coinduced (grassmannianChartPoint b hd J) inferInstance) _
  rw [isOpen_iSup_iff]
  intro J
  rw [isOpen_coinduced]
  let f (A : Matrix (Outside J) (Inside J) ℂ) := (graphMatrix J A).submatrix id (pivotIndexEquiv J I)
  let F (A : Matrix (Outside J) (Inside J) ℂ) := normalizedGraph I (f A)
  let D : Set (Matrix (Outside J) (Inside J) ℂ) := {A | (pivotBlock I (f A)).det ≠ 0}
  have hf (A) (i : ι) (j : Inside I) : AnalyticAt ℂ (fun B ↦ f B i j) A :=
    analyticAt_graphEntry J i (pivotIndexEquiv J I j) A
  have hD : IsOpen D := isOpen_ne_fun (continuous_iff_continuousAt.mpr (fun A ↦
    (analyticAt_pivotDet I (B := f) (hf A)).continuousAt)) continuous_const
  have hrange (A) :
      (grassmannianSubspace b hd (grassmannianChartPoint b hd J A)).map b.equivFun.toLinearMap =
        (f A).mulVecLin.range := by
    rw [grassmannianChartSubspace b hd J]
    exact (range_reindexColumns (graphMatrix J A) (pivotIndexEquiv J I)).symm
  have hnorm (A) (hA : A ∈ D) :
      grassmannianChartPoint b hd I (F A) = grassmannianChartPoint b hd J A := by
    apply grassmannianSubspace_injective b hd
    apply Submodule.map_injective_of_injective b.equivFun.injective
    rw [hrange, grassmannianChartSubspace b hd I]
    exact normalizedGraph_range I (f A) (isUnit_iff_ne_zero.mpr hA)
  have heq : grassmannianChartPoint b hd J ⁻¹' (grassmannianChartPoint b hd I '' U) =
      D ∩ F ⁻¹' U := by
    ext A
    constructor
    · rintro ⟨B, hB, hAB⟩
      have hA : A ∈ D := by
        apply IsUnit.ne_zero
        apply pivotBlock_unit_of_range I (f A) B
        rw [← hrange, ← hAB, grassmannianChartSubspace b hd I]
        rfl
      have hFB : F A = B := grassmannianChart_injective b hd I ((hnorm A hA).trans hAB.symm)
      refine ⟨hA, ?_⟩
      change F A ∈ U
      rwa [hFB]
    · rintro ⟨hA, hFA⟩
      exact ⟨F A, hFA, hnorm A hA⟩
  rw [heq]
  refine isOpen_iff_mem_nhds.2 (fun A hA ↦ inter_mem (hD.mem_nhds hA.1) ?_)
  exact (analyticAt_normalizedGraph I (hf A) hA.1).continuousAt (hU.mem_nhds hA.2)

end AnalyticTopology

private def jetGrassmannianAct {r m n : ℕ} (a : ℤ) (hn : 1 ≤ n) (hmn : m ≤ n)
    (d : WindowDimension r a m) (g : GLJets r n hn) (p : WindowPoints r a m d) :
    WindowPoints r a m d :=
  let b := windowBasis r a m
  let hd := windowDimension_le d
  let P := grassmannianSubspace b hd p
  let T := windowJetLinear a hmn g.val
  subspacePoint b hd (P.map T) ((P.equivMapOfInjective T
    (windowJetLinear_injective a hn hmn g)).finrank_eq.symm.trans
      (grassmannianSubspace_finrank b hd p))

private theorem jetGrassmannianAct_subspace {r m n : ℕ} (a : ℤ) (hn : 1 ≤ n) (hmn : m ≤ n)
    (d : WindowDimension r a m) (g : GLJets r n hn) (p : WindowPoints r a m d) :
    grassmannianSubspace (windowBasis r a m) (windowDimension_le d)
        (jetGrassmannianAct a hn hmn d g p) =
      (grassmannianSubspace (windowBasis r a m) (windowDimension_le d) p).map
        (windowJetLinear a hmn g.val) :=
  subspacePoint_subspace _ _ _ _

private theorem jetMatrixCoefficients_continuous (r n : ℕ) (hn : 1 ≤ n) :
    Continuous (fun g : GLJets r n hn ↦ jetMatrixCoefficients g.val) := by
  have hv : Continuous (fun g : GLJets r n hn ↦ g.val) := continuous_induced_dom
  exact hv.matrix_map continuous_induced_dom

set_option maxHeartbeats 650000 in
set_option maxRecDepth 1400 in
set_option backward.isDefEq.respectTransparency false in
private theorem jetGrassmannianAct_continuous {r m n : ℕ} (a : ℤ) (hn : 1 ≤ n) (hmn : m ≤ n)
    (d : WindowDimension r a m) :
    Continuous (fun z : GLJets r n hn × WindowPoints r a m d ↦
      jetGrassmannianAct a hn hmn d z.1 z.2) := by
  let b := windowBasis r a m
  let hd := windowDimension_le d
  refine continuous_iff_continuousAt.2 ?_
  rintro ⟨g,p⟩
  obtain ⟨I,A,rfl⟩ := grassmannianChartPoint_cover b hd p
  let G : GLJets r n hn × WindowPoints r a m d → WindowPoints r a m d :=
    fun z ↦ jetGrassmannianAct a hn hmn d z.1 z.2
  let e : GLJets r n hn × Matrix (Outside I) (Inside I) ℂ →
      GLJets r n hn × WindowPoints r a m d := Prod.map id (grassmannianChartPoint b hd I)
  have he : Topology.IsOpenEmbedding e :=
    Topology.IsOpenEmbedding.id.prodMap (grassmannianChart_isOpenEmbedding b hd I)
  change ContinuousAt G (e (g,A))
  apply (he.continuousAt_iff (g := G)).mp
  obtain ⟨J,U,F,h0,hU,hF,hact⟩ := glJetChartAnalytic r a m n hn hmn d I g A
  let K (z : GLJets r n hn × Matrix (Outside I) (Inside I) ℂ) :=
    (jetMatrixCoefficients z.1.val, z.2)
  have hK : Continuous K :=
    ((jetMatrixCoefficients_continuous r n hn).comp continuous_fst).prodMk continuous_snd
  have hFK : ContinuousAt F (K (g,A)) := (hF _ h0).continuousAt
  have hKAt : ContinuousAt K (g,A) := hK.continuousAt
  have hc : ContinuousAt (fun z ↦ grassmannianChartPoint b hd J (F (K z))) (g,A) :=
    (grassmannianChart_continuous b hd J).continuousAt.comp (hFK.comp hKAt)
  refine hc.congr ?_
  filter_upwards [hK.continuousAt (hU.mem_nhds h0)] with z hz
  apply grassmannianSubspace_injective b hd
  change grassmannianSubspace b hd (grassmannianChartPoint b hd J (F (K z))) =
    grassmannianSubspace b hd (jetGrassmannianAct a hn hmn d z.1 (grassmannianChartPoint b hd I z.2))
  rw [jetGrassmannianAct_subspace]
  exact (hact z.1 z.2 hz).symm

private def jetStableAct {r m n : ℕ} (a : ℤ) (hn : 1 ≤ n) (hmn : m ≤ n)
    (d : WindowDimension r a m) (g : GLJets r n hn)
    (p : StablePoints (windowBasis r a m) (windowDimension_le d) (windowOperator r a m)) :
    StablePoints (windowBasis r a m) (windowDimension_le d) (windowOperator r a m) :=
  ⟨jetGrassmannianAct a hn hmn d g p.val, by
    unfold StablePlane
    rw [jetGrassmannianAct_subspace]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [windowJetLinear_comm]
    exact ⟨_, p.property ⟨x,hx,rfl⟩, rfl⟩⟩

private theorem continuous_sigma_action {G D : Type} {β : D → Type} [TopologicalSpace G]
    [∀ d, TopologicalSpace (β d)] (f : ∀ d, G × β d → β d)
    (hf : ∀ d, Continuous (f d)) :
    Continuous (fun z : G × Sigma β ↦ (⟨z.2.1, f z.2.1 (z.1,z.2.2)⟩ : Sigma β)) := by
  refine continuous_iff_continuousAt.2 ?_
  rintro ⟨g,d,p⟩
  let F (z : G × Sigma β) : Sigma β := ⟨z.2.1, f z.2.1 (z.1,z.2.2)⟩
  let e : G × β d → G × Sigma β := Prod.map id (Sigma.mk d)
  have he : Topology.IsOpenEmbedding e :=
    Topology.IsOpenEmbedding.id.prodMap Topology.IsOpenEmbedding.sigmaMk
  change ContinuousAt F (e (g,p))
  apply (he.continuousAt_iff (g := F)).mp
  exact (continuous_sigmaMk.comp (hf d)).continuousAt

set_option maxHeartbeats 500000 in
private theorem jetStableAct_continuous {r m n : ℕ} (a : ℤ) (hn : 1 ≤ n) (hmn : m ≤ n)
    (d : WindowDimension r a m) :
    Continuous (fun z : GLJets r n hn × StablePoints (windowBasis r a m)
        (windowDimension_le d) (windowOperator r a m) ↦ jetStableAct a hn hmn d z.1 z.2) := by
  let β := StablePoints (windowBasis r a m) (windowDimension_le d) (windowOperator r a m)
  let f (z : GLJets r n hn × β) : β := jetStableAct a hn hmn d z.1 z.2
  let g (z : GLJets r n hn × β) : GLJets r n hn × WindowPoints r a m d := (z.1,z.2.val)
  have hval : Continuous (fun p : β ↦ (p.val : WindowPoints r a m d)) := continuous_induced_dom
  have hg : Continuous g := continuous_fst.prodMk (hval.comp continuous_snd)
  let F (z : GLJets r n hn × WindowPoints r a m d) : WindowPoints r a m d :=
    jetGrassmannianAct a hn hmn d z.1 z.2
  have hF : Continuous F := jetGrassmannianAct_continuous a hn hmn d
  have hcomp : Continuous (F ∘ g) := hF.comp hg
  have heq : (fun z ↦ (f z).val) = F ∘ g := rfl
  exact (continuous_induced_rng (f := fun p : β ↦ p.val)).2 (heq.symm ▸ hcomp)

set_option maxHeartbeats 650000 in
set_option backward.isDefEq.respectTransparency false in
private theorem windowJetAct_continuous {r m n : ℕ} (a : ℤ) (hn : 1 ≤ n) (hmn : m ≤ n) :
    Continuous (fun z : GLJets r n hn × WindowStage r a m ↦
      (windowJetAct r a m n hn hmn).smul z.1 z.2) := by
  let β (d : WindowDimension r a m) :=
    StablePoints (windowBasis r a m) (windowDimension_le d) (windowOperator r a m)
  let ρ := windowJetAct r a m n hn hmn
  let f (d : WindowDimension r a m) (z : GLJets r n hn × β d) : β d :=
    jetStableAct a hn hmn d z.1 z.2
  have hc := @continuous_sigma_action (GLJets r n hn) (WindowDimension r a m) β
    (glJetTopology r n hn) (fun d ↦ stablePointsTopology (windowBasis r a m)
      (windowDimension_le d) (windowOperator r a m)) f (jetStableAct_continuous a hn hmn)
  have heq (g : GLJets r n hn) (d : WindowDimension r a m) (p : β d) :
      ρ.smul g ⟨d,p⟩ = ⟨d,f d (g,p)⟩ := by
    apply windowStageSubspace_injective r a m
    change windowStageSubspace (ρ.smul g ⟨d,p⟩) =
      grassmannianSubspace _ _ (jetGrassmannianAct a hn hmn d g p.val)
    rw [windowJetAct_subspace, jetGrassmannianAct_subspace]
    rfl
  have h : (fun z : GLJets r n hn × WindowStage r a m ↦ ρ.smul z.1 z.2) =
      (fun z : GLJets r n hn × Sigma β ↦ (⟨z.2.1, f z.2.1 (z.1,z.2.2)⟩ : Sigma β)) :=
    funext (fun ⟨g,d,p⟩ ↦ heq g d p)
  change Continuous (fun z : GLJets r n hn × WindowStage r a m ↦ ρ.smul z.1 z.2)
  rw [h]
  exact hc

theorem glJetAction : GLJetAction := by
  intro r a m n hn hmn
  exact ⟨windowJetAct r a m n hn hmn, windowJetAct_subspace a hn hmn,
    windowJetAct_positive a hn hmn, windowJetAct_continuous a hn hmn⟩

private theorem oneByOne_reduce (n : ℕ) (hn : 1 ≤ n) (u : Oˣ) :
    oneByOne (JetRing n) (Units.map (jetReduction n).toMonoidHom u) =
      reduceGL 1 n hn (oneByOne O u) := by
  apply Units.ext
  rw [oneByOne_val]
  change Matrix.diagonal (fun _ : Fin 1 ↦ jetReduction n u.val) =
    (oneByOne O u).val.map (jetReduction n)
  rw [oneByOne_val, Matrix.diagonal_map (map_zero (jetReduction n))]

private theorem scalarJet_preserves {r m n : ℕ} {a : ℤ} (hmn : m ≤ n)
    (b : JetRing n) (p : WindowStage r a m) :
    (windowStageSubspace p).map (windowJetLinear a hmn (Matrix.diagonal fun _ : Fin r ↦ b)) ≤
      windowStageSubspace p := by
  obtain ⟨u,hu⟩ := Ideal.Quotient.mk_surjective b
  have hb : truncateJet hmn b = jetReduction m u := by
    rw [← hu]
    rfl
  have h (x : Window r a m) :
      windowJetLinear a hmn (Matrix.diagonal fun _ : Fin r ↦ b) x = u • x := by
    apply (windowJets r a m).injective
    rw [windowJetLinear_coords, Matrix.diagonal_map (map_zero (truncateJet hmn)), map_smul]
    funext i
    change ((Matrix.diagonal fun _ : Fin r ↦ truncateJet hmn b) *ᵥ (windowJets r a m x)) i =
      jetReduction m u * windowJets r a m x i
    rw [hb]
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  rintro _ ⟨x,hx,rfl⟩
  rw [h]
  exact windowSubspace_smul_mem ⟨windowStageSubspace p,p.2.property⟩ u hx

private theorem scalarJetUnit_fixes {m n : ℕ} {a : ℤ} (hn : 1 ≤ n) (hmn : m ≤ n)
    (b : (JetRing n)ˣ) (p : WindowStage 1 a m) :
    (windowStageSubspace p).map (windowJetLinear a hmn (Matrix.diagonal fun _ : Fin 1 ↦ b.val)) =
      windowStageSubspace p := by
  let g : GLJets 1 n hn := oneByOne (JetRing n) b
  let ρ := windowJetAct 1 a m n hn hmn
  have hp : windowStageSubspace (ρ.smul g⁻¹ p) ≤ windowStageSubspace p := by
    rw [windowJetAct_subspace]
    have hval : (g⁻¹ : GLJets 1 n hn).val = Matrix.diagonal (fun _ : Fin 1 ↦ (b⁻¹).val) :=
      congrArg Units.val (map_inv (oneByOne (JetRing n)) b).symm |>.trans (oneByOne_val b⁻¹)
    rw [hval]
    exact scalarJet_preserves hmn (b⁻¹).val p
  refine le_antisymm (scalarJet_preserves hmn b.val p) ?_
  have h := Submodule.map_mono (f := windowJetLinear a hmn g.val) hp
  rw [← windowJetAct_subspace] at h
  have hfix : ρ.smul g (ρ.smul g⁻¹ p) = p := by
    calc
      _ = ρ.smul (g * g⁻¹) p := (ρ.mul_smul g g⁻¹ p).symm
      _ = p := by rw [mul_inv_cancel]; exact ρ.one_smul p
  have hfix' := congrArg windowStageSubspace hfix
  rw [hfix'] at h
  change _ ≤ (windowStageSubspace p).map (windowJetLinear a hmn (oneByOne (JetRing n) b).val) at h
  rwa [oneByOne_val] at h

set_option maxHeartbeats 500000 in
theorem torusJetAction : TorusJetAction := by
  intro r N n hn hmn
  let a := -(N : ℤ)
  let ρ : MulAction (TorusJets r n hn) (Fin r → BoundedStage 1 N) :=
    { smul := fun _ p ↦ p, one_smul := fun _ ↦ rfl, mul_smul := fun _ _ _ ↦ rfl }
  refine ⟨ρ, fun g p i ↦ (scalarJetUnit_fixes hn hmn (g i) (p i)).symm, ?_, continuous_snd⟩
  intro g L
  funext i
  change windowStagePoint a (2*N) (L i) =
    windowStagePoint a (2*N) ((positiveTorusMap r g • L) i)
  rw [torus_smul_coordinate]
  change _ = windowStagePoint a (2*N)
    (oneByOne K (Units.map inclusion.toMonoidHom (g i)) • L i)
  rw [oneByOne_positive, ← windowJetAct_positive a hn hmn, ← oneByOne_reduce n hn]
  apply windowStageSubspace_injective 1 a (2*N)
  rw [windowJetAct_subspace, oneByOne_val, scalarJetUnit_fixes hn hmn]

section StageInclusions

private abbrev StageDimension (V : Type) [AddCommGroup V] [Module ℂ V] :=
  Fin (Module.finrank ℂ V + 1)

private theorem stageDimension_le {V : Type} [AddCommGroup V] [Module ℂ V]
    (d : StageDimension V) : d.val ≤ Module.finrank ℂ V :=
  Nat.lt_succ_iff.mp d.isLt

section Incidence

variable {U W A C ι κ : Type}
  [AddCommGroup U] [Module ℂ U] [Module.Finite ℂ U]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup A] [Module ℂ A] [Module.Finite ℂ A]
  [AddCommGroup C] [Module ℂ C] [Module.Finite ℂ C]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

private abbrev StableStage {V σ : Type} [AddCommGroup V] [Module ℂ V]
    [Fintype σ] [DecidableEq σ] (b : Basis σ ℂ V) (T : V →ₗ[ℂ] V) :=
  Σ d : StageDimension V, StablePoints b (stageDimension_le d) T

private abbrev stableStageTopology {V σ : Type} [AddCommGroup V] [Module ℂ V]
    [Fintype σ] [DecidableEq σ] (b : Basis σ ℂ V) (T : V →ₗ[ℂ] V) :
    TopologicalSpace (StableStage b T) :=
  @instTopologicalSpaceSigma _ _ fun d ↦ stablePointsTopology b (stageDimension_le d) T

private def stableStagePlane {V σ : Type} [AddCommGroup V] [Module ℂ V]
    [Fintype σ] [DecidableEq σ] (b : Basis σ ℂ V) (T : V →ₗ[ℂ] V)
    (p : StableStage b T) : Submodule ℂ V :=
  grassmannianSubspace b (stageDimension_le p.1) p.2.val

private def stableSchemePlane {V σ : Type} [AddCommGroup V] [Module ℂ V]
    [Fintype σ] [DecidableEq σ] (b : Basis σ ℂ V) {d : ℕ} (hd : d ≤ Module.finrank ℂ V)
    (T : V →ₗ[ℂ] V) (p : Points (stableScheme b hd T) complexAlgebra) : Submodule ℂ V :=
  grassmannianSubspace b hd (p ≫ reducedClosureInclusion _ {q | StablePlane b hd T q})

/-- An incidence map on each dimension restricts to the stable locus if its
point formula sends the quotient of each lattice to the quotient of the same lattice. -/
private theorem stableIncidenceComponent (e : W ≃ₗ[ℂ] U × (A × C))
    (bu : Basis ι ℂ U) (bw : Basis κ ℂ W) (Tu : U →ₗ[ℂ] U) (Tw : W →ₗ[ℂ] W)
    {L : Type} (P : L → Submodule ℂ U) (Q : L → Submodule ℂ W)
    (hcoord : ∀ l w, w ∈ Q l ↔ (e w).1 ∈ P l ∧ (e w).2.2 = 0)
    (hstable : ∀ l, (Q l).map Tw ≤ Q l)
    {d : ℕ} (hd : d ≤ Module.finrank ℂ U)
    (hsource : ∀ p : StablePoints bu hd Tu, ∃ l, grassmannianSubspace bu hd p.val = P l) :
    let hw := GrassmannianIncidenceSpecs.incidenceDimension_le e hd
    (∃ i : stableScheme bu hd Tu ⟶ stableScheme bw hw Tw, IsClosedImmersion i.left ∧
      ∀ (l : L) (p : Points (stableScheme bu hd Tu) complexAlgebra),
        stableSchemePlane bu hd Tu p = P l → stableSchemePlane bw hw Tw (p ≫ i) = Q l) ∧
    (∃ f : StablePoints bu hd Tu → StablePoints bw hw Tw, Topology.IsClosedEmbedding f ∧
      ∀ (l : L) (p : StablePoints bu hd Tu),
        grassmannianSubspace bu hd p.val = P l → grassmannianSubspace bw hw (f p).val = Q l) := by
  dsimp only
  let hw := GrassmannianIncidenceSpecs.incidenceDimension_le e hd
  obtain ⟨j, hj, hjformula⟩ := GrassmannianIncidenceSchemes.grassmannianIncidence e bu bw hd
  have hmap (l : L) (p : GrassmannianPoints bu hd)
      (hp : grassmannianSubspace bu hd p = P l) :
      grassmannianSubspace bw hw (p ≫ j) = Q l := by
    ext w
    exact (hjformula p w).trans (by rw [hp]; exact (hcoord l w).symm)
  have hst : Set.MapsTo (fun p : GrassmannianPoints bu hd ↦ p ≫ j)
      {p | StablePlane bu hd Tu p} {p | StablePlane bw hw Tw p} := by
    intro p hp
    obtain ⟨l, hl⟩ := hsource ⟨p, hp⟩
    change StablePlane bw hw Tw (p ≫ j)
    unfold StablePlane
    rw [hmap l p hl]
    exact hstable l
  constructor
  · obtain ⟨i, hi, hcomm⟩ := GrassmannianIncidenceSchemes.reducedClosureIncidence j _ _ hj hst
    refine ⟨i, hi, fun l p hp ↦ ?_⟩
    let iu := reducedClosureInclusion (grassmannianCharts bu hd).scheme {q | StablePlane bu hd Tu q}
    let iw := reducedClosureInclusion (grassmannianCharts bw hw).scheme {q | StablePlane bw hw Tw q}
    have hcomp : (p ≫ i) ≫ iw = (p ≫ iu) ≫ j :=
      (Category.assoc p i iw).trans
        ((congrArg (fun t ↦ p ≫ t) hcomm).trans (Category.assoc p iu j).symm)
    exact (congrArg (grassmannianSubspace bw hw) hcomp).trans (hmap l (p ≫ iu) hp)
  · have hc := (GrassmannianIncidenceTopology.incidenceClosedEmbedding bu bw e hd hw rfl
      (fun p ↦ p ≫ j) hjformula).1
    exact ⟨Set.MapsTo.restrict _ _ _ hst,
      GrassmannianIncidenceTopology.restrictClosedEmbedding hc
        (LatticeModels.isClosed_stablePlanes bu hd Tu) hst,
      fun l p hp ↦ hmap l p.val hp⟩

private theorem stableStageIncidence (e : W ≃ₗ[ℂ] U × (A × C))
    (bu : Basis ι ℂ U) (bw : Basis κ ℂ W) (Tu : U →ₗ[ℂ] U) (Tw : W →ₗ[ℂ] W)
    {L : Type} (P : L → Submodule ℂ U) (Q : L → Submodule ℂ W) (offset : ℕ)
    (hdim : Module.finrank ℂ A = offset)
    (hcoord : ∀ l w, w ∈ Q l ↔ (e w).1 ∈ P l ∧ (e w).2.2 = 0)
    (hstable : ∀ l, (Q l).map Tw ≤ Q l)
    (hsource : ∀ p : StableStage bu Tu, ∃ l, stableStagePlane bu Tu p = P l) :
    (∀ d : StageDimension U, ∃ d' : StageDimension W,
      d'.val = d.val + offset ∧
      ∃ i : stableScheme bu (stageDimension_le d) Tu ⟶ stableScheme bw (stageDimension_le d') Tw,
        IsClosedImmersion i.left ∧
        ∀ (l : L) (p : Points (stableScheme bu (stageDimension_le d) Tu) complexAlgebra),
          stableSchemePlane bu (stageDimension_le d) Tu p = P l →
            stableSchemePlane bw (stageDimension_le d') Tw (p ≫ i) = Q l) ∧
    (∃ f : StableStage bu Tu → StableStage bw Tw,
      @Topology.IsClosedEmbedding _ _ (stableStageTopology bu Tu) (stableStageTopology bw Tw) f ∧
      ∀ (l : L) (p : StableStage bu Tu),
        stableStagePlane bu Tu p = P l → stableStagePlane bw Tw (f p) = Q l) := by
  let shift (d : StageDimension U) : StageDimension W :=
    ⟨d.val + Module.finrank ℂ A, Nat.lt_succ_iff.mpr
      (GrassmannianIncidenceSpecs.incidenceDimension_le e (stageDimension_le d))⟩
  have hc (d : StageDimension U) := stableIncidenceComponent e bu bw Tu Tw P Q hcoord
    hstable (stageDimension_le d) (fun p ↦ hsource ⟨d, p⟩)
  refine ⟨fun d ↦ ⟨shift d, congrArg (d.val + ·) hdim, (hc d).1⟩, ?_⟩
  choose f hf using fun d ↦ (hc d).2
  have hshift : Function.Injective shift := by
    intro d d' h
    exact Fin.ext (Nat.add_right_cancel (congrArg Fin.val h))
  refine ⟨Sigma.map shift f, ?_, ?_⟩
  · exact @GrassmannianIncidenceTopology.sigmaClosedEmbedding _ _ _ _
      (fun d ↦ stablePointsTopology bu (stageDimension_le d) Tu)
      (fun d ↦ stablePointsTopology bw (stageDimension_le d) Tw)
      shift f hshift (fun d ↦ (hf d).1)
  · rintro l ⟨d, p⟩ hp
    exact (hf d).2 l p hp

end Incidence

private theorem windowPoint_has_lattice {r : ℕ} {a : ℤ} {m : ℕ} (p : WindowStage r a m) :
    ∃ L : WindowLattice r a m, windowStageSubspace p = latticeSubspace a m L.val := by
  obtain ⟨L, hL⟩ := (windowStageComparison r a m).1.surjective p
  exact ⟨L, (congrArg windowStageSubspace hL).symm.trans (windowStagePoint_subspace a m L.val)⟩

private theorem windowIncidence (r : ℕ) (a b : ℤ) (m k : ℕ)
    (hba : b ≤ a) (hend : a + (m : ℤ) ≤ b + (k : ℤ)) :
    (∀ d : WindowDimension r a m, ∃ d' : WindowDimension r b k,
      d'.val = d.val + r * (b + (k : ℤ) - (a + (m : ℤ))).toNat ∧
      ∃ i : windowStableScheme r a m d ⟶ windowStableScheme r b k d',
        IsClosedImmersion i.left ∧
        ∀ (L : WindowLattice r a m) (q : Points (windowStableScheme r a m d) complexAlgebra),
          windowSchemeSubspace q = latticeSubspace a m L.val →
            windowSchemeSubspace (q ≫ i) = latticeSubspace b k L.val) ∧
    (∃ f : WindowStage r a m → WindowStage r b k, Topology.IsClosedEmbedding f ∧
      ∀ (L : WindowLattice r a m) (p : WindowStage r a m),
        windowStageSubspace p = latticeSubspace a m L.val →
          windowStageSubspace (f p) = latticeSubspace b k L.val) := by
  obtain ⟨e, he, hdim, -⟩ :=
    LatticeWindowInclusionCoordinates.windowInclusionCoordinates r a b m k hba hend
  exact stableStageIncidence e (windowBasis r a m) (windowBasis r b k)
    (windowOperator r a m) (windowOperator r b k)
    (fun L : WindowLattice r a m ↦ latticeSubspace a m L.val)
    (fun L : WindowLattice r a m ↦ latticeSubspace b k L.val)
    _ hdim (fun L ↦ he L.val L.property.1 L.property.2)
    (fun L ↦ latticeSubspace_stable b k L.val) windowPoint_has_lattice

theorem windowInclusions : WindowInclusions := by
  intro r a b m k hba hend
  exact (windowIncidence r a b m k hba hend).1

private theorem windowStageInclusion (r : ℕ) (a b : ℤ) (m k : ℕ)
    (hba : b ≤ a) (hend : a + (m : ℤ) ≤ b + (k : ℤ)) :
    ∃ f : WindowStage r a m → WindowStage r b k,
      Topology.IsClosedEmbedding f ∧
      ∀ L : WindowLattice r a m, f (windowStagePoint a m L.val) = windowStagePoint b k L.val := by
  obtain ⟨f, hf, hmap⟩ := (windowIncidence r a b m k hba hend).2
  refine ⟨f, hf, fun L ↦ windowStageSubspace_injective r b k ?_⟩
  exact (hmap L (windowStagePoint a m L.val) (windowStagePoint_subspace a m L.val)).trans
    (windowStagePoint_subspace b k L.val).symm

private theorem boundedPoint_closedEmbedding (r N : ℕ) :
    Topology.IsClosedEmbedding (boundedPoint (r := r) (N := N)) := by
  have h := (boundedStageComparison r N).1
  exact ⟨⟨⟨rfl⟩, h.injective⟩, h.surjective.range_eq ▸ isClosed_univ⟩

set_option backward.isDefEq.respectTransparency false in
theorem boundedInclusionTopology : BoundedInclusionTopology := by
  intro r N M h
  obtain ⟨f, hf, hpoints⟩ := windowStageInclusion r (-(N : ℤ)) (-(M : ℤ)) (2*N) (2*M)
    (by omega) (by rw [boundedExponent, boundedExponent]; exact_mod_cast h)
  apply Topology.IsClosedEmbedding.of_comp (boundedPoint_closedEmbedding r M).isEmbedding
  have hcomp : (boundedPoint (r := r) (N := M)) ∘ boundedInclusion h =
      f ∘ (boundedPoint (r := r) (N := N)) := by
    funext L
    let L' : WindowLattice r (-(N : ℤ)) (2*N) :=
      ⟨L.val, by rw [boundedExponent]; exact L.property.1, L.property.2⟩
    exact (hpoints L').symm
  rw [hcomp]
  exact hf.comp (boundedPoint_closedEmbedding r N)

end StageInclusions

end

end RepTheorySurvey.Geometric.BoundedLattices
