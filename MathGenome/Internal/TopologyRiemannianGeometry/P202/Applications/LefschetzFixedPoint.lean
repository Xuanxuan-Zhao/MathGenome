import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.SimplicialRelativeParametrizations
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Applications.LefschetzFixedPoint
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Applications.LefschetzTrace
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SimplicialApproximation
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.OrientedSimplicialAlgebra
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.PrismHomotopy
import Mathlib.Topology.Order.Compact

import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.SimplicialComparison
/-! Conditional T35 derivation. No unproved comparison
implementation is imported. The comparison is an explicit proof argument in
the lemmas which need it. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory HomologicalComplex
open scoped BigOperators
universe u v w

namespace P202.LefschetzFixedPoint
attribute [local instance] P202Specs.OrientedSimplicialAlgebra.vertexOrder
open P202.Cellular P202.Cellular.AbstractSimplicialComplex
open P202Specs.LefschetzFixedPoint

/-- Finiteness uses the actual simplex sets, and permits an infinite ambient
vertex type with only finitely many active simplices. -/
theorem finite_oriented_simplex {V : Type w} (K : AbstractSimplicialComplex V)
    (hK : K.IsFinite) (n : ℕ) :
    Finite (P202Specs.OrientedSimplicialAlgebra.Simplex K n) := by
  classical
  let : Finite K.Simplex := hK.to_subtype
  apply Finite.of_injective
    (fun s : P202Specs.OrientedSimplicialAlgebra.Simplex K n =>
      (⟨Finset.univ.image s.1, s.2⟩ : K.Simplex))
  intro a b hab
  apply (P202Specs.OrientedSimplicialAlgebra.simplexEquiv K n).injective
  apply Subtype.ext
  exact congrArg (fun s : K.Simplex => s.1) hab

theorem finite_oriented_chains {V : Type w} (K : AbstractSimplicialComplex V)
    (hK : K.IsFinite) (R : Type u) [Field R] (A : Type v)
    [AddCommGroup A] [Module R A] [FiniteDimensional R A] (n : ℕ) :
    FiniteDimensional R (P202Specs.OrientedSimplicialAlgebra.Chains K A n) := by
  let := finite_oriented_simplex K hK n
  infer_instance

/-- The categorical homology is a quotient of a subspace of the middle term.
This works for any complex shape, including degree zero of an ordinary complex. -/
theorem finite_homology_of_finite_chain {R : Type u} [Field R] {ι : Type*}
    {c : ComplexShape ι} (C : HomologicalComplex (ModuleCat.{v} R) c)
    (n : ι) [FiniteDimensional R (C.X n)] :
    FiniteDimensional R (C.homology n) := by
  let : FiniteDimensional R (C.sc n).X₂ := inferInstanceAs (FiniteDimensional R (C.X n))
  have : FiniteDimensional R (C.sc n).moduleCatLeftHomologyData.H := by
    change FiniteDimensional R (_ ⧸ _)
    infer_instance
  let e := (C.sc n).moduleCatHomologyIso.toLinearEquiv
  exact Module.Finite.of_injective e.toLinearMap e.injective

theorem homology_subsingleton_of_chain_subsingleton {R : Type u} [Ring R]
    {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{v} R) c) (n : ι)
    [Subsingleton (C.X n)] : Subsingleton (C.homology n) := by
  let : Subsingleton (C.sc n).X₂ := inferInstanceAs (Subsingleton (C.X n))
  exact ModuleCat.subsingleton_of_isZero
    ((C.sc n).isZero_homology_of_isZero_X₂ (ModuleCat.isZero_of_subsingleton _))

theorem no_oriented_simplex_above_bound {V : Type w}
    (K : AbstractSimplicialComplex V) (D : ℕ)
    (hD : ∀ s : K.Simplex, s.1.card ≤ D) (n : ℕ) (hn : D ≤ n) :
    IsEmpty (P202Specs.OrientedSimplicialAlgebra.Simplex K n) := by
  classical
  refine ⟨fun s => ?_⟩
  have h := hD ⟨Finset.univ.image s.1, s.2⟩
  rw [Finset.card_image_of_injective _ s.1.injective,
    Finset.card_univ, Fintype.card_fin] at h
  omega

theorem oriented_homology_finiteness {V : Type w}
    (K : AbstractSimplicialComplex V) (hK : K.IsFinite)
    (R : Type u) [Field R] (A : Type v) [AddCommGroup A]
    [Module R A] [FiniteDimensional R A] :
    (∀ n, FiniteDimensional R
      ((P202Specs.OrientedSimplicialAlgebra.complex R A (K := K)).homology n)) ∧
    ∃ D : ℕ, ∀ n, D ≤ n → Subsingleton
      ((P202Specs.OrientedSimplicialAlgebra.complex R A (K := K)).homology n) := by
  constructor
  · intro n
    let : FiniteDimensional R ((P202Specs.OrientedSimplicialAlgebra.complex R A (K := K)).X n) :=
      finite_oriented_chains K hK R A n
    exact finite_homology_of_finite_chain _ n
  · obtain ⟨D, hD⟩ := P202.Topology.finite_complex_simplex_card_bound K hK
    refine ⟨D, fun n hn => ?_⟩
    let := no_oriented_simplex_above_bound K D (hD 0) n hn
    let : Subsingleton ((P202Specs.OrientedSimplicialAlgebra.complex R A (K := K)).X n) :=
      inferInstanceAs (Subsingleton (P202Specs.OrientedSimplicialAlgebra.Chains K A n))
    exact homology_subsingleton_of_chain_subsingleton _ n

/-- Only the absolute part of the specified comparison is needed here. -/
theorem realization_homology_finiteness
    (comparison : P202Specs.SimplicialComparison.simplicialComparison_type.{u,v,w})
    {V : Type w} (K : AbstractSimplicialComplex V) (hK : K.IsFinite)
    (R : Type u) [Field R] (A : Type v) [AddCommGroup A]
    [Module R A] [FiniteDimensional R A] :
    (∀ n, FiniteDimensional R
      ((P202Specs.SingularChains.complex R A (TopCat.of K.Realization)).homology n)) ∧
    ∃ D : ℕ, ∀ n, D ≤ n → Subsingleton
      ((P202Specs.SingularChains.complex R A (TopCat.of K.Realization)).homology n) := by
  obtain ⟨F, hF, _⟩ := comparison R A K
    (P202Specs.RelativeParametrizations.Simplicial.Subcomplex.empty K)
  obtain ⟨hfin, D, hD⟩ := oriented_homology_finiteness K hK R A
  constructor
  · intro n
    let := hfin n
    let := hF n
    let e := (asIso (homologyMap F.absolute n)).toLinearEquiv
    exact Module.Finite.of_surjective e.toLinearMap e.surjective
  · refine ⟨D, fun n hn => ?_⟩
    let := hD n hn
    let := hF n
    exact (asIso (homologyMap F.absolute n)).toLinearEquiv.symm.injective.subsingleton

/-- Singular homology transport uses the same singular chain functor as the
comparison, so there is no change of homology theories in passing to a model. -/
def homologyEquivOfHomeomorph (R : Type u) [CommRing R] (A : Type v)
    [AddCommGroup A] [Module R A] {X Y : TopCat.{w}} (h : X ≃ₜ Y) (n : ℕ) :
    (P202Specs.SingularChains.complex R A X).homology n ≃ₗ[R]
      (P202Specs.SingularChains.complex R A Y).homology n :=
  ((P202Specs.SingularChains.chainFunctor R A ⋙
    HomologicalComplex.homologyFunctor _ _ n).mapIso (TopCat.isoOfHomeo h)).toLinearEquiv

theorem finite_polyhedron_homology_finiteness
    (comparison : P202Specs.SimplicialComparison.simplicialComparison_type.{u,v,w})
    (R : Type u) [Field R] (A : Type v) [AddCommGroup A] [Module R A]
    [FiniteDimensional R A] (X : TopCat.{w}) (hX : IsFinitePolyhedron X) :
    (∀ n, FiniteDimensional R ((P202Specs.SingularChains.complex R A X).homology n)) ∧
    ∃ N : ℕ, ∀ n, N ≤ n →
      Subsingleton ((P202Specs.SingularChains.complex R A X).homology n) := by
  obtain ⟨V, K, hK, ⟨h⟩⟩ := hX
  obtain ⟨hfin, D, hD⟩ := realization_homology_finiteness comparison K hK R A
  constructor
  · intro n
    let := hfin n
    let e := homologyEquivOfHomeomorph R A (X := X) (Y := TopCat.of K.Realization) h n
    exact Module.Finite.of_injective e.toLinearMap e.injective
  · refine ⟨D, fun n hn => ?_⟩
    let := hD n hn
    exact (homologyEquivOfHomeomorph R A (X := X)
      (Y := TopCat.of K.Realization) h n).injective.subsingleton

theorem rational_homology_finiteness_of_comparison
    (comparison : P202Specs.SimplicialComparison.simplicialComparison_type.{0,0,w}) :
    P202Specs.LefschetzFixedPoint.homologyFiniteness_type.{0,0,w} := by
  intro X hX
  exact finite_polyhedron_homology_finiteness comparison ℚ ℚ X hX

/-- One bound works for every self-map, not just for the particular map whose
fixed points are being considered. -/
theorem lefschetz_sum_of_bounded_homology {X : TopCat.{w}} (N : ℕ)
    (hN : ∀ n, N ≤ n → Subsingleton (rationalHomology X n)) (f : X ⟶ X) :
    Function.support (fun n : ℕ => (-1 : ℚ) ^ n *
      LinearMap.trace ℚ (rationalHomology X n) (rationalHomologyMap f n).hom)
        ⊆ ↑(Finset.range N) ∧
    lefschetzNumber f = ∑ n ∈ Finset.range N, (-1 : ℚ) ^ n *
      LinearMap.trace ℚ (rationalHomology X n) (rationalHomologyMap f n).hom := by
  have hs : Function.support (fun n : ℕ => (-1 : ℚ) ^ n *
      LinearMap.trace ℚ (rationalHomology X n) (rationalHomologyMap f n).hom)
        ⊆ ↑(Finset.range N) := by
    intro n hn
    change n ∈ Finset.range N
    rw [Finset.mem_range]
    by_contra hn'
    let := hN n (Nat.le_of_not_gt hn')
    have hz : (rationalHomologyMap f n).hom = 0 := Subsingleton.elim _ _
    simpa [Function.mem_support, hz] using hn
  exact ⟨hs, finsum_eq_sum_of_support_subset _ hs⟩

theorem lefschetz_sum_of_homology_finiteness
    (hfin : P202Specs.LefschetzFixedPoint.homologyFiniteness_type.{0,0,w}) :
    P202Specs.LefschetzFixedPoint.lefschetzSum_type.{0,0,w} := by
  intro X hX
  obtain ⟨_, N, hN⟩ := hfin X hX
  exact ⟨N, lefschetz_sum_of_bounded_homology N hN⟩

theorem rational_lefschetz_sum_of_comparison
    (comparison : P202Specs.SimplicialComparison.simplicialComparison_type.{0,0,w}) :
    P202Specs.LefschetzFixedPoint.lefschetzSum_type.{0,0,w} :=
  lefschetz_sum_of_homology_finiteness
    (rational_homology_finiteness_of_comparison comparison)

/-- On the empty space every chain group, including degree zero, vanishes. -/
theorem empty_rational_homology_subsingleton (X : TopCat.{w}) [IsEmpty X] (n : ℕ) :
    Subsingleton (rationalHomology X n) := by
  let : IsEmpty (P202Specs.SingularChains.Simplex X n) := ⟨fun s => by
    let t : Convexity.StdSimplex ℝ (Fin (n + 1)) := .single 0
    exact isEmptyElim ((P202Specs.SingularChains.simplexEquiv X n s) t)⟩
  let : Subsingleton ((P202Specs.SingularChains.complex ℚ ℚ X).X n) :=
    inferInstanceAs (Subsingleton (P202Specs.SingularChains.Chains ℚ X n))
  exact homology_subsingleton_of_chain_subsingleton _ n

theorem empty_lefschetz_number (X : TopCat.{w}) [IsEmpty X] (f : X ⟶ X) :
    lefschetzNumber f = 0 := by
  have h := (lefschetz_sum_of_bounded_homology 0
    (fun n _ => empty_rational_homology_subsingleton X n) f).2
  simpa using h

/-- A fixed-point-free map of a compact metric space has a uniform positive
displacement. The empty space is included by the extreme value theorem's
empty-set branch. -/
theorem positive_displacement {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : C(X, X)) (hf : ∀ x, f x ≠ x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, δ ≤ dist x (f x) := by
  obtain ⟨δ, hδ, h⟩ := isCompact_univ.exists_forall_le'
    (continuous_id.dist f.continuous).continuousOn
    (fun x _ => dist_pos.mpr (hf x).symm)
  exact ⟨δ, hδ, fun x => h x (Set.mem_univ x)⟩

/-- The numerical estimate in the source proof. It applies separately to each
subsimplex and does not assume the subsimplex has full dimension. -/
theorem image_disjoint_of_mesh_and_error {X : Type*} [PseudoMetricSpace X]
    (f g : X → X) (δ : ℝ) (hδ : 0 < δ)
    (hdisp : ∀ x, δ ≤ dist x (f x)) {s t : Set X} (hts : t ⊆ s)
    (hmesh : ∀ x ∈ s, ∀ y ∈ s, dist x y < δ / 3)
    (herror : ∀ x ∈ t, dist (g x) (f x) < δ / 3) :
    Disjoint (g '' t) s := by
  rw [Set.disjoint_left]
  rintro y ⟨x, hx, rfl⟩ hy
  have h₁ := hmesh x (hts hx) (g x) hy
  have h₂ := herror x hx
  have h₃ := dist_triangle x (g x) (f x)
  have h₄ := hdisp x
  linarith

/-- The same estimate for maps whose domain is a subdivision realization and
whose underlying point in the coarse realization is given by `h`. -/
theorem subdivision_image_disjoint_of_mesh_and_error
    {X Y : Type*} [PseudoMetricSpace X] (h : Y → X) (f : X → X) (g : Y → X)
    (δ : ℝ) (hδ : 0 < δ) (hdisp : ∀ x, δ ≤ dist x (f x))
    {s : Set X} {t : Set Y} (hts : h '' t ⊆ s)
    (hmesh : ∀ x ∈ s, ∀ y ∈ s, dist x y < δ / 3)
    (herror : ∀ x ∈ t, dist (g x) (f (h x)) < δ / 3) :
    Disjoint (g '' t) s := by
  rw [Set.disjoint_left]
  rintro y ⟨x, hx, rfl⟩ hy
  have h₁ := hmesh (h x) (hts ⟨x, hx, rfl⟩) (g x) hy
  have h₂ := herror x hx
  have h₃ := dist_triangle (h x) (g x) (f (h x))
  have h₄ := hdisp (h x)
  linarith

/-- In finite free chains, the simplex basis computes the trace by its actual
diagonal coefficients. -/
theorem trace_finsupp_zero_of_diagonal_zero {R : Type*} [CommRing R]
    {I : Type*} [Finite I] (F : (I →₀ R) →ₗ[R] (I →₀ R))
    (hF : ∀ i, F (Finsupp.single i 1) i = 0) :
    LinearMap.trace R (I →₀ R) F = 0 := by
  classical
  let : Fintype I := Fintype.ofFinite I
  rw [LinearMap.trace_eq_matrix_trace R Finsupp.basisSingleOne]
  exact Finset.sum_eq_zero (fun i _ => by simpa [LinearMap.toMatrix_apply] using hF i)

/-- A finite linear combination inherits a zero coefficient from all the
generators which occur in its support. This is the step used after applying
the subdivision operator to one coarse simplex. -/
theorem coefficient_zero_on_supported_chain {R : Type*} [Semiring R]
    {I J : Type*} (F : (I →₀ R) →ₗ[R] (J →₀ R)) (c : I →₀ R) (j : J)
    (h : ∀ i ∈ c.support, F (Finsupp.single i 1) j = 0) : F c j = 0 := by
  classical
  rw [← c.sum_single]
  simp only [Finsupp.sum, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  have he : Finsupp.single i (c i) = c i • Finsupp.single i (1 : R) := by simp
  rw [he, map_smul, Finsupp.smul_apply, h i hi, smul_zero]

/-- Homotopic continuous self-maps have the same Lefschetz number in the
specified singular model; this requires no finiteness assertion. -/
theorem lefschetz_number_homotopy {X : TopCat.{w}} {f g : X ⟶ X}
    (H : TopCat.Homotopy f g) : lefschetzNumber f = lefschetzNumber g := by
  unfold lefschetzNumber
  congr 1
  funext n
  have he : rationalHomologyMap f n = rationalHomologyMap g n :=
    ((P202.PrismHomotopy.chainPrism ℚ ℚ H).homologyMap_eq n).symm
  rw [he]

def conjugateMap {X Y : TopCat.{w}} (h : X ≃ₜ Y) (f : X ⟶ X) : Y ⟶ Y :=
  (TopCat.isoOfHomeo h).inv ≫ f ≫ (TopCat.isoOfHomeo h).hom

theorem lefschetz_number_conjugate {X Y : TopCat.{w}} (h : X ≃ₜ Y) (f : X ⟶ X) :
    lefschetzNumber f = lefschetzNumber (conjugateMap h f) := by
  unfold lefschetzNumber
  congr 1
  funext n
  let H := P202Specs.SingularChains.chainFunctor ℚ ℚ ⋙
    HomologicalComplex.homologyFunctor _ _ n
  let i := TopCat.isoOfHomeo h
  have hc : f ≫ i.hom = i.hom ≫ conjugateMap h f := by
    change f ≫ i.hom = i.hom ≫ i.inv ≫ f ≫ i.hom
    rw [i.hom_inv_id_assoc]
  have hn : H.map f ≫ H.map i.hom = H.map i.hom ≫ H.map (conjugateMap h f) := by
    rw [← H.map_comp, ← H.map_comp, hc]
  have ht := P202.LefschetzTrace.trace_equivariant
    (homologyEquivOfHomeomorph ℚ ℚ h n) (rationalHomologyMap f n).hom
    (rationalHomologyMap (conjugateMap h f) n).hom
    (fun x => congr($(hn) x))
  rw [ht]

theorem fixed_point_of_conjugate {X Y : TopCat.{w}} (h : X ≃ₜ Y) (f : X ⟶ X)
    (hy : ∃ y : Y, conjugateMap h f y = y) : ∃ x : X, f x = x := by
  obtain ⟨y, hy⟩ := hy
  change h (f (h.symm y)) = y at hy
  refine ⟨h.symm y, h.injective ?_⟩
  simpa using hy

/-- A realization proof gives the stated theorem for arbitrary finite
polyhedra by conjugation, without an embedding or connectedness assumption. -/
theorem fixed_point_reduce_to_realizations
    (hreal : ∀ {V : Type w} (K : AbstractSimplicialComplex V), K.IsFinite →
      ∀ f : TopCat.of K.Realization ⟶ TopCat.of K.Realization,
        lefschetzNumber f ≠ 0 → ∃ x : K.Realization, f x = x) :
    P202Specs.LefschetzFixedPoint.fixedPoint_type.{0,0,w} := by
  rintro X ⟨V, K, hK, ⟨h⟩⟩ f hf
  have h' : X ≃ₜ TopCat.of K.Realization := h
  apply fixed_point_of_conjugate h' f
  apply hreal K hK (conjugateMap h' f)
  rwa [← lefschetz_number_conjugate h' f]

/-- The topological approximation interface uses active vertices, whereas
the oriented chain interface uses all ambient vertices. -/
theorem mem_simplexVertices {V : Type w} (K : AbstractSimplicialComplex V)
    (s : K.Simplex) (v : K.Vertex) :
    v ∈ K.simplexVertices s ↔ v.1 ∈ s.1 := by
  constructor
  · intro hv
    obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hv
    exact (congrArg Subtype.val ha) ▸ a.2
  · intro hv
    apply Finset.mem_map.mpr
    exact ⟨⟨v.1, hv⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩

def extendActiveVertices {V : Type w} {W : Type v}
    {K : AbstractSimplicialComplex V} {L : AbstractSimplicialComplex W}
    (g : SimplicialMap K L) (w₀ : W) (v : V) : W := by
  classical
  exact if hv : ({v} : Finset V) ∈ K.simplices then g.vertex ⟨v, hv⟩ else w₀

theorem extendActiveVertices_on_vertex {V : Type w} {W : Type v}
    {K : AbstractSimplicialComplex V} {L : AbstractSimplicialComplex W}
    (g : SimplicialMap K L) (w₀ : W) (v : K.Vertex) :
    extendActiveVertices g w₀ v.1 = g.vertex v := by
  simp [extendActiveVertices, v.2]

def extendActiveMap {V : Type w} {W : Type v}
    {K : AbstractSimplicialComplex V} {L : AbstractSimplicialComplex W}
    (g : SimplicialMap K L) (w₀ : W) :
    P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L where
  vertices := extendActiveVertices g w₀
  map_simplex s hs := by
    convert g.map_simplex ⟨s, hs⟩ using 1
    ext w
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨v, hv, rfl⟩
      let a : K.Vertex := ⟨v, vertex_mem_of_mem hs hv⟩
      exact ⟨a, (mem_simplexVertices K ⟨s, hs⟩ a).mpr hv,
        (extendActiveVertices_on_vertex g w₀ a).symm⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.1, (mem_simplexVertices K ⟨s, hs⟩ v).mp hv,
        extendActiveVertices_on_vertex g w₀ v⟩

/-- The extension on unused vertices has exactly the original realization;
in particular it introduces no restriction on the approximation. -/
theorem extendActiveMap_realization {V : Type w} {W : Type v}
    {K : AbstractSimplicialComplex V} {L : AbstractSimplicialComplex W}
    (g : SimplicialMap K L) (w₀ : W) (x : K.Realization) :
    (g.realization x).val = x.val.map (extendActiveMap g w₀).vertices := by
  change (K.activeCoordinates x).map g.vertex = x.val.map (extendActiveVertices g w₀)
  rw [← P202.Topology.activeCoordinates_map_val K x, Convexity.StdSimplex.map_map]
  congr 1
  funext v
  exact (extendActiveVertices_on_vertex g w₀ v).symm

/-- The open-star construction's support inclusion gives the pointwise error
bound in the very same target mesh used by the displacement argument. -/
theorem approximation_error_of_carrier {V : Type w} {W : Type v}
    {K : AbstractSimplicialComplex V} {L : AbstractSimplicialComplex W}
    (d : MetricSpace L.Realization) (ε : ℝ) (hε : 0 < ε)
    (hmesh : ∀ s : L.Simplex, D10Topology.Ch09.diameter d.toPseudoMetricSpace
      (Set.range (L.simplexChart s)) < ENNReal.ofReal ε)
    (f : K.Realization → L.Realization) (g : SimplicialMap K L)
    (hcarrier : ∀ x, (g.realization x).val.weights.support ⊆ (f x).val.weights.support)
    (x : K.Realization) :
    D10Topology.Ch09.distance d.toPseudoMetricSpace (g.realization x) (f x) < ε := by
  let s : L.Simplex := ⟨(f x).val.weights.support, (f x).property⟩
  have hg : g.realization x ∈ Set.range (L.simplexChart s) :=
    (P202.Topology.mem_simplexChart_iff_support_subset L s _).mpr (hcarrier x)
  have hf : f x ∈ Set.range (L.simplexChart s) :=
    (P202.Topology.mem_simplexChart_iff_support_subset L s _).mpr (Finset.Subset.refl _)
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mp
    ((P202.Topology.distance_le_diameter d.toPseudoMetricSpace hg hf).trans_lt (hmesh s))

/-- The supplied trace theorem uses integer-indexed complexes. Extending an
ordinary complex by zero gives its usual nonnegative-degree version, with the
same endomorphism and the same induced homology maps. -/
theorem trace_identity_nat {R : Type u} [Field R]
    (C : ChainComplex (ModuleCat.{v} R) ℕ) (F : C ⟶ C)
    [∀ n, FiniteDimensional R (C.X n)] (N : ℕ)
    (hN : ∀ n, N ≤ n → Subsingleton (C.X n)) :
    (∑ j ∈ Finset.range N, (-1 : R) ^ j * LinearMap.trace R (C.X j) (F.f j).hom) =
      ∑ j ∈ Finset.range N, (-1 : R) ^ j *
        LinearMap.trace R (C.homology j) (homologyMap F j).hom := by
  let e := P202Specs.SingularChains.degreeEmbedding 0
  let E := C.extend e
  let G := extendMap F e
  have he (j : ℕ) : e.f j = (j : ℤ) := by
    change (0 : ℤ) + (j : ℤ) = (j : ℤ)
    omega
  let : ∀ z : ℤ, FiniteDimensional R (E.X z) := fun z => by
    by_cases hz : 0 ≤ z
    · have hj : e.f z.toNat = z := by
        change (0 : ℤ) + (z.toNat : ℤ) = z
        omega
      let q := (C.extendXIso e hj).toLinearEquiv
      exact Module.Finite.of_injective q.toLinearMap q.injective
    · let : Subsingleton (E.X z) := ModuleCat.subsingleton_of_isZero
        (C.isZero_extend_X e z (fun j => by rw [he j]; omega))
      infer_instance
  have hs : P202Specs.LefschetzTrace.SupportedIn E 0 N := by
    intro z hz
    by_cases hneg : z < 0
    · exact ModuleCat.subsingleton_of_isZero
        (C.isZero_extend_X e z (fun j => by rw [he j]; omega))
    · have hj : e.f z.toNat = z := by
        change (0 : ℤ) + (z.toNat : ℤ) = z
        omega
      let := hN z.toNat (by omega)
      exact (C.extendXIso e hj).toLinearEquiv.injective.subsingleton
  have hchain (j : ℕ) :
      LinearMap.trace R (E.X (0 + (j : ℤ))) (G.f (0 + (j : ℤ))).hom =
        LinearMap.trace R (C.X j) (F.f j).hom := by
    let q := C.extendXIso e (show e.f j = 0 + (j : ℤ) from rfl)
    apply P202.LefschetzTrace.trace_equivariant q.toLinearEquiv _ _
    intro x
    have hh : G.f (0 + (j : ℤ)) ≫ q.hom = q.hom ≫ F.f j := by
      dsimp [G]
      rw [extendMap_f F e (show e.f j = 0 + (j : ℤ) from rfl)]
      simp [q]
    exact congr($(hh) x)
  have hhomology (j : ℕ) :
      LinearMap.trace R (E.homology (0 + (j : ℤ))) (homologyMap G (0 + (j : ℤ))).hom =
        LinearMap.trace R (C.homology j) (homologyMap F j).hom := by
    let q := C.extendHomologyIso e (show e.f j = 0 + (j : ℤ) from rfl)
    apply P202.LefschetzTrace.trace_equivariant q.toLinearEquiv _ _
    intro x
    exact congr($(extendHomologyIso_hom_naturality F e (show e.f j = 0 + (j : ℤ) from rfl)) x)
  have ht := P202.LefschetzTrace.trace_identity E G 0 N hs
  simp only [zero_add, zpow_natCast] at ht
  calc
    _ = ∑ j ∈ Finset.range N, (-1 : R) ^ j *
        LinearMap.trace R (E.X (0 + (j : ℤ))) (G.f (0 + (j : ℤ))).hom := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hchain]
    _ = ∑ j ∈ Finset.range N, (-1 : R) ^ j *
        LinearMap.trace R (E.homology (0 + (j : ℤ))) (homologyMap G (0 + (j : ℤ))).hom := ht
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hhomology]

/-- The algebraic end of the Lefschetz argument. Its hypotheses specify an
actual finite chain endomorphism, an equivariant comparison with the singular
map, and zero chain traces. These data are constructed below from a fixed-point-free
map by carried subdivision and the last-vertex map. -/
theorem lefschetz_zero_of_finite_chain_model {X : TopCat.{w}} (f : X ⟶ X)
    (C : ChainComplex (ModuleCat.{v} ℚ) ℕ) (F : C ⟶ C)
    [∀ n, FiniteDimensional ℚ (C.X n)] (N : ℕ)
    (hN : ∀ n, N ≤ n → Subsingleton (C.X n))
    (e : ∀ n, C.homology n ≃ₗ[ℚ] rationalHomology X n)
    (he : ∀ n x, e n ((homologyMap F n) x) = rationalHomologyMap f n (e n x))
    (htrace : ∀ n, LinearMap.trace ℚ (C.X n) (F.f n).hom = 0) :
    lefschetzNumber f = 0 := by
  have hvanish : ∀ n, N ≤ n → Subsingleton (rationalHomology X n) := by
    intro n hn
    let := hN n hn
    let := homology_subsingleton_of_chain_subsingleton C n
    exact (e n).symm.injective.subsingleton
  rw [(lefschetz_sum_of_bounded_homology N hvanish f).2]
  calc
    _ = ∑ n ∈ Finset.range N, (-1 : ℚ) ^ n *
        LinearMap.trace ℚ (C.homology n) (homologyMap F n).hom := by
      apply Finset.sum_congr rfl
      intro n _
      rw [P202.LefschetzTrace.trace_equivariant (e n) _ _ (he n)]
    _ = ∑ n ∈ Finset.range N, (-1 : ℚ) ^ n *
        LinearMap.trace ℚ (C.X n) (F.f n).hom := (trace_identity_nat C F N hN).symm
    _ = 0 := by simp [htrace]

section DiagonalCoefficients
open P202Specs.OrientedSimplicialAlgebra

theorem sorted_vertex_set {V : Type w} {K : AbstractSimplicialComplex V}
    {n : ℕ} (s : VertexTuple K n) (hs : Function.Injective s.1) :
    Finset.univ.image (sorted s hs).1 = Finset.univ.image s.1 := by
  classical
  change Finset.univ.image (s.1 ∘ Tuple.sort s.1) = Finset.univ.image s.1
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨Tuple.sort s.1 i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨(Tuple.sort s.1).symm i, by simpa using hi⟩

theorem oriented_coefficient_zero_of_vertex_set_ne
    {V : Type w} {K : AbstractSimplicialComplex V} (A : Type v) [AddCommGroup A]
    {n : ℕ} (s : VertexTuple K n) (t : Simplex K n)
    (hne : Finset.univ.image s.1 ≠ Finset.univ.image t.1) (a : A) :
    oriented A s a t = 0 := by
  classical
  unfold oriented
  split_ifs with hs
  · have hst : sorted s hs ≠ t := by
      intro h
      have hh := sorted_vertex_set s hs
      rw [h] at hh
      exact hne hh.symm
    simp [Finsupp.smul_apply, Finsupp.single_apply, hst, Ne.symm hst]
  · simp

theorem pushforward_coefficient_zero_of_vertex_set_ne
    {V W : Type w} {K : AbstractSimplicialComplex V} {L : AbstractSimplicialComplex W}
    (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L)
    {n : ℕ} (s : Simplex K n) (t : Simplex L n)
    (hne : Finset.univ.image (f.vertices ∘ s.1) ≠ Finset.univ.image t.1) (a : A) :
    pushforward R A f n (Finsupp.single s a) t = 0 := by
  rw [P202.OrientedSimplicialAlgebra.pushforward_single]
  exact oriented_coefficient_zero_of_vertex_set_ne A _ t hne a

/-- A carried subdivision chain followed by a simplicial map has zero
diagonal coefficient once each occurring subsimplex has a different image
vertex set. Collapsed images are included by the oriented convention. -/
theorem subdivision_pushforward_diagonal_zero
    {V W : Type w} {K : AbstractSimplicialComplex V} {L : AbstractSimplicialComplex W}
    (R : Type u) [CommRing R]
    (g : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := L) K)
    (n : ℕ) (S : Chains K R n →ₗ[R] Chains L R n) (s : Simplex K n)
    (hS : ∀ t ∈ (S (Finsupp.single s 1)).support,
      Finset.univ.image (g.vertices ∘ t.1) ≠ Finset.univ.image s.1) :
    pushforward R R g n (S (Finsupp.single s 1)) s = 0 := by
  apply coefficient_zero_on_supported_chain
  intro t ht
  exact pushforward_coefficient_zero_of_vertex_set_ne R R g t s (hS t ht) 1

end DiagonalCoefficients

namespace OrientedCone
open P202Specs.OrientedSimplicialAlgebra

variable {V : Type w} {K : AbstractSimplicialComplex V}

theorem image_cons (v : V) {n : ℕ} (t : Fin n → V) :
    Finset.univ.image (Fin.cons v t) = insert v (Finset.univ.image t) := by
  classical
  ext x
  simp [Fin.exists_fin_succ, eq_comm]

/-- A cone vertex may already occur: the oriented convention automatically
sets the repeated tuple to zero. -/
def coneTuple (v : V) (hv : ∀ s ∈ K.simplices, insert v s ∈ K.simplices)
    {n : ℕ} (s : Simplex K n) : VertexTuple K (n + 1) :=
  ⟨Fin.cons v s.1, by rw [image_cons]; exact hv _ s.2⟩

def cone (R : Type u) [CommRing R] (v : V)
    (hv : ∀ s ∈ K.simplices, insert v s ∈ K.simplices) (n : ℕ) :
    Chains K R n →ₗ[R] Chains K R (n + 1) :=
  Finsupp.linearCombination R (fun s => oriented R (coneTuple v hv s) 1)

theorem cone_single_one (R : Type u) [CommRing R] (v : V)
    (hv : ∀ s ∈ K.simplices, insert v s ∈ K.simplices)
    {n : ℕ} (s : Simplex K n) :
    cone R v hv n (Finsupp.single s 1) = oriented R (coneTuple v hv s) 1 := by
  simp [cone, Finsupp.linearCombination_single]

theorem face_zero (v : V)
    (hv : ∀ s ∈ K.simplices, insert v s ∈ K.simplices)
    {n : ℕ} (s : Simplex K n) :
    tupleFace 0 (coneTuple v hv s) = (⟨s.1, s.2⟩ : VertexTuple K n) := by
  apply Subtype.ext
  simp [tupleFace, coneTuple, Fin.succAbove_zero]

theorem face_succ (v : V)
    (hv : ∀ s ∈ K.simplices, insert v s ∈ K.simplices)
    {n : ℕ} (s : Simplex K (n + 1)) (i : Fin (n + 2)) :
    tupleFace i.succ (coneTuple v hv s) = coneTuple v hv (face i s) := by
  apply Subtype.ext
  exact Fin.cons_comp_succ_succAbove v s.1 i

theorem linearMap_ext_on_single_one {R : Type*} [Semiring R]
    {I M : Type*} [AddCommMonoid M] [Module R M]
    {f g : (I →₀ R) →ₗ[R] M}
    (h : ∀ i, f (Finsupp.single i 1) = g (Finsupp.single i 1)) : f = g := by
  apply Finsupp.lhom_ext
  intro i r
  rw [← Finsupp.smul_single_one i r]
  simpa only [map_smul] using congrArg (r • ·) (h i)

/-- The simplicial cone contracts positive-dimensional cycles. This is the
algebraic ingredient for constructing carried subdivision maps recursively. -/
theorem boundary_cone (R : Type u) [CommRing R] (v : V)
    (hv : ∀ s ∈ K.simplices, insert v s ∈ K.simplices)
    (n : ℕ) (c : Chains K R (n + 1)) :
    boundary R R (n + 1) (cone R v hv (n + 1) c) =
      c - cone R v hv n (boundary R R n c) := by
  have he : (boundary R R (n + 1)).comp (cone R v hv (n + 1)) =
      LinearMap.id - (cone R v hv n).comp (boundary R R n) := by
    apply linearMap_ext_on_single_one
    intro s
    change boundary R R (n + 1) (cone R v hv (n + 1) (Finsupp.single s 1)) =
      Finsupp.single s 1 - cone R v hv n (boundary R R n (Finsupp.single s 1))
    rw [cone_single_one, P202.OrientedSimplicialAlgebra.boundary_oriented,
      Fin.sum_univ_succ, face_zero,
      P202.OrientedSimplicialAlgebra.oriented_increasing,
      P202.OrientedSimplicialAlgebra.boundary_single]
    simp only [Fin.val_zero, pow_zero, one_smul, face_succ, Fin.val_succ,
      pow_succ, mul_neg_one, neg_smul, map_sum, map_zsmul, cone_single_one,
      ← Finset.sum_neg_distrib, sub_eq_add_neg]
  exact LinearMap.congr_fun he c

theorem cycle_bounds (R : Type u) [CommRing R] (v : V)
    (hv : ∀ s ∈ K.simplices, insert v s ∈ K.simplices)
    (n : ℕ) (c : Chains K R (n + 1)) (hc : boundary R R n c = 0) :
    ∃ b : Chains K R (n + 2), boundary R R (n + 1) b = c := by
  refine ⟨cone R v hv (n + 1) c, ?_⟩
  rw [boundary_cone, hc, map_zero, sub_zero]

def vertexSimplex (v : V) (hv : ({v} : Finset V) ∈ K.simplices) : Simplex K 0 :=
  ⟨OrderEmbedding.ofStrictMono (fun _ : Fin 1 => v) (by
    intro i j hij
    have hi := i.is_lt
    have hj := j.is_lt
    have hij' := hij
    change i.val < j.val at hij'
    omega), by simpa using hv⟩

theorem boundary_cone_zero (R : Type u) [CommRing R] (v : V)
    (hv : ∀ s ∈ K.simplices, insert v s ∈ K.simplices)
    (hv₀ : ({v} : Finset V) ∈ K.simplices) (c : Chains K R 0) :
    boundary R R 0 (cone R v hv 0 c) = c -
      Finsupp.single (vertexSimplex v hv₀)
        (P202Specs.SingularChains.sumCoefficients R R (Simplex K 0) c) := by
  have he : (boundary R R 0).comp (cone R v hv 0) =
      LinearMap.id - (Finsupp.lsingle (vertexSimplex v hv₀)).comp
        (P202Specs.SingularChains.sumCoefficients R R (Simplex K 0)) := by
    apply linearMap_ext_on_single_one
    intro s
    change boundary R R 0 (cone R v hv 0 (Finsupp.single s 1)) = _
    have hface : tupleFace 1 (coneTuple v hv s) =
        (⟨(vertexSimplex v hv₀).1, (vertexSimplex v hv₀).2⟩ : VertexTuple K 0) := by
      apply Subtype.ext
      funext i
      have hi : i = 0 := Fin.ext (by have hi := i.is_lt; omega)
      subst hi
      rfl
    rw [cone_single_one, P202.OrientedSimplicialAlgebra.boundary_oriented,
      Fin.sum_univ_two, face_zero, hface,
      P202.OrientedSimplicialAlgebra.oriented_increasing,
      P202.OrientedSimplicialAlgebra.oriented_increasing]
    simp [P202Specs.SingularChains.sumCoefficients, sub_eq_add_neg]
  exact LinearMap.congr_fun he c

theorem augmented_zero_cycle_bounds (R : Type u) [CommRing R] (v : V)
    (hv : ∀ s ∈ K.simplices, insert v s ∈ K.simplices)
    (hv₀ : ({v} : Finset V) ∈ K.simplices) (c : Chains K R 0)
    (hc : P202Specs.SingularChains.sumCoefficients R R (Simplex K 0) c = 0) :
    ∃ b : Chains K R 1, boundary R R 0 b = c := by
  refine ⟨cone R v hv 0 c, ?_⟩
  rw [boundary_cone_zero R v hv hv₀, hc, Finsupp.single_zero, sub_zero]

end OrientedCone

/-- All flags of nonempty faces of a fixed simplex, as a subcomplex of the
actual barycentric subdivision (on its actual ambient face type). -/
def subdivisionCarrier {V : Type w} (K : AbstractSimplicialComplex V) (s : K.Simplex) :
    AbstractSimplicialComplex K.Simplex where
  simplices := {c | c ∈ K.barycentricSubdivision.simplices ∧ ∀ t ∈ c, t.1 ⊆ s.1}
  nonempty _ hc := K.barycentricSubdivision.nonempty _ hc.1
  face hc hdc hd := ⟨K.barycentricSubdivision.face hc.1 hdc hd,
    fun t ht => hc.2 t (hdc ht)⟩

theorem subdivisionCarrier_apex {V : Type w} (K : AbstractSimplicialComplex V)
    (s : K.Simplex) : ({s} : Finset K.Simplex) ∈ (subdivisionCarrier K s).simplices := by
  refine ⟨⟨Finset.singleton_nonempty s, ?_⟩, ?_⟩ <;> simp

theorem subdivisionCarrier_cone {V : Type w} (K : AbstractSimplicialComplex V)
    (s : K.Simplex) :
    ∀ c ∈ (subdivisionCarrier K s).simplices,
      insert s c ∈ (subdivisionCarrier K s).simplices := by
  intro c hc
  refine ⟨⟨Finset.insert_nonempty _ _, ?_⟩, ?_⟩
  · intro a ha b hb
    by_cases has : a = s
    · subst a
      by_cases hbs : b = s
      · subst b
        exact Or.inl (Finset.Subset.refl _)
      · exact Or.inr (hc.2 b ((Finset.mem_insert.mp hb).resolve_left hbs))
    · have ha' : a ∈ c := (Finset.mem_insert.mp ha).resolve_left has
      by_cases hbs : b = s
      · subst b
        exact Or.inl (hc.2 a ha')
      · exact hc.1.2 a ha' b ((Finset.mem_insert.mp hb).resolve_left hbs)
  · intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact Finset.Subset.refl _
    · exact hc.2 t ht

theorem subdivisionCarrier_cycle_bounds {V : Type w} (K : AbstractSimplicialComplex V)
    (s : K.Simplex) (R : Type u) [CommRing R] (n : ℕ)
    (c : P202Specs.OrientedSimplicialAlgebra.Chains (subdivisionCarrier K s) R (n + 1))
    (hc : P202Specs.OrientedSimplicialAlgebra.boundary R R n c = 0) :
    ∃ b : P202Specs.OrientedSimplicialAlgebra.Chains (subdivisionCarrier K s) R (n + 2),
      P202Specs.OrientedSimplicialAlgebra.boundary R R (n + 1) b = c := by
  apply OrientedCone.cycle_bounds R s ?_ n c hc
  intro t ht
  convert subdivisionCarrier_cone K s t ht using 1
  congr 3
  exact Subsingleton.elim _ _

end P202.LefschetzFixedPoint

namespace P202.LefschetzFixedPoint
attribute [local instance] P202Specs.OrientedSimplicialAlgebra.vertexOrder
open P202.Cellular P202.Cellular.AbstractSimplicialComplex

/-- The largest original vertex of a nonempty face. -/
def lastVertex {V : Type w} (K : AbstractSimplicialComplex V) (s : K.Simplex) : V :=
  s.1.max' (K.nonempty _ s.2)

theorem lastVertex_mem {V : Type w} (K : AbstractSimplicialComplex V) (s : K.Simplex) :
    lastVertex K s ∈ s.1 := Finset.max'_mem _ _

/-- A positive flag weight gives positive barycentric evaluation at every
vertex of that face, in particular at its selected last vertex. -/
theorem subdivisionMap_weight_pos {V : Type w} (K : AbstractSimplicialComplex V)
    (s : K.Simplex) (x : K.barycentricSubdivision.Realization)
    (hs : 0 < x.1.weights s) {v : V} (hv : v ∈ s.1) :
    0 < (K.subdivisionMap x).1.weights v := by
  rw [P202.Topology.subdivisionMap_weights_linear,
    P202.Topology.barycentricEvalWeights_apply]
  have hm : s ∈ x.1.weights.support := Finsupp.mem_support_iff.mpr hs.ne'
  have hbp : 0 < (K.simplexBarycenter s).weights v := by
    rw [P202.Topology.simplexBarycenter_weight_of_mem K s hv]
    exact inv_pos.mpr (by exact_mod_cast (K.nonempty _ s.2).card_pos)
  exact (mul_pos hs hbp).trans_le (Finset.single_le_sum
    (fun t ht => mul_nonneg (x.1.weights_nonneg t) ((K.simplexBarycenter t).weights_nonneg v)) hm)

/-- The last-vertex map is obtained from the star criterion and has the
canonical barycentric homeomorphism as its star approximation. -/
theorem exists_lastVertexMap {V : Type w} (K : AbstractSimplicialComplex V) :
    ∃ p : SimplicialMap K.barycentricSubdivision K,
      (∀ s, p.vertex s = lastVertex K s.1) ∧
      ∀ x, (p.realization x).1.weights.support ⊆ (K.subdivisionMap x).1.weights.support := by
  obtain ⟨p, hp, hsupp⟩ := P202.Topology.starCriterion_map
    K.barycentricSubdivision K K.subdivisionMap
    (fun s => lastVertex K s.1) (by
      intro s x hx
      exact subdivisionMap_weight_pos K s.1 x hx (lastVertex_mem K s.1))
  exact ⟨p, fun s => congrFun hp s, hsupp⟩

def lastVertexMap {V : Type w} (K : AbstractSimplicialComplex V) :
    SimplicialMap K.barycentricSubdivision K :=
  (exists_lastVertexMap K).choose

theorem lastVertexMap_vertex {V : Type w} (K : AbstractSimplicialComplex V)
    (s : K.barycentricSubdivision.Vertex) :
    (lastVertexMap K).vertex s = lastVertex K s.1 :=
  (exists_lastVertexMap K).choose_spec.1 s

theorem lastVertexMap_support {V : Type w} (K : AbstractSimplicialComplex V)
    (x : K.barycentricSubdivision.Realization) :
    ((lastVertexMap K).realization x).1.weights.support ⊆
      (K.subdivisionMap x).1.weights.support :=
  (exists_lastVertexMap K).choose_spec.2 x

theorem lastVertexMap_star {V : Type w} (K : AbstractSimplicialComplex V)
    (s : K.barycentricSubdivision.Vertex) (x : K.barycentricSubdivision.Realization)
    (hx : x ∈ K.barycentricSubdivision.openStar s) :
    0 < (K.subdivisionMap x).1.weights ((lastVertexMap K).vertex s) := by
  rw [lastVertexMap_vertex]
  exact subdivisionMap_weight_pos K s.1 x hx (lastVertex_mem K s.1)

/-- The last-vertex realization has the same induced singular homology map
as the canonical barycentric evaluation. -/
theorem lastVertexMap_homotopy {V : Type w} (K : AbstractSimplicialComplex V)
    (hK : K.IsFinite) :
    ∃ H : C(K.barycentricSubdivision.Realization × Interval, K.Realization),
      (∀ x, H (x, 0) = K.subdivisionMap x) ∧
      (∀ x, H (x, 1) = (lastVertexMap K).realization x) := by
  obtain ⟨H, h0, h1, _⟩ := P202.Topology.star_homotopy K.barycentricSubdivision K
    (P202.Topology.finite_subdivision K hK)
    ⟨K.subdivisionMap, P202.Topology.subdivisionMap_continuous K⟩
    (lastVertexMap K) (lastVertexMap_star K)
  exact ⟨H, h0, h1⟩

/-- The ambient-vertex form used by the oriented chain interfaces. -/
def lastVertexOrientedMap {V : Type w} (K : AbstractSimplicialComplex V) :
    P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K.barycentricSubdivision) K where
  vertices := lastVertex K
  map_simplex c hc := by
    obtain ⟨s, hs, htop⟩ := chain_has_largest hc
    apply K.face s.2
    · intro v hv
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
      exact htop t ht (lastVertex_mem K t)
    · exact hc.1.image _

theorem lastVertexOrientedMap_realization {V : Type w} (K : AbstractSimplicialComplex V)
    (x : K.barycentricSubdivision.Realization) :
    ((lastVertexMap K).realization x).1 = x.1.map (lastVertexOrientedMap K).vertices := by
  change (K.barycentricSubdivision.activeCoordinates x).map (lastVertexMap K).vertex = _
  rw [← P202.Topology.activeCoordinates_map_val K.barycentricSubdivision x,
    Convexity.StdSimplex.map_map]
  congr 1
  funext v
  exact lastVertexMap_vertex K v

theorem lastVertexOrientedMap_carried {V : Type w} (K : AbstractSimplicialComplex V)
    (s : K.Simplex) {n : ℕ}
    (t : P202Specs.OrientedSimplicialAlgebra.Simplex K.barycentricSubdivision n)
    (ht : ∀ a ∈ Finset.univ.image t.1, a.1 ⊆ s.1) :
    Finset.univ.image ((lastVertexOrientedMap K).vertices ∘ t.1) ⊆ s.1 := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
  exact ht (t.1 i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩) (lastVertex_mem K (t.1 i))

/-- Converts the source's source-times-interval convention to Mathlib's
interval-times-source homotopies. -/
def homotopyOfProduct {X Y : TopCat.{w}} {f g : X ⟶ Y}
    (H : C(X × Interval, Y)) (h0 : ∀ x, H (x, 0) = f x)
    (h1 : ∀ x, H (x, 1) = g x) : TopCat.Homotopy f g where
  toFun z := H (z.2, z.1)
  continuous_toFun := H.continuous.comp (continuous_snd.prodMk continuous_fst)
  map_zero_left := h0
  map_one_left := h1

def canonicalSubdivisionHom {V : Type w} (K : AbstractSimplicialComplex V) :
    TopCat.of K.barycentricSubdivision.Realization ⟶ TopCat.of K.Realization :=
  TopCat.ofHom ⟨K.subdivisionMap, P202.Topology.subdivisionMap_continuous K⟩

def lastVertexHom {V : Type w} (K : AbstractSimplicialComplex V) :
    TopCat.of K.barycentricSubdivision.Realization ⟶ TopCat.of K.Realization :=
  TopCat.ofHom ⟨(lastVertexMap K).realization,
    P202.Topology.simplicialMap_continuous (lastVertexMap K)⟩

theorem lastVertex_homotopic {V : Type w} (K : AbstractSimplicialComplex V)
    (hK : K.IsFinite) :
    Nonempty (TopCat.Homotopy (canonicalSubdivisionHom K) (lastVertexHom K)) := by
  obtain ⟨H, h0, h1⟩ := lastVertexMap_homotopy K hK
  exact ⟨homotopyOfProduct H h0 h1⟩

end P202.LefschetzFixedPoint

namespace P202.LefschetzFixedPoint.CarrierIdentity
open P202.Cellular P202.Cellular.AbstractSimplicialComplex
open P202Specs.OrientedSimplicialAlgebra
attribute [local instance] P202Specs.OrientedSimplicialAlgebra.vertexOrder
variable {V : Type w} {K : AbstractSimplicialComplex V}

theorem simplex_eq_of_vertex_subset {n : ℕ} (s t : Simplex K n)
    (h : Finset.univ.image t.1 ⊆ Finset.univ.image s.1) : t = s := by
  classical
  apply (simplexEquiv K n).injective
  apply Subtype.ext
  change Finset.univ.image t.1 = Finset.univ.image s.1
  apply Finset.eq_of_subset_of_card_le h
  simp only [Finset.card_image_of_injective _ t.1.injective,
    Finset.card_image_of_injective _ s.1.injective]
  exact le_rfl
  
theorem face_injective {n : ℕ} (s : Simplex K (n + 1)) :
    Function.Injective (fun i : Fin (n + 2) => face i s) := by
  intro i j h
  apply Fin.succAbove_left_injective
  funext k
  apply s.1.injective
  exact congrArg (fun t : Simplex K n => t.1 k) h

theorem boundary_coefficient_face_zero (R : Type u) [CommRing R]
    {n : ℕ} (s : Simplex K (n + 1)) (a : R) :
    boundary R R n (Finsupp.single s a) (face 0 s) = a := by
  classical
  rw [P202.OrientedSimplicialAlgebra.boundary_single]
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply]
  rw [Finset.sum_eq_single (0 : Fin (n + 2))]
  · simp
  · intro i hi hne
    have hface : face i s ≠ face 0 s := fun h => hne (face_injective s h)
    simp [hface]
  · simp

theorem supported_single_eq (R : Type u) [CommRing R] {n : ℕ}
    (s : Simplex K n) (c : Chains K R n)
    (hc : ∀ t ∈ c.support, Finset.univ.image t.1 ⊆ Finset.univ.image s.1) :
    c = Finsupp.single s (c s) := by
  classical
  ext t
  by_cases h : t = s
  · subst t
    simp
  · have ht : t ∉ c.support := by
      intro ht
      exact h (simplex_eq_of_vertex_subset s t (hc t ht))
    simp [Finsupp.notMem_support_iff.mp ht, h]

theorem carried_maps_eq_id (R : Type u) [CommRing R]
    (F : ∀ n, Chains K R n →ₗ[R] Chains K R n)
    (hcomm : ∀ n c, boundary R R n (F (n + 1) c) = F n (boundary R R n c))
    (hcarrier : ∀ n (s : Simplex K n) t,
      t ∈ (F n (Finsupp.single s 1)).support →
      Finset.univ.image t.1 ⊆ Finset.univ.image s.1)
    (haug : ∀ c, P202Specs.SingularChains.sumCoefficients R R (Simplex K 0) (F 0 c) =
      P202Specs.SingularChains.sumCoefficients R R (Simplex K 0) c) :
    ∀ n, F n = LinearMap.id := by
  intro n
  induction n with
  | zero =>
    apply P202.LefschetzFixedPoint.OrientedCone.linearMap_ext_on_single_one
    intro s
    have hs := supported_single_eq R s (F 0 (Finsupp.single s 1)) (hcarrier 0 s)
    have ha := haug (Finsupp.single s 1)
    rw [hs] at ha
    simp only [P202Specs.SingularChains.sumCoefficients, Finsupp.lsum_single,
      LinearMap.id_coe, id_eq] at ha
    change F _ (Finsupp.single s 1) = Finsupp.single s 1
    exact hs.trans (congrArg (Finsupp.single s) ha)
  | succ n ih =>
    apply P202.LefschetzFixedPoint.OrientedCone.linearMap_ext_on_single_one
    intro s
    have hs := supported_single_eq R s (F (n + 1) (Finsupp.single s 1)) (hcarrier (n + 1) s)
    have hb := hcomm n (Finsupp.single s 1)
    rw [hs, ih] at hb
    have ha := congrArg (fun c : Chains K R n => c (face 0 s)) hb
    simp only [LinearMap.id_coe, id_eq, boundary_coefficient_face_zero] at ha
    change F _ (Finsupp.single s 1) = Finsupp.single s 1
    exact hs.trans (congrArg (Finsupp.single s) ha)

theorem carried_chainMap_eq_id (R : Type u) [CommRing R]
    (F : complex R R (K := K) ⟶ complex R R (K := K))
    (hcarrier : ∀ n (s : Simplex K n) t,
      t ∈ ((F.f n).hom (Finsupp.single s 1)).support →
      Finset.univ.image t.1 ⊆ Finset.univ.image s.1)
    (haug : ∀ c, P202Specs.SingularChains.sumCoefficients R R (Simplex K 0)
      ((F.f 0).hom c) = P202Specs.SingularChains.sumCoefficients R R (Simplex K 0) c) :
    F = 𝟙 _ := by
  have hcomm : ∀ n c, boundary R R n ((F.f (n + 1)).hom c) =
      (F.f n).hom (boundary R R n c) := by
    intro n c
    have hh := congrArg (fun f => f.hom)
      (F.comm (n + 1) n)
    simp only [ModuleCat.hom_comp, P202.OrientedSimplicialAlgebra.boundary_eq] at hh
    exact LinearMap.congr_fun hh c
  have h := carried_maps_eq_id R (fun n => (F.f n).hom) hcomm hcarrier haug
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  exact h n

theorem augmentation_pushforward_zero (R : Type u) [CommRing R]
    {W : Type w} {L : AbstractSimplicialComplex W}
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L) (c : Chains K R 0) :
    P202Specs.SingularChains.sumCoefficients R R (Simplex L 0)
      (pushforward R R f 0 c) =
    P202Specs.SingularChains.sumCoefficients R R (Simplex K 0) c := by
  have he : (P202Specs.SingularChains.sumCoefficients R R (Simplex L 0)).comp
      (pushforward R R f 0) =
      P202Specs.SingularChains.sumCoefficients R R (Simplex K 0) := by
    apply P202.LefschetzFixedPoint.OrientedCone.linearMap_ext_on_single_one
    intro s
    simp only [LinearMap.comp_apply, P202.OrientedSimplicialAlgebra.pushforward_single]
    let : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
    have hinj : Function.Injective (f.imageTuple (⟨s.1, s.2⟩ : VertexTuple K 0)).1 :=
      Function.injective_of_subsingleton _
    have hsort : Tuple.sort (f.imageTuple (⟨s.1, s.2⟩ : VertexTuple K 0)).1 = 1 :=
      Subsingleton.elim _ _
    simp [oriented, hinj, hsort, P202Specs.SingularChains.sumCoefficients]
  exact LinearMap.congr_fun he c

theorem pushforward_support_vertex_subset (R : Type u) [CommRing R]
    {W : Type w} {L : AbstractSimplicialComplex W}
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L) (n : ℕ) (c : Chains K R n)
    (s : Finset W)
    (hc : ∀ t ∈ c.support, Finset.univ.image (f.vertices ∘ t.1) ⊆ s)
    (t : Simplex L n) (ht : t ∈ (pushforward R R f n c).support) :
    Finset.univ.image t.1 ⊆ s := by
  classical
  by_contra h
  have hz : pushforward R R f n c t = 0 := by
    apply P202.LefschetzFixedPoint.coefficient_zero_on_supported_chain
    intro u hu
    apply P202.LefschetzFixedPoint.pushforward_coefficient_zero_of_vertex_set_ne
    intro he
    exact h (he ▸ hc u hu)
  exact Finsupp.mem_support_iff.mp ht hz

end P202.LefschetzFixedPoint.CarrierIdentity

namespace P202.LefschetzFixedPoint
attribute [local instance] P202Specs.OrientedSimplicialAlgebra.vertexOrder
open P202.Cellular P202.Cellular.AbstractSimplicialComplex
open P202Specs.OrientedSimplicialAlgebra
namespace Subdivision
variable {V : Type w} (K : AbstractSimplicialComplex V)

abbrev Carrier (s : K.Simplex) := subdivisionCarrier K s

def inc (s : K.Simplex) : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := Carrier K s) K.barycentricSubdivision :=
  P202Specs.OrientedSimplicialAlgebra.SimplicialMap.inclusion (K := Carrier K s) (fun _ h => h.1)

def incl (R : Type u) [CommRing R] (s : K.Simplex) (n : ℕ) :=
  pushforward R R (inc K s) n

def simplexIncl (s : K.Simplex) (n : ℕ) :
    Simplex (Carrier K s) n → Simplex K.barycentricSubdivision n :=
  inclusionSimplex (K := Carrier K s) (fun _ h => h.1)

theorem simplexIncl_injective (s : K.Simplex) (n : ℕ) :
    Function.Injective (simplexIncl K s n) := by
  intro a b h
  apply Subtype.ext
  exact congrArg (fun x : Simplex K.barycentricSubdivision n => x.1) h

theorem incl_eq (R : Type u) [CommRing R] (s : K.Simplex) (n : ℕ) :
    incl K R s n = Finsupp.lmapDomain R R (simplexIncl K s n) := by
  apply Finsupp.lhom_ext
  intro t a
  simpa only [incl, inc, simplexIncl, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single] using
    P202.OrientedSimplicialAlgebra.pushforward_inclusion_single R R
      (K := Carrier K s) (L := K.barycentricSubdivision) (fun _ h => h.1) n t a

def restrict (R : Type u) [CommRing R] (s : K.Simplex) (n : ℕ) :
    Chains K.barycentricSubdivision R n →ₗ[R] Chains (Carrier K s) R n :=
  Finsupp.lcomapDomain (simplexIncl K s n) (simplexIncl_injective K s n)

theorem restrict_incl (R : Type u) [CommRing R] (s : K.Simplex) (n : ℕ)
    (c : Chains (Carrier K s) R n) : restrict K R s n (incl K R s n c) = c := by
  rw [incl_eq]
  exact Finsupp.comapDomain_mapDomain _ (simplexIncl_injective K s n) c

def Supported (R : Type u) [CommRing R] (s : K.Simplex) {n : ℕ}
    (c : Chains K.barycentricSubdivision R n) : Prop :=
  ∀ t ∈ c.support, ∀ i : Fin (n+1), (t.1 i).1 ⊆ s.1

theorem supported_iff_range (R : Type u) [CommRing R] (s : K.Simplex) {n : ℕ}
    (c : Chains K.barycentricSubdivision R n) :
    Supported K R s c ↔ c ∈ LinearMap.range (incl K R s n) := by
  let : DecidableEq K.Simplex := (vertexOrder K.Simplex).toDecidableEq
  rw [incl_eq]
  constructor
  · intro hc
    refine ⟨restrict K R s n c, ?_⟩
    apply Finsupp.mapDomain_comapDomain _ (simplexIncl_injective K s n)
    intro t ht
    refine ⟨⟨t.1, t.2, ?_⟩, ?_⟩
    · intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact hc t ht i
    · exact Subtype.ext rfl
  · rintro ⟨d, rfl⟩ t ht i
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ht)
    exact a.2.2 _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

def localCone (R : Type u) [CommRing R] (s : K.Simplex) (n : ℕ) :
    Chains (Carrier K s) R n →ₗ[R] Chains (Carrier K s) R (n+1) :=
  OrientedCone.cone R s (by
    intro t ht
    convert subdivisionCarrier_cone K s t ht using 1
    congr 3
    exact Subsingleton.elim _ _) n

def coneAt (R : Type u) [CommRing R] (s : K.Simplex) (n : ℕ) :
    Chains K.barycentricSubdivision R n →ₗ[R] Chains K.barycentricSubdivision R (n+1) :=
  (incl K R s (n+1)).comp ((localCone K R s n).comp (restrict K R s n))

theorem supported_coneAt (R : Type u) [CommRing R] (s : K.Simplex) (n : ℕ)
    (c : Chains K.barycentricSubdivision R n) : Supported K R s (coneAt K R s n c) := by
  apply (supported_iff_range K R s _).2
  exact ⟨_, rfl⟩

theorem incl_restrict (R : Type u) [CommRing R] (s : K.Simplex) {n : ℕ}
    (c : Chains K.barycentricSubdivision R n) (hc : Supported K R s c) :
    incl K R s n (restrict K R s n c) = c := by
  obtain ⟨d, rfl⟩ := (supported_iff_range K R s c).1 hc
  rw [restrict_incl]

theorem incl_boundary (R : Type u) [CommRing R] (s : K.Simplex) (n : ℕ)
    (c : Chains (Carrier K s) R (n+1)) :
    boundary R R n (incl K R s (n+1) c) = incl K R s n (boundary R R n c) := by
  exact LinearMap.congr_fun (P202.OrientedSimplicialAlgebra.pushforward_boundary R R (inc K s) n) c

theorem boundary_coneAt (R : Type u) [CommRing R] (s : K.Simplex) (n : ℕ)
    (c : Chains K.barycentricSubdivision R (n+1)) (hc : Supported K R s c)
    (hz : boundary R R n c = 0) :
    boundary R R (n+1) (coneAt K R s (n+1) c) = c := by
  obtain ⟨d, rfl⟩ := (supported_iff_range K R s c).1 hc
  have hd : boundary R R n d = 0 := by
    apply P202.OrientedSimplicialAlgebra.pushforward_inclusion_injective R R
      (K := Carrier K s) (L := K.barycentricSubdivision) (fun _ h => h.1) n
    change incl K R s n (boundary R R n d) = incl K R s n 0
    rw [← incl_boundary, hz, map_zero]
  change boundary R R (n+1) (incl K R s (n+2)
    (localCone K R s (n+1) (restrict K R s (n+1) (incl K R s (n+1) d)))) = _
  rw [restrict_incl, incl_boundary]
  unfold localCone
  rw [OrientedCone.boundary_cone, hd, map_zero, sub_zero]

theorem incl_augmentation (R : Type u) [CommRing R] (s : K.Simplex)
    (c : Chains (Carrier K s) R 0) :
    P202Specs.SingularChains.sumCoefficients R R _ (incl K R s 0 c) =
      P202Specs.SingularChains.sumCoefficients R R _ c := by
  have h : (P202Specs.SingularChains.sumCoefficients R R _).comp (incl K R s 0) =
      P202Specs.SingularChains.sumCoefficients R R _ := by
    apply OrientedCone.linearMap_ext_on_single_one
    intro t
    rw [incl_eq]
    simp [Finsupp.lmapDomain_apply, P202Specs.SingularChains.sumCoefficients]
  exact LinearMap.congr_fun h c

theorem boundary_coneAt_zero (R : Type u) [CommRing R] (s : K.Simplex)
    (c : Chains K.barycentricSubdivision R 0) (hc : Supported K R s c)
    (hz : P202Specs.SingularChains.sumCoefficients R R _ c = 0) :
    boundary R R 0 (coneAt K R s 0 c) = c := by
  obtain ⟨d, rfl⟩ := (supported_iff_range K R s c).1 hc
  have hd : P202Specs.SingularChains.sumCoefficients R R _ d = 0 := by
    rwa [incl_augmentation] at hz
  change boundary R R 0 (incl K R s 1
    (localCone K R s 0 (restrict K R s 0 (incl K R s 0 d)))) = _
  rw [restrict_incl, incl_boundary]
  unfold localCone
  rw [OrientedCone.boundary_cone_zero R s _ (subdivisionCarrier_apex K s), hd,
    Finsupp.single_zero, sub_zero]

theorem supported_mono (R : Type u) [CommRing R] {s t : K.Simplex}
    (hst : s.1 ⊆ t.1) {n : ℕ} {c : Chains K.barycentricSubdivision R n}
    (hc : Supported K R s c) : Supported K R t c := by
  intro a ha i
  exact (hc a ha i).trans hst

theorem supported_sum (R : Type u) [CommRing R] (s : K.Simplex)
    {I : Type*} (f : Finset I) {n : ℕ} (c : I → Chains K.barycentricSubdivision R n)
    (hc : ∀ i ∈ f, Supported K R s (c i)) : Supported K R s (∑ i ∈ f, c i) := by
  apply (supported_iff_range K R s _).2
  apply Submodule.sum_mem
  intro i hi
  exact (supported_iff_range K R s _).1 (hc i hi)

theorem supported_zsmul (R : Type u) [CommRing R] (s : K.Simplex) {n : ℕ}
    (c : Chains K.barycentricSubdivision R n) (hc : Supported K R s c) (a : ℤ) :
    Supported K R s (a • c) := by
  apply (supported_iff_range K R s _).2
  exact zsmul_mem ((supported_iff_range K R s _).1 hc) a

def coarse {n : ℕ} (s : Simplex K n) : K.Simplex := ⟨Finset.univ.image s.1, s.2⟩

def map (R : Type u) [CommRing R] :
    (n : ℕ) → Chains K R n →ₗ[R] Chains K.barycentricSubdivision R n
  | 0 => Finsupp.linearCombination R (fun s => Finsupp.single
      (OrientedCone.vertexSimplex (coarse K s)
        ((subdivisionCarrier_apex K (coarse K s)).1)) 1)
  | n+1 => Finsupp.linearCombination R (fun s =>
      coneAt K R (coarse K s) n (map R n (boundary R R n (Finsupp.single s 1))))

theorem map_zero_single (R : Type u) [CommRing R] (s : Simplex K 0) :
    map K R 0 (Finsupp.single s 1) = Finsupp.single
      (OrientedCone.vertexSimplex (coarse K s)
        ((subdivisionCarrier_apex K (coarse K s)).1)) 1 := by
  simp [map, Finsupp.linearCombination_single]

theorem map_succ_single (R : Type u) [CommRing R] (n : ℕ) (s : Simplex K (n+1)) :
    map K R (n+1) (Finsupp.single s 1) =
      coneAt K R (coarse K s) n (map K R n (boundary R R n (Finsupp.single s 1))) := by
  simp [map, Finsupp.linearCombination_single]

theorem map_supported (R : Type u) [CommRing R] (n : ℕ) (s : Simplex K n) :
    Supported K R (coarse K s) (map K R n (Finsupp.single s 1)) := by
  cases n with
  | zero =>
    rw [map_zero_single]
    intro t ht i
    have ht' := (Finsupp.mem_support_single _ _ _).mp ht
    obtain ⟨rfl, _⟩ := ht'
    change (coarse K s).1 ⊆ (coarse K s).1
    exact Finset.Subset.refl _
  | succ n =>
    rw [map_succ_single]
    exact supported_coneAt K R _ n _

theorem coarse_face_subset {n : ℕ} (s : Simplex K (n+1)) (i : Fin (n+2)) :
    (coarse K (face i s)).1 ⊆ (coarse K s).1 := by
  intro x hx
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨i.succAbove j, Finset.mem_univ _, rfl⟩

theorem map_boundary_supported (R : Type u) [CommRing R] (n : ℕ)
    (s : Simplex K (n+1)) :
    Supported K R (coarse K s) (map K R n (boundary R R n (Finsupp.single s 1))) := by
  rw [P202.OrientedSimplicialAlgebra.boundary_single]
  simp only [map_sum, map_zsmul]
  apply supported_sum
  intro i hi
  apply supported_zsmul
  exact supported_mono K R (coarse_face_subset K s i) (map_supported K R n _)

theorem map_augmentation (R : Type u) [CommRing R] (c : Chains K R 0) :
    P202Specs.SingularChains.sumCoefficients R R _ (map K R 0 c) =
      P202Specs.SingularChains.sumCoefficients R R _ c := by
  have h : (P202Specs.SingularChains.sumCoefficients R R _).comp (map K R 0) =
      P202Specs.SingularChains.sumCoefficients R R _ := by
    apply OrientedCone.linearMap_ext_on_single_one
    intro s
    change P202Specs.SingularChains.sumCoefficients R R _ (map K R 0 (Finsupp.single s 1)) = _
    rw [map_zero_single]
    simp [P202Specs.SingularChains.sumCoefficients]
  exact LinearMap.congr_fun h c

theorem augmentation_boundary (R : Type u) [CommRing R] (c : Chains K R 1) :
    P202Specs.SingularChains.sumCoefficients R R _ (boundary R R 0 c) = 0 := by
  have h : (P202Specs.SingularChains.sumCoefficients R R _).comp (boundary R R (K := K) 0) = 0 := by
    apply OrientedCone.linearMap_ext_on_single_one
    intro s
    change P202Specs.SingularChains.sumCoefficients R R _ (boundary R R 0 (Finsupp.single s 1)) = 0
    rw [P202.OrientedSimplicialAlgebra.boundary_single]
    simp only [map_sum, map_zsmul]
    simp [Fin.sum_univ_two, P202Specs.SingularChains.sumCoefficients]
  exact LinearMap.congr_fun h c

theorem map_boundary (R : Type u) [CommRing R] (n : ℕ) :
    (boundary R R n).comp (map K R (n+1)) =
      (map K R n).comp (boundary R R n) := by
  induction n with
  | zero =>
    apply OrientedCone.linearMap_ext_on_single_one
    intro s
    change boundary R R 0 (map K R 1 (Finsupp.single s 1)) = _
    rw [map_succ_single]
    apply boundary_coneAt_zero
    · exact map_boundary_supported K R 0 s
    · rw [map_augmentation]
      exact augmentation_boundary K R _
  | succ n ih =>
    apply OrientedCone.linearMap_ext_on_single_one
    intro s
    change boundary R R (n+1) (map K R (n+2) (Finsupp.single s 1)) = _
    rw [map_succ_single]
    apply boundary_coneAt
    · exact map_boundary_supported K R (n+1) s
    · change ((boundary R R n).comp (map K R (n+1))) _ = 0
      rw [ih]
      change map K R n ((boundary R R n).comp (boundary R R (n+1)) (Finsupp.single s 1)) = 0
      rw [P202.OrientedSimplicialAlgebra.boundary_squared]
      simp

/-- The carried barycentric subdivision map on the original ordinary chains. -/
def chainMap (R : Type u) [CommRing R] :
    complex R R (K := K) ⟶ complex R R (K := K.barycentricSubdivision) :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (map K R n)) (by
    intro n
    apply ModuleCat.hom_ext
    change (((complex R R (K := K.barycentricSubdivision)).d (n+1) n).hom).comp (map K R (n+1)) =
      (map K R n).comp (((complex R R (K := K)).d (n+1) n).hom)
    rw [P202.OrientedSimplicialAlgebra.boundary_eq R R,
      P202.OrientedSimplicialAlgebra.boundary_eq R R]
    exact map_boundary K R n)

@[simp] theorem chainMap_f (R : Type u) [CommRing R] (n : ℕ) :
    ((chainMap K R).f n).hom = map K R n := rfl

end Subdivision
end P202.LefschetzFixedPoint

namespace P202.LefschetzFixedPoint
attribute [local instance] P202Specs.OrientedSimplicialAlgebra.vertexOrder
open P202.Cellular P202.Cellular.AbstractSimplicialComplex
open P202Specs.LefschetzFixedPoint

def activeRealizationHom {V W : Type w} {K : AbstractSimplicialComplex V}
    {L : AbstractSimplicialComplex W} (g : SimplicialMap K L) :
    TopCat.of K.Realization ⟶ TopCat.of L.Realization :=
  TopCat.ofHom ⟨g.realization, P202.Topology.simplicialMap_continuous g⟩

/-- Only the rational absolute part of the full comparison premise is needed
by the finite chain argument. This is a derived interface, never an axiom. -/
def RationalComparison : Prop :=
  ∀ {V : Type w} (K : AbstractSimplicialComplex V),
    ∃ F : P202Specs.SimplicialComparison.SimplicialComparisonData ℚ ℚ K
      (P202Specs.RelativeParametrizations.Simplicial.Subcomplex.empty K),
      ∀ q : ℕ, IsIso (homologyMap F.absolute q)

/-- The corresponding rational absolute naturality interface, including
maps that collapse vertices. -/
def RationalNaturality : Prop :=
  ∀ {V W : Type w} (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (g : SimplicialMap K L) (w₀ : W)
    (T : P202Specs.OrientedSimplicialAlgebra.complex ℚ ℚ (K := K) ⟶
      P202Specs.OrientedSimplicialAlgebra.complex ℚ ℚ (K := L))
    (hT : ∀ n, (T.f n).hom = P202Specs.OrientedSimplicialAlgebra.pushforward ℚ ℚ
      (extendActiveMap g w₀) n)
    (F : P202Specs.SimplicialComparison.SimplicialComparisonData ℚ ℚ K
      (P202Specs.RelativeParametrizations.Simplicial.Subcomplex.empty K))
    (G : P202Specs.SimplicialComparison.SimplicialComparisonData ℚ ℚ L
      (P202Specs.RelativeParametrizations.Simplicial.Subcomplex.empty L)) (n : ℕ),
    homologyMap T n ≫ homologyMap G.absolute n =
      homologyMap F.absolute n ≫ rationalHomologyMap (activeRealizationHom g) n

theorem active_naturality
    (naturality : P202Specs.SimplicialComparison.simplicialNaturality_type.{0,0,w})
    {V W : Type w} (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (g : SimplicialMap K L) (w₀ : W)
    (T : P202Specs.OrientedSimplicialAlgebra.complex ℚ ℚ (K := K) ⟶
      P202Specs.OrientedSimplicialAlgebra.complex ℚ ℚ (K := L))
    (hT : ∀ n, (T.f n).hom = P202Specs.OrientedSimplicialAlgebra.pushforward ℚ ℚ
      (extendActiveMap g w₀) n)
    (F : P202Specs.SimplicialComparison.SimplicialComparisonData ℚ ℚ K
      (P202Specs.RelativeParametrizations.Simplicial.Subcomplex.empty K))
    (G : P202Specs.SimplicialComparison.SimplicialComparisonData ℚ ℚ L
      (P202Specs.RelativeParametrizations.Simplicial.Subcomplex.empty L)) (n : ℕ) :
    homologyMap T n ≫ homologyMap G.absolute n =
      homologyMap F.absolute n ≫ rationalHomologyMap (activeRealizationHom g) n := by
  obtain ⟨a, ha, U, _, _, hU, _, _, hnat⟩ := naturality ℚ ℚ K L
    (P202Specs.RelativeParametrizations.Simplicial.Subcomplex.empty K)
    (P202Specs.RelativeParametrizations.Simplicial.Subcomplex.empty L)
    (extendActiveMap g w₀) (by intro s hs; exact hs.elim)
  have ha' : a = activeRealizationHom g := by
    ext x
    apply Subtype.ext
    exact (ha x).trans (extendActiveMap_realization g w₀ x).symm
  have hU' : U = T := by
    apply HomologicalComplex.hom_ext
    intro j
    apply ModuleCat.hom_ext
    exact (hU j).trans (hT j).symm
  simpa only [ha', hU'] using (hnat F G n).1

/-- A carried subdivision map with a simplicial left inverse represents the
realization identity. Naturality and the approximation homotopy then identify
the induced finite chain endomorphism with the required singular homology map. -/
theorem finite_model_equivariance
    (comparison : RationalComparison.{w})
    (naturality : RationalNaturality.{w})
    {V W : Type w} (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (w₀ : V) (p g : SimplicialMap L K)
    (S : P202Specs.OrientedSimplicialAlgebra.complex ℚ ℚ (K := K) ⟶
      P202Specs.OrientedSimplicialAlgebra.complex ℚ ℚ (K := L))
    (P G : P202Specs.OrientedSimplicialAlgebra.complex ℚ ℚ (K := L) ⟶
      P202Specs.OrientedSimplicialAlgebra.complex ℚ ℚ (K := K))
    (hP : ∀ n, (P.f n).hom = P202Specs.OrientedSimplicialAlgebra.pushforward ℚ ℚ
      (extendActiveMap p w₀) n)
    (hG : ∀ n, (G.f n).hom = P202Specs.OrientedSimplicialAlgebra.pushforward ℚ ℚ
      (extendActiveMap g w₀) n)
    (hSP : S ≫ P = 𝟙 _)
    (f : TopCat.of K.Realization ⟶ TopCat.of K.Realization)
    (H : TopCat.Homotopy (activeRealizationHom g) (activeRealizationHom p ≫ f)) :
    ∃ e : ∀ n, (P202Specs.OrientedSimplicialAlgebra.complex ℚ ℚ (K := K)).homology n
      ≃ₗ[ℚ] rationalHomology (TopCat.of K.Realization) n,
      ∀ n x, e n ((homologyMap (S ≫ G) n) x) = rationalHomologyMap f n (e n x) := by
  obtain ⟨A, hA⟩ := comparison K
  obtain ⟨B, _⟩ := comparison L
  let := hA
  refine ⟨fun n => (asIso (homologyMap A.absolute n)).toLinearEquiv, ?_⟩
  intro n x
  have hnP := naturality L K p w₀ P hP B A n
  have hnG := naturality L K g w₀ G hG B A n
  have hhom := (P202.PrismHomotopy.chainPrism ℚ ℚ H).homologyMap_eq n
  change rationalHomologyMap (activeRealizationHom p ≫ f) n =
    rationalHomologyMap (activeRealizationHom g) n at hhom
  have hcomp : rationalHomologyMap (activeRealizationHom p ≫ f) n =
      rationalHomologyMap (activeRealizationHom p) n ≫ rationalHomologyMap f n := by
    exact (P202Specs.SingularChains.chainFunctor ℚ ℚ ⋙ homologyFunctor _ _ n).map_comp _ _
  have hS : homologyMap S n ≫ homologyMap P n = 𝟙 _ := by
    rw [← homologyMap_comp, hSP, homologyMap_id]
  have heq : homologyMap (S ≫ G) n ≫ homologyMap A.absolute n =
      homologyMap A.absolute n ≫ rationalHomologyMap f n := by
    calc
      _ = homologyMap S n ≫ homologyMap B.absolute n ≫
          rationalHomologyMap (activeRealizationHom g) n := by
        rw [homologyMap_comp, Category.assoc, hnG]
      _ = homologyMap S n ≫ homologyMap B.absolute n ≫
          rationalHomologyMap (activeRealizationHom p) n ≫ rationalHomologyMap f n := by
        rw [← hhom, hcomp]
      _ = (homologyMap S n ≫ homologyMap P n) ≫ homologyMap A.absolute n ≫
          rationalHomologyMap f n := by
        simpa only [Category.assoc] using congrArg
          (fun z => homologyMap S n ≫ z ≫ rationalHomologyMap f n) hnP.symm
      _ = _ := by rw [hS, Category.id_comp]
  exact congr($(heq) x)

/-- A strengthened approximation interface retaining the star carrier needed
for the displacement estimate. Both support control and the homotopy are
conclusions of the accepted open-star construction. -/
theorem approximation_with_carrier {V W : Type w}
    (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W) (hK : K.IsFinite)
    (f : C(K.Realization, L.Realization)) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (g : SimplicialMap (K.Subdivision n) L)
        (h : (K.Subdivision n).Realization ≃ₜ K.Realization)
        (H : C((K.Subdivision n).Realization × Interval, L.Realization)),
        (h : _ → _) = K.iteratedSubdivisionMap n ∧
        (∀ x, H (x, 0) = f (h x)) ∧ (∀ x, H (x, 1) = g.realization x) ∧
        ∀ x, (g.realization x).1.weights.support ⊆ (f (h x)).1.weights.support := by
  obtain ⟨N, hN⟩ := P202.Topology.starRefinement K L hK f
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h, hh⟩ := P202.Topology.subdivisionHomeomorphism K hK n
  choose a ha using hN n hn
  let f' : C((K.Subdivision n).Realization, L.Realization) := f.comp ⟨h, h.continuous_toFun⟩
  have hstar : ∀ v x, x ∈ (K.Subdivision n).openStar v →
      0 < (f' x).1.weights (a v).1 := by
    intro v x hx
    change 0 < (f (h x)).1.weights (a v).1
    rw [hh]
    exact ha v hx
  obtain ⟨g, hg, hsupp⟩ := P202.Topology.starCriterion_map (K.Subdivision n) L f'
    (fun v => (a v).1) hstar
  obtain ⟨H, h0, h1, _⟩ := P202.Topology.star_homotopy (K.Subdivision n) L
    (P202.Topology.finite_iteratedSubdivision K hK n) f' g (by rw [hg]; exact hstar)
  exact ⟨g, h, H, hh, h0, h1, hsupp⟩

end P202.LefschetzFixedPoint

namespace P202.LefschetzFixedPoint
attribute [local instance] P202Specs.OrientedSimplicialAlgebra.vertexOrder
open P202.Cellular P202.Cellular.AbstractSimplicialComplex
open P202Specs.OrientedSimplicialAlgebra
namespace Subdivision
variable {V : Type w} (K : AbstractSimplicialComplex V)

def lastVertexChainMap (R : Type u) [CommRing R] :
    complex R R (K := K.barycentricSubdivision) ⟶ complex R R (K := K) :=
  Classical.choose (P202.OrientedSimplicialAlgebra.pushforward_chainMap R R (lastVertexOrientedMap K))

@[simp] theorem lastVertexChainMap_f (R : Type u) [CommRing R] (n : ℕ) :
    ((lastVertexChainMap K R).f n).hom = pushforward R R (lastVertexOrientedMap K) n :=
  Classical.choose_spec (P202.OrientedSimplicialAlgebra.pushforward_chainMap R R (lastVertexOrientedMap K)) n

theorem chainMap_lastVertex (R : Type u) [CommRing R] :
    chainMap K R ≫ lastVertexChainMap K R = 𝟙 _ := by
  apply CarrierIdentity.carried_chainMap_eq_id R
  · intro n s t ht
    change t ∈ (((lastVertexChainMap K R).f n).hom (((chainMap K R).f n).hom (Finsupp.single s 1))).support at ht
    rw [chainMap_f, lastVertexChainMap_f] at ht
    apply CarrierIdentity.pushforward_support_vertex_subset R _ n _ _ ?_ t ht
    intro u hu
    apply lastVertexOrientedMap_carried K (coarse K s) u
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact map_supported K R n s u hu i
  · intro c
    change P202Specs.SingularChains.sumCoefficients R R _
      (((lastVertexChainMap K R).f 0).hom (((chainMap K R).f 0).hom c)) = _
    rw [chainMap_f, lastVertexChainMap_f]
    exact (CarrierIdentity.augmentation_pushforward_zero R (lastVertexOrientedMap K)
      (map K R 0 c)).trans (map_augmentation K R c)

def iteratedChainMap (R : Type u) [CommRing R] :
    ∀ n, complex R R (K := K) ⟶ complex R R (K := K.Subdivision n)
  | 0 => 𝟙 _
  | n+1 => iteratedChainMap R n ≫ chainMap (K.Subdivision n) R

def iteratedLastVertexChainMap (R : Type u) [CommRing R] :
    ∀ n, complex R R (K := K.Subdivision n) ⟶ complex R R (K := K)
  | 0 => 𝟙 _
  | n+1 => lastVertexChainMap (K.Subdivision n) R ≫ iteratedLastVertexChainMap R n

theorem iteratedChainMap_lastVertex (R : Type u) [CommRing R] :
    ∀ n, iteratedChainMap K R n ≫ iteratedLastVertexChainMap K R n = 𝟙 _
  | 0 => by simp [iteratedChainMap, iteratedLastVertexChainMap]
  | n+1 => by
    change (iteratedChainMap K R n ≫ chainMap (K.Subdivision n) R) ≫
      (lastVertexChainMap (K.Subdivision n) R ≫ iteratedLastVertexChainMap K R n) = _
    rw [Category.assoc, ← Category.assoc (chainMap (K.Subdivision n) R),
      chainMap_lastVertex, Category.id_comp, iteratedChainMap_lastVertex R n]

def iteratedLastVertexOrientedMap :
    ∀ n, P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K.Subdivision n) K
  | 0 => P202Specs.OrientedSimplicialAlgebra.SimplicialMap.id K
  | n+1 => P202Specs.OrientedSimplicialAlgebra.SimplicialMap.comp
      (iteratedLastVertexOrientedMap n) (lastVertexOrientedMap (K.Subdivision n))

theorem iteratedLastVertexChainMap_f (R : Type u) [CommRing R] :
    ∀ r n, ((iteratedLastVertexChainMap K R r).f n).hom =
      pushforward R R (iteratedLastVertexOrientedMap K r) n
  | 0, n => by
    simp only [iteratedLastVertexChainMap, HomologicalComplex.id_f, ModuleCat.hom_id,
      iteratedLastVertexOrientedMap]
    exact (P202.OrientedSimplicialAlgebra.pushforward_id R R n).symm
  | r+1, n => by
    change ((iteratedLastVertexChainMap K R r).f n).hom.comp
      (((lastVertexChainMap (K.Subdivision r) R).f n).hom) = _
    rw [iteratedLastVertexChainMap_f R r n, lastVertexChainMap_f]
    exact P202.OrientedSimplicialAlgebra.pushforward_comp R R
      (iteratedLastVertexOrientedMap K r) (lastVertexOrientedMap (K.Subdivision r)) n

def iteratedCanonicalHom : ∀ n,
    TopCat.of (K.Subdivision n).Realization ⟶ TopCat.of K.Realization
  | 0 => 𝟙 _
  | n+1 => canonicalSubdivisionHom (K.Subdivision n) ≫ iteratedCanonicalHom n

def iteratedLastVertexHom : ∀ n,
    TopCat.of (K.Subdivision n).Realization ⟶ TopCat.of K.Realization
  | 0 => 𝟙 _
  | n+1 => lastVertexHom (K.Subdivision n) ≫ iteratedLastVertexHom n

@[simp] theorem iteratedCanonicalHom_apply : ∀ n x,
    iteratedCanonicalHom K n x = K.iteratedSubdivisionMap n x
  | 0, _ => rfl
  | n+1, _ => iteratedCanonicalHom_apply n _

theorem iteratedLastVertexHom_realization : ∀ n x,
    (iteratedLastVertexHom K n x).1 = x.1.map (iteratedLastVertexOrientedMap K n).vertices
  | 0, x => by
    change x.1 = x.1.map _root_.id
    exact (Convexity.StdSimplex.map_id x.1).symm
  | n+1, x => by
    change (iteratedLastVertexHom K n (lastVertexHom (K.Subdivision n) x)).1 = _
    rw [iteratedLastVertexHom_realization]
    change ((lastVertexMap (K.Subdivision n)).realization x).1.map
      (iteratedLastVertexOrientedMap K n).vertices = _
    rw [lastVertexOrientedMap_realization, Convexity.StdSimplex.map_map]
    rfl

theorem iteratedLastVertex_homotopic (hK : K.IsFinite) : ∀ n,
    Nonempty (TopCat.Homotopy (iteratedCanonicalHom K n) (iteratedLastVertexHom K n))
  | 0 => ⟨ContinuousMap.Homotopy.refl _⟩
  | n+1 => by
    obtain ⟨H⟩ := iteratedLastVertex_homotopic hK n
    obtain ⟨G⟩ := lastVertex_homotopic (K.Subdivision n)
      (P202.Topology.finite_iteratedSubdivision K hK n)
    exact ⟨ContinuousMap.Homotopy.comp H G⟩

end Subdivision
end P202.LefschetzFixedPoint

namespace P202.LefschetzFixedPoint.GeometricDiagonal
open P202.Cellular P202.Cellular.AbstractSimplicialComplex
open P202Specs.OrientedSimplicialAlgebra
attribute [local instance] P202Specs.OrientedSimplicialAlgebra.vertexOrder

variable {V W : Type w} {K : AbstractSimplicialComplex V}
    {L : AbstractSimplicialComplex W}

theorem image_vertex_set_ne_of_disjoint
    (g : P202.Cellular.AbstractSimplicialComplex.SimplicialMap L K) (v₀ : V)
    {n : ℕ} (t : Simplex L n) (s : Simplex K n)
    (hdisj : Disjoint
      (g.realization '' Set.range (L.simplexChart ⟨Finset.univ.image t.1, t.2⟩))
      (Set.range (K.simplexChart ⟨Finset.univ.image s.1, s.2⟩))) :
    Finset.univ.image ((extendActiveMap g v₀).vertices ∘ t.1) ≠
      Finset.univ.image s.1 := by
  classical
  intro he
  let v : L.Vertex := ⟨t.1 0, vertex_mem_of_mem t.2
    (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)⟩
  have hx : P202.Topology.vertexPoint L v ∈
      Set.range (L.simplexChart ⟨Finset.univ.image t.1, t.2⟩) := by
    apply P202.Topology.vertexPoint_mem_simplexChart
    exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  have hy : g.realization (P202.Topology.vertexPoint L v) ∈
      Set.range (K.simplexChart ⟨Finset.univ.image s.1, s.2⟩) := by
    rw [P202.Topology.mem_simplexChart_iff_support_subset]
    rw [extendActiveMap_realization g v₀]
    change ((Convexity.StdSimplex.single v.1).map (extendActiveMap g v₀).vertices).weights.support ⊆ _
    rw [Convexity.StdSimplex.map_single]
    simp only [Convexity.StdSimplex.weights_single, Finsupp.support_single _ (one_ne_zero : (1 : ℝ) ≠ 0),
      Finset.singleton_subset_iff]
    rw [← he]
    exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  exact Set.disjoint_left.mp hdisj ⟨_, hx, rfl⟩ hy

theorem subdivision_pushforward_diagonal_zero_of_disjoint
    (R : Type u) [CommRing R]
    (g : P202.Cellular.AbstractSimplicialComplex.SimplicialMap L K) (v₀ : V)
    (n : ℕ) (S : Chains K R n →ₗ[R] Chains L R n)
    (hdisj : ∀ (s : Simplex K n) (t : Simplex L n), t ∈ (S (Finsupp.single s 1)).support → Disjoint
      (g.realization '' Set.range (L.simplexChart ⟨Finset.univ.image t.1, t.2⟩))
      (Set.range (K.simplexChart ⟨Finset.univ.image s.1, s.2⟩))) :
    ∀ s, pushforward R R (extendActiveMap g v₀) n (S (Finsupp.single s 1)) s = 0 := by
  intro s
  apply subdivision_pushforward_diagonal_zero
  intro t ht
  exact image_vertex_set_ne_of_disjoint g v₀ t s (hdisj s t ht)

theorem trace_subdivision_pushforward_zero_of_disjoint
    (R : Type u) [CommRing R] (hK : K.IsFinite)
    (g : P202.Cellular.AbstractSimplicialComplex.SimplicialMap L K) (v₀ : V)
    (n : ℕ) (S : Chains K R n →ₗ[R] Chains L R n)
    (hdisj : ∀ (s : Simplex K n) (t : Simplex L n), t ∈ (S (Finsupp.single s 1)).support → Disjoint
      (g.realization '' Set.range (L.simplexChart ⟨Finset.univ.image t.1, t.2⟩))
      (Set.range (K.simplexChart ⟨Finset.univ.image s.1, s.2⟩))) :
    LinearMap.trace R (Chains K R n) ((pushforward R R (extendActiveMap g v₀) n).comp S) = 0 := by
  let := finite_oriented_simplex K hK n
  apply trace_finsupp_zero_of_diagonal_zero
  exact subdivision_pushforward_diagonal_zero_of_disjoint R g v₀ n S hdisj

end P202.LefschetzFixedPoint.GeometricDiagonal

namespace P202.LefschetzFixedPoint
attribute [local instance] P202Specs.OrientedSimplicialAlgebra.vertexOrder
open P202.Cellular P202.Cellular.AbstractSimplicialComplex

/-- A fine simplicial approximation separated from every coarse simplex that
carries its source simplex. The two changes of coordinates are canonical. -/
structure SeparatedApproximation {V : Type w} (K : AbstractSimplicialComplex V)
    (f : TopCat.of K.Realization ⟶ TopCat.of K.Realization) where
  coarse : ℕ
  fine : ℕ
  coarseHomeo : (K.Subdivision coarse).Realization ≃ₜ K.Realization
  coarse_canonical : (coarseHomeo : _ → _) = K.iteratedSubdivisionMap coarse
  fineHomeo : ((K.Subdivision coarse).Subdivision fine).Realization ≃ₜ
    (K.Subdivision coarse).Realization
  fine_canonical : (fineHomeo : _ → _) = (K.Subdivision coarse).iteratedSubdivisionMap fine
  approximation : SimplicialMap ((K.Subdivision coarse).Subdivision fine) (K.Subdivision coarse)
  homotopy : TopCat.Homotopy
    ((TopCat.isoOfHomeo fineHomeo).hom ≫ conjugateMap coarseHomeo.symm f)
    (activeRealizationHom approximation)
  separated : ∀ (s : (K.Subdivision coarse).Simplex)
    (t : ((K.Subdivision coarse).Subdivision fine).Simplex),
    fineHomeo '' Set.range (((K.Subdivision coarse).Subdivision fine).simplexChart t) ⊆
      Set.range ((K.Subdivision coarse).simplexChart s) →
    Disjoint (approximation.realization '' Set.range
      (((K.Subdivision coarse).Subdivision fine).simplexChart t))
      (Set.range ((K.Subdivision coarse).simplexChart s))

/-- Positive displacement, shrinking mesh, and the star approximation give
the separated finite chain geometry. No connectedness or nonemptiness is used. -/
theorem exists_separatedApproximation {V : Type w} (K : AbstractSimplicialComplex V)
    (hK : K.IsFinite) (f : TopCat.of K.Realization ⟶ TopCat.of K.Realization)
    (hf : ∀ x, f x ≠ x) : Nonempty (SeparatedApproximation K f) := by
  obtain ⟨d, hd, _⟩ := P202.Topology.finiteMetricRealization K hK
  let d' := d.replaceTopology hd.symm
  let : MetricSpace K.Realization := d'
  let : CompactSpace K.Realization := ⟨P202.Topology.finiteRealization_compact K hK⟩
  obtain ⟨δ, hδ, hdisp⟩ := positive_displacement f.hom hf
  obtain ⟨m, hm⟩ := P202.Topology.shrinkingMeshAndStars K hK d' rfl (δ / 3) (by positivity)
  obtain ⟨h₀, hh₀⟩ := P202.Topology.subdivisionHomeomorphism K hK m
  let L := K.Subdivision m
  have hL : L.IsFinite := P202.Topology.finite_iteratedSubdivision K hK m
  let fL : TopCat.of L.Realization ⟶ TopCat.of L.Realization := conjugateMap h₀.symm f
  obtain ⟨n, hn⟩ := approximation_with_carrier L L hL fL.hom
  obtain ⟨g, h₁, H, hh₁, h0, h1, hsupp⟩ := hn n le_rfl
  have hmesh (s : L.Simplex) {x y : L.Realization}
      (hx : x ∈ Set.range (L.simplexChart s))
      (hy : y ∈ Set.range (L.simplexChart s)) : dist (h₀ x) (h₀ y) < δ / 3 := by
    have hdiam := (hm m le_rfl).1 s
    rw [← hh₀] at hdiam
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < δ / 3)).mp
      ((P202.Topology.distance_le_diameter d'.toPseudoMetricSpace
        (Set.mem_image_of_mem _ hx) (Set.mem_image_of_mem _ hy)).trans_lt hdiam)
  have herror (x : (L.Subdivision n).Realization) :
      dist (h₀ (g.realization x)) (f (h₀ (h₁ x))) < δ / 3 := by
    let s : L.Simplex := ⟨(fL (h₁ x)).1.weights.support, (fL (h₁ x)).2⟩
    have hg : g.realization x ∈ Set.range (L.simplexChart s) :=
      (P202.Topology.mem_simplexChart_iff_support_subset L s _).mpr (hsupp x)
    have hfx : fL (h₁ x) ∈ Set.range (L.simplexChart s) :=
      (P202.Topology.mem_simplexChart_iff_support_subset L s _).mpr (Finset.Subset.refl _)
    have he : h₀ (fL (h₁ x)) = f (h₀ (h₁ x)) := h₀.apply_symm_apply _
    rw [← he]
    exact hmesh s hg hfx
  refine ⟨⟨m, n, h₀, hh₀, h₁, hh₁, g, homotopyOfProduct H h0 h1, ?_⟩⟩
  intro s t hts
  rw [Set.disjoint_left]
  rintro y ⟨x, hx, rfl⟩ hy
  have hx' : h₁ x ∈ Set.range (L.simplexChart s) := hts (Set.mem_image_of_mem _ hx)
  have h₁' := hmesh s hx' hy
  have h₂ := herror x
  have h₃ := dist_triangle (h₀ (h₁ x)) (h₀ (g.realization x)) (f (h₀ (h₁ x)))
  have h₄ := hdisp (h₀ (h₁ x))
  linarith

end P202.LefschetzFixedPoint

namespace P202.LefschetzFixedPoint
attribute [local instance] P202Specs.OrientedSimplicialAlgebra.vertexOrder
open P202.Cellular P202.Cellular.AbstractSimplicialComplex
open P202Specs.OrientedSimplicialAlgebra
namespace Subdivision
variable {V : Type w} (K : AbstractSimplicialComplex V)

def activeMapOfOriented {W : Type w} {L : AbstractSimplicialComplex W}
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L) :
    AbstractSimplicialComplex.SimplicialMap K L where
  vertex v := f.vertices v.1
  map_simplex s := by
    convert f.map_simplex s.1 s.2 using 1
    ext w
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.1, (mem_simplexVertices K s v).mp hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      let a : K.Vertex := ⟨v, vertex_mem_of_mem s.2 hv⟩
      exact ⟨a, (mem_simplexVertices K s a).mpr hv, rfl⟩

theorem activeMapOfOriented_realization {W : Type w} {L : AbstractSimplicialComplex W}
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L) (x : K.Realization) :
    ((activeMapOfOriented K f).realization x).1 = x.1.map f.vertices := by
  change (K.activeCoordinates x).map (fun v => f.vertices v.1) = _
  rw [← P202.Topology.activeCoordinates_map_val K x, Convexity.StdSimplex.map_map]

theorem extendActiveMap_pushforward_eq (R : Type u) [CommRing R]
    {W : Type w} {L : AbstractSimplicialComplex W}
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L)
    (w₀ : W) (n : ℕ) :
    pushforward R R (extendActiveMap (activeMapOfOriented K f) w₀) n = pushforward R R f n := by
  apply Finsupp.lhom_ext
  intro s a
  rw [P202.OrientedSimplicialAlgebra.pushforward_single,
    P202.OrientedSimplicialAlgebra.pushforward_single]
  congr 1
  apply Subtype.ext
  funext i
  let v : K.Vertex := ⟨s.1 i, vertex_mem_of_mem s.2
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩
  exact extendActiveVertices_on_vertex (activeMapOfOriented K f) w₀ v

def iteratedLastVertexMap (n : ℕ) :
    AbstractSimplicialComplex.SimplicialMap (K.Subdivision n) K :=
  activeMapOfOriented (K.Subdivision n) (iteratedLastVertexOrientedMap K n)

theorem iteratedLastVertexMap_realization (n : ℕ) (x : (K.Subdivision n).Realization) :
    (iteratedLastVertexMap K n).realization x = iteratedLastVertexHom K n x := by
  apply Subtype.ext
  exact (activeMapOfOriented_realization (K.Subdivision n) _ x).trans
    (iteratedLastVertexHom_realization K n x).symm

theorem iteratedLastVertexChainMap_active_f (R : Type u) [CommRing R] (r n : ℕ) (v₀ : V) :
    ((iteratedLastVertexChainMap K R r).f n).hom =
      pushforward R R (extendActiveMap (iteratedLastVertexMap K r) v₀) n := by
  rw [iteratedLastVertexChainMap_f]
  exact (extendActiveMap_pushforward_eq (K.Subdivision r) R
    (iteratedLastVertexOrientedMap K r) v₀ n).symm

theorem iteratedLastVertexMap_homotopic (hK : K.IsFinite) (n : ℕ) :
    Nonempty (TopCat.Homotopy (iteratedCanonicalHom K n)
      (TopCat.ofHom ⟨(iteratedLastVertexMap K n).realization,
        P202.Topology.simplicialMap_continuous (iteratedLastVertexMap K n)⟩)) := by
  have heq : TopCat.ofHom ⟨(iteratedLastVertexMap K n).realization,
      P202.Topology.simplicialMap_continuous (iteratedLastVertexMap K n)⟩ =
      iteratedLastVertexHom K n := by
    ext x
    exact iteratedLastVertexMap_realization K n x
  rw [heq]
  exact iteratedLastVertex_homotopic K hK n

end Subdivision
end P202.LefschetzFixedPoint

namespace P202.LefschetzFixedPoint.GeometricCarrier
open P202.Cellular P202.Cellular.AbstractSimplicialComplex
open P202Specs.OrientedSimplicialAlgebra
attribute [local instance] P202Specs.OrientedSimplicialAlgebra.vertexOrder

variable {V : Type w} (K : AbstractSimplicialComplex V)

theorem subdivisionMap_chart_carried (s : K.Simplex)
    (t : K.barycentricSubdivision.Simplex)
    (ht : ∀ a ∈ t.1, a.1 ⊆ s.1) :
    K.subdivisionMap '' Set.range (K.barycentricSubdivision.simplexChart t) ⊆
      Set.range (K.simplexChart s) := by
  rintro y ⟨x, hx, rfl⟩
  have hxs := (P202.Topology.mem_simplexChart_iff_support_subset
    K.barycentricSubdivision t x).mp hx
  rw [P202.Topology.mem_simplexChart_iff_support_subset]
  obtain ⟨a, ha, hmax⟩ := chain_has_largest x.property
  rw [P202.Topology.subdivisionMap_weights_linear,
    P202.Topology.barycentricEvalWeights_support K x.1.weights x.1.nonneg x.property ha hmax]
  exact ht a (hxs ha)

theorem mem_support_linearMap_exists (R : Type u) [Semiring R]
    {I J : Type*} (G : (I →₀ R) →ₗ[R] (J →₀ R))
    (c : I →₀ R) (j : J) (hj : j ∈ (G c).support) :
    ∃ i ∈ c.support, j ∈ (G (Finsupp.single i 1)).support := by
  classical
  by_contra h
  have hz : G c j = 0 := by
    apply coefficient_zero_on_supported_chain
    intro i hi
    exact Finsupp.notMem_support_iff.mp (fun hj => h ⟨i, hi, hj⟩)
  exact Finsupp.mem_support_iff.mp hj hz

theorem geometric_carrier_comp (R : Type u) [Semiring R]
    {I J N X Y Z : Type*}
    (F : (I →₀ R) →ₗ[R] (J →₀ R)) (G : (J →₀ R) →ₗ[R] (N →₀ R))
    (A : I → Set X) (B : J → Set Y) (C : N → Set Z)
    (h : Y → X) (p : Z → Y)
    (hF : ∀ i j, j ∈ (F (Finsupp.single i 1)).support → h '' B j ⊆ A i)
    (hG : ∀ j k, k ∈ (G (Finsupp.single j 1)).support → p '' C k ⊆ B j) :
    ∀ i k, k ∈ ((G.comp F) (Finsupp.single i 1)).support →
      (h ∘ p) '' C k ⊆ A i := by
  intro i k hk
  obtain ⟨j, hj, hkj⟩ := mem_support_linearMap_exists R G
    (F (Finsupp.single i 1)) k hk
  rintro x ⟨z, hz, rfl⟩
  exact hF i j hj ⟨p z, hG j k hkj ⟨z, hz, rfl⟩, rfl⟩

theorem map_chart_carried (R : Type u) [CommRing R] (n : ℕ)
    (s : Simplex K n) (t : Simplex K.barycentricSubdivision n)
    (ht : t ∈ (Subdivision.map K R n (Finsupp.single s 1)).support) :
    K.subdivisionMap '' Set.range (K.barycentricSubdivision.simplexChart
      (Subdivision.coarse K.barycentricSubdivision t)) ⊆
      Set.range (K.simplexChart (Subdivision.coarse K s)) := by
  classical
  apply subdivisionMap_chart_carried
  intro a ha
  simp only [Subdivision.coarse, Finset.mem_image, Finset.mem_univ, true_and] at ha
  obtain ⟨i, rfl⟩ := ha
  exact Subdivision.map_supported K R n s t ht i

theorem iteratedChainMap_chart_carried (R : Type u) [CommRing R] (n : ℕ)
    (s : Simplex K n) : ∀ r (t : Simplex (K.Subdivision r) n),
    t ∈ (((Subdivision.iteratedChainMap K R r).f n).hom (Finsupp.single s 1)).support →
    K.iteratedSubdivisionMap r '' Set.range ((K.Subdivision r).simplexChart
      (Subdivision.coarse (K.Subdivision r) t)) ⊆
      Set.range (K.simplexChart (Subdivision.coarse K s)) := by
  intro r
  induction r with
  | zero =>
    intro t ht
    change t ∈ (Finsupp.single s (1 : R)).support at ht
    have hts : t = s := (Finsupp.mem_support_single _ _ _).mp ht |>.1
    subst t
    rintro x ⟨y, hy, rfl⟩
    exact hy
  | succ r ih =>
    intro t ht
    change t ∈ ((((Subdivision.chainMap (K.Subdivision r) R).f n).hom).comp
      (((Subdivision.iteratedChainMap K R r).f n).hom) (Finsupp.single s 1)).support at ht
    rw [Subdivision.chainMap_f] at ht
    obtain ⟨a, ha, hta⟩ := mem_support_linearMap_exists R (Subdivision.map (K.Subdivision r) R n)
      (((Subdivision.iteratedChainMap K R r).f n).hom (Finsupp.single s 1)) t ht
    have hp := map_chart_carried (K.Subdivision r) R n a t hta
    have hq := ih a ha
    rintro x ⟨y, hy, rfl⟩
    exact hq ⟨_, hp ⟨y, hy, rfl⟩, rfl⟩

end P202.LefschetzFixedPoint.GeometricCarrier

namespace P202.LefschetzFixedPoint
attribute [local instance] P202Specs.OrientedSimplicialAlgebra.vertexOrder
open P202.Cellular P202.Cellular.AbstractSimplicialComplex
open P202Specs.LefschetzFixedPoint

/-- Every fixed-point-free self-map has zero Lefschetz number, computed on
singular rational homology, using the actual carried finite chain model. -/
theorem lefschetz_zero_of_no_fixed_point
    (comparison : RationalComparison.{w})
    (naturality : RationalNaturality.{w})
    {V : Type w} (K : AbstractSimplicialComplex V) (hK : K.IsFinite)
    (f : TopCat.of K.Realization ⟶ TopCat.of K.Realization) (hf : ∀ x, f x ≠ x) :
    lefschetzNumber f = 0 := by
  classical
  obtain ⟨D⟩ := exists_separatedApproximation K hK f hf
  let L := K.Subdivision D.coarse
  let M := L.Subdivision D.fine
  have hL : L.IsFinite := P202.Topology.finite_iteratedSubdivision K hK D.coarse
  let fL : TopCat.of L.Realization ⟶ TopCat.of L.Realization :=
    conjugateMap D.coarseHomeo.symm f
  have hconj : lefschetzNumber f = lefschetzNumber fL :=
    lefschetz_number_conjugate (X := TopCat.of K.Realization) (Y := TopCat.of L.Realization)
      D.coarseHomeo.symm f
  rw [hconj]
  by_cases hne : Nonempty L.Realization
  · let x₀ : L.Realization := hne.some
    obtain ⟨v₀, _⟩ := Convexity.StdSimplex.support_weights_nonempty x₀.1
    let S := Subdivision.iteratedChainMap L ℚ D.fine
    let P := Subdivision.iteratedLastVertexChainMap L ℚ D.fine
    let p := Subdivision.iteratedLastVertexMap L D.fine
    obtain ⟨G, hG⟩ := P202.OrientedSimplicialAlgebra.pushforward_chainMap ℚ ℚ
      (extendActiveMap D.approximation v₀)
    have hP : ∀ n, (P.f n).hom = P202Specs.OrientedSimplicialAlgebra.pushforward ℚ ℚ
        (extendActiveMap p v₀) n :=
      fun n => Subdivision.iteratedLastVertexChainMap_active_f L ℚ D.fine n v₀
    obtain ⟨Hp⟩ := Subdivision.iteratedLastVertexMap_homotopic L hL D.fine
    have hcan : Subdivision.iteratedCanonicalHom L D.fine = (TopCat.isoOfHomeo D.fineHomeo).hom := by
      ext x
      change Subdivision.iteratedCanonicalHom L D.fine x = D.fineHomeo x
      rw [Subdivision.iteratedCanonicalHom_apply]
      exact congrFun D.fine_canonical.symm x
    rw [hcan] at Hp
    have H : TopCat.Homotopy (activeRealizationHom D.approximation)
        (activeRealizationHom p ≫ fL) :=
      D.homotopy.symm.trans ((TopCat.Homotopy.refl fL).comp Hp)
    obtain ⟨e, he⟩ := finite_model_equivariance comparison naturality L M v₀ p D.approximation
      S P G hP hG (Subdivision.iteratedChainMap_lastVertex L ℚ D.fine) fL H
    let C := P202Specs.OrientedSimplicialAlgebra.complex ℚ ℚ (K := L)
    let : ∀ n, FiniteDimensional ℚ (C.X n) := fun n => finite_oriented_chains L hL ℚ ℚ n
    obtain ⟨N, hN⟩ := P202.Topology.finite_complex_simplex_card_bound L hL
    have hvanish : ∀ n, N ≤ n → Subsingleton (C.X n) := by
      intro n hn
      let := no_oriented_simplex_above_bound L N (hN 0) n hn
      exact inferInstanceAs (Subsingleton (P202Specs.OrientedSimplicialAlgebra.Chains L ℚ n))
    apply lefschetz_zero_of_finite_chain_model fL C (S ≫ G) N hvanish e he
    intro n
    change LinearMap.trace ℚ (P202Specs.OrientedSimplicialAlgebra.Chains L ℚ n)
      ((G.f n).hom.comp (S.f n).hom) = 0
    rw [hG n]
    apply GeometricDiagonal.trace_subdivision_pushforward_zero_of_disjoint ℚ hL
    intro s t ht
    apply D.separated (Subdivision.coarse L s) (Subdivision.coarse M t)
    rw [D.fine_canonical]
    exact GeometricCarrier.iteratedChainMap_chart_carried L ℚ n s D.fine t ht
  · let : IsEmpty L.Realization := not_nonempty_iff.mp hne
    exact empty_lefschetz_number _ fL

/-- The complete mathematical fixed point theorem, before packaging the full
ordered conditional premise interface. -/
theorem fixed_point_of_rational_comparison
    (comparison : RationalComparison.{w})
    (naturality : RationalNaturality.{w}) :
    P202Specs.LefschetzFixedPoint.fixedPoint_type.{0,0,w} := by
  apply fixed_point_reduce_to_realizations
  intro V K hK f hf
  by_contra hn
  have hnofix : ∀ x, f x ≠ x := by simpa only [not_exists] using hn
  exact hf (lefschetz_zero_of_no_fixed_point comparison naturality K hK f hnofix)

end P202.LefschetzFixedPoint

namespace P202.LefschetzFixedPoint.LiftedRational
attribute [local instance 2000] CategoryTheory.CategoryWithHomology.hasHomology
abbrev Ring := ULift.{u} ℚ
abbrev Coeff := ULift.{v} ℚ
instance coeffModule : Module Ring.{u} Coeff.{v} :=
  Module.compHom Coeff (ULift.ringEquiv : Ring ≃+* ℚ).toRingHom
abbrev upHom : ℚ →+* Ring.{u} :=
  (ULift.ringEquiv : Ring ≃+* ℚ).symm.toRingHom
abbrev restrictFunctor := ModuleCat.restrictScalars.{max v w} upHom.{u}
abbrev liftFunctor := ModuleCat.uliftFunctor.{v,w} ℚ

def coeffIso (I : Type w) :
    (liftFunctor.{v,w}).obj (ModuleCat.of ℚ (I →₀ ℚ)) ≅
      (restrictFunctor.{u,v,w}).obj (ModuleCat.of Ring.{u} (I →₀ Coeff.{v})) := by
  apply LinearEquiv.toModuleIso
  exact (ULift.moduleEquiv : ULift.{v} (I →₀ ℚ) ≃ₗ[ℚ] I →₀ ℚ).trans
    (Finsupp.mapRange.linearEquiv (ULift.moduleEquiv.symm : ℚ ≃ₗ[ℚ] Coeff.{v}))


def coeffFunctorIso :
    P202Specs.SingularChains.finsuppFunctor ℚ ℚ ⋙ liftFunctor.{v,w} ≅
      P202Specs.SingularChains.finsuppFunctor Ring.{u} Coeff.{v} ⋙ restrictFunctor.{u,v,w} :=
  NatIso.ofComponents coeffIso.{u,v,w} (by
    intro I J f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (Finsupp.mapDomain f x.down).mapRange ULift.up (by rfl) =
      (Finsupp.mapDomain f (x.down.mapRange ULift.up (by rfl)))
    exact (Finsupp.mapDomain_mapRange f x.down ULift.up (by rfl) (by intros; rfl)).symm)

def singularChainIso (X : TopCat.{w}) :
    (liftFunctor.{v,w}.mapHomologicalComplex _).obj
      (P202Specs.SingularChains.complex ℚ ℚ X) ≅
    (restrictFunctor.{u,v,w}.mapHomologicalComplex _).obj
      (P202Specs.SingularChains.complex Ring.{u} Coeff.{v} X) :=
  (AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
    liftFunctor.{v,w}).app (P202Specs.SingularChains.simplicialChains ℚ ℚ X) ≪≫
  (AlgebraicTopology.alternatingFaceMapComplex _).mapIso
    (Functor.isoWhiskerLeft (TopCat.toSSet.obj X) coeffFunctorIso.{u,v,w}) ≪≫
  ((AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
    restrictFunctor.{u,v,w}).app
      (P202Specs.SingularChains.simplicialChains Ring.{u} Coeff.{v} X)).symm

def restrictEquivalence : ModuleCat.{max v w} Ring.{u} ≌ ModuleCat.{max v w} ℚ where
  functor := restrictFunctor.{u,v,w}
  inverse := ModuleCat.restrictScalars (ULift.ringEquiv : Ring.{u} ≃+* ℚ).toRingHom
  unitIso := (ModuleCat.restrictScalarsId Ring.{u}).symm ≪≫
    ModuleCat.restrictScalarsComp' _ _ _ (by ext x; rfl)
  counitIso := (ModuleCat.restrictScalarsComp' _ _ _ (by ext x; rfl)).symm ≪≫
    (ModuleCat.restrictScalarsId ℚ)

instance restrict_isEquivalence : restrictFunctor.{u,v,w}.IsEquivalence :=
  restrictEquivalence.{u,v,w}.isEquivalence_functor

instance (priority := 2000) restrict_isRightAdjoint : restrictFunctor.{u,v,w}.IsRightAdjoint :=
  restrictEquivalence.{u,v,w}.symm.toAdjunction.isRightAdjoint
instance (priority := 2000) restrict_isLeftAdjoint : restrictFunctor.{u,v,w}.IsLeftAdjoint :=
  restrictEquivalence.{u,v,w}.toAdjunction.isLeftAdjoint

def singularHomologyIso (X : TopCat.{w}) (n : ℕ) :
    liftFunctor.{v,w}.obj ((P202Specs.SingularChains.complex ℚ ℚ X).homology n) ≅
      restrictFunctor.{u,v,w}.obj
        ((P202Specs.SingularChains.complex Ring.{u} Coeff.{v} X).homology n) :=
  (((P202Specs.SingularChains.complex ℚ ℚ X).sc n).mapHomologyIso liftFunctor.{v,w}).symm ≪≫
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (singularChainIso.{u,v,w} X) ≪≫
  ((P202Specs.SingularChains.complex Ring.{u} Coeff.{v} X).sc n).mapHomologyIso
    restrictFunctor.{u,v,w}

def singularHomologyEquiv (X : TopCat.{w}) (n : ℕ) :
    (P202Specs.SingularChains.complex ℚ ℚ X).homology n ≃ₗ[ℚ]
      restrictFunctor.{u,v,w}.obj
        ((P202Specs.SingularChains.complex Ring.{u} Coeff.{v} X).homology n) :=
  ULift.moduleEquiv.symm.trans (singularHomologyIso.{u,v,w} X n).toLinearEquiv


def coeffEquivRing : Coeff.{v} ≃ₗ[Ring.{u}] Ring.{u} where
  toFun a := ⟨a.down⟩
  invFun r := ⟨r.down⟩
  left_inv a := rfl
  right_inv r := rfl
  map_add' a b := rfl
  map_smul' r a := rfl

instance coeffFinite : FiniteDimensional Ring.{u} Coeff.{v} :=
  Module.Finite.of_injective (coeffEquivRing.{u,v}).toLinearMap
    (coeffEquivRing.{u,v}).injective

theorem restrict_finite (M : ModuleCat.{max v w} Ring.{u})
    [FiniteDimensional Ring.{u} M] :
    FiniteDimensional ℚ (restrictFunctor.{u,v,w}.obj M) := by
  let f : M →ₛₗ[(ULift.ringEquiv : Ring.{u} ≃+* ℚ).toRingHom]
      (restrictFunctor.{u,v,w}.obj M) :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by cases r; rfl }
  exact Module.Finite.of_surjective f Function.surjective_id

theorem rational_homology_finiteness_of_universe_comparison
    (comparison : P202Specs.SimplicialComparison.simplicialComparison_type.{u,v,w}) :
    P202Specs.LefschetzFixedPoint.homologyFiniteness_type.{u,v,w} := by
  intro X hX
  obtain ⟨hfin, N, hN⟩ :=
    P202.LefschetzFixedPoint.finite_polyhedron_homology_finiteness
      comparison Ring.{u} Coeff.{v} X hX
  constructor
  · intro n
    let := hfin n
    let := restrict_finite.{u,v,w}
      ((P202Specs.SingularChains.complex Ring.{u} Coeff.{v} X).homology n)
    exact Module.Finite.of_injective (singularHomologyEquiv.{u,v,w} X n).toLinearMap
      (singularHomologyEquiv.{u,v,w} X n).injective
  · refine ⟨N, fun n hn => ?_⟩
    let : Subsingleton (restrictFunctor.{u,v,w}.obj
        ((P202Specs.SingularChains.complex Ring.{u} Coeff.{v} X).homology n)) := hN n hn
    exact (singularHomologyEquiv.{u,v,w} X n).injective.subsingleton

end P202.LefschetzFixedPoint.LiftedRational

namespace P202.LefschetzFixedPoint

/-- Conditional draft with every supplied premise in its frozen order. -/
theorem homologyFiniteness_conditional
    (_deltaComparison : P202Specs.SimplicialComparison.deltaComparison_type.{u,v,w})
    (_deltaNaturality : P202Specs.SimplicialComparison.deltaNaturality_type.{u,v,w})
    (_orderIndependence : P202Specs.SimplicialComparison.orderIndependence_type.{u,v,w})
    (simplicialComparison : P202Specs.SimplicialComparison.simplicialComparison_type.{u,v,w})
    (simplicialNaturality : P202Specs.SimplicialComparison.simplicialNaturality_type.{u,v,w}) :
    P202Specs.LefschetzFixedPoint.homologyFiniteness_type.{u,v,w} :=
  LiftedRational.rational_homology_finiteness_of_universe_comparison.{u,v,w} simplicialComparison

/-- Conditional draft with every supplied premise in its frozen order. -/
theorem lefschetzSum_conditional
    (_deltaComparison : P202Specs.SimplicialComparison.deltaComparison_type.{u,v,w})
    (_deltaNaturality : P202Specs.SimplicialComparison.deltaNaturality_type.{u,v,w})
    (_orderIndependence : P202Specs.SimplicialComparison.orderIndependence_type.{u,v,w})
    (simplicialComparison : P202Specs.SimplicialComparison.simplicialComparison_type.{u,v,w})
    (simplicialNaturality : P202Specs.SimplicialComparison.simplicialNaturality_type.{u,v,w}) :
    P202Specs.LefschetzFixedPoint.lefschetzSum_type.{u,v,w} :=
  lefschetz_sum_of_homology_finiteness
    (LiftedRational.rational_homology_finiteness_of_universe_comparison.{u,v,w} simplicialComparison)

end P202.LefschetzFixedPoint

namespace P202.LefschetzFixedPoint.LiftedRational
attribute [local instance] P202Specs.OrientedSimplicialAlgebra.vertexOrder
open P202.Cellular
open P202Specs.OrientedSimplicialAlgebra

def coeffUp (I : Type w) : (I →₀ ℚ) →ₗ[ℚ] (I →₀ Coeff.{v}) :=
  Finsupp.mapRange.linearMap (ULift.moduleEquiv.symm : ℚ ≃ₗ[ℚ] Coeff.{v}).toLinearMap

@[simp] theorem coeffUp_single (I : Type w) (i : I) (a : ℚ) :
    coeffUp.{v,w} I (Finsupp.single i a) = Finsupp.single i (ULift.up a) :=
  by
    exact Finsupp.mapRange_single (hf := map_zero _)

def orientedChainIso {V : Type w} (K : AbstractSimplicialComplex V) :
    (liftFunctor.{v,w}.mapHomologicalComplex _).obj (complex ℚ ℚ (K := K)) ≅
    (restrictFunctor.{u,v,w}.mapHomologicalComplex _).obj
      (complex Ring.{u} Coeff.{v} (K := K)) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => coeffIso.{u,v,w} (Simplex K n)) (by
    intro i j hij
    have h : i = j+1 := by simpa only [ComplexShape.down_Rel] using hij.symm
    subst i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    simp only [Functor.mapHomologicalComplex_obj_d, ModuleCat.hom_comp]
    dsimp [restrictFunctor, liftFunctor, ModuleCat.restrictScalars, ModuleCat.RestrictScalars.map', ModuleCat.uliftFunctor]
    rw [P202.OrientedSimplicialAlgebra.boundary_eq, P202.OrientedSimplicialAlgebra.boundary_eq]
    dsimp [coeffIso, Finsupp.mapRange.linearEquiv, Finsupp.mapRange.linearMap, LinearEquiv.trans]
    change boundary Ring.{u} Coeff.{v} j (c.down.mapRange (ULift.up : ℚ → Coeff.{v}) (by rfl)) =
      (boundary ℚ ℚ j c.down).mapRange (ULift.up : ℚ → Coeff.{v}) (by rfl)
    have he : ∀ c : Chains K ℚ (j+1),
        boundary Ring.{u} Coeff.{v} j (c.mapRange (ULift.up : ℚ → Coeff.{v}) (by rfl)) =
          (boundary ℚ ℚ j c).mapRange (ULift.up : ℚ → Coeff.{v}) (by rfl) := by
      intro c
      change boundary Ring.{u} Coeff.{v} j (coeffUp (Simplex K (j+1)) c) =
        coeffUp (Simplex K j) (boundary ℚ ℚ j c)
      induction c using Finsupp.induction_linear with
      | zero => simp
      | add c d hc hd =>
        simp only [map_add, hc, hd]
      | single s a =>
        rw [coeffUp_single, P202.OrientedSimplicialAlgebra.boundary_single,
          P202.OrientedSimplicialAlgebra.boundary_single]
        simp only [map_sum, map_zsmul, coeffUp_single]
    exact he c.down)

@[simp] theorem orientedChainIso_hom_f {V : Type w} (K : AbstractSimplicialComplex V) (n : ℕ) :
    ((orientedChainIso.{u,v,w} K).hom.f n) = (coeffIso.{u,v,w} (Simplex K n)).hom := rfl

@[simp] theorem singularChainIso_hom_f (X : TopCat.{w}) (n : ℕ) :
    ((singularChainIso.{u,v,w} X).hom.f n) =
      (coeffIso.{u,v,w} (P202Specs.SingularChains.Simplex X n)).hom := by
  rfl

theorem affine_square {V : Type w} (K : AbstractSimplicialComplex V)
    (B : P202Specs.RelativeParametrizations.Simplicial.Subcomplex K)
    (F : P202Specs.SimplicialComparison.SimplicialComparisonData ℚ ℚ K B)
    (G : P202Specs.SimplicialComparison.SimplicialComparisonData Ring.{u} Coeff.{v} K B) :
    (liftFunctor.{v,w}.mapHomologicalComplex _).map F.absolute ≫
      (singularChainIso.{u,v,w} (TopCat.of K.Realization)).hom =
    (orientedChainIso.{u,v,w} K).hom ≫
      (restrictFunctor.{u,v,w}.mapHomologicalComplex _).map G.absolute := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    singularChainIso_hom_f, orientedChainIso_hom_f, ModuleCat.hom_comp]
  dsimp [restrictFunctor, liftFunctor, ModuleCat.restrictScalars,
    ModuleCat.RestrictScalars.map', ModuleCat.uliftFunctor]
  rw [F.absolute_formula, G.absolute_formula]
  change (P202Specs.RelativeParametrizations.Simplicial.affineLinear K ℚ ℚ n c.down).mapRange
      (ULift.up : ℚ → Coeff.{v}) (by rfl) =
    P202Specs.RelativeParametrizations.Simplicial.affineLinear K Ring.{u} Coeff.{v} n
      (c.down.mapRange (ULift.up : ℚ → Coeff.{v}) (by rfl))
  unfold P202Specs.RelativeParametrizations.Simplicial.affineLinear
  exact (Finsupp.mapDomain_mapRange _ c.down ULift.up (by rfl) (by intros; rfl)).symm

end P202.LefschetzFixedPoint.LiftedRational

namespace P202.LefschetzFixedPoint

theorem quasiIso_of_mapped_square {ι C D E : Type*}
    [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E] {c : ComplexShape ι}
    (L : C ⥤ E) [L.Additive] [L.PreservesHomology] [L.ReflectsIsomorphisms]
    (T : D ⥤ E) [T.Additive] [T.PreservesHomology]
    {A B : HomologicalComplex C c} {A' B' : HomologicalComplex D c}
    (f : A ⟶ B) (F : A' ⟶ B') [QuasiIso F]
    (iA : (L.mapHomologicalComplex c).obj A ≅ (T.mapHomologicalComplex c).obj A')
    (iB : (L.mapHomologicalComplex c).obj B ≅ (T.mapHomologicalComplex c).obj B')
    (h : (L.mapHomologicalComplex c).map f ≫ iB.hom =
      iA.hom ≫ (T.mapHomologicalComplex c).map F) : QuasiIso f := by
  have he : (L.mapHomologicalComplex c).map f =
      iA.hom ≫ (T.mapHomologicalComplex c).map F ≫ iB.inv := by
    rw [← Category.assoc, ← h, Category.assoc, iB.hom_inv_id, Category.comp_id]
  haveI : QuasiIso ((L.mapHomologicalComplex c).map f) := by
    rw [he]
    infer_instance
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology f L).mp inferInstance


/-- The already proved affine chain maps assembled as comparison data,
without assuming their homology maps are isomorphisms. -/
def canonicalAffineComparison (R : Type*) [CommRing R]
    (A : Type*) [AddCommGroup A] [Module R A]
    {V : Type*} (K : P202.Cellular.AbstractSimplicialComplex V)
    (B : P202Specs.RelativeParametrizations.Simplicial.Subcomplex K) :
    P202Specs.SimplicialComparison.SimplicialComparisonData R A K B where
  absolute := (P202.RelativeParametrizations.Simplicial.affineChainMap R A K).choose
  absolute_formula := (P202.RelativeParametrizations.Simplicial.affineChainMap R A K).choose_spec
  relative := (P202.RelativeParametrizations.Simplicial.relativeAffineChainMap R A K B).choose
  relative_formula := (P202.RelativeParametrizations.Simplicial.relativeAffineChainMap R A K B).choose_spec


namespace LiftedRational

theorem rationalComparison_of_universe_comparison
    (comparison : P202Specs.SimplicialComparison.simplicialComparison_type.{u,v,w}) :
    P202.LefschetzFixedPoint.RationalComparison.{w} := by
  intro V K
  let B := P202Specs.RelativeParametrizations.Simplicial.Subcomplex.empty K
  obtain ⟨G, hG, _⟩ := comparison Ring.{u} Coeff.{v} K B
  let F := canonicalAffineComparison ℚ ℚ K B
  refine ⟨F, fun n => ?_⟩
  letI : QuasiIso G.absolute :=
    (quasiIso_iff G.absolute).mpr (fun n =>
      (quasiIsoAt_iff_isIso_homologyMap G.absolute n).mpr (hG n))
  haveI : QuasiIso F.absolute := quasiIso_of_mapped_square
    liftFunctor.{v,w} restrictFunctor.{u,v,w} F.absolute G.absolute
    (orientedChainIso.{u,v,w} K)
    (singularChainIso.{u,v,w} (TopCat.of K.Realization))
    (affine_square.{u,v,w} K B F G)
  exact (quasiIsoAt_iff_isIso_homologyMap F.absolute n).mp inferInstance

end LiftedRational
end P202.LefschetzFixedPoint

namespace P202.LefschetzFixedPoint.LiftedRational
attribute [local instance] P202Specs.OrientedSimplicialAlgebra.vertexOrder
open P202.Cellular
open P202Specs.OrientedSimplicialAlgebra

theorem coeffUp_oriented {V : Type w} {K : AbstractSimplicialComplex V}
    {n : ℕ} (s : VertexTuple K n) (a : ℚ) :
    coeffUp.{v,w} (Simplex K n) (oriented ℚ s a) = oriented Coeff.{v} s (ULift.up a) := by
  classical
  unfold oriented
  split_ifs <;> simp only [map_zsmul, coeffUp_single, map_zero]

theorem pushforward_square {V W : Type w} (K : AbstractSimplicialComplex V)
    (L : AbstractSimplicialComplex W)
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L)
    (F : complex ℚ ℚ (K := K) ⟶ complex ℚ ℚ (K := L))
    (G : complex Ring.{u} Coeff.{v} (K := K) ⟶ complex Ring.{u} Coeff.{v} (K := L))
    (hF : ∀ n, (F.f n).hom = pushforward ℚ ℚ f n)
    (hG : ∀ n, (G.f n).hom = pushforward Ring.{u} Coeff.{v} f n) :
    (liftFunctor.{v,w}.mapHomologicalComplex _).map F ≫ (orientedChainIso.{u,v,w} L).hom =
    (orientedChainIso.{u,v,w} K).hom ≫ (restrictFunctor.{u,v,w}.mapHomologicalComplex _).map G := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    orientedChainIso_hom_f, ModuleCat.hom_comp]
  dsimp [restrictFunctor, liftFunctor, ModuleCat.restrictScalars,
    ModuleCat.RestrictScalars.map', ModuleCat.uliftFunctor]
  rw [hF, hG]
  change coeffUp.{v,w} (Simplex L n) (pushforward ℚ ℚ f n c.down) =
    pushforward Ring.{u} Coeff.{v} f n (coeffUp.{v,w} (Simplex K n) c.down)
  have he : ∀ c : Chains K ℚ n,
      coeffUp.{v,w} (Simplex L n) (pushforward ℚ ℚ f n c) =
        pushforward Ring.{u} Coeff.{v} f n (coeffUp.{v,w} (Simplex K n) c) := by
    intro c
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]
    | single s a =>
      rw [P202.OrientedSimplicialAlgebra.pushforward_single, coeffUp_single,
        P202.OrientedSimplicialAlgebra.pushforward_single, coeffUp_oriented]
  exact he c.down

theorem singular_square {X Y : TopCat.{w}} (f : X ⟶ Y) :
    (liftFunctor.{v,w}.mapHomologicalComplex _).map (P202Specs.SingularChains.chainMap ℚ ℚ f) ≫
      (singularChainIso.{u,v,w} Y).hom =
    (singularChainIso.{u,v,w} X).hom ≫ (restrictFunctor.{u,v,w}.mapHomologicalComplex _).map
      (P202Specs.SingularChains.chainMap Ring.{u} Coeff.{v} f) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    singularChainIso_hom_f, ModuleCat.hom_comp]
  change (Finsupp.mapDomain _ c.down).mapRange (ULift.up : ℚ → Coeff.{v}) (by rfl) =
    Finsupp.mapDomain _ (c.down.mapRange (ULift.up : ℚ → Coeff.{v}) (by rfl))
  exact (Finsupp.mapDomain_mapRange _ c.down ULift.up (by rfl) (by intros; rfl)).symm

theorem map_homology_naturality {ι C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] {c : ComplexShape ι}
    (L : C ⥤ D) [L.Additive] [L.PreservesHomology]
    {A B : HomologicalComplex C c} (f : A ⟶ B) (n : ι) :
    homologyMap ((L.mapHomologicalComplex c).map f) n ≫ ((B.sc n).mapHomologyIso L).hom =
      ((A.sc n).mapHomologyIso L).hom ≫ L.map (homologyMap f n) :=
  ShortComplex.mapHomologyIso_hom_naturality ((shortComplexFunctor C c n).map f) L

theorem homologyMap_eq_of_mapped {ι C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] {c : ComplexShape ι}
    (L : C ⥤ D) [L.Additive] [L.PreservesHomology] [L.Faithful]
    {A B : HomologicalComplex C c} (f g : A ⟶ B) (n : ι)
    (h : homologyMap ((L.mapHomologicalComplex c).map f) n =
      homologyMap ((L.mapHomologicalComplex c).map g) n) : homologyMap f n = homologyMap g n := by
  apply L.map_injective
  apply (cancel_epi ((A.sc n).mapHomologyIso L).hom).mp
  rw [← map_homology_naturality, ← map_homology_naturality, h]

theorem homologyMap_mapped_eq {ι C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] {c : ComplexShape ι}
    (L : C ⥤ D) [L.Additive] [L.PreservesHomology]
    {A B : HomologicalComplex C c} (f g : A ⟶ B) (n : ι)
    (h : homologyMap f n = homologyMap g n) :
    homologyMap ((L.mapHomologicalComplex c).map f) n =
      homologyMap ((L.mapHomologicalComplex c).map g) n := by
  apply (cancel_mono ((B.sc n).mapHomologyIso L).hom).mp
  rw [map_homology_naturality, map_homology_naturality, h]

theorem homologyMap_eq_of_squares {ι C D E : Type*}
    [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E] {c : ComplexShape ι}
    (L : C ⥤ E) [L.Additive] [L.PreservesHomology] [L.Faithful]
    (T : D ⥤ E) [T.Additive] [T.PreservesHomology]
    {A B : HomologicalComplex C c} {A' B' : HomologicalComplex D c}
    (f g : A ⟶ B) (F G : A' ⟶ B') (n : ι)
    (iA : (L.mapHomologicalComplex c).obj A ≅ (T.mapHomologicalComplex c).obj A')
    (iB : (L.mapHomologicalComplex c).obj B ≅ (T.mapHomologicalComplex c).obj B')
    (hf : (L.mapHomologicalComplex c).map f ≫ iB.hom =
      iA.hom ≫ (T.mapHomologicalComplex c).map F)
    (hg : (L.mapHomologicalComplex c).map g ≫ iB.hom =
      iA.hom ≫ (T.mapHomologicalComplex c).map G)
    (h : homologyMap F n = homologyMap G n) : homologyMap f n = homologyMap g n := by
  apply homologyMap_eq_of_mapped L f g n
  apply (cancel_mono (homologyMap iB.hom n)).mp
  rw [← homologyMap_comp, ← homologyMap_comp, hf, hg, homologyMap_comp,
    homologyMap_comp, homologyMap_mapped_eq T F G n h]

theorem rationalNaturality_of_universe
    (comparison : P202Specs.SimplicialComparison.simplicialComparison_type.{u,v,w})
    (naturality : P202Specs.SimplicialComparison.simplicialNaturality_type.{u,v,w}) :
    P202.LefschetzFixedPoint.RationalNaturality.{w} := by
  rintro V W K L g w₀ T hT F G n
  let B := P202Specs.RelativeParametrizations.Simplicial.Subcomplex.empty K
  let E := P202Specs.RelativeParametrizations.Simplicial.Subcomplex.empty L
  obtain ⟨F', _, _⟩ := comparison Ring.{u} Coeff.{v} K B
  obtain ⟨G', _, _⟩ := comparison Ring.{u} Coeff.{v} L E
  obtain ⟨a, ha, T', _, _, hT', _, _, hnat⟩ := naturality Ring.{u} Coeff.{v} K L B E
    (extendActiveMap g w₀) (by intro s hs; exact hs.elim)
  have ha' : a = activeRealizationHom g := by
    ext x
    apply Subtype.ext
    exact (ha x).trans (extendActiveMap_realization g w₀ x).symm
  subst a
  have hnat' : homologyMap (T' ≫ G'.absolute) n =
      homologyMap (F'.absolute ≫ P202Specs.SingularChains.chainMap Ring.{u} Coeff.{v}
        (activeRealizationHom g)) n := by
    simpa only [homologyMap_comp] using (hnat F' G' n).1
  have h1 : (liftFunctor.{v,w}.mapHomologicalComplex _).map (T ≫ G.absolute) ≫
      (singularChainIso.{u,v,w} (TopCat.of L.Realization)).hom =
      (orientedChainIso.{u,v,w} K).hom ≫
        (restrictFunctor.{u,v,w}.mapHomologicalComplex _).map (T' ≫ G'.absolute) := by
    rw [Functor.map_comp, Category.assoc, affine_square L E G G',
      ← Category.assoc, pushforward_square K L (extendActiveMap g w₀) T T' hT hT',
      Category.assoc, ← Functor.map_comp]
  have h2 : (liftFunctor.{v,w}.mapHomologicalComplex _).map
      (F.absolute ≫ P202Specs.SingularChains.chainMap ℚ ℚ (activeRealizationHom g)) ≫
      (singularChainIso.{u,v,w} (TopCat.of L.Realization)).hom =
      (orientedChainIso.{u,v,w} K).hom ≫
        (restrictFunctor.{u,v,w}.mapHomologicalComplex _).map
          (F'.absolute ≫ P202Specs.SingularChains.chainMap Ring.{u} Coeff.{v}
            (activeRealizationHom g)) := by
    rw [Functor.map_comp, Category.assoc, singular_square,
      ← Category.assoc, affine_square K B F F', Category.assoc, ← Functor.map_comp]
  have h := homologyMap_eq_of_squares liftFunctor.{v,w} restrictFunctor.{u,v,w}
    (T ≫ G.absolute) (F.absolute ≫ P202Specs.SingularChains.chainMap ℚ ℚ (activeRealizationHom g))
    (T' ≫ G'.absolute) (F'.absolute ≫ P202Specs.SingularChains.chainMap Ring.{u} Coeff.{v}
      (activeRealizationHom g)) n (orientedChainIso.{u,v,w} K)
    (singularChainIso.{u,v,w} (TopCat.of L.Realization)) h1 h2 hnat'
  simpa only [homologyMap_comp] using h

end P202.LefschetzFixedPoint.LiftedRational

namespace P202.LefschetzFixedPoint

/-- The full conditional fixed-point theorem. Its original closed name is
reserved for the owner after genuine upstream dependency closure. -/
theorem fixedPoint_conditional
    (_deltaComparison : P202Specs.SimplicialComparison.deltaComparison_type.{u,v,w})
    (_deltaNaturality : P202Specs.SimplicialComparison.deltaNaturality_type.{u,v,w})
    (_orderIndependence : P202Specs.SimplicialComparison.orderIndependence_type.{u,v,w})
    (simplicialComparison : P202Specs.SimplicialComparison.simplicialComparison_type.{u,v,w})
    (simplicialNaturality : P202Specs.SimplicialComparison.simplicialNaturality_type.{u,v,w})
    : P202Specs.LefschetzFixedPoint.fixedPoint_type.{u,v,w} :=
  fixed_point_of_rational_comparison.{w}
    (LiftedRational.rationalComparison_of_universe_comparison.{u,v,w} simplicialComparison)
    (LiftedRational.rationalNaturality_of_universe.{u,v,w} simplicialComparison simplicialNaturality)

end P202.LefschetzFixedPoint

universe v8_closure_af03dae2f871aa83_u0 v8_closure_af03dae2f871aa83_u1 v8_closure_af03dae2f871aa83_u2
theorem _root_.«P202».«LefschetzFixedPoint».«fixedPoint» : _root_.«P202Specs».«LefschetzFixedPoint».«fixedPoint_type».{v8_closure_af03dae2f871aa83_u0, v8_closure_af03dae2f871aa83_u1, v8_closure_af03dae2f871aa83_u2} :=
  @_root_.«P202».«LefschetzFixedPoint».«fixedPoint_conditional».{v8_closure_af03dae2f871aa83_u0, v8_closure_af03dae2f871aa83_u1, v8_closure_af03dae2f871aa83_u2} (@_root_.«P202».«SimplicialComparison».«deltaComparison».{v8_closure_af03dae2f871aa83_u0, v8_closure_af03dae2f871aa83_u1, v8_closure_af03dae2f871aa83_u2}) (@_root_.«P202».«SimplicialComparison».«deltaNaturality».{v8_closure_af03dae2f871aa83_u0, v8_closure_af03dae2f871aa83_u1, v8_closure_af03dae2f871aa83_u2}) (@_root_.«P202».«SimplicialComparison».«orderIndependence».{v8_closure_af03dae2f871aa83_u0, v8_closure_af03dae2f871aa83_u1, v8_closure_af03dae2f871aa83_u2}) (@_root_.«P202».«SimplicialComparison».«simplicialComparison».{v8_closure_af03dae2f871aa83_u0, v8_closure_af03dae2f871aa83_u1, v8_closure_af03dae2f871aa83_u2}) (@_root_.«P202».«SimplicialComparison».«simplicialNaturality».{v8_closure_af03dae2f871aa83_u0, v8_closure_af03dae2f871aa83_u1, v8_closure_af03dae2f871aa83_u2})
theorem _root_.«P202».«LefschetzFixedPoint».«homologyFiniteness» : _root_.«P202Specs».«LefschetzFixedPoint».«homologyFiniteness_type».{v8_closure_af03dae2f871aa83_u0, v8_closure_af03dae2f871aa83_u1, v8_closure_af03dae2f871aa83_u2} :=
  @_root_.«P202».«LefschetzFixedPoint».«homologyFiniteness_conditional».{v8_closure_af03dae2f871aa83_u0, v8_closure_af03dae2f871aa83_u1, v8_closure_af03dae2f871aa83_u2} (@_root_.«P202».«SimplicialComparison».«deltaComparison».{v8_closure_af03dae2f871aa83_u0, v8_closure_af03dae2f871aa83_u1, v8_closure_af03dae2f871aa83_u2}) (@_root_.«P202».«SimplicialComparison».«deltaNaturality».{v8_closure_af03dae2f871aa83_u0, v8_closure_af03dae2f871aa83_u1, v8_closure_af03dae2f871aa83_u2}) (@_root_.«P202».«SimplicialComparison».«orderIndependence».{v8_closure_af03dae2f871aa83_u0, v8_closure_af03dae2f871aa83_u1, v8_closure_af03dae2f871aa83_u2}) (@_root_.«P202».«SimplicialComparison».«simplicialComparison».{v8_closure_af03dae2f871aa83_u0, v8_closure_af03dae2f871aa83_u1, v8_closure_af03dae2f871aa83_u2}) (@_root_.«P202».«SimplicialComparison».«simplicialNaturality».{v8_closure_af03dae2f871aa83_u0, v8_closure_af03dae2f871aa83_u1, v8_closure_af03dae2f871aa83_u2})
theorem _root_.«P202».«LefschetzFixedPoint».«lefschetzSum» : _root_.«P202Specs».«LefschetzFixedPoint».«lefschetzSum_type».{v8_closure_af03dae2f871aa83_u0, v8_closure_af03dae2f871aa83_u1, v8_closure_af03dae2f871aa83_u2} :=
  @_root_.«P202».«LefschetzFixedPoint».«lefschetzSum_conditional».{v8_closure_af03dae2f871aa83_u0, v8_closure_af03dae2f871aa83_u1, v8_closure_af03dae2f871aa83_u2} (@_root_.«P202».«SimplicialComparison».«deltaComparison».{v8_closure_af03dae2f871aa83_u0, v8_closure_af03dae2f871aa83_u1, v8_closure_af03dae2f871aa83_u2}) (@_root_.«P202».«SimplicialComparison».«deltaNaturality».{v8_closure_af03dae2f871aa83_u0, v8_closure_af03dae2f871aa83_u1, v8_closure_af03dae2f871aa83_u2}) (@_root_.«P202».«SimplicialComparison».«orderIndependence».{v8_closure_af03dae2f871aa83_u0, v8_closure_af03dae2f871aa83_u1, v8_closure_af03dae2f871aa83_u2}) (@_root_.«P202».«SimplicialComparison».«simplicialComparison».{v8_closure_af03dae2f871aa83_u0, v8_closure_af03dae2f871aa83_u1, v8_closure_af03dae2f871aa83_u2}) (@_root_.«P202».«SimplicialComparison».«simplicialNaturality».{v8_closure_af03dae2f871aa83_u0, v8_closure_af03dae2f871aa83_u1, v8_closure_af03dae2f871aa83_u2})
