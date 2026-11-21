import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Plane.RealizationGeometry
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Plane.CellularBridge
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Plane.Euler
import Mathlib.Analysis.Convex.PathConnected
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SingularDegreeZero
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.AlexanderDuality
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

universe u
noncomputable section

namespace FiniteCombinatorics.Graph.Plane.Euler
open Specs.FiniteCombinatorics.Graph.Plane.Foundations
open Specs.FiniteCombinatorics.Graph.Plane.RealizationGeometry

/-- A finite convex cover suffices for finiteness of the actual components.
Empty covering sets and overlapping covering sets are allowed. -/
theorem finite_components_of_convex_cover {ι : Type*} [Finite ι]
    (U : Set Point) (C : ι → Set Point) (hC : ∀ i, Convex ℝ (C i))
    (hsub : ∀ i, C i ⊆ U) (hcover : U ⊆ ⋃ i, C i) :
    Finite (ConnectedComponents U) := by
  classical
  let (i : ι) : PreconnectedSpace (C i) :=
    isPreconnected_iff_preconnectedSpace.mp (hC i).isPreconnected
  let f : (Σ i, ConnectedComponents (C i)) → ConnectedComponents U :=
    fun b => (continuous_inclusion (hsub b.1)).connectedComponentsMap b.2
  apply Finite.of_surjective f
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover x.property)
  refine ⟨⟨i, ConnectedComponents.mk (⟨x.val, hi⟩ : C i)⟩, ?_⟩
  rfl

private def transverse (a b : Point) : Point →ₗ[ℝ] ℝ :=
  (b.1 - a.1) • LinearMap.snd ℝ ℝ ℝ -
    (b.2 - a.2) • LinearMap.fst ℝ ℝ ℝ

private lemma transverse_endpoints (a b : Point) :
    transverse a b b = transverse a b a := by
  dsimp [transverse]
  ring

private lemma transverse_combination (a b : Point) (r s : ℝ) (h : r + s = 1) :
    transverse a b (r • a + s • b) = transverse a b a := by
  rw [map_add, map_smul, map_smul, transverse_endpoints, ← add_smul, h, one_smul]

private lemma mem_segment_nonvertical (a b x : Point) (hab : a.1 ≠ b.1) :
    x ∈ segment ℝ a b ↔
      transverse a b x = transverse a b a ∧ x.1 ∈ Set.uIcc a.1 b.1 := by
  constructor
  · rintro ⟨r, s, hr, hs, hrs, rfl⟩
    refine ⟨transverse_combination a b r s hrs, ?_⟩
    rw [← segment_eq_uIcc]
    exact ⟨r, s, hr, hs, hrs, rfl⟩
  · rintro ⟨hcross, hcoord⟩
    rw [← segment_eq_uIcc] at hcoord
    obtain ⟨r, s, hr, hs, hrs, hfst⟩ := hcoord
    refine ⟨r, s, hr, hs, hrs, ?_⟩
    apply Prod.ext
    · exact hfst
    · have hL := (transverse_combination a b r s hrs).trans hcross.symm
      change (b.1 - a.1) * (r * a.2 + s * b.2) -
          (b.2 - a.2) * (r * a.1 + s * b.1) =
        (b.1 - a.1) * x.2 - (b.2 - a.2) * x.1 at hL
      change r * a.1 + s * b.1 = x.1 at hfst
      rw [hfst] at hL
      exact mul_left_cancel₀ (sub_ne_zero.mpr hab.symm) (sub_left_inj.mp hL)

private lemma mem_segment_vertical (a b x : Point) (hab : a.1 = b.1) :
    x ∈ segment ℝ a b ↔ x.1 = a.1 ∧ x.2 ∈ Set.uIcc a.2 b.2 := by
  constructor
  · rintro ⟨r, s, hr, hs, hrs, rfl⟩
    constructor
    · change r * a.1 + s * b.1 = a.1
      rw [← hab, ← add_mul, hrs, one_mul]
    · rw [← segment_eq_uIcc]
      exact ⟨r, s, hr, hs, hrs, rfl⟩
  · rintro ⟨hfst, hcoord⟩
    rw [← segment_eq_uIcc] at hcoord
    obtain ⟨r, s, hr, hs, hrs, hsnd⟩ := hcoord
    refine ⟨r, s, hr, hs, hrs, ?_⟩
    apply Prod.ext
    · change r * a.1 + s * b.1 = x.1
      rw [← hab, ← add_mul, hrs, one_mul, hfst]
    · exact hsnd

/-- Four convex sets cover exactly the complement of a straight segment,
including a degenerate segment. -/
theorem segment_complement_convex_cover (a b : Point) :
    ∃ C : Fin 4 → Set Point, (∀ i, Convex ℝ (C i)) ∧
      (segment ℝ a b)ᶜ = ⋃ i, C i := by
  classical
  have hf : IsLinearMap ℝ (fun x : Point => x.1) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hg : IsLinearMap ℝ (fun x : Point => x.2) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  by_cases hab : a.1 = b.1
  · let C : Fin 4 → Set Point := ![
      {x | x.1 < a.1}, {x | a.1 < x.1},
      {x | x.2 < min a.2 b.2}, {x | max a.2 b.2 < x.2}]
    refine ⟨C, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact convex_halfSpace_lt hf _
      · exact convex_halfSpace_gt hf _
      · exact convex_halfSpace_lt hg _
      · exact convex_halfSpace_gt hg _
    · ext x
      simp only [Set.mem_compl_iff, mem_segment_vertical a b x hab,
        Set.uIcc, Set.mem_Icc, Set.mem_iUnion]
      simp only [C, Fin.exists_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Set.mem_ofPred_eq, Fin.exists_fin_zero, or_false]
      simp only [not_and_or, not_le, ne_iff_lt_or_gt]
      tauto
  · let L := transverse a b
    let C : Fin 4 → Set Point := ![
      {x | L x < L a}, {x | L a < L x},
      {x | x.1 < min a.1 b.1}, {x | max a.1 b.1 < x.1}]
    refine ⟨C, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact convex_halfSpace_lt L.isLinear _
      · exact convex_halfSpace_gt L.isLinear _
      · exact convex_halfSpace_lt hf _
      · exact convex_halfSpace_gt hf _
    · ext x
      simp only [Set.mem_compl_iff, mem_segment_nonvertical a b x hab,
        Set.uIcc, Set.mem_Icc, Set.mem_iUnion]
      simp only [C, Fin.exists_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Set.mem_ofPred_eq, Fin.exists_fin_zero, or_false]
      simp only [not_and_or, not_le, ne_iff_lt_or_gt]
      tauto

/-- Finiteness for the complement of any finite union of planar segments.
This argument requires no embedding or nondegeneracy assumptions. -/
theorem finite_components_complement_segments {ι : Type*} [Finite ι]
    (a b : ι → Point) :
    Finite (ConnectedComponents (↥(⋃ i, segment ℝ (a i) (b i))ᶜ)) := by
  classical
  choose C hC hcover using fun i => segment_complement_convex_cover (a i) (b i)
  let U := (⋃ i, segment ℝ (a i) (b i))ᶜ
  let K : (ι → Fin 4) → Set Point := fun σ => ⋂ i, C i (σ i)
  apply finite_components_of_convex_cover U K
  · intro σ
    exact convex_iInter fun i => hC i (σ i)
  · intro σ x hx
    simp only [U, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    intro i
    have hi := Set.mem_iInter.mp hx i
    have : x ∈ (segment ℝ (a i) (b i))ᶜ := by
      rw [hcover i]
      exact Set.mem_iUnion.mpr ⟨σ i, hi⟩
    exact this
  · intro x hx
    have hex : ∀ i, ∃ k : Fin 4, x ∈ C i k := by
      intro i
      apply Set.mem_iUnion.mp
      rw [← hcover i]
      exact fun hi => hx (Set.mem_iUnion.mpr ⟨i, hi⟩)
    choose σ hσ using hex
    exact Set.mem_iUnion.mpr ⟨σ, Set.mem_iInter.mpr hσ⟩

/-- Actual plane faces are finite because each polygonal edge is made of
finitely many straight segments; isolated vertices are degenerate segments. -/
theorem finite_plane_faces {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : Drawing G) : Finite (PlaneFace D) := by
  classical
  choose n a b hab using fun e => edge_polygonal D e
  let ι := V ⊕ (Σ e : G.edgeSet, Fin (n e))
  let p : ι → Point := Sum.elim D.point (fun j => a j.1 j.2)
  let q : ι → Point := Sum.elim D.point (fun j => b j.1 j.2)
  have himage : planeImage D = ⋃ i, segment ℝ (p i) (q i) := by
    ext x
    simp only [Specs.FiniteCombinatorics.Graph.Plane.Foundations.planeImage,
      Set.mem_union, Set.mem_range, Set.mem_iUnion]
    constructor
    · rintro (⟨v, rfl⟩ | ⟨e, he⟩)
      · exact ⟨Sum.inl v, left_mem_segment ℝ _ _⟩
      · rw [hab e] at he
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
        exact ⟨Sum.inr ⟨e, i⟩, hi⟩
    · rintro ⟨v | ⟨e, i⟩, hi⟩
      · left
        exact ⟨v, (by simpa [p, q] using hi : x = D.point v).symm⟩
      · right
        refine ⟨e, ?_⟩
        rw [hab e]
        exact Set.mem_iUnion.mpr ⟨i, hi⟩
  change Finite (ConnectedComponents (↥(planeImage D)ᶜ))
  rw [himage]
  exact finite_components_complement_segments p q

/-- Finiteness of the actual sphere faces, transported through the proved
plane/sphere correspondence. -/
theorem finite_sphere_faces {V : Type u} [Finite V] {G : SimpleGraph V}
    (D : Drawing G) : Finite (Face D) := by
  have := finite_plane_faces D
  obtain ⟨E, _⟩ := plane_sphere_faces D
  exact Finite.of_equiv (PlaneFace D) E

/-- With no vertices there are no edge arcs and the sphere image is empty. -/
theorem sphere_image_empty {V : Type u} [Finite V] [IsEmpty V]
    {G : SimpleGraph V} (D : Drawing G) : sphereImage D = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hX : Nonempty (Realization D) := ⟨⟨x, hx⟩⟩
  obtain ⟨v⟩ := (realization_nonempty_iff D).mp hX
  exact isEmptyElim v

/-- The complement of the empty drawing is the whole sphere. -/
def emptyComplementHomeomorph {V : Type u} [Finite V] [IsEmpty V]
    {G : SimpleGraph V} (D : Drawing G) : SphereComplement D ≃ₜ Sphere :=
  (Homeomorph.setCongr (by
    change (sphereImage D)ᶜ = Set.univ
    rw [sphere_image_empty D, Set.compl_empty])).trans
    (Homeomorph.Set.univ Sphere)

/-- All counts and the connected-complement assertion in the empty case. -/
theorem empty_drawing_counts {V : Type u} [Finite V] [IsEmpty V]
    {G : SimpleGraph V} (D : Drawing G) :
    ConnectedSpace (SphereComplement D) ∧ Nat.card (Face D) = 1 ∧
      Nat.card V = 0 ∧ Nat.card G.edgeSet = 0 ∧ Nat.card G.ConnectedComponent = 0 := by
  have : ConnectedSpace (SphereComplement D) :=
    (emptyComplementHomeomorph D).connectedSpace_iff.mpr inferInstance
  have hf : Nat.card (Face D) = 1 := by
    change Nat.card (ConnectedComponents (SphereComplement D)) = 1
    exact Nat.card_unique
  exact ⟨this, hf, Nat.card_of_isEmpty,
    Nat.card_of_isEmpty, Nat.card_of_isEmpty⟩

/-- The augmentation on finitely many nonempty component indices has a
kernel of dimension one less than the number of indices. -/
theorem component_sum_kernel_finrank (ι : Type*) [Finite ι] [Nonempty ι] :
    Module.finrank ℚ (LinearMap.ker (P202Specs.SingularChains.sumCoefficients ℚ ℚ ι)) =
      Nat.card ι - 1 := by
  classical
  let := Fintype.ofFinite ι
  let S := P202Specs.SingularChains.sumCoefficients ℚ ℚ ι
  have hsurj : Function.Surjective S := by
    intro r
    refine ⟨Finsupp.single (Classical.arbitrary ι) r, ?_⟩
    simp [S, P202Specs.SingularChains.sumCoefficients]
  have hdim := S.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
    Module.finrank_finsupp_self] at hdim
  rw [Nat.card_eq_fintype_card]
  dsimp [S] at hdim
  omega

/-- Singular reduced degree-zero homology of the actual sphere complement
has dimension f-1. No face finiteness or homology comparison is assumed here. -/
theorem reduced_complement_zero_finrank {V : Type u} [Finite V]
    {G : SimpleGraph V} (D : Drawing G) :
    FiniteDimensional ℚ (P202Specs.SingularChains.reducedHomology ℚ ℚ
      (TopCat.of (SphereComplement D)) 0) ∧
    Module.finrank ℚ (P202Specs.SingularChains.reducedHomology ℚ ℚ
      (TopCat.of (SphereComplement D)) 0) = Nat.card (Face D) - 1 := by
  let X := TopCat.of (SphereComplement D)
  have := sphere_complement_locally_path_connected D
  have := finite_sphere_faces D
  let E : Face D ≃ ZerothHomotopy X := connectedComponentsEquivZerothHomotopy
  have : Finite (ZerothHomotopy X) := Finite.of_equiv (Face D) E
  have : Nonempty X := ⟨⟨OnePoint.infty, OnePoint.infty_notMem_image_coe⟩⟩
  obtain ⟨e⟩ := P202.SingularDegreeZero.reducedDegreeZero ℚ ℚ X
  have hfd : FiniteDimensional ℚ (P202Specs.SingularChains.reducedHomology ℚ ℚ X 0) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  refine ⟨hfd, ?_⟩
  rw [e.finrank_eq]
  change Module.finrank ℚ (LinearMap.ker
    (P202Specs.SingularChains.sumCoefficients ℚ ℚ (ZerothHomotopy X))) = _
  rw [component_sum_kernel_finrank, Nat.card_congr E]

/-- Alexander duality for the actual embedded graph, after transporting the
one-point compactification to the library's standard two-sphere. All its
geometric hypotheses follow from the drawing. -/
theorem alexander_realization_equiv {V : Type u} [Finite V] [Nonempty V]
    {G : SimpleGraph V} (D : Drawing G) :
    Nonempty (P202Specs.SingularChains.reducedHomology ℚ ℚ
        (TopCat.of (SphereComplement D)) 0 ≃ₗ[ℚ]
      P202Specs.CohomologyPairs.ordinaryCohomology ℚ ℚ
        (TopCat.of (Realization D)) 1) := by
  let h := sphereHomeomorph
  let K := h '' sphereImage D
  let eX : Realization D ≃ₜ K := h.isEmbedding.homeomorphImage (sphereImage D)
  let eU : SphereComplement D ≃ₜ (Kᶜ : Set _) :=
    (h.isEmbedding.homeomorphImage (sphereImage D)ᶜ).trans
      (Homeomorph.setCongr (Set.image_compl_eq h.bijective))
  have hK : IsCompact K := (sphere_image_compact D).image h.continuous
  have hne : K.Nonempty := by
    have hX := (realization_nonempty_iff D).mpr inferInstance
    obtain ⟨x⟩ := hX
    exact ⟨h x.val, x.val, x.property, rfl⟩
  have hproper : K ≠ Set.univ := by
    intro hfull
    have hi : h OnePoint.infty ∈ K := hfull ▸ Set.mem_univ _
    obtain ⟨x, hx, hxi⟩ := hi
    exact infinity_not_in_image D (h.injective hxi ▸ hx)
  have := plane_realization_stronglyLocallyContractible D
  have := ((realization_homeomorph D).trans eX).symm.isOpenEmbedding.stronglyLocallyContractibleSpace
  have hLC : LocallyContractibleSpace K := StronglyLocallyContractibleSpace.locallyContractible
  obtain ⟨eA⟩ := P202.AlexanderDuality.holds ℚ 2 K (by norm_num)
    hne hproper hK hLC 0
  let e0 := ((P202Specs.SingularChains.reducedHomologyFunctor ℚ ℚ 0).mapIso
    (TopCat.isoOfHomeo (X := TopCat.of (SphereComplement D))
      (Y := TopCat.of (Kᶜ : Set _)) eU)).toLinearEquiv
  let e1 := (P202.AlexanderDuality.positiveReducedCohomologyIso ℚ
    (TopCat.of K) 1 (by norm_num)).toLinearEquiv
  let e2 := ((P202Specs.CohomologyPairs.ordinaryCohomologyFunctor ℚ ℚ 1).mapIso
    (TopCat.isoOfHomeo (X := TopCat.of (Realization D))
      (Y := TopCat.of K) eX).op).toLinearEquiv
  exact ⟨e0.trans (eA.trans (e1.symm.trans e2))⟩

/-- The first rational singular cohomology of a nonempty drawing is finite
dimensional, with dimension f-1, independently of the incidence calculation. -/
theorem cohomology_faces_finrank {V : Type u} [Finite V] [Nonempty V]
    {G : SimpleGraph V} (D : Drawing G) :
    FiniteDimensional ℚ (P202Specs.CohomologyPairs.ordinaryCohomology ℚ ℚ
      (TopCat.of (Realization D)) 1) ∧
    Module.finrank ℚ (P202Specs.CohomologyPairs.ordinaryCohomology ℚ ℚ
      (TopCat.of (Realization D)) 1) = Nat.card (Face D) - 1 := by
  obtain ⟨e⟩ := alexander_realization_equiv D
  obtain ⟨hfd, hdim⟩ := reduced_complement_zero_finrank D
  exact ⟨FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective,
    e.finrank_eq.symm.trans hdim⟩

/-- The rank statement supplies the inequality needed to interpret the
natural subtraction in the nullity formula as an integer difference. -/
theorem incidence_count_inequality
    (hrank : Specs.FiniteCombinatorics.Graph.Plane.CellularBridge.incidence_rankType.{u})
    {V : Type u} [Finite V] (G : SimpleGraph V)
    (o : _root_.FiniteCombinatorics.Graph.Trees.EdgeOrientation G) :
    Nat.card V ≤ Nat.card G.edgeSet + Nat.card G.ConnectedComponent := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite G.edgeSet
  have hc : Nat.card G.ConnectedComponent ≤ Nat.card V :=
    Nat.card_le_card_of_surjective G.connectedComponentMk Quot.mk_surjective
  have hr := (Specs.FiniteCombinatorics.Graph.Plane.CellularBridge.incidenceMap G o).finrank_range_le
  rw [hrank G o, Module.finrank_pi, ← Nat.card_eq_fintype_card] at hr
  omega

/-- Assembly from the incidence rank and the actual first-cohomology dimension. -/
theorem euler_from_cohomology_finrank
    (hrank : Specs.FiniteCombinatorics.Graph.Plane.CellularBridge.incidence_rankType.{u})
    {V : Type u} [Finite V] [Nonempty V] {G : SimpleGraph V} (D : Drawing G)
    (o : _root_.FiniteCombinatorics.Graph.Trees.EdgeOrientation G)
    (hdim : Module.finrank ℚ (P202Specs.CohomologyPairs.ordinaryCohomology ℚ ℚ
      (TopCat.of (Realization D)) 1) =
        Nat.card G.edgeSet + Nat.card G.ConnectedComponent - Nat.card V) :
    (Nat.card V : ℤ) - (Nat.card G.edgeSet : ℤ) + (Nat.card (Face D) : ℤ) =
      1 + (Nat.card G.ConnectedComponent : ℤ) := by
  have hle := incidence_count_inequality hrank G o
  have hface := (cohomology_faces_finrank D).2
  have := finite_sphere_faces D
  have : Nonempty (Face D) := ⟨unboundedFace D⟩
  have hf : 0 < Nat.card (Face D) := Nat.card_pos_iff.mpr ⟨inferInstance, inferInstance⟩
  omega

/-- Euler assembly directly from a singular-homology/incidence equivalence. -/
theorem euler_of_homology_incidence_equiv
    (hrank : Specs.FiniteCombinatorics.Graph.Plane.CellularBridge.incidence_rankType.{u})
    (hdual : Specs.FiniteCombinatorics.Graph.Plane.CellularBridge.incidence_kernel_dual_finrankType.{u})
    (hUCT : Specs.FiniteCombinatorics.Graph.Plane.CellularBridge.realization_universal_coefficientsType.{u})
    {V : Type u} [Fintype V] [Nonempty V] {G : SimpleGraph V} [Fintype G.edgeSet]
    (D : Drawing G) (o : _root_.FiniteCombinatorics.Graph.Trees.EdgeOrientation G)
    (eH : P202Specs.SingularChains.homology ℚ ℚ (TopCat.of (Realization D)) 1 ≃ₗ[ℚ]
      LinearMap.ker (Specs.FiniteCombinatorics.Graph.Plane.CellularBridge.incidenceMap G o)) :
    (Nat.card V : ℤ) - (Nat.card G.edgeSet : ℤ) + (Nat.card (Face D) : ℤ) =
      1 + (Nat.card G.ConnectedComponent : ℤ) := by
  obtain ⟨eC, _⟩ := hUCT D
  have hdim := (eC.trans eH.symm.dualMap).finrank_eq.trans (hdual G o)
  exact euler_from_cohomology_finrank hrank D o hdim

/-- Finiteness is a conclusion about actual connected components. -/
theorem finite_faces : Specs.FiniteCombinatorics.Graph.Plane.Euler.finite_facesType.{u} := by
  intro V _ G D
  exact finite_sphere_faces D

/-- Euler's formula for every drawing, including disconnected and empty graphs. -/
theorem euler_formula : Specs.FiniteCombinatorics.Graph.Plane.Euler.euler_formulaType.{u} := by
  intro V _ G D
  classical
  cases isEmpty_or_nonempty V with
  | inl h =>
    letI := h
    obtain ⟨_, hf, hv, he, hc⟩ := empty_drawing_counts D
    simp only [hv, he, hf, hc]
    norm_num
  | inr h =>
    letI := h
    obtain ⟨o⟩ := _root_.FiniteCombinatorics.Graph.Trees.orientation_exists G
    exact euler_from_cohomology_finrank
      _root_.FiniteCombinatorics.Graph.Plane.CellularBridge.incidence_rank D o
      (_root_.FiniteCombinatorics.Graph.Plane.CellularBridge.realization_cohomology_finrank D).2

/-- The empty drawing has the connected whole sphere as its complement. -/
theorem empty_euler : Specs.FiniteCombinatorics.Graph.Plane.Euler.empty_eulerType.{u} := by
  intro V _ _ G D
  exact empty_drawing_counts D

end FiniteCombinatorics.Graph.Plane.Euler
