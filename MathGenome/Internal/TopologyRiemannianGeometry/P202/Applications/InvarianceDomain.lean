import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Applications.InvarianceDomain
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Applications.JordanBrouwer

/-! Invariance of domain (paper.tex, T34). The embedded open ball and the
exterior of the embedded closed ball form the two complementary components
of the embedded boundary. Local ball restrictions then prove that every
continuous injection on an arbitrary open Euclidean subset is open. -/

noncomputable section
open Set Topology

namespace P202.InvarianceDomain
open P202.Duality.NeighborhoodCohomology

/-- A partition into two nonempty connected sets in a disconnected space
is necessarily the partition into its two components. -/
theorem isOpen_of_connected_partition {X : Type*} [TopologicalSpace X]
    [Nontrivial (ConnectedComponents X)] {A B : Set X}
    (hA : IsConnected A) (hB : IsConnected B)
    (hdis : Disjoint A B) (hcover : A ∪ B = univ) : IsOpen A := by
  classical
  obtain ⟨a, ha⟩ := hA.nonempty
  obtain ⟨b, hb⟩ := hB.nonempty
  have hAc : A ⊆ connectedComponent a := hA.isPreconnected.subset_connectedComponent ha
  have hBc : B ⊆ connectedComponent b := hB.isPreconnected.subset_connectedComponent hb
  have hab : connectedComponent a ≠ connectedComponent b := by
    intro hab
    have hall : ∀ x : X, ConnectedComponents.mk x = ConnectedComponents.mk a := by
      intro x
      apply ConnectedComponents.coe_eq_coe'.mpr
      have hx : x ∈ A ∪ B := hcover.symm ▸ mem_univ x
      rcases hx with hx | hx
      · exact hAc hx
      · rw [hab]; exact hBc hx
    obtain ⟨p, q, hpq⟩ := exists_pair_ne (ConnectedComponents X)
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe p
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe q
    exact hpq ((hall x).trans (hall y).symm)
  have hcomp : connectedComponent b = B := by
    apply Subset.antisymm _ hBc
    intro x hx
    have hxAB : x ∈ A ∪ B := hcover.symm ▸ mem_univ x
    rcases hxAB with hxA | hxB
    · have heq := connectedComponent_eq_iff_mem.mpr hx
      have heq' := connectedComponent_eq_iff_mem.mpr (hAc hxA)
      exact False.elim (hab (heq'.symm.trans heq))
    · exact hxB
  have hcompl : A = Bᶜ := by
    ext x
    have hx : x ∈ A ∪ B := hcover.symm ▸ mem_univ x
    exact ⟨fun h => fun h' => Set.disjoint_left.mp hdis h h', fun h => hx.resolve_right h⟩
  rw [hcompl, ← hcomp]
  exact isClosed_connectedComponent.isOpen_compl


/-- The image of the open unit ball under an embedding of the closed ball
in a sphere is one of the two complementary components of its boundary. -/
theorem sphere_openBall_image (m : ℕ)
    (g : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m+1))) 1 → Sphere (m+1))
    (hg : Topology.IsEmbedding g) :
    IsOpen (range (fun y : Metric.ball (0 : EuclideanSpace ℝ (Fin (m+1))) 1 =>
      g (Set.inclusion Metric.ball_subset_closedBall y))) := by
  let e : Sphere m → Sphere (m+1) :=
    g ∘ Set.inclusion Metric.sphere_subset_closedBall
  have he : Topology.IsEmbedding e := hg.comp (Topology.IsEmbedding.inclusion _)
  let A := range (fun y : Metric.ball (0 : EuclideanSpace ℝ (Fin (m+1))) 1 =>
    g (Set.inclusion Metric.ball_subset_closedBall y))
  let B := (range g)ᶜ
  let C := (range e)ᶜ
  have hC : IsOpen C := (P202.JordanBrouwer.sphere_range_closed he).isOpen_compl
  have hAc : IsConnected A := by
    have : ConnectedSpace (Metric.ball (0 : EuclideanSpace ℝ (Fin (m+1))) 1) :=
      Subtype.connectedSpace ((convex_ball _ _).isConnected
        (Metric.nonempty_ball.mpr (by norm_num)))
    exact isConnected_range (hg.continuous.comp (continuous_inclusion _))
  have hBc : IsConnected B :=
    P202.JordanBrouwer.closedBallComplement (m+1) (by omega) (m+1) 1 (by norm_num) g hg
  have hdis : Disjoint A B := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨y, rfl⟩ hy
    exact hy (mem_range_self _)
  have hcover : A ∪ B = C := by
    ext z
    constructor
    · rintro (⟨y, rfl⟩ | hz)
      · rintro ⟨w, hw⟩
        have hv : w.val = y.val := congrArg Subtype.val (hg.injective hw)
        have hw' := w.property
        have hy' := y.property
        rw [Metric.mem_sphere, hv] at hw'
        exact (ne_of_lt hy') hw'
      · rintro ⟨w, rfl⟩
        exact hz (mem_range_self _)
    · intro hz
      by_cases hz' : z ∈ range g
      · obtain ⟨y, rfl⟩ := hz'
        left
        have hylt : dist y.val 0 < 1 := by
          have hyle : dist y.val 0 ≤ 1 := y.property
          apply lt_of_le_of_ne hyle
          intro heq
          apply hz
          exact ⟨⟨y.val, heq⟩, rfl⟩
        exact ⟨⟨y.val, hylt⟩, rfl⟩
      · exact Or.inr hz'
  have hAsub : A ⊆ C := by rw [← hcover]; exact subset_union_left
  have hBsub : B ⊆ C := by rw [← hcover]; exact subset_union_right
  obtain ⟨q⟩ := P202.JordanBrouwer.componentCount (m+1) (by omega) e he
  have : Nontrivial (ConnectedComponents C) := q.nontrivial
  have hAc' : IsConnected (Subtype.val ⁻¹' A : Set C) :=
    hAc.preimage_of_isOpenMap Subtype.val_injective hC.isOpenEmbedding_subtypeVal.isOpenMap
      (by simpa using hAsub)
  have hBc' : IsConnected (Subtype.val ⁻¹' B : Set C) :=
    hBc.preimage_of_isOpenMap Subtype.val_injective hC.isOpenEmbedding_subtypeVal.isOpenMap
      (by simpa using hBsub)
  have hopen := isOpen_of_connected_partition hAc' hBc' (hdis.preimage Subtype.val)
    (by ext y; simpa only [mem_union, mem_preimage, mem_univ, iff_true] using
      (show y.val ∈ A ∪ B from hcover.symm ▸ y.property))
  have hout := hC.isOpenEmbedding_subtypeVal.isOpenMap _ hopen
  rwa [image_preimage_eq_of_subset (by simpa using hAsub)] at hout

/-- Stereographic coordinates transfer the preceding openness statement to
ordinary Euclidean space. Compactness supplies the embedding of the closed ball. -/
theorem euclidean_openBall_image (m : ℕ)
    (g : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m+1))) 1 →
      EuclideanSpace ℝ (Fin (m+1)))
    (hg : Continuous g) (hi : Function.Injective g) :
    IsOpen (range (fun y : Metric.ball (0 : EuclideanSpace ℝ (Fin (m+1))) 1 =>
      g (Set.inclusion Metric.ball_subset_closedBall y))) := by
  let p : Sphere (m+1) := Classical.choice (P202.JordanBrouwer.sphere_nonempty (m+1))
  let s : {y : Sphere (m+1) | y ≠ p} ≃ₜ EuclideanSpace ℝ (Fin (m+1)) :=
    P202.AlexanderDuality.spherePuncturedHomeomorph (m+1) p
  let j : EuclideanSpace ℝ (Fin (m+1)) → Sphere (m+1) := Subtype.val ∘ s.symm
  have hj : Topology.IsEmbedding j := Topology.IsEmbedding.subtypeVal.comp s.symm.isEmbedding
  have hgj : Topology.IsEmbedding (j ∘ g) :=
    hj.comp (hg.isClosedEmbedding hi).isEmbedding
  have h := sphere_openBall_image m (j ∘ g) hgj
  have heq : j ⁻¹' range (fun y : Metric.ball (0 : EuclideanSpace ℝ (Fin (m+1))) 1 =>
      (j ∘ g) (Set.inclusion Metric.ball_subset_closedBall y)) =
      range (fun y : Metric.ball (0 : EuclideanSpace ℝ (Fin (m+1))) 1 =>
      g (Set.inclusion Metric.ball_subset_closedBall y)) := by
    ext z
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, hj.injective hy⟩
    · rintro ⟨y, rfl⟩
      exact mem_range_self y
  rw [← heq]
  exact h.preimage hj.continuous

/-- Local closed-ball restrictions imply openness of the original injection,
with no compactness or connectedness condition on its open domain. -/
theorem isOpenMap_injection (m : ℕ)
    (U : Set (EuclideanSpace ℝ (Fin (m+1)))) (hU : IsOpen U)
    (f : U → EuclideanSpace ℝ (Fin (m+1)))
    (hf : Continuous f) (hi : Function.Injective f) : IsOpenMap f := by
  intro V hV
  apply isOpen_iff_forall_mem_open.mpr
  rintro z ⟨x, hx, rfl⟩
  have hW : IsOpen (Subtype.val '' V) := hU.isOpenEmbedding_subtypeVal.isOpenMap V hV
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hW.mem_nhds (show x.val ∈ Subtype.val '' V from ⟨x, hx, rfl⟩))
  have hmem (y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m+1))) 1) :
      x.val + r • y.val ∈ Subtype.val '' V := by
    apply hball
    have hy : ‖y.val‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using y.property
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith
  let g : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m+1))) 1 →
      EuclideanSpace ℝ (Fin (m+1)) :=
    fun y => f ⟨x.val + r • y.val, by obtain ⟨v, hv, heq⟩ := hmem y; exact heq ▸ v.property⟩
  have hg : Continuous g := by
    have hc : Continuous (fun y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m+1))) 1 =>
        x.val + r • y.val) := by fun_prop
    exact hf.comp (hc.subtype_mk _)
  have hgi : Function.Injective g := by
    intro y w h
    have h' := congrArg Subtype.val (hi h)
    apply Subtype.ext
    exact smul_right_injective _ hr.ne' (add_left_cancel h')
  let T := range (fun y : Metric.ball (0 : EuclideanSpace ℝ (Fin (m+1))) 1 =>
    g (Set.inclusion Metric.ball_subset_closedBall y))
  refine ⟨T, ?_, euclidean_openBall_image m g hg hgi, ?_⟩
  · rintro _ ⟨y, rfl⟩
    obtain ⟨v, hv, heq⟩ := hmem (Set.inclusion Metric.ball_subset_closedBall y)
    refine ⟨v, hv, ?_⟩
    apply congrArg f
    apply Subtype.ext
    exact heq
  · refine ⟨⟨0, Metric.mem_ball_self (by norm_num)⟩, ?_⟩
    change f _ = f x
    congr 1
    apply Subtype.ext
    simp

/-- Invariance of domain, including the empty open set. -/
theorem invarianceDomain : P202Specs.InvarianceDomain.Expected.invarianceDomain := by
  intro n hn U hU f hf hi
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have ho := isOpenMap_injection m U hU f hf hi
  have he := Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hf hi ho
  exact ⟨ho, by simpa using ho univ isOpen_univ, he.isEmbedding.toHomeomorph,
    fun _ => rfl⟩

end P202.InvarianceDomain
