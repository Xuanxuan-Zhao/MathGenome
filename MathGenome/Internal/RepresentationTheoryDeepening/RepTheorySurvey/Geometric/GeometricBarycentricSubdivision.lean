import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.GeometricBarycentricSubdivision
import MathGenome.Internal.PointSetTopology.D10Topology.Ch17.BarycentricSubdivision

namespace RepTheorySurvey.Geometric.GeometricBarycentricSubdivision

open Geometry Set GeometricBarycentricSubdivisionSpecs
open scoped BigOperators

noncomputable section

/-- Positive barycentric coordinates characterize the relative interior of a simplex. -/
private theorem mem_intrinsicInterior_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Finset E} (hs : s.Nonempty)
    (hind : AffineIndependent ℝ ((↑) : s → E)) {x : E} :
    x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ↔
      ∃ w : s → ℝ, (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧
        (∑ i : s, w i • (i : E)) = x := by
  classical
  obtain ⟨v, hv⟩ := hs
  let A := affineSpan ℝ (s : Set E)
  let p : A := ⟨v, subset_affineSpan ℝ (s : Set E) hv⟩
  let : Nonempty A := ⟨p⟩
  let : Nonempty (s : Set E) := ⟨⟨v, hv⟩⟩
  let q (i : s) : A := ⟨i, subset_affineSpan ℝ (s : Set E) i.property⟩
  let e : A.direction ≃ᵃⁱ[ℝ] A := AffineIsometryEquiv.vaddConst ℝ p
  let f : A.direction →ᵃ[ℝ] E := A.subtype.comp e.toAffineEquiv.toAffineMap
  have hq : range q = (Subtype.val : A → E) ⁻¹' (s : Set E) := by
    ext y
    exact ⟨by rintro ⟨i, rfl⟩; exact i.property,
      fun hy => ⟨⟨y.val, hy⟩, Subtype.ext rfl⟩⟩
  let b : AffineBasis s ℝ A.direction :=
    ⟨e.symm ∘ q,
      e.symm.toAffineEquiv.affineIndependent_iff.mpr
        ((A.subtype.affineIndependent_iff Subtype.val_injective).mp hind),
      by
        rw [range_comp, hq]
        exact e.symm.toAffineEquiv.toAffineMap.span_eq_top_of_surjective e.symm.surjective
          (affineSpan_coe_preimage_eq_top (s : Set E))⟩
  have hfb : f ∘ b = ((↑) : s → E) := by
    funext i
    change (e (e.symm (q i))).val = i.val
    rw [e.apply_symm_apply]
  have hHull : f '' convexHull ℝ (range b) = convexHull ℝ (s : Set E) := by
    rw [f.image_convexHull, ← range_comp, hfb]
    exact congrArg (convexHull ℝ) Subtype.range_coe
  have hPre : e ⁻¹' ((Subtype.val : A → E) ⁻¹' convexHull ℝ (s : Set E)) =
      convexHull ℝ (range b) := by
    change f ⁻¹' convexHull ℝ (s : Set E) = _
    rw [← hHull, preimage_image_eq _ (show Function.Injective f from
      Subtype.val_injective.comp e.injective)]
  have hInt : intrinsicInterior ℝ (convexHull ℝ (s : Set E)) =
      f '' interior (convexHull ℝ (range b)) := by
    rw [intrinsicInterior, affineSpan_convexHull, ← hPre]
    change Subtype.val '' interior _ =
      (Subtype.val ∘ e.toHomeomorph) '' interior (e.toHomeomorph ⁻¹' _)
    rw [← e.toHomeomorph.preimage_interior]
    change Subtype.val '' interior _ =
      (fun y => (e.toHomeomorph y).val) '' (e.toHomeomorph ⁻¹' interior _)
    rw [← Set.image_image (Subtype.val : A → E) (e.toHomeomorph : A.direction → A),
      Set.image_preimage_eq _ e.toHomeomorph.surjective]
  have hComb (w : s → ℝ) (hw : (∑ i, w i) = 1) :
      f (Finset.univ.affineCombination ℝ b w) = ∑ i : s, w i • (i : E) := by
    rw [Finset.map_affineCombination Finset.univ b w hw f, hfb,
      Finset.affineCombination_eq_linear_combination _ _ _ hw]
  rw [hInt, b.interior_convexHull]
  constructor
  · rintro ⟨y, hy, rfl⟩
    let w := fun i => b.coord i y
    have hw : (∑ i, w i) = 1 := b.sum_coord_apply_eq_one y
    exact ⟨w, hy, hw, by rw [← hComb w hw, b.affineCombination_coord_eq_self]⟩
  · rintro ⟨w, hw, hsum, rfl⟩
    refine ⟨Finset.univ.affineCombination ℝ b w, ?_, hComb w hsum⟩
    intro i
    rw [b.coord_apply_combination_of_mem (Finset.mem_univ i) hsum]
    exact hw i

/-- A point of the relative interior of a simplex cannot lie in a proper face. -/
private theorem subset_of_mem_intrinsicInterior_of_mem_hull {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {s t : Finset E}
    (hs : s.Nonempty) (hind : AffineIndependent ℝ ((↑) : s → E)) (hts : t ⊆ s)
    {x : E} (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hxt : x ∈ convexHull ℝ (t : Set E)) : s ⊆ t := by
  classical
  obtain ⟨w, hw, hsum, hcomb⟩ := (mem_intrinsicInterior_iff hs hind).mp hx
  let J : Set s := {i | i.val ∈ t}
  have hJ : ((↑) : s → E) '' J = (t : Set E) := by
    ext y
    exact ⟨by rintro ⟨i, hi, rfl⟩; exact hi, fun hy => ⟨⟨y, hts hy⟩, hy, rfl⟩⟩
  have hspan : Finset.univ.affineCombination ℝ ((↑) : s → E) w ∈
      affineSpan ℝ (((↑) : s → E) '' J) := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum, hcomb, hJ]
    exact convexHull_subset_affineSpan _ hxt
  intro i hi
  by_contra hit
  exact (hw ⟨i, hi⟩).ne' (hind.eq_zero_of_affineCombination_mem_affineSpan hsum hspan
    (Finset.mem_univ (⟨i, hi⟩ : s)) hit)

theorem disjoint_face_intrinsicInteriors : DisjointFaceIntrinsicInteriors := by
  classical
  intro σ _ K s t hs ht hne
  let := Fintype.ofFinite σ
  refine Set.disjoint_left.mpr fun x hx hy => hne ?_
  have h : x ∈ convexHull ℝ ((s ∩ t : Finset (σ → ℝ)) : Set (σ → ℝ)) := by
    rw [Finset.coe_inter, ← K.convexHull_inter_convexHull hs ht]
    exact ⟨intrinsicInterior_subset hx, intrinsicInterior_subset hy⟩
  apply Finset.Subset.antisymm
  · exact Finset.Subset.trans
      (subset_of_mem_intrinsicInterior_of_mem_hull (K.nonempty_of_mem_faces hs)
        (K.indep hs) Finset.inter_subset_left hx h) Finset.inter_subset_right
  · exact Finset.Subset.trans
      (subset_of_mem_intrinsicInterior_of_mem_hull (K.nonempty_of_mem_faces ht)
        (K.indep ht) Finset.inter_subset_right hy h) Finset.inter_subset_left

open D10Topology.Ch17 (Euclidean GeometricComplex toMathlib toMathlib_faces toMathlib_space)
open D10Topology.Ch17.Subdivision
open Specs.D10Topology.Ch17.BarycentricSubdivision (FaceChain)

/-- The finite cell representation includes the empty face. -/
private def withEmptyFace {m : ℕ} (K : SimplicialComplex ℝ (Euclidean m))
    (hK : K.faces.Finite) : GeometricComplex m where
  cells := insert ∅ hK.toFinset
  empty_mem := Finset.mem_insert_self _ _
  independent := by
    classical
    intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact affineIndependent_of_subsingleton ℝ _
    · exact K.indep (hK.mem_toFinset.mp hs)
  face_closed := by
    classical
    intro s hs t hts
    rcases Finset.eq_empty_or_nonempty t with rfl | ht
    · exact Finset.mem_insert_self _ _
    · rcases Finset.mem_insert.mp hs with rfl | hs
      · exact (ht.ne_empty (Finset.subset_empty.mp hts)).elim
      · exact Finset.mem_insert_of_mem (hK.mem_toFinset.mpr
          (K.down_closed (hK.mem_toFinset.mp hs) hts ht))
  inter_eq := by
    classical
    intro s hs t ht
    change convexHull ℝ (s : Set (Euclidean m)) ∩ convexHull ℝ (t : Set (Euclidean m)) =
      convexHull ℝ ((s ∩ t : Finset (Euclidean m)) : Set (Euclidean m))
    rcases Finset.mem_insert.mp hs with rfl | hs
    · simp
    rcases Finset.mem_insert.mp ht with rfl | ht
    · simp
    rw [Finset.coe_inter]
    exact K.convexHull_inter_convexHull (hK.mem_toFinset.mp hs) (hK.mem_toFinset.mp ht)

private theorem mem_withEmptyFace {m : ℕ} {K : SimplicialComplex ℝ (Euclidean m)}
    (hK : K.faces.Finite) {s : Finset (Euclidean m)} :
    s ∈ (withEmptyFace K hK).cells ↔ s = ∅ ∨ s ∈ K.faces := by
  classical
  change s ∈ insert ∅ hK.toFinset ↔ _
  rw [Finset.mem_insert, hK.mem_toFinset]

private theorem toMathlib_withEmptyFace {m : ℕ} (K : SimplicialComplex ℝ (Euclidean m))
    (hK : K.faces.Finite) : toMathlib (withEmptyFace K hK) = K := by
  apply SimplicialComplex.ext
  ext s
  rw [toMathlib_faces]
  change (s ∈ (withEmptyFace K hK).cells ∧ s ≠ ∅) ↔ s ∈ K.faces
  rw [mem_withEmptyFace hK]
  exact ⟨fun ⟨hs, hn⟩ => hs.resolve_left hn,
    fun hs => ⟨Or.inr hs, (K.nonempty_of_mem_faces hs).ne_empty⟩⟩

private theorem faceMean_mem_intrinsicInterior {m : ℕ} {K : GeometricComplex m}
    {s : Finset (Euclidean m)} (hs : s ∈ K.cells) (hne : s.Nonempty) :
    faceMean s ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set (Euclidean m))) := by
  classical
  let w : s → ℝ := fun _ => (s.card : ℝ)⁻¹
  have hc : 0 < (s.card : ℝ) := Nat.cast_pos.mpr hne.card_pos
  have hsum : (∑ i, w i) = 1 := by simp [w, hc.ne']
  refine (mem_intrinsicInterior_iff hne (K.independent s hs)).mpr
    ⟨w, fun _ => inv_pos.mpr hc, hsum, ?_⟩
  rw [faceMean_eq_affineCombination s hne,
    Finset.affineCombination_eq_linear_combination _ _ _ hsum]

/-- The greatest face in a chain contains the entire chain simplex. Positive coefficients
on the means give positive coordinates on every vertex of that greatest face. -/
private theorem chain_hull_properties {m : ℕ} (K : GeometricComplex m)
    {C : Finset (Finset (Euclidean m))} (hC : FaceChain K C)
    {G : Finset (Euclidean m)} (hGC : G ∈ C) (hmax : ∀ F ∈ C, F ⊆ G)
    (hind : AffineIndependent ℝ
      ((↑) : ↥(C.image faceMean) → Euclidean m)) :
    convexHull ℝ ((C.image faceMean : Finset (Euclidean m)) : Set (Euclidean m)) ⊆
        convexHull ℝ (G : Set (Euclidean m)) ∧
    intrinsicInterior ℝ (convexHull ℝ ((C.image faceMean : Finset (Euclidean m)) :
        Set (Euclidean m))) ⊆ intrinsicInterior ℝ (convexHull ℝ (G : Set (Euclidean m))) ∧
    ∃ v ∈ C.image faceMean, v ∈ intrinsicInterior ℝ (convexHull ℝ (G : Set (Euclidean m))) := by
  classical
  have hG := hC.1 G hGC
  refine ⟨convexHull_min ?_ (convex_convexHull ℝ _), ?_, ?_⟩
  · intro v hv
    obtain ⟨F, hFC, rfl⟩ := Finset.mem_image.mp hv
    exact convexHull_mono (hmax F hFC) (faceMean_mem F (hC.1 F hFC).2)
  · intro x hx
    have hne : (C.image faceMean).Nonempty := Finset.image_nonempty.mpr ⟨G, hGC⟩
    obtain ⟨w, hw, hsum, hxsum⟩ := (mem_intrinsicInterior_iff hne hind).mp hx
    let a (F : Finset (Euclidean m)) : ℝ :=
      if h : F ∈ C then w ⟨faceMean F, Finset.mem_image.mpr ⟨F, h, rfl⟩⟩ else 0
    have ha (F : Finset (Euclidean m)) (hF : F ∈ C) : 0 < a F := by
      simpa only [a, dite_eq_left hF] using hw ⟨faceMean F, Finset.mem_image.mpr ⟨F, hF, rfl⟩⟩
    obtain ⟨H, hHC, hHmax, hpos, _, _⟩ := positive_chain_coordinates_top C ⟨G, hGC⟩
      (fun F hF => (hC.1 F hF).2) hC.2 a ha
    have hHG : H = G := Finset.Subset.antisymm (hmax H hHC) (hHmax G hGC)
    have hinj : Set.InjOn faceMean (C : Set (Finset (Euclidean m))) :=
      (faceMean_injective K).mono fun F hF => hC.1 F hF
    have hcoeff (F : C) : a F = w ⟨faceMean F, Finset.mem_image.mpr ⟨F, F.property, rfl⟩⟩ := by
      simp only [a, dite_eq_left F.property]
    let e : C ≃ (C.image faceMean : Finset (Euclidean m)) :=
      Equiv.ofBijective (fun F => ⟨faceMean F, Finset.mem_image.mpr ⟨F, F.property, rfl⟩⟩)
        ⟨fun F F' h => Subtype.ext (hinj F.property F'.property (congrArg Subtype.val h)),
          by
            intro v
            obtain ⟨F, hF, heq⟩ := Finset.mem_image.mp v.property
            exact ⟨⟨F, hF⟩, Subtype.ext heq⟩⟩
    have hsub (F : Finset (Euclidean m)) (hF : F ∈ C) : F ⊆ G ∧ F.Nonempty :=
      ⟨hmax F hF, (hC.1 F hF).2⟩
    refine (mem_intrinsicInterior_iff hG.2 (K.independent _ hG.1)).mpr
      ⟨fun i => chainCoordinates C a i, fun i => (hpos i).mpr (hHG.symm ▸ i.property), ?_, ?_⟩
    · rw [Finset.sum_coe_sort, sum_chainCoordinates _ _ _ hsub, ← Finset.sum_coe_sort C a]
      exact (Fintype.sum_equiv e _ _ hcoeff).trans hsum
    · rw [Finset.sum_coe_sort G (fun v => chainCoordinates C a v • v),
        sum_smul_chainCoordinates _ _ _ hsub,
        ← Finset.sum_coe_sort C (fun F => a F • faceMean F)]
      exact (Fintype.sum_equiv e _ _ (fun F : C =>
        congrArg (fun r : ℝ => r • faceMean F.val) (hcoeff F))).trans hxsum
  · exact ⟨faceMean G, Finset.mem_image.mpr ⟨G, hGC, rfl⟩, faceMean_mem_intrinsicInterior hG.1 hG.2⟩

private theorem exists_subdivision_euclidean {m : ℕ}
    (K : SimplicialComplex ℝ (Euclidean m)) (hK : K.faces.Finite) :
    ∃ (L : SimplicialComplex ℝ (Euclidean m)) (carrier : L.faces → K.faces),
      L.faces.Finite ∧ L.space = K.space ∧ Monotone carrier ∧
      ∀ s : L.faces,
        convexHull ℝ (s.val : Set (Euclidean m)) ⊆ convexHull ℝ ((carrier s).val : Set (Euclidean m)) ∧
        intrinsicInterior ℝ (convexHull ℝ (s.val : Set (Euclidean m))) ⊆
          intrinsicInterior ℝ (convexHull ℝ ((carrier s).val : Set (Euclidean m))) ∧
        ∃ v ∈ s.val, v ∈ intrinsicInterior ℝ (convexHull ℝ ((carrier s).val : Set (Euclidean m))) := by
  classical
  let D := withEmptyFace K hK
  let B := barycentricComplex D
  let L := toMathlib B
  have hex (s : L.faces) : ∃ C, FaceChain D C ∧ C.image faceMean = s.val := by
    rcases s with ⟨s, hs⟩
    change s ∈ (toMathlib B).faces at hs
    rw [toMathlib_faces] at hs
    exact (mem_barycentricCells_iff D _).mp hs.1
  choose chain hchain using hex
  have hgreatest (s : L.faces) : ∃ G ∈ chain s, ∀ F ∈ chain s, F ⊆ G := by
    apply inclusionChain_greatest _ _ (hchain s).1.2
    exact Finset.image_nonempty.mp ((hchain s).2 ▸ L.nonempty_of_mem_faces s.property)
  choose top htop using hgreatest
  have htopface (s : L.faces) : top s ∈ K.faces := by
    have h := (hchain s).1.1 _ (htop s).1
    exact ((mem_withEmptyFace hK).mp h.1).resolve_left h.2.ne_empty
  let carrier (s : L.faces) : K.faces := ⟨top s, htopface s⟩
  have hgeom (s : L.faces) :
      convexHull ℝ (s.val : Set (Euclidean m)) ⊆ convexHull ℝ ((carrier s).val : Set (Euclidean m)) ∧
      intrinsicInterior ℝ (convexHull ℝ (s.val : Set (Euclidean m))) ⊆
        intrinsicInterior ℝ (convexHull ℝ ((carrier s).val : Set (Euclidean m))) ∧
      ∃ v ∈ s.val, v ∈ intrinsicInterior ℝ (convexHull ℝ ((carrier s).val : Set (Euclidean m))) := by
    have hind : AffineIndependent ℝ
        ((↑) : ↥((chain s).image faceMean) → Euclidean m) := by
      rw [(hchain s).2]
      exact L.indep s.property
    simpa only [carrier, (hchain s).2] using
      chain_hull_properties D (hchain s).1 (htop s).1 (htop s).2 hind
  refine ⟨L, carrier, ?_, ?_, ?_, hgeom⟩
  · rw [toMathlib_faces]
    exact B.cells.finite_toSet.sdiff
  · rw [toMathlib_space, barycentricComplex_support, ← toMathlib_space, toMathlib_withEmptyFace]
  · intro s t hst
    obtain ⟨v, hvs, hv⟩ := (hgeom s).2.2
    have hvt : v ∈ convexHull ℝ ((carrier t).val : Set (Euclidean m)) :=
      (hgeom t).1 (subset_convexHull ℝ _ (hst hvs))
    change top s ⊆ top t
    have hi : v ∈ convexHull ℝ ((top s ∩ top t : Finset (Euclidean m)) : Set (Euclidean m)) := by
      rw [Finset.coe_inter, ← K.convexHull_inter_convexHull (htopface s) (htopface t)]
      exact ⟨intrinsicInterior_subset hv, hvt⟩
    exact Finset.Subset.trans
      (subset_of_mem_intrinsicInterior_of_mem_hull (K.nonempty_of_mem_faces (htopface s))
        (K.indep (htopface s)) Finset.inter_subset_left hv hi) Finset.inter_subset_right

section AffineImage

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [DecidableEq F]

private theorem convexHull_image (φ : E ≃ᵃ[ℝ] F) (s : Finset E) :
    convexHull ℝ (s.image φ : Set F) = φ '' convexHull ℝ (s : Set E) := by
  rw [Finset.coe_image]
  exact (φ.toAffineMap.image_convexHull _).symm

/-- Applying an affine equivalence to every vertex transports the geometric complex. -/
private def imageComplex (φ : E ≃ᵃ[ℝ] F) (K : SimplicialComplex ℝ E) :
    SimplicialComplex ℝ F where
  toPreAbstractSimplicialComplex := K.toPreAbstractSimplicialComplex.map φ
  indep := by
    rintro _ ⟨s, hs, rfl⟩
    change AffineIndependent ℝ (Subtype.val : ↥((s.image φ : Finset F) : Set F) → F)
    rw [Finset.coe_image]
    exact (φ.affineIndependent_set_of_eq_iff).mpr (K.indep hs)
  inter_subset_convexHull := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    have h (A : Set E) : convexHull ℝ (φ '' A) = φ '' convexHull ℝ A :=
      (φ.toAffineMap.image_convexHull A).symm
    simp only [Finset.coe_image, ← Set.image_inter φ.injective, h]
    exact Set.image_mono (K.inter_subset_convexHull hs ht)

private theorem imageComplex_finite (φ : E ≃ᵃ[ℝ] F) {K : SimplicialComplex ℝ E}
    (hK : K.faces.Finite) : (imageComplex φ K).faces.Finite := by
  change ((fun s : Finset E => s.image φ) '' K.faces).Finite
  exact hK.image _

private theorem imageComplex_space (φ : E ≃ᵃ[ℝ] F) (K : SimplicialComplex ℝ E) :
    (imageComplex φ K).space = φ '' K.space := by
  ext x
  rw [SimplicialComplex.mem_space_iff]
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, hx⟩
    rw [convexHull_image] at hx
    exact Set.image_mono (K.convexHull_subset_space hs) hx
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨s, hs, hys⟩ := SimplicialComplex.mem_space_iff.mp hy
    exact ⟨s.image φ, ⟨s, hs, rfl⟩, convexHull_image φ s ▸ ⟨y, hys, rfl⟩⟩

private def faceImage (φ : E ≃ᵃ[ℝ] F) (K : SimplicialComplex ℝ E) :
    K.faces ≃o (imageComplex φ K).faces :=
  { Equiv.ofBijective (fun s : K.faces =>
        (⟨s.val.image φ, ⟨s.val, s.property, rfl⟩⟩ : (imageComplex φ K).faces))
      ⟨fun s t h => Subtype.ext (Finset.image_injective φ.injective (congrArg Subtype.val h)),
        by rintro ⟨t, s, hs, rfl⟩; exact ⟨⟨s, hs⟩, rfl⟩⟩ with
    map_rel_iff' := by
      intro s t
      change s.val.image φ ⊆ t.val.image φ ↔ s.val ⊆ t.val
      exact Finset.image_subset_image_iff φ.injective }

end AffineImage

private theorem intrinsicInterior_hull_image {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [DecidableEq F]
    (φ : E ≃ᵃ[ℝ] F) (s : Finset E) :
    intrinsicInterior ℝ (convexHull ℝ (s.image φ : Set F)) =
      φ '' intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
  rw [convexHull_image, φ.intrinsicInterior_image]

theorem exists_barycentric_subdivision : ExistsBarycentricSubdivision := by
  classical
  intro σ _ K hK
  let := Fintype.ofFinite σ
  let m := Fintype.card σ
  let φ : (σ → ℝ) ≃ᵃ[ℝ] Euclidean m :=
    ((LinearEquiv.piCongrLeft' ℝ (fun _ : σ => ℝ) (Fintype.equivFin σ)).trans
      (EuclideanSpace.equiv (Fin m) ℝ).symm.toLinearEquiv).toAffineEquiv
  let K₀ := imageComplex φ K
  obtain ⟨L₀, carrier₀, hf, he, hm, hg⟩ :=
    exists_subdivision_euclidean K₀ (imageComplex_finite φ hK)
  let L := imageComplex φ.symm L₀
  let iK := faceImage φ K
  let iL := faceImage φ.symm L₀
  let carrier := iK.symm ∘ carrier₀ ∘ iL.symm
  refine ⟨L, carrier, imageComplex_finite φ.symm hf, ?_,
    iK.symm.monotone.comp (hm.comp iL.symm.monotone), ?_⟩
  · change (imageComplex φ.symm L₀).space = K.space
    rw [imageComplex_space, he, imageComplex_space]
    exact φ.toEquiv.symm_image_image _
  · intro s
    let t := iL.symm s
    let u := carrier s
    have hs : t.val.image φ.symm = s.val := congrArg Subtype.val (iL.apply_symm_apply s)
    have hu : u.val.image φ = (carrier₀ t).val :=
      congrArg Subtype.val (iK.apply_symm_apply (carrier₀ t))
    have hu' : (carrier₀ t).val.image φ.symm = u.val := by
      rw [← hu, Finset.image_image]
      have hinv : (φ.symm : Euclidean m → σ → ℝ) ∘ φ = id := funext φ.symm_apply_apply
      rw [hinv, Finset.image_id]
    obtain ⟨hhull, hint, v, hv, hvi⟩ := hg t
    change convexHull ℝ (s.val : Set (σ → ℝ)) ⊆ convexHull ℝ (u.val : Set (σ → ℝ)) ∧
      intrinsicInterior ℝ (convexHull ℝ (s.val : Set (σ → ℝ))) ⊆
        intrinsicInterior ℝ (convexHull ℝ (u.val : Set (σ → ℝ))) ∧
      ∃ v ∈ s.val, v ∈ intrinsicInterior ℝ (convexHull ℝ (u.val : Set (σ → ℝ)))
    rw [← hs, ← hu', intrinsicInterior_hull_image, intrinsicInterior_hull_image,
      convexHull_image, convexHull_image]
    exact ⟨Set.image_mono hhull, Set.image_mono hint, φ.symm v,
      Finset.mem_image.mpr ⟨v, hv, rfl⟩, ⟨v, hvi, rfl⟩⟩

end

end RepTheorySurvey.Geometric.GeometricBarycentricSubdivision
