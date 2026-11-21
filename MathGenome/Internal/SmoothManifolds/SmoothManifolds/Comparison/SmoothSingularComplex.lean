import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Comparison.SmoothSingularComplex
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Corners.StructureAndFaces
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.SmoothMaps
import Mathlib.Tactic.ApplyFun

namespace SmoothManifolds.SmoothSingular
open ModelData AtlasData MapData CornerData SmoothSingularData Set Filter
open scoped Topology
universe u v w

abbrev Simplex := SmoothSingularData.Simplex
abbrev faceAmbient := @SmoothSingularData.faceAmbient
abbrev face := @SmoothSingularData.face
abbrev SimplexSmooth := @SmoothSingularData.SimplexSmooth
abbrev SingularSimplex := @SmoothSingularData.SingularSimplex
abbrev Chains := @SmoothSingularData.Chains
noncomputable abbrev generate := @SmoothSingularData.generate
noncomputable abbrev boundary := @SmoothSingularData.boundary
noncomputable abbrev boundaryZero := @SmoothSingularData.boundaryZero
abbrev Cochains := @SmoothSingularData.Cochains
noncomputable abbrev coboundary := @SmoothSingularData.coboundary
noncomputable abbrev cocycles := @SmoothSingularData.cocycles
noncomputable abbrev previousCoboundary := @SmoothSingularData.previousCoboundary
noncomputable abbrev coboundaries := @SmoothSingularData.coboundaries
noncomputable abbrev Cohomology := @SmoothSingularData.Cohomology
noncomputable abbrev chainMap := @SmoothSingularData.chainMap
noncomputable abbrev cochainMap := @SmoothSingularData.cochainMap

@[simp] theorem face_val {q : ℕ} (j : Fin (q+2)) (x : Simplex q) :
    (face j x).val = faceAmbient j x.val := rfl

@[simp] theorem barycentric_faceAmbient {q : ℕ} (j : Fin (q+2)) (x : Euclidean q) :
    simplexBarycentric (faceAmbient j x) = (j.insertNth 0 (simplexBarycentric x) : Euclidean (q+2)) := by
  apply CornerExamples.barycentric_tail_of_sum
  simp [Fin.sum_insertNth]

@[simp] theorem face_barycentric {q : ℕ} (j : Fin (q+2)) (x : Simplex q) :
    simplexBarycentric (face j x).val = (j.insertNth 0 (simplexBarycentric x.val) : Euclidean (q+2)) :=
  barycentric_faceAmbient j x.val

theorem faceAmbient_smooth {q : ℕ} (j : Fin (q+2)) :
    ContDiff ℝ (⊤ : ℕ∞) (faceAmbient j) := by
  apply contDiff_pi.mpr
  intro i
  change ContDiff ℝ (⊤ : ℕ∞) (fun x : Euclidean q =>
    (j.insertNth 0 (simplexBarycentric x) : Euclidean (q+2)) i.succ)
  generalize hi : i.succ = k
  refine Fin.succAboveCases j ?_ (fun k => ?_) k
  · simp only [Fin.insertNth_apply_same]
    exact contDiff_const
  · simp only [Fin.insertNth_apply_succAbove]
    exact (contDiff_apply ℝ (fun _ : Fin (q+1) => ℝ) k).comp
      (CornerExamples.contDiff_barycentric q)

theorem face_continuous {q : ℕ} (j : Fin (q+2)) : Continuous (face j) :=
  ((faceAmbient_smooth j).continuous.comp continuous_subtype_val).subtype_mk _

/-- Simplicial face identity, as an identity of the actual affine maps. -/
theorem face_comp_face {q : ℕ} (i : Fin (q+2)) (j : Fin (q+3))
    (h : j.val ≤ i.val) :
    face j ∘ face i = face i.succ ∘ face (Fin.castLT j (lt_of_le_of_lt h i.isLt)) := by
  funext x
  apply Subtype.ext
  apply_fun simplexBarycentric
  · simp only [Function.comp_apply, face_barycentric]
    -- Insert zeros at j ≤ i, in the two orders.
    let k : Fin (q+2) := Fin.castLT j (lt_of_le_of_lt h i.isLt)
    have hik : k ≤ i := h
    have hji : j = k.castSucc := by ext; rfl
    change (j.insertNth 0 (i.insertNth 0 (simplexBarycentric x.val) : Euclidean (q+2)) : Euclidean (q+3)) =
      (i.succ.insertNth 0 (k.insertNth 0 (simplexBarycentric x.val) : Euclidean (q+2)) : Euclidean (q+3))
    rw [hji]
    apply (Fin.insertNth_eq_iff).mpr
    constructor
    · have hki : k.castSucc = i.succ.succAbove k := by
        symm
        exact Fin.succAbove_succ_of_le i k hik
      rw [hki, Fin.insertNth_apply_succAbove]
      simp
    · funext r
      symm
      change (i.succ.insertNth 0
        (k.insertNth 0 (simplexBarycentric x.val) : Euclidean (q+2)) : Euclidean (q+3))
          (k.castSucc.succAbove r) = (i.insertNth 0 (simplexBarycentric x.val) : Euclidean (q+2)) r
      by_cases hr : r = i
      · subst r
        rw [Fin.succAbove_castSucc_of_le k i hik, Fin.insertNth_apply_same]
        simp
      · obtain ⟨s, rfl⟩ := Fin.exists_succAbove_eq hr
        have hf : k.castSucc.succAbove (i.succAbove s) =
            i.succ.succAbove (k.succAbove s) := by
          apply Fin.ext
          simp only [Fin.succAbove, Fin.coe_castSucc, Fin.val_succ,
            Fin.lt_def]
          split_ifs <;> simp_all [Fin.lt_def] <;> omega
        rw [hf, Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
        simp
  · intro a b hab
    funext r
    exact congrFun hab r.succ

section Smoothness
variable {n m q : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}

/-- Restriction along a globally smooth ambient map preserves local extensions. -/
theorem smooth_precompose {p : ℕ} {f : Simplex q → M}
    (hf : SimplexSmooth S f) (g : Simplex p → Simplex q)
    (G : Euclidean p → Euclidean q) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hg : ∀ x, (g x).val = G x.val) : SimplexSmooth S (f ∘ g) := by
  have hgc : Continuous g := by
    apply continuous_induced_rng.mpr
    simpa only [Function.comp_def, hg] using hG.continuous.comp continuous_subtype_val
  refine ⟨hf.1.comp hgc, ?_⟩
  intro x d hd hdx
  have he := SmoothManifolds.LocalCoordinateExtension.precomp
    (hf.2 (g x) d hd hdx) hgc.continuousAt rfl
  have hge : MapData.LocalCoordinateExtension (⊤ : ℕ∞) Subtype.val
      (fun y : Simplex p => (g y).val) x :=
    ⟨univ, isOpen_univ, mem_univ _, G, hG.contDiffOn,
      Eventually.of_forall (fun y => (hg y).symm)⟩
  exact SmoothManifolds.LocalCoordinateExtension.comp he hge

theorem smooth_face {f : Simplex (q+1) → M} (hf : SimplexSmooth S f)
    (j : Fin (q+2)) : SimplexSmooth S (f ∘ face j) :=
  smooth_precompose hf (face j) (faceAmbient j) (faceAmbient_smooth j) (face_val j)

theorem smooth_postcompose {f : M → N} (hf : IsSmoothMap S T f)
    {σ : Simplex q → M} (hσ : SimplexSmooth S σ) : SimplexSmooth T (f ∘ σ) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).1)
  refine ⟨hfc.comp hσ.1, ?_⟩
  intro x d hd hdx
  obtain ⟨e, he, hxe⟩ := S.smoothStructure.property.1.1 (σ x)
  have hg := (hf (σ x)).2 e he d hd hxe hdx
  have hp := SmoothManifolds.LocalCoordinateExtension.precomp hg hσ.1.continuousAt rfl
  exact SmoothManifolds.LocalCoordinateExtension.comp hp (hσ.2 x e he hxe)

end Smoothness

section Algebra
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : SmoothManifold n a M)

@[simp] theorem generate_smooth {q : ℕ} {f : Simplex q → M} (hf : SimplexSmooth S f) :
    generate S f = Finsupp.single ⟨f,hf⟩ 1 := by
  simp [generate, SmoothSingularData.generate, hf]

@[simp] theorem generate_simplex {q : ℕ} (σ : SingularSimplex S q) :
    generate S σ.val = Finsupp.single σ 1 := generate_smooth S σ.property

/-- The actual face restriction, with its proved smoothness. -/
def restrict {q : ℕ} (σ : SingularSimplex S (q+1)) (j : Fin (q+2)) :
    SingularSimplex S q := ⟨σ.val ∘ face j, smooth_face σ.property j⟩

@[simp] theorem boundary_single {q : ℕ} (σ : SingularSimplex S (q+1)) (r : ℝ) :
    boundary S q (Finsupp.single σ r) =
      r • ∑ j : Fin (q+2), (-1 : ℝ)^j.val • Finsupp.single (restrict S σ j) 1 := by
  simp only [boundary, SmoothSingularData.boundary, Finsupp.linearCombination_single]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  change (-1 : ℝ)^j.val • generate S (σ.val ∘ face j) = _
  rw [generate_smooth S (smooth_face σ.property j)]
  rfl

@[simp] theorem boundary_generate {q : ℕ} {f : Simplex (q+1) → M}
    (hf : SimplexSmooth S f) :
    boundary S q (generate S f) =
      ∑ j : Fin (q+2), (-1 : ℝ)^j.val • generate S (f ∘ face j) := by
  rw [generate_smooth S hf]
  simp only [boundary, SmoothSingularData.boundary, Finsupp.linearCombination_single, one_smul]

end Algebra

/-- The cancellation bijection (i,j) ↦ (j,i+1), for j ≤ i. -/
theorem alternating_double_sum {V : Type*} [AddCommGroup V] [Module ℝ V]
    (q : ℕ) (F : Fin (q+2) → Fin (q+3) → V)
    (hF : ∀ i j (h : j.val ≤ i.val),
      F i j = F (Fin.castLT j (lt_of_le_of_lt h i.isLt)) i.succ) :
    ∑ i, ∑ j, ((-1 : ℝ)^i.val * (-1 : ℝ)^j.val) • F i j = 0 := by
  classical
  rw [← Finset.sum_product']
  let P := Fin (q+2) × Fin (q+3)
  let A : Finset P := {ij | ij.2.val ≤ ij.1.val}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl A,
    ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ A → P := fun ij hij =>
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).2 ij.1.isLt), ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp only [A, φ, Finset.compl_filter, Finset.mem_filter_univ,
      Fin.val_castLT, Fin.val_succ] at hij ⊢
    omega
  · rintro ⟨i,j⟩ hij ⟨i',j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using congrArg Prod.snd h,
      by simpa [φ, Fin.castSucc_castLT] using congrArg (fun x => Fin.castSucc x.1) h⟩
  · rintro ⟨i',j'⟩ hij'
    simp only [A, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(j'.pred (by intro h; subst j'; simp at hij'), i'.castSucc), ?_, ?_⟩
    · simpa [A] using Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · rintro ⟨i,j⟩ hij
    dsimp only
    rw [hF i j (Finset.mem_filter.mp hij).2]
    dsimp only [φ]
    simp only [Fin.val_castLT, Fin.val_succ, pow_succ, mul_neg_one]
    simp [mul_neg, mul_comm]

section Complex
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : SmoothManifold n a M)

theorem boundary_squared (q : ℕ) :
    (boundary S q).comp (boundary S (q+1)) = 0 := by
  apply Finsupp.lhom_ext
  intro σ r
  have hr : Finsupp.single σ r = r • generate S σ.val := by simp
  change boundary S q (boundary S (q+1) (Finsupp.single σ r)) = 0
  rw [hr, map_smul, map_smul]
  suffices hzero : boundary S q (boundary S (q+1) (generate S σ.val)) = 0 by
    rw [hzero, smul_zero]
  rw [boundary_generate S σ.property, map_sum]
  simp only [map_smul]
  have he : ∀ j : Fin (q+3),
      boundary S q (generate S (σ.val ∘ face j)) =
        ∑ i : Fin (q+2), (-1 : ℝ)^i.val • generate S ((σ.val ∘ face j) ∘ face i) :=
    fun j => boundary_generate S (smooth_face σ.property j)
  simp_rw [he, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]
  apply alternating_double_sum q
  intro i j hij
  congr 1
  rw [Function.comp_assoc, face_comp_face i j hij, ← Function.comp_assoc]

@[simp] theorem coboundary_apply (q : ℕ) (c : Cochains S q) (z : Chains S (q+1)) :
    coboundary S q c z = c (boundary S q z) := rfl

theorem coboundary_squared (q : ℕ) :
    (coboundary S (q+1)).comp (coboundary S q) = 0 := by
  apply LinearMap.ext
  intro c
  apply LinearMap.ext
  intro z
  change c (boundary S q (boundary S (q+1) z)) = 0
  have hz := LinearMap.congr_fun (boundary_squared S q) z
  change boundary S q (boundary S (q+1) z) = 0 at hz
  rw [hz, map_zero]

theorem coboundaries_are_cocycles (q : ℕ) :
    LinearMap.range (previousCoboundary S q) ≤ cocycles S q := by
  cases q with
  | zero =>
    rintro c ⟨x,rfl⟩
    exact (cocycles S 0).zero_mem
  | succ q =>
    rintro c ⟨x,rfl⟩
    exact LinearMap.congr_fun (coboundary_squared S q) x

theorem cohomology_zero_incoming :
    coboundaries S 0 = ⊥ := by
  ext c
  change (∃ x, (0 : Cochains S 0 →ₗ[ℝ] Cochains S 0) x = c.val) ↔ c = 0
  simp only [LinearMap.zero_apply, exists_const]
  exact ⟨fun h => Subtype.ext h.symm, fun h => by simp [h]⟩

end Complex

section Functoriality
variable {n m l : ℕ} {a b c : ModelKind} {M : Type u} {N : Type v} {P : Type w}
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
  (S : SmoothManifold n a M) (T : SmoothManifold m b N) (U : SmoothManifold l c P)

@[simp] theorem chainMap_single (f : M → N) (q : ℕ) (σ : SingularSimplex S q) (r : ℝ) :
    chainMap S T f q (Finsupp.single σ r) = r • generate T (f ∘ σ.val) :=
  by simp [chainMap, SmoothSingularData.chainMap]

@[simp] theorem chainMap_generate (f : M → N) {q : ℕ} {σ : Simplex q → M}
    (hσ : SimplexSmooth S σ) :
    chainMap S T f q (generate S σ) = generate T (f ∘ σ) := by
  rw [generate_smooth S hσ, chainMap_single, one_smul]

theorem chainMap_id (q : ℕ) : chainMap S S id q = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro σ r
  simp

theorem chainMap_comp {f : M → N} {g : N → P}
    (hf : IsSmoothMap S T f) (_hg : IsSmoothMap T U g) (q : ℕ) :
    chainMap S U (g ∘ f) q = (chainMap T U g q).comp (chainMap S T f q) := by
  apply Finsupp.lhom_ext
  intro σ r
  simp only [LinearMap.comp_apply, chainMap_single, map_smul]
  rw [chainMap_generate T U g (smooth_postcompose hf σ.property)]
  rfl

theorem chainMap_boundary {f : M → N} (hf : IsSmoothMap S T f) (q : ℕ) :
    (boundary T q).comp (chainMap S T f (q+1)) =
      (chainMap S T f q).comp (boundary S q) := by
  apply Finsupp.lhom_ext
  intro σ r
  simp only [LinearMap.comp_apply, chainMap_single, map_smul]
  rw [boundary_generate T (smooth_postcompose hf σ.property)]
  -- Expand the source boundary in its smooth generators.
  change r • _ = chainMap S T f q (boundary S q (Finsupp.single σ r))
  have hr : Finsupp.single σ r = r • generate S σ.val := by simp
  rw [hr, map_smul, boundary_generate S σ.property, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, chainMap_generate S T f (smooth_face σ.property j)]
  rfl

@[simp] theorem cochainMap_apply (f : M → N) (q : ℕ) (d : Cochains T q)
    (z : Chains S q) : cochainMap S T f q d z = d (chainMap S T f q z) := rfl

theorem cochainMap_id (q : ℕ) : cochainMap S S id q = LinearMap.id := by
  apply LinearMap.ext
  intro d
  apply LinearMap.ext
  intro z
  simp [cochainMap_apply, chainMap_id]

theorem cochainMap_comp {f : M → N} {g : N → P}
    (hf : IsSmoothMap S T f) (hg : IsSmoothMap T U g) (q : ℕ) :
    cochainMap S U (g ∘ f) q = (cochainMap S T f q).comp (cochainMap T U g q) := by
  apply LinearMap.ext
  intro d
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply, cochainMap_apply]
  rw [chainMap_comp S T U hf hg]
  rfl

theorem cochainMap_coboundary {f : M → N} (hf : IsSmoothMap S T f) (q : ℕ) :
    (coboundary S q).comp (cochainMap S T f q) =
      (cochainMap S T f (q+1)).comp (coboundary T q) := by
  apply LinearMap.ext
  intro d
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply, coboundary_apply, cochainMap_apply]
  exact congrArg d (LinearMap.congr_fun (chainMap_boundary S T hf q) z).symm

end Functoriality

section Endpoints
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : SmoothManifold n a M)

theorem boundary_interval (σ : SingularSimplex S 1) :
    boundary S 0 (Finsupp.single σ 1) =
      generate S (σ.val ∘ face (0 : Fin 2)) -
      generate S (σ.val ∘ face (1 : Fin 2)) := by
  change Finsupp.linearCombination ℝ _ (Finsupp.single σ 1) = _
  simp [Fin.sum_univ_succ, sub_eq_add_neg]

end Endpoints

abbrev vertex := @SmoothSingularData.vertex

@[simp] theorem vertex_barycentric {q : ℕ} (i : Fin (q+1)) :
    simplexBarycentric (vertex i).val = Pi.single i 1 := by
  change simplexBarycentric (Fin.tail (Pi.single i (1 : ℝ) : Euclidean (q+1))) = Pi.single i 1
  apply CornerExamples.barycentric_tail_of_sum
  simp [Pi.single_apply]

@[simp] theorem vertex_zero (q : ℕ) : (vertex (0 : Fin (q+1))).val = 0 := by
  funext i
  simp [vertex, SmoothSingularData.vertex, SmoothSingularData.fromBarycentric,
    Fin.tail, Pi.single_apply, Fin.succ_ne_zero]

@[simp] theorem vertex_succ {q : ℕ} (i : Fin q) : (vertex i.succ).val = Pi.single i 1 := by
  funext k
  simp [vertex, SmoothSingularData.vertex, SmoothSingularData.fromBarycentric,
    Fin.tail, Pi.single_apply]

theorem face_vertex {q : ℕ} (j : Fin (q+2)) (i : Fin (q+1)) :
    face j (vertex i) = vertex (j.succAbove i) := by
  apply Subtype.ext
  have h : simplexBarycentric (face j (vertex i)).val =
      simplexBarycentric (vertex (j.succAbove i)).val := by
    rw [face_barycentric, vertex_barycentric, vertex_barycentric]
    funext k
    refine Fin.succAboveCases j ?_ (fun r => ?_) k
    · simp [Pi.single_apply, Fin.succAbove_ne]
    · simp [Pi.single_apply, Fin.succAbove_right_inj]
  funext k
  exact congrFun h k.succ

/-- The shared simplex has the established affine corner charts and coordinate orientation. -/
theorem simplex_geometry :
    Specs.SmoothManifolds.Corners.FaceOrientations.simplex_source_orientationType :=
  CornerFaceOrientations.simplex_source_orientation

theorem simplex_zero : Nonempty (Simplex 0) ∧ Subsingleton (Simplex 0) := by
  refine ⟨⟨⟨0, by simp [simplexSet]⟩⟩, ?_⟩
  exact ⟨fun x y => Subtype.ext (Subsingleton.elim x.val y.val)⟩

/-- The ordered interval faces are the terminal and initial endpoints, respectively. -/
theorem face_endpoints (x : Simplex 0) :
    (face (0 : Fin 2) x).val 0 = 1 ∧ (face (1 : Fin 2) x).val 0 = 0 := by
  simp [face_val, faceAmbient, SmoothSingularData.faceAmbient,
    simplexBarycentric, Fin.tail]

/-- Affineness of the ambient face maps, expressed without a choice of base point. -/
theorem face_affine {q : ℕ} (j : Fin (q+2)) (r : ℝ) (x y : Euclidean q) :
    faceAmbient j (r • x + (1-r) • y) =
      r • faceAmbient j x + (1-r) • faceAmbient j y := by
  have hb : simplexBarycentric (r • x + (1-r) • y) =
      r • simplexBarycentric x + (1-r) • simplexBarycentric y := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp only [simplexBarycentric, Fin.cons_zero, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    · simp [simplexBarycentric]
  funext i
  change (j.insertNth 0 (simplexBarycentric (r • x + (1-r) • y)) : Euclidean (q+2)) i.succ =
    r * (j.insertNth 0 (simplexBarycentric x) : Euclidean (q+2)) i.succ +
      (1-r) * (j.insertNth 0 (simplexBarycentric y) : Euclidean (q+2)) i.succ
  rw [hb]
  generalize i.succ = k
  refine Fin.succAboveCases j ?_ (fun k => ?_) k
  · simp [SmoothSingularData.faceAmbient, Fin.tail]
  · simp [SmoothSingularData.faceAmbient, Fin.tail]


theorem ordered_faces :
    Specs.SmoothManifolds.Comparison.SmoothSingularComplex.ordered_facesType :=
  ⟨simplex_zero, vertex_zero, vertex_succ, face_vertex, face_affine, face_comp_face, face_endpoints⟩

theorem smooth_closure :
    Specs.SmoothManifolds.Comparison.SmoothSingularComplex.smooth_closureType := by
  intro n m q a b M N _ _ S T
  exact ⟨fun σ j => smooth_face σ.property j,
    fun _ hf σ => smooth_postcompose hf σ.property⟩

theorem complex_identities :
    Specs.SmoothManifolds.Comparison.SmoothSingularComplex.complex_identitiesType := by
  intro n a M _ S
  refine ⟨boundary_squared S, rfl, coboundary_squared S, coboundaries_are_cocycles S,
    cohomology_zero_incoming S, ?_, coboundary_apply S, boundary_interval S⟩
  intro q σ
  simpa only [generate_simplex] using boundary_generate S σ.property

theorem naturality :
    Specs.SmoothManifolds.Comparison.SmoothSingularComplex.naturalityType := by
  intro n m l a b c M N P _ _ _ S T U
  refine ⟨chainMap_id S, cochainMap_id S, ?_, ?_, ?_⟩
  · intro f g hf hg q
    exact ⟨chainMap_comp S T U hf hg q, cochainMap_comp S T U hf hg q⟩
  · intro f hf q
    exact ⟨chainMap_boundary S T hf q, cochainMap_coboundary S T hf q⟩
  · intro f hf q σ
    simp

/-- The defining universal property of the real free vector space. -/
theorem free_chains {n q : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) {V : Type v} [AddCommGroup V] [Module ℝ V]
    (F : SingularSimplex S q → V) :
    ∃! L : Chains S q →ₗ[ℝ] V, ∀ σ, L (Finsupp.single σ 1) = F σ := by
  refine ⟨Finsupp.linearCombination ℝ F, ?_, ?_⟩
  · intro σ
    simp
  · intro L hL
    apply Finsupp.lhom_ext
    intro σ r
    have hr : Finsupp.single σ r = r • Finsupp.single σ 1 := by simp
    rw [hr, map_smul, map_smul, hL]
    simp

theorem local_extension_iff {q m : ℕ} (f : Simplex q → Euclidean m) (x : Simplex q) :
    MapData.LocalCoordinateExtension (⊤ : ℕ∞) Subtype.val f x ↔
      ModelData.HasLocalContDiffExtensionAt (⊤ : ℕ∞) Subtype.val f x := by
  constructor
  · rintro ⟨U,hU,hxU,F,hF,he⟩
    obtain ⟨V,hV,hsub⟩ :=
      (mem_nhds_subtype (simplexSet q) x {y | F y.val = f y}).mp he
    obtain ⟨W,hWV,hWo,hxW⟩ := mem_nhds_iff.mp hV
    refine ⟨U ∩ W, hU.inter hWo, ⟨hxU,hxW⟩, F, hF.mono inter_subset_left, ?_⟩
    intro y hy
    exact hsub (hWV hy.2)
  · rintro ⟨U,hU,hxU,F,hF,he⟩
    refine ⟨U,hU,hxU,F,hF, ?_⟩
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
      (hU.mem_nhds hxU)] with y hy
    exact he y hy

theorem extension_convention {n q : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (f : Simplex q → M) :
    SimplexSmooth S f ↔ Continuous f ∧
      ∀ x, ∀ d ∈ S.smoothStructure.val, f x ∈ d.source →
        ModelData.HasLocalContDiffExtensionAt (⊤ : ℕ∞) Subtype.val
          (fun y => (d (f y)).val) x := by
  unfold SimplexSmooth SmoothSingularData.SimplexSmooth
  simp only [local_extension_iff]


end SmoothManifolds.SmoothSingular
