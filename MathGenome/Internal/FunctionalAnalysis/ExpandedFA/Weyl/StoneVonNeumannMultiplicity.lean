import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Weyl.StoneVonNeumannMultiplicity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Weyl.SchrodingerGaussianCorner
import Mathlib.LinearAlgebra.Isomorphisms

noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory
open scoped TensorProduct
universe u v
namespace ExpandedFA.Weyl
open RegularWeylRepresentationSpec GaussianCornerSpec SchrodingerGaussianCornerSpec
open StoneVonNeumannMultiplicitySpec

section Rescaling

lemma momentumRescale_add {d : ℕ} (c : ℝ) (z w : PhaseSpace d) :
    momentumRescale c (z + w) = momentumRescale c z + momentumRescale c w := by
  ext <;> simp [momentumRescale, smul_add]

lemma symplectic_momentumRescale {d : ℕ} (c : ℝ) (z w : PhaseSpace d) :
    SymplecticFormValue (momentumRescale c z) (momentumRescale c w) =
      c * SymplecticFormValue z w := by
  simp only [SymplecticFormValue, momentumRescale, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem central_rescaling : CentralRescaling.{u} := by
  intro d H _ _ _ c hc R
  let S : RegularRepresentation d H := {
    dimension_pos := R.dimension_pos
    nontrivial_space := R.nontrivial_space
    W := fun z => R.W (momentumRescale c⁻¹ z)
    zero := by
      intro x
      have hz : momentumRescale (d := d) c⁻¹ 0 = 0 := by
        ext <;> simp [momentumRescale]
      rw [hz, R.zero]
    mul := by
      intro z w x
      rw [R.mul, ← momentumRescale_add, symplectic_momentumRescale]
      congr 2
      push_cast
      congr 2
      field_simp [hc]
    strong_continuous := fun x => (R.strong_continuous x).comp (by
      unfold momentumRescale
      fun_prop) }
  refine ⟨S, fun _ _ => rfl, ?_⟩
  intro z x
  change R.W z x = R.W (momentumRescale c⁻¹ (momentumRescale c z)) x
  congr 2
  ext <;> simp [momentumRescale, smul_smul, hc]

end Rescaling

/-- A closed invariant subspace is preserved by the strong Gaussian average. -/
lemma gaussianProjection_mem {d : ℕ} {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (R : RegularRepresentation d H)
    (K : Submodule ℂ H) (hK : IsClosed (K : Set H))
    (hInv : ∀ z x, x ∈ K → R.W z x ∈ K) {x : H} (hx : x ∈ K) :
    gaussianProjection R x ∈ K := by
  have hclosure : K.topologicalClosure = K := hK.submodule_topologicalClosure_eq
  rw [← hclosure, ← K.orthogonal_orthogonal_eq_closure]
  apply (Kᗮ.mem_orthogonal _).mpr
  intro y hy
  rw [gaussianProjection_apply, gaussianVectorIntegral]
  erw [inner_smul_right_eq_smul (𝕜 := ℂ) y _ (gaussianNormalization d)]
  rw [← integral_inner (gaussianOrbit_integrable R x)]
  have hi : ∀ z : PhaseSpace d, inner ℂ y (gaussianWeight z • R.W z x) = 0 := by
    intro z
    erw [inner_smul_right_eq_smul (𝕜 := ℂ) y _ (gaussianWeight z)]
    rw [K.inner_left_of_mem_orthogonal (hInv z x hx) hy, smul_zero]
  simp only [hi, integral_zero, smul_zero]

theorem schrodinger_irreducible : SchrodingerIrreducible := by
  intro d hd K hK hInv
  obtain ⟨R, hR⟩ := schrodinger_regular d hd
  have hInvR : ∀ z x, x ∈ K → R.W z x ∈ K := by simpa only [hR] using hInv
  by_cases hh : vacuum d ∈ K
  · right
    have hle : (Submodule.span ℂ (Set.range (fun z : PhaseSpace d =>
        SchrodingerActionValue z (vacuum d)))).topologicalClosure ≤ K := by
      apply Submodule.topologicalClosure_minimal _ _ hK
      apply Submodule.span_le.mpr
      rintro _ ⟨z, rfl⟩
      exact hInv z _ hh
    rw [vacuum_orbit_dense d hd] at hle
    exact top_unique hle
  · left
    apply (Submodule.eq_bot_iff _).mpr
    intro f hf
    apply vacuum_modulations_total
    intro p
    have hcoef (z : PhaseSpace d) : inner ℂ (vacuum d) (R.W z f) = 0 := by
      have hmem := gaussianProjection_mem R K hK hInvR (hInvR z f hf)
      rw [gaussianProjection_apply, concrete_gaussian_projection d hd R hR] at hmem
      by_contra hn
      exact hh ((K.smul_mem_iff hn).mp hmem)
    have hi := hcoef (-(0, p) : PhaseSpace d)
    rw [← weyl_inner_inverse R (0, p), hR] at hi
    exact inner_eq_zero_symm.mp hi

section GramExtension
variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {ι : Type*}

/-- Matching Gram matrices determine a unitary between complete spaces when
both families have dense linear span. -/
theorem unitary_of_dense_gram (a : ι → E) (b : ι → F)
    (ha : (Submodule.span ℂ (Set.range a)).topologicalClosure = ⊤)
    (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)
    (hab : ∀ i j, inner ℂ (b i) (b j) = inner ℂ (a i) (a j)) :
    ∃ U : E ≃ₗᵢ[ℂ] F, ∀ i, U (a i) = b i := by
  classical
  let A := Finsupp.linearCombination ℂ a
  let B := Finsupp.linearCombination ℂ b
  have hip (s t : ι →₀ ℂ) : inner ℂ (B s) (B t) = inner ℂ (A s) (A t) := by
    simp only [A, B, Finsupp.linearCombination_apply, Finsupp.sum,
      inner_sum, sum_inner, inner_smul_left, inner_smul_right, hab]
  have hker : A.ker ≤ B.ker := by
    intro s hs
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [hip, LinearMap.mem_ker.mp hs, inner_zero_left]
  let C : A.range →ₗ[ℂ] F := A.rangeRestrict.liftOfSurjective
    A.surjective_rangeRestrict ⟨B, by simpa only [LinearMap.ker_rangeRestrict] using hker⟩
  have hC (s : ι →₀ ℂ) : C (A.rangeRestrict s) = B s :=
    LinearMap.equivOfSurjective_apply A.surjective_rangeRestrict _
  have hinner (x y : A.range) : inner ℂ (C x) (C y) = inner ℂ x y := by
    obtain ⟨s, rfl⟩ := A.surjective_rangeRestrict x
    obtain ⟨t, rfl⟩ := A.surjective_rangeRestrict y
    rw [hC, hC, hip]
    rfl
  let L := C.isometryOfInner hinner
  have hd : DenseRange (A.range.subtypeL : A.range →L[ℂ] E) := by
    change DenseRange (Subtype.val : A.range → E)
    rw [denseRange_subtype_val]
    change Dense (A.range : Set E)
    apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
    simpa only [A, Finsupp.range_linearCombination] using ha
  let T := L.toContinuousLinearMap.extend A.range.subtypeL
  have hT (x : A.range) : T x = L x :=
    ContinuousLinearMap.extend_eq _ hd A.range.subtypeₗᵢ.isometry.isUniformInducing x
  have hnorm : ∀ x : E, ‖T x‖ = ‖x‖ := by
    intro x
    refine hd.induction_on x (p := fun x => ‖T x‖ = ‖x‖)
      (isClosed_eq (T.continuous.norm) continuous_norm) ?_
    intro x
    change ‖T (x : E)‖ = ‖(x : E)‖
    rw [hT, L.norm_map]
    rfl
  let I : E →ₗᵢ[ℂ] F := { T.toLinearMap with norm_map' := hnorm }
  have hI (i : ι) : I (a i) = b i := by
    have h := hT (A.rangeRestrict (Finsupp.single i 1))
    change T (A (Finsupp.single i 1)) = C (A.rangeRestrict (Finsupp.single i 1)) at h
    rw [hC] at h
    simpa [I, A, B, Finsupp.linearCombination_single] using h
  have hrange : I.toLinearMap.range = ⊤ := by
    have hc : IsClosed (I.toLinearMap.range : Set F) := I.isometry.isClosedEmbedding.isClosed_range
    have hle : (Submodule.span ℂ (Set.range b)).topologicalClosure ≤ I.toLinearMap.range := by
      apply Submodule.topologicalClosure_minimal _ _ hc
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact ⟨a i, hI i⟩
    rw [hb] at hle
    exact top_unique hle
  exact ⟨LinearIsometryEquiv.ofSurjective I (LinearMap.range_eq_top.mp hrange), hI⟩

end GramExtension

section MultiplicityCorner
variable {d : ℕ} {H : Type u} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The multiplicity space is the closed fixed space of the Gaussian projection. -/
def multiplicitySpace (R : RegularRepresentation d H) : Submodule ℂ H :=
  (gaussianProjection R - ContinuousLinearMap.id ℂ H).ker

instance multiplicitySpace_complete (R : RegularRepresentation d H) :
    CompleteSpace (multiplicitySpace R) :=
  ContinuousLinearMap.completeSpace_ker _

lemma mem_multiplicitySpace (R : RegularRepresentation d H) (x : H) :
    x ∈ multiplicitySpace R ↔ gaussianProjection R x = x := by
  simp [multiplicitySpace, sub_eq_zero]

lemma projection_mem_multiplicitySpace (R : RegularRepresentation d H) (x : H) :
    gaussianProjection R x ∈ multiplicitySpace R := by
  apply (mem_multiplicitySpace R _).mpr
  exact congrArg (fun T : H →L[ℂ] H => T x) (gaussianProjection_idempotent R)

instance multiplicitySpace_nontrivial (R : RegularRepresentation d H) :
    Nontrivial (multiplicitySpace R) := by
  have hex : ∃ x, gaussianProjection R x ≠ 0 := by
    by_contra h
    push Not at h
    exact gaussianProjection_ne_zero R (ContinuousLinearMap.ext h)
  obtain ⟨x, hx⟩ := hex
  exact nontrivial_of_ne (⟨gaussianProjection R x, projection_mem_multiplicitySpace R x⟩ :
    multiplicitySpace R) 0 (fun h => hx (congrArg Subtype.val h))

lemma corner_inner (R : RegularRepresentation d H) (z : PhaseSpace d)
    (ξ η : multiplicitySpace R) :
    inner ℂ (ξ : H) (R.W z η) = (gaussianWeight z : ℂ) * inner ℂ (ξ : H) (η : H) := by
  have hξ := (mem_multiplicitySpace R _).mp ξ.property
  have hη := (mem_multiplicitySpace R _).mp η.property
  have hc := congrArg (fun T : H →L[ℂ] H => T (η : H)) (gaussianProjection_sandwich R z)
  change gaussianProjection R (R.W z (gaussianProjection R η)) =
    (gaussianWeight z : ℂ) • gaussianProjection R η at hc
  rw [hη] at hc
  calc
    _ = inner ℂ (gaussianProjection R ξ) (R.W z η) := by rw [hξ]
    _ = inner ℂ (ξ : H) (gaussianProjection R (R.W z η)) := gaussianIntegral_symmetric R _ _
    _ = _ := by rw [hc, inner_smul_right]

lemma corner_orbit_gram (R : RegularRepresentation d H) (z w : PhaseSpace d)
    (ξ η : multiplicitySpace R) :
    inner ℂ (R.W z ξ) (R.W w η) =
      inner ℂ (SchrodingerActionValue z (vacuum d))
        (SchrodingerActionValue w (vacuum d)) * inner ℂ ξ η := by
  have hv (z w : PhaseSpace d) :
      inner ℂ (SchrodingerActionValue z (vacuum d))
        (SchrodingerActionValue w (vacuum d)) =
        WeylPhaseValue (-z) w * (gaussianWeight (-z + w) : ℂ) := by
    obtain ⟨S, hS⟩ := schrodinger_regular d R.dimension_pos
    rw [← hS, ← hS, weyl_inner_inverse, S.mul, inner_smul_right, hS,
      vacuum_coefficient_all]
  rw [hv, weyl_inner_inverse, R.mul, inner_smul_right, corner_inner]
  exact (mul_assoc _ _ _).symm

/-- Vanishing of all translated Gaussian averages forces the vector to vanish.
This is Fourier uniqueness applied to a scalar matrix coefficient, with no
separability condition on the ambient Hilbert space. -/
lemma gaussian_translates_total (R : RegularRepresentation d H) (x : H)
    (hx : ∀ w, gaussianProjection R (R.W w x) = 0) : x = 0 := by
  have hA (w : PhaseSpace d) :
      (∫ z : PhaseSpace d, gaussianWeight z • R.W z (R.W w x)) = 0 := by
    have h := hx w
    change gaussianNormalization d • (∫ z : PhaseSpace d,
      gaussianWeight z • R.W z (R.W w x)) = 0 at h
    exact (smul_eq_zero.mp h).resolve_left (ne_of_gt (gaussianNormalization_pos d))
  let f : PhaseSpace d → ℂ := fun z => inner ℂ x (gaussianWeight z • R.W z x)
  have hf : Integrable f := (gaussianOrbit_integrable R x).const_inner x
  have hc : Continuous f := continuous_const.inner (gaussianOrbit_continuous R x)
  have hz (w : PhaseSpace d) :
      (∫ z, Complex.exp ((SymplecticFormValue w z : ℝ) * Complex.I) * f z) = 0 := by
    let L := (R.W w).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
    have hv : (∫ z : PhaseSpace d,
        L (gaussianWeight z • R.W z (R.W (-w) x))) = 0 := by
      rw [L.integral_comp_comm (gaussianOrbit_integrable R (R.W (-w) x)), hA, map_zero]
    calc
      _ = ∫ z : PhaseSpace d, inner ℂ x
          (L (gaussianWeight z • R.W z (R.W (-w) x))) := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [L.map_smul]
        change _ = inner ℂ x (gaussianWeight z • R.W w (R.W z (R.W (-w) x)))
        rw [weyl_conjugation]
        simp only [f, inner_smul_right_eq_smul, RCLike.real_smul_eq_coe_mul, smul_eq_mul]
        ring
      _ = inner ℂ x (∫ z : PhaseSpace d,
          L (gaussianWeight z • R.W z (R.W (-w) x))) :=
        integral_inner (L.integrable_comp (gaussianOrbit_integrable R (R.W (-w) x))) x
      _ = 0 := by rw [hv, inner_zero_right]
  have h0 := symplectic_continuous_uniqueness f hf hc hz 0
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  simpa only [f, gaussianWeight_zero, R.zero, one_smul] using h0

lemma multiplicity_orbit_dense (R : RegularRepresentation d H) :
    (Submodule.span ℂ (Set.range (fun i : PhaseSpace d × multiplicitySpace R =>
      R.W i.1 i.2))).topologicalClosure = ⊤ := by
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  apply gaussian_translates_total R x
  intro w
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  let y := gaussianProjection R (R.W w x)
  have hy : y ∈ multiplicitySpace R := projection_mem_multiplicitySpace R _
  have ho := (Submodule.mem_orthogonal _ _).mp hx _
    (Submodule.le_topologicalClosure _ (Submodule.subset_span
      ⟨(-w, ⟨y, hy⟩), rfl⟩))
  change inner ℂ (R.W (-w) y) x = 0 at ho
  rw [weyl_inner_inverse] at ho
  simp only [neg_neg] at ho
  calc
    inner ℂ y y = inner ℂ (gaussianProjection R y) (R.W w x) := by
      exact (gaussianIntegral_symmetric R y (R.W w x)).symm
    _ = 0 := by rw [(mem_multiplicitySpace R _).mp hy]; exact ho

end MultiplicityCorner

section TensorDensity
variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] {ι : Type*}

lemma elementaryTensor_add_left (x y : E) (ξ : F) :
    elementaryTensor (x + y) ξ = elementaryTensor x ξ + elementaryTensor y ξ := by
  simp only [elementaryTensor, TensorProduct.add_tmul, UniformSpace.Completion.coe_add]

lemma elementaryTensor_smul_left (c : ℂ) (x : E) (ξ : F) :
    elementaryTensor (c • x) ξ = c • elementaryTensor x ξ := by
  exact (UniformSpace.Completion.toComplL : (E ⊗[ℂ] F) →L[ℂ]
    UniformSpace.Completion (E ⊗[ℂ] F)).map_smul c (x ⊗ₜ[ℂ] ξ)

/-- Tensoring a total family with every vector of the other factor stays total
in the completed Hilbert tensor product. -/
lemma tensor_family_dense (a : ι → E)
    (ha : (Submodule.span ℂ (Set.range a)).topologicalClosure = ⊤) :
    (Submodule.span ℂ (Set.range (fun i : ι × F =>
      elementaryTensor (a i.1) i.2))).topologicalClosure = ⊤ := by
  let Q := (Submodule.span ℂ (Set.range (fun i : ι × F =>
    elementaryTensor (a i.1) i.2))).topologicalClosure
  have hmem (f : E) (ξ : F) : elementaryTensor f ξ ∈ Q := by
    let T : E →L[ℂ] HilbertTensor E F :=
      UniformSpace.Completion.toComplL.comp ((TensorProduct.mkL ℂ E F).flip ξ)
    let K := Q.comap T.toLinearMap
    have hclosed : IsClosed (K : Set E) := (Submodule.isClosed_topologicalClosure _).preimage T.continuous
    have hle : (Submodule.span ℂ (Set.range a)).topologicalClosure ≤ K := by
      apply Submodule.topologicalClosure_minimal _ _ hclosed
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(i, ξ), rfl⟩)
    rw [ha] at hle
    exact hle (Submodule.mem_top : f ∈ (⊤ : Submodule ℂ E))
  apply Submodule.eq_top_iff'.mpr
  intro x
  change x ∈ Q
  refine UniformSpace.Completion.induction_on x
    (p := fun x => x ∈ Q) (Submodule.isClosed_topologicalClosure _) ?_
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul f ξ => exact hmem f ξ
  | add x y hx hy => simpa only [UniformSpace.Completion.coe_add] using Q.add_mem hx hy

end TensorDensity

/-- The completed tensor action is obtained from the actual Schrödinger unitary. -/
def amplifiedSchrodinger {d : ℕ} (M : Type u) [NormedAddCommGroup M]
    [InnerProductSpace ℂ M] (z : PhaseSpace d) :
    HilbertTensor (SchrodingerSpace d) M →L[ℂ] HilbertTensor (SchrodingerSpace d) M :=
  (TensorProduct.mapL (schrodingerLinearIsometryEquiv z).toContinuousLinearEquiv.toContinuousLinearMap
    (ContinuousLinearMap.id ℂ M)).completion

lemma amplifiedSchrodinger_elementary {d : ℕ} {M : Type u} [NormedAddCommGroup M]
    [InnerProductSpace ℂ M] (z : PhaseSpace d) (f : SchrodingerSpace d) (ξ : M) :
    amplifiedSchrodinger M z (elementaryTensor f ξ) =
      elementaryTensor (SchrodingerActionValue z f) ξ := by
  simp [amplifiedSchrodinger, elementaryTensor, schrodingerLinearIsometryEquiv]

set_option maxHeartbeats 400000 in
theorem stone_von_neumann_multiplicity : Multiplicity.{u} := by
  intro d H _ _ _ R
  let M := multiplicitySpace R
  let a : PhaseSpace d × M → HilbertTensor (SchrodingerSpace d) M :=
    fun i => elementaryTensor (SchrodingerActionValue i.1 (vacuum d)) i.2
  let b : PhaseSpace d × M → H := fun i => R.W i.1 i.2
  have ha : (Submodule.span ℂ (Set.range a)).topologicalClosure = ⊤ := by
    exact tensor_family_dense (F := M) (fun z : PhaseSpace d =>
      SchrodingerActionValue z (vacuum d)) (vacuum_orbit_dense d R.dimension_pos)
  obtain ⟨V, hV⟩ := unitary_of_dense_gram a b ha (multiplicity_orbit_dense R) (by
    rintro ⟨z, ξ⟩ ⟨w, η⟩
    simpa only [a, b, elementaryTensor, UniformSpace.Completion.inner_coe,
      TensorProduct.inner_tmul] using corner_orbit_gram R z w ξ η)
  have hinter (w : PhaseSpace d) (t : HilbertTensor (SchrodingerSpace d) M) :
      V (amplifiedSchrodinger M w t) = R.W w (V t) := by
    let L := V.toContinuousLinearEquiv.toContinuousLinearMap
    let B := (R.W w).toContinuousLinearEquiv.toContinuousLinearMap
    have heq : L.comp (amplifiedSchrodinger M w) = B.comp L := by
      apply ContinuousLinearMap.ext_on
        (Submodule.dense_iff_topologicalClosure_eq_top.mpr ha)
      rintro _ ⟨⟨z, ξ⟩, rfl⟩
      change V (amplifiedSchrodinger M w (a (z, ξ))) = R.W w (V (a (z, ξ)))
      rw [hV]
      change V (amplifiedSchrodinger M w
        (elementaryTensor (SchrodingerActionValue z (vacuum d)) ξ)) = R.W w (R.W z ξ)
      rw [amplifiedSchrodinger_elementary, schrodinger_weyl, elementaryTensor_smul_left,
        V.map_smul, R.mul]
      congr 1
      exact hV (w + z, ξ)
    exact congrArg (fun T : HilbertTensor (SchrodingerSpace d) M →L[ℂ] H => T t) heq
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, V.symm, ?_⟩
  intro z f ξ
  apply V.injective
  simp only [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.symm_symm]
  rw [← hinter, amplifiedSchrodinger_elementary]

section IrreducibleMultiplicity
variable {d : ℕ} {H : Type u} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : Type v} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
  [CompleteSpace M] [Nontrivial M]

lemma exists_unit_vector : ∃ ξ : M, ‖ξ‖ = 1 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  refine ⟨(‖x‖⁻¹ : ℂ) • x, ?_⟩
  simp [norm_smul, norm_inv, norm_ne_zero_iff.mpr hx]

/-- The isometric copy of E obtained by tensoring with a unit vector. -/
def tensorEmbedding (ξ : M) (hξ : ‖ξ‖ = 1) :
    SchrodingerSpace d →ₗᵢ[ℂ] HilbertTensor (SchrodingerSpace d) M where
  toFun f := elementaryTensor f ξ
  map_add' f g := elementaryTensor_add_left f g ξ
  map_smul' c f := elementaryTensor_smul_left c f ξ
  norm_map' f := by
    change ‖elementaryTensor f ξ‖ = ‖f‖
    simp only [elementaryTensor, UniformSpace.Completion.norm_coe, TensorProduct.norm_tmul,
      hξ, mul_one]

lemma tensorEmbedding_surjective_of_irreducible (R : RegularRepresentation d H)
    (U : H ≃ₗᵢ[ℂ] HilbertTensor (SchrodingerSpace d) M)
    (hU : Intertwines R M U) (hirr : IsIrreducible (fun z x => R.W z x))
    (ξ : M) (hξ : ‖ξ‖ = 1) : Function.Surjective (tensorEmbedding (d := d) ξ hξ) := by
  let J := U.symm.toLinearIsometry.comp (tensorEmbedding (d := d) ξ hξ)
  have hinter (z : PhaseSpace d) (f : SchrodingerSpace d) :
      R.W z (J f) = J (SchrodingerActionValue z f) := by
    apply U.injective
    exact (hU z f ξ).trans (by simp [J, tensorEmbedding])
  have hclosed : IsClosed (J.toLinearMap.range : Set H) := J.isometry.isClosedEmbedding.isClosed_range
  have hInv : ∀ z x, x ∈ J.toLinearMap.range → R.W z x ∈ J.toLinearMap.range := by
    rintro z _ ⟨f, rfl⟩
    exact ⟨SchrodingerActionValue z f, (hinter z f).symm⟩
  have htop : J.toLinearMap.range = ⊤ := by
    rcases hirr _ hclosed hInv with hbot | htop
    · have hmem : J (vacuum d) ∈ J.toLinearMap.range := ⟨vacuum d, rfl⟩
      rw [hbot, Submodule.mem_bot] at hmem
      have hn := J.norm_map (vacuum d)
      rw [hmem, norm_zero, vacuum_norm d R.dimension_pos] at hn
      exact False.elim (zero_ne_one hn)
    · exact htop
  intro t
  obtain ⟨f, hf⟩ := LinearMap.range_eq_top.mp htop (U.symm t)
  refine ⟨f, ?_⟩
  have h := congrArg U hf
  change U (U.symm (tensorEmbedding ξ hξ f)) = U (U.symm t) at h
  simpa only [U.apply_symm_apply] using h

lemma multiplicity_one_of_tensorEmbedding_surjective (ξ : M) (hξ : ‖ξ‖ = 1)
    (hd : 0 < d) (hs : Function.Surjective (tensorEmbedding (d := d) ξ hξ)) :
    Module.finrank ℂ M = 1 ∧ Nonempty (M ≃ₗᵢ[ℂ] ℂ) := by
  have hhh : inner ℂ (vacuum d) (vacuum d) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, vacuum_norm d hd]
    norm_num
  have hspan : ∀ η : M, ∃ c : ℂ, c • ξ = η := by
    intro η
    obtain ⟨f, hf⟩ := hs (elementaryTensor (vacuum d) η)
    refine ⟨inner ℂ (vacuum d) f, ?_⟩
    apply ext_inner_left ℂ
    intro a
    have h := congrArg (inner ℂ (elementaryTensor (vacuum d) a)) hf
    change inner ℂ (elementaryTensor (vacuum d) a) (elementaryTensor f ξ) =
      inner ℂ (elementaryTensor (vacuum d) a) (elementaryTensor (vacuum d) η) at h
    simp only [elementaryTensor, UniformSpace.Completion.inner_coe, TensorProduct.inner_tmul,
      hhh, one_mul] at h
    simpa only [inner_smul_right, mul_comm] using h
  have hne : ξ ≠ 0 := by intro hz; simp [hz] at hξ
  let I : ℂ →ₗᵢ[ℂ] M := {
    toFun := fun c => c • ξ
    map_add' := fun c e => add_smul c e ξ
    map_smul' := fun c e => mul_smul c e ξ
    norm_map' := fun c => by
      change ‖c • ξ‖ = ‖c‖
      simp only [norm_smul, hξ, mul_one] }
  have hsurj : Function.Surjective I := hspan
  exact ⟨finrank_eq_one ξ hne hspan,
    ⟨(LinearIsometryEquiv.ofSurjective I hsurj).symm⟩⟩

theorem irreducible_multiplicity : IrreducibleMultiplicity.{u,v} := by
  intro d H _ _ _ R M _ _ _ _ U hU hirr
  obtain ⟨ξ, hξ⟩ := exists_unit_vector (M := M)
  exact multiplicity_one_of_tensorEmbedding_surjective ξ hξ R.dimension_pos
    (tensorEmbedding_surjective_of_irreducible R U hU hirr ξ hξ)

end IrreducibleMultiplicity

theorem irreducible_uniqueness : IrreducibleUniqueness.{u} := by
  intro d H _ _ _ R hirr
  obtain ⟨M, hM, iM, cM, nM, U, hU⟩ := stone_von_neumann_multiplicity R
  obtain ⟨ξ, hξ⟩ := exists_unit_vector (M := M)
  let V : SchrodingerSpace d ≃ₗᵢ[ℂ] HilbertTensor (SchrodingerSpace d) M :=
    LinearIsometryEquiv.ofSurjective (tensorEmbedding ξ hξ)
      (tensorEmbedding_surjective_of_irreducible R U hU hirr ξ hξ)
  let T := U.trans V.symm
  refine ⟨T, ?_⟩
  intro z x
  apply V.injective
  have hx : U x = elementaryTensor (T x) ξ := by
    change U x = V (V.symm (U x))
    exact (V.apply_symm_apply _).symm
  have hx' : x = U.symm (elementaryTensor (T x) ξ) := by
    rw [← hx, U.symm_apply_apply]
  change V (V.symm (U (R.W z x))) = V (SchrodingerActionValue z (T x))
  rw [V.apply_symm_apply]
  conv_lhs => rw [hx']
  exact hU z (T x) ξ

end ExpandedFA.Weyl
