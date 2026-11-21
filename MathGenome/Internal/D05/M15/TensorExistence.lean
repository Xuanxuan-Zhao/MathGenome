import MathGenome.Internal.D05.M15.TensorUniversal
import MathGenome.Internal.D05.Foundations.FreeVectors
import MathGenome.Internal.D05.M06.QuotientLift
import MathGenome.Internal.Specs.D05.M15.TensorExistence

/-! The free-vector quotient construction of tensor products, with no choice of
bases or finite-dimensionality. See paper.tex:2714–2719. -/
namespace D05.M15.TensorExistence

universe u
noncomputable section
open Specs.D05.M15.TensorExistence
open Specs.D05.M15.TensorUniversal (IsTensorProduct IsMultitensorProduct)

/-- Equality on the images of free generators determines a map out of a quotient. -/
theorem quotient_generator_ext {K S H : Type u} [Field K]
    [AddCommGroup H] [Module K H] (R : Submodule K (S →₀ K))
    (f g : ((S →₀ K) ⧸ R) →ₗ[K] H)
    (h : ∀ s, f (R.mkQ (Finsupp.single s 1)) = g (R.mkQ (Finsupp.single s 1))) :
    f = g := by
  obtain ⟨l, _, hl⟩ := D05.Foundations.FreeVectors.unique_linear_extension (K := K)
    (fun s => g (R.mkQ (Finsupp.single s 1)))
  have hc : f.comp R.mkQ = g.comp R.mkQ :=
    (hl (f.comp R.mkQ) h).trans (hl (g.comp R.mkQ) (fun _ => rfl)).symm
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := R.mkQ_surjective z
  exact LinearMap.congr_fun hc x

/-- Free extension followed by quotient descent; both values and the full
factorization equality are recorded. -/
theorem descend_free_extension {K S H : Type u} [Field K]
    [AddCommGroup H] [Module K H] (R : Submodule K (S →₀ K)) (b : S → H)
    (hb : R ≤ LinearMap.ker (Finsupp.linearCombination K b)) :
    ∃! l : ((S →₀ K) ⧸ R) →ₗ[K] H,
      (∀ s, l (R.mkQ (Finsupp.single s 1)) = b s) ∧
        l.comp R.mkQ = Finsupp.linearCombination K b := by
  obtain ⟨l, hl, _⟩ := (D05.M06.QuotientLift.quotient_lift R
    (Finsupp.linearCombination K b)).mpr hb
  change Finsupp.linearCombination K b = l.comp R.mkQ at hl
  refine ⟨l, ⟨?_, hl.symm⟩, ?_⟩
  · intro s
    change (l.comp R.mkQ) (Finsupp.single s 1) = b s
    rw [← hl]
    exact D05.Foundations.FreeVectors.linearExtension_delta b s
  · intro g hg
    exact quotient_generator_ext R g l (fun s => (hg.1 s).trans (by
      change b s = (l.comp R.mkQ) (Finsupp.single s 1)
      rw [← hl]
      simp))

theorem binary_annihilation : Specs.D05.M15.TensorExistence.binary_annihilation := by
  intro K V W H _ _ _ _ _ _ _ b
  apply Submodule.span_le.mpr
  intro r hr
  change Finsupp.linearCombination K (fun p : V × W => b p.1 p.2) r = 0
  cases hr <;> simp [map_sub, map_smul, map_add, LinearMap.add_apply, LinearMap.smul_apply,
    Finsupp.linearCombination_single]

theorem binary_descent : Specs.D05.M15.TensorExistence.binary_descent := by
  intro K V W H _ _ _ _ _ _ _ b
  obtain ⟨l, hl, hu⟩ := descend_free_extension (binaryRelations K V W)
    (fun p : V × W => b p.1 p.2) (binary_annihilation b)
  refine ⟨l, ⟨fun v w => hl.1 (v, w), hl.2⟩, ?_⟩
  intro g hg
  exact hu g ⟨fun p => hg.1 p.1 p.2, hg.2⟩

section BinaryConstruction
variable {K V W : Type u} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- The generators of the relation span have zero quotient class. -/
theorem binary_relation_zero (r : (V × W) →₀ K) (hr : BinaryRelation K V W r) :
    (binaryRelations K V W).mkQ r = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span hr)

theorem elementary_add_left (v v' : V) (w : W) :
    elementary K V W (v + v') w = elementary K V W v w + elementary K V W v' w := by
  apply sub_eq_zero.mp
  simpa only [map_sub, map_add, sub_sub, elementary] using
    binary_relation_zero _ (BinaryRelation.add_left (K := K) v v' w)

theorem elementary_smul_left (a : K) (v : V) (w : W) :
    elementary K V W (a • v) w = a • elementary K V W v w := by
  apply sub_eq_zero.mp
  simpa only [map_sub, map_smul, elementary] using
    binary_relation_zero _ (BinaryRelation.smul_left (K := K) a v w)

theorem elementary_add_right (v : V) (w w' : W) :
    elementary K V W v (w + w') = elementary K V W v w + elementary K V W v w' := by
  apply sub_eq_zero.mp
  simpa only [map_sub, map_add, sub_sub, elementary] using
    binary_relation_zero _ (BinaryRelation.add_right (K := K) v w w')

theorem elementary_smul_right (a : K) (v : V) (w : W) :
    elementary K V W v (a • w) = a • elementary K V W v w := by
  apply sub_eq_zero.mp
  simpa only [map_sub, map_smul, elementary] using
    binary_relation_zero _ (BinaryRelation.smul_right (K := K) a v w)

/-- The elementary quotient classes, bundled as a bilinear map. -/
def quotientBilinear : V →ₗ[K] W →ₗ[K] BinaryQuotient K V W where
  toFun v :=
    { toFun := elementary K V W v
      map_add' := elementary_add_right v
      map_smul' := fun a w => elementary_smul_right a v w }
  map_add' v v' := by
    ext w
    exact elementary_add_left v v' w
  map_smul' a v := by
    ext w
    exact elementary_smul_left a v w
end BinaryConstruction

theorem binary_existence : Specs.D05.M15.TensorExistence.binary_existence := by
  intro K V W _ _ _ _ _
  refine ⟨quotientBilinear, (fun _ _ => rfl), ?_⟩
  intro H _ _ b
  obtain ⟨l, hl, _⟩ := binary_descent b
  refine ⟨l, hl.1, ?_⟩
  intro g hg
  apply quotient_generator_ext (binaryRelations K V W)
  intro p
  exact (hg p.1 p.2).trans (hl.1 p.1 p.2).symm

theorem binary_span : Specs.D05.M15.TensorExistence.binary_span := by
  intro K V W _ _ _ _ _
  obtain ⟨τ, hτ, hu⟩ := binary_existence (K := K) (V := V) (W := W)
  simpa only [hτ] using D05.M15.TensorUniversal.elementary_span_of_universal τ hu

theorem binary_unique_equivalence :
    Specs.D05.M15.TensorExistence.binary_unique_equivalence := by
  intro K V W U U' _ _ _ _ _ _ _ _ _ τ σ hτ hσ
  obtain ⟨f, hf, hfu⟩ := hτ U' σ
  obtain ⟨g, hg, _⟩ := hσ U τ
  have hfg : f.comp g = LinearMap.id := by
    apply D05.M15.TensorUniversal.linear_ext_of_universal σ hσ
    intro v w
    change f (g (σ v w)) = σ v w
    rw [hg, hf]
  have hgf : g.comp f = LinearMap.id := by
    apply D05.M15.TensorUniversal.linear_ext_of_universal τ hτ
    intro v w
    change g (f (τ v w)) = τ v w
    rw [hf, hg]
  refine ⟨LinearEquiv.ofLinearMap f g hfg hgf, hf, ?_⟩
  intro E hE
  apply LinearEquiv.toLinearMap_injective
  exact hfu E.toLinearMap hE

theorem binary_canonical_equivalence :
    Specs.D05.M15.TensorExistence.binary_canonical_equivalence := by
  intro K V W _ _ _ _ _
  obtain ⟨τ, hτ, hu⟩ := binary_existence (K := K) (V := V) (W := W)
  simpa only [hτ, TensorProduct.mk_apply] using binary_unique_equivalence τ (TensorProduct.mk K V W) hu
    D05.M15.TensorUniversal.binary_universal

theorem finite_annihilation : Specs.D05.M15.TensorExistence.finite_annihilation := by
  intro K I H V _ _ _ _ _ _ b
  apply Submodule.span_le.mpr
  intro r hr
  change Finsupp.linearCombination K b r = 0
  cases hr with
  | add_slot m i x y =>
      simp [Finsupp.linearCombination_single, b.map_update_add]
  | smul_slot m i a x =>
      simp [Finsupp.linearCombination_single, b.map_update_smul]

theorem finite_descent : Specs.D05.M15.TensorExistence.finite_descent := by
  intro K I H V _ _ _ _ _ _ b
  exact descend_free_extension (slotRelations K I V) b (finite_annihilation b)

section FiniteConstruction
variable {K I : Type u} {V : I → Type u} [Field K]
  [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

theorem slot_relation_zero (r : (∀ i, V i) →₀ K) (hr : SlotRelation K I V r) :
    (slotRelations K I V).mkQ r = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span hr)

/-- Bundling the elementary class uses precisely the two relations in each slot. -/
def quotientMultilinear : MultilinearMap K V (FiniteQuotient K I V) where
  toFun := finiteElementary K I V
  map_update_add' m i x y := by
    apply sub_eq_zero.mp
    simpa only [map_sub, map_add, sub_sub, finiteElementary] using
      slot_relation_zero _ (SlotRelation.add_slot (K := K) m i x y)
  map_update_smul' m i a x := by
    apply sub_eq_zero.mp
    simpa only [map_sub, map_smul, finiteElementary] using
      slot_relation_zero _ (SlotRelation.smul_slot (K := K) m i a x)
end FiniteConstruction

theorem finite_existence : Specs.D05.M15.TensorExistence.finite_existence := by
  intro K I V _ _ _ _
  refine ⟨quotientMultilinear, (fun _ => rfl), ?_⟩
  intro H _ _ b
  obtain ⟨l, hl, _⟩ := finite_descent b
  refine ⟨l, hl.1, ?_⟩
  intro g hg
  apply quotient_generator_ext (slotRelations K I V)
  intro m
  exact (hg m).trans (hl.1 m).symm

theorem finite_span : Specs.D05.M15.TensorExistence.finite_span := by
  intro K I V _ _ _ _
  obtain ⟨τ, hτ, hu⟩ := finite_existence (K := K) (V := V)
  have ht : (τ : (∀ i, V i) → FiniteQuotient K I V) = finiteElementary K I V :=
    funext hτ
  simpa only [ht] using D05.M15.TensorUniversal.finite_span_of_universal τ hu

theorem finite_unique_equivalence :
    Specs.D05.M15.TensorExistence.finite_unique_equivalence := by
  intro K I U U' V _ _ _ _ _ _ _ _ τ σ hτ hσ
  obtain ⟨f, hf, hfu⟩ := hτ U' σ
  obtain ⟨g, hg, _⟩ := hσ U τ
  have hfg : f.comp g = LinearMap.id := by
    apply D05.M15.TensorUniversal.finite_ext_of_universal σ hσ
    intro m
    change f (g (σ m)) = σ m
    rw [hg, hf]
  have hgf : g.comp f = LinearMap.id := by
    apply D05.M15.TensorUniversal.finite_ext_of_universal τ hτ
    intro m
    change g (f (τ m)) = τ m
    rw [hf, hg]
  refine ⟨LinearEquiv.ofLinearMap f g hfg hgf, hf, ?_⟩
  intro E hE
  apply LinearEquiv.toLinearMap_injective
  exact hfu E.toLinearMap hE

theorem finite_canonical_equivalence :
    Specs.D05.M15.TensorExistence.finite_canonical_equivalence := by
  intro K I V _ _ _ _
  obtain ⟨τ, hτ, hu⟩ := finite_existence (K := K) (V := V)
  obtain ⟨E, hE, hEu⟩ := finite_unique_equivalence τ (PiTensorProduct.tprod K) hu
    D05.M15.TensorUniversal.finite_universal
  refine ⟨E, (fun m => by rw [← hτ]; exact hE m), ?_⟩
  intro E' hE'
  exact hEu E' (fun m => by rw [hτ]; exact hE' m)

theorem nullary_equivalence : Specs.D05.M15.TensorExistence.nullary_equivalence := by
  intro K I V _ _ _ _ _
  refine ⟨?_, ?_⟩
  · apply le_antisymm _ bot_le
    apply Submodule.span_le.mpr
    intro r hr
    cases hr with
    | add_slot m i x y => exact False.elim (IsEmpty.false i)
    | smul_slot m i a x => exact False.elim (IsEmpty.false i)
  · obtain ⟨E, hE, _⟩ := finite_canonical_equivalence (K := K) (V := V)
    obtain ⟨N, hN, _⟩ := D05.M15.TensorUniversal.nullary_equivalence
      (K := K) (V := V)
    refine ⟨E.trans N, ?_, ?_⟩
    · intro m
      change N (E (finiteElementary K I V m)) = 1
      rw [hE, hN]
    · intro E' hE'
      apply LinearEquiv.toLinearMap_injective
      apply quotient_generator_ext (slotRelations K I V)
      intro m
      change E' (finiteElementary K I V m) = N (E (finiteElementary K I V m))
      rw [hE', hE, hN]

end
end D05.M15.TensorExistence
