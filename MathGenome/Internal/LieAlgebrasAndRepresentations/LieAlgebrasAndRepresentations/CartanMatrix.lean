import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CartanMatrix
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleRoots
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.LinearAlgebra.Pi

/-! Cartan matrices, Dynkin reconstruction, and orthogonal Weyl factors (LA-E04).
Source: res:E04, notes/005/lie-algebras-and-representations.tex:2146–2168.

The Cartan matrix uses rows for coroots. Symmetrization is twice the Gram
matrix. Equal diagram data recover the Cartan entries; the resulting basis
map commutes with all simple reflections and therefore maps all roots.
Ratios of squared lengths propagate along graph edges, giving a positive
metric scale on each full component subspace. Component spans are invariant
under simple reflections. This identifies their root sets with the canonical
orthogonal factors. Finally, intrinsic factor reflections extend by the
identity on the other summands, giving the Weyl group product isomorphism.
No step requires a nonempty root system.
-/

noncomputable section
namespace LieAlgebrasAndRepresentations
open Set Module
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} {R : Set E} {v : E} {b : Basis ι ℝ E}

/-- Public Cartan matrix construction with the source's row convention. -/
abbrev simpleRootCartanMatrix : CartanMatrixSpecs.cartanMatrixType := @cartanMatrix

/-- Public Dynkin diagram with multiplicities and arrows to shorter roots. -/
abbrev simpleRootDynkinDiagram : CartanMatrixSpecs.dynkinDiagramType := @dynkinDiagram

lemma IsSimpleBasis.mem (hb : IsSimpleBasis R v b) (i : ι) : b i ∈ simpleRoots R v :=
  hb ▸ Set.mem_range_self i

lemma IsSimpleBasis.root_mem (hb : IsSimpleBasis R v b) (i : ι) : b i ∈ R :=
  (hb.mem i).1.1

lemma IsSimpleBasis.nonpos (hR : RootAxioms R) (hv : RootRegular R v)
    (hb : IsSimpleBasis R v b) {i j : ι} (hij : i ≠ j) : inner ℝ (b i) (b j) ≤ 0 :=
  simpleRoots_pairwise_nonpos hR hv (hb.mem i) (hb.mem j)
    (fun h => hij (b.injective h))

lemma basis_pair_independent (b : Basis ι ℝ E) {i j : ι} (hij : i ≠ j) :
    LinearIndependent ℝ ![b i, b j] := by
  have hinj : Function.Injective (fun k : Fin 2 => ![i,j] k) := by
    intro k l h
    fin_cases k <;> fin_cases l <;> simp_all
  convert b.linearIndependent.comp (fun k : Fin 2 => ![i,j] k) hinj using 1
  ext k
  fin_cases k <;> rfl

theorem cartan_diagonal : CartanMatrixSpecs.diagonalType := by
  intro E _ _ ι R hR v hv b hb i
  exact mul_div_cancel_right₀ 2 (inner_self_ne_zero (hR.nonzero _ (hb.root_mem i)))

theorem cartan_offDiagonal : CartanMatrixSpecs.offDiagonalType := by
  intro E _ _ ι R hR v hv b hb
  constructor
  · intro i j
    exact hR.integral (b i) (hb.root_mem i) (b j) (hb.root_mem j)
  · intro i j hij
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (hb.nonpos hR.toRootAxioms hv hij.symm))
      (real_inner_self_nonneg)

theorem cartan_product : CartanMatrixSpecs.productType := by
  intro E _ _ ι R hR v hv b hb i j hij
  have hp := cartan_product_values hR.toRootAxioms (hb.root_mem j) (hb.root_mem i)
    (basis_pair_independent b hij.symm)
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, cartanMatrix] using hp

theorem cartan_symmetrization : CartanMatrixSpecs.symmetrizationType := by
  intro E _ _ ι _ _ R hR v hv b hb
  have he : Matrix.diagonal (fun i => inner ℝ (b i) (b i)) * cartanMatrix b =
      (2 : ℝ) • Matrix.gram ℝ b := by
    ext i j
    simp only [Matrix.diagonal_mul, cartanMatrix, Matrix.smul_apply, Matrix.gram_apply,
      smul_eq_mul]
    rw [mul_comm, rootCartan_mul_self, real_inner_comm]
  refine ⟨he, ?_, ?_⟩
  · rw [he]
    ext i j
    simp [Matrix.transpose_apply, real_inner_comm]
  · rw [he]
    exact (Matrix.posDef_gram_of_linearIndependent b.linearIndependent).smul (by norm_num)

lemma dynkin_edges_cast (hR : IsRootSystem R) (hv : RootRegular R v)
    (hb : IsSimpleBasis R v b) {i j : ι} (hij : i ≠ j) :
    ((dynkinDiagram b).edges i j : ℝ) = cartanMatrix b i j * cartanMatrix b j i := by
  have hp := cartan_product R hR v hv b hb i j hij
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with h | h | h | h <;> simp [dynkinDiagram, hij, h]

lemma cartan_zero_iff (hR : RootAxioms R) (hb : IsSimpleBasis R v b) (i j : ι) :
    cartanMatrix b i j = 0 ↔ inner ℝ (b i) (b j) = 0 := by
  simp [cartanMatrix, rootCartan, b.ne_zero i,
    real_inner_comm (b j) (b i)]

lemma dynkin_edges_ne_zero (hR : IsRootSystem R) (hv : RootRegular R v)
    (hb : IsSimpleBasis R v b) (i j : ι) :
    (dynkinDiagram b).edges i j ≠ 0 ↔ i ≠ j ∧ inner ℝ (b i) (b j) ≠ 0 := by
  by_cases hij : i = j
  · subst j
    simp [dynkinDiagram]
  · have he := dynkin_edges_cast hR hv hb hij
    have hz : (dynkinDiagram b).edges i j = 0 ↔ inner ℝ (b i) (b j) = 0 := by
      rw [← Nat.cast_eq_zero (R := ℝ), he, mul_eq_zero,
        cartan_zero_iff hR.toRootAxioms hb i j, cartan_zero_iff hR.toRootAxioms hb j i,
        real_inner_comm (b j) (b i), or_self]
    simp [hij, hz]

theorem dynkin_diagram_properties : CartanMatrixSpecs.diagramType := by
  intro E _ _ ι R hR v hv b hb
  refine ⟨?_, ?_, ?_, dynkin_edges_ne_zero hR hv hb, ?_⟩
  · intro i
    simp [dynkinDiagram]
  · exact fun i j hij => dynkin_edges_cast hR hv hb hij
  · intro i j
    by_cases hij : i = j
    · subst j; rfl
    · apply Nat.cast_injective (R := ℝ)
      rw [dynkin_edges_cast hR hv hb hij, dynkin_edges_cast hR hv hb (Ne.symm hij), mul_comm]
  · intro i j
    rw [dynkin_edges_ne_zero hR hv hb]
    exact and_assoc.symm

lemma cartan_pair_values (hR : IsRootSystem R) (hv : RootRegular R v)
    (hb : IsSimpleBasis R v b) {i j : ι} (hij : i ≠ j) :
    (cartanMatrix b i j, cartanMatrix b j i) ∈
      ({(0,0),(-1,-1),(-1,-2),(-2,-1),(-1,-3),(-3,-1)} : Set (ℝ × ℝ)) := by
  have hr := cartan_restrictions R hR.toRootAxioms (b j) (hb.root_mem j)
    (b i) (hb.root_mem i) (basis_pair_independent b (Ne.symm hij))
  have hi := (cartan_offDiagonal R hR v hv b hb).2 i j hij
  have hj := (cartan_offDiagonal R hR v hv b hb).2 j i (Ne.symm hij)
  change rootCartan (b j) (b i) ≤ 0 at hi
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hr ⊢
  rcases hr with h | h | h | h | h | h | h | h | h | h | h <;>
    rcases h with ⟨h₁,h₂⟩ <;> simp_all [cartanMatrix] <;> norm_num at *

lemma dynkin_arrow_iff_cartan_lt (hR : IsRootSystem R) (hv : RootRegular R v)
    (hb : IsSimpleBasis R v b) {i j : ι} (hij : i ≠ j) :
    (dynkinDiagram b).arrow i j ↔ cartanMatrix b j i < cartanMatrix b i j := by
  have hp := cartan_pair_values hR hv hb hij
  have hi : 0 < inner ℝ (b i) (b i) := real_inner_self_pos.mpr (b.ne_zero i)
  have hj : 0 < inner ℝ (b j) (b j) := real_inner_self_pos.mpr (b.ne_zero j)
  have he : cartanMatrix b i j * inner ℝ (b i) (b i) =
      cartanMatrix b j i * inner ℝ (b j) (b j) := by
    simp only [cartanMatrix, rootCartan_mul_self, real_inner_comm (b j) (b i)]
  have hz := cartan_zero_iff hR.toRootAxioms hb i j
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hp
  change (i ≠ j ∧ inner ℝ (b i) (b j) ≠ 0 ∧
    inner ℝ (b j) (b j) < inner ℝ (b i) (b i)) ↔ _
  rcases hp with h | h | h | h | h | h <;> rcases h with ⟨h₁,h₂⟩ <;>
    rw [h₁,h₂] at he ⊢ <;> rw [h₁] at hz <;> norm_num at hz ⊢ <;>
    simp_all <;> linarith

lemma cartan_eq_of_diagram_eq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {S : Set F} {z : F} {c : Basis ι ℝ F}
    (hR : IsRootSystem R) (hS : IsRootSystem S)
    (hv : RootRegular R v) (hz : RootRegular S z)
    (hb : IsSimpleBasis R v b) (hc : IsSimpleBasis S z c)
    (hedge : ∀ i j, (dynkinDiagram b).edges i j = (dynkinDiagram c).edges i j)
    (harrow : ∀ i j, (dynkinDiagram b).arrow i j ↔ (dynkinDiagram c).arrow i j) :
    cartanMatrix b = cartanMatrix c := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [cartan_diagonal R hR v hv b hb, cartan_diagonal S hS z hz c hc]
  have hp := cartan_pair_values hR hv hb hij
  have hq := cartan_pair_values hS hz hc hij
  have he : cartanMatrix b i j * cartanMatrix b j i =
      cartanMatrix c i j * cartanMatrix c j i := by
    rw [← dynkin_edges_cast hR hv hb hij, ← dynkin_edges_cast hS hz hc hij, hedge]
  have ha := harrow i j
  rw [dynkin_arrow_iff_cartan_lt hR hv hb hij, dynkin_arrow_iff_cartan_lt hS hz hc hij] at ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hp hq
  rcases hp with h | h | h | h | h | h <;> rcases h with ⟨h₁,h₂⟩ <;>
    rcases hq with h | h | h | h | h | h <;> rcases h with ⟨h₃,h₄⟩ <;> simp_all

section Reconstruction
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {S : Set F} {z : F} {c : Basis ι ℝ F}

lemma reflection_map_of_cartan (f : E ≃ₗ[ℝ] F) (hf : ∀ i, f (b i) = c i)
    (hcartan : cartanMatrix b = cartanMatrix c) (i : ι) (x : E) :
    f (rootReflection (b i) x) = rootReflection (c i) (f x) := by
  have he : f.toLinearMap.comp (rootReflectionEquiv (b i)).toLinearMap =
      (rootReflectionEquiv (c i)).toLinearMap.comp f.toLinearMap := by
    apply b.ext
    intro j
    change f (rootReflectionEquiv (b i) (b j)) = rootReflectionEquiv (c i) (f (b j))
    simp only [rootReflectionEquiv_apply, hf, rootReflection, map_sub, map_smul]
    change c j - cartanMatrix b i j • c i = c j - cartanMatrix c i j • c i
    rw [hcartan]
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, rootReflectionEquiv_apply] using
    LinearMap.congr_fun he x

lemma map_roots_of_cartan (hR : IsRootSystem R) (hS : IsRootSystem S)
    (hv : RootRegular R v) (hb : IsSimpleBasis R v b) (hc : IsSimpleBasis S z c)
    (f : E ≃ₗ[ℝ] F) (hf : ∀ i, f (b i) = c i)
    (hcartan : cartanMatrix b = cartanMatrix c) : f '' R ⊆ S := by
  have hgroup {w : E ≃ₗ[ℝ] E} (hw : w ∈ simpleWeylGroup R v) :
      ∀ x, f (w x) ∈ S ↔ f x ∈ S := by
    induction hw using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, rfl⟩ := hw
      obtain ⟨i, rfl⟩ := hb.symm ▸ ha
      intro x
      rw [rootReflectionEquiv_apply, reflection_map_of_cartan f hf hcartan]
      exact ⟨fun hx => by simpa using hS.reflection_mem _ (hc.root_mem i) _ hx,
        fun hx => hS.reflection_mem _ (hc.root_mem i) _ hx⟩
    | one => intro x; rfl
    | mul w u hw hu ihw ihu =>
      intro x
      exact (ihw (u x)).trans (ihu x)
    | inv w hw ih =>
      intro x
      simpa using (ih (w.symm x)).symm
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨w,a,ha,hw⟩ := root_simple_orbit hR hv hx
  obtain ⟨i,hi⟩ := hb.symm ▸ ha
  rw [← hw, ← hi]
  exact (hgroup w.property (b i)).mpr (hf i ▸ hc.root_mem i)

lemma root_image_of_cartan (hR : IsRootSystem R) (hS : IsRootSystem S)
    (hv : RootRegular R v) (hz : RootRegular S z)
    (hb : IsSimpleBasis R v b) (hc : IsSimpleBasis S z c)
    (f : E ≃ₗ[ℝ] F) (hf : ∀ i, f (b i) = c i)
    (hcartan : cartanMatrix b = cartanMatrix c) : f '' R = S := by
  apply Set.Subset.antisymm (map_roots_of_cartan hR hS hv hb hc f hf hcartan)
  intro y hy
  have hi : ∀ i, f.symm (c i) = b i := fun i => by rw [← hf i, f.symm_apply_apply]
  have hm := map_roots_of_cartan hS hR hz hc hb f.symm hi hcartan.symm
  exact ⟨f.symm y, hm (Set.mem_image_of_mem _ hy), f.apply_symm_apply y⟩

/-- Squared metric scale on a basis line. -/
def basisLengthScale (b : Basis ι ℝ E) (c : Basis ι ℝ F) (i : ι) : ℝ :=
  inner ℝ (c i) (c i) / inner ℝ (b i) (b i)

lemma basisLengthScale_pos (b : Basis ι ℝ E) (c : Basis ι ℝ F) (i : ι) :
    0 < basisLengthScale b c i :=
  div_pos (real_inner_self_pos.mpr (c.ne_zero i)) (real_inner_self_pos.mpr (b.ne_zero i))

lemma gram_entry_scaled (hcartan : cartanMatrix b = cartanMatrix c) (i j : ι) :
    inner ℝ (c i) (c j) = basisLengthScale b c i * inner ℝ (b i) (b j) := by
  have he : cartanMatrix b i j * inner ℝ (b i) (b i) = 2 * inner ℝ (b i) (b j) := by
    rw [cartanMatrix, rootCartan_mul_self, real_inner_comm]
  have he' : cartanMatrix b i j * inner ℝ (c i) (c i) = 2 * inner ℝ (c i) (c j) := by
    rw [hcartan, cartanMatrix, rootCartan_mul_self, real_inner_comm]
  have hs : basisLengthScale b c i * inner ℝ (b i) (b i) = inner ℝ (c i) (c i) :=
    div_mul_cancel₀ _ (inner_self_ne_zero (b.ne_zero i))
  have hmul := congrArg (fun t : ℝ => basisLengthScale b c i * t) he
  nlinarith only [hmul, he', congrArg (fun t : ℝ => cartanMatrix b i j * t) hs]

lemma basisLengthScale_constant (hR : IsRootSystem R) (hv : RootRegular R v)
    (hb : IsSimpleBasis R v b) (hcartan : cartanMatrix b = cartanMatrix c)
    {i j : ι} (hij : DynkinConnected b i j) : basisLengthScale b c i = basisLengthScale b c j := by
  induction hij with
  | rel i j hij =>
    have hip := ((dynkin_edges_ne_zero hR hv hb i j).mp hij).2
    have h₁ := gram_entry_scaled hcartan i j
    have h₂ := gram_entry_scaled hcartan j i
    rw [real_inner_comm (c i) (c j), real_inner_comm (b i) (b j)] at h₂
    exact mul_right_cancel₀ hip (h₁.symm.trans h₂)
  | refl => rfl
  | symm i j hij ih => exact ih.symm
  | trans i j k hij hjk ih₁ ih₂ => exact ih₁.trans ih₂

lemma component_metric_scaled (hR : IsRootSystem R) (hv : RootRegular R v)
    (hb : IsSimpleBasis R v b) (hcartan : cartanMatrix b = cartanMatrix c)
    (f : E ≃ₗ[ℝ] F) (hf : ∀ i, f (b i) = c i) (i : ι)
    {x y : E} (hx : x ∈ dynkinComponentSpan b i) (hy : y ∈ dynkinComponentSpan b i) :
    inner ℝ (f x) (f y) = basisLengthScale b c i * inner ℝ x y := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j,hj,rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k,hk,rfl⟩ := hy
      rw [hf,hf,gram_entry_scaled hcartan,
        ← basisLengthScale_constant hR hv hb hcartan hj]
    | zero => simp
    | add x y hx hy ihx ihy => simp only [map_add, inner_add_right, ihx, ihy, mul_add]
    | smul t x hx ih => simp only [map_smul, real_inner_smul_right, ih, mul_left_comm]
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add, inner_add_left, ihx, ihy, mul_add]
  | smul t x hx ih => simp only [map_smul, real_inner_smul_left, ih, mul_left_comm]

set_option maxHeartbeats 800000 in
theorem dynkin_reconstruction : CartanMatrixSpecs.reconstructionType := by
  intro E F _ _ _ _ ι R S hR hS v z hv hz b c hb hc hedge harrow
  have hcartan := cartan_eq_of_diagram_eq hR hS hv hz hb hc hedge harrow
  let f := b.equiv c (Equiv.refl ι)
  have hf : ∀ i, f (b i) = c i := fun i => b.equiv_apply i c (Equiv.refl ι)
  refine ⟨f, basisLengthScale b c, hf,
    root_image_of_cartan hR hS hv hz hb hc f hf hcartan,
    basisLengthScale_pos b c, ?_, ?_⟩
  · exact fun i j hij => basisLengthScale_constant hR hv hb hcartan hij
  · exact fun i x hx y hy => component_metric_scaled hR hv hb hcartan f hf i hx hy

set_option maxHeartbeats 800000 in
theorem dynkin_reconstruction_iso : CartanMatrixSpecs.reconstructionIsoType := by
  intro E F _ _ _ _ ι κ R S hR hS v z hv hz b c hb hc e hedge harrow
  let d : Basis ι ℝ F := c.reindex e.symm
  have hd (i : ι) : d i = c (e i) := by simp [d]
  have hds : IsSimpleBasis S z d := by
    change Set.range (c.reindex e.symm) = simpleRoots S z
    rw [Basis.range_reindex]
    exact hc
  have he : ∀ i j, (dynkinDiagram b).edges i j = (dynkinDiagram d).edges i j := by
    intro i j
    by_cases hij : i = j
    · subst j; simp [dynkinDiagram]
    · have heij : e i ≠ e j := fun h => hij (e.injective h)
      simpa [dynkinDiagram, cartanMatrix, hd, hij, heij] using hedge i j
  have ha : ∀ i j, (dynkinDiagram b).arrow i j ↔ (dynkinDiagram d).arrow i j := by
    intro i j
    simpa [dynkinDiagram, hd, e.injective.ne_iff] using harrow i j
  obtain ⟨f,s,hf,hroots,hs,hconst,hmetric⟩ := dynkin_reconstruction R S hR hS v z hv hz b d hb hds he ha
  exact ⟨f,s,fun i => (hf i).trans (hd i),hroots,hs,hconst,hmetric⟩

end Reconstruction
namespace DynkinConnected
variable {i j k : ι}
lemma refl (b : ι → E) (i : ι) : DynkinConnected b i i := Relation.EqvGen.refl i
lemma symm (h : DynkinConnected b i j) : DynkinConnected b j i := Relation.EqvGen.symm _ _ h
lemma trans (h : DynkinConnected b i j) (h' : DynkinConnected b j k) :
    DynkinConnected b i k := Relation.EqvGen.trans _ _ _ h h'
end DynkinConnected

lemma dynkin_connected_of_inner_ne_zero (hR : IsRootSystem R) (hv : RootRegular R v)
    (hb : IsSimpleBasis R v b) {i j : ι} (hip : inner ℝ (b i) (b j) ≠ 0) :
    DynkinConnected b i j := by
  by_cases hij : i = j
  · subst j; exact .refl b i
  · exact .rel _ _ ((dynkin_edges_ne_zero hR hv hb i j).mpr ⟨hij, hip⟩)

lemma dynkin_connected_rootConnected (hR : IsRootSystem R) (hv : RootRegular R v)
    (hb : IsSimpleBasis R v b) {i j : ι} (h : DynkinConnected b i j) :
    RootConnected R (b i) (b j) := by
  induction h with
  | rel i j h => exact .rel _ _ ⟨hb.root_mem i, hb.root_mem j,
      ((dynkin_edges_ne_zero hR hv hb i j).mp h).2⟩
  | refl => exact .refl _
  | symm i j h ih => exact ih.symm
  | trans i j k h h' ih ih' => exact ih.trans ih'

lemma dynkin_component_span_eq {i j : ι} (h : DynkinConnected b i j) :
    dynkinComponentSpan b i = dynkinComponentSpan b j := by
  have hc : dynkinComponent b i = dynkinComponent b j := by
    ext k
    exact ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩
  unfold dynkinComponentSpan
  rw [hc]

lemma basis_mem_dynkin_span (b : Basis ι ℝ E) (i : ι) : b i ∈ dynkinComponentSpan b i :=
  Submodule.subset_span ⟨i, DynkinConnected.refl b i, rfl⟩

lemma dynkin_spans_orthogonal (hR : IsRootSystem R) (hv : RootRegular R v)
    (hb : IsSimpleBasis R v b) {i j : ι} (hij : ¬ DynkinConnected b i j)
    {x y : E} (hx : x ∈ dynkinComponentSpan b i) (hy : y ∈ dynkinComponentSpan b j) :
    inner ℝ x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k,hk,rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l,hl,rfl⟩ := hy
      by_contra hip
      exact hij (hk.trans ((dynkin_connected_of_inner_ne_zero hR hv hb hip).trans hl.symm))
    | zero => simp
    | add x y hx hy ihx ihy => simp [inner_add_right, ihx, ihy]
    | smul t x hx ih => simp [real_inner_smul_right, ih]
  | zero => simp
  | add x y hx hy ihx ihy => simp [inner_add_left, ihx, ihy]
  | smul t x hx ih => simp [real_inner_smul_left, ih]

lemma simple_reflection_dynkin_span (hR : IsRootSystem R) (hv : RootRegular R v)
    (hb : IsSimpleBasis R v b) (i k : ι) {x : E} (hx : x ∈ dynkinComponentSpan b i) :
    rootReflection (b k) x ∈ dynkinComponentSpan b i := by
  by_cases hik : DynkinConnected b i k
  · exact (dynkinComponentSpan b i).sub_mem hx
      ((dynkinComponentSpan b i).smul_mem _
        (Submodule.subset_span ⟨k,hik,rfl⟩))
  · have hip := dynkin_spans_orthogonal hR hv hb hik hx (basis_mem_dynkin_span b k)
    simpa [rootReflection, hip] using hx

lemma simpleWeylGroup_dynkin_span (hR : IsRootSystem R) (hv : RootRegular R v)
    (hb : IsSimpleBasis R v b) (i : ι) {w : E ≃ₗ[ℝ] E} (hw : w ∈ simpleWeylGroup R v) :
    ∀ x, x ∈ dynkinComponentSpan b i ↔ w x ∈ dynkinComponentSpan b i := by
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a,ha,rfl⟩ := hw
    obtain ⟨k,rfl⟩ := hb.symm ▸ ha
    intro x
    simp only [rootReflectionEquiv_apply]
    exact ⟨fun hx => simple_reflection_dynkin_span hR hv hb i k hx,
      fun hx => by simpa using simple_reflection_dynkin_span hR hv hb i k hx⟩
  | one => intro x; rfl
  | mul w u hw hu ihw ihu => intro x; exact (ihu x).trans (ihw (u x))
  | inv w hw ih => intro x; simpa using (ih (w.symm x)).symm

lemma root_mem_some_dynkin_span (hR : IsRootSystem R) (hv : RootRegular R v)
    (hb : IsSimpleBasis R v b) {x : E} (hx : x ∈ R) :
    ∃ i, x ∈ dynkinComponentSpan b i := by
  obtain ⟨w,a,ha,hw⟩ := root_simple_orbit hR hv hx
  obtain ⟨i,rfl⟩ := hb.symm ▸ ha
  exact ⟨i, hw ▸ (simpleWeylGroup_dynkin_span hR hv hb i w.property (b i)).mp
    (basis_mem_dynkin_span b i)⟩

lemma root_mem_dynkin_span_of_nonorthogonal (hR : IsRootSystem R) (hv : RootRegular R v)
    (hb : IsSimpleBasis R v b) {i : ι} {x y : E}
    (hy : y ∈ R) (hx : x ∈ dynkinComponentSpan b i) (hip : inner ℝ x y ≠ 0) :
    y ∈ dynkinComponentSpan b i := by
  obtain ⟨j,hj⟩ := root_mem_some_dynkin_span hR hv hb hy
  by_cases hij : DynkinConnected b i j
  · rwa [dynkin_component_span_eq hij]
  · exact (hip (dynkin_spans_orthogonal hR hv hb hij hx hj)).elim

lemma rootConnected_dynkin_span (hR : IsRootSystem R) (hv : RootRegular R v)
    (hb : IsSimpleBasis R v b) (i : ι) {x y : E} (h : RootConnected R x y) :
    x ∈ dynkinComponentSpan b i ↔ y ∈ dynkinComponentSpan b i := by
  induction h with
  | rel x y h =>
    exact ⟨fun hx => root_mem_dynkin_span_of_nonorthogonal hR hv hb h.2.1 hx h.2.2,
      fun hy => root_mem_dynkin_span_of_nonorthogonal hR hv hb h.1 hy
        (by simpa only [real_inner_comm x y] using h.2.2)⟩
  | refl => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z h h' ih ih' => exact ih.trans ih'

lemma root_mem_dynkin_span_iff (hR : IsRootSystem R) (hv : RootRegular R v)
    (hb : IsSimpleBasis R v b) (i : ι) {x : E} (hx : x ∈ R) :
    x ∈ dynkinComponentSpan b i ↔ RootConnected R (b i) x := by
  constructor
  · intro hxi
    by_contra hn
    have horth : ∀ y ∈ dynkinComponentSpan b i, inner ℝ y x = 0 := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j,hj,rfl⟩ := hy
        by_contra hjx
        exact hn ((dynkin_connected_rootConnected hR hv hb hj).trans
          (.rel _ _ ⟨hb.root_mem j, hx, hjx⟩))
      | zero => simp
      | add y z hy hz ihy ihz => simp [inner_add_left, ihy, ihz]
      | smul t y hy ih => simp [real_inner_smul_left, ih]
    exact (inner_self_ne_zero (hR.nonzero x hx)) (horth x hxi)
  · intro h
    exact (rootConnected_dynkin_span hR hv hb i h).mp (basis_mem_dynkin_span b i)

lemma dynkin_connected_iff_rootConnected (hR : IsRootSystem R) (hv : RootRegular R v)
    (hb : IsSimpleBasis R v b) (i j : ι) :
    DynkinConnected b i j ↔ RootConnected R (b i) (b j) := by
  refine ⟨dynkin_connected_rootConnected hR hv hb, ?_⟩
  intro h
  by_contra hn
  have hj := (root_mem_dynkin_span_iff hR hv hb i (hb.root_mem j)).mpr h
  exact (inner_self_ne_zero (b.ne_zero j))
    (dynkin_spans_orthogonal hR hv hb hn hj (basis_mem_dynkin_span b j))

theorem dynkin_components : CartanMatrixSpecs.componentsType := by
  intro E _ _ ι R hR v hv b hb
  refine ⟨dynkin_connected_iff_rootConnected hR hv hb, ?_, ?_⟩
  · exact fun i x hx => root_mem_dynkin_span_iff hR hv hb i hx
  · have he : Set.range (fun i => {x | x ∈ R ∧ x ∈ dynkinComponentSpan b i}) =
        rootComponents R := by
      have hfactor (i : ι) : {x | x ∈ R ∧ x ∈ dynkinComponentSpan b i} = rootComponent R (b i) := by
        ext x
        exact ⟨fun h => (root_mem_dynkin_span_iff hR hv hb i h.1).mp h.2,
          fun h => ⟨component_subset (hb.root_mem i) h,
            (rootConnected_dynkin_span hR hv hb i h).mp (basis_mem_dynkin_span b i)⟩⟩
      apply Set.Subset.antisymm
      · rintro A ⟨i,rfl⟩
        change {x | x ∈ R ∧ x ∈ dynkinComponentSpan b i} ∈ rootComponents R
        rw [hfactor i]
        exact Set.mem_image_of_mem _ (hb.root_mem i)
      · rintro A ⟨x,hx,rfl⟩
        obtain ⟨i,hi⟩ := root_mem_some_dynkin_span hR hv hb hx
        have hc := (root_mem_dynkin_span_iff hR hv hb i hx).mp hi
        exact ⟨i,(hfactor i).trans (component_eq hc)⟩
    rw [he]
    exact canonical_decomposition hR

section OrthogonalProduct
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable (V : κ → Submodule ℝ E) (hV : DirectSum.IsInternal V)

/-- Coordinates in an internal orthogonal decomposition, including an empty sum. -/
def orthogonalSumCoordinates : E ≃ₗ[ℝ] (∀ i, V i) :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap V) hV).symm.trans
    (DirectSum.linearEquivFunOnFintype ℝ κ (fun i => V i))

lemma orthogonalSumCoordinates_symm_single (i : κ) (x : V i) :
    (orthogonalSumCoordinates V hV).symm (Pi.single i x) = (x : E) := by
  simp only [orthogonalSumCoordinates, LinearEquiv.symm_trans_apply,
    DirectSum.linearEquivFunOnFintype_symm_single, LinearEquiv.symm_symm]
  exact DirectSum.coeLinearMap_lof V i x

lemma orthogonalSumCoordinates_subtype (i : κ) (x : V i) :
    orthogonalSumCoordinates V hV (x : E) = Pi.single i x := by
  apply (orthogonalSumCoordinates V hV).symm.injective
  rw [LinearEquiv.symm_apply_apply, orthogonalSumCoordinates_symm_single]

/-- Extend a family of automorphisms by its block diagonal action. -/
def orthogonalBlockAction : (∀ i, V i ≃ₗ[ℝ] V i) →* (E ≃ₗ[ℝ] E) where
  toFun u := (orthogonalSumCoordinates V hV).trans
    ((LinearEquiv.piCongrRight u).trans (orthogonalSumCoordinates V hV).symm)
  map_one' := by
    ext x
    change (orthogonalSumCoordinates V hV).symm (orthogonalSumCoordinates V hV x) = x
    exact (orthogonalSumCoordinates V hV).symm_apply_apply x
  map_mul' u w := by
    ext x
    simp only [LinearEquiv.trans_apply, LinearEquiv.mul_apply,
      LinearEquiv.apply_symm_apply]
    rfl

lemma orthogonalBlockAction_subtype (u : ∀ i, V i ≃ₗ[ℝ] V i) (i : κ) (x : V i) :
    orthogonalBlockAction V hV u (x : E) = (u i x : E) := by
  change (orthogonalSumCoordinates V hV).symm
    (LinearEquiv.piCongrRight u (orthogonalSumCoordinates V hV (x : E))) = _
  rw [orthogonalSumCoordinates_subtype]
  have he : LinearEquiv.piCongrRight u (Pi.single i x) = Pi.single i (u i x) := by
    ext j
    by_cases hj : j = i
    · subst j; simp
    · simp [Pi.single_apply, hj, Ne.symm hj]
  rw [he, orthogonalSumCoordinates_symm_single]

lemma orthogonalBlockAction_injective : Function.Injective (orthogonalBlockAction V hV) := by
  intro u w he
  funext i
  ext x
  exact (orthogonalBlockAction_subtype V hV u i x).symm.trans
    ((LinearEquiv.congr_fun he (x : E)).trans (orthogonalBlockAction_subtype V hV w i x))

include hV in
/-- Equality of ambient linear transformations can be tested on all summands. -/
lemma linearEquiv_eq_on_summands {f g : E ≃ₗ[ℝ] E}
    (h : ∀ i (x : V i), f x = g x) : f = g := by
  have he : f.toLinearMap.comp (DirectSum.coeLinearMap V) =
      g.toLinearMap.comp (DirectSum.coeLinearMap V) := by
    apply DirectSum.linearMap_ext
    intro i
    ext x
    simpa using h i x
  ext x
  obtain ⟨y,rfl⟩ := hV.surjective x
  exact LinearMap.congr_fun he y

lemma orthogonalBlockAction_reflection
    (ho : ∀ i j, i ≠ j → ∀ x ∈ V i, ∀ y ∈ V j, inner ℝ x y = 0)
    (i : κ) (a : V i) :
    orthogonalBlockAction V hV (Pi.mulSingle i (rootReflectionEquiv a)) =
      rootReflectionEquiv (a : E) := by
  apply linearEquiv_eq_on_summands V hV
  intro j x
  rw [orthogonalBlockAction_subtype, rootReflectionEquiv_apply]
  by_cases hji : j = i
  · subst j
    simp only [Pi.mulSingle_eq_same, rootReflectionEquiv_apply]
    rfl
  · have hip := ho j i hji x x.property a a.property
    simp [Pi.mulSingle_eq_of_ne hji, rootReflection, hip]

include hV in
set_option maxHeartbeats 800000 in
/-- Weyl group factorization for a genuine orthogonal internal decomposition.
The generators in a summand extend to the ambient root reflections. -/
lemma weyl_product_of_orthogonal_sum (hR : IsRootSystem R)
    (ho : ∀ i j, i ≠ j → ∀ x ∈ V i, ∀ y ∈ V j, inner ℝ x y = 0)
    (hroots : ∀ a ∈ R, ∃ i, a ∈ V i) :
    ∃ φ : rootWeylGroup R ≃*
      (∀ i, rootWeylGroup {x : V i | (x : E) ∈ R}),
      ∀ w i (x : V i), (((φ w i).val x : V i) : E) = w.val (x : E) := by
  let H (i : κ) : Subgroup (V i ≃ₗ[ℝ] V i) :=
    rootWeylGroup {x : V i | (x : E) ∈ R}
  let B := orthogonalBlockAction V hV
  have hsingle (i : κ) (w : V i ≃ₗ[ℝ] V i) (hw : w ∈ H i) :
      B (Pi.mulSingle i w) ∈ rootWeylGroup R := by
    induction hw using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a,ha,rfl⟩ := hw
      rw [orthogonalBlockAction_reflection V hV ho]
      exact Subgroup.subset_closure (Set.mem_image_of_mem _ ha)
    | one => simp [B]
    | mul w u hw hu ihw ihu =>
      simpa only [Pi.mulSingle_mul, map_mul] using (rootWeylGroup R).mul_mem ihw ihu
    | inv w hw ih =>
      simpa only [Pi.mulSingle_inv, map_inv] using (rootWeylGroup R).inv_mem ih
  have hblock (u : ∀ i, H i) : B (fun i => (u i).val) ∈ rootWeylGroup R := by
    exact Subgroup.pi_mem_of_mulSingle_mem
      (H := (rootWeylGroup R).comap B) (fun i => (u i).val)
      (fun i => hsingle i (u i).val (u i).property)
  let P : (∀ i, H i) →* (∀ i, V i ≃ₗ[ℝ] V i) :=
    { toFun := fun u i => (u i).val
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let L : (∀ i, H i) →* rootWeylGroup R :=
    { toFun := fun u => ⟨B (fun i => (u i).val), hblock u⟩
      map_one' := by apply Subtype.ext; exact B.map_one
      map_mul' := fun u w => by apply Subtype.ext; exact B.map_mul _ _ }
  have hinj : Function.Injective L := by
    intro u w he
    have he' : (fun i => (u i).val) = (fun i => (w i).val) :=
      orthogonalBlockAction_injective V hV (congrArg Subtype.val he)
    funext i
    exact Subtype.ext (congrFun he' i)
  have hsurj : Function.Surjective L := by
    have hrange : rootWeylGroup R ≤ (B.comp P).range := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨a,ha,rfl⟩
      obtain ⟨i,hi⟩ := hroots a ha
      let a' : V i := ⟨a,hi⟩
      let r : H i := ⟨rootReflectionEquiv a', Subgroup.subset_closure
        (Set.mem_image_of_mem _ ha)⟩
      refine ⟨Pi.mulSingle i r, ?_⟩
      rw [MonoidHom.comp_apply]
      have hv : P (Pi.mulSingle i r) =
          Pi.mulSingle i (rootReflectionEquiv a') := by
        ext j
        by_cases hj : j = i
        · subst j; simp [P, r]
        · simp [P, Pi.mulSingle_eq_of_ne hj, r]
      rw [hv]
      exact orthogonalBlockAction_reflection V hV ho i a'
    intro w
    obtain ⟨u,hu⟩ := hrange w.property
    exact ⟨u, Subtype.ext hu⟩
  let e := MulEquiv.ofBijective L ⟨hinj,hsurj⟩
  refine ⟨e.symm, ?_⟩
  intro w i x
  have he := congrArg (fun u : rootWeylGroup R => u.val (x : E)) (e.apply_symm_apply w)
  change B (fun j => (e.symm w j).val) (x : E) = w.val (x : E) at he
  rw [orthogonalBlockAction_subtype] at he
  exact he

end OrthogonalProduct

set_option maxHeartbeats 800000 in
theorem dynkin_weyl_product : CartanMatrixSpecs.weylProductType := by
  intro E _ _ ι R hR v hv b hb
  classical
  letI : Finite R := hR.finite.to_subtype
  letI : Finite ι := Finite.of_injective
    (fun i => (⟨b i, hb.root_mem i⟩ : R)) (fun i j h => b.injective (Subtype.mk.inj h))
  let K := Set.range (dynkinComponent b)
  letI : Fintype K := Fintype.ofFinite K
  let V : K → Submodule ℝ E := fun A => dynkinFactorSpace b A.val
  have hspan (i : ι) : V ⟨dynkinComponent b i, Set.mem_range_self i⟩ = dynkinComponentSpan b i := rfl
  have ho : ∀ A B, A ≠ B → ∀ x ∈ V A, ∀ y ∈ V B, inner ℝ x y = 0 := by
    intro A B hne x hx y hy
    obtain ⟨i,hi⟩ := A.property
    obtain ⟨j,hj⟩ := B.property
    have hnot : ¬ DynkinConnected b i j := by
      intro hc
      apply hne
      apply Subtype.ext
      rw [← hi, ← hj]
      ext k
      exact ⟨fun hk => hc.symm.trans hk, fun hk => hc.trans hk⟩
    change x ∈ Submodule.span ℝ (b '' A.val) at hx
    change y ∈ Submodule.span ℝ (b '' B.val) at hy
    rw [← hi] at hx
    rw [← hj] at hy
    exact dynkin_spans_orthogonal hR hv hb hnot hx hy
  have htop : iSup V = ⊤ := by
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro x ⟨i,rfl⟩
    exact Submodule.mem_iSup_of_mem ⟨dynkinComponent b i, Set.mem_range_self i⟩
      (basis_mem_dynkin_span b i)
  have horth : OrthogonalFamily ℝ (fun A => V A) (fun A => (V A).subtypeₗᵢ) := by
    intro A B hne x y
    exact ho A B hne x x.property y y.property
  have hV : DirectSum.IsInternal V :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top horth.independent htop
  have hroots : ∀ a ∈ R, ∃ A, a ∈ V A := by
    intro a ha
    obtain ⟨i,hi⟩ := root_mem_some_dynkin_span hR hv hb ha
    exact ⟨⟨dynkinComponent b i, Set.mem_range_self i⟩,hi⟩
  exact weyl_product_of_orthogonal_sum V hV hR ho hroots

end LieAlgebrasAndRepresentations
