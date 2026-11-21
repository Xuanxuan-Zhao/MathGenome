import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.UniformConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch04.ProperFilters

open Set Filter
open scoped Uniformity Topology SetRel
universe u v
/-! Chapter 12 conventions (paper.tex: d10:12:uniformity,
 d10:12:uniform-continuity, d10:12:cauchy).

The canonical uniformity is Mathlib's UniformSpace. The reconstruction theorem
checks that its filter axioms are exactly the paper's entourage axioms. Properness
holds precisely for nonempty underlying types; Cauchy filters always include
properness, even on the empty type. No separation hypothesis is imposed.
-/
namespace D10Topology.Ch12

def Uniformity (X : Type u) : Type u :=
  UniformSpace X

def relationInverse {X : Type u} (U : Set (X × X)) : Set (X × X) :=
  {p | (p.2, p.1) ∈ U}

def relationComp {X : Type u} (U V : Set (X × X)) : Set (X × X) :=
  {p | ∃ y, (p.1, y) ∈ V ∧ (y, p.2) ∈ U}

def entourageBall {X : Type u} (U : Set (X × X)) (x : X) : Set X :=
  {y | (x, y) ∈ U}

def EntourageAxioms {X : Type u} (F : Filter (X × X)) : Prop :=
  (∀ U ∈ F, ∀ x : X, (x, x) ∈ U) ∧
  (∀ U ∈ F, relationInverse U ∈ F) ∧
  (∀ U ∈ F, ∃ V ∈ F, relationComp V V ⊆ U)

def Separated {X : Type u} [UniformSpace X] : Prop :=
  ⋂₀ (𝓤 X).sets = diagonal X

def EntourageContinuous {X : Type u} {Y : Type v} [UniformSpace X] [UniformSpace Y] (f : X → Y) : Prop :=
  ∀ V ∈ 𝓤 Y, (Prod.map f f) ⁻¹' V ∈ 𝓤 X

def UniformIsomorphism {X : Type u} {Y : Type v} [UniformSpace X] [UniformSpace Y] (e : X ≃ Y) : Prop :=
  EntourageContinuous e ∧ EntourageContinuous e.symm

@[instance_reducible]
def inducedUniformity {X : Type u} {Y : Type v} [uY : UniformSpace Y] (f : X → Y) : UniformSpace X :=
  UniformSpace.comap f uY

def UniformEmbedding {X : Type u} {Y : Type v} [uX : UniformSpace X] [UniformSpace Y] (f : X → Y) : Prop :=
  Function.Injective f ∧ inducedUniformity f = uX

def CauchyFilter {X : Type u} [UniformSpace X] (F : Filter X) : Prop :=
  F.NeBot ∧ ∀ U ∈ 𝓤 X, ∃ A ∈ F, A ×ˢ A ⊆ U

def Complete (X : Type u) [UniformSpace X] : Prop :=
  ∀ F : Filter X, CauchyFilter F → ∃ x : X, Specs.D10Topology.Ch04.ProperFilters.FilterConverges F x

def TotallyBoundedSpace (X : Type u) [UniformSpace X] : Prop :=
  ∀ U ∈ 𝓤 X, ∃ C : Set X, C.Finite ∧ (⋃ x ∈ C, entourageBall U x) = univ

theorem relationInverse_preimage : ∀ {X : Type u} (U : Set (X × X)), relationInverse U = Prod.swap ⁻¹' U := by
  intros
  rfl

theorem relationInverse_image : ∀ {X : Type u} (U : Set (X × X)), relationInverse U = Prod.swap '' U := by
  intro X U
  exact (congrFun image_swap_eq_preimage_swap U).symm

theorem relationComp_mathlib : ∀ {X : Type u} (U V : Set (X × X)), relationComp U V = V ○ U := by
  intros
  rfl

theorem entourageBall_mathlib : ∀ {X : Type u} (U : Set (X × X)) (x : X), entourageBall U x = UniformSpace.ball x U := by
  intros
  rfl

theorem uniformity_axioms : ∀ {X : Type u} [UniformSpace X], EntourageAxioms (𝓤 X) := by
  intro X uX
  exact ⟨fun _ hU _ => refl_mem_uniformity hU,
    fun _ hU => symm_le_uniformity hU, fun _ hU => comp_mem_uniformity_sets hU⟩

theorem uniformity_iff_axioms : ∀ {X : Type u} (F : Filter (X × X)), EntourageAxioms F ↔ ∃! uX : Uniformity X, @uniformity X uX = F := by
  intro X F
  constructor
  · rintro ⟨hr, hi, hc⟩
    let core := UniformSpace.Core.mk' F hr hi hc
    refine ⟨UniformSpace.ofCore core, rfl, ?_⟩
    intro v hv
    exact UniformSpace.ext hv
  · rintro ⟨uX, rfl, _⟩
    letI : UniformSpace X := uX
    exact uniformity_axioms

theorem uniformity_proper : ∀ {X : Type u} [UniformSpace X] [Nonempty X], (𝓤 X).NeBot := by
  intro X uX hX
  infer_instance

theorem uniformity_empty : ∀ {X : Type u} [UniformSpace X] [IsEmpty X], (𝓤 X).sets = {∅} := by
  intro X uX hX
  ext U
  have h0 : U = ∅ := by ext p; exact isEmptyElim p
  have h1 : U = univ := by ext p; exact isEmptyElim p
  constructor
  · intro _
    exact h0
  · intro _
    rw [h1]
    exact univ_mem

theorem uniformity_empty_unique : ∀ {X : Type u} [IsEmpty X] (uX vX : Uniformity X), uX = vX := by
  intro X hX uX vX
  apply UniformSpace.ext
  apply Filter.ext
  intro U
  have h1 : U = univ := by ext p; exact isEmptyElim p
  rw [h1]
  simp

theorem separated_iff_mathlib : ∀ {X : Type u} [UniformSpace X], Separated (X := X) ↔ T0Space X := by
  intro X uX
  exact t0Space_iff_ker_uniformity.symm

theorem entourageContinuous_iff_mathlib : ∀ {X : Type u} {Y : Type v} [UniformSpace X] [UniformSpace Y] (f : X → Y), EntourageContinuous f ↔ UniformContinuous f := by
  intros
  rfl

theorem uniformIsomorphism_iff_mathlib : ∀ {X : Type u} {Y : Type v} [UniformSpace X] [UniformSpace Y] (e : X ≃ Y), UniformIsomorphism e ↔ ∃ h : X ≃ᵤ Y, h.toEquiv = e := by
  intro X Y uX uY e
  constructor
  · rintro ⟨hf, hg⟩
    exact ⟨{ toEquiv := e, uniformContinuous_toFun := hf, uniformContinuous_invFun := hg }, rfl⟩
  · rintro ⟨h, rfl⟩
    exact ⟨h.uniformContinuous, h.uniformContinuous_symm⟩

theorem inducedUniformity_entourages : ∀ {X : Type u} {Y : Type v} [UniformSpace Y] (f : X → Y) (U : Set (X × X)), U ∈ @uniformity X (inducedUniformity f) ↔ ∃ V ∈ 𝓤 Y, (Prod.map f f) ⁻¹' V ⊆ U := by
  intros
  exact mem_comap

theorem subspaceUniformity_entourages : ∀ {X : Type u} [UniformSpace X] (A : Set X) (U : Set (A × A)), U ∈ 𝓤 A ↔ ∃ V ∈ 𝓤 X, (Prod.map Subtype.val Subtype.val) ⁻¹' V ⊆ U := by
  intros
  exact mem_comap

theorem uniformEmbedding_iff_mathlib : ∀ {X : Type u} {Y : Type v} [UniformSpace X] [UniformSpace Y] (f : X → Y), UniformEmbedding f ↔ IsUniformEmbedding f := by
  intro X Y uX uY f
  change (Function.Injective f ∧ UniformSpace.comap f uY = uX) ↔ _
  rw [← isUniformInducing_iff_uniformSpace, isUniformEmbedding_iff, and_comm]

theorem uniformEmbedding_iff_range : ∀ {X : Type u} {Y : Type v} [UniformSpace X] [UniformSpace Y] (f : X → Y),
  UniformEmbedding f ↔ ∃ e : X ≃ range f, UniformIsomorphism e ∧ ∀ x, (e x).val = f x := by
  intro X Y uX uY f
  rw [uniformEmbedding_iff_mathlib]
  constructor
  · intro hf
    let e := UniformEquiv.ofIsUniformEmbedding f hf
    exact ⟨e.toEquiv, ⟨e.uniformContinuous, e.uniformContinuous_symm⟩, fun _ => rfl⟩
  · rintro ⟨e, ⟨hf, hg⟩, he⟩
    have hE : IsUniformEmbedding e := e.isUniformEmbedding hf hg
    have h := isUniformEmbedding_subtype_val.comp hE
    have hfun : Subtype.val ∘ e = f := funext he
    rwa [hfun] at h

theorem cauchyFilter_iff_mathlib : ∀ {X : Type u} [UniformSpace X] (F : Filter X), CauchyFilter F ↔ Cauchy F := by
  intros
  exact cauchy_iff.symm

theorem complete_iff_mathlib : ∀ {X : Type u} [UniformSpace X], Complete X ↔ CompleteSpace X := by
  intro X uX
  constructor
  · intro h
    refine ⟨fun {F} hF => ?_⟩
    obtain ⟨x, hx⟩ := h F ((cauchyFilter_iff_mathlib F).mpr hF)
    exact ⟨x, (Ch04.converges_iff_le_nhds F x).mp hx⟩
  · intro h F hF
    obtain ⟨x, hx⟩ := h.complete ((cauchyFilter_iff_mathlib F).mp hF)
    exact ⟨x, (Ch04.converges_iff_le_nhds F x).mpr hx⟩

theorem cauchyFilter_proper : ∀ {X : Type u} [UniformSpace X] (F : Filter X), CauchyFilter F → F.NeBot := by
  intro X uX F hF
  exact hF.1

theorem no_proper_filter_empty : ∀ {X : Type u} [IsEmpty X], IsEmpty (Specs.D10Topology.Ch04.ProperFilters.ProperFilter X) := by
  intro X hX
  exact Ch04.no_proper_filter_on_empty

theorem no_cauchyFilter_empty : ∀ {X : Type u} [UniformSpace X] [IsEmpty X] (F : Filter X), ¬ CauchyFilter F := by
  intro X uX hX F hF
  have hne := hF.1
  have hem : (∅ : Set X) ∈ F := by
    have : (∅ : Set X) = univ := by ext x; exact isEmptyElim x
    rw [this]
    exact univ_mem
  exact (Filter.empty_notMem F) hem

theorem complete_empty : ∀ {X : Type u} [UniformSpace X] [IsEmpty X], Complete X := by
  intro X uX hX F hF
  exact (no_cauchyFilter_empty F hF).elim

theorem entourageContinuous_empty : ∀ {X : Type u} {Y : Type v} [UniformSpace X] [UniformSpace Y] [IsEmpty X] (f : X → Y), EntourageContinuous f := by
  intro X Y uX uY hX f V hV
  have : (Prod.map f f) ⁻¹' V = univ := by ext p; exact isEmptyElim p
  rw [this]
  exact univ_mem

/-- Mathlib's finite covers use `(x, center) ∈ U`; the paper uses
`(center, x) ∈ U`. Applying either cover condition to the inverse entourage
identifies these formulations, including the empty cover. -/
theorem totallyBoundedSpace_iff_mathlib : ∀ {X : Type u} [UniformSpace X], TotallyBoundedSpace X ↔ TotallyBounded (univ : Set X) := by
  intro X uX
  constructor
  · intro h U hU
    obtain ⟨C, hC, hcover⟩ := h (relationInverse U) (symm_le_uniformity hU)
    refine ⟨C, hC, ?_⟩
    intro x _
    have hx : x ∈ ⋃ y ∈ C, entourageBall (relationInverse U) y := hcover.symm ▸ mem_univ x
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨y, hy, hxy⟩
  · intro h U hU
    obtain ⟨C, hC, hcover⟩ := h (relationInverse U) (symm_le_uniformity hU)
    refine ⟨C, hC, eq_univ_iff_forall.mpr ?_⟩
    intro x
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover (mem_univ x))
    exact mem_iUnion₂.mpr ⟨y, hy, hxy⟩

theorem empty_finite_cover : ∀ {X : Type u} [IsEmpty X] (U : Set (X × X)), (∅ : Set X).Finite ∧ (⋃ x ∈ (∅ : Set X), entourageBall U x) = univ := by
  intro X hX U
  refine ⟨finite_empty, ?_⟩
  ext x
  exact isEmptyElim x

theorem totallyBoundedSpace_empty : ∀ {X : Type u} [UniformSpace X] [IsEmpty X], TotallyBoundedSpace X := by
  intro X uX hX U hU
  exact ⟨∅, empty_finite_cover U⟩

theorem uniformity_proper_iff_nonempty : ∀ {X : Type u} [UniformSpace X], (𝓤 X).NeBot ↔ Nonempty X := by
  intro X uX
  constructor
  · intro h
    obtain ⟨p, _⟩ := h.nonempty_of_mem (univ_mem : (univ : Set (X × X)) ∈ 𝓤 X)
    exact ⟨p.1⟩
  · intro h
    letI := h
    exact uniformity_proper

end D10Topology.Ch12
