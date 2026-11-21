import MathGenome.Internal.Specs.D07.Ch15.PolynomialRadicals
import MathGenome.Internal.D07.Ch15.RadicalComposita
import MathGenome.Internal.D07.Ch12.EmbeddingExtension

/-! Solvability by radicals of all polynomial roots, common finite towers,
and embeddings of arbitrary splitting-field models. -/

universe u v w t
namespace D07.Ch15.PolynomialRadicals
open Polynomial
open Specs.D07.Ch15.RadicalDefinition
open Specs.D07.Ch15.PolynomialRadicals
open D07.Ch15.RadicalComposita

/-- Every root in the specified closure is radical; the zero polynomial is excluded. -/
def IsSolvableByRadicals : PolynomialSolvableType.{u, v} :=
  fun K Ω _ _ _ _ _ f => f ≠ 0 ∧
    ∀ x : Ω, aeval x f = 0 → solvableByRadicalsValue K Ω x

/-- A single finite tower contains all roots. -/
def HasCommonRadicalTower : CommonTowerType.{u, v} :=
  fun K Ω _ _ _ _ f =>
    ∃ (r : ℕ) (T : Fin (r + 1) → IntermediateField K Ω),
      radicalTowerValue K Ω r T ∧
        ∀ x : Ω, aeval x f = 0 → x ∈ T (Fin.last r)

/-- An arbitrary splitting-field model embeds in a radical intermediate field. -/
def HasRadicalEmbedding : RadicalEmbeddingType.{u, v, w} :=
  fun K Ω S _ _ _ _ _ _ =>
    ∃ E : IntermediateField K Ω, radicalExtensionValue K Ω E ∧ Nonempty (S →ₐ[K] E)

/-- The image of a splitting field contains every root, including when f is
inseparable or has repeated factors. -/
theorem root_mem_fieldRange {K : Type u} {S : Type w} {L : Type v}
    [Field K] [Field S] [Field L] [Algebra K S] [Algebra K L]
    (f : K[X]) [IsSplittingField K S f] (i : S →ₐ[K] L)
    {x : L} (hx : x ∈ f.rootSet L) : x ∈ i.fieldRange := by
  have h : x ∈ Algebra.adjoin K (f.rootSet L) := Algebra.subset_adjoin hx
  rw [IsSplittingField.adjoin_rootSet_eq_range S f i] at h
  exact h

theorem solvable_iff_common_tower : SolvableIffCommonTower.{u, v} := by
  intro K Ω _ _ _ _ _ f hf
  constructor
  · rintro ⟨_, hroots⟩
    classical
    let ι := {x : Ω // x ∈ f.rootSet Ω}
    have : Finite ι := (f.rootSet_finite Ω).to_subtype
    have heach (x : ι) : ∃ E : IntermediateField K Ω,
        radicalExtensionValue K Ω E ∧ (x : Ω) ∈ E :=
      hroots x (aeval_eq_zero_of_mem_rootSet x.2)
    choose E hE hxE using heach
    have hc := finite_radical_compositum K Ω ι E hE
    obtain ⟨r, T, hT, hlast⟩ := hc
    refine ⟨r, T, hT, fun x hx => ?_⟩
    rw [hlast]
    let y : ι := ⟨x, (mem_rootSet_of_ne hf).mpr hx⟩
    exact (le_iSup E y) (hxE y)
  · rintro ⟨r, T, hT, hx⟩
    exact ⟨hf, fun x h => ⟨T (Fin.last r), ⟨r, T, hT, rfl⟩, hx x h⟩⟩

/-- Compare a radical extension presented in another algebraic overfield
with the fixed closure, retaining the specified embedding of K. -/
theorem solvable_of_embedding_in_overfield : SolvableOfEmbeddingInOverfield.{u, v, w, t} := by
  intro K Ω S Ω' _ _ _ _ _ _ _ _ _ _ f _ hf E hE ⟨i⟩
  obtain ⟨τ, _, hτ⟩ :=
    D07.Ch12.EmbeddingExtension.extensionIntoAlgebraicallyClosed K E Ω (algebraMap K Ω)
  let σ : E →ₐ[K] Ω := { __ := τ, commutes' := hτ }
  have hrad := radical_extension_image K Ω' Ω E σ hE
  refine ⟨hf, fun x hx => ⟨σ.fieldRange, hrad, ?_⟩⟩
  obtain ⟨y, hy⟩ := root_mem_fieldRange f (σ.comp i) ((mem_rootSet_of_ne hf).mpr hx)
  exact ⟨i y, hy⟩

theorem solvable_iff_splitting_field_embedding :
    SolvableIffSplittingFieldEmbedding.{u, v, w} := by
  intro K Ω S _ _ _ _ _ _ _ f _ hf
  constructor
  · intro h
    obtain ⟨r, T, hT, hroots⟩ := (solvable_iff_common_tower K Ω f hf).mp h
    let E := T (Fin.last r)
    have hsplit : (f.map (algebraMap K E)).Splits :=
      IntermediateField.splits_of_splits (IsAlgClosed.splits _)
        (fun x hx => hroots x (aeval_eq_zero_of_mem_rootSet hx))
    exact ⟨E, ⟨r, T, hT, rfl⟩, ⟨IsSplittingField.lift S f hsplit⟩⟩
  · rintro ⟨E, hE, hi⟩
    exact solvable_of_embedding_in_overfield K Ω S Ω f hf E hE hi

end D07.Ch15.PolynomialRadicals
