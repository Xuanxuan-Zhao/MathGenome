import MathGenome.Internal.Specs.D07.Ch13.EmbeddingCompatibility
import MathGenome.Internal.D07.Ch13.Embeddings
import MathGenome.Internal.D07.Ch13.SubfieldLattice
import Mathlib.FieldTheory.Extension

/-!
Compatible embedding towers over a shared finite base (K07.13.embedding_compatibility).

Choose an embedding of the middle field into the last field. Minimal
polynomials over K split in the middle field (finite fields are normal),
so their coefficient images split in the last field as well. The embedding
extension theorem therefore extends σ ∘ ι⁻¹ from the image of ι. This proves
compatibility even for any prescribed first arrow. For the entire coherent
family, the canonical root-field inclusions preserve every ambient element;
identity and composition follow by extensionality.
-/

universe u v w z

namespace D07.Ch13.EmbeddingCompatibility

open Specs.D07.Ch13.EmbeddingCompatibility

/-- Any chosen first arrow admits a compatible second arrow. -/
theorem extend_first_embedding
    (K : Type u) (Ea : Type v) (Eb : Type w) (Ec : Type z)
    [Field K] [Field Ea] [Field Eb] [Field Ec]
    [Algebra K Ea] [Algebra K Eb] [Algebra K Ec]
    [Finite K] [FiniteDimensional K Ea] [FiniteDimensional K Eb]
    [FiniteDimensional K Ec]
    (hbc : Module.finrank K Eb ∣ Module.finrank K Ec)
    (ι : Ea →ₐ[K] Eb) (σ : Ea →ₐ[K] Ec) :
    ∃ τ : Eb →ₐ[K] Ec, τ.comp ι = σ := by
  have : Finite Eb := Module.finite_of_finite K
  have : Finite Ec := Module.finite_of_finite K
  obtain ⟨ρ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := K) (K := Eb) (L := Ec) hbc
  have hs : ∀ x : Eb, IsIntegral K x ∧
      ((minpoly K x).map (algebraMap K Ec)).Splits := by
    intro x
    refine ⟨Algebra.IsIntegral.isIntegral x, ?_⟩
    have h := (Normal.splits (inferInstance : Normal K Eb) x).map ρ.toRingHom
    simpa only [Polynomial.map_map, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap] using h
  let f : ι.fieldRange →ₐ[K] Ec := σ.comp ι.equivFieldRange.symm.toAlgHom
  obtain ⟨τ, hτ⟩ := IntermediateField.exists_algHom_of_splits hs f
  refine ⟨τ, ?_⟩
  ext x
  have h := DFunLike.congr_fun hτ (ι.equivFieldRange x)
  simpa [f] using h

theorem prescribed_triangle : PrescribedTriangle.{u, v, w, z} := by
  intro K Ea Eb Ec _ _ _ _ _ _ _ _ _ _ _ a b c _ha _hb _hc ha hb hc hab hbc σ
  obtain ⟨ι⟩ := (Embeddings.embedding_exists_iff K Ea Eb a b ha hb).mpr hab
  obtain ⟨τ, hτ⟩ := extend_first_embedding K Ea Eb Ec (by simpa [hb, hc] using hbc) ι σ
  exact ⟨ι, τ, hτ⟩

theorem compatible_tower : CompatibleTower.{u, v, w, z} := by
  intro K Ea Eb Ec _ _ _ _ _ _ _ _ _ _ _ a b c hapos hbpos hcpos ha hb hc hab hbc
  obtain ⟨σ⟩ := (Embeddings.embedding_exists_iff K Ea Ec a c ha hc).mpr (hab.trans hbc)
  obtain ⟨ι, τ, hτ⟩ := prescribed_triangle K Ea Eb Ec a b c hapos hbpos hcpos
    ha hb hc hab hbc σ
  exact ⟨ι, τ, σ, hτ⟩

/-- Divisibility-indexed nested intermediate fields have a simultaneous
system of inclusions satisfying the identity and composition laws. -/
theorem coherent_inclusions
    {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
    (F : ℕ+ → IntermediateField K Ω)
    (hle : ∀ a b : ℕ+, (a : ℕ) ∣ (b : ℕ) → F a ≤ F b) :
    ∃ j : ∀ a b : ℕ+, (a : ℕ) ∣ (b : ℕ) → F a →ₐ[K] F b,
      (∀ (a b : ℕ+) (h : (a : ℕ) ∣ (b : ℕ)) (x : F a),
        (j a b h x : Ω) = (x : Ω)) ∧
      (∀ a : ℕ+, j a a (dvd_refl _) = AlgHom.id K (F a)) ∧
      (∀ (a b c : ℕ+) (hab : (a : ℕ) ∣ (b : ℕ)) (hbc : (b : ℕ) ∣ (c : ℕ)),
        (j b c hbc).comp (j a b hab) = j a c (hab.trans hbc)) := by
  refine ⟨fun a b h => IntermediateField.inclusion (hle a b h), ?_, ?_, ?_⟩
  · intro a b h x
    exact IntermediateField.coe_inclusion _ x
  · intro a
    exact IntermediateField.inclusion_self
  · intro a b c hab hbc
    exact AlgHom.ext fun x => IntermediateField.inclusion_inclusion (hle a b hab) (hle b c hbc) x


theorem coherent_embedded_family : CoherentEmbeddedFamily.{u, v} := by
  intro K Ω _ _ _ _ _ _ q hq
  exact coherent_inclusions
    (fun n : ℕ+ => Specs.D07.Ch13.Existence.rootFieldValue K Ω q (n : ℕ))
    (fun a b h => SubfieldLattice.root_field_le_of_dvd K Ω q a b hq h)

end D07.Ch13.EmbeddingCompatibility
