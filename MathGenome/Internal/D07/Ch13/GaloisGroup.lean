import MathGenome.Internal.Specs.D07.Ch13.GaloisGroup
import MathGenome.Internal.D07.Ch13.Existence
import Mathlib.FieldTheory.Finite.Basic

/-!
The relative finite-field Galois group (K07.13.galois_group).

The library's order calculation uses precisely the source's argument:
Frobenius to the extension degree is the identity, and a smaller positive
power would make the whole field a set of roots of X^(q^j)-X, violating
the polynomial root bound. Its enumeration theorem compares these distinct
powers with the upper bound on the number of algebra embeddings. Thus no
cyclicity or prescribed order is assumed.

The full automorphism count also yields normality and separability by the
library criterion for finite extensions. For the specified embedded field,
the upstream construction supplies finiteness and the precise degree n.
No later project chapter or independently chosen field copy is used.
-/

universe u v

namespace D07.Ch13.GaloisGroup

open Specs.D07.Ch13.GaloisGroup

/-- For a finite field extension, exhibiting Frobenius and enumerating its
powers already determines the entire relative automorphism group. -/
theorem finite_extension_galois_group : FiniteExtensionGaloisGroup.{u, v} := by
  intro K L _ _ _ _ _ q n hq hn
  let := Fintype.ofFinite K
  let Φ : L ≃ₐ[K] L := FiniteField.frobeniusAlgEquivOfAlgebraic K L
  have hΦ : ∀ x : L, Φ x = x ^ q := by
    intro x
    change x ^ Fintype.card K = x ^ q
    rw [← Nat.card_eq_fintype_card, hq]
  have hord : orderOf Φ = n :=
    (FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic K L).trans hn
  have hbij : Function.Bijective (fun j : Fin n => Φ ^ (j : ℕ)) := by
    subst n
    exact FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K L
  have hcard : Nat.card (L ≃ₐ[K] L) = n := by
    rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_fin]
  let hgalois : IsGalois K L := IsGalois.of_card_aut_eq_finrank K L
    (hcard.trans hn.symm)
  have hnormal : Normal K L := inferInstance
  have hsep : Algebra.IsSeparable K L := inferInstance
  exact ⟨hnormal, hsep, inferInstance, hgalois, inferInstance,
    hcard, inferInstance, Φ, hΦ, hord, hord ▸ pow_orderOf_eq_one Φ, hbij⟩

/-- Apply the general result to the actual root field in the chosen closure. -/
theorem embedded_galois_group : EmbeddedGaloisGroup.{u, v} := by
  intro K Ω _ _ _ _ _ _ q n hq hn
  obtain ⟨hfinite, _, hdegree, hfinrank, _, _, _⟩ :=
    D07.Ch13.Existence.embedded_existence K Ω q n hq hn
  let := hfinite
  let := hdegree
  exact finite_extension_galois_group K _ q n hq hfinrank

end D07.Ch13.GaloisGroup
