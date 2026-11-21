import MathGenome.Internal.Specs.D07.Ch13.Embeddings
import Mathlib.FieldTheory.Finite.GaloisField

/-!
Embeddings over a shared finite base, K07.13.embeddings.

Finite vector-space degree over finite K makes E and L finite sets. The
library's finite-field embedding criterion then applies to these exact
Algebra structures. Its converse constructs an embedding by splitting-field
lifting; the forward direction uses the tower degree formula. Its counting
theorem identifies embeddings with automorphisms of the finite normal,
separable source field over K. Thus it counts maps preserving the chosen
base, not merely field maps preserving the characteristic.
-/

universe u v w

namespace D07.Ch13.Embeddings

open Specs.D07.Ch13.Embeddings

theorem finite_embeddings : FiniteEmbeddings.{u, v, w} := by
  intro K E L _ _ _ _ _ _ _ _
  have : Finite E := Module.finite_of_finite K
  have : Finite L := Module.finite_of_finite K
  infer_instance

theorem embedding_exists_iff : EmbeddingExistsIff.{u, v, w} := by
  intro K E L _ _ _ _ _ _ _ _ a b ha hb
  have : Finite L := Module.finite_of_finite K
  simpa only [ha, hb] using
    (FiniteField.nonempty_algHom_iff_finrank_dvd (F := K) (K := E) (L := L))

theorem embedding_count : EmbeddingCount.{u, v, w} := by
  intro K E L _ _ _ _ _ _ _ _ a b ha hb h
  have : Finite L := Module.finite_of_finite K
  have hdvd := (embedding_exists_iff K E L a b ha hb).mp h
  rw [← ha, ← hb] at hdvd
  exact (FiniteField.natCard_algHom_of_finrank_dvd hdvd).trans ha

end D07.Ch13.Embeddings
