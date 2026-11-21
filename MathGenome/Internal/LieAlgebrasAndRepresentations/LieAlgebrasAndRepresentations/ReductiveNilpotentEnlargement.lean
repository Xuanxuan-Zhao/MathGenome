import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ReductiveNilpotentEnlargement
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.LeviDecomposition
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.DiagonalEnlargementStep
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
LA-I09, reductive–nilpotent enlargement. Levi decomposition supplies the
initial semidirect product. Strong induction on the dimension of the
nilradical quotient iterates the diagonal enlargement step.
-/

noncomputable section
universe u

namespace LieAlgebrasAndRepresentations.ReductiveNilpotentEnlargement

open Module LieAlgebra
open Specs.LieAlgebrasAndRepresentations
open Specs.LieAlgebrasAndRepresentations.DiagonalEnlargementStep
open LieAlgebrasAndRepresentations.DiagonalEnlargementStep (idealAdjoint enlargement_step)
open Specs.LieAlgebrasAndRepresentations.ReductiveNilpotentEnlargement

section Semidirect

variable {k : Type*} [Field k]
variable {A B H K : Type*}
  [LieRing A] [LieAlgebra k A] [LieRing B] [LieAlgebra k B]
  [LieRing H] [LieAlgebra k H] [LieRing K] [LieAlgebra k K]

/-- A map of semidirect products from compatible maps of both factors. -/
def semidirectMap
    (θ : H →ₗ⁅k⁆ LieDerivation k A A) (ψ : K →ₗ⁅k⁆ LieDerivation k B B)
    (f : A →ₗ⁅k⁆ B) (g : H →ₗ⁅k⁆ K)
    (h : ∀ x a, f (θ x a) = ψ (g x) (f a)) :
    (A ⋊⁅θ⁆ H) →ₗ⁅k⁆ (B ⋊⁅ψ⁆ K) where
  toFun z := ⟨f z.left, g z.right⟩
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp
  map_lie' := by
    intro x y
    apply SemiDirectSum.ext
    · change f (⁅x.left, y.left⁆ + θ x.right y.left - θ y.right x.left) = _
      simp only [map_sub, map_add, f.map_lie, h]
      rfl
    · exact g.map_lie x.right y.right

theorem semidirectMap_injective
    (θ : H →ₗ⁅k⁆ LieDerivation k A A) (ψ : K →ₗ⁅k⁆ LieDerivation k B B)
    (f : A →ₗ⁅k⁆ B) (g : H →ₗ⁅k⁆ K)
    (h : ∀ x a, f (θ x a) = ψ (g x) (f a))
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (semidirectMap θ ψ f g h) := by
  intro x y he
  exact SemiDirectSum.ext (hf (congrArg SemiDirectSum.left he))
    (hg (congrArg SemiDirectSum.right he))

/-- Reassociation of three direct summands preserves their componentwise bracket. -/
def prodAssoc : ((A × B) × H) ≃ₗ⁅k⁆ (A × (B × H)) where
  __ := LinearEquiv.prodAssoc k A B H
  map_lie' := by intros; rfl

end Semidirect

section IdealComplement

variable {k : Type*} [Field k] {L : Type*} [LieRing L] [LieAlgebra k L]

/-- A subalgebra complementary to an ideal gives the expected semidirect splitting. -/
def idealComplementEquiv (I : LieIdeal k L) (S : LieSubalgebra k L)
    (hc : IsCompl S.toSubmodule I.toSubmodule) :
    (I ⋊⁅(idealAdjoint I).comp S.incl⁆ S) ≃ₗ⁅k⁆ L where
  __ := (SemiDirectSum.toProdl _).trans
    (Submodule.prodEquivOfIsCompl I.toSubmodule S.toSubmodule hc.symm)
  map_lie' := by
    intro x y
    change ⁅(x.left : L), (y.left : L)⁆ + ⁅(x.right : L), (y.left : L)⁆ -
        ⁅(y.right : L), (x.left : L)⁆ + ⁅(x.right : L), (y.right : L)⁆ =
      ⁅(x.left : L) + (x.right : L), (y.left : L) + (y.right : L)⁆
    rw [lie_add, add_lie, add_lie, ← lie_skew (y.right : L) (x.left : L)]
    abel

@[simp] theorem idealComplementEquiv_apply (I : LieIdeal k L)
    (S : LieSubalgebra k L) (hc : IsCompl S.toSubmodule I.toSubmodule)
    (z : I ⋊⁅(idealAdjoint I).comp S.incl⁆ S) :
    idealComplementEquiv I S hc z = (z.left : L) + (z.right : L) := rfl

end IdealComplement

section Terminal

variable (B : Type u) [LieRing B] [LieAlgebra ℂ B] [FiniteDimensional ℂ B]

/-- Zero quotient dimension is exactly the stopping condition needed by the induction. -/
theorem nilpotent_of_quotient_finrank_zero
    (h : finrank ℂ (B ⧸ Nilradical.nilradical_value ℂ B) = 0) :
    LieRing.IsNilpotent B := by
  let I := Nilradical.nilradical_value ℂ B
  have hI : I = ⊤ := by
    apply LieSubmodule.toSubmodule_injective
    apply Submodule.eq_top_of_finrank_eq
    have hd := Submodule.finrank_quotient_add_finrank I.toSubmodule
    change finrank ℂ (B ⧸ I) + finrank ℂ I = finrank ℂ B at hd
    rw [h, zero_add] at hd
    exact hd
  have hn := _root_.LieAlgebrasAndRepresentations.nilradical_nilpotent ℂ B
  change LieRing.IsNilpotent I at hn
  rw [hI] at hn
  letI := hn
  exact (LieIdeal.topEquiv : (⊤ : LieIdeal ℂ B) ≃ₗ⁅ℂ⁆ B).surjective.lieAlgebra_isNilpotent

end Terminal

section Embeddings

variable {G H : Type u} [LieRing G] [LieAlgebra ℂ G]
  [LieRing H] [LieAlgebra ℂ H]

/-- Containment in a constructed enlargement is transitive. -/
def precompose (E : Enlargement H) (f : G →ₗ⁅ℂ⁆ H) (hf : Function.Injective f) :
    Enlargement G where
  S := E.S
  T := E.T
  N := E.N
  semisimple := E.semisimple
  nilpotent := E.nilpotent
  action := E.action
  rank := E.rank
  basis := E.basis
  integer_weights := E.integer_weights
  embedding := E.embedding.comp f
  injective := E.injective.comp hf

end Embeddings

section Initial

variable (G : Type u) [LieRing G] [LieAlgebra ℂ G] [FiniteDimensional ℂ G]

/-- Levi decomposition in the semidirect-product coordinates used in this proof. -/
theorem levi_semidirect :
    ∃ S : LieSubalgebra ℂ G,
      SolvableRadical.IsSemisimple_value ℂ S ∧
      Nonempty ((SolvableRadical.radical_value ℂ G ⋊⁅
        (idealAdjoint (SolvableRadical.radical_value ℂ G)).comp S.incl⁆ S) ≃ₗ⁅ℂ⁆ G) := by
  obtain ⟨S, hs, hc, _⟩ := LeviDecomposition.leviDecomposition ℂ G
  exact ⟨S, hs, ⟨idealComplementEquiv _ S hc⟩⟩

end Initial

section Induction

attribute [local instance 100] LieRing.ofAssociativeRing

variable {S T B : Type u} [LieRing S] [LieAlgebra ℂ S]
  [LieRing T] [LieAlgebra ℂ T] [LieRing B] [LieAlgebra ℂ B]

local instance semidirect_finite [FiniteDimensional ℂ B] [FiniteDimensional ℂ S]
    (θ : S →ₗ⁅ℂ⁆ LieDerivation ℂ B B) : FiniteDimensional ℂ (B ⋊⁅θ⁆ S) :=
  (SemiDirectSum.toProdl θ).symm.finiteDimensional

/-- Reindexing the chosen torus basis reindexes the same integer weights. -/
theorem integerWeights_reindex {ι ι' : Type*} (b : Basis ι ℂ T)
    (ρ : T →ₗ[ℂ] Module.End ℂ B) (e : ι ≃ ι')
    (hw : HasIntegerWeights b ρ) : HasIntegerWeights (b.reindex e) ρ := by
  obtain ⟨n, c, w, hw⟩ := hw
  refine ⟨n, c, fun i j => w i (e.symm j), ?_⟩
  intro i j
  simpa only [Basis.reindex_apply] using hw i (e.symm j)

/-- Iterate the diagonal step until the solvable factor is nilpotent. -/
theorem enlarge_semidirect :
    ∀ (S T B : Type u)
      [LieRing S] [LieAlgebra ℂ S] [FiniteDimensional ℂ S]
      [LieRing T] [LieAlgebra ℂ T] [FiniteDimensional ℂ T] [IsLieAbelian T]
      [LieRing B] [LieAlgebra ℂ B] [FiniteDimensional ℂ B] [LieAlgebra.IsSolvable B]
      (θ : (S × T) →ₗ⁅ℂ⁆ LieDerivation ℂ B B)
      (r : ℕ) (bT : Basis (Fin r) ℂ T),
      SolvableRadical.IsSemisimple_value ℂ S →
      HasIntegerWeights bT (centerAction θ) →
      Nonempty (Enlargement (B ⋊⁅θ⁆ (S × T))) := by
  suffices h : ∀ q : ℕ, ∀ (S T B : Type u)
      [LieRing S] [LieAlgebra ℂ S] [FiniteDimensional ℂ S]
      [LieRing T] [LieAlgebra ℂ T] [FiniteDimensional ℂ T] [IsLieAbelian T]
      [LieRing B] [LieAlgebra ℂ B] [FiniteDimensional ℂ B] [LieAlgebra.IsSolvable B]
      (θ : (S × T) →ₗ⁅ℂ⁆ LieDerivation ℂ B B)
      (r : ℕ) (bT : Basis (Fin r) ℂ T),
      SolvableRadical.IsSemisimple_value ℂ S →
      HasIntegerWeights bT (centerAction θ) →
      finrank ℂ (B ⧸ Nilradical.nilradical_value ℂ B) = q →
      Nonempty (Enlargement (B ⋊⁅θ⁆ (S × T))) by
    intro S T B _ _ _ _ _ _ _ _ _ _ _ θ r bT hs hw
    exact h _ S T B θ r bT hs hw rfl
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro S T B _ _ _ _ _ _ _ _ _ _ _ θ r bT hs hw hq
    by_cases hz : q = 0
    · refine ⟨{
        S := S
        T := T
        N := B
        semisimple := hs
        nilpotent := nilpotent_of_quotient_finrank_zero B (hq.trans hz)
        action := θ
        rank := r
        basis := bT
        integer_weights := hw
        embedding := LieHom.id
        injective := Function.injective_id }⟩
    · have hpos : 0 < finrank ℂ (B ⧸ Nilradical.nilradical_value ℂ B) := by omega
      obtain ⟨E⟩ := enlargement_step S T B θ r bT hs hw hpos
      let U := Torus E.torus.rank
      let T' := T × U
      letI : IsLieAbelian U := ⟨fun x y => by
        change x * y - y * x = 0
        rw [mul_comm, sub_self]⟩
      letI : IsLieAbelian T' := ⟨fun x y => by
        apply Prod.ext
        · exact trivial_lie_zero T T x.1 y.1
        · exact trivial_lie_zero U U x.2 y.2⟩
      letI : LieAlgebra.IsSolvable E.replacement := E.replacement_solvable
      let assoc : ((S × T) × U) ≃ₗ⁅ℂ⁆ S × T' := prodAssoc
      let ψ := E.newAction.comp assoc.symm.toLieHom
      let b := (bT.prod (Pi.basisFun ℂ (Fin E.torus.rank))).reindex finSumFinEquiv
      have hw' : HasIntegerWeights b (centerAction ψ) := by
        apply integerWeights_reindex
        change HasIntegerWeights _ (enlargedCenterAction E.newAction)
        exact E.integer_weights
      have hdrop : finrank ℂ (E.replacement ⧸ Nilradical.nilradical_value ℂ E.replacement) < q := by
        rw [← hq]
        exact E.dimension_drop
      obtain ⟨F⟩ := ih _ hdrop S T' E.replacement ψ _ b hs hw' rfl
      let f := semidirectMap E.newAction ψ LieHom.id assoc.toLieHom
        (fun x a => by
          change E.newAction x a = E.newAction (assoc.symm (assoc x)) a
          rw [assoc.symm_apply_apply])
      have hf : Function.Injective f :=
        semidirectMap_injective _ _ _ _ _ Function.injective_id assoc.injective
      exact ⟨precompose F (f.comp (E.splitting.symm.toLieHom.comp E.oldEmbedding))
        (hf.comp (E.splitting.symm.injective.comp E.oldEmbedding_injective))⟩

end Induction

/-- Every finite-dimensional complex Lie algebra embeds in a semidirect
product of a reductive algebra and a nilpotent algebra, with integral
weights for the abelian summand of the reductive algebra. -/
theorem enlargement : enlargement_type.{u} := by
  intro G _ _ _
  obtain ⟨S, hs, ⟨e⟩⟩ := levi_semidirect G
  let R := SolvableRadical.radical_value ℂ G
  let Z := (⊥ : LieSubalgebra ℂ G)
  letI : Subsingleton Z := LieSubalgebra.subsingleton_bot
  letI : IsLieAbelian Z := ⟨fun _ _ => Subsingleton.elim _ _⟩
  letI : LieAlgebra.IsSolvable R := radical_solvable ℂ G
  let ρ := (idealAdjoint R).comp S.incl
  let θ := ρ.comp (LieHom.fst ℂ S Z)
  let bZ : Basis (Fin 0) ℂ Z := Basis.empty _
  have hw : HasIntegerWeights bZ (centerAction θ) := by
    refine ⟨finrank ℂ R, Module.finBasis ℂ R, fun _ j => Fin.elim0 j, ?_⟩
    intro _ j
    exact Fin.elim0 j
  obtain ⟨E⟩ := enlarge_semidirect S Z R θ 0 bZ hs hw
  let f := semidirectMap ρ θ LieHom.id (LieHom.inl ℂ S Z) (fun _ _ => rfl)
  have hf : Function.Injective f :=
    semidirectMap_injective _ _ _ _ _ Function.injective_id
      (LieHom.inl_injective (R := ℂ) (L₁ := S) (L₂ := Z))
  exact ⟨precompose E (f.comp e.symm.toLieHom) (hf.comp e.symm.injective)⟩

end LieAlgebrasAndRepresentations.ReductiveNilpotentEnlargement
