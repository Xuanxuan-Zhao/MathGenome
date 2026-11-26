import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.PowerSeriesDiagonal
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.IsolatedTorSupport
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import Mathlib.RingTheory.Length

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace CommutativeAlgebraNotes.Intersection.FieldDiagonalTor

open ExteriorTensorProduct (S includeX)
open PowerSeriesDiagonal
open scoped ExteriorTensorProduct PowerSeriesDiagonal

universe u

abbrev chainShape := ComplexShape.down ℤ

/-- The embedding of nonnegative homological degrees. -/
abbrev nonnegativeEmbedding : (ComplexShape.down ℕ).Embedding chainShape :=
  ComplexShape.embeddingUpNat.op

instance : nonnegativeEmbedding.IsTruncLE where
  rel' i j h := by change (j : ℤ) + 1 = (i : ℤ) at h; change j + 1 = i; omega
  mem_prev {i j} h := by
    change (j : ℤ) + 1 = i at h
    exact ⟨j + 1, by change ((j + 1 : ℕ) : ℤ) = i; omega⟩

abbrev extendChain {A : Type*} [Ring A] (P : ChainComplex (ModuleCat A) ℕ) :=
  P.extend nonnegativeEmbedding

abbrev exteriorTotal (k : Type u) [Field k] (d : ℕ)
    (P Q : ChainComplex (ModuleCat.{u} (R k d)) ℕ) :=
  (exteriorBicomplex k d (extendChain P) (extendChain Q)).total chainShape

abbrev diagonalList (k : Type u) [Field k] (d : ℕ) :=
  List.ofFn (difference k d)

abbrev koszulHomology (k : Type u) [Field k] (d : ℕ)
    (M N : ModuleCat.{u} (R k d)) (i : ℕ) :=
  AdvCommAlg.Koszul.homology (exteriorPair M N) (diagonalList k d) i

/-- The action of the left copy, which agrees with the quotient action
when multiplication by the diagonal ideal vanishes. -/
abbrev restrictLeft (k : Type u) [Field k] (d : ℕ) :
    ModuleCat.{u} (S k d d) ⥤ ModuleCat.{u} (R k d) :=
  ModuleCat.restrictScalars (includeX k d d).toRingHom

namespace Spec

def FiniteFreeResolution : Prop :=
  ∀ (k : Type u) [Field k] (d : ℕ) (M N : ModuleCat.{u} (R k d))
    [Module.Finite (R k d) M] [Module.Finite (R k d) N],
    ∃ (P : ProjectiveResolution M) (Q : ProjectiveResolution N),
      (∀ i, Module.Free (R k d) (P.complex.X i) ∧ Module.Finite (R k d) (P.complex.X i)) ∧
      (∀ i, Module.Free (R k d) (Q.complex.X i) ∧ Module.Finite (R k d) (Q.complex.X i)) ∧
      (∀ i : ℕ, d < i → Subsingleton (P.complex.X i) ∧ Subsingleton (Q.complex.X i)) ∧
      let C := exteriorTotal k d P.complex Q.complex
      ∃ ε : C ⟶ (HomologicalComplex.single _ chainShape 0).obj (exteriorPair M N),
        QuasiIso ε ∧
        (∀ i : ℤ, Module.Free (S k d d) (C.X i) ∧ Module.Finite (S k d d) (C.X i)) ∧
        (∀ i : ℤ, i < 0 ∨ (2 * d : ℤ) < i → IsZero (C.X i)) ∧
        Nonempty ((extendDiagonal k d |>.mapHomologicalComplex chainShape).obj C ≅
          (ordinaryBicomplex k d (extendChain P.complex) (extendChain Q.complex)).total chainShape)

def DiagonalAction : Prop :=
  ∀ (k : Type u) [Field k] (d : ℕ) (M N : ModuleCat.{u} (R k d)) (i : ℕ)
    (s : S k d d) (x : koszulHomology k d M N i),
    s • x = includeX k d d (identify k d s) • x

def HomologyTor : Prop :=
  ∀ (k : Type u) [Field k] (d : ℕ) (M N : ModuleCat.{u} (R k d))
    [Module.Finite (R k d) M] [Module.Finite (R k d) N] (i : ℕ),
    Nonempty (↥((restrictLeft k d).obj (koszulHomology k d M N i)) ≃ₗ[R k d]
      IsolatedTorSupport.Specs.Tor M N i)

def LengthComparison : Prop :=
  ∀ (k : Type u) [Field k] (d : ℕ) (M N : ModuleCat.{u} (R k d))
    [Module.Finite (R k d) M] [Module.Finite (R k d) N] (i : ℕ),
    Module.length (S k d d) (koszulHomology k d M N i) =
      Module.length (R k d) (IsolatedTorSupport.Specs.Tor M N i)

def TensorQuotientLength : Prop :=
  ∀ (k : Type u) [Field k] (d : ℕ) (M N : ModuleCat.{u} (R k d)),
    Module.length (S k d d) (diagonalReduction k d (exteriorPair M N)) =
      Module.length (R k d) (M ⊗[R k d] N)

def IsolatedFiniteLength : Prop :=
  ∀ (k : Type u) [Field k] (d : ℕ) (M N : ModuleCat.{u} (R k d))
    [Module.Finite (R k d) M] [Module.Finite (R k d) N],
    IsFiniteLength (R k d) (M ⊗[R k d] N) →
      IsFiniteLength (S k d d) (diagonalReduction k d (exteriorPair M N)) ∧
        ∀ i : ℕ, IsFiniteLength (S k d d) (koszulHomology k d M N i)

end Spec
end CommutativeAlgebraNotes.Intersection.FieldDiagonalTor
