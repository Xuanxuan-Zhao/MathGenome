import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.StandardParabolicLevi

open CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.TrialitarianMarkedLevi

open AutomorphismSequence (AdjointQuotient SplitSequence relativePoints)
open CharacterDescent (Cocharacter)
open _root_.LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition)
open GeometricRadicals (IsReductive)
open Pinning (AttachedDatum PinnedGroup)
open QuasiSplitInnerForms (outerHom)
open RelativeFormComparison (IsInduced fieldTest transportedAut)
open RootGroups (AdditiveLine)
open StandardParabolicLevi (HasFace)

/-- An aligned finite-level comparison gives the marked face of
the original proper limit parabolic and identifies its actual Levi. -/
def MarkedFace : Prop :=
  ∀ (F S : Type u) [Field F] [Field S] [Algebra F S] [IsSepClosure F S]
    {A : AdditiveLine F} (P : PinnedGroup A) (D : AttachedDatum P.pair)
    {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
    (seq : SplitSequence P D l Q) (G : AffineAlgebraicGroup F), IsReductive G →
    ∀ (a : (groupBaseChange F S).obj P.pair.G.val ≅ (groupBaseChange F S).obj G.val)
      (i : relativePoints P.pair.G.val (fieldTest F S) ≅ relativePoints G.val (fieldTest F S)),
      IsInduced F S a i →
      ∀ (c : Cocharacter G.val) (M : LimitDecomposition c)
        (K₀ : FiniteGaloisIntermediateField F S), ¬ IsIso M.parabolic.inclusion →
        ∃ (K : FiniteGaloisIntermediateField F S)
          (d₀ : Cocharacter P.pair.T.group)
          (M₀ : LimitDecomposition (d₀ ≫ P.pair.T.inclusion))
          (aK : (groupBaseChange F K).obj P.pair.G.val ≅ (groupBaseChange F K).obj G.val)
          (pK : (groupBaseChange F K).obj M₀.parabolic.group ≅
            (groupBaseChange F K).obj M.parabolic.group)
          (lK : (groupBaseChange F K).obj M₀.centralizer.group ≅
            (groupBaseChange F K).obj M.centralizer.group)
          (iK : relativePoints P.pair.G.val (fieldTest F K) ≅ relativePoints G.val (fieldTest F K))
          (J : Set D.toBased.I),
          K₀ ≤ K ∧ IsInduced F K aK iK ∧
          (groupBaseChange F K).map M₀.parabolic.inclusion ≫ aK.hom =
            pK.hom ≫ (groupBaseChange F K).map M.parabolic.inclusion ∧
          (groupBaseChange F K).map M₀.centralizer.inclusion ≫ aK.hom =
            lK.hom ≫ (groupBaseChange F K).map M.centralizer.inclusion ∧
          J ⊂ D.toBased.base.support ∧
          (letI := D.comm; HasFace D.base J d₀) ∧
          (∀ τ : Gal(K/F),
            (outerHom seq (transportedAut F K iK τ)).asIso.hom.val.indexEquiv '' J = J) ∧
          ∀ σ : Gal(S/F),
            outerHom seq (transportedAut F K iK (σ.restrictNormal K)) =
              outerHom seq (transportedAut F S i σ)

end LinearAlgebraicGroups.Specs.Arithmetic.TrialitarianMarkedLevi
