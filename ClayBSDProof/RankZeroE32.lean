import ClayBSDProof.Continuation
import ClayBSDProof.CongruentCurve

/-!
# `y² = x³ − x` tem posto 0

Portado do ATK kernel (espelho público, M-Core commit `390e378`), `ATK/LigacaoBSDTestes.lean`
(`curva32_eliptica`, `dois_torcao`, `posto_curva32`).

`E : y² = x³ − x` (`ClayBSDProof.CongruentCurve.E`) é elíptica (`Δ = 64`). Pela descida de Fermat
(`CongruentCurve.E_point_cases`: `E(ℚ) = {O, (0,0), (1,0), (−1,0)}`), todo ponto racional tem
ordem que divide 2, logo `Module.rank ℤ E(ℚ) = 0`: o posto algébrico do enunciado fixado
(`ClayBSD.algebraicRank`) é `0`. Resultado clássico (Fermat).
-/

namespace ClayBSDProof.RankZeroE32

open ClayBSDProof.Continuation

/-- A curva `y² = x³ − x` como `WeierstrassCurve ℚ` da Mathlib. -/
abbrev E32 : WeierstrassCurve ℚ := ClayBSDProof.CongruentCurve.E

/-- `y² = x³ − x` é elíptica: `Δ = 64`. -/
instance isElliptic_E32 : E32.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by
    norm_num [E32, ClayBSDProof.CongruentCurve.E, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈])⟩

/-- Todo ponto racional de `y² = x³ − x` tem ordem dividindo 2. -/
theorem dois_torcao (P : E32.toAffine.Point) : P + P = 0 := by
  rcases ClayBSDProof.CongruentCurve.E_point_cases P with rfl | ⟨x, h, rfl, -⟩
  · exact add_zero 0
  · exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq (by simp [ClayBSDProof.CongruentCurve.E])

/-- `rank_ℤ E(ℚ) = 0` para `y² = x³ − x`. -/
theorem rank_E32 : Module.rank ℤ E32.toAffine.Point = 0 := by
  rw [rank_eq_zero_iff]
  intro P
  exact ⟨2, two_ne_zero, by rw [two_zsmul]; exact dois_torcao P⟩

/-- **O posto algébrico do enunciado fixado é `0` para `y² = x³ − x`.** -/
theorem algebraicRank_E32 : ClayBSD.algebraicRank E32 = 0 := rank_E32

/-- `postoMW(y² = x³ − x) = 0`. -/
theorem posto_curva32 : postoMW E32 = 0 := by
  unfold postoMW
  rw [rank_E32]
  simp

end ClayBSDProof.RankZeroE32
