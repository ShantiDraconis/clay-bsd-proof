import ClayBSDProof.ModularE32

/-!
# O enunciado fixado `ClayBSD.Statement` para `y² = x³ − x`

`statement_E32 : ClayBSD.Statement E32` — BSD (parte do posto, na forma do enunciado fixado) para
**uma** curva: `E32 : y² = x³ − x` (condutor 32, multiplicação complexa por `ℤ[i]`).

Conteúdo matemático (todo provado no kernel, sem hipóteses):
* a continuação inteira `ModularE32.Lcurva32` de `L(E32, s)` existe (equação funcional de peso 2
  via o caráter de Hecke de `ℚ(i)` e os núcleos de Hurwitz da Mathlib) e a série converge
  absolutamente em `Re s > 3/2` (`ModularE32.lseriesSummable_curva32`);
* `L(E32, 1) ≠ 0` (`AtaqueBSD.L1_ne_zero`: `L(1) = 2c Σ aₙ e^{−cn}/(cn)` e a série tem parte real
  positiva porque `e^{−c} < 1/2`, `|aₙ| ≤ n`), logo a ordem em `s = 1` é `0`;
* `E32(ℚ) = {O, (0,0), (1,0), (−1,0)}` (descida de Fermat), logo `rank_ℤ E32(ℚ) = 0`.

**O que isto é**: o caso de posto analítico 0 de uma curva com multiplicação complexa, coberto
classicamente por Coates–Wiles (1977) (e, para esta curva, já pela descida de Fermat e o cálculo
de `L(E, 1)`). **O que isto não é**: uma prova de `ClayBSD.Conjecture`, que quantifica sobre todas
as curvas elípticas sobre `ℚ`; nada aqui trata posto analítico ≥ 1. `OPEN_MATH = true`.
-/

namespace ClayBSDProof.CaseE32

open ClayBSDProof.Continuation ClayBSDProof.RankZeroE32 ClayBSDProof.ModularE32

/-- A continuação construída satisfaz a definição do enunciado fixado (inclusive a
somabilidade absoluta da série em `Re s > 3/2`). -/
theorem isContinuation_Lcurva32 : ClayBSD.IsContinuation E32 Lcurva32 :=
  (isContinuation_iff E32 Lcurva32).mpr
    ⟨existe_continuacao, fun _ hs => lseriesSummable_curva32 hs⟩

/-- `L(E32, 1) ≠ 0`. -/
theorem Lcurva32_one_ne_zero : Lcurva32 1 ≠ 0 :=
  (bsd_posto_curva32_incondicional existe_continuacao).1

/-- O posto analítico de `y² = x³ − x` é `0`. -/
theorem analyticOrderAt_Lcurva32 : analyticOrderAt Lcurva32 1 = 0 :=
  analyticOrderAt_eq_zero.mpr (Or.inr Lcurva32_one_ne_zero)

/-- **O enunciado fixado de BSD vale para `y² = x³ − x`**: existe a continuação analítica
inteira de `L(E32, s)` e a sua ordem em `s = 1` é o posto de `E32(ℚ)` (ambos `0`). Caso de
posto 0 de Coates–Wiles (1977); não é `ClayBSD.Conjecture`. -/
theorem statement_E32 : ClayBSD.Statement E32 :=
  ⟨Lcurva32, isContinuation_Lcurva32, by
    rw [analyticOrderAt_Lcurva32, algebraicRank_E32]
    simp⟩

/-- Toda continuação (no sentido do enunciado fixado) de `L(E32, s)` é não nula em `s = 1`. -/
theorem continuation_one_ne_zero {L : ℂ → ℂ} (hL : ClayBSD.IsContinuation E32 L) : L 1 ≠ 0 := by
  rw [ClayBSD.continuation_unique E32 hL isContinuation_Lcurva32]
  exact Lcurva32_one_ne_zero

end ClayBSDProof.CaseE32
