import ClayBSDProof.FermatRightTriangle
import ClayBSDProof.CongruentCurve
import ClayBSDProof.Continuation
import ClayBSDProof.RankZeroE32
import ClayBSDProof.MellinFold
import ClayBSDProof.AtaqueBSD
import ClayBSDProof.HasseE32
import ClayBSDProof.CoefBoundE32
import ClayBSDProof.GoodReductionE32
import ClayBSDProof.LocalFactorsE32
import ClayBSDProof.GaussPrimary
import ClayBSDProof.HeckeCharE32
import ClayBSDProof.ModularE32
import ClayBSDProof.CaseE32
import ClayBSDProof.MordellWeil.ChangeOfVariables
import ClayBSDProof.MordellWeil.Field
import ClayBSDProof.MordellWeil.SelmerFinite
import ClayBSDProof.MordellWeil.WeakNumberField
import ClayBSDProof.MordellWeil
import ClayBSDProof.RankDecomposition

/-!
# Auditoria de axiomas

Um `#guard_msgs` por declaração pública nova, com a saída real de `#print axioms`. Se aparecer
qualquer axioma diferente de `propext`, `Classical.choice` e `Quot.sound` (inclusive `sorryAx`),
a compilação falha. `Classical.choice` vem do Mathlib (`#print axioms Real` já o contém).

Declarações-chave: `ClayBSDProof.CaseE32.statement_E32` (o enunciado fixado para
`y² = x³ − x`), `ClayBSDProof.MordellWeil.mordellWeil_fg`, `ClayBSDProof.RankDecomposition.conjecture_iff`.
-/


/-! ## `ClayBSDProof.FermatRightTriangle` -/

/-- info: 'ClayBSDProof.FermatRightTriangle.FermatM42' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayBSDProof.FermatRightTriangle.FermatM42

/-- info: 'ClayBSDProof.FermatRightTriangle.FermatM42.Minimal' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayBSDProof.FermatRightTriangle.FermatM42.Minimal

/-- info: 'ClayBSDProof.FermatRightTriangle.FermatM42.a_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.FermatRightTriangle.FermatM42.a_ne_zero

/-- info: 'ClayBSDProof.FermatRightTriangle.FermatM42.coprime_of_minimal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.FermatRightTriangle.FermatM42.coprime_of_minimal

/-- info: 'ClayBSDProof.FermatRightTriangle.FermatM42.exists_minimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.FermatRightTriangle.FermatM42.exists_minimal

/-- info: 'ClayBSDProof.FermatRightTriangle.FermatM42.exists_pos_minimal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.FermatRightTriangle.FermatM42.exists_pos_minimal

/-- info: 'ClayBSDProof.FermatRightTriangle.FermatM42.neg_a' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.FermatRightTriangle.FermatM42.neg_a

/-- info: 'ClayBSDProof.FermatRightTriangle.FermatM42.not_minimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.FermatRightTriangle.FermatM42.not_minimal

/-- info: 'ClayBSDProof.FermatRightTriangle.FermatM42.of_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.FermatRightTriangle.FermatM42.of_mul

/-- info: 'ClayBSDProof.FermatRightTriangle.descent_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.FermatRightTriangle.descent_even

/-- info: 'ClayBSDProof.FermatRightTriangle.descent_even_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.FermatRightTriangle.descent_even_core

/-- info: 'ClayBSDProof.FermatRightTriangle.descent_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.FermatRightTriangle.descent_odd

/-- info: 'ClayBSDProof.FermatRightTriangle.fermat_right_triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.FermatRightTriangle.fermat_right_triangle

/-- info: 'ClayBSDProof.FermatRightTriangle.isCoprime_sq_sub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.FermatRightTriangle.isCoprime_sq_sub

/-- info: 'ClayBSDProof.FermatRightTriangle.not_fermat_4m4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.FermatRightTriangle.not_fermat_4m4

/-- info: 'ClayBSDProof.FermatRightTriangle.not_fourth_add_sq_eq_fourth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.FermatRightTriangle.not_fourth_add_sq_eq_fourth

/-- info: 'ClayBSDProof.FermatRightTriangle.not_sq_add_and_sub_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.FermatRightTriangle.not_sq_add_and_sub_sq

/-- info: 'ClayBSDProof.FermatRightTriangle.one_not_congruent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.FermatRightTriangle.one_not_congruent

/-- info: 'ClayBSDProof.FermatRightTriangle.sq_ne_two_mul_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.FermatRightTriangle.sq_ne_two_mul_sq

/-- info: 'ClayBSDProof.FermatRightTriangle.sq_ne_two_mul_sq_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.FermatRightTriangle.sq_ne_two_mul_sq_aux


/-! ## `ClayBSDProof.CongruentCurve` -/

/-- info: 'ClayBSDProof.CongruentCurve.E' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.CongruentCurve.E

/-- info: 'ClayBSDProof.CongruentCurve.E_equation_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.CongruentCurve.E_equation_iff

/-- info: 'ClayBSDProof.CongruentCurve.E_nonsingular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.CongruentCurve.E_nonsingular

/-- info: 'ClayBSDProof.CongruentCurve.E_point_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.CongruentCurve.E_point_cases

/-- info: 'ClayBSDProof.CongruentCurve.E_torsion_points' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.CongruentCurve.E_torsion_points

/-- info: 'ClayBSDProof.CongruentCurve.fermatM42_iff_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.CongruentCurve.fermatM42_iff_point

/-- info: 'ClayBSDProof.CongruentCurve.point_of_fermatM42' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.CongruentCurve.point_of_fermatM42

/-- info: 'ClayBSDProof.CongruentCurve.rational_points' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.CongruentCurve.rational_points

/-- info: 'ClayBSDProof.CongruentCurve.rational_points_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.CongruentCurve.rational_points_iff

/-- info: 'ClayBSDProof.CongruentCurve.y_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.CongruentCurve.y_eq_zero


/-! ## `ClayBSDProof.Continuation` -/

/-- info: 'ClayBSDProof.Continuation.Continuacao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.Continuation.Continuacao

/-- info: 'ClayBSDProof.Continuation.LFunction_um' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.Continuation.LFunction_um

/-- info: 'ClayBSDProof.Continuation.algebraicRank_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.Continuation.algebraicRank_eq_zero_iff

/-- info: 'ClayBSDProof.Continuation.coef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.Continuation.coef

/-- info: 'ClayBSDProof.Continuation.coef_um' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.Continuation.coef_um

/-- info: 'ClayBSDProof.Continuation.continuacao_unica' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.Continuation.continuacao_unica

/-- info: 'ClayBSDProof.Continuation.fator_multiplicativo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.Continuation.fator_multiplicativo

/-- info: 'ClayBSDProof.Continuation.isContinuation_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.Continuation.isContinuation_iff

/-- info: 'ClayBSDProof.Continuation.lseries_coef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.Continuation.lseries_coef

/-- info: 'ClayBSDProof.Continuation.postoMW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.Continuation.postoMW


/-! ## `ClayBSDProof.RankZeroE32` -/

/-- info: 'ClayBSDProof.RankZeroE32.E32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.RankZeroE32.E32

/-- info: 'ClayBSDProof.RankZeroE32.algebraicRank_E32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.RankZeroE32.algebraicRank_E32

/-- info: 'ClayBSDProof.RankZeroE32.dois_torcao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.RankZeroE32.dois_torcao

/-- info: 'ClayBSDProof.RankZeroE32.isElliptic_E32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.RankZeroE32.isElliptic_E32

/-- info: 'ClayBSDProof.RankZeroE32.posto_curva32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.RankZeroE32.posto_curva32

/-- info: 'ClayBSDProof.RankZeroE32.rank_E32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.RankZeroE32.rank_E32


/-! ## `ClayBSDProof.MellinFold` -/

/-- info: 'ClayBSDProof.MellinFold.cauda' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MellinFold.cauda

/-- info: 'ClayBSDProof.MellinFold.f_modif_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MellinFold.f_modif_eq

/-- info: 'ClayBSDProof.MellinFold.mellinConvergent_cauda' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MellinFold.mellinConvergent_cauda

/-- info: 'ClayBSDProof.MellinFold.mellinConvergent_f_modif' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MellinFold.mellinConvergent_f_modif

/-- info: 'ClayBSDProof.MellinFold.Λ₀_eq_caudas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MellinFold.Λ₀_eq_caudas


/-! ## `ClayBSDProof.AtaqueBSD` -/

/-- info: 'ClayBSDProof.AtaqueBSD.CotaCoef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.CotaCoef

/-- info: 'ClayBSDProof.AtaqueBSD.L1_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.L1_ne_zero

/-- info: 'ClayBSDProof.AtaqueBSD.Lc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.Lc

/-- info: 'ClayBSDProof.AtaqueBSD.Lc_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.Lc_eq

/-- info: 'ClayBSDProof.AtaqueBSD.Lc_um' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.Lc_um

/-- info: 'ClayBSDProof.AtaqueBSD.PonteModular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.PonteModular

/-- info: 'ClayBSDProof.AtaqueBSD.bsd_posto_curva32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.bsd_posto_curva32

/-- info: 'ClayBSDProof.AtaqueBSD.c32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.c32

/-- info: 'ClayBSDProof.AtaqueBSD.c32_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.c32_pos

/-- info: 'ClayBSDProof.AtaqueBSD.clay_curva32_de_pontes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.clay_curva32_de_pontes

/-- info: 'ClayBSDProof.AtaqueBSD.coef_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.coef_zero

/-- info: 'ClayBSDProof.AtaqueBSD.continuacao_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.continuacao_eq

/-- info: 'ClayBSDProof.AtaqueBSD.continuousOn_teta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.continuousOn_teta

/-- info: 'ClayBSDProof.AtaqueBSD.cota_integral_termo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.cota_integral_termo

/-- info: 'ClayBSDProof.AtaqueBSD.differentiable_Lc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.differentiable_Lc

/-- info: 'ClayBSDProof.AtaqueBSD.exp_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.exp_nat

/-- info: 'ClayBSDProof.AtaqueBSD.exp_neg_c32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.exp_neg_c32

/-- info: 'ClayBSDProof.AtaqueBSD.exp_neg_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.exp_neg_lt_one

/-- info: 'ClayBSDProof.AtaqueBSD.integrable_mellin_termo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.integrable_mellin_termo

/-- info: 'ClayBSDProof.AtaqueBSD.integrable_termo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.integrable_termo

/-- info: 'ClayBSDProof.AtaqueBSD.integral_exp_Ioi_um' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.integral_exp_Ioi_um

/-- info: 'ClayBSDProof.AtaqueBSD.integral_mellin_termo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.integral_mellin_termo

/-- info: 'ClayBSDProof.AtaqueBSD.integral_norm_mellin_termo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.integral_norm_mellin_termo

/-- info: 'ClayBSDProof.AtaqueBSD.integral_norm_termo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.integral_norm_termo

/-- info: 'ClayBSDProof.AtaqueBSD.integral_termo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.integral_termo

/-- info: 'ClayBSDProof.AtaqueBSD.integral_teta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.integral_teta

/-- info: 'ClayBSDProof.AtaqueBSD.mellin_teta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.mellin_teta

/-- info: 'ClayBSDProof.AtaqueBSD.norm_termo_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.norm_termo_le

/-- info: 'ClayBSDProof.AtaqueBSD.par' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.par

/-- info: 'ClayBSDProof.AtaqueBSD.par_forte' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.par_forte

/-- info: 'ClayBSDProof.AtaqueBSD.serie_re_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.serie_re_pos

/-- info: 'ClayBSDProof.AtaqueBSD.summable_maj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.summable_maj

/-- info: 'ClayBSDProof.AtaqueBSD.summable_serie' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.summable_serie

/-- info: 'ClayBSDProof.AtaqueBSD.summable_teta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.summable_teta

/-- info: 'ClayBSDProof.AtaqueBSD.teta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.teta

/-- info: 'ClayBSDProof.AtaqueBSD.teta_isBigO_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.teta_isBigO_exp

/-- info: 'ClayBSDProof.AtaqueBSD.teta_isBigO_rpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.teta_isBigO_rpow

/-- info: 'ClayBSDProof.AtaqueBSD.um_lt_c32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.um_lt_c32

/-- info: 'ClayBSDProof.AtaqueBSD.Λ₀_eq_mellin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.Λ₀_eq_mellin

/-- info: 'ClayBSDProof.AtaqueBSD.Λ₀_um' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.AtaqueBSD.Λ₀_um


/-! ## `ClayBSDProof.HasseE32` -/

/-- info: 'ClayBSDProof.HasseE32.S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HasseE32.S

/-- info: 'ClayBSDProof.HasseE32.S_escala' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HasseE32.S_escala

/-- info: 'ClayBSDProof.HasseE32.S_sq_classe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HasseE32.S_sq_classe

/-- info: 'ClayBSDProof.HasseE32.S_sq_escala' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HasseE32.S_sq_escala

/-- info: 'ClayBSDProof.HasseE32.S_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HasseE32.S_zero

/-- info: 'ClayBSDProof.HasseE32.card_afim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HasseE32.card_afim

/-- info: 'ClayBSDProof.HasseE32.chi_cubo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HasseE32.chi_cubo

/-- info: 'ClayBSDProof.HasseE32.chi_sq_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HasseE32.chi_sq_eq_one

/-- info: 'ClayBSDProof.HasseE32.hasse_curva32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HasseE32.hasse_curva32

/-- info: 'ClayBSDProof.HasseE32.hasse_pontos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HasseE32.hasse_pontos

/-- info: 'ClayBSDProof.HasseE32.soma_AB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HasseE32.soma_AB

/-- info: 'ClayBSDProof.HasseE32.soma_S_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HasseE32.soma_S_sq

/-- info: 'ClayBSDProof.HasseE32.soma_desloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HasseE32.soma_desloc

/-- info: 'ClayBSDProof.HasseE32.soma_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HasseE32.soma_diag

/-- info: 'ClayBSDProof.HasseE32.soma_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HasseE32.soma_diagonal

/-- info: 'ClayBSDProof.HasseE32.soma_interna' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HasseE32.soma_interna

/-- info: 'ClayBSDProof.HasseE32.soma_par' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HasseE32.soma_par

/-- info: 'ClayBSDProof.HasseE32.traco_eq_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HasseE32.traco_eq_S

/-- info: 'ClayBSDProof.HasseE32.traco_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HasseE32.traco_zero


/-! ## `ClayBSDProof.CoefBoundE32` -/

/-- info: 'ClayBSDProof.CoefBoundE32.FatoresPadrao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.CoefBoundE32.FatoresPadrao

/-- info: 'ClayBSDProof.CoefBoundE32.bsd_posto_curva32_P1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.CoefBoundE32.bsd_posto_curva32_P1

/-- info: 'ClayBSDProof.CoefBoundE32.cotaCoef_de_fatores' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.CoefBoundE32.cotaCoef_de_fatores

/-- info: 'ClayBSDProof.CoefBoundE32.cota_forma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.CoefBoundE32.cota_forma

/-- info: 'ClayBSDProof.CoefBoundE32.cota_hecke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.CoefBoundE32.cota_hecke

/-- info: 'ClayBSDProof.CoefBoundE32.cota_hecke_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.CoefBoundE32.cota_hecke_zero

/-- info: 'ClayBSDProof.CoefBoundE32.cota_inteira' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.CoefBoundE32.cota_inteira

/-- info: 'ClayBSDProof.CoefBoundE32.cota_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.CoefBoundE32.cota_local

/-- info: 'ClayBSDProof.CoefBoundE32.cota_pot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.CoefBoundE32.cota_pot

/-- info: 'ClayBSDProof.CoefBoundE32.hecke' does not depend on any axioms -/
#guard_msgs in #print axioms ClayBSDProof.CoefBoundE32.hecke

/-- info: 'ClayBSDProof.CoefBoundE32.invariante' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.CoefBoundE32.invariante

/-- info: 'ClayBSDProof.CoefBoundE32.lfun_mult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.CoefBoundE32.lfun_mult

/-- info: 'ClayBSDProof.CoefBoundE32.sq_ne_quatro_p' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.CoefBoundE32.sq_ne_quatro_p

/-- info: 'ClayBSDProof.CoefBoundE32.traco' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.CoefBoundE32.traco

/-- info: 'ClayBSDProof.CoefBoundE32.traco_tres' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.CoefBoundE32.traco_tres


/-! ## `ClayBSDProof.GoodReductionE32` -/

/-- info: 'ClayBSDProof.GoodReductionE32.boa_E32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GoodReductionE32.boa_E32

/-- info: 'ClayBSDProof.GoodReductionE32.boa_reducao_de_unidade' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GoodReductionE32.boa_reducao_de_unidade

/-- info: 'ClayBSDProof.GoodReductionE32.dois_unidade' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GoodReductionE32.dois_unidade


/-! ## `ClayBSDProof.LocalFactorsE32` -/

/-- info: 'ClayBSDProof.LocalFactorsE32.E32' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.E32

/-- info: 'ClayBSDProof.LocalFactorsE32.E32_c₆' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.E32_c₆

/-- info: 'ClayBSDProof.LocalFactorsE32.E32_equation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.E32_equation

/-- info: 'ClayBSDProof.LocalFactorsE32.E32_Δ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.E32_Δ

/-- info: 'ClayBSDProof.LocalFactorsE32.E_baseChange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.E_baseChange

/-- info: 'ClayBSDProof.LocalFactorsE32.Kv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.Kv

/-- info: 'ClayBSDProof.LocalFactorsE32.Nula' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.Nula

/-- info: 'ClayBSDProof.LocalFactorsE32.Rv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.Rv

/-- info: 'ClayBSDProof.LocalFactorsE32.Wv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.Wv

/-- info: 'ClayBSDProof.LocalFactorsE32.bsd_posto_curva32_modP1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.bsd_posto_curva32_modP1

/-- info: 'ClayBSDProof.LocalFactorsE32.card_E32_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.card_E32_equiv

/-- info: 'ClayBSDProof.LocalFactorsE32.card_E32_zmod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.card_E32_zmod

/-- info: 'ClayBSDProof.LocalFactorsE32.card_pontos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.card_pontos

/-- info: 'ClayBSDProof.LocalFactorsE32.card_reducao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.card_reducao

/-- info: 'ClayBSDProof.LocalFactorsE32.card_residuo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.card_residuo

/-- info: 'ClayBSDProof.LocalFactorsE32.card_vc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.card_vc

/-- info: 'ClayBSDProof.LocalFactorsE32.coef_inv_quad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.coef_inv_quad

/-- info: 'ClayBSDProof.LocalFactorsE32.coef_inv_um' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.coef_inv_um

/-- info: 'ClayBSDProof.LocalFactorsE32.cotaCoef_curva32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.cotaCoef_curva32

/-- info: 'ClayBSDProof.LocalFactorsE32.c₆_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.c₆_E

/-- info: 'ClayBSDProof.LocalFactorsE32.dois_irredutivel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.dois_irredutivel

/-- info: 'ClayBSDProof.LocalFactorsE32.dois_nao_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.dois_nao_mem

/-- info: 'ClayBSDProof.LocalFactorsE32.equation_vc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.equation_vc

/-- info: 'ClayBSDProof.LocalFactorsE32.fatoresPadrao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.fatoresPadrao

/-- info: 'ClayBSDProof.LocalFactorsE32.instFactPrimeValNat_clayBSDProof' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.instFactPrimeValNat_clayBSDProof

/-- info: 'ClayBSDProof.LocalFactorsE32.instFactPrimes' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.instFactPrimes

/-- info: 'ClayBSDProof.LocalFactorsE32.instFactPrimes'' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.instFactPrimes'

/-- info: 'ClayBSDProof.LocalFactorsE32.integral_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.integral_E

/-- info: 'ClayBSDProof.LocalFactorsE32.lfun_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.lfun_eq

/-- info: 'ClayBSDProof.LocalFactorsE32.lfun_pot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.lfun_pot

/-- info: 'ClayBSDProof.LocalFactorsE32.lugar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.lugar

/-- info: 'ClayBSDProof.LocalFactorsE32.mul_pot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.mul_pot

/-- info: 'ClayBSDProof.LocalFactorsE32.nao_boa_dois' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.nao_boa_dois

/-- info: 'ClayBSDProof.LocalFactorsE32.nao_mult_dois' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.nao_mult_dois

/-- info: 'ClayBSDProof.LocalFactorsE32.natGenerator_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.natGenerator_inj

/-- info: 'ClayBSDProof.LocalFactorsE32.natGenerator_lugar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.natGenerator_lugar

/-- info: 'ClayBSDProof.LocalFactorsE32.northcott_residuo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.northcott_residuo

/-- info: 'ClayBSDProof.LocalFactorsE32.nula_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.nula_mul

/-- info: 'ClayBSDProof.LocalFactorsE32.nula_ofPowerSeries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.nula_ofPowerSeries

/-- info: 'ClayBSDProof.LocalFactorsE32.nula_um' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.nula_um

/-- info: 'ClayBSDProof.LocalFactorsE32.reducao_vc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.reducao_vc

/-- info: 'ClayBSDProof.LocalFactorsE32.residuoEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.residuoEquiv

/-- info: 'ClayBSDProof.LocalFactorsE32.serieLocal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.serieLocal

/-- info: 'ClayBSDProof.LocalFactorsE32.serie_dois' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.serie_dois

/-- info: 'ClayBSDProof.LocalFactorsE32.serie_impar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.serie_impar

/-- info: 'ClayBSDProof.LocalFactorsE32.transf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.transf

/-- info: 'ClayBSDProof.LocalFactorsE32.u_unidade' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.u_unidade

/-- info: 'ClayBSDProof.LocalFactorsE32.unidade_de_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.unidade_de_val

/-- info: 'ClayBSDProof.LocalFactorsE32.val_dois' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.val_dois

/-- info: 'ClayBSDProof.LocalFactorsE32.val_Δ_impar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.val_Δ_impar

/-- info: 'ClayBSDProof.LocalFactorsE32.Δ_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.LocalFactorsE32.Δ_E


/-! ## `ClayBSDProof.GaussPrimary` -/

/-- info: 'ClayBSDProof.GaussPrimary.Prim' does not depend on any axioms -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.Prim

/-- info: 'ClayBSDProof.GaussPrimary.coprimo_de_normas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.coprimo_de_normas

/-- info: 'ClayBSDProof.GaussPrimary.existe_prim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.existe_prim

/-- info: 'ClayBSDProof.GaussPrimary.hecke_zero_impar' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.hecke_zero_impar

/-- info: 'ClayBSDProof.GaussPrimary.hecke_zero_par' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.hecke_zero_par

/-- info: 'ClayBSDProof.GaussPrimary.instDecidablePredGaussianIntPrim' does not depend on any axioms -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.instDecidablePredGaussianIntPrim

/-- info: 'ClayBSDProof.GaussPrimary.irred_de_norma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.irred_de_norma

/-- info: 'ClayBSDProof.GaussPrimary.isUnit_i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.isUnit_i

/-- info: 'ClayBSDProof.GaussPrimary.isUnit_menos_i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.isUnit_menos_i

/-- info: 'ClayBSDProof.GaussPrimary.mem_primN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.mem_primN

/-- info: 'ClayBSDProof.GaussPrimary.norma' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.norma

/-- info: 'ClayBSDProof.GaussPrimary.norma_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.norma_assoc

/-- info: 'ClayBSDProof.GaussPrimary.norma_dvd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.norma_dvd

/-- info: 'ClayBSDProof.GaussPrimary.norma_natCast' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.norma_natCast

/-- info: 'ClayBSDProof.GaussPrimary.norma_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.norma_nonneg

/-- info: 'ClayBSDProof.GaussPrimary.norma_pow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.norma_pow

/-- info: 'ClayBSDProof.GaussPrimary.norma_unidade' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.norma_unidade

/-- info: 'ClayBSDProof.GaussPrimary.primN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.primN

/-- info: 'ClayBSDProof.GaussPrimary.primN_um' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.primN_um

/-- info: 'ClayBSDProof.GaussPrimary.primN_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.primN_zero

/-- info: 'ClayBSDProof.GaussPrimary.prim_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.prim_assoc

/-- info: 'ClayBSDProof.GaussPrimary.prim_de_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.prim_de_mul

/-- info: 'ClayBSDProof.GaussPrimary.prim_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.prim_iff

/-- info: 'ClayBSDProof.GaussPrimary.prim_menos_p' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.prim_menos_p

/-- info: 'ClayBSDProof.GaussPrimary.prim_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.prim_mul

/-- info: 'ClayBSDProof.GaussPrimary.prim_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.prim_ne_zero

/-- info: 'ClayBSDProof.GaussPrimary.prim_norma_impar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.prim_norma_impar

/-- info: 'ClayBSDProof.GaussPrimary.prim_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.prim_one

/-- info: 'ClayBSDProof.GaussPrimary.prim_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.prim_pow

/-- info: 'ClayBSDProof.GaussPrimary.prim_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.prim_star

/-- info: 'ClayBSDProof.GaussPrimary.prim_unidade' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.prim_unidade

/-- info: 'ClayBSDProof.GaussPrimary.somaGeo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.somaGeo

/-- info: 'ClayBSDProof.GaussPrimary.somaGeo_hecke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.somaGeo_hecke

/-- info: 'ClayBSDProof.GaussPrimary.somaGeo_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.somaGeo_succ

/-- info: 'ClayBSDProof.GaussPrimary.somaPrim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.somaPrim

/-- info: 'ClayBSDProof.GaussPrimary.somaPrim_decomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.somaPrim_decomp

/-- info: 'ClayBSDProof.GaussPrimary.somaPrim_dois' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.somaPrim_dois

/-- info: 'ClayBSDProof.GaussPrimary.somaPrim_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.somaPrim_mul

/-- info: 'ClayBSDProof.GaussPrimary.somaPrim_tres' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.somaPrim_tres

/-- info: 'ClayBSDProof.GaussPrimary.somaPrim_um' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.somaPrim_um

/-- info: 'ClayBSDProof.GaussPrimary.somaPrim_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.somaPrim_zero

/-- info: 'ClayBSDProof.GaussPrimary.unidade_coord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.GaussPrimary.unidade_coord


/-! ## `ClayBSDProof.HeckeCharE32` -/

/-- info: 'ClayBSDProof.HeckeCharE32.card_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HeckeCharE32.card_E

/-- info: 'ClayBSDProof.HeckeCharE32.coefG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HeckeCharE32.coefG

/-- info: 'ClayBSDProof.HeckeCharE32.coefG_mult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HeckeCharE32.coefG_mult

/-- info: 'ClayBSDProof.HeckeCharE32.coef_gauss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HeckeCharE32.coef_gauss

/-- info: 'ClayBSDProof.HeckeCharE32.dois_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HeckeCharE32.dois_ne

/-- info: 'ClayBSDProof.HeckeCharE32.existe_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HeckeCharE32.existe_pi

/-- info: 'ClayBSDProof.HeckeCharE32.ns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HeckeCharE32.ns

/-- info: 'ClayBSDProof.HeckeCharE32.oito_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HeckeCharE32.oito_dvd

/-- info: 'ClayBSDProof.HeckeCharE32.oito_dvd_traco' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HeckeCharE32.oito_dvd_traco

/-- info: 'ClayBSDProof.HeckeCharE32.quadrado_traco' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HeckeCharE32.quadrado_traco

/-- info: 'ClayBSDProof.HeckeCharE32.somaG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HeckeCharE32.somaG

/-- info: 'ClayBSDProof.HeckeCharE32.somaG_mult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HeckeCharE32.somaG_mult

/-- info: 'ClayBSDProof.HeckeCharE32.some_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HeckeCharE32.some_inj

/-- info: 'ClayBSDProof.HeckeCharE32.traco_tres' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HeckeCharE32.traco_tres

/-- info: 'ClayBSDProof.HeckeCharE32.Δ_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.HeckeCharE32.Δ_ne


/-! ## `ClayBSDProof.ModularE32` -/

/-- info: 'ClayBSDProof.ModularE32.A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.A

/-- info: 'ClayBSDProof.ModularE32.At' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.At

/-- info: 'ClayBSDProof.ModularE32.K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.K

/-- info: 'ClayBSDProof.ModularE32.K_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.K_pos

/-- info: 'ClayBSDProof.ModularE32.K_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.K_sq

/-- info: 'ClayBSDProof.ModularE32.Lcurva32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.Lcurva32

/-- info: 'ClayBSDProof.ModularE32.T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.T

/-- info: 'ClayBSDProof.ModularE32.Tt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.Tt

/-- info: 'ClayBSDProof.ModularE32.U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.U

/-- info: 'ClayBSDProof.ModularE32.Ut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.Ut

/-- info: 'ClayBSDProof.ModularE32.V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.V

/-- info: 'ClayBSDProof.ModularE32.Vt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.Vt

/-- info: 'ClayBSDProof.ModularE32.abscissa_curva32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.abscissa_curva32

/-- info: 'ClayBSDProof.ModularE32.bsd_posto_curva32_completo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.bsd_posto_curva32_completo

/-- info: 'ClayBSDProof.ModularE32.bsd_posto_curva32_incondicional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.bsd_posto_curva32_incondicional

/-- info: 'ClayBSDProof.ModularE32.c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.c

/-- info: 'ClayBSDProof.ModularE32.c_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.c_pos

/-- info: 'ClayBSDProof.ModularE32.c_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.c_sq

/-- info: 'ClayBSDProof.ModularE32.caixa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.caixa

/-- info: 'ClayBSDProof.ModularE32.coef_caixa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.coef_caixa

/-- info: 'ClayBSDProof.ModularE32.cos_pi_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.cos_pi_int

/-- info: 'ClayBSDProof.ModularE32.cos_quarto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.cos_quarto

/-- info: 'ClayBSDProof.ModularE32.cota_caixa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.cota_caixa

/-- info: 'ClayBSDProof.ModularE32.equacao_UV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.equacao_UV

/-- info: 'ClayBSDProof.ModularE32.equacao_funcional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.equacao_funcional

/-- info: 'ClayBSDProof.ModularE32.existe_continuacao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.existe_continuacao

/-- info: 'ClayBSDProof.ModularE32.f' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.f

/-- info: 'ClayBSDProof.ModularE32.fat_ab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.fat_ab

/-- info: 'ClayBSDProof.ModularE32.fat_uw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.fat_uw

/-- info: 'ClayBSDProof.ModularE32.fibra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.fibra

/-- info: 'ClayBSDProof.ModularE32.hasSum_A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.hasSum_A

/-- info: 'ClayBSDProof.ModularE32.hasSum_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.hasSum_T

/-- info: 'ClayBSDProof.ModularE32.hasSum_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.hasSum_U

/-- info: 'ClayBSDProof.ModularE32.hasSum_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.hasSum_V

/-- info: 'ClayBSDProof.ModularE32.hasSum_coef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.hasSum_coef

/-- info: 'ClayBSDProof.ModularE32.hasSum_cos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.hasSum_cos

/-- info: 'ClayBSDProof.ModularE32.hasSum_sin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.hasSum_sin

/-- info: 'ClayBSDProof.ModularE32.lseriesSummable_curva32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.lseriesSummable_curva32

/-- info: 'ClayBSDProof.ModularE32.pi_div_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.pi_div_K

/-- info: 'ClayBSDProof.ModularE32.ponteModular_curva32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.ponteModular_curva32

/-- info: 'ClayBSDProof.ModularE32.prim_coord' does not depend on any axioms -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.prim_coord

/-- info: 'ClayBSDProof.ModularE32.re_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.re_sum

/-- info: 'ClayBSDProof.ModularE32.rpow_par' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.rpow_par

/-- info: 'ClayBSDProof.ModularE32.sin_quarto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.sin_quarto

/-- info: 'ClayBSDProof.ModularE32.sumAbs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.sumAbs

/-- info: 'ClayBSDProof.ModularE32.summable_rede' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.summable_rede

/-- info: 'ClayBSDProof.ModularE32.teta_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.ModularE32.teta_eq


/-! ## `ClayBSDProof.CaseE32` -/

/-- info: 'ClayBSDProof.CaseE32.Lcurva32_one_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.CaseE32.Lcurva32_one_ne_zero

/-- info: 'ClayBSDProof.CaseE32.analyticOrderAt_Lcurva32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.CaseE32.analyticOrderAt_Lcurva32

/-- info: 'ClayBSDProof.CaseE32.continuation_one_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.CaseE32.continuation_one_ne_zero

/-- info: 'ClayBSDProof.CaseE32.isContinuation_Lcurva32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.CaseE32.isContinuation_Lcurva32

/-- info: 'ClayBSDProof.CaseE32.statement_E32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.CaseE32.statement_E32


/-! ## `ClayBSDProof.MordellWeil.ChangeOfVariables` -/

/-- info: 'ClayBSDProof.MordellWeil.ChangeOfVariables.addX_normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.ChangeOfVariables.addX_normal

/-- info: 'ClayBSDProof.MordellWeil.ChangeOfVariables.addY_normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.ChangeOfVariables.addY_normal

/-- info: 'ClayBSDProof.MordellWeil.ChangeOfVariables.delta_normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.ChangeOfVariables.delta_normal

/-- info: 'ClayBSDProof.MordellWeil.ChangeOfVariables.eliptica_normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.ChangeOfVariables.eliptica_normal

/-- info: 'ClayBSDProof.MordellWeil.ChangeOfVariables.equation_normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.ChangeOfVariables.equation_normal

/-- info: 'ClayBSDProof.MordellWeil.ChangeOfVariables.fraco_de_normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.ChangeOfVariables.fraco_de_normal

/-- info: 'ClayBSDProof.MordellWeil.ChangeOfVariables.mudar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.ChangeOfVariables.mudar

/-- info: 'ClayBSDProof.MordellWeil.ChangeOfVariables.mudarEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.ChangeOfVariables.mudarEquiv

/-- info: 'ClayBSDProof.MordellWeil.ChangeOfVariables.mudarHom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.ChangeOfVariables.mudarHom

/-- info: 'ClayBSDProof.MordellWeil.ChangeOfVariables.mudar_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.ChangeOfVariables.mudar_add

/-- info: 'ClayBSDProof.MordellWeil.ChangeOfVariables.mudar_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.ChangeOfVariables.mudar_injective

/-- info: 'ClayBSDProof.MordellWeil.ChangeOfVariables.mudar_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.ChangeOfVariables.mudar_some

/-- info: 'ClayBSDProof.MordellWeil.ChangeOfVariables.mudar_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.ChangeOfVariables.mudar_surjective

/-- info: 'ClayBSDProof.MordellWeil.ChangeOfVariables.mudar_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.ChangeOfVariables.mudar_zero

/-- info: 'ClayBSDProof.MordellWeil.ChangeOfVariables.negY_normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.ChangeOfVariables.negY_normal

/-- info: 'ClayBSDProof.MordellWeil.ChangeOfVariables.nonsingular_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.ChangeOfVariables.nonsingular_normal

/-- info: 'ClayBSDProof.MordellWeil.ChangeOfVariables.normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.ChangeOfVariables.normal

/-- info: 'ClayBSDProof.MordellWeil.ChangeOfVariables.slope_normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.ChangeOfVariables.slope_normal

/-- info: 'ClayBSDProof.MordellWeil.ChangeOfVariables.yN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.ChangeOfVariables.yN

/-- info: 'ClayBSDProof.MordellWeil.ChangeOfVariables.yN_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.ChangeOfVariables.yN_inj

/-- info: 'ClayBSDProof.MordellWeil.ChangeOfVariables.yN_negY' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.ChangeOfVariables.yN_negY


/-! ## `ClayBSDProof.MordellWeil.Field` -/

/-- info: 'ClayBSDProof.MordellWeil.Field.F2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.F2

/-- info: 'ClayBSDProof.MordellWeil.Field.Pt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.Pt

/-- info: 'ClayBSDProof.MordellWeil.Field.Raiz' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.Raiz

/-- info: 'ClayBSDProof.MordellWeil.Field.Raizes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.Raizes

/-- info: 'ClayBSDProof.MordellWeil.Field.caso_raiz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.caso_raiz

/-- info: 'ClayBSDProof.MordellWeil.Field.cls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.cls

/-- info: 'ClayBSDProof.MordellWeil.Field.cls_eq_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.cls_eq_one_iff

/-- info: 'ClayBSDProof.MordellWeil.Field.cls_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.cls_mul

/-- info: 'ClayBSDProof.MordellWeil.Field.cls_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.cls_mul_self

/-- info: 'ClayBSDProof.MordellWeil.Field.cls_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.cls_of_ne

/-- info: 'ClayBSDProof.MordellWeil.Field.curva' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.curva

/-- info: 'ClayBSDProof.MordellWeil.Field.dd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.dd

/-- info: 'ClayBSDProof.MordellWeil.Field.dd_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.dd_ne_zero

/-- info: 'ClayBSDProof.MordellWeil.Field.delta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.delta

/-- info: 'ClayBSDProof.MordellWeil.Field.delta_curva' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.delta_curva

/-- info: 'ClayBSDProof.MordellWeil.Field.delta_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.delta_ne_zero

/-- info: 'ClayBSDProof.MordellWeil.Field.delta_some_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.delta_some_eq

/-- info: 'ClayBSDProof.MordellWeil.Field.delta_some_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.delta_some_ne

/-- info: 'ClayBSDProof.MordellWeil.Field.delta_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.delta_zero

/-- info: 'ClayBSDProof.MordellWeil.Field.dois_torcao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.dois_torcao

/-- info: 'ClayBSDProof.MordellWeil.Field.eliptica' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.eliptica

/-- info: 'ClayBSDProof.MordellWeil.Field.equacao_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.equacao_iff

/-- info: 'ClayBSDProof.MordellWeil.Field.f' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.f

/-- info: 'ClayBSDProof.MordellWeil.Field.finito_dois_torcao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.finito_dois_torcao

/-- info: 'ClayBSDProof.MordellWeil.Field.fraco_de_finito' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.fraco_de_finito

/-- info: 'ClayBSDProof.MordellWeil.Field.identidade_reta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.identidade_reta

/-- info: 'ClayBSDProof.MordellWeil.Field.instCommGroupF2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.instCommGroupF2

/-- info: 'ClayBSDProof.MordellWeil.Field.lado_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.lado_T

/-- info: 'ClayBSDProof.MordellWeil.Field.metade' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.metade

/-- info: 'ClayBSDProof.MordellWeil.Field.mk2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.mk2

/-- info: 'ClayBSDProof.MordellWeil.Field.mk2_eq_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.mk2_eq_one_iff

/-- info: 'ClayBSDProof.MordellWeil.Field.mk2_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.mk2_surjective

/-- info: 'ClayBSDProof.MordellWeil.Field.negY_curva' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.negY_curva

/-- info: 'ClayBSDProof.MordellWeil.Field.nonsingular_raiz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.nonsingular_raiz

/-- info: 'ClayBSDProof.MordellWeil.Field.nucleo_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.nucleo_le

/-- info: 'ClayBSDProof.MordellWeil.Field.phi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.phi

/-- info: 'ClayBSDProof.MordellWeil.Field.phiE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.phiE

/-- info: 'ClayBSDProof.MordellWeil.Field.phiE_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.phiE_add

/-- info: 'ClayBSDProof.MordellWeil.Field.phi_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.phi_eq_zero_iff

/-- info: 'ClayBSDProof.MordellWeil.Field.produto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.produto

/-- info: 'ClayBSDProof.MordellWeil.Field.raiz₁' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.raiz₁

/-- info: 'ClayBSDProof.MordellWeil.Field.raiz₂' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.raiz₂

/-- info: 'ClayBSDProof.MordellWeil.Field.raiz₃' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.raiz₃

/-- info: 'ClayBSDProof.MordellWeil.Field.y_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Field.y_zero


/-! ## `ClayBSDProof.MordellWeil.SelmerFinite` -/

/-- info: 'ClayBSDProof.MordellWeil.SelmerFinite.count_spanSingleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.SelmerFinite.count_spanSingleton

/-- info: 'ClayBSDProof.MordellWeil.SelmerFinite.existe_raiz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.SelmerFinite.existe_raiz

/-- info: 'ClayBSDProof.MordellWeil.SelmerFinite.finito_imagem_unidades' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.SelmerFinite.finito_imagem_unidades

/-- info: 'ClayBSDProof.MordellWeil.SelmerFinite.finito_por_fibras' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.SelmerFinite.finito_por_fibras

/-- info: 'ClayBSDProof.MordellWeil.SelmerFinite.finito_selmer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.SelmerFinite.finito_selmer

/-- info: 'ClayBSDProof.MordellWeil.SelmerFinite.finito_selmer_vazio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.SelmerFinite.finito_selmer_vazio

/-- info: 'ClayBSDProof.MordellWeil.SelmerFinite.finito_unidades_mod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.SelmerFinite.finito_unidades_mod

/-- info: 'ClayBSDProof.MordellWeil.SelmerFinite.mem_selmer_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.SelmerFinite.mem_selmer_iff

/-- info: 'ClayBSDProof.MordellWeil.SelmerFinite.selmer_finito' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.SelmerFinite.selmer_finito

/-- info: 'ClayBSDProof.MordellWeil.SelmerFinite.valuationOfNeZeroMod_eq_one_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.SelmerFinite.valuationOfNeZeroMod_eq_one_iff


/-! ## `ClayBSDProof.MordellWeil.WeakNumberField` -/

/-- info: 'ClayBSDProof.MordellWeil.WeakNumberField.Boa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.WeakNumberField.Boa

/-- info: 'ClayBSDProof.MordellWeil.WeakNumberField.boa₁' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.WeakNumberField.boa₁

/-- info: 'ClayBSDProof.MordellWeil.WeakNumberField.boa₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.WeakNumberField.boa₂

/-- info: 'ClayBSDProof.MordellWeil.WeakNumberField.dvd_de_quadrado' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.WeakNumberField.dvd_de_quadrado

/-- info: 'ClayBSDProof.MordellWeil.WeakNumberField.finito_phi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.WeakNumberField.finito_phi

/-- info: 'ClayBSDProof.MordellWeil.WeakNumberField.fraco_numero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.WeakNumberField.fraco_numero

/-- info: 'ClayBSDProof.MordellWeil.WeakNumberField.le_um_de_fora' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.WeakNumberField.le_um_de_fora

/-- info: 'ClayBSDProof.MordellWeil.WeakNumberField.par_x_menos_e' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.WeakNumberField.par_x_menos_e

/-- info: 'ClayBSDProof.MordellWeil.WeakNumberField.phiE_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.WeakNumberField.phiE_mem

/-- info: 'ClayBSDProof.MordellWeil.WeakNumberField.ruins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.WeakNumberField.ruins

/-- info: 'ClayBSDProof.MordellWeil.WeakNumberField.ruins_finito' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.WeakNumberField.ruins_finito

/-- info: 'ClayBSDProof.MordellWeil.WeakNumberField.unidade_de_fora' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.WeakNumberField.unidade_de_fora


/-! ## `ClayBSDProof.MordellWeil` -/

/-- info: 'ClayBSDProof.MordellWeil.Lc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.Lc

/-- info: 'ClayBSDProof.MordellWeil.MordellWeilFraco' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.MordellWeilFraco

/-- info: 'ClayBSDProof.MordellWeil.algebraicRank_lt_aleph0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.algebraicRank_lt_aleph0

/-- info: 'ClayBSDProof.MordellWeil.cubica' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.cubica

/-- info: 'ClayBSDProof.MordellWeil.cubica_monic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.cubica_monic

/-- info: 'ClayBSDProof.MordellWeil.cubica_natDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.cubica_natDegree

/-- info: 'ClayBSDProof.MordellWeil.descida' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.descida

/-- info: 'ClayBSDProof.MordellWeil.eval_cubica' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.eval_cubica

/-- info: 'ClayBSDProof.MordellWeil.existe_raizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.existe_raizes

/-- info: 'ClayBSDProof.MordellWeil.fg_of_fraco' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.fg_of_fraco

/-- info: 'ClayBSDProof.MordellWeil.fixos_racionais' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.fixos_racionais

/-- info: 'ClayBSDProof.MordellWeil.fraco_a1a3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.fraco_a1a3

/-- info: 'ClayBSDProof.MordellWeil.isGalois_Lc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.isGalois_Lc

/-- info: 'ClayBSDProof.MordellWeil.mordellWeilFraco' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.mordellWeilFraco

/-- info: 'ClayBSDProof.MordellWeil.mordellWeil_fg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.mordellWeil_fg

/-- info: 'ClayBSDProof.MordellWeil.numberField_Lc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.numberField_Lc

/-- info: 'ClayBSDProof.MordellWeil.postoMW_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.postoMW_ne_top

/-- info: 'ClayBSDProof.MordellWeil.raizes_cubica' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.raizes_cubica

/-- info: 'ClayBSDProof.MordellWeil.vieta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.MordellWeil.vieta


/-! ## `ClayBSDProof.RankDecomposition` -/

/-- info: 'ClayBSDProof.RankDecomposition.ContinuationExists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.RankDecomposition.ContinuationExists

/-- info: 'ClayBSDProof.RankDecomposition.LowRankTheorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.RankDecomposition.LowRankTheorem

/-- info: 'ClayBSDProof.RankDecomposition.RankOpen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.RankDecomposition.RankOpen

/-- info: 'ClayBSDProof.RankDecomposition.conjecture_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.RankDecomposition.conjecture_iff

/-- info: 'ClayBSDProof.RankDecomposition.conjecture_iff_rankOpen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.RankDecomposition.conjecture_iff_rankOpen

/-- info: 'ClayBSDProof.RankDecomposition.order_eq_of_conjecture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayBSDProof.RankDecomposition.order_eq_of_conjecture
