/-
Sanity test: confirm no theorem in the development depends on `sorryAx`.
Expected output for every line below is exactly
  [propext, Classical.choice, Quot.sound]
-/
import ShiftStableExponents

#print axioms ShiftStableExponents.bala_eq_Bint
#print axioms ShiftStableExponents.coeff_one_add_pow_mul
#print axioms ShiftStableExponents.Bint_shift
#print axioms ShiftStableExponents.bala_congruence
#print axioms ShiftStableExponents.bala_congruence_A361036
#print axioms ShiftStableExponents.bala_congruence_A278070
#print axioms ShiftStableExponents.bala_congruence_A361281
#print axioms ShiftStableExponents.bala_congruence_A293013
#print axioms ShiftStableExponents.bala_congruence_sq
