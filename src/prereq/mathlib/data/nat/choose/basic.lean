/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import data.nat.choose.basic
import prereq.mathlib.data.nat.factorial.basic

/-!
# Stuff for data.nat.choose.basic
-/
namespace nat

lemma choose_add_le_pow_left (s t : ℕ) : (s + t).choose s ≤ (t + 1) ^ s :=
begin
  rw [add_comm, choose_eq_asc_factorial_div_factorial],
  exact nat.div_le_of_le_mul asc_le_pow_mul_factorial,
end

lemma choose_le_pow_left (s t : ℕ) : s.choose t ≤ (s + 1 - t) ^ t :=
begin
  cases le_or_lt t s,
  { obtain ⟨s, rfl⟩ := exists_add_of_le h,
    refine (choose_add_le_pow_left t s).trans _,
    rw [add_assoc, nat.add_sub_cancel_left] },
  rw choose_eq_zero_of_lt h,
  exact zero_le'
end

end nat
