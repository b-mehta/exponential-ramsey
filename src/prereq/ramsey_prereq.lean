/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import prereq.mathlib.algebra.big_operators.ring
import prereq.mathlib.algebra.order.monoid.lemmas
import prereq.mathlib.combinatorics.simple_graph.basic
import prereq.mathlib.combinatorics.simple_graph.degree_sum
import prereq.mathlib.data.nat.choose.basic
import prereq.mathlib.data.nat.choose.central
import prereq.mathlib.data.nat.choose.sum
import prereq.mathlib.data.nat.factorial.basic
import prereq.mathlib.data.fin.vec_notation

/-!
# Misc prereqs and collect imports
-/

lemma fin.ne_zero_iff_eq_one : ∀ {x : fin 2}, x ≠ 0 ↔ x = 1 := by dec_trivial

lemma fin.eq_zero_iff_ne_one : ∀ {x : fin 2}, x = 0 ↔ x ≠ 1 := by dec_trivial

lemma fin.fin_two_eq_zero_of_ne_one {x : fin 2} (hx : x ≠ 1) : x = 0 :=
by rwa [fin.eq_zero_iff_ne_one]
