import Mathlib

theorem n_cube_sub_n_dvd_six (n : ℤ) :
    (6 : ℤ) ∣ n ^ 3 - n := by
  -- 在 ZMod 6 中，每个剩余类 x 都满足 x ^ 3 = x
  have h : ∀ x : ZMod 6, x ^ 3 = x := by
    decide
  -- 因此 n ^ 3 - n 在 ZMod 6 中为 0
  have hzero : ((n ^ 3 - n : ℤ) : ZMod 6) = 0 := by
    push_cast
    rw [h (n : ZMod 6), sub_self]
  -- 用 ZMod 的整除判别法转回整数整除
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (n ^ 3 - n) 6).mp hzero

#print axioms n_cube_sub_n_dvd_six
