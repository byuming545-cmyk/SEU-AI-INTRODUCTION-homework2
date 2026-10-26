import Mathlib

theorem four_fifths_eq_fifth :
  (27 : Nat)^5 + 84^5 + 110^5 + 133^5 = 144^5 := by
  decide

def EulerConjectureInstanceN5 : Prop :=
  ∀ a b c d e : Nat, 0 < a → 0 < b → 0 < c → 0 < d → 0 < e →
  a^5 + b^5 + c^5 + d^5 ≠ e^5

theorem euler_conjecture_instance_false : ¬ EulerConjectureInstanceN5 := by
  intro h
  have key := h 27 84 110 133 144
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact key four_fifths_eq_fifth

#print axioms euler_conjecture_instance_false