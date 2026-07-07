import Mathlib

lemma den_dvd_two_of_den_le_two {q : ℚ} (hq : q.den ≤ 2) : q.den ∣ 2 := by
  have := q.pos; interval_cases q.den <;> decide

lemma add_den_le_two {q₁ q₂ : ℚ} (hq₁ : q₁.den ≤ 2) (hq₂ : q₂.den ≤ 2) : (q₁ + q₂).den ≤ 2 :=
    Nat.le_of_dvd Nat.zero_lt_two <| by
  exact q₁.add_den_dvd_lcm q₂ |>.trans <| by grind [Nat.lcm_dvd, den_dvd_two_of_den_le_two]

abbrev ℚ₂ := {q : ℚ // q.den ≤ 2}

instance : Add ℚ₂ where
  add (q₁ q₂ : ℚ₂) := ⟨q₁.val + q₂.val, add_den_le_two q₁.property q₂.property⟩

instance : Zero ℚ₂ := ⟨⟨0, by norm_num⟩⟩

instance : Neg ℚ₂ where
  neg (q : ℚ₂) := ⟨-q.val, by grind only [Rat.den_neg_eq_den]⟩

instance : AddGroup ℚ₂ :=
  AddGroup.ofLeftAxioms sorry sorry sorry
