import LeanRAG.Test2

-- open thms
namespace Test

@[simp]
theorem one_plus_one_eq_two : ∀ (n : ℕ ), ∃ (m : ℕ), n = (fun x => x) m := by
  intro n
  exists n


def x := 1 + 1

theorem test : a 0 = 0 := by
  exact test2

theorem test' : a 0 = 0 := by
  exact test

end Test
