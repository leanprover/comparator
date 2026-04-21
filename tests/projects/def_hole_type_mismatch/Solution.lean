-- Solution's hole has a different type; should be rejected even though the
-- theorem body is `sorry`.
def n : Int := 17

theorem foo : n + 17 = 34 := sorry
