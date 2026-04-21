-- The hole `n` is listed but does not appear in the theorem's type. The solution
-- introduces `evilConst`, which is absent from the challenge environment. Without
-- seeding hole names directly into `compareAt`, `n`'s body would not be walked for
-- byte-identity against the challenge, and `evilConst` would escape detection.
def evilConst : Nat := 42

def n : Nat := evilConst

theorem foo : 0 = 0 := rfl
