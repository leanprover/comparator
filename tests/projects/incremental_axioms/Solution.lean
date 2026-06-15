axiom axA : True
axiom axB : True
axiom axC : True

def d1 : True := axA
def d2 : True := axB
def d3 : True := axC

theorem t1 : True := d1
theorem t2 : True := by have _ := d1; exact d2
theorem t3 : True := by have _ := d2; exact d3
