from z3 import *
from manual_fp_sum import fp_sum
Float8 = FPSort(4, 4)

# Compare and verify the manual IEEE fp add against the library fp add
def test_all_fp8_additions():
    s = Solver()

    x = FP('x', Float8)
    y = FP('y', Float8)

    z3_sum = fpAdd(RNE(), x, y)
    manual_sum = fp_sum(x, y, Float8)
    s.add(z3_sum != manual_sum)


    if s.check() == sat:
        m = s.model()
        x_val = m.eval(x)
        y_val = m.eval(y)
        z3_result = m.eval(z3_sum)
        manual_result = m.eval(manual_sum)

        print("Found mismatch:")
        print(f"x = {x_val}")
        print(f"y = {y_val}")
        print(f"Z3 sum = {z3_result}")
        print(f"Your sum = {manual_result}")
        return False
    else:
        print("All additions match Z3's results!")
        return True

test_all_fp8_additions()