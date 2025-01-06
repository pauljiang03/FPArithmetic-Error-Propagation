from z3 import *
from manual_fp_mul import fp_mul

Float8 = FPSort(4, 4)


def test_all_fp8_multiplications():
    s = Solver()

    x = FP('x', Float8)
    y = FP('y', Float8)


    z3_mul = fpMul(RNE(), x, y)
    manual_mul = fp_mul(x, y, Float8)


    s.add(z3_mul != manual_mul)

    if s.check() == sat:
        m = s.model()
        x_val = m.eval(x)
        y_val = m.eval(y)
        z3_result = m.eval(z3_mul)
        manual_result = m.eval(manual_mul)

        print("Found mismatch:")
        print(f"x = {x_val}")
        print(f"y = {y_val}")
        print(f"Z3 mul = {z3_result}")
        print(f"Your mul = {manual_result}")
        return False
    else:
        print("All multiplications match Z3's results!")
        return True


test_all_fp8_multiplications()