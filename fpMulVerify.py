from z3 import *
from manual_fp_mul import fp_mul

Float8 = FPSort(4, 4)

def bv_to_binary_str(bv):
    return bin(bv.as_long())[2:].zfill(bv.size())

def format_fp(binary_str, exp_bits):
    sign = binary_str[0]
    exp = binary_str[1:1 + exp_bits]
    frac = binary_str[1 + exp_bits:]
    return f"S:{sign} E:{exp} M:{frac}"


def test_all_fp8_multiplications():
    s = Solver()

    x = FP('x', Float8)
    y = FP('y', Float8)


    z3_mul = fpMul(RNE(), x, y)
    manual_mul = fp_mul(x, y, Float8)

    s.add(z3_mul != manual_mul[0])
    #s.add(Not(fpIsInf(z3_mul)))

    if s.check() == sat:
        m = s.model()
        x_val = m.eval(x)
        y_val = m.eval(y)
        z3_result = m.eval(z3_mul)
        manual_result = m.eval(manual_mul[0])
        vals = [m.eval(a) for a in manual_mul[1]]
        z3_bstr = bv_to_binary_str(m.eval(fpToIEEEBV(z3_result)))
        manual_bstr = bv_to_binary_str(m.eval(fpToIEEEBV(manual_result)))

        print("Found mismatch:")
        print(f"x = {x_val}")
        print(f"y = {y_val}")
        print(f"Z3 mul = {z3_result}")
        print(f"\t Binary: {format_fp(z3_bstr, 4)}")
        print(f"Your mul = {manual_result}")
        print(f"\t Binary: {format_fp(manual_bstr, 4)}")
        print(f"{vals}")
        return False
    else:
        print("All multiplications match Z3's results!")
        return True


test_all_fp8_multiplications()