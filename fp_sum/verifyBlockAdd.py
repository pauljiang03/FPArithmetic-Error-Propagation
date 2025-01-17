from z3 import *
from fp_sum.blockadd import fp_multi_sum

Float16 = FPSort(5, 11)


def test_specific_case():
    s = Solver()

    x = FPVal(0.0068359375 * (2 ** -14), Float16)
    y = FPVal(0.0048828125 * (2 ** -14), Float16)
    z = FPVal(0.0029296875 * (2 ** -14), Float16)


    z3_sum = x + y + z
    manual_sum = fp_multi_sum([x, y, z], Float16, debug_solver=s)

    if s.check() == sat:
        m = s.model()

        print("\nFinal Results:")
        print(f"x = {m.eval(x)}")
        print(f"y = {m.eval(y)}")
        print(f"z = {m.eval(z)}")

        print(f"Z3 sum = {m.eval(z3_sum)}")
        print(f"Your sum = {m.eval(manual_sum)}")

        return False
    else:
        print("Error: Could not create model")
        return False


def test_all_multi_additions():
    s = Solver()

    x = FP('x', Float16)
    y = FP('y', Float16)
    z = FP('z', Float16)

    s.add(fpGT(y, 0))
    s.add(fpGT(z, 0))

    s.add(Not(fpIsInf(x)))
    s.add(Not(fpIsNaN(x)))
    s.add(Not(fpIsInf(y)))
    s.add(Not(fpIsNaN(y)))
    s.add(Not(fpIsInf(z)))
    s.add(Not(fpIsNaN(z)))

    s.add(fpGT(x, y))
    s.add(fpGT(x, z))

    z3_sum = x + y + z
    manual_sum = fp_multi_sum([x, y, z], Float16)
    s.add(z3_sum != manual_sum)

    z3_bv = fpToIEEEBV(z3_sum)
    manual_bv = fpToIEEEBV(manual_sum)

    z3_exp = Extract(14, 10, z3_bv)
    manual_exp = Extract(14, 10, manual_bv)

    s.add(z3_exp != manual_exp)
    #s.add(z3_exp != manual_exp + 1)
    #s.add(z3_exp != manual_exp - 1)



    if s.check() == sat:
        m = s.model()
        x_val = m.eval(x)
        y_val = m.eval(y)
        z_val = m.eval(z)
        z3_result = m.eval(z3_sum)
        manual_result = m.eval(manual_sum)

        print("Found mismatch:")
        print(f"x = {x_val}")
        print(f"y = {y_val}")
        print(f"z = {z_val}")
        print(f"Z3 sum = {z3_result}")
        print(f"Your sum = {manual_result}")
        return False
    else:
        print("All multi-additions match Z3's results!")
        return True


if __name__ == "__main__":
    print("Testing specific case with detailed debugging...")
    test_specific_case()

    print("\nTesting all possible cases...")
    test_all_multi_additions()