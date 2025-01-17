from z3 import *
from fp_sum.blockadd_trun import fp_multi_sum

Float16 = FPSort(5, 11)


def test_specific_case():
    s = Solver()

    a = FPVal(1.0, Float16)
    c = FPVal(1.0 - 2 ** -11, Float16)
    b = FPVal(2 ** -11, Float16)

    sum_with_a = fp_multi_sum([a, b, b, b, b], Float16, debug_solver=s)
    sum_with_c = fp_multi_sum([c, b, b, b, b], Float16, debug_solver=s)

    if s.check() == sat:
        m = s.model()

        print("\nValues in decimal:")
        print(f"a = {m.eval(a)}")
        print(f"c = {m.eval(c)}")
        print(f"b = {m.eval(b)}")

        print("\nValues in binary:")
        print(f"a = {bin(m.eval(fpToIEEEBV(a)).as_long())[2:].zfill(16)}")
        print(f"c = {bin(m.eval(fpToIEEEBV(c)).as_long())[2:].zfill(16)}")
        print(f"b = {bin(m.eval(fpToIEEEBV(b)).as_long())[2:].zfill(16)}")

        print("\nSums:")
        print(f"Sum with a = {m.eval(sum_with_a)}")
        print(f"Sum with c = {m.eval(sum_with_c)}")

        print("\nSums in binary:")
        print(f"Sum with a = {bin(m.eval(fpToIEEEBV(sum_with_a)).as_long())[2:].zfill(16)}")
        print(f"Sum with c = {bin(m.eval(fpToIEEEBV(sum_with_c)).as_long())[2:].zfill(16)}")

        return True
    else:
        print("Could not solve constraints")
        return False


if __name__ == "__main__":
    test_specific_case()