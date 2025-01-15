from z3 import *
from fp_mul.ieee_compliant import fp_mul
from fp_sum.ieee_compliant import fp_sum
import time

def bv_to_binary(bv, width):
    return format(bv.as_long(), f'0{width}b')

def parse_z3_fp(fp_str):
    if '*(2**' in fp_str:
        coeff_str, exp_str = fp_str.split('*(2**')
        coeff = float(coeff_str.strip())
        exp = int(exp_str.strip(')'))
        return coeff * (2 ** exp)
    return float(fp_str)


FP8 = FPSort(5, 11)


def compare_fp8_implementations(min_diff_percentage):
    start = time.time()
    solver = Solver()

    x1 = FP('x1', FP8)
    x2 = FP('x2', FP8)
    x3 = FP('x3', FP8)
    x4 = FP('x4', FP8)

    w1 = FP('w1', FP8)
    w2 = FP('w2', FP8)
    w3 = FP('w3', FP8)
    w4 = FP('w4', FP8)
    b = FP('b', FP8)

    for var in [x1, x2, x3, x4, w1, w2, w3, w4, b]:
        solver.add(fpLEQ(var, FPVal(2.0, FP8)))
        solver.add(fpGEQ(var, FPVal(-2.0, FP8)))

    all_vars = [x1, x2, x3, x4, w1, w2, w3, w4, b]
    for i in range(len(all_vars)):
        for j in range(i + 1, len(all_vars)):
            solver.add(Not(fpEQ(all_vars[i], all_vars[j])))

    prod1_custom = fp_mul(x1, w1, FP8)
    prod2_custom = fp_mul(x2, w2, FP8)
    prod3_custom = fp_mul(x3, w3, FP8)
    prod4_custom = fp_mul(x4, w4, FP8)

    sum1_custom = fp_sum(prod1_custom, prod2_custom, FP8)
    sum2_custom = fp_sum(sum1_custom, prod3_custom, FP8)
    sum3_custom = fp_sum(sum2_custom, prod4_custom, FP8)
    y_custom = fp_sum(sum3_custom, b, FP8)

    prod1_z3 = fpMul(RNE(), x1, w1)
    prod2_z3 = fpMul(RNE(), x2, w2)
    prod3_z3 = fpMul(RNE(), x3, w3)
    prod4_z3 = fpMul(RNE(), x4, w4)

    sum1_z3 = fpAdd(RNE(), prod1_z3, prod2_z3)
    sum2_z3 = fpAdd(RNE(), sum1_z3, prod3_z3)
    sum3_z3 = fpAdd(RNE(), sum2_z3, prod4_z3)
    y_z3 = fpAdd(RNE(), sum3_z3, b)

    solver.add(fpGT(y_custom, FPVal(0.0, FP8)))
    solver.add(fpLT(y_custom, FPVal(8.0, FP8)))

    solver.add(Not(fpEQ(y_custom, y_z3)))

    diff = fpSub(RNE(), y_custom, y_z3)
    abs_diff = fpAbs(diff)

    min_diff = fpMul(RNE(), fpAbs(y_z3), FPVal(min_diff_percentage / 100.0, FP8))
    solver.add(fpGT(abs_diff, min_diff))
    solver.add(Not(fpEQ(y_z3, 0)))

    if solver.check() == sat:
        m = solver.model()

        print("\nValues found:")
        print(f"x1 = {m.eval(x1)}")
        print(f"x2 = {m.eval(x2)}")
        print(f"x3 = {m.eval(x3)}")
        print(f"x4 = {m.eval(x4)}")
        print(f"w1 = {m.eval(w1)}")
        print(f"w2 = {m.eval(w2)}")
        print(f"w3 = {m.eval(w3)}")
        print(f"w4 = {m.eval(w4)}")
        print(f"b = {m.eval(b)}")

        print("\nResults:")
        print(f"Custom implementation: {m.eval(y_custom)}")
        print(f"Z3 implementation: {m.eval(y_z3)}")
        print(f"Absolute difference: {m.eval(abs_diff)}")

        custom_float = parse_z3_fp(str(m.eval(y_custom)))
        z3_float = parse_z3_fp(str(m.eval(y_z3)))
        if z3_float != 0:
            percentage_diff = abs((custom_float - z3_float) / z3_float * 100)
        elif custom_float != 0:
            percentage_diff = abs((custom_float - z3_float) / custom_float * 100)
        else:
            percentage_diff = 0

        print(f"Percentage difference: {percentage_diff:.2f}%")
        print(f"\nDecimal values:")
        print(f"Custom: {custom_float}")
        print(f"Z3: {z3_float}")
        print(f"Absolute diff: {parse_z3_fp(str(m.eval(abs_diff)))}")

        print(f"\nTime: {time.time() - start}")

compare_fp8_implementations(20)
