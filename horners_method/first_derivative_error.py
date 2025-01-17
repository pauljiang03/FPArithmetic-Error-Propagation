from z3 import *
from fp_mul.one_rounding_bit import fp_mul
from fp_sum.one_rounding_bit import fp_sum
import time
import sys


def parse_z3_fp(fp_str):
    if '*(2**' in fp_str:
        coeff_str, exp_str = fp_str.split('*(2**')
        coeff = float(coeff_str.strip())
        exp = int(exp_str.strip(')'))
        return coeff * (2 ** exp)
    return float(fp_str)


def format_decimal(val):
    if isinstance(val, str):
        return parse_z3_fp(val)
    return val


def maximize_horner_error(degree, exp=4, mant=4, max_attempts=50):
    start = time.time()
    solver = Solver()
    FP8 = FPSort(exp, mant)

    # Create variables
    x = FP('x', FP8)
    coeffs = [FP(f'a{i}', FP8) for i in range(degree + 1)]

    # Add constraints for coefficients
    for var in coeffs:
        solver.add(fpGEQ(var, FPVal(-5, FP8)))
        solver.add(fpLEQ(var, FPVal(5, FP8)))
        solver.add(Not(fpIsNaN(var)))
        solver.add(Not(fpIsInf(var)))

    # Add constraints for x
    solver.add(fpGT(x, FPVal(-1, FP8)))
    solver.add(fpLT(x, FPVal(1, FP8)))
    solver.add(Not(fpIsNaN(x)))
    solver.add(Not(fpIsInf(x)))

    # Compute custom implementation with tracking
    def compute_custom():
        steps = []
        result = FPVal(0, FP8)
        val = coeffs[0]
        steps.append(("init", result))

        for i, coeff in enumerate(coeffs[1:], 1):
            derivative_mul = fp_mul(result, x, FP8)
            steps.append((f"derivative mul {i}", derivative_mul))
            result = fp_sum(derivative_mul, val, FP8)
            steps.append((f"derivative add {i}", result))

            val_mul = fp_mul(val, x, FP8)
            steps.append((f"value mul {i}", val_mul))
            val = fp_sum(val_mul, coeff, FP8)
            steps.append((f"value add {i}", val))

        return result, steps

    # Compute Z3 implementation with tracking
    def compute_z3():
        steps = []
        result = FPVal(0, FP8)
        val = coeffs[0]
        steps.append(("init", result))

        for i, coeff in enumerate(coeffs[1:], 1):
            derivative_mul = fpMul(RNE(), result, x)
            steps.append((f"derivative mul {i}", derivative_mul))
            result = fpAdd(RNE(), derivative_mul, val)
            steps.append((f"derivative add {i}", result))

            val_mul = fpMul(RNE(), val, x)
            steps.append((f"value mul {i}", val_mul))
            val = fpAdd(RNE(), val_mul, coeff)
            steps.append((f"value add {i}", val))

        return result, steps

    result_custom, custom_steps = compute_custom()
    result_z3, z3_steps = compute_z3()

    # Add constraints for meaningful results
    solver.add(Not(fpIsNaN(result_custom)))
    solver.add(Not(fpIsInf(result_custom)))
    solver.add(Not(fpIsNaN(result_z3)))
    solver.add(Not(fpIsInf(result_z3)))

    # Calculate difference
    diff = fpSub(RNE(), result_custom, result_z3)
    abs_diff = fpAbs(diff)
    solver.add(fpGT(abs_diff, FPVal(0.0, FP8)))

    # Incrementally find larger errors
    max_error = None
    max_model = None

    for attempt in range(max_attempts):
        solver.push()

        if max_error is not None:
            solver.add(fpGT(abs_diff, max_error))

        if solver.check() == sat:
            m = solver.model()
            max_error = m.eval(abs_diff)
            max_model = m

            print(f"\nAttempt {attempt + 1}: Found larger error")
            print(f"\nInputs:")
            x_val = format_decimal(str(m.eval(x)))
            print(f"x = {m.eval(x)} ({x_val})")
            coeff_vals = []
            for i, coeff in enumerate(coeffs):
                val = format_decimal(str(m.eval(coeff)))
                coeff_vals.append(val)
                print(f"a{i} = {m.eval(coeff)} ({val})")

            print("\nStep by step computation:")
            print("\nCustom implementation:")
            for step_name, step_val in custom_steps:
                val = format_decimal(str(m.eval(step_val)))
                print(f"{step_name}: {m.eval(step_val)} ({val})")

            print("\nZ3 implementation:")
            for step_name, step_val in z3_steps:
                val = format_decimal(str(m.eval(step_val)))
                print(f"{step_name}: {m.eval(step_val)} ({val})")

            custom_final = format_decimal(str(m.eval(result_custom)))
            z3_final = format_decimal(str(m.eval(result_z3)))
            abs_error = abs(custom_final - z3_final)
            error_percentage = 0 if custom_final == 0 else (abs_error / abs(custom_final)) * 100

            print(f"\nResults:")
            print(f"Custom final: {custom_final}")
            print(f"Z3 final: {z3_final}")
            print(f"Absolute error: {abs_error}")
            print(f"Error percentage of final sum: {error_percentage:.2f}%")

        else:
            print(f"\nAttempt {attempt + 1}: Cannot find larger error")
            break

        solver.pop()

    if max_model is not None:
        print(f"\nTime taken: {time.time() - start:.2f} seconds")

        solver.push()
        solver.add(fpGT(abs_diff, max_error))
        if solver.check() == unsat:
            print("PROVED: This is the true maximum error!")
        else:
            print("Note: Larger errors might be possible")
        solver.pop()

'''
    The first command line argument is the degree of the polynomial to maximize
    The second command line argument is number of bits to use for the exponent
    The third command line argument is number of bits to use for the mantissa (including the implicit bit)
'''
if __name__ == "__main__":
    maximize_horner_error(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
