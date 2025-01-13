from z3 import *
from fp_mul.ieee_compliant import fp_mul
from fp_sum.ieee_compliant import fp_sum
import time


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


def maximize_horner_error(degree, max_attempts=20):
    start = time.time()
    solver = Solver()
    FP16 = FPSort(4, 4)

    # Create variables
    x = FP('x', FP16)
    coeffs = [FP(f'a{i}', FP16) for i in range(degree + 1)]

    # Add range constraints
    for var in [x] + coeffs:
        solver.add(fpGEQ(var, FPVal(0, FP16)))
        solver.add(fpLEQ(var, FPVal(3.0, FP16)))
        solver.add(Not(fpIsNaN(var)))
        solver.add(Not(fpIsInf(var)))

    # Make all variables different
    '''all_vars = [x] + coeffs
    for i in range(len(all_vars)):
        for j in range(i + 1, len(all_vars)):
            solver.add(Not(fpEQ(all_vars[i], all_vars[j])))'''

    # Compute custom implementation with tracking
    def compute_custom():
        steps = []
        result = coeffs[0]
        steps.append(("init", result))

        for i, coeff in enumerate(coeffs[1:], 1):
            mul = fp_mul(result, x, FP16)
            steps.append((f"mul{i}", mul))
            result = fp_sum(mul, coeff, FP16)
            steps.append((f"add{i}", result))
        return result, steps

    # Compute Z3 implementation with tracking
    def compute_z3():
        steps = []
        result = coeffs[0]
        steps.append(("init", result))

        for i, coeff in enumerate(coeffs[1:], 1):
            mul = fpMul(RNE(), result, x)
            steps.append((f"mul{i}", mul))
            result = fpAdd(RNE(), mul, coeff)
            steps.append((f"add{i}", result))
        return result, steps

    result_custom, custom_steps = compute_custom()
    result_z3, z3_steps = compute_z3()

    # Add constraints for meaningful results
    #solver.add(fpLEQ(fpAbs(result_custom), FPVal(degree + 1, FP16)))
    solver.add(Not(fpIsNaN(result_custom)))
    solver.add(Not(fpIsInf(result_custom)))
    solver.add(Not(fpIsNaN(result_z3)))
    solver.add(Not(fpIsInf(result_z3)))

    # Calculate difference
    diff = fpSub(RNE(), result_custom, result_z3)
    abs_diff = fpAbs(diff)
    solver.add(fpGT(abs_diff, FPVal(0.0, FP16)))

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
            running_sum = 0
            for step_name, step_val in custom_steps:
                val = format_decimal(str(m.eval(step_val)))
                print(f"{step_name}: {m.eval(step_val)} ({val})")
                if step_name.startswith("add"):
                    running_sum = val

            print("\nZ3 implementation:")
            for step_name, step_val in z3_steps:
                val = format_decimal(str(m.eval(step_val)))
                print(f"{step_name}: {m.eval(step_val)} ({val})")

            custom_final = format_decimal(str(m.eval(result_custom)))
            z3_final = format_decimal(str(m.eval(result_z3)))
            abs_error = abs(custom_final - z3_final)
            error_percentage = 0 if running_sum == 0 else (abs_error / abs(running_sum)) * 100

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


if __name__ == "__main__":
    maximize_horner_error(2)

