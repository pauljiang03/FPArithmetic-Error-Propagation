from z3 import *
import time
from manual_fp_mul import fp_mul
from manual_fp_sum import fp_sum

FP16 = FPSort(5, 11)
FP8 = FPSort(4, 4)  # e4m3 format


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


def bv_to_binary_str(bv):
    return bin(bv.as_long())[2:].zfill(bv.size())


def format_fp(binary_str, exp_bits, frac_bits):
    sign = binary_str[0]
    exp = binary_str[1:1 + exp_bits]
    frac = binary_str[1 + exp_bits:]
    return f"S:{sign} E:{exp} M:{frac}"


def fp8_to_fp16(x):
    return fpFPToFP(RNE(), x, FP16)


def compare_summations():
    start = time.time()
    max_diff = FPVal(0.0, FP16)
    itr = 0

    while True:
        solver = Solver()

        # Create test numbers in FP8
        nums_fp8 = [FP(f'n{i}', FP8) for i in range(5)]

        # Add range constraints for FP8 values
        for num in nums_fp8:
            solver.add(fpGEQ(num, FPVal(0, FP8)))
            solver.add(fpLEQ(num, FPVal(2.0, FP8)))
            solver.add(Not(fpIsNaN(num)))
            solver.add(Not(fpIsInf(num)))

        # 1. Compute FP8 Kahan sum
        sum_kahan_fp8 = FPVal(0.0, FP8)
        c = FPVal(0.0, FP8)  # compensation

        for num in nums_fp8:
            y = fpAdd(RNE(), num, fpNeg(c))
            t = fpAdd(RNE(), sum_kahan_fp8, y)
            c = fpAdd(RNE(),
                      fpAdd(RNE(), t, fpNeg(sum_kahan_fp8)),
                      fpNeg(y)
                      )
            sum_kahan_fp8 = t

        # 2. Basic FP16 sum (convert numbers first)
        nums_fp16 = [fp8_to_fp16(num) for num in nums_fp8]
        sum_fp16 = FPVal(0.0, FP16)
        for num in nums_fp16:
            sum_fp16 = fpAdd(RNE(), sum_fp16, num)

        # 3. Basic FP8 sum
        sum_fp8 = FPVal(0.0, FP8)
        for num in nums_fp8:
            sum_fp8 = fpAdd(RNE(), sum_fp8, num)

        # Convert all results to FP16 for comparison
        sum_kahan_fp8_as_fp16 = fp8_to_fp16(sum_kahan_fp8)
        sum_fp8_as_fp16 = fp8_to_fp16(sum_fp8)

        # Calculate differences between Kahan FP8 and others
        diff1 = fpSub(RNE(), sum_fp16, sum_kahan_fp8_as_fp16)  # FP16 vs Kahan FP8
        diff2 = fpSub(RNE(), sum_fp16, sum_fp8_as_fp16)  # Basic FP8 vs  FP16
        #abs_diff = fpMax(fpAbs(diff1), fpAbs(diff2))
        abs_diff = fpAbs(diff1)


        # Look for cases with increasing differences
        solver.add(fpGT(abs_diff, max_diff))
        solver.add(Not(fpIsNaN(sum_kahan_fp8)))
        solver.add(Not(fpIsInf(sum_kahan_fp8)))
        solver.add(Not(fpIsNaN(sum_fp16)))
        solver.add(Not(fpIsInf(sum_fp16)))
        solver.add(Not(fpIsNaN(sum_fp8)))
        solver.add(Not(fpIsInf(sum_fp8)))

        itr += 1

        if solver.check() == sat:
            m = solver.model()
            max_diff = m.eval(abs_diff)

            print(f"\nIteration {itr} found larger difference:")
            print("\nInput numbers:")
            for i, num in enumerate(nums_fp8):
                val_fp8 = format_decimal(str(m.eval(num)))
                val_fp16 = format_decimal(str(m.eval(fp8_to_fp16(num))))
                print(f"n{i} = FP8: {val_fp8}, FP16: {val_fp16}")

            kahan_fp8_result = format_decimal(str(m.eval(sum_kahan_fp8)))
            fp16_result = format_decimal(str(m.eval(sum_fp16)))
            fp8_result = format_decimal(str(m.eval(sum_fp8)))
            kahan_fp8_as_fp16_result = format_decimal(str(m.eval(sum_kahan_fp8_as_fp16)))
            fp8_as_fp16_result = format_decimal(str(m.eval(sum_fp8_as_fp16)))

            print(f"\nResults:")
            print(f"FP8 Kahan sum: {kahan_fp8_result}")
            print(f"Basic FP16 sum: {fp16_result}")
            print(f"Basic FP8 sum: {fp8_result}")

            print(f"\nResults (all in FP16):")
            print(f"FP8 Kahan sum as FP16: {kahan_fp8_as_fp16_result}")
            print(f"Basic FP16 sum: {fp16_result}")
            print(f"Basic FP8 sum as FP16: {fp8_as_fp16_result}")

            diff1_val = format_decimal(str(m.eval(fpAbs(diff1))))
            diff2_val = format_decimal(str(m.eval(fpAbs(diff2))))
            print(f"\nDifferences:")
            print(f"FP16 vs Kahan FP8: {diff1_val}")
            print(f"FP16 vs Basic FP8: {diff2_val}")

            # Print binary representations of sums
            kahan_fp8_binary = bv_to_binary_str(m.eval(fpToIEEEBV(sum_kahan_fp8)))
            fp16_binary = bv_to_binary_str(m.eval(fpToIEEEBV(sum_fp16)))
            fp8_binary = bv_to_binary_str(m.eval(fpToIEEEBV(sum_fp8)))

            print("\nBinary representations:")
            print(f"FP8 Kahan sum:  {format_fp(kahan_fp8_binary, 4, 3)}")
            print(f"Basic FP16 sum: {format_fp(fp16_binary, 5, 10)}")
            print(f"Basic FP8 sum:  {format_fp(fp8_binary, 4, 3)}")

        else:
            print(f"\nNo larger differences found after {itr} iterations")
            break

    print(f"\nTime taken: {time.time() - start:.2f} seconds")


if __name__ == "__main__":
    compare_summations()