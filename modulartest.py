from z3 import *
from multisum import fp_align, fp_add, fp_normalize, create_intermediate_fp


def format_bv(bv_val, width=None):
    if width is None:
        width = bv_val.size()
    return format(bv_val.as_long(), f'0{width}b')


def test_three_fp8_additions():
    Float16 = FPSort(5, 11)
    s = Solver()

    x = FP('x', Float16)
    y = FP('y', Float16)
    z = FP('z', Float16)

    SIGN_BITS = 1
    EXP_BITS = 5
    MANT_BITS = 10
    GRS_BITS = 3
    FULL_MANT_BITS = 1 + MANT_BITS + GRS_BITS

    # Convert to bit vectors
    x_bv = fpToIEEEBV(x)
    y_bv = fpToIEEEBV(y)
    z_bv = fpToIEEEBV(z)

    x_exp = Extract(14, 10, x_bv)  # Bits 14-10 are exponent in FP16
    y_exp = Extract(14, 10, y_bv)
    z_exp = Extract(14, 10, z_bv)

    s.add(x_exp != BitVecVal(0x1F, 5))  # No NaN/Inf for x
    s.add(y_exp != BitVecVal(0x1F, 5))  # No NaN/Inf for y
    s.add(z_exp != BitVecVal(0x1F, 5))  # No NaN/Inf for z
    s.add(x > 0)
    s.add(y > 0)
    s.add(z > 0)

    a = Concat(x_bv, BitVecVal(0, GRS_BITS))
    b = Concat(y_bv, BitVecVal(0, GRS_BITS))
    c = Concat(z_bv, BitVecVal(0, GRS_BITS))

    aligned_data1 = fp_align(a, b, SIGN_BITS, EXP_BITS, MANT_BITS, GRS_BITS, FULL_MANT_BITS)
    subtract1 = aligned_data1[0] != aligned_data1[4]
    sum_mant1 = fp_add((aligned_data1[8], aligned_data1[9], aligned_data1[10], aligned_data1[11]),
                       subtract1, FULL_MANT_BITS, GRS_BITS)

    intermediate_bv1 = create_intermediate_fp(sum_mant1, aligned_data1,
                                              SIGN_BITS, EXP_BITS, MANT_BITS,
                                              GRS_BITS, FULL_MANT_BITS)

    aligned_data2 = fp_align(intermediate_bv1, c, SIGN_BITS, EXP_BITS, MANT_BITS, GRS_BITS, FULL_MANT_BITS)
    subtract2 = aligned_data2[0] != aligned_data2[4]
    sum_mant2 = fp_add((aligned_data2[8], aligned_data2[9], aligned_data2[10], aligned_data2[11]),
                       subtract2, FULL_MANT_BITS, GRS_BITS)

    is_subnormal = And(aligned_data2[12], aligned_data2[13])
    final_mant, final_exp = fp_normalize(sum_mant2, aligned_data2[1], is_subnormal,
                                         subtract2, EXP_BITS, MANT_BITS, GRS_BITS, FULL_MANT_BITS)

    final_sign = If(aligned_data2[11], aligned_data2[0], aligned_data2[4])
    manual_sum = fpBVToFP(Concat(final_sign, final_exp, final_mant), Float16)

    z3_sum = fpAdd(RNE(), fpAdd(RNE(), x, y), z)
    s.add(z3_sum != manual_sum)

    if s.check() == sat:
        m = s.model()
        x_val = m.eval(x)
        y_val = m.eval(y)
        z_val = m.eval(z)
        z3_result = m.eval(z3_sum)
        manual_result = m.eval(manual_sum)

        x_bv = m.eval(fpToIEEEBV(x))
        y_bv = m.eval(fpToIEEEBV(y))
        z_bv = m.eval(fpToIEEEBV(z))
        z3_result_bv = m.eval(fpToIEEEBV(z3_result))
        manual_result_bv = m.eval(fpToIEEEBV(manual_result))

        print("Found mismatch:")
        print(f"x = {x_val} (BV: {format_bv(x_bv, 8)})")
        print(f"y = {y_val} (BV: {format_bv(y_bv, 8)})")
        print(f"z = {z_val} (BV: {format_bv(z_bv, 8)})")

        print("\nIntermediate results:")
        print(f"Input a with GRS: {format_bv(m.eval(a), 11)}")
        print(f"Input b with GRS: {format_bv(m.eval(b), 11)}")
        print(f"Input c with GRS: {format_bv(m.eval(c), 11)}")

        print(f"\nFirst addition:")
        print(f"a_sign: {format_bv(m.eval(aligned_data1[0]), 1)}")
        print(f"a_exp:  {format_bv(m.eval(aligned_data1[1]), 4)}")
        print(f"a_mant: {format_bv(m.eval(aligned_data1[2]), 3)}")
        print(f"a_grs:  {format_bv(m.eval(aligned_data1[3]), 3)}")
        print(
            f"First aligned mantissas: {format_bv(m.eval(aligned_data1[8]), 7)}, {format_bv(m.eval(aligned_data1[9]), 7)}")
        print(f"First sum mantissa (no normalization): {format_bv(m.eval(sum_mant1), 8)}")

        print(f"\nIntermediate result:")
        print(f"intermediate_bv1: {format_bv(m.eval(intermediate_bv1), 11)}")

        print(f"\nSecond addition:")
        print(
            f"Second aligned mantissas: {format_bv(m.eval(aligned_data2[8]), 7)}, {format_bv(m.eval(aligned_data2[9]), 7)}")
        print(f"Second sum mantissa before normalization: {format_bv(m.eval(sum_mant2), 8)}")
        print(f"Final mantissa after normalization: {format_bv(m.eval(final_mant), 3)}")
        print(f"Final exponent: {format_bv(m.eval(final_exp), 4)}")
        print(f"Final sign: {format_bv(m.eval(final_sign), 1)}")

        print("\nFinal results:")
        print(f"Z3 sum = {z3_result} (BV: {format_bv(z3_result_bv, 8)})")
        print(f"Your sum = {manual_result} (BV: {format_bv(manual_result_bv, 8)})")
        return False
    else:
        print("All additions match Z3's results!")
        return True

test_three_fp8_additions()