from z3 import *


def fp_align(a, b, SIGN_BITS, EXP_BITS, MANT_BITS, GRS_BITS, FULL_MANT_BITS):
    """Returns aligned operands and all necessary metadata for addition"""
    TOTAL_BITS = SIGN_BITS + EXP_BITS + MANT_BITS + GRS_BITS

    # Split inputs into components
    a_sign = Extract(TOTAL_BITS - 1, TOTAL_BITS - SIGN_BITS, a)
    a_exp = Extract(TOTAL_BITS - SIGN_BITS - 1, TOTAL_BITS - SIGN_BITS - EXP_BITS, a)
    a_mant = Extract(TOTAL_BITS - SIGN_BITS - EXP_BITS - 1, GRS_BITS, a)
    a_grs = Extract(GRS_BITS - 1, 0, a)

    b_sign = Extract(TOTAL_BITS - 1, TOTAL_BITS - SIGN_BITS, b)
    b_exp = Extract(TOTAL_BITS - SIGN_BITS - 1, TOTAL_BITS - SIGN_BITS - EXP_BITS, b)
    b_mant = Extract(TOTAL_BITS - SIGN_BITS - EXP_BITS - 1, GRS_BITS, b)
    b_grs = Extract(GRS_BITS - 1, 0, b)

    # Handle subnormal numbers
    a_is_subnormal = a_exp == 0
    b_is_subnormal = b_exp == 0

    # Calculate effective exponents
    a_effective_exp = If(a_is_subnormal, BitVecVal(1, EXP_BITS), a_exp)
    b_effective_exp = If(b_is_subnormal, BitVecVal(1, EXP_BITS), b_exp)

    # Construct full mantissa including implicit bit
    a_full_mant = If(a_is_subnormal,
                     Concat(BitVecVal(0, 1), a_mant, a_grs),
                     Concat(BitVecVal(1, 1), a_mant, a_grs))
    b_full_mant = If(b_is_subnormal,
                     Concat(BitVecVal(0, 1), b_mant, b_grs),
                     Concat(BitVecVal(1, 1), b_mant, b_grs))

    # Determine which number is larger
    a_exp_int, b_exp_int = BV2Int(a_exp), BV2Int(b_exp)
    a_larger = If(UGT(a_exp, b_exp), True,
                  If(a_exp == b_exp, UGE(a_full_mant, b_full_mant), False))

    # Calculate exponent difference
    exp_diff = If(a_exp_int >= b_exp_int,
                  ZeroExt(FULL_MANT_BITS - EXP_BITS, a_effective_exp) -
                  ZeroExt(FULL_MANT_BITS - EXP_BITS, b_effective_exp),
                  ZeroExt(FULL_MANT_BITS - EXP_BITS, b_effective_exp) -
                  ZeroExt(FULL_MANT_BITS - EXP_BITS, a_effective_exp))

    return (a_sign, a_exp, a_mant, a_grs, b_sign, b_exp, b_mant, b_grs,
            a_full_mant, b_full_mant, exp_diff, a_larger, a_is_subnormal, b_is_subnormal)


def fp_add(aligned_data, subtract, FULL_MANT_BITS, GRS_BITS):
    """Performs addition and returns the sum mantissa and updated exponent"""
    (a_full_mant, b_full_mant, exp_diff, a_larger) = aligned_data

    # Handle subtraction
    neg_a, neg_b = ~a_full_mant + 1, ~b_full_mant + 1
    a_full_mant = If(subtract, If(a_larger, a_full_mant, neg_a), a_full_mant)
    b_full_mant = If(subtract, If(a_larger, neg_b, b_full_mant), b_full_mant)

    # Prepare operands with extra bit for carry
    tempa = If(subtract,
               If(a_larger,
                  Concat(BitVecVal(0, 1), a_full_mant),
                  Concat(BitVecVal(1, 1), a_full_mant)),
               Concat(BitVecVal(0, 1), a_full_mant))

    tempb = If(subtract,
               If(a_larger,
                  Concat(BitVecVal(1, 1), b_full_mant),
                  Concat(BitVecVal(0, 1), b_full_mant)),
               Concat(BitVecVal(0, 1), b_full_mant))

    # Align mantissas
    tempa_size = tempa.size()
    exp_diff_extended = ZeroExt(tempa_size - exp_diff.size(), exp_diff)

    shift_tempa = If(a_larger, ZeroExt(1, tempa), SignExt(1, tempa >> exp_diff_extended))
    shift_tempb = If(a_larger, SignExt(1, tempb >> exp_diff_extended), ZeroExt(1, tempb))

    # Extract mantissa portions after alignment
    shifted_a = ZeroExt(1, Extract(FULL_MANT_BITS - 1, 0, shift_tempa))
    shifted_b = ZeroExt(1, Extract(FULL_MANT_BITS - 1, 0, shift_tempb))

    # Perform addition
    extended_sum_mant = shifted_a + shifted_b

    return extended_sum_mant


def create_intermediate_fp(sum_mant, aligned_data, SIGN_BITS, EXP_BITS, MANT_BITS, GRS_BITS, FULL_MANT_BITS):
    """Creates an intermediate floating-point value, preserving exponent information"""
    leading_one = Extract(FULL_MANT_BITS - 1, FULL_MANT_BITS - 1, sum_mant)
    intermediate_sign = If(aligned_data[11], aligned_data[0], aligned_data[4])
    intermediate_exp = If(leading_one == 1,
                          aligned_data[1] + 1,
                          aligned_data[1])

    return Concat(
        intermediate_sign,
        intermediate_exp,
        Extract(FULL_MANT_BITS - 2, GRS_BITS, sum_mant),
        Extract(GRS_BITS - 1, 0, sum_mant)
    )


def fp_normalize(sum_mant, exp, is_subnormal, subtract, EXP_BITS, MANT_BITS, GRS_BITS, FULL_MANT_BITS):
    """Normalizes the result and returns normalized mantissa and exponent"""
    EXTENDED_MANT_BITS = FULL_MANT_BITS + 1

    # Extract components
    leading_one = Extract(EXTENDED_MANT_BITS - 1, EXTENDED_MANT_BITS - 1, sum_mant)
    sum_mant_no_leading = Extract(EXTENDED_MANT_BITS - 2, 0, sum_mant)

    # Count leading zeros
    lz_count = count_leading_zeros(Extract(FULL_MANT_BITS - 1, GRS_BITS, sum_mant), EXP_BITS)
    lz_count = If(is_subnormal, 0, lz_count)
    lz_count = If(UGT(lz_count, exp), exp, lz_count)

    # Calculate normalized exponent
    normalized_exp = If(leading_one == 1, exp + 1, exp)
    normalized_exp = If(subtract,
                        If(leading_one == 1, exp - lz_count, exp - lz_count),
                        normalized_exp)

    # Adjust leading zeros count for subnormal results
    lz_count = If(And(normalized_exp == 0, lz_count != 0),
                  lz_count - 1, lz_count)

    # Normalize mantissa
    mant_size = sum_mant_no_leading.size()
    sum_mant_shifted = If(subtract,
                          sum_mant_no_leading << ZeroExt(mant_size - EXP_BITS, lz_count),
                          sum_mant_no_leading)

    # Extract final components
    normalized_mant = If(leading_one == 1,
                         Extract(FULL_MANT_BITS - 1, GRS_BITS + 1, sum_mant_shifted),
                         Extract(FULL_MANT_BITS - 2, GRS_BITS, sum_mant_shifted))

    normalized_mant = If(subtract,
                         Extract(FULL_MANT_BITS - 2, GRS_BITS, sum_mant_shifted),
                         normalized_mant)

    return normalized_mant, normalized_exp


def count_leading_zeros(bv, result_size):
    """Counts leading zeros in a bit vector"""
    size = bv.size()
    result = BitVecVal(size, result_size)
    for i in range(size):
        condition = Extract(size - 1 - i, size - 1 - i, bv) == 1
        result = If(And(condition, result == BitVecVal(size, result_size)),
                    BitVecVal(i, result_size),
                    result)
    return result