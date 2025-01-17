from .helpers import *

def fp_sum(x: FPRef, y: FPRef, sort: FPSortRef):
    SIGN_BITS = 1  # Sign bit (1 bit)
    EXP_BITS = sort.ebits()  # Exponent bits (5 for Float16)
    MANT_BITS = sort.sbits() - 1  # Mantissa bits minus implicit bit
    TOTAL_BITS = SIGN_BITS + EXP_BITS + MANT_BITS
    FULL_MANT_BITS = 1 + MANT_BITS  # Full mantissa including implicit bit
    EXTENDED_MANT_BITS = FULL_MANT_BITS + 1  # Extended mantissa for intermediate calculations

    result_exp_inf = BitVecVal(2 ** EXP_BITS - 1, EXP_BITS)
    result_mant_nan = BitVecVal((1 << MANT_BITS) - 1, MANT_BITS)
    result_mant_inf = BitVecVal(0, MANT_BITS)

    a = fpToIEEEBV(x)
    b = fpToIEEEBV(y)

    # Split inputs into components
    a_sign, a_exp, a_mant = split_input_trun(a, TOTAL_BITS, SIGN_BITS, EXP_BITS)
    b_sign, b_exp, b_mant = split_input_trun(b, TOTAL_BITS, SIGN_BITS, EXP_BITS)

    # Check for special cases
    a_inf = is_infinity(a_exp, a_mant, EXP_BITS)
    b_inf = is_infinity(b_exp, b_mant, EXP_BITS)
    a_nan = is_nan(a_exp, a_mant, EXP_BITS)
    b_nan = is_nan(b_exp, b_mant, EXP_BITS)
    a_zero = is_zero(a_exp, a_mant)
    b_zero = is_zero(b_exp, b_mant)

    # Determine if subtraction based on signs
    subtract = a_sign != b_sign

    # Handle subnormal numbers
    a_is_subnormal = a_exp == 0
    b_is_subnormal = b_exp == 0

    # Calculate effective exponents
    a_effective_exp = If(a_is_subnormal, BitVecVal(1, EXP_BITS), a_exp)
    b_effective_exp = If(b_is_subnormal, BitVecVal(1, EXP_BITS), b_exp)

    # Construct full mantissa including implicit bit
    a_full_mant = If(a_is_subnormal, Concat(BitVecVal(0, 1), a_mant), Concat(BitVecVal(1, 1), a_mant))
    b_full_mant = If(b_is_subnormal, Concat(BitVecVal(0, 1), b_mant), Concat(BitVecVal(1, 1), b_mant))

    # Determine which number is larger
    a_exp_int, b_exp_int = BV2Int(a_exp), BV2Int(b_exp)
    a_larger = If(UGT(a_exp, b_exp), True,
                  If(a_exp == b_exp, UGE(a_full_mant, b_full_mant), False))

    # Handle subtraction
    neg_a, neg_b = ~a_full_mant + 1, ~b_full_mant + 1
    a_full_mant = If(subtract, If(a_larger, a_full_mant, neg_a), a_full_mant)
    b_full_mant = If(subtract, If(a_larger, neg_b, b_full_mant), b_full_mant)

    # Calculate exponent difference for alignment
    exp_diff = If(a_exp_int >= b_exp_int,
                  ZeroExt(FULL_MANT_BITS - EXP_BITS, a_effective_exp) - ZeroExt(FULL_MANT_BITS - EXP_BITS, b_effective_exp),
                  ZeroExt(FULL_MANT_BITS - EXP_BITS, b_effective_exp) - ZeroExt(FULL_MANT_BITS - EXP_BITS, a_effective_exp))

    # Prepare operands for addition/subtraction
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

    tempa_size = tempa.size()
    exp_diff_extended = ZeroExt(tempa_size - exp_diff.size(), exp_diff)

    # Align mantissas
    shift_tempa = If(a_larger, ZeroExt(1, tempa), SignExt(1, tempa >> exp_diff_extended))
    shift_tempb = If(a_larger, SignExt(1, tempb >> exp_diff_extended), ZeroExt(1, tempb))

    # Extract mantissa portions after alignment
    shifted_a = ZeroExt(1, Extract(FULL_MANT_BITS - 1, 0, shift_tempa))
    shifted_b = ZeroExt(1, Extract(FULL_MANT_BITS - 1, 0, shift_tempb))

    # Add aligned mantissas
    extended_sum_mant = shifted_a + shifted_b
    leading_one = Extract(EXTENDED_MANT_BITS - 1, EXTENDED_MANT_BITS - 1, extended_sum_mant)
    sum_mant = Extract(EXTENDED_MANT_BITS - 2, 0, extended_sum_mant)

    # Handle subnormal results
    sub_one = Extract(EXTENDED_MANT_BITS - 2, EXTENDED_MANT_BITS - 2, sum_mant)
    sub_one = If(And(a_is_subnormal, b_is_subnormal), sub_one, 0)

    mant_size = sum_mant.size()

    # Start with larger number's exponent
    sum_exp = If(a_larger, a_exp, b_exp)

    # Count leading zeros and normalize
    lz_count = count_leading_zeros(Extract(FULL_MANT_BITS - 1, 0, extended_sum_mant), EXP_BITS)
    lz_count = If(And(a_is_subnormal, b_is_subnormal), 0, lz_count)
    lz_count = If(UGT(lz_count, sum_exp), sum_exp, lz_count)

    # Calculate normalized exponent
    normalized_exp = If(leading_one == 1, sum_exp + 1, sum_exp)
    normalized_exp = If(sub_one == 1, normalized_exp + 1, normalized_exp)
    normalized_exp = If(subtract, If(leading_one == 1, sum_exp - lz_count, sum_exp - lz_count), normalized_exp)

    # Adjust leading zeros count for subnormal results
    lz_count = If(And(normalized_exp == 0, lz_count != 0), lz_count - 1, lz_count)

    # Normalize mantissa
    sum_mant = If(subtract, sum_mant << ZeroExt(mant_size - EXP_BITS, lz_count), sum_mant)

    # Extract normalized mantissa bits
    normalized_mant = If(leading_one == 1,
                         Extract(FULL_MANT_BITS - 1, 1, sum_mant),
                         Extract(FULL_MANT_BITS - 2, 0, sum_mant))
    normalized_mant = If(subtract, Extract(FULL_MANT_BITS - 2, 0, sum_mant), normalized_mant)

    final_mant = normalized_mant
    final_exp = normalized_exp

    # Handle equal numbers and cancellation
    a_cancels_b = And(a_exp == b_exp, a_mant == b_mant, a_sign != b_sign)
    final_sign = If(a_cancels_b, 0, If(a_larger, a_sign, b_sign))
    final_exp = If(a_cancels_b, 0, final_exp)

    # Handle zeros
    final_mant = If(a_zero, b_mant, final_mant)
    final_exp = If(a_zero, b_exp, final_exp)
    final_mant = If(b_zero, a_mant, final_mant)
    final_exp = If(b_zero, a_exp, final_exp)

    # Handle infinities
    final_exp = If(Or(a_inf, b_inf), result_exp_inf, final_exp)
    final_mant = If(Or(a_inf, b_inf, is_infinity(final_exp, result_mant_inf, EXP_BITS)),
                    result_mant_inf, final_mant)

    # Handle NaNs
    final_mant = If(Or(a_nan, b_nan), result_mant_nan, final_mant)
    final_exp = If(Or(a_nan, b_nan), result_exp_inf, final_exp)
    final_mant = If(And(a_inf, b_inf, a_sign != b_sign), result_mant_nan, final_mant)

    return fpBVToFP(Concat(final_sign, final_exp, final_mant), sort)