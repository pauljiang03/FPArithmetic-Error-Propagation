from z3 import *

def is_infinity(exp, mant, exp_bits):
    return exp == (2 ** exp_bits - 1) and mant == 0

def is_nan(exp, mant, exp_bits):
    return exp == (2 ** exp_bits - 1) and mant != 0

def is_zero(exp, mant):
    return And(exp == 0, mant == 0)

def any_last_bits_set(bv, n):
    return UGT(URem(bv, 1 << n), 0)

def count_leading_zeros(bv, result_size):
    size = bv.size()
    result = BitVecVal(size, result_size)
    for i in range(size):
        condition = Extract(size - 1 - i, size - 1 - i, bv) == 1
        result = If(And(condition, result == BitVecVal(size, result_size)),
                    BitVecVal(i, result_size),
                    result)
    return result

def fp_sum(x: FPRef, y: FPRef, sort: FPSortRef):
    SIGN_BITS = 1  # Sign bit (1 bit)
    EXP_BITS = sort.ebits()  # Exponent bits (5 for Float16)
    MANT_BITS = sort.sbits() - 1  # Mantissa bits minus implicit bit (.sbits() returns 11 for mant)
    GRS_BITS = 3  # Guard, Round, and Sticky bits
    TOTAL_BITS = SIGN_BITS + EXP_BITS + MANT_BITS + GRS_BITS
    BIAS = 2 ** (EXP_BITS - 1) - 1  # Exponent bias (15 for Float16)
    FULL_MANT_BITS = 1 + MANT_BITS + GRS_BITS  # Full mantissa including implicit and GRS bits
    EXTENDED_MANT_BITS = FULL_MANT_BITS + 1  # Extended mantissa for intermediate calculations
    result_exp_inf = BitVecVal(2 ** EXP_BITS - 1, EXP_BITS)
    result_mant_nan = BitVecVal((1 << MANT_BITS) - 1, MANT_BITS)
    result_mant_inf = BitVecVal(0, MANT_BITS)

    #a = ZeroExt(GRS_BITS, fpToIEEEBV(x))
    #b = ZeroExt(GRS_BITS, fpToIEEEBV(y))
    a = Concat(fpToIEEEBV(x), BitVecVal(0, 3))
    b = Concat(fpToIEEEBV(y), BitVecVal(0, 3))
    result = BitVec('result', TOTAL_BITS)

    # Split inputs and result into components (sign, exponent, mantissa, GRS bits)
    '''a_sign, a_exp, a_mant, a_grs = BitVec('a_sign', SIGN_BITS), BitVec('a_exp', EXP_BITS), BitVec('a_mant',
                                                                                                  MANT_BITS), BitVec(
        'a_grs', GRS_BITS)
    b_sign, b_exp, b_mant, b_grs = BitVec('b_sign', SIGN_BITS), BitVec('b_exp', EXP_BITS), BitVec('b_mant',
                                                                                                  MANT_BITS), BitVec(
        'b_grs', GRS_BITS)
    result_sign, result_exp, result_mant, result_grs = BitVec('result_sign', SIGN_BITS), BitVec('result_exp',
                                                                                                EXP_BITS), BitVec(
        'result_mant', MANT_BITS), BitVec('result_grs', GRS_BITS)'''
    a_sign = Extract(TOTAL_BITS - 1, TOTAL_BITS - SIGN_BITS, a)
    a_exp = Extract(TOTAL_BITS - SIGN_BITS - 1, TOTAL_BITS - SIGN_BITS - EXP_BITS, a)
    a_mant = Extract(TOTAL_BITS - SIGN_BITS - EXP_BITS - 1, GRS_BITS, a)
    a_grs = Extract(GRS_BITS - 1, 0, a)
    b_sign = Extract(TOTAL_BITS - 1, TOTAL_BITS - SIGN_BITS, b)
    b_exp = Extract(TOTAL_BITS - SIGN_BITS - 1, TOTAL_BITS - SIGN_BITS - EXP_BITS, b)
    b_mant = Extract(TOTAL_BITS - SIGN_BITS - EXP_BITS - 1, GRS_BITS, b)
    b_grs = Extract(GRS_BITS - 1, 0, b)

    # Extract components from bitvectors
    '''for x, sign, exp, mant, grs in [(a, a_sign, a_exp, a_mant, a_grs),
                                    (b, b_sign, b_exp, b_mant, b_grs),
                                    (result, result_sign, result_exp, result_mant, result_grs)]:
        s.add(sign == Extract(TOTAL_BITS - 1, TOTAL_BITS - SIGN_BITS, x))
        s.add(exp == Extract(TOTAL_BITS - SIGN_BITS - 1, TOTAL_BITS - SIGN_BITS - EXP_BITS, x))
        s.add(mant == Extract(TOTAL_BITS - SIGN_BITS - EXP_BITS - 1, GRS_BITS, x))
        s.add(grs == Extract(GRS_BITS - 1, 0, x))'''

    # Check for special cases
    a_inf = is_infinity(a_exp, a_mant, EXP_BITS)
    b_inf = is_infinity(b_exp, b_mant, EXP_BITS)
    a_nan = is_nan(a_exp, a_mant, EXP_BITS)
    b_nan = is_nan(b_exp, b_mant, EXP_BITS)
    a_zero = is_zero(a_exp, a_mant)
    b_zero = is_zero(b_exp, b_mant)

    # Determine if is subtraction based on signs
    subtract = a_sign != b_sign

    # Handle subnormal numbers
    a_is_subnormal = a_exp == 0
    b_is_subnormal = b_exp == 0

    # Calculate effective exponents (in order for exponents to actually work, we need to set to 1)
    a_effective_exp = If(a_is_subnormal, BitVecVal(1, EXP_BITS), a_exp)
    b_effective_exp = If(b_is_subnormal, BitVecVal(1, EXP_BITS), b_exp)

    # Construct full mantissa including implicit bit
    a_full_mant = If(a_is_subnormal, Concat(BitVecVal(0, 1), a_mant, a_grs), Concat(BitVecVal(1, 1), a_mant, a_grs))
    b_full_mant = If(b_is_subnormal, Concat(BitVecVal(0, 1), b_mant, b_grs), Concat(BitVecVal(1, 1), b_mant, b_grs))

    # Determine which number is larger
    a_exp_int, b_exp_int = BV2Int(a_exp), BV2Int(b_exp)
    a_larger = If(UGT(a_exp, b_exp), True,
                  If(a_exp == b_exp, UGE(a_full_mant, b_full_mant), False))

    # Handle subtraction, negated addition = subtraction
    neg_a, neg_b = ~a_full_mant + 1, ~b_full_mant + 1
    a_full_mant = If(subtract, If(a_larger, a_full_mant, neg_a), a_full_mant)
    b_full_mant = If(subtract, If(a_larger, neg_b, b_full_mant), b_full_mant)

    # Calculate exponent difference for alignment
    exp_diff = If(a_exp_int >= b_exp_int,
                  ZeroExt(FULL_MANT_BITS - EXP_BITS, a_effective_exp) - ZeroExt(FULL_MANT_BITS - EXP_BITS,
                                                                                b_effective_exp),
                  ZeroExt(FULL_MANT_BITS - EXP_BITS, b_effective_exp) - ZeroExt(FULL_MANT_BITS - EXP_BITS,
                                                                                a_effective_exp))

    # Maximum shift allowed for mantissa alignment
    max_shift = BitVecVal(FULL_MANT_BITS - 1, FULL_MANT_BITS)

    # Prepare operands for addition/subtraction by adding a bit for potential carry
    tempa = If(subtract,
               If(a_larger,
                  Concat(BitVecVal(0, 1), a_full_mant),  # Add 0 if larger in subtraction
                  Concat(BitVecVal(1, 1), a_full_mant)),  # Add 1 if smaller in subtraction
               Concat(BitVecVal(0, 1), a_full_mant))  # Add 0 for addition

    tempb = If(subtract,
               If(a_larger,
                  Concat(BitVecVal(1, 1), b_full_mant),  # Add 1 if larger in subtraction
                  Concat(BitVecVal(0, 1), b_full_mant)),  # Add 0 if smaller in subtraction
               Concat(BitVecVal(0, 1), b_full_mant))  # Add 0 for addition

    tempa_size = tempa.size()

    # Extend exp_diff to match operand size for shifting
    exp_diff_extended = ZeroExt(tempa_size - exp_diff.size(), exp_diff)

    # Align mantissas by shifting the smaller number right
    shift_tempa = If(a_larger, ZeroExt(1, tempa), SignExt(1, tempa >> exp_diff_extended))
    shift_tempb = If(a_larger, SignExt(1, tempb >> exp_diff_extended), ZeroExt(1, tempb))

    # Extract mantissa portions after alignment
    shifted_a = ZeroExt(1, Extract(FULL_MANT_BITS - 1, 0, shift_tempa))
    shifted_b = ZeroExt(1, Extract(FULL_MANT_BITS - 1, 0, shift_tempb))

    # Keep track of bits lost in shifting for rounding
    # if the last bit is set, then sticky bit will set to 1 even if shifted out after
    smaller_mant = If(a_larger, b_full_mant, a_full_mant)
    sticky_bits = If(ULT(exp_diff, max_shift),
                     any_last_bits_set(smaller_mant, exp_diff),
                     UGT(smaller_mant, 0))

    # Perform addition of aligned mantissas
    extended_sum_mant = shifted_a + shifted_b
    leading_one = Extract(EXTENDED_MANT_BITS - 1, EXTENDED_MANT_BITS - 1, extended_sum_mant)  # Check for overflow
    sum_mant = Extract(EXTENDED_MANT_BITS - 2, 0, extended_sum_mant)
    test_mant = sum_mant

    # Handle subnormal results
    sub_one = Extract(EXTENDED_MANT_BITS - 2, EXTENDED_MANT_BITS - 2, sum_mant)
    sub_one = If(And(a_is_subnormal, b_is_subnormal), sub_one, 0)

    mant_size = sum_mant.size()

    # Start with larger number's exponent
    sum_exp = If(a_larger, a_exp, b_exp)

    # Count leading zeros for normalization
    lz_count = count_leading_zeros(Extract(FULL_MANT_BITS - 1, GRS_BITS, extended_sum_mant), EXP_BITS)
    lz_count = If(And(a_is_subnormal, b_is_subnormal), 0, lz_count)  # Don't normalize subnormals
    lz_count = If(UGT(lz_count, sum_exp), sum_exp, lz_count)  # Prevent underflow

    # Calculate normalized exponent
    normalized_exp = If(leading_one == 1, sum_exp + 1, sum_exp)  # Adjust if overflow occurred
    normalized_exp = If(sub_one == 1, normalized_exp + 1, normalized_exp)  # Adjust for subnormal result
    normalized_exp = If(subtract, If(leading_one == 1, sum_exp - lz_count, sum_exp - lz_count), normalized_exp)

    # Adjust leading zeros count for subnormal results
    lz_count = If(And(normalized_exp == 0, lz_count != 0), lz_count - 1, lz_count)
    # Shift mantissa left to normalize
    sum_mant = If(subtract, sum_mant << ZeroExt(mant_size - EXP_BITS, lz_count), sum_mant)

    # Extract normalized mantissa bits
    normalized_mant = If(leading_one == 1,
                         Extract(FULL_MANT_BITS - 1, GRS_BITS + 1, sum_mant),  # Overflow case
                         Extract(FULL_MANT_BITS - 2, GRS_BITS, sum_mant))  # Normal case
    normalized_mant = If(subtract, Extract(FULL_MANT_BITS - 2, GRS_BITS, sum_mant), normalized_mant)

    # Extract Guard, Round, and Sticky bits for rounding
    normalized_grs = If(leading_one == 1,
                        Extract(GRS_BITS, 1, sum_mant),
                        Extract(GRS_BITS - 1, 0, sum_mant))
    normalized_grs = If(subtract, Extract(GRS_BITS - 1, 0, sum_mant), normalized_grs)

    # Calculate sticky bit for rounding
    sticky_bit = Or(sticky_bits, If(leading_one == 1, Extract(0, 0, sum_mant) != 0,
                                    Or(Extract(1, 1, sum_mant) != 0, Extract(0, 0, sum_mant) != 0)))
    guard_bit = Extract(2, 2, normalized_grs)
    round_bit = Extract(1, 1, normalized_grs)
    sticky_bit = If(Or(sticky_bit, Extract(0, 0, normalized_grs) != 0), BitVecVal(1, 1), BitVecVal(0, 1))

    # Determine if rounding up is needed (round to nearest even)
    round_up = And(guard_bit == 1, Or(sticky_bit == 1, round_bit == 1, Extract(0, 0, normalized_mant) == 1))
    rounding_increment = If(round_up, BitVecVal(1, MANT_BITS + 1), BitVecVal(0, MANT_BITS + 1))

    # Apply rounding
    rounded_mant_extended = ZeroExt(1, normalized_mant) + rounding_increment
    mant_overflow = Extract(MANT_BITS, MANT_BITS, rounded_mant_extended)

    final_mant = Extract(MANT_BITS - 1, 0, rounded_mant_extended)

    final_exp = If(mant_overflow == 1, normalized_exp + 1, normalized_exp)

    # Handle equal numbers and cancellation
    a_equals_b = And(a_sign == b_sign, a_exp == b_exp, a_mant == b_mant, a_grs == b_grs)  # Check if numbers are equal
    a_cancels_b = And(a_exp == b_exp, a_mant == b_mant, a_grs == b_grs,
                      a_sign != b_sign)  # Check for exact cancellation
    final_sign = If(a_cancels_b, 0, If(a_larger, a_sign, b_sign))  # Determine result sign
    final_exp = If(a_cancels_b, 0, final_exp)  # Handle cancellation to zero
    custom_result = Extract(TOTAL_BITS - 1, GRS_BITS, result)
    return fpBVToFP(Concat(final_sign, final_exp, final_mant), sort)
