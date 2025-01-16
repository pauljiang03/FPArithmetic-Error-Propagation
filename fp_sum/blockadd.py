from .helpers import *
from typing import List


def fp_multi_sum(inputs: List[FPRef], sort: FPSortRef, debug_solver=None):
    if not inputs:
        return None
    if len(inputs) == 1:
        return inputs[0]

    SIGN_BITS = 1
    EXP_BITS = sort.ebits()
    MANT_BITS = sort.sbits() - 1
    GRS_BITS = 3
    TOTAL_BITS = SIGN_BITS + EXP_BITS + MANT_BITS + GRS_BITS
    FULL_MANT_BITS = 1 + MANT_BITS + GRS_BITS
    EXTENDED_BITS = FULL_MANT_BITS + 2  # Add 2 bits for carry and sign

    def debug_print(msg, val):
        if debug_solver and debug_solver.check() == sat:
            m = debug_solver.model()
            if isinstance(val, list):
                print(f"\n{msg}")
                for i, v in enumerate(val):
                    try:
                        eval_val = m.eval(v)
                        print(f"  [{i}]: {bin(eval_val.as_long())[2:].zfill(v.size())}")
                    except:
                        print(f"  [{i}]: Could not evaluate")
            else:
                try:
                    if is_bool(val):
                        eval_val = m.eval(val)
                        print(f"{msg}: {1 if eval_val else 0}")  # Just output 1 or 0
                    else:
                        eval_val = m.eval(val)
                        print(f"{msg}: {bin(eval_val.as_long())[2:].zfill(val.size())}")
                except:
                    print(f"{msg}: Could not evaluate")

    result_exp_inf = BitVecVal(2 ** EXP_BITS - 1, EXP_BITS)
    result_mant_nan = BitVecVal((1 << MANT_BITS) - 1, MANT_BITS)
    result_mant_inf = BitVecVal(0, MANT_BITS)

    # Convert all inputs to extended format with GRS bits
    values = [Concat(fpToIEEEBV(x), BitVecVal(0, GRS_BITS)) for x in inputs]
    debug_print("Initial values", values)

    # Split all inputs into components
    components = [split_input(v, TOTAL_BITS, SIGN_BITS, EXP_BITS, GRS_BITS) for v in values]
    signs = [c[0] for c in components]
    exps = [c[1] for c in components]
    mants = [c[2] for c in components]
    grs = [c[3] for c in components]

    debug_print("Signs", signs)
    debug_print("Exponents", exps)
    debug_print("Mantissas", mants)
    debug_print("GRS bits", grs)

    # Check special cases for all inputs
    infinities = [is_infinity(e, m, EXP_BITS) for e, m in zip(exps, mants)]
    nans = [is_nan(e, m, EXP_BITS) for e, m in zip(exps, mants)]
    zeros = [is_zero(e, m) for e, m in zip(exps, mants)]
    subnormals = [e == BitVecVal(0, EXP_BITS) for e in exps]

    # Find the maximum exponent for alignment
    effective_exps = [If(sub, BitVecVal(1, EXP_BITS), exp)
                      for sub, exp in zip(subnormals, exps)]
    debug_print("Effective exponents", effective_exps)

    max_exp = effective_exps[0]
    for exp in effective_exps[1:]:
        max_exp = If(UGT(exp, max_exp), exp, max_exp)
    debug_print("Max exponent", max_exp)

    # Construct full mantissas with implicit bits
    full_mants = [If(sub,
                     Concat(BitVecVal(0, 1), mant, gr),
                     Concat(BitVecVal(1, 1), mant, gr))
                  for sub, mant, gr in zip(subnormals, mants, grs)]
    debug_print("Full mantissas", full_mants)

    # Calculate shifts needed for each mantissa
    exp_diffs = []
    for exp in effective_exps:
        diff = max_exp - exp
        exp_diffs.append(ZeroExt(EXTENDED_BITS - EXP_BITS, diff))
    debug_print("Exponent differences", exp_diffs)

    # Align all mantissas and handle signs
    aligned_mants = []
    sticky_bits = []

    for i in range(len(inputs)):
        # Handle sign by negating if needed
        signed_mant = If(signs[i] == BitVecVal(1, 1),
                         ~full_mants[i] + 1,
                         full_mants[i])
        debug_print(f"Signed mantissa {i}", signed_mant)

        # Extend mantissa to full width
        extended_mant = ZeroExt(EXTENDED_BITS - FULL_MANT_BITS, signed_mant)
        debug_print(f"Extended mantissa {i}", extended_mant)

        # Create shift amount of matching width
        shift_amount = exp_diffs[i]

        # Calculate sticky bits before shift
        mask = (BitVecVal(1, EXTENDED_BITS) << shift_amount) - 1
        sticky = UGT(extended_mant & mask, BitVecVal(0, EXTENDED_BITS))
        debug_print(f"Mask for sticky {i}", mask)  # Add this debug line
        debug_print(f"Masked value {i}", extended_mant & mask)  # Add this debug line
        debug_print(f"Sticky bit set for value {i}", sticky)
        sticky_bits.append(sticky)

        # Perform arithmetic right shift
        shifted_mant = extended_mant >> shift_amount
        aligned_mants.append(shifted_mant)

    debug_print("Aligned mantissas", aligned_mants)

    # Sum all aligned mantissas
    sum_mant = aligned_mants[0]
    for mant in aligned_mants[1:]:
        sum_mant += mant
    debug_print("Sum before normalization", sum_mant)

    # Determine sign and take absolute value if negative
    is_negative = Extract(EXTENDED_BITS - 1, EXTENDED_BITS - 1, sum_mant) == BitVecVal(1, 1)
    abs_sum = If(is_negative, ~sum_mant + 1, sum_mant)

    # Normalize result
    leading_zeros = count_leading_zeros(abs_sum, EXP_BITS)
    debug_print("Leading zeros", leading_zeros)

    # Shift left to normalize
    normalized_sum = abs_sum << ZeroExt(EXTENDED_BITS - EXP_BITS, leading_zeros)
    debug_print("Normalized sum", normalized_sum)

    # Adjust exponent
    ext_bits = 2
    final_exp = If(ULE(leading_zeros, 2), max_exp + 2 - leading_zeros, max_exp + 2 - leading_zeros)
    #final_exp = max_exp - leading_zeros
    debug_print("Final exponent", final_exp)

    # Extract mantissa and GRS bits
    final_mant = Extract(MANT_BITS + GRS_BITS - 1, GRS_BITS, normalized_sum)
    grs_bits = Extract(GRS_BITS - 1 + ext_bits, ext_bits, normalized_sum)
    debug_print("Final mantissa", final_mant)
    debug_print("Final GRS bits", grs_bits)

    # Handle rounding
    guard_bit = Extract(2, 2, grs_bits)
    round_bit = Extract(1, 1, grs_bits)
    sticky_bit = Or(Or(*sticky_bits), Extract(0, 0, grs_bits) != BitVecVal(0, 1))

    # Round to nearest even
    round_up = And(guard_bit == BitVecVal(1, 1),
                   Or(sticky_bit,
                      round_bit == BitVecVal(1, 1),
                      Extract(0, 0, final_mant) == BitVecVal(1, 1)))

    # Apply rounding
    rounding_increment = If(round_up, BitVecVal(1, MANT_BITS), BitVecVal(0, MANT_BITS))
    rounded_mant = final_mant + rounding_increment
    debug_print("Rounded mantissa", rounded_mant)

    # Check for rounding overflow
    mant_overflow = ULT(rounded_mant, final_mant)
    final_exp = If(mant_overflow, final_exp + 1, final_exp)
    final_mant = If(mant_overflow,
                    Concat(BitVecVal(1, 1), Extract(MANT_BITS - 1, 1, rounded_mant)),
                    rounded_mant)

    # Handle special cases
    any_nan = Or(*nans)
    any_inf = Or(*infinities)
    all_zero = And(*zeros)

    final_exp = If(any_inf, result_exp_inf, final_exp)
    final_mant = If(any_inf, result_mant_inf, final_mant)
    final_mant = If(any_nan, result_mant_nan, final_mant)
    final_exp = If(any_nan, result_exp_inf, final_exp)
    final_exp = If(all_zero, BitVecVal(0, EXP_BITS), final_exp)
    final_mant = If(all_zero, BitVecVal(0, MANT_BITS), final_mant)

    debug_print("Final mantissa after special cases", final_mant)
    debug_print("Final exponent after special cases", final_exp)

    return fpBVToFP(Concat(BitVecVal(1, 1) if is_negative else BitVecVal(0, 1),
                           final_exp, final_mant), sort)