from .helpers import *
from typing import List

#TODO: need to fix addition of subnormals (it tries to normalize, BAD)
#TODO: need to fix overflow to infinity
#TODO: need to implement negative number handling

def fp_multi_sum(inputs: List[FPRef], sort: FPSortRef, debug_solver=None):
    if not inputs:
        return None
    if len(inputs) == 1:
        return inputs[0]

    SIGN_BITS = 1
    EXP_BITS = sort.ebits()
    MANT_BITS = sort.sbits() - 1
    TOTAL_BITS = SIGN_BITS + EXP_BITS + MANT_BITS
    FULL_MANT_BITS = 1 + MANT_BITS
    EXTENDED_BITS = FULL_MANT_BITS + 2

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
                        print(f"{msg}: {1 if eval_val else 0}")
                    else:
                        eval_val = m.eval(val)
                        print(f"{msg}: {bin(eval_val.as_long())[2:].zfill(val.size())}")
                except:
                    print(f"{msg}: Could not evaluate")

    result_exp_inf = BitVecVal(2 ** EXP_BITS - 1, EXP_BITS)
    result_mant_nan = BitVecVal((1 << MANT_BITS) - 1, MANT_BITS)
    result_mant_inf = BitVecVal(0, MANT_BITS)

    values = [fpToIEEEBV(x) for x in inputs]
    debug_print("Initial values", values)

    components = [split_input_trun(v, TOTAL_BITS, SIGN_BITS, EXP_BITS) for v in values]
    signs = [c[0] for c in components]
    exps = [c[1] for c in components]
    mants = [c[2] for c in components]

    debug_print("Signs", signs)
    debug_print("Exponents", exps)
    debug_print("Mantissas", mants)

    infinities = [is_infinity(e, m, EXP_BITS) for e, m in zip(exps, mants)]
    nans = [is_nan(e, m, EXP_BITS) for e, m in zip(exps, mants)]
    zeros = [is_zero(e, m) for e, m in zip(exps, mants)]
    subnormals = [e == BitVecVal(0, EXP_BITS) for e in exps]

    effective_exps = [If(sub, BitVecVal(1, EXP_BITS), exp)
                      for sub, exp in zip(subnormals, exps)]
    debug_print("Effective exponents", effective_exps)

    max_exp = effective_exps[0]
    for exp in effective_exps[1:]:
        max_exp = If(UGT(exp, max_exp), exp, max_exp)
    debug_print("Max exponent", max_exp)

    full_mants = [If(sub,
                     Concat(BitVecVal(0, 1), mant),
                     Concat(BitVecVal(1, 1), mant))
                  for sub, mant in zip(subnormals, mants)]
    debug_print("Full mantissas", full_mants)

    exp_diffs = []
    for exp in effective_exps:
        diff = max_exp - exp
        exp_diffs.append(ZeroExt(EXTENDED_BITS - EXP_BITS, diff))
    debug_print("Exponent differences", exp_diffs)

    aligned_mants = []

    for i in range(len(inputs)):
        signed_mant = If(signs[i] == BitVecVal(1, 1),
                         ~full_mants[i] + 1,
                         full_mants[i])
        debug_print(f"Signed mantissa {i}", signed_mant)

        extended_mant = ZeroExt(EXTENDED_BITS - FULL_MANT_BITS, signed_mant)
        debug_print(f"Extended mantissa {i}", extended_mant)

        shift_amount = exp_diffs[i]
        shifted_mant = extended_mant >> shift_amount
        aligned_mants.append(shifted_mant)

    debug_print("Aligned mantissas", aligned_mants)

    sum_mant = aligned_mants[0]
    for mant in aligned_mants[1:]:
        sum_mant += mant
    debug_print("Sum before normalization", sum_mant)

    is_negative = Extract(EXTENDED_BITS - 1, EXTENDED_BITS - 1, sum_mant) == BitVecVal(1, 1)

    leading_zeros = count_leading_zeros(sum_mant, EXP_BITS)
    debug_print("Leading zeros", leading_zeros)

    normalized_sum = sum_mant << ZeroExt(EXTENDED_BITS - EXP_BITS, leading_zeros)
    debug_print("Normalized sum", normalized_sum)

    final_exp = If(ULE(leading_zeros, 2), max_exp + 2 - leading_zeros, max_exp + 2 - leading_zeros)
    debug_print("Final exponent", final_exp)

    final_mant = Extract(EXTENDED_BITS - 2, EXTENDED_BITS - MANT_BITS - 1, normalized_sum)
    debug_print("Final mantissa", final_mant)

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