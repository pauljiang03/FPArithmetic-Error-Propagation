from z3 import *


def is_infinity(exp, mant, exp_bits):
    return And(exp == (2 ** exp_bits - 1), mant == 0)


def is_n(exp, mant, exp_bits):
    return And(exp == (2 ** exp_bits - 1), mant != 0)


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



class BlockFPAdder:
    def __init__(self, sort: FPSortRef):
        self.sort = sort
        self.SIGN_BITS = 1
        self.EXP_BITS = sort.ebits()
        self.MANT_BITS = sort.sbits() - 1
        self.GRS_BITS = 3
        self.TOTAL_BITS = self.SIGN_BITS + self.EXP_BITS + self.MANT_BITS + self.GRS_BITS
        self.FULL_MANT_BITS = 1 + self.MANT_BITS + self.GRS_BITS
        self.EXTENDED_MANT_BITS = self.FULL_MANT_BITS + 1

        # Constants for special values
        self.result_exp_inf = BitVecVal(2 ** self.EXP_BITS - 1, self.EXP_BITS)
        self.result_mant_nan = BitVecVal((1 << self.MANT_BITS) - 1, self.MANT_BITS)
        self.result_mant_inf = BitVecVal(0, self.MANT_BITS)

        # Initialize accumulator state
        self.reset()

    def reset(self):
        """Reset accumulator state"""
        self.acc_exp = None
        self.acc_mant = None
        self.acc_sign = None
        self.sticky_bits = False
        self.has_nan = False
        self.has_infinity = False
        self.infinity_sign = None
        self.seen_opposing_infinities = False

    def _prepare_operand(self, x: FPRef):
        """Convert FP number to internal representation with extended precision"""
        a = Concat(fpToIEEEBV(x), BitVecVal(0, self.GRS_BITS))

        sign = Extract(self.TOTAL_BITS - 1, self.TOTAL_BITS - self.SIGN_BITS, a)
        exp = Extract(self.TOTAL_BITS - self.SIGN_BITS - 1,
                      self.TOTAL_BITS - self.SIGN_BITS - self.EXP_BITS, a)
        mant = Extract(self.TOTAL_BITS - self.SIGN_BITS - self.EXP_BITS - 1, self.GRS_BITS, a)
        grs = Extract(self.GRS_BITS - 1, 0, a)

        # Check special cases
        is_inf = is_infinity(exp, mant, self.EXP_BITS)
        is_nan = is_n(exp, mant, self.EXP_BITS)
        is_zero = And(exp == 0, mant == 0)
        is_subnormal = And(exp == 0, mant != 0)

        # Handle subnormal numbers
        effective_exp = If(is_subnormal, BitVecVal(1, self.EXP_BITS), exp)
        full_mant = If(is_subnormal,
                       Concat(BitVecVal(0, 1), mant, grs),
                       Concat(BitVecVal(1, 1), mant, grs))

        return sign, exp, effective_exp, full_mant, is_inf, is_nan, is_zero, is_subnormal

    def add_number(self, x: FPRef):
        """Add a number to the accumulator"""
        sign, exp, effective_exp, full_mant, is_inf, is_nan, is_zero, is_subnormal = self._prepare_operand(x)

        # Handle special cases
        if is_nan:
            self.has_nan = True
            return

        if is_inf:
            if self.has_infinity and self.infinity_sign != sign:
                self.seen_opposing_infinities = True
                self.has_nan = True
                return
            self.has_infinity = True
            self.infinity_sign = sign
            return

        if is_zero and self.acc_mant is None:
            self.acc_sign = sign
            self.acc_exp = BitVecVal(0, self.EXP_BITS)
            self.acc_mant = BitVecVal(0, self.EXTENDED_MANT_BITS)
            return

        if self.acc_mant is None:
            # First non-zero number, initialize accumulator
            self.acc_sign = sign
            self.acc_exp = effective_exp
            self.acc_mant = ZeroExt(1, full_mant)  # Extra bit for carries
            return

        # Align mantissas based on exponent difference
        exp_diff = If(BV2Int(self.acc_exp) >= BV2Int(effective_exp),
                      ZeroExt(self.FULL_MANT_BITS - self.EXP_BITS, self.acc_exp) -
                      ZeroExt(self.FULL_MANT_BITS - self.EXP_BITS, effective_exp),
                      ZeroExt(self.FULL_MANT_BITS - self.EXP_BITS, effective_exp) -
                      ZeroExt(self.FULL_MANT_BITS - self.EXP_BITS, self.acc_exp))

        # Determine if we're adding or subtracting based on signs
        subtract = self.acc_sign != sign

        # Determine which number is larger for subtraction
        a_larger = If(UGT(self.acc_exp, effective_exp), True,
                      If(self.acc_exp == effective_exp,
                         UGE(self.acc_mant, ZeroExt(1, full_mant)), False))

        # Handle subtraction
        if subtract:
            if a_larger:
                full_mant = ~full_mant + 1
            else:
                temp_mant = self.acc_mant
                self.acc_mant = ZeroExt(1, full_mant)
                self.acc_sign = sign
                full_mant = ~temp_mant + 1

        # Align mantissas
        max_shift = BitVecVal(self.FULL_MANT_BITS - 1, self.FULL_MANT_BITS)
        if BV2Int(self.acc_exp) >= BV2Int(effective_exp):
            aligned_mant = SignExt(1, full_mant >> exp_diff)
            # Track sticky bits
            self.sticky_bits = Or(self.sticky_bits,
                                  If(ULT(exp_diff, max_shift),
                                     any_last_bits_set(full_mant, exp_diff),
                                     UGT(full_mant, 0)))
        else:
            old_acc_mant = self.acc_mant
            self.acc_mant = ZeroExt(1, full_mant)
            aligned_mant = SignExt(1, old_acc_mant >> exp_diff)
            self.acc_exp = effective_exp
            self.sticky_bits = Or(self.sticky_bits,
                                  If(ULT(exp_diff, max_shift),
                                     any_last_bits_set(old_acc_mant, exp_diff),
                                     UGT(old_acc_mant, 0)))

        # Add mantissas
        self.acc_mant = self.acc_mant + aligned_mant

    def normalize_and_round(self) -> FPRef:
        """Normalize accumulated sum and convert back to FP number"""
        # Handle special cases
        if self.has_nan or self.seen_opposing_infinities:
            return Concat(BitVecVal(0, self.SIGN_BITS),
                          self.result_exp_inf,
                          self.result_mant_nan)

        if self.has_infinity:
            return Concat(self.infinity_sign,
                          self.result_exp_inf,
                          self.result_mant_inf)

        if self.acc_mant is None:
            return fpZero(self.sort)

        if is_zero(self.acc_exp, Extract(self.MANT_BITS - 1, 0, self.acc_mant)):
            return Concat(self.acc_sign,
                          BitVecVal(0, self.EXP_BITS),
                          BitVecVal(0, self.MANT_BITS))

        # Count leading zeros for normalization
        lz_count = count_leading_zeros(self.acc_mant, self.EXP_BITS)

        # Prevent underflow
        lz_count = If(UGT(lz_count, self.acc_exp), self.acc_exp, lz_count)

        # Normalize mantissa
        normalized_mant = self.acc_mant << ZeroExt(self.acc_mant.size() - self.EXP_BITS, lz_count)

        # Extract components for rounding
        final_mant = Extract(self.MANT_BITS + self.GRS_BITS - 1, self.GRS_BITS, normalized_mant)
        guard_bit = Extract(self.GRS_BITS - 1, self.GRS_BITS - 1, normalized_mant)
        round_bit = Extract(self.GRS_BITS - 2, self.GRS_BITS - 2, normalized_mant)
        sticky_bit = Or(self.sticky_bits,
                        Extract(self.GRS_BITS - 3, 0, normalized_mant) != 0)

        # Round (using round-to-nearest-even)
        round_up = And(guard_bit == 1,
                       Or(sticky_bit == 1,
                          round_bit == 1,
                          Extract(0, 0, final_mant) == 1))

        if round_up:
            final_mant = final_mant + 1

        # Adjust exponent
        final_exp = self.acc_exp - lz_count

        # Handle overflow from rounding
        if Extract(self.MANT_BITS, self.MANT_BITS, final_mant) == 1:
            final_exp = final_exp + 1
            final_mant = Extract(self.MANT_BITS - 1, 0, final_mant)

        # Overflow check
        if UGE(final_exp, self.result_exp_inf):
            return Concat(self.acc_sign,
                          self.result_exp_inf,
                          self.result_mant_inf)

        # Construct final FP number
        result = Concat(self.acc_sign, final_exp, final_mant)
        return fpBVToFP(result, self.sort)