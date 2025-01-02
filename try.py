from z3 import *

Float16 = FPSort(5, 11)
Float32 = FPSort(8, 24)
Float64 = FPSort(11, 53)

def fp64_to_fp16(x):
    return fpFPToFP(RNE(), x, Float16)
def fp16_to_fp32(x):
    return fpFPToFP(RNE(), x, Float32)
def fp64_to_fp32(x):
    return fpFPToFP(RNE(), x, Float32)

def fp32_to_fp16(x):
    return fpFPToFP(RNE(), x, Float16)

def fp_to_bv(fp, sort):
    return fpToIEEEBV(fp)

def bv_to_binary_str(bv):
    return bin(bv.as_long())[2:].zfill(bv.size())

def format_fp(binary_str, exp_bits, frac_bits):
    sign = binary_str[0]
    exp = binary_str[1:1+exp_bits]
    frac = binary_str[1+exp_bits:]
    return f"S:{sign} E:{exp} M:{frac}"

s = Solver()

x_test = FP('x', Float16)
y_test = FP('y', Float16)
z_test = FP('z', Float16)
t = FP('t', Float16)

roundup_x = fp16_to_fp32(x_test)
roundup_y = fp16_to_fp32(y_test)
roundup_z = fp16_to_fp32(z_test)

sum_16 = fpAdd(RNE(), x_test, y_test)
sum_16 = fpAdd(RNE(), z_test, sum_16)
sum_32 = fpAdd(RNE(), roundup_x, roundup_y)
sum_32 = fpAdd(RNE(), roundup_z, sum_32)

compare_16 = fp16_to_fp32(sum_16)

s.add(x_test == 234)
s.add(And(t >= 0, t <= 1))
s.add(y_test == 48 * t)
s.add(z_test == -4.9 * t * t)
s.add(Not(fpIsInf(compare_16)))
s.add(sum_32 != compare_16)
diff = If(compare_16 > sum_32, fpSub(RNE(), compare_16, sum_32), fpSub(RNE(), sum_32, compare_16))
s.add(diff == 1*(2**-2))

if s.check() == sat:
    m = s.model()
    print("Values:")
    print(f"x = {m.eval(x_test)}")
    print(f"y = {m.eval(y_test)}")
    print(f"z = {m.eval(z_test)}")
    print(f"t = {m.eval(t)}")
    print(f"x_fp64 = {m.eval(roundup_x)}")
    print(f"y_fp64 = {m.eval(roundup_y)}")
    print(f"z_fp64 = {m.eval(roundup_z)}")
    print(f"sum64 = {m.eval(sum_32)}")
    print(f"sum16 = {m.eval(compare_16)}")
    print(f"diff = {m.eval(sum_32 - compare_16)}")

    diff_val = m.eval(fpToIEEEBV(diff))
    binary_str = bv_to_binary_str(diff_val)
    print(f"Diff as binary: {binary_str}")

    sum32_binary = bv_to_binary_str(m.eval(fpToIEEEBV(sum_32)))
    sum16_binary = bv_to_binary_str(m.eval(fpToIEEEBV(compare_16)))

    print("\nBinary representations:")
    print(f"sum32: {format_fp(sum32_binary, 8, 23)}")
    print(f"sum16: {format_fp(sum16_binary, 8, 23)}")
else:
    print("unsat")