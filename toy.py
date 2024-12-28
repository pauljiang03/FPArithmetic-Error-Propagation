from z3 import *

Float16 = FPSort(5, 11)
Float32 = FPSort(8, 24)
Float64 = FPSort(11, 53)

def fp64_to_fp16(x):
    return fpFPToFP(RNE(), x, Float16)

def fp16_to_fp64(x):
    return fpFPToFP(RNE(), x, Float64)

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

s = Optimize()


# Create FP16 variables
x_test = FP('x', Float16)
y_test = FP('y', Float16)
z_test = FP('z', Float16)

roundup_x = fp16_to_fp64(x_test)
roundup_y = fp16_to_fp64(y_test)
roundup_z = fp16_to_fp64(z_test)

sum_16 = fpAdd(RNE(), x_test, y_test)
sum_16 = fpAdd(RNE(), z_test, sum_16)
sum_64 = fpAdd(RNE(), roundup_x, roundup_y)
sum_64 = fpAdd(RNE(), roundup_z, sum_64)

compare_16 = fp16_to_fp64(sum_16)


s.add(x_test > 0)
s.add(y_test > 0)
s.add(z_test > 0)
s.add(z_test == -4.9 * t)


s.add(Not(fpIsInf(compare_16)))
s.add(sum_64 != compare_16)
bvsumsum16 = fpToIEEEBV(compare_16)
bvsumsum64 = fpToIEEEBV(sum_64)
diff = If(bvsumsum64 > bvsumsum16, bvsumsum64 - bvsumsum16, bvsumsum16 - bvsumsum64)
h = s.maximize(diff)

if s.check() == sat:
    m = s.model()
    print("Values:")
    print(f"x = {m.eval(x_test)}")
    print(f"y = {m.eval(y_test)}")
    print(f"y = {m.eval(z_test)}")
    print(f"x_fp64 = {m.eval(roundup_x)}")
    print(f"y_fp64 = {m.eval(roundup_y)}")
    print(f"y_fp64 = {m.eval(roundup_z)}")
    print(f"sum64 = {m.eval(sum_64)}")
    print(f"sum16 = {m.eval(compare_16)}")
    print(f"diff = {m.eval(sum_64 - compare_16)}")
else:
    print("unsat")