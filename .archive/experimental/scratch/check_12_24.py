from fractions import Fraction

cot_pi_12_24_lower = Fraction(-488112137, 9671406556917033397649408)
cot_pi_12_24_upper = Fraction(-488112137, 9671406556917033397649408) # wait what is it actually?

cot_pi_1_2_lower = Fraction(-488112139, 9671406556917033397649408)
cot_pi_1_2_upper = Fraction(1671954449, 9671406556917033397649408)

print("cot_pi_12_24_lower <= cot_pi_1_2_lower ?", cot_pi_12_24_lower <= cot_pi_1_2_lower)
