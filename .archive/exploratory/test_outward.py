import flint
import math
from fractions import Fraction

def outward_round_lower(x_arb, denom=10**12):
    guess_f = float(x_arb.lower())
    num = math.floor(guess_f * denom)
    while True:
        q = flint.fmpq(num, denom)
        if x_arb >= q:
            return Fraction(num, denom)
        num -= 1

def outward_round_upper(x_arb, denom=10**12):
    guess_f = float(x_arb.upper())
    num = math.ceil(guess_f * denom)
    while True:
        q = flint.fmpq(num, denom)
        if x_arb <= q:
            return Fraction(num, denom)
        num += 1

flint.ctx.dps = 50
log_2pi = flint.arb.pi() * 2
log_2pi = log_2pi.log()
print(log_2pi)

lower = outward_round_lower(log_2pi)
upper = outward_round_upper(log_2pi)
print(f"Lower: {lower} ({float(lower)})")
print(f"Upper: {upper} ({float(upper)})")
print(f"Check lower <= upper: {lower <= upper}")
