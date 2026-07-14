import math

table = []
needed = 0

for k in range(2, 51):
    for h in range(1, k):
        if max(h, k) > 20:
            d = math.gcd(h, k)
            hp, kp = h // d, k // d
            prim = "primitive" if d == 1 else "reducible"
            table.append(f"{h} {k} | gcd={d} | {prim} | numeric_trust_{h}_{k} | vasyuninBEntry_{hp}{kp}_formula_bound")
            if d == 1:
                needed += 1

print(f"Total fallback entries for h < k <= 50 with max > 20: {len(table)}")
print(f"Total NEW primitive bounds needed: {needed}")

with open("scratch/phase10P_table.txt", "w") as f:
    f.write("h k | gcd | type | current fallback | target transparent\n")
    f.write("-" * 60 + "\n")
    for row in table[:20]: # show first 20 as sample
        f.write(row + "\n")
    f.write("... (and so on)\n")
