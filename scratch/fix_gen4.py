with open("scratch/generate_k21.py", "r") as f:
    text = f.read()

old_loop = """    for a in sorted(bounds.keys()):
        if math.gcd(a, k) == 1 and 2*a <= k:
            proof = gen_proof(a, k, bounds[a]['lo_str'], bounds[a]['up_str'])
            f.write(proof + "\\n\\n")"""

new_loop = """    for a in sorted(bounds.keys()):
        if math.gcd(a, k) == 1 and 2*a <= k:
            a_ref = k - a
            
            lo1_val = bounds[a]['lo']
            lo2_val = -bounds[a_ref]['up']
            if lo1_val >= lo2_val:
                target_lo_str = bounds[a]['lo_str']
            else:
                if bounds[a_ref]['up_str'].startswith("-"):
                    target_lo_str = bounds[a_ref]['up_str'][1:]
                else:
                    target_lo_str = "-" + bounds[a_ref]['up_str']
                    
            up1_val = bounds[a]['up']
            up2_val = -bounds[a_ref]['lo']
            if up1_val <= up2_val:
                target_up_str = bounds[a]['up_str']
            else:
                if bounds[a_ref]['lo_str'].startswith("-"):
                    target_up_str = bounds[a_ref]['lo_str'][1:]
                else:
                    target_up_str = "-" + bounds[a_ref]['lo_str']
                    
            proof = gen_proof(a, k, target_lo_str, target_up_str)
            f.write(proof + "\\n\\n")"""

text = text.replace(old_loop, new_loop)

with open("scratch/generate_k21.py", "w") as f:
    f.write(text)

