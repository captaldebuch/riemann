with open("scratch/generate_k21.py", "r") as f:
    text = f.read()

# We need to change the loop where we generate proofs
# to find the tightest bounds.

new_loop = """
    for a in sorted(bounds.keys()):
        if math.gcd(a, k) == 1 and 2*a <= k:
            a_ref = k - a
            # lo = max(bounds[a]['lo'], -bounds[a_ref]['up'])
            # up = min(bounds[a]['up'], -bounds[a_ref]['lo'])
            
            lo1_val = bounds[a]['lo']
            lo2_val = -bounds[a_ref]['up']
            if lo1_val >= lo2_val:
                target_lo_str = bounds[a]['lo_str']
            else:
                target_lo_str = "-" + (bounds[a_ref]['up_str'] if not bounds[a_ref]['up_str'].startswith("-") else bounds[a_ref]['up_str'][1:])
                # wait, if up_str is "-X", we want "X".
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
            f.write(proof + "\\n\\n")
"""

import re
text = re.sub(r"    for a in sorted\(bounds.keys\(\)\):.*?(?=    f.write\(\"end RH.Certificates.Generated\\\\n\"\))", new_loop, text, flags=re.DOTALL)

with open("scratch/generate_k21.py", "w") as f:
    f.write(text)
