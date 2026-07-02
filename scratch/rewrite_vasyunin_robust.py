with open("RiemannHypothesis/Criteria/NymanBeurling/VasyuninSmallEntries.lean", "r") as f:
    lines = f.readlines()

new_lines = []
i = 0
count = 0
while i < len(lines):
    line = lines[i]
    if line.startswith("axiom vasyuninBEntry_") and "_formula_bound :" in line:
        # found an axiom
        axiom_name = line.split("axiom ")[1].split(" :")[0].strip()
        new_lines.append(f"theorem {axiom_name} :\n")
        
        # collect the next two lines which contain the inequalities
        i += 1
        bound_1 = lines[i]
        i += 1
        bound_2 = lines[i]
        
        new_lines.append(bound_1)
        # bound_2 may or may not end with newline, ensure it does
        if bound_2.endswith("\n"):
            bound_2 = bound_2[:-1]
            
        # replace the axiom with a theorem using the exact same bounds
        new_lines.append(f"{bound_2} := by\n")
        new_lines.append(f"  have h := RH.Certificates.Generated.{axiom_name}\n")
        new_lines.append(f"  constructor\n")
        new_lines.append(f"  · have h1 := h.1; linarith\n")
        new_lines.append(f"  · have h2 := h.2; linarith\n")
        count += 1
    else:
        new_lines.append(line)
    i += 1

print(f"Replaced {count} formula bounds axioms.")
with open("RiemannHypothesis/Criteria/NymanBeurling/VasyuninSmallEntries.lean", "w") as f:
    f.writelines(new_lines)
