with open("RiemannHypothesis/Certificates/Generated/CotangentBoundsK21.lean", "r") as f:
    text = f.read()

text = text.replace("cos_sin_base_bound", "RH.Certificates.TrigIntervalDemo.cos_sin_base_bound")
text = text.replace("cos_sin_double_bound", "RH.Certificates.TrigIntervalDemo.cos_sin_double_bound")

with open("RiemannHypothesis/Certificates/Generated/CotangentBoundsK21.lean", "w") as f:
    f.write(text)

with open("RiemannHypothesis/Certificates/Generated/VasyuninPrimitiveBoundsCore.lean", "r") as f:
    lines = f.readlines()

if "import RiemannHypothesis.Certificates.Generated.CotangentBoundsK21\n" not in lines:
    idx = 0
    for i, line in enumerate(lines):
        if line.startswith("import RiemannHypothesis.Certificates.Generated.CotangentBounds"):
            idx = i
    lines.insert(idx + 1, "import RiemannHypothesis.Certificates.Generated.CotangentBoundsK21\n")
    
    with open("RiemannHypothesis/Certificates/Generated/VasyuninPrimitiveBoundsCore.lean", "w") as f:
        f.writelines(lines)
        
print("Fixes applied.")
