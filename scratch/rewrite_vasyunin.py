import re

with open("RiemannHypothesis/Criteria/NymanBeurling/VasyuninSmallEntries.lean", "r") as f:
    content = f.read()

# Make sure we add the import at the top if it's not there
if "import RiemannHypothesis.Certificates.Generated.VasyuninPrimitiveBoundsGenerated" not in content:
    content = content.replace(
        "import RiemannHypothesis.Criteria.NymanBeurling.VasyuninGram",
        "import RiemannHypothesis.Criteria.NymanBeurling.VasyuninGram\nimport RiemannHypothesis.Certificates.Generated.VasyuninPrimitiveBoundsGenerated"
    )

# The pattern matches the axiom and its bounds.
# Example:
# axiom vasyuninBEntry_12_formula_bound :
#     (((3861 / 5000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 2) ∧
#     (vasyuninBEntryFormula 1 2 ≤ ((7723 / 10000 : ℚ) : ℝ))

pattern = r"axiom (vasyuninBEntry_\d+_formula_bound) :\s*\n\s*\(\(\([^)]+\) : ℝ\) ≤ (vasyuninBEntryFormula \d+ \d+)\) ∧\s*\n\s*\(\2 ≤ \(\([^)]+\) : ℝ\)\)"

def replace_axiom(m):
    axiom_name = m.group(1)
    original_text = m.group(0)
    # Reconstruct the theorem based on the original bounds text
    lines = original_text.split('\n')
    lines[0] = lines[0].replace('axiom', 'theorem')
    
    # We append the proof
    proof = f" := by\n  have h := RH.Certificates.Generated.{axiom_name}\n  constructor\n  · have h1 := h.1; linarith\n  · have h2 := h.2; linarith"
    
    return '\n'.join(lines) + proof

new_content, count = re.subn(pattern, replace_axiom, content)
print(f"Replaced {count} formula bounds axioms.")

with open("RiemannHypothesis/Criteria/NymanBeurling/VasyuninSmallEntries.lean", "w") as f:
    f.write(new_content)
