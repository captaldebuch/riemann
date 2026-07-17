import os
import glob

def replace_in_file(filepath):
    with open(filepath, 'r') as f:
        content = f.read()

    replacements = {
        "We formalize the Nyman–Beurling criterion in Lean 4, proving that": "We outline an exploratory formalization model of the Nyman–Beurling criterion in Lean 4, exploring how",
        "We formalize the Nyman–Beurling criterion in Lean 4, establishing that": "We outline an exploratory formalization model of the Nyman–Beurling criterion in Lean 4, experimentally modeling how",
        "We formalize a conditional approach to": "We outline a conditional, exploratory approach to",
        "proven via: (1)": "experimentally modeled via: (1)",
        "We formalize all nine propositions": "We experimentally map and model all nine propositions",
        "We formalize the Hilbert space structure": "We experimentally model the Hilbert space structure",
        "We formalize the Bettin–Conrey–Farmer": "We outline an exploratory formalization model of the Bettin–Conrey–Farmer",
        "proving the main term emerges": "experimentally modeling how the main term emerges",
        "we establish $E_N^{BCF}": "we model $E_N^{BCF}",
        "We formalize this phenomenon in Lean 4, explicitly stating the hypotheses required (RH, zero simplicity, moment bound) and proving the resulting asymptotic expansion:": "We experimentally model this phenomenon in Lean 4, explicitly stating the hypotheses required (RH, zero simplicity, moment bound) and exploring the resulting asymptotic expansion:"
    }

    new_content = content
    for old, new in replacements.items():
        new_content = new_content.replace(old, new)
        
    if new_content != content:
        with open(filepath, 'w') as f:
            f.write(new_content)
        print(f"Updated {filepath}")

for root, _, files in os.walk('doc/html'):
    for file in files:
        if file.endswith('.js') or file.endswith('.html'):
            replace_in_file(os.path.join(root, file))

