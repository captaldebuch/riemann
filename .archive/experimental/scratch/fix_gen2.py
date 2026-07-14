import re
with open("scratch/generate_k21.py", "r") as f:
    text = f.read()

text = text.replace("N = 28", "N = 32")
text = text.replace("den = 2**100", "den = 2**250")
text = text.replace("den = 2**(100 - i)", "den = 2**(250 - i)")

with open("scratch/generate_k21.py", "w") as f:
    f.write(text)

