with open("scratch/generate_k21.py", "r") as f:
    text = f.read()

text = text.replace("Real.cos {func_angle}", "Real.cos ({func_angle})")
text = text.replace("Real.sin {func_angle}", "Real.sin ({func_angle})")

with open("scratch/generate_k21.py", "w") as f:
    f.write(text)
