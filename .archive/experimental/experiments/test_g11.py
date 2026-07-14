import math

def G11UnitIntegralFormula(n):
    return 1 + n/(n+1) - 2*n*math.log((n+1)/n)

def G11UnitFormulaPartialSum(N):
    return 1 + sum(G11UnitIntegralFormula(n) for n in range(1, N+1))

def G11FiniteClosedForm(N):
    harmonic = sum(1/k for k in range(1, N+2))
    return 2*N + 2 - harmonic - 2*(N+1)*math.log(N+1) + 2*math.log(math.factorial(N+1))

for i in range(1, 5):
    print(f"N={i}")
    print(f"  Sum:  {G11UnitFormulaPartialSum(i)}")
    print(f"  Form: {G11FiniteClosedForm(i)}")
    print(f"  Diff: {G11UnitFormulaPartialSum(i) - G11FiniteClosedForm(i)}")
