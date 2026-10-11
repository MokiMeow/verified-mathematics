"""Count monomials in the actual Lean certificate RHS; this is not the proof."""
import ast
import json
import re
from pathlib import Path
import sympy

symbols = dict(zip("m a t r b v u".split(), sympy.symbols("m a t r b v u")))

def polynomial(node):
    if isinstance(node, ast.Expression):
        return polynomial(node.body)
    if isinstance(node, ast.Constant) and type(node.value) is int:
        return sympy.Integer(node.value)
    if isinstance(node, ast.Name) and node.id in symbols:
        return symbols[node.id]
    if isinstance(node, ast.BinOp):
        left, right = polynomial(node.left), polynomial(node.right)
        if isinstance(node.op, ast.Add):
            return left + right
        if isinstance(node.op, ast.Mult):
            return left * right
        if isinstance(node.op, ast.Pow) and right.is_Integer and right >= 0:
            return left ** right
    raise ValueError("Unsupported certificate expression")

source = Path("Kantorovich/ThreeCertificates.lean").read_text(encoding="utf-8")
expected = dict(zip(
    ["lower_cone_0", "lower_cone_1", "lower_cone_2",
     "reflectedUpper_cone_0", "reflectedUpper_cone_1", "reflectedUpper_cone_2"],
    [66, 71, 83, 89, 107, 115]))
actual = {}
for name, count in expected.items():
    block = source.split("theorem " + name + " ", 1)[1].split("set_option", 1)[0]
    rhs = re.search(r"have hid :.*?=\s*\n\s*(.*?)\s*:= by", block, re.S).group(1)
    expression = polynomial(ast.parse(rhs.replace("^", "**"), mode="eval"))
    poly = sympy.Poly(expression, *symbols.values())
    assert len(poly.terms()) == count
    assert all(c > 0 for c in poly.coeffs())
    actual[name] = len(poly.terms())
print(json.dumps({"monomial_counts": actual, "sympy_version": sympy.__version__,
                  "scope": "Actual Lean RHS counts only; Lean ring and positivity verify the identities and signs."}))
