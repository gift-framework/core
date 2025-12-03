# Utilities Reference

Helper functions for working with GIFT constants.

## Verification Functions

### `verify_relation`

Check that a relation holds exactly:

```python
from gift_core import verify_relation, B2, B3, DIM_G2, SIN2_THETA_W
from fractions import Fraction

# Verify sin²θ_W = b₂/(b₃ + dim G₂)
result = verify_relation(
    computed=Fraction(B2, B3 + DIM_G2),
    expected=SIN2_THETA_W
)
print(result)  # True
```

### `verify_all_relations`

Verify all 13 relations at once:

```python
from gift_core import verify_all_relations

results = verify_all_relations()
print(f"All verified: {all(results.values())}")
```

## Conversion Functions

### `to_decimal`

Convert a Fraction to decimal with specified precision:

```python
from gift_core import to_decimal, SIN2_THETA_W

value = to_decimal(SIN2_THETA_W, precision=10)
print(value)  # "0.2307692308"
```

### `to_latex`

Generate LaTeX representation:

```python
from gift_core import to_latex, SIN2_THETA_W

latex = to_latex(SIN2_THETA_W)
print(latex)  # "\\frac{3}{13}"
```

## Comparison Functions

### `compare_with_experiment`

Compare GIFT predictions with experimental values:

```python
from gift_core import compare_with_experiment

# Returns deviation in percent
deviation = compare_with_experiment(
    gift_value=0.23077,
    exp_value=0.23122,
    exp_error=0.00003
)
print(f"Deviation: {deviation:.2f}%")  # 0.19%
print(f"Within 1σ: {deviation < 0.03/0.23122*100}")
```

## Export Functions

### `export_to_dict`

Export all constants as a dictionary:

```python
from gift_core import export_to_dict

data = export_to_dict()
print(data['SIN2_THETA_W'])  # {'value': '3/13', 'float': 0.23076923...}
```

### `export_to_json`

Export all constants as JSON:

```python
from gift_core import export_to_json

json_str = export_to_json(indent=2)
print(json_str)
```

Output:
```json
{
  "topological_inputs": {
    "DIM_E8": 248,
    "B2": 21,
    "B3": 77,
    ...
  },
  "derived_relations": {
    "SIN2_THETA_W": "3/13",
    "TAU": "3472/891",
    ...
  }
}
```

## Formula Functions

### `compute_sin2_theta_w`

Compute sin²θ_W from Betti numbers:

```python
from gift_core import compute_sin2_theta_w

result = compute_sin2_theta_w(b2=21, b3=77, dim_g2=14)
print(result)  # Fraction(3, 13)
```

### `compute_tau`

Compute the hierarchy parameter:

```python
from gift_core import compute_tau

result = compute_tau(
    dim_e8xe8=496,
    b2=21,
    dim_j3o=27,
    h_star=99
)
print(result)  # Fraction(3472, 891)
```

### `compute_delta_cp`

Compute the CP violation phase:

```python
from gift_core import compute_delta_cp

result = compute_delta_cp(dim_g2=14, h_star=99)
print(result)  # 197
```

## Validation

### `is_valid_k7`

Check if Betti numbers are valid for a K₇ manifold:

```python
from gift_core import is_valid_k7

# Valid TCS construction
print(is_valid_k7(b2=21, b3=77))  # True

# Invalid
print(is_valid_k7(b2=20, b3=77))  # False
```
