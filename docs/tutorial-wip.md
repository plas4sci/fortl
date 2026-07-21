# Fortl tutorial

## Syntax

The syntax of Fortl is based on that of Python.

## Primitive types

There are a number of built-in types in Fortl that are
'unadorned', i.e., they do not carry any additional type information:

- `float` equivalent to `Float[{Base}][1]`
- `str` equivalent to `String[{Base}][1]`
- `integer` equivalent to `Integer[{Base}][1]`

Example:
```
x : float = 1.0
y : Float[{Base}][1] = x + 2.0
it : float = y * 3.0
```
In this example, we are mixing the unadorned alias for
floating-point types with a graded floating point type
with the unit grade.