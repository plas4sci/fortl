# Fortl - A language for descriptive and prescriptive scientific code

<table><tr><td valign="top" width="160">
  <img src="logo.png" alt="Fortl logo" width="140"/>
</td><td valign="top">

**Fortl** is a programming language for scientific and numerical computing with rich, graded types.

- **Statically-typed**: say what you mean, enforce what you need
- **Graded numerical types**: types are indexed and carry structure, allowing for domain-specific properties to be expressed (and enforced) in the type system;

- **Python-like syntax**: lower barrier to entry

</td></tr></table>

## Example

```fortl
"""
Simple example showing units and quantities
"""
x : Float[Unit[m] & Quantity[length]] = 2.0
y : Float[Unit[m] & Quantity[length]] = 1.0
t : Float[Unit[s] & Quantity[time]] = 4.0
# End result
it : Float[Unit[m / s] & Quantity[length / time]] = (x + y) / t
```

## Building and Installing

Fortl is built with [Stack](https://docs.haskellstack.org/).

**Prerequisites**: [GHC 9.2.5](https://www.haskell.org/ghc/) and Stack installed.

**Build:**

```bash
stack build
```

**Run a file:**

```bash
stack exec fortl -- <file.frtl>
```

**Interactive REPL:**

```bash
stack exec fortli
```

**Install executables to your PATH:**

```bash
stack install
```

After installing, `fortl` and `fortli` will be available as commands directly.

## Contributing

This project is in its early stages, but we would welcome
any contributions, bug reports, or feature requests. Please start by raising an issue if you want to contribute or have a question.