# Fortl - A language for descriptive and prescriptive scientific code

<table style="border-width:0;"><tr><td valign="top" width="160">
  <img src="logo.png" alt="Fortl logo" width="140"/>
</td><td valign="top">

**Fortl** is a programming language for scientific and numerical computing.

**System principles/values**. Code should enable:

- _Codifying human scientific knowledge_;
- _Expressing meaning, inntent, and limitations of scientific models_;
- _Computation of predictions in a way that is repeatable, reusable, and reproducable_

How does this work out technically?

- **Statically-typed**: say what you mean, enforce what you need
- **Graded numerical types**: types are indexed and carry structure, allowing for domain-specific properties to be expressed (and enforced) in the type system;
- **Python-like syntax**: lower barrier to entry

</td></tr></table>

## Example and usage

From [examples/quantity.frtl](examples/quantity.frtl):

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
Running `fortl examples/quantity.frtl` produces:
```
Well-typed as Float[{(UoM & KoQ)}][(Unit[(m * s^-1.0)] & Quantity[(length * time^-1.0)])]
0.75
```
The type checker verifies the units and quantities are consistent, and evaluates the result `(2.0 + 1.0) / 4.0 = 0.75` with inferred type `Float[Unit[m/s] & Quantity[length/time]]`.

### REPL

The interactive REPL (`fortli`) supports interactive evaluation and type inference. You can:

- **Evaluate an expression** — type any expression and press Enter
- **Infer a type** — `:t expr` infers the type of an expression; `:k type` infers the kind of a type
- **Load a file** — `:l path/to/file.frtl` runs type inference on the file and loads its definitions into the environment
- **Get help** — `:h` lists all available commands
- **Quit** — `:q`

**Example session:**

```bash
% fortli
...
[F]> :l examples/units.frtl
Well-typed as Float[{UoM}][Unit[(M * S^-1.0)]]
0.25
units> x
1.0
units> :t x
Float[{UoM}][Unit[M]]
units> :k Float
{d : Descriptor} -> d -> Type
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

## Background

`fortl` is based on ideas around using 'graded monoids' (due to McBride and Nordvall-Forsberg) appearing in this paper:

* [Type systems for programs respecting dimensions (McBride, Conor, and Fredrik Nordvall-Forsberg); Advanced Mathematical and Computational Tools in Metrology and Testing XII. 2021. 331-345.](https://strathprints.strath.ac.uk/76626/1/McBride_etal_amctmtxii2021_type_systems_for_programs_respecting_dimensions.pdf)

and early ideas we had about building languages for science, in this paper:

* [A computational science agenda for programming language research (Orchard, Dominic, and Andrew Rice); Procedia Computer Science 29 (2014): 713-727.](https://www.cs.kent.ac.uk/people/staff/dao7/publ/iccs14-orchard-rice.pdf)

There are some similarities to [F#](https://learn.microsoft.com/en-us/dotnet/fsharp/language-reference/units-of-measure) but fortl's aim is to be much more general and flexible, going beyond units-of-measure.


## Contributing

This project is in its early stages, but we would welcome
any contributions, bug reports, or feature requests. Please start by raising an issue if you want to contribute or have a question.
