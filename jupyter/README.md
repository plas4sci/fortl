# fortl Jupyter kernel

A Jupyter kernel for fortl. Cells run cumulatively, like a notebook: each
cell sees the definitions from earlier cells, and its output is the type and
value of its last definition. A cell with no definitions is evaluated as an
expression.

## Setup

    python3 -m venv jupyter/.venv
    jupyter/.venv/bin/pip install jupyterlab -e jupyter/
    jupyter/.venv/bin/python -m fortl_kernel.install

This registers a `fortl` kernel for your user, so it also shows up in VS Code
notebooks. Needs `fortl` on the PATH at install time (`stack install`).

## Use

Start JupyterLab from the **repository root** (so notebooks can reach
`examples/` and `articles/`):

    jupyter/lab.sh jupyter/geotherm.ipynb

`lab.sh` also turns on `~/.jupyter/custom/custom.css`, which sets markdown cells
in Latin Modern. To set this up:

    mkdir -p ~/.jupyter/custom && cp jupyter/custom.css ~/.jupyter/custom/
    cp articles/fonts/*.otf ~/Library/Fonts/      # macOS user fonts
 In VS Code the
same look comes from `notebook.markup.fontFamily` in `.vscode/settings.json`.

- **Tab** completes names; **Shift-Tab** on a name shows its type and value.
- `%file path [a-b] [show=name]` shows (part of) a file, with a link that opens
  it in the editor, and runs it.
- `%load path` adds a file's definitions to the session.
- `%program` shows the accumulated program; `%reset` clears it.
