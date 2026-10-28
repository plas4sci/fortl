"""
A Jupyter kernel for fortl.

Cells are run cumulatively, like the Quarto filter in articles/: each
cell is appended to the definitions of all earlier (successful) cells
and the whole program is run through the `fortl` executable. The type
and value of the last definition in the cell is shown as its result.

A cell containing no top-level definitions is treated as an expression
and evaluated against the current definitions, without being kept.

Magics (on the first line of a cell):
  %file path [a-b] [show=name]   show (part of) a file, and run it
  %load path                     add a file's definitions to the session
  %program                       show the accumulated program
  %reset                         forget all definitions
"""

import html
import os
import re
import subprocess
import tempfile

from ipykernel.kernelbase import Kernel

from . import __version__
from .highlight import highlight

FORTL = os.environ.get("FORTL_COMMAND", "fortl")

KEYWORDS = ["lambda", "if", "else", "and", "or", "not", "let", "in",
            "case", "of", "import", "from", "True", "False", "None",
            "Float", "Int", "Unit", "Quantity", "sqrt"]

BINDING = re.compile(r"^([A-Za-z_][\w']*)\s*(?::|=(?!=))")
ANSI = re.compile(r"\x1b\[[\d;]*m")
IDENT = re.compile(r"[A-Za-z_][\w']*")

# Inline styles, since JupyterLab strips <style> from untrusted outputs
OUT_STYLE = ("margin:0; padding:0.4em 0.8em; border-left:3px solid #2e8b57; "
             "white-space:pre-wrap; background:transparent;")
FILE_STYLE = ("font-size:0.85em; padding:0.3em 0.8em; background:#f3f3f3; "
              "border:1px solid #ddd; border-bottom:none; border-radius:4px 4px 0 0;")
CODE_STYLE = ("margin-top:0; padding:0.6em 0.8em; border:1px solid #ddd; "
              "border-radius:0 0 4px 4px;")
TYPE_STYLE = "color:#555;"


def last_binding(src):
    """Name of the last top-level definition, skipping docstrings."""
    name, in_doc = None, False
    for line in src.splitlines():
        quotes = line.count('"""')
        if in_doc:
            if quotes % 2 == 1:
                in_doc = False
        elif quotes % 2 == 1:
            in_doc = True
        else:
            m = BINDING.match(line)
            if m:
                name = m.group(1)
    return name


def defined_names(src):
    names, in_doc = [], False
    for line in src.splitlines():
        quotes = line.count('"""')
        if in_doc:
            in_doc = quotes % 2 == 0
        elif quotes % 2 == 1:
            in_doc = True
        else:
            m = BINDING.match(line)
            if m and m.group(1) not in names:
                names.append(m.group(1))
    return names


def simplify_type(t):
    t = re.sub(r"\[\{[^}]*\}\]", "", t)       # grade sets, e.g. Float[{UoM}][...]
    t = re.sub(r"(\^-?\d+)\.0\b", r"\1", t)    # m^2.0 -> m^2
    return t


def run_fortl(program, offset=0, label="cell"):
    """Run a program; returns (ok, type, value) or (False, None, message)."""
    with tempfile.NamedTemporaryFile("w", suffix=".frtl", delete=False) as f:
        f.write(program)
        path = f.name
    try:
        proc = subprocess.run([FORTL, path], capture_output=True, text=True)
    except FileNotFoundError:
        return False, None, f"Cannot find the fortl executable `{FORTL}`"
    finally:
        os.unlink(path)

    out = ANSI.sub("", proc.stdout + proc.stderr)
    lines = [l for l in out.splitlines()
             if not (l.startswith("fortl v") or l.startswith("Checking "))]
    body = "\n".join(lines)

    m = re.match(r"Well-typed as ([^\n]*)\n?(.*)\Z", body, re.S)
    if proc.returncode == 0 and m:
        return True, simplify_type(m.group(1)), m.group(2).strip()

    def relocate(m):
        line = int(m.group(1)) - offset
        if line < 1:
            return f"(earlier cell):{m.group(1)}:{m.group(2)}"
        return f"{label}:{line}:{m.group(2)}"

    body = re.sub(re.escape(path) + r":(\d+):(\d+)", relocate, body)
    body = re.sub(r"^Not well-typed\.\n?", "", body)
    body = re.sub(r"^Error: ", "", body)
    return False, None, simplify_type(body)


class FortlKernel(Kernel):
    implementation = "fortl_kernel"
    implementation_version = __version__
    language = "fortl"
    language_version = "0.2"
    language_info = {
        "name": "fortl",
        "mimetype": "text/x-fortl",
        "file_extension": ".frtl",
        # fortl's syntax is Python-like, so borrow Python's highlighting
        "codemirror_mode": "python",
        "pygments_lexer": "python",
    }
    banner = "fortl - programming for science"

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.cells = []

    # -- helpers -----------------------------------------------------------

    def prefix(self):
        return "\n".join(self.cells)

    def run_in_session(self, text, show):
        """Run `text` after the session's definitions, showing binding `show`."""
        prefix = self.prefix()
        offset = len(prefix.splitlines()) if prefix else 0
        program = (prefix + "\n" if prefix else "") + text
        if show and show != "it":
            program += f"\nit = {show}"
        return run_fortl(program + "\n", offset)

    def send_result(self, name, ty, value):
        plain = f"{name} : {ty}" if name else ty
        rich = (f'<span style="{TYPE_STYLE}">{html.escape(name)} : </span>' if name else "") + \
               f'<span style="{TYPE_STYLE}">{html.escape(ty)}</span>'
        if value and value != "None":
            pad = " " * (len(name) if name else 0)
            plain += f"\n{pad}= {value}"
            rich += f"\n{pad}= <b>{html.escape(value)}</b>"
        self.send_response(self.iopub_socket, "execute_result", {
            "execution_count": self.execution_count,
            "data": {"text/plain": plain,
                     "text/html": f'<pre style="{OUT_STYLE}">{rich}</pre>'},
            "metadata": {},
        })

    def send_html(self, markup, plain=""):
        self.send_response(self.iopub_socket, "display_data", {
            "data": {"text/plain": plain, "text/html": markup},
            "metadata": {},
        })

    def send_text(self, text):
        self.send_response(self.iopub_socket, "stream",
                           {"name": "stdout", "text": text})

    def error(self, message, ename="TypeError"):
        if not self.silent:
            self.send_response(self.iopub_socket, "error", {
                "ename": ename, "evalue": "",
                "traceback": [f"\x1b[31m{message}\x1b[0m"],
            })
        return {"status": "error", "ename": ename, "evalue": message,
                "traceback": [message], "execution_count": self.execution_count}

    def ok(self):
        return {"status": "ok", "execution_count": self.execution_count,
                "payload": [], "user_expressions": {}}

    # -- magics ------------------------------------------------------------

    def magic_file(self, args):
        if not args:
            return self.error("usage: %file path [a-b] [show=name]", "UsageError")
        path, rng, show = args[0], None, None
        for a in args[1:]:
            if a.startswith("show="):
                show = a[5:]
            else:
                rng = a
        try:
            with open(path) as f:
                src = f.read()
        except OSError as e:
            return self.error(str(e), "FileNotFoundError")

        lines = src.splitlines()
        first, last = 1, len(lines)
        if rng:
            m = re.match(r"(\d+)(?:-(\d+))?$", rng)
            if m:
                first = int(m.group(1))
                last = min(int(m.group(2) or first), len(lines))
        note = "" if (first, last) == (1, len(lines)) else \
            f" <i>(lines {first}–{last} of {len(lines)})</i>"
        excerpt = "\n".join(lines[first - 1:last])
        # A relative link opens the file in JupyterLab's editor
        self.send_html(
            f'<div style="{FILE_STYLE}"><a href="{html.escape(path)}" target="_blank">'
            f'<code>{html.escape(path)}</code></a>{note}</div>'
            f'<pre style="{CODE_STYLE}">{highlight(excerpt)}</pre>', excerpt)

        program = src + (f"\nit = {show}\n" if show else "\n")
        ok, ty, value = run_fortl(program, 0, path)
        if not ok:
            return self.error(value)
        self.send_result(show, ty, value)
        return self.ok()

    def magic_load(self, args):
        if not args:
            return self.error("usage: %load path", "UsageError")
        try:
            with open(args[0]) as f:
                src = f.read()
        except OSError as e:
            return self.error(str(e), "FileNotFoundError")
        ok, ty, msg = self.run_in_session(src, None)
        if not ok:
            return self.error(msg)
        self.cells.append(src.rstrip("\n"))
        names = defined_names(src)
        self.send_text(f"Loaded {len(names)} definitions from {args[0]}: "
                       + ", ".join(names) + "\n")
        return self.ok()

    # -- kernel protocol ---------------------------------------------------

    def do_execute(self, code, silent, store_history=True,
                   user_expressions=None, allow_stdin=False):
        self.silent = silent
        stripped = code.strip()
        if not stripped:
            return self.ok()

        if stripped.startswith("%"):
            first, _, rest = stripped.partition("\n")
            magic, *args = first[1:].split()
            if magic == "reset":
                self.cells = []
                self.send_text("Session cleared.\n")
                return self.ok()
            if magic == "program":
                self.send_html(f"<pre>{highlight(self.prefix())}</pre>", self.prefix())
                return self.ok()
            if magic == "file":
                return self.magic_file(args)
            if magic == "load":
                return self.magic_load(args)
            return self.error(f"Unknown magic %{magic}", "UsageError")

        code = code.rstrip("\n")
        name = last_binding(code)
        if name is None:
            # An expression: evaluate it against the session, don't keep it
            ok, ty, value = self.run_in_session(f"it = ({code})", None)
            name = None
        else:
            ok, ty, value = self.run_in_session(code, name)
            if ok:
                self.cells.append(code)

        if not ok:
            return self.error(value)
        if not silent:
            self.send_result(name, ty, value)
        return self.ok()

    def do_complete(self, code, cursor_pos):
        m = re.search(r"[A-Za-z_][\w']*$", code[:cursor_pos])
        start = m.start() if m else cursor_pos
        word = m.group(0) if m else ""
        names = defined_names(self.prefix()) + KEYWORDS
        matches = sorted({n for n in names if n.startswith(word)})
        return {"status": "ok", "matches": matches, "cursor_start": start,
                "cursor_end": cursor_pos, "metadata": {}}

    def do_inspect(self, code, cursor_pos, detail_level=0, omit_sections=()):
        """Shift-Tab on a name shows its type (and value)."""
        word = None
        for m in IDENT.finditer(code):
            if m.start() <= cursor_pos <= m.end():
                word = m.group(0)
        if not word or word not in defined_names(self.prefix()):
            return {"status": "ok", "found": False, "data": {}, "metadata": {}}
        ok, ty, value = self.run_in_session("", word)
        if not ok:
            return {"status": "ok", "found": False, "data": {}, "metadata": {}}
        text = f"{word} : {ty}" + (f"\n= {value}" if value else "")
        return {"status": "ok", "found": True,
                "data": {"text/plain": text}, "metadata": {}}

    def do_is_complete(self, code):
        # Unbalanced brackets mean the cell continues (for the console)
        depth = sum(code.count(c) for c in "([{") - sum(code.count(c) for c in ")]}")
        return {"status": "incomplete" if depth > 0 else "complete", "indent": ""}
