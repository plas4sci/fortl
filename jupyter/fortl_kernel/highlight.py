"""Pygments highlighting for fortl, used for %file output."""

from pygments import highlight as pyg_highlight
from pygments.formatters import HtmlFormatter
from pygments.lexer import RegexLexer, bygroups, words
from pygments.token import (Comment, Keyword, Name, Number, Operator,
                            Punctuation, String, Text, Whitespace)


class FortlLexer(RegexLexer):
    name = "fortl"
    aliases = ["fortl"]
    filenames = ["*.frtl"]

    tokens = {
        "root": [
            (r'"""', String.Doc, "docstring"),
            (r'"[^"]*"', String),
            (r"#.*$", Comment.Single),
            (words(("lambda", "if", "else", "and", "or", "not", "let", "in",
                    "case", "of", "fix", "import", "from", "return", "forall",
                    "data"), suffix=r"\b"), Keyword),
            (words(("True", "False", "None"), suffix=r"\b"), Keyword.Constant),
            (words(("sqrt", "fst", "snd", "inl", "inr", "cast", "lift"),
                   suffix=r"\b"), Name.Builtin),
            (r"^([a-z_][\w']*)(\s*)(?=[:=])", bygroups(Name.Function, Whitespace)),
            (r"[A-Z][\w']*", Keyword.Type),
            (r"-?\d+\.\d+([eE]-?\d+)?", Number.Float),
            (r"-?\d+", Number.Integer),
            (r"->|[+\-*/^&=:|]", Operator),
            (r"[()\[\],.{}]", Punctuation),
            (r"[a-z_][\w']*", Name),
            (r"\s+", Whitespace),
            (r".", Text),
        ],
        "docstring": [
            (r'"""', String.Doc, "#pop"),
            (r'[^"]+', String.Doc),
            (r'"', String.Doc),
        ],
    }


_formatter = HtmlFormatter(nowrap=True, noclasses=True, style="friendly")


def highlight(code):
    return pyg_highlight(code, FortlLexer(), _formatter)
