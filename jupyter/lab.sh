#!/bin/sh
# Start JupyterLab from the repository root, with the serif notebook style
# from ~/.jupyter/custom/custom.css.
cd "$(dirname "$0")/.." && exec jupyter/.venv/bin/jupyter lab --LabApp.custom_css=True "$@"
