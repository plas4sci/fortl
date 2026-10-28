"""
Register the fortl kernel with Jupyter:

    python -m fortl_kernel.install [--sys-prefix]

The kernelspec records this Python and the absolute path of `fortl`, so
the kernel works however Jupyter (or VS Code) is launched.
"""

import argparse
import json
import os
import shutil
import sys
import tempfile

from jupyter_client.kernelspec import KernelSpecManager

HERE = os.path.dirname(os.path.abspath(__file__))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--sys-prefix", action="store_true",
                        help="install into this environment rather than for the user")
    parser.add_argument("--fortl", default=shutil.which("fortl"),
                        help="path to the fortl executable")
    args = parser.parse_args()

    if not args.fortl:
        sys.exit("Cannot find `fortl` on the PATH; pass --fortl /path/to/fortl")

    spec = {
        "argv": [sys.executable, "-m", "fortl_kernel", "-f", "{connection_file}"],
        "display_name": "fortl",
        "language": "fortl",
        "env": {"FORTL_COMMAND": os.path.abspath(args.fortl)},
    }

    with tempfile.TemporaryDirectory() as d:
        with open(os.path.join(d, "kernel.json"), "w") as f:
            json.dump(spec, f, indent=2)
        for logo in ("logo-32x32.png", "logo-64x64.png"):
            src = os.path.join(HERE, logo)
            if os.path.exists(src):
                shutil.copy(src, d)
        dest = KernelSpecManager().install_kernel_spec(
            d, "fortl", user=not args.sys_prefix,
            prefix=sys.prefix if args.sys_prefix else None)
    print(f"Installed fortl kernel in {dest} (using {args.fortl})")


if __name__ == "__main__":
    main()
