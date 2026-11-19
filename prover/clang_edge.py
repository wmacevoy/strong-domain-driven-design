"""
The edge to Clang's library: finding it, the compiler's own include directory, and the few questions asked of a cursor that the Python binding does not answer. Nothing else in the prover sets Clang up.
"""

import ctypes
import os
import subprocess

import clang.cindex as ci


def configure_libclang():
    """
    Prefer the toolchain's own libclang: it has to parse the same standard
    library headers the compiler will, and a pip-installed libclang that is
    older than the installed SDK cannot always do that.  Fall back to whatever
    the `libclang` wheel bundles.
    """
    for path in (
        "/Library/Developer/CommandLineTools/usr/lib/libclang.dylib",
        "/opt/homebrew/opt/llvm/lib/libclang.dylib",
        "/usr/local/opt/llvm/lib/libclang.dylib",
        "/usr/lib/llvm-18/lib/libclang.so.1",
        "/usr/lib/x86_64-linux-gnu/libclang-18.so.1",
    ):
        if os.path.exists(path):
            try:
                ci.Config.set_library_file(path)
                ci.Index.create()
                return
            except Exception:
                ci.Config.loaded = False
    try:
        ci.Index.create()          # the wheel's bundled copy
        return
    except Exception:
        raise SystemExit("prover: no libclang found -- pip install libclang")


def probe(argv, flag):
    """[flag, value] from a compiler query, or [] if the query fails."""
    try:
        out = subprocess.run(argv, capture_output=True, text=True, check=True)
        value = out.stdout.strip()
        return [flag, value] if value and os.path.exists(value) else []
    except Exception:
        return []


class Unsupported(Exception):
    """A construct outside the flattenable subset."""


def where(cursor):
    loc = cursor.location
    return "%s:%d:%d" % (os.path.basename(loc.file.name) if loc.file else "?",
                         loc.line, loc.column)


def operator_of(cursor):
    """The spelling of a binary or compound-assignment operator, asked of the library: the words are not where the cursor says, inside a macro's argument. "" if the library gives none."""
    lib = ci.conf.lib
    lib.clang_getCursorBinaryOperatorKind.argtypes = [ci.Cursor]
    lib.clang_getCursorBinaryOperatorKind.restype = ctypes.c_int
    lib.clang_getBinaryOperatorKindSpelling.argtypes = [ctypes.c_int]
    lib.clang_getBinaryOperatorKindSpelling.restype = ci._CXString
    text = lib.clang_getCString(lib.clang_getBinaryOperatorKindSpelling(lib.clang_getCursorBinaryOperatorKind(cursor)))
    text = text.decode("utf-8") if isinstance(text, bytes) else text
    return text or ""
