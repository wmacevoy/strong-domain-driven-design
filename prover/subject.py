"""What reads a class out of another program: its own text, the names it is written with, and
the C++26 `pre( condition )` made readable.
"""

import os

from clang.cindex import CursorKind as CK

from clang_edge import Unsupported
from cxxtypes import OPTIONS
from reader import outer_constant, refuse


PRE_FLAGS = ["-Dpre(x)=", "-Dprooc_pre=__builtin_assume"]

# What stands before a class read from another program. The standard headers a class in the subset
# can need; and the two names a way in for code that is not proved is written with:
#   STRONG_CHECK( condition, from );   as the first statements of a `_checked` constructor or method:
#       the condition is tested when the program runs, and the process ends, saying who called,
#       if it is not so. Here it is read as what the rest of the body may rest on.
#   Strong::caller                     who called: a last parameter, with a default. Not modelled.
PRELUDE = ["#include <cstddef>", "#include <cstdint>", "#include <cstring>", "",
           "namespace Strong { struct caller { caller() {} }; }",
           # Strong::subarray<Iterator, Of>( a, n ): the n elements from a, read by at() and size(). Not modelled
           # as a class: it is the byte view (Prooc.Bytes), and this is the text the comparison runs.
           # That the elements are there, and stay, is whoever makes one to keep. Of says what they are,
           # to the compiler only: every window is the one byte view, whatever its Of.
           "#include <iterator>",
           "#ifdef PROOC_CHECKED", "#include <cstdlib>", "#define PROOC_INSIDE( c ) if ( !( c ) ) std::abort()",
           "#else", "#define PROOC_INSIDE( c )", "#endif",
           "namespace Strong { template <typename Iterator, typename Of = void> class subarray { Iterator first; uint64_t count; public: "
           "subarray( Iterator a, uint64_t n ) : first( a ), count( n ) {} uint64_t size() const { return count; } "
           "typename std::iterator_traits<Iterator>::value_type at( uint64_t i ) const { PROOC_INSIDE( i < count ); return *( first + i ); } }; }",
           # Strong::fixed<N, Of>( a ): the N bytes from a. The byte view too, of N bytes by its type: read at
           # an index written out below N, which the reader checks, so a read of one cannot fail.
           "namespace Strong { template <uint64_t N, typename Of = void> class fixed { const unsigned char* first; public: "
           "explicit fixed( const unsigned char* a ) : first( a ) {} uint64_t size() const { return N; } "
           "unsigned char at( uint64_t i ) const { PROOC_INSIDE( i < N ); return first[i]; } }; }",
           "#ifndef STRONG_CHECK", "#define STRONG_CHECK( condition, from ) prooc_pre( condition )", "#endif", ""]


def with_pre(index, here, text, flags):
    """C++26 says what a method expects of its caller after its parameters: `pre( condition )`. The
    library this reads C++ with does not know that, so the text is read with `pre(...)` as nothing,
    and each condition is found by its words and written again as the first statement of its
    method's body: `prooc_pre( condition );`. Nothing else of the text is changed, and no line
    moves. The text so written, or None if no method says `pre`. What is trusted here: that a
    condition means at the head of the body what it means after the parameters."""
    if "prooc_pre" in text.replace("\n".join(PRELUDE), ""):
        raise Unsupported("%s: the name prooc_pre is the generator's own" % here)
    tu = index.parse(here, args=flags + PRE_FLAGS, unsaved_files=[(here, text)], options=0x200)
    data = text.encode("utf-8")
    adds = []

    def walk(c):
        for x in c.get_children():
            if not x.location.file or os.path.abspath(x.location.file.name) != here:
                continue
            body = [y for y in x.get_children() if y.kind == CK.COMPOUND_STMT]
            if x.kind in (CK.CXX_METHOD, CK.CONSTRUCTOR, CK.FUNCTION_DECL) and len(body) == 1:
                stop = body[0].extent.start.offset
                toks = [t for t in x.get_tokens() if t.extent.start.offset < stop]
                depth, said, i = 0, [], 0
                while i < len(toks):
                    w = toks[i].spelling
                    if w == "pre" and depth == 0 and i + 1 < len(toks) and toks[i + 1].spelling == "(":
                        j, d = i + 1, 0
                        while j < len(toks):
                            d += {"(": 1, ")": -1}.get(toks[j].spelling, 0)
                            if d == 0:
                                break
                            j += 1
                        if j == len(toks):
                            refuse(x, "a pre( that is not closed")
                        said.append(data[toks[i + 1].extent.end.offset:toks[j].extent.start.offset].decode("utf-8").strip())
                        i = j
                    else:
                        depth += {"(": 1, ")": -1}.get(w, 0)
                    i += 1
                if said:
                    adds.append((stop + 1, "".join(" prooc_pre( %s );" % q for q in said)))
            else:
                walk(x)

    walk(tu.cursor)
    if not adds:
        return None
    for at, more in sorted(adds, reverse=True):
        data = data[:at] + more.encode("utf-8") + data[at:]
    return data.decode("utf-8")


def find_class(cursor, name, spaces=(), function=False):
    """Every definition of a class (or a function) of this name, with the namespaces it is in."""
    found = []
    for c in cursor.get_children():
        if c.kind == CK.NAMESPACE:
            found += find_class(c, name, spaces + (c.spelling,), function)
        elif (c.kind in (CK.CLASS_DECL, CK.CLASS_TEMPLATE, CK.FUNCTION_DECL) and c.is_definition() and c.spelling == name
              and (c.kind == CK.FUNCTION_DECL) == function):
            found.append((c, spaces))
    return found


NAMES = (CK.TYPEDEF_DECL, CK.TYPE_ALIAS_DECL, CK.TYPE_ALIAS_TEMPLATE_DECL, CK.VAR_DECL)


def needed_text(index, path, name, std, builtin):
    """A declaration that is not a class, which the class read is written with: a name for a type,
    or for a number. Its own text, as it stands in its file, in its namespaces. The file is read with
    PRELUDE before it, so that a name for a window (a template on Strong::subarray) is not dropped
    for want of the file's includes."""
    content = "\n".join(PRELUDE) + "\n" + open(path, encoding="utf-8").read()
    tu = index.parse(path, args=["-x", "c++", "-std=" + std] + builtin + PRE_FLAGS, unsaved_files=[(path, content)], options=0x200)
    here = os.path.abspath(path)

    def find(cursor, spaces):
        found = []
        for c in cursor.get_children():
            if c.kind == CK.NAMESPACE:
                found += find(c, spaces + (c.spelling,))
            elif c.kind in NAMES and c.spelling == name and c.location.file and os.path.abspath(c.location.file.name) == here:
                found.append((c, spaces))
        return found

    found = find(tu.cursor, ())
    if len(found) != 1:
        raise Unsupported("%s: %d declarations of %s that are a name for a type or a number (one is wanted)" % (path, len(found), name))
    c, spaces = found[0]
    text = content.encode("utf-8")[c.extent.start.offset:c.extent.end.offset].decode("utf-8")
    return ["namespace %s {" % sp for sp in spaces] + [text + ";"] + ["}" for _ in spaces]


def subject_text(index, path, name, std, builtin, function=False, uses=(), needs=()):
    """A class as it stands in a file of another program: its own text, not one character changed,
    with only the standard headers a class in the subset can need before it and its namespaces
    around it. The file is parsed here only to find where the class begins and ends: it need not
    compile alone (its other includes may be missing). Everything that is owed is then read from
    this text, which must compile alone, with no error."""
    tu = index.parse(path, args=["-x", "c++", "-std=" + std] + builtin + PRE_FLAGS, options=0x200)     # keep going past errors
    here = os.path.abspath(path)
    found = [(c, sp) for c, sp in find_class(tu.cursor, name, function=function)
             if c.location.file and os.path.abspath(c.location.file.name) == here]
    if len(found) != 1:
        raise Unsupported("%s: %d definitions of a %s %s (one is wanted)" % (path, len(found), "function" if function else "class", name))
    c, spaces = found[0]
    data = open(path, "rb").read()
    text = data[c.extent.start.offset:c.extent.end.offset].decode("utf-8")
    lines = "lines %d to %d of %s" % (c.extent.start.line, c.extent.end.line, os.path.basename(path))
    out = ["/* GENERATED by prover/prooc.py: %s %s, %s, as it stands there. */" % ("function" if function else "class", name, lines)] + PRELUDE
    for upath, uname in uses:      # the classes it takes as parameters, each as it stands, before it
        utext = subject_text(index, upath, uname, std, builtin)[0]
        out += utext.split("\n")[1 + len(PRELUDE):]
    for npath, nname in needs:     # and the names it is written with, each as it stands
        out += needed_text(index, npath, nname, std, builtin)
    for bpath, bname in ([] if name in OPTIONS["buffers"] else OPTIONS.get("buffer_files", [])):     # and its buffers' types, as they stand: not read, only compiled
        btext = subject_text(index, bpath, bname, std, builtin)[0]
        out += btext.split("\n")[1 + len(PRELUDE):]
    out += ["namespace %s {" % sp for sp in spaces]
    out += [text + ("" if function else ";")]
    out += ["}" for _ in spaces]
    return "\n".join(out) + "\n", lines, "::".join(spaces + (name,))


def file_scope(cursor, here, spaces_allowed):
    """The classes at file scope of the file `here`; anything else beside them is refused."""
    classes = []
    for c in cursor.get_children():
        if not c.location.file or os.path.abspath(c.location.file.name) != here:
            continue
        if c.kind == CK.CLASS_TEMPLATE and c.spelling in ("subarray", "fixed") and c.semantic_parent.spelling == "Strong":
            continue        # the windows on an array (PRELUDE): the byte view, not a class read here
        if c.kind == CK.CLASS_DECL and c.spelling in OPTIONS["buffers"]:
            continue        # a buffer the program says it is (read by a person): not a class read here
        if c.kind in (CK.CLASS_DECL, CK.CLASS_TEMPLATE) and c.is_definition():
            classes.append(c)
        elif c.kind == CK.FUNCTION_DECL and c.is_definition() and spaces_allowed == "function":
            classes.append(c)
        elif c.kind == CK.INCLUSION_DIRECTIVE:
            continue
        elif c.kind == CK.STRUCT_DECL and c.spelling == "caller" and c.semantic_parent.spelling == "Strong":
            continue        # who called (PRELUDE): not modelled
        elif c.kind in NAMES and (c.kind != CK.VAR_DECL or (c.type.is_const_qualified() and outer_constant(c) is not None)):
            continue        # a name for a type, or for a number a literal gives: no state
        elif c.kind == CK.NAMESPACE and spaces_allowed:
            classes += file_scope(c, here, spaces_allowed)
        else:
            refuse(c, "%s at file scope: a model is one class and nothing beside it (a global is "
                      "state outside the class)" % c.kind.name.lower().replace("_", " "))
    return classes
