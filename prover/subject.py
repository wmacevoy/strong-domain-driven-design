"""What reads a class out of another program: its own text, the names it is written with, and
the C++26 `pre( condition )` made readable.
"""

import os
import re

from clang.cindex import CursorKind as CK

from clang_edge import Unsupported
from cxxtypes import OPTIONS
from reader import named_in, outer_constant, refuse


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
# what `needs` may name: those, or a class the class read gives back a value of, which is not read, only compiled
NEEDED = NAMES + (CK.CLASS_DECL, CK.STRUCT_DECL)


def needed_text(index, path, name, std, builtin, kinds=None):
    """A declaration the class read is written with: a name for a type, or for a number; or a class
    it gives back a value of, which is not read. Its own text, as it stands in its file, in its namespaces. The file is read with
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
            elif c.kind == CK.LINKAGE_SPEC:
                found += find(c, spaces)
            elif (c.kind in (kinds or NEEDED) and c.spelling == name and c.location.file and os.path.abspath(c.location.file.name) == here
                  and (c.kind not in (CK.CLASS_DECL, CK.STRUCT_DECL) or c.is_definition())):
                found.append((c, spaces))
        return found

    found = find(tu.cursor, ())
    if not found and (kinds or NEEDED) == NEEDED:     # a class the file only declares (`class PRNG;`): declared so
        found = [(c, sp) for c, sp in find_decl(tu.cursor, (), name, here)]
    if len(found) != 1:
        raise Unsupported("%s: %d declarations of %s that are a name for a type or a number (one is wanted)" % (path, len(found), name))
    c, spaces = found[0]
    text = content.encode("utf-8")[c.extent.start.offset:c.extent.end.offset].decode("utf-8")
    return ["namespace %s {" % sp for sp in spaces] + [text + ";"] + ["}" for _ in spaces]


def find_decl(cursor, spaces, name, here):
    """The declarations of a class that are not its definition, in the file `here`: the first of them."""
    for c in cursor.get_children():
        if c.kind == CK.NAMESPACE:
            got = find_decl(c, spaces + (c.spelling,), name, here)
            if got:
                return got
        elif (c.kind in (CK.CLASS_DECL, CK.STRUCT_DECL) and c.spelling == name and not c.is_definition()
              and c.location.file and os.path.abspath(c.location.file.name) == here):
            return [(c, spaces)]
    return []


def subject_text(index, path, name, std, builtin, function=False, uses=(), needs=(), alone=False):
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
    out += [] if alone else ['#include "%s"' % os.path.abspath(f) for f in OPTIONS.get("includes", [])]     # headers it is written with: compiled, not read
    for upath, uname in uses:      # the classes it takes as parameters, each as it stands, before it
        utext = subject_text(index, upath, uname, std, builtin, alone=True)[0]     # (its own text: what the class read adds is added once, below)
        out += utext.split("\n")[1 + len(PRELUDE):]
    for npath, nname in needs:     # and the names it is written with, each as it stands
        out += needed_text(index, npath, nname, std, builtin)
    for oname, o in ([] if alone or name in OPTIONS["buffers"] else OPTIONS["outside"].items()):     # the functions outside, declared
        out += needed_text(index, o["file"], oname, std, builtin, kinds=(CK.FUNCTION_DECL,))
    for bpath, bname in ([] if alone or name in OPTIONS["buffers"] else OPTIONS.get("buffer_files", [])):     # and its buffers' types, as they stand: not read, only compiled
        btext = subject_text(index, bpath, bname, std, builtin)[0]
        out += btext.split("\n")[1 + len(PRELUDE):]
    for f in dict.fromkeys(([OPTIONS["defined"]] if OPTIONS["defined"] and not function and name not in OPTIONS["buffers"] else []) +
                           [OPTIONS.get("of", {}).get(u, {}).get("defined") for _, u in uses]):
        if f and not alone:
            out += standard_headers(f)     # what the definitions there are written with, of the standard library
    out += ["namespace %s {" % sp for sp in spaces]
    out += [text + ("" if function else ";")]
    if OPTIONS["defined"] and not function and not alone and name not in OPTIONS["buffers"]:
        out += defined_text(index, OPTIONS["defined"], name, std, builtin)
    out += ["}" for _ in spaces]
    for upath, uname in ([] if alone else uses):     # and each class it uses that is defined in a source file: those definitions, last
        theirs = OPTIONS.get("of", {}).get(uname, {})
        if theirs.get("defined"):
            uspaces = subject_text(index, upath, uname, std, builtin, alone=True)[2].split("::")[:-1]
            out += ["namespace %s {" % sp for sp in uspaces]
            out += defined_text(index, theirs["defined"], uname, std, builtin, only=theirs.get("only"))
            out += ["}" for _ in uspaces]
    return "\n".join(out) + "\n", lines, "::".join(spaces + (name,))


def standard_headers(path):
    """The standard headers a source file includes (`#include <...>`), as it says them."""
    return [l.strip() for l in open(path, encoding="utf-8") if re.match(r"\s*#\s*include\s*<[^>]+>\s*$", l)]


def defined_text(index, path, name, std, builtin, only=False):
    """The definitions, in a source file, of the methods and constructors of class `name` that
    are read (all of them, or those `only` names, and a constructor), each as it stands there. They
    are written after the class, in its namespaces, where `Name::method` means what it means in the
    file."""
    include = [("-I" + os.environ["SUBJECT"])] if os.environ.get("SUBJECT") else []
    tu = index.parse(path, args=["-x", "c++", "-std=" + std] + builtin + include + PRE_FLAGS, options=0x200)
    here = os.path.abspath(path)
    data = open(path, "rb").read()
    out = ["/* defined in %s: */" % os.path.basename(path)]
    # what a name means there: the file's using-directives at file scope (`using namespace Crypto::Imp;`)
    for c in tu.cursor.get_children():
        if c.kind == CK.USING_DIRECTIVE and c.location.file and os.path.abspath(c.location.file.name) == here:
            out.append(data[c.extent.start.offset:c.extent.end.offset].decode("utf-8") + ";")
    for c in tu.cursor.walk_preorder():
        if (c.kind in (CK.CXX_METHOD, CK.CONSTRUCTOR) and c.is_definition() and c.location.file
                and os.path.abspath(c.location.file.name) == here and c.semantic_parent is not None
                and c.semantic_parent.spelling == name and c.lexical_parent.kind != CK.CLASS_DECL):
            if only is False:
                only = OPTIONS["only"]
            if c.kind == CK.CXX_METHOD and only is not None and not named_in(c, only):
                continue
            out.append(data[c.extent.start.offset:c.extent.end.offset].decode("utf-8"))
    return out


def file_scope(cursor, here, spaces_allowed):
    """The classes at file scope of the file `here`; anything else beside them is refused."""
    classes = []
    for c in cursor.get_children():
        if not c.location.file or os.path.abspath(c.location.file.name) != here:
            continue
        if c.kind == CK.CLASS_TEMPLATE and c.spelling in ("subarray", "fixed") and c.semantic_parent.spelling == "Strong":
            continue        # the windows on an array (PRELUDE): the byte view, not a class read here
        if c.kind in (CK.CXX_METHOD, CK.CONSTRUCTOR) and c.semantic_parent is not None and c.semantic_parent.kind == CK.CLASS_DECL:
            continue        # a method of a class here, defined outside it (`defined FILE`): read with its class
        if c.kind == CK.FUNCTION_DECL and not c.is_definition() and c.spelling in OPTIONS["outside"]:
            continue        # a function outside the program, declared: called by its contract
        if c.kind == CK.CLASS_DECL and c.spelling in OPTIONS["buffers"]:
            continue        # a buffer the program says it is (read by a person): not a class read here
        if c.kind in (CK.CLASS_DECL, CK.CLASS_TEMPLATE) and c.is_definition():
            classes.append(c)
        elif c.kind in (CK.CLASS_DECL, CK.STRUCT_DECL) and not c.is_definition():
            continue        # a class declared, not defined (`class PRNG;`): a name, and no state
        elif c.kind == CK.FUNCTION_DECL and c.is_definition() and spaces_allowed == "function":
            classes.append(c)
        elif c.kind in (CK.INCLUSION_DIRECTIVE, CK.USING_DIRECTIVE):
            continue        # (a using-directive: what a name means, as the file defining the methods has it; no state)
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
