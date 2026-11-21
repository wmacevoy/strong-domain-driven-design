"""What the modules of the prover share, and none of it asks Clang: the names Lean is written with,
and the types a C++ class's numbers, views and parameters are read as (the reader makes them, from
Clang's types; the writers only look at them). Three pieces of state are kept here, as they were:
USED, OPTIONS and READ.
"""

OPTIONS = {"no_invariant": False}
LEAN_WORDS = set("""at by do else end for from fun have if in let match mut of open return show then
where with def theorem structure class instance namespace section import variable universe example
local private Type Prop given""".split())
OWN = ("me", "me'", "fuel", "left", "r")       # the model's own names: no name read may be one (reader.named)


def lean_name(name):
    """A name as Lean is written with it. A name of the model's own was refused by the reader, before
    anything was written: reaching here, it is the generator's fault, not the class's."""
    assert name not in OWN, "the reader let the model's own name '%s' through" % name
    return "«%s»" % name if name in LEAN_WORDS else name


class Int:
    """An integer type the model knows exactly: its width, and whether it is signed."""

    def __init__(self, width, signed=False, is_bool=False):
        self.width, self.signed = width, signed
        self.is_bool = is_bool          # a byte that is 0 or 1: every way to make one here gives one of them

    def lean(self):
        return "BitVec %d" % self.width


class BytesT:
    """The byte view: a parameter only. Either a `Bytes`, read by at() and size(); or a pointer to
    const bytes with the unsigned 64-bit parameter after it, its length: read by `p[i]`, and the
    length by its name. `readable` is false for `const char*`, whose bytes are signed: it is read
    through a `const unsigned char*` local made from it. `fixed` is N for a Strong::fixed<N, of>: a
    window whose length is its type, read only at an index written out below N."""
    width, signed, is_bool = None, False, False

    def __init__(self, length=None, readable=True, ctype="Bytes", fixed=None):
        self.length, self.readable, self.ctype, self.fixed = length, readable, ctype, fixed

    def lean(self):
        return "Prooc.Bytes"


class GenT:
    """The type parameter of a class template, of which nothing is known but that two values of it
    may be compared by `<=`. What is proved of such a class is proved for every type and every value
    of its other parameters at once."""
    width, signed, is_bool = None, False, False

    def lean(self):
        return "T"


class ClassT:
    """A value of another class, as a parameter: a domain of its own, proved apart. What is owed of
    a method that takes one is owed only for values that satisfy that class's invariant, since its
    constructor and its methods are the only ways to make one. Here it is used by calling its const
    methods, and no other way."""
    width, signed, is_bool = None, False, False

    def __init__(self, klass, at=None, qual=None):
        self.k = klass
        self.at = at            # of a class template: (the type its T is here, the values of its parameters)
        self.qual = qual or klass.qual
        self.ga = "".join(" %d#%d" % (v % (1 << at[0].width), at[0].width) for v in at[1]) if at else ""

    def lean(self):
        return "(%s (%s))" % (self.k.name, self.at[0].lean()) if self.at else self.k.name

    def inv(self, name):
        return "%s.Inv%s %s" % (self.k.name, self.ga, name)

    def of(self, t):
        """A type of the class's own, as it is here: its T is the type it was given."""
        return self.at[0] if isinstance(t, GenT) else t

    def params(self):
        return [(n, self.of(t)) for n, t in self.k.ctor_params]

    def same(self, other):
        return other is not None and self.k is other.k and self.ga == other.ga


USED = {}       # the classes used as parameters, by name: read once each

READ = {"text": b""}     # the text being read, as bytes: what a cursor's place is a place in


def convert(text, src, dst):
    """The value `text` of type src, as C++ converts it to dst."""
    if dst.is_bool and not src.is_bool:
        return "(if %s = 0#%d then 0#8 else 1#8)" % (text, src.width)
    if src.width == dst.width:
        return text
    if dst.width > src.width and src.signed:
        return "((%s).signExtend %d)" % (text, dst.width)
    return "((%s).setWidth %d)" % (text, dst.width)


def binders(m):
    return "".join(" (%s : %s)" % (lean_name(n), t.lean()) for n, t in m.params)


def result_type(m):
    return "Unit" if m.result is None else m.result.lean()
