"""What was read of a C++ class of the subset, as plain data: the tree between the reader
(reader.py, which alone asks Clang and alone refuses) and the writers (model.py, owed.py,
compare.py, which write Lean and C++ from it and refuse nothing). Its last section is the tree of a
proof file, between proofs_reader.py and proofs.py.

Each node is what the C++ says, already resolved by the reader: its types and widths (cxxtypes'
Int, BytesT, GenT, ClassT), its literal values, which field, local, parameter or view a name is.
Nothing of Clang is held. `place` is where it stands in the text read, "file:line:column", as messages
and the model's comments say it. Where spike-tree/Cxx.lean names a node, the name is the same.
"""

from dataclasses import dataclass, field, fields

from cxxtypes import lean_name


@dataclass
class Node:
    place: str = field(default="", kw_only=True)
    # How many parentheses stand around it in the text where the tree has no Paren: around a
    # condition, which the writers do not need, and spike-tree/tree.py writes back as words.
    parens: int = field(default=0, kw_only=True)


def walk(node):
    """The node and every node under it, in order: what the tree holds, not what it names (a call's
    method, a field, a type are not under it)."""
    yield node
    for f in fields(node):
        value = getattr(node, f.name)
        for x in (value if isinstance(value, list) else [value]):
            if isinstance(x, Node):
                yield from walk(x)


# ---- expressions: each is a number of its type, or (Cmp, LNot, Logic, NonZero, Truth) a condition

@dataclass
class Lit(Node):
    """A number of a width: an integer literal, a name for a number (a constant), or a literal
    converted where it stands. (spike: lit)
    `written`: the literal's own word, where it is an integer literal, alone or converted by C++
    unasked; else None. `converted`: in that conversion, the type it is converted to (an Int); else
    None. (The writers need neither; spike-tree/tree.py writes the tree back as words.)"""
    value: int
    width: int
    written: object = None
    converted: object = None


@dataclass
class Truth(Node):
    """`true` or `false`. (spike: truth)"""
    value: bool


@dataclass
class Name(Node):
    """A name, and what it names: "local", "param", "field" (of this object), "generic" (a value
    parameter of a class template), "object" (a value of another class, handed to a call), "var"
    (a variable of a proof file: a loop's). (spike: name)"""
    x: str
    what: str


@dataclass
class Conv(Node):
    """A conversion, asked for or not: `e`, of type `src`, as type `dst` (each an Int). `cast`: asked
    for, by a cast in words; else made by C++ unasked. `same`: the two are one type in the compiler's
    tree, `const` and all (it only reads a name; a field read in a const method is `const` and is
    not). (spike: conv)"""
    src: object
    dst: object
    e: Node
    cast: bool = False
    same: bool = False


@dataclass
class Paren(Node):
    """(spike: paren)"""
    e: Node


@dataclass
class Bin(Node):
    """`a op b`, op one of + - * & | ^, on one unsigned type. (spike: bin)"""
    op: str
    a: Node
    b: Node


@dataclass
class Cmp(Node):
    """`a op b`, op one of < <= > >= == !=, of two numbers of one type. (spike: cmp)"""
    op: str
    a: Node
    b: Node
    signed: bool


@dataclass
class Div(Node):
    """`a / b` or `a % b`, unsigned. `known`: b is a literal that is not zero."""
    op: str
    a: Node
    b: Node
    known: bool


@dataclass
class Shift(Node):
    """`a << b` or `a >> b`, unsigned: by `amount`, a literal below the width; or (amount None)
    by `b`, known only when it runs."""
    op: str
    a: Node
    b: Node
    amount: object


@dataclass
class Compl(Node):
    """`~e`."""
    e: Node


@dataclass
class LNot(Node):
    """`!c`, a condition."""
    c: Node


@dataclass
class Logic(Node):
    """`a && b` or `a || b`, conditions: b is not evaluated when a decides."""
    op: str
    a: Node
    b: Node


@dataclass
class NonZero(Node):
    """A number as a condition: `e != 0`, e of `width` bits."""
    e: Node
    width: int


@dataclass
class Value(Node):
    """A condition as a number: 1 or 0, of 8 bits (a bool)."""
    c: Node


@dataclass
class Elem(Node):
    """An element of one of the object's arrays, `field[index]`. `lit`: the index, where it is a
    literal of a signed type (an `int`); else None, and the index is unsigned."""
    field: str
    index: Node
    lit: object


@dataclass
class Size(Node):
    """How many bytes a view has: `size()` of a Bytes, or a pointer's length parameter."""
    view: str


@dataclass
class Byte(Node):
    """A byte of a view: `p[i]` or `d.at(i)`. By `lit`, a literal index; or (lit None) by `index`.
    `whole`: of a fixed window, at a literal index below its length, so there by its type."""
    view: str
    index: object
    lit: object
    whole: bool = False


@dataclass
class Call(Node):
    """A call of a method of this class on this object. `method` is that method (a Method, read
    before this one); `args` the arguments, a value of another class by its Name ("object")."""
    method: object
    args: list


@dataclass
class OtherCall(Node):
    """A call of a public const method of `obj`, a value of another class (`klass`, a ClassT):
    a parameter or a local, or (`field`) a field of this class that is such a value."""
    obj: str
    klass: object
    method: object
    args: list
    field: bool = False


@dataclass
class Made(Node):
    """`field( args )` in the initializer list, of a field that is a value of another class
    (`klass`, a ClassT): made by that class's constructor."""
    klass: object
    args: list


# ---- statements

@dataclass
class Skip(Node):
    """`;`, or a pre( condition ) written at the head of a body (it is the method's `pre`, not a
    statement). (spike: skip)"""


@dataclass
class Seq(Node):
    """Statements with no block of their own: a declaration of several names. (spike: seq)"""
    stmts: list


@dataclass
class Block(Node):
    """`{ ... }`: each statement of it, one for each in the text. (spike: block)"""
    stmts: list


@dataclass
class Set(Node):
    """`target = value;`. The target is a Name (a local, a parameter, a field) or an Elem.
    (spike: set)"""
    target: Node
    value: Node


@dataclass
class Compound(Node):
    """`target op value;`, op one of += -= *= &= |= ^=, on one unsigned type of 32 bits or more."""
    op: str
    target: Node
    value: Node


@dataclass
class Step(Node):
    """`target++` or `target--` (or before), its value not used: op is "++" or "--"."""
    op: str
    target: Node
    width: int


@dataclass
class Decl(Node):
    """`type x = value;`, a local number. `word`: the declaration's first word, the type as it is
    written. (spike: decl)"""
    x: str
    type: object
    value: Node
    word: str = ""


@dataclass
class ViewDecl(Node):
    """`const unsigned char* x = ... view ...;`: another name for the view `of`."""
    x: str
    of: str


@dataclass
class ObjDecl(Node):
    """`U x( args );`: a value of another class (`klass`, a ClassT), made by its constructor."""
    x: str
    klass: object
    args: list


@dataclass
class FieldDo(Node):
    """`field.method( args );`: a public method of a field that is a value of another class
    (`klass`, a ClassT), one that is not const, as a statement. The field becomes what the method
    leaves it; what it gives is kept nowhere."""
    field: str
    klass: object
    method: object
    args: list


@dataclass
class Ite(Node):
    """`if (c) then else other`; other is None if there is no else. (spike: ite)"""
    c: Node
    then: Node
    other: object


@dataclass
class WhileLoop(Node):
    """(spike: whileLoop)"""
    c: Node
    body: Node


@dataclass
class ForLoop(Node):
    """`for (init c; inc) body`. (spike: forLoop)"""
    init: Node
    c: Node
    inc: Node
    body: Node


@dataclass
class Ret(Node):
    """`return value;`, value None if there is none. A value that is a Call is `return method( ... );`:
    the method's state, then its answer. (spike: ret)"""
    value: object


@dataclass
class Throw(Node):
    """`throw E( literals );`: the method ends, and its caller is told it threw. What is thrown is
    not read: it is made of literals alone, so it says nothing of the state."""
    pass


@dataclass
class End(Node):
    """The process ends: `assert( c )` where c is not so (c None: `exit( n )`, `abort()`, always).
    Nothing of the program runs after it."""
    c: object
    how: str


@dataclass
class Break(Node):
    pass


@dataclass
class Continue(Node):
    pass


@dataclass
class CallStmt(Node):
    """A call of a method of this class, as a statement."""
    call: Node


@dataclass
class Memset(Node):
    """`memset( field, byte, sizeof( field ) )`: every byte of one of the object's arrays."""
    field: str
    byte: int


# ---- the class

@dataclass
class Init(Node):
    """`field( value )` in the constructor's initializer list; value None for `field()`, zeros."""
    field: str
    value: object


class Field:
    """A field: its name, its type (an Int, GenT, or a ClassT: a value of another class, a part
    this class has), and if it is an array, how many elements."""

    def __init__(self, name, type, count=None):
        self.name, self.type, self.count = name, type, count


class Method:
    """A method (or the one call of a function). `params`: (name, type) in order, a view's length
    not among them but in `lengths` (the length's name: the view's). `pre`: the conditions it
    expects of its caller, or (`tested`) tests when it runs. `fuel`: it has a loop, or calls a
    method that has (so its model is given a number of rounds). `words`: its body's, as the
    compiler's tokenizer gives them (spike-tree/tree.py checks its tree against them)."""

    def __init__(self, name, const, public, result, place=""):
        self.name, self.const, self.public, self.result, self.place = name, const, public, result, place
        self.params = []
        self.lengths = {}
        self.body = None            # a Block
        self.pre, self.tested = [], False
        self.fuel = False
        self.throws = False         # a `throw` is in its body
        self.ends = False           # an `assert`, `exit` or `abort` is: either way its model gives back a Prooc.Outcome
        self.words = []


class Klass:
    """A class read whole, or (is_function) a function read as a class with no state and one
    method, `call`. `generic`: of a class template, (the type parameter's name, the names of its
    value parameters). `inv`: the condition `invariant()` returns, or None."""

    generic = None

    def __init__(self, name, qual, place=""):
        self.name, self.qual, self.place = name, qual, place
        self.is_function = False
        self.fields = []
        self.field = {}                 # the fields by name
        self.constants = {}             # static const members with a literal value: names for numbers
        self.methods = []
        self.public = []
        self.uses = {}                  # the other classes its methods take or make, by name
        self.ctor_params = []
        self.ctor_pre, self.ctor_tested = [], False
        self.inits = []                 # the constructor's initializer list
        self.ctor_body = None           # a Block, or None for a function
        self.inv = None
        self.ctor_words = []            # the words of the constructor's body, and of the invariant's (as Method.words)
        self.inv_words = []

    # How the class is named in Lean, by every writer:

    @property
    def lt(self):
        """Its type, in Lean."""
        return "%s %s" % (self.name, self.generic[0]) if self.generic else self.name

    @property
    def gb(self):
        """What a class template's model is given before anything else: the type, that two values of
        it compare, and the values of its other parameters."""
        if not self.generic:
            return ""
        t = self.generic[0]
        return " {%s : Type} [LE %s] [DecidableLE %s] [Inhabited %s]" % (t, t, t, t) + "".join(" (%s : %s)" % (lean_name(v), t) for v in self.generic[1])

    @property
    def ga(self):
        return "".join(" " + lean_name(v) for v in self.generic[1]) if self.generic else ""


# ---- a proof file (model/forall.h): read by proofs_reader.py, written by proofs.py as what is owed.
# A PROVE's condition is a Cmp, Logic or LNot (`signed` always False) of conditions and numbers; a
# number is a Lit, a Name (what: "var", a variable of the proof: a loop's), or one of these.
# A proof is of a set of domains: the one whose file it is, and those proved before it. An object
# is of any class of the set, and `obj` and `klass` say which object and which class (the name it
# is proved under); a function of the set is called by CallFn.

@dataclass
class Ask(Node):
    """`obj.method( args )`, in a condition: a const method of an object of the proof. `args`:
    numbers."""
    method: str
    obj: str = None
    klass: str = None
    args: list = None


@dataclass
class AskInv(Node):
    """`obj.invariant()`, in a condition: the class's invariant holds of the object as it is."""
    obj: str = None
    klass: str = None


@dataclass
class CallFn(Node):
    """`f( args )`, in a condition: a function of the set (`fn`, the name it is proved under), which
    gives a number. `args`: numbers."""
    fn: str
    args: list


@dataclass
class Choose(Node):
    """`c ? a : b`, of numbers."""
    c: Node
    a: Node
    b: Node


@dataclass
class SeqSize(Node):
    """`x.size()`: how many bytes the sequence `x` of a loop over every_bytes() has."""
    x: str


@dataclass
class Window(Node):
    """`W( x.data(), x.size() )`, handed to a method: a window on all of a loop's sequence `x`."""
    x: str


@dataclass
class Make(Node):
    """`C x;` or `C x( args );`: an object of a class of the set, made. `args`: numbers."""
    x: str
    args: list
    klass: str = None


@dataclass
class Prove(Node):
    """`PROVE( c );`: c must be shown to hold here."""
    c: Node


@dataclass
class Do(Node):
    """`obj.method( args );`: a call of a method of an object, which says that it ends and
    commits no memory error. `void`: it gives nothing. `args`: numbers, or a Window."""
    method: str
    void: bool
    args: list
    obj: str = None
    klass: str = None


@dataclass
class AllValues(Node):
    """`for ( T x : all<T>() ) { body }`, every x of T, unsigned of `width` bits; or, `bounds` [lo, hi]
    (numbers), `all<T>( lo, hi )`. `carried`: what a round hands to the next, conditions (none where
    the loop is read before the object is made). `line`: the loop's, in the proof file."""
    x: str
    width: int
    bounds: list
    body: list
    carried: list
    line: int


@dataclass
class AllBytes(Node):
    """`for ( const std::vector<unsigned char>& x : every_bytes() ) { body }`: every sequence of
    bytes, of every length; or of `length` alone, `every_bytes( n )`. `carried` and `line` as AllValues's."""
    x: str
    body: list
    carried: list
    line: int
    length: object = None


@dataclass
class Proof(Node):
    """`PROOF( name ) { body }`."""
    name: str
    body: list
