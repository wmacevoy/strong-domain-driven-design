"""What was read of a C++ class of the subset, as plain data: the tree between the reader
(reader.py, which alone asks Clang and alone refuses) and the writers (model.py, owed.py,
compare.py, which write Lean and C++ from it and refuse nothing).

Each node is what the C++ says, already resolved by the reader: its types and widths (cxxtypes'
Int, BytesT, GenT, ClassT), its literal values, which field, local, parameter or view a name is.
None holds a cursor. `place` is where it stands in the text read, "file:line:column", as messages
and the model's comments say it. Where spike-tree/Cxx.lean names a node, the name is the same.
"""

from dataclasses import dataclass, field, fields


@dataclass
class Node:
    place: str = field(default="", kw_only=True)


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
    converted where it stands. (spike: lit)"""
    value: int
    width: int


@dataclass
class Truth(Node):
    """`true` or `false`. (spike: truth)"""
    value: bool


@dataclass
class Name(Node):
    """A name, and what it names: "local", "param", "field" (of this object), "generic" (a value
    parameter of a class template), "object" (a value of another class, handed to a call).
    (spike: name)"""
    x: str
    what: str


@dataclass
class Conv(Node):
    """A conversion, asked for or not: `e`, of type `src`, as type `dst` (each an Int). (spike: conv)"""
    src: object
    dst: object
    e: Node


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
    """A byte of a view: `p[i]` or `d.at(i)`. By `lit`, a literal index; or (lit None) by `index`."""
    view: str
    index: object
    lit: object


@dataclass
class Call(Node):
    """A call of a method of this class on this object. `method` is that method (a Method, read
    before this one); `args` the arguments, a value of another class by its Name ("object")."""
    method: object
    args: list


@dataclass
class OtherCall(Node):
    """A call of a public const method of `obj`, a value of another class (`klass`, a ClassT)."""
    obj: str
    klass: object
    method: object
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
    """`type x = value;`, a local number. (spike: decl)"""
    x: str
    type: object
    value: Node


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
