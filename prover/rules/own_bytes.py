"""
own bytes  Outside STRONG, a value of a class declared under STRONG is reached by its methods
           and by copying it whole, and no other way: its address is not taken, a pointer or
           reference to it is not cast, and it is not a member of a union. So its fields are
           changed by its own methods and by nothing else. Refused otherwise.
"""
from clang.cindex import CursorKind as K, TypeKind as TK

from .names import CASTS, NOT_EXPRESSION, inner, line_at


class OwnBytes:
    def __init__(self, program):
        self.program = program
        self.refused = []

    def see(self, c, path):
        program = self.program
        if path.startswith(program.strong_dir):
            return
        proved_record = program.proved_record
        what = None
        if c.kind == K.UNARY_OPERATOR:
            first = next(iter(c.get_tokens()), None)
            ch = list(c.get_children())
            if first is not None and first.spelling == "&" and len(ch) == 1:
                r = proved_record(ch[0].type)
                if r and ch[0].type.get_canonical().kind not in (TK.POINTER,):
                    what = "the address of a %s is taken" % r
        elif c.kind in CASTS:
            ch = [x for x in c.get_children() if x.kind not in NOT_EXPRESSION]
            if ch:                      # a pointer to one, or one itself (cast as a reference), made something else
                r = proved_record(inner(ch[-1]).type) if inner(ch[-1]).type.get_canonical().kind in (TK.POINTER, TK.RECORD) else None
                if r and proved_record(c.type) != r:
                    what = "a %s is cast to something else" % r
        elif c.kind == K.UNION_DECL:
            for m in c.get_children():
                if m.kind == K.FIELD_DECL and proved_record(m.type):
                    what = "a %s is a member of a union" % proved_record(m.type)
        if what:
            rel, line = program.at(c)
            self.refused.append("%s:%d: outside %s/, %s: its fields could be changed by other than its methods:\n    %s"
                                % (rel, line, program.strong_name, what, line_at(path, line)[:150]))

    def found(self):
        return self.refused, {}
