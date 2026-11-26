"""
a domain  A program's parts are each a domain: a few directories, and of them the headers that are
          its ABI, the boundary; the rest is its inside, which only the domain uses. The program
          says them in a map: the file DOMAINS names, under SUBJECT (the rule is off without it):

              # a comment
              meetup  src/meetup src/strong/meetup | src/meetup/meetup.h src/meetup/ticket.h

          one line a domain: its name, its directories, `|`, its ABI headers. And a crossing that is
          there and is to go, one line each, so that the list can only shrink:

              allow src/pathfinding/finding.h meetup    # until meetup has an end

          a file that may still reach that domain's inside (or, for its own domain, an ABI header that
          may still name its inside): each such reach is said, every run, not refused; one that is not
          used any more is refused, so the line goes with it. Then, of every file
          under SUBJECT that is read:
            - a name declared in another domain is used only where that domain's ABI declares it,
              and only an ABI header of another domain is included;
            - what an ABI header declares (a function's parameters and result, a public field, a
              name for a type) names no type of its own domain's inside;
            - every source and header is of one domain, and an ABI header is of its own.
          Refused otherwise. What is outside SUBJECT (the system's, INCLUDE's) is no domain's, and
          is used freely. It costs nothing when the program runs: the compiler is not asked to
          hide anything, and the boundary is read here, from Clang's tree.
"""
import os
import re

import clang.cindex as ci
from clang.cindex import CursorKind as K

USES = (K.DECL_REF_EXPR, K.MEMBER_REF_EXPR, K.TYPE_REF, K.TEMPLATE_REF, K.CALL_EXPR, K.OVERLOADED_DECL_REF)
DECLARES = (K.FUNCTION_DECL, K.CXX_METHOD, K.CONSTRUCTOR, K.FIELD_DECL, K.TYPEDEF_DECL, K.TYPE_ALIAS_DECL, K.VAR_DECL)


INCLUDE = re.compile(r'^\s*#\s*include\s*"([^"]+)"', re.M)


def read_map(path):
    """([(name, [dir, ...], {abi header, ...})], {(file, domain): line}), from the DOMAINS file; SystemExit if it is not
    there, or a line is not one."""
    if not os.path.isfile(path):
        raise SystemExit("lint: cannot start: DOMAINS names %s, which is not there" % path)
    domains, allows = [], {}
    for n, line in enumerate(open(path, encoding="utf-8"), 1):
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        if line.startswith("allow "):
            words = line.split()
            if len(words) != 3:
                raise SystemExit("lint: %s:%d: a crossing is `allow FILE DOMAIN`" % (path, n))
            allows[(words[1], words[2])] = n
            continue
        if line.count("|") != 1:
            raise SystemExit("lint: %s:%d: a domain is `NAME DIR... | ABI-HEADER...`" % (path, n))
        left, right = line.split("|")
        words = left.split()
        if len(words) < 2:
            raise SystemExit("lint: %s:%d: a domain has a name and at least one directory" % (path, n))
        domains.append((words[0], [w.rstrip("/") for w in words[1:]], set(right.split())))
    return domains, allows


class ADomain:
    def __init__(self, program, map_path):
        self.program = program
        self.map_name = os.path.relpath(map_path, program.subject_dir)
        self.domains, self.allows = read_map(map_path)
        self.used = set()               # each allow that a reach was found for
        self.said = []
        self.refused = []
        self.seen = set()

    def rel(self, path):
        return os.path.relpath(os.path.realpath(path), self.program.subject_dir)

    def domain_of(self, rel):
        """The domain whose directory holds the file, the deepest if several; None if none."""
        best = None
        for name, dirs, abi in self.domains:
            for d in dirs:
                if (rel == d or rel.startswith(d + "/")) and (best is None or len(d) > len(best[1])):
                    best = (name, d, abi)
        return best

    def ours(self, path):
        return os.path.realpath(path).startswith(self.program.subject_dir)

    def check_files(self, paths, include_dirs):
        """Every source and header of the program is of a domain, and includes no other domain's inside; every ABI
        header is of its own, and there. The #include lines are read as they are written, each one: Clang's list
        has a header only where it was first read."""
        for path in paths:
            rel = self.rel(path)
            if self.domain_of(rel) is None:
                self.refused.append("%s: of no domain (%s says what each file is of)" % (rel, self.map_name))
            text = open(path, encoding="utf-8", errors="replace").read()
            for m in INCLUDE.finditer(text):
                for d in [os.path.dirname(path), self.program.subject] + include_dirs:
                    found = os.path.join(d, m.group(1))
                    if os.path.isfile(found):
                        self.see_include(path, found, text.count("\n", 0, m.start()) + 1)
                        break
        for name, dirs, abi in self.domains:
            for h in sorted(abi):
                if not os.path.isfile(os.path.join(self.program.subject_dir, h)):
                    self.refused.append("%s: %s's ABI names %s, which is not there" % (self.map_name, name, h))
                elif (self.domain_of(h) or (None,))[0] != name:
                    self.refused.append("%s: %s's ABI names %s, which is not in its directories" % (self.map_name, name, h))

    def see_include(self, source, included, line):
        """An #include of another domain's header that is not of its ABI."""
        if not (self.ours(source) and self.ours(included)):
            return
        here, there = self.domain_of(self.rel(source)), self.domain_of(self.rel(included))
        if here is None or there is None or here[0] == there[0] or self.rel(included) in there[2]:
            return
        self.found_one(source, there[0], "%s:%d: includes %s, of %s's inside" % (self.rel(source), line, self.rel(included), there[0]))

    def see(self, c, path):
        if c.kind in USES:
            self.use(c, path)
        elif c.kind in DECLARES:
            self.declare(c, path)

    def use(self, c, path):
        d = c.referenced
        if d is None or d.location.file is None:
            return
        d = d.canonical                                 # where it is first declared: an ABI header, if it is one
        if d.location.file is None or not self.ours(d.location.file.name):
            return
        here, there = self.domain_of(self.rel(path)), self.domain_of(self.rel(d.location.file.name))
        if here is None or there is None or here[0] == there[0]:
            return
        if self.rel(d.location.file.name) in there[2]:
            return
        key = (path, c.location.line, d.spelling)
        if key in self.seen:
            return
        self.seen.add(key)
        self.found_one(path, there[0], "%s:%d: uses %s, of %s's inside (%s)"
                       % (self.rel(path), c.location.line, d.spelling, there[0], self.rel(d.location.file.name)))

    def found_one(self, path, domain, what):
        """A reach into another domain's inside: said, if the map allows that file that crossing; refused otherwise."""
        if (self.rel(path), domain) in self.allows:
            self.used.add((self.rel(path), domain))
            self.said.append(what)
        else:
            self.refused.append(what + ": another domain is used by its ABI (%s)" % self.map_name)

    def declare(self, c, path):
        """What an ABI header declares names no type of its own domain's inside."""
        here = self.domain_of(self.rel(path))
        if here is None or self.rel(path) not in here[2]:
            return
        if c.kind in (K.CXX_METHOD, K.CONSTRUCTOR, K.FIELD_DECL) and c.access_specifier == ci.AccessSpecifier.PRIVATE:
            return                                      # of the class's own inside: not on its boundary
        p = c.semantic_parent
        while p is not None and p.kind in (K.CLASS_DECL, K.STRUCT_DECL, K.CLASS_TEMPLATE, K.UNION_DECL):
            p = p.semantic_parent
        if p is not None and p.kind not in (K.NAMESPACE, K.TRANSLATION_UNIT):
            return                                      # a local, or what a function's body declares: its inside
        types = []
        if c.kind in (K.FUNCTION_DECL, K.CXX_METHOD, K.CONSTRUCTOR):
            types = [c.result_type] + [a.type for a in c.get_arguments()]
        elif c.kind in (K.TYPEDEF_DECL, K.TYPE_ALIAS_DECL):
            types = [c.underlying_typedef_type]
        else:
            types = [c.type]
        for t in types:
            for named in self.named(t):
                f = named.location.file
                if f is None or not self.ours(f.name):
                    continue
                rel = self.rel(f.name)
                there = self.domain_of(rel)
                if there is not None and there[0] == here[0] and rel not in here[2]:
                    key = (path, c.location.line, named.spelling)
                    if key not in self.seen:
                        self.seen.add(key)
                        what = "%s:%d: %s, of %s's ABI, names %s, of its inside (%s)" % (self.rel(path), c.location.line, c.spelling, here[0], named.spelling, rel)
                        if (self.rel(path), here[0]) in self.allows:
                            self.used.add((self.rel(path), here[0]))
                            self.said.append(what)
                        else:
                            self.refused.append(what + ": what a boundary declares is of the boundary (%s)" % self.map_name)

    def named(self, t):
        """The declarations of the classes and types a type is made of: pointed to, referred to, an array's, a template's arguments."""
        out, todo, seen = [], [t], set()
        while todo:
            t = todo.pop()
            if t is None or t.spelling in seen:
                continue
            seen.add(t.spelling)
            if t.kind in (ci.TypeKind.POINTER, ci.TypeKind.LVALUEREFERENCE, ci.TypeKind.RVALUEREFERENCE):
                todo.append(t.get_pointee())
                continue
            if t.kind in (ci.TypeKind.CONSTANTARRAY, ci.TypeKind.INCOMPLETEARRAY):
                todo.append(t.element_type)
                continue
            decl = t.get_declaration()
            if decl is not None and decl.kind != K.NO_DECL_FOUND:
                out.append(decl)
            for i in range(max(t.get_num_template_arguments(), 0)):
                todo.append(t.get_template_argument_type(i))
        return out

    def found(self):
        for (f, d), n in sorted(self.allows.items()):
            if (f, d) not in self.used:
                self.refused.append("%s:%d: allows %s to reach %s's inside, and it no longer does: the line goes" % (self.map_name, n, f, d))
        return sorted(set(self.refused)), {"crossings": sorted(set(self.said))}
